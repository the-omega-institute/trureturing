# 递归关系观察：动态充分边界与内部观察者

本卷把主卷的过程、Context 卷的允许上下文、Recovery 卷的完成和 Transport 卷的记忆接口收束为一个最小研究对象：一族带类型的局部过程，以及一个内部观察者能够取得、保存并继续使用的边界表示。

本卷的“边界”不是预先给定的空间平面；它是对指定未来实验充分的关系摘要。空间连接、路径顺序、局部钟、档案和参考都可以进入同一个配置，但它们只有在声明了接口、合法域和共同来源以后才有相应含义。本文的新增组合为普通数学推导，未因此取得新的 Lean 核验；Lean 支点只按各自声明的量词引用。

已有接口：

- [过程几何卷](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 第 1、2、3、27 节给出部分过程、完整行为、拼接和预测接口；
- [上下文几何卷](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 第 1、2 节给出允许上下文和最小实验距离；
- [有效分辨率卷](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md) 给出受控动作、失败状态和动态闭合的算术实例；
- [运输、任务记忆与完成化卷](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) 给出记忆、代价和完成化的区别；
- [恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 给出逆极限、共同来源和实际像的边界。

## 1. 最小关系载体

**定义 1.1（带接口的关系过程）。** 一个关系过程载体由
\[
\mathfrak R=(S,\mathsf A,\mathsf D,\mathsf T,\mathsf O,\mathsf C,\mathsf P)
\]
组成。

这里 \(S\) 是实际配置的集合；\(\mathsf A\) 是带类型的操作接口；\(\mathsf D(a)\subseteq S\) 是操作 \(a\) 的合法域；\(\mathsf T_a:\mathsf D(a)\to S\) 是后继；\(\mathsf O_a:\mathsf D(a)\to Y_a\) 是输出；\(\mathsf C\) 是已经取得且仍可访问的记录；\(\mathsf P\) 是权限、参考和校准等会影响合法接续的配置。随机过程把 \(\mathsf T_a,\mathsf O_a\) 换成同一来源上的联合核，量子过程把它们换成声明过的仪器或通道。

配置必须来自共同来源的实际像。例如
\[
S\subseteq
C^{\rm archive}\times M^{\rm work}\times R^{\rm ref}\times P^{\rm access}
\]
只是值域记号；真正允许的配置是某个
\[
\Omega\longrightarrow
C^{\rm archive}\times M^{\rm work}\times R^{\rm ref}\times P^{\rm access}
\]
的像。把各部分分别可实现的值拼成一个元组，需要另证联合来源与合法性。

**定义 1.2（内部观察者配置）。** 内部观察者是配置中的一个子结构
\[
O=(C,\kappa,\rho,P),
\]
其中 \(C\) 是可访问档案，\(\kappa\) 是控制状态，\(\rho\) 是参考和校准，\(P\) 是当前权限。选择器
\[
a=\pi(O)
\]
只能读取 \(O\) 中声明的内容。若策略程序本身会被检查，它也必须作为配置或档案的一部分进入 \(O\)。

一次闭环接续写成
\[
\begin{aligned}
a&=\pi(C,\kappa,\rho,P),\\
(Y,s')&\sim T_a(s),\\
C'&=C\mathbin{\|}\operatorname{Record}(a,Y,\rho),\\
(\kappa',\rho',P')&=U(O,a,Y).
\end{aligned}
\tag{1.1}
\]
这里 \(Y\) 是实际取得的输出，不是从未读出的完整状态中预先选择的答案。

**定义 1.3（指定任务的未来等价）。** 固定一族共同允许的未来实验 \(\mathcal T\)。对两个同接口配置 \(s,t\)，定义
\[
s\equiv_{\mathcal T}t
\iff
\forall E\in\mathcal T,\quad
\operatorname{Obs}(E[s])=\operatorname{Obs}(E[t]).
\tag{1.2}
\]
读数应包含任务声明要求保留的成功、失败、合法性、记录和终止标签。概率模型比较完整结果分布。

式（1.2）是任务相关的行为商。它不声称 \(s,t\) 在所有未声明的实验中相同，也不声称观察者已经执行了 \(\mathcal T\) 中的每项实验。

仓内 CausalStateFactorization.causal_state_factorization 与 CanonicalPredictiveStateSufficiency.canonical_predictive_state_is_sufficient 分别给出了“接口因子化到未来律”和“完整条件未来律作为充分状态”的形式支点；它们的载体和概率假设不能被本卷的组合叙述扩大。

## 2. 边界何时可以成为真正的状态

设 \(\eta:S\to B\) 是把完整配置压到边界载体的映射。仅有一个函数 \(\eta\) 不足以称为状态；必须证明它对任务所需的后续操作闭合。

**定理 2.1（动态充分边界判据）。** 对每个允许操作 \(a\)，下列条件等价于在 \(B\) 上存在相应的合法性、读数和后继
\[
\bar D_a,\qquad \bar O_a,\qquad \bar T_a
\]
使
\[
\begin{aligned}
s\in\mathsf D(a)&\Longleftrightarrow \eta(s)\in\bar D_a,\\
\mathsf O_a(s)&=\bar O_a(\eta(s)),\\
\eta(\mathsf T_a(s))&=\bar T_a(\eta(s))
\end{aligned}
\tag{2.1}
\]
对每个 \(s\in\mathsf D(a)\) 成立。

等价条件是：只要 \(\eta(s)=\eta(t)\)，则 \(s,t\) 对 \(a\) 同时合法或同时非法；合法时输出相同；且后继边界相同。

**证明。** 若 \(\bar D_a,\bar O_a,\bar T_a\) 存在，三项条件直接由式（2.1）得到。反过来，在每个非空边界纤维上任选代表 \(s\)，定义 \(\bar D_a\) 为该纤维共同的合法性，定义 \(\bar O_a(\eta(s))=\mathsf O_a(s)\)，定义 \(\bar T_a(\eta(s))=\eta(\mathsf T_a(s))\)。纤维内的同合法性、同读数和同后继条件保证这些定义与代表选择无关。$\square$

如果策略也要在边界上运行，还必须加入
\[
\pi(s)=\bar\pi(\eta(s)).
\tag{2.2}
\]
否则同一边界可能要求两个不同的下一动作，边界虽能预测被动读数，却不能成为内部观察者的闭环状态。

这一定理是 InterfaceKernelCriterion.interface_refinement_iff_kernel_inclusion 与 PredictionCompletionUniversality.prediction_completion_universality 的过程化读法：先证明纤维上的未来响应恒定，再得到唯一的有效像因子。它并不把任意当前后验自动变成动态充分状态。

**推论 2.2（未来等价是最小精确边界）。** 令 \(\eta_\infty(s)=[s]_{\equiv_{\mathcal T}}\)。若 \(\mathcal T\) 对前后合法接续封闭，则 \(\eta_\infty\) 满足定理 2.1，并且任何满足定理 2.1 的边界 \(\eta\) 都因子化到 \(\eta_\infty\)。

证明只需把外部实验 \(E\) 与任意合法前后接续合并成新的测试。因而两个被同一 \(\eta\) 合并的配置必须属于同一未来行为类。反向闭合性给出行为类上的合法后继和读数。$\square$

## 3. 局部响应与边界拼接

固定一个可交换的组合系统 \((\oplus,\otimes)\)。\(\oplus\) 可以是计数加法、概率质量加法、逻辑或或最小值；\(\otimes\) 则按任务取乘法、逻辑且或代价加法。

设区域 \(\Sigma\) 的边界变量为 \(b\in B_\Sigma\)，内部变量为 \(x\)，局部规则为 \(f_\alpha\)。定义边界响应
\[
\mathcal H_\Sigma(b)
=
\bigoplus_x\ \bigotimes_{\alpha\in\Sigma} f_\alpha(x,b).
\tag{3.1}
\]

接入局部块 \(e:\Sigma\to\Sigma'\)，其内部可消去变量为 \(z\)，局部核为 \(W_e(b,z,b')\)。若区域之间的全部跨界关联都经过共同边界，且每条约束只计算一次，则
\[
\boxed{
\mathcal H_{\Sigma'}(b')
=
\bigoplus_{b,z}
\mathcal H_\Sigma(b)\otimes W_e(b,z,b').
}
\tag{3.2}
\]

**定理 3.1（边界拼接与核复合）。** 在上述截断条件下，定义
\[
K_e(b',b)=\bigoplus_zW_e(b,z,b').
\]
则
\[
\mathbf H_{\Sigma'}=K_e\mathbf H_\Sigma
\tag{3.3}
\]
并且连续接入 \(e,f\) 满足
\[
K_{f\circ e}(b'',b)
=
\bigoplus_{b'}K_f(b'',b')\otimes K_e(b',b),
\qquad
K_{f\circ e}=K_fK_e.
\tag{3.4}
\]

**证明。** 每份整体实现唯一给出一份共同边界赋值 \(b\)、左侧内部实现和右侧内部实现；反向把两侧在同一 \(b\) 上拼接即可。先汇总 \(z\)，再汇总 \(b\)，利用 \(\oplus,\otimes\) 的分配律得到式（3.2）—（3.4）。若存在未进入边界的共同随机种子、参考位、历史或约束变量，二侧不再条件独立，式（3.2）没有自动成立。$\square$

这一定理给出“全息”的任务含义：边界保存的是内部对允许外部接续的作用，而不是内部每个微观细节。

**命题 3.2（当前总量不是动态边界）。** 即使两个历史的总实现数相同，也可能有不同的后续响应。若边界有 \(b\in\{0,1\}\)，旧响应分别为 \((3,5)\) 与 \((4,4)\)，而新块只允许 \(b=0\)，拼接后的总数分别为 \(3\) 与 \(4\)。因此总量不能替代边界函数。

这也是 FiniteCapacity.finite_knowledge_capacity 只比较有限读数类数、不替代未来接口的原因。

## 4. 观察者的闭环边界

令完整边界响应为 \(\mathcal H_\Sigma\)，观察者状态为 \(O\)。内部选择器和局部核共同给出
\[
\begin{aligned}
a&=\pi(O),\\
\mathcal H_{\Sigma'}(b')
&=
\bigoplus_{b,z}\mathcal H_\Sigma(b)\otimes
W^{O}_{a,Y}(b,z,b'),\\
O'&=U(O,a,Y).
\end{aligned}
\tag{4.1}
\]

**定理 4.1（内部观察闭环的边界闭合）。** 假设 \(\eta\) 同时保留：

1. 当前边界响应对任务所需读数的充分类；
2. 选择器 \(\pi\) 所需的档案、控制、参考和权限；
3. 每个合法结果 \(Y\) 下的边界运输与观察者更新。

则 \((\eta(s),O)\) 的后继只依赖 \((\eta(s),O)\)，并且任意有限合法实验的结果分布由该联合边界递归计算。

**证明。** 对当前联合边界相同的两份配置，条件 2 给出相同动作，条件 1 给出相同当前接口律，条件 3 给出每个结果分支的相同后继。按实验长度归纳。$\square$

这里的“思考”只是内部过程的一类：重新排列旧记录可以改变可用性，却不自动增加关于固定目标的独立证据。把计算结果写回档案会改变后续可访问接口，因此即使即时信息增量为零，也不能在未检查动态充分性前把该步骤删除。

**命题 4.2（延迟解码关系不能只按当前后验合并）。** 设 \(X,K\) 是独立均匀 bit，第一条记录为 \(Y=X\oplus K\)。则
\[
I(X;Y)=0,\qquad I(X;Y\mid K)=1.
\tag{4.2}
\]
因此，若后续操作允许读取 \(K\)，保存 \(Y\) 是未来解码 \(X\) 所需的关系；只保存当前的 \(X\) 后验会把不同 \(Y\) 历史合并而失去动态充分性。

证明是四种联合赋值的直接计数。它说明“没有即时目标信息”不等于“没有未来作用”。$\square$

若在有限经典概率模型中 \(M'=U(M,A,Y)\) 是确定性记忆更新，且 \(A=\pi(M)\)，则
\[
I(X;M')-I(X;M)
=
I(X;Y\mid M,A)-I(X;M,A,Y\mid M').
\tag{4.3}
\]
第一项是本次取得的目标信息，第二项是没有保留进新记忆的目标相关信息。式（4.3）是指定概率模型下的平均恒等式，不是“整体封闭”自动给出的守恒律。

## 5. 分辨率改变与拼接交换

设 \(P_r\) 把精细边界响应汇总为粗边界响应。粗边界有自己的局部核 \(\bar K_e\) 当且仅当对声明的响应空间至少满足
\[
\boxed{
P_{r'}K_e=\bar K_eP_r.
}
\tag{5.1}
\]
在确定性配置层面，它对应
\[
\eta_{\Sigma'}T_a=\bar T_a\eta_\Sigma.
\tag{5.2}
\]

**定理 5.1（粗化—拼接交换的充分性）。** 若式（5.1）对每个共同允许的局部操作成立，则任意有限连续接入、任意只根据已取得记录选择的策略，都满足先精确运输再粗化与先粗化再运输的一致性。

**证明。** 对一步使用式（5.1）；对策略长度归纳时，当前粗记录决定与精细记录相同的动作，下一步再次使用式（5.1）。$\square$

任意投影都不满足式（5.1)。有限反例是共同边界 \(B=\{0,1\}\)，左侧只允许 \(A=\{0\}\)，右侧只允许 \(C=\{1\}\)，而粗化 \(q(0)=q(1)=*\)。精细拼接为空，粗化后却出现共同的 \(*\)。所以
\[
q(A\cap C)\ne q(A)\cap q(C).
\tag{5.3}
\]
粗化若要保持联合可行性，相关允许集合必须对 \(q\) 的纤维饱和，或必须把被遗漏的关系补回边界。

## 6. 从边界到几何表达

同一个动态充分边界可以有多种表达，表达之间的恢复必须由关系映射承担。

**定义 6.1（四种表达）。**

- 连接表达记录哪些端口可以共同作用；
- 路径表达记录合法接续、方向和事件词；
- 边界表达记录未来等价类或边界响应；
- 记忆表达记录观察者实际保存、可访问并能用于选择的状态。

它们不是四个独立宇宙。一个表达能否恢复另一个表达，取决于是否有保持合法性、读数、后继和共同来源的映射。

局部钟是路径上的累积量。例如
\[
\tau(uv)=\tau(u)+\tau(v)
\tag{6.1}
\]
可以定义实际历时或费用，但它未必是端点状态势差。正费用自环已足以阻止“时间只是终点减起点”的普遍化。

若在同一边界上沿闭路运输得到
\[
H_\gamma:B\to B,
\]
则 \(H_\gamma\) 是该边界表示的 holonomy。只有在声明所有闭路运输相容为恒等，或给出额外平坦性条件时，才能把局部坐标拼成一个无路径依赖的全局坐标。

**命题 6.2（逆系统是完成，不是免费全局状态）。** 对一族分辨率边界
\[
B_0\leftarrow B_1\leftarrow B_2\leftarrow\cdots
\]
，逆极限
\[
\varprojlim B_r
\]
由相容线程组成。每个有限层相容不保证线程来自原始实际配置；反向恢复原配置还需要实际像、分离性和存在性条件。该边界对应 Recovery 卷的完成—实现区分，以及 InverseLimitCompletion.stateThread_bijective_iff_complete_and_separates 等形式支点的量词范围。

因此“无穷”在本框架中首先是持续细化、仍有未吸收关系的边界，而不是一个观察者已经访问的额外状态。

## 7. 有限状态实例与状态数边界

**命题 7.1（HMM 预测秩下界）。** 设一个时间齐次有限状态 Markov/HMM 有 \(m\) 个隐藏状态，并保留完整输出历史。对每个正概率历史 \(h\)，令 \(\alpha_h\in\mathbb R^m\) 为隐藏状态后验；对每个固定未来事件 \(E\)，令 \(k_E\in\mathbb R^m\) 为从各隐藏状态开始取得 \(E\) 的概率。则
\[
R^h(E)=\alpha_h k_E.
\tag{7.1}
\]
故任何实际历史—固定未来测试矩阵的实秩不超过 \(m\)。

证明是后验条件化。若某一来源的实际矩阵秩为 \(15\)，则该 HMM 必须有 \(m\ge15\)。

这一命题与仓内 ReachableBehaviorMinimality.finite_state_minimality 的有限实现因子化方向一致；后者的动作、载体和可达性假设仍须逐项映射，不能只引用名称。

在当前 SOURCE72 的普通数学研究实例中，PROCESS100 的固定未来测试矩阵给出秩 \(15\)，而一个经独立审查的十四暂态加吸收态 Doob 构造给出 \(15\) 状态上界。因此在“有限、时间齐次、Markov/HMM、完整输出律相同”的合同内，最小状态数为 \(15\)。这不是仓库 Lean 定理，也不外推到历史依赖生成器、随机摘要、额外免费输入或未知模型的实际取得成本。

## 8. 形式化落点与未解决边界

本卷新增的组合关系可按以下顺序寻找形式化复用：

1. 用 PredictionCompletionUniversality.prediction_completion_universality 承担“交换关系推出完整未来读数因子化”；
2. 用 InterfaceKernelCriterion.interface_refinement_iff_kernel_inclusion 承担“边界细化等价于核包含”；
3. 用 CanonicalPredictiveStateSufficiency.canonical_predictive_state_is_sufficient 与 CausalStateFactorization.causal_state_factorization 承担未来律状态与条件独立；
4. 用 PredictionCompletionIdempotence.prediction_completion_idempotent 承担二次预测完成不再改变已完成商；
5. 用 ReadoutCoarseningKnowledge.readout_coarsening_shrinks_knowledge、FiniteCapacity.finite_knowledge_capacity 承担读数粗化的知识空间单调性与有限类数边界；
6. 用 ControlledBehaviorUniversality.controlled_behavior_universal_property（若动作合同满足其有限性与交换条件）承担当接口实现到行为商的唯一满射。

这些支点分别证明局部桥梁，尚未把本卷全部联合成一条新的 Lean 命题。特别是概率互信息式（4.3）、HMM 的 SOURCE72 状态构造、连续时间或量子通道版本都不能由上述名称自动获得形式核验。

本卷的最小研究判据是：对指定任务，边界必须同时保留合法性、读数、后继、策略和共同来源；若任一项不能在边界纤维上因子化，就只能把该表示标为近似或未闭合。它把空间、时间、边界和记忆统一为同一关系载体的不同表达，同时保留各自的成本、量词和恢复障碍。

## 9.99 追加锚

## 10. 四种表达的同一商与互相恢复

本节把连接、路径、边界和记忆放在同一个恢复判据中。恢复始终相对于同一实际来源和同一未来实验族；它不声称恢复未声明的内部细节。

### 10.1 表达的共同任务商

**定义 10.1（表达族）。** 设 \(S\) 是共同来源的实际配置像，\(\mathcal T\) 是对前后合法接续封闭的未来实验族。令

$$
s\sim_{\mathcal T}t
\quad\Longleftrightarrow\quad
\forall E\in\mathcal T,
\operatorname{Obs}(E[s])=\operatorname{Obs}(E[t]).
$$

记 \(K=S/{\sim_{\mathcal T}}\)、\(\kappa:S\to K\)。连接、路径、边界和记忆是同一 \(S\) 上的四个表示

$$
j:S\to J,\qquad p:S\to P,\qquad b:S\to B,\qquad m:S\to M.
$$

值域只取实际像 \(j(S),p(S),b(S),m(S)\)，不能把各部分分别可实现的值任意组成笛卡尔积。路径若携带累积钟读数，必须把 \((p,\tau)\) 作为联合表示。

称 \(e:S\to E\) 对 \(\mathcal T\) 充分，如果

$$
e(s)=e(t)\Longrightarrow\kappa(s)=\kappa(t),
\tag{10.1}
$$

称它无冗余，如果

$$
\kappa(s)=\kappa(t)\Longrightarrow e(s)=e(t).
\tag{10.2}
$$

因此精确、无冗余的表达满足 \(\ker e=\ker\kappa\)。

**命题 10.2（商因子化）。** 表达 \(e\) 充分，当且仅当存在唯一

$$
\widehat\kappa_e:e(S)\to K,\qquad
\kappa=\widehat\kappa_e\circ e.
\tag{10.3}
$$

它同时无冗余，当且仅当 \(\widehat\kappa_e\) 是双射；逆映射就是从任务商恢复该表达的唯一方式。

**证明。** 在每个 \(e\)-纤维上取代表定义因子，充分性保证与代表无关。无冗余使因子单射，实际像定义使其满射。反向直接由双射的纤维得到两项包含。证毕。

因此，空间、时间、边界和记忆互相恢复，要求四者在同一任务商上诱导双射，而不是仅仅拥有不同的图形或坐标记号。

### 10.2 动力学与策略的恢复

对每个操作 \(a\)，表达 \(e\) 还必须有合法域、输出和后继 \(D_a^e,O_a^e,T_a^e\)，满足

$$
s\in D_a\Longleftrightarrow e(s)\in D_a^e,\qquad
O_a(s)=O_a^e(e(s)),\qquad
e(T_a(s))=T_a^e(e(s)).
\tag{10.4}
$$

若表达驱动内部策略，还须满足 \(\pi(s)=\pi^e(e(s))\)。

**定理 10.3（动态互相恢复判据）。** 若 \(e_i,e_j\) 满足 \(\ker e_i=\ker\kappa=\ker e_j\) 及式（10.4），并且策略也因子化，则存在唯一双射

$$
R_{ij}:e_i(S)\to e_j(S),\qquad R_{ij}\circ e_i=e_j,
\tag{10.5}
$$

且

$$
R_{ij}(D_a^{e_i})=D_a^{e_j},\quad
O_a^{e_j}\circ R_{ij}=O_a^{e_i},\quad
R_{ij}\circ T_a^{e_i}=T_a^{e_j}\circ R_{ij}.
\tag{10.6}
$$

此外 \(R_{ji}=R_{ij}^{-1}\)，且 \(R_{ik}=R_{jk}\circ R_{ij}\)。

**证明。** 由命题 10.2 取 \(R_{ij}=\widehat\kappa_{e_j}^{-1}\circ\widehat\kappa_{e_i}\)。代入式（10.4）即得所有交换式；唯一性给出逆映射和三角恒等式。证毕。

若端点状态有正费用自环 \(q(T_\ell s)=q(s)\)、\(c(s,\ell)=1\)，则端点表达恒定而路径钟 \(\tau(\ell^n)=n\)。时间不能从端点状态恢复；必须把路径记录、费用标签或钟字段纳入表达，并保留 \(\tau(uv)=\tau(u)+\tau(v)\)。

### 10.3 共同来源与图册相容

在重叠表达上，恢复映射还必须来自同一来源：

$$
R_{ij}(e_i(\omega))=e_j(\omega),\qquad
R_{jk}\circ R_{ij}=R_{ik}.
\tag{10.7}
$$

若闭路运输 \(H_\gamma\ne\operatorname{id}\)，这些表示只能组成带 holonomy 的图册，不能压成无路径依赖的全局坐标。若所有闭路恒等、任务商分离且实际来源满足存在条件，才可粘成全局商表示。

**反例 10.4（边缘满不等于共同实现）。** 令

$$
\Omega=\{(x,y,z)\in\{0,1\}^3:x+y+z=0\pmod 2\}.
$$

任意两个坐标投影都满，但 \((1,1,1)\notin\Omega\)。二坐标表达可各自合法，不能因此把它们的边缘值任意拼成三坐标记忆。共同来源条件正是截住边界外仍影响联合实现的关系。

### 10.4 完成塔上的动态提升

设边界塔 \(B_0\xleftarrow{r_0^1}B_1\xleftarrow{r_1^2}B_2\leftarrow\cdots\)，层更新为 \(u_n:B_n\to B_n\)，并满足

$$
r_n^{n+1}\circ u_{n+1}=u_n\circ r_n^{n+1}.
\tag{10.8}
$$

对相容线程 \(t=(b_n)_n\) 定义 \((U_\infty t)_n=u_n(b_n)\)。式（10.8）保证它仍是相容线程。令 \(\iota:S\to\varprojlim B_n\) 为完整配置的线程读出。

**定理 10.5（动态完成提升判据）。** 存在 \(U:S\to S\) 使

$$
\iota\circ U=U_\infty\circ\iota
\tag{10.9}
$$

当且仅当

$$
U_\infty(\operatorname{ran}\iota)\subseteq\operatorname{ran}\iota.
\tag{10.10}
$$

若 \(\iota\) 分离配置，则 \(U\) 唯一；若 \(\iota\) 还是满射，则任意满足式（10.8）的层更新都有唯一全局提升，并且 \(\iota\) 给出共轭。

**证明。** 式（10.9）直接推出式（10.10）。反向对每个 \(s\) 选择其像的实际原像即可；分离性给唯一性，满射使像闭合自动成立。证毕。

这把边界运输回落为记忆更新分成三个独立条件：层间交换、实际像闭合和来源分离。InverseLimitCompletion.stateThread_bijective_iff_complete_and_separates 只在声明的完备与分离假设下供应静态双射；StableObservationInverseLimit.stable_observation_inverse_limit_laws 供应限制相容律，不能替代式（10.10）。

**反例 10.6（逐层合法而无全局提升）。** 取 \(B_n=\operatorname{Fin}(n+1)\)，限制为截断，令候选线程第 \(n\) 层值为 \(n\)，并令 \(u_n\) 把所有输入送到该层顶点。各 \(u_n\) 满足式（10.8），但该线程不在给定实际来源的线程像中；因此式（10.10）失败，不存在满足式（10.9）的全局记忆更新。局部交换不保证来源闭合。

因此，逆极限是表达的完成空间，不是免费的全局观察者。若空间、时间、边界和记忆都要在无限细化下互相恢复，必须同时验证式（10.7）和式（10.10）；有限层局部等式不足以推出全局恢复。

## 10.99 追加锚

## 11. 自适应预测档案与联合信念边界

完成塔处理的是分辨率方向的动态恢复；概率观察还需要说明当前档案究竟保留了哪些关于隐藏来源的联合关系。本节限定在 posterior-adaptive 子合同：控制器只能按当前 belief 选实验。完整观察者若还使用控制、参考、权限或旧档案，必须把这些分量并入边界并另证它们的纤维常值。

设 \(H\) 是历史集合，\(\beta:H\to\mathcal B\) 是历史的后验 belief。令 \(\Phi(h)\) 是从 \(h\) 出发、对所有有限 horizon、所有 belief-adaptive policy 和所有输出 transcript 的未来输出律族。

**命题 11.1（自适应档案的前向充分性）。** 在 Bayes 条件律、分支更新和实验核均来自同一共同来源的前提下，

$$
\beta(h)=\beta(h')\Longrightarrow\Phi(h)=\Phi(h').
\tag{11.1}
$$

这表示 posterior 是该子合同的一个动态边界；它不表示任意读取档案的策略都能从 posterior 恢复。

为得到反向结论，定义一步预测映射 \(L_e:\mathcal B\to\mathsf{Dist}(Y_e)\)。假设实验族满足可检验的 separating 条件

$$
\left[
\forall e,\forall o,\quad
L_e(o\mid b)=L_e(o\mid b')
\right]\Longrightarrow b=b'.
\tag{11.2}
$$

**定理 11.2（自适应 profile 的反向恢复）。** 在命题 11.1 的前提和式（11.2）下，

$$
\Phi(h)=\Phi(h')
\quad\Longleftrightarrow\quad
\beta(h)=\beta(h').
\tag{11.3}
$$

**证明。** 只取 horizon 一、固定实验 \(e\) 的常策略，以及单一输出 transcript \([o]\)，式（11.3）的左侧给出 \(L_e(o\mid\beta(h))=L_e(o\mid\beta(h'))\)。对全部 \(e,o\) 应用式（11.2）得到后验相等；正向是命题 11.1。证毕。

一步 separating 是容易检查的充分证书；一般的最弱条件是完整 profile 本身分离，即直接要求 \(\ker\Phi=\ker\beta\)。一步混合不分离时，多步自适应实验仍可能分离，不能把式（11.2）冒充必要条件。

### 11.1 分支更新的交换

对合法实验 \(e\) 和输出 \(o\)，写 \(h^+=\operatorname{extend}(h,e,o)\)。若共同来源的 Bayes 条件律给出

$$
\beta(h^+)=U_{e,o}(\beta(h)),
\tag{11.4}
$$

且零概率分支被排除或采用明示的 totalized update，则 profile 等价类上的分支更新

$$
\overline U_{e,o}([h]_\Phi)=[\operatorname{extend}(h,e,o)]_\Phi
\tag{11.5}
$$

是良定义的，并满足

$$
\overline\beta\circ\overline U_{e,o}
=U_{e,o}\circ\overline\beta,
\tag{11.6}
$$

其中 \(\overline\beta([h]_\Phi)=\beta(h)\)。定理 11.2 使 \(\overline\beta\) 在 realized belief image 上成为双射，所以式（11.6）把 profile 边界和 belief 边界动态互相恢复。

证明只需取 \(\Phi(h)=\Phi(h')\)，由式（11.3）得 \(\beta(h)=\beta(h')\)，再用式（11.4）得到两个扩展历史的后验相等，最后再次使用式（11.3）。正概率条件不能省略：零概率输出没有条件律，不能由分母为零的形式表达冒充可执行分支。

若内部观察者还保留 \((C,\kappa,\rho,P)\)，总边界应写成

$$
B(h)=\bigl(\beta(h),\kappa(h),\rho(h),P(h)\bigr).
\tag{11.7}
$$

此时必须分别证明策略、控制更新、参考更新和权限更新在 \(B\)-纤维上常值；posterior-only 的式（11.3）不能自动升级为完整内部观察者定理。这个区分把概率 belief 的动态充分性与一般档案记忆的动态充分性分开，避免把单一后验误当作所有关系的边界。

## 11.99 追加锚

## 12. 联合边界与策略残余的最小细化

第 11 节的 posterior 边界只对“策略由当前 belief 决定”的子合同充分。一般内部观察者还可能保留控制器、权限标签、校准状态或策略程序；这些量即使不改变当前目标的后验，也可能改变下一步是否合法、读出什么以及怎样更新。因此需要把当前状态和继续行动所用的策略作为同一实际来源上的联合读出处理。

### 12.1 当前读出与策略读出的共同细化

设 (S) 是同一共同来源的实际配置像，令

$$
c:S\to C,\qquad p:S\to P
$$

分别表示当前边界读出和下一步策略（也可以是权限、参考或控制器摘要）。只取实际联合像

$$
E=\operatorname{ran}(c,p)\subseteq C\times P,\qquad
e(s)=(c(s),p(s)).
$$

于是有精确的核恒等式

$$
\boxed{\ker e=\ker c\cap\ker p.}
\tag{12.1}
$$

这里的交集是历史在两份读出上同时相等；它不是把 \(\operatorname{ran}c\) 与 \(\operatorname{ran}p\) 的边缘值任意配成笛卡尔积。仓内 `JointReadoutSupremum.pair_readout_kernel` 对同一事实给出了集合商版本。

**命题 12.1（最小共同细化）。** 若另一读出 \(d:S\to D\) 能分别恢复 \(c\) 与 \(p\)，即存在实际像上的映射

$$
\bar c:\operatorname{ran}d\to\operatorname{ran}c,\qquad
\bar p:\operatorname{ran}d\to\operatorname{ran}p
$$

满足

$$
c=\bar c\circ d,\qquad p=\bar p\circ d,
$$

则存在唯一

$$
\bar e:\operatorname{ran}d\to E,\qquad e=\bar e\circ d.
$$

**证明。** 对 \(v=d(s)\) 定义

$$
\bar e(v)=\bigl(\bar c(v),\bar p(v)\bigr).
$$

若 \(d(s)=d(t)\)，两项分别相等，所以定义与代表无关；它落在 \(E\) 是因为该值等于 \(e(s)\)。唯一性由 \(e=\bar e\circ d\) 在实际像上逐点决定。证毕。

因此 \(e\) 是同时保留当前读出和策略读出的最小共同细化。它只是在任务确实需要两者时加入联合区别，并不声称恢复 \(S\) 中未声明的内部细节。

### 12.2 策略残余与何时可以只保存当前边界

定义当前 \(c\)-纤维中的策略残余为

$$
\operatorname{Res}_{c,p}(s,t)
\iff c(s)=c(t)\land p(s)\ne p(t).
$$

**定理 12.2（策略因子化的充要条件）。** 下列命题等价：

1. 存在唯一的实际像映射 \(\widehat p:\operatorname{ran}c\to\operatorname{ran}p\)，使 \(p=\widehat p\circ c\)；
2. 任意 \(c\)-纤维上的策略残余都为空：
   $$
   \forall s,t,\quad c(s)=c(t)\Longrightarrow p(s)=p(t);
   $$
3. 联合边界没有增加区别：
   $$
   \ker e=\ker c.
   $$

**证明。** \(1\Rightarrow2\) 由因子化直接得到。\(2\Rightarrow1\) 在 \(c\)-纤维上取代表定义 \(\widehat p\)，条件 2 保证无歧义；实际像保证值域正确，且逐点给出唯一性。由式（12.1），条件 2 等价于 \(\ker c\subseteq\ker p\)，再与 \(\ker e=\ker c\cap\ker p\) 合并即得 \(3\)。反向同理。证毕。

仓内 `AgencyEnrichment.strategy_factorization_iff_no_residual` 和 `agency_enrichment_kernel_eq_current_iff_no_residual` 正好供应这一充要条件。它只说明策略能否由当前读出恢复；不自动说明当前读出对外部任务充分。

若存在 \(s,t\) 使 \(\operatorname{Res}_{c,p}(s,t)\)，但策略会影响某个后续合法性、输出或后继，那么任何只使用 \(c\) 的表示都会把两份配置错误合并。此时 \(e\) 是至少要保留的联合边界；若策略对任务完全惰性，则可以在任务商中把这项残余声明为不相关，但不能同时声称恢复策略本身。

### 12.3 联合边界的动态闭合

令 \(T_a\) 是完整配置在操作 \(a\) 下的后继，\(D_a\) 是合法域，\(O_a\) 是指定输出。若存在实际像上的

$$
\bar T_a:E\to E,\qquad
\bar D_a\subseteq E,\qquad
\bar O_a:E\to Y_a
$$

满足

$$
\begin{aligned}
s\in D_a&\Longleftrightarrow e(s)\in\bar D_a,\\
O_a(s)&=\bar O_a(e(s)),\\
e(T_a(s))&=\bar T_a(e(s))\qquad(s\in D_a),
\end{aligned}
\tag{12.2}
$$

那么 \(e\) 是该操作合同下的动态充分边界。若当前读出与策略各自已有因子化更新

$$
c(T_a(s))=\bar c_a(c(s),p(s)),\qquad
p(T_a(s))=\bar p_a(c(s),p(s)),
$$

且合法性与输出也只依赖 \((c(s),p(s))\)，则可取

$$
\bar T_a(c,p)=\bigl(\bar c_a(c,p),\bar p_a(c,p)\bigr).
$$

仍需检查该联合值落在实际像 \(E\)；分别可实现的 \(c'\) 与 \(p'\) 可能没有同一份来源。反过来，若式（12.2）成立，投影 \(\operatorname{fst}\circ\bar T_a\) 和 \(\operatorname{snd}\circ\bar T_a\) 就给出两个分量的更新。

### 12.4 一个即时后验相同而未来解码不同的有限例

令共同来源为两个均匀 bit \((X,K)\)，观察者当前只显示

$$
C=X\mathbin\oplus K,
$$

而策略或参考摘要保存 \(P=K\)。四个来源配置均有正概率；对目标 \(X\) 而言，给定 \(C\) 仍为均匀后验：

$$
I(X;C)=0.
$$

未来允许一次 `decode` 操作，输出

$$
Y=C\mathbin\oplus P=X.
$$

同一 \(C\) 的两份历史具有不同 \(P\)，所以要求不同的未来输出。只保存当前后验或显示值不能定义统一的 `decode` 后继；联合边界 \(e=(C,P)\) 则在实际四点像上区分全部来源，并直接支持该操作。

这个例子说明“当前目标信息为零”与“该记录对未来没有作用”是两个不同命题。策略残余不要求整体联合熵增加，也不把 \(P\) 当作系统外免费输入。

### 12.5 递归观察者的有限层组合

若策略 \(p\) 本身由另一个内部观察者的边界 \(r:S\to R\) 产生，可继续取

$$
e_2(s)=\bigl(c(s),p(s),r(s)\bigr).
$$

有限次联合读出的核为所有分量核的交：

$$
\ker e_2=\ker c\cap\ker p\cap\ker r.
$$

改变配对顺序只改变乘积类型的括号；在实际像上由投影给出规范的重括号双射。因此“观察者观察策略，策略又读取参考”仍然是在同一关系结构内做共同细化，不需要在模型外增加一个观察宇宙。

但有限层逐次配对不自动给出无限递归的全局状态。无限层仍须满足第 10 节的三个条件：层间更新交换、逆极限线程落在实际来源像中、以及线程读出分离实际配置。

## 12.99 追加锚

## 13. 后验与续接残余的联合最小边界

第 12 节的 \((c,p)\) 可以具体化为隐藏来源的后验和仍决定未来续接的残余。这样可以说明何时联合边界确实是最小精确边界，而不把两个坐标分别可区分误当作联合 profile 必然可区分。

### 13.1 两个完整 profile

设 \(H\) 是实际历史集合，令

$$
\beta:H\to\mathcal B,\qquad r:H\to\mathcal R
$$

分别记录后验 belief 与续接残余。这里 \(r\) 可以是带类型的完整 continuation profile：它至少包含未来动作的合法性、策略所需控制读数以及任务要求保留的费用或终止标签。定义

$$
\Psi(h)=(\beta(h),r(h))
$$

并只取 \(\operatorname{ran}\Psi\) 作为联合边界值域。

若 \(H,\mathcal B,\mathcal R\) 的相关实际像均为有限集，则

$$
|\operatorname{ran}\Psi|
\le |\operatorname{ran}\beta|\,|\operatorname{ran}r|.
\tag{13.0}
$$

等号还需要每个 \(\beta\)-值纤维都与每个 \(r\)-值纤维相交；共同来源通常只实现其中一部分配对。仓内 `JointPredictionProductFullness.joint_prediction_product_fullness_criterion` 给出了这一有限乘积满性判据。

令 \(\Phi_\beta(h)\) 是所有 posterior-adaptive 有限实验的未来输出律族，令 \(\Phi_r(h)\) 是所有指定续接的合法性、控制读数、费用和终止 profile。联合 profile 为

$$
\Phi_J(h)=\bigl(\Phi_\beta(h),\Phi_r(h)\bigr).
$$

假设

$$
\ker\Phi_\beta=\ker\beta,\qquad
\ker\Phi_r=\ker r.
\tag{13.1}
$$

第一项可由第 11.2 节的一步 separating 条件得到；第二项是把 \(r\) 定义为完整续接 profile 的结果，或需要另行证明的策略最小性条件。

**定理 13.1（联合 profile 的最小性）。** 在式（13.1）下，

$$
\boxed{\ker\Phi_J=\ker\Psi=\ker\beta\cap\ker r.}
\tag{13.2}
$$

因此，任何摘要 \(q:H\to Q\) 若能因子化全部联合 profile，存在 \(F:\operatorname{ran}q\to\operatorname{ran}\Phi_J\) 使 \(\Phi_J=F\circ q\)，则

$$
\ker q\subseteq\ker\Psi.
\tag{13.3}
$$

也就是说，\(q\) 至少必须细化 \(\Psi\)。在前述联合 profile 已能由 \(q\) 因子化的充分性条件下，若再有 \(\Psi\) 能由 \(q\) 因子化（即 \(\ker\Psi\subseteq\ker q\)），两边核相等，因而在实际像上由唯一双射互相恢复。

**证明。** 有序对相等当且仅当两个坐标分别相等，所以
\(\ker\Phi_J=\ker\Phi_\beta\cap\ker\Phi_r
=\ker\beta\cap\ker r\)。若 \(\Phi_J=F\circ q\)，则 \(q(h)=q(h')\) 蕴含 \(\Phi_J(h)=\Phi_J(h')\)，得到式（13.3）。核相等时应用实际像上的商因子化即可。证毕。

不能把“\(\beta\) 能分离”和“\(r\) 能分离”替换成一个未经检验的逐坐标实验选择。两个坐标同时变化时，不同实验的输出差可能抵消；式（13.1）直接使用完整 profile，避免了这个量词错误。

### 13.2 联合分支更新的闭合

对合法实验 \(a\) 和正概率结果 \(y\)，假设共同来源给出

$$
\beta(h\cdot a,y)=B_{a,y}(\beta(h)),\qquad
r(h\cdot a,y)=R_{a,y}(r(h)).
\tag{13.4}
$$

并且动作合法性、策略选择以及输出核分别能从 \(r\)、\(\Psi\) 和 \(\beta\)（或 \(\Psi\)）恢复。若实际联合像对

$$
\Psi_{a,y}(b,u)=\bigl(B_{a,y}(b),R_{a,y}(u)\bigr)
$$

闭合，则

$$
\Psi(h\cdot a,y)=\Psi_{a,y}(\Psi(h)).
\tag{13.5}
$$

对 transcript 长度归纳，式（13.5）推出：任意 \(\Psi\)-adaptive policy 的联合合法性与未来输出律只依赖 \(\Psi(h)\)。令 \(\bar D_a\subseteq\operatorname{ran}\Psi\) 为由残余和联合边界恢复的合法域；若输出核还依赖 \(\beta\)--\(r\) 的联合相关，该相关必须已经纳入 \(r\) 或直接纳入 \(\Psi\)。更明确地，对固定 policy \(\pi_n\)，令 \(L_0((b,u),\varepsilon)=1\)，并在实际支持上定义

$$
L_{n+1}\bigl((b,u),y::w\bigr)
=\mathbf 1_{\{(b,u)\in\bar D_a\}}\,
K_{a}(y\mid b,u)
L_n\bigl(\Psi_{a,y}(b,u),w\bigr),
\qquad a=\pi_n(b,u),
\tag{13.6}
$$

非法分支质量取零。对 \(\Psi(h)=\Psi(h')\) 的两份历史，按 \(n\) 归纳得全部有限 transcript 律相同。式（13.6）应按分支理解：若 \(K_a(y\mid b,u)=0\)，则该 transcript 分支的质量定义为零；只有在 \(K_a(y\mid b,u)>0\) 时才调用 \(\Psi_{a,y}\) 的条件更新。随机策略若依赖随机源，必须把该源并入 \(r\) 或 \(\Psi\)。

## 13.99 追加锚

## 14. 嵌套观察者的复合下降

有限层递归还可以写成两个边界下降的复合。设

$$
q_1:S\to B_1,\qquad q_2:B_1\to B_2,\qquad q=q_2\circ q_1.
$$

对操作 \(a\)，假设内层更新满足

$$
q_1\circ T_a=\bar T^1_a\circ q_1.
\tag{14.1}
$$

若 \(q_2\) 的纤维在每个 \(\bar T^1_a\) 下稳定，即

$$
q_2(b)=q_2(b')
\Longrightarrow
q_2(\bar T^1_a(b))=q_2(\bar T^1_a(b')),
\tag{14.2}
$$

由 \(T_a:S\to S\) 和式（14.1）可知 \(\bar T^1_a(q_1(S))\subseteq q_1(S)\)。因此存在唯一实际像更新
\(\bar T^2_a:q_2(q_1(S))\to q_2(q_1(S))\)，使

$$
q\circ T_a=\bar T^2_a\circ q.
\tag{14.3}
$$

证明是在 \(q_2\)-纤维上定义 \(\bar T^2_a(q_2(b))=q_2(\bar T^1_a(b))\)，其中
\(b\in q_1(S)\)；式（14.2）保证无歧义，实际像保证值域正确，唯一性逐点成立。合法域、输出、费用和控制器也必须先在 \(q_1\)-纤维上因子化，再在 \(q_2\)-纤维上保持常值。

若外层观察者还要读取内层策略或档案 \(p:S\to P\)，这里的 \(p\) 必须是同一共同来源实际配置 \(S\) 的函数；若它依赖外置档案、控制器或随机种子，这些分量必须先并入 \(S\)，或作为明确匹配参数纳入合同。复合边界必须满足

$$
\ker q\subseteq\ker p,
\tag{14.4}
$$

等价地，\(p\) 在 \(q\)-实际像上因子化。否则 \(q\) 虽然对两层各自原任务充分，却不能支持 observer-of-observer 的首步选择；应改用联合边界 \((q,p)\)。

**反例 14.1（逐层充分不推出嵌套充分）。** 令

$$
S=\{0,1\}\times\{0,1\},\qquad q_1(x,b)=x,\qquad q_2=\operatorname{id}.
$$

内层和外层原合同都只读 \(x\)，因而 \(q_1\) 与 \(q_2\) 各自精确。现在允许外层的自读操作报告 \(p(x,b)=b\)，或根据 \(b\) 在两个动作之间选择。状态 \((0,0)\) 与 \((0,1)\) 具有相同复合边界 \(q=0\)，却要求不同报告或不同首步，违反式（14.4）；复合边界失效。加入 \(p\) 后，\((x,b)\) 恢复实际四状态并闭合。

所以递归观察的正确组合条件不是“每一层单独都有充分边界”，而是“外层核稳定于内层更新，并且外层要读取的内层 profile 在复合核上因子化”。这正是 `DescentCompositionLaw.descent_composition_law`、`ObserverMorphismComposition.observer_morphism_composition` 与 `AgencyEnrichment.strategy_factorization_iff_no_residual` 所对应的普通数学组合；这些仓内支点没有自动核验本节的联合概率合同。

## 14.99 追加锚

## 15. 双侧观察者态射与协议运输

第 14 节只追踪了状态边界的复合。可是一个边界是否充分，总是相对于允许的测试、协议或后续动作而言；只给状态侧的映射，不能说明外部读数在运输后仍有同一意义。为此，把状态和测试写成同一个双侧接口。

### 15.1 评价保持的双侧态射

设两个观察接口分别为

$$
E_1:X_1\times P_1\to L,\qquad
E_2:X_2\times P_2\to L.
$$

这里 \(X_i\) 是边界或观察者状态，\(P_i\) 是协议、测试或控制程序，\(L\) 是带标签的结果空间；失败、非法和记录差异若属于任务，就必须已经编码进 \(L\)。一对映射

$$
 f:X_1\to X_2,\qquad g:P_2\to P_1
$$

称为评价保持的双侧态射，如果

$$
\boxed{
E_2(f(x),p)=E_1(x,g(p))\qquad(x\in X_1,\ p\in P_2).
}
\tag{15.1}
$$

状态沿 \(f\) 正向运输，而协议沿 \(g\) 反向回拉。方向不能任意交换：外层协议先被翻译到内层，内层才可以执行它。

**命题 15.1（双侧态射复合）。** 若 \((f_1,g_1)\) 保持 \(E_1\) 到 \(E_2\) 的评价，\((f_2,g_2)\) 保持 \(E_2\) 到 \(E_3\) 的评价，则

$$
(f_2\circ f_1,\;g_1\circ g_2)
$$

保持 \(E_1\) 到 \(E_3\) 的评价：

$$
E_3((f_2\circ f_1)(x),p)
=E_1(x,(g_1\circ g_2)(p)).
\tag{15.2}
$$

**证明。** 对任意 \(x,p\)，先使用第二个态射得到
\(E_2(f_1(x),g_2(p))\)，再使用第一个态射得到
\(E_1(x,g_1(g_2(p)))\)，最后展开复合即可。这个命题正是仓内 ObserverMorphismComposition.observer_morphism_composition 的双侧版本；该既有 Lean 声明已核验这个函数等式，但没有替本节声明新的联合概率或部分域合同。

### 15.2 边界充分性的协议版本

令完整实际配置为 \(S\)，边界读出为

$$
q:S\to B,
$$

允许协议为 \(P\)，完整评价为

$$
E:S\times P\to L.
$$

称 \(q\) 对协议族 \(P\) 充分，如果存在唯一的实际像评价

$$
\bar E:\operatorname{ran}q\times P\to L
$$

使

$$
E(s,p)=\bar E(q(s),p).
\tag{15.3}
$$

“实际像”是必要的：若 \(B\) 中有从未由共同来源实现的值，\(\bar E\) 在这些值上的任意填充不构成观察者拥有的接口。

在完整协议族已经列明的前提下，式（15.3）等价于逐协议的核条件

$$
\boxed{
q(s)=q(t)\Longrightarrow
\forall p\in P,\ E(s,p)=E(t,p).
}
\tag{15.4}
$$

从式（15.3) 到式（15.4) 只需代入同一边界值。反过来，在 \(\operatorname{ran}q\) 上定义

$$
\bar E(q(s),p):=E(s,p).
$$

若 \(q(s)=q(t)\)，式（15.4）保证定义与代表无关；因此它给出唯一的 \(\bar E\)。这一步不能把各个 \(p\) 分别选出不同代表，也不能把边缘可实现的协议和状态自由配成乘积。

若外部协议 \(Q\) 先经 \(g:Q\to P\) 回拉，则相应充分性条件为

$$
E(s,g(r))=\widehat E(q(s),r),\qquad r\in Q,
\tag{15.5}
$$

并只要求 \(q\)-纤维在这组回拉协议下不可区分。扩大协议族会收紧核条件；缩小协议族可能允许更粗的边界。

### 15.3 把合法性、读数和记录放入同一个评价值

若任务同时要求合法域 \(D_p\subseteq S\)、输出 \(O_p\) 和事件记录 \(R_p\)，不要分别声称三个对象各自保持就已经得到整体充分。将它们打包为带标签结果

$$
E(s,p)=
\begin{cases}
(\mathsf{illegal},\,R_p(s)),&s\notin D_p,\\
(\mathsf{legal},\,O_p(s),\,R_p(s)),&s\in D_p.
\end{cases}
\tag{15.6}
$$

若还要保留费用、终止原因或控制器分支，就把相应标签加入 \(L\)。这样，式（15.4）同时强制：同一边界纤维上的配置具有相同合法性、输出和记录。

这一打包没有制造新的宇宙状态；它只是明确声明当前任务究竟允许哪些实验区分历史。若某个标签日后被加入任务，旧的 \(q\) 可能不再充分，必须按新的协议族重新计算核，而不能沿用旧商。

### 15.4 双侧态射与联合边界的关系

令当前读出 \(c:S\to C\)，策略或协议摘要 \(p:S\to P\)。若存在策略残余，即

$$
c(s)=c(t),\qquad p(s)\ne p(t),
$$

则一个只保留 \(c\) 的边界无法为所有依赖 \(p\) 的协议定义统一评价。联合读出

$$
e=(c,p):S\to C\times P
$$

的核为

$$
\ker e=\ker c\cap\ker p,
\tag{15.7}
$$

并且它是同时保留两项读出的最小共同细化。仓内 JointReadoutSupremum.pair_readout_kernel 和 pair_readout_least_common_refinement 已分别核验核交与最小共同细化；本节只把它们解释成协议运输的必要边界。

若策略实际能由 \(c\) 的实际像因子化，

$$
p=\widehat p\circ c,
\tag{15.8}
$$

则联合边界对该策略不增加区别。仓内 AgencyEnrichment.strategy_factorization_iff_no_residual 给出在实际像上的充要条件。注意式（15.8）只解决策略摘要的恢复；它还不保证 \(c\) 对其他协议、参考或隐藏来源充分。

### 15.5 三层复合的相容方程

设有三层状态下降与协议回拉：

$$
X_1\xrightarrow{f_1}X_2\xrightarrow{f_2}X_3,
\qquad
P_3\xrightarrow{g_2}P_2\xrightarrow{g_1}P_1.
$$

若每一层都满足式（15.1），则无论先组合哪一对，最终方程都是

$$
E_3(f_2(f_1(x)),p)
=E_1(x,g_1(g_2(p))).
\tag{15.9}
$$

状态侧的下降与协议侧的回拉因此构成一个相反方向的复合图。若各 \(X_i\) 只是名义载体，必须把每层限制到共同来源的实际像；若动作有部分合法域，则把合法性标签放入 \(L\)，并要求每次中间协议的回拉仍落在声明的域内。

这给出一个递归观察者的三层判据：

1. 每一层状态更新在上一层纤维上因子化；
2. 每一层外部协议在内层实际像上有明确回拉；
3. 评价、合法性和记录在复合后的纤维上保持常值。

缺少第 2 项时，可以得到状态的复合下降，却不能保证外层观察者仍能运行原协议。缺少第 3 项时，状态和协议映射形式上可复合，但失败、输出或档案会在边界纤维中分裂。

### 15.6 一个状态下降成立而协议运输失败的有限反例

令

$$
S=\{0,1\}\times\{0,1\},\qquad q(x,b)=x,\qquad P=\{r_0,r_1\},
$$

并定义

$$
E((x,b),r_0)=b,\qquad E((x,b),r_1)=1-b.
$$

状态 \(q\) 对只读取 \(x\) 的旧任务是精确的；但对协议族 \(P\)，两份配置 \((x,0)\) 与 \((x,1)\) 具有相同 \(q\) 值，却被 \(r_0\) 区分。因此不存在满足式（15.3）的 \(\bar E\)。

把策略位并入联合边界 \(e(x,b)=(x,b)\) 后，评价在实际四点像上直接下降。这个反例与第 14 节的嵌套失败相同，但双侧表述揭示了缺失项：状态下降本身没有运输外层协议。

### 15.7 对空间、时间和记忆表达的约束

在这一层，所谓“空间图、时间顺序和记忆档案”都可以看作不同的接口对：状态侧给出实际边界，协议侧给出允许的切面、路径或读取程序。它们只有在满足式（15.1）时，才是同一观察结构的不同表达。

因此需要区分三种结论：

$$
\boxed{
\text{状态核相等}\quad
\not\Rightarrow\quad
\text{协议评价相等}
}
$$

$$
\boxed{
\text{逐层协议可回拉}
+
\text{纤维稳定}
\Longrightarrow
\text{复合协议仍可评价}
}
$$

$$
\boxed{
\text{全部声明协议上的评价相等}
\Longleftrightarrow
\text{该边界对当前任务充分}
}
$$

第三个等价只在“全部声明协议”和实际像前提下成立。改变任务协议族、加入新记录标签或允许新的内部自读，都会改变任务核；这正是边界、分辨率和记忆不能脱离其合同单独比较的原因。

## 15.99 追加锚

## 16. 双侧行为商：状态与协议必须同时压缩

第 15 节给出了状态运输和协议回拉的双侧态射。本节再向内推进一步：如果状态和协议本身都含有可被任务区分的冗余，就不能只对状态取商。最小的关系对象应当同时记录“一个状态面对一个协议会给出什么评价”。

### 16.1 评价矩与两条行为核

固定共同来源的实际状态像 $S$、允许协议像 $P$ 和带标签的评价值 $L$，令

$$
E:S\times P\longrightarrow L.
\tag{16.1}
$$

$L$ 可以是读数、合法性、失败、事件记录、费用和终止标签的打包值。把这些标签省略，所得商只对较弱任务充分。

定义状态行核和协议列核：

$$
\begin{aligned}
s\mathrel{\sim_S}t
&\iff \forall p\in P,\ E(s,p)=E(t,p),\\
p\mathrel{\sim_P}q
&\iff \forall s\in S,\ E(s,p)=E(s,q).
\end{aligned}
\tag{16.2}
$$

第一条说两个状态对所有允许协议的行为相同；第二条说两个协议对所有实际状态的作用相同。它们分别是状态边界和协议菜单的任务商，而不是任意坐标的代数核。

令

$$
\bar S=S/{\sim_S},\qquad \bar P=P/{\sim_P}.
$$

则存在唯一的双侧评价

$$
\bar E:\bar S\times\bar P\to L,
\qquad
\bar E([s],[p])=E(s,p).
\tag{16.3}
$$

**命题 16.1（双侧评价下降）。** 式（16.3）良定义且唯一。

**证明。** 若 $s\sim_S t$ 且 $p\sim_P q$，则

$$
E(s,p)=E(t,p)=E(t,q).
$$

因此代表元的选择不影响右端。对商上的任意评价，代入 $([s],[p])$ 都必须得到 $E(s,p)$，故唯一。这个构造正是 `DoubleExtensionalEvaluationDescent.double_extensional_evaluation_descent` 的普通数学形式。\(\square\)

### 16.2 商后的两轴分离与幂等性

双侧商并不只是删除重复值；它还把“再用全部协议测试状态”与“再用全部状态测试协议”变成分离条件：

$$
\begin{aligned}
\bigl(\forall \bar p\in\bar P,\ \bar E(\bar s,\bar p)=\bar E(\bar t,\bar p)\bigr)
&\Longrightarrow \bar s=\bar t,\\
\bigl(\forall \bar s\in\bar S,\ \bar E(\bar s,\bar p)=\bar E(\bar s,\bar q)\bigr)
&\Longrightarrow \bar p=\bar q.
\end{aligned}
\tag{16.4}
$$

第一式把商中两个状态类提升回代表元，得到 $s\sim_S t$；第二式同理得到 $p\sim_P q$。这由 `CanonicalRowColumnSeparation.canonical_row_column_separation` 直接供应。

所以对同一个 $E$ 再做一次状态行商或协议列商，不会产生新的类：第一次商已经是相应轴上的行为分离正规形。这里的“幂等”只针对固定的评价和固定的协议族；加入新的读数、失败标签或自读协议后，$E$ 变了，旧商不自动保持充分。

### 16.3 先压状态还是先压协议

也可以先对原状态取商，再把在状态类上相同的协议取商；或者反过来先压协议，再压状态。这里每个第二阶段等价关系都由同一个 $E$ 的代表无关评价定义，而不是任意另选一个商。则存在保持代表元的规范双射，使两种顺序下的最终评价相同：

$$
\boxed{
\text{state-first quotient}
\cong
\text{protocol-first quotient},
\qquad
\bar E_{S\to P}=\bar E_{P\to S}.
}
\tag{16.5}
$$

`StateProtocolQuotientOrderCommutation.state_protocol_quotient_order_commutes` 给出这个交换的精确商构造、代表元公式和评价等式。它说明“空间切面先固定，时间协议后压缩”与“先合并等效协议，再压缩状态”不是两个不同的整体，只是同一双侧关系的两种消元顺序。

### 16.4 双侧核心的恢复判据

设另一个接口由

$$
u:S\to U,\qquad v:P\to V,\qquad F:U\times V\to L
$$

给出，且

$$
E(s,p)=F(u(s),v(p)).
\tag{16.6}
$$

若 $u$ 和 $v$ 只保留实际像，并满足各自的分离条件

$$
\begin{aligned}
u(s)\ne u(t)&\Longrightarrow\exists p\in P,
  F(u(s),v(p))\ne F(u(t),v(p)),\\
v(p)\ne v(q)&\Longrightarrow\exists s\in S,
  F(u(s),v(p))\ne F(u(s),v(q)),
\end{aligned}
\tag{16.7}
$$

则 $u$ 在 $\sim_S$ 的类上诱导双射

$$
\bar u:\bar S\xrightarrow{\ \cong\ }u(S),
$$

$v$ 在 $\sim_P$ 的类上诱导双射

$$
\bar v:\bar P\xrightarrow{\ \cong\ }v(P),
$$

并且

$$
F(\bar u([s]),\bar v([p]))=\bar E([s],[p]).
\tag{16.8}
$$

反之，若某个表示与 $(\bar S,\bar P,\bar E)$ 之间存在这种双侧双射并保持评价，则式（16.6)—（16.7）成立。因而，空间坐标、时间协议、边界状态和记忆读出只有在它们都能双射恢复这一个实际双侧核心时，才是同一任务下的互相恢复表达。

这比“状态边界的核相同”更强：即使两个状态表示相同，协议菜单仍可能被不同地压缩；缺少协议侧的分离，外层观察者的操作序列无法恢复。

更强的普适性可直接写成一个可复用条件。若 $f:S\to S'$、$g:P\to P'$ 都满射，存在 $E':S'\times P'\to L$ 使

$$
E(s,p)=E'(f(s),g(p)),
$$

并且 $E'$ 在状态轴和协议轴上分别外延，即相同整行或整列的元素必相等，那么存在唯一的双射

$$
\alpha:\bar S\xrightarrow{\ \cong\ }S',
\qquad
\beta:\bar P\xrightarrow{\ \cong\ }P'
$$

满足

$$
\alpha([s])=f(s),\qquad
\beta([p])=g(p),\qquad
E'(\alpha([s]),\beta([p]))=\bar E([s],[p]).
\tag{16.9}
$$

这正是冻结声明 `DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality`：满射排除不可达目标值，双轴外延排除目标内部重复，唯一双射因此给出所有实际表达之间的唯一运输。只有“有一个因子化函数”而没有这两个条件时，不能称为恢复；目标可能仍藏有重复状态，或包含共同来源从未实现的值。

在有限状态下，协议族也不必全部显式保存。若 $S$ 有限，`FiniteProtocolCompression.finite_protocol_subfamily_card_le_quotient_card_sub_one` 给出一个有限协议子集，保持完整协议族的状态行为商，并满足

$$
|P_0|\le |\bar S|-1.
\tag{16.10}
$$

这里的上界是指定评价任务的有限证书，不是固定记忆容量，也不表示无限协议的计算成本自动消失；每个被选协议的删除都会产生一个仍未被其他选项区分的状态对。

### 16.5 一个有限关系表

取 $S=\{s_0,s_1,s_2\}$、$P=\{p_0,p_1,p_2\}$，评价表为

$$
\begin{array}{c|ccc}
E&p_0&p_1&p_2\\ \hline
s_0&0&1&0\\
s_1&0&1&0\\
s_2&1&0&1
\end{array}
$$

状态行商把 $s_0,s_1$ 合并，协议列商把 $p_0,p_2$ 合并。双侧核心是一个 $2\times2$ 表：

$$
\begin{array}{c|cc}
\bar E&[p_0]=[p_2]&[p_1]\\ \hline
[s_0]=[s_1]&0&1\\
[s_2]&1&0
\end{array}
$$

先合并两条相同行再合并两列，或先合并两列再合并两行，都会得到同一张表。若只读取 $p_0$，则 $s_0,s_1,s_2$ 中的区分可能被错误地提前商掉；$p_1$ 是切开该纤维所需的未来协议。这是“当前边界读数相同”不等于“对所有后续协议相同”的最小二维例子。

### 16.6 对空间、时间、边界和记忆的统一读法

在这套结构中，可以作如下角色对应：

* $S$ 是某个切面上的实际边界配置，或观察者当前可处置的状态；
* $P$ 是允许的路径、动作词、时钟读取和自检程序；
* $E(s,p)$ 是把读数、合法性、记录和费用打包后的过程响应；
* $(\bar S,\bar P,\bar E)$ 是指定任务下的双侧最小关系核心。

空间改变通常改变 $S$ 的切面，时间改变通常改变 $P$ 的接续顺序，记忆改变 $E$ 的记录分量；它们只有在双侧商上仍由评价保持映射连接，才可称为同一关系的不同表达。若只证明状态运输而没有协议回拉，最多得到单侧坐标改写；若只证明边缘读数相等而没有共同来源，连式（16.1）的实际评价域都未建立。

因此，本节的精简对象不是一个更大的“全局状态”，而是一个可递归使用的二侧核：外层观察者可以把内层的状态类和协议类再次作为新的 $(S,P)$，对其评价重新取行商、列商和实际像。递归发生在同一个关系构造内，不需要为每一层另造系统外的坐标。

本节使用的有限商、双轴分离和两种商序等式分别对应已冻结的 `DoubleExtensionalEvaluationDescent`、`CanonicalRowColumnSeparation` 和 `StateProtocolQuotientOrderCommutation`。本节是它们对统一关系几何的普通数学组织，未新增 Lean 声明。

## 16.99 追加锚

## 17. 阶段化双侧自然性与整体恢复

双侧核心描述一个固定分辨率。若空间切面、时间协议和记忆深度继续细化，就得到两侧同时变化的阶段族，而不是一条预先给定的绝对时间轴。

### 17.1 阶段族的评价方程

令 $X_i$ 是第 $i$ 个状态切面，$P_j$ 是第 $j$ 个协议层，$L$ 是共同的带标签结果。设有降阶映射和协议回拉

$$
r_i^{i'}:X_{i'}\to X_i,
\qquad
\ell_j^{j'}:P_{j'}\to P_j
\qquad(i\le i',\ j\le j'),
$$

以及阶段评价 $E_{ij}:X_i\times P_j\to L$。双侧自然性要求

$$
E_{ij}(r_i^{i'}x,\ell_j^{j'}p)=E_{i'j'}(x,p).
\tag{17.1}
$$

这些限制还须满足恒等和传递复合律；并假设状态指标与协议指标有向，使任意两层都有共同细化层。式（17.1）说：先把细状态和细协议送到粗层再评价，与在细层直接评价相同。状态侧可以代表空间/边界分辨率，协议侧可以代表时间/动作深度；若档案随层传递，则它是同一方程中的记录分量，而不是第三个外部坐标。

若 $f_i:X_i\to Y_i$、$g_j:Q_j\to P_j$ 满足

$$
E'_{ij}(f_i(x),q)=E_{ij}(x,g_j(q)),
\tag{17.2}
$$

并且 $(f_i,g_j)$ 与各层的 $r,\ell$ 交换，则它们给出阶段族之间的双侧态射。逐层代入式（17.2）即可证明有限阶段复合保持评价；这把第 15 节的双侧态射提升为带切面和协议深度的自然变换。

### 17.2 相容线程与实际来源

相容状态线程是满足

$$
r_i^{i'}(x_{i'})=x_i
$$

的族 $x=(x_i)_i$；协议线程同理满足 $\ell_j^{j'}(p_{j'})=p_j$。在这些线程上，式（17.1）使所有有限层评价一致，因此可以定义形式极限评价

$$
E_\infty(x,p):=E_{ij}(x_i,p_j),
\tag{17.3}
$$

若状态和协议指标集分别是有向的（任意两层都有共同细化层），则对任意两组选定层可送到共同细化层，并由式（17.1）比较。因此只要选取的 $i,j$ 在这些有向系统中可共同比较，右端不变。

但形式极限线程的存在不等于它来自原始共同来源。令

$$
\iota:S\to\varprojlim_i X_i
$$

是实际配置的线程读出。若每层还有更新 $u_i:X_i\to X_i$，并满足

$$
r_i^{i'}\circ u_{i'}=u_i\circ r_i^{i'},
$$

则才可在相容线程上定义

$$
U_\infty((x_i)_i):=(u_i(x_i))_i.
$$

要把这个阶段更新提升回 $S$，至少需要

$$
U_\infty(\operatorname{ran}\iota)\subseteq\operatorname{ran}\iota.
\tag{17.4}
$$

若 $\iota$ 分离实际配置，提升唯一；若 $\iota$ 满射，则闭合条件自动成立。式（17.4）是“有限层都相容”与“同一整体中确有该配置”之间的缺口，不能用逐层自然性代替。仓内 `IndependentDescentCriterion.inverse_limit_descent_and_independent_converse`、`LocalDescentGlobalCompatibility.escaping_thread_not_in_global_image` 和既有完成化卷的实际像条件分别承担这三个边界。

### 17.3 局部胶合不自动给全局记忆

若阶段族还由多个局部切片覆盖，重叠上的评价相同只能给出局部匹配。要得到一个全局记忆线程，还需：

1. 重叠限制的评价相等；
2. 胶合后的状态和协议仍在共同来源实际像中；
3. 胶合后更新对下一层相容。

第一项是局部唯一性，第二项是存在性，第三项是动态闭合。缺少第二项时，可以得到一个形式上相容、但来源中不存在的线程；缺少第三项时，当前读出可胶合而下一次操作不能下降。`SheafPairwiseEqualizer.sheaf_sections_equiv_pairwise_equalizer` 只承担声明的匹配—唯一胶合接口，不能替这两项实际像条件。

### 17.4 四种表达的真正恢复条件

因此，空间切面 $X_i$、时间协议 $P_j$、边界摘要和记忆线程互相恢复，还要有线程级联合分离：若两个相容状态线程 $x\ne y$，必须存在某个 $i,j$ 及 $p\in P_j$ 使

$$
E_{ij}(x_i,p)\ne E_{ij}(y_i,p),
$$

协议线程也要满足对称条件。逐层每个评价都能区分有限状态，不保证这个条件；若协议族不共尾，两个不同的极限线程可能在所有已声明读数上仍相同。

在此基础上，空间切面、时间协议、边界摘要和记忆线程互相恢复要同时满足：

$$
\boxed{
\begin{gathered}
\text{双侧评价自然性},\\
\text{状态与协议两轴的行为分离},\\
\text{共同来源实际像闭合},\\
\text{胶合后的更新可提升且保持记录标签}.
\end{gathered}}
\tag{17.5}
$$

前两项给出表示内的可恢复性；后两项才把表示接回同一个整体。它们分别对应“能从当前接口算出未来响应”和“这个接口确实由某个共同来源配置实现”。只有四项同时成立，才可以把空间、时间、边界和记忆称为同一关系结构的不同表达，而不是四组彼此相容的边缘数据。

本节把已存在的完成化、胶合和独立下降支点接到第 16 节的双侧行为商上；它没有把逆极限中的虚拟线程当作物理配置，也没有新增 Lean 核验。

## 17.99 追加锚

## 18. 三阶关系：递归协议与扁平化条件

第 16 节的双侧核心把一次评价写成

$$
E:S\times P\longrightarrow L.
$$

这仍把协议 $p\in P$ 当作一个已经封装好的整体。内部观察者继续运行时，协议本身也可能有一个后续接口：先执行 $p$，再把取得的记录交给 $q$。此时不能只看两个边缘集合 $P,Q$；还要保留哪些 $(p,q)$ 真的可以接续。

### 18.1 把协议的关系显式放进评价

设

$$
D\subseteq P\times Q
$$

是合法的二段协议对，且有三阶响应

$$
E^{(2)}:S\times D\longrightarrow L.
$$

等价地，可以把它写成带部分定义域的关系值评价

$$
\widehat E:S\times P\longrightarrow (Q\rightharpoonup L),
\qquad
\widehat E(s,p)(q)=E^{(2)}(s,(p,q))
$$

其中未定义的 $q$ 仍然是一个失败或不合法标签，而不是空白。这样，“关系的关系”不是再加一个系统外观察者，而是把协议的后续接口作为评价的值的一部分。

如果存在一个实际的扁平协议载体 $R$、一个组合映射

$$
m:D\longrightarrow R
$$

以及

$$
E^{(1)}:S\times R\longrightarrow L
$$

满足

$$
E^{(2)}(s,(p,q))=E^{(1)}(s,m(p,q)),
\tag{18.1}
$$

那么 $m(p,q)$ 才是这两个协议在当前任务下的真正接法。$R$ 应取实际像 $m(D)$；把整个预设的集合当作可执行协议，会把未实现的组合误当成配置。

### 18.2 递归压缩需要联合合法域的同余性

对状态和联合协议分别定义行为等价：

$$
\begin{aligned}
s\sim_S t
&\iff
\forall (p,q)\in D,\quad
E^{(2)}(s,(p,q))=E^{(2)}(t,(p,q)),\\
(p,q)\sim_D(p',q')
&\iff
\forall s\in S,\quad
E^{(2)}(s,(p,q))=E^{(2)}(s,(p',q')).
\end{aligned}
\tag{18.2}
$$

这里第二行只比较 $D$ 中的实际协议对。若要先分别压缩 $P$ 与 $Q$，再重建联合协议，至少要满足四个条件：

1. **联合合法域饱和：**若 $(p,q)\in D$、$p\sim_Pp'$、$q\sim_Qq'$，则 $(p',q')\in D$；
2. **响应同余：**被合并的联合协议对对所有 $s$ 产生同一标签，包括合法性与失败标签；
3. **实际像闭合：**组合后的代表仍来自某个共同来源配置，而不是分别可达的两个边缘值；
4. **接续结合：**三段协议的两种括号化在实际像上给出同一联合协议类。

在这些条件下，先取 $S$ 的行商、再取 $D$ 的列商，或者先把 $D$ 扁平化到 $R$ 再取双侧商，都会得到保持评价的规范同构。证明只是把 (18.2) 的代表元换回 $S$ 和 $D$，用饱和性保证换元后的协议仍合法，再用 (18.1) 比较扁平代表。这里的“同构”依赖的是指定的 $D$、失败标签和共同来源；只对 $P$、$Q$ 的边缘读数相等不能推出它。

### 18.3 为什么不能默认使用 $P\times Q$

取

$$
S=\{s\},\qquad P=Q=\{0,1\},
\qquad D=\{(0,0),(1,1)\}.
$$

令

$$
E^{(2)}(s,(0,0))=0,
\qquad
E^{(2)}(s,(1,1))=1.
$$

两个边缘协议集合都完整出现，但 $(0,1)$ 与 $(1,0)$ 从未是合法接续。若把联合接口替换成 $P\times Q$，就会凭空加入两条没有来源、没有响应的路径；之后再对它们取商，无法恢复原来的合法过程。

这个有限反例说明：**递归观察的边界必须保存协议之间的关系，而不只是每个协议端口各自的可见值。**它与第 17 节的实际像条件是同一个缺口在第三个接口上的表现。

### 18.4 阶段化协议与 pro-object 的高阶版本

当 $S$、$P$ 或 $Q$ 都由逐步细化的阶段表示时，一个高阶协议不是“每个阶段随意选一张映射表”。对两个阶段图 $X:I^{\mathrm{op}}\to\mathcal C$、$Y:J^{\mathrm{op}}\to\mathcal C$，仓内冻结的
`GeneralHomFormula.pro_category_hom_formula` 给出

$$
\operatorname{Hom}(X_\bullet,Y_\bullet)
\cong
\varprojlim_{j\in J}\varinjlim_{i\in I}
\operatorname{Hom}(X_i,Y_j).
\tag{18.3}
$$

因此，协议的“关系的关系”同时包含：某个足够细的源阶段代表，以及在目标阶段上的相容类。`pro_hom_has_stage_representatives` 说明每个目标层分量可在某个源层取得代表；`pro_hom_stage_classes_compatible` 说明这些代表不能独立拼接，必须沿目标细化保持相容。

式 (18.3) 也解释了为什么不能把“每一层都找到一个局部接法”当成一个全局协议。全局对象要先成为同一个极限元素，才可以进入 (18.1) 的共同来源像。若再要求协议自读自身，仓内 `NoTerminalSelfDescription.no_terminal_self_description` 提供相应的边界：一个终端阶段不能把扭转后的自评价全部收进自身的同类型列举。

### 18.5 三阶互相恢复判据

在指定三阶任务下，空间切面、边界摘要、记忆读出和递归协议可以互相恢复，至少要同时满足：

$$
\boxed{
\begin{gathered}
\text{状态、联合协议与结果的评价下降良定义},\\
\text{联合合法域对两侧行为商饱和},\\
\text{扁平组合在实际来源像上结合},\\
\text{阶段线程的代表沿细化相容},\\
\text{实际像闭合且由全部联合协议分离}.
\end{gathered}}
\tag{18.4}
$$

前两项保证摘要可以继续执行；第三项保证“先接续再压缩”与“先压缩再接续”相同；后两项把形式上的极限和商接回同一个关系整体。少掉任一项，都可能出现同样的边缘读数、不同的联合合法性，或每个有限层都相容却不存在共同来源配置。

所以递归关系的最小载体不是无限增加的坐标串，而是一个带联合合法域的高阶评价对象

$$
\bigl(S,\ D\subseteq P\times Q,\ E^{(2)}\bigr),
$$

并在每次升阶时重复同一件事：保留实际接法，按全部后续实验取行为商，再证明组合、细化和实际来源三者交换。第 16 节的双侧核心是它的二阶特例；第 17 节的阶段自然性是它的多分辨率特例。本节没有新增 Lean 声明，公式和判据是对既有冻结结果的普通数学组织。

## 18.99 追加锚

## 19. 动态双侧行为商：未来响应决定真正的边界

第 16 节的行商和列商是针对一次固定评价的。它们还不保证更新以后仍能在商上运行：两个状态现在给出同一读数，下一次接续却可能把它们送到不同的行为类。因此，持续运行的观察者需要把未来响应也纳入边界定义。

### 19.1 把未来协议读数收进同一个核

设状态更新为 $F:S\to S$，协议推进为 $\sigma:P\to P$。若合法性、失败和记录也需要保留，就把它们一并编码进带标签的结果集 $\widehat L$，并令

$$
\mathcal E(s,p)(n):=E\bigl(F^{[n]}(s),\sigma^{[n]}(p)\bigr)\in\widehat L.
\tag{19.1}
$$

定义未来状态核和未来协议核：

$$
\begin{aligned}
s\approx_S t
&\iff
\forall n\in\mathbb N,\ \forall p\in P,\quad
\mathcal E(s,p)(n)=\mathcal E(t,p)(n),\\
p\approx_P q
&\iff
\forall n\in\mathbb N,\ \forall s\in S,\quad
\mathcal E(s,p)(n)=\mathcal E(s,q)(n).
\end{aligned}
\tag{19.2}
$$

它们分别要求所有未来深度和对方的全部接口都相同。只比较 $n=0$ 得到的是静态商；(19.2) 才是对后续选择、记录和失败都闭合的动态商。

由移位直接得到

$$
s\approx_S t\Longrightarrow F(s)\approx_S F(t),
\qquad
p\approx_P q\Longrightarrow \sigma(p)\approx_P\sigma(q).
\tag{19.3}
$$

因此 $F$ 与 $\sigma$ 唯一下降为商上的更新 $\bar F$、$\bar\sigma$。这正是一个边界可以继续运行，而不只是一次性回答问题的条件。

### 19.2 静态商失败的最小反例

取

$$
S=\{a,b,c\},\qquad P=\{0,1\},
$$

并令

$$
E(a,0)=E(a,1)=E(b,0)=E(b,1)=0,
\qquad E(c,0)=E(c,1)=1.
$$

静态行商把 $a,b$ 合并。现在定义

$$
F(a)=a,\qquad F(b)=c,\qquad F(c)=c.
$$

则 $a$ 的未来响应为 $(0,0,0,\ldots)$，而 $b$ 的未来响应为 $(0,1,1,\ldots)$。静态类 $[a,b]$ 的后继同时要求是 $[a,b]$ 和 $[c]$，所以不存在诱导的单值更新。动态核则把三个状态分开，正好恢复唯一后继。

协议轴有完全对称的现象：若当前 $p_0,p_1$ 的列相同，但 $\sigma(p_0)$ 与 $\sigma(p_1)$ 被下一层读数区分，则只取当前列商会破坏协议推进。故“当前读数相同”不能替代“全部未来协议相同”。

### 19.3 动态商的最小性与选择器条件

设摘要 $q_S:S\to B$ 能决定所有未来带标签读数，并存在 $\bar F:B\to B$ 使

$$
q_S\circ F=\bar F\circ q_S.
\tag{19.4}
$$

则

$$
q_S(s)=q_S(t)\Longrightarrow s\approx_S t.
\tag{19.5}
$$

换言之，任何真正可继续运行的摘要，都必须至少保留动态核所保留的区别；它可以更细，但不能更粗。协议摘要满足对称结论。在线性情形，冻结声明 `FutureReadoutQuotient.future_readout_quotient_is_coarsest_with_unique_dynamics` 以所有未来读出核的交集构造最粗商，并给出唯一诱导线性动力学；一般集合情形，`PredictionCompletionUniversality.prediction_completion_universality` 与 `PredictiveMemoryMinimalQuotient.predictive_memory_minimal_quotient` 给出完整未来轨迹因子化及其最小记忆像。

选择器也必须落在同一条件内。若 $A=\pi(M)$ 依赖记忆 $M$，而摘要只保留读数、不保留 $\pi$ 的动作分支，那么两个相同摘要可能选择不同协议，(19.4) 就不能成立。此时要么把动作、权限和失败标签加入 $\widehat L$，要么把选择器的残余加入边界；仓内 `AgencyEnrichment.strategy_factorization_iff_no_residual` 正是“无残余才能因子化”的这一侧条件。

### 19.4 有限深度稳定与无限未来

若任务只允许深度不超过 $N$，可以先用

$$
s\approx_{S,N}t
\iff
\forall n\le N,\ \forall p,\quad
\mathcal E(s,p)(n)=\mathcal E(t,p)(n)
$$

构造有限 horizon 边界。它随 $N$ 增大而细化；只有在某个有限深度关系已经永久稳定，才可把它当作无限未来商。仓内 `FiniteHistoryPermanentStability.finite_history_relation_stable_forever` 给出这种“相邻深度稳定即永久”的有限条件。否则，所有有限层都可有一个商，并不表示存在一个固定有限边界保留全部无限行为。

同理，阶段索引 $n$ 是协议深度，不自动是物理时间。`ClockTimeVersusRefinementDepth.clock_time_does_not_determine_refinement_depth` 保留了这一区分；实际时钟仍需作为标签或独立可观察量放进 (19.1)。

### 19.5 四种表达的动态恢复

把第 17 节的阶段自然性、第 18 节的联合合法域和本节的未来核合在一起，空间切面、时间协议、边界摘要和记忆线程要互相恢复，至少需要

$$
\boxed{
\begin{gathered}
\text{双侧未来核对状态和协议都分离},\\
F,\sigma\text{ 在这些核上下降且选择器同样因子化},\\
\text{联合协议域对商饱和并在实际像上结合},\\
\text{阶段线程相容，更新保持共同来源实际像闭合}.
\end{gathered}}
\tag{19.6}
$$

前两项使摘要可继续执行，第三项防止把两个边缘协议误拼成一个不存在的联合接法，最后一项把形式商和极限线程接回同一个整体。静态双侧商只有在 (19.3) 与选择器条件已经成立时，才是动态双侧商的等价表达。本节是对既有冻结声明的普通数学组合，没有新增 Lean 声明。

## 19.99 追加锚

## 20. 合法动作词树：把空间、时间、边界和记忆收束到一个过程核

固定的 $F$ 和 $\sigma$ 仍然把“下一步能做什么”预先写死了。内部观察者通常还带有权限、失败和记录：同一个动作在不同状态可能合法，也可能只产生一个失败事件。为此，最小载体应改为一个带标签的合法动作词树。

### 20.1 总化失败而不是删除非法边

令 $A$ 是动作字母表，$S_\bot=S\sqcup\{\dagger\}$ 是加入吸收失败状态后的配置集。对每个 $a\in A$，给出

$$
T_a:S_\bot\to S_\bot,
\qquad
O_a:S_\bot\to\widehat L,
$$

其中 $T_a$ 把非法接续送到 $\dagger$，$O_a$ 的值域 $\widehat L$ 同时包含正常读数、失败原因、权限结果和必要的记录标签。$\dagger$ 的后续动作仍可得到固定的失败记录；因此非法分支没有从模型中消失，也不会被当作“没有输出”。

对动作词 $w=a_1\cdots a_n\in A^*$，递归运行并收集完整标签词，记为

$$
\operatorname{Trace}(s,w)\in\widehat L^*.
$$

完整未来 profile 是

$$
\Phi(s):A^*\to\widehat L^*,
\qquad
\Phi(s)(w)=\operatorname{Trace}(s,w).
\tag{20.1}
$$

若任务只允许一部分动作词，则把不允许的词也解释为带原因的失败标签；这样所有未来测试仍在同一个固定的 $A^*$ 上，权限条件成为响应的一部分。

### 20.2 未来核是唯一可递归的最小边界

定义

$$
s\sim_{\mathrm{word}}t
\iff
\forall w\in A^*,\quad \Phi(s)(w)=\Phi(t)(w).
\tag{20.2}
$$

对任意首动作 $a$，完整轨迹满足前缀恒等式

$$
\Phi(T_a s)(w)=\operatorname{tail}_a\bigl(\Phi(s)(aw)\bigr),
\tag{20.3}
$$

其中右端删除首个动作对应的标签；若采用终点读数版本，则相应地写成

$$
\Phi_{\mathrm{end}}(T_a s)(w)=\Phi_{\mathrm{end}}(s)(aw).
$$

由 (20.3)，$s\sim_{\mathrm{word}}t$ 会被每个 $T_a$ 保持。因此每个动作在商

$$
S_{\mathrm{word}}:=S_\bot/\!\sim_{\mathrm{word}}
$$

上都有唯一的前缀更新 $\overline T_a$，并且所有合法性、输出和记录都由商上的 profile 恢复。这个商不是“当前显示值相同”的商，而是对全部有限续接都不可区分的商。

仓内 `ControlledBehaviorUniversality.controlled_behavior_universal_property` 已对有限动作字母和完整有限词读出给出同一普适性：完整行为商的每个动作更新、当前读出和候选实现都唯一因子化，且在有限载体上得到基数上界。对具有共同幺半群协议的可达子系统，`ReachableBehaviorCore.reachable_behavior_core` 进一步给出可达性、未来分离和每个协议前缀的唯一商更新。

### 20.3 任意动态记忆都必须映到这个核

设 $r:S\to M$ 是一个实际记忆摘要。若它满足：

$$
\begin{aligned}
\Phi(s)(w)&=\psi_w(r(s))qquad &&(w\in A^*),\\
r(T_a s)&=\overline T_a(r(s))qquad &&(a\in A),
\end{aligned}
\tag{20.4}
$$

并且选择器、权限和失败标签也由 $r(s)$ 决定，那么

$$
r(s)=r(t)\Longrightarrow s\sim_{\mathrm{word}}t.
\tag{20.5}
$$

在实际记忆像 $r(S)$ 上存在唯一映射

$$
\theta:r(S)\to S_{\mathrm{word}},
\qquad
\theta(r(s))=[s].
\tag{20.6}
$$

若 $r$ 还分离所有不同的未来 profile，则 $\theta$ 为双射。故空间切面、时间动作词、边界状态和记忆摘要要互相恢复，不能只要求它们的当前读数相等；它们都必须在同一个实际像上双射到 (20.2) 的未来核。

这正是 `CausalStateFactorization.causal_state_factorization` 的过程化读法：预测律在摘要纤维上恒定时，摘要实际像唯一映到预测律像；`PredictionCompletionUniversality.prediction_completion_universality` 则把当前读出和更新的因子化提升为完整未来轨迹的因子化。两者结合得到 (20.6)，但一般动作词树版本是本节的数学组合，并非仓内已单独冻结的泛化定理。

### 20.4 当前读数相同仍可能没有后继

仓内 `EarliestFutureWitness.memory_is_earliest_future_witness` 的有限例可以直接写成：

$$
S=\operatorname{Fin}3,
\quad
F(0)=0,\quad F(1)=2,\quad F(2)=2,
\quad
q(s)=[s=2].
$$

当前有 $q(0)=q(1)=\mathsf{false}$，但

$$
q(F(0))=\mathsf{false}\ne\mathsf{true}=q(F(1)).
$$

所以 $q$ 的当前纤维不能承载后继；完整 profile 在一步处把两者分开。动作词树版本还会同时记录“哪一个动作在何时失败”，因而比只比较一条固定时间轨道更适合内部观察者。

### 20.5 有限词、无限词与实际来源

对词长不超过 $N$ 的任务，使用

$$
s\sim_N t
\iff
\forall w\in A^*,\ |w|\le N\Rightarrow
\Phi(s)(w)=\Phi(t)(w).
$$

有

$$
\sim_{N+1}\subseteq\sim_N,
\qquad
\sim_{\mathrm{word}}=\bigcap_N\sim_N.
\tag{20.7}
$$

在有限状态且全动作更新已固定时，`FiniteFutureCongruence.infinite_relation_stabilizes` 说明某个有限深度达到最大分离深度后，有限商就等于无限未来商；没有该稳定条件时，所有有限层相容不等于一个固定有限边界足够。对阶段化或逆极限系统，还要保留第 17 节的实际来源像闭合与更新提升条件：形式上存在的 profile 线程可能不来自任何共同配置。

### 20.6 四种表达的最终收束

在这个动作词树模型中，四种通常分开的词只承担不同角色：

* **空间**是可达配置及其接口的局部载体 $S$；
* **时间**是动作词的前缀序和记录顺序；实际钟读数是 $\widehat L$ 中的一类标签；
* **边界**是未来核商 $S_{\mathrm{word}}$ 或其指定任务的有限 horizon 商；
* **记忆**是一个实际像 $r(S)$，以及它到未来核的因子化映射。

在指定任务下，它们互相恢复的充分结构可收束为

$$
\boxed{
\begin{gathered}
\text{固定共同来源与总化失败的动作词树},\\
\text{完整 profile 对所有允许词包含读数、权限和记录},\\
\text{未来核对每个动作前缀闭合并给出唯一商更新},\\
\text{每个表示在实际像上因子化并对未来 profile 分离},\\
\text{阶段极限的实际来源像与更新闭合}.
\end{gathered}}
\tag{20.8}
$$

这组条件比预设一个外部时空坐标更小：只需一个带标签的关系过程及其未来行为核；空间、时间、边界和记忆是同一过程的不同投影。它也保留了递归性：把一个商类的内部协议再展开成动作词树，重复 (20.1)—(20.6)，无需另造系统外观察者。本节没有新增 Lean 声明。

## 20.99 追加锚

## 21. 词作用商：协议顺序本身也是关系

第 20 节把动作词作为未来测试的索引；还可以把动作词本身当作一个可压缩对象。设 $A^*$ 是由动作字母生成的自由幺半群，并固定以下运行约定：词 $uv$ 表示先执行 $u$，再执行 $v$。写

$$
\rho(\varepsilon,s)=s,
\qquad
\rho(ua,s)=T_a(\rho(u,s)).
\tag{21.1}
$$

于是

$$
\rho(uv,s)=\rho(v,\rho(u,s)).
\tag{21.2}
$$

这条约定必须始终保留；若改用左作用，所有乘法次序都要同时反转。动作词不是无序的计数向量。

### 21.1 协议词的有效商

定义两个词在当前状态载体上作用相同为

$$
u\equiv_{\mathrm{act}}v
\iff
\forall s\in S,\quad \rho(u,s)=\rho(v,s).
\tag{21.3}
$$

它是一个双侧同余：若 $u\equiv_{\mathrm{act}}v$，则对任意前缀 $x$ 与后缀 $y$，都有

$$
xuy\equiv_{\mathrm{act}}xvy.
\tag{21.4}
$$

因此 $A^*/\!\equiv_{\mathrm{act}}$ 仍是一个幺半群，并且它在 $S$ 上的诱导作用是 faithful 的；作用不同的词类必在某个状态上留下差别。仓内冻结声明 `EffectiveProtocolActionMonoid.effective_protocol_action_monoid` 正好给出 (21.3)—(21.4) 的两侧同余和忠实商。

状态侧的完整控制 profile 则为

$$
\Gamma(s)(u)=\widehat q(\rho(u,s)),
\qquad u\in A^*,
\tag{21.5}
$$

其中 $\widehat q$ 已包含合法性、读数、失败和记录。由 (21.2)，对任意前缀动作，后续 profile 在商上唯一运输。`ControlQuotientUniversalMinimality.control_quotient_universal_minimality` 把这个商的核识别为动态闭包，并证明当前读出、每个动作后继和每个动作结果都可从中恢复；`BehaviorUpdateWordAction.behavior_update_well_defined` 则在实际行为像上给出词的空词、拼接和运行运输。

### 21.2 深度一的商仍可能丢掉词关系

考虑动作 $a,b$ 和状态

$$
S=\{s,t,u,v,r_0,r_1\},
$$

令 $q(r_1)=1$，其余状态读数为 $0$，并规定

$$
a(s)=u,\quad a(t)=v,\quad b(s)=b(t)=r_0,
\qquad b(u)=r_0,\quad b(v)=r_1.
$$

则 $s,t$ 的当前读数相同，执行单步 $a$ 或单步 $b$ 后的读数也相同；但是按 (21.1) 先执行 $a$ 再执行 $b$ 时

$$
q\bigl(\rho(ab,s)\bigr)=0,
\qquad
q\bigl(\rho(ab,t)\bigr)=1.
\tag{21.6}
$$

所以深度不超过一的边界不能代替完整词 profile。这个例子说明“当前读数加每个单步读数”仍不等于全部关系；未来区分可能只在一个组合词上出现。

### 21.3 不可默认把时间协议交换化

只有在

$$
T_a\circ T_b=T_b\circ T_a
\tag{21.7}
$$

对所有动作对成立时，才可以把词作用化成按字母计数的正规形，并把协议“时间”压成两个迭代次数。仓内 `CommutingCompletionExchange.commuting_completion_exchange` 在明确交换假设下给出两种完成顺序的相同核；对应的 `commutativity_hypothesis_is_necessary` 给出四状态反例：两个更新不交换时，两种完成顺序的行为核不同。

因此，在没有 (21.7) 时，$ab$ 与 $ba$ 是不同的协议，即使它们使用了同一组动作、总步数相同，也不能互换。把词改写成计数会删除观察者可以取得的顺序关系，随后得到的边界可能无法继续执行原过程。

### 21.4 词商与四种表达的最终关系

在指定动作字母、失败标签和共同来源后，最小的递归对象可以写成

$$
\boxed{
\bigl(S,\ A^*\curvearrowright S,\ \widehat q,\ \Gamma\bigr),
}
\tag{21.8}
$$

其中 $A^*$ 的作用保留协议顺序，$\Gamma$ 保留对全部有限词的关系响应。空间是 $S$ 的可达局部载体，时间是词的前缀序，边界是 $\ker\Gamma$ 的商，记忆是实际像上的一个因子化实现。四者互相恢复要求：

$$
\ker(r)=\ker(\Gamma)
$$

（或至少在实际像上诱导双射），动作词商满足两侧同余，失败与权限标签没有被删去，并且逆极限阶段的实际共同来源像对词更新闭合。若只满足当前读数或固定深度轨迹相等，最多得到一个有限任务视图，不能称为整个递归过程的恢复。

本节把第 18 节的联合协议域和第 20 节的合法动作词树连接成一个有序协议作用商；一般的状态—协议双侧普适性仍是普通数学组合，未新增 Lean 声明。

## 21.99 追加锚

## 22. 观察者塔与完成化幂等性

前面已经把一个固定任务的边界写成未来响应商。现在把观察者的逐层细化写成一座塔。设 $q_0:S\to B_0$ 是当前可用的表示，$\mathcal T$ 是已经声明的目标、动作、失败和记录标签的任务族，记

$$
C_{\mathcal T}(q)(s)=\Gamma_{\mathcal T,q}(s)
$$

为把状态送到全部合法未来响应的完成化。这里的响应仍然只在实际可达配置上取值；它不是把形式上任意的函数或逆极限线程免费加入系统。

下文 $q\preceq r$ 表示 $q$ 从 $r$ 因子化，即存在映射 $h$ 使 $q=h\circ r$；方向与仓内 `Refines q r` 相同。式中的 $C_{\mathcal T}$ 先按确定性对象层的响应特例书写；若任务保留概率、失败、权限或记录标签，就必须把相应联合 profile 纳入 $\Gamma_{\mathcal T,q}$，不能由对象层记号自动推出完整过程结论。

### 22.1 固定任务下的观察者塔

**theorem 22.1: 固定任务下的观察者塔；Claim status: open.** 固定 $\mathcal T$ 时，定义

$$
B_0=S,\qquad q_{n+1}=C_{\mathcal T}(q_n).
\tag{22.1}
$$

每一层都保留前一层的读出，因为

$$
q_n\preceq C_{\mathcal T}(q_n).
\tag{22.2}
$$

若 $q_n\preceq r_n$，则同一任务下的完成化也保持这个细化顺序：

$$
C_{\mathcal T}(q_n)\preceq C_{\mathcal T}(r_n).
\tag{22.3}
$$

完成后的状态已经记录了同一任务的全部未来响应，所以再次完成只改变载体的编码方式：

$$
C_{\mathcal T}(C_{\mathcal T}(q))\simeq C_{\mathcal T}(q).
\tag{22.4}
$$

仓内 `PredictionCompletionIdempotence.prediction_completion_idempotent` 与 `CanonicalCompletionIdempotence.canonical_completion_idempotence` 给出相应的固定任务幂等性；`BehaviorCompletionFunctoriality.behavior_completion_is_functorial` 和 `BehaviorCompletionUniqueStability.behavior_completion_has_unique_induced_update` 说明运输、更新和唯一诱导在该等价下相容。因此，从第一个已经完备的层起，塔只发生规范等价，不再产生新的同一任务响应。

这里的“稳定”是相对于 $(\mathcal T,\text{更新},\text{读出})$ 的稳定。它不表示这个载体已经能够回答尚未加入任务族的所有问题。

### 22.2 新任务如何重新打开边界

**theorem 22.2: 新任务如何重新打开边界；Claim status: open.** 设下一阶段加入一个新目标 $T':S\to Y'$，而旧边界是 $q$。旧纤维中仍能被新目标区分的成对配置组成

$$
\operatorname{Esc}_{T'}(q)
 =
 \{(s,t):q(s)=q(t)\ \land\ T'(s)\ne T'(t)\}.
\tag{22.5}
$$

若这个集合非空，$T'$ 就不在旧摘要上因子化；加入它的目标完成化会严格切开旧纤维。反之，若 $T'=g\circ q$，则旧边界已经足以恢复这个目标，加入 $T'$ 不会造成新的区分。仓内 `TargetClosureOperator.target_closure_equivalent_iff_target_sufficient` 正好把这一因子化条件与目标完成的固定点联系起来；`target_closure_three_laws` 则给出扩张、单调和同一目标下的幂等（按 `ConceptEquivalent` 计）。

一个最小例子是 $S=\mathrm{Bool}$，旧读出 $q_0:S\to\{*\}$ 为常值，更新为恒等。对旧任务，未来完成仍只有一个状态类，再次完成稳定。若新任务取 $T'=\mathrm{id}_{\mathrm{Bool}}$，则

$$
\operatorname{targetClosure}(q_0,T')(x)=(*,x)
$$

把两个旧配置分开；第二次加入同一个 $T'$ 只给出规范等价的重复坐标。这说明“完成化幂等”不能被误读为“对所有未来任务一次完成就永远足够”。

### 22.3 最大不变核与有限层稳定

**theorem 22.3: 最大不变核与有限层稳定；Claim status: open.** 对确定更新 $F:S\to S$ 和当前读出 $q$，完整未来商的核是当前观察核中最大的前向不变关系：它既包含在 $\ker q$ 中，又满足

$$
(s,t)\sim\Longrightarrow(Fs,Ft)\sim,
$$

并且任何同时具有这两项性质的关系都包含在它里面。仓内 `CompletionKernelGreatestFixedPoint.completion_kernel_is_greatest_fixed_point` 给出这一最大不变核表述。因而有限 horizon 商的稳定，只能在已有的有限分离深度、有限状态或其他明确条件下推出；没有这些条件，

$$
\bigcap_N\ker\Gamma_{\mathcal T,\le N}
$$

仍可能严格小于任何一个有限层核。

即使所有有限层都彼此相容，也还要检查逆极限线程是否来自同一个实际配置，以及更新是否在实际来源像上闭合。第 17 节的实际来源像条件不能由形式上的逆极限存在自动替代。

### 22.4 动态完成、状态忠实与自描述是不同性质

**theorem 22.4: 动态完成、状态忠实与自描述是不同性质；Claim status: open.** 完成后的动态下降、状态读出忠实、表示映射满射，以及同类型的自描述闭合，必须分开记录。它们分别回答：更新能否在摘要上定义、不同状态是否仍可被读出区分、载体是否覆盖目标对象、以及所有同类型自映射是否都能在对象内部编码。

布尔例子已经足以分开这些性质：恒等读出可以状态忠实，恒等或取反更新也可以下降，但 $\mathrm{Bool}$ 不能在同类型内满射地编码全部布尔自映射；相反，常值读出可以有动态下降，却不是状态忠实。仓内 `DiagonalEscapeNeedsTypeExtension` 的 `state_faithfulness_not_self_description_closure`、`effective_descent_not_self_description_closure` 与 `ClosureNonimplicationTriple.closure_nonimplication_triple` 提供了这些非蕴含的具体支点。

因此，完成化塔在固定任务上达到幂等，不等于存在一个同类型的终端自描述观察者。若把“观察者能够描述所有同类型观察者”也加入任务，旧载体上会出现新的对角逃逸；`ProObjects.NoTerminalSelfDescription.no_terminal_self_description` 说明即使形式上有终端阶段表示，扭曲的自评价仍能逃出该阶段的枚举像。

### 22.5 塔、完成与全局恢复的边界

**theorem 22.5: 塔、完成与全局恢复的边界；Claim status: open.** 观察者塔可以在固定任务下稳定，而全局恢复仍需另外的共同来源条件。一个稳定的形式塔只说明每层的响应商已对声明任务闭合；它不证明：

* 新任务加入后旧纤维仍然充分；
* 每个相容的无限线程都来自一个实际状态；
* 完成后的载体对所有自身操作都能做同类型编码；
* 数学上定义的边界能在固定资源和实际接口下被取得。

所以更准确的收束是：

$$
\boxed{
\begin{aligned}
\text{固定任务完成化}&\Rightarrow\text{同任务响应的规范稳定};\\
\text{任务扩大且旧纤维不因子化}&\Rightarrow\text{边界重新细化};\\
\text{逆极限相容}&\not\Rightarrow\text{实际共同来源};\\
\text{动态下降或状态忠实}&\not\Rightarrow\text{同类型终端自描述}.
\end{aligned}}
\tag{22.6}
$$

这使“无穷观察”获得一个可检验的含义：不是寻找一张容纳所有任务的最大坐标图，而是研究任务族扩张时哪些边界纤维必须继续被切开，以及哪些运输和来源条件能让各层仍然来自同一个关系整体。任务增长下是否总会在某个有限阶段稳定，仍取决于任务族、状态载体和资源条件，不能由固定任务的幂等性推出。

本节只组织既有过程、完成化、目标闭包和对角逃逸结果的关系，没有新增 Lean 声明；正文中的“稳定”“严格细化”和“实际来源”均受各自明示条件限制。

## 22.99 追加锚

## 23. 对第 19.1 节同步未来核下降断言的更正

### 23.1 同步未来核不必保持单轴更新

**命题 23.1（式（19.3）的状态轴反例）。** 式（19.1）、（19.2）所定义的关系仍是等价关系，但在任意状态更新和协议推进下，式（19.3）的状态轴蕴含不成立；相应的状态商不必有与原更新交换的诱导更新。

**证明。** 取 $S=\{a,b,c\}$、$P=\{0,1\}$、$\widehat L=\{0,1\}$，定义

$$
F(a)=a,\qquad F(b)=F(c)=c,\qquad \sigma(0)=\sigma(1)=0,
$$

并令评价表为

$$
\begin{array}{c|cc}
E&0&1\\\hline
a&0&0\\
b&0&0\\
c&0&1
\end{array}.
$$

当 $n=0$ 时，$a,b$ 两行相同。当 $n\ge1$ 时，对每个 $p\in P$ 都有 $\sigma^{[n]}(p)=0$，因而对任意状态 $s$ 都有

$$
E(F^{[n]}(s),\sigma^{[n]}(p))=E(F^{[n]}(s),0)=0.
$$

所以 $a\approx_S b$，这里的量词覆盖所有 $n\in\mathbb N$。但取 $n=0,p=1$，得到

$$
E(F(a),1)=0\ne1=E(F(b),1),
$$

故 $F(a)\not\approx_S F(b)$。若存在 $\bar F:S/\!\approx_S\to S/\!\approx_S$ 满足 $\bar F([s])=[F(s)]$，则由 $[a]=[b]$ 推出 $[F(a)]=[F(b)]$，与上述不等价矛盾。等价关系本身由逐项读数相等的自反、对称、传递性得到，并不需要更新下降。$\square$

### 23.2 协议轴的对称反例

**命题 23.2（式（19.3）的协议轴反例）。** 式（19.3）的协议轴蕴含也不在原假设下成立。

**证明。** 对命题 23.1 的系统转置两轴：令 $S'=P$、$P'=S$、$F'=\sigma$、$\sigma'=F$，并定义 $E'(p,s)=E(s,p)$。于是 $E'((F')^{[n]}p,(\sigma')^{[n]}s)=E(F^{[n]}s,\sigma^{[n]}p)$。命题 23.1 中的状态等价恰好变成此系统的协议等价，因此 $a\approx_{P'}b$ 而 $\sigma'(a)\not\approx_{P'}\sigma'(b)$。同样不存在相容的协议商更新。$\square$

### 23.3 协议满射足以恢复状态轴下降

**命题 23.3。** 保留式（19.1）、（19.2）的定义。若 $\sigma:P\to P$ 满射，则

$$
s\approx_S t\Longrightarrow F(s)\approx_S F(t).
$$

**证明。** 固定 $n\in\mathbb N$ 和 $p\in P$。取 $q\in P$ 使 $\sigma(q)=p$。在 $s\approx_S t$ 中代入时域 $n+1$ 和协议 $q$，并使用迭代恒等式，得到

$$
\begin{aligned}
E(F^{[n]}(F(s)),\sigma^{[n]}(p))
&=E(F^{[n+1]}(s),\sigma^{[n+1]}(q))\\
&=E(F^{[n+1]}(t),\sigma^{[n+1]}(q))\\
&=E(F^{[n]}(F(t)),\sigma^{[n]}(p)).
\end{aligned}
$$

对所有 $n,p$ 成立，故结论成立。于是 $\bar F([s])=[F(s)]$ 与代表元无关，并由商投影满射而唯一。$\square$

### 23.4 状态满射足以恢复协议轴下降

**命题 23.4。** 保留式（19.1）、（19.2）的定义。若 $F:S\to S$ 满射，则

$$
p\approx_P q\Longrightarrow\sigma(p)\approx_P\sigma(q).
$$

**证明。** 固定 $n\in\mathbb N$ 和 $s\in S$，取 $t$ 使 $F(t)=s$。在 $p\approx_P q$ 中代入 $n+1,t$，得到

$$
E(F^{[n]}(s),\sigma^{[n]}(\sigma(p)))
=E(F^{[n+1]}(t),\sigma^{[n+1]}(p))
=E(F^{[n+1]}(t),\sigma^{[n+1]}(q))
=E(F^{[n]}(s),\sigma^{[n]}(\sigma(q))).
$$

故协议轴下降，且 $\bar\sigma([p])=[\sigma(p)]$ 唯一。$\square$

### 23.5 独立迭代时域的替代定义

**定义 23.5。** 对同一 $S,P,\widehat L,E,F,\sigma$，定义两个独立时域的核：

$$
\begin{aligned}
s\equiv_S t&\iff\forall m,n\in\mathbb N\ \forall p\in P,\quad
E(F^{[m]}s,\sigma^{[n]}p)=E(F^{[m]}t,\sigma^{[n]}p),\\
p\equiv_P q&\iff\forall m,n\in\mathbb N\ \forall s\in S,\quad
E(F^{[m]}s,\sigma^{[n]}p)=E(F^{[m]}s,\sigma^{[n]}q).
\end{aligned}
$$

**命题 23.6。** 无须满射假设，$\equiv_S$ 被 $F$ 保持，$\equiv_P$ 被 $\sigma$ 保持，故两者分别给出唯一诱导商更新。

**证明。** 状态轴在定义中把 $m$ 换成 $m+1$，协议轴把 $n$ 换成 $n+1$，各用迭代恒等式即可。代表元无关性和唯一性同命题 23.3、23.4。$\square$

**命题 23.7（更正的适用范围）。** 命题 23.3、23.4 是式（19.3）的附加充分条件，不是原定义的隐含假设，也不主张它们必要。定义 23.5 是替代定义，不把它与式（19.2）等同。第 19.3 节式（19.5）关于充分摘要核包含的条件结论，以及第 19.5 节显式要求下降和选择器因子化的条件表述，不依赖式（19.3）的无条件版本。

**证明。** 两个独立时域取 $m=n$ 即蕴含同步时域的相等；命题 23.1 的 $a,b$ 同步等价，而 $m=1,n=0,p=1$ 区分它们，故二者一般不等同。若摘要 $q_S$ 确能决定全部未来读数，则同一摘要给出同一未来读数，直接得到式（19.5）。第 19.5 节中的下降条件必须单独履行；命题 23.1、23.2 排除了从式（19.2）无条件推出它。固定读出、单侧状态迭代的未来核以及对全部动作词闭合的未来核具有各自的移位恒等式，不被上述反例否定。第 19.4 节引用的相邻深度稳定判据在其固定读出迭代的假设内成立；应用于另一类同步读数时，仍须核对相应递推闭合条件。$\square$

## 23.99 追加锚

## 24. 有限稳定深度与双侧最小边界

第 22 节说明固定任务的完成化何时达到同任务稳定，但还没有给出一个有限系统中可以直接计算的停止深度，也没有把这个深度和实际记忆容量连起来。本节在有限确定性模型中补上这两个接口。设 $X$ 是有限状态载体，$F:X\to X$ 是更新，$q:X\to Q$ 是当前读出。对 $n\in\mathbb N$，令

$$
x\equiv_n y
\iff
\forall 0\le k\le n,\quad q(F^k x)=q(F^k y),
$$

并令 $\equiv_\infty$ 要求所有有限 $k$ 都相等。这里的等价关系只记录声明的读出和更新；若任务还保存失败、权限、费用或事件记录，就把它们先打包进 $q$ 或扩充成联合读出。

### 24.1 稳定深度是完整动态边界的有限证书

**theorem 24.1: 有限稳定深度达到完整未来商；Claim status: open.** 设 $X$ 为有限类型，$m$ 是最小满足相邻稳定

$$
\equiv_m=\equiv_{m+1}
$$

的深度。则

$$
\boxed{
\equiv_m=\equiv_{m+1}=\equiv_\infty
}
$$

而且对任何 $n$，若 $\equiv_n=\equiv_{n+1}$，则 $m\le n$。因此，在有限状态模型里，第一次相邻稳定不是一次经验截断，而是已经足以恢复全部未来读出律的动态边界。

仓内 `FiniteStabilityClassBound.finite_stability_class_bound` 给出这三个等式与最小性，并给出数量界。写 $C_\infty=X/{\equiv_\infty}$，写 $C_0=X/{\ker q}$，则

$$
\boxed{
m\le |C_\infty|-|C_0|
\le |X|-|\operatorname{ran}q|.
}
\tag{24.1}
$$

右侧不是把状态数当作信息量，而是把每次未来区分可能新增的等价类数作为一个有限预算。若 $q$ 已经是动态充分的，$m=0$；若初始读出把不同未来合并，深度只能在新的等价类出现时增加。

**证明状态。** 这是既有有限未来关系稳定、类数增长和 `Setoid.quotientKerEquivRange` 的组合；本节没有新增 Lean 声明，也不把式（24.1）外推到无限状态或近似读出。

### 24.2 从动态边界到任意精确记忆的唯一因子

**theorem 24.2: 精确有限记忆必须承载完整未来商；Claim status: open.** 设 $r:X\to W$ 是一个有限确定性记忆实现，存在 $G:W\to W$、$q_W:W\to Q$ 使

$$
r\circ F=G\circ r,
\qquad
q=q_W\circ r,
$$

并且 $r$ 满射。则存在唯一满射

$$
\theta:W\twoheadrightarrow C_\infty
$$

满足

$$
\theta\circ r=\pi_\infty,
\qquad
\theta\circ G=\bar F\circ\theta,
\qquad
\bar q\circ\theta=q_W,
$$

其中 $\pi_\infty:X\to C_\infty$ 是完整未来商，$\bar F$ 与 $\bar q$ 是其诱导更新和读出。因此

$$
\boxed{|C_\infty|\le |W|.}
\tag{24.2}
$$

仓内 `DeterministicCompletionMinimality.minimal_deterministic_completion` 正是这一唯一满射因子和三条交换式的有限版本。它的含义是：任意精确记忆都至少包含完整未来行为类；当前显示 $q$ 只有在 $C_0\cong C_\infty$ 时才已经是最小动态记忆。

这也说明“现在的目标后验”通常不是充分边界。它可能把两个状态合成同一当前读数，但两者的下一步更新落在不同未来类中；若要定义单值的记忆更新，必须保留能区分这些残余的结构。

### 24.3 达到界的三状态反例

取

$$
X=\{a,b,c\},
\qquad
q(a)=q(b)=0,\quad q(c)=1,
$$

并令

$$
F(a)=a,\qquad F(b)=c,\qquad F(c)=c.
$$

初始读出把 $a,b$ 合并，所以 $|C_0|=2$。一步之后，$a$ 的读出轨迹为 $0,0,0,\ldots$，$b$ 的轨迹为 $0,1,1,\ldots$，故

$$
|C_\infty|=3,
\qquad m=1,
\qquad |C_\infty|-|C_0|=1.
$$

这使式（24.1）的第一项界达到等号。只保留 $q$ 还不能定义后继：同一摘要类中，$F(a)=a$ 仍在该类，而 $F(b)=c$ 离开该类。身份记忆 $r=\operatorname{id}_X$ 达到式（24.2）的下界；任何精确确定性记忆都至少需要三个状态。

### 24.4 双侧评价的最小边界

动态边界还必须支持“状态怎样被协议读取”。令

$$
E:X\times P\to L
$$

把合法性、读数、记录、费用和终止标签打包到同一个结果值中。定义状态行与协议列

$$
R_x(p)=E(x,p),
\qquad
C_p(x)=E(x,p),
$$

并令 $x\sim_S y$ 当且仅当 $R_x=R_y$，令 $p\sim_P q$ 当且仅当 $C_p=C_q$。则评价可下降为

$$
\bar E:(X/{\sim_S})\times(P/{\sim_P})\to L,
\qquad
\bar E([x],[p])=E(x,p).
\tag{24.3}
$$

**theorem 24.3: 双侧商的普适最小性；Claim status: open.** 式（24.3）良定义，并且两个商都分别具有分离性：不同状态类可由某个协议区分，不同协议类可由某个状态区分。若另有满射 $f:X\to X'$、$g:P\to P'$ 和

$$
E(x,p)=E'(f(x),g(p)),
$$

且 $E'$ 的状态行与协议列都分离，那么存在唯一的等价

$$
X/{\sim_S}\simeq X',
\qquad
P/{\sim_P}\simeq P'
$$

保持代表元与评价。仓内 `RowColumnObserverCore.row_column_observer_core`、`DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` 给出相应的商下降和唯一双侧等价；`StateProtocolQuotientOrderCommutation.state_protocol_quotient_order_commutes` 说明先约化状态或先约化协议只改变规范表示，不改变联合评价。

这里的满射条件排除“把从未由共同来源实现的值”误当作观察者状态，外延条件排除“目标内部仍有不可区分副本”。所以空间切面、时间读数和记忆摘要要互相恢复，至少需要同一实际像、状态运输、协议回拉和评价保持；一张数值坐标图或单边边界函数本身不够。

若更新还要运输协议，必须另给 $T:X\to X$ 与 $G:P'\to P$，并证明

$$
E'(T x,p')=E(x,Gp').
\tag{24.4}
$$

式（24.4）才使 $T$ 和 $G$ 在两个商上诱导同一动态评价。没有协议回拉，只能说状态被重标；不能说后续实验被保留。

本节把有限稳定深度、动态记忆下界和双侧协议商接成一条链：

$$
\boxed{
\text{首次有限稳定}
\Rightarrow
\text{完整未来边界}
\Rightarrow
\text{任意精确记忆的唯一因子}
\Rightarrow
\text{双侧评价的最小恢复载体}.
}
$$

它仍是有限、确定性、任务相对的数学结论；不声称所有物理观察、无限状态或未知概率模型都具有同样的有限界。

## 24.99 追加锚

## 25. 有限时间投影与空间边界的共同恢复

前面的双侧评价给出了抽象的状态—协议商，但还需要一个可以落到过程档案上的空间—时间接口。本节把有限未来读出、当前空间投影和隐藏档案放在同一个联合边界中。它只讨论有限档案与声明的实验族；不把有限投影外推为物理时空的完整坐标。

### 25.1 有限时间投影是逐层增加的边界

设 $X$ 是实际共同来源的状态像，$F:X\to X$ 是合法更新，$r:X\to R$ 是指定的记录读出。对 $N\in\mathbb N$ 定义有限时间投影

$$
\operatorname{TP}_N(x)(k)=r(F^k x),\qquad 0\le k\le N.
$$

若 $\pi_{\rm sp}:X\to S$ 是当前空间或端口投影，则联合边界为

$$
\boxed{
Q_N(x)=\bigl(\pi_{\rm sp}(x),\operatorname{TP}_N(x)\bigr).
}
\tag{25.1}
$$

这里的“时间”只是沿合法更新取得的一列记录；若任务还需要失败、权限或 inactive archive event，就必须把相应读出并入 $r$ 或扩充 $Q_N$。

仓内 `PredictionExpansionEscape.prediction_escape_iff_expansion_escape`、`TimeExpansionEscape.time_expansion_escape_iff_expansion_escape` 和 `FiniteTimeProjectionRestrictionLaws.finite_time_projection_expansion_and_restriction_laws` 给出有限投影的逐项刻画与限制律；`FiniteTimeProjectionKernelAntitone.finite_time_projection_kernel_antitone` 给出

$$
N\le M\Longrightarrow
\ker(\operatorname{TP}_M)\subseteq\ker(\operatorname{TP}_N).
\tag{25.2}
$$

因此 $N$ 增大只会切开原来合并的未来，不会把已经区分的有限记录重新合并。若存在 $x,y$ 使得 $\operatorname{TP}_N(x)=\operatorname{TP}_N(y)$ 而 $\operatorname{TP}_M(x)\ne\operatorname{TP}_M(y)$，这正是有限时间分辨率下的 expansion escape；它表示当前边界还没有承载足够的未来关系，而不是表示某个外部观察者看见了一个额外对象。

### 25.2 目标恢复的纤维条件

**proposition 25.1: 有限联合边界的目标充分性；Claim status: open.** 设 $T:X\to Y$ 是要由该接口回答的目标。存在唯一的实际像映射

$$
D_N:\operatorname{im}(Q_N)\to\operatorname{im}(T),
\qquad T=D_N\circ Q_N,
\tag{25.3}
$$

当且仅当

$$
Q_N(x)=Q_N(y)\Longrightarrow T(x)=T(y).
\tag{25.4}
$$

这就是“先取空间与有限时间边界，再恢复目标”的准确判据。它只要求目标在 $Q_N$ 的纤维上恒定；不要求 $Q_N$ 反演完整状态。`UniversalSufficiencyFactorization.universal_sufficiency_factorization` 提供相应的有限像因子化支点，`causal_state_factorization` 则说明在实际像上因子是唯一的。

若要说空间摘要与完整时间摘要互相恢复，必须在实际像上同时有两个方向的因子化，等价地满足

$$
\ker(\pi_{\rm sp})=\ker(\operatorname{TP}_\infty).
\tag{25.5}
$$

相同的值域大小、相同的当前读数，或存在一个单向编码，都不足以推出式（25.5）。若只需恢复某一项时间合法性 $L_y(x)$，要求可以弱化为 $L_y$ 在 $\pi_{\rm sp}$ 的纤维上恒定；但这是针对一个指定测试的充分性，不是对全部未来协议的充分性。

### 25.3 隐藏档案反例：当前空间投影不能自动恢复时间域

**theorem 25.2: 当前空间投影对隐藏档案时间域不充分；Claim status: open.** 在 `HiddenArchiveTemporalDomain.hidden_archive_preserves_current_changes_temporal_domain` 的有限构造中，$U$ 与 $U_{\rm old}$ 具有相同的 current/selected 数据和空间投影：

$$
\pi_{\rm sp}(U)=\pi_{\rm sp}(U_{\rm old})=(0,\delta_0).
\tag{25.6}
$$

但 $U_{\rm old}$ 还含有一个 inactive archived event $e$，满足

$$
\tau(e)=2,\qquad \operatorname{position}(e)=0.
$$

令 $Y=\operatorname{shiftRich}(U,1)$，使右侧事件 $f$ 的时间为 $1$。则已有构造精确给出

$$
\operatorname{Guard}(U,Y),
\qquad
\neg\operatorname{Guard}(U_{\rm old},Y),
\tag{25.7}
$$

因为在后一份档案中需要检查 $\tau(e)<\tau(f)$，即 $2<1$，该条件失败。于是存在同一空间纤维中的两个实际状态，它们对同一个后续时间接续给出不同合法性；式（25.4）对目标 $T=\operatorname{Guard}(-,Y)$ 失败。

这个反例不说明空间投影没有用，而说明它没有截住所有仍影响联合实现的关系。要恢复该时间域，边界至少要保留 inactive archive 的时间资料，或保留一个对所有声明时间协议充分的未来行为摘要。把 archived event 当作“当前不显示所以不存在”，正是把必要的联合约束从边界删掉。

### 25.4 相对时间的恢复与绝对原点的缺失

在 `TemporalComposition` 与 `ProductPaths` 的有限实例中，带标签因果边、严格时间坐标和父节点接口可以共同恢复局部空间—时间结构：`temporal_guard_iff`、`edge_time`、`path_time` 及其 path 分解分别把合法接续、边时间和路径时间联系起来。单独的时间数值不能恢复因果边，单独的当前空间读数也不能恢复全部时间合法性。

另一方面，`shift_attributes`、`shift_causal`、`q_shift` 和 `background_shift` 表明统一平移保持因果关系与指定当前读出；`guard_of_large_shift` 与 `exists_shift` 表明足够大的平移可以建立相对顺序。因此在没有外部原点或参考时钟的模型中，接口至多恢复

$$
\tau(y)-\tau(x)
$$

这类相对量，不能从不变的联合读出中恢复一个绝对时间零点。若任务需要绝对原点，必须把校准事件、参考记录或边界条件作为额外接口输入。

本节把空间—时间恢复收束为一条可检验链：

$$
\boxed{
\text{有限时间投影}
\longrightarrow
\text{联合边界 }Q_N
\longrightarrow
\text{目标纤维恒定}
\longrightarrow
\text{指定时间域可恢复}.
}
$$

所有“充分”“互相恢复”和“相对时间”都限定在声明的实际像与协议族上；本节没有新增 Lean 声明，正文推导的 claim status 保持 open。

### 25.5 追加勘误：实际像类型、联合纤维与时间平移条件

**proposition 25.3: 实际像因子化的准确类型；Claim status: open.** 式（25.3）中的 $Q_N,T$ 若仍取原名义陪域，应先取实际像映射
\[
\widehat Q_N:X\to\operatorname{im}(Q_N),\qquad
\widehat T:X\to\operatorname{im}(T).
\]
准确的交换式是
\[
\widehat T=D_N\circ\widehat Q_N.
\tag{25.8}
\]
其存在且唯一，当且仅当式（25.4）成立。存在性由纤维恒定使 $D_N(\widehat Q_N(x))=\widehat T(x)$ 无歧义，唯一性由 $\widehat Q_N$ 满射。空 $X$ 时两实际像皆空，取唯一空映射。`UniversalSufficiencyFactorization.universal_sufficiency_factorization` 的名义全域版本要求非空来源，用以给不可达坐标补值；`CausalStateFactorization.causal_state_factorization` 的实际像唯一性不要求把不可达坐标当作观察状态。本节只假设时间窗口有限，不假设状态像或观察像有限。

为免与第24节的有限性条件混淆，那里“有限状态”应理解为 $X$ 带有有限 `Fintype` 结构，而第24.2节的精确记忆实现还应明确 $W$ 带有有限 `Fintype` 结构；仅有有限时间窗口或有限值域读出，不能推出这两个载体有限。第24.4节的动态运输也应使用跨接口类型
\[
T:X\to X',\qquad G:P'\to P,
\]
并满足
\[
E'(Tx,p')=E(x,Gp').
\tag{25.8a}
\]
它首先给出评价保持；由此自动得到状态行 kernel preservation。协议列 kernel preservation 若要按相反方向使用，还需 $T$ 满射、源列由 $\operatorname{im}(T)$ 决定，或显式假设
\[
C_{p'}=C_{q'}\Longrightarrow C_{G p'}=C_{G q'}\quad\text{对所有 }x\in X.
\]
满足所需方向的这些条件后，才可在实际像上下降到相应商。只有再加满射、双射或明确的实际像双向条件，才可把下降后的映射称为等价或互相恢复。

**proposition 25.4: 隐藏档案反例只否定其实际合并的纤维；Claim status: open.** 第25.3节的既有 Lean 反例无条件否定的是
\[
\pi_{\rm sp}(x)=\pi_{\rm sp}(x')
\Longrightarrow
\bigl(\operatorname{Guard}(x,Y)\leftrightarrow\operatorname{Guard}(x',Y)\bigr).
\tag{25.9}
\]
它未指定 $F,r$，因而不能直接否定含有 $\operatorname{TP}_N$ 的式（25.4）。例如，若所声明读出本身已分离该合法性，联合边界可以在零窗口就区分两个档案；这种读出的实际可取得性仍须另证。

一个明确的联合边界反例可以取包含 $U,U_{\rm old}$ 的档案状态类、恒等更新 $F=\mathrm{id}$ 以及单点读出 $r\equiv *$。此时对全部 $N$，
\[
Q_N(U)=Q_N(U_{\rm old}),
\]
而式（25.7）的合法性仍不同。因此，增加同一个不分离读出的窗口长度不能补回隐藏档案差别。所需补充不必是全部不活动事件资料；准确要求只是新摘要切开仍被目标区分的纤维。`HiddenArchiveTemporalDomain.current_spatial_projection_domain_refutation` 承担式（25.9）的有限反驳，以上指定恒等更新的连接是普通数学推导。

**theorem 25.5: 联合未来边界的平移盲性条件；Claim status: open.** 设整数平移 $\sigma_k:X\to X$ 保持实际来源域，并满足
\[
\pi_{\rm sp}\sigma_k=\pi_{\rm sp},\qquad
r\sigma_k=r,\qquad
F\sigma_k=\sigma_kF.
\tag{25.10}
\]
对迭代次数归纳得 $F^j\sigma_k=\sigma_kF^j$，故对每个有限 $N$，
\[
Q_N\sigma_k=Q_N.
\tag{25.11}
\]
若绝对时间目标 $\Theta:X\to\mathbb Z$ 满足
\[
\Theta(\sigma_kx)=\Theta(x)+k
\]
且实际域中存在 $x,\sigma_kx$ 与 $k\ne0$，则 $\Theta$ 不能经 $Q_N$ 因子化：式（25.11）会迫使两目标值相同，与非零平移矛盾。

`TemporalComposition.shift_attributes`、`shift_causal`、`q_shift` 和 `background_shift` 供应其指定档案字段的平移性质，不自动供应任意 $r,F$ 的式（25.10）。`guard_of_large_shift` 与 `exists_shift` 只移动右档案，以取得一份新的合法接续，不是所有数据不变的同时平移。相对时间差虽在同时平移下不变，也不因此自动可由接口恢复；仍须逐个检查它在观察纤维上恒定。

最后，第25.4节的路径恢复只指所声明的拼接构造：`temporal_guard_iff` 刻画其时间合法性，`path_left_iff`、`path_right_iff` 和 `path_generated_iff` 刻画其来源路径；单独的 `edge_time`、`path_time` 不提供反向恢复。数学上定义的 $\operatorname{TP}_N$ 是指定未来响应表，只有实际执行并保留的记录才属于观察者当前档案。上述勘误保留式（25.1）、（25.2）、（25.4）与 HiddenArchive 的具体反例，并限定原式（25.3）及第25.3—25.4节的推论范围。

还需区分第24节的未来读出商与双侧评价商：$C_\infty=X/{\equiv_\infty}$ 只由 $F,q$ 生成，不会自动包含协议 $P$ 可能读取的隐藏字段。若要把它作为第24.4节的双侧边界，必须另加任务条件
\[
x\equiv_\infty y\Longrightarrow\forall p,\ E(x,p)=E(y,p),
\tag{25.12}
\]
其中合法性、记录和费用均已打包在 $E$ 中；若还要声称互相恢复，则需相反方向的分离条件，或直接证明评价行的 kernel 正好是 $\equiv_\infty$。相应地，$\bar F([x])=[F x]$ 与 $\bar q([x])=q(x)$ 的定义只在 $\equiv_\infty$ 对更新和读出稳定时良定义。缺少式（25.12）时，第24节的“完整未来边界”与双侧协议边界只能并列，不能自动串成同一商。

## 25.99 追加锚

### 25.6 再追加勘误：无限投影、共同载体与双侧链条件

式（25.5）中的无限时间投影需先定义为
\[
\operatorname{TP}_\infty(x)(k)=r(F^k x)\quad(k\in\mathbb N),
\]
或等价地约定 $\ker(\operatorname{TP}_\infty):=\bigcap_{N\in\mathbb N}\ker(\operatorname{TP}_N)$。前文只直接使用有限 $N$；不作此定义，$\ker(\operatorname{TP}_\infty)$ 不是已声明的对象。

HiddenArchive 的联合反例还应明确共同载体：取同一个状态类型 $X$，令 $U,U_{\rm old}\in X$，并令 $\pi_{\rm sp}:X\to S$ 满足 $\pi_{\rm sp}(U)=\pi_{\rm sp}(U_{\rm old})$；再指定 $F=\mathrm{id}_X$ 与 $r\equiv *$。这样才由定义得到对全部 $N$ 的 $Q_N(U)=Q_N(U_{\rm old})$。Lean 反例实际证明的是相应 image/Subtype.val（嵌入后的空间投影）相等及 Guard 的分歧；“current/selected 数据字面相同”不是额外的集合论前提。

第24.4节末尾的链式收束须带条件：
\[
\text{有限稳定}
\Longrightarrow
\text{完整未来商}
\Longrightarrow
\text{精确记忆因子}
\Longrightarrow
\text{双侧评价边界}
\]
只有在式（25.12）成立且评价行对 $\equiv_\infty$ 具有反向分离（等价地，行 kernel 正好是 $\equiv_\infty$）时才成立；否则最后一步只能作为条件分支，$C_\infty$ 与双侧协议商须分别保留。第24.4节的跨接口动态式亦应按第25.5节解释为 $T:X\to X'$、$G:P'\to P$；同接口写法只是特例。

此外，前述“$W$ 有限 `Fintype`”应读作 $W$ 具有 `Finite` 载体（需要枚举时可选择一个 `Fintype` 实例）。有限时间窗口或有限读出值域本身都不能推出 $W$ 有限；这一修正只限定第24.2节的有限记忆合同，不改变其因子化方向。

## 25.99 追加锚（再追加勘误）

## 26. 共同未来核与空间、时间、边界、记忆的四种表示

第25节的联合边界回答了一个给定目标是否能从空间投影和有限未来窗口恢复。本节把它推广为一个带类型的部分标记接续系统，并区分单个表示充分、多个表示联合充分以及动态更新可下降这三个不同命题。以下都限定在同一个实际共同来源；没有共同来源时，四个值域的相同或同构不能构成同一对象的恢复。

### 26.1 带类型的部分标记接续与完整未来 profile

令 $X$ 为实际状态像，$A$ 为合法操作类型，$L$ 为包含合法性、读数、记录、费用和失败原因的标签类型。一个确定性部分标记接续关系写成

$$
\mathcal R\subseteq X\times A\times L\times X.
$$

对固定 $x,a$，若存在 $(x,a,\ell,x')\in\mathcal R$，则操作 $a$ 合法、标签为 $\ell$ 并把状态推进到 $x'$；若不存在这样的元组，定义结果为一个带失败原因的标签。若系统允许多个后继，则把下述单值结果替换成带类型的结果集合或分布，核的定义不变。

对操作词 $w\in A^*$，递归得到完整响应

$$
\operatorname{Obs}_{\mathcal R,\varepsilon}(x)=\text{初始记录},
$$

$$
\operatorname{Obs}_{\mathcal R,wa}(x)
 =\text{把 }\operatorname{Obs}_{\mathcal R,w}(x)\text{ 的后继状态接入 }a\text{ 后得到的带标签响应}.
$$

这里的响应必须保留任务声明要求的失败、记录和费用；只留下后继工作态会把不同过程错误地合并。定义共同未来核

$$
\boxed{
 x\approx_{\mathcal R}y
 \iff
 \forall w\in A^*,\quad
 \operatorname{Obs}_{\mathcal R,w}(x)
 =\operatorname{Obs}_{\mathcal R,w}(y).
}
\tag{26.1}
$$

它是“面对所有允许的未来接续都不可区分”的关系版本。若 $x\approx_{\mathcal R}y$，则对任意首操作 $a$，两者要么具有相同的失败标签，要么具有相同的首标签且后继再次处于 $\approx_{\mathcal R}$ 中；否则把该后继词接在 $a$ 后面即可区分二者。因此，(26.1) 是可以继续沿操作词拼接的动态核，而不是只比较当前显示值的静态核。

仓内 `CongruenceKernel.congruence_kernel_laws`、`FiniteStableDepth.finite_state_has_stable_depth` 与 `FiniteHistoryPermanentStability.finite_history_relation_stable_forever` 分别提供核的接续律、有限状态下的稳定深度和稳定后永久保持的支点；本节只把它们组织到统一的带标签关系中，没有新增 Lean 声明。

### 26.2 四种表示何时各自完整

设空间、时间、边界和记忆表示分别为

$$
q_{\rm sp}:X\to Y_{\rm sp},\quad
q_{\rm tm}:X\to Y_{\rm tm},\quad
q_{\rm bd}:X\to Y_{\rm bd},\quad
q_{\rm mem}:X\to Y_{\rm mem},
$$

并令完整 profile 为

$$
\Phi_{\mathcal R}:X\to (A^*\to L),\qquad
\Phi_{\mathcal R}(x)(w)=\operatorname{Obs}_{\mathcal R,w}(x).
$$

所有映射都应先限制到实际像。对任意 $q:X\to Y$，以下三件事在实际像上等价：

1. 存在唯一双射 $d_q:\operatorname{im}(q)\to\operatorname{im}(\Phi_{\mathcal R})$，满足
   $$
   \widehat\Phi_{\mathcal R}=d_q\circ\widehat q,
   \qquad
   \widehat q=d_q^{-1}\circ\widehat\Phi_{\mathcal R};
   $$
2.
   $$
   \ker(q)=\ker(\Phi_{\mathcal R})=\approx_{\mathcal R};
   $$
3. $q$ 是该操作词任务的最小动态边界：它既能恢复所有声明的标签与合法性，又不把未来核中不同的状态合并。

证明只使用实际像因子化：$d_q(\widehat q(x)):=\widehat\Phi_{\mathcal R}(x)$ 由 kernel 相等而良定义，由两侧实际像映射的满射性得到双射与唯一性。`InterfaceKernelCriterion.interface_refinement_iff_kernel_inclusion`、`UniversalSufficiencyFactorization.universal_sufficiency_factorization` 和 `CausalStateFactorization.causal_state_factorization` 是这一判据的仓内支点。

因此，若四个表示都满足

$$
\boxed{
\ker(q_{\rm sp})
=\ker(q_{\rm tm})
=\ker(q_{\rm bd})
=\ker(q_{\rm mem})
=\approx_{\mathcal R},
}
\tag{26.2}
$$

它们才是在同一任务下互相恢复的四种表达。相同的值域基数、相同的当前读数或单向编码均不足以推出 (26.2)。若某一表示只需回答一个指定目标 $T$，则条件可弱化为 $\ker(q)\subseteq\ker(T)$；那是目标充分性，不是完整未来边界。

### 26.3 联合充分严格弱于各自充分

令

$$
X=\{0,1\}^2,\qquad P=\{0,1\},
$$

并定义评价

$$
E((u,v),0)=u,\qquad E((u,v),1)=v,
$$

于是完整双侧 profile $\Phi(u,v)=(u,v)$。再取四个表示

$$
q_{\rm sp}(u,v)=u,\quad
q_{\rm tm}(u,v)=v,\quad
q_{\rm bd}(u,v)=u\oplus v,\quad
q_{\rm mem}(u,v)=u\wedge v.
$$

每个单独表示都把不同状态合并，所以没有一个单独满足 (26.2)。但联合表示

$$
J=(q_{\rm sp},q_{\rm tm},q_{\rm bd},q_{\rm mem})
$$

满足

$$
\ker(J)=\ker(\Phi)=\{((u,v),(u,v)):(u,v)\in X\}.
\tag{26.3}
$$

这说明“空间、时间、边界、记忆合起来足够”只要求

$$
\ker(J)=\bigcap_i\ker(q_i)=\approx_{\mathcal R},
$$

严格弱于每个 $q_i$ 都能单独恢复完整 profile。联合接口只有在同一 $X$ 上定义，或已有共同来源态射把各分量拉回同一实际像时，才可作这种结论。

### 26.4 有限时间窗口何时在有限层停止细化

第25.1节中的有限投影应带有明确类型：

$$
\operatorname{TP}_N:X\to(\operatorname{Fin}(N+1)\to R),
\qquad
\operatorname{TP}_N(x)(i)=r(F^i x),
$$

并且

$$
Q_N:X\to S\times(\operatorname{Fin}(N+1)\to R),
\qquad
Q_N(x)=(\pi_{\rm sp}(x),\operatorname{TP}_N(x)).
\tag{26.4}
$$

若空间标签沿更新保持，即 $\pi_{\rm sp}\circ F=\pi_{\rm sp}$，令 $q_0=(\pi_{\rm sp},r)$，则 $Q_N$ 的 kernel 正好是由 $q_0$ 生成的长度 $N$ 未来关系。若空间标签不保持，不能直接把现有 `finiteFutureRelation` 套在 $q_0$ 上；此时应改用

$$
K_N=\ker(\pi_{\rm sp})\cap
\bigcap_{i=0}^{N}\ker(r\circ F^i)
$$

并单独证明这条关系链稳定，或者把冻结的空间标签扩展进状态载体后再应用有限稳定定理。

在 $X$ 带有限 `Finite` 载体、操作更新和读出满足相应稳定条件时，仓内 `FiniteFutureCongruence.infinite_relation_stabilizes`、`FiniteHistoryStability.finite_history_stability` 和 `FiniteEquivalenceDescent.finite_equivalence_descent_and_stability_bound` 给出某个深度 $d$，使

$$
\ker(Q_d)=\ker(Q_{d+1})=\ker(Q_\infty),
$$

并且所有 $N\ge d$ 保持同一 kernel。这里

$$
\operatorname{TP}_\infty(x)(k)=r(F^k x)\quad(k\in\mathbb N)
$$

是完整未来 profile，或等价地把其 kernel 定义为 $\bigcap_N\ker(\operatorname{TP}_N)$。稳定深度给出的是一个有限精确边界存在的条件，不是有限窗口对任意系统自动足够。

`FiniteStabilityClassBound.finite_stability_class_bound` 与 `FiniteEquivalenceDescent.finite_equivalence_descent_and_stability_bound` 还给出类数差的上界；在这些有限条件下，$Q_d$ 可以作为空间当前投影加有限时间窗口的最小精确联合边界。若动态更新在该 kernel 上闭合，便有唯一的诱导 $\bar F$；再与任一表示 $q_i$ 比较时，互相恢复仍等价于 $\ker(q_i)=\ker(Q_\infty)$，而不是由窗口长度或值域大小单独推出。

### 26.5 动态下降与关系态射

静态 kernel 相等还不够。若 $q:X\to Y$ 要承担后续更新，必须存在 $\bar F:Y\to Y$ 使

$$
q\circ F=\bar F\circ q,
\tag{26.5}
$$

并且相同 $q$ 值的状态对每个允许操作具有相同合法性、标签和后继摘要。对协议化表示，还要把操作回拉或操作类型映射一并计入；否则两个当前相同的摘要可能选择不同的下一操作，$\bar F$ 就不是一个良定义的内部更新。

若各 $q_i$ 与完整 profile 都满足相应的更新交换式，且 $\ker(q_i)=\ker(\Phi_{\mathcal R})$，则实际像上的恢复双射 $d_i$ 满足

$$
 d_i\circ \bar F_i=\bar F_{\Phi}\circ d_i.
\tag{26.6}
$$

因此换一种表示只是同一动态过程的共轭改写。若只有联合 kernel 条件 (26.3)，则只能得到联合表示 $J$ 的动态下降，不能把每个分量单独宣称为完整动态边界。

关系态射可以统一写成 $(f,g,\lambda)$：状态映射 $f:X\to X'$、协议回拉 $g:P'\to P$ 和标签映射 $\lambda:L\to L'$ 满足

$$
E'(f(x),p')=\lambda(E(x,g(p'))).
\tag{26.7}
$$

它给出评价保持及正向 kernel 保持。要把诱导映射称为反射、双射或两种表示的等价，还需在实际像上加入相应的满射与行列分离条件；单向评价保持本身只给出下降方向。

本节把“空间、时间、边界、记忆是同一个东西”改写为可检验的分层命题：单独互相恢复需要 (26.2)，联合恢复只需 (26.3)，动态可用还需 (26.5)，跨接口运输还需 (26.7)。这些结论是有限经典关系模型中的理论组织，Claim status 均为 open；没有新增 Lean 声明，也不把数学 profile 充当观察者已经实际取得的档案。

## 26.99 追加锚

## 27. 最小切面族与最大动态完成

第26节区分了单个表示充分与多个表示联合充分。本节进一步回答两个精简问题：一组空间、时间、边界和记忆切面中哪些成员不可删除；以及给定当前读出后，怎样得到仍能继续运行的最粗动态边界。

### 27.1 联合切面的交核判据

固定同一个实际来源 $X$、完整未来 profile $\Phi:X\to R$，以及有限索引集 $I$。对每个 $i\in I$ 令

$$
q_i:X\to Y_i,
\qquad
K_i:=\ker(q_i),
$$

并定义联合读出

$$
J_I(x):=(q_i(x))_{i\in I}.
$$

逐点展开立即得到

$$
\boxed{
\ker(J_I)=\bigcap_{i\in I}K_i.
}
\tag{27.1}
$$

所以联合切面对目标 $T$ 充分，当且仅当

$$
\bigcap_{i\in I}K_i\subseteq\ker(T),
\tag{27.2}
$$

而联合切面对完整未来任务精确，当且仅当

$$
\boxed{
\bigcap_{i\in I}K_i=\ker(\Phi)=\approx_{\mathcal R}.
}
\tag{27.3}
$$

这把“几种表示合起来是否足够”化成了一个只涉及观察纤维的判据；它不要求每个切面单独恢复完整 profile。

若 (27.3) 成立，$I$ inclusion-minimal 当且仅当对每个 $i\in I$ 存在一对见证状态 $x_i,y_i$，满足

$$
\Phi(x_i)\ne\Phi(y_i),
\qquad
q_j(x_i)=q_j(y_i)\quad(j\ne i).
\tag{27.4}
$$

因为全族精确，(27.4) 自动迫使 $q_i(x_i)\ne q_i(y_i)$；删去 $i$ 后这对状态落在剩余联合读出的同一纤维中，故剩余切面不再充分。反向地，若删去任一 $i$ 都不充分，就由 (27.2) 的失败取得这样的见证对。这是“哪一项关系不可删”的必要充分条件，属于普通集合论推导；当前仓内没有把它包装成新的 Lean 声明。

### 27.2 一个有冗余切面的有限例子

仍取 $X=\{0,1\}^2$，$\Phi(u,v)=(u,v)$，并令

$$
q_{\rm sp}(u,v)=u,\qquad q_{\rm tm}(u,v)=v,
$$

$$
q_{\rm bd}(u,v)=u\oplus v,\qquad
q_{\rm mem}(u,v)=u\wedge v.
$$

由 $(q_{\rm sp},q_{\rm tm})=\Phi$，切面族 $\{\mathrm{sp},\mathrm{tm}\}$ 已满足 (27.3)，且删去任一成员都会丢失一个坐标，因此它是 inclusion-minimal。加入 `bd` 或 `mem` 不改变联合 kernel，它们在这个任务中是冗余切面；但它们可能对另一个目标、另一个协议族或不同的代价函数成为不可删成员。故“冗余”总是相对于声明的未来任务，而不是某个表示的内在属性。

若每个 $q_i$ 都有动态下降

$$
q_i\circ F=F_i\circ q_i,
$$

则联合读出自动有坐标逐项的下降

$$
J_I\circ F=\bigl(\prod_{i\in I}F_i\bigr)\circ J_I.
\tag{27.5}
$$

若某个分量没有这样的更新或协议回拉，(27.1)—(27.4) 仍可作为静态判据，但不能把它称为可继续运行的联合边界。

### 27.3 当前读出内的最大前向不变核

令 $\tau:Y\to Y$ 是更新，$q:Y\to O$ 是当前实际读出。定义当前读出核

$$
K_0=\{(y_1,y_2):q(y_1)=q(y_2)\}.
$$

在 $K_0$ 中取所有满足前向不变条件

$$
(y_1,y_2)\in K\Longrightarrow
(\tau y_1,\tau y_2)\in K
$$

的关系，其最大者记为 $K_\infty$。等价地，

$$
K_\infty=\ker\bigl(y\mapsto(k\mapsto q(\tau^k y))\bigr).
\tag{27.6}
$$

它正是共同未来 profile 的 kernel。仓内 `PredictiveCompletionMaximalInvariantQuotient.predictive_completion_maximal_invariant_quotient` 直接给出四个条件：

1. 完成投影的 kernel 是 $K_\infty$；
2. $K_\infty$ 是当前读出核内的最大前向不变关系；
3. 当前读出唯一下降到该商；
4. 更新唯一下降到该商上的更新。

因此，把 $Y$ 压到 $Y/K_\infty$ 得到的不是任意摘要，而是**保留当前读出且仍可继续更新的最粗动态边界**。若另一个摘要 $h:Y\to B$ 也保留当前读出并有更新 $\bar\tau$，则

$$
\ker(h)\subseteq K_0,
\qquad
(h(y_1)=h(y_2)\Longrightarrow h(\tau y_1)=h(\tau y_2)),
$$

所以 $\ker(h)$ 是 $K_0$ 内的前向不变关系，从最大性得到

$$
\ker(h)\subseteq K_\infty.
\tag{27.7}
$$

式 (27.7) 表明任意其他精确动态摘要都至少保留 canonical completion 所保留的区别；它可以更细，不能更粗。这里的“最小”是按可区分关系的偏序理解，而不是按某个编码字节数或计算时间理解。若要优化存储大小或取得成本，还需另行指定代价模型。

### 27.4 协议作用下的同一结论

当允许操作由幺半群 $M$ 作用于 $X$，当前读出为 $q:X\to O$ 时，完整协议 profile 为

$$
\operatorname{controlProfile}(x)(a)=q(a\mathbin{\cdot}x),
\qquad a\in M.
$$

`ControlQuotientUniversalMinimality.control_quotient_universal_minimality` 给出该 profile 商的三项结构：当前读出可恢复、每个动作在商上有诱导作用、每个动作的后果可由商读出；并且任意同时满足这三项的候选摘要唯一因子到该商的实际像。`DynamicProfileCausalClosure.dynamic_profile_causal_closure` 则把执行一次动作后的 profile 写成 continuation 坐标的右平移。

所以，自治更新的 (27.6) 与受控协议的完整 action profile 是同一模式的两个特例：前者把未来时间词作为索引，后者把合法操作词作为索引。若空间、时间、边界和记忆各自只记录 profile 的一个投影，它们能否联合恢复，仍由 (27.1)—(27.4) 的交核条件决定；若要每个投影单独可运行，还必须各自满足 (27.5) 的动态下降。

### 27.5 精简结构的三层判定

因此，给定四个表示，精简性应分三层检查：

$$
\boxed{
\begin{array}{ll}
\text{静态充分：}&\displaystyle \bigcap_i\ker(q_i)\subseteq\ker(T);\\[4pt]
\text{任务精确：}&\displaystyle \bigcap_i\ker(q_i)=\ker(\Phi);\\[4pt]
\text{动态可运行：}&\displaystyle q_iF=F_iq_i\text{（或联合版本 }JF=F_JJ\text{）}.
\end{array}
}
\tag{27.8}
$$

第一层只回答一个目标，第二层保留全部声明的未来区别，第三层才保证下一项合法操作可以继续在摘要上定义。把其中任何一层偷换成“值域大小相同”或“当前读数相同”，都会重新引入前面隐藏档案与未来解码的反例。

本节把仓内已形式化的最大不变商、控制 profile 商和实际像因子化接到同一个交核框架中。新增的切面不可删判据、冗余例子和三层判定是普通数学组织，Claim status 均为 open；没有新增 Lean 声明，也不触发消化流程。

## 27.99 追加锚

## 28. 第26—26节的范围勘误：静态核、动态授权与无限联合边界

第26.2节中“最小动态边界”的措辞应按以下条件读取。kernel 与完整操作词 profile 相等，首先只证明一个**静态未来边界**：声明的标签、失败和费用可以从该摘要恢复。要把它称为可继续运行的动态边界，还必须同时满足第26.5节的更新下降，并要求合法操作、权限和选择器在该摘要的纤维上恒定。若动作词已总化且失败标签已纳入 $\Phi_{\mathcal R}$，这些条件可以由动态核的同余律承担；对一般部分操作，不能由 kernel 相等单独推出后续授权。

第26.4节的无限联合边界应明确写成

$$
\operatorname{TP}_\infty(x)(k)=r(F^k x),\qquad
Q_\infty(x)=\bigl(\pi_{\rm sp}(x),\operatorname{TP}_\infty(x)\bigr).
\tag{28.1}
$$

在 $\pi_{\rm sp}\circ F=\pi_{\rm sp}$ 时，

$$
\ker(Q_\infty)=\ker(\pi_{\rm sp})\cap\ker(\operatorname{TP}_\infty),
$$

正是以 $q_0=(\pi_{\rm sp},r)$ 生成的完整未来核；不变性不成立时仍应使用第26.4节的 $K_N$ 链，而不能把 $\ker(\operatorname{TP}_\infty)$ 单独当作空间—时间联合核。有限时间窗口、有限读出值域或一个当前空间读数，都不自动给出这个联合稳定性。

最后，若 (27.3) 成立，则由

$$
\ker(\Phi)=\bigcap_i\ker(q_i)\subseteq\ker(q_i)
$$

自动得到每个 $q_i$ 对完整 profile 的目标尊重；无需另加假设。若只知道联合充分的包含关系而没有精确等式，则各个分量可能保留额外区别，仍应把它们称为联合表示而不是同一最小表示。

这些句子只收紧结论量词与对象类型，不改变第26—26节的交核、最大不变核和协议 profile 结果；没有新增 Lean 声明，Claim status 仍为 open。

## 28.99 追加锚

## 29. 部分接续的总化：合法边与失败结果必须分开

第26.1节的

$$
\mathcal R\subseteq X\times A\times L\times X
$$

只记录成功的合法边。若某个 $(x,a)$ 没有后继，失败标签并不属于这条四元组关系；因此“把失败原因放入 $L$”本身还不足以使 $\mathcal R$ 成为总函数。准确的单步结果应总化为

$$
\operatorname{Step}_{\mathcal R}:X\times A
\longrightarrow
(L_{\rm ok}\times X)\;\sqcup\;L_{\rm fail},
\tag{29.1}
$$

其中左侧表示合法读数、记录和后继，右侧表示失败类型。若失败原因也要和成功标签放在同一个结果载体，需显式取不相交和

$$
L:=L_{\rm ok}\sqcup L_{\rm fail}
$$

并保留结果的成功/失败构造子；不能把一个失败标签伪装成缺失的后继。

在确定性部分系统中，$\operatorname{Step}_{\mathcal R}$ 由 $\mathcal R$ 与失败判定唯一确定；在非确定性系统中，应改成有限集合、概率分布或带权限的结果关系。完整词响应递归读取 (29.1) 的构造子，所以未来核要求相同的成功/失败形状、标签和后继 profile。第26.1节中“首操作后标签相同或后继再次处于未来核”的说法，只有在这种确定性总化或已声明的结果集合语义下成立。

仓内 `D5/S0/Automata/TypedPartialDFAO.lean` 与 `TypedPartialDFAOOverBase.lean` 已把部分转移、输出、类型保持和非法接续分开；`runFrom_append`、`evalOutput` 与 `runFrom_type` 支撑合法词的拼接和失败边界。对多个合法操作，`ControlledRelationRecursion.controlledDepthRelation` 给出深度零的当前读出核，以及深度递归中的 successor 前像交；`ControlledFiniteStability.controlled_finite_stability` 在有限载体和相应满射条件下把相邻深度稳定提升为永久稳定。

因此，部分关系的统一边界必须同时记录：

$$
\boxed{
\text{当前合法域}
+\text{成功标签与后继}
+\text{失败标签}
+\text{操作类型与权限}.
}
\tag{29.2}
$$

只保存成功路径的后继状态，会把“此操作不可执行”和“此操作尚未被测试”合并；只保存失败原因，又会丢失成功读数与后继。两者都必须通过同一个实际来源和同一个协议接口进入 profile。Claim status 为 open；本节没有新增 Lean 声明。

## 29.99 追加锚

## 30. 有限窗口、逆极限与实际来源的完成边界

前面把完整未来边界写成 $\operatorname{TP}_\infty$ 或操作词 profile，但观察者通常只取得有限前缀。要把两者连接起来，必须同时保留每个有限层的实际可实现性和层间限制相容性。

### 30.1 实际有限词与限制系统

令

$$
I_m:=\operatorname{im}(\operatorname{TP}_m)
\subseteq \operatorname{Fin}(m+1)\to R.
$$

对 $m\le n$，限制映射

$$
\rho_{m,n}:I_n\to I_m
$$

把长度 $n+1$ 的读出词截到长度 $m+1$。一个兼容有限族是

$$
\mathbf u=(u_m)_{m\in\mathbb N}
$$

满足

$$
 u_m\in I_m,
 \qquad
 \rho_{m,n}(u_n)=u_m\quad(m\le n).
\tag{30.1}
$$

因此它属于由实际有限窗口组成的逆极限

$$
\varprojlim_m I_m.
$$

条件 $u_m\in I_m$ 不能省略。仅仅给出每层名义值域中的一份相容函数，会产生一个形式上的极限序列，却未必来自任何实际状态。

仓内 `ItineraryCompletion.CompatibleItineraryFamily` 正是把 (30.1) 写成带有 `realized` 与 `compatible` 两个字段的结构；`itineraryToLimit` 把一个实际完整 itinerary 送到其所有有限前缀。

### 30.2 何时逆极限就是实际完整边界

完整实际边界为

$$
I_\infty:=\operatorname{im}(\operatorname{TP}_\infty).
$$

总有一个限制映射

$$
\Lambda:I_\infty\to\varprojlim_m I_m,
\qquad
\Lambda(u)=(u\!\upharpoonright_m)_m.
$$

在任意系统中，$\Lambda$ 的单射只使用函数逐坐标相等；满射则是额外的来源实现性质。若存在一个相容族的每个有限前缀都可由某个状态实现，但这些状态不能统一为同一个实际来源，逆极限会包含一个只在有限层相容的虚拟点。

在仓内 `ItineraryCompletion` 的有限状态假设下，`itineraryLimitEquiv` 给出

$$
\boxed{
I_\infty\cong\varprojlim_m I_m.
}
\tag{30.2}
$$

它的证明依赖有限载体以及 `CompatibleItineraryFamily.realized` 的逐层实际性；不能把 (30.2) 外推到没有这些条件的任意无限关系。`itinerary_completion` 还同时给出 kernel 商、实际完整 itinerary 和兼容有限族之间的动态半共轭，并存在一个有限深度 $d$ 使 $I_\infty$ 与 $I_d$ 已经双射。

因此要区分三种断言：

$$
\boxed{
\begin{array}{ll}
\text{逐层相容：}&u_m\text{ 满足层间限制};\\
\text{实际完成：}&(u_m)_m\text{ 来自同一实际状态的完整 profile};\\
\text{有限终止：}&\exists d,\ I_\infty\cong I_d.
\end{array}}
\tag{30.3}
$$

第一项是逆极限的语法，第二项是来源存在性，第三项是有限状态下的稳定性。三者不能互换。

### 30.3 完成边界的更新与观察者档案

完整 itinerary 的更新是移去第一个坐标的 shift：

$$
\operatorname{TP}_\infty(Fx)(k)=
\operatorname{TP}_\infty(x)(k+1).
\tag{30.4}
$$

所以实际完整边界上有一个 `itineraryUpdate`；在兼容有限族上，则由限制相容性诱导 `limitUpdate`。`itinerary_completion` 的半共轭式表明这两种表达承载同一更新。

但数学上的 $I_\infty$ 或逆极限不是观察者当前档案。观察者在预算 $N$ 下最多持有某个 $u_N\in I_N$，以及为取得它所保存的参考、权限和来源记录。若后续协议需要一个未取得的坐标，必须执行相应操作或把足以预测它的 completion 摘要实际写入记忆；不能把理论上的 $I_\infty$ 当作免费输入。

这也解释了为何有限一致不自动给出观察者知道完整未来：

$$
\text{数学 completion}
\neq
\text{当前可访问 archive}.
$$

前者是用来定义最小动态边界的对象，后者是选择器和更新程序真正可以读取的接口。

### 30.4 与空间、时间、边界和记忆的统一

把空间、时间、边界和记忆分别看作同一完整 profile 的有限或重排投影时，它们的联合恢复需要两个条件：

1. 每个投影都来自同一个实际来源 $X$，或有已证的共同来源态射；
2. 投影的联合 kernel 等于 $\ker(\operatorname{TP}_\infty)$，并且各投影的更新、协议和失败结果在相应纤维上下降。

在有限稳定深度 $d$ 存在时，可以用 $\operatorname{TP}_d$ 替代完整 profile；否则，逆极限只提供一个候选完成对象，仍需单独证明实际来源满射或接受它作为 completion。若某个空间切面只记录当前坐标，时间切面只记录未来读数，记忆只记录档案摘要，它们各自的缺失关系由 (27.1)—(27.4) 的交核判据定位，而不是由“都来自同一个系统”自动消失。

本节直接对应仓内 `ItineraryCompletion.itineraryLimitEquiv`、`itinerary_completion`、`completionCoordinateEquiv` 和有限未来稳定结果。逆极限的实际来源条件、无限系统中的满射性以及观察者取得 completion 的资源成本仍为 open；没有新增 Lean 声明。

## 30.99 追加锚

## 31. 关系的关系：协议族闭包与联合可观测核

第27节的交核是在固定的有限表示族上取交。本节把“哪些读出被允许”也作为变量，得到关系—读出之间的第二层闭包。这是递归关系不应被误解为重复改写同一公式的地方：只有读出族、操作族或标签语义发生扩展，递归才会产生新的区分。

### 31.1 从关系生成可保持读出，再生成联合核

设 $X$ 为状态载体，$O$ 为一个固定的读出值域，$\mathscr R\subseteq X\times X$ 为一组当前被要求保留的关系。令

$$
\Pi(\mathscr R):=\{q:X\to O:\forall(x,y)\in\mathscr R,\ q(x)=q(y)\}
$$

为在 $\mathscr R$ 上不变的读出族，并定义联合可观测核

$$
\mathsf K(\mathscr R)
:=\{(x,y):\forall q\in\Pi(\mathscr R),\ q(x)=q(y)\}.
\tag{31.1}
$$

逐点展开得到三条关系律：

$$
\boxed{
\mathscr R\subseteq\mathsf K(\mathscr R),
}
\tag{31.2}
$$

$$
\mathscr R\subseteq\mathscr S
\Longrightarrow
\mathsf K(\mathscr S)\subseteq\mathsf K(\mathscr R),
\tag{31.3}
$$

以及

$$
\boxed{
\mathsf K(\mathsf K(\mathscr R))=\mathsf K(\mathscr R).
}
\tag{31.4}
$$

(31.2) 是因为每个 $q\in\Pi(\mathscr R)$ 都保持 $\mathscr R$；(31.3) 是因为约束增多后可用的读出变少；(31.4) 表示对同一读出值域再次取“所有保持读出”的联合核，不会创造新的区别。仓内 `ProtocolRelationClosureLaws.protocol_relation_closure_laws` 直接形式化了这三条关系侧结论。

因此 $\mathsf K$ 是由读出—关系极性产生的固定点算子：它是扩张的、反单调的、幂等的。它不是普通意义上单调的闭包；把 (31.3) 错写成同向单调会颠倒信息增益的方向。

### 31.2 协议扩展才会产生新的分辨率

设 $\mathscr P_0\subseteq\mathscr P_1$ 是两组允许协议，定义协议联合核

$$
K_{\mathscr P}(x,y)
\iff
\forall p\in\mathscr P,\quad E(x,p)=E(y,p).
$$

则

$$
\mathscr P_0\subseteq\mathscr P_1
\Longrightarrow
K_{\mathscr P_1}\subseteq K_{\mathscr P_0}.
\tag{31.5}
$$

若存在 $x,y$ 使 $K_{\mathscr P_0}(x,y)$ 成立而某个新增 $p\in\mathscr P_1$ 区分二者，则包含严格。反之，若新增协议在旧核的每条纤维上恒定，协议扩展不会改变动态边界；它只是对已有资料的重排或重复读取。

同理，若观测族按

$$
\mathscr Q_0\subseteq\mathscr Q_1\subseteq\cdots
$$

扩展，则其联合 kernel 形成反向链

$$
K_{\mathscr Q_0}\supseteq K_{\mathscr Q_1}\supseteq\cdots.
\tag{31.6}
$$

空间、时间、边界和记忆可以被理解为四个协议/读出子族；它们的联合恢复只需检查链的交是否达到完整 profile kernel。`QueryKernelHierarchy.query_kernel_hierarchy` 给出观察、干预和反事实查询按可因子化关系形成 kernel 链，并保留严格性见证；它说明“加入更强协议”不是一句信息更多的比喻，而是一个核包含关系。

### 31.3 关系递归何时真正前进

给定初始关系 $\mathscr R_0$ 与逐层协议族 $\mathscr P_n$，可以定义

$$
\mathscr R_{n+1}:=K_{\mathscr P_n}(\mathscr R_n),
$$

其中 $K_{\mathscr P_n}$ 表示只取第 $n$ 层允许协议在 $\mathscr R_n$ 约束下的联合核。若协议族固定且只使用 (31.1) 的同一值域，(31.4) 表明关系闭包在一次取核后已经达到固定点；继续写 $\mathscr R_{n+2}$ 不会凭空增加新信息。

真正的递归细化必须满足至少一项：

$$
\boxed{
\text{扩大协议族}
\quad\text{或}\quad
\text{扩大操作词/失败标签}
\quad\text{或}\quad
\text{改变读出值域与任务目标}.
}
\tag{31.7}
$$

否则“关系的关系的关系”只是同一 kernel 的再次命名。若协议族扩展到其并集，极限核为

$$
K_{\infty}=\bigcap_n K_{\mathscr P_n};
$$

这与第30节的完整未来 profile 相接，但仍要另证该极限是否来自实际共同来源，以及观察者是否能取得它。

### 31.4 与边界最小性相接

对目标 $T:X\to Z$，协议族 $\mathscr P$ 的联合摘要是 $T$ 可恢复的，当且仅当

$$
K_{\mathscr P}\subseteq\ker(T).
\tag{31.8}
$$

当取等号时，协议商既没有漏掉目标相关区别，也没有保留任务无关的合并；它是该任务的精确边界。若 $K_{\mathscr P}$ 严格小于 $\ker(T)$，说明协议保留了额外区别，可能需要再做目标相关压缩；若它不包含于 $\ker(T)$，则当前协议族确实无法恢复目标。

这把“最小关系结构”分成两个正交操作：先用允许协议求联合 kernel，确定动态上不能合并的关系；再在目标 kernel 内检查是否还存在任务无关的细化。空间、时间、边界和记忆的互相恢复，是它们的协议核都落在同一 $K_{\mathscr P}$ 上，而不是它们的编码格式相同。

本节对应仓内 `ProtocolRelationClosureLaws`、`QueryKernelHierarchy` 与实际像 kernel 因子化结果；反单调闭包、协议扩展的严格性以及无限协议并集的实际来源条件，在理论层保持 open。没有新增 Lean 声明。

## 31.99 追加锚

## 32. 切面变换的完成化自然性

空间切面、时间切面、边界摘要和记忆表示若来自不同载体，不能仅凭它们值域之间存在一个编码就称为同一过程。准确的换切面需要同时运输更新和读出，并在完整未来完成上给出自然的交换。

### 32.1 半共轭与读出翻译

设两个带更新的实际系统为

$$
(X,F,q),\qquad (Y,G,r),
$$

其中 $F:X\to X$、$G:Y\to Y$ 是更新，$q:X\to B$、$r:Y\to R$ 是当前读出。设状态运输 $h:X\to Y$、读出翻译 $\eta:B\to R$ 满足

$$
 h\circ F=G\circ h,
 \qquad
 r\circ h=\eta\circ q.
\tag{32.1}
$$

第一式是动态半共轭，第二式是当前接口评价保持。对每个 $n$ 归纳可得

$$
 r(G^n h(x))=\eta(q(F^n x)),
$$

于是完整 profile 有自然运输

$$
\widehat h:\operatorname{im}(\operatorname{TP}_\infty^X)\to
\operatorname{im}(\operatorname{TP}_\infty^Y),
$$

$$
\widehat h\bigl((q(F^n x))_{n\ge0}\bigr)
 =\bigl(r(G^n h(x))\bigr)_{n\ge0}.
\tag{32.2}
$$

若同一个 profile 可由多个 $x$ 表示，(32.1) 保证右侧相同；因此 (32.2) 在实际像上良定义。它满足

$$
\widehat h\circ\operatorname{TP}_\infty^X
=\operatorname{TP}_\infty^Y\circ h,
\qquad
\widehat h\circ\operatorname{shift}_X
=\operatorname{shift}_Y\circ\widehat h.
\tag{32.3}
$$

仓内 `BehaviorCompletionFunctoriality.behavior_completion_is_functorial` 形式化了这两个交换式，并进一步给出运输的唯一性、恒等和复合。因而换切面可被视为完成化对象之间的态射，而不是在原状态空间中任意旋转坐标。

### 32.2 单向精化与双向同一化

(32.1) 只给出单向运输。若 $h$ 或 $\eta$ 合并了两个未来 profile，$\widehat h$ 可以是满射而不是单射；这表示目标切面是源切面的粗化。若要称两种切面互相恢复，需要在实际完成像上证明

$$
\ker(\operatorname{TP}_\infty^X)
\stackrel{h}{\longleftrightarrow}
\ker(\operatorname{TP}_\infty^Y)
$$

之间的双向反射，等价地要求存在反向运输 $k$，使两边的 profile 映射互为逆。单向读出因子化只能推出 kernel 包含和完成商上的满射，不能推出双射。

更一般地，若只对有限窗口 $N$ 有

$$
r(G^n h(x))=\eta(q(F^n x))\quad(0\le n\le N),
$$

则只能构造有限边界运输 $\widehat h_N$；不能把它提升成完整 profile 的自然态射。若未来某个坐标在 $N+1$ 首次分离，有限交换方程会在下一层失效。这正是有限分辨率与完整动态等价之间的缺口。

### 32.3 自然性、恒等与复合

若另有

$$
(Y,G,r)\xrightarrow{k,\theta}(Z,H,s)
$$

满足与 (32.1) 同形的交换式，则完成运输满足

$$
\widehat{(k\circ h)}=\widehat k\circ\widehat h,
\qquad
\widehat{\mathrm{id}}=\mathrm{id}.
\tag{32.4}
$$

这给“改变切面、再改变参考、再改变记忆编码”的路径独立性一个可检验版本：只要每一步都保存动态半共轭和读出因式分解，完整 profile 上的结果与直接运输一致。若某一步只保存当前数值，不保存未来协议或失败标签，(32.4) 的证明条件就断裂，路径依赖不再是坐标记号问题，而是实际 kernel 被扩大。

### 32.4 与四种表示的恢复

对空间、时间、边界和记忆四个表示 $q_i$，若每个表示都与同一完整 profile 满足 (32.1) 的下降条件，并且

$$
\ker(q_i)=\ker(\operatorname{TP}_\infty),
$$

则它们的完成像之间存在唯一的自然双射，且交换各自的更新。若只有联合交核等式

$$
\bigcap_i\ker(q_i)=\ker(\operatorname{TP}_\infty),
$$

则只有联合表示 $J=(q_i)_i$ 得到自然等价；单个分量仍可能只是互补的静态投影。由此，互相恢复的强命题与联合充分的弱命题在完成化范畴中仍然严格区分。

本节对应仓内 `BehaviorCompletionFunctoriality`、`BehaviorCompletionTranslation` 和 `PredictionCompletion.observation_refinement_completion`。它把跨切面运输的交换、唯一性、复合和有限窗口限制写成统一条件；没有新增 Lean 声明，理论结论 Claim status 为 open。

## 32.99 追加锚

## 33. 完成运输的实际像与双向条件勘误

第32.2节的“kernel 双向对应”应严格理解为完成像上的诱导映射，而不是把状态映射 $h$ 直接当成两个关系集合之间的双射。令

$$
I_X=\operatorname{im}(\operatorname{TP}_\infty^X),
\qquad
I_Y=\operatorname{im}(\operatorname{TP}_\infty^Y).
$$

在 (32.1) 下，$\widehat h:I_X\to I_Y$ 首先只是良定义的单向映射；若 $h$ 在实际来源像上满射，则 $\widehat h$ 在相应 profile 像上满射。只有再有反向系统态射、或直接证明 $\widehat h$ 单射并满足反向的更新与读出交换，才能称两种完成表示双向恢复。

若 $h(x)=h(y)$ 蕴含两者的完整 profile 相同，则 $\widehat h$ 的良定义不需要 $h$ 单射；若完整 profile 相同的反向蕴含也成立，则它们在状态 quotient 上反射同一未来核。因而可检验的双向条件是

$$
\widehat h\text{ 在 }I_X\text{ 与 }I_Y\text{ 之间为双射，且}
\widehat h\circ\operatorname{itineraryUpdate}_X
=\operatorname{itineraryUpdate}_Y\circ\widehat h,
$$

并带有读出翻译的交换式。第32节中的 `shift` 均指这里的 `itineraryUpdate`；有限窗口只得到对应的有限 itinerary 映射。

本勘误只限定跨切面双向恢复的对象和量词，不改变单向半共轭、唯一运输或复合自然性。Claim status 为 open，无新增 Lean 声明。

## 33.99 追加锚

## 34. 未来完成与过去逆极限的方向不对称

第30节把完整未来 profile 与有限前缀的逆极限连接起来，但这仍是单向时间结构。若更新不可逆，未来 completion 不会自动包含全部过去记忆；过去兼容线程只保留能够无限向前追溯的稳定核心。

### 34.1 两种线程载体

先取有限状态载体 $Y$ 与自映射 $F:Y\to Y$。恒等读出下，正向未来线程为

$$
I_F^+:=\{(F^n y)_{n\ge0}:y\in Y\},
\qquad
\operatorname{ev}_0^+:I_F^+\to Y,
\quad
\operatorname{ev}_0^+((y_n)_n)=y_0.
$$

过去兼容线程为

$$
I_F^-:=\{u:\mathbb N\to Y:\forall n,\ F(u_{n+1})=u_n\},
\qquad
\operatorname{ev}_0^-:I_F^-\to Y.
\tag{34.1}
$$

正向线程的零坐标恢复初态，因此

$$
I_F^+\cong Y.
\tag{34.2}
$$

过去线程的零坐标只能落在周期核心

$$
\operatorname{Per}(F):=\{y:\exists n>0,\ F^n y=y\}.
$$

在有限载体上，`BackwardOrbitCore.backward_orbit_eval_zero_bijective` 与 `pastCoreEquiv` 给出

$$
I_F^-\cong\operatorname{Per}(F).
\tag{34.3}
$$

仓内 `IdentityFuturePastGap.identity_future_completion_exceeds_past_core` 进一步给出：若 $F$ 非双射，则

$$
\operatorname{Nat.card}(\operatorname{Per}(F))
<\operatorname{Nat.card}(Y),
$$

且过去线程严格少于正向 identity completion。未来可区分的瞬态初态不会因为存在一个兼容过去线程而获得过去坐标。

### 34.2 最小有限反例

令

$$
Y=\{0,1\},qquad F(0)=0,quad F(1)=0.
$$

恒等读出下，正向线程分别为

$$
(0,0,0,\ldots),qquad(1,0,0,\ldots),
$$

所以 $I_F^+$ 有两个元素并能恢复初态。过去兼容条件强迫 $u_0=0$，再递归强迫每个 $u_n=0$；因此 $I_F^-$ 只有常值零线程。

这不是“未来和过去使用了不同坐标”的记号现象，而是 $F$ 把瞬态状态 $1$ 压入稳定状态 $0$ 后，已没有可逆的前驱链可以恢复它。若观察者要保留这份过去区别，必须把档案或可逆辅助变量并入状态；未来 profile 本身不会自动重建已被非单射更新遗忘的前身。

### 34.3 双向恢复的准确条件

若 $F$ 在实际来源上是双射，则有限情形下每个状态都在周期核心中，(34.2) 与 (34.3) 可由双向 shift 互相运输。更一般地，令

$$
Y_\infty:=\operatorname{range}(F^{[|Y|]}).
$$

在有限载体上，`StableImagePeriodicCore.iterate_range_card_antitone_and_stable` 给出足够迭代后稳定像等于 $\operatorname{Per}(F)$；把实际来源限制到 $Y_\infty$ 后，更新在该核心上可逆，`FiniteBilateralTrajectory.finite_bilateral_trajectory` 给出双侧轨迹由周期点基准唯一确定。

因此，若统一模型要求空间、时间、边界和记忆同时支持正向与反向恢复，至少要声明下列之一：

$$
\boxed{
F\text{ 在实际来源像上双射}
\quad\text{或}\quad
\text{先把来源限制到稳定周期核心 }Y_\infty.
}
\tag{34.4}
$$

若只要求正向预测，非双射更新仍可使用第27节的最大前向不变 completion；若还要求过去档案可由同一边界重建，(34.4) 是额外的双向条件，而非未来 kernel 自动提供的结论。

### 34.4 带一般读出的推广

对一般 $q:Y\to O$，正向 completion 是

$$
I_{F,q}^+=\operatorname{im}\bigl(y\mapsto(q(F^n y))_{n\ge0}\bigr),
$$

其 kernel 是未来可观测等价；过去线程还需满足同一读出下的双侧兼容。恒等读出反例表明，即使正向 kernel 为最细，过去线程也可能严格缺少瞬态来源。因而一般情况下，双向恢复需要同时证明：

1. 更新在实际来源像上可逆，或已限制到稳定核心；
2. 过去与未来 profile 的 kernel 在该核心上相等；
3. 空间、边界和记忆投影在这个双向 kernel 上都满足动态下降。

本节组织仓内 `IdentityFuturePastGap`、`BackwardOrbitCore`、`StableImagePeriodicCore` 与 `FiniteBilateralTrajectory` 的既有结果，强调未来 completion 与过去记忆的方向性差异。没有新增 Lean 声明，理论结论 Claim status 为 open。

## 34.99 追加锚

## 35. 折扣未来伪度量：近似边界与精确核的分层

前面的 kernel 判据是零误差的任务等价。若读出值域 $O$ 带有度量，观察者也可以用一个有界的近似边界来排序仍未完全相同的未来行为，但这不会自动产生一个新的精确商。

### 35.1 折扣未来距离

设 $q:Y\to O$，更新为 $F:Y\to Y$，并假设 $(O,d)$ 是度量空间，存在 $B<\infty$ 使

$$
 d(a,b)\le B\qquad(a,b\in O).
$$

对 $0<\gamma<1$ 定义

$$
D_\gamma(y,y')
:=\sup_{n\ge0}
 \gamma^n d\bigl(q(F^n y),q(F^n y')\bigr).
\tag{35.1}
$$

仓内 `CanonicalDiscountedFutureGeometry.canonical_discounted_future_geometry` 形式化了以下性质：$D_\gamma$ 是 $Y$ 上的伪度量，满足

$$
 d(qy,qy')\le D_\gamma(y,y'),
\tag{35.2}
$$

$$
D_\gamma(Fy,Fy')\le\gamma^{-1}D_\gamma(y,y'),
\tag{35.3}
$$

以及

$$
\boxed{
D_\gamma(y,y')=0
\iff
\forall n,\ q(F^n y)=q(F^n y').
}
\tag{35.4}
$$

因此，对任意严格正的折扣，零核仍然是完整未来核；折扣只改变不同非等价状态之间的距离权重，不改变精确空间、时间、边界和记忆在任务上的等价类。

### 35.2 近似纤维不是自动的商

给定容差 $\varepsilon>0$，可定义近似关系

$$
 y\sim_{\gamma,\varepsilon}y'
 \iff D_\gamma(y,y')\le\varepsilon.
$$

它通常不是传递关系：三角不等式只能给出 $D_\gamma(y,z)\le2\varepsilon$。所以不能直接把近似纤维当作精确 quotient 的类，也不能由两个相邻近似运输步骤自动得到零误差的互相恢复。

要让近似表示继续支持拼接，至少需要：

1. 每个局部运输的缺陷上界；
2. 更新对所选距离的 Lipschitz 或收缩界；
3. 所有后续协议的读出误差预算；
4. 合法性/失败标签的判定裕度，避免误差跨过域边界。

若用 $D_\gamma$ 作为边界上的取得优先级，(35.3) 给出一次更新后误差的最坏放大；若同时把折扣与更新改写为相反方向的归一化距离，还需另给相应的收缩合同。几何距离本身不授予观察者取得或认证精确读数的权限。

### 35.3 多切面的加权近似

对有限切面族 $I$、正权重 $w_i$ 和离散读出距离，可定义

$$
D_{I,\gamma}(x,y)
:=\sup_{i\in I,\ n\ge0}
 w_i\gamma^n d_i(q_i(F^n x),q_i(F^n y)).
\tag{35.5}
$$

仓内 `DiscountedPrimeTimeUltrametric.discounted_prime_time_distance_strong_triangle` 给出有限正权重、$0<\gamma\le1$ 时的强三角不等式。其零核是所有选定切面、所有未来时刻都相同的联合 kernel；这与第27节的交核判据一致。若权重族或协议族扩展，零核只会收缩，但数值距离是否有统一上界和取得成本，仍须逐项声明。

因此，精简统一结构应保持三层区别：

$$
\boxed{
\text{精确未来核}
\quad\subseteq\quad
\text{近似距离的零集/商}
\quad\subseteq\quad
\text{给定容差的近似纤维}.
}
\tag{35.6}
$$

第一层决定可组合的精确边界；第二层在正折扣下与第一层有相同零核；第三层只提供带误差的分辨率，必须另配误差传播和合法域裕度。本节对应仓内 `CanonicalDiscountedFutureGeometry` 与 `DiscountedPrimeTimeUltrametric`；没有新增 Lean 声明，理论结论 Claim status 为 open。

## 35.99 追加锚

## 36. 四种表达的共同核与双向恢复判据

**本批导航。** 本节把前文的未来行为、过去线程、切面边界和观察者记忆放回同一个实际关系载体，给出四种表示何时可以互相恢复的统一判据。它补充第26—26节的共同未来核、第31—32节的协议闭包与完成运输，以及第34节的过去核心；不改判既有条目，也不新增 Lean 声明。

### 36.1 最小关系载体不是一个坐标，而是一个带作用的商

设实际来源中的联合配置为 $S$。一项合法有类型接续由

$$
 s\xrightarrow{a/y}s'
$$

给出；其中 $a$ 包含接口和权限要求，$y$ 包含正常读数、失败标签与本次必须保留的记录。对可接续的动作词 $w$，记

$$
 \operatorname{Run}_w(s)
 $$

为从 $s$ 出发的完整带类型结果：它同时包含词是否合法、各步输出、记录和最终配置。于是定义任务族 $\mathcal W$ 的未来核

$$
 s\equiv^+_{\mathcal W}t
 \iff
 \forall w\in\mathcal W,
 \operatorname{Run}_w(s)=\operatorname{Run}_w(t).
 \tag{36.1}
$$

若只保留输出而忘记合法性或档案，所得关系一般更粗；它可能仍是某个较弱任务的核，却不是原任务的动态充分边界。

当更新 $F:S\to S$ 允许无限向前运行时，过去核不能仅由 $F$ 的形式逆函数定义。令

$$
 S^-_F:=\{u:\mathbb N\to S\mid F(u_{n+1})=u_n\},
$$

并令 $\operatorname{Past}(s)$ 表示以 $s$ 为零坐标的所有实际兼容线程及其记录。只有当 $\operatorname{Past}(s)$ 非空且所需的过去记录被任务声明为可读时，才定义

$$
 s\equiv^- t
 \iff
 \operatorname{Past}(s)=\operatorname{Past}(t).
 \tag{36.2}
$$

在有限非双射系统中，第34节的 `IdentityFuturePastGap` 说明 $S^-_F$ 只覆盖周期核心；因此 $\equiv^-$ 的定义域应写成实际双向来源 $S^{\leftrightarrow}\subseteq S$，不能把瞬态状态默认为有过去坐标。

把合法性和记忆分别纳入核：

$$
 \equiv^{\mathrm{adm}},\qquad
 \equiv^{\mathrm{rec}}.
$$

对要求同时保留未来作用、过去可回溯性、合法选择和档案读出的任务，最小共同核是

$$
 \boxed{
 \equiv_\star
 :=
 \equiv^+_{\mathcal W}
 \cap
 \equiv^-\cap
 \equiv^{\mathrm{adm}}
 \cap
 \equiv^{\mathrm{rec}}.
 }
 \tag{36.3}
$$

这里的“最小”是指不能再合并而仍保持声明的全部续接；它不是说商的元素数对所有未来任务都绝对最少。缩小 $\mathcal W$、删除失败标签或撤销过去读权限，都会改变任务，因而也会改变 $\equiv_\star$。

在这个意义下，真正的最小关系对象是

$$
 \boxed{(S/\!\equiv_\star,\ \{\overline T_a\},\ \{\overline{\operatorname{Run}}_w\})}
 \tag{36.4}
$$

而不是商集合单独。若商上没有诱导的合法动作、输出和记录更新，边界只是静态标签，不能递归拼接。

### 36.2 四种表示的核比较

设四个实际表示分别为

$$
 r_{\mathrm{sp}}:S\to R_{\mathrm{sp}},\quad
 r_{\mathrm{tm}}:S\to R_{\mathrm{tm}},\quad
 r_{\partial}:S\to R_{\partial},\quad
 r_{\mathrm{mem}}:S\to R_{\mathrm{mem}}.
 \tag{36.5}
$$

它们可以分别被解释为：端口与连通关系的空间表示、合法动作词及其顺序的时间表示、对未来接续充分的边界类、以及同一实际来源中观察者可继续调用的档案和控制记忆。它们的值域只取实际像，不把未实现的形式点偷偷加入。

对任一表示 $r_i$，有两个不同的判据：

* $\equiv_\star\subseteq\ker(r_i)$ 表示它至少不把任务已经视为相同的状态拆开；这是从共同商向该表示下降的充分性。
* $\ker(r_i)\subseteq\equiv_\star$ 表示它没有把仍可由任务区分的状态合并；这是无损性。

所以精确表示满足

$$
 \boxed{\ker(r_i)=\equiv_\star.}
 \tag{36.6}
$$

只满足第一项的表示可以是冗余编码；只满足第二项的表示可以保存区别但未必支持任务所需的统一计算。两项都满足，才是同一任务下的最小充分表示。

### 36.3 四表示互相恢复的充分且必要条件

**命题 36.1（共同核恢复判据）。** 若四个表示均取实际像，且

$$
 \ker(r_{\mathrm{sp}})=
 \ker(r_{\mathrm{tm}})=
 \ker(r_{\partial})=
 \ker(r_{\mathrm{mem}})=\equiv_\star,
 \tag{36.7}
$$

则对任意 $(i,j)$ 存在唯一双射

$$
 g_{ij}:R_i\to R_j,
 \qquad
 g_{ij}(r_i(s))=r_j(s),
 \tag{36.8}
$$

并满足 $g_{ii}=\mathrm{id}$、$g_{jk}\circ g_{ij}=g_{ik}$。反之，若这些双射满足 (36.8)，则所有四个核相等。

**证明。** 由 (36.7)，若 $r_i(s)=r_i(t)$，则 $s\equiv_\star t$，从而 $r_j(s)=r_j(t)$，故 (36.8) 良定义。实际像条件给出满射；用 $g_{ji}$ 可得逆映射。唯一性来自每个实际像元素都有表示 $r_i(s)$。复合与恒等式逐点成立。反向若 $g_{ij}\circ r_i=r_j$ 且 $g_{ij}$ 为双射，则 $r_i(s)=r_i(t)$ 当且仅当 $r_j(s)=r_j(t)$，四个核相等。

这个命题把“空间、时间、边界和记忆是同一对象的不同表达”变成可检查的核等式。只有名称相似、值域同构或总数相同，都不能替代 (36.7)。

### 36.4 动力下降与双向恢复的附加条件

对每个合法动作 $a$，若

$$
 s\equiv_\star t
 \Longrightarrow
 \bigl(
 \operatorname{Adm}_a(s)=\operatorname{Adm}_a(t)
 \land
 \operatorname{Out}_a(s)=\operatorname{Out}_a(t)
 \land
 T_a(s)\equiv_\star T_a(t)
 \bigr),
 \tag{36.9}
$$

则 $T_a$ 在共同商上下降为 $\overline T_a$，四个表示之间的 $g_{ij}$ 都满足动态半共轭

$$
 g_{ij}\circ \overline T_a^{\,i}
 =
 \overline T_a^{\,j}\circ g_{ij}.
 \tag{36.10}
$$

这正是边界方程、时钟方程和观察者更新可以使用同一商的条件。若式 (36.9) 只对未来输出成立而不含合法性、失败或档案，得到的只是输出商，不能声称观察者的完整状态已恢复。

若还要求反向恢复，则需在实际双向来源 $S^{\leftrightarrow}$ 上给出逆作用 $T_a^{-1}$，或证明每个所需的后继都有唯一带记录的前驱。有限载体上，足够迭代后的稳定周期核心满足这一要求；第34节的二点常值映射说明在核心之外不成立。于是双向版本的条件是

$$
 \boxed{
 \text{(36.9) 对正向和反向均成立，且更新在 }S^{\leftrightarrow}\text{ 上可逆。}
 }
 \tag{36.11}
$$

没有式 (36.11)，最多得到正向时间、边界和记忆的互相恢复；把过去记忆写成未来边界的函数会把瞬态来源误当成已保存信息。

### 36.5 关系的关系的关系：任务族的递归闭包

令 $\mathcal W_0$ 是原始动作词族。观察者可以把已取得的记录、校准和组合协议重新作为下一层动作，因此定义

$$
 \mathcal W_{n+1}
 :=
 \operatorname{Cl}\bigl(
 \mathcal W_n,
 \operatorname{Compose},
 \operatorname{Read},
 \operatorname{Record},
 \operatorname{Calibrate}
 \bigr),
 \tag{36.12}
$$

其中每个生成操作都必须保留共同来源、合法域和失败标签。令

$$
 K_n:=\equiv^+_{\mathcal W_n}.
$$

协议族扩张只会增加测试，所以

$$
 K_{n+1}\subseteq K_n,
 \qquad
 K_\infty:=\bigcap_{n\ge0}K_n.
 \tag{36.13}
$$

若载体的可达商有限，下降链最终稳定；若商无限，(36.13) 只是极限核，不能声称存在有限阶段的最终边界。这个递归闭包解释了“关系的关系”而不另造系统外观察者：新层仍是同一个接口上的动作，只是测试族和记忆接口被扩展。

每一层的表示若都满足

$$
 \ker(r_i^{(n)})=K_n,
 \tag{36.14}
$$

则层间存在唯一的商运输 $R_i^{(n+1)}\to R_i^{(n)}$，并且四表示的横向运输与纵向细化交换。若某层只保存一个标量（例如总实现数或熵），式 (36.14) 通常失败；这正是“当前信息量相同但未来解码能力不同”的二位 XOR 反例在一般形式上的原因。

### 36.6 适用范围与未解决边界

本节使用的是集合、关系和有限或可数动作词上的普通数学推导。仓内 `IdentityFuturePastGap`、`FiniteBilateralTrajectory`、`CanonicalRowColumnSeparation`、`DoubleExtensionalEvaluationDescent`、`DynamicProfileCausalClosure` 及相关模块是可引用的形式化支点；本节没有新增 Lean 声明，也没有把这些支点包装成新的形式定理。

仍需单独证明的内容包括：无限任务族的实际来源存在性、带概率或量子权重时的正性与归一化、近似边界的误差预算、以及具体系统的有限可取得性。若这些条件缺失，(36.7) 只能作为目标判据，不能报作已经成立的物理统一或全局恢复。

本节的 Claim status 为 open。

## 36.99 追加锚

## 37. 行为商、窗口逆极限、完备化与实际来源的四层区分

**本批导航。** 本节把“completion”拆成四个不同对象，并给出它们之间的规范映射、来源满射条件和最小反例。它补充第30节的有限窗口、第34节的过去逆极限和第35节的折扣距离；不把形式相容点、度量完备化或延拓后的状态冒充原始来源中的实际配置。

### 37.1 四个对象及其规范映射

固定一个处处有定义的更新 $F:X\to X$ 和读出 $q:X\to O$。完整未来行为写成

$$
 B(x):=(q(F^n x))_{n\ge0}\in O^{\mathbb N}.
 \tag{37.1}
$$

由它得到行为商

$$
 Q_B:=X/\ker B,
$$

以及已实现的行为像

$$
 I_B:=B(X)\subseteq O^{\mathbb N}.
$$

二者有规范双射

$$
 Q_B\simeq I_B.
 \tag{37.2}
$$

对每个 $n$，令有限窗口集合为

$$
 W_n:=\{(q(x),q(Fx),\ldots,q(F^n x)):x\in X\}
 \subseteq O^{n+1}.
$$

删除最后一个坐标给出限制映射 $r_{n+1,n}:W_{n+1}\to W_n$。其逆极限为

$$
 L_W:=\varprojlim_n W_n.
 \tag{37.3}
$$

把完整行为截断到各窗口，得到规范单射

$$
 I_B\hookrightarrow L_W.
 \tag{37.4}
$$

单射来自所有有限前缀相等就逐坐标相等；满射则是额外的来源实现命题。若在 $Q_B$ 上另选一个与行为相容的度量并取完备化，记为 $\widehat Q_B$。于是至少要区分

$$
\boxed{
 Q_B
 \ \simeq\ I_B
 \ \hookrightarrow\ L_W,
 \qquad
 Q_B\longrightarrow\widehat Q_B .
}
\tag{37.5}
$$

这里没有默认 $L_W=\widehat Q_B$，也没有默认任一形式点来自 $X$。四个对象分别回答：

* $Q_B$：哪些原始状态具有相同的全部未来行为；
* $I_B$：原始来源实际产生了哪些完整行为；
* $L_W$：每个有限窗口都相容的形式行为有哪些；
* $\widehat Q_B$：在所选度量下加入哪些 Cauchy 极限。

ItineraryCompletion、BehaviorCompletionFunctoriality 与 CanonicalDiscountedFutureGeometry 分别提供这些层次的部分形式化支点；它们的假设不能在转述时删去。

### 37.2 什么时候有限窗口能被同一个来源实现

给定相容族 $\lambda=(w_n)_n\in L_W$，定义来源纤维

$$
 C_n(\lambda):=\{x\in X:
 (q(x),\ldots,q(F^n x))=w_n\}.
$$

则

$$
 C_{n+1}(\lambda)\subseteq C_n(\lambda),
$$

并且有精确等价

$$
\boxed{
 \lambda\in I_B
 \iff
 \bigcap_{n\ge0}C_n(\lambda)\ne\varnothing .
}
\tag{37.6}
$$

因此，单层窗口满射只说明每个 $C_n(\lambda)$ 非空；限制映射满射只说明有限窗口之间可以逐层延长；它们都不直接给出右端的全体交非空。

下列条件分别提供不同强度的实现结论：

1. 若 $X$ 有限，所有 $C_n(\lambda)$ 非空，则递减有限集合族的交非空；若窗口联合分离 $X$，实现还唯一。
2. 若 $X$ 紧致 Hausdorff、各 $C_n(\lambda)$ 闭且非空，则紧致性给出全体交非空；连续读出到 Hausdorff 值域是一个常见充分条件。
3. 若 $X$ 是完备度量空间，$C_n(\lambda)$ 闭、递减、非空且 $\operatorname{diam}(C_n(\lambda))\to0$，则交恰有一个点。

这些条件不能互相替代。特别是“来源本身完备”必须相对于一个明确的、使纤维成为闭集并产生 Cauchy 控制的度量；通常离散度量下的完备性不能证明行为度量下的来源实现。

### 37.3 倒计时反例：逆极限有形式点而原始来源没有

取

$$
 X=\mathbb N_0,\qquad
 F(k)=\max(k-1,0),\qquad
 q(k)=
 \begin{cases}
  1,&k>0,\\
  0,&k=0.
 \end{cases}
$$

状态 $k$ 的完整行为为

$$
 B(k)=1^k0^\infty .
$$

长度 $n+1$ 的窗口集合包含

$$
1^j0^{\,n+1-j}\qquad(0\le j\le n+1),
$$

所有限制映射均可由增加一个前导 $1$ 的窗口实现。于是形式族

$$
\lambda_n=1^{n+1}
$$

属于 $L_W$，因为删除最后坐标仍得到 $\lambda_{n-1}$。但不存在有限 $k$ 使

$$
 B(k)=1^\infty .
$$

对应来源纤维为

$$
 C_n(\lambda)=\{k:k\ge n+1\},
 \qquad
 \bigcap_nC_n(\lambda)=\varnothing .
$$

因此

$$
 I_B\subsetneq L_W.
 \tag{37.7}
$$

若使用离散输出的折扣未来距离，则完备化会为这列状态添加一个固定点 $\infty$，其行为为 $1^\infty$；这个固定点是完备化或扩张动力学中的状态，不是原始 $\mathbb N_0$ 中的来源。它说明“形式相容”“完备化新增点”和“原始实际来源”必须写成三种不同的断言。

### 37.4 过去逆极限是另一种 completion

完整过去空间定义为

$$
 P_F:=
 \{(x_0,x_{-1},x_{-2},\ldots):
 F(x_{-n-1})=x_{-n}\ \forall n\ge0\}.
 \tag{37.8}
$$

它是平稳逆系统的逆极限。其移位在 $P_F$ 上可以是双射，即使原始 $F$ 不是双射；但零坐标映射

$$
 \operatorname{ev}_0:P_F\to X
$$

可能不满射，甚至 $P_F$ 可能为空。有限载体上，公开的 BackwardOrbitCore、IdentityFuturePastGap 与 FiniteBilateralTrajectory 给出

$$
 \operatorname{im}(\operatorname{ev}_0)
 =\operatorname{Per}(F),
 \qquad
 P_F\simeq\operatorname{Per}(F).
 \tag{37.9}
$$

二点反例

$$
 X=\{0,1\},\qquad F(0)=F(1)=0,\qquad q=\operatorname{id}
$$

的未来行为商仍有两个元素，但 $P_F$ 只有常值零线程。故正向行为商不能自动恢复被非单射更新抹去的过去。

在无限系统中，$\operatorname{im}(\operatorname{ev}_0)$ 也不必等于稳定像
$\bigcap_nF^n(X)$：每个有限深度可以有前驱，却可能没有一条可相容的无限分支。要把商上的过去线程提升回原始来源，至少需要逐步后向提升条件

$$
\forall x\in X,\ \forall b\in Q,\quad
 \overline F(b)=\pi(x)
 \Longrightarrow
 \exists y\in X,\ F(y)=x\land\pi(y)=b,
 \tag{37.10}
$$

以及能够把这些局部选择组成一条完整历史的相容性条件。商映射满射和正向半共轭本身不充分。

### 37.5 折扣距离的零核与正误差

若输出距离 $\rho$ 是分离的且有界，$0<\gamma<1$，定义

$$
 D_\gamma(x,y):=
 \sup_{n\ge0}\gamma^n
 \rho(q(F^n x),q(F^n y)).
 \tag{37.11}
$$

则严格正权重给出

$$
D_\gamma(x,y)=0
 \iff
 B(x)=B(y)
 \iff
 x\equiv^+y.
 \tag{37.12}
$$

这只说明零集与精确行为核相同；它不说明每个正距离阈值都能恢复精确等价。若两个行为首次在时刻 $k$ 区分，离散 $0/1$ 输出下距离为 $\gamma^k$，因此不同类可以任意接近。要从 $D_\gamma\le\varepsilon$ 得到精确商，必须另有正分离间隙，例如有限行为商下的类间最小正距离。

此外，Bellman 关系是

$$
 D_\gamma(x,y)
 =
 \max\{\rho(qx,qy),\gamma D_\gamma(Fx,Fy)\},
 \tag{37.13}
$$

所以

$$
D_\gamma(Fx,Fy)\le\gamma^{-1}D_\gamma(x,y).
$$

这通常是状态更新的扩张界；收缩的是作用在候选距离函数上的 Bellman 算子，而不是 $F$ 本身。CanonicalDiscountedFutureGeometry 与仓内相关距离模块只在各自声明的范围内支持这些结论。

### 37.6 四层映射的正确结算方式

今后正文中使用 “completion” 时，应同时写清下列四项：

1. completion 的载体是 $Q_B$、$I_B$、$L_W$、$\widehat Q_B$ 还是 $P_F$；
2. 规范映射是哪一个，以及它是否单射或满射；
3. “实际来源”要求哪个来源映射满射，使用有限性、紧致性、完备性还是直接的纤维交证明；
4. 若更新在 completion 上延拓，延拓后的状态是否仍有原始来源。

因此，最稳妥的总括不是“相容窗口已经实现了整体”，而是：

$$
\boxed{
\text{有限窗口相容性产生形式行为；
来源实现性是这些来源纤维全体交非空的额外命题。}
}
$$

本节的构造与反例是普通数学组织，引用仓内既有模块但没有新增 Lean 声明；Claim status 为 open。

## 37.99 追加锚

## 38. 递归协议闭包与 completion 的正交性

**本批导航。** 本节把递归观察中的三类 completion、全体局部读出的最小 profile 商和协议创新判据放在同一条核细化链上。它补充第31节的协议族闭包与第36—36节的共同核、实际来源区分；不把身份恢复、规范化选择、未来行为充分性或概率极限混为一个“完成”。

### 38.1 三种 completion 不是同一个性质

给定读出 $r:X\to R$、未来目标 $b:X\to B$ 和代表关系 $\mathsf{Rep}\subseteq X\times U$，分别定义：

$$
\begin{aligned}
 \operatorname{IdComp}(r)
 &:\Longleftrightarrow \operatorname{Injective}(r),\\
 \operatorname{NormComp}(\mathsf{Rep})
 &:\Longleftrightarrow
   \forall x,\ \exists!u,\ \mathsf{Rep}(x,u),\\
 \operatorname{BehComp}(r,b)
 &:\Longleftrightarrow
   \forall x,y,\ r(x)=r(y)\Longrightarrow b(x)=b(y).
\end{aligned}
\tag{38.1}
$$

第一项说当前读出保留身份，第二项说每个对象有唯一规范代表，第三项说当前读出足以恢复指定未来目标。它们的量词不同，互相没有一般蕴含。

最小的有限反例已经存在于二点载体：

* 恒等读出满足 $\operatorname{IdComp}$，但“任意代表都合法”的关系不满足 $\operatorname{NormComp}$；
* 对象等于代表的关系满足 $\operatorname{NormComp}$，但常值读出不满足 $\operatorname{IdComp}$；
* 常值未来目标与常值读出满足 $\operatorname{BehComp}$，但读出仍不能区分两个当前身份。

仓内 ThreeCompletionOrthogonality 形式化了这些方向的分离。于是理论中每次写“completion”都必须标注它完成的是身份、代表选择、未来行为、联合约束还是某种代数残差。

### 38.2 全体局部读出的规范最小 profile

设协议索引为 $P$，每个协议有可能不同的读出值域 $O_p$，并给出

$$
 q_p:X\to O_p.
$$

定义 global profile

$$
 Q(x):=(q_p(x))_{p\in P},
 \qquad
 X_{\mathrm{prof}}:=X/\ker Q.
 \tag{38.2}
$$

对每个 $p$，存在唯一局部读出

$$
 \widehat q_p:X_{\mathrm{prof}}\to O_p,
 \qquad
 q_p=\widehat q_p\circ\pi_{\mathrm{prof}}.
 \tag{38.3}
$$

若另一个接口 $r:X\to R$ 能恢复全部局部读出，即对每个 $p$ 存在 $d_p:R\to O_p$ 满足

$$
 q_p=d_p\circ r,
 \tag{38.4}
$$

则存在唯一

$$
 h:R\to X_{\mathrm{prof}},
 \qquad
 \pi_{\mathrm{prof}}=h\circ r.
 \tag{38.5}
$$

因此 $X_{\mathrm{prof}}$ 是“同时保留这整个局部读出族”的最小接口。仓内 GlobalProfileQuotientUniversality 还表明，只要求每个有限子族存在共同解码器，就足以推出 (38.5)；非空来源条件是为了把因子定义在任意接口值上。

这个 profile 商仍是静态对象。若更新 $F$、合法性和记录没有被纳入索引族 $P$，则 (38.4) 只保证当前局部读出可恢复，不能保证下一步动作或完整未来可恢复。把所有合法续接读出加入 $P$，才会把静态 profile 连接到第36节的动态共同核。

### 38.3 协议创新是切开当前纤维的关系

令当前摘要为 $q:X\to Q$，新增协议律为 $\ell:X\to L$。联合摘要为

$$
(q,\ell):X\to Q\times L.
$$

其核严格小于当前核当且仅当存在一对当前不可区分、但被新协议分开的来源：

$$
\boxed{
 \ker(q,\ell)\subsetneq\ker q
 \iff
 \exists x,y,\ q(x)=q(y)\land\ell(x)\ne\ell(y).
}
\tag{38.6}
$$

这给出递归细化的局部证书。若第 $n$ 步协议为 $\ell_n$，令

$$
 K_0:=\ker q,
 \qquad
 K_{n+1}:=K_n\cap\ker\ell_n,
 \tag{38.7}
$$

则 $K_{n+1}\subseteq K_n$；严格性恰由某个仍在 $K_n$ 中的 private witness 见证。有限状态时这条下降链只能有限次严格下降，之后的稳定核才可作为有限阶段证书。无限状态时，充分协议族可能没有包含极小子族：例如 $X=\mathbb N$、$\ell_n(x)=\min(x,n)$，任何无界指标族都能区分所有状态，但删除一个指标后仍无界。

因此三种优化不能互换：

$$
\text{每个协议都有 private witness}
\not\Longleftrightarrow
\text{协议数最少}
\not\Longleftrightarrow
\text{读出信息量最少}.
\tag{38.8}
$$

(38.6) 只给出严格细化判据；成本最优化需要另行声明成本函数和允许的协议族。

### 38.4 有限前缀的等价不保证无限完成的等价

在概率模型中，有限前缀的所有结果可能都互相绝对连续，而完整无限记录却由某个尾事件严格区分两个来源。仓内 FinitePrefixInfiniteCompletionSeparation 给出这样的形式化实例：两个 Bernoulli 参数的每个有限 transcript law 互相绝对连续，但完整 state laws 互相奇异。

这不是与第37节的集合来源反例相同的现象：

* 第37节的倒计时例说明相容形式行为可能没有原始来源；
* 本节的概率例说明每个有限观察层都不能作零一判定，但无限记录的可测事件可以把来源分开。

因此，若边界任务包含无限尾事件、几乎处处区分或完成后的可测协议，必须把这些对象加入目标核；只保存每个有限层的统计等价，不能自动推出完成层的等价。

同时，不能把“无限完成后存在一个区分事件”解释成某个有限观察者已经取得了它。它是极限语义中的可测对象；实际观察者还需另有可取得性、资源和记录接口。

### 38.5 refinement 是表示之间的箭头，而不是另一个状态坐标

若接口 $r_1:X\to R_1$ 能由接口 $r_2:X\to R_2$ 解码，记

$$
 r_1\preceq r_2
 \iff
 \exists h:R_2\to R_1,\quad r_1=h\circ r_2.
 \tag{38.9}
$$

恒等解码给出自反性，解码复合给出传递性。于是接口表示形成一个预序；互相可解码的表示在反对称化后成为同一 refinement 类。仓内 RefinementCompositionStructure 给出了因子化范畴、恒等、结合律和互相细化后的预序。

在这个预序中：

* global profile 商是恢复指定局部读出族的最小类；
* 动态行为商是恢复全部声明续接的最小类；
* 任何夹带额外历史的记忆是更细的表示，未必已经动态闭合；
* 任何只保留当前标量的摘要可能更粗，若其核超出目标核便失去充分性。

因此“空间、时间、边界和记忆互相恢复”应写成同一 refinement 类中的实际像双射，并同时检查更新和协议作用的交换式；值域字面相同或状态数相同都不够。

### 38.6 与已形式化支点的范围

本节直接复用 ThreeCompletionOrthogonality、GlobalProfileQuotientUniversality、ProtocolInnovationCriterion、FinitePrefixInfiniteCompletionSeparation 和 RefinementCompositionStructure 的公开结论。它们分别支撑 completion 正交性、全体局部读出的最小 profile、严格细化的 private witness、有限—无限概率分离和 refinement 复合；本节只是把这些结果接入共同核叙述，没有新增 Lean 声明。

具体模型仍需声明：索引族是否包含合法性和失败、概率完成是否要求尾事件、接口值是否取实际像、以及更新是否在该核上下降。缺少这些条件时，本节结论只是一组适用判据，不能声称已得到物理时空统一。

本节 Claim status 为 open。

## 38.99 追加锚

## 39. 语义核与类型化 completion 的正交积

**本批导航。** 第27节已经给出 action-profile 的动态闭合判据，第36—37节已经给出共同核、实际来源、三类语义 completion、global profile 与 refinement。本节不重复把这些结果改写成新的 profile 定理，而是加入一个尚未明确分开的轴：边界表示的**语义充分性与可运输性**，和它所附带的**解析或代数 completion 类型**不是同一个偏序。若把它们压成一个“完成度”标量，会把不同的失败原因混在一起。

### 39.1 语义精确性与动态可运行性是两个必要条件

固定一个实际配置空间 $S$。先区分当前静态任务核 $K_{\mathrm{cur}}$ 与把全部声明未来续接、失败和记录纳入后的行为核 $K_{\infty}$；二者都应是相应任务输出的等价关系。若本节写 $K_*$，须先说明它取哪一个。对一个边界表示

$$
r:S\longrightarrow R
$$

写

$$
\operatorname{Sem}_{K_*}(r)\ :\Longleftrightarrow\ \ker r=K_*.
\tag{39.1}
$$

这只说当前表示恰好保留指定任务要求区分的状态。它没有说下一项操作可以在 $R$ 上执行。

设 $a$ 是一个声明过的合法操作，完整配置上的后继为 $T_a$；把合法性、指定输出、失败与记录统一记为 $L_a(s)$。动态下降要求存在边界侧的 $\bar T_a$ 与 $\bar L_a$，使

$$
\boxed{
 r\circ T_a=\bar T_a\circ r,
 \qquad
 L_a=\bar L_a\circ r.
}
\tag{39.2}
$$

当 $T_a$ 只在合法域上定义时，(39.2) 的含义是：若 $r(s)=r(t)$，则 $s,t$ 对 $a$ 同时合法或同时失败；合法时输出和记录相同，且后继的边界值相同。于是可以定义

$$
\operatorname{Dyn}(r):\Longleftrightarrow
\text{对每个声明动作，(39.2) 的边界更新存在且唯一。}
\tag{39.3}
$$

因此，一个可继续运行的精确边界至少满足

$$
\boxed{\operatorname{Exact}(r)\ :\Longleftrightarrow\ \operatorname{Sem}_{K_*}(r)\land\operatorname{Dyn}(r).}
\tag{39.4}
$$

值域大小、当前读数的熵或一次实验的互信息都不能替代这两个条件。一个摘要可以在当前目标上精确，却把两条要求不同后续的历史合并；也可以动态闭合，却保留了任务永远不会读取的冗余历史。前者损害继续运行，后者只说明它不是最小表示。

### 39.2 解析 completion 另有自己的类型轴

现在给边界或载体附加一个解析对象 $V=(V_n)_n$、测试集 $T$、目标点 $x$ 与操作代数 $A$。可以分别提出四种性质：

* **uniform completion**：投影误差趋于零，例如
  $\|I-P_{V_n}\|\to0$；
* **state-family completion**：测试集上的残差趋于零，例如
  $\sup_{t\in T}\|P_{V_n}^{\perp}t\|\to0$（有界测试集的直观写法；仓内形式化支点使用 $\operatorname{ENNReal}$ 上确界）；
* **member-target completion**：只要求一个指定 $x\in T$ 的残差趋于零；
* **algebra equality**：由允许窗口生成的指定 unital 或 $*$-代数恰好等于目标代数；
* **observable containment**：只要求一族指定 observable 包含于该生成代数；这是较弱的独立标签。

在仓内定理列出的 $RCLike$、$NormedAddCommGroup$、$InnerProductSpace$ 与逐项 $HasOrthogonalProjection$ 条件下，仓内 `FourTypedCompletionHierarchy.four_typed_completion_hierarchy` 给出正向层级

$$
\boxed{
\operatorname{Uniform}\Longrightarrow
\operatorname{StateFamily}\Longrightarrow
\operatorname{MemberTarget},
}
\tag{39.5}
$$

并给出两个方向都严格的反例。它还分别给出解析收敛与操作代数的独立反例：可以有完整的窗口生成代数而三种 Hilbert 收敛都失败，也可以三种 Hilbert 收敛都成立而 prime-diagonal 代数仍然是 proper 子代数并漏掉指定非对角 observable。

所以 (39.5) 是**解析强度的偏序**，不是语义核的偏序。特别地，不能从

$$
\operatorname{Sem}_{K_*}(r)\land\operatorname{Dyn}(r)
$$

推出 Uniform、StateFamily、MemberTarget 或 Algebra 中任何一个；也不能从其中任意一个解析性质反推出 $\ker r=K_*$。这些结论各自需要自己的载体、范数、测试族和运算代数假设。

### 39.3 正确的统一数据是带类型的积，而不是一条总序

给每个表示 $r$ 附上语义核、动态下降和一个明确的 completion 标签 $m$。可以写成

$$
\boxed{
\mathsf{TypedBoundary}(r;\mathcal A)=
\bigl(\ker r,\ \operatorname{Dyn}(r),\ m(r;\mathcal A)\bigr),
}
\tag{39.6}
$$

其中 $\mathcal A$ 包含 $V=(V_n)$、测试族 $T$、目标点或目标集、范数/拓扑、允许窗口和目标代数等辅助数据；$m(r;\mathcal A)$ 取值于所声明的解析/代数模式，而不是只由裸表示 $r$ 决定的数。两个表示 $r_i:S\to R_i$ 只有在以下条件同时成立时，才可以声称是同一个任务下的互相恢复：

1. $\ker r_1=\ker r_2=K_*$；
2. 两边的全部合法动作、失败、读数和记录都分别下降；
3. 存在实际像之间的唯一双射 $g_{12}:\operatorname{im}r_1\simeq\operatorname{im}r_2$，满足
   $g_{12}\circ r_1=r_2$，并与每一个边界更新交换；
4. 若还要比较解析 completion，则必须另外声明 $m(r_1;\mathcal A_1),m(r_2;\mathcal A_2)$ 相同，或给出携带辅助数据并保持该模式的映射。

前两项是语义与运输条件，第三项是表示间的恢复，第四项才是解析类型的比较。它们组成一个带任务参数的多轴数据结构；语义轴可以严格细化而解析模式不变，也可以解析模式改变而语义核完全不变。

一个直接的有限构造说明这一点。取同一个有限 $S$、同一个 $r$ 和同一组边界更新，令解析载体在两次描述中分别为全空间序列 $V_n=\top$ 与零子空间序列 $V_n=\bot$，并把测试集和目标点按相应类型选择。语义核和动态下降没有改变，但 Uniform、StateFamily、MemberTarget 的真假可以改变。反向地，即使 $V_n=\top$ 使三种 Hilbert 性质都成立，若 $r$ 合并了两个未来输出不同的状态，仍有

$$
\neg\operatorname{Sem}_{K_*}(r).
\tag{39.7}
$$

这排除了“解析完备所以边界完备”的偷换。

### 39.4 与身份、规范化、行为三类 completion 的交叉

第38.1节所定义的

$$
\operatorname{IdComp},\qquad
\operatorname{NormComp},\qquad
\operatorname{BehComp}
$$

属于语义任务轴；它们分别讨论身份单射、代表的唯一存在和指定未来在读出纤维上的恒定。仓内 `ThreeCompletionOrthogonality` 已给出三者之间的有限反例以及“同一 readout 下身份蕴含行为”的唯一一般方向。

因此，完整描述至少需要记录两类标签：

$$
\boxed{
\bigl(\text{语义任务参数与 completion 类型},\ \text{解析/代数辅助数据与 completion 类型}\bigr).
}
\tag{39.8}
$$

不能把 `IdentityCompletion` 当成 Uniform，也不能把 `BehaviorCompletion` 当成 MemberTarget；`NormalizationCompletion` 还依赖代表关系 $\mathsf{Rep}$，并非裸读出 $r$ 的属性。前者讨论读出是否单射，后者讨论未来行为是否在纤维上恒定；Hilbert 投影误差和窗口生成代数又是另一组载体条件。

同样，解析对象的收敛不是一个免费来源。若 $r$ 只在形式极限上有值，必须另行说明该极限是否来自实际配置、是否落在观测者可取得的接口中，以及更新是否仍然保留在来源像内。第37节已经区分有限窗口的形式行为、completion 载体和实际来源；本节只把这一区分提升为类型化积，不把它们重新合并。

### 39.5 双侧恢复时还要保留端口的类型

若统一表示同时有状态端 $X$、协议端 $P$ 和评价

$$
E:X\times P\to\Lambda,
$$

则状态行商与协议列商分别由评价核决定。仓内 `DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` 的条件显示：要把两个商与目标端口双射对应，需要目标评价的行、列外延性以及两个原始映射的满射性。没有这些条件，只能得到商上的下降或一个实际像上的因子，不能声称原始空间和协议空间互相恢复。

这为“空间、时间、边界和记忆”的共同核陈述加上了一个类型限制：互相恢复的不是四个裸集合，而是带有端口、动作、记录与评价的 typed interfaces。若某一表示忘记了协议列、参考位或失败标签，它可能仍与另一表示有相同的状态数，却不满足 (39.2) 的记录交换式。

有限反例很简单。令 $X=P=\{0,1\}$，令 $E(x,p)=x\land p$，并把协议映射压成常值。状态行仍可能在某个受限协议像上区分，协议列却不再能区分 $p=0,1$；商上的更新可以下降，但不存在把原协议元素唯一恢复的双射。故“有一个矩阵核”不等于“两侧 typed interface 已互相恢复”。

### 39.6 可检验的后续义务与开放边界

对具体系统，声明统一恢复时至少要逐项提供：

* 目标共同核 $K_*$ 的任务范围，包含哪些失败、记录和未来动作；
* 表示 $r$ 的实际值域或实际像，以及 $\operatorname{Sem}_{K_*}(r)$ 的证明或反例；
* 每个合法动作的边界下降式 (39.2)，包括权限、参考和观察者选择器；
* 解析/代数标签的载体和量词，明确是 Uniform、StateFamily、MemberTarget 还是 Algebra；
* 若声称空间与时间双向恢复，状态映射与协议映射的满射、目标评价的行列外延性及实际像双射；
* 有限阶段相容与实际来源存在性之间没有被省略的 completion 条件。

这些义务不能由一个统一术语“全息”“完备”或“时空几何”代替。当前仓内形式化结果为上述每一轴分别提供支点，但尚未给出把语义核、动态下降和任意解析 completion 自动合成为单一总定理的声明；本节是普通数学综合，Claim status 为 open，不新增 Lean 声明。

## 39.99 追加锚

## 40. 局部接口、transition cocycle 与全局恢复

**本批导航。** 本节把局部边界的拼接进一步分成三个层次：读出因子在交叠上的一致、局部坐标或 frame 的 transition 数据、以及沿路径运输时的 holonomy。它接回仓内 `LocalFactorOverlapCompatibility`、`ContinuousLocalFactorGluing`、`GlobalFrameCoboundaryCriterion`、`HistoricalCongruence` 与 `CumulativeInverse`，但不把这些分别已证的支点冒充一条“全局时空统一”定理。

### 40.1 局部因子的一致性先于连续 gluing

设 $q:X\to B$ 是一个边界读出，$U_i\subseteq B$ 是局部接口域，$t:X\to Y$ 是目标读出。局部因子为

$$
f_i:U_i\to Y,
\qquad
t(x)=f_i(q(x))\quad\text{当 }q(x)\in U_i.
\tag{40.1}
$$

若 $q$ 满射，则同一交叠点 $b\in U_i\cap U_j$ 必有

$$
f_i(b)=f_j(b).
\tag{40.2}
$$

证明只需取 $x$ 使 $q(x)=b$，再分别应用 (40.1)。这正是仓内 `local_factor_overlap_compatibility` 的内容：开性、覆盖和连续性不是得到 (40.2) 所必需的，真正关键的是同一个满射来源同时解释两份局部因子。

若 $q$ 不满射，(40.2) 只能在 $\operatorname{im}q$ 的交叠上推出。一个有限反例是

$$
X=\{0\},\quad B=\{0,1\},\quad q(0)=0,
$$

令两个域都为 $B$，令 $f_1(0)=f_2(0)$ 而 $f_1(1)\ne f_2(1)$。两份局部因子都正确解释 $t(0)$，但在不可达的 $1$ 处不相容。因此“每个局部片都能解释来源”不等于“局部片在整个接口交叠上相容”；必须声明满射，或把断言域限制为实际像。

若进一步假设 $B$ 为拓扑空间、$U_i$ 开且覆盖 $B$，各 $f_i$ 连续，并满足 (40.2)，则存在唯一连续全局因子

$$
f:B\to Y,
\qquad
t=f\circ q,
\qquad
f|_{U_i}=f_i.
\tag{40.3}
$$

仓内 `continuous_local_factors_glue_uniquely` 给出这一结论。这里的唯一性来自覆盖，而不是来自 $q$ 的满射：满射用于把 $t$ 的来源解释为局部因子，覆盖用于确定 $B$ 上每一点的全局值。若只知道实际像上的覆盖，则 (40.3) 只能先在实际像上得到；对像外的延拓需要额外条件。

### 40.2 transition 数据的 coboundary 判据

局部标架或局部记忆的值域不必是同一个线性坐标。设重叠上的 transition 取值于群 $G$：

$$
g_{ij}(x)\in G,
\qquad x\in U_i\cap U_j.
\tag{40.4}
$$

在固定方向约定下，局部 frame 系数 $c_i:U_i\to G$ 的相容式可写为

$$
c_i(x)=g_{ij}(x)c_j(x).
\tag{40.5}
$$

如果存在这样的系数，就有

$$
g_{ij}(x)=c_i(x)c_j(x)^{-1}.
\tag{40.6}
$$

反过来，(40.6) 代回 (40.5) 即得相容。因此，对单位群值 transition，

$$
\boxed{
\text{存在全局非零 frame 系数}
\Longleftrightarrow
\text{transition 是一族局部单位的 coboundary}.
}
\tag{40.7}
$$

仓内 `global_frame_iff_transition_coboundary` 正是这个代数判据。它只给出声明的 overlap 关系上的群值系数等价，并没有自动加入自交叠、反向交叠或三重交叠的域闭合。若另加这些域条件，并要求同一个 $x$ 同时属于相应交叠，则 coboundary 在共同定义域上推出：

$$
g_{ij}g_{jk}=g_{ik},
\qquad
g_{ii}=e,
\qquad
g_{ji}=g_{ij}^{-1}.
\tag{40.8}
$$

所以要声明一个可以继续拼接的局部 frame，至少要分别检查：交叠域是否真的存在、transition 的方向是否一致、三重交叠上的 cocycle、以及是否存在把它平凡化的 $c_i$。pairwise overlap equality 只处理 (40.2)，并不能替代带定义域条件的 (40.8) 或 (40.7)。

### 40.3 路径运输与 holonomy 是另一层条件

把每条有向交叠边 $i\to j$ 的 transition 相乘，可以定义一条路径；以下固定 $x$ 必须属于路径中每条边的共同定义域，并且各次乘法的陪域按方向相容：

$$
\gamma=(i_0,i_1,\ldots,i_n)
$$

上的运输

$$
G(\gamma;x)=g_{i_0i_1}(x)g_{i_1i_2}(x)\cdots g_{i_{n-1}i_n}(x).
\tag{40.9}
$$

若路径首尾相同，$G(\gamma;x)$ 是 holonomy。全局 frame 存在时，(40.6) 使每个闭路的运输望远镜相消，故

$$
G(\gamma;x)=e
\quad\text{对所有声明的闭路 }\gamma.
\tag{40.10}
$$

这是全局 frame 的必要条件。反过来，只有在声明了足够的路径连接、转移的 cocycle、以及从基点到各片的运输与路径无关时，(40.10) 才能构造 $c_i$ 并给出一个充分条件。一般拓扑载体上，局部相容或某一组有限闭路的平凡并不自动证明所有可能的全局 obstruction 消失。

一个纯有限反例说明为什么不能跳过 holonomy。取三个片 $1,2,3$，单位群 $G=\{+1,-1\}$，在每条有向边上令

$$
g_{12}=g_{23}=g_{31}=-1.
$$

若存在 $c_i$ 满足 (40.6)，则闭路乘积应为

$$
g_{12}g_{23}g_{31}=c_1c_1^{-1}=+1,
$$

但实际乘积为 $-1$。因此没有全局 frame 系数，尽管每条单独的二片交叠都给出了一个合法的 transition。这个失败发生在三边关系上，不能由逐边合法性发现。

### 40.4 历史同构运输的不变量范围

当局部接口带有历史档案、当前集合、选择集合和因果关系时，transition 还必须运输这些结构。仓内 `HistoricalCongruence` 对历史同构的 product、complement 和 temporal composition 逐项运输 attributes、causal、current 与 selection，并保持相应的边界关系；它本身没有把 records、合法域、失败标签、reference 或 permissions 纳入同一结论。

抽象地，若 $h_i:S_i\simeq S_i'$ 是局部接口的历史同构，则对每个局部操作 $T$ 应有

$$
h_{\mathrm{out}}\circ T_i
=
T_i'\circ h_{\mathrm{in}},
\tag{40.11}
$$

若任务还要求记录、合法域和失败标签随接口运输，则必须把它们作为额外的 transition 假设写入：它们也要交换。仅有状态集合之间的双射不够；它可能把当前显示对应起来，却不保持因果边或选择集合，因而不能作为 transition 参与全局拼接。

若多个局部接口沿路径运输满足 (40.11)，闭路后的 holonomy 至少必须保持声明的记录和操作；是否要求 holonomy 恒等，取决于任务是恢复裸状态、恢复带参考的状态，还是允许一个可观测的 gauge 变换。这里的“允许 gauge”必须写入目标共同核，不能在证明失败后临时扩大等价关系。

### 40.5 累积历史与有限增量的双向恢复

时间或记忆表示可以取增量而不是完整历史。对加法交换群 $R$，设 $c:\mathbb Z\to_0 R$ 是有限支撑增量，定义

$$
C(n)=\sum_{t\le n}c(t).
\tag{40.12}
$$

若 $C$ 在足够左侧恒为零、在足够右侧恒为常值，则相邻差分

$$
(\nabla C)(n)=C(n)-C(n-1)
\tag{40.13}
$$

仍是有限支撑，并满足

$$
\nabla(\operatorname{cumulative}(c))=c,
\qquad
\operatorname{cumulative}(\nabla C)=C.
\tag{40.14}
$$

仓内 `CumulativeInverse.cumulative_inverse` 把这一点提升为带加法结构的双射，并进一步给出整数时间乘空间 profile 的版本。

这提供了一个明确的“时间—记忆”双向恢复例子，但条件不能省略。若没有左尾锚定，所有常数平移的历史具有同一差分；若允许无限支撑而不加收敛或尾条件，累积和可能没有定义；若只保存总和而不保存增量位置，则不同路径会被错误合并。因此，时间表示和记忆表示互相恢复的准确对象是

$$
\boxed{
\text{有限增量}\ +\ \text{尾部规范化}
\longleftrightarrow
\text{满足尾条件的完整历史}.
}
\tag{40.15}
$$

它不是“任何时钟读数都等价于全部历史”的结论。

### 40.6 局部到全局的最小证明义务

对一个声称由局部关系恢复全局结构的具体模型，应按以下顺序检查：

1. 实际来源是否满射到接口，或断言是否明确限制在实际像；
2. 局部因子是否在真实交叠上相容；
3. 若有连续结构，域是否开、是否覆盖、局部因子是否连续；
4. transition 是否满足方向约定和 cocycle；
5. 声称全局 frame 时，是否证明 coboundary 或等价的 holonomy 平凡条件；
6. 历史、合法性、记录、参考和权限是否随 transition 一起运输；
7. completion 或无穷路径是否另有实际来源存在性，而不是只有每个有限窗口相容。

其中第 1—3 项对应局部 gluing 的直接条件；第 4—5 项是 transition/frame 的额外域与 holonomy 条件，不能由 `global_frame_iff_transition_coboundary` 在任意未声明的 overlap 图上自动补出。仓内 `LocalDescentGlobalCompatibility.local_descent_requires_global_gluing_checks` 是把局部下降接回全局检查的直接形式化支点。第 6—7 项还要把历史和实际来源接回观察者过程与 completion。缺少任何一项时，最多得到局部表示或形式边界响应，不能声称空间、时间、边界和记忆已经互相恢复。

本节是对既有形式化声明的普通数学综合，没有新增 Lean 声明；局部到全局的统一构造仍按上述义务逐模型开放。

## 40.99 追加锚

## 41. §39 的定义域与双侧因式分解勘误

**本批导航。** 本节只修正上一批 §39 的表述边界，不撤回其“语义轴与解析轴正交”的主旨。修正集中在三个容易把开放综合说得过强的地方：边界更新应定义在实际像、失败分支应总化、双侧评价必须带完整因式分解数据。§27、§36 和 §38 已有的共同核与动态商判据仍是语义轴的主要来源；本节不另造同形定理。

### 41.1 共同核、当前核与实际像

若本节的 $K_*$ 被定义为包含全部合法续接、失败和记录的未来行为核，则它本身已经是一个等价关系，并且在完整未来 profile 的定义下具有动态闭合。为了避免循环，§39.1 的一般记号应作如下区分：

* $K_{\mathrm{cur}}$ 是当前表示任务声明的等价关系，可能只包含有限读数或当前标签；
* $K_{\infty}$ 是把所有声明的未来合法续接加入后的行为核；
* 精确边界的语义条件是 $\ker r=K_{\infty}$，而在只给 $K_{\mathrm{cur}}$ 时，还必须另证 $K_{\mathrm{cur}}$ 对每个动作的纤维保持。

因此，§39.1 的 `Sem ∧ Dyn` 是一个防止把当前核误报成未来核的分解写法；若 $K_*$ 已明确取 $K_{\infty}$，则 `Dyn` 应引用第36节的残余闭合结论，而不是再次当作独立假设。

同时，边界更新的唯一性只应在实际像上声称。令

$$
\bar R:=\operatorname{im}(r),
\qquad
\bar r:S\to\bar R,
\qquad
\bar r(s)=r(s).
\tag{41.1}
$$

若完整操作以总的 tagged successor 表示

$$
\widehat T_a:S\to S_a^{\mathrm{ok}}\sqcup S_a^{\mathrm{fail}},
\tag{41.2}
$$

并把合法性、指定输出和记录一并放入总标签 $\widehat L_a$，则动态下降应写成

$$
\bar r_a\circ\widehat T_a
=
\bar T_a\circ\bar r,
\qquad
\widehat L_a=\bar L_a\circ\bar r,
\tag{41.3}
$$

其中 $\bar T_a:\bar R\to\overline{R_a}$、$\bar L_a:\bar R\to L_a$ 只要求在实际像上定义。若动作由内生选择器 $\pi:S\to A$ 产生，还要加入策略下降条件

$$
\operatorname{Policy}(r):\Longleftrightarrow
r(s)=r(t)\Longrightarrow \pi(s)=\pi(t),
\tag{41.3a}
$$

或更弱地要求存在 $\bar\pi:\bar R\to A$ 使 $\pi=\bar\pi\circ\bar r$。此时内生观察者的可运行性应写成 $\operatorname{Sem}_{K_*}(r)\land\operatorname{Dyn}(r)\land\operatorname{Policy}(r)$；若动作序列是外部预先固定的，才可以省略这一项。若仍使用只在合法域上的偏函数，则 (41.3) 必须分别写在合法分支和失败分支，不能把 $r\circ T_a$ 当作全域函数。陪域 $R\setminus\operatorname{im}(r)$ 上可以任意延拓，所以那里没有唯一性内容。

### 41.2 解析与代数标签要分开

§39.2 中的“algebra completion”包含了两个强度不同的断言，应拆成

$$
\begin{aligned}
\operatorname{AlgEq}(A,\mathcal A_*)
&:\Longleftrightarrow A=\mathcal A_*,\\
\operatorname{ObsContain}(A,\mathcal O_*)
&:\Longleftrightarrow \mathcal O_*\subseteq A.
\end{aligned}
\tag{41.4}
$$

这里必须另行声明 $A$ 是哪一种 unital 或 $*$-代数、$\mathcal A_*$ 的目标代数是什么，以及 $\mathcal O_*$ 是单个 observable 还是一族 observable。`ObsContain` 由 `AlgEq` 蕴含的方向取决于 $\mathcal O_*\subseteq\mathcal A_*$，反向一般不成立。

`FourTypedCompletionHierarchy` 的窗口生成反例只支持相应的具体包含或 properness 断言；它不提供一个不带载体和量词的统一 `Algebra` 谓词。因而 §39 的 typed 数据应写成

$$
\bigl(\text{语义核},\ \text{动态下降},\ \text{Uniform/StateFamily/MemberTarget},
\ \text{AlgEq 或 ObsContain}\bigr),
\tag{41.5}
$$

而不是把两个代数命题用“或”并成一个模式。

### 41.3 双侧 quotient 的完整条件

若 $E:X\times P\to\Lambda$ 与 $E':X'\times P'\to\Lambda$ 要被证明为同一 typed interface 的两个表达，数据必须包括

$$
f:X\to X',\qquad g:P\to P',
\tag{41.6}
$$

以及明确的因式分解

$$
\boxed{
E(x,p)=E'(f(x),g(p))\quad(\forall x,p).
}
\tag{41.7}
$$

此外，需要 $f,g$ 各自满射，且 $E'$ 的状态行与协议列外延：

$$
\begin{aligned}
\bigl(\forall p',E'(x',p')=E'(y',p')\bigr)&\Longrightarrow x'=y',\\
\bigl(\forall x',E'(x',p')=E'(x',q')\bigr)&\Longrightarrow p'=q'.
\end{aligned}
\tag{41.8}
$$

在这些条件下，评价核的状态商和协议商才分别与 $X'$、$P'$ 唯一等价；仓内 `DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` 正是这一完整数据的形式化支点。$E'$ 不需要额外满射到 $\Lambda$；定理需要的是 $f,g$ 的来源满射与 (41.7) 的因式分解。

因此，§39.5 原先的有限提示应精确解释为缺条件反例：取 $E(x,p)=x\land p$ 并把协议映射压成常值时，若试图保持一个仍能区分原协议的目标评价，(41.7) 已经失败；它说明不能省略因式分解和列外延性，不能把该例当作满足双侧 quotient 定理的实例。

### 41.4 §39 的范围收束

经本节修正，§39 的新增内容只保留以下组合结论：语义核与动态运输沿第一轴比较，解析投影或窗口代数沿第二轴比较，双侧接口还要携带 (41.6)—(41.8) 的端口数据；这些轴没有自动的单调合并。§39.1 对既有共同核的复述应读作防止循环的分层说明，§39.4 对三类语义 completion 的定义应读作引用第38.1节，而不是新的形式化成果。

本勘误仍是普通数学组织，没有新增 Lean 声明；其目的只是把定义域、量词、因式分解和结论强度收回到仓内既有形式化结果真正支持的范围。

## 41.99 追加锚

## 42. 实际来源、holonomy 固定点与细化提升

**本批导航。** §40 已给出局部因子、transition coboundary 和连续 gluing 的条件。本节继续追问一个更窄但更关键的问题：局部拼接得到的 global profile 是否真的来自同一个实际来源，并且是否能沿分辨率细化继续提升。这里要区分源交叠、商后的接口交叠、一个相容 section 与一整套 frame，以及形式逆极限与实际来源实现。

### 42.1 源交叠不等于商后交叠

令实际来源被局部子集覆盖：

$$
\Omega=\bigcup_i\Omega_i,
\qquad
q_i:\Omega_i\twoheadrightarrow B_i.
\tag{42.1}
$$

在来源交叠 $\Omega_i\cap\Omega_j$ 上，若存在过渡映射

$$
t_{ij}:q_i(\Omega_i\cap\Omega_j)\to q_j(\Omega_i\cap\Omega_j),
\qquad
t_{ij}\circ q_i=q_j,
\tag{42.2}
$$

其存在的充分必要条件是

$$
\ker(q_i|_{\Omega_i\cap\Omega_j})
\subseteq
\ker(q_j|_{\Omega_i\cap\Omega_j}).
\tag{42.3}
$$

若两侧核相等，$t_{ij}$ 才在这些实际像之间双射。由同一个来源诱导的三重交叠运输自动满足

$$
t_{jk}\circ t_{ij}=t_{ik}
\tag{42.4}
$$

但等式的定义域只是实际三重交叠像。把 (42.4) 延拓到形式上可组合、却没有共同来源代表的接口点，需要另行证明域相容。

一个有限反例说明“各片都能因子化”仍不够。令

$$
\Omega=\{a,b\},\quad
\Omega_1=\{a\},\quad\Omega_2=\{b\},\quad
q(a)=q(b)=*,
$$

并令目标读出 $f(a)=0,f(b)=1$。两个局部限制的来源交叠为空，所以局部一致性条件真空成立；但全局 $f$ 不能因子化为 $\bar f\circ q$，因为同一商点 $*$ 要求两个不同值。修复方式是要求补丁对 $q$ 饱和，或直接在所有由商合并产生的接口交叠上检查 fiber-constant 条件。

### 42.2 相容 section、global frame 与 holonomy 固定点

在一个有限连通图上，给每个顶点 $i$ 一个纤维 $B_i$，给每条有向边 $e:i\to j$ 一个可逆运输 $T_e:B_i\simeq B_j$，逆边运输为 $T_e^{-1}$。取根 $v$ 和一棵生成树；令 $P_i:B_v\simeq B_i$ 为树路径运输。对每条非树边 $e:i\to j$ 定义根纤维上的 holonomy

$$
H_e:=P_j^{-1}\circ T_e\circ P_i\in\operatorname{Aut}(B_v).
\tag{42.5}
$$

所有运输相容的 section 组成

$$
\Gamma(T)=\{(b_i)_i:\ T_e(b_i)=b_j\text{ 对所有边 }e:i\to j\}.
$$

根评价给出一个规范双射

$$
\boxed{
\Gamma(T)\simeq
\bigcap_{e\notin\mathrm{Tree}}\operatorname{Fix}(H_e).
}
\tag{42.6}
$$

树边强制 $b_i=P_i(b_v)$，非树边恰好变成根值的固定点方程。由此得到三个不同结论：

* 相容 section 存在，当且仅当 holonomy 共同固定点非空；
* 每个根值都能延拓，当且仅当所有 holonomy 恒等；
* 若把“full frame”定义为根评价 $\Gamma(T)\to B_v$ 的双射（有限连通图、每条边运输可逆，并且每个根值都有唯一相容 section），则一整套 transport-compatible frame 才需要后一个更强条件。

所以“有一个全局 profile”与“局部接口之间存在可逆的全局 frame”不是同一命题。取三角形图、纤维 $\{0,1,2\}$，两条边为恒等、第三条边交换 $1,2$ 而固定 $0$，则只有全零 section，却没有 transport-compatible full frame。

若运输只有有向箭头而没有逆，闭路测试也不充分。取菱形 $v\to a\to w$ 与 $v\to b\to w$，令一条路径的复合为交换、另一条为恒等。图中没有有向闭路，但两条平行路径作用不同；正确条件是对声明的平行路径直接要求复合相等。

### 42.3 细化运输与固定点集合的逆极限

设每个分辨率 $n$ 都有纤维 $B_{i,n}$、运输 $T_{e,n}$ 和限制映射

$$
r_{i,n}:B_{i,n+1}\to B_{i,n}
$$

满足自然性

$$
r_{j,n}\circ T_{e,n+1}
=
T_{e,n}\circ r_{i,n}.
\tag{42.7}
$$

同一生成树下，(42.7) 把细层 holonomy 降到粗层 holonomy，并诱导固定点集合之间的映射

$$
F_{n+1}:=\bigcap_e\operatorname{Fix}(H_{e,n+1})
\longrightarrow
F_n:=\bigcap_e\operatorname{Fix}(H_{e,n}).
\tag{42.8}
$$

于是形式上有

$$
\Gamma\!\left(\varprojlim_n B_{\bullet,n}\right)
\simeq
\varprojlim_n\Gamma(B_{\bullet,n})
\simeq
\varprojlim_n F_n,
\tag{42.9}
$$

但 (42.9) 只是相容 section 的形式重排，不是实际来源存在性定理。

细化限制即使全都满射，也不保证全局 section 能提升。粗层取单点纤维和恒等运输，故 $F_0$ 非空；细层取三角形 bit 纤维，第三边为交换，故 $F_1=\varnothing$。每个 $r_{i,0}:\{0,1\}\twoheadrightarrow\{*\}$ 都满射且满足 (42.7)，但粗 section 没有细层提升。

### 42.4 形式 profile 的实际来源判据

固定任务索引集 $J$ 和实际 profile 映射

$$
\Phi:\Omega\to\prod_{j\in J}Y_j.
$$

每个有限或局部片上的相容选择可以拼成一个形式 profile $p=(p_j)_{j\in J}$，但

$$
\boxed{
p\text{ 实际可实现}
\Longleftrightarrow
p\in\operatorname{im}\Phi.
}
\tag{42.10}
$$

因此，普通函数的 gluing 只解决“存在一个形式函数”，不解决它是否来自同一个来源。一个最小有限反例是

$$
\Omega=\{00,11\}\subseteq\{0,1\}^2.
$$

两个坐标的局部读出都允许 $0$ 和 $1$；局部选择 $(0,1)$ 形成了良定义的全局 profile，却不在 $\operatorname{im}\Phi$ 中。

在图运输模型中，若 $r:\Omega\to\Gamma(T)$ 尊重每条运输，且根读出 $\operatorname{ev}_v\circ r:\Omega\to B_v$ 满射，则 (42.6) 的固定点集合必须等于整个 $B_v$，从而 $r$ 满射到全部相容 section。这个正向结论同时说明：不能在同一模型中既假设根值全部实际可达、又保留非平凡 holonomy 固定点限制。

### 42.5 无穷细化的交集条件

给定实际来源 $\Omega$ 和一列读出 $q_n:\Omega\to B_n$，一个相容线程 $b=(b_n)_n$ 的实际实现精确要求

$$
\bigcap_n q_n^{-1}(\{b_n\})\ne\varnothing.
\tag{42.11}
$$

若 $\Omega$ 紧、每个纤维闭、并且这些纤维按 $n$ 嵌套，紧性可保证 (42.11)。没有这类来源完备性条件，所有有限前缀都可实现仍不够。

例如令

$$
\Omega=\mathbb N,\qquad
B_n=\{0,\ldots,n\},\qquad
q_n(k)=\min(k,n).
$$

线程 $b_n=n$ 的每个有限前缀都由某个自然数实现，但不存在一个 $k\in\mathbb N$ 同时实现全部 $b_n$。这是形式逆极限与实际来源的分离；它不与有限来源的嵌套交集性质矛盾。

### 42.6 动态 gluing 还要运输策略与实际像

静态 transition 不能自动给出过程 transition。对每条边 $e:i\to j$，先明确输入/输出边界及局部数据：

$$
T_e^{\mathrm{in}}:B_i^{\mathrm{in}}\simeq B_j^{\mathrm{in}},
\quad
T_e^{\mathrm{out}}:B_i^{\mathrm{out}}\simeq B_j^{\mathrm{out}},
$$

$$
D_{i,a}\subseteq B_i^{\mathrm{in}},
\quad
O_{i,a}:D_{i,a}\to Y_a,
\quad
U_{i,a}:D_{i,a}\to B_i^{\mathrm{out}},
\quad
\pi_i:B_i^{\mathrm{in}}\to A.
$$

对每个动作 $a$，局部运输至少需要交换

$$
T_e^{\mathrm{in}}(D_{i,a})=D_{j,a},
\qquad
O_{j,a}\circ T_e^{\mathrm{in}}=O_{i,a},
\qquad
T_e^{\mathrm{out}}\circ U_{i,a}=U_{j,a}\circ T_e^{\mathrm{in}},
\tag{42.12}
$$

并且内生策略满足

$$
\pi_j\circ T_e^{\mathrm{in}}=\pi_i.
\tag{42.13}
$$

这些式子才能把局部更新诱导到相容 section 上；若输入输出边界已通过一个声明的 canonical identification 视为同一纤维，才可以把 $T_e^{\mathrm{in}}$ 与 $T_e^{\mathrm{out}}$ 简写成同一个 $T_e$。若 $r$ 是实际来源到 global profile 的映射，诱导更新还要求

$$
U_\Gamma(r(\Omega))\subseteq r(\Omega).
\tag{42.14}
$$

否则形式 section 虽有更新，实际来源像却会被送出，不能把它报告为内部观察者可执行的后继。

有限反例是：$q(a)=q(b)=0,q(c)=1$，读出当前因子通过 $q$，但令 $U(a)=a$、$U(b)=U(c)=c$。同一摘要类 $q(a)=q(b)$ 的后继类不同，所以不存在边界更新；静态 factorization 不提供动态 descent。

本节把局部 gluing、holonomy、细化和实际来源放在同一条证明链上，但没有把它们自动合成无限模型的全局存在定理。相关具体来源、拓扑和策略条件仍须逐模型核对；本节是普通数学综合，Claim status 为 open。

## 42.7 共同任务商上的有限动态恢复群胚

第 36 节给出共同未来行为核，第 40 节给出局部 transition 与 cocycle，第 42.1—42.6 节分别说明实际来源、holonomy 和动态 gluing 的附加条件。本节把三者接成一个有限桥；它仍只在声明的实际来源和任务上成立。

设 $S$ 是有限实际来源，$W$ 是带完整失败、输出、记录和后继标签的有限动作词族，令

$$
\Phi_W(s)=\bigl(\operatorname{Resp}(s,w)\bigr)_{w\in W},
\qquad
K=\ker\Phi_W,
\qquad
Q=S/K.
\tag{42.15}
$$

记自然商映射为 $q:S\to Q$，即 $q(s)=[s]_K$。

取四个局部表达图表 $S_i\subseteq S$，其中

$$
S=\bigcup_iS_i,
\qquad
i\in\{\mathrm{sp},\mathrm{tm},\partial,\mathrm{mem}\}.
$$

每个图表给出

$$
e_i:S_i\to R_i,
\qquad
R_i=e_i[S_i],
$$

并要求

$$
\ker e_i=\ker(q|_{S_i}),
\qquad
Q_i:=q[S_i].
\tag{42.16}
$$

假设每个动作的合法域、完整标签（包括输出、失败、记录和时钟）、档案更新、选择器和后继都在 $e_i$ 的纤维上常值，从而完整请求合同在 $R_i$ 上下降。定义

$$
d_i:R_i\longrightarrow Q_i,
\qquad
d_i(e_i(s))=q(s).
\tag{42.17}
$$

则每个 $d_i$ 都是双射：良定性来自(42.16)，满射来自 $R_i=e_i[S_i]$，单射则由相同 $K$ 纤维得到。当所有 $Q_i=Q$ 时，四个图表才共同覆盖同一个全局任务商；一般情形只得到局部商图册。

### 命题 42.8（实际重叠上的恢复器群胚）

令 $\mathcal G$ 是四个表达的有限局部接口群胚。对每条边 $i\to j$ 令

$$
S_{ij}=S_i\cap S_j=S_{ji}
$$

是实际重叠，并要求它对 $K$ 饱和；在实际重叠像上定义

$$
t_{ij}:e_i[S_{ij}]\longrightarrow e_j[S_{ij}],
\qquad
t_{ij}(e_i(s))=e_j(s).
\tag{42.18}
$$

则：

1. $t_{ij}$ 良定且唯一，并且是双射，逆为 $t_{ji}$；在共同三重重叠上有
   $$
   t_{jk}\circ t_{ij}=t_{ik}.
   \tag{42.19}
   $$
2. 在输入、输出边界已经通过声明的 canonical identification 视为同一重叠纤维的记号下，若局部下降数据满足
   $$
   t_{ij}(D_{i,a})=D_{j,a},
   \qquad
   O_{j,a}\circ t_{ij}=O_{i,a},
   \qquad
   t_{ij}\circ U_{i,a}=U_{j,a}\circ t_{ij},
   \qquad
   \pi_j\circ t_{ij}=\pi_i,
   \tag{42.20}
   $$
   则每条路径的 $t_\gamma$ 都是保持合法性、读数、记录、策略和后继的动态态射。
3. 对实际来源诱导的闭路，$t_\gamma$ 在其实际重叠像上恒等；等价地，若改用共同商坐标，则
   $$
   t_\gamma=d_i^{-1}\circ d_i=\operatorname{id}_{q(S_\gamma)}
   \tag{42.21}
   $$
   在其定义域上成立，其中 $S_\gamma$ 是该闭路的实际来源交叠。若 transition 只在形式接口上给出，则必须另加 holonomy 在目标商 $q(S_\gamma)$ 上平凡以及实际来源像闭合；不能由形式闭路自动推出实际闭路平凡。

证明。若 $e_i(s)=e_i(s')$，则 $sKs'$，由 $S_{ij}$ 的饱和性可取同一重叠类代表，(42.16) 给出 $e_j(s)=e_j(s')$，所以(42.18) 良定。交换 $i,j$ 得逆与唯一性。三重重叠上，两种复合都把 $e_i(s)$ 送到 $e_k(s)$，得到(42.19)。式(42.20) 逐边保持动作的完整响应，沿路径归纳即可。闭路时同一来源类在 $Q$ 中望远镜回到自身，得到(42.21)。

反向地，若给定一个共同商 $Q$、四个双射 $d_i:R_i\simeq Q$、满足(42.19)的 transition、式(42.20)的动态自然性，以及每个实际像对后继闭合，则对任意满射 $q:S\twoheadrightarrow Q$ 定义

$$
e_i=d_i^{-1}\circ q.
\tag{42.22}
$$

这些表达具有共同核 $\ker q$，恢复器唯一为 $d_j^{-1}\circ d_i$，并满足上述动态运输。这里的实际像闭合是必要条件；没有它，商上虽有更新，来源表达却可能被送出 $e_i[S_i]$。若 $Q_i$ 只覆盖 $Q$ 的局部子集，则反向构造只能得到局部图册；要得到四个全局表达，必须另加 $Q_i=Q$ 及所有声明后继的源闭合。
$\square$

当完整行为核在深度 $d$ 稳定时，$K$ 可替换为第 $d$ 层有限 horizon kernel；于是群胚的验证只需检查有限 profile、有限重叠和有限条动态交换式。这一点与仓内 `ControlledCompletion`、`BehaviorCompletionMinimality`、`FiniteHorizonKernelRecurrence` 和 `PredictiveMemoryMinimalQuotient` 的接口相吻合；这些形式化声明提供的是因子化、稳定性和唯一下降的支点，本命题本身仍是理论层综合，没有新增 Lean 声明。

这个群胚桥给出“空间、时间、边界和记忆是同一关系的不同表达”的严格读法：它们不是四个任意同构的数据表，而是同一共同任务商上的四个实际坐标，以及在实际重叠上满足 cocycle、动态自然性和来源闭合的运输系统。

## 42.99 追加锚

## 43. 活性边界：鲁棒安全核与反复更新

**本批导航。** 前面的动态商保证摘要可以继续执行一项或有限串动作；它没有说明观察者能否在任意对手后继下永远留在安全域，并且无穷次回到一个允许继续校准、读取或换参考的更新集合。本节把这个缺口写成有限控制系统中的 Büchi 活性条件。它补充一阶 descent，不把“能继续一步”冒充“能无限运行”。

### 43.1 安全前驱与反复更新核

设 $S$ 是有限配置集。对每个 $s$，$A(s)$ 是非空合法动作集；动作 $a$ 的对手后继集合记为

$$
\operatorname{Succ}(s,a)\subseteq S,
\qquad
\operatorname{Succ}(s,a)\ne\varnothing.
$$

对 $Y\subseteq S$ 定义鲁棒控制前驱

$$
\operatorname{CPre}(Y)
=
\{s:\exists a\in A(s),
\operatorname{Succ}(s,a)\subseteq Y\}.
\tag{43.1}
$$

安全核是最大的前向不变集合

$$
\operatorname{Safe}:=\nu Z.\operatorname{CPre}(Z).
\tag{43.2}
$$

再指定一个 renewal 集 $R\subseteq S$，它表示校准、取得新端口、写入必要记录或其它允许循环的状态。对固定 $X$ 定义相对吸引子

$$
\operatorname{Attr}_{X}(G)
:=
\mu Y.\bigl(G\cup(X\cap\operatorname{CPre}(Y))\bigr),
\tag{43.3}
$$

并定义反复更新核

$$
\boxed{
\operatorname{Live}(R)
:=
\nu X.\operatorname{Attr}_{X}\bigl(R\cap\operatorname{CPre}(X)\bigr).
}
\tag{43.4}
$$

在有限状态、有限分支和非空合法动作的条件下，$\operatorname{Live}(R)$ 中的配置有一个位置策略，使所有对手路径满足

$$
\square\operatorname{Safe}
\quad\land\quad
\square\Diamond R.
\tag{43.5}
$$

这里 $\square\Diamond R$ 的量词是“对每个路径、任意 $N$，存在 $n\ge N$ 使状态落在 $R$”；它不是一个有限窗口里已经发生一次 renewal 的声明。仓内 `BuchiAgencyKernel.live_agency_buchi_kernel` 在有限控制模型中给出 live 到安全策略、秩下降和无限 renewal 的对应结构；本节把其条件改写成边界语言，未把它外推到无限状态或无限分支。

### 43.2 秩证书与最小边界需要的附加标签

有限不动点迭代可以为每个 live 状态附一个自然数秩。非 renewal 步骤沿所选策略严格降低秩，进入 $R\cap\operatorname{CPre}(X)$ 后重新获得一个可继续的 live 状态。因此，策略不是一个只返回“允许/拒绝”的静态标签；它还需要知道合法动作、对手后继的安全闭包，以及 renewal 是否已经发生。

令 $q:S\to B$ 是候选边界。要在 $B$ 上实现 (43.5)，至少需要：

$$
q(T_a s)=\bar T_a(qs)
\tag{43.6}
$$

对所有被选动作及其实际后继成立；安全谓词和 renewal 谓词在 $q$ 的实际纤维上恒定；并且存在边界策略 $\bar\pi:B\to A$ 使

$$
\pi=\bar\pi\circ q.
\tag{43.7}
$$

若同一 $q$-纤维内有两个配置需要不同动作才能保证所有后继留在安全核，(43.7) 失败，即使 (43.6) 对一个预先固定动作成立，也不能得到内部观察者可执行的 Büchi 策略。若 renewal 标记在同一纤维内一真一假，边界也无法判断何时重置秩；这不是时钟精度问题，而是边界漏掉了活性关系。

因此，动态充分性现在分成三层：

$$
\boxed{
\text{单步下降}
\Rightarrow
\text{安全闭包}
\Rightarrow
\text{安全且无限 renewal 的策略闭包}.
}
\tag{43.8}
$$

右侧两个蕴含都需要新增条件，不能由普通的状态商自动推出。

### 43.3 一阶精确而活性失败的有限反例

取 $S=\{0,1\}$，每个状态只有一个动作，且

$$
F(0)=1,
\qquad
F(1)=1,
\qquad
R=\{0\}.
\tag{43.9}
$$

取 $q=\operatorname{id}_S$。它当然满足当前读出和后继的精确下降，安全核是 $S$，但任何路径至多一次经过 $0$，所以

$$
\operatorname{Live}(R)=\varnothing.
$$

这个例子排除了“边界已经无损”便自动得到持续活性的推论。反向地，若把 $R=S$，同一个更新就满足 $\square\Diamond R$；活性取决于声明的 renewal 任务，而非单靠更新图的名称。

若把 $q$ 改成常值摘要，(43.6) 甚至已经失败，因为两个状态的后继在摘要外的 renewal 关系不同。若把 renewal 标签并入 $q$，静态摘要可能恢复该标签，但仍需检查策略因子化和所有对手后继。仓内 `DeterministicSafePolicyExistence.deterministic_safe_policy_exists_iff` 给出每个纤维有共同合法安全动作与存在安全策略之间的有限判据；`BoundaryRelativeAgency.boundary_relative_agency` 与 `ActionLoopRequiresMemory.policy_change_implies_memory_change` 则分别说明隐藏决策和循环中的策略变化不能免费从粗边界恢复。

### 43.4 反复更新与空间、时间、记忆

在统一读法中，空间是 $S$ 的局部配置载体，时间是策略路径的前缀序，边界是保持 (43.6)—(43.7) 的商，记忆则至少保存 renewal 标签和策略所需的秩或其等价残余。时钟读数可以记录路径长度，却不能单独替代秩：仓内 `ClockTimeVersusRefinementDepth.clock_time_does_not_determine_refinement_depth` 的一状态任意计时与延迟四状态例子，已经给出时钟步数和预测细化深度不相等的有限见证。

本节的普通数学结论只覆盖有限状态、有限分支、非空动作和已声明的安全/renewal 语义。无限状态、概率几乎处处活性、随机策略的种子来源和资源受限的可取得性需要分别建立量词与接口；它们不能由 (43.4) 的符号自动补上。Claim status: open；没有新增 Lean 声明。

## 43.99 追加锚

## 44. 自适应取得的成本与被动联合边界

**本批导航。** 活性核回答“是否能一直运行”，但没有回答“用多少次实验才能得到目标”。本节把被动联合读出、历史自适应策略和取得成本分开：自适应可以改变成本，却不能在固定实验族之外创造被动联合边界没有的区别。

### 44.1 被动联合边界和策略转录

设有限实际来源为 $S$，实验族为 $E$，每个实验 $e$ 有响应类型 $Y_e$ 和读出

$$
\rho_e:S\to Y_e.
$$

把同一来源上的全部被动读出合成

$$
J:S\to\prod_{e\in E}Y_e,
\qquad
J(s)=(\rho_e(s))_{e\in E}.
\tag{44.1}
$$

一个确定的深度 $N$ 策略由历史选择器

$$
\pi_t:\prod_{u<t}Y_{\pi_u}\to E,
\qquad 0\le t<N,
$$

给出；其实际转录为

$$
\tau_\pi(s)=
\bigl(\rho_{\pi_0}(s),\ldots,
\rho_{\pi_{N-1}}(s)\bigr).
\tag{44.2}
$$

归纳可构造唯一函数 $\bar\tau_\pi$ 使

$$
\boxed{
\tau_\pi=\bar\tau_\pi\circ J.
}
\tag{44.3}
$$

第一步由 $J$ 的相应坐标给出；若前 $t$ 个响应相同，选择器给出同一实验，下一坐标仍由 $J$ 给出。因而任何只使用这组被动实验的自适应转录，都不会切开 $J$ 的纤维。

若目标 $T:S\to Z$ 不满足 $T=g\circ J$ 的因式分解，则不存在这类策略的转录 $\tau_\pi$ 能精确识别 $T$。仓内 `PassiveAdaptiveTranscriptUpperBound.passive_adaptive_transcript_upper_bound` 和 `ExperimentBoundary.PassiveJointBoundaryObstruction.adaptive_cost_reduction_and_passive_boundary` 给出这一上界；`ProtocolInnovationCriterion.protocol_innovation_iff_separates_current_fiber` 则把加入一个新协议真正带来新分辨率精确化为“存在同一当前纤维而新协议值不同”的成对见证。

### 44.2 成本是另一种路径读出

给每个实验一个非负费用 $c(e)$，策略在来源 $s$ 上的费用为

$$
C_\pi(s)=\sum_{t=0}^{N-1}c(\pi_t(\text{history}_t(s)));
\tag{44.4}
$$

若协议允许提前停止，$N$ 换成由转录决定的停止时刻 $\tau_\pi(s)$。两个策略可能有相同的被动边界 $J$、相同的目标恢复能力，却有不同的 $C_\pi$；因此“边界充分”与“取得便宜”是两个偏序。

四状态余数模型给出具体分离：只允许模 $2,3,5$ 三个被动传感器时，固定套件要三项才精确，而先问模 $2$、再按首个答案选择模 $3$ 或模 $5$ 的自适应树在两轮内精确。仓内 `AdaptiveResidueIdentification.two_step_adaptive_residue_identification` 证明深度 $2$ 与静态基数 $3$ 的严格差异；`AdaptiveEarlyStopping.expected_experiment_count_eq_one_add` 及其严格小于二的条件进一步说明期望查询数要以先验和停止协议为参数，不能由边界类数直接读出。

### 44.3 何时自适应真的扩大边界

若实验族本身随控制器、参考或隐藏随机种子改变，(44.1) 中的来源必须扩大为联合配置 $S'=S\times R\times K$，并把相应的合法性、种子和参考读出纳入 $J'$. 否则把控制器当作免费外部输入，会错误地把不同实际来源拼成一个策略。

一个新协议 $\ell$ 只有在

$$
\ker(J\mathbin{\times}\ell)\subsetneq\ker J
\tag{44.5}
$$

时才增加被动边界的分辨率；若只是 $\ell=g\circ J$ 的后处理，它不增加目标信息。即使 (44.5) 成立，协议仍可能无法在实际接口取得，或其费用使它在给定预算内不可行。于是新区别的三项判据应分别写成：

$$
\boxed{
\text{切开旧纤维}
\quad+
\text{合法取得}
\quad+
\text{预算内可执行}.
}
\tag{44.6}
$$

### 44.4 范围

本节只在有限确定性实验族、共同来源和显式停止/费用合同下给出普通推导。随机实验、未知通道、测量反作用和连续目标需要把概率核、后继和成本一起纳入实际配置；不把自适应成本例子外推成一般信息论最优定理。Claim status: open；没有新增 Lean 声明。

## 44.99 追加锚


## 45. 双端口相对相位：联合最小边界与分开保存的严格差距

**本批导航。** 第36节的共同核判据已经回答表示之间何时存在恢复器，主卷第124.9节也已经处理存在性商、分支相容与有限路径提升。这里不把这些既有机制再命名为新一般定理，而给出一个可直接计算的双端口模型：空间关系、带校准的相对时钟、未来边界和有限记忆都由一个循环差值恢复；但把左右端口分别摘要再拼接，需要严格更多的联合代码。所需的差别来自允许怎样取得和存储关系，而非给同一个状态改名。本节是既有行为商方法的一项有限经典综合应用，Claim status: open；没有新增 Lean 核验，不声明文献原创。

### 45.1 固定来源、动作及需要保留的任务

固定整数 $n\ge2$，所有加减在循环群 $G=\mathbb Z/n\mathbb Z$ 内进行。实际联合配置取全部

$$
S=G\times G,
\qquad s=(x,y).
\tag{45.1}
$$

左右端口分别允许操作

$$
L(x,y)=(x+1,y),
\qquad
R(x,y)=(x,y+1).
\tag{45.2}
$$

二者在全部配置上合法；另允许不改态的读取操作 $Q$，其读数为相等性

$$
e(x,y)=\mathbf1_{\{x=y\}}.
\tag{45.3}
$$

研究任务固定为：当前相等性和任意有限 $L,R$ 词继续执行后可取得的相等性记录，并保留实际协议中的动作及读取先后标签。移动与读取是分别计费的操作，未执行 $Q$ 的位置不产生免费读数。左右绝对坐标不是本任务的读出；把它们加入实验族会改变下面的最小商。外部选择某个词只用来定义响应，内部控制器若选择下一步，仍须从实际可访问的记忆作决定。

对词 $w\in\{L,R\}^{*}$，$N_L(w),N_R(w)$ 是两种动作的出现次数。令

$$
d(x,y)=x-y,
\qquad
k(w)=N_L(w)-N_R(w)\pmod n.
\tag{45.4}
$$

逐步执行直接给出

$$
T_w(x,y)=\bigl(x+N_L(w),y+N_R(w)\bigr),
\qquad
 d(T_ws)=d(s)+k(w).
\tag{45.5}
$$

因此一个差值寄存器支持全部未来响应：对词的每个前缀 $v$，对应读数为 $\mathbf1_{\{d(s)+k(v)=0\}}$。这里只用 $k(w)$ 恢复最终读数；恢复完整读数序列需要逐前缀的 $k(v)$，动作次序不能仅由总计数恢复。

### 45.2 恰有 $n$ 个未来行为类

若两配置差值相同，(45.5) 使任何相同动作词的每个前缀读数都相同。反向，若 $d(s)=a\ne b=d(t)$，选择 $j\in\{0,\ldots,n-1\}$ 满足 $j=-a\pmod n$。在词 $L^j$ 后读取相等性，则

$$
e(T_{L^j}s)=1,
\qquad
e(T_{L^j}t)=\mathbf1_{\{b-a=0\}}=0.
\tag{45.6}
$$

所以本任务的未来等价关系准确是

$$
s\equiv t\iff d(s)=d(t),
\qquad
|S/\!\equiv|=n.
\tag{45.7}
$$

任意支持全部这些续接的确定性摘要都必须区分全部 $n$ 个差值，差值寄存器达到这个下界。所需最坏二进制存储至少 $\lceil\log_2n\rceil$ 位；这只是表示容量，不计取得初值、操作执行或策略搜索的成本。

相同核的另一个具体来源是共同平移作用

$$
g\cdot(x,y)=(x+g,y+g).
\tag{45.8}
$$

一条轨道内差值不变；若差值相同，取 $g=x'-x=y'-y$ 就把 $(x,y)$ 送到 $(x',y')$。因而共同平移的轨道恰为行为类。空间读法可以是这个已声明对称作用下的相对位置，既不保留绝对位置，也不把任意空间几何预设为循环群。

### 45.3 四种表达的显式恢复器与动态交换

在一份实际历史 $(s_0,w)$ 上，令 $s=T_ws_0$。四个表示具体取为

$$
\begin{aligned}
r_{\mathrm{sp}}(s_0,w)&=[s]_{G},\\
r_{\mathrm{tm}}(s_0,w)&=d(s_0)+k(w),\\
r_{\partial}(s_0,w)&=\left(e(T_vs)\right)_{v\in\{L,R\}^{*}},\\
r_{\mathrm{mem}}(s_0,w)&=m_w,
\end{aligned}
\tag{45.9}
$$

其中实际记忆按

$$
m_{\varepsilon}=d(s_0),
\qquad
m_{wL}=m_w+1,
\qquad
m_{wR}=m_w-1
\tag{45.10}
$$

更新。时间表达是有初始参考的相对 tick 相位；它不声称恢复完整历史顺序、经过步数或物理时长。记忆初值须由允许的准备、校准或查询取得；(45.10) 的数学定义不授予控制器读取未知 $d(s_0)$ 的能力。

四个实际像都可以显式恢复 $d(s)$：空间轨道经 $[(x,y)]_G\mapsto x-y$；相对时钟和记忆直接读取其值；边界表则在 $j=0,\ldots,n-1$ 中寻找唯一满足 $e(T_{L^j}s)=1$ 的 $j$，并返回 $-j$。反向从 $a\in G$ 取轨道代表 $(a,0)$、相位 $a$、寄存器 $a$，以及响应

$$
v\longmapsto\mathbf1_{\{a+k(v)=0\}}
\tag{45.11}
$$

即可恢复四个表示的实际值。唯一命中是边界函数的有限坐标计算，并非免费得到这整张表的物理实验；实际查询要按更新后的状态解释读数。

各恢复器都把 $L$ 送到 $a\mapsto a+1$，把 $R$ 送到 $a\mapsto a-1$。所以不仅当前值可互算，动作更新也交换。此处 (45.2) 与 (45.5) 履行了第36节额外要求的动态下降，而不是由当前相等性相同直接推出后继闭合。

对内部策略，若选择器为 $\bar\pi:G\to\{L,R\}$，四表达中的恢复器都执行相同选择。若选择器读取绝对的 $x$ 或 $y$，则其信息超过 (45.9)，需重新检验动作选择能否在差值纤维上下降；不能把该选择器当成免费的外部输入。

### 45.4 分开编码的代价不能由联合最小性消去

现在增加一项取得结构限制：左右各自产生确定性消息

$$
u:G\to U,
\qquad
v:G\to V,
\tag{45.12}
$$

且接收者只取得消息对 $(u(x),v(y))$。要求一份统一解码器在全部 $G\times G$ 上恢复当前相等性，已经足以迫使 $u,v$ 都单射。

确实，若 $u(x)=u(x')$ 且 $x\ne x'$，比较实际配置 $(x,x)$ 与 $(x',x)$：消息对完全相同，相等性却分别为一和零，矛盾。右侧交换角色即可。因此

$$
|\operatorname{im}u|\ge n,
\qquad
|\operatorname{im}v|\ge n,
\qquad
\bigl|\{(u(x),v(y)):(x,y)\in S\}\bigr|\ge n^2.
\tag{45.13}
$$

最后一项使用了 (45.1) 中全部配对都实际允许的前提；它不是在受限共同来源中把不可达消息对也算进去。直接保留 $x,y$ 达到全部三个下界，并且支持后续动作。

于是同一个任务有严格差距：联合可计算边界只需 $n$ 类，而先独立编码两侧再拼接的精确消息对至少有 $n^2$ 个实际值。在各自使用固定长度二进制存储的方案中，两侧分别至少需要 $\lceil\log_2n\rceil$ 位；不能把联合边界的一个寄存器同时当成两个端口各自免费可取得的本地寄存器。

这个差距不是新增信息被创造出来。共同平移改变两端的绝对坐标，却不改变任务；联合差值可以消去这一冗余。但在确定另一端之前，单侧不能判断自己哪两个值可被合并：对手端取其中一个值，就能用相等性区分它们。若允许通信、共享初始校准、受限来源或误差，合同已经改变，(45.13) 的当前下界不能直接搬用。

### 45.5 有限边界递推及计数重数

以列表示旧差值、行表示新差值，取 $n\times n$ 置换核

$$
K_L(a',a)=\mathbf1_{\{a'=a+1\}},
\qquad
K_R(a',a)=\mathbf1_{\{a'=a-1\}}.
\tag{45.14}
$$

对联合配置上的有限权重 $h(x,y)$，边界响应为

$$
H(a)=\sum_{x-y=a}h(x,y).
\tag{45.15}
$$

把微观权重沿 $L$ 或 $R$ 推前，再按差值汇总，等于先用 (45.15) 汇总再用相应 $K$ 更新；这是因为每个共同平移轨道被双射送到下一差值轨道。因而

$$
H'=K_LH\quad\text{或}\quad H'=K_RH,
\qquad
K_w=K_{a_k}\cdots K_{a_1}.
\tag{45.16}
$$

当前相等性只读取 $H(0)$，而未来任意词把其他坐标搬到零，因此不能只保存 $H(0)$。若 $h\equiv1$，每个差值有恰好 $n$ 个微观实现，所以 $H(a)=n$，总实现数为 $n^2$。行为状态有 $n$ 类，不意味着每类的实现权重可以改为一；商的类数与内部计数由不同任务决定。

(45.14)—(45.16) 在任意交换半环中可用相应有限汇总解释：布尔值保存可行性，自然数保存重数，非负实数保存质量。概率更新以同一准备的联合律为起点。把两侧边缘先相乘只在已声明独立准备时成立，不能由差值响应的存在性推导独立性。

### 45.6 完整协议窗口的稳定深度

再固定移动窗口 $r\ge0$，比较所有长度不超过 $r$ 的 $L,R$ 续接词及其末端的一次 $Q$ 读数；这里的窗口深度只计移动，不把末端读取混入词长。它们可达到的净相位恰为整数区间 $[-r,r]$ 在 $G$ 中的像；设该集合为 $A_r$。每个 $d\in A_r$ 都被某个唯一命中的相等性测试与其余差值区分；不在 $A_r$ 内的差值，对全部窗口测试都回答零，因此暂时归为一类。于是窗口行为类数为

$$
c_r=|A_r|+\mathbf1_{\{A_r\ne G\}}
    =\min\{n,2r+2\}.
\tag{45.17}
$$

这里 $A_r=-A_r$，所以用 $d\in A_r$ 或 $-d\in A_r$ 判断可命中是同一条件。每个 $|k|\le r$ 可用全 $L$ 或全 $R$ 的词实现，长度为 $|k|$；任意更一般词的净位移也落在这个区间，给出所用集合的两方向。

因此完整窗口第一次得到全部 $n$ 个行为类的深度恰为

$$
r_* =\left\lceil\frac{n-2}{2}\right\rceil
    =\left\lfloor\frac{n-1}{2}\right\rfloor.
\tag{45.18}
$$

$n=2$ 时当前相等性已经区分两个差值，故 $r_*=0$；其余情形在 $r<r_*$ 时至少两个未命中差值同类，在 $r_*$ 时每类已唯一，之后永久稳定。仓内 `ControlledFiniteStability.controlled_finite_stability` 为有限控制词提供一般稳定性与类数上界；本模型以动作集 $\{L,R\}$、二值满射读出和有限状态集履行其前提，(45.17)—(45.18) 给出此循环族的精确剖面。

这个 $r_*$ 是完整分支实验族的最大词长，不是沿一条未知来源实际取得全部区别所需的读数次数。数学上同时拥有全部短词响应，与一次运行中只能选择下一项合法操作，是不同的取得合同。

### 45.7 从相等性接口实际取得相位

初始差值未知时，可以只用本模型声明的动作与读数校准寄存器。依次在已执行 $0,1,\ldots,n-2$ 次 $L$ 后读取相等性。一旦第 $j$ 次推进后的读数为一，就识别 $d(s_0)=-j$，当前差值为零；若全部 $n-1$ 次读数为零，唯一剩余初值为一，当前差值为 $n-1$。两种分支都能写入正确的当前 $m$，并从此按 (45.10) 更新。最坏使用 $n-1$ 次读取和 $n-2$ 次 $L$。

在允许确定性自适应选择 $L,R$、没有其他读数的合同下，$n-1$ 也是最坏读取次数下界。固定一个共同历史，每次读相等性只测试一个候选初始差值：已执行词的净相位 $k$ 由历史确定，读数为一恰在 $d(s_0)=-k$。沿始终返回零的分支，每次最多排除一个候选；少于 $n-1$ 次读取后至少两个初值还给出同一记录。在这条共同分支上，它们经历相同平移，当前差值仍不同，(45.6) 又说明不能合并成同一精确未来状态。因此任何对全部初态正确的协议都必须允许至少 $n-1$ 次读取。这个计数按一次读数为一次查询，不把可能很长的移动序列算成免费物理时间；上面的实现另外给出其移动次数。

这同时分离四项资源：完整协议窗口深度为 $\lfloor(n-1)/2\rfloor$，取得相位的最坏查询数为 $n-1$，已校准的当前预测记忆只需 $n$ 个状态，独立预编码双端口的实际消息对需要 $n^2$ 个值。四者在同一有限关系模型中各有明确量词，不能互换为一个“信息量”。若校准控制器需要保留查询索引或原始初值，这些准备阶段的控制及档案须另计；校准完成后只保留当前 $m$，是因为本节任务不要求恢复完整旧记录。

### 45.8 三个边界反例与可继续验证的问题

取 $n\ge3$。差值 $1$ 与 $2$ 的当前相等性都为零，但后接 $R$ 后分别为一和零。因此只保留当前相等性位，不能定义统一的下一读数。长度、输出总量或熵若同样合并这两个状态，也不能替代本任务的 $n$ 类边界。

其次，固定相同动作词 $w$ 却让初始差值分别为零和一，净 tick $k(w)$ 完全相同，最终差值却不同。去掉初始参考 $d(s_0)$ 后，相对 tick 数不能恢复空间轨道或未来响应。若参考未知且没有任何取得接口，(45.9) 的四向恢复只描述数学坐标的对应，未成为内部观察者可执行的恢复协议。

再次，从相同初态出发，词 $\varepsilon$ 与 $L^n$ 具有相同末端配置、差值、相位和未来响应，但完整已发生的动作档案不同。因此 (45.10) 只保留继续执行本任务所需的最小记忆，不恢复完整历史。将“读取全部旧档案”加入任务后，长度任意的词记录不能再由这 $n$ 个记忆值恢复。

本节把四表达互相恢复落实到一份可算的关系不变量，同时留下一个明确研究接口：给定端口访问方式和共同来源，联合行为商能否由各端口独立取得的摘要实现，不能只看共同核大小。需要同时核对局部取得、共同参考、实际消息对、动作下降和记录任务。这里已经得到有限循环族的精确 $n$ 对 $n^2$ 差距；对一般耦合关系、交互通信与带误差恢复，仍须按各自接口建立下界与实现，不由本例自动外推。Claim status: open。

## 45.99 追加锚


## 46. 对角来源上的动态记忆分配与共享控制位冗余

**本批导航。** 第45节使用全部端口对作为实际来源，得到联合差值边界与分开编码的差距。本节改变并明确固定来源：两端保证持有同一个三位状态，任务只在这份实际对角来源上恢复当前状态，不要求判定来源外的输入是否合法。这个合同允许多种互补编码；加入局部更新闭合后，某个控制位却必须在两端重复保存。具体结论是三位模型的六种局部稳定核及状态数 Pareto 前沿 $(8,1),(4,4),(1,8)$，并推广为任意 $d$ 个数据位共享一个控制位的精确资源前沿。本节给出有限经典综合推导，Claim status: open；没有新增 Lean 核验，不作文献原创性声明。

### 46.1 共同来源、目标与无通信局部更新合同

令

$$
V=\mathbb F_2^3,
\qquad z=(a,b,c),
\qquad e_a=(1,0,0),\quad e_b=(0,1,0),\quad e_c=(0,0,1).
\tag{46.1}
$$

所有加法均按位模二。实际联合来源和目标是

$$
C=\{(z,z):z\in V\}\subset V\times V,
\qquad
T(z,z)=z.
\tag{46.2}
$$

有八个实际来源，而不是六十四个独立端口对。对 $C$ 外的输入，本任务没有定义目标，也不要求观察者检测它们。对角关系作为准备合同给定，其建立、复制和认证成本不在下面的记忆计数中。

允许的五项动作是三个基平移以及两个读出控制位后重写状态的映射：

$$
\begin{aligned}
\tau_a(z)&=z+e_a,&
\tau_b(z)&=z+e_b,&
\tau_c(z)&=z+e_c,\\
N_a(a,b,c)&=(c,0,0),&
N_b(a,b,c)&=(0,c,0).
\end{aligned}
\tag{46.3}
$$

每项动作 $f$ 同步作用于两端，$(z,z)\mapsto(fz,fz)$，因此全部动作在 $C$ 上合法并保持同一来源约束。$N_a,N_b$ 可以非可逆；本节不假设整体信息守恒，也不要求由更新后状态恢复已被擦除的过去。

两份局部编码是取实际像的确定性映射

$$
u:V\twoheadrightarrow U,
\qquad
v:V\twoheadrightarrow W.
\tag{46.4}
$$

要求存在一份目标解码器 $D$，在实际消息像上满足

$$
D(u(z),v(z))=z\qquad(z\in V).
\tag{46.5}
$$

此外，每侧只能用自身当前摘要及共同收到的具名动作更新，不能在更新时重新读出整个原状态或向另一侧取数。准确地说，对每个 $f$ 都须有

$$
u\circ f=\bar f_U\circ u,
\qquad
v\circ f=\bar f_W\circ v.
\tag{46.6}
$$

这些等式对全部 $z$、每个已声明动作分别成立，不能靠把动作选择限制到某个有利来源子集来规避。动作标签本身不另编码未知的 $z$。若选择下一动作的控制器需要额外记忆、公共时钟或旧档案，应把该访问纳入接口与资源；以下只计算 (46.4)—(46.6) 的固定状态编码。

### 46.2 受限来源不要求整个矩形都合法

一般地，给定 $C\subseteq X\times Y$ 和 $T:C\to Z$，消息对能够恢复目标的条件只是：对任意 $(x,y),(x',y')\in C$，

$$
u(x)=u(x'),\quad v(y)=v(y')
\quad\Longrightarrow\quad
T(x,y)=T(x',y').
\tag{46.7}
$$

即每个代码矩形与 $C$ 的交上目标常值。它不要求该矩形全部包含在 $C$ 中，也不要求恢复 $C$ 的指示函数。过程卷定理3.5的实际联合比较载体已经区分这两个范围；这里采用的是 $C$ 内的目标恢复。

在一位对角来源 $C_1=\{(0,0),(1,1)\}$、目标 $T(i,i)=i$ 上，$(u,v)=(\operatorname{id},*)$ 与 $(*,\operatorname{id})$ 都精确，并且互不细化。它们共同的进一步粗化 $(*,*)$ 不能恢复目标，因此不存在同时比所有精确编码对都粗的唯一编码对。若另要求在全部四个端口对上判定是否相等，则两侧都必须区分零与一；那是另一个带来源外判定的任务。

三位模型同样保留这种资源互补。接下来增加的不是新的全矩形合法性要求，而是 (46.6) 的逐侧动态闭合。

### 46.3 平移与两项重写共同允许的六种核

对任一局部编码 $u$，记 $z\sim_u z'$ 当且仅当 $u(z)=u(z')$。由于三个基平移是对合，(46.6) 蕴含所有平移双向保持 $\sim_u$。令

$$
H_u=\{h\in V:h\sim_u0\}.
\tag{46.8}
$$

于是 $H_u$ 是加法子群，也就是 $\mathbb F_2$ 子空间，且

$$
z\sim_u z'\quad\Longleftrightarrow\quad z-z'\in H_u.
\tag{46.9}
$$

平移不变等价关系由子群陪集描述，是标准群论机制；本有限模型中可直接核对：若 $h,k\sim_u0$，平移 $k$ 给 $h+k\sim_uk$，再由传递性得 $h+k\sim_u0$；把任意一对同时平移 $-z'$ 则给 (46.9)。因此没有预先假设编码是线性函数，任意满足平移闭合的确定性编码都落入这个分类。

由于 $N_a,N_b$ 线性，它们在陪集商上良定义恰要求

$$
N_aH_u\subseteq H_u,
\qquad N_bH_u\subseteq H_u.
\tag{46.10}
$$

若 $H_u$ 包含某个 $h=(a,b,1)$，两项包含式给 $e_a,e_b\in H_u$，再由 $h+ae_a+be_b=e_c$ 得 $H_u=V$。否则 $H_u$ 中每个向量的第三位都是零。因此所有稳定核精确是

$$
\boxed{
H\le V_0:=\operatorname{span}\{e_a,e_b\}
\quad\text{或}\quad H=V.
}
\tag{46.11}
$$

反向，$N_a,N_b$ 在 $V_0$ 上恒为零，故其任意子空间都稳定；$V$ 也稳定，平移本来就保持所有陪集关系。所以 (46.11) 没有遗漏必要或充分方向。

二维空间 $V_0$ 恰有五个子空间，加上 $V$，给出全部六种局部编码核。下列代表只说明实际像和更新结构，任意其他同核编码只对其值作双射重标：

$$
\begin{array}{c|c|c}
\text{稳定核 }H&\text{编码代表 }q_H(a,b,c)&|V/H|\\ \hline
\{0\}&(a,b,c)&8\\
\langle e_a\rangle&(b,c)&4\\
\langle e_b\rangle&(a,c)&4\\
\langle e_a+e_b\rangle&(a+b,c)&4\\
V_0&c&2\\
V&*&1
\end{array}
\tag{46.12}
$$

特别是，三个四态编码全都恢复控制位 $c$；这个性质由动态稳定性强迫，不是编码者额外选择多保存一位。

### 46.4 全部精确编码对及其 Pareto 前沿

**命题 46.1（三位对角来源的动态资源前沿）。** 在 (46.1)—(46.6) 的合同下，令 $r_U=|U|$、$r_W=|W|$。可行状态数对按两个坐标同时最小化的 Pareto 前沿恰为

$$
\boxed{(8,1),\qquad(4,4),\qquad(1,8).}
\tag{46.13}
$$

每个点都可达到。若两侧各自都不允许保存完整八态源，即 $r_U<8$ 且 $r_W<8$，则必有 $r_U=r_W=4$。

证明。由 (46.9)，两份编码的消息对相等恰在两源之差属于 $H_u\cap H_v$ 时发生。因此 (46.5) 等价于

$$
H_u\cap H_v=\{0\},
\qquad
r_U=\frac8{|H_u|},\quad r_W=\frac8{|H_v|}.
\tag{46.14}
$$

若任一核为 $V$，另一核只能为零，分别得到 $(1,8)$、$(8,1)$。若某核为零而另一核不为 $V$，状态数对被相应的 $(8,1)$ 或 $(1,8)$ 弱支配，且至少一坐标严格改进。

余下两核都是 $V_0$ 的非零子空间。$V_0$ 与其中每个非零子空间都有非零交，所以两核都不能取 $V_0$；它们只能是两条不同的一维子空间。二维空间中的不同直线交为零，故这六个有序直线对全部可行，状态数均为 $(4,4)$。没有其他情形。三种资源点互不支配，证明精确前沿及两侧容量受限时的结论。证毕。

按核而非标签命名计数，可行编码对共有十七种：至少一核为零的十一种，加上两条不同直线的六种。在逐侧再粗化的偏序下，最小者有八种：两个单侧承担全部信息的极端，以及这六个直线对。它们并不形成一个唯一最粗的局部编码对；(46.13) 则把同样资源数量的不同核分配归为三个成本点。

### 46.5 四态加四态的显式局部递推

取

$$
u(a,b,c)=(b,c),
\qquad
v(a,b,c)=(a,c).
\tag{46.15}
$$

在实际输入上，解码器由 $((b,c),(a,c))\mapsto(a,b,c)$ 给出。对两侧记忆分别记 $m_U=(b,c)$、$m_W=(a,c)$，五项动作的更新全部是局部可计算的：

$$
\begin{array}{c|c|c}
\text{共同动作}&m_U'&m_W'\\ \hline
\tau_a&(b,c)&(a+1,c)\\
\tau_b&(b+1,c)&(a,c)\\
\tau_c&(b,c+1)&(a,c+1)\\
N_a&(0,0)&(c,0)\\
N_b&(c,0)&(0,0)
\end{array}
\tag{46.16}
$$

每行右侧只访问本侧已保存的两个 bit。逐行代入 (46.3) 即验证 (46.6)，再沿任意动作词归纳，实际解码始终恢复当前共同状态。该表提供的是运行实现，不要求每一步把两个本地消息互发。

三位目标在联合寄存器中只需三个 bit；在禁止任一侧独占完整状态的合同下，(46.13) 却要求两边各两个 bit，共四个本地存储位。额外一位正是重复的 $c$。若只保存左侧 $b$、右侧 $(a,c)$，当前目标仍可恢复，但动作 $N_b$ 后左侧应保存的新 $b$ 等于旧 $c$；同一个左记忆 $b$ 对两个不同 $c$ 要求不同后继，局部更新函数不存在。

这不是联合来源出现第四个独立随机 bit。即使给八个 $z$ 均匀先验，两份记忆联合熵仍为三位；两边各两位的熵之和为四位，重复部分表现为一位互信息。这里的锐下界首先是确定性状态容量结论，概率说明只解释同一共享控制位为何被重复保存。

### 46.6 八个实际消息对与十六个名义组合

(46.15) 的两侧实际像各有四个值，但共同来源只产生

$$
A_C=
\left\{\bigl((b,c),(a,c)\bigr):a,b,c\in\mathbb F_2\right\},
\qquad |A_C|=8.
\tag{46.17}
$$

自由乘积 $U\times W$ 有十六个元素；其中两个控制位不等的八个组合从未由 $C$ 产生。解码器只需定义在 $A_C$ 上；若为编程方便向其余八点延拓，这些任意值不成为实际模型的预测。更新表 (46.16) 保持两个控制位相等，因此实际像对全部动作闭合。

所以要分别记录三种不同数量：共同目标有八种可能值、实际联合消息也有八种值、两个四态存储器合起来有十六个名义组合。四个本地 bit 是独立硬件槽或独立固定长度编码的容量成本，不能用 $|A_C|=8$ 把共享的 $c$ 免费从任一侧删去；也不能反向把十六个名义组合误报成十六种实际来源。

若改成要求在全部 $V\times V$ 上检测对角合法性，两侧编码必须分别单射：假设 $u(z)=u(z')$ 而 $z\ne z'$，则 $(z,z)$ 与 $(z',z)$ 有相同消息、合法性相反。右侧同理，故需要 $(8,8)$。这条结论适用于扩张后的总判定任务，不是 (46.13) 的额外要求。

### 46.7 保留已有局部记录时，最小修复与重新分配不同

考虑已经取得的局部摘要

$$
u_0(a,b,c)=b,
\qquad
v_0(a,b,c)=(a,c).
\tag{46.18}
$$

两者合起来静态恢复目标，但 $u_0$ 不对 $N_b$ 闭合。若只允许增加本地信息、不删除已经取得的本地读数，修复后的核须满足

$$
H_u\subseteq\ker u_0=\operatorname{span}\{e_a,e_c\},
\qquad
H_v\subseteq\ker v_0=\langle e_b\rangle.
\tag{46.19}
$$

将 (46.11) 与第一项相交，最大的允许稳定核是 $\langle e_a\rangle$；第二项本来已经稳定，最大的允许核仍为 $\langle e_b\rangle$。故保留旧本地记录的唯一最粗修复，按标签重标等价，恰是 (46.15) 的四态加四态方案。

另一种任务若从头选择信息放在哪一侧，可以采用 $(8,1)$；但它不保留 (46.18) 右侧原有的本地读数。这说明“给定旧记录后的最小稳定细化”可以唯一，而“在全部分配方案中寻找最小局部记忆对”只给出 Pareto 前沿。共同来源的总信息、当前分配及允许的重新分配操作必须分别声明。

### 46.8 参数族：任意多个数据位仍恰需一位最小重复

三位例子可以在同一个取得合同下推广。固定 $d\ge2$，令

$$
V_d=\mathbb F_2^d\oplus\mathbb F_2,
\qquad z=(w,c),
\qquad W_d=\mathbb F_2^d\oplus\{0\}.
\tag{46.20}
$$

实际来源仍为 $C_d=\{(z,z):z\in V_d\}$，目标为当前 $z$。允许 $d+1$ 个基平移，以及全部 $d$ 项线性重写

$$
N_i(w,c)=(c e_i,0),\qquad 1\le i\le d.
\tag{46.21}
$$

同一动作在两侧同步执行，局部编码仍须满足 (46.6)。本节只用 $\mathbb F_2$：加法子群在这里自动是线性子空间，不将该步骤未经检查搬到任意有限域。

平移先把任意局部编码的核变为某个子空间 $H$ 的陪集关系。若 $H$ 含 $(w,1)$，所有 $N_i$ 的稳定性给出 $(e_i,0)\in H$，减去 $w$ 后再得 $(0,1)\in H$，于是 $H=V_d$；否则 $H\subseteq W_d$。反向这些子空间确实稳定。因此完整分类为

$$
H\text{ 是允许的局部稳定核}
\quad\Longleftrightarrow\quad
H\le W_d\ \text{或}\ H=V_d.
\tag{46.22}
$$

两端联合恢复目标仍等价于 $H_U\cap H_W=\{0\}$。若至少一核为 $V_d$，另一核为零，给两个极端；若一核为零而另一核较小，这份方案由对应极端弱支配。对两核均非零的其余情形，记维数 $h_U,h_W$，有

$$
H_U,H_W\le W_d,
\qquad
h_U+h_W\le d,
\qquad
(r_U,r_W)=\bigl(2^{d+1-h_U},2^{d+1-h_W}\bigr).
\tag{46.23}
$$

若 $h_U+h_W<d$，从 $W_d$ 中取 $H_U\oplus H_W$ 的一个非零补方向并加入 $H_U$，就保持交为零且严格减少左侧状态数。重复此步到二者直和等于 $W_d$。所以非极端方案位于 Pareto 前沿，当且仅当

$$
W_d=H_U\oplus H_W,
\qquad 1\le h_U\le d-1.
\tag{46.24}
$$

**命题 46.2（共享单控制位族的精确资源前沿）。** 固定 (46.20)—(46.21) 的动作与对角来源，所有确定性、分别动态闭合的状态编码对的资源 Pareto 前沿恰为

$$
\boxed{
\{(2^{d+1},1),(1,2^{d+1})\}
\ \cup\
\left\{\bigl(2^{d+1-h},2^{h+1}\bigr):1\le h\le d-1\right\}.
}
\tag{46.25}
$$

证明中的分类和支配方向由 (46.22)—(46.24) 给出。为验证每个点可达，把 $w=(p,q)$ 分成 $h$ 位与 $d-h$ 位，取

$$
u(p,q,c)=(q,c),
\qquad
v(p,q,c)=(p,c).
\tag{46.26}
$$

每个基平移只翻转本侧已保存的相应位，或同时翻转两侧已有的 $c$；$N_i$ 的本侧数据输出是 $c e_i$ 在该侧所保存坐标上的投影，新控制位为零。因此每项更新都只读取本侧记忆。两份代码又逐坐标恢复 $(p,q,c)$，实现 (46.25) 的各个非极端点；极端点由一侧保存全部状态、另一侧常值实现。内部点之间，一个坐标严格增加时另一个严格减少；两个极端也不支配内部点，故所列前沿准确。证毕。

若两端分别小于完整 $2^{d+1}$ 态，即不准任一侧独占全部状态，(46.23)给出固定长度本地存储的锐下界

$$
\boxed{
\log_2r_U+\log_2r_W
 =2(d+1)-h_U-h_W
 \ge d+2.
}
\tag{46.27}
$$

各状态数均为二的整数次幂，因此这里没有向上取整误差。联合目标本身有 $2^{d+1}$ 个值，只需 $d+1$ 个集中存储位；(46.26) 以 $d+2$ 个本地位达到下界。对任一非恒定稳定编码，(46.22)给 $H\subseteq W_d=\ker c$，所以 $c$ 必能从本地摘要恢复：两端都承担信息时，两端都必须保留这个控制位。

在达到界的 (46.26) 中，名义代码乘积有 $2^{d+2}$ 个组合，但实际共同像为

$$
\left\{\bigl((q,c),(p,c)\bigr):p\in\mathbb F_2^h,
 q\in\mathbb F_2^{d-h},c\in\mathbb F_2\right\},
\tag{46.28}
$$

只有 $2^{d+1}$ 个值。若共同源均匀，两个局部摘要的互信息恰为一位，联合熵仍为 $d+1$ 位。多出的一个本地存储位表示同一 $c$ 的重复可访问性，不表示来源多出独立信息。$d=2$ 恰回到 (46.13)—(46.17)；$d=3$ 的内部资源点为 $(8,4)$ 与 $(4,8)$，两种分配都只重复一位控制信息。

### 46.9 既有机制与本节新增的模型内容

过程卷定理3.5已给出实际比较载体上的联合下降，定理3.6及仓内 `StrictOneHoleContexts.contextual_equivalence_is_greatest` 处理强上下文同余；`RowColumnObserverCore.row_column_observer_core` 与 `DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` 处理总评价的行列商；`DynamicClosureMinimality.dynamic_closure_is_least` 处理给定初始观察后的最小动态细化。它们的既有一般机制不在这里重新取得新内容名义，也不把总评价范围自动换成对角受限来源。

本节具体补入的是 (46.3) 的同一有限动作族下，六个全部稳定核、三个资源极小点、不能由两端各少于八态规避的控制位重复，以及 (46.18) 的保记录修复；(46.20)—(46.28) 进一步给出维数可变的精确前沿和一位最小重复。平移使分类覆盖任意确定性状态编码，而非只覆盖事先选定的线性编码。上述普通证明和显式表没有被计作新增 Lean 结果。

全部结论限制在固定状态编码、同步具名动作、无额外本地原态读取及无跨端通信的合同。允许交互通信、免费共享档案、依赖完整历史的变动编码、随机化、误差或来源外输入，会产生不同问题。本节未给这些扩张模型的普遍最小内存定理。空间上的信息分配、时间上的更新作用、边界的恢复性与记忆的容量在这里由同一实际关系连接，但其最优值不能被一个标量或一份唯一最小坐标取代。Claim status: open。

## 46.99 追加锚

## 47. 共享控制位的精确通信方向与存储替换

本节沿用第46节的共同来源和动作族，把重写时的零通信约束改为计费的二进制通信，仍要求两端恢复各自被指定的新摘要。问题是：少存一份控制位后，哪个方向必须传位，以及相同存储容量能否要求不同通信。以下是基于既有模型的普通数学推导，文献状态为 repo-derived，不主张原创性；所有新增命题的 Claim status: open，未获 Lean 核验。

### 47.1 固定摘要、共同来源与逐操作资源

**定义 47.1（允许通信的固定状态摘要合同）。** 固定 $d\ge2$，取数据基 $e_1,\ldots,e_d$ 和控制基 $e_c$，令 $c:V\to\mathbb F_2$ 同时表示控制坐标函数。写

$$
\begin{gathered}
V=\mathbb F_2^d\oplus\mathbb F_2,
\qquad W=\ker c=\operatorname{span}\{e_1,\ldots,e_d\},
\qquad z=(w,c(z)),\\
\mathcal C=\{(z,z):z\in V\},\qquad T(z,z)=z,\\
\tau_j(z)=z+e_j\quad(j\in\{1,\ldots,d,c\}),
\qquad N_i(z)=c(z)e_i\quad(1\le i\le d).
\end{gathered}
\tag{47.1}
$$

左右两端只持有当前源的确定性摘要 $u:V\twoheadrightarrow U$、$v:V\twoheadrightarrow Q$，值域取各自实际像。共同源的准备合同仍是 $\mathcal C$；可供操作访问的持久信息只有这两份摘要，不能重新读取未保存的原态。要求

$$
\begin{gathered}
D(u(z),v(z))=z\quad(z\in V),\\
u\circ\tau_j=\bar\tau_{j,U}\circ u,
\qquad v\circ\tau_j=\bar\tau_{j,Q}\circ v.
\end{gathered}
\tag{47.2}
$$

因此基平移必须零通信地逐侧更新。对重写 $N_i$ 则允许通信，但结束时必须分别写入 $u(N_i z)$、$v(N_i z)$，不能改换摘要定义或仅让某一端知道完整新状态来替代这两个指定输出。解码器 $D$ 表示联合恢复能力，不是额外免费参与计算的控制器。

每个具名动作是两端共同给定的输入，正确性对全部 $z$ 和每个动作分别量化。动作标签不以免费、依赖未知源的选择方式传递信息；旧动作、旧通信、公共时钟及来源相关控制器状态均不作为免费输入。固定摘要跨操作不变。在一次操作内保留旧摘要，通信完成后同步提交新摘要；临时计算空间不计为持久记忆，但不得把临时消息或其他源相关状态带入下一次操作。

持久存储计为 $S=\log_2|U|+\log_2|Q|$ 个本地位。先研究无冗余的容量等式

$$
|U|\,|Q|=2^{d+1},\qquad S=d+1.
\tag{47.3}
$$

第47.6节再解除这个等式，在所有满足平移局部闭合的容量上求资源前沿。此处的容量是各端固定状态集的大小，不是仅对实际联合像取一次对数。

### 47.2 最小容量下的互补核与实际乘积来源

由 (47.2)，每个基平移保持摘要相等；基平移的合成给全部平移，且每个平移可逆。因此，令 $H_U=\{h:u(h)=u(0)\}$、$H_V=\{h:v(h)=v(0)\}$，可得

$$
\begin{gathered}
u(z)=u(z')\ \Longleftrightarrow\ z-z'\in H_U,
\qquad
v(z)=v(z')\ \Longleftrightarrow\ z-z'\in H_V,\\
H_U,H_V\le V,
\qquad |U|=2^{d+1-\dim H_U},
\qquad |Q|=2^{d+1-\dim H_V}.
\end{gathered}
\tag{47.4}
$$

这是第46.3节的平移陪集机制，仍不假定原编码线性。直接推导是：把相等的一对同时平移 $-z'$，得到它们之差与零同类；若 $h,k$ 与零同类，平移 $k$ 后再用传递性，得 $h+k$ 与零同类。故零类为子群，在 $\mathbb F_2$ 上就是子空间。同核摘要只差实际像上的双射重标。

联合恢复给 $H_U\cap H_V=\{0\}$；反过来，交为零也使摘要对单射，从而定义实际像上的解码器。这正是既有 `D5/S3/ConceptDynamics/Communication/JointLosslessCommunicationCriterion.lean` 中 `joint_lossless_communication_criterion` 所用的实际联合像注入机制，不另立一个普遍恢复定理。将 (47.3) 代入 (47.4)，有 $\dim H_U+\dim H_V=d+1$，所以两核互补。

取 $A=H_V$、$B=H_U$，并令 $p_A,p_B$ 为沿该直和的投影。每个 $H_U$ 陪集恰交 $A$ 于一点，每个 $H_V$ 陪集恰交 $B$ 于一点，因此可把左右摘要分别双射重标为

$$
V=A\oplus B,\qquad z=a+b,
\qquad u(z)=a=p_Az,\quad v(z)=b=p_Bz,
\qquad r=\dim A,\quad s=\dim B,\quad r+s=d+1.
\tag{47.5}
$$

重标不改变存储或通信量，$|U|=2^r$、$|Q|=2^s$。对任意 $(a,b)\in A\times B$，实际共同源 $(a+b,a+b)$ 都产生这对摘要。因此这里的整个摘要乘积确实是实际像；这由最小容量和联合单射导出，不能搬到第46节重复控制位的较大容量方案。后面的下界比较总在这些实际源之间进行。

商动态良定义等价于保持纤维，是既有 `D5/S0/Rewriting/Quotients/DynamicsDescent.lean` 的 `dynamics_descends_iff`。给定观察的最小动态细化见 `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean` 的 `dynamic_closure_is_least`。这里仅要求平移逐侧闭合，重写所缺的信息由通信取得；不把这两个既有机制重述为新增结论。

### 47.3 公开二进制协议与每条执行的方向下界

**定义 47.2（逐位通信与指定输出）。** 对每个固定动作 $N_i$，协议是一棵确定性的公开二叉树。内部节点的发送者由动作和此前传出的位串固定；该节点发送的一个位只能依赖发送端的旧摘要与此前位串，并沿标为零或一的边前进。叶的位置和停止规则同样公开固定，所有实际输入均在有限步停止。每端的最终输出只能依赖本端旧摘要和整个已传位串。发送者选择、静默、时间间隔、消息是否出现、停止与否及提前显露的输出都不能另作免费信道。成本是全部发送位数，两个方向各发送一位计两位，即使它们能在同一轮完成。

令 $C_i$ 为所有对全部实际源正确的此类协议中，最小的最坏输入总位数。对 (47.5) 记

$$
\begin{gathered}
\alpha_i=p_A(e_i),\qquad \beta_i=p_B(e_i),
\qquad \ell_A=c|_A,\qquad\ell_B=c|_B,\\
c(a+b)=\ell_A(a)+\ell_B(b),\\
a'=\alpha_i\bigl(\ell_A(a)+\ell_B(b)\bigr),
\qquad
b'=\beta_i\bigl(\ell_A(a)+\ell_B(b)\bigr).
\end{gathered}
\tag{47.6}
$$

式中向量乘零或一表示标量乘法，$\ell_A\ne0$ 表示线性函数非零，不是它在某次输入上恰取一。

**命题 47.1（指定两摘要的精确方向成本）。** Claim status: open。在 (47.1)—(47.5) 及定义47.2的合同下，

$$
\boxed{
C_i=\mathbf1_{\{\alpha_i\ne0\ \text{且}\ \ell_B\ne0\}}
    +\mathbf1_{\{\beta_i\ne0\ \text{且}\ \ell_A\ne0\}}.
}
\tag{47.7}
$$

第一项是右端 $B\to A$ 的必要位，第二项是左端 $A\to B$ 的必要位。更强地，任意正确协议、任意实际输入 $(a,b)$ 的执行都满足

$$
n_{B\to A}(a,b)\ge\mathbf1_{\{\alpha_i\ne0,\ \ell_B\ne0\}},
\qquad
n_{A\to B}(a,b)\ge\mathbf1_{\{\beta_i\ne0,\ \ell_A\ne0\}}.
\tag{47.8}
$$

存在一个协议在每个输入上同时达到这两项下界。

证明。上界直接传所缺贡献：第一项为一时由右端发送 $\ell_B(b)$；第二项为一时由左端发送 $\ell_A(a)$。需要两位时可固定先右后左，发送前保留两份旧摘要。未发送某一方向，意味着该接收端的投影为零，或者对端贡献恒为零；无论哪种情形，都能按 (47.6) 算出本端输出。因此该公开固定长度协议对所有输入正确，且只用所列位数。

对下界，设 $\alpha_i\ne0$、$\ell_B\ne0$，并任取一次输入 $(a,b)$ 的执行。若这条路径没有 $B\to A$ 位，则其每个内部节点的发送者都是左端。取 $b_0\in B$ 使 $\ell_B(b_0)=1$，比较另一实际输入 $(a,b+b_0)$。在根节点两次执行具有相同的左摘要；归纳地，只要此前位串相同，公开树就指定同一个左端发送节点，而发送位由相同的 $a$ 和此前位串确定，仍相同。原路径停止处是公开叶，新输入也在同一叶停止。这一归纳亦涵盖空路径。

故左端在两次执行得到相同的全部可访问信息，只能输出同一个值；但 (47.6) 的两个所需左输出之差是非零的 $\alpha_i$，矛盾。于是该次执行至少有一位 $B\to A$。交换两端，若 $\beta_i\ne0$、$\ell_A\ne0$，则每次执行至少有一位 $A\to B$。两项必要性作用于同一条任取的执行，故可相加，而不是把两个分别达到的最坏输入相加。交互、变长分支和由既有位串确定的停止均不能绕开 (47.8)。证毕。

既有 `D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound.lean` 的 `adaptive_binary_protocol_depth_lower_bound` 约束一般二进制问答的纤维多样性与深度。它不提供这里发送者只能访问本侧摘要的方向结论；(47.8) 的证明额外使用了发送者局部性、公开树和全部 $(a,b)$ 都实际可达这三项条件。

### 47.4 控制位归属决定的锐分类

**命题 47.2（非极端分配的最坏动作与字母表汇总）。** Claim status: open。在命题47.1的条件下再设 $r,s>0$，即两端都不独占完整源。记

$$
M=\max_{1\le i\le d}C_i,
\qquad L=\sum_{i=1}^d C_i.
\tag{47.9}
$$

$L$ 只是在动作字母表 $\{N_1,\ldots,N_d\}$ 上，把各动作面对全部当前源的最优最坏成本相加。它不是沿某条时间路径的累计成本，也不是摊还成本。全部分配分为三类：

$$
\begin{array}{c|c|c|c}
\text{控制信息的归属}&C_i&M&L\text{ 的锐下界}\\ \hline
\ell_B=0\ (A\text{ 单独确定 }c)&\mathbf1_{\{\beta_i\ne0\}}&1&s\\
\ell_A=0\ (B\text{ 单独确定 }c)&\mathbf1_{\{\alpha_i\ne0\}}&1&r\\
\ell_A\ne0,\ \ell_B\ne0
 &\mathbf1_{\{\alpha_i\ne0\}}+\mathbf1_{\{\beta_i\ne0\}}&2&d+1
\end{array}
\tag{47.10}
$$

对每个 $r,s\ge1$、$r+s=d+1$，三行各自的下界均可达到。

证明。$c$ 非零，所以两限制不可能同时为零。若 $\ell_B=0$，则 $c(a+b)=\ell_A(a)$，正好表示左摘要单独确定 $c$。反向，若左摘要单独确定 $c$，比较全部真实输入 $(a,b)$、$(a,0)$，便有 $\ell_B(b)=0$。另一侧相同。

先取 $\ell_B=0$。由 $B\subseteq W$，投影 $p_B:W\to B$ 满射；$e_1,\ldots,e_d$ 是 $W$ 的基，故非零列 $\beta_i$ 张成 $B$，至少有 $s$ 列非零。由 (47.7)，恰在这些列各付一位 $A\to B$，故 $L\ge s$。$s>0$ 保证至少一列非零，所以 $M=1$。若 $\ell_A=0$，交换两端得 $L\ge r$、$M=1$。

若两限制均非零，对任意 $a\in A$，可选 $b\in B$ 满足 $\ell_B(b)=\ell_A(a)$，使 $a+b\in W$。故 $p_A:W\to A$ 满射；同理 $p_B:W\to B$ 满射。因此

$$
\#\{i:\alpha_i\ne0\}\ge r,
\qquad
\#\{i:\beta_i\ne0\}\ge s,
\qquad L\ge r+s=d+1.
\tag{47.11}
$$

每个 $e_i=\alpha_i+\beta_i\ne0$，故每个 $C_i\ge1$。若所有 $C_i$ 都是一，则 $L=d$，与 (47.11) 矛盾；而 (47.7) 又给 $C_i\le2$，所以 $M=2$。这一步利用共同的投影列与维数，不以分别可达的资源最优值代替同一个分配。

第一行的锐构造为

$$
A=\operatorname{span}\{e_c,e_1,\ldots,e_{r-1}\},
\qquad B=\operatorname{span}\{e_r,\ldots,e_d\}.
\tag{47.12}
$$

它把 $c$ 放在左端，$r-1$ 个数据坐标也放左端，其余 $s$ 个数据坐标放右端。仅 $i=r,\ldots,d$ 需要左向右一位，所以 $L=s$。第二行由交换两端的相应构造达到 $L=r$。

第三行取分散控制信息的直和

$$
\boxed{
A=\operatorname{span}\{e_c,e_1,\ldots,e_{r-1}\},
\qquad B=\operatorname{span}\{e_c+e_d,e_r,\ldots,e_{d-1}\}.
}
\tag{47.13}
$$

这里 $1\le r\le d$，空指标段按空集处理。所列向量共 $d+1$ 个，生成全部数据基和控制基：$e_d=e_c+(e_c+e_d)$，其余基已在列表中。故它们是一组基，确给维数 $r,s$ 的互补子空间；两侧各含一个控制坐标为一的向量。投影具体为

$$
(\alpha_i,\beta_i)=
\begin{cases}
(e_i,0),&1\le i<r,\\
(0,e_i),&r\le i<d,\\
(e_c,e_c+e_d),&i=d.
\end{cases}
\tag{47.14}
$$

于是 $N_d$ 恰需两个方向各一位，其余每项恰需一位，$L=(d-1)+2=d+1$。三类构造都通过直和投影给出摘要，基平移只在本侧加上相应常量投影，故满足原合同。证毕。

### 47.5 相同二态与四态容量的不同通信

**命题 47.3（同容量分配的通信差异与接收者区别）。** Claim status: open。令 $d=2$、$z=(x,y,c)$。下列两份固定摘要都以 $(|U|,|Q|)=(2,4)$ 联合恢复全部当前源，且对三个基平移局部闭合，但其 $(C_x,C_y)$ 分别为 $(1,0)$ 和 $(2,1)$。

证明。第一份取 $u=x$、$v=(y,c)$。联合逆映射就是读取这三个坐标；对 $N_xz=(c,0,0)$、$N_yz=(0,c,0)$，直接代入摘要定义得

$$
\begin{array}{c|c|c|c}
\text{第一份摘要的动作}&u'&v'&\text{必要且充分的通信}\\ \hline
N_x&c&(0,0)&\text{右向左传 }c\text{，一位}\\
N_y&0&(c,0)&\text{零位}
\end{array}
\tag{47.15}
$$

这里 $A=\langle e_x\rangle$、$B=\langle e_y,e_c\rangle$，控制位由右端独占；$\ell_A=0$，$e_x$ 只有左投影，$e_y$ 只有右投影。故 (47.7) 不仅给表中的协议，也证明位数最小。

第二份取 $u=t=x+c$、$v=(x,y)$。对每个 $t,x,y$ 都存在唯一真实源 $(x,y,t+x)$，所以两份摘要联合恢复当前源，且整个二态乘四态的乘积实际可达。更新给

$$
\begin{array}{c|c|c|c}
\text{第二份摘要的动作}&u'&v'&\text{必要且充分的通信}\\ \hline
N_x&t+x&(t+x,0)&\text{右向左传旧 }x\text{，左向右传旧 }t\\
N_y&0&(0,t+x)&\text{左向右传旧 }t\text{，一位}
\end{array}
\tag{47.16}
$$

第二行右端已有旧 $x$，收到 $t$ 后得到 $c$。第一行两端分别缺对方的一个贡献，因此保留旧 $t,x$ 至两位发完，再各自写入新摘要。相应直和为 $A=\langle e_c\rangle$、$B=\langle e_x+e_c,e_y\rangle$：$e_x=e_c+(e_x+e_c)$ 的两个投影都非零，而 $e_y$ 的左投影为零，两侧控制限制均非零。因此 (47.7) 分别给二位、一位的下界。

两份摘要的平移闭合亦直接成立：第一份只是选择坐标；第二份在 $\tau_x$ 下左端翻 $t$、右端翻 $x$，在 $\tau_y$ 下仅右端翻 $y$，在 $\tau_c$ 下仅左端翻 $t$。每端都只改自己的已有位。以上差异因而发生于相同源、相同动作、相同静态容量和相同精确性要求内。证毕。

指定摘要的恢复与“让某一个指定接收者得到完整新状态”有不同输出合同。在 (47.5) 中，新状态总是 $N_i z=c(z)e_i$。若指定左端为唯一接收者，右端发送 $\ell_B(b)$ 即足以使左端求出 $c(z)$；指定右端则发送 $\ell_A(a)$，所以各自至多需要一位。这一观察不满足原任务要求的另一个端点输出。例如 (47.16) 的 $N_x$，只让左端知道完整新态，一位旧 $x$ 就足够；同时满足两端指定摘要则必须两位。若改成两端都要得到完整新态，该例也必须两位，因为从完整新态可算出各自指定摘要，而两位交换又确实使双方都得到 $c$。这里不把单接收者的上界冒充两端任务的成本。

### 47.6 在全部容量上替换一位持久冗余的资源前沿

**命题 47.4（总持久存储与最坏单次通信的精确前沿）。** Claim status: open。保留 (47.1)—(47.2) 和定义47.2的全部合同，解除 (47.3) 的容量等式，允许任意确定性摘要设计；要求两端均不独占完整源，即 $|U|,|Q|<2^{d+1}$。对每份设计令 $K$ 为所有重写动作和所有当前源上的最坏单次总通信位数的最小值，基平移仍为零位。按 $S,K$ 同时最小化的 Pareto 前沿恰为

$$
\boxed{\operatorname{Pareto}(S,K)=\{(d+1,1),\ (d+2,0)\}.}
\tag{47.17}
$$

若允许一端保存完整源、另一端常值，则 $(d+1,0)$ 可达，并成为这个扩大设计类的唯一 Pareto 资源点。

证明。对任意设计，联合单射给 $|U||Q|\ge2^{d+1}$，故 $S\ge d+1$。只用平移闭合就已有 (47.4)，所以两个实际像大小均为二的整数次幂，$S$ 是整数；此处没有连续容量或向上取整的遗漏。两端总可先互传有限摘要、联合解码，再求各自新摘要，因此 $K$ 有有限可达值，其最小值存在。

若 $K=0$，公开树没有传位，每端输出只依赖本端摘要和动作，恰回到第46节逐侧动态闭合的合同。为明确这一引入对任意容量都成立，可用 (46.22) 的稳定核分类：每个核或者包含于 $W$，或者等于 $V$。若某核等于 $V$，相应摘要常值，联合恢复迫使另一摘要单射，从而独占完整源，与当前限制矛盾。因此两核均包含于 $W$，且交为零，故

$$
\dim H_U+\dim H_V\le d,
\qquad S=2(d+1)-\dim H_U-\dim H_V\ge d+2.
\tag{47.18}
$$

这也是第46.8节 (46.27) 的零通信存储下界。特别地，$S=d+1$ 时必有 $K\ge1$。

点 $(d+1,1)$ 可取 (47.12) 的任意非极端单侧控制方案：$1\le r\le d$、$s=d+1-r$，两端都小于完整容量。命题47.2给最坏重写成本一位；所有平移零通信，且新摘要继续联合恢复新状态。

为达到 $(d+2,0)$，把数据分成非空的 $p\in\mathbb F_2^h$、$q\in\mathbb F_2^{d-h}$，其中 $1\le h\le d-1$，取第46节的重复控制方案

$$
u(p,q,c)=(q,c),\qquad v(p,q,c)=(p,c),
\qquad S=(d-h+1)+(h+1)=d+2.
\tag{47.19}
$$

每项平移只翻转已存坐标，每项 $N_i$ 只需本端已有的 $c$，把它放到本端负责的第 $i$ 个数据坐标（若该坐标属另一端，则本端数据全为零），并把新控制位置零。因此所有动作零通信，两个摘要仍联合精确；两端各至多 $d$ 位，均不独占完整源。

最后，任一设计若 $S=d+1$，即被 $(d+1,1)$ 弱支配；若 $S>d+1$，整性给 $S\ge d+2$，即被 $(d+2,0)$ 弱支配。两展示点互不支配，故确为全部容量上的前沿，而不只是在 (47.3) 等式切片上优化。解除非独占限制后，$(u,v)=(\operatorname{id},*)$ 以 $d+1$ 位、零通信实现全部动作；联合单射下界和非负通信使它支配全部其他资源点。证毕。

### 47.7 字母表量与可保留历史的边界

定义47.1要求同一固定摘要对在每次操作面对任意当前源时都正确，下一次操作不能额外读取前次公开记录。这是一项资源与访问约束，并不意味着运行过的状态仍在每一时刻遍历全部 $V$。本模型的重写实际满足

$$
c(N_i z)=0\qquad(z\in V,\ 1\le i\le d).
\tag{47.20}
$$

若扩张合同，允许一个额外保留的公共历史告诉两端“上一步是重写，之后没有其他动作”，则当前源已被限制在 $c=0$。在这个受限来源上再次做任意 $N_j$，新态恒为零，两端可直接写入 $u(0),v(0)$，无需通信。随后若允许基平移，历史对当前 $c$ 的约束又随控制基平移的次数奇偶变化。这些信息属于额外控制状态或历史访问，不能免费并入原来的两份固定摘要。

所以 $L=\sum_i C_i$ 只比较同一分配面对各具名动作、各自从全部当前源开始的难度。把 $N_1,\ldots,N_d$ 顺次执行既改变实际可达源，也会在保留历史的模型里改变可访问信息，不能直接宣称该路径需要 $L$ 位。若要优化这种多步过程，必须同时指定并计入保留的历史或控制器状态，重新给出来源、输出与累计成本合同。本节的方向等式、分配分类和 (47.17) 均限于已声明的固定摘要逐操作模型。

## 47.99 追加锚

## 48. 局部初始化的持久控制器：有限累计通信的锐记忆界

第47.7节指出，重写把控制位置零；若能保留这一事实，后续通信合同就会改变。本节把这份历史落实为计入容量的本地状态，固定原直和与原投影，求对全部动作词统一有界的累计通信需要多少记忆。以下结论为基于第47节模型的普通数学推导，文献状态为 repo-derived；所有新增命题的 Claim status: open，未获 Lean 核验。恢复目标始终是每次动作后的当前 $z$，不要求从不可逆重写后的状态恢复重写前的来源。

### 48.1 固定投影、实际初始化与可访问的历史

**定义 48.1（局部初始化的持久协议合同）。** 固定 $d\ge2$，令 $D=d+1$，沿用第47节

$$
\begin{gathered}
V=\mathbb F_2^d\oplus\mathbb F_2,
\quad W=\ker c=\langle e_1,\ldots,e_d\rangle,
\quad V=A\oplus B,\\
r=\dim A>0,\quad s=\dim B>0,\quad r+s=D,\\
a=p_Az,\quad b=p_Bz,\quad
\ell_A=c|_A,\quad\ell_B=c|_B,\quad
\alpha_i=p_Ae_i,\quad\beta_i=p_Be_i.
\end{gathered}
\tag{48.1}
$$

这里“非中心化”仅指 $r,s>0$：固定的两个原摘要都不独占完整 $z$。持久控制器扩充这两份摘要，分别具有状态集 $M_A,M_B$ 与固定读出 $\rho_A:M_A\to A$、$\rho_B:M_B\to B$。局部准备映射满足

$$
\begin{gathered}
\iota_A:A\to M_A,\quad \rho_A\iota_A=\operatorname{id}_A,
\qquad
\iota_B:B\to M_B,\quad \rho_B\iota_B=\operatorname{id}_B,\\
I=\{(\iota_A(a),\iota_B(b)):a\in A,\ b\in B\}
  =\iota_A(A)\times\iota_B(B).
\end{gathered}
\tag{48.2}
$$

因此两准备映射自动单射，整个初始乘积均由实际共同源 $z=a+b$ 产生。初始化时，左端只能读取 $a$，右端只能读取 $b$；额外缓存不能预先从对端摘要取得控制位。

公开动作字母表固定为

$$
\mathcal F=\{\tau_1,\ldots,\tau_d,\tau_c,N_1,\ldots,N_d\},
\qquad \tau_jz=z+e_j,\quad N_i z=c(z)e_i.
\tag{48.3}
$$

令 $Q\subseteq M_A\times M_B$ 为从 $I$ 经所有有限动作词实际可达的联合状态集，且 $M_A,M_B$ 取 $Q$ 的两个实际投影；允许这些集合无限。对每个 $f\in\mathcal F$，协议在每个 $m=(m_A,m_B)\in Q$ 上确定、总定义并有限停止，给后继 $T_fm\in Q$ 和发送位数 $w(m,f)\in\mathbb N$。定义当前态读出

$$
R(m)=\rho_A(m_A)+\rho_B(m_B),\qquad
\rho_A((T_fm)_A)=p_A(f(R(m))),\quad
\rho_B((T_fm)_B)=p_B(f(R(m))).
\tag{48.4}
$$

这要求固定投影在每步末仍恢复当前态，$R$ 只是数学读出，不是免费参与执行的中央控制器。全部基平移均零通信；动作词是外部给定的操作要求，正确性量化于每个词，动作选择本身不充当来源相关的免费信号。

协议根也必须局部可选。对每个当前动作 $f$，存在本地函数 $\sigma_{f,A},\sigma_{f,B}$，在所有实际 $m\in Q$ 上满足

$$
\sigma_{f,A}(m_A)=\sigma_{f,B}(m_B)=:\sigma_f(m).
\tag{48.5}
$$

共同标识选定一棵公开确定性二叉协议树。内部节点的发送者由 $f$、树标识及已传位串固定；所发位只能是本端旧持久状态、$f$ 与此前位串的函数。两端在叶处各自写入的新持久状态，也只能是本端旧持久状态、$f$ 与本次完整位串的函数；树标识本身已由本端旧状态与 $f$ 决定。不得把对端旧状态作为任何本地更新的免费实参。根为叶时成本零，根为内部节点时至少传一位；消息是否出现、静默时长、停止时刻及提前显露的输出均不额外传信息。

凡影响未来行为的旧动作、计时器、模式、缓存与通信记录，都必须保存在 $M_A,M_B$ 中并计入容量。下一次操作仅接受本端旧持久状态、当前公开动作及该次通信；不额外读取过去动作词或外部历史。临时计算可用旧状态与本次位串，但带入下次操作的部分必须写回持久状态。

对 $m_0\in I$ 与有限词 $u=f_1\cdots f_n$，按 $m_k=T_{f_k}m_{k-1}$ 定义

$$
\operatorname{Comm}(m_0,u)=\sum_{k=1}^n w(m_{k-1},f_k).
\tag{48.6}
$$

“统一有限累计通信”指存在一个有限整数 $K$，使每个 $m_0\in I$ 和每个 $u\in\mathcal F^*$ 都满足 $\operatorname{Comm}(m_0,u)\le K$。这同时量化全部初始源与任意长动作词，不是逐词另选一个界。

### 48.2 共同协议根与达到预算后的静默后继

对实际支撑 $H\subseteq M_A\times M_B$，把每个实际对视为连接其两个坐标的边。若一个输出分别由两坐标算出且在每条边上一致，它沿支撑图路径必为常量。这是 RRO 主卷第76—77节共同商与支撑图机制的直接应用；`D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.lean` 中 `commonCoarsening` 及 `concept_kernel_order_duality` 的末项，以两观察核之并的等价闭包表达同一共同商结构。这里取来源为 $H$、读出为两个坐标、共同输出为协议树标识，不要求概率律。

特别地，在 (48.2) 的非空完整乘积上，每个固定动作的初始根标识为常量：固定一个 $b_0$，有 $\sigma_{f,A}(\iota_A(a))=\sigma_{f,B}(\iota_B(b_0))$ 对全部 $a$ 成立；再固定任一 $a_0$ 得右侧同样常量。此处只应用既有共同商机制，不另主张一般共同信息定理。

**引理 48.2（饱和预算给出覆盖当前态的静默后继集）。** Claim status: open。在定义48.1下，若累计通信统一有限，则存在从某次实际初始化可达的状态 $m_*$，使其全部后继组成的集合

$$
H_*:=\{T_um_*:u\in\mathcal F^*\}
\tag{48.7}
$$

对动作封闭，其中每步成本均零，且 $R(H_*)=V$。还存在一个重写 $N_h$，使它在整个初始乘积上的共同根为内部节点，在 $H_*$ 上的根却都是叶。

证明。所有实际初始化与有限词的成本构成一个非空、上有界的非负整数集，故其最大值 $K_*$ 确由某个 $(m_0,u_*)$ 达到。取 $m_*=T_{u_*}m_0$。若其任一有限后继处某动作付费，把这条后继词及付费动作接到 $u_*$ 后，成本将超过 $K_*$。因此所有这些边成本为零，后继集也按定义封闭。这一步不需要 $Q$ 有限。

全部基平移都总定义，其有限合成实现任意 $z\mapsto z+t$。从 $R(m_*)$ 出发，对每个目标 $z$ 选取表示 $z-R(m_*)$ 的基平移词，由 (48.4) 得一个读出为 $z$ 的 $H_*$ 状态。因此 $R(H_*)=V$；这里没有断言 $H_*$ 是两个本地投影的完整乘积。

第47.3—47.4节给

$$
C_i=\mathbf1_{\{\alpha_i\ne0,\ \ell_B\ne0\}}
   +\mathbf1_{\{\beta_i\ne0,\ \ell_A\ne0\}},
\qquad C_*:=\max_i C_i\in\{1,2\}.
\tag{48.8}
$$

取 $C_h>0$。初始根在完整乘积上为同一个根；若它是叶，两端从 $\iota_A(a),\iota_B(b)$ 各自零通信更新，再应用 $\rho_A,\rho_B$，就得到第47.3节所排除的、对全部原摘要正确的零通信 $N_h$ 协议。因此初始根是内部节点。$H_*$ 上所有动作成本零，按根合同，它们对应的 $N_h$ 根全为叶。证毕。

### 48.3 每个投影纤维的锐下界

**定理 48.3（统一有限累计通信的必要记忆）。** Claim status: open。在定义48.1下，若存在统一有限累计通信界，则对每个 $a\in A$、$b\in B$，

$$
\begin{gathered}
|\rho_A^{-1}(a)|\ge1+2^{\operatorname{rank}\ell_B},\qquad
|\rho_B^{-1}(b)|\ge1+2^{\operatorname{rank}\ell_A},\\
|M_A|\ge(1+2^{\operatorname{rank}\ell_B})|A|,\qquad
|M_B|\ge(1+2^{\operatorname{rank}\ell_A})|B|,\qquad
|Q|\ge2|V|.
\end{gathered}
\tag{48.9}
$$

秩在此只取零或一。集合可无限；这些是不依赖有限状态假设的有限基数下界。

证明。先用引理48.2选择 $N_h$ 与 $H_*$。$H_*$ 中出现的任何左状态都不等于任一 $\iota_A(a)$：否则局部函数 $\sigma_{N_h,A}$ 在同一状态上既选初始的内部根，又选静默后继的叶根，矛盾。右端相同。因此两端的静默后继状态各自与初始本地像不交；尤其在每个读出纤维中，初始状态占据一个与静默状态不同的位置。

若 $\ell_B=0$，由 $R(H_*)=V$，每个 $a$ 至少有一个静默左状态，连同 $\iota_A(a)$ 得两态，恰为 $1+2^0$。若 $\ell_B\ne0$，则对任意 $a\in A$，可选 $b\in B$ 使 $\ell_B(b)=\ell_A(a)$，从而 $a+b\in W$。所以 $p_A(W)=A$。由于 $A\ne0$ 且 $e_1,\ldots,e_d$ 张成 $W$，必存在 $i$ 使 $\alpha_i\ne0$；不能在需要此列时省略非中心化前提。

固定 $a$，分别选 $b_0,b_1$ 使 $c(a+b_\varepsilon)=\varepsilon$，$\varepsilon\in\{0,1\}$。覆盖性给 $m^{(0)},m^{(1)}\in H_*$，读出恰为这两个当前态。若两者左持久状态相同，在当前同一动作 $N_i$ 下，两次协议都零通信，位串同为空；按终端更新局部性，左端新状态及其读出必须相同。但指定输出分别为 $0$ 与 $\alpha_i$，矛盾。于是同一 $a$ 纤维内至少有两个不同的静默状态，再加一个初始状态，共三态。这里比较的两对都在实际 $H_*$ 中，未把其不同端点拼成未经证明可达的新输入。

交换左右即得右侧逐纤维界；跨不同纤维的状态由固定读出区分，求和得到两个本地容量界。最后，$I$ 含 $|V|$ 个状态，$R(H_*)=V$ 迫使 $H_*$ 至少含 $|V|$ 个状态；初始与静默状态已在每一端分离，故 $I\cap H_*=\varnothing$。两集合均包含于 $Q$，得 $|Q|\ge2|V|$。证毕。

### 48.4 达到全部界的受限状态并与首次重写协议

**定理 48.4（局部容量、联合容量与统一预算同时达到）。** Claim status: open。对每个固定的非中心化直和 (48.1)，定义48.1存在一个控制器，同时达到 (48.9) 的所有基数下界。所有动作词的成本等于首次重写的 $C_i$，没有重写则为零；最小统一预算恰为 $C_*$。

证明。用 $?$ 表示“尚未发生重写”，用带已知标记的 $q\in\mathbb F_2$ 表示保存的当前控制值。实际本地状态取受限不交并

$$
\begin{aligned}
M_A&=(A\times\{?\})\ \sqcup
 \{(a,\mathsf K,q):a\in A,\ q\in\ell_A(a)+\ell_B(B)\},\\
M_B&=(B\times\{?\})\ \sqcup
 \{(b,\mathsf K,q):b\in B,\ q\in\ell_B(b)+\ell_A(A)\}.
\end{aligned}
\tag{48.10}
$$

这不是任意 $a,q$ 或 $b,q$ 的完整笛卡尔积：当远端控制限制为零时，本端已知层的 $q$ 已由原投影决定。读出只取 $a,b$，初始化为 $(a,?),(b,?)$。实际联合状态是两层

$$
\begin{aligned}
Q_{?}&=\{((a,?),(b,?)):a\in A,b\in B\},\\
Q_{\mathsf K}&=\{((a,\mathsf K,q),(b,\mathsf K,q)):
       a\in A,b\in B,\ q=\ell_A(a)+\ell_B(b)\},\\
Q&=Q_{?}\sqcup Q_{\mathsf K}.
\end{aligned}
\tag{48.11}
$$

对平移 $\tau_j$，两端分别在本地把 $a,b$ 加上 $p_Ae_j,p_Be_j$。未知标记保持未知；已知层各自把 $q$ 改为 $q+c(e_j)$。这些规则仅访问本端旧状态与公开动作，而且保持 (48.10)—(48.11)，成本为零。

对 $N_i$，两端由自己的未知或已知标记同意选择协议模式。在未知层，直接执行第47.3节的协议：若 $\alpha_i\ne0,\ell_B\ne0$，右端传旧 $\ell_B(b)$；若 $\beta_i\ne0,\ell_A\ne0$，左端传旧 $\ell_A(a)$，需要两位时固定先右后左。各端从自己的旧摘要与收到的位算出指定新投影；若本端投影系数为零，直接输出零，无须求出旧 $c$。在已知层，两端各自用已存 $q$ 算出 $\alpha_iq,\beta_iq$，选择叶根，零通信。无论哪层，动作结束都写入

$$
\bigl((\alpha_i c(z),\mathsf K,0),
      (\beta_i c(z),\mathsf K,0)\bigr).
\tag{48.12}
$$

式 (48.12) 是联合结果的表达式；本地实现按刚给的局部规则取得各自分量，不免费读取联合 $z$。因 $c(N_i z)=0$，已知控制值置零正确，输出也满足两个受限集合的成员条件。故首次重写把状态从未知层送到已知层，之后平移与重写都留在已知层且零通信。首次 $N_i$ 的 $C_i$ 也可以为零；它仍使双方公开同步进入已知模式。

初始所有源使 $Q_?$ 的每个状态可达。从初始零态作任一重写，得到已知零态；再用基平移到任意当前 $z$，得到 $Q_{\mathsf K}$ 的对应状态。故 (48.11) 恰是全部可达联合状态，(48.10) 恰是实际本地投影，而非声明了未用状态的容量上界。于是

$$
|M_A|=(1+2^{\operatorname{rank}\ell_B})2^r,\quad
|M_B|=(1+2^{\operatorname{rank}\ell_A})2^s,\quad
|Q|=2^{D+1}.
\tag{48.13}
$$

这同时达到定理48.3。它给统一预算 $C_*$。反向，对任一符合合同的控制器，取初始即执行 $N_i$；初始树标识在完整乘积上恒定，$\iota_A(a),\iota_B(b)$ 可分别从 $a,b$ 计算，动作末再接各端 $\rho$，便是一份第47.3节的协议。该节的方向下界使任一输入至少付 $C_i$，故统一预算至少 $\max_i C_i=C_*$。证毕。

把本地容量的对数与独立固定宽度二进制存储分开，定义

$$
S_{\log}=\log_2|M_A|+\log_2|M_B|,\qquad
B_{\mathrm{fix}}=\lceil\log_2|M_A|\rceil+
                 \lceil\log_2|M_B|\rceil.
\tag{48.14}
$$

由必要界和同一达到构造，三项最小值分别为

$$
\begin{array}{c|c|c|c|c}
\text{固定直和的控制限制}&(|M_A|,|M_B|)_{\min}&S_{\log,\min}&B_{\mathrm{fix},\min}&K_{\min}\\ \hline
\ell_A=0,\ \ell_B\ne0&(3\cdot2^r,2\cdot2^s)&D+\log_2 6&D+3&1\\
\ell_B=0,\ \ell_A\ne0&(2\cdot2^r,3\cdot2^s)&D+\log_2 6&D+3&1\\
\ell_A\ne0,\ \ell_B\ne0&(3\cdot2^r,3\cdot2^s)&D+\log_2 9&D+4&2
\end{array}
\tag{48.15}
$$

例如首行左右固定宽度分别为 $r+2,s+1$ 位；第二行为 $r+1,s+2$ 位；第三行为 $r+2,s+2$ 位。联合像的最小集中编码只需 $\log_2|Q|=D+1$ 位，但集中编码没有提供两端可各自访问、各自更新的编码，不能代替 (48.14) 的本地资源。

协议树选择只需未知、已知两个模式；已知零与已知一可以选择同一叶根，却在本地更新时给出不同输出。因此逐纤维三态必要性约束持久状态，不是协议根标识至少三个的断言。即便某端已能由自己的原摘要读出 $c$，它仍需区分尚未重写与已同步的模式，以同意另一端是否需要通信。第47.6节的 $D+1,D+2$ 存储前沿允许重新设计当前态摘要；这里固定原投影、要求严格局部初始化并优化全词累计成本，两份合同不同。

### 48.5 两个三维的完整实现

**例 48.5（控制在一侧与控制分散）。** 取 $d=2$、$z=(x,y,c)$，以下加法均在 $\mathbb F_2$ 上。为缩短记号，把 $(a,\mathsf K,q)$ 写为 $(a,q)$，其中 $q=0,1$ 与 $q=?$ 不相混淆。

第一份原摘要为 $a=x,b=(y,c)$。左端保存 $(x,q)$，$q\in\{?,0,1\}$；右端保存 $(y,c,k)$，$k\in\{0,1\}$，实际不变量为 $q=?\Leftrightarrow k=0$，以及 $k=1\Rightarrow q=c$。初始化为 $q=?,k=0$。$\tau_x$ 只翻左端 $x$，$\tau_y$ 只翻右端 $y$，$\tau_c$ 翻右端 $c$，并使左端已知 $q$ 翻转、未知 $q$ 保持未知。

执行 $N_x$ 时，若 $q=?$（等价于右端的 $k=0$），右端发送旧 $c$；左端以收到的一位求新 $x$。若已知，则双方同意叶根，左端以 $q$ 求新 $x$。末态为左 $(c,0)$、右 $(0,0,1)$，成本 $1-k$。执行 $N_y$ 时两个模式都选叶根，左端写 $(0,0)$，右端写 $(c,0,1)$，成本零；右端本来就有旧 $c$。故全部词成本至多一位。未知联合层八态，已知联合层八态；本地实际容量为六态、八态，联合十六态。

第二份原摘要为 $a=t=x+c,b=(x,y)$。左端保存 $(t,q)$，右端保存 $(x,y,q)$；两端的 $q\in\{?,0,1\}$ 相同，且已知时 $q=c=t+x$。初始化均为未知。$\tau_x$ 翻左端 $t$ 与右端 $x$，$q$ 不变；$\tau_y$ 只翻右端 $y$；$\tau_c$ 翻左端 $t$，并使两端已知 $q$ 翻转，未知保持未知。

执行 $N_x$ 时，未知模式固定先由右端发旧 $x$、再由左端发旧 $t$；保留旧值直到通信结束。双方分别从本地旧值与收到的一位求 $t+x$，写入左 $(t+x,0)$、右 $(t+x,0,0)$，成本二位。已知模式用各自 $q$ 得同样输出并置 $q=0$，成本零。执行 $N_y$ 时，未知模式只由左端发旧 $t$，左端写 $(0,0)$，右端用旧 $x$ 与收到的 $t$ 写 $(0,t+x,0)$，成本一位；已知模式右端以 $q$ 求新 $y$，两端置 $q=0$，成本零。因此全部词成本至多二位，本地实际容量六态、十二态，联合仍十六态。

两例的已知层每个当前 $z$ 都能由重写零态后平移取得，未知层每个 $z$ 都是允许的初始源。模式选择在通信前已由各自持久状态决定，无须检测消息是否出现。第二例固定 $t=0$ 时，已知 $q=0$ 与 $q=1$ 的左状态对 $N_x$ 必给不同的新 $t$；两者虽共享“已知”根标识，仍不能合并为一个本地持久状态。

### 48.6 有限状态图、正费周期与容量不足

**定理 48.6（有限确定性动作图的累计通信判据）。** Claim status: open。取非空实际初始化集 $I$，有限非空动作字母表 $\mathcal F$，以及从 $I$ 经全部有限词实际可达的有限非空状态集 $Q$。每个动作 $f$ 给总定义确定性转移 $T_f:Q\to Q$ 与非负整数成本 $w(m,f)$；多条具名动作即使连接同一对状态，也各保留为自己的边。对无限词 $\omega$ 定义总成本为有限前缀成本的上确界

$$
\operatorname{Comm}(m_0,\omega)
 :=\sup_{n\ge0}\operatorname{Comm}(m_0,\omega_{<n})
 \in[0,+\infty].
\tag{48.16}
$$

下列三项等价：每个 $m_0\in I$ 与每个无限词的总成本有限；所有初始化与所有有限词共享一个有限成本界；可达动作图没有正总成本的有向周期。后一条件成立时，令 $W_{\max}=\max_{m\in Q,f\in\mathcal F}w(m,f)$，可统一取界

$$
\operatorname{Comm}(m_0,u)\le(|Q|-1)W_{\max}.
\tag{48.17}
$$

证明。统一有限界直接约束每个无限词的前缀上确界。若有可达正费周期，选一次初始化和前缀 $p$ 到达周期起点，把周期的非空动作词 $v$ 无限重复。确定性使每圈回到同一状态、付同一正成本，故总成本无限；这排除了“每条无限词各自有限”。

反向，没有正费周期时，每条有向闭走法都费零：闭走法可逐次切成简单周期，非负边费保证每项周期费都是零。在任意有限执行中，一旦状态重复，就删去两次出现之间的闭段。其成本为零，且两端状态相同，余下后缀仍是合法执行。有限次删除后剩一条无重复顶点的路径，至多 $|Q|-1$ 条边，成本保持原值而每边至多 $W_{\max}$，得 (48.17)。有限动作集和有限 $Q$ 保证这个最大边费存在。三项遂等价。证毕。

**推论 48.7（记忆不足必有最终周期的持续付费动作词）。** Claim status: open。对定义48.1再要求实际 $Q$ 有限。若任一个逐纤维或总本地容量界、或联合容量界 (48.9) 不成立，则存在某个 $m_0\in I$、有限词 $p$ 和非空词 $v$，其对应周期简单，满足

$$
\begin{gathered}
1\le |v|\le |Q|,\qquad C\in\mathbb N,\quad C\ge1,\\
\operatorname{Comm}(m_0,pv^m)
 =\operatorname{Comm}(m_0,p)+mC\quad(m\ge0),\\
\lim_{n\to\infty}\frac{\operatorname{Comm}(m_0,(pv^\infty)_{<n})}{n}
 =\frac{C}{|v|}\ge\frac1{|Q|}.
\end{gathered}
\tag{48.18}
$$

证明。若没有可达正费周期，定理48.6给统一有限界，定理48.3遂强制全部容量界，与假设矛盾。故存在正费闭路；把它分解为简单周期，非负总和为正保证某个简单周期费用 $C>0$。它仍可达，长度至多 $|Q|$，且整数费用使 $C\ge1$。取初始化到其起点的前缀 $p$，确定性给每圈同费及 (48.18) 的等式。任意前缀只比完整圈数多一个长度小于 $|v|$ 的尾段；这段费用有界，除以 $n$ 后趋零，得极限。证毕。

这只断言存在一条最终周期的正费路径，不断言每条动作词都付费。有限累计通信也不提供统一的“最后一次付费时间”：例如在例48.5第一份模型的未知层，$\tau_x\tau_x$ 是零费循环，词 $(\tau_x\tau_x)^nN_x$ 都只付一位，但付费时刻 $2n+1$ 无界。

路径累计与端点势的区别沿用 Process Geometry 第9节。没有正费周期不自动给任意可达图上的全局势差表达；其定理9.3(c)的无环菱形已有同端点不同路费。定理9.5的零有向闭和势判据另需强连通。这里的证明只删零费闭段取得统一上界，并未认定不同路径到同一终点时具有相同累计成本。`D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean` 的 `finite_orbit_and_readout_eventually_periodic` 处理单个自治自映射及其读出的最终周期；本节对全部动作词的加权判据由上述直接图论证明承担。

### 48.7 三项合同各自失效时的具体边界

**例 48.8（允许免费检测静默）。** 仍取 $z=(x,y,c)$ 与原摘要 $a=x,b=(y,c)$；在完整合同下锐容量是本地六、八态和联合十六态。现取消共同根要求，允许在固定时隙结束时免费判断消息有无。左端仅存 $(x,g)$，右端存 $(y,c,h)$，其中 $g,h$ 为位，初始化 $g=h=0$。$\tau_x,\tau_y$ 更新各自数据，$\tau_c$ 同时翻右端 $c$ 与左端 $g$，$h$ 不变。

对 $N_x$，右端当且仅当 $h=0$ 时发送旧 $c$；左端若收到消息就用该位作新 $x$，否则在时隙结束时用旧 $g$ 作新 $x$。末态左 $(c,0)$、右 $(0,0,1)$。对 $N_y$，不传消息，左写 $(0,0)$、右写 $(c,0,1)$。任一重写后 $g=c=0,h=1$，后续平移保持 $g=c$，故所有动作正确且总发送位数至多一。

其实际联合像为 $h=0$ 时全部 $(x,y,c,g)$ 的十六态，与 $h=1,g=c$ 时的八态，共二十四态：前一层从任选初始 $c$ 配合控制平移取得，后一层从重写零态后平移取得。本地容量分别四、八态，左侧低于六态。相同左状态可对应不同 $h$，左端不能在发送前同意“本次发位还是叶根”；免费检测消息缺席承担了模式信号。这是删去根与静默合同的反例，不是定义48.1内的协议。

**例 48.9（允许非局部初始化）。** 同一原摘要分解下，左端预存 $(x,c)$，右端预存 $(y,c)$。三个平移各自更新所存坐标；$N_x$ 写左 $(c,0)$、右 $(0,0)$，$N_y$ 写左 $(0,0)$、右 $(c,0)$，全部零通信。联合实际像是两端 $c$ 相同的八态，本地四、四态。但左端初始化读了其原摘要 $x$ 未提供的 $c$，初始像不再是 (48.2) 的局部准备乘积，因此容量下界不适用。

**例 48.10（只允许未知模式下作控制平移）。** 保留局部初始化与共同根，左存 $(x,k)$、右存 $(y,c,k)$，共同模式 $k\in\{?,\mathsf K\}$，初始化 $k=?$。数据平移总合法且只改本端数据；控制平移 $\tau_c$ 仅在 $k=?$ 时合法，届时只翻右端 $c$。未知模式的 $N_x$ 由右端传一位旧 $c$，写左 $(c,\mathsf K)$、右 $(0,0,\mathsf K)$；$N_y$ 零通信写左 $(0,\mathsf K)$、右 $(c,0,\mathsf K)$。已知模式下 $c=0$，两个重写都零通信写各自零数据并保持已知。

合法性由各端自己的模式可判；每条合法词总通信至多一位。实际联合像为未知时的全部八个 $z$，加已知且 $c=0$ 的四个 $z$，共十二态；本地容量四、六态。已知层由重写零态后数据平移覆盖，故这些计数都是实际像。此时静默后继中没有 $c=1$ 的状态，正好失去引理48.2靠总控制平移取得的全 $V$ 覆盖；它没有满足所有具名动作在每个可达状态总定义的前提。

有限状态前提也不能从“每条无限词都只付有限费用”删去。取 $Q=\{\operatorname{wait}(n),\operatorname{pay}(n):n\ge0\}\cup\{\operatorname{done}\}$，初始 $\operatorname{wait}(0)$，两动作 $w,s$，令 $\operatorname{wait}(n)\xrightarrow{w/0}\operatorname{wait}(n+1)$、$\operatorname{wait}(n)\xrightarrow{s/0}\operatorname{pay}(n)$，在 $\operatorname{pay}(k)$、$k>0$ 时任一动作都以成本一到 $\operatorname{pay}(k-1)$，在 $\operatorname{pay}(0)$ 时任一动作以成本零到 $\operatorname{done}$，后者零费自环；每条无限词或者永远等待而成本零，或者首次选择 $s$ 前等待 $n$ 次、随后总成本恰为 $n$，故逐词有限且无正费周期，但 $w^nsw^n$ 的成本为 $n$，没有统一有限界。

### 48.8 来源与结论范围

本节单动作方向成本直接使用第47.3—47.4节；共同根在实际支撑分量上恒定使用 RRO 主卷第76—77节及上述共同核机制；累计费用与端点势的区分使用 Process Geometry 第9节。锐容量的连接步骤是局部准备乘积、预算饱和后的零费后继、总平移覆盖及零位更新的本地不可区分性，已在本节逐项证明。

Joseph Y. Halpern、Yoram Moses，*Knowledge and Common Knowledge in a Distributed Environment*，版本 [arXiv:cs/0006009v1](https://arxiv.org/abs/cs/0006009v1)，以处理者自己的初始信息与所观察事件形成局部历史，支持这里明确本地可访问信息的建模边界。Guy Goren、Yoram Moses，*Silence*，版本 [arXiv:1805.07954v1](https://arxiv.org/abs/1805.07954v1)，研究同步系统中静默何时传递信息，支持把消息缺席和计时是否计作信道明确写入合同；其故障模型和结论不直接充当本节锐容量的证明。

结论限于一位二元控制、固定非中心化直和、严格局部准备、总动作与确定性公开二进制协议。有限状态图推论另需实际状态集有限。普通证明与有限实例核算都不等于 Lean kernel 核验；这里保留形式状态 open，不据此宣称新颖性或更一般的控制秩结论。记忆恢复的是当前投影、当前控制关系及足够的继续操作模式，不是重写前已被抹去的原始数据，也不是 Shannon 信息守恒命题。

## 48.99 追加锚

## 49. 相关准备的共同控制与有限累计通信的锐容量

本节保留第48.1节的动态协议合同，只把完整乘积初始化换成设计时已知的实际准备关系。结论为 repo-derived 的普通数学推导；新增命题的 Claim status: open，未作 Lean 核验，不主张原创性。问题分成两层：准备关系何时允许永久零通信；若只要求存在某个统一有限累计通信界，全部正确控制器的实际本地容量与联合容量最小是多少。

### 49.1 实际准备、支撑分量与资源量词

**定义 49.1（满投影的相关准备合同）。** 沿用 (48.1) 的 $d\ge2$、$D=d+1$、$V=W\oplus\langle e_c\rangle=A\oplus B$、$r,s>0$、$c,\ell_A,\ell_B,\alpha_i,\beta_i$。固定关系 $C\subseteq A\times B$，要求两个投影分别充满 $A,B$，并把 (48.2) 的实际初始化集替换为

$$
I_C=\{(\iota_A(a),\iota_B(b)):(a,b)\in C\},
\qquad \rho_A\iota_A=\operatorname{id}_A,\quad
\rho_B\iota_B=\operatorname{id}_B.
\tag{49.1}
$$

$C$ 是协议设计时固定、双方已知的关系；准备映射与控制器可以依赖这个固定参数，但一次初始化仍只能读取本端的 $a$ 或 $b$。不假设端点能够学到未公开的 $C$，也不优化从 $C$ 构造表格、程序或执行本地计算的时间成本。

其余合同逐项保持：具名动作仍为全部基平移与 $N_i z=c(z)e_i$；每个动作在每个实际可达状态上总定义、确定且有限停止；全部基平移发送零位；初始化、当前投影读出、共同协议根、发送位和终端更新均满足第48.1节的端点局部性。没有免费的旧动作史、计时器、消息缺席信号、提前输出或来源相关的动作选择。须保留的历史都计入持久状态。$Q$ 是从 $I_C$ 经全部有限动作词可达的联合像，$M_A,M_B$ 恰为其两个实际投影；它们允许无限。当前读出仍为 $R(m)=\rho_A(m_A)+\rho_B(m_B)$，每步满足 (48.4)。

把每个 $(a,b)\in C$ 作为二分支撑图 $A\sqcup B$ 的一条边，边的控制值为 $c(a+b)=\ell_A(a)+\ell_B(b)$。置

$$
\begin{gathered}
\varepsilon_A=\operatorname{rank}\ell_A\in\{0,1\},\quad
\varepsilon_B=\operatorname{rank}\ell_B\in\{0,1\},\quad
\varepsilon_A+\varepsilon_B\ge1,\\
A_\epsilon=\{a:\ell_A(a)=\epsilon\},\qquad
B_\delta=\{b:\ell_B(b)=\delta\},\\
h=\mathbf1_{\{\text{某个支撑连通分量含两条控制值不同的边}\}}.
\end{gathered}
\tag{49.2}
$$

称后一种分量为硬分量。满投影保证没有孤立顶点，且 $C\ne\varnothing$。不同分量可以带不同控制值。

本节容量最小值取遍满足此合同、并且存在某个整数 $K<\infty$ 使

$$
\forall m_0\in I_C\ \forall u\in\mathcal F^*,\qquad
\operatorname{Comm}(m_0,u)\le K
\tag{49.3}
$$

的全部正确控制器。$K$ 可随控制器改变；这不是预先固定一个预算后求容量前沿，也不要求先把 $K$ 最小化。

补充 (48.14) 的记号域：$\log_2|M|$ 与 $\lceil\log_2|M|\rceil$ 对有限非空实际状态集按通常意义定义，对无限实际状态集均约定为 $+\infty$；本节所有同类本地指标沿用此约定，集中联合编码指标对 $Q$ 也同样处理。因此有限基数下界可以量化无限控制器，而后述对数与固定宽度最小值由有限达到者取得；不对无限基数直接作实对数运算。

### 49.2 永久零通信的精确支撑判据

**定理 49.2（初始共同控制恰好允许永久零通信）。** Claim status: open。在定义49.1下，以下条件等价：存在对所有实际初始化及全部动作词永久零通信的正确控制器；存在函数 $\kappa_A:A\to\mathbb F_2$、$\kappa_B:B\to\mathbb F_2$ 使

$$
c(a+b)=\kappa_A(a)=\kappa_B(b)\quad((a,b)\in C);
\tag{49.4}
$$

控制值在每个支撑连通分量上恒定，即 $h=0$；每个分量的边集都包含于某个控制份额矩形 $A_\epsilon\times B_\delta$。这里仅要求包含，不要求填满该矩形；也不要求所有分量给出同一控制值。

证明。先假设永久零通信。若 $\ell_B=0$，则初始控制本来就是 $\ell_A(a)$，可由左端确定。若 $\ell_B\ne0$，对每个 $a\in A$ 选 $b\in B$ 使 $\ell_B(b)=\ell_A(a)$，得到 $a+b\in W$；因此 $p_A(W)=A$。这些 $a+b$ 只用来证明线性投影满射，不把它们当作 $C$ 中的准备。由于 $A\ne0$ 且 $e_1,\ldots,e_d$ 张成 $W$，存在一个 $i$ 满足 $\alpha_i\ne0$。从初始化立即执行这个 $N_i$：同一实际左纤维上的两条边有相同左持久状态 $\iota_A(a)$，零位协议的根及终端更新均由本端状态决定，故新左读出相同。正确性要求它等于 $\alpha_i c(a+b)$，非零 $\alpha_i$ 迫使这两条边的控制值相同。满投影遂给出 $\kappa_A$。交换左右，以 $\ell_A=0$ 的直接读出情形或 $p_B(W)=B$ 的非零系数情形，得到 $\kappa_B$。这证明 (49.4)。

式 (49.4) 使控制沿共端点邻接保持，故沿整条支撑路径恒定。反向，分量常值可赋给该分量内的左右顶点，得到两个函数。若分量控制为 $q$，同一个左顶点相邻的所有右顶点具有同一 $\ell_B$ 值，同一个右顶点相邻的所有左顶点具有同一 $\ell_A$ 值；沿路径传播，整个分量上的左份额为某个 $\epsilon$，右份额为某个 $\delta$，且 $q=\epsilon+\delta$。这正是所述矩形包含。反向由线性式立即得到分量控制恒定。以上因子化与共同商是 RRO 主卷第76—77节的机制在实际源 $C$ 上的应用，不另主张新的通用静态判据。

最后由 (49.4) 构造动态控制器。两端分别把 $q$ 初始化为自己的 $\kappa_A(a),\kappa_B(b)$；每个公开基平移 $\tau_e$ 在更新原投影的同时，把本端 $q$ 改为 $q+c(e)$；每个 $N_i$ 用本端旧 $q$ 写出 $\alpha_iq$ 或 $\beta_iq$，然后将 $q$ 置零。所有根均为叶，全部更新局部。归纳可得两个缓存始终相同且等于当前 $c(R(m))$，故永久零通信。$C$ 无须对动作不变；初始函数 $\kappa_A,\kappa_B$ 只用于初始化，不能把它们重新应用于任意当前投影来代替缓存更新。证毕。

### 49.3 预算饱和后的静默容量

**引理 49.3（任意准备下的静默后继与逐纤维基数界）。** Claim status: open。任一满足 (49.3) 的正确控制器都有一个非空、对全部动作封闭的实际后继集 $H\subseteq Q$，其中全部动作成本零，且 $R(H)=V$。记 $H_A,H_B$ 为其实际本地投影，则

$$
\begin{gathered}
|H_A\cap\rho_A^{-1}(a)|\ge2^{\varepsilon_B}\quad(a\in A),\qquad
|H_B\cap\rho_B^{-1}(b)|\ge2^{\varepsilon_A}\quad(b\in B),\\
|H\cap R^{-1}(z)|\ge1\quad(z\in V).
\end{gathered}
\tag{49.5}
$$

证明。把量词完整地放进成本集

$$
\mathcal K=\{\operatorname{Comm}(m_0,u):m_0\in I_C,\ u\in\mathcal F^*\}
 \subseteq\{0,1,\ldots,K\}.
\tag{49.6}
$$

它非空且为有界整数集，故最大值 $K_*$ 在一次实际有限执行 $(m_0,u_*)$ 上达到。令 $m_*=T_{u_*}m_0$，$H=\{T_vm_*:v\in\mathcal F^*\}$。若某个后继再有正费动作，将该有限后继词和这个动作接到 $u_*$ 后就超过 $K_*$。故 $H$ 的每步都零费，且按定义封闭。任意目标 $z$ 都可由 $R(m_*)$ 经一个总定义基平移词取得，所以 $R(H)=V$。最大值来自执行成本的整数有界性；这里完全没有用 $Q$ 有限。

若 $\varepsilon_B=0$，覆盖性给每个左读出至少一态。若 $\varepsilon_B=1$，固定 $a$，选 $b_0,b_1$ 使 $c(a+b_j)=j$。覆盖性分别给实际 $m^{(j)}\in H$，读出为 $a+b_j$。由定理49.2证明中的线性论证，存在 $\alpha_i\ne0$。若这两个实际对有相同左持久状态，立即可执行的同一 $N_i$ 在两者上都零位，故左终端更新相同；指定读出却分别为 $0,\alpha_i$，矛盾。于是每个左纤维至少两态。左右交换给右界，联合界直接来自覆盖。两个被比较的状态各自在 $H$ 中，没有把它们的边缘拼成新输入。即使 $h=0$，优化范围中仍可有选择通信的其他控制器；上述必要界同样约束它们，未先假定被比较控制器永久零通信。证毕。

### 49.4 硬分量沿每个实际平移词的搬运

**引理 49.4（固定重写的内部根覆盖与两端分离）。** Claim status: open。若 $h=1$，则对任一正确控制器，可以选一个固定重写 $N_{i_*}$ 及一个由纯平移前缀实际到达的集合 $S_{\rm pre}\subseteq Q$，使 $R(S_{\rm pre})=V$，并且这个重写在 $S_{\rm pre}$ 上的共同根全部为内部节点。若该控制器还有统一有限累计预算，则 $S_{\rm pre}$ 与引理49.3的 $H$ 在每一端的投影均不交。

证明。取一个硬分量 $E\subseteq C$。连接两条不同控制边的有限支撑路径上，必有相邻两条边的控制不同。先设它们为 $(a_*,b_0),(a_*,b_1)$。于是 $\ell_B\ne0$，由 $p_A(W)=A\ne0$ 可固定一个 $i_*$ 满足 $\alpha_{i_*}\ne0$。这个重写的选择以后不随平移词改变。若相邻边共右端点，则交换左右并固定 $\beta_{i_*}\ne0$ 的重写，下面论证完全对偶。

现在任取一个固定的纯平移词 $u$，把同一个词应用于 $E$ 的全部初始边。每个基平移都零位，且根与终端更新局部，故逐步复合得到本地函数 $F_{A,u},F_{B,u}$，满足

$$
\begin{gathered}
T_u(\iota_A(a),\iota_B(b))=(F_{A,u}(a),F_{B,u}(b))\quad((a,b)\in E),\\
\rho_A(F_{A,u}(a))=a+p_A(t_u),\qquad
\rho_B(F_{B,u}(b))=b+p_B(t_u),\qquad
t_u=\sum_{\tau_e\text{ 出现在 }u\text{ 中}}e.
\end{gathered}
\tag{49.7}
$$

这些函数只须定义在 $E$ 的相应顶点上。固定词下的当前读出平移是单射，所以两端的顶点映射各自单射；它们将 $E$ 送成实际状态支撑中的一个连通图 $E_u$。同一对见证边在 $E_u$ 中仍共左端点 $F_{A,u}(a_*)$，当前控制为原控制各加 $c(t_u)$，仍然相反。

共同根合同使固定动作 $N_{i_*}$ 的根标识沿 $E_u$ 的所有边恒定。若此根为叶，见证两边的左端收到同一个空位串，从同一个旧状态产生同一新读出；正确性却要求分别输出 $\alpha_{i_*}q$ 与 $\alpha_{i_*}(q+1)$，二者不同。因此这个共同根为内部节点，整个 $E_u$ 都须至少发送一位。根的具体标识可以随 $u$ 改变；所需不变量只是“内部”这一性质。

取

$$
S_{\rm pre}=\bigcup_{u\in\{\tau_1,\ldots,\tau_d,\tau_c\}^*}E_u.
\tag{49.8}
$$

固定 $E$ 中一条实际边，从它出发，基平移词可把当前读出送到任意 $z\in V$，故 $R(S_{\rm pre})=V$。尤其每个当前左摘要、右摘要和联合当前态都有一个实际的重写前内部根状态。若存在统一有限预算，$H$ 上的 $N_{i_*}$ 根全为叶。倘若 $S_{\rm pre}$ 中某态和 $H$ 中某态有相同左状态，本地根函数在同一输入上就既选内部根又选叶根，矛盾；右端同理。故

$$
\pi_A(S_{\rm pre})\cap H_A=\varnothing,\qquad
\pi_B(S_{\rm pre})\cap H_B=\varnothing,
\qquad S_{\rm pre}\cap H=\varnothing.
\tag{49.9}
$$

这里只对每个固定词分别建立局部函数，没有断言净平移相同的两个词具有相同记忆效应，也没有把记忆上的平移当作群作用。用于覆盖的词是量词下的真实执行见证，不是执行者取得的免费私人信号。零费平移同时保证固定词的本地分解与这些免费前缀的合法使用；本节不作有费平移的推广。证毕。

### 49.5 全部统一有限预算控制器的同时锐界

**定理 49.5（由控制秩与硬分量决定的实际容量）。** Claim status: open。在定义49.1下，对每个满足某个统一有限累计预算的正确控制器，逐当前读出有

$$
\begin{gathered}
|\rho_A^{-1}(a)|\ge2^{\varepsilon_B}+h\quad(a\in A),\qquad
|\rho_B^{-1}(b)|\ge2^{\varepsilon_A}+h\quad(b\in B),\\
|Q\cap R^{-1}(z)|\ge1+h\quad(z\in V).
\end{gathered}
\tag{49.10}
$$

允许任意乃至无限本地状态集。三个总容量最小值为

$$
|M_A|_{\min}=(2^{\varepsilon_B}+h)|A|,\qquad
|M_B|_{\min}=(2^{\varepsilon_A}+h)|B|,\qquad
|Q|_{\min}=(1+h)|V|,
\tag{49.11}
$$

且由同一个有限控制器同时达到。$h=0$ 的达到者永久零通信；$h=1$ 的达到者累计通信至多两位，此处不声称这个预算对给定 $C$ 最优。

证明。引理49.3给每个本地纤维的 $2^{\varepsilon_B},2^{\varepsilon_A}$ 个静默状态，以及每个联合读出的一态。若 $h=1$，引理49.4的 $S_{\rm pre}$ 在每个当前 $z$ 上非空，在每个本地摘要上也非空；它与静默集合在左右两端分别不交，因而每个纤维都再加一态。若 $h=0$，直接使用静默界即可。固定读出的不同纤维互斥，求和得到 (49.11) 的下界。这些都是有限数目的实际状态见证，不要求总体有限，也不把“有一个硬分量”加强为“整个支撑图连通”。

构造达到者时，先定义受限已知状态集

$$
\begin{aligned}
\mathcal M_A^{\mathsf K}
 &=\{(a,\mathsf K,q):q\in\ell_A(a)+\ell_B(B)\},\\
\mathcal M_B^{\mathsf K}
 &=\{(b,\mathsf K,q):q\in\ell_B(b)+\ell_A(A)\},\\
\mathcal Q^{\mathsf K}
 &=\{((a,\mathsf K,q),(b,\mathsf K,q)):
       a\in A,b\in B,\ q=\ell_A(a)+\ell_B(b)\}.
\end{aligned}
\tag{49.12}
$$

当远端控制秩为零时，已知 $q$ 已由本端摘要限定，故不能把这一层计作任意的两倍笛卡尔积。若 $h=0$，只用这层，以

$$
\iota_A(a)=(a,\mathsf K,\kappa_A(a)),\qquad
\iota_B(b)=(b,\mathsf K,\kappa_B(b))
\tag{49.13}
$$

局部初始化。满投影和 (49.4) 保证这两个初始化的值属于受限集合。平移更新原摘要与 $q\mapsto q+c(e)$；重写用本端 $q$ 输出本端系数乘 $q$，再置 $q=0$，如定理49.2。任取一条初始边，纯平移已能使当前读出覆盖 $V$；已知控制不变量使得到的状态恰为 $\mathcal Q^{\mathsf K}$ 中对应的状态。因此这层的每个联合状态及每个本地状态都实际出现。

若 $h=1$，另加未知层

$$
\begin{gathered}
\mathcal M_A^?=\{(a,?):a\in A\},\qquad
\mathcal M_B^?=\{(b,?):b\in B\},\\
\mathcal Q^?=\{((a,?),(b,?)):a\in A,b\in B\},\qquad
\iota_A(a)=(a,?),\quad\iota_B(b)=(b,?).
\end{gathered}
\tag{49.14}
$$

初始化的实际对仍仅取 $C$。平移保持未知标记，在已知层则按前述规则更新 $q$。首次 $N_i$ 在未知层执行第48.4节协议：若 $\alpha_i\ne0$ 且 $\ell_B\ne0$，右端传旧 $\ell_B(b)$；若 $\beta_i\ne0$ 且 $\ell_A\ne0$，左端传旧 $\ell_A(a)$；需要两位时固定先右后左。端点从自己的旧摘要和所收位计算必要的输出，系数为零的一端直接写零。已知层选择叶根并用旧 $q$ 计算。两种模式末尾均进入共同已知状态，所存当前控制为零，因为 $c(N_i z)=0$。模式由各端本地标记同步选择，不靠消息缺席判断；首次重写即便发送零位也进入已知层。

这逐动作证明了受限集合闭合及本地可执行性；之后的所有动作均免费。任取一条实际初始边，平移得到未知层全部 $V$；对任意实际初态执行一次重写，再作平移，得到已知层全部 $V$。因此准确的可达集合是

$$
\begin{array}{c|c|c|c}
h&M_A&M_B&Q\\ \hline
0&\mathcal M_A^{\mathsf K}&\mathcal M_B^{\mathsf K}&\mathcal Q^{\mathsf K}\\
1&\mathcal M_A^?\sqcup\mathcal M_A^{\mathsf K}
 &\mathcal M_B^?\sqcup\mathcal M_B^{\mathsf K}
 &\mathcal Q^?\sqcup\mathcal Q^{\mathsf K}
\end{array}
\tag{49.15}
$$

每个 $a$ 在已知层有恰 $2^{\varepsilon_B}$ 个允许 $q$，每个 $b$ 有恰 $2^{\varepsilon_A}$ 个，联合已知层每个 $z$ 恰一态；未知层每个本地摘要及每个 $z$ 又恰一态。得到 (49.11) 及逐纤维同时取等。每词至多首次重写付费，费用为 (48.8) 的 $C_i\le2$，所以构造确在所优化的控制器类内。证毕。

### 49.6 本地寄存器与集中编码的容量读数

**推论 49.6（有限达到者的对数与固定宽度）。** Claim status: open。在第49.1节的扩展实数约定下，同一优化范围中的最小值为

$$
\begin{aligned}
S_{\log,\min}
 &=D+\log_2\bigl((2^{\varepsilon_A}+h)(2^{\varepsilon_B}+h)\bigr),\\
B_{\mathrm{fix},\min}
 &=D+\left\lceil\log_2(2^{\varepsilon_B}+h)\right\rceil
      +\left\lceil\log_2(2^{\varepsilon_A}+h)\right\rceil\\
 &=D+\varepsilon_A+\varepsilon_B+2h,\\
B_{\mathrm{central},\min}
 &:=\min\left\lceil\log_2|Q|\right\rceil=D+h.
\end{aligned}
\tag{49.16}
$$

证明。对定理49.5的各必要容量取单调的对数或向上取整，同一有限达到者保证下界同时达到。因 $|A|=2^r,|B|=2^s$，整数维数可移出取整；对 $\varepsilon,h\in\{0,1\}$ 有 $\lceil\log_2(2^\varepsilon+h)\rceil=\varepsilon+h$，联合最小值为 $2^{D+h}$，得到各式。证毕。

单侧情形以下取 $\varepsilon_A=0,\varepsilon_B=1$，反向单侧只需交换左右：

$$
\begin{array}{c|c|c|c|c|c}
\text{控制分布}&h&(|M_A|,|M_B|)_{\min}&S_{\log,\min}&B_{\mathrm{fix},\min}&B_{\mathrm{central},\min}\\ \hline
\text{单侧}&0&(2|A|,|B|)&D+1&D+1&D\\
\text{单侧}&1&(3|A|,2|B|)&D+\log_2 6&D+3&D+1\\
\text{分散}&0&(2|A|,2|B|)&D+2&D+2&D\\
\text{分散}&1&(3|A|,3|B|)&D+\log_2 9&D+4&D+1
\end{array}
\tag{49.17}
$$

本地固定宽度允许分别给两个有限实际状态集编号，并由本地状态和本次位串更新；集中编码则只给整个实际联合像编号。后一编号不提供两端各自可访问、可更新的寄存器，不能替换前两项本地资源。程序描述长度、查表构造成本和运行时间不包含在这些容量指标内。

### 49.7 相同边数与分量规模下的不同容量

**例 49.7（准备关系可失效，所存当前控制仍有效）。** 取 $d=2$、$z=(x,y,c)$、$a=x,b=(y,c)$，令

$$
C_0=\{(x,(y,c)):c=x\}.
\tag{49.18}
$$

它有四条边，两个各含两条边的分量，投影充满两端；一个分量控制零，另一个控制一。取 $\kappa_A(x)=x$、$\kappa_B(y,c)=c$，有 $h=0$，定理49.5给同时最小容量 $(4,4,8)$。右端的控制已在原摘要中，左端持久保存 $q$；每个平移与重写按当前控制不变量更新即可。

$\tau_x$ 可把 $c=x$ 的初态送到不满足该关系的当前态，但不改变真实 $c$，所以保存的 $q$ 应保持。具体比较两次实际历史：从 $(0,0,0)$ 经 $\tau_x$ 到 $(1,0,0)$；从 $(1,0,1)$ 经空词仍为 $(1,0,1)$。两者当前 $x=1$ 相同，控制分别为零和一。重新令 $q=\kappa_A(x)=x$ 会使第一条历史随后的 $N_x$ 错误；正确缓存把这两次历史区分开。

在同一原摘要下，改为

$$
C_1=\{(x,(y,c)):x=y\},\qquad c\text{ 自由}.
\tag{49.19}
$$

仍然是四条边、两个各含两条边的分量、相同的满投影边缘；但每个分量都同时含 $c=0,1$ 的边，故 $h=1$，同时最小容量变为 $(6,8,16)$。因此边缘、边数和分量规模都不足以替代控制在实际边上的分布。

**例 49.8（一个硬分量已强制整行容量）。** 保持 $a=x,b=(y,c)$，令二位标签按 $(y,c)$ 顺序书写，并取

$$
C_2=\{(0,00),(0,01),(0,10),(1,11)\}.
\tag{49.20}
$$

三个共左端点的边构成一个硬分量，剩下一条边是简单分量；两个投影仍满。尽管图不连通，$h=1$ 已给容量 $(6,8,16)$。现在改用分散直和 $a=t=x+c,b=(x,y)$，在这些新坐标中采用同一四边标签图案；控制成为 $c=t+x$，三边分量依旧同时含零与一。此时 $\varepsilon_A=\varepsilon_B=1$，容量为 $(6,12,16)$。这是在各自固定直和下的两份准备，不能把更换摘要误作同一个物理准备关系保持不变。两例分别说明硬分量不必占满支撑，以及原投影上的控制秩仍参与容量。

### 49.8 准备可降低预算，容量最小化不等于预算分类

**例 49.9（分散控制中一次一位已足够）。** 取 $a=t=x+c,b=(x,y)$，准备关系为 $t=y$。右端可在初始化时仅由自己的 $(x,y)$ 得到当前 $q=x+y=c$，左端初始化未知。左状态写作 $(t,q_A)$，其中 $q_A\in\{?,0,1\}$；右状态为 $(x,y,q_B,k)$，$k=0$ 表示尚未重写，$k=1$ 表示双方已同步已知。初始化为

$$
q_A=?,\qquad q_B=x+y,\qquad k=0.
\tag{49.21}
$$

$\tau_x$ 翻左端 $t$ 和右端 $x$，$\tau_y$ 只翻右端 $y$，这两种平移都保持所存 $q_B$；$\tau_c$ 翻左端 $t$、右端 $q_B$，并翻转左端已知的 $q_A$，未知标记保持。一般地，平移仅在其控制增量非零时改变已存 $q$；不重新计算当前 $x+y$。始终有 $q_B=c$，且 $q_A=?\Leftrightarrow k=0$，在 $k=1$ 时两端已知值均等于当前控制。

首次 $N_x$ 由右端发送旧 $q_B$ 一位，左端从该位得到新 $t$，右端从自己的旧 $q_B$ 得到新 $x$，新 $y=0$；首次 $N_y$ 无通信，左端直接写 $t=0$，右端用旧 $q_B$ 写 $(x,y)=(0,q_B)$。任一重写均将两端控制缓存置零、右端 $k$ 置一；之后重写由两端各自缓存免费执行。两个模式在操作前已经可以分别从左端未知标记和右端 $k$ 同意选择，无须等待静默信号。因此每个动作词的累计通信至多一位，而同一分散直和的完整乘积准备在第48节有 $C_*=2$。

这份控制器的实际容量为 $(6,16,16)$：尚未重写时从一条初始边经平移覆盖全部八个 $z$，左端只有两个未知状态，右端有八个带 $k=0$ 且 $q_B=c$ 的状态；重写后平移又覆盖全部八个 $z$，左端有四个已知状态，右端有八个带 $k=1$ 的状态。两层联合各八态。该准备有硬分量，定理49.5的同时最小容量为 $(6,12,16)$；这个一位方案没有声称同时取得那些最小值。准备 $t=y$ 也可被后续平移破坏，正确性来自所存控制的更新。给定 $C$ 的完整最优预算分类及一位预算下的容量前沿留作后续问题，本节不据此例作推广。

### 49.9 来源、有限核验与结论边界

静态归属保持明确：RRO 主卷第76—77节给实际支撑路径与共同商；`D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.lean` 的 `commonCoarsening` 及 `concept_kernel_order_duality` 末项给两观察核之并的等价闭包。在本节取共同来源为 $C$、观察为两端投影，即得到分量语言。`D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean` 的 `refinement_iff_kernel_inclusion_on_effective_images` 在粗观察为初始控制、细观察为任一端投影时，精确对应 (49.4) 的该端静态恢复；满投影使其有效细像就是整个 $A$ 或 $B$。它并未保证初始化函数能在动作后重新应用。

动态归属也保留前提：`D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean` 的 `dynamic_closure_is_least` 要求候选细化已经满足 `InterventionClosed`，不能代替本节逐动作证明的当前控制不变量。`D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean` 的 `controlled_behavior_universal_property` 要求有限载体、满射实现以及更新和读出的交织；这些条件对任意带历史的分布式控制器并未自动成立，也不能直接给出两端可访问容量。Process Geometry 第3节及定义20.1所要求的共同实际载体、后继闭合和局部可访问字段，在这里由 $I_C$、其实际可达闭包 $Q$ 及协议合同承担。预算饱和步骤沿用第48.2节的整数最大值论证，首次重写构造沿用第48.4节；硬分量搬运和逐端静默分离的连接证明已在引理49.4中给出。

有限核验采用 $d=2$ 的独立逐项枚举：枚举 $\mathbb F_2^3$ 的全部56个有序非中心直和，以及每个直和的79份满投影准备，共4424份，其中 $h=0$ 为208份、$h=1$ 为4216份。分别以支撑连通性、两个本地控制函数的存在、份额矩形包含及每个首次重写的实际局部纤维输出一致性检验零通信判据，结果一致。对每个硬分量固定一对见证边和一个重写，再枚举长度不超过四的121个纯平移词，共核对533368个词见证；检验同词像的连通性、两端单射、控制差保持及固定端点输出冲突，并在保留词历史的局部状态中检验净平移相同而记忆不同的情形。

对达到构造，从各自实际 $I_C$ 作广度优先闭包，共得到69120个状态、345600条具名动作转移；逐项检查读出正确性、根的叶／内部模式、终端更新的端点局部性、已知控制不变量、精确可达容量及累计成本至多二位。例49.7—49.8的四份边集分别核得 $(4,4,8)$、$(6,8,16)$、$(6,8,16)$、$(6,12,16)$；例49.9另核对16个实际联合状态的80条转移及累计成本至多一位，容量为 $(6,16,16)$。这些有限结果验证所列有限支撑与具体构造，没有枚举任意控制器，不能替代引理49.3—49.4对任意状态集和任意词的普通证明。

本节限于二元标量控制、固定非中心直和、设计时已知的满投影准备、总具名动作、零费基平移及第48.1节的确定性局部协议合同。静态共同恢复、动态继续操作、双方可访问容量和集中编码分别使用各自的条件；没有从静态相关性推出准备关系永久保持，也没有从有限状态核算推出无限控制器分类。以上来源均为所列仓内接口；未增加外部文献断言。形式状态仍为 open，本节不改变既有机器账本或冻结状态。

## 49.99 追加锚
## 50. 准备决定的累计预算与一位通信下的三层记忆

本节补足第49.8节留下的正预算分类和一位预算容量前沿，保持第49.1节的实际准备与第48.1节的严格局部协议合同。结论为 repo-derived 的普通数学推导；新增命题的 Claim status: open，未获 Lean 核验，不主张原创性。承重连接是：同一个混合重写在累计一位的约束下强制根发送者，从而在两个端点各自的持久状态中分离两种控制拥有者和静默层。

### 50.1 实际支撑上的两种不确定性

**定义 50.1（分量不确定性与预算约束）。** 使用定义49.1的全部对象，只将其中的准备关系 $C$ 记为 $P$，以免与通信成本混淆。特别地，

$$
\begin{gathered}
d\ge2,\quad D=d+1,\quad V=\mathbb F_2^d\oplus\mathbb F_2=A\oplus B,
\quad W=\ker c=\langle e_1,\ldots,e_d\rangle,\\
\dim A=r>0,\quad\dim B=s>0,\quad r+s=D,\quad
\ell_A=c|_A,\quad\ell_B=c|_B,\\
\alpha_i=p_Ae_i,\quad\beta_i=p_Be_i,\quad
P\subseteq A\times B,\quad\pi_A(P)=A,\quad\pi_B(P)=B,\\
I_P=\{(\iota_A(a),\iota_B(b)):(a,b)\in P\},\qquad
\rho_A\iota_A=\operatorname{id}_A,\quad\rho_B\iota_B=\operatorname{id}_B.
\end{gathered}
\tag{50.1}
$$

$P$ 在设计时固定且双方已知，实际初始化只发生在 $P$ 的边上；本端只能用自己的初始摘要初始化。当前摘要始终是 $a=p_Az,b=p_Bz$，$M_A,M_B$ 是实际可达联合像 $Q$ 的两个投影。全部基平移总定义且零位，全部 $N_i(z)=c(z)e_i$ 总定义；公开动作词对来源独立，正确性和累计费用同时量化全部初始边及任意有限词。共同根由两端分别从本地旧持久状态与当前动作算出，二元发送和叶处写入满足 (48.5) 后的局部合同。计时、静默、旧词、对端状态均不提供额外免费输入，所有影响后续的标签和缓存都计入持久记忆。程序构造和运行成本不属于本节容量指标。

对实际二分支撑的每个连通分量 $H$，定义

$$
\begin{aligned}
d_A(H)=1
&\ \Longleftrightarrow\ \exists(a,b),(a,b')\in H,
       \ c(a+b)\ne c(a+b'),\\
d_B(H)=1
&\ \Longleftrightarrow\ \exists(a,b),(a',b)\in H,
       \ c(a+b)\ne c(a'+b).
\end{aligned}
\tag{50.2}
$$

否则相应值为零。$d_A(H)=0$ 恰指初始控制能从该分量的左顶点恢复，记其函数为 $\kappa_{A,H}$；$d_B(H)=0$ 对偶。每个顶点只属于一个分量，故端点由自己的初始摘要就能确定其分量及上述适用函数。沿用第49.2节的共同商判据，$(d_A,d_B)=(0,0)$ 恰是控制常值的简单分量，其余为硬分量；这里不重证通用共同商。

称 $(d_A,d_B)=(0,1)$ 为 A 拥有者分量，$(1,0)$ 为 B 拥有者分量，$(1,1)$ 为双方不确定分量，并置

$$
t_A=\mathbf1_{\{\exists H:(d_A(H),d_B(H))=(0,1)\}},\qquad
t_B=\mathbf1_{\{\exists H:(d_A(H),d_B(H))=(1,0)\}}.
\tag{50.3}
$$

“拥有者”仅描述初始信息及下文搬运出的层，不声称初始恢复函数在任意动作后仍有效。对固定整数 $K\ge0$，预算为 $K$ 指 (49.3) 中对所有初始边和所有有限词的同一个上界 $K$。容量优化仍允许无限候选记忆，有限／无限状态集的对数和固定宽度沿用第49.1节约定；最小值将由有限控制器取得。

### 50.2 初始一次重写的分量最坏费用

**定理 50.2（实际边上的初始成本）。** Claim status: open。从局部初始化立即执行 $N_i$，在分量 $H$ 的全部实际边上取最坏费用，再对满足局部合同的正确协议取最小，得到

$$
C_{i,H}=\mathbf1_{\{\alpha_i\ne0\}}d_A(H)
        +\mathbf1_{\{\beta_i\ne0\}}d_B(H).
\tag{50.4}
$$

这是一个分量上的最小最坏成本，不是每条边都恰付该费用的断言，也不把稀疏支撑补成矩形。

证明。左项为一时，两条实际边共左顶点而控制相反，要求的左输出 $\alpha_i c$ 不同，因此零通信不可能。右项为一时对偶。若两项均为一，假设所有实际边上至多一位。局部初始化的单射性与共同根合同使同一分量的根标识恒定，这是第49.4节使用的支撑路径结论。根不能为叶；若固定发送者为 A，它在这些一次动作执行中收不到任何位，相同旧左状态决定同一发送位和同一终端写入，与左项的见证边矛盾。发送者为 B 时由右项矛盾。所以最坏费用至少二位。此论证只比较实际见证边，未使用不存在的交叉边或矩形叶集。

上界按分量选择公开协议。左端输出系数非零且 $d_A(H)=1$ 时，B 发送自己的旧份额 $\ell_B(b)$ 一位，A 用自己的 $\ell_A(a)$ 求控制；右端的对称条件成立时，A 发送旧 $\ell_A(a)$。需要两位时固定先 B 后 A。若相应 $d$ 为零，端点用 $\kappa_{A,H}(a)$ 或 $\kappa_{B,H}(b)$；若输出系数为零，则直接写零。分量由各端本地初始摘要决定，故根选择合法，费用等于右侧。每次重写后的控制都是零，可以将这一事实局部写入双方缓存以供续接。这里的初始解码只使用旧初始顶点，未把它当作永久可重算的控制公式。证毕。

### 50.3 精确的统一累计预算

**定理 50.3（零、一、二位的完整分类）。** Claim status: open。在定义50.1下，任意有限持久记忆正确控制器的最小统一累计预算为

$$
K_{\min}=\max_{1\le i\le d,\ H}C_{i,H}
=\begin{cases}
0,&\text{全部分量简单},\\
1,&\text{存在硬分量，但不存在双方不确定分量},\\
2,&\text{存在双方不确定分量}.
\end{cases}
\tag{50.5}
$$

下界也适用于无限候选记忆，有限达到者使两种优化范围具有相同最小值。

证明。累计预算至少支付从初始化立即执行的任意 $N_i$，故不小于 (50.4) 的最大值。须核实这个最大值确实检测所有硬分量。若 $d_A(H)=1$，见证边给 $\ell_B\ne0$。对每个 $a\in A$ 可选 $b\in B$ 使 $\ell_B(b)=\ell_A(a)$，于是 $a+b\in W$，所以 $p_A(W)=A\ne0$，某个 $\alpha_i\ne0$。这一步只是线性投影论证，所选 $(a,b)$ 不被宣称属于 $P$。$d_B(H)=1$ 时交换左右，得到某个 $\beta_i\ne0$。

双方不确定还给 $\ell_A,\ell_B$ 均非零。此时必有一个混合数据基向量 $e_{i_*}$，使 $\alpha_{i_*},\beta_{i_*}$ 均非零。否则每个 $e_i$ 都完全落在 $A$ 或 $B$ 中，而 $e_i\in W$，将推出

$$
W\subseteq(A\cap W)\oplus(B\cap W),\qquad
\dim W=D-1> (r-1)+(s-1)=D-2,
\tag{50.6}
$$

矛盾。因此有双方不确定分量时，同一个该分量上的某次重写给成本二；无此分量而有硬分量时，最大值恰为一。

现给累计上界。全简单时用定理49.2的共同已知控制缓存，永久零通信。有双方不确定分量时，用第49.5节的未知／已知构造：全部初态未知，首次重写至多交换两份控制份额，然后双方进入已知控制零，后续免费。

剩余情形中，初始化按本端初始顶点的分量选共同阶段：A 拥有者分量选 $\mathsf A$，仅 A 缓存当前控制 $q=\kappa_{A,H}(a)$；B 拥有者分量选 $\mathsf B$ 并对偶缓存；简单分量选 $\mathsf Q$，双方各由本地顶点取得同一 $q$。这些阶段都是收费的本地持久标签。平移更新两端摘要、将已有缓存改为 $q+c(e)$，并保持阶段。首次重写在 $\mathsf A$ 阶段仅当 $\beta_i\ne0$ 时由 A 发送其旧 $q$ 一位，$\mathsf B$ 阶段仅当 $\alpha_i\ne0$ 时由 B 发送；拥有者用自己的缓存计算本端输出，未缓存控制的一端若输出系数为零则直接写零。$\mathsf Q$ 阶段由双方缓存免费计算。每个重写均进入 $\mathsf Q$ 并写入控制零，包括无需消息的重写；所有后续动作于是免费。根由阶段及当前动作分别局部决定，不靠是否收到消息来辨识阶段。有限摘要、三种阶段和每端至多一个控制位给有限状态控制器，累计费用至多一。第50.5节将在分散控制下给出其准确实际容量。证毕。

### 50.4 同一个混合重写强制发送者并分离本地记忆

**定理 50.4（一位预算的逐纤维必要容量）。** Claim status: open。再设 $\ell_A,\ell_B$ 均非零，且准备没有双方不确定分量。任意统一累计预算至多一位的正确控制器，无论记忆有限与否，均满足

$$
\begin{gathered}
|\rho_A^{-1}(a)|\ge2+2t_A+t_B\quad(a\in A),\qquad
|\rho_B^{-1}(b)|\ge2+t_A+2t_B\quad(b\in B),\\
|Q\cap R^{-1}(z)|\ge1+t_A+t_B\quad(z\in V).
\end{gathered}
\tag{50.7}
$$

证明。用 (50.6) 的维数论证固定一个 $N_{i_*}$，使 $\alpha_{i_*},\beta_{i_*}\ne0$；下面所有分量、所有词及两个端点始终使用这一个动作。

先取任一 A 拥有者分量 $H$，其中有共右顶点、控制相反的两条实际边。对每个固定的纯平移词 $u$，调用引理49.4的固定词搬运：由零位局部更新复合得到 $F_{A,u},F_{B,u}$，当前摘要分别加上固定投影位移，故两端顶点映射单射，像 $H_u$ 仍连通，见证边仍共同一右持久状态且当前控制相反。这里未要求两个净平移相同的词对记忆有相同作用。

$N_{i_*}$ 的共同根在 $H_u$ 上恒定。它不能为叶，因为右输出 $\beta_{i_*}c$ 在那两条见证边上不同。它也不能以 B 为根发送者：这些实际运行的平移前缀费用为零，总预算至多一，所以一旦 B 发送一位，该次动作就必须停止；B 收不到信息，其发送位、终端更新及新右输出全由自己的旧状态决定。见证边的旧右状态相同，新右输出却必须不同，矛盾。因此整个 $H_u$ 上的根发送者被强制为 A。这个论证不假设所发位字面等于控制位。对 B 拥有者分量，完全对偶地强制根发送者为 B。

分别取所有存在的相应分量和所有实际纯平移词之像的并：

$$
S_A=\bigcup_{H\text{ 为 A 拥有者分量}}\ \bigcup_{u\text{ 为纯平移词}}H_u,
\qquad
S_B=\bigcup_{H\text{ 为 B 拥有者分量}}\ \bigcup_{u\text{ 为纯平移词}}H_u.
\tag{50.8}
$$

若 $t_A=1$，固定一条 A 拥有者分量的实际边，改变实际平移词就能把它的读出送到任意 $z\in V$，所以 $R(S_A)=V$；$t_B=1$ 时 $R(S_B)=V$。这是各词之并的覆盖，不是每个固定词的单个分量都覆盖 $V$。选词只提供全称正确性量词下的实际执行见证，不给端点免费读取旧词的权限。

在 $S_A$ 中固定当前左摘要 $a$。因 $\ell_B\ne0$，可选当前控制分别为零、一的两个 $z=a+b$；覆盖性各给一实际状态。若其左持久状态相同，执行同一 $N_{i_*}$ 时，A 均为唯一发送者，收不到信息。它的发送位和终端写入均由同一个旧状态决定，故左输出相同；正确性却要求输出 $0$ 与 $\alpha_{i_*}$。所以每个当前 $a$ 至少有两个 A 拥有者层的左状态。每个当前 $b$ 至少有一个右状态，直接由覆盖性得到。B 拥有者层对偶给每个左纤维至少一态、右纤维至少两态。该乘数二来自发送者无输入的因果约束，不依赖对消息编码的指定。

再调用引理49.3的饱和静默后继集 $\mathcal H$。其存在只需实际累计费用集 $\{\operatorname{Comm}(m_0,u):m_0\in I_P,u\in\mathcal F^*\}$ 为非空有界整数集，从而最大值在某次实际有限执行上达到；完全不需要候选记忆有限。$R(\mathcal H)=V$，其每个动作零位。分散控制下，(49.5) 给每个左、右纤维各至少两态，每个联合读出至少一态。

关键是上述三层能在两端分别相加。对固定的 $N_{i_*}$，共同根标识的“叶／根发送者 A／根发送者 B”分类是各端本地旧状态的函数，记为 $\chi_A,\chi_B$，且在实际联合状态上相等。已有结论为

$$
\begin{array}{c|ccc}
\text{实际层}&S_A&S_B&\mathcal H\\ \hline
\chi_A\text{ 与 }\chi_B&\text{发送者 A}&\text{发送者 B}&\text{叶}
\end{array}
\tag{50.9}
$$

故三层在每个端点的投影均两两不交；例如同一左持久状态不可能使同一本地根函数同时给 A 发送和 B 发送。联合层亦不交。逐纤维的必要乘数于是为

$$
\begin{array}{c|ccc}
\text{实际层}&\text{每个 }a&\text{每个 }b&\text{每个 }z\\ \hline
\mathcal H&2&2&1\\
S_A\ (t_A=1)&2&1&1\\
S_B\ (t_B=1)&1&2&1
\end{array}
\tag{50.10}
$$

将存在的行相加得到 (50.7)。所比较的状态各自来自实际执行，没有把边缘状态任意拼成输入，也没有引入外部阶段选择器、轮次或历史词。证毕。

### 50.5 带本地阶段标签的同时有限达到者

**定理 50.5（三种实际层的同时锐容量）。** Claim status: open。在定理50.4的假设下，对全部预算至多一位的正确控制器取最小，有

$$
|M_A|_{\min}=(2+2t_A+t_B)|A|,\qquad
|M_B|_{\min}=(2+t_A+2t_B)|B|,\qquad
|Q|_{\min}=(1+t_A+t_B)|V|.
\tag{50.11}
$$

同一个有限控制器同时取得这三个最小值，并在 (50.7) 的每个当前纤维上取等。

证明。下界将 (50.7) 在互斥的当前读出纤维上求和即可。构造取阶段 $\mathsf A,\mathsf B,\mathsf Q$，本地状态依次写为“阶段、当前摘要、控制缓存”，$\bot$ 表示本端不缓存控制。对每个 $z=a+b$，令 $q=c(z)$，定义联合态

$$
\begin{aligned}
m^{\mathsf A}(z)&=((\mathsf A,a,q),(\mathsf A,b,\bot)),\\
m^{\mathsf B}(z)&=((\mathsf B,a,\bot),(\mathsf B,b,q)),\\
m^{\mathsf Q}(z)&=((\mathsf Q,a,q),(\mathsf Q,b,q)).
\end{aligned}
\tag{50.12}
$$

$\mathsf Q$ 必取，$\mathsf A$ 仅在 $t_A=1$ 时取，$\mathsf B$ 仅在 $t_B=1$ 时取。两端的阶段标签都属于各自持久状态；共同 $q$ 的关系约束实际联合像，而非许可任意组合两个本地缓存。

初始化使用第50.3节的分量规则。A 拥有者分量中，A 写入本地 $\kappa_{A,H}(a)$、B 写 $\bot$，两端都选 $\mathsf A$；B 拥有者分量对偶；简单分量由两端本地常值解码选 $\mathsf Q$。同一初始顶点所属的分量唯一，所以这确实是两个函数 $\iota_A(a),\iota_B(b)$，无需向本端传入另一端顶点。分量信息用于初始化选标签，后续不额外保存或免费读取旧分量。

平移 $\tau_e$ 将本端摘要加上 $p_Ae$ 或 $p_Be$，将每个非 $\bot$ 缓存更新为 $q+c(e)$，阶段不变。对重写 $N_i$，共同根和唯一可能的发送为

$$
\begin{array}{c|c|c}
\text{旧阶段}&\text{根及发送条件}&\text{发送位}\\ \hline
\mathsf A&\beta_i\ne0\text{ 时 A 发送，否则叶}&\text{A 的旧 }q\\
\mathsf B&\alpha_i\ne0\text{ 时 B 发送，否则叶}&\text{B 的旧 }q\\
\mathsf Q&\text{叶}&\text{无}
\end{array}
\tag{50.13}
$$

本端有缓存时用自己的旧 $q$ 计算 $\alpha_iq$ 或 $\beta_iq$；没有缓存且系数非零时用收到的一位；系数为零则写零。所有分支在末尾均将阶段写为 $\mathsf Q$、缓存写为零。即使本次不发消息，也作同样的阶段写入。根在操作前由本地标签和公开 $i$ 决定，所发位和终端更新只使用本端旧状态与本次位串，严格满足局部合同。

归纳可得每个已有缓存始终等于真实当前控制，重写后双方都知道新控制零。准备关系在平移后即使失效，缓存更新仍正确；从不重新套用初始 $\kappa$。首次重写以前全为免费平移，首次重写至多一位，此后均免费，故统一累计预算至多一。

令 $\mathcal T$ 包含 $\mathsf Q$，并仅在 $t_A=1$ 时包含 $\mathsf A$、在 $t_B=1$ 时包含 $\mathsf B$。准确的实际可达联合集为

$$
Q=\bigsqcup_{\mathsf X\in\mathcal T}\mathcal Q^{\mathsf X},
\qquad
\mathcal Q^{\mathsf X}=\{m^{\mathsf X}(z):z\in V\}.
\tag{50.14}
$$

一方面，逐动作规则保持这些集合之并；另一方面，每个存在的拥有者阶段有一条该类实际初始边，纯平移即使其读出覆盖全部 $V$。$\mathsf Q$ 若已有简单分量可同样得到；若没有，则任取一条实际初始边执行一次重写，再作纯平移。每个阶段由当前 $z$ 唯一确定 (50.12) 中的状态，所以这些覆盖给出该阶段全部且仅有的 $|V|$ 个实际联合态。

由于 $\ell_A,\ell_B$ 均非零，$\mathsf Q$ 的左右实际投影分别为 $2|A|,2|B|$；$\mathsf A$ 的投影为 $2|A|,|B|$；$\mathsf B$ 的投影为 $|A|,2|B|$。阶段标签使投影不交，各阶段的每个本地纤维具有上述固定乘数。相加即 (50.11)，且逐纤维取等。计数对象始终是 (50.14) 及其真实投影，不是名义上的 $M_A\times M_B$。证毕。

### 50.6 分散控制的完整整数预算容量表

**定理 50.6（原始容量、逐端取整与集中编号）。** Claim status: open。固定 $\ell_A,\ell_B\ne0$，仍限于定义50.1的同一标量合同。记 $h$ 为存在硬分量的指示量。对每个可行整数预算，原始容量的三个最小值同时达到。预算一且无双方不确定分量时，令 $f_A=2+2t_A+t_B$、$f_B=2+t_A+2t_B$、$g=1+t_A+t_B$，则

$$
\begin{aligned}
S_{\log,\min}&:=\min(\log_2|M_A|+\log_2|M_B|)=D+\log_2(f_Af_B),\\
B_{\mathrm{fix},\min}&:=\min(\lceil\log_2|M_A|\rceil+\lceil\log_2|M_B|\rceil)
 =D+\lceil\log_2f_A\rceil+\lceil\log_2f_B\rceil,\\
B_{\mathrm{central},\min}&:=\min\lceil\log_2|Q|\rceil=D+\lceil\log_2g\rceil.
\end{aligned}
\tag{50.15}
$$

全部整数预算的紧凑表如下。“仅 A”允许另有简单分量，指硬分量全为 A 拥有者型；“仅 B”对偶；“A、B 均有”仍排除双方不确定分量。不可行行不赋予容量最小值。

$$
\begin{array}{c|c|c|c|c|c}
\text{准备类型}&K&(|M_A|,|M_B|,|Q|)_{\min}&S_{\log,\min}&B_{\mathrm{fix},\min}&B_{\mathrm{central},\min}\\ \hline
h=0&K\ge0&(2|A|,2|B|,|V|)&D+2&D+2&D\\
\text{仅 A}&1&(4|A|,3|B|,2|V|)&D+\log_2 12&D+4&D+1\\
\text{仅 B}&1&(3|A|,4|B|,2|V|)&D+\log_2 12&D+4&D+1\\
\text{A、B 均有}&1&(5|A|,5|B|,3|V|)&D+\log_2 25&D+6&D+2\\
h=1&K\ge2&(3|A|,3|B|,2|V|)&D+\log_2 9&D+4&D+1\\
h=1&0&\text{不可行}&-&-&-\\
\text{有双方不确定分量}&1&\text{不可行}&-&-&-
\end{array}
\tag{50.16}
$$

证明。预算零的可行性由定理50.3给出，全简单时第49.5节的已知层达到下界。预算一的原始容量由定理50.5给出。任意有限整数 $K\ge2$ 的候选控制器都在定理49.5“存在某个统一有限预算”的优化范围内，因此容量不低于其下界；该定理的至多两位达到者已属于每个这样的预算类，故取等。由此更大预算不能再降容量，未将第49节的最小值误作每个较小预算下都可达到。

对数和逐端取整是单调函数，同一个有限达到者保证分别取最小与同时取最小一致。$|A|=2^r,|B|=2^s$ 使维数移出取整，分别得到表中 $D+2,D+4,D+6$。无限候选使用第49.1节的 $+\infty$ 约定，不改变这些有限最小值。集中指标只给实际联合像编号；它没有提供两端各自可访问和可更新的寄存器，不能以集中编号代替两份本地存储。证毕。

### 50.7 五条实际边给出取整后仍严格的分离

**定理 50.7（四维五边准备的两个锐达到者）。** Claim status: open。取 $d=3$、$z=(x_1,x_2,x_3,c)$，令

$$
\begin{gathered}
A=\langle e_c,e_1\rangle,\qquad B=\langle e_c+e_3,e_2\rangle,\\
a=a_0e_c+a_1e_1\equiv(a_0,a_1),\qquad
b=b_0(e_c+e_3)+b_1e_2\equiv(b_0,b_1),\\
z=(a_1,b_1,b_0,a_0+b_0),\qquad \ell_A(a)=a_0,\quad\ell_B(b)=b_0.
\end{gathered}
\tag{50.17}
$$

采用以下五条准备边，二位顶点按上述坐标顺序、四位源按 $(x_1,x_2,x_3,c)$ 顺序书写：

$$
\begin{array}{c|c|c|c}
\text{分量类型}&a&b&z\\ \hline
\text{A 拥有者}&00&00&0000\\
\text{A 拥有者}&10&00&0001\\
\text{B 拥有者}&01&01&1100\\
\text{B 拥有者}&01&11&1111\\
\text{简单}&11&10&1010
\end{array}
\tag{50.18}
$$

此时 $K_{\min}=1$；预算一的同时锐容量为 $(20,20,48)$，两端固定宽度之和为十位；预算二及以上的同时锐容量为 $(12,12,32)$，固定宽度之和为八位。

证明。式 (50.17) 是唯一的坐标分解，故确为两个非零二维空间的直和，且控制在两端均非零。五边的两个投影各为全部四个顶点；前两边构成 $(d_A,d_B)=(0,1)$ 分量，中间两边构成 $(1,0)$ 分量，最后一边为独立简单分量。因此 $t_A=t_B=1$，无双方不确定分量，定理50.3及表 (50.16) 适用。

同时也可将两个有限达到者写到这些坐标上。平移及已有缓存的变化为

$$
\begin{array}{c|c|c|c}
\text{平移}&\text{左摘要变化}&\text{右摘要变化}&\text{每个已有 }q\text{ 的变化}\\ \hline
\tau_1&a_1\mapsto a_1+1&\text{不变}&\text{不变}\\
\tau_2&\text{不变}&b_1\mapsto b_1+1&\text{不变}\\
\tau_3&a_0\mapsto a_0+1&b_0\mapsto b_0+1&\text{不变}\\
\tau_c&a_0\mapsto a_0+1&\text{不变}&q\mapsto q+1
\end{array}
\tag{50.19}
$$

阶段均保持，$\bot$ 不变。三个重写要求的当前输出以及一位达到者的通信为

$$
\begin{array}{c|c|c|c|c|c}
\text{重写}&\text{新 }a&\text{新 }b&\mathsf A\text{ 阶段}&\mathsf B\text{ 阶段}&\mathsf Q\text{ 阶段}\\ \hline
N_1&(0,q)&(0,0)&0&\text{B 向 A 一位}&0\\
N_2&(0,0)&(0,q)&\text{A 向 B 一位}&0&0\\
N_3&(q,0)&(q,0)&\text{A 向 B 一位}&\text{B 向 A 一位}&0
\end{array}
\tag{50.20}
$$

这里 $q$ 是动作前当前控制，表中零表示叶根，无消息；每个分支末尾都进入 $\mathsf Q$、新缓存为零。拥有者初始化及发送用自己的旧 $q$，接受端仅在自己的系数非零时需要这一位，各自的输出与阶段写入均满足端点局部性。三层各经实际平移覆盖十六个当前源；本地投影分别按第50.5节相加，得二十态、二十态及四十八个联合态。

两位达到者改用第49.5节的未知／已知两层，并使五条实际初始边全部初始化为未知。未知层的 $N_1$ 由 B 向 A 发送旧 $b_0$，$N_2$ 由 A 向 B 发送旧 $a_0$；$N_3$ 固定先 B 发送旧 $b_0$、再 A 发送旧 $a_0$。非零输出端用自己的旧份额和所收远端份额求 $q=a_0+b_0$。每次重写末尾都进入共同已知控制零，之后只用缓存免费执行；平移按 (50.19) 更新摘要及已有缓存。因此任意词最多首次重写付两位，且首次 $N_3$ 达到两位。未知层每端四态，已知层每端八态；两层各由实际执行覆盖十六个联合态，给 $(12,12,32)$。

最后分别取整可见

$$
\begin{aligned}
K=1:&\quad \lceil\log_2 20\rceil+\lceil\log_2 20\rceil=5+5=10,
\qquad \lceil\log_2 48\rceil=6,\\
K\ge2:&\quad \lceil\log_2 12\rceil+\lceil\log_2 12\rceil=4+4=8,
\qquad \lceil\log_2 32\rceil=5.
\end{aligned}
\tag{50.21}
$$

所以这份准备在固定二进制宽度上仍有严格的两位差；不是仅原始状态数不同而取整后相同的例子。必要性分别由定理50.4和定理49.5保证，坐标构造只负责达到这些界。证毕。

### 50.8 两种拥有者并存时的有限最小性

**定理 50.8（本合同内的维数与边数最小性）。** Claim status: open。在二元线性摘要和分散标量控制的本合同内，若两种硬拥有者类型均出现，则 $|A|,|B|\ge4$，从而 $D\ge4$。固定两端各四个顶点并要求满投影时，四条边全部简单；定理50.7的五条边是使两种拥有者并存的最少边数。

证明。A 拥有者分量有共右端点而控制不同的两条边，故至少占两个左顶点和一个右顶点。B 拥有者分量至少占一个左顶点和两个右顶点。两种类型不可能属于同一分量，故这些顶点集合两侧分别互斥，共需至少三个左顶点、三个右顶点。二元线性空间的基数是二的整数次幂，因而每侧至少四态，维数各至少二，得到 $D\ge4$。

在 $4\times4$ 的满投影支撑中，边数至少四；恰有四条边时，每一侧的四个顶点都至少关联一条边，其度数和恰为四，所以每个顶点的度都为一，支撑是完美匹配，每个分量只有一条边，全部简单。五边构造 (50.18) 则确有两种拥有者，且 $D=4$，同时达到所述边数与维数界。这只证明本合同及这两个明确条件下的最小性，不涉及非满投影、非线性摘要或其他动作族。证毕。

### 50.9 单一拥有者可在取整后隐藏原始差别

**定理 50.9（第49.8节中例49.9的锐化）。** Claim status: open。对第49.8节内部的例49.9，即 $d=2$、$a=t=x+c$、$b=(x,y)$、准备 $t=y$，预算一的同时最小容量为 $(6,16,16)$；预算二及以上为 $(6,12,16)$，两种预算的最小本地固定宽度之和均为七位。

证明。初始 $c=t+x$。每个固定 $t=y$ 的分量中，右顶点分别取 $(0,t),(1,t)$，共左顶点而控制相反，故 $d_A=1$。每个右顶点的 $t=y$ 唯一，右端由 $x+y$ 恢复控制，故 $d_B=0$。两个分量都是 B 拥有者型，$t_A=0,t_B=1$，并且两份原摘要上的控制限制均非零。将 $|A|=2,|B|=4,|V|=8,D=3$ 代入 (50.11)，得 $(6,16,16)$；将同一准备的 $h=1$ 代入第49.5节，得 $(6,12,16)$。分别固定宽度都是 $3+4=7$。所以例49.9原有一位构造在预算一内确已同时最优；它与允许两位时的原始右端容量不同，但取整抹去了差别。定理50.7的两种拥有者并存才在所示实例中保留严格的固定宽度分离。证毕。

### 50.10 接口归属与适用边界

共同商的静态部分归 RRO 主卷第76—77节与 `D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.lean`：`commonCoarsening` 取两观察核之上确界的商，`concept_kernel_order_duality` 末项将其核识别为两核之并的等价闭包。在本节共同来源 $P$ 上取两端投影，就是第49节已使用的支撑分量。`D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean` 的 `refinement_iff_kernel_inclusion_on_effective_images` 给有效像上的唯一因子化与核包含的等价；对分量边集取控制为粗观察、本端顶点为细观察，对应 $d_A=0$ 或 $d_B=0$ 的初始恢复。它不保证平移后的旧解码可重用，也不蕴含本节的分布式容量。

固定词的本地单射与连通搬运直接采用引理49.4，任意有限累计预算的静默后继直接采用引理49.3，预算至少二位的容量行采用定理49.5。Process Geometry 第3节和定义20.1要求的共同实际载体、后继闭合及可访问字段，在这里分别由 $P$、$Q$ 和严格局部更新承担；其第9节的同路径费用求和对应 (48.6)，不提供免费计时器。本节额外的动态连接是定理50.4中同一个混合重写对根发送者的强制、发送者自身无输入所需的两重状态，以及三类根在两个本地投影上的分别分离。

上述结论仅量化固定非零直和、二元标量控制、设计时已知的满投影实际准备、全部总定义基平移及指定重写、零费平移、局部初始化与源独立公开动作词。有限达到者不限制下界中候选控制器的记忆大小。不存在把静态因子化直接提升为局部可执行性的步骤，也没有对向量控制、非满投影准备或任意动作族作推广。Claim status: open 与 repo-derived 的边界适用于全部新增结论。

## 50.99 追加锚
## 51. 有限齐性来源上的未来读出商与持久观察容量

Claim status: open。归属为 repo-derived synthesis：本节沿用第48.1节的持久协议合同、第49节的预算饱和与实际支撑搬运思路，以及已有完整未来行为商，给出任意非空准备下的同时锐容量及普通数学证明。结论不依赖第50节，不主张文献原创性或新增 Lean 核验。这里的任务是精确保持**全部未来动作后的物理当前读出**；消息、通信费用、完整事件档案和已经流逝的时钟不属于下面的行为等价，分别由协议约束或其他恢复任务承担。

### 51.1 实际来源、可逆免费动作与边界状态合同

**定义 51.1（总动作下的两端持久实现）。** 设 $X$ 为有限非空物理状态集，$p_A:X\to A$、$p_B:X\to B$ 均满射，且

$$
x\longmapsto(p_Ax,p_Bx)
\quad\text{单射},\qquad
C:=\{(p_Ax,p_Bx):x\in X\}\subseteq A\times B.
\tag{51.1}
$$

$A,B$ 因而有限非空；$C$ 可以是真子集。所有正确性要求只作用于实际来源及其实际后继，不补造 $A\times B$ 中缺失的组合。固定任意非空准备 $P\subseteq X$，允许 $p_A(P),p_B(P)$ 不满；模型与 $P$ 可作为固定知识编入协议规则，运行时不额外给出准备源的信息。

有限公开具名动作字母表为不交并 $\Sigma=\mathcal G_0\sqcup\mathcal F$。每个 $g\in\mathcal G_0$ 是 $X$ 上的置换，要求免费执行，且有局部下降

$$
p_Ag=\alpha_gp_A,\qquad p_Bg=\beta_gp_B,
\qquad \alpha_g\in\operatorname{Sym}(A),\quad
\beta_g\in\operatorname{Sym}(B).
\tag{51.2}
$$

$\mathcal G_0$ 生成的群 $G$ 在 $X$ 上传递。每个 $f\in\mathcal F$ 是任意总映射 $X\to X$，不要求线性或可逆。动作名可以不同而物理映射相同；全部名字在每个实际状态均合法。有限置换的逆可写成合法免费词：$g^{-1}=g^{\operatorname{ord}(g)-1}$，故 $G$ 的每个元素及其逆都有 $\mathcal G_0^*$ 中的表示。这里的群作用只声明在物理状态上。

沿用第48.1节的局部信息约束，具体规定如下。

1. 持久状态集 $M_A,M_B$ 可无限，读出为 $\rho_A:M_A\to A$、$\rho_B:M_B\to B$。总初始化函数满足 $\rho_A\iota_A=\operatorname{id}_A$、$\rho_B\iota_B=\operatorname{id}_B$，实际初态仅为
   $I_P=\{(\iota_A(p_Ax),\iota_B(p_Bx)):x\in P\}$。令 $Q$ 为 $I_P$ 经全部有限动作词的实际可达闭包，$M_A^{\rm act}=\operatorname{pr}_AQ$、$M_B^{\rm act}=\operatorname{pr}_BQ$。
2. 每个动作在每个 $m\in Q$ 上的协议均确定、总定义且有限停止，产生后继 $\widehat T_sm\in Q$ 与整数位费 $c(m,s)\ge0$。两当前读出必须构成 $C$ 中的一对；由联合单射性定义唯一的数学读出 $R:Q\to X$，并要求 $R(\widehat T_sm)=s(R(m))$。$R$ 不作为中央执行者向两端供给信息。
3. 对当前动作 $s$，两端分别从自己的旧持久状态选根，满足 $\sigma_{s,A}(m_A)=\sigma_{s,B}(m_B)$。该共同标识选定公开确定性二叉协议树。内部节点恰发送一个计费比特；发送者由动作、根标识和先前位串确定，发送位及叶处写回只能用本端旧状态、当前动作和本次已有位串。叶根只作局部零消息更新；内部根至少付一位。所有免费生成元在全部实际可达对上均为零费。
4. 动作是双方共同输入，正确性量化于每个动作词，不能靠私下选择公开动作或发送时间传递来源信息。没有免费外部选根器、静默检测器、运行档案、旧动作词、计时器或阶段寄存器。模式、引用、缓存、控制态及任何保留到下一动作的历史和通信内容，全部计入本地持久状态。
5. 容量计动作边界的状态数。一次动作内的临时位串与协议游标不另作边界状态收费，但全部发送位仍收费，临时信息一旦跨动作保留便须写入持久状态。模型或程序的构造成本、描述长度、协议树规模、执行时间及动作内峰值工作空间不是本节的边界状态指标。

对 $m_0\in I_P$、$w=s_1\cdots s_n$，令 $m_j=\widehat T_{s_j}m_{j-1}$。优化范围要求存在**某个统一有限整数** $K$，使

$$
\operatorname{Comm}(m_0,w):=\sum_{j=1}^n c(m_{j-1},s_j)\le K
\quad(m_0\in I_P,\ w\in\Sigma^*).
\tag{51.3}
$$

逐步有界不足以代替此条件。联合容量是 $|Q|$，不是 $|M_A^{\rm act}\times M_B^{\rm act}|$。下界按基数比较，适用于无限竞争者；有限非空状态集 $S$ 的对数容量和定宽二进制容量分别为 $\log_2|S|$、$\lceil\log_2|S|\rceil$，无限状态集的这两项均约定为 $+\infty$。下面同一有限构造达到三个基数最小值，因而也达到对它们分别取对数、取整以及两端定宽之和的最小值。

### 51.2 完整未来商与既有的有限区分深度

**定义 51.2（物理当前读出的完整未来核）。** 令 $T_w:X\to X$ 按词的先后顺序执行物理动作，$T_{\varnothing}=\operatorname{id}$。采用已有完整未来读出核

$$
xE_Ay\iff\forall w\in\Sigma^*,\ p_A(T_wx)=p_A(T_wy),
\qquad
xE_By\iff\forall w\in\Sigma^*,\ p_B(T_wx)=p_B(T_wy).
\tag{51.4}
$$

记 $\mathcal C_A=X/E_A$、$\mathcal C_B=X/E_B$，类数为 $k_A,k_B$。空词使 $E_A\subseteq\ker p_A$、$E_B\subseteq\ker p_B$。在任一动作后接任意词，立即得到两个关系的前向稳定性，故每个动作均诱导商上的局部更新，商类也确定当前读出。

这一构造直接对应 `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean` 的 `controlledBehavior`、`ControlledCompletion`。区分深度采用 `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.lean` 的 `controlled_finite_stability`：其有限非空 $Y,U,O$、满射 `readout` 在这里分别取 $X,\Sigma,A,p_A$，另一端取 $B,p_B$；声明已给出最小稳定深度不超过完整商类数减读出基数。Process Geometry 定理6.3(c)已给相应的完整商类数差界；其第29.4节命题29.1则在保留联合标签核的有限细化中给出原状态数减初层类数的同类计数界。以下只是这些界对本节物理读出的专门化。

具体地，从 $E_{A,0}=\ker p_A$ 出发，令

$$
xE_{A,n+1}y\iff xE_{A,n}y\ \land
\bigwedge_{s\in\Sigma}s(x)E_{A,n}s(y).
\tag{51.5}
$$

按词首字母归纳，$E_{A,n}$ 正是长度至多 $n$ 的读出相等。每次严格细化至少增加一个类，类数由 $|A|$ 起且不超过 $k_A$；一旦相邻两层相等，该关系就在每个动作下稳定，逐词归纳给它等于 $E_A$。因此

$$
n_A:=k_A-|A|,\quad n_B:=k_B-|B|,\quad
E_{A,n_A}=E_A,\quad E_{B,n_B}=E_B,\quad
L:=\max\{n_A,n_B\}.
\tag{51.6}
$$

若 $\Sigma=\varnothing$，上引 Lean 声明的 `Nonempty U` 不满足；此时只有空词，两商就是当前读出核，$n_A=n_B=L=0$，直接成立。对任意一对 $x\not E_Ay$，存在长度至多 $n_A$ 的区分词，B 端同理。此为逐对存在的有限视界，不要求一条通用词同时区分所有来源，也不声称 $L$ 最优。本节未增加通用分割细化算法或新的形式化基础设施。

### 51.3 齐性使各当前读出纤维具有同一商类数

**定理 51.3（物理可逆运输下的均匀纤维）。** 在定义51.1下，存在正整数 $r_A,r_B$，使每个 $p_A^{-1}(a)$ 恰含 $r_A$ 个 $E_A$ 类，每个 $p_B^{-1}(b)$ 恰含 $r_B$ 个 $E_B$ 类，且

$$
k_A=r_A|A|,\qquad k_B=r_B|B|,\qquad
\left|\{([x]_{E_A},[x]_{E_B}):x\in X\}\right|=|X|.
\tag{51.7}
$$

证明。任取 $g\in G$，它和逆均有合法免费物理词。前向稳定性双向应用给

$$
xE_Ay\iff g(x)E_Ag(y),\qquad
xE_By\iff g(x)E_Bg(y).
\tag{51.8}
$$

所以 $g$ 置换两商的类；由 (51.2)，它将 $p_A^{-1}(a)$ 内的类双射到 $p_A^{-1}(\alpha_g(a))$ 内的类。对任意 $a,a'$，满射性允许在两纤维各选物理代表，传递性给一个 $g$ 将前者送到后者，于是 $\alpha_g(a)=a'$。各纤维的类数相同且非零，得到 $r_A$；B 端相同。最后，两商类相同必使两当前读出均相同，联合单射性给来源相同，所以商类对的实际像有 $|X|$ 个元素。上述论证只在物理源及其商上使用群作用，没有把控制器的持久更新赋予群律。证毕。

### 51.4 准备缺陷与同时锐容量

先约定准备的一个二值缺陷：令 $h=0$ 当且仅当存在

$$
c_A:p_A(P)\to\mathcal C_A,\qquad c_B:p_B(P)\to\mathcal C_B,
\qquad [x]_{E_A}=c_A(p_Ax),\quad [x]_{E_B}=c_B(p_Bx)\quad(x\in P);
\tag{51.9}
$$

否则令 $h=1$。这仅是在实际初始投影像上的因子化；A 端失败恰指存在 $x,y\in P$，满足 $p_Ax=p_Ay$ 而 $x\not E_Ay$，B 端对称。

**定理 51.4（任意统一有限累计预算下的逐纤维锐界）。** 在定义51.1下，每个满足某个 (51.3) 的正确实现均满足

$$
\begin{aligned}
|M_A^{\rm act}\cap\rho_A^{-1}(a)|&\ge r_A+h &&(a\in A),\\
|M_B^{\rm act}\cap\rho_B^{-1}(b)|&\ge r_B+h &&(b\in B),\\
|Q\cap R^{-1}(x)|&\ge1+h &&(x\in X).
\end{aligned}
\tag{51.10}
$$

同一个有限实现同时使全部纤维取等。因此三个实际总容量的同时最小值是

$$
\boxed{\bigl(|M_A^{\rm act}|_{\min},|M_B^{\rm act}|_{\min},|Q|_{\min}\bigr)
=\bigl((r_A+h)|A|,(r_B+h)|B|,(1+h)|X|\bigr).}
\tag{51.11}
$$

存在永久零通信实现当且仅当 $h=0$。$h=1$ 时，一个同时达到者的统一累计预算不超过

$$
K_{\rm exch}=\lceil\log_2|A|\rceil+\lceil\log_2|B|\rceil.
\tag{51.12}
$$

这是在允许**某个**有限累计预算的控制器类中优化容量；(51.12)只是可达的充分预算，不给最小正预算，也不给另行固定更小预算时的容量前沿。存在合适编码和协议不意味着任意预定转移表都可实现。证明由以下两节的必要界和第51.7节的单一达到构造组成。

### 51.5 整数最大成本产生覆盖全来源的静默后继

**定理 51.5（无限竞争者也有静默容量下界）。** 对定理51.4的任一竞争者，存在非空且对全部动作封闭的实际集合 $H\subseteq Q$，其每步通信均零，$R(H)=X$；其两个本地投影在每个当前读出纤维分别至少有 $r_A,r_B$ 态。

证明。所有实际有限执行的累计费用构成

$$
\mathcal K=\{\operatorname{Comm}(m_0,w):m_0\in I_P,\ w\in\Sigma^*\}
\subseteq\{0,\ldots,K\}.
\tag{51.13}
$$

空词使集合非空，它的整数最大值 $K_*$ 必在某次实际执行 $(m_0,w_*)$ 上达到。设 $m_* =\widehat T_{w_*}m_0$，取全部后继
$H=\{\widehat T_vm_*:v\in\Sigma^*\}$。若其中任何一步付正费，将其前缀及该步接到 $w_*$ 后便超过 $K_*$；故 $H$ 封闭且永久静默。由免费物理群的传递性，从 $R(m_*)$ 可到任意 $x\in X$，相应真实执行在 $H$ 内，故 $R(H)=X$。最大值来自有界整数费用，未使用记忆集有限、有限状态紧致性或记忆更新的可逆性。

若 $m,n\in H$ 有同一 A 持久状态，则对每个共同未来词，两条实际执行均无通信。根和叶更新由本端旧状态及动作决定，逐步归纳使两条 A 局部轨迹一致，故 $R(m)E_AR(n)$。固定当前 $a$，覆盖性在 $p_A^{-1}(a)$ 中实现全部 $r_A$ 个未来类；不同类必须有不同 A 持久状态。B 端同理，每个 $x$ 也至少有一个联合状态。比较始终在两条实际执行之间进行，未拼接不相容的边缘。这给 (51.10) 中不含 $h$ 的部分。证毕。

### 51.6 有限共同根命中旗标与硬准备层的逐端分离

**定理 51.6（有界未来谓词将一个硬分量搬运到全来源）。** 若 $h=1$，对任一正确实现存在由实际免费前缀到达的 $T\subseteq Q$，满足 $R(T)=X$。若该实现有统一有限累计预算，则它与定理51.5的 $H$ 在**每一端**的投影均不交，因而给 (51.10) 各纤维再加一态。

证明。先对固定有限词 $w$ 定义一个局部根命中旗标 $\phi_A^w(m_A)$：只沿该词模拟本端叶根更新；检查下一动作的本地根，一遇内部根就立即返回一并停止，绝不越过内部根假装收到空消息；若词耗尽则返回零。B 端作同样定义。只需在实际可达的本地投影上定义；模拟尚未停止时可由一条真实零消息执行见证其可达性。

对每个实际对 $(m_A,m_B)\in Q$，两次模拟在首次内部根以前都等于真实执行。共同选根合同使它们同时遇到内部根，或都以叶根走完；因此对每个词有 $\phi_A^w(m_A)=\phi_B^w(m_B)$。用 (51.6) 的同一有限视界定义

$$
J_A^L(m_A)=\bigvee_{w\in\Sigma^*,\ |w|\le L}\phi_A^w(m_A),
\qquad
J_B^L(m_B)=\bigvee_{w\in\Sigma^*,\ |w|\le L}\phi_B^w(m_B).
\tag{51.14}
$$

字母表有限，故这是有限析取；两端在每条实际边上相等。它是用于证明状态分离的数学谓词，不是运行时 oracle，不给协议免费旗标、额外状态或未来词，也不要求实际执行者枚举这批词。$H$ 的每个本地投影状态的旗标均为零，因为其中任何后继都静默。

取 $h=1$ 的一个见证，先设在 A 端：$x,y\in P$、$p_Ax=p_Ay$、$x\not E_Ay$。将 $P$ 看作两类顶点 $p_A(P),p_B(P)$ 之间的实际二部支撑，边为 $(p_Az,p_Bz)$；两条见证边共左端点，处于同一连通分量 $P_0$。共享初始端点给共享本地初始化状态。

任取免费词 $u$，其物理置换记作 $g$。将**同一个词**应用于 $P_0$ 的所有初始边。每步均零消息，复合叶更新给两个各自的本地函数，所以共享端点仍有共享本地后继；所得实际支撑 $P_{0,u}\subseteq Q$ 连通。由 (51.14) 在每条边上的两端相等，旗标值沿任意有限支撑路径相传，故在 $P_{0,u}$ 的全部端点上为同一常值。此为每个运输后实际分量上的常值性，未要求整个准备图连通。

见证两边运输后仍有同一 A 持久状态，但由 (51.8)，$g(x)\not E_Ag(y)$。第51.2节给某个 $|v|\le n_A\le L$，使 $p_A(T_vg(x))\ne p_A(T_vg(y))$。若运输分量的共同旗标为零，则两条 $v$ 执行都不遇内部根，全程无通信；同一 A 初始持久状态经同一词的叶更新给同一末读出，与要求矛盾。因此整个 $P_{0,u}$ 的两端旗标都为一。B 端见证完全对称。

现在取

$$
T=\bigcup_{u\in\mathcal G_0^*}P_{0,u}.
\tag{51.15}
$$

固定 $P_0$ 的任一实际边，物理传递性使它经免费词覆盖 $X$，所以 $R(T)=X$。覆盖来自**所有实际免费前缀的并**，每一个 $P_{0,u}$ 无须单独覆盖 $X$。$T$ 的两端旗标为一，$H$ 的两端旗标为零，因而分别有

$$
\operatorname{pr}_AT\cap\operatorname{pr}_AH=\varnothing,
\qquad
\operatorname{pr}_BT\cap\operatorname{pr}_BH=\varnothing.
\tag{51.16}
$$

对每个当前读出，$T$ 贡献至少一个与相应静默本地状态不同的状态；对每个 $x$，$T$ 也贡献一个与 $H$ 不同的联合状态。只有先建立两端各自不交，才可分别相加得到 (51.10)；仅联合集合不交不足以相加本地容量。

这里的逆词只用于物理未来不等价的保存：若 $g(x)E_Ag(y)$，接一个表示 $g^{-1}$ 的合法物理词便推出 $xE_Ay$。它不必把执行 $u$ 后的持久记忆恢复原样；净物理置换相同的两个词也不必有相同的记忆效应。新的短区分词由既有有限视界给出，不从记忆上的群作用取得。证毕。

### 51.7 一个有限协议同时达到全部下界

**定理 51.7（商类已知层与当前标签未知层）。** 定理51.4的所有下界可由同一个有限实现同时达到。

证明。对 $i=A,B$，商类读出与动作更新为

$$
\bar p_i([x]_{E_i})=p_ix,\qquad
\bar s_i([x]_{E_i})=[s(x)]_{E_i}.
\tag{51.17}
$$

第51.2节保证它们良定义。若 $h=0$，直接以 $\mathcal C_A,\mathcal C_B$ 作持久状态，在 $p_A(P),p_B(P)$ 上用 (51.9) 初始化，全部动作均用 (51.17) 的局部叶更新。要求初始化为总函数时，在每个未使用标签 $a\notin p_A(P)$ 任取一个位于 $p_A^{-1}(a)$ 的商类，B 端同理；满射性保证可选，且保留 $\rho_i\iota_i=\operatorname{id}$。这些补值不被误当成额外准备源，也不把 (51.9) 强加于全体当前来源。

每个实际联合状态都恰为 $([x]_{E_A},[x]_{E_B})$。由任意一个准备点出发的免费词已覆盖 $X$，所以整个商类对实际像都出现，两个本地实际容量及联合容量恰为 $k_A,k_B,|X|$。

若 $h=1$，使用显式不交的两层

$$
\begin{aligned}
M_A&=(\{\mathsf U\}\times A)\sqcup(\{\mathsf K\}\times\mathcal C_A),\\
M_B&=(\{\mathsf U\}\times B)\sqcup(\{\mathsf K\}\times\mathcal C_B).
\end{aligned}
\tag{51.18}
$$

未知层读出标签，已知层读出商类。两端分别初始化为 $(\mathsf U,p_Ax)$、$(\mathsf U,p_Bx)$。在未知层，免费 $g$ 用 $\alpha_g,\beta_g$ 更新标签并保持 $\mathsf U$；在已知层，每个动作都用 (51.17) 且保持 $\mathsf K$。

首次在未知层执行 $f\in\mathcal F$ 时，预先固定 A 先、B 后的发送次序，两端各发自己**动作前当前标签**的固定长度二进制编码，长度分别为 $\lceil\log_2|A|\rceil,\lceil\log_2|B|\rceil$，零长度段直接省略。发送位只依赖自己的旧状态和公开游标；两端从自己的标签与所收编码取得 $(a,b)\in C$。只在这个实际像上，用联合单射性恢复唯一实际 $x$，然后各自写入 $(\mathsf K,[f(x)]_{E_A})$、$(\mathsf K,[f(x)]_{E_B})$。不需要给 $C$ 外的标签对发明物理来源。若协议语法要求给不可能到达的位串分支定义叶更新，可任取固定默认商类；实际正确性和容量只量化于 $Q$。

两端模式始终相同，且**分别存于各自状态中计费**，故当前模式与动作已足以局部同意选择叶根或固定交换树，无需免费阶段信息。已知层中以后永不通信，所以每个有限词至多付一次 (51.12)；所有实际动作均总定义、有限停止。若 $\mathcal F=\varnothing$，每个未来读出本来就是当前读出的局部置换复合，两商等于当前读出核，必有 $h=0$。所以 $h=1$ 确保存在可执行的首个附加动作。

未知层由一个准备点的免费前缀覆盖 $X$；执行一次附加动作进入已知层后，再由免费前缀覆盖 $X$。准确的联合实际集合因而是

$$
\begin{aligned}
Q^{\mathsf U}&=\{((\mathsf U,p_Ax),(\mathsf U,p_Bx)):x\in X\},\\
Q^{\mathsf K}&=\{((\mathsf K,[x]_{E_A}),(\mathsf K,[x]_{E_B})):x\in X\},\\
Q&=Q^{\mathsf U}\sqcup Q^{\mathsf K}\quad(h=1).
\end{aligned}
\tag{51.19}
$$

两个联合层各 $|X|$ 态，而非任意本地状态的笛卡尔积。每个 A 标签在未知层恰有一态、在已知层恰有 $r_A$ 态，B 端为一态加 $r_B$ 态；每个物理 $x$ 在每层恰有一联合态。于是同时达到 (51.10)—(51.11)。取固定读出的互斥纤维求和，亦完成总容量的必要界。

最后，任意永久零通信协议都使每个未来本地读出成为初始本地持久状态的函数。严格局部初始化使共 A 准备标签的任意两源属于同一 $E_A$ 类，B 端同理，因此必有 (51.9)。结合 $h=0$ 的构造，零通信当且仅当 $h=0$，定理51.4全部得证。

### 51.8 非乘积六周期：相同满投影下的不同准备容量

**定理 51.8（六边实际来源的两个同时达到值）。** 令

$$
\begin{gathered}
A=B=\mathbb Z/3\mathbb Z,\qquad
X=\{(a,b):b-a\in\{0,1\}\},\\
R(a,b)=(a+1,b+1),\qquad S(a,b)=(-a,1-b),\qquad f(a,b)=(b,b),
\end{gathered}
\tag{51.20}
$$

读出为两个坐标，$R,S$ 免费，$f$ 为附加动作。则 $r_A=2,r_B=1$。完整准备 $P=X$ 的同时锐容量为 $(9,6,12)$；对角准备 $P=\{(a,a):a\in\mathbb Z/3\mathbb Z\}$ 的同时锐容量为 $(6,3,6)$。

证明。$X$ 有六点，严格小于九点乘积。$R$ 保持差值，$S$ 将差值 $d$ 变成 $1-d$，二者均保持 $X$ 并局部置换读出；先按需使用 $S$ 改差值，再用 $R$ 改坐标，即传递。逆词是 $R^2,S$。当前 A 读出给 $a$，动作 $f$ 后 A 读出给 $b$，故 $E_A$ 离散、$k_A=6$。B 读出在 $R,S,f$ 下分别变为 $b+1,1-b,b$，故 $E_B=\ker p_B$、$k_B=3$；(51.7)给所列 $r_A,r_B$。

完整准备中 $(a,a)$、$(a,a+1)$ 共 A 标签而不属同一 A 未来类，故 $h=1$。对角准备中两端各自由当前标签恢复唯一准备源，故 $h=0$。代入定理51.4给两组容量；两份准备的两投影均满，差别来自实际准备关系。第51.7节的同一构造给完整准备至多四位累计费用、对角准备零位；四位只是此标签交换方案的费用，不声称最优通信。

还有一个紧凑的历史恢复边界：在任一上述达到者中，从同一准备源出发，空词与 $RRR$ 回到完全相同的本地及联合状态，模式亦相同；二者动作长度却为零与三。因此其边界状态不恢复已执行动作数或完整事件档案。若每动作另赋单位时长，它也不恢复该另加时钟；这一例只划定 (51.4) 的任务范围，没有把计时器偷偷加入其状态指标。证毕。

### 51.9 布尔平移、非线性更新与线性差分特化

**定理 51.9（平移齐性并不要求附加动作线性）。** 设 $X=V=A\oplus B$ 为有限维 $\mathbb F_2$ 向量空间，读出为坐标投影，全部基平移为免费动作，附加动作可为任意总布尔函数。若 $H_A$ 是零的 $E_A$ 类、$H_B$ 是零的 $E_B$ 类，则它们分别为 $\ker p_A,\ker p_B$ 中的线性子空间，各行为类为其陪集，并有

$$
r_A=2^{\dim B-\dim H_A},\qquad
r_B=2^{\dim A-\dim H_B}.
\tag{51.21}
$$

证明。基平移生成全部平移，(51.8)给 $xE_Ay\iff0E_A(y-x)$。若 $u,v\in H_A$，由 $0E_Au$ 平移 $v$ 得 $vE_A(u+v)$，再与 $0E_Av$ 传递得 $u+v\in H_A$；零在其中，二元域上加法闭合即线性子空间。空词给 $H_A\subseteq\ker p_A$，关系的平移不变性又给所有类恰为陪集。每个当前 A 纤维有 $2^{\dim B}/|H_A|$ 个类，得到第一式，B 端相同。商上的诱导动作仍可非线性。

特别地，当附加动作均线性时，含免费平移的任意词仍应写成仿射形式

$$
T_w(z)=N_wz+t_w,\qquad N_{\varnothing}=I,\quad t_{\varnothing}=0.
\tag{51.22}
$$

这里 $N_w$ 是该词的线性部分：若下一动作 $s(z)=N_sz+t_s$，则 $N_{ws}=N_sN_w$、$t_{ws}=N_st_w+t_s$；免费平移的线性部分为 $I$。因此 $T_w(z+d)-T_w(z)=N_wd$，未来相等约束的是**差分**，从而

$$
H_A=\bigcap_{w\in\Sigma^*}\ker(p_AN_w),\qquad
H_B=\bigcap_{w\in\Sigma^*}\ker(p_BN_w).
\tag{51.23}
$$

令 $q_A:=\dim B-\dim H_A$、$q_B:=\dim A-\dim H_B$，便有 $r_A=2^{q_A},r_B=2^{q_B}$。等价地，$q_A$ 是所有未来观察行在隐藏子空间 $\ker p_A$ 上所张成行空间的秩，$q_B$ 对称；这正是线性未来观察码的容量特化。没有使用仿射映射 $T_w$ 的所谓“线性核”。

一个具体非线性实例为

$$
V=\mathbb F_2^3,\quad p_A(x,y,z)=x,\quad p_B(x,y,z)=(y,z),\quad
f(x,y,z)=(x+yz,y,z).
\tag{51.24}
$$

$f$ 是非线性对合，B 未来类恰为当前 $(y,z)$。若两源的 $x$ 不同，空词已区分 A；若 $x$ 相同而 B 标签不同，可对两者作同一 B 平移，把其中一份标签送到 $(1,1)$，另一份不会等于 $(1,1)$。随后 $f$ 恰翻转前者的 A 位，于是 A 未来商离散。故 $k_A=8,k_B=4$，$r_A=4,r_B=1$；完整准备 $h=1$，同时锐容量为 $(10,8,16)$。第51.7节给一位 A 标签加两位 B 标签的三位充分累计预算。本例说明附加动作既可非线性又不擦除物理信息；未提出最优 Toffoli 通信预算或布尔导数算法。证毕。

### 51.10 传递半群不能替换可逆免费运输

**定理 51.10（reset/swap 的五、六、六态反例）。** 若把定义51.1的免费置换群改为任意传递总映射半群，即使未来商的纤维类数仍均匀，(51.11)也不成立。

证明。取 $X=\{0,1\}^2$ 及坐标读出，免费动作是四个公开常值重置 $c_t(x)=t$，$t\in X$；附加动作是交换 $s(a,b)=(b,a)$；准备为 $P=\{(0,0),(0,1)\}$。重置各自局部执行，其半群能把任一状态送到任一目标。当前读出和一次交换给两坐标，故两未来商都离散，$r_A=r_B=2$，A 准备因子化失败，$h=1$。直接把群结论套到此处会预测 $(6,6,8)$。

构造另一正确协议。A 的未知层仅有 $(\mathsf U,0)$，B 的未知层有 $(\mathsf U,0),(\mathsf U,1)$；两端各有四个已知状态 $(\mathsf K,x)$，存完整当前物理源并读相应坐标。未知初态严格由各自准备标签产生。若要求总初始化，在未用的 A 标签一处可选 $(\mathsf K,(1,0))$，它不增加实际准备源或状态数。任何模式下的 $c_t$ 均选叶根，两端立即写 $(\mathsf K,t)$。未知模式的交换选共同内部根，由 B 发送当前 $b$ 一位；A 原标签为零，B 由固定准备知识也知这一点，故二者均写 $(\mathsf K,(b,0))$。已知模式的交换各自局部交换所存两坐标。模式在两端均有实际状态承担，选根及更新符合局部性。

四个重置使已知层全部出现，未知层只有两条实际准备边，所以两端和联合实际容量精确为

$$
|M_A^{\rm act}|=1+4=5,\qquad
|M_B^{\rm act}|=2+4=6,\qquad |Q|=2+4=6.
\tag{51.25}
$$

每个动作有限停止，总费用至多首次未知交换的一位；首次动作若为重置则以后全静默。重置消灭原有不等价，并由公开动作确定新源，硬准备层不能在保持歧义的同时搬运到全部 $X$。这给出对所述半群推广的反例，而不声称 $(5,6,6)$ 已是该新合同的最小容量。证毕。

### 51.11 局部下降与联合可辨识性的耦合边界

**定理 51.11（假设间的蕴涵及两种失效）。** 定义51.1的物理置换、局部置换下降、联合单射性彼此有关，不能把下列反例解释成三个相互独立的删假设实验。

证明。若有限 $X$ 上的物理置换 $g$ 通过满射 $p_A$ 下降为任一总映射 $\alpha$，取 $g^m=\operatorname{id}$，则 $\alpha^mp_A=p_A$，满射性给 $\alpha^m=\operatorname{id}_A$，故 $\alpha$ 自动为置换；B 端相同。反向，若一个物理总映射同时下降为两局部置换且两读出联合单射，则 $g(x)=g(y)$ 蕴涵两原读出相同，进而 $x=y$；有限 $X$ 上的单射即置换。所以局部可逆性不是在物理置换和满射下降之外再独立添加的要求。第51.10节的重置同时失去物理可逆性和局部置换性，保留的是局部总映射下降。

下降本身不可省：取 $X=\{0,1,2\}$、免费候选 $g(x)=x+1\pmod3$，A 读 $\mathbf1_{x=0}$，B 读完整 $x$，完整准备。物理作用传递、两读出满射且联合单射，但 $x=1,2$ 的初始 A 状态相同，经过 $g$ 后指定 A 读出分别为零、一；叶根的同一局部更新不能做到，故这个被要求免费执行的动作无正确实现。A 的完整未来商离散，而当前读出两纤维分别有一类和两类，也不再有共同 $r_A$。

联合单射性亦承担真实信息条件：取 $X=\mathbb F_2^3$，两读出仅为 $a,b$，免费动作为全部基平移，附加动作

$$
f(a,b,c)=(c,b,0),\qquad P=X.
\tag{51.26}
$$

免费平移传递且下降到两读出的局部置换。两份只在 $c$ 上不同的准备源却产生完全相同的两端初始记忆；确定性、共同选根和逐节点局部消息使它们的全协议执行相同，而 $f$ 后要求的 A 读出不同。因此无论给多少通信或记忆都无精确实现，交换两个标签也恢复不了隐藏坐标。若隐藏重数永久不影响任何未来任务，则正确的联合行为目标还可能小于 $X$；那需要另一个合同，不能保留本节的 $|X|$ 联合计数而直接删掉联合单射性。证毕。

### 51.12 既有接口的精确归属与结论范围

(51.9) 的静态因子化使用实际来源 $P$：以 $p_A|_P$ 为细观察、$x\mapsto[x]_{E_A}$ 为粗观察，`D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean` 的 `refinement_iff_kernel_inclusion_on_effective_images` 正好将有效像上的唯一因子化与核包含对应起来。它只证明初始恢复，不保证把初始解码函数重新用于任意后继标签。`D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.lean` 的 `commonCoarsening` 是两观察核上确界的商，`concept_kernel_order_duality` 末项将其核识别为两核之并的等价闭包；在准备边或运输后的实际支撑上取两端投影，就得到共同函数沿连通分量恒定的静态结构。第51.6节还须证明根命中旗标是两端共同函数，并证明运输后的物理不等价与逐端分离，不能由这个静态商直接跳到容量界。

`ControlledBehaviorUniversality.controlled_behavior_universal_property` 的声明另要求有限来源 $Y$、有限实现 $W$、满射 `realization : Y → W` 以及更新、读出的交织。任意分布式控制器可保留历史，记忆可无限，同一物理源也可对应多个实际联合状态，因此并未自动提供这些假设。本节使用它所定义的物理未来商；对无限竞争者的容量必要性由第51.5—51.6节独立承担。有限深度的精确归属与空字母表例外已在第51.2节列明，未把已有商或分割细化界作为本节的新通用结果。

数学背景可参照 Edward F. Moore 的 [Gedanken-Experiments on Sequential Machines](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf) 中以输入实验区分有限状态的定义。本节 (51.4) 采用全部有限词的当前物理输出，经典可区分性只承担这一背景。Guy Goren、Yoram Moses 的 [Silence](https://arxiv.org/abs/1805.07954)（2018，§2.2）明确采用共享离散全局时钟、按轮投递保证和可崩溃进程；其引言以等待已知投递时限后检测缺席来说明静默信息。本节采用定义51.1的二叉协议根合同，没有这种免费同步时钟或缺席信号，因此不把该文的静默通信结论移植为此处的零费动作规则。这两项只作背景来源，不承担定理51.4的分布式容量结论。

承重连接是有限共同根命中旗标、实际硬分量的免费运输、两端各自与静默层分离，以及未知标签层和未来商层的同时达到。它们限定于有限非空物理源、有限总动作字母表、满射且联合单射的当前读出、任意非空实际准备、局部下降的传递免费置换群、每个实际对上有限停止的确定性协议和统一有限累计预算。结论是这些条件下的精确未来物理读出容量，不分类实现消息、通信费用、完整事件档案或已逝时钟，不包含非齐性模型的分类；其形式状态仍为 Claim status: open、repo-derived synthesis。

## 51.99 追加锚

## 52. 静态概率响应的反馈归一化与顺序充分边界

第 3 节的精确收缩给出区域响应及其拼接，第 2、4 节给出摘要成为闭环状态所需的因子化条件。概率模型还需要一个连接条件：同一张静态响应表接入所有允许的因果反馈后仍须归一化。本节在有限经典模型中给出这一条件的充要判据、直接违例反馈和条件未来响应的递归更新。其顺序实现属于成熟的因果信道与经典梳结构；一般半环响应及一般量子过程仍使用各自的操作合同。

### 52.1 同一接口上的完整响应表

**定义 52.1（自由控制的有限响应表）。** 固定整数 $T\ge1$，非空有限动作集 $A_t$ 和输出集 $Y_t$。第 $t$ 轮先选择动作 $a_t\in A_t$，随后取得输出 $y_t\in Y_t$。记 $A_{r:s}=\prod_{j=r}^s A_j$、$Y_{r:s}=\prod_{j=r}^s Y_j$，空乘积取单点。给定完整非负实表

$$
P:Y_{1:T}\times A_{1:T}\longrightarrow[0,\infty),\qquad
\sum_{y_{1:T}}P(y_{1:T}\mid a_{1:T})=1
\quad\text{对每个 }a_{1:T}\in A_{1:T}.
\tag{52.1}
$$

每个 $A_t$ 中的动作在该层所有历史上均允许。动作作为同一准备与接口中的可干预输入；实际来源、参考和校准在各动作列中保持所声明的共同关系。普通观测联合律的条件表不自动满足这一干预解释。

确定性因果策略为 $f_t:Y_{1:t-1}\to A_t$。定义其动作词与反馈代入质量

$$
\begin{aligned}
a^f(y)&=\bigl(f_1(\varnothing),f_2(y_1),\ldots,f_T(y_{1:T-1})\bigr),\\
Z_f(P)&=\sum_{y\in Y_{1:T}}P(y\mid a^f(y)).
\end{aligned}
\tag{52.2}
$$

确定性策略过去所选动作已经由策略程序和输出前缀决定，因此该表示允许控制器记住自己的动作。归一化尚未证明时，$Z_f(P)$ 只是非负总质量。对 $0\le t\le T$ 定义固定动作词下的前缀边缘

$$
P_{\le t}(x\mid a)=\sum_{z\in Y_{t+1:T}}P(x,z\mid a),
\qquad x\in Y_{1:t};
\qquad
P_{\le t}(E\mid a)=\sum_{x\in E}P_{\le t}(x\mid a).
\tag{52.3}
$$

**定义 52.2（单切口事件开关）。** 固定 $1\le t<T$、$u\in A_{1:t}$、$v,w\in A_{t+1:T}$ 和 $E\subseteq Y_{1:t}$。策略 $f^{E;u,v,w}$ 前 $t$ 轮按 $u$ 执行；取得 $y_{1:t}$ 后，若它属于 $E$，后续按预设动作词 $v$ 执行，否则按 $w$ 执行。所有后续时刻读取的分支事件都已经发生，因此这是定义 52.1 中的因果策略。

### 52.2 精确判据与有限开关测试

**定理 52.3（反馈归一化、前缀因果与顺序核）。** 在定义 52.1 下，下列四项等价：

1. 每个确定性因果策略 $f$ 都满足 $Z_f(P)=1$。
2. 每个定义 52.2 的单切口事件开关都满足 $Z_f(P)=1$。
3. 对每个 $0\le t\le T$，$P_{\le t}(x\mid a)$ 只依赖 $x$ 与 $a_{1:t}$，不依赖未来动作 $a_{t+1:T}$。记所得表为 $p_t(x\mid a_{1:t})$，其中 $p_0=1$、$p_T=P$。
4. 存在对所有历史及动作共同定义的概率核 $q_t$，满足

$$
q_t(y_t\mid a_{1:t},y_{1:t-1})\ge0,\qquad
\sum_{y_t\in Y_t}q_t(y_t\mid a_{1:t},y_{1:t-1})=1,
\tag{52.4}
$$

且对每个完整动作词和输出词都有

$$
P(y_{1:T}\mid a_{1:T})
=\prod_{t=1}^Tq_t(y_t\mid a_{1:t},y_{1:t-1}).
\tag{52.5}
$$

这些核给出保存完整动作—输出历史及当前层的有限时域顺序实现。

**证明。** 第一项立即包含第二项。对任意单切口事件开关，分别对事件 $E$ 及其补集求和，由两个固定动作词均满足式（52.1），得到

$$
\boxed{
Z_{f^{E;u,v,w}}(P)
=1+P_{\le t}(E\mid u,v)-P_{\le t}(E\mid u,w).
}
\tag{52.6}
$$

第二项于是强制两个前缀边缘在每个事件 $E$ 上相等；取单点事件便得逐项相等。$t=0$ 由式（52.1）处理，$t=T$ 没有未来动作，故第三项成立。$T=1$ 时不存在中间切口，第二项为空条件，第三项同样由式（52.1）直接成立。

第三项给出递归边缘等式

$$
\sum_{y_t}p_t(y_{1:t}\mid a_{1:t})
=p_{t-1}(y_{1:t-1}\mid a_{1:t-1}).
\tag{52.7}
$$

分母正时定义

$$
q_t(y_t\mid a_{1:t},y_{1:t-1})
=\frac{p_t(y_{1:t}\mid a_{1:t})}
{p_{t-1}(y_{1:t-1}\mid a_{1:t-1})}.
\tag{52.8}
$$

分母为零时，式（52.7）和非负性使全部子项为零；在该参数处任选一个概率分布作为 $q_t$，并对所有策略共同固定这一延拓。两种情形都满足 $p_t=p_{t-1}q_t$，逐层相乘便得式（52.5）。核在正概率父前缀上唯一，在零概率父前缀上可以不唯一。

最后，把式（52.5）代入式（52.2）。固定 $y_{1:T-1}$ 后，全部过去动作及末轮动作都已确定，故对 $y_T$ 求和消去末核。依次从末轮向首轮求和，得到 $Z_f(P)=1$。逐轮按 $q_t$ 采样并追加本次动作、输出即可实现该表。由于时域和字母表有限，完整历史只需有限个状态；这里没有最小记忆或无限时域统一实现的结论。$\square$

**推论 52.4（单点事件与一个参考后缀足够）。** 在式（52.1）已知时，每个切口 $1\le t<T$ 任取一个参考后缀动作词 $w_t\in A_{t+1:T}$。定理 52.3 等价于以下有限线性等式族：

$$
\sum_{z\in Y_{t+1:T}}P(x,z\mid u,v)
=\sum_{z\in Y_{t+1:T}}P(x,z\mid u,w_t)
\quad
\left(
\begin{array}{l}
u\in A_{1:t},\\
x\in Y_{1:t},\\
v\in A_{t+1:T}
\end{array}
\right).
\tag{52.9}
$$

因此，只检验“前缀恰为 $x$ 时选 $v$，否则选 $w_t$”这一有限开关族的归一化，便足以保证全部确定性因果反馈归一化。

**证明。** 式（52.6）在 $E=\{x\}$、$w=w_t$ 时正好给出该开关质量为一与式（52.9）的等价。式（52.9）使每个前缀边缘等于同一参考后缀下的边缘，因此独立于任意未来动作词；反向直接由定理 52.3 第三项得到。$\square$

**命题 52.5（来源独立的随机控制）。** 定理 52.3 成立时，随机种子与响应来源独立的因果控制也给出归一化闭环律。对于在同一控制合同中实现的归一化动作核 $\pi_t(a_t\mid a_{1:t-1},y_{1:t-1})$，该联合律为

$$
\Pr_\pi(a,y)
=P(y\mid a)\prod_{t=1}^T
\pi_t(a_t\mid a_{1:t-1},y_{1:t-1}),
\qquad
\sum_{a,y}\Pr_\pi(a,y)=1.
\tag{52.10}
$$

**证明。** 将式（52.5）代入式（52.10），从末轮开始，每轮先对 $y_t$ 求和，再对 $a_t$ 求和，两个归一化核依次消去。也可预采样有限历史树上整张策略表：固定该表后是确定性因果策略，再按与来源无关的权重混合。独立种子可跨轮复用；这不要求每轮重新取得独立种子。$\square$

若控制种子与未观测来源共享相关性，式（52.10）使用同一 $P$ 的前提须重新核对；一般不能把这项相关性省略后继续代入。控制器从已取得输出获得的信息已包含在历史依赖中，与额外的隐藏来源信息不同。

### 52.3 归一化缺陷、反馈放大与最优因果修复

**命题 52.6（前缀总变差被反馈质量缺陷控制）。** 对满足式（52.1）的任意非负整表，定义

$$
\Delta(P)=\max_f|Z_f(P)-1|.
\tag{52.11}
$$

策略族有限，故最大值存在。对任意 $1\le t<T$、$u\in A_{1:t}$ 与 $v,w\in A_{t+1:T}$，有

$$
\operatorname{TV}\bigl(P_{\le t}(\cdot\mid u,v),
P_{\le t}(\cdot\mid u,w)\bigr)\le\Delta(P).
\tag{52.12}
$$

并且存在两个单切口事件开关，其质量分别为 $1+\operatorname{TV}$ 与 $1-\operatorname{TV}$，其中总变差取式（52.12）左侧的两个边缘。

**证明。** 记两个边缘为 $p_v,p_w$。式（52.6）给出 $|p_v(E)-p_w(E)|\le\Delta(P)$。取 $E=\{x:p_v(x)>p_w(x)\}$，有限概率分布的总变差等于 $p_v(E)-p_w(E)$，所以该开关质量为 $1+\operatorname{TV}$；交换两条后缀词在 $E$ 及其补集上的位置，质量为 $1-\operatorname{TV}$。$\square$

式（52.12）是反馈缺陷的下界见证，不把所有单切口边缘差的最大值认作 $\Delta(P)$ 的一般等式，也不把它当作到因果模型类距离的完整刻画。

**命题 52.7（严格正表的失败反馈与最优常数）。** 存在每个固定动作词均归一化的严格正表，使因果反馈代入质量分别为 $4/3$ 和 $2/3$。式（52.12）的常数一不能减小。

**证明。** 取 $T=2$，$A_1,Y_2$ 为单点，$Y_1=A_2=\{0,1\}$，令

$$
P(y_1=y\mid a_2=a)=
\begin{cases}
2/3,&y=a,\\
1/3,&y\ne a.
\end{cases}
\tag{52.13}
$$

每个固定动作列严格为正且归一化，两个第一轮输出边缘的总变差为 $1/3$。四个确定性因果策略为两种常动作、$a_2=y_1$ 和 $a_2=1-y_1$，其质量依次为 $1,1,4/3,2/3$。故 $\Delta(P)=1/3$，式（52.12）取等号。第一轮边缘依赖第二轮自由动作，违反定理 52.3 的前缀条件。$\square$

同一数表也定义合法的静态共同来源

$$
\Pr(A_2=a,Y_1=y)=\frac12P(y\mid a).
\tag{52.14}
$$

例如先产生均匀 $Y_1$，随后以概率 $2/3$ 令 $A_2=Y_1$、以概率 $1/3$ 令 $A_2=1-Y_1$，便得到式（52.14）。其观测条件表恰为式（52.13）。这个实际因果生成过程没有矛盾；不能成立的是把它的观测条件列重新当作“先输出 $Y_1$、再自由干预 $A_2$”的响应。同一来源的条件化、控制器取得的记录及自由动作权限须分别保留。

**命题 52.8（两轮反馈缺陷与字母表放大）。** 取 $T=2$，$A_1,Y_2$ 为单点，记 $A=A_2$、$Y=Y_1$，并写 $r_a(y)=P(y\mid a)$。每列 $r_a$ 是 $Y$ 上的概率分布。令

$$
L_y=\min_{a\in A}r_a(y),\qquad
U_y=\max_{a\in A}r_a(y).
$$

则全部反馈 $a=f(y)$ 的缺陷精确为

$$
\Delta(r)=
\max\left\{
\sum_{y\in Y}U_y-1,\;
1-\sum_{y\in Y}L_y
\right\}.
\tag{52.15}
$$

对每个整数 $m\ge2$ 和 $0\le\varepsilon\le1$，取 $A=Y=\{1,\ldots,m\}$ 及

$$
r_a(y)=\frac{1-\varepsilon}{m}
+\varepsilon\,\mathbf1_{\{y=a\}}.
\tag{52.16}
$$

则

$$
\max_{a,b}\operatorname{TV}(r_a,r_b)=\varepsilon,\qquad
\Delta(r)=(m-1)\varepsilon.
\tag{52.17}
$$

因此不存在独立于动作、输出字母表大小的有限常数 $C$，使所有这类表都满足 $\Delta(r)\le C\max_{a,b}\operatorname{TV}(r_a,r_b)$。

**证明。** 每个输出 $y$ 上的动作 $f(y)$ 可独立选择，故反馈质量的最大值为 $\sum_yU_y$，最小值为 $\sum_yL_y$。常策略给出质量一，所以 $\sum L_y\le1\le\sum U_y$，得到式（52.15）。

式（52.16）中，两个不同动作列只在对应的两个坐标相差 $\varepsilon$，故总变差为 $\varepsilon$。逐行有 $L_y=(1-\varepsilon)/m$、$U_y=(1-\varepsilon)/m+\varepsilon$，代入式（52.15）得式（52.17）。选择 $a=y$ 给出质量 $1+(m-1)\varepsilon$；在每行选择任一 $a\ne y$ 给出质量 $1-\varepsilon$。特别地，令 $\varepsilon=1/(m-1)$、$m\to\infty$，列间总变差趋于零，而反馈缺陷恒为一。$m\ge3$ 时这些表仍严格为正。$\square$

**定理 52.9（有限时域的精确因果修复误差）。** 保留定义 52.1 的有限动作、输出与自由控制合同。令 $\mathcal C_T$ 为满足定理 52.3 的因果概率表全体，定义

$$
D_{\mathrm{fb}}(P,Q)=
\max_{\substack{f\text{ 为确定性因果策略}\\ E\subseteq Y_{1:T}}}
\left|
\sum_{y\in E}\bigl(P(y\mid a^f(y))-Q(y\mid a^f(y))\bigr)
\right|.
\tag{52.18}
$$

原表的反馈响应可以不归一化，因此这里比较事件质量，不把它称为两个概率分布的总变差。则

$$
\min_{Q\in\mathcal C_T}D_{\mathrm{fb}}(P,Q)=\Delta(P).
\tag{52.19}
$$

该最小值可以由对完整有限表的前后递推达到。

**证明。** 记

$$
u=\max_f Z_f(P),\qquad l=\min_fZ_f(P).
\tag{52.20}
$$

常动作词策略的质量为一，所以 $0\le l\le1\le u$，且 $\Delta(P)=\max\{u-1,1-l\}$。任何 $Q\in\mathcal C_T$ 在每个策略下质量均为一；取事件 $E=Y_{1:T}$，得 $D_{\mathrm{fb}}(P,Q)\ge\Delta(P)$。

以下构造达到下界的 $Q$。对每个深度 $t$，前缀变量为 $h_t=(a_{1:t},y_{1:t})$。从叶层向根定义非负表

$$
S_T(h_T)=M_T(h_T)=P(y_{1:T}\mid a_{1:T}),\qquad
\begin{aligned}
S_{t-1}(h_{t-1})&=\max_{a_t}\sum_{y_t}S_t(h_{t-1},a_t,y_t),\\
M_{t-1}(h_{t-1})&=\min_{a_t}\sum_{y_t}M_t(h_{t-1},a_t,y_t).
\end{aligned}
\tag{52.21}
$$

在一个固定父历史上，先选动作，再对所有输出分支求和；各后继分支的后续控制可以独立选择。因此对剩余深度归纳，这两个递推分别给出最大、最小续接质量，根值为 $S_0=u$、$M_0=l$。使用完整动作—输出前缀不扩大确定策略族：在同一实际策略下，过去动作由输出前缀和策略自身确定。

取每层一个固定输出 $y_t^\ast\in Y_t$。从根向前构造 $C_t^+$，初值 $C_0^+=u$，并令

$$
C_t^+(h,a,y)
=S_t(h,a,y)
+\mathbf1_{\{y=y_t^\ast\}}
\left(C_{t-1}^+(h)-\sum_zS_t(h,a,z)\right).
\tag{52.22}
$$

若 $C_{t-1}^+\ge S_{t-1}$，则括号由上递推非负，故 $C_t^+\ge S_t$，且对每个动作 $a$ 有 $\sum_yC_t^+(h,a,y)=C_{t-1}^+(h)$。根处不变量成立，因而所有层成立。

再从根构造 $C_t^-$，初值 $C_0^-=l$。令 $d_t(h,a)=\sum_zM_t(h,a,z)$，并取

$$
C_t^-(h,a,y)=
\begin{cases}
\dfrac{C_{t-1}^-(h)}{d_t(h,a)}\,M_t(h,a,y),&d_t(h,a)>0,\\
0,&d_t(h,a)=0.
\end{cases}
\tag{52.23}
$$

归纳假设 $0\le C_{t-1}^-\le M_{t-1}$ 给出
$0\le C_{t-1}^-(h)\le M_{t-1}(h)\le d_t(h,a)$。
因此非零分母时比例在 $[0,1]$，得到 $0\le C_t^-\le M_t$；零分母时父质量也为零。两种情形均满足 $\sum_yC_t^-(h,a,y)=C_{t-1}^-(h)$。

令叶表 $C^\pm=C_T^\pm$。于是 $C^-\le P\le C^+$ 逐项成立，两族表各自满足因果前缀递归，每个反馈下的总质量分别为 $l,u$。若 $u=l$，两者必均为一，原表已经满足定理 52.3，取 $Q=P$。若 $u>l$，取

$$
\theta=\frac{1-l}{u-l},\qquad
Q=C^-+\theta(C^+-C^-).
\tag{52.24}
$$

由于 $0\le\theta\le1$，所得 $Q$ 非负，位于 $C^-$ 与 $C^+$ 之间。各层也作同一凸组合，给出因果前缀递归，根质量为 $l+\theta(u-l)=1$，故 $Q\in\mathcal C_T$。

对任意策略 $f$ 与事件 $E$，用下标 $f$ 表示沿该策略代入，逐项夹逼及非负性给出

$$
\begin{aligned}
\sum_{y\in E}(P_f(y)-Q_f(y))
&\le\sum_{y\in E}(C_f^+(y)-Q_f(y))
\le\sum_y(C_f^+(y)-Q_f(y))=u-1,\\
\sum_{y\in E}(Q_f(y)-P_f(y))
&\le\sum_{y\in E}(Q_f(y)-C_f^-(y))
\le\sum_y(Q_f(y)-C_f^-(y))=1-l.
\end{aligned}
\tag{52.25}
$$

于是 $D_{\mathrm{fb}}(P,Q)\le\Delta(P)$，与先前的普遍下界相合。$\square$

**推论 52.10（两轮模型的显式最优替代表）。** 在命题 52.8 的模型中，因果替代表就是不依赖后续动作的概率分布 $q(y)$。任何满足 $L_y\le q(y)\le U_y$ 的概率分布都达到定理 52.9 的最小误差 $\Delta(r)$。若 $s=\sum_y(U_y-L_y)>0$，可显式取

$$
\theta=\frac{1-\sum_yL_y}{s},\qquad
q(y)=L_y+\theta(U_y-L_y).
\tag{52.26}
$$

若 $s=0$，取共同列 $q=L=U$。

**证明。** 由 $\sum L_y\le1\le\sum U_y$，式（52.26）的 $\theta$ 属于 $[0,1]$，且 $q$ 总和为一。若 $s=0$，每项 $U_y-L_y$ 为零，所有列相同。对任意夹在两者之间的概率分布 $q$，事件正偏差被 $\sum_y(U_y-q(y))=\sum_yU_y-1$ 控制，负偏差被 $\sum_y(q(y)-L_y)=1-\sum_yL_y$ 控制。式（52.15）和定理 52.9 的下界给出 $D_{\mathrm{fb}}(r,q)=\Delta(r)$。$\square$

定理 52.9 的替代表与原表在全部允许确定反馈和完整输出事件下比较。它给出有限经典响应表的最优误差，不据此认定替代表保留原实际物理来源或取得其控制权限；一般量子参考合同也不由该经典构造供应。

### 52.4 经典梳与可递归更新的预测边界

**命题 52.11（因果前缀的经典梳对应）。** 定理 52.3 成立时，在动作与输出的经典正交基上定义

$$
R^{(0)}=1,\qquad
R^{(t)}=
\sum_{a_{1:t},y_{1:t}}
p_t(y_{1:t}\mid a_{1:t})
|a_1,y_1,\ldots,a_t,y_t\rangle
\langle a_1,y_1,\ldots,a_t,y_t|.
\tag{52.27}
$$

则它们满足

$$
R^{(t)}\ge0,\qquad
\operatorname{Tr}_{Y_t}R^{(t)}
=R^{(t-1)}\otimes I_{A_t},\qquad
\operatorname{Tr}R^{(t)}=\prod_{j=1}^t|A_j|.
\tag{52.28}
$$

这些正性与偏迹条件就是[上下文几何卷](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)定义 11.5 的经典对角情形。

**证明。** 非负对角元给正性。对 $Y_t$ 求偏迹就是对 $y_t$ 求和，式（52.7）使所得对角元与 $a_t$ 无关，给出第二个等式。每个固定动作前缀下的 $p_t$ 总和为一，再对所有动作前缀求和，得到迹公式。反向，式（52.28）的逐对角元等式给出式（52.7），继而从末轮向前求和恢复前缀因果性。$\square$

因此，定理 52.3 的有限表检验接入该卷定理 11.6 的顺序实现接口；其量子实现依据见 Chiribella、D'Ariano、Perinotti 的 Theorem 3 与 Theorem 5。一般量子过程仍须验证完整 Choi 正性、参考扩张和因果偏迹，不能用一组经典标量响应的正性与归一化代替。

**定义 52.12（完整条件后续响应）。** 在定理 52.3 下，对正概率历史 $h=(a_{1:t},y_{1:t})$，即 $p_t(y_{1:t}\mid a_{1:t})>0$，定义

$$
F_h(v,z)=
\frac{P(y_{1:t},z\mid a_{1:t},v)}
{p_t(y_{1:t}\mid a_{1:t})},
\qquad
v\in A_{t+1:T},\quad z\in Y_{t+1:T}.
\tag{52.29}
$$

每个固定 $v$ 下，$F_h(v,\cdot)$ 都是概率分布。相等比较只在同一层、同一接口合同中进行。

**命题 52.13（未来响应商的顺序闭合）。** 对 $t<T$，相同 $F_h$ 的两个历史具有相同的下一输出核；在同一实际动作及同一正概率输出之后，后继响应仍相同。因此，按 $F_h$ 相等取得的商是可递归更新的未来预测边界。

**证明。** 固定下一动作 $a\in A_{t+1}$ 和输出 $y\in Y_{t+1}$。对任意 $v\in A_{t+2:T}$，下一输出概率为

$$
k_h(y\mid a)
=\sum_{z'\in Y_{t+2:T}}F_h((a,v),(y,z'))
=\frac{p_{t+1}(y_{1:t},y\mid a_{1:t},a)}
{p_t(y_{1:t}\mid a_{1:t})}.
\tag{52.30}
$$

前缀因果性使它独立于未来动作词 $v$。若 $k_h(y\mid a)>0$，将式（52.29）的分子、分母相除得到

$$
F_{h(a,y)}(v,z)
=\frac{F_h((a,v),(y,z))}{k_h(y\mid a)}.
\tag{52.31}
$$

式（52.30）、（52.31）只使用当前响应、实际动作及实际输出，所以与历史代表元无关。零概率输出不发生，可在需要总化状态转移时指定同一延拓。逐轮归纳即得未来输出与响应的共同顺序律。$\square$

这项边界只压缩未来任务。两条不同过去可以具有同一未来响应；若任务要求保留完整既有原始档案，须继续保留档案字段。指定策略若读取被商掉的过去，也不自动在响应商上运行。对任意另选的摘要，应继续履行本卷定理 2.1、4.1 的合同：下一输出核、后继摘要、动作合法性和选择器都通过同一摘要因子化。预测响应的数学存在不等于它已经被观察者取得。

式（52.31）是成熟的条件预测状态更新。Singh、James、Rudary 对动作—观察测试及历史条件预测的定义，以及 $p(q_i\mid hao)=p(aoq_i\mid h)/p(ao\mid h)$ 的更新给出相同结构；本节使用完整有限后续响应，不主张发现更小的线性核心、最小数值维数或学习算法。[过程几何卷](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)第 27 节的共同来源、未归一化分支核与 Bayes 更新在其具体模型中给出相应实现接口。

### 52.5 来源、权限与资源范围

**注记 52.14（从静态收缩到实际边界的适用条件）。** 若第 3 节的因子收缩产生定义 52.1 的整表，定理 52.3 判断它是否存在所声明时间次序下的概率核实现，定理 52.9 给出有限经典响应度量中的最优因果替代表，命题 52.13 给出完整未来响应的递归闭合。这些结论各有明确前提：

- 收缩结果须是同一干预接口下的非负、逐固定动作词归一化响应族。一般半环没有这里的概率、除法和采样结构。
- 整表或局部核的取得、求和、除法、采样与存储须由任务合同提供或计费。有限个任意实数条目不自动给出统一可计算的精确采样器；有限线性检验族也不免除输入读取和核验费用。
- 时域和层 $t$ 是明确数据。使用不同逐层核的实现仍须容纳控制器、阶段寄存器与时钟校准；它不自动成为没有时钟输入的统一自治门，也不保证跨无限时域的统一有限记忆。
- 共同初态、实际回流记忆、控制器随机性、参考和访问权限保持原有联合关系。重新解释普通条件表，不会自动取得干预端口或隐藏读数。
- 如果只允许受限策略族，开关见证也必须在该权限内合法。缩小策略量词后，归一化只约束该族能够接出的分支，不能无条件推出全部自由动作列之间的前缀等式。

上述因果分解与梳实现采用已有数学结构。式（52.6）的事件切换、推论 52.4 的有限测试、命题 52.6—52.8 的缺陷与反馈放大、定理 52.9 和推论 52.10 的因果修复及命题 52.13 的条件响应更新按本节证明使用；其作用是把精确静态响应、顺序概率实现和指定边界的闭环合同接到同一模型中。

相关原始文献与范围如下：

1. Giulio Chiribella、Giacomo Mauro D'Ariano、Paolo Perinotti，*Theoretical framework for quantum networks*，Physical Review A 80, 022339 (2009)，[arXiv:0904.4483v2](https://arxiv.org/pdf/0904.4483v2)。Theorem 3、式（25），PDF 第 7 页；Theorem 5、式（40），PDF 第 11 页，给出递归正性、归一化与顺序量子网络的实现及确定性梳的充要条件。上下文几何卷定义 11.5、定理 11.6 已按这些结果给出接口，定理 11.10 给出合法逐轮仪器的历史树归一化。
2. Haim Permuter、Tsachy Weissman、Andrea Goldsmith，*Finite State Channels with Time-Invariant Deterministic Feedback*，[arXiv:cs/0608070v1](https://arxiv.org/pdf/cs/0608070v1)，2006。§II 式（5），PDF 第 4 页，定义因果条件化乘积；Lemma 1、式（12）—（14），PDF 第 5—6 页，给输入—输出联合链式分解；Lemma 3，PDF 第 6 页，给归一化。这里使用这些概率结构，不将其后续平稳有限状态信道的容量结论用于任意静态表。
3. Satinder Singh、Michael R. James、Matthew R. Rudary，*Predictive State Representations: A New Theory for Modeling Dynamical Systems*，UAI 2004，作者稿 [arXiv:1207.4167](https://arxiv.org/pdf/1207.4167)。PDF 第 2 页定义动作—观察测试、历史与历史条件预测；第 5 页给出条件预测的比值更新及式（3）的线性 PSR 更新。完整未来响应采用这一预测状态结构，并保留本节固定时域与完整响应的范围。

## 52.99 追加锚

## 53. 因果修复的权限与线性实现边界

定理 52.9 在完整有限响应表上构造最优因果替代表。将它用于内部观察者，还须区分两种条件：哪些历史与动作实际可读、可选，以及修复怎样从输入资料实现。可见合法菜单随历史变化时，原来的局部递推仍适用；控制器不能区分的历史却可能阻止策略拼接，使归一化缺陷不再控制修复误差。另一方面，即使整表已经给出，也不存在对所有输入通用、保持全部已有因果表的仿射修复。

### 53.1 可见合法执行树与局部证书

**定义 53.1（可见合法执行树）。** 取有限根树。每个非终端节点 $h$ 是完整公开执行历史，具有已知非空有限合法动作集 $A(h)$。动作 $a\in A(h)$ 的输出集 $Y(h,a)$ 非空有限，取得输出 $y$ 后进入唯一子节点 $hay$。动作、输出和终止标签属于公开记录；节点身份、当前菜单及其更新由控制器实际获准读取的历史确定。不同动作可以有不同后续菜单、输出集和终止深度。

允许策略族 $\Pi$ 包含所有逐节点选择 $\pi(h)\in A(h)$，并允许在任意指定的已取得历史之后换入任意合法续接。这个局部可拼接性是操作合同的一部分。若策略必须在不能区分的节点上作同一选择，就不能使用这里的全策略族。

令 $\Lambda$ 为全部合法终端路径，同一来源合同上的完整静态资料为非负叶权 $P:\Lambda\to[0,\infty)$。不假定全部叶权之和为一，也不假定存在对所有输出都合法的固定动作词。令 $\Lambda_\pi$ 为与 $\pi$ 一致的叶路径，定义

$$
P_\pi(\lambda)=\mathbf1_{\{\lambda\in\Lambda_\pi\}}P(\lambda),
\qquad
Z_\pi(P)=\sum_{\lambda\in\Lambda_\pi}P(\lambda).
\tag{53.1}
$$

在该合同中，第 52 节的前缀递归按树节点表达为

$$
m(\mathrm{root})=1,\qquad
m(\lambda)=P(\lambda)\quad(\lambda\in\Lambda),\qquad
m(h)\ge0,\qquad
\sum_{y\in Y(h,a)}m(hay)=m(h)\quad(a\in A(h)).
\tag{53.2}
$$

式（53.2）给出顺序核：父质量正时取 $q(y\mid h,a)=m(hay)/m(h)$；父质量零时，各非负子质量均为零，在该合法输出集任选一个共同归一化延拓。沿路径相乘恢复叶表，任意合法策略下从叶到根求和得到质量一。反向，归一化条件核的路径乘积给出这些节点质量。这是定理 52.3 在已知合法树上的直接使用。

归一化也有一份有限局部证书。每个节点先选择参考动作 $\pi_0(h)$，令 $g(h)$ 为从 $h$ 出发、后续按 $\pi_0$ 行动时的未条件化叶权总和。对节点 $h$ 和动作 $a\in A(h)$，构造 $\rho^{h,a}$：沿通向 $h$ 的祖先路径选择对应动作，在 $h$ 选择 $a$，其余节点按 $\pi_0$ 行动。公开历史与合法菜单保证该策略存在。

两份在 $h$ 之外完全相同的策略，树外贡献相消，故

$$
Z_{\rho^{h,a}}(P)-Z_{\rho^{h,\pi_0(h)}}(P)
=\sum_{y\in Y(h,a)}g(hay)-g(h).
\tag{53.3}
$$

因此，$Z_{\pi_0}(P)=1$ 加上式（53.3）对每个 $h,a$ 的差为零，等价于全部合法策略归一化。正向，因为 $g(\lambda)=P(\lambda)$，这些等式使 $g$ 满足式（53.2）。反向，若全部合法策略归一化，证书两侧均为一。证明没有除以到达 $h$ 的概率，因而也覆盖零质量前缀。这里比较的是同一可见历史之后的合法续接，没有补入非法边。

**命题 53.2（只改变参考策略的一个节点会漏检）。** 不加入到达待测节点的路径准备时，单节点改策检验不足以保证全部合法策略归一化。

**证明。** 根节点可选动作 $a,b$。选择 $a$ 立即到达叶权为一的终点；选择 $b$ 到节点 $h$，在 $h$ 可选 $c,d$，对应叶权分别为一、二，所有输出为单点。参考策略在根选 $a$、在 $h$ 选 $c$。只改根动作为 $b$，质量仍为一；只将 $h$ 的动作改成 $d$，根仍选择 $a$，质量也为一。但同时选择 $b,d$ 的合法策略质量为二。

式（53.3）在 $h$ 先沿根动作 $b$ 到达，再比较 $c,d$，便检出差一。故缺失的是共同可执行背景，不是可以省去的不可达分支。$\square$

### 53.2 合法树上的包络修复

令 $\mathcal C$ 为定义 53.1 的同一合法树上的因果概率叶表，定义

$$
\begin{aligned}
D_\Pi(P,Q)&=
\max_{\pi\in\Pi,\ E\subseteq\Lambda}
\left|\sum_{\lambda\in E}\bigl(P_\pi(\lambda)-Q_\pi(\lambda)\bigr)\right|,\\
\Delta_\Pi(P)&=\max_{\pi\in\Pi}|Z_\pi(P)-1|.
\end{aligned}
\tag{53.4}
$$

定理 52.9 的包络构造在每个节点使用其实际 $A(h)$，给出

$$
\min_{Q\in\mathcal C}D_\Pi(P,Q)=\Delta_\Pi(P).
\tag{53.5}
$$

这一应用要求全部合法节点选择均被允许，并保持定义 53.1 的拼接合同。它不对任意受限策略族成立。这里还可容许任意非负叶权，不必先指定归一化参考策略，证明如下。

沿用逆向递推

$$
\begin{aligned}
S(\lambda)&=M(\lambda)=P(\lambda),\\
S(h)&=\max_{a\in A(h)}\sum_{y\in Y(h,a)}S(hay),\\
M(h)&=\min_{a\in A(h)}\sum_{y\in Y(h,a)}M(hay).
\end{aligned}
\tag{53.6}
$$

各后继子树的续接可以独立选择，故按树高归纳，根值准确等于 $u=\max_\pi Z_\pi(P)$、$l=\min_\pi Z_\pi(P)$。按定理 52.9 的前向公式，在每个动作行以一个固定合法输出接收非负余量，得到因果上包络 $C^+\ge P$，每策略质量为 $u$；把该行 $M$ 按所需父质量缩放，得到 $0\le C^-\le P$，每策略质量为 $l$。非空合法输出集使余量有处安放，下包络分母为零时父质量也为零。两者逐动作保持相同父质量，故原证明逐节点适用。

若 $l\le1\le u$ 且 $u>l$，仍取原来的包络混合；其余质量范围用单侧包络归一化：

$$
Q=
\begin{cases}
C^-+\dfrac{1-l}{u-l}(C^+-C^-),&l\le1\le u,\ u>l,\\[6pt]
P,&u=l=1,\\[2pt]
C^-/l,&l>1,\\[2pt]
C^+/u,&0<u<1.
\end{cases}
\tag{53.7}
$$

第一种情形由逐项夹逼，使事件正、负偏差分别不超过 $u-1$、$1-l$。第二种误差为零。若 $l>1$，则 $Q\le P$，任意策略的全部正差为 $Z_\pi(P)-1\le u-1$，其事件差更小。若 $0<u<1$，则 $Q\ge P$，全部负差为 $1-Z_\pi(P)\le1-l$。最后，若 $u=0$，每个叶节点都属于某个合法策略，非负性迫使 $P=0$；任选同一树的因果概率表，误差为一。

以上上界均为 $\max\{|u-1|,|l-1|\}=\Delta_\Pi(P)$。对任何因果 $Q$，在式（53.4）取 $E=\Lambda$ 给出匹配下界，完成式（53.5）的证明。修复始终位于同一已知合法树中，不认证隐藏权限，也不扩大菜单。

### 53.3 受限策略的零缺陷与正修复误差

**定理 53.3（不闭合策略族的归一化不足）。** 存在两轮模型，所有动作在所有节点分别合法，但允许的常动作策略均归一化，而到真正因果替代表的最优受限事件误差可任意接近一。

取第一轮动作及第二轮输出为单点，$Y_1=A_2=\{1,\ldots,m\}$，$m\ge2$。完整第一轮输出记入任务的终端档案，但在线控制器不能读取它，只能读常值摘要。因此允许策略族 $\Pi_{\mathrm{const}}$ 只含 $a_2\equiv a$。终端测试者可读完整输出档案，不构成在线控制器的额外权限。

对 $0\le\varepsilon\le1$，使用命题 52.8 的同一表族

$$
r_a(y)=\frac{1-\varepsilon}{m}
+\varepsilon\,\mathbf1_{\{y=a\}}.
\tag{53.8}
$$

任何按“先输出、后动作”实现的因果替代表均为与后动作无关的概率分布 $q(y)$。在同一常动作策略族和终端事件族下，有

$$
\Delta_{\mathrm{const}}(r)=0,\qquad
\min_qD_{\mathrm{const}}(r,q)
=\varepsilon\left(1-\frac1m\right),
\quad
D_{\mathrm{const}}(r,q)=\max_a\operatorname{TV}(r_a,q).
\tag{53.9}
$$

**证明。** 每个常动作策略对应一列概率分布，总质量为一，所以受限缺陷为零。固定动作下两个被比较响应都归一化，故最大事件差正好是该列与 $q$ 的总变差。

对任意 $q$，存在坐标 $a$ 满足 $q(a)\le1/m$。以事件 $\{a\}$ 测试该列，得到

$$
\operatorname{TV}(r_a,q)
\ge r_a(a)-q(a)
\ge\varepsilon\left(1-\frac1m\right).
$$

取均匀 $q$，该列在坐标 $a$ 的正差为 $\varepsilon(1-1/m)$，其余坐标各为 $-\varepsilon/m$，故每列总变差都达到下界。$\square$

取 $\varepsilon=1$、$m\to\infty$，最优修复误差趋于一，而受限归一化缺陷恒为零。要求严格正表时，可令 $\varepsilon=1-1/m$，仍得到同一极限。二元 $\varepsilon=1/3$ 给最优误差 $1/6$。

这里没有把禁止的分支控制用于实际执行。每个动作分别可用，但控制器的信息接口合并了不同输出分支，不能分别选择动作，策略族因而不对历史分支拼接闭合。把式（53.6）的逐节点最大、最小直接用于这种控制器，会暗中增加它没有的区分能力。

### 53.4 预测边界缺少权限信息的实例

**例 53.4（合法菜单非矩形与隐藏权限）。** 共同来源先产生公平位 $Y_1\in\{0,1\}$，控制器实际取得该位；随后只允许动作 $a_2=Y_1$，最后输出恒为零。两条合法完整路径各有叶权 $1/2$。合法反馈归一化，但不存在对两种第一轮输出都合法的固定第二动作。因此可以使用定义 53.1 的树合同，却不能直接使用矩形的固定动作词基线。

若取得 $Y_1$ 后，控制器只准读取丢掉该位的常值摘要，两个相容历史的合法动作集交为空。未来普通输出仍恒为零，所以完美预测下一输出的摘要不能支持下一合法动作。

更一般地，若两个实际相容来源状态 $\theta=0,1$ 的当前观察相同，而实际合法动作集分别为 $\{0\}$、$\{1\}$，即使各合法动作的输出都为零，也没有一个观察纤维上共同安全的动作。这里直接应用[观察完成与反思卷](FORMAL_OBSERVER_COMPLETION_REFLECTION.md)定理 58.1：只依赖观察的确定性安全选择器存在，当且仅当每个有效观察纤维上的合法动作交非空。来源独立随机化也不能实现逐来源安全，因为随机动作的支持须包含在同一交集中。

两来源等概率时，任何盲选动作的非法概率都是 $1/2$。将各动作在其合法来源上的输出分别记成两列常输出表，这些数学列虽全部归一化，却来自不同来源条件化，不能认证共同干预权限。交集为空时，定义 53.1 的非空可见菜单前提已经失效；不能把空策略族上的全称归一化作为实现证据。

补入拒绝标签同样需要区分数学与操作含义。[过程几何卷](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)定理 3.2 明确区分准入缺失与可执行失败状态。请求、检测、拒绝、扰动及费用本身有合法操作合同，才能把它们作为实际输出并入本卷第 20 节的总化模型。符号补齐不能取得原本缺少的动作权限。

**命题 53.5（当前菜单不足以更新未来权限）。** “未来普通输出预测＋当前合法菜单”可以在两个历史上相同，却不能决定下一步的权限摘要。

**证明。** 取同层两个实际历史 $s_0,s_1$，当前菜单都为 $\{\mathrm{wait}\}$，等待均输出零。等待后分别进入 $t_0,t_1$，菜单为 $\{b_0\}$、$\{b_1\}$，执行各自唯一合法动作后也输出零。两个起点具有相同未来普通输出和当前菜单，却在同一动作后产生不同菜单，故该摘要没有代表元无关的后继。$\square$

最小补全取决于任务。只要求选择一个安全动作时，纤维合法动作交非空即可，不必恢复整个菜单。要保留全部原有动作可用性，菜单须在摘要纤维上相同；要逐步保持这种能力，还须保各合法动作的输出核、正概率后继摘要和终止标签，指定选择器也须通过保留字段运行。这直接使用本卷定理 2.1、4.1 及第 12、13 节的共同细化合同。有限完整载体上的最粗稳定细化可沿用过程几何卷定理 19.8；完整既有档案仍按其原任务保留，未来预测和权限残余不自动重建过去。

### 53.5 保留末轮输出时的仿射修复障碍

**定义 53.6（二元两轮完整响应）。** 第一轮无控制，产生 $x\in\{0,1\}$；第二轮选择 $a\in\{0,1\}$，随后产生 $z\in\{0,1\}$。末轮输出 $z$ 是任务保留的数据。静态响应表及其因果子集为

$$
\begin{aligned}
\mathcal P
&=\left\{P_a(x,z)\ge0:
\sum_{x,z}P_a(x,z)=1\quad(a=0,1)\right\}
=\Delta_3\times\Delta_3,\\
d(P)&=\sum_zP_0(0,z)-\sum_zP_1(0,z),\\
\mathcal C&=\{P\in\mathcal P:d(P)=0\}.
\end{aligned}
\tag{53.10}
$$

因为两个固定动作列都归一化，$d=0$ 正好表示第一输出的整个边缘不依赖后续动作。满足时可写为 $p(x)q(z\mid x,a)$；零概率父分支按定理 52.3 取共同归一化延拓。

**定理 53.7（不存在通用仿射因果回缩）。** 不存在仿射映射 $\mathcal R:\mathcal P\to\mathcal C$，使每个 $P\in\mathcal C$ 都满足 $\mathcal R(P)=P$。

**证明。** $\mathcal P$ 的仿射包 $A$ 由两条列和为一的等式给出，维数为六。函数 $d$ 在 $A$ 上不是常数；例如一列集中在 $x=0$、另一列集中在 $x=1$ 时 $d\ne0$。因此 $H=\{P\in A:d(P)=0\}$ 是五维仿射超平面。

共同均匀表 $P_a(x,z)=1/4$ 属于 $\mathcal C$，其所有坐标严格为正，所以 $\mathcal C$ 在 $H$ 中包含该点的一个相对开邻域。由此 $\operatorname{aff}(\mathcal C)=H$。

$\mathcal P$ 在 $A$ 中有非空相对内部，仿射映射 $\mathcal R$ 的各坐标具有唯一的仿射延拓。对每个坐标 $i=(a,x,z)$，仿射函数 $\mathcal R(P)_i-P_i$ 在 $\mathcal C$ 为零，故在其仿射包 $H$ 为零。超平面的余维为一，因此存在实常数 $k_i$ 使

$$
\mathcal R(P)_i=P_i+k_i d(P)
\qquad(P\in\mathcal P).
\tag{53.11}
$$

固定任意 $i=(a,x,z)$，构造两份表 $P^+,P^-$。$P^+$ 的第 $a$ 列集中于 $(x,1-z)$，另一列集中于 $(1-x,0)$；$P^-$ 的第 $a$ 列集中于 $(1-x,0)$，另一列集中于 $(x,0)$。两表均属于 $\mathcal P$，而且

$$
P_i^+=P_i^-=0,\qquad
d(P^+)=s,\qquad d(P^-)=-s,\qquad
s=(-1)^a(1-2x)\in\{1,-1\}.
\tag{53.12}
$$

修复表各坐标非负，式（53.11）于是给 $k_i s\ge0$ 和 $-k_i s\ge0$，故 $k_i=0$。所有坐标同理，所以 $\mathcal R$ 在整个 $\mathcal P$ 上是恒等映射。但 $\mathcal P$ 含 $d\ne0$ 的表，不可能全落在 $\mathcal C$。矛盾。$\square$

在这份两轮布局中，三个二元变量都承担实际作用：若动作 $a$ 或第一输出 $x$ 为单点，所有表已经因果；若末输出 $z$ 为单点，取一个固定动作列或各动作列的固定凸组合，再向所有动作列重复同一分布，就得到正的仿射因果回缩。式（53.12）的双符号构造使用了同一 $x$ 下另一个 $z$；保留该末轮输出正是障碍发生的接口差别。

**推论 53.8（通用精确最优修复不能仿射选择）。** 使用第 52 节的全部因果反馈与全部终端事件偏差 $D_{\mathrm{fb}}$。任何对每个 $P\in\mathcal P$ 选择最优因果替代表的映射，都不可能在 $\mathcal P$ 上仿射。

**证明。** 对 $P\in\mathcal C$，最小偏差为零。若 $D_{\mathrm{fb}}(P,Q)=0$，分别取两个固定动作策略和每个单点终端事件 $\{(x,z)\}$，得到全部坐标 $P_a(x,z)=Q_a(x,z)$。所以每个已有因果表的唯一零误差修复是它自身。任何普遍最优选择映射都满足定理 53.7 排除的回缩条件。$\square$

### 53.6 单份编码的确定性物理边界

**推论 53.9（固定单份编码不能实现通用回缩）。** 将定义 53.6 的表编码为

$$
\rho_P=\frac12
\sum_{a,x,z}P_a(x,z)
|a,x,z\rangle\langle a,x,z|.
\tag{53.13}
$$

不存在一个固定、确定性的量子通道，对每个输入的一份 $\rho_P$，经过固定线性读出后都准确给出一份因果表，并逐点保持全部原本因果的表。

**证明。** 式（53.13）是密度矩阵，并对 $P$ 仿射。量子通道及固定线性读出均为线性映射，复合后得到 $P$ 的仿射函数。若其结果对全部输入都是因果表，并固定全部因果输入，便构成定理 53.7 中不存在的仿射回缩。固定的、与输入无关的辅助状态可以吸收到通道中，不改变结论。$\square$

该推论使用固定装置的无条件输出。它不把带成功条件的后选择归一化当作确定性通道，也不把概率编码当作可免费读取的完整经典表。已知完整表之后运行第 52 节的非线性算法，不在这一单份编码合同内。多份编码作为输入、受限输入族或不同资料接口也不由本推论判定；它没有证明这些替代接口一定足以精确修复。

因此，因果表的数学构造、允许策略的历史访问和固定物理操作的仿射性是三项独立条件。第 52 节的最优包络不提供缺失的权限；它的非线性数据处理也不能直接被解释为普遍保持既有因果过程的单次线性操作。

## 53.99 追加锚

## 54. 最小量子接口的尖锐因果修复

本节考虑先输出 $B$、后接收 $A$ 的有限维量子接口：第一轮输入和第二轮输出均为一维。静态候选仍可把晚输入 $A$ 映到早输出 $B$；因果替代表必须先准备一个与 $A$ 无关的态。允许的反馈包含全部量子通道、辅助参考、保留记忆及最终测量。在这个完整 tester 合同下，归一化缺陷恰好等于最优因果修复的事件响应误差。

### 54.1 Choi 配对与全部反馈事件

固定非零有限维 Hilbert 空间 $A,B$ 及其基，记 $d_A=\dim A$。静态候选是通道 $\Phi:A\to B$ 的未归一化 Choi 算符

$$
R\succeq0,\qquad \operatorname{Tr}_B R=I_A,
\tag{54.1}
$$

作用于 $B\otimes A$。这里的通道方向描述静态对应关系，而 $B$ 的输出被赋予较早的时刻。此接口上的归一化因果梳恰为

$$
S_\sigma=\sigma\otimes I_A,
\qquad \sigma\succeq0,\qquad \operatorname{Tr}\sigma=1.
\tag{54.2}
$$

**定义 54.1（完整反馈 tester）。** 反馈归一化算符及其事件集合为

$$
\mathcal C=
\{C\succeq0:\operatorname{Tr}_A C=I_B\},
\qquad C\in\mathcal C,\quad 0\preceq E\preceq C.
\tag{54.3}
$$

统一采用配对 $\operatorname{Tr}(RE)$。具体地，若反馈通道 $\Lambda:B\to A$ 的标准 Choi 算符为 $J_\Lambda$，则先交换其张量因子，再取**全转置**，得到式（54.3）的 $C$。全转置保持正性及对应的偏迹条件；该约定吸收量子梳 Born 规则中的全转置，不使用部分转置保持正性的错误推断。

$E$ 与 $C-E$ 正是某个二结果量子 instrument 的两个 Choi 元素。它可以通过辅助态、量子记忆、与 $B$ 的相互作用、输出 $A$ 和最后的测量实现；反过来，每个式（54.3）的正分解都可这样实现。因此，量词已经包含任意有限辅助参考和量子记忆。这个对应是 [Chiribella–D’Ariano–Perinotti，arXiv:0904.4483v2](https://arxiv.org/abs/0904.4483v2) 定义 11、引理 8 与定理 11–12（PDF 第 17–18 页）的本接口特例。

对非因果候选，$\operatorname{Tr}(RC)$ 不必为一，故 $\operatorname{Tr}(RE)$ 称为事件**响应**，不预先称为概率。定义

$$
\begin{aligned}
\Delta(R)
&=\max_{C\in\mathcal C}
\left|\operatorname{Tr}(RC)-1\right|,\\
D(R,S_\sigma)
&=\max_{\substack{C\in\mathcal C\\0\preceq E\preceq C}}
\left|\operatorname{Tr}\bigl((R-S_\sigma)E\bigr)\right|.
\end{aligned}
\tag{54.4}
$$

式（54.3）给 $\operatorname{Tr}C=\dim B$，故归一化算符与事件的联合可行集紧，以上最大值均能达到。每个因果替代表都满足 $\operatorname{Tr}(S_\sigma C)=1$。

### 54.2 最优修复等于归一化缺陷

**定理 54.2（最小量子接口的尖锐修复）。** 对每个满足式（54.1）的 $R$，

$$
\min_{\substack{\sigma\succeq0\\\operatorname{Tr}\sigma=1}}
D(R,\sigma\otimes I_A)=\Delta(R).
\tag{54.5}
$$

而且，任取输入密度算符 $\tau$，通道输出 $\Phi(\tau)$ 都是一个最优的 $\sigma$。

**证明。** 记

$$
u=\max_{C\in\mathcal C}\operatorname{Tr}(RC),
\qquad
\ell=\min_{C\in\mathcal C}\operatorname{Tr}(RC).
\tag{54.6}
$$

取任意密度算符 $\omega$，归一化算符 $C=I_B\otimes\omega$ 的响应为一。因此

$$
0\le\ell\le1\le u,
\qquad
\Delta(R)=\max\{u-1,1-\ell\}.
\tag{54.7}
$$

式（54.6）的两个半定规划对偶为

$$
\begin{aligned}
u&=\min_{U=U^*}
\{\operatorname{Tr}U:U\otimes I_A\succeq R\},\\
\ell&=\max_{L=L^*}
\{\operatorname{Tr}L:L\otimes I_A\preceq R\}.
\end{aligned}
\tag{54.8}
$$

原问题有严格正可行点 $I_B\otimes I_A/d_A$，两个对偶分别有充分大的 $U=tI_B$ 和 $L=-tI_B$ 作为严格可行点；紧性给有限最优值，半定规划强对偶遂给式（54.8）及最优值达到。相关强对偶条件可见 [Gutoski，arXiv:1008.4636v4](https://arxiv.org/abs/1008.4636v4) 附录 A 的 Fact 6。上界条件自动给 $U\succeq0$；**下界 $L$ 只要求厄米，不要求正性**。

先固定单位向量 $a\in A$，并令

$$
\sigma_a=(I_B\otimes\langle a|)R(I_B\otimes|a\rangle).
\tag{54.9}
$$

压缩式（54.1）与（54.8），得到

$$
\sigma_a\succeq0,\qquad
\operatorname{Tr}\sigma_a=1,\qquad
L\preceq\sigma_a\preceq U.
\tag{54.10}
$$

对任意 $C\in\mathcal C$、$0\preceq E\preceq C$，由 $U-\sigma_a\succeq0$ 得

$$
\begin{aligned}
\operatorname{Tr}\bigl((R-S_{\sigma_a})E\bigr)
&\le\operatorname{Tr}\bigl(((U-\sigma_a)\otimes I_A)E\bigr)\\
&\le\operatorname{Tr}\bigl(((U-\sigma_a)\otimes I_A)C\bigr)\\
&=\operatorname{Tr}(U-\sigma_a)=u-1.
\end{aligned}
\tag{54.11}
$$

同理由 $\sigma_a-L\succeq0$ 得

$$
\begin{aligned}
\operatorname{Tr}\bigl((S_{\sigma_a}-R)E\bigr)
&\le\operatorname{Tr}\bigl(((\sigma_a-L)\otimes I_A)E\bigr)\\
&\le\operatorname{Tr}\bigl(((\sigma_a-L)\otimes I_A)C\bigr)\\
&=\operatorname{Tr}(\sigma_a-L)=1-\ell.
\end{aligned}
\tag{54.12}
$$

故 $D(R,S_{\sigma_a})\le\Delta(R)$。另一方面，整个事件 $E=C$ 合法，所以任意因果替代表均满足

$$
D(R,S_\sigma)
\ge\max_{C\in\mathcal C}
\left|\operatorname{Tr}(RC)-\operatorname{Tr}(S_\sigma C)\right|
=\Delta(R).
\tag{54.13}
$$

这证明式（54.5）。

对任意输入态 $\tau$，改用正压缩

$$
X\longmapsto
\operatorname{Tr}_A\!\left[
(I_B\otimes\sqrt{\tau^{\mathsf T}})
X
(I_B\otimes\sqrt{\tau^{\mathsf T}})
\right].
\tag{54.14}
$$

它将 $R$ 送到 $\Phi(\tau)$，并分别将 $U\otimes I_A,L\otimes I_A$ 送到 $U,L$，于是同一证明成立。式（54.9）在标准 Choi 约定下对应输入 $|\bar a\rangle\langle\bar a|$，与式（54.14）一致。$\square$

**推论 54.3（统一的线性正投影达到最优修复）。** 定义

$$
\Pi X=\frac{\operatorname{Tr}_A X}{d_A}\otimes I_A.
\tag{54.15}
$$

则 $\Pi$ 是线性、完全正且保持迹的投影，固定每个 $S_\sigma$，并对全部满足式（54.1）的候选给

$$
D(R,\Pi R)=\Delta(R).
\tag{54.16}
$$

**证明。** 式（54.15）是对 $A$ 取偏迹再准备最大混合态的完全正映射，直接计算给保持迹和 $\Pi^2=\Pi$。若 $R$ 满足式（54.1），则 $\operatorname{Tr}_A R/d_A$ 是密度算符；在定理 54.2 中取 $\tau=I_A/d_A$ 即得式（54.16）。$\square$

特别地，$\Delta(R)=0$ 当且仅当 $R$ 已为式（54.2）的因果梳。正向由式（54.16）及事件分离性得到：满支撑归一化算符 $C_0=I_B\otimes I_A/d_A$ 的区间 $0\preceq E\preceq C_0$ 已能分离所有厄米算符。反向由归一化直接成立。

### 54.3 正 Loewner 下包络不能照搬经典构造

**命题 54.4（正下包络的严格损失）。** 存在满足式（54.1）的候选，其最小反馈响应 $\ell>0$，但所有正下包络 $L\succeq0$、$L\otimes I_A\preceq R$ 都只能取 $L=0$。

**证明。** 取 $A=B=\mathbb C^2$，令 $\rho_0,\rho_1$ 为两个不同且不正交的纯态，并定义

$$
R=\rho_0\otimes|0\rangle\langle0|
 +\rho_1\otimes|1\rangle\langle1|,
\qquad
\delta=\frac12\|\rho_0-\rho_1\|_1\in(0,1).
\tag{54.17}
$$

只有 $C$ 的两个 $A$ 对角块 $C_0,C_1$ 参与响应，而它们遍历全部 $C_0,C_1\succeq0$、$C_0+C_1=I_B$。对 $\rho_0-\rho_1$ 取正负谱分解，得到

$$
u=1+\delta,\qquad \ell=1-\delta,\qquad\Delta(R)=\delta.
\tag{54.18}
$$

若 $L\succeq0$ 且 $L\otimes I_A\preceq R$，则 $L\preceq\rho_0,\rho_1$。被秩一正算符支配的正算符，其支撑包含于该秩一支撑。两条不同纯态射线的交为零，故 $L=0$，于是

$$
\max\{\operatorname{Tr}L:L\succeq0,\ L\otimes I_A\preceq R\}
=0<\ell.
\tag{54.19}
$$

例如取 $\rho_0=|0\rangle\langle0|$、$\rho_1=|+\rangle\langle+|$，则 $\delta=1/\sqrt2$，式（54.8）的一对最优解为

$$
L=\frac{\rho_0+\rho_1-\delta I_B}{2},
\qquad
U=\frac{\rho_0+\rho_1+\delta I_B}{2}.
\tag{54.20}
$$

其中 $L$ 有一个负特征值。$\square$

因此，经典逐点正下包络不能仅把大小关系换成 Loewner 序便保留相同最优质量。定理 54.2 使用厄米下界，并通过同一次正压缩取得 $L\preceq\sigma\preceq U$；命题 54.4 不反驳尖锐修复等式。

### 54.4 非归一化候选必须保留迹项

**命题 54.5（事件误差与策略范数的准确关系）。** 对任意厄米算符 $X$ 和固定 $C\succeq0$，

$$
\max_{0\preceq E\preceq C}|\operatorname{Tr}(XE)|
=\frac12\left(
\|\sqrt C X\sqrt C\|_1
+|\operatorname{Tr}(XC)|
\right).
\tag{54.21}
$$

因而本节的事件误差为

$$
D(R,S)=\frac12\max_{C\in\mathcal C}
\left[
\|\sqrt C(R-S)\sqrt C\|_1
+|\operatorname{Tr}((R-S)C)|
\right].
\tag{54.22}
$$

**证明。** 在 $C$ 的支撑上写 $E=\sqrt C F\sqrt C$，其中 $0\preceq F\preceq I$。令 $Y=\sqrt C X\sqrt C$。正向最大值为 $\operatorname{Tr}Y_+$，负向最大值为 $\operatorname{Tr}Y_-$；二者的较大值等于 $(\|Y\|_1+|\operatorname{Tr}Y|)/2$。再对 $C$ 取最大即得式（54.22）。$\square$

若 $R,S$ 均为归一化确定性量子梳，则每个 $C$ 都给 $\operatorname{Tr}((R-S)C)=0$，事件误差才化为通常策略范数的一半。策略范数的半定规划和序区间对偶见 [Gutoski，arXiv:1008.4636v4](https://arxiv.org/abs/1008.4636v4) 第 4 节式（1）–（2）、定理 3（PDF 第 14–15 页）；正算符的最小策略上界质量见该文定理 4。对非因果候选，式（54.22）的迹项不能删掉，而且两个项必须在**同一个** $C$ 上相加后再取最大。

### 54.5 与完整两轮问题的边界

完整两轮接口 $A_1\to B_1$、$A_2\to B_2$ 的确定性因果梳满足

$$
\begin{gathered}
S\succeq0,\qquad
\operatorname{Tr}_{B_2}S=I_{A_2}\otimes S_1,\\
S_1\succeq0,\qquad
\operatorname{Tr}_{B_1}S_1=I_{A_1}.
\end{gathered}
\tag{54.23}
$$

这里采用张量次序 $B_2\otimes A_2\otimes B_1\otimes A_1$。其全部 tester 归一化算符与事件为

$$
\begin{gathered}
C=I_{B_2}\otimes T,\qquad T\succeq0,\\
\operatorname{Tr}_{A_2}T=I_{B_1}\otimes\tau,
\qquad\tau\succeq0,\quad\operatorname{Tr}\tau=1,
\qquad0\preceq E\preceq C.
\end{gathered}
\tag{54.24}
$$

式（54.23）为确定性梳的标准递归条件，见 [Chiribella–D’Ariano–Perinotti，arXiv:0904.4483v2](https://arxiv.org/abs/0904.4483v2) 定理 5（PDF 第 11 页）；式（54.24）为同文 tester 条件在两轮的展开。

若静态候选仅满足 $R\succeq0$、$\operatorname{Tr}_{B_1B_2}R=I_{A_1A_2}$，仍可用式（54.24）定义 $\Delta,D$。整个事件 $E=C$ 继续证明

$$
\inf_{S\text{ 满足式（54.23）}}D(R,S)\ge\Delta(R).
\tag{54.25}
$$

但定理 54.2 的压缩论证本身没有给出这里的反向不等式：对 $\operatorname{Tr}_{B_2}R$ 压缩可产生早期 Choi 边缘，却还须证明能把它延拓为正的完整 $S$，同时保留足够的 $B_2$ 关联并达到同一事件误差界。这个正延拓步骤没有包含在式（54.9）–（54.12）中。

**命题 54.6（任意有限轮数的统一修复界）。** 对任意有限轮数，令 $\mathcal S$ 为全部归一化确定性因果梳，$\mathcal C$ 为其全部确定性 tester 归一化算符。对 $R\succeq0$ 定义

$$
u=\max_{C\in\mathcal C}\operatorname{Tr}(RC),
\qquad
\ell=\min_{C\in\mathcal C}\operatorname{Tr}(RC),
$$

并假设 $\ell\le1\le u$。归一化的全局静态通道满足这个假设：选择提前准备全部输入、逐轮送入并丢弃输出的 tester，响应为一。沿用式（54.4）的事件响应定义，则存在 $S^+\in\mathcal S$ 满足

$$
\Delta(R)\le\inf_{S\in\mathcal S}D(R,S)
\le D(R,S^+)
\le\max\left\{u-1,\frac{u-\ell}{u}\right\}
\le2\Delta(R).
\tag{54.26}
$$

**证明。** 每轮使用完全去极化通道便得到一个正定的因果梳 $S_0$。有限维性保证存在 $q>0$ 使 $R/q\preceq S_0$，故 $R/q$ 与 $S_0-R/q$ 是一个二结果 measuring strategy 的正元素。[Gutoski，arXiv:1008.4636v4](https://arxiv.org/abs/1008.4636v4) 定理 4 的最大响应与最小策略上界质量相等，应用于 $R/q$ 后再乘以 $q$，给出达到最优值的

$$
R\preceq uS^+,\qquad S^+\in\mathcal S.
\tag{54.27}
$$

因此任意合法事件 $0\preceq E\preceq C$ 满足

$$
\operatorname{Tr}((R-S^+)E)
\le(u-1)\operatorname{Tr}(S^+E)
\le u-1.
\tag{54.28}
$$

令 $K=uS^+-R\succeq0$。由于 $u\ge1$ 及 $R\succeq0$，

$$
S^+-R=\frac Ku-\frac{u-1}{u}R\preceq\frac Ku.
$$

于是另一方向满足

$$
\operatorname{Tr}((S^+-R)E)
\le\frac{\operatorname{Tr}(KE)}u
\le\frac{\operatorname{Tr}(KC)}u
=\frac{u-\operatorname{Tr}(RC)}u
\le\frac{u-\ell}u.
\tag{54.29}
$$

两向结合给式（54.26）的中间上界；由 $u-1\le\Delta(R)$、$1-\ell\le\Delta(R)$ 及 $u\ge1$ 得最后一项。下界仍由整个事件 $E=C$ 给出。$\square$

**推论 54.7（一般界留下的精确范围）。** 记 $\delta=\Delta(R)$，则

$$
\begin{cases}
\displaystyle
\delta\le\inf_{S\in\mathcal S}D(R,S)
\le\dfrac{2\delta}{1+\delta},&0\le\delta\le1,\\[6pt]
\displaystyle
\inf_{S\in\mathcal S}D(R,S)=\delta,&\delta\ge1.
\end{cases}
\tag{54.30}
$$

**证明。** 令 $a=u-1$、$b=1-\ell$，则 $a\ge0$、$0\le b\le1$ 且 $\delta=\max\{a,b\}$。若 $\delta\le1$，由 $a,b\le\delta$ 得

$$
\frac{a+b}{1+a}
\le\frac{a+\delta}{1+a}
\le\frac{2\delta}{1+\delta};
$$

最后一步等价于 $a(1-\delta)\le\delta(1-\delta)$。同时 $a\le\delta\le2\delta/(1+\delta)$。若 $\delta\ge1$，则 $b\le1$ 给 $(a+b)/(1+a)\le1\le\delta$，而 $a\le\delta$。代入式（54.26），并结合普遍下界即得。$\square$

上述界在完整参考和全部序贯 tester 的同一合同下成立。一般尖锐等式的未决范围因此只剩 $0<\Delta(R)<1$；本节没有把式（54.30）的上界判为最优。将它收紧到普遍的系数 $1$，仍需解决上述正延拓或插值问题。

第 53 节的仿射选择障碍保留了非平凡的末轮输出；定理 54.2 将该输出空间取为一维，因此式（54.15）的正投影与该障碍属于不同接口范围。本节既不将此投影外推为完整两轮的仿射修复，也不把所选因果替代表等同于对原物理来源的识别。

## 54.99 追加锚

## 55. 完整末轮输出下的量子因果修复严格反例

本节在第54节的同一完整量子 tester 合同下，给出保留末轮输出时的严格反例：最优因果修复误差不总等于归一化缺陷。第54节的普遍上下界、最小接口的尖锐等式及大缺陷区间的等式均保留；这里排除将系数一推广到全部有限量子过程。全文给出普通数学证明，不声称新增 Lean 核验或原创优先权。

### 55.1 接口、配对和事件合同

取早期输出 $B=\mathbb C^2$、晚输入 $A=\mathbb C^2$、晚输出 $D=\mathbb C^3$；第一轮输入为一维。固定基并采用张量次序 $A\otimes B\otimes D$。静态候选是通道 $A\to B\otimes D$ 的未归一化 Choi 算符：

$$
R\succeq0,\qquad\operatorname{Tr}_{BD}R=I_A.
\tag{55.1}
$$

归一化因果修复恰为

$$
S\succeq0,\qquad
\operatorname{Tr}_D S=I_A\otimes\sigma,
\qquad\sigma\succeq0,\quad\operatorname{Tr}\sigma=1.
\tag{55.2}
$$

所有反馈归一化算符写作 $\widehat C=C\otimes I_D$，其中

$$
C\succeq0,\qquad\operatorname{Tr}_A C=I_B.
\tag{55.3}
$$

吸收标准梳 Born 规则中的全转置后，事件为全部 $0\preceq E\preceq\widehat C$，配对为 $\operatorname{Tr}(RE)$。量词包括全部有限辅助参考、量子记忆及最终测量，而不限定某个反馈通道的经典实现方式。任意正分解 $(E,\widehat C-E)$ 都是可实现的二结果 tester。

定义

$$
\begin{aligned}
\Delta(R)&=\max_C|\operatorname{Tr}(R\widehat C)-1|,\\
D(R,S)&=\max_{C,\;0\preceq E\preceq\widehat C}
|\operatorname{Tr}((R-S)E)|.
\end{aligned}
\tag{55.4}
$$

对非因果候选，式（55.4）比较事件响应，不预设其在每个反馈下已归一化。

### 55.2 单向事件支持函数的半定规划对偶

**引理 55.1。** 对任意厄米 $X$，令

$$
h(X)=\max_{C,\;0\preceq E\preceq C\otimes I_D}\operatorname{Tr}(XE).
$$

则

$$
h(X)=\min\left\{\operatorname{Tr}n:
N\succeq0,\ N\succeq X,\quad
\operatorname{Tr}_D N=I_A\otimes n\right\},
\tag{55.5}
$$

且最小值达到。这里 $n$ 自动为正算符。

**证明。** 引入 $F\succeq0$，将原问题写成

$$
E,F\succeq0,\qquad E+F=C\otimes I_D,
\qquad\operatorname{Tr}_A C=I_B.
$$

可将 $C$ 当作自由厄米变量，因为前一等式已推出 $C\succeq0$。对两条等式分别使用厄米乘子 $N,n$，Lagrange 表达式为

$$
\operatorname{Tr}n+
\operatorname{Tr}((X-N)E)-\operatorname{Tr}(NF)
+\operatorname{Tr}\bigl((\operatorname{Tr}_D N-I_A\otimes n)C\bigr).
$$

其上确界有限当且仅当式（55.5）的约束成立。原问题有严格正可行点
$C=I_{AB}/\dim A$、$E=F=(C\otimes I_D)/2$；对偶取充分大的 $N=tI_{ABD}$、$n=t(\dim D)I_B$ 亦严格可行。原问题的可行集紧，故有限维半定规划强对偶给式（55.5）及达到性。$\square$

特别地，

$$
D(R,S)=\max\{h(R-S),h(S-R)\}.
\tag{55.6}
$$

这是两套独立的单向上界，不是把单独的策略范数除以二。

### 55.3 一个 $2\times2\times3$ 等距候选

定义等距

$$
V|0\rangle=|0\rangle_B|0\rangle_D,
\qquad
V|1\rangle=\frac{\sqrt3}{2}|0\rangle_B|1\rangle_D
+\frac12|1\rangle_B|2\rangle_D.
\tag{55.7}
$$

在 $A\otimes B\otimes D$ 中记

$$
x=|0,0,0\rangle,\quad
y=|1,0,1\rangle,\quad
z=|1,1,2\rangle,\quad
v=x+\frac{\sqrt3}{2}y+\frac12z,
\qquad R=|v\rangle\langle v|.
\tag{55.8}
$$

$V$ 的两列正交且单位，因此 $R$ 满足式（55.1）。其早期边缘为

$$
M=\operatorname{Tr}_D R
=|0,0\rangle\langle0,0|
+\frac34|1,0\rangle\langle1,0|
+\frac14|1,1\rangle\langle1,1|.
\tag{55.9}
$$

这是对角的经典通道边缘；完整 Choi 算符仍保留晚输出相干。

**命题 55.2。** 此候选满足

$$
u=\max_C\operatorname{Tr}(R\widehat C)=\frac54,
\qquad
\ell=\min_C\operatorname{Tr}(R\widehat C)=\frac34,
\qquad
\Delta(R)=\frac14.
\tag{55.10}
$$

**证明。** 若 $c_{ab}=\langle a,b|C|a,b\rangle$，式（55.3）给
$c_{00}+c_{10}=1$、$c_{01}+c_{11}=1$ 及 $0\le c_{ab}\le1$。由式（55.9），

$$
\operatorname{Tr}(R\widehat C)
=\frac34+\frac14(c_{00}+c_{11})\in[3/4,5/4].
$$

两端分别由

$$
\begin{aligned}
C_+&=|0,0\rangle\langle0,0|+|1,1\rangle\langle1,1|,\\
C_-&=|0,1\rangle\langle0,1|+|1,0\rangle\langle1,0|
\end{aligned}
\tag{55.11}
$$

达到。二者都满足式（55.3）。$\square$

### 55.4 系数一的严格失败

**定理 55.3。** 对式（55.8）的候选，

$$
\min_{S\text{ 满足式（55.2）}}D(R,S)>\frac14=\Delta(R).
\tag{55.12}
$$

**证明。** 反设某个因果 $S$ 满足 $D(R,S)\le1/4$。令

$$
Q_+=C_+\otimes I_D,\qquad Q_-=C_-\otimes I_D;
$$

它们是正交互补投影。

先看 $Q_+$。归一化给

$$
\operatorname{Tr}((R-S)Q_+)=\frac54-1=\frac14.
\tag{55.13}
$$

若 $Q_+(R-S)Q_+$ 有负谱部分，则其正谱部分的迹严格大于 $1/4$。取该正谱部分的支撑投影作为 $E\preceq Q_+$，就违反 $D\le1/4$。因此

$$
0\preceq Q_+SQ_+\preceq Q_+RQ_+
=|w\rangle\langle w|,
\qquad w=x+\frac12z.
$$

秩一支撑于是迫使

$$
Q_+SQ_+=t|w\rangle\langle w|.
$$

其迹为 $\operatorname{Tr}(SQ_+)=1$，而 $\|w\|^2=5/4$，所以

$$
t=\frac45,
\qquad
\langle x|S|x\rangle=\frac45,
\qquad
\langle0|\sigma|0\rangle=\frac45.
\tag{55.14}
$$

最后一式来自 $Q_+$ 包含完整的 $A=0,B=0$ 块，并结合式（55.2）。再由 $A=1,B=0$ 块的偏迹，得到

$$
0\le\langle y|S|y\rangle\le\frac45.
\tag{55.15}
$$

正性矩阵元界给

$$
|\langle x|S|y\rangle|^2
\le\langle x|S|x\rangle\langle y|S|y\rangle
\le\left(\frac45\right)^2.
\tag{55.16}
$$

再看负方向。由引理 55.1 及 $h(S-R)\le1/4$，存在

$$
N\succeq0,\quad N\succeq S-R,\quad
\operatorname{Tr}_D N=I_A\otimes n,
\quad\operatorname{Tr}n\le\frac14.
\tag{55.17}
$$

但 $Q_-$ 上的总差已经为

$$
\operatorname{Tr}((S-R)Q_-)=1-\frac34=\frac14.
$$

而 $\operatorname{Tr}(NQ_-)=\operatorname{Tr}n$，故式（55.17）强制

$$
\operatorname{Tr}n=\frac14,
\qquad (N-S+R)Q_-=0.
\tag{55.18}
$$

此处使用的事实是：若 $Y\succeq0$、$Q$ 为投影且 $\operatorname{Tr}(YQ)=0$，则 $YQ=0$。

因为 $y\in\operatorname{ran}Q_-$，式（55.18）给

$$
\langle x|N|y\rangle
=\langle x|S|y\rangle-\frac{\sqrt3}{2}.
\tag{55.19}
$$

整个 $A=1,B=0$ 块也包含于 $Q_-$。对该块取 $D$ 迹，并用式（55.9）、（55.14），得

$$
\langle0|n|0\rangle
=\langle0|\sigma|0\rangle-\frac34
=\frac45-\frac34=\frac1{20}.
\tag{55.20}
$$

式（55.17）的因果偏迹及 $N\succeq0$ 因而分别给

$$
\langle x|N|x\rangle\le\frac1{20},
\qquad
\langle y|N|y\rangle\le\frac1{20}.
$$

再用正性矩阵元界与式（55.19），

$$
\left|\langle x|S|y\rangle-\frac{\sqrt3}{2}\right|
=|\langle x|N|y\rangle|
\le\frac1{20}.
\tag{55.21}
$$

式（55.16）与（55.21）的三角不等式给

$$
\frac{\sqrt3}{2}
\le\frac45+\frac1{20}=\frac{17}{20},
$$

而 $3/4=300/400>289/400=(17/20)^2$，矛盾。

最后，式（55.2）的因果集合为闭且有界的有限维集合，且 $D(R,S)$ 是紧 tester 集上连续线性响应绝对值的最大值，因此连续并达到最小值。既然没有任何 $S$ 满足 $D(R,S)\le1/4$，最小值必严格大于 $1/4$。$\square$

### 55.5 任意小缺陷的同一反例族

**推论 55.4。** 对每个 $0<\varepsilon\le1/4$，令

$$
V_\varepsilon|0\rangle=|0,0\rangle,
\qquad
V_\varepsilon|1\rangle
=\sqrt{1-\varepsilon}|0,1\rangle
+\sqrt\varepsilon|1,2\rangle,
\qquad
R_\varepsilon=|x+\sqrt{1-\varepsilon}\,y+\sqrt\varepsilon\,z\rangle
\langle x+\sqrt{1-\varepsilon}\,y+\sqrt\varepsilon\,z|.
\tag{55.22}
$$

则

$$
\Delta(R_\varepsilon)=\varepsilon,
\qquad
\min_{S\text{ 因果}}D(R_\varepsilon,S)>\varepsilon.
\tag{55.23}
$$

**证明。** 同一 $C_+,C_-$ 分别给 $u=1+\varepsilon$、$\ell=1-\varepsilon$。反设 $D\le\varepsilon$，定理 55.3 的两个饱和步骤给

$$
t=\frac1{1+\varepsilon},
\qquad \sigma_{00}=t,
\qquad n_{00}=t-(1-\varepsilon)
=\frac{\varepsilon^2}{1+\varepsilon}.
$$

相同的两次正性矩阵元界于是迫使

$$
\sqrt{1-\varepsilon}
\le t+\frac{\varepsilon^2}{1+\varepsilon}
=\frac{1+\varepsilon^2}{1+\varepsilon}.
\tag{55.24}
$$

对 $0<\varepsilon<1$，式（55.24）的反向严格不等式等价于

$$
(1-\varepsilon)(1+\varepsilon)^2
>(1+\varepsilon^2)^2
\iff
1-3\varepsilon-\varepsilon^2-\varepsilon^3>0.
$$

当 $0<\varepsilon\le1/4$ 时，最后一式的左边至少为 $11/64>0$，矛盾。最小值达到性同定理 55.3。$\square$

因此，归一化缺陷任意小仍不能保证完整两轮接口的同系数修复。这个严格族结论没有给出独立于 $\varepsilon$ 的比例间隙，也不将误差增长误写为平方根级；一般线性上界继续适用。

### 55.6 同边缘退相干对照：全部总响应相同，修复成本不同

**命题 55.5。** 对推论 55.4 的 $R_\varepsilon$，在末输出 $D$ 的指定基上完全退相干，得到

$$
R_\varepsilon^{\mathrm{diag}}
=|x\rangle\langle x|
+(1-\varepsilon)|y\rangle\langle y|
+\varepsilon|z\rangle\langle z|.
\tag{55.25}
$$

它与 $R_\varepsilon$ 具有相同的早期边缘，因而对**每一个**反馈归一化算符都有

$$
\operatorname{Tr}(R_\varepsilon^{\mathrm{diag}}\widehat C)
=\operatorname{Tr}(R_\varepsilon\widehat C).
\tag{55.26}
$$

但其最优因果修复误差恰为

$$
\min_{S\text{ 因果}}D(R_\varepsilon^{\mathrm{diag}},S)
=\varepsilon
<\min_{S\text{ 因果}}D(R_\varepsilon,S).
\tag{55.27}
$$

**证明。** 对 $D$ 退相干保留 $\operatorname{Tr}_D R$，而 $\widehat C=C\otimes I_D$ 只读取该偏迹，故式（55.26）成立。取

$$
S^{\mathrm{diag}}=|x\rangle\langle x|+|y\rangle\langle y|.
$$

其偏迹为 $I_A\otimes|0\rangle\langle0|$，所以因果且归一化。二者之差为

$$
R_\varepsilon^{\mathrm{diag}}-S^{\mathrm{diag}}
=\varepsilon\bigl(|z\rangle\langle z|-|y\rangle\langle y|\bigr).
$$

对任意合法 $E\preceq C\otimes I_D$，式（55.3）给

$$
0\le\langle y|E|y\rangle\le\langle1,0|C|1,0\rangle\le1,
\qquad
0\le\langle z|E|z\rangle\le\langle1,1|C|1,1\rangle\le1.
$$

故事件响应差的绝对值不超过 $\varepsilon$。结合归一化缺陷的下界，得到左侧等号；右侧严格不等式由推论 55.4 给出。$\square$

所以，全部反馈总质量的读数一致仍不足以决定最优因果修复成本。式（55.26）没有把事件算符也限制为对角；两边始终接受相同的全部量子 tester。差异来自完整候选保留的末输出相干。

### 55.7 正插值障碍的具体位置

$R$ 是秩一且非因果。若 $0\preceq T\preceq R$，则 $T=cR$；若另要求 $T$ 为非零正的因果梳倍数，$c>0$ 会使 $R$ 自身满足因果偏迹，与式（55.9）矛盾。因此它没有非零的正因果下包络，尽管最小反馈响应为 $3/4$。

比“没有正下包络”更强的结论是定理 55.3：即使允许任意非线性的因果替代表选择，也不能达到归一化缺陷本身。两份极端反馈 $Q_+,Q_-$ 的同时饱和，分别强制修复算符的秩一压缩和负方向因果上界的零余量；正性最终不能容纳原候选的矩阵元 $\langle x|R|y\rangle=\sqrt3/2$。

一般的策略上界质量构造仍给此例

$$
\frac14<\min_S D(R,S)\le\frac25.
\tag{55.28}
$$

这个上界也有本例内的直接构造。对任意 $0<\varepsilon\le1/4$，令

$$
T=R_\varepsilon
+\varepsilon|0,1,0\rangle\langle0,1,0|
+\varepsilon|1,0,0\rangle\langle1,0,0|.
$$

则 $T\succeq R_\varepsilon$，且
$\operatorname{Tr}_D T=I_A\otimes\operatorname{diag}(1,\varepsilon)$，所以 $S=T/(1+\varepsilon)$ 因果且归一化。正向事件差由 $R_\varepsilon-S\preceq\varepsilon S$ 控制为 $\varepsilon$；负向使用

$$
S-R_\varepsilon\preceq\frac{T-R_\varepsilon}{1+\varepsilon},
\qquad
\operatorname{Tr}((T-R_\varepsilon)\widehat C)
=1+\varepsilon-\operatorname{Tr}(R_\varepsilon\widehat C)
\le2\varepsilon,
$$

得到 $D(R_\varepsilon,S)\le2\varepsilon/(1+\varepsilon)$，在 $\varepsilon=1/4$ 时即为 $2/5$。未将该上界或任何数值解宣称为本例的精确最优值。最小接口去掉 $D$ 后，保留下来的 $M$ 可以按尖锐修复定理达到 $1/4$；式（55.12）说明保留末输出及其相干后，边缘结论不能直接提升为完整梳的同系数结论。

### 55.8 来源范围

完整 tester 与实现定理采用 [Chiribella–D’Ariano–Perinotti, arXiv:0904.4483v2](https://arxiv.org/abs/0904.4483v2)，定义 11、引理 8、定理 11–12，PDF 第 17–18 页。有限维半定规划强对偶条件可见 [Gutoski, arXiv:1008.4636v4](https://arxiv.org/abs/1008.4636v4)，附录 A 的 Fact 6；该文定理 4 给一般策略上界质量。式（55.5）的单向对偶及本反例的证明均已在上文展开，未以数值最优值作为证明前提。

## 追加锚（本行以下为增补区）

## 56. 两轮量子因果修复的统一线性比例间隙

### 56.1 合同与结论

采用 $A\otimes B\otimes D$ 端口次序，$\dim A=\dim B=2$、$\dim D=3$，其中 $A$ 为晚输入、$B$ 为早输出、$D$ 为晚输出。因果归一化修复满足

$$
S\succeq0,\qquad\operatorname{Tr}_D S=I_A\otimes\sigma,
\qquad\sigma\succeq0,\quad\operatorname{Tr}\sigma=1.
\tag{56.1}
$$

吸收全转置后，全部 tester 归一化算符为 $C\otimes I_D$，其中 $C\succeq0$、$\operatorname{Tr}_A C=I_B$；事件遍历全部 $0\preceq E\preceq C\otimes I_D$。定义

$$
D(R,S)=\max_{C,E}|\operatorname{Tr}((R-S)E)|.
\tag{56.2}
$$

记

$$
x=|0,0,0\rangle,\quad y=|1,0,1\rangle,\quad z=|1,1,2\rangle,
\qquad
R_\varepsilon=|x+\sqrt{1-\varepsilon}\,y+\sqrt\varepsilon\,z\rangle
\langle x+\sqrt{1-\varepsilon}\,y+\sqrt\varepsilon\,z|,
\qquad0<\varepsilon\le\frac14.
\tag{56.3}
$$

这是等距通道的 Choi 算符，全部反馈总响应的范围为 $[1-\varepsilon,1+\varepsilon]$，因此归一化缺陷为 $\Delta(R_\varepsilon)=\varepsilon$。

**定理 56.1（统一线性比例间隙）。** 对式（56.3）的整个族，

$$
\left(1+\frac1{10000}\right)\varepsilon
<\min_{S\text{ 因果}}D(R_\varepsilon,S)
\le\frac{2\varepsilon}{1+\varepsilon}.
\tag{56.4}
$$

所以额外修复成本满足

$$
\frac{\varepsilon}{10000}
<\min_S D(R_\varepsilon,S)-\varepsilon
\le\frac{\varepsilon(1-\varepsilon)}{1+\varepsilon}
<\varepsilon.
\tag{56.5}
$$

因此该额外成本在 $\varepsilon\downarrow0$ 时为 $\Theta(\varepsilon)$。式（56.4）的比例常数不主张尖锐。 特别地，在 $\varepsilon=1/4$ 时，

$$
\min_{S\text{ 因果}}D(R_{1/4},S)>\frac{10001}{40000}.
$$

### 56.2 单向对偶与两个极端反馈

对任意厄米 $X$，单向支持函数的准确对偶为

$$
h(X)=\max_{C,\,0\preceq E\preceq C\otimes I_D}\operatorname{Tr}(XE)
=\min\{\operatorname{Tr}n:
N\succeq0,\ N\succeq X,\operatorname{Tr}_D N=I_A\otimes n\}.
\tag{56.6}
$$

式（56.6）直接复用引理 55.1，最小值达到，并且

$$
D(R,S)=\max\{h(R-S),h(S-R)\}.
$$

两个方向使用独立上界，保留非归一化候选的完整事件响应。

定义互补投影

$$
\begin{aligned}
Q_+&=(|0,0\rangle\langle0,0|+|1,1\rangle\langle1,1|)\otimes I_D,\\
Q_-&=(|0,1\rangle\langle0,1|+|1,0\rangle\langle1,0|)\otimes I_D.
\end{aligned}
\tag{56.7}
$$

它们都是合法反馈归一化算符，并满足

$$
\operatorname{Tr}(SQ_\pm)=1,
\quad\operatorname{Tr}(R_\varepsilon Q_+)=1+\varepsilon,
\quad\operatorname{Tr}(R_\varepsilon Q_-)=1-\varepsilon.
\tag{56.8}
$$

下面证明：若某个 $\eta\ge0$ 允许

$$
D(R_\varepsilon,S)\le\varepsilon+\eta,
\tag{56.9}
$$

则必须满足一个明确的不等式，再以 $\eta=\varepsilon/10000$ 反驳它。

### 56.3 正方向压缩的精细概率界

令

$$
\rho=Q_+SQ_+,\qquad
q=\frac{x+\sqrt\varepsilon\,z}{\sqrt{1+\varepsilon}},
\qquad P=Q_+-|q\rangle\langle q|,
\qquad k=\operatorname{Tr}(P\rho).
$$

由式（56.8），$\rho\succeq0$、$\operatorname{Tr}\rho=1$。算符

$$
H_+=Q_+(R_\varepsilon-S)Q_+
=(1+\varepsilon)|q\rangle\langle q|-\rho
$$

的迹为 $\varepsilon$。其正谱事件合法，式（56.9）给

$$
\operatorname{Tr}(H_+)_-
=\operatorname{Tr}(H_+)_+-\varepsilon\le\eta.
$$

因为 $Pq=0$，

$$
k=-\operatorname{Tr}(PH_+)
\le\operatorname{Tr}(H_+)_-\le\eta.
\tag{56.10}
$$

令 $B_{00}=|0,0\rangle\langle0,0|\otimes I_D$，并记

$$
s=\sigma_{00}=\operatorname{Tr}(B_{00}\rho),
\qquad t=\langle q|B_{00}|q\rangle=\frac1{1+\varepsilon}.
$$

$B_{00}$ 是包含于 $Q_+$ 的投影，因此

$$
\|PB_{00}q\|^2=t(1-t).
$$

按 $q\oplus q^\perp$ 对 $\rho$ 分块。其 $q$ 对角块为 $1-k$，正的补块迹为 $k$。正性矩阵元界给交叉项的绝对值不超过
$\sqrt{(1-k)t(1-t)k}$，而补块对 $B_{00}$ 的响应不超过 $k$。因此

$$
\begin{aligned}
s
&\le(1-k)t+2\sqrt{(1-k)t(1-t)k}+k\\
&\le t+(1-t)\eta+2\sqrt{t(1-t)\eta}\\
&=t+\frac{\varepsilon\eta}{1+\varepsilon}
+\frac{2\sqrt{\varepsilon\eta}}{1+\varepsilon}.
\end{aligned}
\tag{56.11}
$$

交叉项界可直接写成
$|\langle q|\rho PB_{00}|q\rangle|^2
\le\langle q|\rho|q\rangle
\langle PB_{00}q|\rho|PB_{00}q\rangle
\le(1-k)t(1-t)k$；不需要对补块作交换性假设。

另一个关键界保留了实际坐标 $x$。$B_{00}-|x\rangle\langle x|$ 是 $q$ 正交补内的投影，故

$$
0\le s-\langle x|S|x\rangle
\le k\le\eta.
\tag{56.12}
$$

因果偏迹仍给 $S_{xx},S_{yy}\le s$，因此 $|S_{xy}|\le s$。

### 56.4 负向余量的局部界

由式（56.6）、（56.9），取

$$
N\succeq0,\quad N\succeq S-R_\varepsilon,
\quad\operatorname{Tr}_D N=I_A\otimes n,
\quad\operatorname{Tr}n\le\varepsilon+\eta.
$$

令 $Y=N-S+R_\varepsilon\succeq0$。在 $Q_-$ 上，

$$
\operatorname{Tr}(YQ_-)=\operatorname{Tr}n-\varepsilon\le\eta.
\tag{56.13}
$$

所以 $Y_{yy}\le\eta$。对 $A=1,B=0$ 的完整 $D$ 块取迹，得到

$$
n_{00}=s-(1-\varepsilon)
+\operatorname{Tr}(Y|_{A=1,B=0})
\le s-1+\varepsilon+\eta.
\tag{56.14}
$$

因为 $N_{xx}\le n_{00}$，式（56.12）、（56.14）给出局部取消

$$
\begin{aligned}
Y_{xx}
&=N_{xx}-S_{xx}+1\\
&\le n_{00}-S_{xx}+1\\
&\le(s-S_{xx})+\varepsilon+\eta
\le\varepsilon+2\eta.
\end{aligned}
\tag{56.15}
$$

于是

$$
|Y_{xy}|\le\sqrt{(\varepsilon+2\eta)\eta},
\qquad
|N_{xy}|\le n_{00}\le s-1+\varepsilon+\eta.
\tag{56.16}
$$

在恒等式 $R_{xy}=S_{xy}-N_{xy}+Y_{xy}$ 中使用式（56.11）、（56.16），得到

$$
\begin{aligned}
\sqrt{1-\varepsilon}
&\le2s-1+\varepsilon+\eta
+\sqrt{(\varepsilon+2\eta)\eta}\\
&\le\frac{1+\varepsilon^2}{1+\varepsilon}
+\frac{4\sqrt{\varepsilon\eta}}{1+\varepsilon}
+\frac{2\varepsilon\eta}{1+\varepsilon}
+\eta+\sqrt{(\varepsilon+2\eta)\eta}.
\end{aligned}
$$

故假设（56.9）要求

$$
g_\varepsilon:=\sqrt{1-\varepsilon}
-\frac{1+\varepsilon^2}{1+\varepsilon}
\le
\frac{4\sqrt{\varepsilon\eta}}{1+\varepsilon}
+\frac{2\varepsilon\eta}{1+\varepsilon}
+\eta+\sqrt{(\varepsilon+2\eta)\eta}.
\tag{56.17}
$$

### 56.5 统一的有理阈值

平方差恒等式给

$$
\frac{g_\varepsilon}{\varepsilon}
=
\frac{1-3\varepsilon-\varepsilon^2-\varepsilon^3}
{(1+\varepsilon)[(1+\varepsilon)\sqrt{1-\varepsilon}+1+\varepsilon^2]}.
$$

对 $0<\varepsilon\le1/4$，分子至少为 $11/64$，分母至多为
$(5/4)(5/4+5/4)=25/8$，故

$$
\frac{g_\varepsilon}{\varepsilon}\ge\frac{11}{200}.
\tag{56.18}
$$

在式（56.17）取 $\eta=\varepsilon/10000$，其右侧除以 $\varepsilon$ 后不超过

$$
\frac1{25}+\frac1{20000}+\frac1{10000}
+\frac1{100}\sqrt{1+\frac1{5000}}
<\frac1{25}+\frac1{20000}+\frac1{10000}
+\frac{1001}{100000}
=\frac{627}{12500}
<\frac{11}{200}.
\tag{56.19}
$$

第一个严格不等式使用
$(1001/1000)^2>1+1/5000$。式（56.18）、（56.19）矛盾，因此不存在满足
$D(R_\varepsilon,S)\le(1+1/10000)\varepsilon$ 的因果 $S$。

因果集合有限维且紧，事件误差连续，最小值达到，从而式（56.4）的下界严格成立。

最后，令

$$
T=R_\varepsilon
+\varepsilon|0,1,0\rangle\langle0,1,0|
+\varepsilon|1,0,0\rangle\langle1,0,0|.
$$

则 $T\succeq R_\varepsilon$ 且
$\operatorname{Tr}_D T=I_A\otimes\operatorname{diag}(1,\varepsilon)$。
$S=T/(1+\varepsilon)$ 是因果修复；由
$R_\varepsilon-S\preceq\varepsilon S$ 及
$S-R_\varepsilon\preceq(T-R_\varepsilon)/(1+\varepsilon)$，两个方向的事件误差分别不超过 $\varepsilon$ 与 $2\varepsilon/(1+\varepsilon)$，得式（56.4）的上界。$\square$

这个线性比例间隙排除了本族的 $\varepsilon+O(\varepsilon^2)$ 修复上界。这里的结论只针对指定等距族和全部量子 tester 的同一合同，不把常数 $1+1/10000$ 宣称为任何全局最优常数。

## 追加锚（本行以下为增补区）

## 57. 固定早期边缘的纯化极值与末端处理

### 57.1 固定合同

本节把标准的 Schmidt 纯化与末端数据处理工具用于完整量子 tester 下的因果修复比较；纯化存在性和末端数据处理在此承担已有工具的角色。

固定有限维非零端口 $A,B$，分别表示晚输入与早输出。令

$$
M\succeq0\quad\text{作用于 }A\otimes B,
\qquad\operatorname{Tr}_B M=I_A.
\tag{57.1}
$$

晚输出空间 $D$ 上的一个扩展是

$$
R\succeq0\quad\text{作用于 }A\otimes B\otimes D,
\qquad\operatorname{Tr}_D R=M.
\tag{57.2}
$$

因此 $\operatorname{Tr}_{BD}R=I_A$，它是一个全局静态通道的 Choi 算符。因果归一化修复集合为

$$
\mathcal S_D=
\{S\succeq0:\operatorname{Tr}_D S=I_A\otimes\sigma,
\ \sigma\succeq0,\operatorname{Tr}\sigma=1\}.
\tag{57.3}
$$

采用吸收全转置后的 tester 配对，所有反馈归一化算符是 $C\otimes I_D$，其中 $C\succeq0$、$\operatorname{Tr}_A C=I_B$。事件遍历全部 $0\preceq F\preceq C\otimes I_D$，包括任意量子参考、记忆与最终测量。记

$$
\begin{aligned}
D_D(R,S)&=\max_{C,F}|\operatorname{Tr}((R-S)F)|,\\
\mathfrak r_D(R)&=\min_{S\in\mathcal S_D}D_D(R,S),\\
\delta(M)&=\max_C|\operatorname{Tr}(MC)-1|.
\end{aligned}
\tag{57.4}
$$

因为 $\operatorname{Tr}(R(C\otimes I_D))=\operatorname{Tr}(MC)$，全部扩展具有相同的每个反馈总响应及相同的归一化缺陷 $\delta(M)$。所用集合有限维且紧，式（57.4）的极值达到。

### 57.2 任意扩展是纯化的末端通道像

令 $r=\operatorname{rank}M$，取 $E=\mathbb C^r$。对 $M$ 的正谱分解

$$
M=\sum_{j=1}^r\lambda_j|m_j\rangle\langle m_j|,
\qquad\lambda_j>0,
$$

定义未归一化的最小纯化

$$
|\Omega\rangle=\sum_{j=1}^r\sqrt{\lambda_j}|m_j\rangle_{AB}|j\rangle_E,
\qquad R^{\mathrm{pur}}=|\Omega\rangle\langle\Omega|.
\tag{57.5}
$$

其范数平方为 $\operatorname{Tr}M=\dim A$，与未归一化 Choi 约定一致。

**引理 57.1（扩展由末端 CPTP 通道产生）。** 对任意满足式（57.2）的 $R$，存在 CPTP 通道 $\Lambda:\mathcal L(E)\to\mathcal L(D)$，使

$$
R=(\operatorname{id}_{AB}\otimes\Lambda)(R^{\mathrm{pur}}).
\tag{57.6}
$$

**证明。** 在 $D$ 后添加一个有限维辅助空间 $F$，取 $R$ 的纯化 $|\Psi\rangle_{ABDF}$。因为 $|\Psi\rangle$ 对 $DF$ 的偏迹也是 $M$，可写

$$
|\Psi\rangle=\sum_{j=1}^r\sqrt{\lambda_j}|m_j\rangle|f_j\rangle,
\qquad\langle f_i|f_j\rangle=\delta_{ij}.
$$

具体可取 $|f_j\rangle=\lambda_j^{-1/2}(\langle m_j|\otimes I)|\Psi\rangle$，其正交性直接由偏迹等于 $M$ 得到。令等距 $W:E\to D\otimes F$ 满足 $W|j\rangle=|f_j\rangle$，并定义

$$
\Lambda(X)=\operatorname{Tr}_F(WXW^*).
$$

它完全正且保持迹，且 $(I_{AB}\otimes W)|\Omega\rangle=|\Psi\rangle$，所以式（57.6）成立。$\square$

### 57.3 末端通道收缩完整事件误差

**引理 57.2。** 任意 CPTP $\Lambda:E\to D$ 都将 $\mathcal S_E$ 映到 $\mathcal S_D$，且对所有厄米差和任意候选 $R_E,S_E$ 有

$$
D_D\bigl((\operatorname{id}_{AB}\otimes\Lambda)R_E,
(\operatorname{id}_{AB}\otimes\Lambda)S_E\bigr)
\le D_E(R_E,S_E).
\tag{57.7}
$$

**证明。** 完全正性保持正算符，而保持迹给

$$
\operatorname{Tr}_D[(\operatorname{id}_{AB}\otimes\Lambda)S_E]
=\operatorname{Tr}_E S_E.
$$

所以因果偏迹和归一化保持。

对任意末端事件 $0\preceq F_D\preceq C\otimes I_D$，定义

$$
F_E=(\operatorname{id}_{AB}\otimes\Lambda^*)(F_D).
$$

$\Lambda^*$ 完全正且保持单位算符，即 $\Lambda^*(I_D)=I_E$，故

$$
0\preceq F_E\preceq C\otimes I_E.
$$

迹配对给

$$
\operatorname{Tr}\!\left(
[(\operatorname{id}_{AB}\otimes\Lambda)(R_E-S_E)]F_D
\right)
=\operatorname{Tr}((R_E-S_E)F_E).
$$

对所有 $C,F_D$ 取最大得到式（57.7）。这一证明直接使用全部事件，不需要假设候选本身在所有反馈下归一化，也没有删除归一化迹项。$\square$

**定理 57.3（固定边缘的纯化上界达到）。** 对式（57.2）的每个有限维扩展，

$$
\mathfrak r_D(R)\le\mathfrak r_E(R^{\mathrm{pur}}).
\tag{57.8}
$$

因此，在允许任意有限晚输出空间时，固定早期边缘 $M$ 的最大最优修复误差由最小纯化达到；寻找最困难扩展可将晚输出维数限制为 $r=\operatorname{rank}M\le(\dim A)(\dim B)$。

**证明。** 取引理 57.1 的 $\Lambda$。每个 $S_E\in\mathcal S_E$ 的像都在 $\mathcal S_D$，所以

$$
\begin{aligned}
\mathfrak r_D(R)
&\le\inf_{S_E\in\mathcal S_E}
D_D\bigl((\operatorname{id}\otimes\Lambda)R^{\mathrm{pur}},
(\operatorname{id}\otimes\Lambda)S_E\bigr)\\
&\le\inf_{S_E\in\mathcal S_E}D_E(R^{\mathrm{pur}},S_E)
=\mathfrak r_E(R^{\mathrm{pur}}).
\end{aligned}
$$

$R^{\mathrm{pur}}$ 本身是一个允许的扩展，故上界达到。$\square$

比较方向是：对末输出做通道后处理，只会使最优修复问题更容易或同样困难。它没有声称每个最优修复都能从某个纯化最优修复获得。

### 57.4 固定末输出维数与同边缘的最容易扩展

**推论 57.4（末端等距不改最优值）。** 若 $J:E\to D$ 为等距，则

$$
\mathfrak r_D((I_{AB}\otimes J)R_E(I_{AB}\otimes J^*))
=\mathfrak r_E(R_E).
\tag{57.9}
$$

**证明。** 等距嵌入是 CPTP 通道，给一个方向。固定 $E$ 上的密度算符 $\omega$，定义恢复通道

$$
\Gamma(X)=J^*XJ+
\operatorname{Tr}((I_D-JJ^*)X)\,\omega.
$$

它完全正且保持迹，且 $\Gamma(JXJ^*)=X$。对它再次使用引理 57.2 及因果集合封闭，得到反向不等式。$\square$

因此，对固定 $D$，若 $\dim D\ge r$，式（57.8）的上界仍由嵌入 $D$ 的最小纯化达到。若 $\dim D<r$，此处只保留上界，不能声称 $D$ 内存在这个纯化。

同时，对任意非零 $D$ 和其密度算符 $\omega_D$，积扩展 $M\otimes\omega_D$ 满足

$$
\mathfrak r_D(M\otimes\omega_D)=\delta(M).
\tag{57.10}
$$

证明使用定理 54.2 的最小接口尖锐修复结论（交换固定的张量因子次序）：存在 $\sigma$ 使 $D_{\mathbb C}(M,I_A\otimes\sigma)=\delta(M)$。追加固定态 $\omega_D$ 是末端 CPTP 通道，故引理 57.2 给式（57.10）的上界；整个事件 $F=C\otimes I_D$ 给相同的下界。于是固定 $M$ 时，归一化缺陷是所有扩展的最小可能最优修复成本，而纯化给允许足够末输出维数时的最大成本。

### 57.5 与等距反例的对应

对早期边缘

$$
M_\varepsilon=|0,0\rangle\langle0,0|
+(1-\varepsilon)|1,0\rangle\langle1,0|
+\varepsilon|1,1\rangle\langle1,1|,
\qquad0<\varepsilon\le1/4,
$$

其秩为三。向量

$$
|0,0,0\rangle+\sqrt{1-\varepsilon}|1,0,1\rangle
+\sqrt\varepsilon|1,1,2\rangle
$$

就是式（57.5）的最小纯化。因此第 55 节的纯等距反例在固定 $M_\varepsilon$ 的全部有限末输出扩展中达到最大修复困难。末端基退相干保持同一 $M_\varepsilon$，且具有已证的最优修复误差 $\varepsilon$；这与式（57.8）的收缩方向一致。

这里的“最大”只在固定 $M$、固定早期/晚输入端口和同一完整 tester 合同下比较扩展，不外推为只固定数值 $\delta$ 的所有边缘之间的最大值。

## 追加锚（本行以下为增补区）

## 58. 两轮量子因果修复的显式上界与准确八分之九渐近比例

### 58.1 接口与显式修复

使用 $A\otimes B\otimes D$ 次序，$\dim A=\dim B=2$、$\dim D=3$，其中 $B$ 是早输出、$A$ 是晚输入、$D$ 是晚输出。因果归一化修复满足

$$
S\succeq0,\qquad \operatorname{Tr}_D S=I_A\otimes\sigma,
\qquad\sigma\succeq0,\quad\operatorname{Tr}\sigma=1.
$$

完整 tester 的归一化算符为 $C\otimes I_D$，其中 $C\succeq0$、$\operatorname{Tr}_A C=I_B$；事件遍历全部 $0\preceq E\preceq C\otimes I_D$，全转置已吸收到配对约定。对任意厄米 $X$ 定义

$$
h(X)=\max_{C,E}\operatorname{Tr}(XE),\qquad
N(X)=\max\{h(X),h(-X)\}.
\tag{58.1}
$$

因果修复的完整事件误差是 $D(R,S)=N(R-S)$。

记

$$
x=|0,0,0\rangle,\quad y=|1,0,1\rangle,
\quad z=|1,1,2\rangle,\quad h_0=|0,1,0\rangle,
\qquad c=\sqrt{1-\varepsilon},\quad s=\sqrt\varepsilon,
$$

并取 $0<\varepsilon\le1/4$。候选与修复定义为

$$
\begin{aligned}
R_\varepsilon&=|x+cy+sz\rangle\langle x+cy+sz|,\\
S_\varepsilon&=|cx+cy+sz\rangle\langle cx+cy+sz|
+\varepsilon|h_0\rangle\langle h_0|.
\end{aligned}
\tag{58.2}
$$

三个向量 $x,y,z$ 的 $D$ 坐标不同，故

$$
\operatorname{Tr}_D S_\varepsilon
=I_A\otimes\operatorname{diag}(1-\varepsilon,\varepsilon).
\tag{58.3}
$$

因此 $S_\varepsilon$ 是正且归一化的因果梳。候选 $R_\varepsilon$ 的归一化缺陷是 $\varepsilon$。

**定理 58.1。** 对式（58.2）的显式修复，准确误差为

$$
D(R_\varepsilon,S_\varepsilon)
=\varepsilon\left(1+\frac{c^2}{(1+c)(1+3c)}\right)
<\frac98\varepsilon,
\qquad 0<\varepsilon\le\frac14.
\tag{58.4}
$$

尤其

$$
\lim_{\varepsilon\downarrow0}
\frac{D(R_\varepsilon,S_\varepsilon)}{\varepsilon}=\frac98.
\tag{58.5}
$$

式（58.4）给最优修复的上界；式（58.5）先计算这一份显式修复的极限；第 58.6 节另用匹配下界证明真正最优误差具有相同极限。

### 58.2 联合相位平均与完整 tester

定义

$$
\begin{aligned}
U_A(\alpha)&=\operatorname{diag}(1,e^{i\alpha}),\\
U_B(\beta)&=\operatorname{diag}(1,e^{i\beta}),\\
U_D(\alpha,\beta)&=
\operatorname{diag}(1,e^{-i\alpha},e^{-i(\alpha+\beta)}),\\
U(\alpha,\beta)&=U_A(\alpha)\otimes U_B(\beta)\otimes U_D(\alpha,\beta).
\end{aligned}
\tag{58.6}
$$

$U$ 分别固定 $x,y,z$，将 $h_0$ 乘以 $e^{i\beta}$。因此 $R_\varepsilon,S_\varepsilon$ 及其厄米差均在该群下不变。

**引理 58.2（联合平均允许取对角归一化算符）。** 对任意在式（58.6）下不变的厄米 $X$，计算 $h(X)$ 和 $h(-X)$ 时可限制 $C$ 为 $AB$ 指定基上的对角算符，但事件 $E$ 仍遍历完整的正区间，不要求对角。

**证明。** 若 $E\preceq C\otimes I_D$，则

$$
UEU^*\preceq
[(U_A\otimes U_B)C(U_A\otimes U_B)^*]\otimes I_D.
$$

$C$ 的偏迹条件在此变换下保持，且 $X$ 不变给
$\operatorname{Tr}(XUEU^*)=\operatorname{Tr}(XE)$。
对 $(\alpha,\beta)\in\{0,\pi\}^2$ 的四个变换同时平均 $(E,C)$，得到可行对 $(\bar E,\bar C)$ 和相同响应。$AB$ 四个基向量在这个四元群上具有不同字符，所以 $\bar C$ 对角。这个联合平均保留事件的合法性；不能只把 $C$ 对角化而保留未经变换的 $E$。反过来，对角 $C$ 是原可行集的子集，故最优值相同。$\square$

同一平均也保持 CPTP 静态候选和因果修复集合：对因果 $S$，

$$
\operatorname{Tr}_D(USU^*)
=I_A\otimes U_B\sigma U_B^*.
$$

平均保持正性及归一化；由事件误差的凸性和 $R_\varepsilon$ 不变性，平均一个修复不会增加其误差。故这种对称化也可用于最优修复问题，并非只适用于当前显式构造。

每个对角反馈归一化算符可唯一写成

$$
C=\operatorname{diag}(q,1-r,1-q,r),
\qquad 0\le q,r\le1,
\tag{58.7}
$$

其中对角次序为 $00,01,10,11$。

### 58.3 准确差算符与谱

令

$$
k=\frac{c}{1+c},\qquad b=\frac{\sqrt\varepsilon}{1+c},
\qquad X_\varepsilon=\frac{S_\varepsilon-R_\varepsilon}{\varepsilon}.
$$

直接展开式（58.2），使用 $1-c=\varepsilon/(1+c)$，得到

$$
X_\varepsilon
=-|x\rangle\langle x|
-k(|x\rangle\langle y|+|y\rangle\langle x|)
-b(|x\rangle\langle z|+|z\rangle\langle x|)
+|h_0\rangle\langle h_0|.
\tag{58.8}
$$

对固定 $C$，完整正区间的支持函数是

$$
\max_{0\preceq E\preceq C\otimes I_D}\operatorname{Tr}(X_\varepsilon E)
=\operatorname{Tr}\left[
\sqrt{C\otimes I_D}X_\varepsilon\sqrt{C\otimes I_D}
\right]_+.
\tag{58.9}
$$

式（58.9）在奇异 $C$ 时亦成立：在其支撑上写 $E=\sqrt{C\otimes I_D}F\sqrt{C\otimes I_D}$，$0\preceq F\preceq I$，再选正谱投影。

对式（58.7），压缩算符在 $\operatorname{span}\{x,y,z\}$ 上的矩阵为

$$
\begin{pmatrix}
-q&-k\sqrt{q(1-q)}&-b\sqrt{qr}\\
-k\sqrt{q(1-q)}&0&0\\
-b\sqrt{qr}&0&0
\end{pmatrix}.
$$

其特征值是零与

$$
\lambda_\pm(q,r)=
\frac{-q\pm\sqrt{q^2+4k^2q(1-q)+4b^2qr}}2.
\tag{58.10}
$$

另外，$h_0$ 方向的特征值为 $1-r\ge0$。因此

$$
\begin{aligned}
h(X_\varepsilon)&=\max_{q,r}\bigl[1-r+\lambda_+(q,r)\bigr],\\
h(-X_\varepsilon)&=\max_{q,r}\bigl[-\lambda_-(q,r)\bigr].
\end{aligned}
\tag{58.11}
$$

### 58.4 两个方向的极值

**引理 58.3。** 对全部 $0<\varepsilon<1$，

$$
h(X_\varepsilon)=1+\frac{k^2}{1+2k},
\qquad
h(-X_\varepsilon)=\frac{1+\sqrt{1+4b^2}}2.
\tag{58.12}
$$

**证明。** 记
$A(q)=q^2+4k^2q(1-q)\ge q^2$。对 $q>0$，

$$
\lambda_+(q,r)-\lambda_+(q,0)
=\frac{2b^2qr}{\sqrt{A(q)+4b^2qr}+\sqrt{A(q)}}
\le b^2r.
$$

当 $q=0$ 时此增量为零。因为
$b^2=(1-c)/(1+c)<1$，式（58.11）的第一式在 $r=0$ 达到最大。

设

$$
a=\frac{k^2}{1+2k},\qquad q_* =\frac{k}{1+2k}.
$$

恒等式

$$
(q+2a)^2-[q^2+4k^2q(1-q)]
=4k^2(q-q_*)^2\ge0
$$

给 $\lambda_+(q,0)\le a$，且在 $q=q_*$ 达到等号，得第一式。

第二式随 $r$ 不减，故可取 $r=1$。此时根号内为

$$
(1-4k^2)q^2+4(k^2+b^2)q.
$$

由于 $0<k<1/2$，该式随 $q\in[0,1]$ 不减，所以 $-\lambda_-$ 在 $q=1$ 最大，给第二式。$\square$

当 $0<\varepsilon\le1/4$ 时，$c\ge\sqrt3/2>5/6$，故

$$
k>\frac5{11},\qquad b^2<\frac1{11}.
$$

函数 $k^2/(1+2k)$ 随 $k\ge0$ 递增，而
$\sqrt{1+4b^2}\le1+2b^2$。所以

$$
h(X_\varepsilon)>1+\frac{25}{231}
>1+\frac{21}{231}
>h(-X_\varepsilon).
$$

结合式（58.1）、（58.12），得到定理 58.1 的准确表达式，因为

$$
\frac{k^2}{1+2k}=\frac{c^2}{(1+c)(1+3c)}.
$$

最后，$0<c<1$ 给

$$
8c^2<(1+c)(1+3c)
\iff(5c+1)(c-1)<0,
$$

故式（58.4）的 $9/8$ 上界严格成立；令 $\varepsilon\downarrow0$、$c\to1$ 即得式（58.5）。$\square$

### 58.5 显式构造的一阶极限

式（58.8）给

$$
X_\varepsilon\longrightarrow
H=-|x\rangle\langle x|
-\frac12(|x\rangle\langle y|+|y\rangle\langle x|)
+|h_0\rangle\langle h_0|.
$$

同一完整 tester 计算给 $h(H)=9/8$、$h(-H)=1$。有限 $\varepsilon$ 的准确计算比只使用该极限更强：没有必要为式（58.4）添加 $O(\varepsilon^{3/2})$ 余项。

与第 56 节的统一线性下界结合，当前先得到

$$
\left(1+\frac1{10000}\right)\varepsilon
<\min_{S\text{ 因果}}D(R_\varepsilon,S)
\le\varepsilon\left(1+\frac{c^2}{(1+c)(1+3c)}\right)
<\frac98\varepsilon.
\tag{58.13}
$$

因此，单用上述构造只能推出最优比例的上极限至多 $9/8$。下面给匹配的一阶下界。


### 58.6 对全部因果修复的匹配渐近下界

记

$$
e_\varepsilon=\min_{S\text{ 因果}}D(R_\varepsilon,S).
\tag{58.14}
$$

因果集合有限维、闭且具有固定迹二，因此紧；完整 tester 事件集也紧，所以事件误差连续，最小值达到。

**定理 58.4（最优修复的准确渐近比例）。** 对 $0<\varepsilon\le1/4$，

$$
\frac98\varepsilon-\frac{27}{16}\varepsilon^{3/2}
\le e_\varepsilon
\le\varepsilon\left(1+\frac{c^2}{(1+c)(1+3c)}\right)
<\frac98\varepsilon.
\tag{58.15}
$$

特别地，

$$
\lim_{\varepsilon\downarrow0}\frac{e_\varepsilon}{\varepsilon}
=\frac98,
\qquad
\lim_{\varepsilon\downarrow0}\frac{e_\varepsilon-\varepsilon}{\varepsilon}
=\frac18.
\tag{58.16}
$$

**证明。** 取达到 $e_\varepsilon$ 的因果修复 $S$，并写

$$
p=\sigma_{11},\qquad S_{uv}=\langle u|S|v\rangle.
$$

先用两个事件测量 $x,z$ 间的实矩阵元。令

$$
C_+=|0,0\rangle\langle0,0|+|1,1\rangle\langle1,1|.
$$

它满足 $\operatorname{Tr}_A C_+=I_B$，而

$$
E_\pm=\left|\frac{x\pm z}{\sqrt2}\right\rangle
\left\langle\frac{x\pm z}{\sqrt2}\right|
\preceq C_+\otimes I_D
$$

是合法事件。令 $J=S-R_\varepsilon$，两个事件各满足
$|\operatorname{Tr}(JE_\pm)|\le e_\varepsilon$，相减的配对为 $2\operatorname{Re}J_{xz}$，故

$$
|\operatorname{Re}J_{xz}|\le e_\varepsilon,
\qquad
\operatorname{Re}S_{xz}\ge\sqrt\varepsilon-e_\varepsilon.
\tag{58.17}
$$

因果偏迹给 $S_{xx}\le1$、$S_{zz}\le p$。$S\succeq0$ 的 $xz$ 主子式因此给

$$
p\ge S_{zz}\ge |S_{xz}|^2
\ge (\sqrt\varepsilon-e_\varepsilon)_+^2.
\tag{58.18}
$$

这里若式（58.17）的右端为负，最后一项按正部取零，未对负下界直接平方。定理 58.1 给 $e_\varepsilon\le9\varepsilon/8$；在 $\varepsilon\le1/4$ 时，
$\sqrt\varepsilon-9\varepsilon/8>0$，于是

$$
p\ge\left(\sqrt\varepsilon-\frac98\varepsilon\right)^2
=\varepsilon-\frac94\varepsilon^{3/2}
+\frac{81}{64}\varepsilon^2.
\tag{58.19}
$$

再固定一个同时读取全部相关块的事件。记
$B_{ab}=|a,b\rangle\langle a,b|\otimes I_D$，取

$$
\begin{aligned}
C_*&=\operatorname{diag}(1/4,1,3/4,0),\\
w&=\frac14x-\frac34y,\\
E_*&=|w\rangle\langle w|
+\frac14(B_{00}-|x\rangle\langle x|)
+\frac34(B_{10}-|y\rangle\langle y|)
+B_{01}.
\end{aligned}
\tag{58.20}
$$

$C_*$ 满足 $\operatorname{Tr}_A C_*=I_B$。在 $xy$ 子空间，$w$ 是
$\operatorname{diag}(1/2,\sqrt3/2)$ 作用于单位向量
$(1/2,-\sqrt3/2)$ 所得，所以

$$
|w\rangle\langle w|
\preceq\frac14|x\rangle\langle x|
+\frac34|y\rangle\langle y|.
$$

其他项支撑正交，故 $0\preceq E_*\preceq C_*\otimes I_D$。这个事件把 $00$、$10$ 块中 $x,y$ 以外的质量也计入，未把修复限制在 $\operatorname{span}\{x,y,z,h_0\}$。

利用因果偏迹，$B_{00}$ 和 $B_{10}$ 的响应都为 $1-p$，$B_{01}$ 的响应为 $p$。因此准确计算得到

$$
\begin{aligned}
\operatorname{Tr}(SE_*)
&=1-\frac3{16}(S_{xx}+S_{yy})-\frac38\operatorname{Re}S_{xy},\\
\operatorname{Tr}(R_\varepsilon E_*)
&=\frac1{16}+\frac9{16}(1-\varepsilon)-\frac38c.
\end{aligned}
$$

相减即

$$
\operatorname{Tr}((S-R_\varepsilon)E_*)
=\frac3{16}\bigl[2+3\varepsilon+2c
-S_{xx}-S_{yy}-2\operatorname{Re}S_{xy}\bigr].
\tag{58.21}
$$

正性与因果偏迹给

$$
\operatorname{Re}S_{xy}\le\sqrt{S_{xx}S_{yy}}
\le\frac{S_{xx}+S_{yy}}2,
\qquad S_{xx},S_{yy}\le1-p.
$$

将其代入式（58.21），得到对任意因果修复均成立的事件下界

$$
\begin{aligned}
D(R_\varepsilon,S)
&\ge\operatorname{Tr}((S-R_\varepsilon)E_*)\\
&\ge\frac34p+\frac9{16}\varepsilon+\frac38(c-1)\\
&=\frac34p+\frac38\varepsilon
-\frac{3\varepsilon^2}{16(1+c)^2}.
\end{aligned}
\tag{58.22}
$$

最后一个等号使用
$c-1=-\varepsilon/2-\varepsilon^2/[2(1+c)^2]$。代入式（58.19），有

$$
e_\varepsilon
\ge\frac98\varepsilon-\frac{27}{16}\varepsilon^{3/2}
+\left(\frac{243}{256}-\frac{3}{16(1+c)^2}\right)\varepsilon^2.
$$

括号为正，丢掉最后一项便得式（58.15）的下界。式（58.15）的上界来自定理 58.1，两边除以 $\varepsilon$ 并令 $\varepsilon\downarrow0$，得到式（58.16）。$\square$

### 58.7 结论范围

式（58.16）给整个完整量子 tester 合同下、对所有因果修复取最小后的渐近比例。上界使用一个显式合法修复；下界同时使用合法矩阵元事件和固定事件 $E_*$，且不限制未知修复的支撑或对称形态。

这证明完整末输出相干造成的一阶额外成本在本族中恰为 $\varepsilon/8+o(\varepsilon)$。它没有给有限 $\varepsilon$ 的精确最优值，也没有证明其他边缘或其他两轮候选的统一最优常数为 $9/8$。

## 追加锚（本行以下为增补区）

## 59. 完整两轮因果修复的单参数精确约化

### 59.1 接口与准确优化结论

沿用第 58 节的端口次序 $A\otimes B\otimes D$，维数为 $2\times2\times3$，其中 $A$ 为晚输入、$B$ 为早输出、$D$ 为晚输出。记

$$
x=|0,0,0\rangle,\quad y=|1,0,1\rangle,
\quad z=|1,1,2\rangle,\quad h_0=|0,1,0\rangle,
$$

并在本节固定

$$
0<\varepsilon\le\frac1{16},\qquad
c=\sqrt{1-\varepsilon},\qquad s=\sqrt\varepsilon,
\qquad r_0=(1,c,s)^{\mathsf T},
\qquad R_\varepsilon=|x+cy+sz\rangle\langle x+cy+sz|.
\tag{59.1}
$$

全部归一化因果修复满足

$$
S\succeq0,\qquad\operatorname{Tr}_D S=I_A\otimes\sigma,
\qquad\sigma\succeq0,\quad\operatorname{Tr}\sigma=1.
\tag{59.2}
$$

在吸收全转置后的配对约定下，完整 tester 归一化算符和事件遍历

$$
C\succeq0,\qquad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D.
\tag{59.3}
$$

这些量词包含全部有限量子参考、记忆和最终测量。对厄米 $X$ 记

$$
h(X)=\max_{C,E}\operatorname{Tr}(XE),
\qquad N(X)=\max\{h(X),h(-X)\},
\qquad e_\varepsilon=\min_{S\text{ 满足式（59.2）}}N(R_\varepsilon-S).
\tag{59.4}
$$

**定理 59.1（单参数精确约化）。** 对 $p\in[1-c,\varepsilon]$，定义

$$
\begin{aligned}
v_p&=\sqrt{1-p}\,x+\sqrt{1-p}\,y+\sqrt p\,z,\\
S_p&=|v_p\rangle\langle v_p|+p|h_0\rangle\langle h_0|.
\end{aligned}
\tag{59.5}
$$

则 $S_p$ 是归一化因果梳，而且

$$
e_\varepsilon=\min_{1-c\le p\le\varepsilon}N(R_\varepsilon-S_p).
\tag{59.6}
$$

进一步，对 $q,t\in[0,1]$ 定义

$$
\begin{aligned}
U&=q+c^2(1-q)+\varepsilon t,\\
V&=1-p+pt,\\
W&=\sqrt{1-p}\,[q+c(1-q)]+\sqrt{\varepsilon p}\,t,\\
\Lambda(p,q,t)
&=\frac{U-V+\sqrt{(U+V)^2-4W^2}}2.
\end{aligned}
\tag{59.7}
$$

则有完全标量的准确表达式

$$
e_\varepsilon
=\min_{1-c\le p\le\varepsilon}
\max_{0\le q,t\le1}
\left[\Lambda(p,q,t)+\varepsilon(1-q-t)_+\right],
\tag{59.8}
$$

其中 $a_+=\max\{a,0\}$。该结论从全体因果修复推出，不预先假设未知修复只有式（59.5）的支撑或秩。

### 59.2 合法对称化与完整事件公式

使用连续联合相位群

$$
\begin{aligned}
U_A(\alpha)&=\operatorname{diag}(1,e^{i\alpha}),\\
U_B(\beta)&=\operatorname{diag}(1,e^{i\beta}),\\
U_D(\alpha,\beta)&=
\operatorname{diag}(1,e^{-i\alpha},e^{-i(\alpha+\beta)}),\\
U(\alpha,\beta)&=U_A(\alpha)\otimes U_B(\beta)\otimes U_D(\alpha,\beta).
\end{aligned}
\tag{59.9}
$$

该群固定 $R_\varepsilon$，并同时保持因果集合与完整 tester 集合。$N$ 是凸函数，所以对 $\alpha,\beta$ 平均一个最优修复不会增加误差。

在十二个标准基向量中，恰好 $x,y,z$ 具有零相位字符。记 $\Pi$ 为它们张成空间的投影。平均后的修复满足

$$
S=P\oplus S_\perp,
\qquad P=\Pi S\Pi\succeq0,
\qquad S_\perp\succeq0.
\tag{59.10}
$$

早输出边缘也被相位平均为 $\sigma=\operatorname{diag}(1-p,p)$，其中 $0\le p\le1$，故

$$
P_{xx},P_{yy}\le1-p,
\qquad P_{zz}\le p.
\tag{59.11}
$$

复共轭保持 $R_\varepsilon$、因果集合及 tester 集合，因此再取 $(S+\overline S)/2$ 仍不增加误差。主块解耦性质保持，可设 $P$ 实对称。

对这样的 $S$，$R_\varepsilon-S$ 仍在联合相位群下不变。按第 58 节的联合平均论证，计算 $h$ 时可取

$$
C(q,t)=\operatorname{diag}(q,1-t,1-q,t),
\qquad0\le q,t\le1,
\tag{59.12}
$$

其对角次序为 $00,01,10,11$；事件仍遍历整个正区间。令

$$
D(q,t)=\operatorname{diag}(\sqrt q,\sqrt{1-q},\sqrt t),
\qquad
B(P;q,t)=D(q,t)(r_0r_0^{\mathsf T}-P)D(q,t),
$$

并定义

$$
\lambda(P;q,t)=\max\{0,\lambda_{\max}(B(P;q,t))\}.
\tag{59.13}
$$

由于 $P\succeq0$，$B$ 至多有一个严格正特征值。$C\otimes I_D$ 与 $\Pi$ 交换，而 $R_\varepsilon-S$ 在 $\Pi$ 外的压缩非正。因此固定 $C$ 时，$R_\varepsilon-S$ 的加权正谱和就是 $\lambda$。

反向使用 $\operatorname{Tr}X_+=\operatorname{Tr}X+\operatorname{Tr}(-X)_+$，以及因果归一化
$\operatorname{Tr}(S(C\otimes I_D))=1$，得到固定 $C$ 时 $S-R_\varepsilon$ 的加权正谱和为

$$
\lambda+1-\operatorname{Tr}(R_\varepsilon(C\otimes I_D))
=\lambda+\varepsilon(1-q-t).
$$

所以完整双向事件误差恰为

$$
N(R_\varepsilon-S)
=\max_{0\le q,t\le1}
\left[\lambda(P;q,t)+\varepsilon(1-q-t)_+\right].
\tag{59.14}
$$

补块 $S_\perp$ 的细节通过归一化迹项进入此式；其正质量没有被丢弃。

### 59.3 最优修复的边缘参数区间

因果集合闭且迹固定为二，完整事件集合也紧，因此最优修复存在。

先看下端。第 58 节的合法 $xz$ 事件与正性给

$$
p\ge(\sqrt\varepsilon-e_\varepsilon)_+^2.
$$

显式修复 $S_\varepsilon$ 给 $e_\varepsilon<9\varepsilon/8$。由于 $\varepsilon\le1/16$，括号为正，并有

$$
p\ge\varepsilon\left(1-\frac98\sqrt\varepsilon\right)^2
\ge\frac{529}{1024}\varepsilon.
$$

另一方面，$c\ge\sqrt{15}/4>15/16$，所以

$$
1-c=\frac\varepsilon{1+c}
<\frac{16}{31}\varepsilon
<\frac{529}{1024}\varepsilon.
\tag{59.15}
$$

最后一个比较是 $16\cdot1024=16384<16399=529\cdot31$。故最优修复的 $p>1-c$。

再看上端。令

$$
d_\varepsilon=N(R_\varepsilon-S_\varepsilon),
\qquad k=\frac c{1+c},
\qquad q_* =\frac{k}{1+2k}=\frac c{1+3c},
\qquad C_*=C(q_*,0).
$$

第 58 节证明 $d_\varepsilon=h(S_\varepsilon-R_\varepsilon)$，且最大值在 $C_*$ 达到。在 $xy$ 主块，加权算符
$(C_*\otimes I_D)^{1/2}(S_\varepsilon-R_\varepsilon)(C_*\otimes I_D)^{1/2}/\varepsilon$
是

$$
\begin{pmatrix}
-q_*&-k\sqrt{q_*(1-q_*)}\\
-k\sqrt{q_*(1-q_*)}&0
\end{pmatrix}.
$$

它的单位负特征向量 $n=(n_x,n_y)$ 可取两个分量严格为正：取矩阵的相反数后，非对角严格为正，最大特征向量可取严格正。令

$$
\ell=\sqrt{q_*}\,n_x\,x+\sqrt{1-q_*}\,n_y\,y,
\qquad L=|\ell\rangle\langle\ell|,
\qquad g=(\ell_x+\ell_y)^2>0.
\tag{59.16}
$$

$n$ 单位给 $L\preceq C_*\otimes I_D$，故

$$
E_*=C_*\otimes I_D-L
$$

合法。它去掉加权差算符唯一的负特征方向，因此

$$
\operatorname{Tr}((S_\varepsilon-R_\varepsilon)E_*)=d_\varepsilon.
$$

对任意因果 $S$，正性与对角预算给

$$
\operatorname{Tr}(SL)
\le(1-p)(\ell_x+\ell_y)^2=(1-p)g.
$$

这个不等式在未经平均的 $S$ 上也成立，因为
$\operatorname{Re}S_{xy}\le\sqrt{S_{xx}S_{yy}}\le1-p$。$S_\varepsilon$ 在该界达到等号，故

$$
\begin{aligned}
\operatorname{Tr}((S-R_\varepsilon)E_*)
&=1-\operatorname{Tr}(R_\varepsilon E_*)-\operatorname{Tr}(SL)\\
&\ge d_\varepsilon+g(p-\varepsilon).
\end{aligned}
\tag{59.17}
$$

若最优修复有 $p>\varepsilon$，其误差便严格大于 $d_\varepsilon$，与显式修复 $S_\varepsilon$ 矛盾。因此每个最优修复满足 $p\le\varepsilon$。这些参数界针对最优解，不施加于任意非最优修复。

### 59.4 逐元素比较保留全部事件误差

对已平均的最优修复及其 $p\in[1-c,\varepsilon]$，令

$$
\widehat v_p=(\sqrt{1-p},\sqrt{1-p},\sqrt p)^{\mathsf T},
\qquad P_p=\widehat v_p\widehat v_p^{\mathsf T}.
$$

式（59.11）与 $P\succeq0$ 逐项给

$$
P_{ii}\le(P_p)_{ii},
\qquad P_{ij}\le\sqrt{P_{ii}P_{jj}}\le(P_p)_{ij}.
\tag{59.18}
$$

所以 $r_0r_0^{\mathsf T}-P$ 的每个实矩阵元都不小于
$r_0r_0^{\mathsf T}-P_p$。后者的三个非对角元分别为

$$
c-(1-p),\qquad
\sqrt\varepsilon-\sqrt{p(1-p)},\qquad
c\sqrt\varepsilon-\sqrt{p(1-p)}.
\tag{59.19}
$$

第一项由 $p\ge1-c$ 非负；第二项由 $p\le\varepsilon$ 非负；第三项使用
$p\le\varepsilon<1/2$ 及 $u(1-u)$ 在 $[0,1/2]$ 上递增，也非负。

因此对每个非负对角矩阵 $D(q,t)$，
$D(q,t)(r_0r_0^{\mathsf T}-P_p)D(q,t)$ 是实对称且非对角非负的矩阵。给两个比较矩阵加同一个充分大的标量单位阵，得到逐项有序的非负对称矩阵；Perron 最大特征值的单调性给

$$
\lambda(P;q,t)\ge\lambda(P_p;q,t).
\tag{59.20}
$$

也可取右侧矩阵的非负单位最大特征向量，代入左侧的 Rayleigh 商直接证明式（59.20）。这里使用的是逐元素比较和非负特征向量，不将逐元素序等同于 Loewner 序。

$x,y,z$ 的末输出坐标互异，所以式（59.5）的 $S_p$ 有偏迹
$I_A\otimes\operatorname{diag}(1-p,p)$，是合法因果修复；其主块恰为 $P_p$。式（59.14）、（59.20）于是同时控制两个事件方向，给

$$
N(R_\varepsilon-S_p)\le N(R_\varepsilon-S).
$$

故全体因果修复的最优值在这一族中达到。反向比较由该族包含于全部因果修复集合得到，证明式（59.6）。

### 59.5 标量根式与适用边界

对 $P_p$，加权主块为

$$
B=(D r_0)(D r_0)^{\mathsf T}
-(D\widehat v_p)(D\widehat v_p)^{\mathsf T}.
$$

两向量的平方范数是式（59.7）的 $U,V$，内积为 $W$，故 $W^2\le UV$。$B$ 的两个可能非零特征值之和为 $U-V$、之积为 $W^2-UV$，所以其正部最大特征值就是

$$
\Lambda(p,q,t)
=\frac{U-V+\sqrt{(U+V)^2-4W^2}}2\ge0.
$$

共线或零向量的退化情形也由该式给出 $\max\{U-V,0\}$。代入式（59.14）得到式（59.8），定理 59.1 证毕。

这将当前族的完整矩阵修复精确降为一个外层修复参数和两个 tester 归一化参数。结论限定于式（59.1）的族与 $0<\varepsilon\le1/16$；不主张其他候选具有相同的秩一主块约化，也尚未求出式（59.8）在有限 $\varepsilon$ 下的闭式最优值。

## 追加锚（本行以下为增补区）

## 60. 两条相干保留时的量子比特末输出修复证书

### 60.1 同边缘的 CPTP 压缩族

取端口序 $A\otimes B\otimes D$，三者均为二维，$B$ 是早输出，$A$ 是晚输入，$D$ 是晚输出。在指定基上记

$$
x=|0,0,0\rangle,\quad y=|1,0,1\rangle,
\quad z=|1,1,1\rangle,
\quad h_0=|0,1,0\rangle,\quad h_1=|0,1,1\rangle,
\quad v=|1,0,0\rangle.
$$

对 $0<a<1$、$0<\varepsilon<1$，令

$$
R_{a,\varepsilon}
=|\sqrt a\,x+\sqrt{1-\varepsilon}\,y\rangle
 \langle\sqrt a\,x+\sqrt{1-\varepsilon}\,y|
+|\sqrt{1-a}\,x+\sqrt\varepsilon\,z\rangle
 \langle\sqrt{1-a}\,x+\sqrt\varepsilon\,z|.
\tag{60.1}
$$

这是一个正、秩二的全局通道 Choi 算符。其早期边缘为

$$
\operatorname{Tr}_D R_{a,\varepsilon}
=|0,0\rangle\langle0,0|
+(1-\varepsilon)|1,0\rangle\langle1,0|
+\varepsilon|1,1\rangle\langle1,1|.
\tag{60.2}
$$

式（60.1）可以由第 55 节三维末输出的纯等距反例作 CPTP 末端处理得到：对输入末端基 $0,1,2$ 使用

$$
K_0=\sqrt a\,|0\rangle\langle0|+|1\rangle\langle1|,
\qquad
K_1=\sqrt{1-a}\,|0\rangle\langle0|+|1\rangle\langle2|.
\tag{60.3}
$$

$K_0^*K_0+K_1^*K_1=I_3$；两条原先的 $xy$、$xz$ 相干都保留但衰减，而 $yz$ 相干被丢弃。

因果修复与完整 tester 的合同为

$$
\begin{gathered}
S\succeq0,\quad\operatorname{Tr}_D S=I_A\otimes\sigma,
\quad\operatorname{Tr}\sigma=1,\\
C\succeq0,\quad\operatorname{Tr}_A C=I_B,
\quad0\preceq E\preceq C\otimes I_D,\\
D(R,S)=\max_{C,E}|\operatorname{Tr}((R-S)E)|.
\end{gathered}
\tag{60.4}
$$

全转置已吸收到 $C$ 的配对约定，事件量词包含全部量子参考与记忆。式（60.2）给所有反馈总响应的范围 $[1-\varepsilon,1+\varepsilon]$，故归一化缺陷为 $\varepsilon$。可用 $AB$ 的对角投影 $C_+=|00\rangle\langle00|+|11\rangle\langle11|$、$C_-=|01\rangle\langle01|+|10\rangle\langle10|$ 达到两端。

### 60.2 指定点的准确修复

**定理 60.1。** 在 $a=1/2$、$\varepsilon=1/4$ 时，

$$
\min_{S\text{ 因果}}D(R_{1/2,1/4},S)=\frac14.
\tag{60.5}
$$

特别地，保留两条非零相干本身不充分保证严格超过归一化缺陷的修复成本。

**证明。** 定义正候选 $S$ 的对角元素为

$$
\begin{array}{c|rrrrrr}
\text{向量}&x&y&z&h_0&h_1&v\\\hline
\text{对角值}&17/20&4/5&3/20&3/40&3/40&1/20
\end{array}
$$

另外两个基向量 $|0,0,1\rangle,|1,1,0\rangle$ 的对角值为零。仅有的非零非对角元素为

$$
S_{xy}=S_{yx}=\frac35,
\qquad S_{xz}=S_{zx}=\frac6{25}.
\tag{60.6}
$$

在 $x,y,z$ 的星形块上，Schur 补为

$$
\frac{17}{20}-\frac{(3/5)^2}{4/5}
-\frac{(6/25)^2}{3/20}=\frac2{125}>0.
\tag{60.7}
$$

其余非零对角值为正，故 $S\succeq0$。直接偏迹给

$$
\operatorname{Tr}_D S
=I_A\otimes\operatorname{diag}(17/20,3/20),
\tag{60.8}
$$

所以 $S$ 因果且归一化。

记

$$
\alpha=\frac{\sqrt6}{4}-\frac35,
\qquad
\beta=\frac{\sqrt2}{4}-\frac6{25}.
$$

平方比较给简单有理界

$$
0<\alpha<\frac1{80},\qquad0<\beta<\frac3{25}.
\tag{60.9}
$$

令 $Q_-=C_-\otimes I_D$，并定义正向上界

$$
P=R_{1/2,1/4}-S+\frac18Q_-.
\tag{60.10}
$$

它的非零对角值为

$$
P_{xx}=\frac3{20},\quad
P_{yy}=P_{vv}=\frac3{40},\quad
P_{zz}=\frac1{10},\quad
P_{h_0h_0}=P_{h_1h_1}=\frac1{20},
$$

非零非对角元素为 $P_{xy}=\alpha$、$P_{xz}=\beta$ 及其共轭。其星形块的 Schur 补由式（60.9）满足

$$
\frac3{20}-\frac{\alpha^2}{3/40}-\frac{\beta^2}{1/10}
>\frac3{20}-\frac1{480}-\frac{18}{125}
=\frac{47}{12000}>0.
\tag{60.11}
$$

因此 $P\succeq0$，式（60.10）又直接给 $P\succeq R-S$，且

$$
\operatorname{Tr}_D P
=I_A\otimes\operatorname{diag}(3/20,1/10).
\tag{60.12}
$$

这是质量 $1/4$ 的正因果上界。

负向上界 $N$ 在标准二进制基次序
$000,001,010,011,100,101,110,111$ 上的对角为

$$
\operatorname{diag}N=
(1/20,1/20,3/40,3/40,1/20,1/20,3/40,3/40),
$$

仅有的非零非对角元素为 $N_{xy}=N_{yx}=-\alpha$。由于 $\alpha<1/80<1/20$，$N\succeq0$，并有

$$
\operatorname{Tr}_D N
=I_A\otimes\operatorname{diag}(1/10,3/20).
\tag{60.13}
$$

$Y=N-S+R$ 支撑在 $Q_+=C_+\otimes I_D$ 上。其 $xz$ 块为

$$
\begin{pmatrix}1/5&\beta\\\beta&7/40\end{pmatrix},
$$

另外在 $|0,0,1\rangle$、$|1,1,0\rangle$ 上分别有正对角 $1/20,3/40$。由式（60.9），

$$
\frac15\frac7{40}-\beta^2
>\frac7{200}-\frac9{625}>0,
$$

故 $Y\succeq0$，即 $N\succeq S-R$。

对每个合法事件，正性和因果偏迹给

$$
\begin{aligned}
\operatorname{Tr}((R-S)E)
&\le\operatorname{Tr}(PE)
\le\operatorname{Tr}(P(C\otimes I_D))=\frac14,\\
\operatorname{Tr}((S-R)E)
&\le\operatorname{Tr}(NE)
\le\operatorname{Tr}(N(C\otimes I_D))=\frac14.
\end{aligned}
$$

因此 $D(R,S)\le1/4$。整个事件的归一化缺陷给反向下界 $D(R,S)\ge1/4$，从而式（60.5）成立。$\square$

### 60.3 同一证书对参数邻域的充分条件

上述构造还能给同族内可直接检验的参数区域，不将单点结论外推为整个族。保持定理 60.1 的 $S$ 不变，并令

$$
\alpha(a,\varepsilon)=\sqrt{a(1-\varepsilon)}-\frac35,
\qquad
\beta(a,\varepsilon)=\sqrt{(1-a)\varepsilon}-\frac6{25}.
$$

**命题 60.2（同一证书的参数区域）。** 若 $1/5<\varepsilon<2/5$ 且以下三个不等式成立：

$$
\begin{aligned}
\frac3{20}
&\ge\frac{\alpha(a,\varepsilon)^2}{1/5-\varepsilon/2}
+\frac{\beta(a,\varepsilon)^2}{\varepsilon-3/20},\\
\frac{\varepsilon-3/20}{2}(\varepsilon-1/5)
&\ge\alpha(a,\varepsilon)^2,\\
\frac{\varepsilon+3/20}{2}(\varepsilon-3/40)
&\ge\beta(a,\varepsilon)^2,
\end{aligned}
\tag{60.14}
$$

则同样有

$$
\min_{S'\text{ 因果}}D(R_{a,\varepsilon},S')
=D(R_{a,\varepsilon},S)=\varepsilon.
\tag{60.15}
$$

**证明。** 取

$$
P=R_{a,\varepsilon}-S+\frac\varepsilon2Q_-.
$$

其偏迹是 $I_A\otimes\operatorname{diag}(3/20,\varepsilon-3/20)$。星形块的对角为 $3/20,1/5-\varepsilon/2,\varepsilon-3/20$，交叉项为 $\alpha,\beta$；第一项条件给其正性。其余非零对角为
$P_{vv}=\varepsilon/2-1/20$、$P_{h_ih_i}=\varepsilon/2-3/40$，在给定区间均正。

负向 $N$ 的对角依次取

$$
\left(
\frac{\varepsilon-3/20}{2},
\frac{\varepsilon-3/20}{2},
\frac3{40},\frac3{40},
\frac1{20},\varepsilon-\frac15,
\frac3{40},\frac3{40}
\right),
$$

仅令 $N_{xy}=N_{yx}=-\alpha$。其偏迹是
$I_A\otimes\operatorname{diag}(\varepsilon-3/20,3/20)$；第二项条件给 $N\succeq0$。余量 $N-S+R$ 的 $xz$ 块对角为
$(\varepsilon+3/20)/2,\varepsilon-3/40$，交叉项为 $\beta$；第三项条件给该块正性。其余非零余量对角为
$(\varepsilon-3/20)/2,3/40$，所以 $N\succeq S-R$。两个方向的上界质量均为 $\varepsilon$，同上得式（60.15）。$\square$

在 $(a,\varepsilon)=(1/2,1/4)$，式（60.14）均严格成立，故由连续性它们至少覆盖该点的一个非空开邻域。这是一个带显式充分条件的参数族结算，不是对所有量子比特末输出、所有秩二扩展或所有 $(a,\varepsilon)$ 的定理。

### 60.4 机制范围

第 55 节三维纯化反例的严格正性约束来自同一秩一扩展；式（60.3）的 CPTP 压缩把它变成秩二扩展。即使 $xy,xz$ 两条矩阵元均非零，因果修复仍能在其他同端口块配置正质量，并分别选择两个质量为 $\varepsilon$ 的正因果上界。这里给出的 $P,N$ 并不要求来自一个共同的正下包络。

因此，“两条相干保留”不是纯反例证明的充分迁移条件；扩展的共同秩、支撑及两个事件方向的正性余量必须一并核对。这个证书没有解决所有末输出为量子比特的候选是否都满足同系数修复。

## 追加锚（本行以下为增补区）

## 61. 两轮因果修复的 $\varepsilon^{3/2}$ 阶渐近与最优边缘参数

### 61.1 合同与结论

沿用 $A\otimes B\otimes D$ 的 $2\times2\times3$ 接口、完整量子 tester 事件和候选

$$
R_\varepsilon=|x+\sqrt{1-\varepsilon}\,y+\sqrt\varepsilon\,z\rangle
\langle x+\sqrt{1-\varepsilon}\,y+\sqrt\varepsilon\,z|,
\qquad x=000,\ y=101,\ z=112,
$$

记全部归一化因果修复中的最优事件误差为 $e_\varepsilon$。采用定理 59.1 的单参数约化：对 $0<\varepsilon\le1/16$，

$$
e_\varepsilon=\min_{1-c\le p\le\varepsilon}N(R_\varepsilon-S_p),
\quad c=\sqrt{1-\varepsilon},
$$

其中

$$
S_p=|\sqrt{1-p}\,x+\sqrt{1-p}\,y+\sqrt p\,z\rangle
\langle\sqrt{1-p}\,x+\sqrt{1-p}\,y+\sqrt p\,z|
+p|010\rangle\langle010|.
\tag{61.1}
$$

$N$ 是完整双向事件误差，不删归一化迹项。

**定理 61.1。** 当 $\varepsilon\downarrow0$，

$$
e_\varepsilon
=\frac98\varepsilon-\frac9{16}\varepsilon^{3/2}
+o(\varepsilon^{3/2}).
\tag{61.2}
$$

对任意最优参数的选择 $p_\varepsilon$，都有

$$
p_\varepsilon
=\varepsilon-\frac34\varepsilon^{3/2}
+o(\varepsilon^{3/2}).
\tag{61.3}
$$

式（61.3）还适用于任意原始最优因果修复的边缘参数 $p=\sigma_{11}$，因为单参数约化在保持该 $p$ 时不会增加误差。

证明使用单参数约化、特征值公式和一致的有限维极值分析。

### 61.2 正向事件最大值的准确公式

令 $P_p$ 为式（61.1）在 $x,y,z$ 上的秩一主块，$r=(1,c,\sqrt\varepsilon)^{\mathsf T}$。对反馈参数 $q,t\in[0,1]$，记

$$
D(q,t)=\operatorname{diag}(\sqrt q,\sqrt{1-q},\sqrt t),
\quad
\lambda_\varepsilon(p;q,t)
=\max\{0,\lambda_{\max}(D(rr^{\mathsf T}-P_p)D)\}.
$$

精确的两单向函数为

$$
\begin{aligned}
f_\varepsilon^+(p)&=\max_{q,t}\lambda_\varepsilon(p;q,t),\\
f_\varepsilon^-(p)&=\max_{q,t}
[\lambda_\varepsilon(p;q,t)+\varepsilon(1-q-t)],\\
N(R_\varepsilon-S_p)&=\max\{f_\varepsilon^+(p),f_\varepsilon^-(p)\}.
\end{aligned}
\tag{61.4}
$$

**引理 61.2。** 对 $1-c\le p\le\varepsilon\le1/16$，正向最大值在 $q=t=1$ 达到，且

$$
f_\varepsilon^+(p)
=\frac{\varepsilon+
\sqrt{\varepsilon^2+4(\sqrt{\varepsilon(1-p)}-\sqrt p)^2}}2.
\tag{61.5}
$$

**证明。** 在该 $p$ 区间，$rr^{\mathsf T}-P_p$ 的非对角元素均非负，且 $zz$ 对角为 $\varepsilon-p\ge0$。增加 $t$ 只增加这些非负元素。因此加共同标量单位阵后的 Perron 比较给 $\lambda$ 随 $t$ 不减，可取 $t=1$。

此时两加权向量的范数平方为 $1+\varepsilon q$ 和 $1$，内积为 $A+Bq$，其中

$$
A=c\sqrt{1-p}+\sqrt{\varepsilon p},
\qquad B=(1-c)\sqrt{1-p}.
$$

Cauchy 给 $A\le1$。又因为 $p\ge1-c$，

$$
2B\le2(1-c)\sqrt c
\le(1-c)(1+c)=\varepsilon.
$$

特征值根式内的多项式是

$$
4(1-A^2)+4(\varepsilon-2AB)q+(\varepsilon^2-4B^2)q^2.
$$

三个系数均非负，迹项 $\varepsilon q$ 也随 $q$ 不减，因此可取 $q=1$。这时两个向量的楔积为
$\sqrt p-\sqrt{\varepsilon(1-p)}$，特征值公式给式（61.5）。$\square$

### 61.3 全部 tester 的一致首阶极限

写

$$
\delta=\sqrt\varepsilon,
\qquad p=\delta^2-\kappa\delta^3.
\tag{61.6}
$$

当 $\kappa$ 在任意固定有界区间变化时，充分小的 $\delta>0$ 使下列根式有定义。主块有一致展开

$$
\frac{rr^{\mathsf T}-P_p}{\delta^2}
=H_\kappa+O(\delta),
\qquad
H_\kappa=\frac{uv_\kappa^{\mathsf T}+v_\kappa u^{\mathsf T}}2,
\quad u=(1,1,0)^{\mathsf T},\quad v_\kappa=(1,0,\kappa)^{\mathsf T}.
\tag{61.7}
$$

$D(q,t)u$ 的范数为一，$D(q,t)v_\kappa$ 的范数平方为 $q+\kappa^2t$，内积为 $q$。所以

$$
\frac{\lambda_\varepsilon(p;q,t)}{\varepsilon}
=\frac{q+\sqrt{q+\kappa^2t}}2+O(\delta),
\tag{61.8}
$$

余项在 $q,t\in[0,1]$ 和有界 $\kappa$ 上一致。这里可以直接使用最大特征值对算符范数的 Lipschitz 界，不要求特征值在原点简单。

因此正向首阶最大值为

$$
F^+(\kappa)=\frac{1+\sqrt{1+\kappa^2}}2.
\tag{61.9}
$$

负向首阶函数是

$$
G_\kappa(q,t)
=1-\frac q2-t+\frac12\sqrt{q+\kappa^2t}.
\tag{61.10}
$$

令 $w=q+\kappa^2t$，则

$$
G_\kappa(q,t)
=1-\frac w2+\frac{\sqrt w}2
-t\left(1-\frac{\kappa^2}{2}\right).
$$

当 $\kappa^2<2$ 时，其唯一全局最大点为 $(q,t)=(1/4,0)$，最大值为 $9/8$。特别地，$\kappa_0=3/4$ 满足

$$
F^+(\kappa_0)=\frac98,
\qquad
\partial_tG_{\kappa_0}(1/4,0)
=-1+\frac{\kappa_0^2}{2}=-\frac{23}{32}<0.
\tag{61.11}
$$

这一步检查了整个 tester 参数方形，不只比较两个预选 tester。

### 61.4 负向最大值的一致下一阶

需要证明，在 $\kappa$ 靠近 $\kappa_0$ 时，有限 $\delta$ 的负向最大值仍在边界 $t=0$ 达到。下面写出局部光滑性，避免把一致值收敛误用为导数收敛。

定义可在 $\delta=0$ 光滑延拓的系数

$$
\begin{aligned}
a_\delta&=\frac{\sqrt{1-\delta^2+\kappa\delta^3}}{1+\sqrt{1-\delta^2}},\\
b_\delta&=\frac{-\kappa+\delta-\kappa\delta^2}
{\sqrt{1-\kappa\delta}+\sqrt{1-\delta^2+\kappa\delta^3}},\\
d_\delta&=\frac{-\kappa}
{\sqrt{1-\delta^2}\sqrt{1-\kappa\delta}
+\sqrt{1-\delta^2+\kappa\delta^3}}.
\end{aligned}
\tag{61.12}
$$

它们是两个加权向量的三个楔积系数除以 $\delta^2$，且在 $\delta=0$ 分别为 $1/2,-\kappa/2,-\kappa/2$。令

$$
\begin{aligned}
T_\delta&=q+\kappa\delta(t-1),\\
Q_\delta&=a_\delta^2q(1-q)+b_\delta^2qt+d_\delta^2(1-q)t.
\end{aligned}
$$

则准确地有

$$
\frac{\lambda_\varepsilon(p;q,t)}{\varepsilon}
=\frac{T_\delta+\sqrt{T_\delta^2+4Q_\delta}}2.
\tag{61.13}
$$

在 $(\kappa,q,t)=(3/4,1/4,0)$ 附近，根式内在 $\delta=0$ 为 $q+\kappa^2t>0$，故式（61.13）及其 $q,t$ 导数都连续光滑，并一致趋于首阶表达式。

取 $\kappa_0$ 的一个小闭邻域。式（61.10）的唯一最大点始终为 $(1/4,0)$；紧性和一致收敛使有限 $\delta$ 的全局最大点全部落入该点的任意预定小邻域。缩小邻域后，式（61.11）及导数一致收敛保证整个邻域内的有限 $\delta$ 负向函数对 $t$ 严格递减。因此所有最大点必有 $t=0$。

在 $t=0$ 时，主块只剩 $xy$。由直接展开，

$$
\frac{D(rr^{\mathsf T}-P_p)D}{\varepsilon}\bigg|_{xy}
=
\begin{pmatrix}q&\frac12\sqrt{q(1-q)}\\
\frac12\sqrt{q(1-q)}&0\end{pmatrix}
-\kappa\delta
\begin{pmatrix}q&\sqrt{q(1-q)}\\
\sqrt{q(1-q)}&1-q\end{pmatrix}
+O(\delta^2),
\tag{61.14}
$$

余项在 $q$ 靠近 $1/4$、$\kappa$ 靠近 $\kappa_0$ 时一致。$q=1/4$ 时，第一个矩阵的单位正特征向量为
$n=(\sqrt3/2,1/2)^{\mathsf T}$，而第二个矩阵是
$w w^{\mathsf T}$，$w=(1/2,\sqrt3/2)^{\mathsf T}$。故

$$
|n^{\mathsf T}w|^2=\frac34.
$$

局部正特征值简单，因此式（61.14）的一阶特征值改变量为 $-3\kappa\delta/4$。其余 $q$ 的最大点趋于 $1/4$。用固定 $q=1/4$ 给下界、实际最大点和首阶函数的 $\le9/8$ 给上界，得到一致的极值展开

$$
\frac{f_\varepsilon^-(p)}{\varepsilon}
=\frac98-\frac34\kappa\delta+o(\delta)
\qquad(\kappa\to\kappa_0,\ \delta\downarrow0).
\tag{61.15}
$$

这里最大点定位与式（61.14）的余项一致性保证可沿变化的 $\kappa$ 使用式（61.15），无需先假设最优 $q$ 的收敛速率。

### 61.5 二阶最优值的下界

对任意最优修复的边缘参数 $p_\varepsilon$，已证区间给 $p_\varepsilon\le\varepsilon$。合法 $xz$ 事件又给

$$
p_\varepsilon\ge(\sqrt\varepsilon-e_\varepsilon)_+^2,
\qquad e_\varepsilon<\frac98\varepsilon.
$$

因此，写 $p_\varepsilon=\varepsilon-\kappa_\varepsilon\varepsilon^{3/2}$ 时，有

$$
0\le\kappa_\varepsilon\le\frac94
$$

对充分小的 $\varepsilon$ 成立。单参数约化允许保留同一个 $p_\varepsilon$ 而取 $S_{p_\varepsilon}$ 为最优修复。

若沿某个趋零子列有 $\kappa_\varepsilon\ge3/4+\eta$，其中 $\eta>0$ 固定，则式（61.8）、（61.9）的一致收敛会给

$$
\frac{e_\varepsilon}{\varepsilon}
\ge F^+(3/4+\eta)+o(1)>\frac98,
$$

与已证上界矛盾。所以

$$
\limsup_{\varepsilon\downarrow0}\kappa_\varepsilon\le\frac34.
\tag{61.16}
$$

第 58 节的固定全块事件 $E_*$ 对任意因果修复给准确下界

$$
D(R_\varepsilon,S)
\ge\frac34p+\frac38\varepsilon
-\frac{3\varepsilon^2}{16(1+c)^2}.
\tag{61.17}
$$

代入最优参数并使用式（61.16），得到

$$
\liminf_{\varepsilon\downarrow0}
\frac{e_\varepsilon-9\varepsilon/8}{\varepsilon^{3/2}}
\ge-\frac9{16}.
\tag{61.18}
$$

### 61.6 匹配上界与最优参数收敛

选取明确的竞争参数

$$
\kappa(\delta)=\frac34-\sqrt\delta,
\qquad
p(\delta)=\delta^2-\kappa(\delta)\delta^3.
\tag{61.19}
$$

充分小的 $\delta>0$ 时，$0<\kappa(\delta)<3/4$ 且
$1-\sqrt{1-\delta^2}<p(\delta)<\delta^2$，故该修复合法并位于约化区间。

式（61.8）、（61.9）或准确式（61.5）给

$$
\frac{f_\varepsilon^+(p(\delta))}{\varepsilon}
=F^+(\kappa(\delta))+O(\delta)
=\frac98-\frac3{10}\sqrt\delta+O(\delta),
\tag{61.20}
$$

其中 $(F^+)'(3/4)=3/10$。另一方面，式（61.15）给

$$
\frac{f_\varepsilon^-(p(\delta))}{\varepsilon}
=\frac98-\frac9{16}\delta+o(\delta).
\tag{61.21}
$$

正向距 $9/8$ 的裕量为 $\sqrt\delta$ 阶，严格大于负向的 $\delta$ 阶下降，所以充分小的 $\delta$ 时，完整误差由负向决定。式（61.21）给式（61.2）的匹配上界，与式（61.18）合并，证明式（61.2）。

最后，对任意最优参数，在式（61.17）中代入式（61.2），得到

$$
-\frac9{16}+o(1)
\ge-\frac34\kappa_\varepsilon-O(\sqrt\varepsilon).
$$

故 $\liminf\kappa_\varepsilon\ge3/4$。与式（61.16）合并得
$\kappa_\varepsilon\to3/4$，证明式（61.3）。$\square$

### 61.7 范围

上述结果只描述指定 $2\times2\times3$ 候选族在 $\varepsilon\downarrow0$ 时的最优修复误差及其边缘参数。它没有给有限 $\varepsilon$ 的闭式最优值，也没有给 $p_\varepsilon$ 的 $\varepsilon^2$ 系数。证明不依赖对全体候选的比例猜测或有限点数值外推。

## 追加锚（本行以下为增补区）

## 62. 有限参数的准确最优修复、边缘唯一性与更高阶展开

### 62.1 接口与结论范围

沿用 $2\times2\times3$ 接口、全部量子 tester 事件和纯等距候选

$$
R_\varepsilon=|x+c y+\sqrt\varepsilon z\rangle
\langle x+c y+\sqrt\varepsilon z|,
\quad c=\sqrt{1-\varepsilon},
\quad x=|000\rangle,\ y=|101\rangle,\ z=|112\rangle.
$$

记最优因果修复误差为 $e_\varepsilon$。第 59 节的精确单参数约化给

$$
e_\varepsilon=\min_{1-c\le p\le\varepsilon}N(R_\varepsilon-S_p),
\tag{62.1}
$$

其中

$$
S_p=|\sqrt{1-p}x+\sqrt{1-p}y+\sqrt p z\rangle
\langle\sqrt{1-p}x+\sqrt{1-p}y+\sqrt p z|
+p|010\rangle\langle010|.
$$

这个约化针对全部归一化因果修复：每个最优修复的早输出边缘参数 $p=\sigma_{11}$ 均在上述区间内，且相同 $p$ 的 $S_p$ 不增加误差。事件误差包含归一化迹项。

对 $0<\varepsilon\le1/16$，令

$$
\begin{aligned}
d&=1-c,\qquad p_0=\frac{d(3-d)}2,
\qquad p_* =\frac{\varepsilon}{1+\varepsilon},\\
B(p)&=4(p-d)+d^2,\qquad b(p)^2=d^2(1-p),\\
F_\varepsilon(p)&=p+\frac{b(p)^2}{B(p)},\\
G_\varepsilon(p)&=\frac{\varepsilon+
\sqrt{\varepsilon^2+4(\sqrt{\varepsilon(1-p)}-\sqrt p)^2}}2,\\
\gamma(p)&=c\sqrt p-\sqrt{\varepsilon(1-p)},\\
L_\varepsilon(p)&=p(p-\varepsilon)
+(p+\varepsilon)\frac{b(p)^2}{B(p)}-\gamma(p)^2.
\end{aligned}
\tag{62.2}
$$

$F_\varepsilon$ 与 $L_\varepsilon$ 的使用范围为 $p\ge p_0$，等价于 $B(p)\ge\varepsilon>0$。

**定理 62.1（整个参数区间的准确最优修复）。** 对每个 $0<\varepsilon\le1/16$，有

$$
d<p_0<p_*<\varepsilon.
\tag{62.3}
$$

方程

$$
F_\varepsilon(p)=G_\varepsilon(p)
\tag{62.4}
$$

在 $(p_0,p_*)$ 内恰有一个解 $\bar p_\varepsilon$，并且

$$
e_\varepsilon=
F_\varepsilon(\bar p_\varepsilon)
=G_\varepsilon(\bar p_\varepsilon).
\tag{62.5}
$$

交点处具有统一的严格证书下界

$$
L_\varepsilon(\bar p_\varepsilon)>\frac{\varepsilon^2}{34}>0.
\tag{62.6}
$$

修复 $S_{\bar p_\varepsilon}$ 达到最优值，而且所有最优修复的早输出边缘参数均满足

$$
\sigma_{11}=\bar p_\varepsilon.
\tag{62.7}
$$

**推论 62.2（最优参数的解析展开）。** 写唯一最优边缘参数为 $p_\varepsilon=\bar p_\varepsilon$。存在实解析函数 $\kappa(\delta)$，在零附近满足 $\kappa(0)=3/4$，并对充分小的正 $\varepsilon$ 有

$$
p_\varepsilon=\varepsilon-\kappa(\sqrt\varepsilon)\varepsilon^{3/2}.
\tag{62.8}
$$

特别地，

$$
\begin{aligned}
p_\varepsilon
&=\varepsilon-\frac34\varepsilon^{3/2}
+\frac{65}{64}\varepsilon^2+O(\varepsilon^{5/2}),\\
e_\varepsilon
&=\frac98\varepsilon-\frac9{16}\varepsilon^{3/2}
+\frac{255}{256}\varepsilon^2+O(\varepsilon^{5/2}).
\end{aligned}
\tag{62.9}
$$

唯一性指边缘参数，不宣称完整最优修复算符唯一。准确交点公式覆盖整个 $0<\varepsilon\le1/16$；幂级数展开描述 $\varepsilon\downarrow0$。

### 62.2 两个方向的事件下界

精确单参数约化中，反馈归一化算符为
$C(q,t)=\operatorname{diag}(q,1-t,1-q,t)$；事件仍遍历整个正区间 $0\preceq E\preceq C\otimes I_D$。记 $\lambda(p;q,t)$ 为加权 $R_\varepsilon-S_p$ 主块的非负最大特征值，则

$$
\begin{aligned}
h(R_\varepsilon-S_p)&=\max_{q,t}\lambda(p;q,t),\\
h(S_p-R_\varepsilon)&=\max_{q,t}
[\lambda(p;q,t)+\varepsilon(1-q-t)].
\end{aligned}
\tag{62.10}
$$

正向最大值准确地为 $G_\varepsilon(p)$，由 $q=t=1$ 达到。其证明只需非负矩阵比较：在 $p\in[d,\varepsilon]$ 上，主块的非对角元素及 $zz$ 对角均非负，增加 $t$ 不减最大特征值，所以可取 $t=1$。此时两加权向量的范数平方为 $1+\varepsilon q$ 与 $1$，内积为 $A+Hq$，其中

$$
A=c\sqrt{1-p}+\sqrt{\varepsilon p}\le1,
\qquad H=d\sqrt{1-p},\qquad
2H\le2d\sqrt c\le d(1+c)=\varepsilon.
$$

特征值根式的被开方多项式为

$$
4(1-A^2)+4(\varepsilon-2AH)q+(\varepsilon^2-4H^2)q^2.
$$

各系数非负，迹项 $\varepsilon q$ 也不减，故可取 $q=1$。此时特征值公式就是 $G_\varepsilon(p)$。

**引理 62.3（$t=0$ 的准确负向最大值）。** 对 $p\in[d,\varepsilon]$，有

$$
J_\varepsilon(p):=
\max_{0\le q\le1}
[\lambda(p;q,0)+\varepsilon(1-q)]
=
\begin{cases}
\varepsilon,&d\le p\le p_0,\\
F_\varepsilon(p),&p_0\le p\le\varepsilon.
\end{cases}
\tag{62.11}
$$

后一段的达到点为

$$
q_* =\frac{B-\varepsilon}{2B},
\qquad
F_\varepsilon(p)\ge\varepsilon,
\qquad F_\varepsilon'(p)=1-\frac{\varepsilon^2}{B^2}\ge0.
\tag{62.12}
$$

**证明。** 当 $t=0$ 时，加权主块的迹是
$T_0=p-\varepsilon+\varepsilon q$，秩二特征方程的常数项是 $-b^2q(1-q)$。因此负向值为

$$
\frac{p+\varepsilon-\varepsilon q+
\sqrt{T_0^2+4b^2q(1-q)}}2.
$$

先设 $p\le p_0$。使用 $\varepsilon=2d-d^2$，有

$$
\varepsilon(\varepsilon-p)-b^2
=2d(1-d)(p_0-p)\ge0.
$$

于是准确平方差满足

$$
\frac{(\varepsilon-p+\varepsilon q)^2
-[T_0^2+4b^2q(1-q)]}{4}
=b^2q^2+[\varepsilon(\varepsilon-p)-b^2]q\ge0.
\tag{62.13}
$$

$\varepsilon-p+\varepsilon q\ge0$，故可取平方根，给出负向值不超过 $\varepsilon$；$q=0$ 达到 $\varepsilon$。

再设 $p\ge p_0$，等价于 $B\ge\varepsilon$。令 $u=b^2/B$、$\mu=p+u=F_\varepsilon(p)$。直接核得

$$
\varepsilon^2-4b^2=d^2B,
\qquad
u(\mu-\varepsilon)=b^2q_*^2.
$$

第二式左端的 $u>0$，所以 $\mu\ge\varepsilon$。准确平方差为

$$
\begin{aligned}
&\frac{(2\mu-p-\varepsilon+\varepsilon q)^2
-[T_0^2+4b^2q(1-q)]}{4}\\
&\qquad=b^2q^2+(\varepsilon u-b^2)q+u(\mu-\varepsilon)
=b^2(q-q_*)^2.
\end{aligned}
\tag{62.14}
$$

根号上界的右侧满足
$2\mu-p-\varepsilon+\varepsilon q\ge\varepsilon-p\ge0$，因此可以取平方根，得到值不超过 $\mu$，并在合法的 $q_*\in[0,1/2)$ 达到。$p=p_0$ 时 $B=\varepsilon$、$q_*=0$，上面的恒等式也给 $F_\varepsilon(p_0)=\varepsilon$，所以两段接合。

求导给

$$
F'(p)=1-\frac{d^2[B+4(1-p)]}{B^2}
=1-\frac{\varepsilon^2}{B^2},
$$

因为 $d^2[B+4(1-p)]=\varepsilon^2$。$\square$

### 62.3 一个控制全部 tester 的多项式证书

令

$$
\beta=\sqrt p-\sqrt{\varepsilon(1-p)},
\qquad
\gamma=c\sqrt p-\sqrt{\varepsilon(1-p)}.
$$

对任意 $q,t\in[0,1]$，主块的迹及秩二特征多项式常数项可写为

$$
\begin{aligned}
T&=p-\varepsilon+\varepsilon q+(\varepsilon-p)t,\\
Q&=b^2q(1-q)+\beta^2qt+\gamma^2(1-q)t,\\
\lambda(p;q,t)&=\frac{T+\sqrt{T^2+4Q}}2.
\end{aligned}
\tag{62.15}
$$

**引理 62.4（全 tester 证书）。** 若 $p\in[p_0,\varepsilon]$ 且 $L_\varepsilon(p)\ge0$，则

$$
h(S_p-R_\varepsilon)=F_\varepsilon(p).
\tag{62.16}
$$

**证明。** 记 $\mu=F_\varepsilon(p)$、$u=\mu-p=b^2/B>0$，并置

$$
k=\mu-\varepsilon+\varepsilon(q+t).
$$

引理 62.3 给 $k\ge0$，且 $k-T=u+pt>0$。直接展开，并使用

$$
\gamma^2-\beta^2=-\varepsilon p
+2d\sqrt{\varepsilon p(1-p)},
$$

得到准确分解

$$
\begin{aligned}
k(k-T)-Q
={}&b^2(q-q_*)^2\\
&+t\left[L_\varepsilon(p)+2d\sqrt{\varepsilon p(1-p)}\,q\right]
+\varepsilon p t^2.
\end{aligned}
\tag{62.17}
$$

在声明条件下右侧非负。由于 $k\ge0$ 且 $k>T$，$k$ 位于二次函数 $z(z-T)-Q$ 的递增区域 $z\ge\max\{0,T\}$；式（62.17）因此给 $k\ge\lambda(p;q,t)$。这也处理 $k=0$ 的边界：此时 $T<0$，而非负乘积条件强制 $Q=0$，故 $\lambda=0$。

于是所有 $q,t$ 都满足

$$
\lambda(p;q,t)+\varepsilon(1-q-t)\le\mu.
$$

$t=0,q=q_*$ 由引理 62.3 达到 $\mu$，证明式（62.16）。$\square$

这个证书明确控制整个 tester 参数方形，不将 $t=0$ 最优先验化。

### 62.4 唯一交点与条件达界

**定理 62.1 的交点与条件达界部分。** 因为 $0<d\le\varepsilon\le1/16$，有

$$
p_0>d,\qquad
\frac{p_*}{d}=\frac{2-d}{1+\varepsilon}
\ge\frac{31}{17}>\frac32>\frac{p_0}{d},
\qquad p_*<\varepsilon.
$$

因此式（62.3）成立。函数 $F_\varepsilon$ 在 $[p_0,\varepsilon]$ 上严格递增；其导数只在左端点为零。对 $p<p_*$，
$\sqrt{\varepsilon(1-p)}-\sqrt p$ 为正且严格递减，所以 $G_\varepsilon$ 在 $[d,p_*]$ 上严格递减。并且

$$
F_\varepsilon(p_0)=\varepsilon<G_\varepsilon(p_0),
\qquad
G_\varepsilon(p_*)=\varepsilon<F_\varepsilon(p_*).
\tag{62.18}
$$

介值定理与严格单调性给 $(p_0,p_*)$ 内的唯一交点 $\bar p_\varepsilon$。

由第 62.2 节，对所有 $p\in[d,\varepsilon]$，均有

$$
N(R_\varepsilon-S_p)\ge
\max\{G_\varepsilon(p),J_\varepsilon(p)\}.
\tag{62.19}
$$

记交点值为 $m_\varepsilon$。若 $p<\bar p_\varepsilon$，则 $G_\varepsilon(p)>m_\varepsilon$；若 $p>\bar p_\varepsilon$，则 $p>p_0$，故 $J_\varepsilon(p)=F_\varepsilon(p)>m_\varepsilon$。在交点两者同等于 $m_\varepsilon$。因此式（62.19）右端在整个约化区间上的唯一最小点是 $\bar p_\varepsilon$，最小值是 $m_\varepsilon$。这与式（62.1）给出 $e_\varepsilon\ge m_\varepsilon$。

如果 $L_\varepsilon(\bar p_\varepsilon)\ge0$，引理 62.4 和正向准确公式给

$$
N(R_\varepsilon-S_{\bar p_\varepsilon})
=\max\{F_\varepsilon(\bar p_\varepsilon),
G_\varepsilon(\bar p_\varepsilon)\}=m_\varepsilon.
\tag{62.20}
$$

所以达到全局下界。任意原始最优修复的参数 $p=\sigma_{11}$ 均在 $[d,\varepsilon]$，且替换为相同参数的 $S_p$ 不增加误差；式（62.19）的严格性迫使 $p=\bar p_\varepsilon$，因此只要该交点满足正性条件，式（62.5）、（62.7）就成立。下面证明整个参数区间都有统一的严格正性余量。

### 62.5 整个参数区间的统一证书

**证明。** 以下固定 $p=\bar p_\varepsilon$，并记

$$
u=\frac{b^2}{B},\qquad\mu=p+u,
\qquad\beta=\sqrt p-\sqrt{\varepsilon(1-p)}.
$$

交点关系 $\mu=G_\varepsilon(p)$ 给

$$
\beta^2=\mu(\mu-\varepsilon).
\tag{62.21}
$$

直接展开两项平方还给出恒等式

$$
\gamma^2=c\beta^2+d\varepsilon-d(c+\varepsilon)p.
\tag{62.22}
$$

式（62.21）、（62.22）使 $L_\varepsilon(p)$ 在交点处可完全改写成有理代数式。

令

$$
\rho=\frac d{2-d}=\frac{1-c}{1+c},
\qquad w=\frac B\varepsilon.
\tag{62.23}
$$

由于 $d\le\varepsilon\le1/16$ 且 $2-d>1$，有
$0<\rho\le1/16$。又因 $p_0<p<p_*<\varepsilon$，

$$
1<w<\frac{B(\varepsilon)}\varepsilon=2-\rho<2.
\tag{62.24}
$$

利用 $\varepsilon=d(2-d)$ 与
$\varepsilon^2-4b^2=d^2B$，得到

$$
\begin{aligned}
P:=\frac p\varepsilon&=\frac{2+w+\rho}{4},\\
U:=\frac u\varepsilon&=\frac{1/w-\rho}{4},\\
M:=\frac\mu\varepsilon&=\frac{(w+1)^2}{4w},\\
c&=\frac{1-\rho}{1+\rho},\qquad
\frac d\varepsilon=\frac{1+\rho}{2},\qquad
\frac{d(c+\varepsilon)}\varepsilon
=\frac{1+4\rho-\rho^2}{2(1+\rho)}.
\end{aligned}
\tag{62.25}
$$

将式（62.21）、（62.22）代入 $L_\varepsilon$，可得

$$
\begin{aligned}
\frac{L_\varepsilon(p)}{\varepsilon^2}
={}&P(P-1)+(P+1)U-cM(M-1)\\
&-\frac{1+\rho}{2}
+\frac{1+4\rho-\rho^2}{2(1+\rho)}P.
\end{aligned}
\tag{62.26}
$$

将式（62.25）代入式（62.26），整理为

$$
16w^2(1+\rho)\frac{L_\varepsilon(p)}{\varepsilon^2}
=N_0(w)+\rho N_1(w)
-\rho^2w(w^2+10w-1)-2\rho^3w^2,
\tag{62.27}
$$

其中

$$
\begin{aligned}
N_0(w)&=2w^3-5w^2+6w-1,\\
N_1(w)&=2w^4+9w^3-9w^2+7w+1.
\end{aligned}
$$

在 $1\le w\le2$ 上，两个正项有直接的下界：

$$
\begin{aligned}
N_0(w)
&=2(w-1)^3+(w-1)^2+2(w-1)+2\ge2,\\
N_1(w)
&=2w^4+9w^2(w-1)+7w+1\ge10.
\end{aligned}
\tag{62.28}
$$

同时

$$
0<w(w^2+10w-1)\le46,\qquad 2w^2\le8.
$$

所以式（62.27）的右侧满足

$$
\begin{aligned}
N_0+\rho N_1-\rho^2w(w^2+10w-1)-2\rho^3w^2
&\ge2+\rho(10-46\rho-8\rho^2)\\
&\ge2+\frac{227}{32}\rho>2,
\end{aligned}
\tag{62.29}
$$

最后一步用了 $\rho\le1/16$。另一方面，

$$
16w^2(1+\rho)<16\cdot4\cdot\frac{17}{16}=68.
$$

因此 $L_\varepsilon(p)/\varepsilon^2>2/68=1/34$，这就是式（62.6）。第 62.4 节的条件达界部分随即给出式（62.5）、最优修复的达到性及全部最优边缘参数的唯一性，完成定理 62.1 的证明。$\square$

### 62.6 解析交点

令 $\delta=\sqrt\varepsilon$、$p=\delta^2(1-\kappa\delta)$、$c=\sqrt{1-\delta^2}$，并定义缩放函数

$$
f(\delta,\kappa)=\frac{F_{\delta^2}(p)}{\delta^2},
\qquad g(\delta,\kappa)=\frac{G_{\delta^2}(p)}{\delta^2}.
$$

其在 $\delta=0$ 处的解析延拓可直接写为

$$
\begin{aligned}
f(\delta,\kappa)
&=1-\kappa\delta+
\frac{(1-p)/(1+c)^2}
{4(1-\kappa\delta)-4/(1+c)+\delta^2/(1+c)^2},\\
z(\delta,\kappa)
&=\frac{\kappa-\delta+\kappa\delta^2}
{\sqrt{1-p}+\sqrt{1-\kappa\delta}},\\
g(\delta,\kappa)
&=\frac{1+\sqrt{1+4z(\delta,\kappa)^2}}2.
\end{aligned}
\tag{62.30}
$$

在 $(\delta,\kappa)=(0,3/4)$ 附近，分母非零且根号内严格正，所以这些是实解析函数。并有

$$
f(0,\kappa)=\frac98,
\qquad g(0,\kappa)=\frac{1+\sqrt{1+\kappa^2}}2,
\qquad
\partial_\kappa(f-g)(0,3/4)=-\frac3{10}\ne0.
\tag{62.31}
$$

解析隐函数定理给唯一的实解析 $\kappa(\delta)$，满足 $f=g$、$\kappa(0)=3/4$。当 $\delta>0$ 充分小时，其对应参数在 $(p_0,p_*)$：下端关系来自 $p/\varepsilon\to1$ 与 $p_0/\varepsilon\to3/4$，上端关系来自

$$
p_*-p=\kappa(\delta)\delta^3-
\frac{\delta^4}{1+\delta^2}>0.
$$

因此这个解析交点正是定理 62.1 中的 $\bar p_\varepsilon$。沿该交点，直接展开给

$$
\frac{B(p)}\varepsilon\longrightarrow2,
\qquad
\frac{L_\varepsilon(p)}{\varepsilon^2}
\longrightarrow\frac{1-(3/4)^2}{4}=\frac7{64}>0.
\tag{62.32}
$$

定理 62.1 已在整个参数区间给出严格正性与最优性，因此这个解析交点就是所有最优修复的唯一边缘参数。这证明式（62.8），不需要预先假定最优参数的渐近位置。

### 62.7 更高阶系数

直接展开式（62.30）得到

$$
f(\delta,\kappa)
=\frac98-\frac34\kappa\delta
+\left(\frac{\kappa^2}{2}-\frac3{64}\right)\delta^2
+O(\delta^3).
\tag{62.33}
$$

在 $\kappa=3/4$，另一函数的偏导为

$$
\partial_\delta g(0,3/4)=-\frac{33}{128},
\qquad
\partial_\kappa g(0,3/4)=\frac3{10}.
$$

因此对 $f(\delta,\kappa(\delta))=g(\delta,\kappa(\delta))$ 求导，得到

$$
-\frac9{16}
=-\frac{33}{128}+\frac3{10}\kappa'(0),
\qquad\kappa'(0)=-\frac{65}{64}.
\tag{62.34}
$$

所以

$$
\kappa(\delta)=\frac34-\frac{65}{64}\delta+O(\delta^2).
$$

代入 $p=\delta^2-\kappa(\delta)\delta^3$ 给式（62.9）的第一式。再代入式（62.33），$\delta^2$ 系数为

$$
-\frac34\left(-\frac{65}{64}\right)
+\frac12\left(\frac34\right)^2-\frac3{64}
=\frac{255}{256},
$$

乘以 $\delta^2=\varepsilon$ 得式（62.9）的第二式。$\square$

### 62.8 含义与边界

对全部 $0<\varepsilon\le1/16$，最优边缘由两个相反方向的合法续接事件达到同一误差来确定：正向在 $q=t=1$，负向在 $t=0,q=q_*$。这是具体相同接口上的平衡条件。

式（62.4）给整个区间内有限非零参数的准确修复误差，不只是渐近拟合。统一证书下界（62.6）使结果无需逐点检验条件；上述范围与第 59 节全体因果修复的单参数约化范围一致。

所得唯一性限定于早输出边缘的 $\sigma_{11}$；完整最优修复仍可有不同补块或其他等误差实现。结论不推广到其他候选族或其他末输出维数。

## 追加锚（本行以下为增补区）

## 63. 秩至多二的量子比特早边缘：全部扩张均可同系数修复

### 63.1 合同与结论

固定晚输入 $A=\mathbb C^2$、早输出 $B=\mathbb C^2$，晚输出 $D$ 可以是任意非零有限维空间，张量次序为 $A\otimes B\otimes D$。早边缘与它的扩张满足

$$
M\succeq0,\quad\operatorname{Tr}_B M=I_A,
\qquad
R\succeq0,\quad\operatorname{Tr}_D R=M.
\tag{63.1}
$$

因果修复与全部量子 tester 合同为

$$
\begin{aligned}
\mathcal S_D&=\{S\succeq0:\operatorname{Tr}_D S=I_A\otimes\sigma,
\quad\sigma\succeq0,\ \operatorname{Tr}\sigma=1\},\\
C&\succeq0,\quad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D.
\end{aligned}
\tag{63.2}
$$

采用吸收全转置的配对约定，记

$$
\begin{aligned}
N_D(X)&=\max_{C,E}|\operatorname{Tr}(XE)|,\\
e_D(R)&=\min_{S\in\mathcal S_D}N_D(R-S),\\
\Delta(M)&=\max_C|\operatorname{Tr}(MC)-1|.
\end{aligned}
\tag{63.3}
$$

事件量词包含任意有限量子参考、记忆和最终测量。即使候选在部分反馈下没有归一化，式（63.3）仍是事件响应误差；这里没有把它当作两个归一化分布的总变差距离。

**定理 63.1（低秩早边缘的全部扩张）。** 若 $\operatorname{rank}M\le2$，则对每个有限维 $D$ 和每个满足式（63.1）的扩张，均有

$$
e_D(R)=\Delta(M).
\tag{63.4}
$$

**推论 63.2（纯三量子比特候选无严格间隙）。** 若 $A,B,D$ 均为量子比特且 $R$ 是纯的静态通道 Choi 算符，则 $e_D(R)=\Delta(M)$。因此在这个 $2\times2\times2$ 接口上，任何严格间隙 $e_D(R)>\Delta(M)$ 必须同时满足

$$
\operatorname{rank}R\ge2,
\qquad\operatorname{rank}(\operatorname{Tr}_D R)\ge3.
\tag{63.5}
$$

式（63.5）是必要条件，没有声称存在满足它的严格反例，也没有解决所有混合 $D=2$ 候选。

### 63.2 两角标准族及其显式因果修复

先在三个量子比特上取

$$
x=|000\rangle,\quad h=|011\rangle,
\quad y=|101\rangle,\quad z=|110\rangle,
$$

以及非负参数

$$
a^2+b^2=c^2+d^2=1,
\qquad a\ge c,\qquad d\ge b.
\tag{63.6}
$$

等价地可写 $a=\cos\alpha,b=\sin\alpha,c=\cos\beta,d=\sin\beta$，其中 $0\le\alpha\le\beta\le\pi/2$。定义

$$
r_0=ax+cy,\qquad r_1=bh+dz,
\qquad r=r_0+r_1,\qquad R=|r\rangle\langle r|,
\qquad t=a^2-c^2=d^2-b^2\ge0.
\tag{63.7}
$$

向量 $r$ 是等距

$$
V|0\rangle=a|00\rangle+b|11\rangle,
\qquad
V|1\rangle=c|01\rangle+d|10\rangle
$$

的 Choi 向量，所以 $\operatorname{Tr}_{BD}R=I_A$。

**引理 63.3（完整 tester 下的两角准确修复）。** 对每个满足式（63.6）的参数组，有

$$
e_D(R)=\Delta(M)=t+2ad=(a+d)^2-1.
\tag{63.8}
$$

一个显式最优修复由任意

$$
p\in[ac,1-bd]
\tag{63.9}
$$

给出：在正交分解 $\operatorname{span}\{x,y\}\oplus\operatorname{span}\{h,z\}$ 上令

$$
S_p=
\begin{pmatrix}p&ac\\ac&p\end{pmatrix}_{x,y}
\oplus
\begin{pmatrix}1-p&bd\\bd&1-p\end{pmatrix}_{h,z},
\tag{63.10}
$$

在其正交补上取零。

**证明。** 先检查参数区间与正性。Cauchy–Schwarz 给

$$
ac+bd\le\sqrt{a^2+b^2}\sqrt{c^2+d^2}=1,
$$

故式（63.9）非空。由 $a\ge c,d\ge b$，

$$
c^2\le ac\le p\le1-bd\le1-b^2=a^2.
\tag{63.11}
$$

两个二阶块的特征值分别是 $p\pm ac$ 和 $1-p\pm bd$，均非负。每个块的交叉项具有不同的 $D$ 坐标，偏迹后消失，因此

$$
\operatorname{Tr}_D S_p
=I_A\otimes\operatorname{diag}(p,1-p).
$$

所以 $S_p$ 是归一化因果修复。

令

$$
R_{\mathrm{diag}}=|r_0\rangle\langle r_0|
+|r_1\rangle\langle r_1|,
\qquad
X=R-R_{\mathrm{diag}}=|r_0\rangle\langle r_1|
+|r_1\rangle\langle r_0|.
\tag{63.12}
$$

修复保留了每个早输出分支内部的交叉项。因此

$$
R_{\mathrm{diag}}-S_p
=(a^2-p)(|x\rangle\langle x|-|h\rangle\langle h|)
+(p-c^2)(|z\rangle\langle z|-|y\rangle\langle y|).
\tag{63.13}
$$

两系数非负、和为 $t$。对任意完整 tester，$\operatorname{Tr}_A C=I_B$ 使每个标准基对角元均位于 $[0,1]$。由 $0\preceq E\preceq C\otimes I_D$，式（63.13）的正、负两个部分与 $E$ 的配对各自至多 $t$，所以

$$
|\operatorname{Tr}[(R_{\mathrm{diag}}-S_p)E]|\le t.
\tag{63.14}
$$

对跨分支项，不限制 $C$ 或 $E$ 的非对角元。正算子 $E$ 的 Cauchy–Schwarz 不等式给

$$
\begin{aligned}
|\operatorname{Tr}(XE)|
&\le2|\langle r_1|E|r_0\rangle|\\
&\le2\sqrt{\langle r_0|E|r_0\rangle
\langle r_1|E|r_1\rangle}\\
&\le2\sqrt{\langle r_0|C\otimes I_D|r_0\rangle
\langle r_1|C\otimes I_D|r_1\rangle}.
\end{aligned}
$$

向量 $x,y$ 具有不同的 $D$ 坐标，$h,z$ 也如此。记 $C$ 对角元按 $AB$ 标记，则

$$
\begin{aligned}
\langle r_0|C\otimes I_D|r_0\rangle
&=a^2C_{00,00}+c^2C_{10,10}\le a^2,\\
\langle r_1|C\otimes I_D|r_1\rangle
&=b^2C_{01,01}+d^2C_{11,11}\le d^2,
\end{aligned}
\tag{63.15}
$$

因为每行右侧所用的两个 $C$ 对角元和为 $1$。于是

$$
|\operatorname{Tr}(XE)|\le2ad.
\tag{63.16}
$$

式（63.14）、（63.16）在同一个任意 $C,E$ 上同时成立，直接相加得到

$$
N_D(R-S_p)\le t+2ad.
\tag{63.17}
$$

下界由一个合法的完整总事件达到。令

$$
|\chi\rangle=|00\rangle+|11\rangle,
\qquad C_+=|\chi\rangle\langle\chi|,
\qquad E_+=C_+\otimes I_D.
\tag{63.18}
$$

$\operatorname{Tr}_A C_+=I_B$，而

$$
\operatorname{Tr}(RE_+)=(a+d)^2.
$$

每个归一化因果修复的同一总响应均为 $1$，因此

$$
t+2ad=(a+d)^2-1\le\Delta(M)\le e_D(R)
\le N_D(R-S_p)\le t+2ad.
$$

全部不等式均取等，证明式（63.8）。这个推导也直接算出了 $\Delta$，无需先求另一个反馈端点。$\square$

### 63.3 为什么标准族覆盖全部低秩量子比特边缘

采用已发表的量子比特通道标准形。Ruskai、Szarek、Werner 的《An Analysis of Completely-Positive Trace-Preserving Maps on $M_2$》，[arXiv:quant-ph/0101003v2](https://arxiv.org/abs/quant-ph/0101003v2)，定理 12（PDF 第 18 页）证明以下条件等价：量子比特通道的 Choi 秩至多二；存在至多两个 Kraus 算符；经输入、输出酉基变换后可化成其式（17）。该文第 1.4 节式（18）（PDF 第 10 页）给出一个对角和一个反对角的 Kraus 表示。本文只使用这些标准形事实，不把它们作为新分类结论。

在通常的 $K\rho K^*$ 约定下，必要时将该文 $A^*\rho A$ 约定中的 Kraus 算符取伴随，可以写成

$$
K_0=\begin{pmatrix}a&0\\0&d\end{pmatrix},
\qquad
K_1=\begin{pmatrix}0&c\\b&0\end{pmatrix},
\qquad a^2+b^2=c^2+d^2=1,
\tag{63.19}
$$

其中四个系数可取非负。具体而言，对角、反对角表示先给四个可能带相位的系数；把它们写入纯化向量的 $000,011,101,110$ 四个位置后，整体相位和 $A,B,D$ 三个局部对角相位可以分别消去四个相位。例如四个相位依次为 $\phi_a,\phi_b,\phi_c,\phi_d$ 时，取整体相位 $-\phi_a$，以及三个局部相位

$$
\theta_A=\frac{\phi_a+\phi_b-\phi_c-\phi_d}{2},\qquad
\theta_B=\frac{\phi_a-\phi_b+\phi_c-\phi_d}{2},\qquad
\theta_D=\frac{\phi_a-\phi_b-\phi_c+\phi_d}{2}.
$$

这些相位消去全部四项的相位；零系数的相位可以任意指定，不添条件。故无需假设通道本来是实的。

这些 Kraus 算符给出 $M$ 的一个至多二维纯化，其向量正是式（63.7）的 $r$。若 $a<c$，同时交换 $A$ 和 $D$ 的两个基向量，会把 $(a,b,c,d)$ 变为 $(c,d,a,b)$。这样总能达到式（63.6）的次序 $a\ge c,d\ge b$。秩一边界可以给第二个 Kraus 算符补零，仍包含于同一结论；例如 $a=d=1,b=c=0$ 时 $\Delta=3$，不应把它排除为小缺陷区间之外的例外。

输入、早输出和晚输出上的局部酉变换都保持因果集合及完整 tester 集合，因而保持 $e_D$ 与 $\Delta$。例如把 $X$ 共轭为 $(U_A\otimes U_B\otimes U_D)X(U_A\otimes U_B\otimes U_D)^*$ 时，对 tester 作相同共轭即可保持配对及两项偏迹归一化；Choi 输入基变换所出现的共轭酉仍属于同一个允许的局部酉集合。

因此每个秩至多二的量子比特早边缘，都存在一个末输出为量子比特的纯扩张，其修复误差由引理 63.3 准确等于 $\Delta(M)$。同一 $M$ 的任意其他纯化，仅在纯化支撑上相差等距；这也保持最优误差。

### 63.4 从纯化到所有混合扩张

**定理 63.1 的证明。** 对给定 $M$，取第 63.3 节的纯扩张 $R^{\mathrm{pur}}$。第 57 节的固定边缘扩张定理给：对任意满足式（63.1）的 $R$，存在作用在末输出的 CPTP 通道 $\Lambda$，使

$$
R=(\operatorname{id}_{AB}\otimes\Lambda)(R^{\mathrm{pur}}).
\tag{63.20}
$$

若使用带有多余零 Kraus 方向的二维纯化，可在其实际支撑上构造该通道，再任意以固定态补全正交方向，从而仍得到定义在整个二维输入空间上的 CPTP 通道。

完整事件误差在末端 CPTP 处理下收缩，而 $\Delta(M)$ 由固定早边缘决定。因此

$$
\Delta(M)\le e_D(R)
\le e_2(R^{\mathrm{pur}})=\Delta(M).
\tag{63.21}
$$

这证明式（63.4）。一个达到最优值的修复可以直接取第 63.2 节显式修复经相应局部酉还原后，再施加同一个 $\Lambda$ 的像。$\square$

**推论 63.2 的证明。** 若 $R=|r\rangle\langle r|$ 且 $\dim D=2$，则

$$
\operatorname{rank}(\operatorname{Tr}_D|r\rangle\langle r|)
\le\dim D=2.
$$

定理 63.1 给同系数等式。因此严格间隙排除了纯 $R$，也排除了任何秩至多二的早边缘，得到式（63.5）。$\square$

### 63.5 范围与剩余问题

该结论对 $A=B=2$、$\operatorname{rank}M\le2$ 的全部扩张成立，末输出维数不必等于二。其新量词是固定早边缘的全部纯、混合扩张；末输出通道不能在这一类边缘上制造严格修复间隙。

对同样的量子比特早、晚端口，已有三维末输出的纯反例早边缘秩恰三。因此就纯静态候选而言，末输出维数三已经足以产生严格间隙，而维数至多二不可能产生；这没有把同样的最小维数结论推广到混合候选。

末输出为量子比特、$\operatorname{rank}M\in\{3,4\}$ 的混合候选仍未由本定理结算。第 60 节的秩二压缩族有秩三早边缘，所以它不属于定理 63.1 的假设范围；其局部参数等式及当前结果均不能替代一般混合量子比特问题的证明或反例。

## 追加锚（本行以下为增补区）

## 64. 三个量子比特上的混合候选严格因果修复间隙

### 64.1 接口与结论

固定晚输入 $A$、早输出 $B$、晚输出 $D$ 均为量子比特，张量次序为 $A\otimes B\otimes D$。因果修复满足

$$
S\succeq0,\qquad\operatorname{Tr}_D S=I_A\otimes\sigma,
\qquad\sigma\succeq0,\quad\operatorname{Tr}\sigma=1.
\tag{64.1}
$$

使用完整量子 tester 合同

$$
C\succeq0,\qquad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D.
\tag{64.2}
$$

全转置已吸收在 tester 的配对约定中。对静态候选 $R\succeq0$、$\operatorname{Tr}_{BD}R=I_A$，记

$$
\Delta(R)=\max_C|\operatorname{Tr}(R(C\otimes I_D))-1|,
\qquad
 e(R)=\min_{S\text{ 满足（64.1）}}\max_{C,E}
 |\operatorname{Tr}((R-S)E)|.
\tag{64.3}
$$

选取参数 $0<\varepsilon<1$、$0<a<1$，记 $c=\sqrt{1-\varepsilon}$，并定义

$$
\begin{aligned}
x&=|000\rangle,\quad x'=|001\rangle,
\quad y=|101\rangle,\\
z&=|110\rangle,\quad z'=|111\rangle,\\
u&=\sqrt a\,x+\sqrt{\varepsilon(1-a)}\,z,\\
v&=\sqrt{1-a}\,x'-\sqrt{\varepsilon a}\,z',\\
R_{a,\varepsilon}&=|u+cy\rangle\langle u+cy|+|v\rangle\langle v|.
\end{aligned}
\tag{64.4}
$$

这是秩恰二的静态通道 Choi 算符；它的早边缘是

$$
M_\varepsilon=|00\rangle\langle00|
+(1-\varepsilon)|10\rangle\langle10|
+\varepsilon|11\rangle\langle11|,
\tag{64.5}
$$

秩恰三。

**定理 64.1（混合量子比特末输出的严格间隙）。** 若

$$
\sqrt a\,(c-\varepsilon)>\varepsilon(1+c),
\tag{64.6}
$$

则

$$
e(R_{a,\varepsilon})>\Delta(R_{a,\varepsilon})=\varepsilon.
\tag{64.7}
$$

特别地，式（64.7）对整个参数区域

$$
0<\varepsilon\le\frac1{16},
\qquad\frac1{49}\le a<1
\tag{64.8}
$$

成立。因此 $a=1/2,\varepsilon=1/16$ 给出一个具体的 $2\times2\times2$ 混合严格反例。

证明只使用归一化总事件的饱和、正性和二阶主子式；不需要数值优化。

### 64.2 静态合法性、早边缘与三维纯反例的压缩

式（64.4）的两个向量具有不交的标准基支撑，且均非零，因此 $R_{a,\varepsilon}$ 正且秩恰二。对 $D$ 取偏迹时，$u$ 中 $x,z$ 的交叉项与 $v$ 中 $x',z'$ 的交叉项准确相消：它们分别为

$$
\pm\sqrt{\varepsilon a(1-a)}\,|00\rangle\langle11|
$$

及其伴随。其余非对角项具有不同的 $D$ 坐标，偏迹后为零。各对角项相加得到式（64.5），所以 $\operatorname{Tr}_{BD}R=I_A$。

若令 $q=C_{00,00}$、$t=C_{11,11}$，则 $q,t\in[0,1]$，且

$$
\operatorname{Tr}(M_\varepsilon C)=1-\varepsilon+\varepsilon(q+t).
\tag{64.9}
$$

两端 $1+\varepsilon$、$1-\varepsilon$ 分别由

$$
C_+=|00\rangle\langle00|+|11\rangle\langle11|,
\qquad
C_-=|01\rangle\langle01|+|10\rangle\langle10|
\tag{64.10}
$$

达到。由此 $\Delta=\varepsilon$，并且任意因果修复都满足 $e(R)\ge\varepsilon$。

这个候选可由三维末输出的纯候选

$$
R^{(3)}_\varepsilon
=|000+c\,101+\sqrt\varepsilon\,112\rangle
\langle000+c\,101+\sqrt\varepsilon\,112|
$$

经真实末端 CPTP 通道得到。定义等距 $W:\mathbb C^3\to\mathbb C^2_D\otimes\mathbb C^2_F$：

$$
\begin{aligned}
W|0\rangle&=\sqrt a\,|0,0\rangle+\sqrt{1-a}\,|1,1\rangle,\\
W|1\rangle&=|1,0\rangle,\\
W|2\rangle&=\sqrt{1-a}\,|0,0\rangle-\sqrt a\,|1,1\rangle.
\end{aligned}
\tag{64.11}
$$

三列正交归一，故 $\Lambda_a(X)=\operatorname{Tr}_F(WXW^*)$ 是 CPTP，并有

$$
R_{a,\varepsilon}
=(\operatorname{id}_{AB}\otimes\Lambda_a)(R^{(3)}_\varepsilon).
\tag{64.12}
$$

末端处理保持全部反馈总响应，却将晚输出压缩成量子比特。下面证明这一个压缩族仍保留严格修复间隙。

### 64.3 若同系数可修复，两个饱和总事件强迫哪些矩阵元

假设存在因果 $S$ 使完整事件误差至多 $\varepsilon$。记

$$
\Pi_+=C_+\otimes I_D,
\qquad\Pi_-=C_-\otimes I_D.
$$

对任意因果 $S$，两个总响应均为 $1$。因此

$$
\operatorname{Tr}(\Pi_+(R-S)\Pi_+)=\varepsilon,
\qquad
\operatorname{Tr}(\Pi_-(S-R)\Pi_-)=\varepsilon.
$$

如果第一个压缩有负特征值，其正谱投影就是合法的 $\Pi_+$ 以下事件，响应将严格超过总迹 $\varepsilon$，与误差假设矛盾。第二个压缩同理。故

$$
S_+:=\Pi_+S\Pi_+\preceq R_+:=\Pi_+R\Pi_+,
\qquad
S_-:=\Pi_-S\Pi_-\succeq R_-:=\Pi_-R\Pi_-.
\tag{64.13}
$$

这里

$$
R_+=|u\rangle\langle u|+|v\rangle\langle v|,
\qquad R_-=c^2|y\rangle\langle y|.
$$

正性与 $S_+\preceq R_+$ 强制 $S_+$ 支撑在 $\operatorname{span}\{u,v\}$。可写

$$
S_+=m|u\rangle\langle u|+n|v\rangle\langle v|
+w|u\rangle\langle v|+\overline w|v\rangle\langle u|,
\tag{64.14}
$$

其中 $m,n\in[0,1]$。因果条件中 $A=0$ 到 $A=1$ 的非对角块为零，故

$$
0=(\operatorname{Tr}_D S)_{00,11}
=\sqrt{\varepsilon a(1-a)}(m-n).
$$

$0<a<1$、$\varepsilon>0$ 保证系数非零，因此 $m=n$。此时

$$
\sigma_{00}=S_{x,x}+S_{x',x'}=m,
\qquad
\sigma_{11}=S_{z,z}+S_{z',z'}=\varepsilon m.
$$

归一化迫使

$$
\mu:=m=n=\frac1{1+\varepsilon},
\qquad p:=\sigma_{11}=\frac{\varepsilon}{1+\varepsilon},
\qquad
S_{x,x}=\mu a,\quad S_{x',x'}=\mu(1-a).
\tag{64.15}
$$

这一结论不要求把 $S$ 相位平均，也不要求式（64.14）的 $w$ 为零。

令

$$
s=S_{y,y},\qquad
k=\frac{S_{x,y}}{\sqrt a},
\qquad
\eta=\mu-c^2=\frac{\varepsilon^2}{1+\varepsilon}.
\tag{64.16}
$$

$S_-\succeq c^2|y\rangle\langle y|$ 给 $s\ge c^2$；而因果偏迹在 $AB=10$ 上给 $s\le\sigma_{00}=\mu$。$S$ 在 $x,y$ 上的二阶主子式给

$$
c^2\le s\le\mu,
\qquad |k|^2\le\mu s\le\mu^2.
\tag{64.17}
$$

### 64.4 第三个反馈族给出不相容的二阶约束

取任意 $0<q<1$，令

$$
C_q=\operatorname{diag}(q,1,1-q,0)
\tag{64.18}
$$

按 $AB=00,01,10,11$ 排列。它满足 $\operatorname{Tr}_A C_q=I_B$。记

$$
H_q=(C_q^{1/2}\otimes I_D)(R-S)(C_q^{1/2}\otimes I_D).
$$

它在 $x,y$ 子空间上的主块为

$$
B_q=
\begin{pmatrix}
a p q&\sqrt{a q(1-q)}(c-k)\\
\sqrt{a q(1-q)}(c-\overline k)&(c^2-s)(1-q)
\end{pmatrix}.
\tag{64.19}
$$

令 $\lambda_q=\max\{0,\lambda_{\max}(B_q)\}$。因为第一个对角元非负、第二个非正，$B_q$ 至多有一个正特征值，故它的正谱和等于 $\lambda_q$。

在加权空间中取 $B_q$ 的正谱投影，再加上与它正交的 $|x'\rangle\langle x'|$ 投影，得到一个效果 $0\preceq F_q\preceq I$。把它变为

$$
E_q=(C_q^{1/2}\otimes I_D)F_q(C_q^{1/2}\otimes I_D)
$$

就是合法 tester 事件，且

$$
\operatorname{Tr}((R-S)E_q)=\lambda_q+p(1-a)q.
\tag{64.20}
$$

即使 $H_q$ 在这些子空间之间有交叉项，它们与所选分块投影配对时也不贡献。另一方面，式（64.9）给完整总响应差

$$
\operatorname{Tr}((R-S)(C_q\otimes I_D))=-\varepsilon(1-q).
$$

因此互补事件 $C_q\otimes I_D-E_q$ 的响应为
$-\varepsilon(1-q)-\lambda_q-p(1-a)q$。误差至多 $\varepsilon$ 的假设迫使

$$
\lambda_q\le q A,
\qquad A:=\varepsilon-p(1-a)=\eta+ap.
\tag{64.21}
$$

于是 $qA I_2-B_q\succeq0$。其行列式非负，除以 $q>0$ 得

$$
\eta\,[qA+(s-c^2)(1-q)]
-a|c-k|^2(1-q)\ge0.
$$

令 $q\downarrow0$，得到必须满足的二阶约束

$$
a|c-k|^2\le\eta(s-c^2)\le\eta^2.
\tag{64.22}
$$

条件（64.6）保证 $c>\mu$；由式（64.17），$|k|\le\mu$，所以

$$
|c-k|\ge c-|k|\ge c-\mu.
$$

因此任何同系数修复都必须满足

$$
a(c-\mu)^2\le\eta^2.
\tag{64.23}
$$

但准确恒等式为

$$
c-\mu=
\frac{\varepsilon(c-\varepsilon)}{(1+c)(1+\varepsilon)},
\qquad
\eta=\frac{\varepsilon^2}{1+\varepsilon}.
\tag{64.24}
$$

故条件（64.6）恰好使式（64.23）严格失败。矛盾说明不存在事件误差至多 $\varepsilon$ 的因果修复。

因果修复集合由正性、闭线性约束及固定迹 $\operatorname{Tr}S=2$ 给出，有限维下紧；完整事件误差连续。因此最优值达到，不存在误差至多 $\varepsilon$ 的修复推出严格的 $e(R)>\varepsilon$，证明定理 64.1 的一般条件部分。

### 64.5 一个完整参数区域与维数含义

若 $0<\varepsilon\le1/16$，则

$$
c=\sqrt{1-\varepsilon}>1-\varepsilon\ge\frac{15}{16},
\qquad c-\varepsilon>\frac78,
\qquad1+c<2.
$$

从而

$$
\frac{\varepsilon(1+c)}{c-\varepsilon}<\frac17.
\tag{64.25}
$$

对 $a\ge1/49$，有 $\sqrt a\ge1/7$，所以式（64.6）严格成立；加上 $a<1$，即可应用全部支撑与因果约束。这证明参数区域（64.8）。$\square$

对该区域，末端通道收缩和三维纯候选的已证上界还给

$$
\varepsilon<e(R_{a,\varepsilon})
\le e(R^{(3)}_\varepsilon)<\frac98\varepsilon.
\tag{64.26}
$$

这里没有给混合候选的准确最优值，也没有给统一的正比例间隙下界；严格不等式本身由前述有限维矩阵论证给出。

该结果与第 63 节的低秩早边缘等式相容：候选恰好具有 $\operatorname{rank}R=2$、$\operatorname{rank}M=3$，满足纯量子比特排除定理留下的必要条件。对于 $A=B=2$，第 54 节已证晚输出一维时同系数修复总可行，而上述晚输出二维混合候选已经不可同系数修复。因此在允许混合静态候选的范围，严格间隙的最小晚输出维数是二；若限于纯候选，二维被排除而已有三维反例。

## 追加锚（本行以下为增补区）

## 65. 混合量子比特反例的显式修复与尖锐首阶误差

### 65.1 结论

沿用第 64 节三个量子比特上的混合候选，令

$$
\begin{aligned}
x&=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,\\
z&=|110\rangle,\quad z'=|111\rangle,\quad h=|010\rangle,\\
b&=\sqrt{1-a},\qquad c=\sqrt{1-\varepsilon},\\
r_0&=\sqrt a\,x+cy+\sqrt\varepsilon b\,z,\\
r_1&=b x'-\sqrt{\varepsilon a}\,z',\\
R_{a,\varepsilon}&=|r_0\rangle\langle r_0|+|r_1\rangle\langle r_1|,
\qquad0<a<1.
\end{aligned}
\tag{65.1}
$$

完整 tester 合同、因果修复集合及最优事件响应误差 $e(R)$ 均保持不变。早边缘仍给 $\Delta(R_{a,\varepsilon})=\varepsilon$。

**定理 65.1。** 对 $0<\varepsilon<1-a$，定义

$$
\beta=\sqrt{\frac{1-a-\varepsilon}{1-\varepsilon}},
\qquad
\xi=\sqrt\varepsilon(b-\beta)
=\frac{a\varepsilon^{3/2}}{(1-\varepsilon)(b+\beta)},
\qquad
\zeta=\frac{a\varepsilon^2}{1-\varepsilon}.
\tag{65.2}
$$

则有显式准确上界

$$
\varepsilon\le e(R_{a,\varepsilon})
\le\varepsilon+2(1+\sqrt a)\xi+\zeta.
\tag{65.3}
$$

因此对每个固定 $a\in(0,1)$，

$$
e(R_{a,\varepsilon})
=\varepsilon+O_a(\varepsilon^{3/2}),
\qquad
\lim_{\varepsilon\downarrow0}
\frac{e(R_{a,\varepsilon})}{\varepsilon}=1.
\tag{65.4}
$$

同时，第 64 节的严格反例条件对充分小的正 $\varepsilon$ 成立，故在该范围仍有

$$
0<e(R_{a,\varepsilon})-\varepsilon
=O_a(\varepsilon^{3/2}).
\tag{65.5}
$$

式（65.5）的上界不是对差值首个非零阶或系数的确定；它排除了固定 $a$ 下统一的正比例间隙 $e\ge(1+\kappa)\varepsilon$、$\kappa>0$。

### 65.2 显式因果修复

定义

$$
\begin{aligned}
s_0&=\sqrt a\,x+cy+\sqrt\varepsilon\beta\,z,\\
s_1&=\sqrt{1-a-\varepsilon}\,x'
-\frac{\sqrt{\varepsilon a}}c\,z',\\
S_{a,\varepsilon}
&=|s_0\rangle\langle s_0|+|s_1\rangle\langle s_1|
+\varepsilon|h\rangle\langle h|.
\end{aligned}
\tag{65.6}
$$

该算符显然正。其早输出 $B=0$ 对角质量在 $A=0$ 和 $A=1$ 下分别是

$$
a+(1-a-\varepsilon)=1-\varepsilon,
\qquad c^2=1-\varepsilon.
$$

早输出 $B=1$ 对角质量在两输入下分别是

$$
\varepsilon,
\qquad
\varepsilon\beta^2+\frac{\varepsilon a}{c^2}
=\varepsilon\frac{1-a-\varepsilon+a}{1-\varepsilon}
=\varepsilon.
$$

唯一可能在 $D$ 偏迹后留下的非对角项是 $AB=00$ 与 $AB=11$ 之间，其系数为

$$
\sqrt{\varepsilon a}\left(
\beta-\frac{\sqrt{1-a-\varepsilon}}c\right)=0.
$$

所以

$$
\operatorname{Tr}_D S_{a,\varepsilon}
=I_A\otimes\operatorname{diag}(1-\varepsilon,\varepsilon).
\tag{65.7}
$$

这是合法的归一化因果修复，不需要优化未知矩阵。

### 65.3 完整事件误差的上界

记 $w=\sqrt a\,x+cy$。由

$$
b^2-\beta^2=\frac{a\varepsilon}{1-\varepsilon},
\qquad
\frac{\sqrt{1-a-\varepsilon}}c=\beta,
$$

直接展开得到准确分解

$$
\begin{aligned}
R_{a,\varepsilon}-S_{a,\varepsilon}
={}&\varepsilon(|x'\rangle\langle x'|-|h\rangle\langle h|)\\
&+\xi\bigl(
|w\rangle\langle z|+|z\rangle\langle w|
-\sqrt a\,|x'\rangle\langle z'|
-\sqrt a\,|z'\rangle\langle x'|
\bigr)\\
&+\zeta(|z\rangle\langle z|-|z'\rangle\langle z'|).
\end{aligned}
\tag{65.8}
$$

对任意完整 tester $C,E$，每个 $C$ 标准基对角元位于 $[0,1]$。因此第一行与 $E$ 的配对绝对值至多 $\varepsilon$，第三行至多 $\zeta$。

第二行使用正算子 $E$ 的 Cauchy–Schwarz，以及 $E\preceq C\otimes I_D$。因为 $x,y$ 具有不同的 $D$ 坐标，

$$
\langle w|C\otimes I_D|w\rangle
=a C_{00,00}+c^2C_{10,10}\le1,
$$

其中 $C_{00,00}+C_{10,10}=1$。其他三个标准基向量也满足

$$
\langle z|C\otimes I_D|z\rangle\le1,
\qquad\langle x'|C\otimes I_D|x'\rangle\le1,
\qquad\langle z'|C\otimes I_D|z'\rangle\le1.
$$

于是

$$
|\langle z|E|w\rangle|\le1,
\qquad|\langle z'|E|x'\rangle|\le1.
$$

第二行与 $E$ 的配对绝对值至多 $2(1+\sqrt a)\xi$。三个界对同一个任意 $C,E$ 同时成立，相加给

$$
N(R_{a,\varepsilon}-S_{a,\varepsilon})
\le\varepsilon+2(1+\sqrt a)\xi+\zeta.
\tag{65.9}
$$

结合总响应下界 $e\ge\Delta=\varepsilon$，得到式（65.3）。

### 65.4 极限与严格性的相容

固定 $0<a<1$ 时，$b>0$ 且 $\beta\to b$，所以

$$
\xi=\frac{a}{2\sqrt{1-a}}\varepsilon^{3/2}
+O_a(\varepsilon^{5/2}),
\qquad\zeta=a\varepsilon^2+O_a(\varepsilon^3).
$$

式（65.3）于是给更具体的上界展开

$$
e(R_{a,\varepsilon})
\le\varepsilon+
\frac{a(1+\sqrt a)}{\sqrt{1-a}}\varepsilon^{3/2}
+a\varepsilon^2+O_a(\varepsilon^{5/2}).
\tag{65.10}
$$

这个展开属于显式修复的误差上界，不是未知最优误差的等式展开。上下夹逼证明式（65.4）。这里固定 $a$；误差常数依赖 $a$，显示的系数在 $a\uparrow1$ 时发散，且修复要求 $\varepsilon<1-a$。因此不能将结论当作整个 $a\in(0,1)$ 上的一致极限，也不能直接代入随 $\varepsilon$ 趋近端点的 $a(\varepsilon)$。

严格反例条件是

$$
\sqrt a(c-\varepsilon)>\varepsilon(1+c).
$$

对固定 $a>0$，左侧趋于 $\sqrt a>0$，右侧趋于零，因此充分小的正 $\varepsilon$ 必满足。它与式（65.4）并不冲突：差值严格为正，但相对误差 $e/\Delta$ 趋于一。由此得到式（65.5）。$\square$

同一固定 $a$ 的末端压缩把三维纯候选的 $e/\Delta\to9/8$ 变成混合量子比特族的 $e/\Delta\to1$，同时在每个充分小的非零参数处保留严格间隙。这一区别由两个相同接口问题的解析结论给出，不由有限参数数值拟合推出。混合族差值的尖锐阶数、非零系数及有限参数准确最优值仍未由这里的上界确定。

## 追加锚（本行以下为增补区）

## 66. 混合量子比特反例的二阶修复上界

### 66.1 候选、参数与结论

沿用第 64 节三个量子比特混合候选及完整 tester 事件误差。记

$$
\begin{aligned}
x&=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,\\
z&=|110\rangle,\quad z'=|111\rangle,\quad h=|010\rangle,\\
b&=\sqrt{1-a},\qquad c=\sqrt{1-\varepsilon},\\
r_0&=\sqrt a\,x+cy+\sqrt\varepsilon b\,z,\\
r_1&=b x'-\sqrt{\varepsilon a}\,z',\\
R_{a,\varepsilon}&=|r_0\rangle\langle r_0|+|r_1\rangle\langle r_1|,
\end{aligned}
\tag{66.1}
$$

其中固定 $0<a<1$。它的归一化缺陷仍是 $\Delta=\varepsilon$。现在取

$$
0<\varepsilon\le\frac{1-a}{8}=\frac{b^2}{8},
\tag{66.2}
$$

令 $p$ 为下述二次方程的小根：

$$
p^2-b^2(1+\varepsilon)p+\varepsilon b^2=0.
\tag{66.3}
$$

显式地，

$$
p=\frac{b^2(1+\varepsilon)
-\sqrt{b^4(1+\varepsilon)^2-4b^2\varepsilon}}2,
\qquad s=1-p,
\qquad d=p-\varepsilon.
\tag{66.4}
$$

**定理 66.1。** 参数范围（66.2）保证 $\varepsilon<p\le2\varepsilon<b^2$。在这一范围内有准确上界

$$
\varepsilon\le e(R_{a,\varepsilon})
\le\varepsilon+d\left[
2+\frac{2(\sqrt a+\sqrt\varepsilon b)}{c+\sqrt{1-p}}
\right].
\tag{66.5}
$$

因此对每个固定 $a\in(0,1)$，

$$
e(R_{a,\varepsilon})=\varepsilon+O_a(\varepsilon^2).
\tag{66.6}
$$

在充分小的正 $\varepsilon$ 下，严格反例定理仍给 $e>\varepsilon$，故

$$
0<e(R_{a,\varepsilon})-\varepsilon
=O_a(\varepsilon^2).
\tag{66.7}
$$

这是差值的上界阶数，不宣称差值为 $\Theta_a(\varepsilon^2)$，也不宣称式（66.5）的显式修复必为最优。

### 66.2 小根合法性与因果修复

判别式满足

$$
b^4(1+\varepsilon)^2-4b^2\varepsilon
\ge b^4-4b^2\varepsilon\ge\frac{b^4}{2}>0.
$$

有理化式（66.4）给

$$
p=\frac{2\varepsilon}
{1+\varepsilon+\sqrt{(1+\varepsilon)^2-4\varepsilon/b^2}}
\le2\varepsilon\le\frac{b^2}{4}<b^2.
\tag{66.8}
$$

$p>0$ 由同一式明显成立。二次方程等价于

$$
p(b^2-p)=\varepsilon b^2(1-p)=\varepsilon b^2s,
\qquad
p-\varepsilon=\frac{a\varepsilon p}{b^2-p}>0.
\tag{66.9}
$$

这也证明 $s>0$，且 $d>0$。

定义

$$
\begin{aligned}
s_0&=\sqrt a\,x+\sqrt s\,y+\sqrt\varepsilon b\,z,\\
s_1&=\sqrt{b^2-p}\,x'-\sqrt{\frac{pa}{s}}\,z',\\
S&=|s_0\rangle\langle s_0|+|s_1\rangle\langle s_1|
+p|h\rangle\langle h|.
\end{aligned}
\tag{66.10}
$$

所有根式均合法，$S\succeq0$。$B=0$ 的两个输入对角质量是

$$
a+b^2-p=s,\qquad s.
$$

$B=1$ 的两个输入对角质量是 $p$ 及

$$
\varepsilon b^2+\frac{pa}{s}=p;
$$

最后一个等式来自式（66.9）。偏迹后唯一可能的跨输入非对角项满足

$$
\sqrt{\varepsilon a}\,b
-\sqrt{b^2-p}\sqrt{\frac{pa}{s}}=0,
$$

因为 $p(b^2-p)/s=\varepsilon b^2$。所以

$$
\operatorname{Tr}_D S=I_A\otimes\operatorname{diag}(s,p).
\tag{66.11}
$$

这给出归一化因果修复。式（66.9）同时保证两条跨输入、相同末输出的相干项与原候选完全匹配。

### 66.3 准确差算符与共同 tester 上界

令

$$
w=\sqrt a\,x+\sqrt\varepsilon b\,z,
\qquad
\gamma=c-\sqrt s=\frac{d}{c+\sqrt s}>0.
\tag{66.12}
$$

式（66.10）保持 $r_0$ 在 $x,z$ 上的两个系数，只改变 $y$ 系数。式（66.9）又使 $s_1$ 与 $r_1$ 的交叉项完全相同。因此直接展开得到

$$
\begin{aligned}
R_{a,\varepsilon}-S
={}&p(|x'\rangle\langle x'|-|h\rangle\langle h|)\\
&+d(|y\rangle\langle y|-|z'\rangle\langle z'|)\\
&+\gamma(|w\rangle\langle y|+|y\rangle\langle w|).
\end{aligned}
\tag{66.13}
$$

这里 $y$ 对角差为 $c^2-s=d$；$z'$ 对角差为
$\varepsilon a-pa/s=\varepsilon-p=-d$。

固定任意完整 tester

$$
C\succeq0,\quad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D.
$$

$C$ 的每个标准基对角元都位于 $[0,1]$，所以式（66.13）第一、二行与 $E$ 配对的绝对值分别至多 $p,d$。

对第三行，正性给

$$
|C_{00,11}|\le\sqrt{C_{00,00}C_{11,11}}.
$$

因为 $x,z$ 具有同一个 $D$ 坐标，

$$
\begin{aligned}
\langle w|C\otimes I_D|w\rangle
&\le\left(\sqrt a\sqrt{C_{00,00}}
+\sqrt\varepsilon b\sqrt{C_{11,11}}\right)^2\\
&\le(\sqrt a+\sqrt\varepsilon b)^2.
\end{aligned}
\tag{66.14}
$$

同时 $\langle y|C\otimes I_D|y\rangle=C_{10,10}\le1$。正算子 $E$ 的 Cauchy–Schwarz 不等式及 $E\preceq C\otimes I_D$ 因而给

$$
|\langle y|E|w\rangle|
\le\sqrt{\langle y|E|y\rangle\langle w|E|w\rangle}
\le\sqrt a+\sqrt\varepsilon b.
\tag{66.15}
$$

三个上界始终使用同一个任意 $C,E$。相加可得

$$
|\operatorname{Tr}((R-S)E)|
\le p+d+2\gamma(\sqrt a+\sqrt\varepsilon b)
=\varepsilon+d\left[
2+\frac{2(\sqrt a+\sqrt\varepsilon b)}{c+\sqrt s}
\right].
$$

取全部事件最大值，再与 $\Delta=\varepsilon$ 的下界合并，证明式（66.5）。

### 66.4 固定参数展开与范围

固定 $a\in(0,1)$ 后，小根在 $\varepsilon=0$ 附近解析：式（66.3）对 $p$ 的偏导在 $(0,0)$ 为 $-b^2\ne0$。直接展开得到

$$
p=\varepsilon+\frac{a}{1-a}\varepsilon^2+O_a(\varepsilon^3),
\qquad
\gamma=\frac{a}{2(1-a)}\varepsilon^2+O_a(\varepsilon^3).
\tag{66.16}
$$

故式（66.5）的上界具有展开

$$
e(R_{a,\varepsilon})
\le\varepsilon+
\frac{a(2+\sqrt a)}{1-a}\varepsilon^2
+\frac{a}{\sqrt{1-a}}\varepsilon^{5/2}
+O_a(\varepsilon^3).
\tag{66.17}
$$

这是一个显式可行修复的上界展开，不能把其中的系数当作最优误差的系数。式（66.17）与 $e\ge\varepsilon$ 给式（66.6）。严格反例条件对每个固定 $a>0$ 在充分小的正 $\varepsilon$ 下成立，得到式（66.7）。$\square$

该修复的参数区间和展开常数依赖 $a$；当 $a\uparrow1$ 时，允许的 $\varepsilon$ 区间缩小，显示系数发散。这不是整个 $a\in(0,1)$ 上的一致二阶估计。差值的匹配下界、尖锐阶数、最优系数和有限参数准确最优值仍需另证。

## 追加锚（本行以下为增补区）

## 67. 混合量子比特候选的相位阻尼阈值

### 67.1 相位阻尼保持同一早边缘

沿用第64节的完整 tester、因果修复与混合候选。本节对该族施加真实末端相位阻尼，给出同系数修复区间和严格间隙区间，并由这两个区间确定转变位置的首阶。

设 $0<a<1$、$0<\varepsilon<1$，$c=\sqrt{1-\varepsilon}$，

$$
x=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,
\quad z=|110\rangle,\quad z'=|111\rangle,\quad h=|010\rangle,
$$

$$
u=\sqrt a\,x+\sqrt{\varepsilon(1-a)}\,z,
\qquad v=\sqrt{1-a}\,x'-\sqrt{\varepsilon a}\,z'.
$$

对 $0\le\lambda\le1$ 定义

$$
R_\lambda=|u\rangle\langle u|+|v\rangle\langle v|
+c^2|y\rangle\langle y|
+\lambda c(|u\rangle\langle y|+|y\rangle\langle u|).
$$

这是对 $R_1=R_{a,\varepsilon}$ 的末输出 $D$ 作相位阻尼所得：保留两个对角块，将异 $D$ 坐标块乘以 $\lambda$。该通道是恒等与完全退相干的凸组合。因此每个 $R_\lambda$ 正、具有同一早边缘 $M_\varepsilon$，归一化缺陷恒为 $\Delta=\varepsilon$。

记

$$
\mu=\frac1{1+\varepsilon},\qquad
p=\frac{\varepsilon}{1+\varepsilon},\qquad
\eta=\mu-c^2=\frac{\varepsilon^2}{1+\varepsilon}.
$$

### 67.2 显式可修复区间

**命题 67.1（阻尼后的显式同系数修复）。** 若 $\lambda c\le\mu$，则 $e(R_\lambda)=\varepsilon$。

**证明。** 取

$$
S_\lambda=\mu(|u\rangle\langle u|+|v\rangle\langle v|+|y\rangle\langle y|)
+p|h\rangle\langle h|
+\lambda c(|u\rangle\langle y|+|y\rangle\langle u|).
$$

在列向量 $u,y$ 所定的合同变换下，相关系数矩阵是

$$
\begin{pmatrix}\mu&\lambda c\\\lambda c&\mu\end{pmatrix}\succeq0.
$$

其余两项亦正，故 $S_\lambda\succeq0$。$u,y$ 的 $D$ 坐标不同，交叉项的 $D$ 偏迹为零；$u,v$ 的 $00,11$ 交叉项相消。于是

$$
\operatorname{Tr}_D S_\lambda
=\mu|00\rangle\langle00|+p|01\rangle\langle01|
+\mu|10\rangle\langle10|+p|11\rangle\langle11|
=I_A\otimes\operatorname{diag}(\mu,p).
$$

这是因果修复。其差算符与 $\lambda$ 无关：

$$
R_\lambda-S_\lambda=P-N,
\qquad P=p(|u\rangle\langle u|+|v\rangle\langle v|),
\quad N=\eta|y\rangle\langle y|+p|h\rangle\langle h|.
$$

对同一任意完整 tester $C,E$，$P,N\succeq0$ 及 $0\preceq E\preceq C\otimes I_D$ 给

$$
0\le\operatorname{Tr}(PE)\le p(C_{00,00}+\varepsilon C_{11,11})\le p(1+\varepsilon)=\varepsilon,
$$

$$
0\le\operatorname{Tr}(NE)\le\eta C_{10,10}+pC_{01,01}\le\eta+p=\varepsilon.
$$

因此配对差的绝对值至多 $\varepsilon$。总事件给普遍下界 $e\ge\Delta=\varepsilon$，故等式成立。

特别地，$\lambda=0$ 总能同系数修复；此时 $D$ 已经典化，但各 $D$ 条件块仍含有 $AB$ 的非对角相干。本命题是该明确族的结论。

### 67.3 严格间隙区间

**命题 67.2（阻尼后仍保留严格间隙的充分条件）。** 若 $\lambda c>\mu+\eta/\sqrt a$，则 $e(R_\lambda)>\varepsilon$。

**证明。** 反设存在因果 $S$，其完整事件误差至多 $\varepsilon$。第64节两个总事件 $C_+,C_-$ 及其饱和压缩保持原样：$R_+=uu^*+vv^*$、$R_-=c^2yy^*$ 都不依赖 $\lambda$。同一支撑、偏迹和归一化论证给

$$
S_{x,x}=\mu a,\quad S_{x',x'}=\mu(1-a),\quad
c^2\le s:=S_{y,y}\le\mu,\quad
k:=S_{x,y}/\sqrt a,\quad |k|^2\le\mu s\le\mu^2.
$$

对 $C_q=\operatorname{diag}(q,1,1-q,0)$，$0<q<1$，加权 $x,y$ 主块变为

$$
B_q=\begin{pmatrix}
apq&\sqrt{aq(1-q)}(\lambda c-k)\\
\sqrt{aq(1-q)}(\lambda c-\overline k)&(c^2-s)(1-q)
\end{pmatrix}.
$$

取该块正谱投影加 $x'$ 投影，再取其互补事件。其总响应仍为 $-\varepsilon(1-q)$，故同样得到

$$
\max\{0,\lambda_{\max}(B_q)\}\le q(\eta+ap).
$$

由 $q(\eta+ap)I-B_q\succeq0$ 的行列式非负，除以 $q$ 并令 $q\downarrow0$，得到

$$
a|\lambda c-k|^2\le\eta(s-c^2)\le\eta^2.
$$

而假设 $\lambda c>\mu+\eta/\sqrt a$ 及 $|k|\le\mu$ 给
$\sqrt a|\lambda c-k|\ge\sqrt a(\lambda c-\mu)>\eta$，矛盾。

因果修复集合紧、误差连续，最优值达到；所以不可能达到误差 $\varepsilon$ 意味着最优值严格大于它。

### 67.4 转变位置的二阶夹逼

**定理 67.3（相位阻尼转变的首阶定位）。** 固定满足 $c>\mu+\eta/\sqrt a$ 的 $(a,\varepsilon)$；例如第64节全部参数区域 $0<\varepsilon\le1/16$、$1/49\le a<1$。则存在唯一转变位置 $\lambda_*\in(0,1)$，使

$$
e(R_\lambda)=\varepsilon\quad\Longleftrightarrow\quad0\le\lambda\le\lambda_*,
$$

并且

$$
\frac\mu c\le\lambda_*\le\frac{\mu+\eta/\sqrt a}{c}<1.
$$

**证明。** 若 $0\le\lambda'\le\lambda$ 且 $\lambda>0$，对 $R_\lambda$ 再施阻尼系数 $\lambda'/\lambda$ 的末端 CPTP 通道就得到 $R_{\lambda'}$。末端数据处理给 $e(R_{\lambda'})\le e(R_\lambda)$。函数 $e$ 对输入连续：三角不等式给 $|e(R)-e(R')|\le N(R-R')$，有限维下右侧连续。因而同系数修复集合是闭初段；前两个命题给其非空性、真子区间性与两端夹逼。

对每个固定 $a\in(0,1)$，充分小的正 $\varepsilon$ 满足上述条件，且

$$
\frac\mu c=1-\frac\varepsilon2+\frac78\varepsilon^2+O(\varepsilon^3),
\qquad
\frac{\eta}{c\sqrt a}=\frac{\varepsilon^2}{\sqrt a}+O_a(\varepsilon^3).
$$

所以

$$
\lambda_*=1-\frac\varepsilon2+O_a(\varepsilon^2),
\qquad
1-\lambda_*=\frac\varepsilon2+O_a(\varepsilon^2).
$$

这里确定的是消除严格间隙所需相位阻尼强度的首阶，而不是准确转变点。对固定 $\lambda<1$，充分小 $\varepsilon$ 时已经处于可同系数修复区间；$\lambda=1$ 却在每个充分小非零参数处保留严格间隙。所有比较保留同一早边缘、同一完整 tester 合同及同一末端处理权限。

## 追加锚（本行以下为增补区）

## 68. 对称压缩混合反例的匹配二阶间隙下界

### 68.1 候选与结论

固定三个量子比特 $A,B,D$，次序为 $A\otimes B\otimes D$，使用全部量子 tester

$$
C\succeq0,\quad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D,
$$

以及归一化因果修复 $S\succeq0$、$\operatorname{Tr}_D S=I_A\otimes\sigma$、$\operatorname{Tr}\sigma=1$。取

$$
x=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,
\quad z=|110\rangle,\quad z'=|111\rangle,
$$

并固定

$$
0<\varepsilon\le\frac1{16},\qquad c=\sqrt{1-\varepsilon},
\qquad
R_\varepsilon=
\left|\frac{x+\sqrt\varepsilon z}{\sqrt2}+cy\right\rangle
\left\langle\frac{x+\sqrt\varepsilon z}{\sqrt2}+cy\right|
+\frac12|x'-\sqrt\varepsilon z'\rangle
\langle x'-\sqrt\varepsilon z'|.
\tag{68.1}
$$

这是前述混合严格反例的 $a=1/2$ 子族。记完整事件最优修复误差为 $e_\varepsilon$；早边缘给 $\Delta=\varepsilon$。

**定理 68.1（对称压缩的二阶间隙）。** 对整个 $0<\varepsilon\le1/16$，有显式严格下界

$$
e_\varepsilon>\varepsilon+\frac{\varepsilon^2}{1024}.
\tag{68.2}
$$

与第66节的二阶修复上界合并，得到

$$
\frac{\varepsilon^2}{1024}
<e_\varepsilon-\varepsilon
\le\left(2+\frac1{\sqrt2}\right)\varepsilon^2
+\frac1{\sqrt2}\varepsilon^{5/2}+O(\varepsilon^3).
\tag{68.3}
$$

因此 $e_\varepsilon-\varepsilon=\Theta(\varepsilon^2)$；差值的二阶量级已定，而尖锐系数及有限参数准确最优值仍未由这些界确定。

### 68.2 总事件近饱和控制核方向质量

反设存在因果 $S$ 满足

$$
N(R_\varepsilon-S)\le\varepsilon+g,
\qquad0\le g\le\frac{\varepsilon^2}{1024}.
\tag{68.4}
$$

令

$$
C_+=|00\rangle\langle00|+|11\rangle\langle11|,
\qquad\Pi_+=C_+\otimes I_D,
\quad S_+=\Pi_+S\Pi_+,
\quad R_+=\Pi_+R_\varepsilon\Pi_+.
$$

归一化给 $\operatorname{Tr}S_+=1$、$\operatorname{Tr}R_+=1+\varepsilon$。$R_+-S_+$ 的正谱投影是合法事件，所以它的正谱和至多 $\varepsilon+g$。总迹等于 $\varepsilon$，因此负谱绝对值之和至多 $g$。

记 $K$ 为 $\operatorname{ran}\Pi_+$ 内 $R_+$ 的核投影，则

$$
\operatorname{Tr}(KS_+)=-\operatorname{Tr}(K(R_+-S_+))\le g.
\tag{68.5}
$$

这是对同一实际修复的核方向正质量的界，没有把小负谱当成精确正性。

在四维 $\operatorname{ran}\Pi_+$ 中取正交归一基

$$
\begin{aligned}
\xi_0&=\frac{x+\sqrt\varepsilon z}{\sqrt{1+\varepsilon}},
&\nu_0&=\frac{\sqrt\varepsilon x-z}{\sqrt{1+\varepsilon}},\\
\xi_1&=\frac{x'-\sqrt\varepsilon z'}{\sqrt{1+\varepsilon}},
&\nu_1&=\frac{\sqrt\varepsilon x'+z'}{\sqrt{1+\varepsilon}}.
\end{aligned}
\tag{68.6}
$$

$\xi_0,\xi_1$ 张成 $R_+$ 的像，$\nu_0,\nu_1$ 张成其核。定义

$$
m_j=\langle\xi_j|S|\xi_j\rangle,
\quad k_j=\langle\nu_j|S|\nu_j\rangle,
\quad f_j=\langle\xi_j|S|\nu_j\rangle
\quad(j=0,1).
$$

不假设其他矩阵元为零。核方向正质量和总迹给

$$
0\le k_0+k_1\le g,\qquad m_0+m_1=1-k_0-k_1.
$$

现在同时使用误差假设对同一个差算符的约束。记 $X=R_+-S_+$。其负谱绝对值之和至多 $g$，所以 $X+gI\succeq0$；其正谱和至多 $\varepsilon+g$，所以

$$
\langle\xi_j|X|\xi_j\rangle\le\varepsilon+g.
$$

$X+gI$ 在 $\xi_j,\nu_j$ 上的二阶主子式非负，而其核方向对角为 $g-k_j$、交叉项为 $-f_j$。因此

$$
\begin{aligned}
|f_j|^2
&\le(\langle\xi_j|X|\xi_j\rangle+g)(g-k_j)
\le(\varepsilon+2g)(g-k_j)\\
&\le(\varepsilon+2g)g,\\
|f_0|+|f_1|&\le2\sqrt{(\varepsilon+2g)g}
\le L:=2\sqrt{2\varepsilon g}.
\end{aligned}
\tag{68.7}
$$

最后一步使用式（68.4）与 $\varepsilon\le1/16$，从而 $2g\le\varepsilon$。这一估计把总事件近饱和与实际修复的核方向质量同时用于同一个矩阵主子式。

### 68.3 因果偏迹与矩阵元的定量约束

因果条件给 $S_{x,z}+S_{x',z'}=0$。在基（68.6）中取实部，得到

$$
\sqrt\varepsilon\,[(m_0-m_1)-(k_0-k_1)]
=(1-\varepsilon)\operatorname{Re}(f_0-f_1).
$$

因此

$$
|m_0-m_1|\le g+
\frac{1-\varepsilon}{\sqrt\varepsilon}L.
\tag{68.8}
$$

记

$$
\mu=\frac1{1+\varepsilon},\qquad p_*=\frac{\varepsilon}{1+\varepsilon},
\qquad A=S_{x,x},\qquad p=\sigma_{11}.
$$

由式（68.6）直接展开，

$$
\begin{aligned}
A&=\frac{m_0+\varepsilon k_0+2\sqrt\varepsilon\operatorname{Re}f_0}{1+\varepsilon},\\
p&=\frac{\varepsilon(m_0+m_1)+(k_0+k_1)
-2\sqrt\varepsilon\operatorname{Re}(f_0+f_1)}{1+\varepsilon}.
\end{aligned}
\tag{68.9}
$$

式（68.7）、（68.8）从而给

$$
\begin{aligned}
\delta_A:=\left|A-\frac\mu2\right|
&\le g+\frac{1+3\varepsilon}{2(1+\varepsilon)\sqrt\varepsilon}L
\le g+\frac{19\sqrt2}{16}\sqrt g,\\
\delta_p:=|p-p_*|&\le g+2\sqrt\varepsilon L
\le g+4\sqrt2\,\varepsilon\sqrt g.
\end{aligned}
\tag{68.10}
$$

在式（68.4）的参数范围内，使用 $\sqrt2<3/2$ 可以取完全显式的简化界

$$
\begin{aligned}
\delta_A
&\le\left(\frac{57}{1024}+\frac1{16384}\right)\varepsilon
<\frac\varepsilon{16},\\
\delta_p
&\le\left(\frac3{16}+\frac1{1024}\right)\varepsilon^2
<\frac{\varepsilon^2}{4}.
\end{aligned}
\tag{68.11}
$$

再令

$$
s=S_{y,y},\qquad k=\sqrt2\,S_{x,y}.
$$

因果偏迹和正性给 $s\le1-p$，$S$ 在 $x,y$ 上的主子式给 $|k|\le\sqrt{2As}$。算术—几何均值不等式于是给

$$
|k|\le A+\frac s2
\le\mu+\delta_A+\frac{\delta_p}{2}.
\tag{68.12}
$$

另一方面，

$$
c-\mu=
\frac{\varepsilon(c-\varepsilon)}{(1+c)(1+\varepsilon)}
>\frac7{17}\varepsilon,
$$

因为 $c-\varepsilon>7/8$ 且 $(1+c)(1+\varepsilon)<17/8$。由式（68.11）、（68.12），

$$
\begin{aligned}
|c-k|&\ge c-|k|\\
&>\left(\frac7{17}-\frac1{16}-\frac1{128}\right)\varepsilon
>\frac\varepsilon3.
\end{aligned}
\tag{68.13}
$$

这里仍允许 $S_{x,y}$ 为复数。

### 68.4 同一反馈下的二阶正性矛盾

对 $0<q<1$，取

$$
C_q=\operatorname{diag}(q,1,1-q,0),
\quad
H_q=(C_q^{1/2}\otimes I_D)(R_\varepsilon-S)(C_q^{1/2}\otimes I_D).
$$

$H_q$ 在 $x,y$ 上的主块为

$$
B_q=
\begin{pmatrix}
q(1/2-A)&\sqrt{q(1-q)/2}\,(c-k)\\
\sqrt{q(1-q)/2}\,(c-\overline k)&(c^2-s)(1-q)
\end{pmatrix}.
\tag{68.14}
$$

记 $\lambda_q=\max\{0,\lambda_{\max}(B_q)\}$。在加权空间中选择一个对应最大非负特征值的投影（若无正特征值则取零），并加上正交的 $x'$ 投影，得到合法事件。它的响应为

$$
\lambda_q+q(1/2-S_{x',x'})
=\lambda_q+q(A+p-1/2),
$$

其中用了 $S_{x',x'}=1-p-A$。同一 $C_q$ 的总响应差为 $-\varepsilon(1-q)$；将所选事件从总事件中取补，误差假设（68.4）给

$$
\lambda_q\le qF+g,
\qquad F=\varepsilon-p+\frac12-A.
\tag{68.15}
$$

这一步不需要假设所选事件的响应为正，也不要求 $H_q$ 在各子空间间没有相干。

式（68.15）蕴含 $(qF+g)I_2-B_q\succeq0$，所以

$$
\bigl[q(\varepsilon-p)+g\bigr]
\bigl[qF+g+(s-c^2)(1-q)\bigr]
\ge\frac{q(1-q)}2|c-k|^2.
\tag{68.16}
$$

现在选取同一个具体反馈参数 $q=\varepsilon$。由式（68.11），

$$
\varepsilon-p\le\varepsilon-p_*+\delta_p<2\varepsilon^2,
\qquad s-c^2\le\varepsilon-p<2\varepsilon^2.
$$

并且

$$
F\le2\varepsilon^2+\frac{p_*}{2}+\delta_A
<2\varepsilon^2+\frac\varepsilon2+\frac\varepsilon{16}
\le\frac{11}{16}\varepsilon<\varepsilon.
$$

式（68.16）左侧的两个因子由正性非负。第一个因子满足

$$
q(\varepsilon-p)+g
<2\varepsilon^3+\frac{\varepsilon^2}{1024}
\le\left(\frac18+\frac1{1024}\right)\varepsilon^2
<\frac{\varepsilon^2}{7}.
$$

第二个因子严格小于

$$
\varepsilon^2+g+2\varepsilon^2<4\varepsilon^2.
$$

故左侧严格小于

$$
\frac47\varepsilon^4\le\frac1{28}\varepsilon^3.
$$

式（68.13）却使其右侧严格大于

$$
\frac{\varepsilon(1-\varepsilon)}2\left(\frac\varepsilon3\right)^2
\ge\frac5{96}\varepsilon^3
>\frac1{28}\varepsilon^3.
$$

矛盾。由此排除所有满足式（68.4）的因果修复。

因果修复集合在有限维下紧，事件误差连续，所以最小值达到。排除误差至多 $\varepsilon+\varepsilon^2/1024$ 的全部修复，便得到严格下界（68.2）。$\square$

### 68.5 尖锐阶数与未定系数

该结果对 $a=1/2$、$0<\varepsilon\le1/16$ 给出一个显式、非零、随参数变化的间隙下界。证明使用同一修复在总事件和 $q=\varepsilon$ 反馈下必须同时满足的约束，没有把分别可达的最优值拼接。

与第 66 节的二阶上界合并，差值的尖锐阶数确定为二阶。下界常数 $1/1024$ 和上界系数仍未匹配，不能据此给出极限系数或有限参数准确最优值。证明限定于 $a=1/2$；其他固定 $a$ 的匹配下界及随参数变化的统一性均需另证。

## 追加锚（本行以下为增补区）

## 69. 每个固定压缩参数的匹配二阶间隙

### 69.1 候选、显式常数与结论

沿用第 64、66 节三个量子比特 $A,B,D$ 的混合候选，张量次序为 $A\otimes B\otimes D$。明确写成

$$
\begin{aligned}
x&=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,\\
z&=|110\rangle,\quad z'=|111\rangle,\\
b&=\sqrt{1-a},\qquad c=\sqrt{1-\varepsilon},\\
u&=\sqrt a\,x+\sqrt\varepsilon b\,z,\qquad
v=b x'-\sqrt{\varepsilon a}\,z',\\
R_{a,\varepsilon}&=|u+cy\rangle\langle u+cy|+|v\rangle\langle v|.
\end{aligned}
\tag{69.1}
$$

其早边缘为

$$
\operatorname{Tr}_D R_{a,\varepsilon}
=|00\rangle\langle00|+(1-\varepsilon)|10\rangle\langle10|
+\varepsilon|11\rangle\langle11|,
$$

归一化缺陷是 $\Delta=\varepsilon$。误差仍对全部量子 tester 事件取最大值：

$$
\begin{gathered}
C\succeq0,\qquad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D,\\
N(X)=\max_{C,E}|\operatorname{Tr}(XE)|,
\qquad e(R)=\min_{S\ \mathrm{causal}}N(R-S).
\end{gathered}
\tag{69.2}
$$

这里因果修复满足 $S\succeq0$、$\operatorname{Tr}_D S=I_A\otimes\sigma$、$\sigma\succeq0$、$\operatorname{Tr}\sigma=1$；不限制事件的非对角元或修复的相干项。

**定理 69.1。** 对每个固定 $0<a<1$，令

$$
m=\min(a,1-a),\qquad
\kappa_a=\left(\frac{am}{256}\right)^2>0.
\tag{69.3}
$$

则

$$
e(R_{a,\varepsilon})>\varepsilon+\kappa_a\varepsilon^2
\qquad\left(0<\varepsilon\le\frac{\sqrt a}{16}\right).
\tag{69.4}
$$

与第 66 节的修复上界合并，在共同区间

$$
0<\varepsilon\le\min\left(\frac{\sqrt a}{16},\frac{1-a}{8}\right)
\tag{69.5}
$$

上有一个完全显式的双侧估计

$$
\kappa_a\varepsilon^2
<e(R_{a,\varepsilon})-\varepsilon
\le\frac{16a}{1-a}\varepsilon^2.
\tag{69.6}
$$

因此

$$
e(R_{a,\varepsilon})-\varepsilon=\Theta_a(\varepsilon^2)
\qquad(\varepsilon\downarrow0)
\tag{69.7}
$$

对每个固定 $a\in(0,1)$ 成立。两个常数和允许区间依赖 $a$；这不是包含 $a\downarrow0$ 或 $a\uparrow1$ 的一致估计。对称情形第 68 节的下界常数 $1/1024$ 比式（69.3）在 $a=1/2$ 的值更强。

### 69.2 近饱和、支撑方向与核方向

固定 $a$ 和式（69.4）的参数范围。反设存在因果修复 $S$ 满足

$$
N(R_{a,\varepsilon}-S)\le\varepsilon+g,
\qquad0\le g\le\kappa_a\varepsilon^2.
\tag{69.8}
$$

因为 $0<a<1$，以下始终有 $\varepsilon\le1/16$、$m\le1/2$、$g\le\varepsilon^2$。取

$$
C_+=|00\rangle\langle00|+|11\rangle\langle11|,
\qquad\Pi_+=C_+\otimes I_D,
$$

并记 $R_+=\Pi_+R_{a,\varepsilon}\Pi_+$、$S_+=\Pi_+S\Pi_+$、$X=R_+-S_+$。因果归一化给

$$
\operatorname{Tr}R_+=1+\varepsilon,\qquad
\operatorname{Tr}S_+=1,\qquad\operatorname{Tr}X=\varepsilon.
$$

$X$ 的正谱投影是合法事件，所以正谱和至多 $\varepsilon+g$，负谱绝对值之和至多 $g$。在 $\operatorname{ran}\Pi_+$ 上，

$$
X+gI\succeq0,
\qquad\langle\xi|X|\xi\rangle\le\varepsilon+g
\quad\text{对每个单位向量 }\xi.
\tag{69.9}
$$

若 $K$ 是该四维空间中 $R_+$ 的核投影，则

$$
\operatorname{Tr}(KS_+)=-\operatorname{Tr}(KX)\le g.
\tag{69.10}
$$

令

$$
\alpha=a+\varepsilon b^2,\qquad
\beta=b^2+\varepsilon a.
$$

在同一四维空间内取正交归一基

$$
\begin{aligned}
\xi_0&=\frac{\sqrt a\,x+\sqrt\varepsilon b\,z}{\sqrt\alpha},
&\nu_0&=\frac{\sqrt\varepsilon b\,x-\sqrt a\,z}{\sqrt\alpha},\\
\xi_1&=\frac{b x'-\sqrt{\varepsilon a}\,z'}{\sqrt\beta},
&\nu_1&=\frac{\sqrt{\varepsilon a}\,x'+b z'}{\sqrt\beta}.
\end{aligned}
\tag{69.11}
$$

$\xi_0,\xi_1$ 张成 $R_+$ 的像，$\nu_0,\nu_1$ 张成其核。定义

$$
m_j=\langle\xi_j|S|\xi_j\rangle,\qquad
k_j=\langle\nu_j|S|\nu_j\rangle,\qquad
f_j=\langle\xi_j|S|\nu_j\rangle,
\qquad\omega=k_0+k_1.
$$

正性、总迹与式（69.10）给

$$
0\le\omega\le g,\qquad m_0+m_1=1-\omega.
\tag{69.12}
$$

$X+gI$ 在 $\xi_j,\nu_j$ 上的二阶主子式给

$$
|f_j|^2\le(\varepsilon+2g)(g-k_j).
$$

从而，记 $L=|f_0|+|f_1|$，有

$$
L\le2\sqrt{(\varepsilon+2g)g}\le3\sqrt{\varepsilon g}.
\tag{69.13}
$$

最后一步使用 $g\le\varepsilon^2$、$\varepsilon\le1/16$，故 $\varepsilon+2g\le(9/8)\varepsilon$。这些估计全部作用于同一个实际修复；其他矩阵元仍可任意。

### 69.3 不等长支撑方向与因果约束

因果条件给 $S_{x,z}+S_{x',z'}=0$。用式（69.11）展开并取实部，得到

$$
\sqrt{\varepsilon a b^2}
\left[\frac{m_0-k_0}{\alpha}-\frac{m_1-k_1}{\beta}\right]
=\frac{a-\varepsilon b^2}{\alpha}\operatorname{Re}f_0
-\frac{b^2-\varepsilon a}{\beta}\operatorname{Re}f_1.
\tag{69.14}
$$

设

$$
r_0=\frac{m_0}{\alpha},\qquad r_1=\frac{m_1}{\beta},
\qquad D_0=r_0-r_1,\qquad\mu=\frac1{1+\varepsilon}.
$$

因为 $\alpha,\beta\ge m$、$\sqrt{ab^2}\ge m$，且式（69.14）右侧的两个实数系数绝对值均不超过 $1$，所以

$$
|D_0|\le\frac{g}{m}
+\frac{L}{\sqrt\varepsilon\sqrt{ab^2}}
\le\frac{g+3\sqrt g}{m}
\le\frac{5\sqrt g}{m}.
\tag{69.15}
$$

这里 $g\le1$，故 $g\le\sqrt g$；最后的常数保留了余量。又因

$$
\alpha+\beta=1+\varepsilon,
\qquad\alpha r_0+\beta r_1=1-\omega,
$$

可准确解得

$$
r_0-\mu=-\mu\omega+\beta\mu D_0,
\qquad r_1-\mu=-\mu\omega-\alpha\mu D_0.
$$

$\alpha\mu,\beta\mu\le1$，因此

$$
|r_j-\mu|\le\frac{6\sqrt g}{m}\qquad(j=0,1).
\tag{69.16}
$$

记

$$
A=S_{x,x},\qquad p=\sigma_{11},\qquad p_*=\varepsilon\mu.
$$

基变换（69.11）直接给

$$
\begin{aligned}
A={}&a r_0+\frac{\varepsilon b^2}{\alpha}k_0
+\frac{2\sqrt{\varepsilon ab^2}}{\alpha}\operatorname{Re}f_0,\\
p={}&\varepsilon b^2r_0+\varepsilon ar_1
+\frac a\alpha k_0+\frac{b^2}\beta k_1\\
&-2\sqrt{\varepsilon ab^2}
\left(\frac{\operatorname{Re}f_0}{\alpha}
+\frac{\operatorname{Re}f_1}{\beta}\right).
\end{aligned}
\tag{69.17}
$$

对于第一式，$\varepsilon b^2/\alpha\le1$，且算术—几何均值不等式给 $2\sqrt{\varepsilon ab^2}/\alpha\le1$。式（69.13）、（69.16）于是给

$$
\begin{aligned}
\delta_A:=|A-a\mu|
&\le\frac{6a\sqrt g}{m}+g+3\sqrt{\varepsilon g}\\
&\le\frac{6\sqrt g}{m}+\frac74\sqrt g
\le\frac{7\sqrt g}{m}.
\end{aligned}
\tag{69.18}
$$

最后两步用了 $g\le\sqrt g$、$\sqrt\varepsilon\le1/4$ 及 $m\le1/2$。对于第二式，$a/\alpha,b^2/\beta\le1$，且 $\sqrt{ab^2}\le1$，所以

$$
\begin{aligned}
\delta_p:=|p-p_*|
&\le\frac{6\varepsilon\sqrt g}{m}+g
+\frac{2\sqrt\varepsilon}{m}L\\
&\le g+\frac{12\varepsilon\sqrt g}{m}.
\end{aligned}
\tag{69.19}
$$

由式（69.3）、（69.8），$\sqrt g\le am\varepsilon/256$，故

$$
\delta_A\le\frac{7a}{256}\varepsilon,
\qquad
\delta_p\le\left(\kappa_a+\frac{3a}{64}\right)\varepsilon^2
<\frac{\varepsilon^2}{16}.
\tag{69.20}
$$

其中 $\kappa_a\le a/65536\le1/65536$，所以最后一个严格不等式对全部 $0<a<1$ 成立。

### 69.4 无法同时消去的相干差

令

$$
s=S_{y,y},\qquad k=\frac{S_{x,y}}{\sqrt a}.
$$

因果偏迹与正性给 $s\le1-p$，而 $S$ 在 $x,y$ 上的二阶主子式给 $|k|\le\sqrt{As/a}$。于是

$$
\begin{aligned}
|k|&\le\frac{A/a+s}{2}
\le\mu+\frac{\delta_A}{2a}+\frac{\delta_p}{2},\\
\frac{\delta_A}{2a}+\frac{\delta_p}{2}
&<\frac7{512}\varepsilon+\frac{\varepsilon^2}{32}
\le\frac\varepsilon{64}.
\end{aligned}
\tag{69.21}
$$

在 $0<\varepsilon\le1/16$ 上，$c-\varepsilon>7/8$、$(1+c)(1+\varepsilon)<17/8$，所以

$$
c-\mu
=\frac{\varepsilon(c-\varepsilon)}{(1+c)(1+\varepsilon)}
>\frac7{17}\varepsilon.
$$

因此，对允许任意复相位的 $k$，

$$
|c-k|\ge c-|k|
>\left(\frac7{17}-\frac1{64}\right)\varepsilon
>\frac\varepsilon3.
\tag{69.22}
$$

### 69.5 一个具体反馈下的行列式矛盾

对 $0<q<1$，选择合法反馈

$$
C_q=\operatorname{diag}(q,1,1-q,0),
\qquad
H_q=(C_q^{1/2}\otimes I_D)(R_{a,\varepsilon}-S)
(C_q^{1/2}\otimes I_D).
$$

$H_q$ 在 $x,y$ 上的主块为

$$
B_q=\begin{pmatrix}
q(a-A)&\sqrt{aq(1-q)}(c-k)\\
\sqrt{aq(1-q)}(c-\overline k)&(c^2-s)(1-q)
\end{pmatrix}.
\tag{69.23}
$$

令 $\lambda_q=\max(0,\lambda_{\max}(B_q))$。在加权空间选择对应最大正特征值的投影；若无正特征值则取零。将它与正交的 $x'$ 投影相加，得到某个 $0\preceq F_q\preceq I$，从而

$$
E_q=(C_q^{1/2}\otimes I_D)F_q(C_q^{1/2}\otimes I_D)
$$

是合法事件。因为 $S_{x',x'}=1-p-A$，该事件的响应差为

$$
\operatorname{Tr}((R_{a,\varepsilon}-S)E_q)
=\lambda_q+q(A+p-a).
$$

同一 $C_q$ 的总响应差是 $-\varepsilon(1-q)$。将所选事件取补，式（69.8）的误差界给

$$
\lambda_q\le qF+g,
\qquad F=\varepsilon-p+a-A.
\tag{69.24}
$$

这一推导不预设所选事件的响应符号，也不要求 $H_q$ 的其他块或跨块矩阵元为零。

式（69.24）蕴含 $(qF+g)I_2-B_q\succeq0$；取行列式可得

$$
\bigl[q(\varepsilon-p)+g\bigr]
\bigl[qF+g+(s-c^2)(1-q)\bigr]
\ge aq(1-q)|c-k|^2.
\tag{69.25}
$$

左侧两个因子均非负。现取同一个具体参数 $q=\varepsilon$。式（69.20）给

$$
\varepsilon-p\le\frac{\varepsilon^2}{1+\varepsilon}+\delta_p
<2\varepsilon^2,
\qquad s-c^2\le\varepsilon-p<2\varepsilon^2.
$$

同时

$$
\begin{aligned}
F&\le2\varepsilon^2+a(1-\mu)+\delta_A\\
&\le2\varepsilon^2+\frac{263a}{256}\varepsilon
\le\frac{295}{256}\varepsilon<2\varepsilon.
\end{aligned}
$$

因此式（69.25）第一个因子严格小于 $\varepsilon^2(2\varepsilon+\kappa_a)$，第二个因子严格小于 $5\varepsilon^2$，左侧严格小于

$$
5\varepsilon^4(2\varepsilon+\kappa_a).
\tag{69.26}
$$

另一方面，式（69.22）使右侧严格大于

$$
a\varepsilon(1-\varepsilon)\frac{\varepsilon^2}{9}
\ge\frac{5a}{48}\varepsilon^3.
\tag{69.27}
$$

式（69.4）的参数范围与 $\kappa_a\le a/65536$ 保证

$$
\varepsilon(2\varepsilon+\kappa_a)
\le\frac a{128}+\frac a{65536}<\frac a{48}.
\tag{69.28}
$$

故式（69.26）严格小于式（69.27），与式（69.25）矛盾。

这排除了全部满足式（69.8）的因果修复。有限维因果修复集合是紧集，事件误差连续，最小值达到。因此所有修复均不能达到误差 $\varepsilon+\kappa_a\varepsilon^2$ 或更小，便得到严格下界（69.4）。

### 69.6 与上界配合及端点边界

在式（69.5）的共同区间，调用第 66 节的显式修复。其参数满足 $\varepsilon<p\le2\varepsilon$ 以及

$$
p-\varepsilon=\frac{a\varepsilon p}{b^2-p}
\le\frac{8a}{3b^2}\varepsilon^2,
$$

其中用了 $\varepsilon\le b^2/8$，所以 $b^2-p\ge3b^2/4$。该节准确上界中的因子满足

$$
2+\frac{2(\sqrt a+\sqrt\varepsilon b)}{c+\sqrt{1-p}}<6:
$$

确实，$\sqrt a+\sqrt\varepsilon b<2$，而 $\varepsilon\le1/8$、$p\le1/4$ 保证 $c+\sqrt{1-p}>1$。相乘得式（69.6）的上界，完成定理证明。$\square$

更细的上界展开仍由第 66 节给出：

$$
e(R_{a,\varepsilon})-\varepsilon
\le\frac{a(2+\sqrt a)}{1-a}\varepsilon^2
+\frac a{\sqrt{1-a}}\varepsilon^{5/2}+O_a(\varepsilon^3).
\tag{69.29}
$$

匹配下界现在确定每个固定 $a\in(0,1)$ 的尖锐阶数，但未确定最优二阶系数，亦未证明 $(e(R_{a,\varepsilon})-\varepsilon)/\varepsilon^2$ 有极限。有限参数准确最优值、$a$ 随 $\varepsilon$ 变化时的尺度及端点过渡仍未由这些界解决。

## 追加锚（本行以下为增补区）

## 70. 随缺陷移动的末端压缩与严格大于一的极限系数

### 70.1 同一混合族的移动参数

固定 $r>0$，令 $a_\varepsilon=1-r\varepsilon$，取

$$
0<\varepsilon<\min\{1/r,1/16\}.
\tag{70.1}
$$

沿用三个量子比特 $A,B,D$ 的完整 tester 和因果修复合同，张量次序为 $A\otimes B\otimes D$。记

$$
x=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,
\quad z=|110\rangle,\quad z'=|111\rangle.
$$

第 64 节同一压缩混合族此时为

$$
\begin{aligned}
r_{0,\varepsilon}&=\sqrt{1-r\varepsilon}\,x
+\sqrt{1-\varepsilon}\,y+\sqrt r\,\varepsilon z,\\
r_{1,\varepsilon}&=\sqrt{r\varepsilon}\,x'
-\sqrt{\varepsilon(1-r\varepsilon)}\,z',\\
R_\varepsilon&=|r_{0,\varepsilon}\rangle\langle r_{0,\varepsilon}|
+|r_{1,\varepsilon}\rangle\langle r_{1,\varepsilon}|.
\end{aligned}
\tag{70.2}
$$

早边缘仍为

$$
M_\varepsilon=|00\rangle\langle00|
+(1-\varepsilon)|10\rangle\langle10|
+\varepsilon|11\rangle\langle11|,
\tag{70.3}
$$

所以归一化缺陷是 $\varepsilon$。在厄米算符空间上记

$$
\begin{gathered}
N(X)=\max_{C,E}|\operatorname{Tr}(XE)|,\\
C\succeq0,\qquad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D,
\end{gathered}
\tag{70.4}
$$

并令 $\mathcal C$ 为满足

$$
S\succeq0,\qquad\operatorname{Tr}_D S=I_A\otimes\sigma,
\qquad\sigma\succeq0,\quad\operatorname{Tr}\sigma=1
\tag{70.5}
$$

的因果修复集合。完整事件最优误差为

$$
e_\varepsilon=\min_{S\in\mathcal C}N(R_\varepsilon-S).
$$

**定理 70.1。** 对每个固定 $r>0$，存在实数 $\gamma_r$，使

$$
\lim_{\varepsilon\downarrow0}\frac{e_\varepsilon}{\varepsilon}
=\gamma_r,
\qquad 1<\gamma_r\le\frac98.
\tag{70.6}
$$

特别地，$e_\varepsilon=\gamma_r\varepsilon+o_r(\varepsilon)$。下面给出 $\gamma_r$ 的一个达到最小值的准确切锥变分式；不将它进一步识别为某个显式数值。

### 70.2 一阶展开与事件范数

令

$$
w=x+y,\qquad R_0=|w\rangle\langle w|.
$$

它满足 $\operatorname{Tr}_D R_0=I_A\otimes|0\rangle\langle0|$，所以 $R_0\in\mathcal C$。在固定有限维算符空间中，

$$
R_\varepsilon=R_0+\varepsilon H_r+O_r(\varepsilon^2),
\tag{70.7}
$$

其中

$$
\begin{aligned}
H_r={}&-\frac12\bigl(|rx+y\rangle\langle w|
+|w\rangle\langle rx+y|\bigr)\\
&+\sqrt r\bigl(|z\rangle\langle w|+|w\rangle\langle z|\bigr)\\
&+|\sqrt r\,x'-z'\rangle\langle\sqrt r\,x'-z'|.
\end{aligned}
\tag{70.8}
$$

确实，第一向量为 $w+\varepsilon(-rx/2-y/2+\sqrt r\,z)+O_r(\varepsilon^2)$，第二向量的外积为式（70.8）第三行乘以 $\varepsilon$，加 $O_r(\varepsilon^2)$。特别地，

$$
\operatorname{Tr}H_r=0,\qquad
\operatorname{Tr}_D H_r=-|10\rangle\langle10|+|11\rangle\langle11|.
\tag{70.9}
$$

$N$ 是有限维实厄米空间上的范数。正齐次性和三角不等式直接来自式（70.4）。对任意厄米 $X$，取合法反馈 $C=I_{AB}/2$，再分别取 $E=P_+(X)/2$、$E=P_-(X)/2$，得到

$$
N(X)\ge\frac12\max\{\operatorname{Tr}X_+,\operatorname{Tr}X_-\}
\ge\frac14\|X\|_1.
\tag{70.10}
$$

这里 $X=X_+-X_-$ 是正负部分分解。另一方面，$\operatorname{Tr}C=2$ 给 $\|E\|_\infty\le2$，所以

$$
N(X)\le2\|X\|_1.
\tag{70.11}
$$

这同时证明正定性、连续性及与迹范数的等价。因果集合 $\mathcal C$ 是含 $R_0$ 的紧凸集：它由闭约束给出，且所有元素正、迹恒为 $2$。

### 70.3 缩放修复集与实际切锥

令 $P$ 为 $w$ 张成的一维空间的正交投影，$P_0=I-P$。定义

$$
\mathcal D_t=\frac{\mathcal C-R_0}{t}\quad(t>0),
\qquad
\mathcal T=\overline{\bigcup_{t>0}\mathcal D_t}.
\tag{70.12}
$$

若 $0<t'\le t$，则 $\mathcal D_t\subseteq\mathcal D_{t'}$：对 $K=(S-R_0)/t$，有

$$
R_0+t'K=\left(1-\frac{t'}t\right)R_0+\frac{t'}t S\in\mathcal C.
$$

所以式（70.12）确实是这个因果修复集合在 $R_0$ 处的闭切锥。

在本问题中，它具有准确描述

$$
\mathcal T=
\left\{K=K^*:
\begin{array}{l}
\operatorname{Tr}_D K=I_A\otimes\dot\sigma
\text{ 对某个 }\dot\sigma=\dot\sigma^*,\quad\operatorname{Tr}\dot\sigma=0,\\
P_0KP_0\succeq0
\end{array}\right\}.
\tag{70.13}
$$

先证必要性。对 $K=(S-R_0)/t$，因果等式相减得到所需偏迹；又因 $P_0R_0P_0=0$，有 $P_0KP_0=P_0SP_0/t\succeq0$。这两个条件均闭，故对闭包中所有 $K$ 成立。

再证充分性。固定式（70.13）右侧的任意 $K$，选择严格正的因果算符

$$
S_{\mathrm{full}}=\frac14 I_{ABD}\in\mathcal C.
$$

对任意 $\delta>0$，置

$$
K_\delta=K+\delta(S_{\mathrm{full}}-R_0).
\tag{70.14}
$$

它仍满足迹零因果线性约束，且在 $P_0$ 空间内

$$
B_\delta:=P_0K_\delta P_0
=P_0KP_0+\frac\delta4P_0\succeq\frac\delta4P_0.
\tag{70.15}
$$

令 $\widehat w=w/\sqrt2$、$\alpha_\delta=\langle\widehat w|K_\delta|\widehat w\rangle$、$b_\delta=P_0K_\delta\widehat w$。相对于 $\operatorname{span}(\widehat w)\oplus w^\perp$，

$$
R_0+tK_\delta=
\begin{pmatrix}
2+t\alpha_\delta&t b_\delta^*\\
t b_\delta&tB_\delta
\end{pmatrix}.
\tag{70.16}
$$

对 $t>0$，右下块严格正，其 Schur 补为

$$
2+t\left(\alpha_\delta-b_\delta^*B_\delta^{-1}b_\delta\right).
$$

它对充分小的正 $t$ 严格为正。因此 $R_0+tK_\delta\succeq0$。因果线性约束给

$$
\operatorname{Tr}_D(R_0+tK_\delta)
=I_A\otimes\bigl(|0\rangle\langle0|+t\dot\sigma_\delta\bigr),
\qquad\operatorname{Tr}\dot\sigma_\delta=0.
$$

括号内的算符由左侧正性自动为正，迹为 $1$。所以 $R_0+tK_\delta\in\mathcal C$，即 $K_\delta\in\mathcal D_t$。令 $\delta\downarrow0$，得到 $K\in\mathcal T$，完成式（70.13）的证明。这个闭包逼近没有把单独的切向正性冒充每个步长上的实际可行性。

### 70.4 极限与达到最小值的系数

令 $H_\varepsilon=(R_\varepsilon-R_0)/\varepsilon$。正齐次性给准确等式

$$
\frac{e_\varepsilon}{\varepsilon}
=\operatorname{dist}_N(H_\varepsilon,\mathcal D_\varepsilon).
\tag{70.17}
$$

任意非空集合 $A$ 的距离函数满足

$$
|\operatorname{dist}_N(U,A)-\operatorname{dist}_N(V,A)|\le N(U-V).
$$

式（70.7）、（70.11）因此给

$$
\left|\frac{e_\varepsilon}{\varepsilon}
-\operatorname{dist}_N(H_r,\mathcal D_\varepsilon)\right|
\le N(H_\varepsilon-H_r)=O_r(\varepsilon)\longrightarrow0.
\tag{70.18}
$$

由式（70.12）的嵌套性，$\operatorname{dist}_N(H_r,\mathcal D_\varepsilon)$ 随 $\varepsilon\downarrow0$ 单调下降，其极限为

$$
\inf_{t>0}\operatorname{dist}_N(H_r,\mathcal D_t)
=\operatorname{dist}_N(H_r,\mathcal T).
\tag{70.19}
$$

最后一个等式使用距离对取闭包不变。将 $t$ 限制在任意固定小区间内也给同一个并集闭包，因为更小的缩放集合包含更大的步长所给集合。

故极限存在，并且

$$
\gamma_r=\min_{K\in\mathcal T}N(H_r-K).
\tag{70.20}
$$

最小值确实达到：$0\in\mathcal T$，所以一个极小化序列可以满足 $N(H_r-K_n)\le N(H_r)+1$；式（70.10）使 $K_n$ 在迹范数下有界。有限维收敛子列、$\mathcal T$ 的闭性与 $N$ 的连续性给一个达到下确界的 $K$。

对任意 $K\in\mathcal T$，取

$$
C_+=|00\rangle\langle00|+|11\rangle\langle11|,
\qquad\Pi_+=C_+\otimes I_D.
$$

式（70.9）、（70.13）给 $\operatorname{Tr}((H_r-K)\Pi_+)=1$，所以 $N(H_r-K)\ge1$，即 $\gamma_r\ge1$。下一步排除等号。

### 70.5 同一切向修复的饱和矛盾

反设 $\gamma_r=1$，取式（70.20）的极小值点 $K$，置 $Y=H_r-K$。再令

$$
C_-=|01\rangle\langle01|+|10\rangle\langle10|,
\qquad\Pi_-=C_-\otimes I_D.
$$

两个总事件的迹满足

$$
\operatorname{Tr}(\Pi_+Y\Pi_+)=1,
\qquad\operatorname{Tr}(\Pi_-Y\Pi_-)=-1.
$$

因为 $N(Y)=1$，每个压缩的正负谱投影也是合法事件；正负谱和于是迫使

$$
\Pi_+Y\Pi_+\succeq0,
\qquad\Pi_-(K-H_r)\Pi_-\succeq0.
\tag{70.21}
$$

在 $\Pi_+$ 空间中，式（70.8）给

$$
(H_{xx},H_{x'x'},H_{zz},H_{z'z'})=(-r,r,0,1),
\qquad H_{xz}=\sqrt r,\quad H_{x'z'}=-\sqrt r.
$$

由于 $z\perp w$，切向正性给 $K_{zz}\ge0$；式（70.21）又给 $Y_{zz}=-K_{zz}\ge0$。所以 $K_{zz}=Y_{zz}=0$。正矩阵的零对角行列全零，故

$$
K_{xz}=H_{xz}=\sqrt r.
$$

因果偏迹的跨输入 $00,11$ 元为零，遂有

$$
K_{x'z'}=-K_{xz}=-\sqrt r.
\tag{70.22}
$$

令 $t=K_{x'x'}$、$p=\dot\sigma_{11}=K_{zz}+K_{z'z'}=K_{z'z'}$。$x',z'$ 均在 $w^\perp$，所以切向正性在这两个方向的主块给

$$
t,p\ge0,\qquad tp\ge r.
$$

式（70.21）同时给 $t\le r$、$p\le1$。固定 $r>0$ 使这些条件只能在

$$
t=r,\qquad p=1
\tag{70.23}
$$

时成立。因 $\dot\sigma$ 迹零，其另一个对角元为 $-1$。因果条件从而给

$$
K_{xx}+K_{x'x'}=-1,\qquad K_{xx}=-1-r.
\tag{70.24}
$$

另一方面，式（70.21）在 $y$ 上给 $K_{yy}\ge H_{yy}=-1$。向量 $|100\rangle$ 在 $w^\perp$，故 $K_{100,100}\ge0$；因果关系 $K_{100,100}+K_{yy}=-1$ 又给 $K_{yy}\le-1$。因此

$$
K_{yy}=-1.
\tag{70.25}
$$

最后用 $x-y\perp w$ 的切向正性：

$$
0\le\langle x-y|K|x-y\rangle
=-r-2-2\operatorname{Re}K_{xy}.
$$

结合 $H_{xy}=-(r+1)/2$，得到

$$
\operatorname{Re}Y_{xy}\ge\frac12,
\qquad Y_{xx}=1,\qquad Y_{yy}=0.
\tag{70.26}
$$

取任意 $q\in(0,1)$，例如 $q=1/2$，并选择

$$
C_q=\operatorname{diag}(q,1,1-q,0).
$$

加权 $Y$ 在 $x,y$ 上的主块为

$$
B_q=\begin{pmatrix}
q&\sqrt{q(1-q)}\,Y_{xy}\\
\sqrt{q(1-q)}\,\overline{Y_{xy}}&0
\end{pmatrix}.
\tag{70.27}
$$

由 $|Y_{xy}|\ge1/2$，有 $\det(qI-B_q)<0$，故最大特征值 $\lambda_q>q$。取对应秩一投影嵌入全空间，再按 $C_q^{1/2}\otimes I_D$ 加权，得到响应为 $\lambda_q$ 的合法事件。

同一总事件的响应由式（70.9）、（70.13）等于 $-(1-q)$。所以互补事件响应为

$$
-(1-q)-\lambda_q<-1,
$$

与 $N(Y)=1$ 矛盾。由极小值达到可知 $\gamma_r>1$。

### 70.6 上界与非一致端点

对每个参数点，式（70.2）仍是第 64 节的末端 CPTP 压缩

$$
R_\varepsilon=(\operatorname{id}_{AB}\otimes\Lambda_{a_\varepsilon})
(R_\varepsilon^{(3)}).
$$

末端处理保持因果修复并收缩完整事件误差，所以

$$
e_\varepsilon\le e(R_\varepsilon^{(3)}).
$$

第 62 节三维纯候选的准确最优值展开给

$$
\lim_{\varepsilon\downarrow0}\frac{e(R_\varepsilon^{(3)})}{\varepsilon}
=\frac98.
$$

结合已证极限，得到 $\gamma_r\le9/8$，完成定理证明。$\square$

对固定 $a\in(0,1)$，第 69 节给 $e(R_{a,\varepsilon})/\varepsilon\to1$。这里沿 $1-a_\varepsilon=r\varepsilon$ 移动，同一混合族的比值却收敛到严格大于一的 $\gamma_r$。因此固定参数的结论不能对整个参数开区间一致化。

式（70.20）是系数的准确变分描述，已证明其达到最小值；本节未求出 $\gamma_r$ 的显式值、最优 $r$ 或不依赖 $r$ 的统一正比例间隙。

## 追加锚（本行以下为增补区）

## 71. 移动压缩系数的连续性、两个端点与内部最大值

### 71.1 系数函数及结论

第 70 节对每个固定 $r>0$ 定义了同一混合量子比特族沿

$$
a_\varepsilon=1-r\varepsilon
$$

移动时的准确极限系数

$$
\gamma_r=\lim_{\varepsilon\downarrow0}\frac{e(R_{a_\varepsilon,\varepsilon})}{\varepsilon}
=\min_{K\in\mathcal T}N(H_r-K),
\qquad1<\gamma_r\le\frac98.
\tag{71.1}
$$

这里 $\mathcal T$ 是第 70 节的同一个闭因果切锥，与 $r$ 无关；$N$ 是完整 tester 事件范数。将式（71.1）的变分式延伸到 $r=0$，仍记所得值为 $\gamma_0$。

**定理 71.1。** 该函数满足

$$
\gamma_0=1,
\qquad
|\gamma_r-\gamma_s|
\le2|r-s|+4|\sqrt r-\sqrt s|
\quad(r,s\ge0).
\tag{71.2}
$$

因而它在 $[0,\infty)$ 连续，在每个远离零的紧参数区间上 Lipschitz 连续。两个端点均满足

$$
\lim_{r\downarrow0}\gamma_r=1,
\qquad\lim_{r\uparrow\infty}\gamma_r=1.
\tag{71.3}
$$

更明确地，若 $r\ge8$，令

$$
u_r=\frac{r-\sqrt{r^2-4r}}2
=\frac{2}{1+\sqrt{1-4/r}},
\tag{71.4}
$$

则

$$
1<\gamma_r\le
\min\left\{\frac98,\ 1+3(u_r-1)\right\}.
\tag{71.5}
$$

因此存在某个有限正数 $r_*$，使

$$
\gamma_{r_*}=\max_{r>0}\gamma_r\in(1,9/8].
\tag{71.6}
$$

本结论不指定最大值、最大点或其唯一性。

### 71.2 同一个切锥上的参数分解

沿用

$$
x=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,
\quad z=|110\rangle,\quad z'=|111\rangle,
\quad w=x+y.
$$

将第 70 节的一阶方向准确分解为

$$
H_r=H_0+rJ_1+\sqrt r\,J_{1/2},
\tag{71.7}
$$

其中

$$
\begin{aligned}
H_0&=-\frac12\bigl(|y\rangle\langle w|+|w\rangle\langle y|\bigr)
+|z'\rangle\langle z'|,\\
J_1&=-\frac12\bigl(|x\rangle\langle w|+|w\rangle\langle x|\bigr)
+|x'\rangle\langle x'|,\\
J_{1/2}&=|z\rangle\langle w|+|w\rangle\langle z|
-|x'\rangle\langle z'|-|z'\rangle\langle x'|.
\end{aligned}
\tag{71.8}
$$

固定任意完整 tester $C,E$，即 $C\succeq0$、$\operatorname{Tr}_A C=I_B$、$0\preceq E\preceq C\otimes I_D$。$C$ 的标准基对角元均位于 $[0,1]$，故对上列任一标准基向量 $v$，

$$
0\le\langle v|E|v\rangle\le1.
$$

更具体地，$x,y$ 的末输出坐标不同，而它们的 $AB$ 坐标为 $00,10$，所以

$$
\langle w|E|w\rangle
\le\langle w|C\otimes I_D|w\rangle
=C_{00,00}+C_{10,10}=1.
\tag{71.9}
$$

对正算子 $E$ 使用 Cauchy–Schwarz，不要求 $E$ 在任何基下对角。式（71.9）及上述标准基对角界给

$$
|\langle w|E|x\rangle|\le1,
\qquad|\langle w|E|z\rangle|\le1,
\qquad|\langle z'|E|x'\rangle|\le1.
$$

因此

$$
\begin{aligned}
|\operatorname{Tr}(J_1E)|
&=\bigl|-\operatorname{Re}\langle w|E|x\rangle
+\langle x'|E|x'\rangle\bigr|\le2,\\
|\operatorname{Tr}(J_{1/2}E)|
&=\bigl|2\operatorname{Re}\langle w|E|z\rangle
-2\operatorname{Re}\langle z'|E|x'\rangle\bigr|\le4.
\end{aligned}
$$

取全部 tester 的最大值得到

$$
N(J_1)\le2,\qquad N(J_{1/2})\le4.
\tag{71.10}
$$

任意固定集合的范数距离函数是 $1$-Lipschitz 的。由于所有参数共用同一个 $\mathcal T$，式（71.7）、（71.10）遂给

$$
\begin{aligned}
|\gamma_r-\gamma_s|
&\le N(H_r-H_s)\\
&\le2|r-s|+4|\sqrt r-\sqrt s|.
\end{aligned}
\tag{71.11}
$$

这证明连续性模量。若 $r,s\ge d>0$，则 $|\sqrt r-\sqrt s|\le|r-s|/(2\sqrt d)$，因此可取局部 Lipschitz 常数 $2+2/\sqrt d$。

### 71.3 零端点的准确修复

把原混合族连续延伸至 $a=1$。对 $0<\varepsilon<1$，置 $c=\sqrt{1-\varepsilon}$、$d=1-c$，并令 $h=|010\rangle$。此时候选为

$$
R_{1,\varepsilon}=|x+cy\rangle\langle x+cy|
+\varepsilon|z'\rangle\langle z'|.
$$

定义显式因果修复

$$
S_\varepsilon=c|w\rangle\langle w|
+d\bigl(|h\rangle\langle h|+|z'\rangle\langle z'|\bigr).
\tag{71.12}
$$

它正，且

$$
\operatorname{Tr}_D S_\varepsilon
=I_A\otimes\operatorname{diag}(c,d).
$$

因为 $c+d=1$，这是归一化因果修复。准确差算符为

$$
R_{1,\varepsilon}-S_\varepsilon
=d\bigl(|x\rangle\langle x|-|h\rangle\langle h|\bigr)
+cd\bigl(|z'\rangle\langle z'|-|y\rangle\langle y|\bigr).
\tag{71.13}
$$

对任意完整事件 $E$，正项响应至多 $d+cd=\varepsilon$，负项绝对响应同样至多 $d+cd=\varepsilon$；这只使用各标准基事件对角元位于 $[0,1]$。所以 $N(R_{1,\varepsilon}-S_\varepsilon)\le\varepsilon$。原早边缘总事件又给下界 $\varepsilon$，故

$$
e(R_{1,\varepsilon})=\varepsilon
\qquad(0<\varepsilon<1).
\tag{71.14}
$$

为了直接核对变分式的零端点，式（71.12）的一阶方向为

$$
K_0=-\frac12|w\rangle\langle w|
+\frac12\bigl(|h\rangle\langle h|+|z'\rangle\langle z'|\bigr)
\in\mathcal T.
$$

它的因果偏迹为 $I_A\otimes\operatorname{diag}(-1/2,1/2)$，在 $w^\perp$ 上的压缩正；也可直接由式（71.12）的可行割线极限确认其切锥成员身份。此时

$$
H_0-K_0=
\frac12\bigl(|x\rangle\langle x|+|z'\rangle\langle z'|
-|y\rangle\langle y|-|h\rangle\langle h|\bigr).
\tag{71.15}
$$

同样的对角事件界给 $N(H_0-K_0)\le1$。而对任意 $K\in\mathcal T$，第 70 节的 $C_+$ 总事件仍给 $\operatorname{Tr}((H_0-K)\Pi_+)=1$。因此 $\gamma_0=1$。

将 $s=0$ 代入式（71.11），得到显式估计

$$
1<\gamma_r\le1+2r+4\sqrt r\quad(r>0),
\tag{71.16}
$$

以及 $r\downarrow0$ 时的极限 $1$。

### 71.4 无穷端点由同一显式修复控制

固定 $r\ge8$，沿 $a_\varepsilon=1-r\varepsilon$ 取充分小的正 $\varepsilon$。第 66 节所需条件

$$
\varepsilon\le\frac{1-a_\varepsilon}{8}
$$

此时等价于 $r\ge8$，所以同一显式二阶修复对每个这样的参数点合法。

将该修复的小根写成 $p_\varepsilon=\varepsilon u_{r,\varepsilon}$。原二次方程变成

$$
u_{r,\varepsilon}^2-r(1+\varepsilon)u_{r,\varepsilon}+r=0,
$$

其小根为

$$
u_{r,\varepsilon}
=\frac{r(1+\varepsilon)
-\sqrt{r^2(1+\varepsilon)^2-4r}}2
\longrightarrow u_r.
\tag{71.17}
$$

第 66 节的准确事件上界除以 $\varepsilon$ 后为

$$
\frac{e(R_{a_\varepsilon,\varepsilon})}{\varepsilon}
\le1+(u_{r,\varepsilon}-1)
\left[
2+\frac{2(\sqrt{1-r\varepsilon}+\sqrt r\,\varepsilon)}
{\sqrt{1-\varepsilon}+\sqrt{1-p_\varepsilon}}
\right].
\tag{71.18}
$$

固定 $r$ 后，方括号趋于 $3$。由第 70 节已证的真实极限可得

$$
\gamma_r\le1+3(u_r-1).
\tag{71.19}
$$

结合 $\gamma_r\le9/8$，得到式（71.5）。式（71.4）显示 $u_r\to1$；因此 $1\le\gamma_r\le1+3(u_r-1)$ 迫使 $r\uparrow\infty$ 时 $\gamma_r\to1$。

显式上界本身还满足

$$
3(u_r-1)=\frac3r+O(r^{-2})\qquad(r\uparrow\infty).
\tag{71.20}
$$

这只是上界的渐近式，不能将 $3/r$ 识别为实际 $\gamma_r-1$ 的首项。

### 71.5 最大值在内部达到及范围

选择一个正参数，例如 $r=1$。第 70 节给 $\gamma_1>1$。取

$$
\rho=\frac{1+\gamma_1}{2}\in(1,\gamma_1).
$$

由两个端点极限，存在 $0<d<1<R<\infty$，使 $r\in[0,d)$ 或 $r>R$ 时均有 $\gamma_r<\rho$。连续函数 $\gamma_r$ 在紧区间 $[d,R]$ 达到最大值，且该值至少为 $\gamma_1>\rho$，因此也是整个 $r>0$ 上的最大值。这证明式（71.6）。$\square$

两个端点结果是在已经定义的系数函数 $\gamma_r$ 上取极限；本节没有交换 $r$ 与 $\varepsilon$ 的极限，也没有证明任意共同变化路径上的一致展开。它们证明不存在对所有 $r>0$ 通用的严格正比例间隙。内部最大值的准确大小、位置和唯一性仍未由这些界确定。

## 追加锚（本行以下为增补区）

## 72. 移动压缩系数与三维纯候选之间的统一严格间隙

### 72.1 固定合同与结论

沿用第70、71节的三个量子比特、完整 tester 范数 $N$、闭因果切锥 $\mathcal T$ 及系数

$$
\gamma_r=\min_{K\in\mathcal T}N(H_r-K),\qquad r\ge0.
\tag{72.1}
$$

切锥和范数不随 $r$ 改变。第71节已证明 $\gamma_0=1$、$\gamma_r>1$ 对每个 $r>0$ 成立、两个端点均趋于一，且全局最大值在有限正参数处取得。

**定理72.1（系数的统一严格上界）。** 存在与 $r$ 无关的 $\eta>0$，使

$$
1<\gamma_r\le\frac98-\eta
\qquad(r>0).
\tag{72.2}
$$

特别地，同一混合量子比特族的移动压缩系数的最大值严格小于三维纯候选的系数 $9/8$。本节不确定 $\eta$ 的显式值，也不将该系数界升级为任意 $r,\varepsilon$ 共同变化时的一致有限参数展开。

### 72.2 一个保持全部因果约束的切向扰动

继续记

$$
x=|000\rangle,\quad x'=|001\rangle,\quad h=|010\rangle,
\quad y=|101\rangle,\quad z=|110\rangle,\quad z'=|111\rangle,
\qquad w=x+y.
$$

对固定 $r>0$，取 $0\le\delta<1$，令

$$
p=1-\delta,\qquad g=\sqrt{rp}.
$$

定义实厄米方向

$$
\begin{aligned}
K_{r,\delta}={}&-(r+p)|x\rangle\langle x|-p|y\rangle\langle y|
-\left(\frac r2+p\right)(|x\rangle\langle y|+|y\rangle\langle x|)\\
&+g(|w\rangle\langle z|+|z\rangle\langle w|)\\
&+r|x'\rangle\langle x'|-g(|x'\rangle\langle z'|+|z'\rangle\langle x'|)
+p|z'\rangle\langle z'|+p|h\rangle\langle h|.
\end{aligned}
\tag{72.3}
$$

它的因果偏迹为

$$
\operatorname{Tr}_D K_{r,\delta}=I_A\otimes\operatorname{diag}(-p,p).
\tag{72.4}
$$

其中跨输入的两个偏迹项 $K_{xz}=g$ 与 $K_{x'z'}=-g$ 相消，其他非对角项在末端偏迹中消失。在 $w^\perp$ 上压缩时，$x-y$ 方向的二次型和它与 $z$ 的配对均为零；$z$ 的对角也为零。其余非零压缩正是

$$
\begin{pmatrix}r&-g\\-g&p\end{pmatrix}
\quad\text{在 }\operatorname{span}(x',z')\text{ 上},
\qquad p|h\rangle\langle h|.
\tag{72.5}
$$

因为 $rp=g^2$ 且 $r,p\ge0$，它们均正。由第70节切锥的准确刻画，

$$
K_{r,\delta}\in\mathcal T.
\tag{72.6}
$$

记 $Y_{r,\delta}=H_r-K_{r,\delta}$。在 $\delta=0$ 时，所有 $r$ 依赖恰好相消：

$$
Y_{r,0}=Y_*:=|x\rangle\langle x|
+\frac12(|x\rangle\langle y|+|y\rangle\langle x|)
-|h\rangle\langle h|.
\tag{72.7}
$$

固定 $r$ 后，$\sqrt{1-\delta}=1-\delta/2+O(\delta^2)$ 给

$$
Y_{r,\delta}=Y_*+\delta Z_r+O_r(\delta^2),
\tag{72.8}
$$

其中

$$
\begin{aligned}
Z_r={}&-|w\rangle\langle w|+|h\rangle\langle h|+|z'\rangle\langle z'|\\
&+\frac{\sqrt r}{2}\bigl(
|w\rangle\langle z|+|z\rangle\langle w|
-|x'\rangle\langle z'|-|z'\rangle\langle x'|
\bigr).
\end{aligned}
\tag{72.9}
$$

下面证明，这个可行扰动使完整事件范数从 $9/8$ 严格下降。

### 72.3 基准误差的全部最优事件

合法 tester 仍为

$$
C\succeq0,\qquad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D.
$$

考虑两个独立角参数的局部酉算符

$$
U_{\phi,\psi}
=\operatorname{diag}(1,e^{i\phi})_A
\otimes\operatorname{diag}(1,e^{i\psi})_B
\otimes\operatorname{diag}(1,e^{-i\phi})_D.
\tag{72.10}
$$

它固定 $x,y$，将 $h$ 乘以相位，所以保持 $Y_*$。同时，局部共轭把合法 tester 送到合法 tester。对两个角分别均匀平均，可把任意 $C$ 变成保持原对角的对角矩阵，而 $\operatorname{Tr}(Y_*E)$ 不变。故对 $Y_*$ 的正、负响应最大值都可在

$$
C=\operatorname{diag}(q,t,1-q,1-t),\qquad0\le q,t\le1
\tag{72.11}
$$

中求取。

令 $L=C^{1/2}\otimes I_D$。加权算符 $LY_*L$ 在 $x,y$ 上的主块为

$$
\begin{pmatrix}
q&\frac12\sqrt{q(1-q)}\\
\frac12\sqrt{q(1-q)}&0
\end{pmatrix},
\tag{72.12}
$$

其本征值为 $(q+\sqrt q)/2$ 与 $(q-\sqrt q)/2$；另有 $h$ 上的本征值 $-t$，其余全零。任意合法事件可写为 $E=LFL$，其中 $0\preceq F\preceq I$，在 $L$ 的核上如何延伸 $F$ 不影响结果。因此正响应最多为

$$
\frac{q+\sqrt q}{2}\le1,
$$

负响应绝对值最多为

$$
t+\frac{\sqrt q-q}{2}\le\frac98.
\tag{72.13}
$$

后一等号只能在 $t=1,q=1/4$ 时成立，也确由负本征投影达到。于是 $N(Y_*)=9/8$，每个绝对值最优事件均满足

$$
\operatorname{Tr}(Y_*E)=-\frac98.
\tag{72.14}
$$

这里还能控制未平均的全部最优 tester。将任一最优 $(C,E)$ 按（72.10）平均，原对角不变，平均后仍达到（72.14），所以原 $C$ 必满足

$$
C_{00,00}=\frac14,\quad C_{01,01}=1,
\quad C_{10,10}=\frac34,\quad C_{11,11}=0.
\tag{72.15}
$$

正性使 $C$ 的 $11$ 行列全零。由于 $0\preceq E\preceq C\otimes I_D$，$E$ 的 $z,z'$ 行列也全零。因此（72.9）中所有含 $z$ 或 $z'$ 的项对这个事件的配对为零，得到

$$
\operatorname{Tr}(Z_rE)
=-\langle w|E|w\rangle+\langle h|E|h\rangle.
\tag{72.16}
$$

右侧被（72.10）的平均保持。只需在平均后的对角 tester 中计算它。此时（72.12）的负本征单位向量为

$$
v_-=-\frac12x+\frac{\sqrt3}{2}y.
$$

达到最负响应要求 $F$ 在 $v_-$ 和 $h$ 上恒等、在正本征方向上为零。其核空间上的自由部分不影响 $w,h$ 的读数。所以

$$
\begin{aligned}
\langle w|E|w\rangle
&=|\langle v_-|Lw\rangle|^2
=\left|-\frac14+\frac34\right|^2=\frac14,\\
\langle h|E|h\rangle&=1.
\end{aligned}
\tag{72.17}
$$

这些值也适用于未平均的原事件。结合（72.16），对 $Y_*$ 的每个最优 tester 都有

$$
-\operatorname{Tr}(Z_rE)=-\frac34.
\tag{72.18}
$$

这一步保留了全部最优事件，未以一个方便的对角事件代替完整范数。

### 72.4 紧致最大化的单侧变化

合法 $(C,E)$ 构成紧集：$C$ 正且迹二，$E$ 正且迹至多四，所有约束闭。把符号 $\varsigma\in\{-1,1\}$ 一起加入，便有

$$
N(Y)=\max_{C,E,\varsigma}\varsigma\operatorname{Tr}(YE).
$$

式（72.8）的余项与所有合法事件配对时仍为 $O_r(\delta^2)$，因为 $\|E\|_\infty\le2$。对任意 $\delta_n\downarrow0$，取最大化事件和符号。紧性给收敛子列；由 $Y_{r,\delta_n}\to Y_*$，其极限必是 $Y_*$ 的最大化点。式（72.13）、（72.14）使极限符号为负，式（72.18）使相应的一阶配对为 $-3/4$。

更明确地，将最大化点记为 $(C_n,E_n,\varsigma_n)$，则

$$
\frac{N(Y_{r,\delta_n})-N(Y_*)}{\delta_n}
\le\varsigma_n\operatorname{Tr}(Z_rE_n)+O_r(\delta_n).
\tag{72.19}
$$

这是因为同一个点在 $Y_*$ 上的响应至多 $N(Y_*)$。取达到上极限的子列后，用（72.18）得到上极限至多 $-3/4$。反向，固定任意一个 $Y_*$ 的最优负事件，将它用于 $Y_{r,\delta}$，便由（72.8）、（72.18）得到下极限至少 $-3/4$。因此

$$
N(Y_{r,\delta})=\frac98-\frac34\delta+o_r(\delta)
\qquad(\delta\downarrow0).
\tag{72.20}
$$

对每个固定有限 $r>0$，充分小正 $\delta$ 遂满足 $N(Y_{r,\delta})<9/8$。由（72.1）、（72.6），

$$
\gamma_r\le N(Y_{r,\delta})<\frac98.
\tag{72.21}
$$

这里的允许扰动大小可以依赖 $r$，尚未声称同一 $\delta$ 对全部参数有效。

### 72.5 从逐点严格性到系数的统一间隙

第71节证明存在有限正 $r_*$，使 $\gamma_{r_*}=\max_{r>0}\gamma_r$。式（72.21）在这个实际最大点也成立，所以

$$
\eta:=\frac98-\gamma_{r_*}>0.
\tag{72.22}
$$

所有参数均满足 $\gamma_r\le\gamma_{r_*}=9/8-\eta$。再用第70节的逐点下界 $\gamma_r>1$，即得定理。证明完毕。

这个统一间隙属于先固定移动尺度参数 $r$、再令缺陷趋零得到的系数族。其结论强于逐参数末端处理收缩给出的 $\gamma_r\le9/8$；但没有比较任意量子比特过程与任意三维过程，也未确定该混合族的最优系数或所有双参数路径的误差尺度。

## 追加锚（本行以下为增补区）

## 73. 移动压缩系数的显式统一间隙

### 73.1 定量结论与同一切向修复

沿用第 70—72 节完整 tester 范数、闭因果切锥及准确极限系数

$$
\gamma_r=\min_{K\in\mathcal T}N(H_r-K),\qquad r>0.
$$

**定理 73.1。** 对每个 $r>0$，都有显式估计

$$
1<\gamma_r\le\frac98-\frac{23}{1024(1+2r)}.
\tag{73.1}
$$

结合大参数的修复上界，可以进一步取一个与 $r$ 无关的明确常数：

$$
1<\gamma_r\le\frac98-\frac{23}{394240}
\qquad(r>0).
\tag{73.2}
$$

这些常数是可行修复给出的保守界，不是最优间隙。

证明仍使用第 72 节的显式切向修复 $K_{r,\delta}$。取

$$
0<\delta\le\frac14,\qquad p=1-\delta,
\qquad g=\sqrt{rp},
\qquad \rho=\sqrt r-g=\sqrt r\,(1-\sqrt{1-\delta}).
\tag{73.3}
$$

第 72 节已直接验证 $K_{r,\delta}\in\mathcal T$。记

$$
\begin{gathered}
x=|000\rangle,\quad x'=|001\rangle,\quad h=|010\rangle,
\quad y=|101\rangle,\quad z=|110\rangle,\quad z'=|111\rangle,\\
w=x+y,\\
J=|w\rangle\langle z|+|z\rangle\langle w|
-|x'\rangle\langle z'|-|z'\rangle\langle x'|.
\end{gathered}
$$

其差算符具有准确分解

$$
\begin{aligned}
Y_{r,\delta}:=H_r-K_{r,\delta}
={}&Y_* -\delta|w\rangle\langle w|
+\delta|h\rangle\langle h|+\delta|z'\rangle\langle z'|
+\rho J,\\
Y_*={}&|x\rangle\langle x|
+\frac12(|x\rangle\langle y|+|y\rangle\langle x|)
-|h\rangle\langle h|.
\end{aligned}
\tag{73.4}
$$

以下直接估计所有 tester 对式（73.4）的正负响应，不需要知道其最优事件。

### 73.2 任意 tester 的末支撑质量

固定任意完整 tester

$$
C\succeq0,\qquad\operatorname{Tr}_A C=I_B,
\qquad0\preceq E\preceq C\otimes I_D.
$$

记

$$
s=C_{11,11}\in[0,1],\qquad q=C_{00,00}\in[0,1].
$$

偏迹归一化给 $C_{01,01}=1-s$、$C_{10,10}=1-q$。由 $E\preceq C\otimes I_D$，

$$
\begin{gathered}
\langle z|E|z\rangle,\ \langle z'|E|z'\rangle\le s,
\qquad\langle x'|E|x'\rangle\le q\le1,\\
\langle w|E|w\rangle
\le\langle w|C\otimes I_D|w\rangle
=C_{00,00}+C_{10,10}=1.
\end{gathered}
\tag{73.5}
$$

最后一个等式使用 $x,y$ 的末输出坐标不同。正算子 $E$ 的 Cauchy–Schwarz 不等式于是给

$$
|\operatorname{Tr}(JE)|
\le2|\langle z|E|w\rangle|+2|\langle z'|E|x'\rangle|
\le4\sqrt s.
\tag{73.6}
$$

这是对同一个任意 tester 的约束；没有将它与另一个 tester 的最优事件拼接。

### 73.3 中心块负响应的准确最大值

定义不含末支撑相干项的中心算符

$$
Z_\delta=Y_*-\delta|w\rangle\langle w|+\delta|h\rangle\langle h|.
\tag{73.7}
$$

它被第 72 节的两个角局部相位群保持。将任意给定 $(C,E)$ 按该群平均，不改变 $-\operatorname{Tr}(Z_\delta E)$，也不改变原对角参数 $q,s$；平均后的反馈矩阵为

$$
\overline C=\operatorname{diag}(q,1-s,1-q,s).
$$

因此对于中心项可以在这个对角反馈下求上界，同时保留原 tester 在式（73.6）中的同一个 $s$。

加权 $Z_\delta$ 在 $x,y$ 上的主块为

$$
B_{q,\delta}=
\begin{pmatrix}
(1-\delta)q&(1/2-\delta)\sqrt{q(1-q)}\\
(1/2-\delta)\sqrt{q(1-q)}&-\delta(1-q)
\end{pmatrix}.
\tag{73.8}
$$

其迹为 $q-\delta$，行列式为 $-q(1-q)/4$。唯一可能的负本征值绝对值为

$$
n_\delta(q)=
\frac{\sqrt{\delta^2+(1-2\delta)q}-q+\delta}{2}.
\tag{73.9}
$$

其余非零部分只有 $h$ 上的负本征值 $-p(1-s)$。故任意原 tester 满足

$$
-\operatorname{Tr}(Z_\delta E)
\le p(1-s)+n_\delta(q).
\tag{73.10}
$$

在 $0<\delta\le1/4$ 上，式（73.9）是 $q\in[0,1]$ 的凹函数，最大点为

$$
q_\delta=\frac{1-4\delta}{4(1-2\delta)}\in[0,1].
$$

可直接求导确认；在 $\delta=1/4$ 时最大点位于 $q=0$。代入得到

$$
F_\delta:=p+\max_{0\le q\le1}n_\delta(q)
=\frac98-\frac34\delta+
\frac{\delta^2}{2(1-2\delta)}.
\tag{73.11}
$$

因此中心负响应具有保留末支撑质量罚项的界

$$
-\operatorname{Tr}(Z_\delta E)\le F_\delta-p s.
\tag{73.12}
$$

### 73.4 完整负响应与正响应

式（73.4）等于 $Z_\delta+\delta|z'\rangle\langle z'|+\rho J$。因为 $E\succeq0$，在负响应上可以舍去非正贡献 $-\delta\langle z'|E|z'\rangle$。式（73.6）、（73.12）于是给

$$
\begin{aligned}
-\operatorname{Tr}(Y_{r,\delta}E)
&\le F_\delta-p s+4\rho\sqrt s\\
&\le F_\delta+\frac{4\rho^2}{p}.
\end{aligned}
\tag{73.13}
$$

最后一步是完成平方：$-p s+4\rho\sqrt s=-p(\sqrt s-2\rho/p)^2+4\rho^2/p$。

由

$$
\rho=\frac{\sqrt r\,\delta}{1+\sqrt p},
\qquad1+\sqrt p\ge2\sqrt p,
$$

以及 $p\ge3/4$，有

$$
\frac{4\rho^2}{p}
\le\frac{r\delta^2}{p^2}
\le\frac{16}{9}r\delta^2\le2r\delta^2.
$$

式（73.11）中 $\delta^2/[2(1-2\delta)]\le\delta^2$。取全部 tester 最大值，得到

$$
\max_{C,E}-\operatorname{Tr}(Y_{r,\delta}E)
\le\frac98-\frac34\delta+(1+2r)\delta^2.
\tag{73.14}
$$

正响应也须控制。第 72 节已准确计算 $\max_{C,E}\operatorname{Tr}(Y_*E)=1$。式（73.4）中的 $-\delta|w\rangle\langle w|$ 对正响应不增益，而两个新增对角元满足

$$
\langle h|E|h\rangle+\langle z'|E|z'\rangle
\le C_{01,01}+C_{11,11}=1.
$$

再用式（73.6）及 $s\le1$，便有

$$
\begin{aligned}
\max_{C,E}\operatorname{Tr}(Y_{r,\delta}E)
&\le1+\delta+4\rho\\
&\le1+\delta(1+4\sqrt r).
\end{aligned}
\tag{73.15}
$$

最后一步只用 $\rho\le\sqrt r\,\delta$。正负响应界分别对全部合法事件成立，故可以共同用于 $N$。

### 73.5 明确选择扰动参数

现在对每个固定 $r>0$ 选择

$$
\delta_r=\frac{1}{32(1+2r)}\le\frac1{32}<\frac14.
\tag{73.16}
$$

式（73.14）给

$$
\max_{C,E}-\operatorname{Tr}(Y_{r,\delta_r}E)
\le\frac98-\frac{23}{1024(1+2r)}.
\tag{73.17}
$$

对正响应，恒等式

$$
2(1+2r)-(1+4\sqrt r)=(2\sqrt r-1)^2\ge0
$$

使式（73.15）成为

$$
\max_{C,E}\operatorname{Tr}(Y_{r,\delta_r}E)
\le1+\frac{1+4\sqrt r}{32(1+2r)}\le\frac{17}{16}.
\tag{73.18}
$$

而式（73.17）的右侧对所有 $r\ge0$ 至少为

$$
\frac98-\frac{23}{1024}=\frac{1129}{1024}
>\frac{17}{16}.
$$

因此正负响应合并给

$$
N(H_r-K_{r,\delta_r})
\le\frac98-\frac{23}{1024(1+2r)}.
\tag{73.19}
$$

由切锥变分式及已证 $\gamma_r>1$，得到式（73.1）。这里参数和常数均显式，不以未计算的小量余项决定可行范围。

### 73.6 与大参数上界组合

第 71 节对 $r\ge8$ 给

$$
\gamma_r\le1+3(u_r-1),
\qquad u_r=\frac{r-\sqrt{r^2-4r}}2.
$$

小根满足 $u_r^2=r(u_r-1)$ 且 $1<u_r\le2$，所以

$$
\gamma_r\le1+\frac{12}{r}\qquad(r\ge8).
\tag{73.20}
$$

当 $r\ge192$ 时，式（73.20）给 $\gamma_r\le17/16$。当 $0<r\le192$ 时，式（73.1）给

$$
\gamma_r\le\frac98-\frac{23}{1024\cdot385}
=\frac98-\frac{23}{394240}.
$$

后一个上界大于 $17/16$，所以同一式对全部 $r>0$ 成立，证明式（73.2）。$\square$

显式常数没有确定真实最大系数或最大点；其意义是给第 72 节的统一严格间隙提供一个可以直接代入的下界。全部估计仍属于先固定 $r$、再令原缺陷趋零得到的系数函数，未据此交换双参数极限。

## 追加锚（本行以下为增补区）

## 74. 全压缩参数的一致尺度轮廓与最坏参数的集中

### 74.1 两个同时变化的参数

考虑第64节同一混合族 $R_{a,\varepsilon}$，其中 $0<a<1$、$0<\varepsilon<1$。完整事件最优修复误差仍为 $e(R_{a,\varepsilon})$，归一化缺陷为 $\varepsilon$。定义尺度比

$$
r=\frac{1-a}{\varepsilon}.
\tag{74.1}
$$

第70、71节的函数 $\gamma_r=\operatorname{dist}_N(H_r,\mathcal T)$ 在 $r\ge0$ 连续，$\gamma_0=1$，且在 $r\to\infty$ 时趋于一。置

$$
\Gamma=\max_{r>0}\gamma_r,\qquad
\mathcal A=\{r>0:\gamma_r=\Gamma\}.
\tag{74.2}
$$

前述结果保证 $\mathcal A$ 为非空紧集，包含于 $(0,\infty)$，并且 $1<\Gamma<9/8$。

**定理74.1（一致尺度轮廓）。** 在整个开压缩参数区间上，有

$$
\lim_{\varepsilon\downarrow0}
\sup_{0<a<1}
\left|
\frac{e(R_{a,\varepsilon})}{\varepsilon}
-\gamma_{(1-a)/\varepsilon}
\right|=0.
\tag{74.3}
$$

因此，对任意随 $\varepsilon\downarrow0$ 变化的合法参数 $a_\varepsilon$，如果

$$
\frac{1-a_\varepsilon}{\varepsilon}\longrightarrow r\in[0,\infty),
$$

则 $e(R_{a_\varepsilon,\varepsilon})/\varepsilon\to\gamma_r$；如果该比值趋于无穷，则误差比趋于一。

整个候选族的最坏比例也具有准确极限：

$$
\lim_{\varepsilon\downarrow0}
\sup_{0<a<1}\frac{e(R_{a,\varepsilon})}{\varepsilon}
=\Gamma.
\tag{74.4}
$$

若 $a_\varepsilon$ 渐近达到同一族的最坏比例，即

$$
\sup_{0<a<1}\frac{e(R_{a,\varepsilon})}{\varepsilon}
-\frac{e(R_{a_\varepsilon,\varepsilon})}{\varepsilon}
\longrightarrow0,
\tag{74.5}
$$

则必有

$$
\operatorname{dist}\left(
\frac{1-a_\varepsilon}{\varepsilon},\mathcal A
\right)\longrightarrow0.
\tag{74.6}
$$

特别地，这些参数满足 $1-a_\varepsilon=\Theta(\varepsilon)$。这并未断言最优尺度唯一。

### 74.2 有界尺度上的一致一阶展开

记 $R_0=|x+y\rangle\langle x+y|$，并沿用第70节的紧凸因果修复集合 $\mathcal C$、缩放集合

$$
\mathcal D_\varepsilon=\frac{\mathcal C-R_0}{\varepsilon},
\qquad
\mathcal T=\overline{\bigcup_{t>0}\mathcal D_t}.
\tag{74.7}
$$

若 $r\ge0$ 且 $r\varepsilon<1$，把 $a=1-r\varepsilon$ 代入候选，得到

$$
\begin{aligned}
R_{1-r\varepsilon,\varepsilon}
={}&|\sqrt{1-r\varepsilon}\,x+\sqrt{1-\varepsilon}\,y
+\sqrt r\,\varepsilon z\rangle
\langle\sqrt{1-r\varepsilon}\,x+\sqrt{1-\varepsilon}\,y
+\sqrt r\,\varepsilon z|\\
&+\varepsilon|\sqrt r\,x'-\sqrt{1-r\varepsilon}\,z'\rangle
\langle\sqrt r\,x'-\sqrt{1-r\varepsilon}\,z'|.
\end{aligned}
\tag{74.8}
$$

在 $r=0$ 时使用第71节已经定义的端点 $a=1$。对任意固定 $R<\infty$，存在常数 $C_R<\infty$，使充分小正 $\varepsilon$ 满足

$$
\sup_{0\le r\le R}
N\left(
\frac{R_{1-r\varepsilon,\varepsilon}-R_0}{\varepsilon}-H_r
\right)\le C_R\varepsilon.
\tag{74.9}
$$

为核对一致性，可将（74.8）逐矩阵元展开。只需对 $\sqrt{1-r\varepsilon}$ 和 $\sqrt{1-\varepsilon}$ 沿 $\varepsilon$ 作二阶 Taylor 估计。在紧集

$$
0\le r\le R,\qquad
0\le\varepsilon\le\frac1{2(1+R)}
$$

上，两个根号的被开方数均至少为 $1/2$，各矩阵元关于 $\varepsilon$ 的二阶导数连续且一致有界。因 $\sqrt r$ 在此紧参数集上连续有界，第二行外积同样满足这一性质。一阶项恰为第70节的 $H_r$，于是余项的迹范数一致为 $O_R(\varepsilon^2)$。再用 $N(X)\le2\|X\|_1$ 即得（74.9）。这里没有要求关于 $r$ 在零点可微。

### 74.3 切锥距离的紧参数一致收敛

定义

$$
d_\varepsilon(H)=\operatorname{dist}_N(H,\mathcal D_\varepsilon),
\qquad d_0(H)=\operatorname{dist}_N(H,\mathcal T).
$$

第70节已证明 $\mathcal D_\varepsilon$ 随 $\varepsilon\downarrow0$ 扩大，且对每个固定 $H$，

$$
d_\varepsilon(H)\downarrow d_0(H).
\tag{74.10}
$$

所有这些距离函数都具有同一个 $1$-Lipschitz 界。$r\mapsto H_r$ 连续，故 $\{H_r:0\le r\le R\}$ 紧。这使（74.10）在该参数集上一致。

具体地，给定 $\xi>0$，取有限个 $r_1,\ldots,r_k$，使每个 $H_r$ 都与某个 $H_{r_j}$ 的 $N$ 距离小于 $\xi$。对有限多个中心同时应用（74.10），充分小的 $\varepsilon$ 满足

$$
d_\varepsilon(H_{r_j})-d_0(H_{r_j})<\xi
\quad\text{对所有 }j.
$$

因为 $\mathcal D_\varepsilon\subset\mathcal T$，结合两个距离函数的 Lipschitz 性，有

$$
0\le d_\varepsilon(H_r)-d_0(H_r)<3\xi
\quad(0\le r\le R).
\tag{74.11}
$$

另一方面，范数正齐次性给准确等式

$$
\frac{e(R_{1-r\varepsilon,\varepsilon})}{\varepsilon}
=d_\varepsilon\left(
\frac{R_{1-r\varepsilon,\varepsilon}-R_0}{\varepsilon}
\right).
\tag{74.12}
$$

结合（74.9）、（74.11）和 $d_0(H_r)=\gamma_r$，得到

$$
\sup_{0\le r\le R}
\left|
\frac{e(R_{1-r\varepsilon,\varepsilon})}{\varepsilon}-\gamma_r
\right|\longrightarrow0.
\tag{74.13}
$$

这一步证明有界尺度中的共同变化结论，不依赖先后交换两个未验证的极限。

### 74.4 无界尺度由显式修复统一控制

现在考虑任意 $0<a<1$，置 $s=1-a$。若 $r=s/\varepsilon\ge8$，则 $\varepsilon\le s/8$，第66节的显式修复适用。其小根满足

$$
\varepsilon<p\le2\varepsilon,\qquad
p-\varepsilon=\frac{a\varepsilon p}{s-p}
\le\frac{8a}{3s}\varepsilon^2.
\tag{74.14}
$$

最后一式使用 $s-p\ge3s/4$。准确事件上界中的另一因子满足

$$
2+\frac{2(\sqrt a+\sqrt{\varepsilon s})}
{\sqrt{1-\varepsilon}+\sqrt{1-p}}<6.
$$

确实，$\varepsilon\le s/8\le1/8$、$p\le1/4$，故分母大于一，而分子括号中的两项和小于二。总事件的下界与这个修复上界合并，给出对所有这些参数同时成立的估计

$$
1\le\frac{e(R_{a,\varepsilon})}{\varepsilon}
\le1+\frac{16a}{r}\le1+\frac{16}{r}.
\tag{74.15}
$$

这里直接使用第66节修复，不需要第69节匹配下界所用的附加条件 $\varepsilon\le\sqrt a/16$。

第71节给同一尺度范围内

$$
1\le\gamma_r\le1+3(u_r-1)\le1+\frac{12}{r},
\tag{74.16}
$$

其中

$$
u_r-1=\frac{4/r}{(1+\sqrt{1-4/r})^2}\le\frac4r.
$$

因此，两个量同在 $[1,1+16/r]$ 中，遂有

$$
\left|\frac{e(R_{a,\varepsilon})}{\varepsilon}-\gamma_r\right|
\le\frac{16}{r}
\qquad(r\ge8).
\tag{74.17}
$$

给定误差容限，先取足够大的有限 $R\ge8$，使 $16/R$ 小于该容限；再对 $0\le r\le R$ 使用（74.13）。所有合法参数的尺度比均属于 $(0,1/\varepsilon)$，已被这两个区域覆盖。故得到（74.3）。各条共同变化路径的结论再由 $\gamma$ 的连续性与无穷端点极限推出。

### 74.5 最坏误差与实际参数尺度

记

$$
F_\varepsilon=\sup_{0<a<1}\frac{e(R_{a,\varepsilon})}{\varepsilon}.
$$

（74.3）给 $\limsup F_\varepsilon\le\Gamma$。反向，取任意 $r_*\in\mathcal A$，令 $a_\varepsilon=1-r_*\varepsilon$。充分小正 $\varepsilon$ 时它属于 $(0,1)$，且第70节给对应比例趋于 $\gamma_{r_*}=\Gamma$。故 $\liminf F_\varepsilon\ge\Gamma$，证明（74.4）。

最后，假设（74.5），记 $r_\varepsilon=(1-a_\varepsilon)/\varepsilon$。由（74.3）、（74.4），

$$
\gamma_{r_\varepsilon}\longrightarrow\Gamma>1.
\tag{74.18}
$$

由于 $\gamma_r$ 在零与无穷两个端点均趋于一，存在 $0<d<R<\infty$，使这些渐近最坏参数最终全部满足 $r_\varepsilon\in[d,R]$。如果到 $\mathcal A$ 的距离不趋零，可取一个距离统一有正下界的子列，再在此紧区间取收敛子列 $r_{\varepsilon_j}\to r_\infty$。（74.18）和连续性给 $\gamma_{r_\infty}=\Gamma$，所以 $r_\infty\in\mathcal A$，与距离下界矛盾。得到（74.6），也得到 $d\varepsilon\le1-a_\varepsilon\le R\varepsilon$。证明完毕。

一致尺度轮廓同时描述固定参数下的比值极限、临界移动参数的一阶比例间隙及两端退化行为；固定参数的二阶超额仍由第69节的更精细估计承担。它只针对本候选族与完整 tester 合同；没有把 $\Gamma$ 识别为所有有限量子过程的通用常数。

## 追加锚（本行以下为增补区）

## 75. 移动压缩系数的显式正下界

### 75.1 一个固定尺度与最坏系数的双侧区间

沿用第 70 节完整 tester 范数 $N$、闭因果切锥 $\mathcal T$ 以及准确极限系数

$$
\gamma_r=\min_{K\in\mathcal T}N(H_r-K).
$$

本节固定 $r=1$。不限制切向修复的矩阵分块或复相干，也不假设最优修复属于某个显式参数族。

**定理 75.1。** 有明确的严格下界

$$
\gamma_1>\frac{401}{400}.
\tag{75.1}
$$

因此第 71、74 节的最坏渐近系数满足

$$
\frac{401}{400}<\Gamma:=\max_{r>0}\gamma_r
\le\frac98-\frac{23}{394240}.
\tag{75.2}
$$

右侧使用第 73 节的显式统一上界。这给出最坏超额的明确正下界 $\Gamma-1>1/400$，不将任一端点常数识别为最优值。

### 75.2 同一总事件的近饱和约束

记

$$
x=|000\rangle,\quad x'=|001\rangle,\quad y=|101\rangle,
\quad z=|110\rangle,\quad z'=|111\rangle,
\quad j=|100\rangle,\quad w=x+y.
$$

固定任意 $K\in\mathcal T$，令 $Y=H_1-K$。切锥的准确刻画给

$$
\operatorname{Tr}_D K=I_A\otimes\dot\sigma,
\qquad\dot\sigma=\dot\sigma^*,\quad\operatorname{Tr}\dot\sigma=0,
\qquad P_0KP_0\succeq0,
\tag{75.3}
$$

其中 $P_0$ 是 $w^\perp$ 上的正交投影。这里不要求 $K$ 本身为正。

反设对某个

$$
0\le g\le\frac1{400}
$$

有

$$
N(Y)\le1+g.
\tag{75.4}
$$

选择合法总事件

$$
C_+=|00\rangle\langle00|+|11\rangle\langle11|,
\qquad\Pi_+=C_+\otimes I_D,
\qquad X=\Pi_+Y\Pi_+.
$$

第 70 节的一阶早边缘和式（75.3）给 $\operatorname{Tr}X=1$。$X$ 的正谱投影是合法事件，所以其正谱和至多 $1+g$，负谱绝对值之和至多 $g$。在 $\operatorname{ran}\Pi_+$ 上，

$$
X+gI\succeq0,
\qquad\langle v|X|v\rangle\le1+g
\quad\text{对每个单位向量 }v.
\tag{75.5}
$$

第 70 节式（70.8）在 $r=1$ 时给

$$
\begin{gathered}
(H_{xx},H_{x'x'},H_{yy},H_{zz},H_{z'z'})=(-1,1,-1,0,1),\\
H_{xz}=1,\qquad H_{x'z'}=-1,\qquad H_{xy}=-1.
\end{gathered}
\tag{75.6}
$$

由于 $z\perp w$，令 $\alpha=K_{zz}$，切向正性给 $\alpha\ge0$。而 $X_{zz}=-\alpha$，故式（75.5）给

$$
0\le\alpha\le g.
$$

在 $x,z$ 上取 $X+gI$ 的二阶主子式，得到

$$
\begin{aligned}
|1-K_{xz}|^2
&\le(X_{xx}+g)(g-\alpha)\\
&\le(1+2g)g.
\end{aligned}
\tag{75.7}
$$

定义

$$
d_g=\sqrt{(1+2g)g},\qquad
\ell_g=\frac{(1-d_g)^2}{1+g}.
\tag{75.8}
$$

本节参数范围保证 $d_g<1$；因此即使 $K_{xz}$ 为任意复数，式（75.7）也给 $|K_{xz}|\ge1-d_g$。

### 75.3 因果偏迹与核正性共同强迫对角质量

令

$$
t=K_{x'x'},\qquad\beta=K_{z'z'},\qquad
p=\dot\sigma_{11}=\alpha+\beta,
\qquad s=-K_{yy}.
$$

$x',z'$ 均在 $w^\perp$，所以 $t,\beta\ge0$。式（75.5）在相应对角上还给

$$
t\le1+g,\qquad\beta\le1+g.
\tag{75.9}
$$

因果偏迹的跨输入 $00,11$ 元为零，故

$$
K_{x'z'}=-K_{xz}.
$$

将 $P_0KP_0\succeq0$ 压缩到 $x',z'$，得到

$$
t\beta\ge|K_{x'z'}|^2=|K_{xz}|^2\ge(1-d_g)^2.
\tag{75.10}
$$

结合式（75.9），这迫使

$$
t\ge\ell_g,\qquad\beta\ge\ell_g,
\qquad p=\alpha+\beta\ge\ell_g.
\tag{75.11}
$$

由于 $j\perp w$，还有 $K_{jj}\ge0$。式（75.3）在 $AB=10$ 上给 $K_{jj}+K_{yy}=-p$，所以

$$
s=p+K_{jj}\ge p\ge\ell_g.
\tag{75.12}
$$

同一因果偏迹在 $AB=00$ 上给

$$
K_{xx}=-p-t.
$$

再使用 $x-y\perp w$ 的切向正性，

$$
0\le\langle x-y|K|x-y\rangle
=-p-t-s-2\operatorname{Re}K_{xy}.
$$

由式（75.6），这给出同一实际方向 $Y$ 的约束

$$
\begin{gathered}
Y_{xx}=p+t-1,\qquad Y_{yy}=s-1,\\
\operatorname{Re}Y_{xy}\ge\frac{p+t+s}{2}-1.
\end{gathered}
\tag{75.13}
$$

从而

$$
\langle w|Y|w\rangle\ge2(p+t+s-2).
\tag{75.14}
$$

至此没有删去任何未跟踪的相干项，也没有将分别可达的矩阵元界换成另一修复。

### 75.4 一个固定反馈事件给出定量矛盾

选择固定反馈

$$
C=\operatorname{diag}\left(\frac14,1,\frac34,0\right),
\qquad L=C^{1/2}\otimes I_D,
\qquad v_+=\frac{\sqrt3}{2}x+\frac12y.
$$

它满足 $\operatorname{Tr}_A C=I_B$，且 $v_+$ 为单位向量。因此

$$
E=L|v_+\rangle\langle v_+|L
=\frac3{16}|w\rangle\langle w|
\tag{75.15}
$$

是合法事件；它在整个推导中不随 $K$ 变化。

由一阶早边缘与因果约束，同一反馈总事件的响应为

$$
\operatorname{Tr}(Y(C\otimes I_D))=-\frac34.
$$

其互补事件 $C\otimes I_D-E$ 也合法。因此，式（75.14）给

$$
\begin{aligned}
N(Y)
&\ge-\operatorname{Tr}\bigl(Y(C\otimes I_D-E)\bigr)\\
&=\frac34+\frac3{16}\langle w|Y|w\rangle\\
&\ge\frac38(p+t+s)
\ge\frac98\ell_g.
\end{aligned}
\tag{75.16}
$$

现在仅需比较显式常数。若 $0\le g\le1/400$，则

$$
d_g^2=(1+2g)g\le\frac{201}{80000}<\frac1{361},
$$

最后一步等价于 $201\cdot361=72561<80000$。所以 $d_g<1/19$，式（75.8）、（75.16）给

$$
N(Y)\ge\frac98\ell_g
>\frac98\frac{(18/19)^2}{1+g}
=\frac{729}{722(1+g)}.
\tag{75.17}
$$

若误差假设（75.4）成立，便必须有

$$
(1+g)^2>\frac{729}{722}.
$$

但同一参数范围内

$$
(1+g)^2\le\left(\frac{401}{400}\right)^2
=\frac{160801}{160000}<\frac{729}{722},
\tag{75.18}
$$

矛盾。这排除了所有满足式（75.4）的 $K\in\mathcal T$。

特别地，没有切向修复能达到误差 $401/400$ 或更小。第 70 节已经证明切锥距离的极小值达到，所以严格下界（75.1）成立。再用 $\Gamma\ge\gamma_1$ 与第 73 节的显式统一上界，即得（75.2）。$\square$

该下界使用固定尺度 $r=1$ 和一个固定补事件，未求解真实最优切向修复，也不定位使 $\gamma_r$ 最大的参数。它提供了明确的系数下界，与同一完整 tester 合同下的显式统一上界共同约束最坏渐近误差。

## 追加锚（本行以下为增补区）

## 76. 最坏修复系数的有限对称约化与实代数性质

### 76.1 从完整复 tester 问题到四个固定荷块

第 70—75 节已经给出完整 tester 合同下的准确系数

$$
\gamma_r=\min_{K\in\mathcal T}N(H_r-K),\qquad r\ge0,
$$

其中最小值达到，$\gamma_0=1$，$\gamma_r>1$ 对每个 $r>0$ 成立，两个参数端点的极限均为一。本节不预设最优修复的秩，也不将某个数值矩阵的零元提升为普遍结构。

沿用三个量子比特的顺序 $A,B,D$，并将八个标准基向量写为

$$
\begin{gathered}
x=|000\rangle,\quad x'=|001\rangle,\quad h=|010\rangle,\quad k=|011\rangle,\\
j=|100\rangle,\quad y=|101\rangle,\quad z=|110\rangle,\quad z'=|111\rangle.
\end{gathered}
$$

令 $w=x+y$、$P_0=I-ww^*/2$。对 $u\ge0$ 定义 $H(u)=H_{u^2}$，即

$$
\begin{aligned}
H(u)={}&-\frac12\bigl[(u^2x+y)w^*+w(u^2x+y)^*\bigr]\\
&+u(zw^*+wz^*)+(ux'-z')(ux'-z')^*.
\end{aligned}
\tag{76.1}
$$

它的全部矩阵元是 $u$ 的有理系数多项式。

定义四阶局部酉算符

$$
U=\operatorname{diag}(1,i)_A\otimes
\operatorname{diag}(1,-i)_B\otimes
\operatorname{diag}(1,-i)_D.
\tag{76.2}
$$

其互异特征值对应子空间为

$$
\begin{array}{c|c}
1&\operatorname{span}(x,y,z)\\
-i&\operatorname{span}(x',h,z')\\
i&\operatorname{span}(j)\\
-1&\operatorname{span}(k).
\end{array}
\tag{76.3}
$$

**定理 76.1（精确实块约化）。** 计算 $\gamma_{u^2}$ 时，可以将切向修复 $K$ 限制为相对于式（76.3）的实对称块对角矩阵。其块大小为 $3,3,1,1$；这个限制保持最优值，并存在达到最优值的此类 $K$。

证明。由式（76.1），$Uw=w$ 且 $UH(u)U^*=H(u)$。若 $K\in\mathcal T$，则

$$
\operatorname{Tr}_D(UKU^*)
=I_A\otimes U_B\dot\sigma U_B^*,
\qquad P_0UKU^*P_0=U(P_0KP_0)U^*\succeq0.
$$

所以 $UKU^*\in\mathcal T$。另一方面，将合法 tester $C,E$ 同时变换为

$$
C'=(U_A\otimes U_B)C(U_A\otimes U_B)^*,\qquad E'=UEU^*,
$$

仍保持 $C'\succeq0$、$\operatorname{Tr}_A C'=I_B$ 和 $0\preceq E'\preceq C'\otimes I_D$。该变换可逆，因此 $N(UXU^*)=N(X)$。

对 $K$ 作有限平均

$$
\mathcal A(K)=\frac14\sum_{a=0}^{3}U^aK(U^*)^a.
\tag{76.4}
$$

凸性和 $H(u)$ 的不变性给

$$
\mathcal A(K)\in\mathcal T,
\qquad N(H(u)-\mathcal A(K))\le N(H(u)-K).
$$

不同特征值之间的矩阵元在四项平均中消去，所以 $\mathcal A(K)$ 正好具有式（76.3）的块形。

标准基中的复共轭同样保持切锥和 tester 可行集，且 $H(u)$ 为实矩阵。因此再用

$$
K_{\mathbb R}=\frac12\bigl(\mathcal A(K)+\overline{\mathcal A(K)}\bigr)
$$

替换，仍然可行且不增目标值。它是同一块形的实对称矩阵。取第 70 节保证存在的原问题最优修复，即得最优值保持及达到性。$\square$

此处只约去由实际局部酉对称强制消失的块间相干；每个三维块内部的所有实相干仍被保留。

**定理 76.1a（切向修复的准确十实参数表示）。** 在定理 76.1 的实块空间内，全部因果线性约束可以完全消去。具体地，令

$$
\theta=(p,t,\zeta,\alpha,\beta,d,e,f,\ell,m)\in\mathbb R^{10},
$$

相对于有序块 $(x,y,z)$、$(x',h,z')$、$(j)$、$(k)$ 定义

$$
\begin{aligned}
K(\theta)&=M_0(\theta)\oplus M_1(\theta)\oplus[\alpha]\oplus[\beta],\\
M_0(\theta)&=
\begin{pmatrix}
-p-t&d&e\\
d&-p-\alpha&f\\
e&f&\zeta
\end{pmatrix},\\
M_1(\theta)&=
\begin{pmatrix}
t&\ell&-e\\
\ell&p-\beta&m\\
-e&m&p-\zeta
\end{pmatrix}.
\end{aligned}
\tag{76.4a}
$$

则 $\mathcal T$ 与实块空间的交恰由这些矩阵中满足

$$
\alpha\ge0,\qquad\beta\ge0,\qquad M_1(\theta)\succeq0,
\qquad
\begin{pmatrix}
-2p-t-\alpha-2d&e-f\\
e-f&\zeta
\end{pmatrix}\succeq0
\tag{76.4b}
$$

者构成；每个这样的矩阵对应唯一的 $\theta$。因此完整 tester 系数也准确等于

$$
\gamma_{u^2}
=\min_{\theta\text{ 满足（76.4b）}}N(H(u)-K(\theta)),
\tag{76.4c}
$$

且这个最小值达到。没有对两个正块的秩作限制。

证明。先取任意实块矩阵 $K\in\mathcal T$。因果偏迹为 $I_A\otimes\dot\sigma$；由四阶相位不变性，$\dot\sigma$ 对角且迹零，所以可唯一写为 $\operatorname{diag}(-p,p)$。定义

$$
\begin{gathered}
t=K_{x'x'},\quad\zeta=K_{zz},\quad
\alpha=K_{jj},\quad\beta=K_{kk},\\
d=K_{xy},\quad e=K_{xz},\quad f=K_{yz},
\quad\ell=K_{x'h},\quad m=K_{hz'}.
\end{gathered}
$$

所有这些数均实。偏迹在四个 $AB$ 对角位置的约束分别为

$$
K_{xx}+t=-p,\qquad
K_{hh}+\beta=p,\qquad
\alpha+K_{yy}=-p,\qquad
\zeta+K_{z'z'}=p.
$$

在非对角位置，实块形使除 $AB=00,11$ 及其转置外的所有偏迹项自动为零；该剩余位置的因果条件恰为

$$
K_{xz}+K_{x'z'}=0.
$$

这五条等式给出式（76.4a）的全部指定矩阵元。反向，逐项取 $D$ 偏迹可直接验证，式（76.4a）对任意实参数都满足

$$
\operatorname{Tr}_D K(\theta)=I_A\otimes\operatorname{diag}(-p,p).
$$

因此没有剩余的因果线性条件。上述各条矩阵元及任一因果对角和又可恢复全部参数，故参数表示唯一。

再核对核压缩正性。因为 $w=x+y$，有正交子空间分解

$$
w^\perp
=\operatorname{span}(x-y,z)
\oplus\operatorname{span}(x',h,z')
\oplus\mathbb Cj\oplus\mathbb Ck.
$$

实块形使核压缩在这四个子空间之间没有耦合。第一块在基 $(x-y,z)$ 中的二次型矩阵正是

$$
\begin{pmatrix}
K_{xx}+K_{yy}-2K_{xy}&K_{xz}-K_{yz}\\
K_{zx}-K_{zy}&K_{zz}
\end{pmatrix}
=
\begin{pmatrix}
-2p-t-\alpha-2d&e-f\\
e-f&\zeta
\end{pmatrix}.
$$

向量 $x-y$ 未归一化，但基变换为可逆合同变换，因此该矩阵半正定与对应子空间上的正性等价。其余三个块分别为 $M_1(\theta)$、$[\alpha]$、$[\beta]$。所以 $P_0KP_0\succeq0$ 恰等价于式（76.4b）。由第 70 节的准确切锥刻画，得到双向参数化。

最后应用定理 76.1 的最优值保持及达到性，即得式（76.4c）。此处只消去了已明确的线性等式；块内相干以及核压缩的所有允许秩均保留。$\square$

这一表示使修复变量从实块空间的十四维降为十个实参数，并把它自身的正性要求准确化为一个二阶正块、一个三阶正块及两个非负标量。事件范数 $N$ 仍取全部合法复 tester，后面的双向半定上界算子 继续承担其完整约束。

### 76.2 保留全部事件的有限半定规划

令 $\mathcal B$ 表示式（76.3）的实对称块对角矩阵空间。它作为实向量空间的维数是 $6+6+1+1=14$，不计随后施加的线性等式。

**定理 76.2（系数的准确半定规划）。** $\gamma_{u^2}$ 是下列有限优化问题的达到最小值：最小化实数 $t$，变量为

$$
K,P_+,P_-\in\mathcal B,\qquad p,a_+,b_+,a_-,b_-\in\mathbb R,
$$

约束为

$$
\begin{gathered}
P_0KP_0\succeq0,\qquad
\operatorname{Tr}_D K=I_A\otimes\operatorname{diag}(-p,p),\\
P_+\succeq0,\quad P_+-H(u)+K\succeq0,\\
P_-\succeq0,\quad P_-+H(u)-K\succeq0,\\
\operatorname{Tr}_D P_\pm=I_A\otimes\operatorname{diag}(a_\pm,b_\pm),\\
a_++b_+\le t,\qquad a_-+b_-\le t.
\end{gathered}
\tag{76.5}
$$

对每个固定 $u$，上述约束都是实仿射矩阵不等式与线性等式。

证明。沿用第 55 节引理 55.1 的单向支持函数 $h$ 及其达到的对偶表示。完整范数满足

$$
N(X)=\max\{h(X),h(-X)\}.
$$

所以 $N(X)\le t$ 当且仅当存在两个半定上界算子 $P_\pm$，分别满足 $P_+\succeq X$、$P_-\succeq-X$，且它们的因果偏迹质量均不超过 $t$。这是同时保留两个符号的对偶约束，并未删去非因果方向的总事件读数。

先取定理 76.1 的最优 $K\in\mathcal B$，于是 $X=H(u)-K$ 也在 $\mathcal B$。对每个符号，取达到单向最优值的对偶见证，然后作式（76.4）的四项平均及复共轭平均。$P_\pm\succeq0$ 与 $P_\pm\succeq\pm X$ 均被保持，偏迹形式及质量也被保持。所得 $P_\pm$ 属于 $\mathcal B$。

在偏迹等式中，有限平均同时使 $n_\pm$ 与 $U_B=\operatorname{diag}(1,-i)$ 对易，故 $n_\pm$ 对角；同样，$\dot\sigma$ 对角且迹零，恰写成 $\operatorname{diag}(-p,p)$。于是得到式（76.5）的可行点，取 $t=N(H(u)-K)$ 即达到 $\gamma_{u^2}$。

反方向，任意满足式（76.5）的变量均给 $K\in\mathcal T$。第 55 节的对偶上界分别给 $h(H(u)-K)\le t$ 与 $h(K-H(u))\le t$，故 $\gamma_{u^2}\le N(H(u)-K)\le t$。两方向合并得到准确等价。$\square$

因此这是一份对全部合法复 tester 有效的有限实问题。块内可以继续出现满秩矩阵；式（76.5）没有给秩另设假设。

### 76.3 从有限多项式合同到实代数系数

本节使用实代数几何的标准消元结论：有理系数多项式等式与不等式定义的集合，在有限次投影和补集下仍为有理系数半代数集；等价地，实闭域的一阶公式可消去量词。这是 Tarski–Seidenberg 定理及实闭域量词消去的内容，相关算法背景见 Basu–Pollack–Roy，*Algorithms in Real Algebraic Geometry*，[第二版](https://doi.org/10.1007/3-540-33099-2)。这里只使用该成熟结果，不把有限矩阵表示本身当作代数性的证明。

**定理 76.3（系数图与代数参数）。** 函数 $r\mapsto\gamma_r$ 在 $r\ge0$ 上的图是有理系数半代数集。特别地，每个非负实代数参数 $r$ 都给实代数数 $\gamma_r$。

证明。实对称矩阵半正定当且仅当全部主子式非负。$P_0$ 是固定有理矩阵，而 $H(u)$ 的矩阵元是有理系数多项式。因此，将式（76.5）的实变量展开后，全部可行性条件是一份有限有理多项式合同，记作 $\mathsf F(u,t,\xi)$，其中 $\xi$ 汇总矩阵与标量见证。

由定理 76.2 的达到性，$u\ge0$ 时

$$
\exists\xi\;\mathsf F(u,t,\xi)
\quad\Longleftrightarrow\quad t\ge\gamma_{u^2}.
\tag{76.6}
$$

因而 $\gamma_{u^2}$ 的图准确由公式

$$
u\ge0,\qquad
\exists\xi\;\mathsf F(u,t,\xi),\qquad
\neg\exists(s,\zeta)\;\bigl[s<t\ \wedge\ \mathsf F(u,s,\zeta)\bigr]
\tag{76.7}
$$

定义。量词消去给出其有理半代数性。再加入 $r=u^2$ 并投影掉 $u$，得到 $\gamma_r$ 的图。

固定一个实代数 $r_0\ge0$。它可以由一个有理多项式及隔离该根的有理区间定义，因此再固定 $r=r_0$ 并投影后，单点集合 $\{\gamma_{r_0}\}$ 仍是有理半代数集。

任何有理半代数单点都是实代数点：在一个无量词定义中只出现有限多个有理多项式；若单点坐标不是它们中任何非零多项式的根，则所有多项式的符号在该点附近不变，使定义不能只选出一个点，矛盾。因此 $\gamma_{r_0}$ 是实代数数。$\square$

这里没有声称 $\gamma_r$ 是 $r$ 的一个全局有理函数，也没有通过有限个数值样本拟合代数方程。

### 76.4 最坏压缩系数与最大参数集的有限代数描述

**定理 76.4（最坏系数的实代数性）。** 第 71、74 节的

$$
\Gamma=\max_{r>0}\gamma_r
$$

是实代数数。最大参数集

$$
\mathcal M=\{r>0:\gamma_r=\Gamma\}
\tag{76.8}
$$

是非空紧集，并且是有限多个实代数单点与闭区间的并；每个非退化区间的两个端点也都是正实代数数。特别地，至少存在一个正实代数参数达到最坏系数。

证明。先用第 71 节的连续性、两端极限为一以及 $\Gamma>1$，将 $\mathcal M$ 限制在某个 $[a,b]\subset(0,\infty)$ 内。它是非空闭集，故紧。

记定理 76.3 的图关系为 $\mathsf G(r,t)$。$\Gamma$ 是下列公式唯一选出的 $t$：

$$
\bigl[\exists r>0\;\mathsf G(r,t)\bigr]
\ \wedge\
\neg\exists(s,v)\;\bigl[s>0\ \wedge\ \mathsf G(s,v)\ \wedge\ v>t\bigr].
\tag{76.9}
$$

由于 $\mathsf G$ 为有理半代数关系，量词消去使该单点集合也为有理半代数集。定理 76.3 证明末尾的单点论证给出 $\Gamma$ 的实代数性。

同理，把式（76.9）与 $\mathsf G(r,t)$ 联合并消去 $t$，得到 $\mathcal M$ 的有理半代数定义。实直线上的半代数集是有限多个点与区间的并：取无量词定义中所有非零多项式的实根，相邻根之间全部符号恒定；有限个根将实线分成有限个这样的区间与点。紧性排除无界区间和缺失的有限端点，因此可写成有限个闭区间与孤立点。全部有限边界点是上述有理多项式的根，所以为实代数数。任取一个孤立点或区间端点便得到代数最大参数。$\square$

结合第 75 节，本模型的同一个实代数常数满足

$$
\frac{401}{400}<\Gamma\le\frac98-\frac{23}{394240}.
\tag{76.10}
$$

量词消去给出了原则上可终止的精确求解路线，但本节没有执行它、没有给出 $\Gamma$ 的最小多项式或隔离区间，也没有排除最大值平台。实际求解的运算成本仍是另一个问题。

这里可以准确连接静态表示与继续研究的接口：完整 tester 修复合同先由局部相位对称约为固定大小的矩阵关系，再由有限多项式合同约束最坏误差及其参数。静态编码保留了可验证的优化条件；它本身不提供一次低成本的最优值计算。

## 追加锚（本行以下为增补区）

## 77. 统一缩放轮廓的幂次误差界与最坏尺度的稳定性

### 77.1 有限代数结构给趋零量一个幂次上界

第 74 节证明了全压缩参数的统一极限，第 76 节把准确系数及其最大参数集写成有限实多项式关系。本节将两者连接：在同一个有限量子模型内，统一误差不只是趋零，还必然具有某个正幂次的上界。这里证明幂次存在，不计算最优指数或常数。

**引理 77.1（一元半代数趋零量的幂次界）。** 设 $f:(0,t_0)\to[0,\infty)$ 的图为半代数集，且 $f(t)\to0$ 当 $t\downarrow0$。则存在整数 $m\ge1$、常数 $C>0$ 和 $t_1>0$，使

$$
f(t)\le Ct^{1/m}\qquad(0<t<t_1).
\tag{77.1}
$$

证明。对函数图取一个由有限个非零实多项式的符号条件组成的无量词定义，恒零多项式可先从定义中删去。在每个图点 $(t,f(t))$，至少一个定义多项式为零。否则全部多项式的符号在该点的某个二维开邻域内不变，定义会把整个邻域都包含进函数图，与每个 $t$ 只有一个函数值矛盾。

令 $P(t,y)$ 为这些非零多项式的乘积，便有非零多项式满足

$$
P(t,f(t))=0\qquad(0<t<t_0).
$$

除去 $P$ 的最大公共 $t$ 幂因子，不改变 $t>0$ 上的等式，并保证 $P(0,y)$ 不是零多项式。由于 $f(t)\to0$，连续性给 $P(0,0)=0$。设其在 $y=0$ 的零点重数为 $m\ge1$。则在充分小的 $y\ge0$ 上存在 $c>0$，使

$$
|P(0,y)|\ge c y^m.
$$

而 $P(t,y)-P(0,y)$ 被 $t$ 整除，所以在一个固定小矩形上有

$$
|P(t,y)-P(0,y)|\le C_0 t.
$$

对充分小的 $t>0$ 代入 $y=f(t)$，得到 $cf(t)^m\le C_0t$，即式（77.1）。常数可放大为严格正数，因此也包含 $f$ 最终恒零的情形。$\square$

这是本节所需的幂次控制的完整证明；没有预先给趋零速度加解析性假设。

### 77.2 原始修复误差也是同一类有限代数对象

将第 64 节的混合量子比特族写为

$$
\begin{aligned}
r_0(a,\varepsilon)
&=\sqrt a\,x+\sqrt{\varepsilon(1-a)}\,z+\sqrt{1-\varepsilon}\,y,\\
r_1(a,\varepsilon)
&=\sqrt{1-a}\,x'-\sqrt{\varepsilon a}\,z',\\
R_{a,\varepsilon}&=r_0r_0^*+r_1r_1^*.
\end{aligned}
\tag{77.2}
$$

记 $\mathcal C$ 为第 70 节的同一个因果修复集合，并令

$$
e(a,\varepsilon)=\min_{S\in\mathcal C}N(R_{a,\varepsilon}-S),
\qquad0<a<1,\quad0<\varepsilon<1.
$$

**引理 77.2（原修复值的半代数性）。** $e(a,\varepsilon)$ 的图是有理系数半代数集。

证明。引入非负实变量 $A,B,E,C$，满足

$$
A^2=a,\quad B^2=1-a,\quad E^2=\varepsilon,\quad C^2=1-\varepsilon.
$$

这些条件唯一指定相应正平方根，式（77.2）的向量成为 $Ax+EBz+Cy$ 与 $Bx'-EAz'$，全部矩阵元均为有理系数多项式。

修复的约束为

$$
S\succeq0,\qquad
\operatorname{Tr}_D S=I_A\otimes\sigma,\qquad
\sigma\succeq0,\quad\operatorname{Tr}\sigma=1.
\tag{77.3}
$$

再对 $X=R_{a,\varepsilon}-S$ 使用第 55 节的两个符号对偶，上界 $N(X)\le t$ 等价于存在厄米矩阵 $P_\pm,n_\pm$，使

$$
\begin{gathered}
P_\pm\succeq0,\qquad P_\pm\succeq\pm X,\\
\operatorname{Tr}_D P_\pm=I_A\otimes n_\pm,
\qquad\operatorname{Tr}n_\pm\le t.
\end{gathered}
\tag{77.4}
$$

每个复厄米矩阵以实部和虚部作为实变量。正性可用全部厄米主子式的非负性表达，等价地也可实化为实对称半定矩阵；因而式（77.3）—（77.4）是有限有理多项式条件。

$\mathcal C$ 是非空紧集：正性与偏迹归一化给 $\operatorname{Tr}S=2$，而其余条件闭合。因此连续目标的极小值达到。对偶最优值也由第 55 节保证达到，所以在上述可行性公式中投影掉矩阵见证，准确得到 $t\ge e(a,\varepsilon)$。再排除同参数下的所有更小可行 $t$，正如式（76.7），得到函数图的有理半代数定义。$\square$

### 77.3 全压缩范围的统一幂次误差

定义实际统一偏差

$$
D(\varepsilon)
=\sup_{0<a<1}
\left|
\frac{e(a,\varepsilon)}{\varepsilon}
-\gamma_{(1-a)/\varepsilon}
\right|.
\tag{77.5}
$$

**定理 77.3（统一轮廓存在正幂次速率）。** 存在正有理数 $\alpha>0$、常数 $C>0$ 及 $\varepsilon_0>0$，使

$$
\sup_{0<a<1}
\left|
\frac{e(a,\varepsilon)}{\varepsilon}
-\gamma_{(1-a)/\varepsilon}
\right|
\le C\varepsilon^\alpha
\qquad(0<\varepsilon<\varepsilon_0).
\tag{77.6}
$$

证明。引理 77.2 与定理 76.3 给式（77.5）中被取上确界函数的半代数性；除法只在 $\varepsilon>0$ 上使用，可通过乘法等式定义。对固定 $\varepsilon$，上确界有限：候选过程和修复的迹固定，完整 tester 集紧，而 $\gamma_r\le9/8$。

有限上确界仍有半代数图。具体地，$d=D(\varepsilon)$ 由“$d$ 是所有上述值的上界，且不存在更小的上界”这一有限实变量量词公式定义；Tarski–Seidenberg 消元适用于这份公式。这里没有把开区间 $0<a<1$ 上的上确界偷换为必然达到的最大值。

第 74 节已经独立证明 $D(\varepsilon)\to0$。因此对 $D$ 应用引理 77.1，得到式（77.6），其中可取 $\alpha=1/m$。$\square$

记完整压缩族的最坏归一化误差为

$$
E_*(\varepsilon)=\sup_{0<a<1}\frac{e(a,\varepsilon)}{\varepsilon}.
$$

**推论 77.4（最坏误差的幂次余项）。** 在适当缩小 $\varepsilon_0$ 后，同一 $\alpha,C$ 满足

$$
|E_*(\varepsilon)-\Gamma|\le C\varepsilon^\alpha,
\qquad
\left|\sup_{0<a<1}e(a,\varepsilon)-\Gamma\varepsilon\right|
\le C\varepsilon^{1+\alpha}.
\tag{77.7}
$$

证明。上界直接来自 $\gamma_r\le\Gamma$ 与定理 77.3。取某个固定最大参数 $r_*\in\mathcal M$；当 $\varepsilon<1/r_*$ 时，$a=1-r_*\varepsilon$ 属于 $(0,1)$，于是同一统一误差界给 $E_*(\varepsilon)\ge\Gamma-C\varepsilon^\alpha$。再乘以正数 $\varepsilon$ 得第二式。$\square$

### 77.4 近最坏压缩尺度的定量定位

第 74 节已经证明渐近最坏尺度靠近 $\mathcal M$。下面保留有限近优误差，给出相应的幂次稳定界。

**定理 77.5（近最坏尺度的稳定性）。** 存在正有理数 $\alpha,\beta$、常数 $C_1,C_2>0$、$\delta_0>0$ 及 $\varepsilon_1>0$，使对任意

$$
0<\varepsilon<\varepsilon_1,\qquad
0\le\delta\le\delta_0,\qquad0<a<1,
$$

只要

$$
\frac{e(a,\varepsilon)}{\varepsilon}
\ge E_*(\varepsilon)-\delta,
\tag{77.8}
$$

就有

$$
\operatorname{dist}\left(\frac{1-a}{\varepsilon},\mathcal M\right)
\le C_1\bigl(\delta+C_2\varepsilon^\alpha\bigr)^\beta.
\tag{77.9}
$$

证明。令 $q(r)=\Gamma-\gamma_r$。第 71 节的两端极限与 $\Gamma>1$ 使我们可以选有理数 $0<c<d$，令 $I=[c,d]$，使 $\mathcal M$ 位于 $I$ 的内部，且对 $r\notin I$ 有

$$
q(r)>\frac{\Gamma-1}{2}.
\tag{77.10}
$$

在此固定紧区间上，定义

$$
\omega(t)=\max\{\operatorname{dist}(r,\mathcal M):
 r\in I,\ q(r)\le t\},\qquad t\ge0.
\tag{77.11}
$$

该集合总是非空，因为包含 $\mathcal M$；连续性和紧性保证最大值存在。$\mathcal M$ 与 $q$ 半代数，距离也半代数：可用非负平方根与紧集上最近点的最小性公式定义。因此 $\omega$ 为非负半代数函数。

并且 $\omega(t)\to0$ 当 $t\downarrow0$。否则可选趋零的 $t_n$ 及对应最大点 $r_n\in I$，使距离有固定正下界。紧性给收敛子列 $r_n\to r$，连续性给 $q(r)=0$，即 $r\in\mathcal M$，与距离下界矛盾。

引理 77.1 因而给某个正有理数 $\beta$ 及常数 $C_1$，使

$$
\omega(t)\le C_1t^\beta
$$

对充分小的 $t\ge0$ 成立；$t=0$ 时两侧均为零。

对满足式（77.8）的 $a,\varepsilon$，令 $r=(1-a)/\varepsilon$。定理 77.3 及推论 77.4 给

$$
\begin{aligned}
\gamma_r
&\ge\frac{e(a,\varepsilon)}{\varepsilon}-C\varepsilon^\alpha\\
&\ge E_*(\varepsilon)-\delta-C\varepsilon^\alpha\\
&\ge\Gamma-\delta-2C\varepsilon^\alpha.
\end{aligned}
$$

因此 $q(r)\le\delta+2C\varepsilon^\alpha$。选 $\delta_0,\varepsilon_1$ 足够小，使该上界小于式（77.10）的阈值，同时位于 $\omega$ 的幂次界适用区间。于是 $r\in I$，代入式（77.11）即得（77.9），取 $C_2=2C$。$\square$

这些指数与常数尚未被显式计算，故本节没有给出可直接代入实验预算的数值误差证书。它给出的增强是：同一有限代数合同将已证的统一渐近轮廓与近优参数定位升级为某个幂次界；精确求值、最优幂次及数值常数仍需要进一步求解。

## 追加锚（本行以下为增补区）

## 78. 切锥修复的显式正则化与三分之一次统一误差界

### 78.1 将一个切向修复变成真实的小步因果修复

第 77 节通过半代数结构证明某个正幂次速率存在。对当前三个量子比特模型，还能直接构造真实修复，得到一份不依赖消元输出的显式界。以下仍使用第 70 节的 $R_0=ww^*$、$w=x+y$、$P_0=I-ww^*/2$、完整 tester 范数 $N$ 与同一个因果修复集合 $\mathcal C$。

令

$$
J=\frac{I_8}{4}-R_0.
\tag{78.1}
$$

相对于单位向量 $w/\sqrt2$ 及其正交补，$J$ 的两个块为 $-7/4$ 与 $I_7/4$，且

$$
\operatorname{Tr}_D J
=I_A\otimes\left(\frac{I_B}{2}-|0\rangle\langle0|\right),
\qquad \|J\|_1=\frac72,
\qquad N(J)\le7.
\tag{78.2}
$$

最后一项使用第 70 节的 $N(X)\le2\|X\|_1$。

**引理 78.1（显式有限步修复）。** 若 $K\in\mathcal T$、$\|K\|_{\rm op}\le M$、$M\ge1$ 且 $0<\varepsilon M\le1/8$，则取

$$
\delta=4\varepsilon M^2,\qquad
S=R_0+\varepsilon(K+\delta J)
\tag{78.3}
$$

有 $S\in\mathcal C$，并且

$$
N\left(\frac{S-R_0}{\varepsilon}-K\right)
\le28\varepsilon M^2.
\tag{78.4}
$$

证明。切锥的因果偏迹条件及式（78.2）使 $S$ 的偏迹为 $I_A\otimes\sigma$，其中 $\sigma$ 厄米、迹一。只需证明 $S\succeq0$；此后偏迹正性自动给 $\sigma\succeq0$。

将 $K$ 在 $\mathbb Cw\oplus w^\perp$ 的正交单位坐标中写为

$$
K=\begin{pmatrix}a&b^*\\b&B\end{pmatrix},
\qquad B\succeq0,\quad |a|\le M,\quad\|b\|\le M.
$$

$S$ 的左上标量块为

$$
A=2+\varepsilon a-\frac74\varepsilon\delta
\ge2-\varepsilon M-7(\varepsilon M)^2>1,
$$

其中最后一步由 $\varepsilon M\le1/8$ 得到。右下块为

$$
\varepsilon B+\frac{\varepsilon\delta}{4}I
=\varepsilon B+\varepsilon^2M^2I.
$$

因此对应 Schur 补满足

$$
\varepsilon B+\varepsilon^2M^2I
-\frac{\varepsilon^2}{A}bb^*\succeq0.
$$

故 $S\succeq0$，从而为真实归一化因果修复。最后由式（78.2）有 $N(\delta J)\le7\delta=28\varepsilon M^2$。$\square$

该引理控制的是一个已经给定的完整切向修复，不把一般半正定切锥误当作有限步可行域。

### 78.2 紧尺度上的可计算余项

定义

$$
\mathcal D_\varepsilon=(\mathcal C-R_0)/\varepsilon,
\qquad
X_{r,\varepsilon}=
\frac{R_{1-r\varepsilon,\varepsilon}-R_0}{\varepsilon}.
$$

**引理 78.2（有界尺度的显式统一界）。** 若 $R\ge0$、$0\le r\le R$、$0<\varepsilon\le1/2$ 且

$$
9\varepsilon(R+1)\le\frac18,
$$

则在该族有效的参数范围内，

$$
\left|
\frac{e(1-r\varepsilon,\varepsilon)}{\varepsilon}-\gamma_r
\right|
\le2280\varepsilon(R+1)^2.
\tag{78.5}
$$

$r=0$ 时使用第 71 节的端点 $a=1$ 定义，其余情形均在原参数域内。

证明。首先由式（76.1）及秩一算子的迹范数，

$$
\begin{aligned}
\|H_r\|_1
&\le\sqrt{2(r^2+1)}+2\sqrt{2r}+r+1\\
&\le(1+2\sqrt2)(r+1)<4(r+1).
\end{aligned}
\tag{78.6}
$$

取达到 $\gamma_r$ 的 $K_r\in\mathcal T$。第 70—73 节的范数下界与 $\gamma_r\le9/8$ 给

$$
\|H_r-K_r\|_1\le4N(H_r-K_r)\le\frac92.
$$

所以

$$
\|K_r\|_{\rm op}\le\|K_r\|_1
\le4(r+1)+\frac92\le9(R+1)=:M.
\tag{78.7}
$$

应用引理 78.1，得到某个 $K_{r,\varepsilon}\in\mathcal D_\varepsilon$，满足

$$
N(K_{r,\varepsilon}-K_r)
\le28\varepsilon M^2=2268\varepsilon(R+1)^2.
$$

而 $\mathcal D_\varepsilon\subset\mathcal T$。因此

$$
0\le\operatorname{dist}_N(H_r,\mathcal D_\varepsilon)-\gamma_r
\le2268\varepsilon(R+1)^2.
\tag{78.8}
$$

还需在同一范围控制实际过程的一阶余项。实际两列为

$$
\begin{aligned}
r_0&=\sqrt{1-r\varepsilon}\,x+\sqrt{1-\varepsilon}\,y
       +\varepsilon\sqrt r\,z,\\
r_1&=\sqrt\varepsilon\left(\sqrt r\,x'-\sqrt{1-r\varepsilon}\,z'\right).
\end{aligned}
$$

令

$$
v=-\frac r2x-\frac12y+\sqrt r\,z,
\qquad t_0=\sqrt r\,x'-z',
$$

并写 $r_0=w+\varepsilon v+d$。对 $0\le s\le1/2$，

$$
\left|\sqrt{1-s}-1+\frac s2\right|
=\frac{s^2}{2(1+\sqrt{1-s})^2}\le\frac{s^2}{2}.
$$

本节假设给 $\varepsilon(R+1)\le1/2$，故

$$
\|v\|\le r+1,\qquad
\|d\|\le\frac12\varepsilon^2(r+1)^2.
$$

于是第一列外积满足

$$
\begin{aligned}
\|r_0r_0^*-R_0-\varepsilon(vw^*+wv^*)\|_1
&\le2\|w\|\|d\|+\|\varepsilon v+d\|^2\\
&\le\left(\sqrt2+\frac{25}{16}\right)
\varepsilon^2(r+1)^2\\
&<3\varepsilon^2(r+1)^2.
\end{aligned}
\tag{78.9}
$$

对第二列，置 $d_1=(1-\sqrt{1-r\varepsilon})z'$，则 $\|d_1\|\le r\varepsilon$、$r_1=\sqrt\varepsilon(t_0+d_1)$。因此

$$
\begin{aligned}
\|r_1r_1^*-\varepsilon t_0t_0^*\|_1
&\le\varepsilon\left(2\sqrt{r+1}\,r\varepsilon+r^2\varepsilon^2\right)\\
&\le\frac52\varepsilon^2(r+1)^2.
\end{aligned}
$$

一阶和正是 $H_r=vw^*+wv^*+t_0t_0^*$。合并两项、再用 $N(X)\le2\|X\|_1$，得到

$$
N(X_{r,\varepsilon}-H_r)
\le12\varepsilon(R+1)^2.
\tag{78.10}
$$

距离函数对自身范数一-Lipschitz，且 $e(1-r\varepsilon,\varepsilon)/\varepsilon=operatorname{dist}_N(X_{r,\varepsilon},\mathcal D_\varepsilon)$。将式（78.8）与（78.10）相加，得到式（78.5）。$\square$

### 78.3 全参数范围的显式三分之一次界

**定理 78.3（全压缩范围的三分之一次界）。** 对

$$
0<\varepsilon\le2^{-12}
$$

有

$$
\sup_{0<a<1}
\left|
\frac{e(a,\varepsilon)}{\varepsilon}
-\gamma_{(1-a)/\varepsilon}
\right|
\le3000\varepsilon^{1/3}.
\tag{78.11}
$$

证明。取 $R=\varepsilon^{-1/3}\ge16$。则

$$
9\varepsilon(R+1)
=9(\varepsilon^{2/3}+\varepsilon)
\le\frac{153}{4096}<\frac18,
$$

所以引理 78.2 适用于 $0<r=(1-a)/\varepsilon\le R$。由 $R\ge8$ 有 $R+1\le9R/8$，于是

$$
2280\varepsilon(R+1)^2
\le\frac{2280\cdot81}{64}\varepsilon^{1/3}
<3000\varepsilon^{1/3}.
$$

对 $r\ge R$，第 74 节的实际修复上界与第 71 节的系数尾界为

$$
1\le\frac{e(a,\varepsilon)}{\varepsilon}\le1+\frac{16}{r},
\qquad
1\le\gamma_r\le1+\frac{12}{r},
$$

它们都对 $r\ge8$ 成立。两者同在 $[1,1+16/r]$ 中，因此差至多

$$
\frac{16}{r}\le\frac{16}{R}=16\varepsilon^{1/3}.
$$

两区间覆盖全部 $0<a<1$，得到统一界。$\square$

### 78.4 最大参数的显式有限区间与最坏误差余项

**推论 78.4。** 第 76 节的最大参数集满足

$$
\mathcal M\subset\left(\frac1{4000000},4800\right).
\tag{78.12}
$$

因此对 $0<\varepsilon\le2^{-13}$，

$$
\left|E_*(\varepsilon)-\Gamma\right|
\le3000\varepsilon^{1/3},
\qquad
\left|\sup_{0<a<1}e(a,\varepsilon)-\Gamma\varepsilon\right|
\le3000\varepsilon^{4/3}.
\tag{78.13}
$$

证明。第 71 节的连续性模给

$$
\gamma_r\le1+2r+4\sqrt r.
$$

当 $0<r\le1/4000000$ 时，右侧至多 $1+1/2000000+1/500<401/400$。当 $r\ge4800$ 时，尾界给 $\gamma_r\le1+12/r\le401/400$。第 75 节却证明 $\Gamma>401/400$，所以这两个区域均不含最大参数，得到式（78.12）。

取任意 $r_*\in\mathcal M$。若 $\varepsilon\le2^{-13}$，则 $r_*\varepsilon<4800/8192<1$，所以 $a=1-r_*\varepsilon$ 在原参数域内。用定理 78.3 分别给全体参数的上界与这个实际参数的下界，即得式（78.13）。$\square$

常数 $3000$ 和幂次 $1/3$ 都未被证明最优。该界在给出的整个范围内有效，但其右侧数值可以很宽；它的内容是通过真实正修复与大尺度尾界直接取得显式、统一的收敛保证，不声称已经得到紧的有限误差估计。第 77 节关于近最坏参数的稳定指数 $\beta$ 仍未显式计算。

## 追加锚（本行以下为增补区）

## 79. 有限切面容量的布局障碍与重叠拼接的最小接口

本节把[主卷第120节](RECURSIVE_RELATIONAL_OBSERVATION.md#120-可组合关系的最小行为表示与保真辅助构造)的完整实验行为具体化到有限坐标任务。重点是两个实现边界：切面容量一般不具有次模分割所需的结构；不交子树上的最小任务接口，在要求检查重叠坐标一致性时必须细化。以下均为普通数学推导，不是新增 Lean 核验或全球原创性声明。

### 79.1 有限响应与固定树的计费模型

**定义 79.1（完整切面响应）。** 设 $I$ 有限，每个 $X_i$ 非空有限，$X_A=\prod_{i\in A}X_i$，$X_\varnothing$ 为单点。固定总任务 $F:X_I\to O$。对 $A\subseteq I$，置

$$
R_A(a)(b)=F(a\sqcup b),\qquad b\in X_{I\setminus A},\qquad
S_A=R_A[X_A],\qquad \eta_A(a)=R_A(a),\qquad \kappa_A=|S_A|.
$$

这里直接取实际响应像，与按相同响应取商规范等价。所有外部赋值都进入测试，包括任务报告失败的赋值；不能把量词改为“两侧共同合法的补全”而仍然默认获得等价关系。若原任务只在部分配置上定义，则先声明哪些非法、失败及原因标签必须保留，再将这些标签纳入总任务。

例如，三个内部值 $p,q,r$，两个外部值 $0,1$，合法对仅为 $(p,0),(q,1),(r,0)$，对应读数分别为 $0,0,1$。只比较共同合法补全，会得到 $p$ 与 $q$ 相容、$q$ 与 $r$ 相容，却使 $p$ 与 $r$ 冲突；相容性不传递。这不反驳完整总响应核的等价性。

**命题 79.2（充分接口与不交拼接，既有模式的有限应用）。** 若 $m:X_A\to M$ 允许对全部 $a,b$ 解码 $F(a,b)=d(m(a),b)$，则有唯一满射 $m[X_A]\to S_A$ 将 $m(a)$ 送到 $R_A(a)$，故 $|m[X_A]|\ge\kappa_A$。对不交 $A,C$，有满射

$$
\mu_{A,C}:S_A\times S_C\longrightarrow S_{A\cup C},\qquad
\mu_{A,C}(R_A(a),R_C(c))=R_{A\cup C}(a\sqcup c).
$$

这些拼接在坐标规范识别下满足结合律、交换律及空坐标单位律，且 $\kappa_{A\cup C}\le\kappa_A\kappa_C$。

**证明。** 同一 $m$ 标签有相同解码响应，故到 $S_A$ 的映射良定义；像定义给满射与唯一性。若 $R_A(a)=R_A(a')$ 且 $R_C(c)=R_C(c')$，对任意剩余赋值 $b$，依次替换得 $F(a,c,b)=F(a',c,b)=F(a',c',b)$，故拼接良定义。每个联合赋值都可限制到两部分，故满射；坐标合并的恒等式给三条代数律。$\square$

在固定二叉树上，叶坐标各出现一次，内部节点只读两个子消息，无跨子树通道。把根输出也计作根消息。节点 $v$ 的消息仅由 $X_{A_v}$ 决定；固定外部输入后，根部给出命题79.2所需解码器。因此任何准确实现都至少有 $\kappa_{A_v}$ 个可达消息。叶发送 $R_{\{i\}}(x_i)$，内部使用 $\mu$，根从 $S_I\cong\operatorname{im}F$ 读出结果，就在全部节点同时达到下界。空坐标任务另由其唯一输出直接实现。

上述结论按可达标签数计费。固定顺序、外部提供当前位置且每步转移为原子操作时，峰值状态编码位数是 $\max_k\lceil\log_2\kappa_{A_k}\rceil$；程序、位置、输入寄存器、转移表及数值工作空间必须另计。状态最小不等于整张加权动态规划表的位数最小。剩余函数与固定变量顺序决策图的关系属于经典背景。[^boundary79-bryant]

### 79.2 容量剖面一般不是对称次模函数

记 $f(A)=\log_2\kappa_A$。以下计数均直接针对完整响应，未将矩阵秩或 Shannon 熵替代为状态数。

**定理 79.3（不对称与不单调）。** 对每个 $m\ge2$，存在布尔输出有限任务，使某切面两侧容量分别为 $2^m$ 与 $m$；同一任务也存在 $A\subset I$ 而 $\kappa_A>\kappa_I$。

**证明。** 取两个坐标 $u\in\{0,1\}^m$、$j\in\{1,\ldots,m\}$，令 $F(u,j)=u_j$。不同向量 $u$ 在某个索引处不同，故 $\kappa_{\{u\}}=2^m$。不同索引 $j,k$ 由满足 $u_j\ne u_k$ 的向量区分，故 $\kappa_{\{j\}}=m$。完整输入只需保留输出位，$\kappa_I=2<2^m$。$\square$

**定理 79.4（任意大的次模缺口）。** 对每个 $m\ge2$，存在布尔输出任务及相交切面 $A,C$，使

$$
f(A\cap C)+f(A\cup C)-f(A)-f(C)=(m-1)^2>0.
\tag{79.1}
$$

**证明。** 取三个坐标 $v\in\{0,1\}^{m\times m}$、$u,w\in\{1,\ldots,m\}$，定义

$$
F(v,u,w)=v_{u,w},\qquad A=\{v,u\},\qquad C=\{v,w\}.
$$

仅给 $v$ 时，全部 $(u,w)$ 查询恢复矩阵的每个元素，所以 $\kappa_{\{v\}}=2^{m^2}$。给定 $(v,u)$ 时，未来响应恰为所选的一行；所有 $m$ 位行向量均可实现，故 $\kappa_A=2^m$。对列同理，$\kappa_C=2^m$。给定全部输入，响应只有输出 $0,1$，故 $\kappa_I=2$。代入得到 $m^2+1-2m=(m-1)^2$。$\square$

这个反例不要求把大向量作为不可拆输入：也可将 $v$ 的 $m^2$ 个矩阵元各设为一个二进制坐标，再令 $A,C$ 都包含这些坐标，计数不变。取 $m=2$ 时，行列索引本身也各为一个二进制坐标，故已有六个二进制坐标的反例。

对两个二进制坐标的奇偶任务，还有 $f(\{1\})=f(\{2\})=f(I)=1$、$f(\varnothing)=0$，故超模不等式也失败。命题79.2给的是不交集合的次可加界；它没有提供相交集合的次模性。应用要求对称性、单调性或次模性的布局算法，必须另证相应条件。这里没有给任何特定算法的复杂性下界，也没有否定其他结构条件下的优化方法。

### 79.3 不依赖次模性的精确布局递推

**定理 79.5（子集与树分割的瓶颈递推）。** 假设全部 $\kappa_A$ 已给出。定义

$$
L(\varnothing)=1,\qquad
L(A)=\max\left\{\kappa_A,\min_{i\in A}L(A\setminus\{i\})\right\}
\quad(A\ne\varnothing).
\tag{79.2}
$$

则 $L(I)$ 是全部固定读取顺序中的最小峰值状态数。对非空 $A$，定义

$$
T(\{i\})=\kappa_{\{i\}},\qquad
T(A)=\max\left\{\kappa_A,
\min_{\varnothing\ne B\subsetneq A}
\max\{T(B),T(A\setminus B)\}\right\}\quad(|A|\ge2).
\tag{79.3}
$$

则 $T(I)$ 是全部二叉计算树中的最小节点峰值状态数，根输出计入。$T(A)$ 使用的始终是原任务 $F$ 的切面容量，不是重新选择一个只在 $A$ 上定义的任务。

**证明。** 任何 $A$ 的排列都有最后一个坐标 $i$，其峰值等于较短排列的峰值与 $\kappa_A$ 的最大值；反之，给较短排列接上 $i$ 就达到该最大值。有限取最小即得式(79.2)。每棵 $A$ 上的二叉树在根处分为非空 $B$ 与 $A\setminus B$；全树峰值为两个子树峰值和 $\kappa_A$ 的最大值。对子树归纳优化，得到式(79.3)。命题79.2保证对应最小接口能同时实现。$\square$

若 $n=|I|\ge1$，已有容量表后的式(79.2)涉及 $O(n2^n)$ 次有限数比较；式(79.3)涉及 $O(3^n)$ 次比较，因全部候选 $(A,B)$ 可由每坐标属于 $B,A\setminus B,I\setminus A$ 三种位置计数。这些是给定容量表后的操作数，不含构造该表、整数位长、回溯存储或接口转移表成本。

抽象有限集合和一个任意值域中的函数名，不自动给出统一有效程序。若输入提供各 $X_i$ 的枚举、$F$ 的完整有限表及可判定相等的输出标签，则可枚举每个切面的响应行，按逐项相等分组，构造所有 $S_A,\kappa_A,\mu_{A,C}$，再运行上述递推。有限存在、有效呈示下的可计算性和高效可计算性是三个不同结论。[^boundary79-presentation]

### 79.4 重叠端口的最小补充信息

**定义 79.6（必须检查的一致性端口）。** 固定 $H\subseteq A$。除全部 $F$ 响应外，要求接口能对任意 $z\in X_H$ 判断 $a|_H=z$。定义实际像

$$
\zeta_{A;H}(a)=(a|_H,R_A(a)),\qquad
P_{A;H}=\zeta_{A;H}[X_A],\qquad
\tau_{A;H}=|P_{A;H}|.
\tag{79.4}
$$

**定理 79.7（端口接口的精确最小性）。** 对同时支持全部 $F$ 补全与全部指定端口相等查询的编码 $m:X_A\to M$，存在唯一满射 $m[X_A]\to P_{A;H}$ 将 $m(a)$ 送到 $\zeta_{A;H}(a)$。此外

$$
\tau_{A;H}
=\sum_{z\in X_H}
\left|\{R_A(a):a\in X_A,\ a|_H=z\}\right|,
\qquad
\max\{|X_H|,\kappa_A\}\le\tau_{A;H}\le |X_H|\kappa_A.
\tag{79.5}
$$

**证明。** $m(a)=m(a')$ 先由任务解码给 $R_A(a)=R_A(a')$。在端口查询中取 $z=a|_H$，一侧回答真，另一侧也必须回答真，故 $a'|_H=a|_H$。因此 $\zeta$ 在每个 $m$ 纤维上恒定，实际像给唯一满射。反过来，$\zeta$ 的两个分量准确支持两组查询，所以达到下界。按第一分量 $z$ 分割实际像得到求和公式。非空坐标积使每个 $z$ 都可延拓，投影到 $X_H$ 满射；投影到 $S_A$ 也满射。两项下界和乘积上界随之成立。$\square$

若 $F$ 恒定，则 $\kappa_A=1$，而 $\tau_{A;H}=|X_H|$。两个端口值给相同任务响应，却对“是否等于第一个端口值”给不同回答，直接证明仅保留 $S_A$ 不够。乘积上界也可达到：取 $I=A=H\sqcup U$，任务仅报告 $U$ 上的赋值，则 $\kappa_A=|X_U|$，$\tau_{A;H}=|X_H||X_U|$。

这里要求精确检查全部端口相等查询。若协议保证共享赋值已由共同来源同步，且无需接口再次检查一致性，这份附加任务可以取消；不能把本定理的额外下界强加给那个较弱任务。

**定理 79.8（重叠接口的相容拼接）。** 对任意 $A,C\subseteq I$，令 $H=A\cap C$。只配对端口分量相等的类型，得到纤维积

$$
P_{A;H}\times_{X_H}P_{C;H}.
$$

其上有规范满射

$$
\nu_{A,C}:P_{A;H}\times_{X_H}P_{C;H}\twoheadrightarrow S_{A\cup C},\qquad
\nu_{A,C}(\zeta_{A;H}(a),\zeta_{C;H}(c))=R_{A\cup C}(a\sqcup_H c).
\tag{79.6}
$$

**证明。** 匹配的端口值使代表元在 $H$ 上一致，因此合并赋值唯一。若 $a,a'$ 具有相同 $\zeta_{A;H}$，则固定 $c|_{C\setminus H}$ 和外部 $b$，由 $R_A(a)=R_A(a')$ 可替换 $a$。端口值没有改变，$a'$ 仍与 $c$ 及同类型的 $c'$ 相容；固定 $a'|_{A\setminus H}$ 和 $b$，再由 $R_C(c)=R_C(c')$ 替换 $c$。于是全部剩余响应不变，式(79.6)良定义。每个联合赋值限制到 $A,C$ 给出一个相容原像，故满射。$\square$

若合并后还要参加另一次重叠拼接，仍需保留届时要检查的端口。式(79.6)只保证当前合并后的任务响应，不能一面丢掉未来需用的共享坐标，一面声称还能验证以后的一致性。任意固定外露端口集的补充方式仍由定义79.6决定；删除端口应当对应任务中相应查询的删除。

### 79.5 带权重叠拼接与权重归属

**定理 79.9（相容类型上的半环聚合）。** 固定交换半环 $R$，任取权函数 $g_A:X_A\to R$、$g_C:X_C\to R$，令

$$
D_A(t)=\bigoplus_{\zeta_{A;H}(a)=t}g_A(a),\qquad
D_C(u)=\bigoplus_{\zeta_{C;H}(c)=u}g_C(c).
$$

对每个 $s\in S_{A\cup C}$，有

$$
\bigoplus_{\substack{(t,u)\in P_{A;H}\times_{X_H}P_{C;H}\\\nu_{A,C}(t,u)=s}}
D_A(t)\otimes D_C(u)
=
\bigoplus_{\substack{x\in X_{A\cup C}\\R_{A\cup C}(x)=s}}
g_A(x|_A)\otimes g_C(x|_C).
\tag{79.7}
$$

**证明。** 展开两个有限聚合并用分配律。端口类型匹配，保证其纤维中每对代表都在 $H$ 上相等。每对相容赋值与一个唯一联合赋值对应，逆为限制到 $A,C$；定理79.8保证目标类型条件相同。因此展开后的求和指标与右侧逐一对应，权重项也一致。$\square$

若目标权重为 $\bigotimes_{i\in A\cup C}w_i(x_i)$，直接令 $g_A,g_C$ 各自乘入自己范围中的全部 $w_i$，会让每个共享坐标的权重出现两次。正确的无除法实现是预先选择

$$
J_A\sqcup J_C=A\cup C,\qquad J_A\subseteq A,\quad J_C\subseteq C,
\qquad
g_A=\bigotimes_{i\in J_A}w_i,\quad g_C=\bigotimes_{i\in J_C}w_i.
$$

于是式(79.7)中的乘积恰为目标权重。在一般半环中不能通过“除掉共享权重”修补重复乘入；逆元可能不存在，权重也可能为零。更一般的局部因子也可各指定一个包含其全部变量的唯一归属块。归属方式是聚合权重的账，不替代共享变量的一致性检查。

### 79.6 来源与适用边界

主卷定理120.2、120.4、120.5已经给出完整实验商、逐孔替换和剩余行为最小实现。仓内 `contextualSetoid` 与 `contextual_equivalence_is_greatest`、`controlled_behavior_universal_property`、`dynamic_closure_is_least` 分别承担其各自声明中的上下文核、有限受控实现与动态闭包接口；参见固定快照 [40fb7ec 的 StrictOneHoleContexts](https://github.com/the-omega-institute/trureturing/blob/40fb7ec023342614dec1c13b19dd925932763dc9/D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)、[ControlledBehaviorUniversality](https://github.com/the-omega-institute/trureturing/blob/40fb7ec023342614dec1c13b19dd925932763dc9/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) 与 [DynamicClosureMinimality](https://github.com/the-omega-institute/trureturing/blob/40fb7ec023342614dec1c13b19dd925932763dc9/D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)。本节没有新建它们的 Lean 绑定包装，也不把上述引用当作本节全部具体定理已经运行过形式核验。

剩余函数、固定变量顺序的规范决策表示与变量排序的重要性为 `literature-attested` 背景。式(79.1)的显式矩阵族、式(79.2)—(79.3)的指定目标递推、式(79.4)—(79.7)的任务与端口联合接口及其聚合，在这里给出完整普通证明，定位为 `repo-derived` 综合；不据此主张这些抽象机制或实例在文献中首次出现。

[^boundary79-bryant]: Randal E. Bryant，*Graph-Based Algorithms for Boolean Function Manipulation*，IEEE Transactions on Computers C-35(8), 677–691 (1986)，[来源条目](../../../Library/ConceptDynamics/bryant1986boolean.md)与[作者原文](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf)。本节只借用固定变量顺序、残余函数合并与规范布尔表示的背景；本节按每个已读位置计费，不把跳过无关变量的图节点总数等同于这里的分层消息数。

[^boundary79-presentation]: [Pauly 的表示空间来源条目](../../../Library/ConceptDynamics/pauly2016represented.md)说明有效内容必须绑定表示。本节对有限显式表给出了直接枚举算法；该算法不需要用无限表示空间定理充当证明。

## 追加锚（本行以下为增补区）

## 80. 任务投影与两次重叠拼接的存活端口

本节把 §36 的任务选择与 §79 的后续端口要求接到同一个有限实例：先沿共享坐标 $h$ 拼接，再沿共享坐标 $y$ 拼接。固定这两次拼接的次序、输出和合法性查询后，当前输出只需两类，而支持下一次拼接的关系需要四类。下面只计算这项任务，不另建一般商理论。

### 80.1 完整运行与声明的任务投影

**定义 80.1（运行结果的任务投影）。** 沿用 §36.1 的实际来源 $S$ 与有类型动作词 $w$，将完整运行结果明确写作

$$
\operatorname{Run}_w(s)
=\bigl(\operatorname{Adm}_w(s),\operatorname{Out}_w(s),
\operatorname{Rec}_w(s),\operatorname{End}_w(s)\bigr).
$$

四个分量依次记录合法性、输出、所保留的记录和终配置；失败情况须有声明的类型及失败标记。对每个 $w$，先声明本任务保留哪些结果，再指定其结果域上的投影 $\Pi_w$，定义

$$
\operatorname{Obs}_w=\Pi_w\circ\operatorname{Run}_w.
\tag{80.1}
$$

任务核指全部已声明 $\operatorname{Obs}_w$ 的相等核之交；取恒等投影才回到相应的完整运行任务。投影可以选取分量，也可以选取已声明的分量读数，但不能在比较状态之后临时改变。特别地，若实验族含空词 $\varepsilon$，并原样保留 $\operatorname{End}_{\varepsilon}(s)=s$，则观察相等强迫 $s=t$：这是更强的身份恢复任务。删除原始终配置后，才可能合并对声明任务无差别的不同来源。

本节的固定任务明确不采用这个原始身份空词：第一次拼接成功后，空词读数只取下文的 $\sigma$，不保留中间联合赋值或原始来源的恒等终配置。若把 $\operatorname{End}_{\varepsilon}$ 原样加入同一任务，四类中间剖面结论就不再是该任务的结论，而应按更强的身份恢复任务重新计数。

§45 保留相对相位所决定的相等性响应及协议标签，§79 保留指定任务的补全响应与指定端口查询；二者使用这样的投影任务，不要求恢复原始终配置。本节明确这些任务与 §36.1 完整 $\operatorname{Run}$ 任务的关系，不把任务强弱的差别称为 §36 的错误，也不改写旧节。

### 80.2 核包含方向的显式读法

沿用 §36 的已声明目标核 $K$ 及其商投影 $q$，令 $r$ 的值域取实际像 $r[S]$。§36.2 的两条包含式保持原样，其“丢失”与“冗余”的方向明确如下：

$$
\begin{aligned}
K\subseteq\ker(r)
&\iff \exists\bar r:\ q[S]\to r[S],\quad r=\bar r\circ q,\\
\ker(r)\subseteq K
&\iff \exists d:\ r[S]\to q[S],\quad q=d\circ r.
\end{aligned}
\tag{80.2}
$$

第一行表示从目标商可以向下得到 $r$；$r$ 可以更粗，严格包含时会丢失目标区别。第二行的 $\ker(r)\subseteq K$ 表示 $r$ 不合并目标仍要区分的状态，是在实际像上由 $r$ 恢复目标商及其任务读出的充要条件；严格包含时，$r$ 还区分目标认为相同的状态，因而可以冗余。两核相等进一步排除这些冗余区别，给出最小的精确表示，两个实际像之间的恢复器互逆。这里的证明就是检查因子在纤维上是否恒定：第一行把 $[s]_K$ 送到 $r(s)$，第二行把 $r(s)$ 送到 $[s]_K$，相应包含式分别保证良定义；从复合等式反推核包含也逐点成立。实际像保证因子唯一。

这是对 §36.2 包含式的澄清，历史正文与公式不变；后文“可丢失”专指第一方向，“可冗余”专指第二方向。集合上的恢复器存在还不自动给出允许协议下的取得算法、成本界或动态闭包。

### 80.3 同一来源上的两次重叠拼接

**定义 80.2（固定的四坐标模型）。** 令 $\mathbb B=\{0,1\}$，取

$$
I=\{x,h,y,z\},\qquad S=\mathbb B^I,\qquad
A=\{x,h\},\quad C=\{h,y\},\quad D=\{y,z\}.
\tag{80.3}
$$

写 $s=(x,h,y,z)$ 时，各字母也表示相应坐标值。局部消息为

$$
m_A(s)=(h,x),\qquad m_C(s)=(h,y),\qquad m_D(s)=(y,z).
$$

在任意局部消息对上，定义带严格失败的部分拼接

$$
J_1\bigl((h_A,x),(h_C,y)\bigr)
=\begin{cases}(x,y),&h_A=h_C,\\ \bot,&h_A\ne h_C,\end{cases}
\qquad
J_2\bigl((x,y),(y',z)\bigr)
=\begin{cases}x\mathbin{\mathrm{xor}}z,&y=y',\\ \bot,&y\ne y'.\end{cases}
\tag{80.4}
$$

$\bot$ 与合法输出 $0,1$ 不同；带 $\bot$ 的输入继续拼接仍返回 $\bot$，不能用某个正常输出代替失败。调度固定为先 $J_1$ 后 $J_2$。$A\cap C=\{h\}$，而 $(A\cup C)\cap D=\{y\}$：第一次检查后可以忘掉 $h$，第二次仍须检查 $y$。

对于每个同一来源 $s$，两次匹配都成功，最终输出为 $x\mathbin{\mathrm{xor}}z$。全部四个中间态 $(x,y)\in\mathbb B^2$ 都由完整来源共同实现：例如取 $s=(x,0,y,0)$。这里不是分别取两个边缘的可达值后假定它们能够联合出现。

下一步的候选输入另记为 $a=(y',z)\in\mathbb B^2$；任务允许对每个候选检查合法性并在合法时读出结果。这些候选不是承诺来自当前同一个 $s$ 的 $m_D(s)$。来自同一 $s$ 的消息必然匹配；外部候选则可以不匹配，失败正是任务要求保留的回答。每个候选本身都是某个完整来源的 $D$ 消息，但不把不匹配的候选与当前中间态冒称为一个共同来源的限制。

### 80.4 两类静态读数与四类续接关系

**命题 80.3（固定任务的四类下界及达到）。** 在成功的中间态集合 $U=\mathbb B^2$ 上，定义

$$
\sigma(x,y)=x,\qquad
\rho_a(x,y)=J_2\bigl((x,y),a\bigr),\qquad
\Pi(x,y)=\bigl(\sigma(x,y),(\rho_a(x,y))_{a\in\mathbb B^2}\bigr).
\tag{80.5}
$$

这里 $\Pi$ 是本实例的完整任务剖面，与式(80.1)的逐词投影 $\Pi_w$ 区分。固定的尝试剖面记为

$$
F_{\mathrm{mid}}(x,y)=\bigl(\sigma(x,y),(\rho_a(x,y))_{a\in\mathbb B^2}\bigr).
$$

它明确表示：从同一个成功中间态分别尝试四个候选动作所得到的四组反事实响应；四个 $\rho_a$ 不是一条失败后仍自动回到原态的顺序运行记录。可取空词的任务读数为 $\sigma$，一步词 $a$ 的任务读数为 $\rho_a$；合法性由是否为 $\bot$ 恢复，不额外要求原始终配置或完整历史。静态读数 $\sigma$ 恰有两类，且在本固定任务上 $F_{\mathrm{mid}}(u)=F_{\mathrm{mid}}(v)$ 当且仅当 $u=v$；从来源 $S$ 提升时，剖面相等当且仅当两来源的 $(x,y)$ 相同，$h,z$ 被任务投影丢弃。任何同时恢复 $\sigma$ 及全部 $\rho_a$ 的确定性中间消息至少有四个实际值；保留 $(x,y)$ 正好达到下界。

**证明。** $\sigma$ 只区分 $x=0,1$，每类包含两个 $y$ 值。若两个中间态的 $x$ 相同而 $y$ 不同，选动作 $(0,0)$：$y=0$ 的一侧合法，$y=1$ 的一侧返回 $\bot$。若 $y$ 相同而 $x$ 不同，选共同合法动作 $(y,0)$，两侧输出分别为各自的 $x$，因而不同。若 $x,y$ 均不同，静态分量 $\sigma$ 已将两态分开。因此 $\Pi$ 区分全部四个中间态。

若消息 $m$ 能恢复 $\Pi$，则 $m(u)=m(v)$ 必有 $\Pi(u)=\Pi(v)$，从而 $u=v$；四个实际可达态不能共用消息。反过来，$(x,y)$ 直接给出 $\sigma$，比较 $y=y'$ 后计算异或就给出每个 $\rho_a$，所以四值编码足够。$\square$

按动作顺序 $(0,0),(0,1),(1,0),(1,1)$，全部读数为：

| 80.4 中间态 | 当前 $\sigma$ | $\rho_{(0,0)}$ | $\rho_{(0,1)}$ | $\rho_{(1,0)}$ | $\rho_{(1,1)}$ |
| --- | --- | --- | --- | --- | --- |
| $(0,0)$ | $0$ | $0$ | $1$ | $\bot$ | $\bot$ |
| $(0,1)$ | $0$ | $\bot$ | $\bot$ | $0$ | $1$ |
| $(1,0)$ | $1$ | $1$ | $0$ | $\bot$ | $\bot$ |
| $(1,1)$ | $1$ | $\bot$ | $\bot$ | $1$ | $0$ |

在来源 $S$ 上，这四类由 $(x,y)$ 标识，每类含四个 $h,z$ 组合；后续候选中的 $z$ 是动作输入，不要求从中间消息恢复原来源的 $z$。四值下界是这一个中间阶段、这一个任务的消息容量，不是对 $m_A,m_C,m_D$ 各自通信成本的同时最优结论。

### 80.5 四种任务完备表达及其恢复器

**定义 80.4（同一四类关系的四种读法）。** 以下表达都取同一实际来源在 $J_1$ 成功后的实际像，并使用式(80.5)的同一任务。空间表达只保留指定切面上的坐标值；时间表达记带动作标签的一步续接树；边界表达记合法端口集合及输出参数；记忆表达由第一次拼接成功时写入两个比特。

| 80.5 角色 | 明确的任务完备表达 | 恢复 $(x,y)$ | 从 $(x,y)$ 恢复该表达 |
| --- | --- | --- | --- |
| 80.5 空间 | 带标签的切面赋值 $r_{\mathrm{sp}}=\{X\mapsto x,\ Y\mapsto y\}$ | 读取 $X,Y$ 两个标签下的值 | 写入这两个坐标值 |
| 80.5 时间 | $r_{\mathrm{tm}}=(\rho_{(0,0)},\rho_{(0,1)},\rho_{(1,0)},\rho_{(1,1)})$，坐标保留动作标签和先 $J_1$ 后 $J_2$ 的阶段约定 | 若 $\rho_{(0,0)}\ne\bot$ 则 $y=0$，否则 $y=1$；再取 $x=\rho_{(y,0)}$ | 按式(80.4)生成四个带标签响应 |
| 80.5 边界 | $r_{\partial}=(x,L)$，$L=\{b\in\mathbb B:y=b\}$，端口 $b$ 合法时的输出规则为 $x\mathbin{\mathrm{xor}}z$ | $x$ 为第一分量，$y$ 为单元素集 $L$ 的唯一元素 | 形成 $(x,\{y\})$ 并用固定异或规则 |
| 80.5 记忆 | $r_{\mathrm{mem}}=(b_x,b_y)$，$J_1$ 成功时赋值 $(b_x,b_y)=(x,y)$ | 读取两个寄存器 | 把 $(x,y)$ 写入这两个寄存器 |

时间行中，在所测试的 $z=0$ 的两个动作 $(0,0)$ 与 $(1,0)$ 中恰有一个合法，其首坐标恢复 $y$；完整四动作表则有两个合法动作。这是式(80.4)给出的事实；因此表中每对恢复器在实际像上互逆，四种表达的核均等于 $\ker\Pi$。它们在 $S$ 上表达同一四类关系，在 $U$ 上则各自区分全部四态。完整的响应表是数学表达；从未知来源实际取得它仍需允许的查询、状态准备和成本条件。记忆初值由实际收到的两份相容消息产生，不授予读取未知来源的额外权限。

单凭“空间”“时间”“边界”“记忆”的角色名称不够。若记忆只写 $x$，或时间表达只记阶段编号，表中的恢复器就不存在。这里证明的是这些指定表达对同一任务的恢复关系，没有证明任意四种视角的普遍本体论，也没有由一张响应表恢复经过时长或原始历史。

### 80.6 动态下降、内部选择与严格失败

对各阶段的实际状态及消息取带阶段标签的不交并；失败值也按阶段带类型。令 $r$ 在每个阶段取该阶段的编码。某个固定动作 $a$ 要在编码上下降，必须有

$$
\operatorname{Adm}_a=\overline{\operatorname{Adm}}_a\circ r,
\qquad
\operatorname{Out}_a=\overline{\operatorname{Out}}_a\circ r,
\qquad
r\circ T_a=\overline T_a\circ r.
\tag{80.6}
$$

最后一式在由阶段 $j$ 到 $j+1$ 的有类型动作上读作
$r_{j+1}\circ T_a=\overline T_a\circ r_j$，不把中间二元组与终端比特混作同一类型。这些等式要求合法性、输出在每个 $r_j$ 纤维上恒定，并要求同纤维状态的后继仍落在同一 $r_{j+1}$ 纤维；失败用 $\bot$ 严格传播，使部分拼接成为带失败标记的总映射。若任务保留额外记录，其读出和更新也须满足对应的下降等式。

**命题 80.5（本例的第二次拼接在保留端口后下降）。** 第一次拼接后尚未压缩的联合赋值为 $v=(x,h,y)\in\mathbb B^{A\cup C}$，取

$$
r_{\mathrm{mid}}(v)=(x,y),\qquad
\operatorname{Adm}_{(y',z)}(v)=\mathbf1_{\{y=y'\}},\qquad
\operatorname{Out}_{(y',z)}(v)=T_{(y',z)}(v)
=\begin{cases}x\mathbin{\mathrm{xor}}z,&y=y',\\ \bot,&y\ne y'.\end{cases}
$$

终端域为 $\mathbb B\sqcup\{\bot\}$，取 $r_{\mathrm{end}}=\mathrm{id}$；中间失败另设 $\bot_{\mathrm{mid}}$，其合法性为假，输出及后继为终端失败。则式(80.6)成立。若改用 $\sigma\circ r_{\mathrm{mid}}$ 作为中间编码，连合法性都不能下降。

**证明。** 在中间像上定义 $\overline{\operatorname{Adm}}_{(y',z)}(x,y)=\mathbf1_{\{y=y'\}}$，$\overline{\operatorname{Out}}_{(y',z)}(x,y)=\overline T_{(y',z)}(x,y)=\rho_{(y',z)}(x,y)$。三式直接成立，且与被丢弃的 $h$ 无关；失败分支按上述约定成立。反向取 $v=(0,0,0)$ 与 $v'=(0,0,1)$，二者静态编码同为 $0$，但动作 $(0,0)$ 的合法性分别为真、假，故不存在静态编码上的合法性函数。$\square$

第一步的端口检查仍由 $J_1$ 负责；不相容的 $(h_A,x),(h_C,y)$ 产生中间失败，相容时将 $(x,h,y)$ 映为 $r_{\mathrm{mid}}(x,h,y)$。因此删除 $h$ 有明确的阶段条件：其相等性已经检查，且剩余调度不再询问 $h$。四种表达之间的动态恢复由表中的互逆映射运输式(80.6)，终端均使用同一终端编码。

若动作由内部控制策略选择，还必须检验

$$
\pi=\bar\pi\circ r.
\tag{80.7}
$$

例如本例选择 $\pi(v)=(y,0)$ 可由 $r_{\mathrm{mid}}$ 得到且总合法；选择 $\pi(v)=(h,0)$ 则不能，因为同一 $(x,y)$ 纤维含不同 $h$。外部给定全部候选动作足以定义响应剖面，不等于内部策略可以使用已经丢掉的坐标。固定动作下降与内部选择下降合在一起，才使闭环执行也由保留的消息决定。

### 80.7 既有接口的范围与本节边界

本节的核方向沿用 [InterfaceKernelCriterion.interface_refinement_iff_kernel_inclusion](../../../D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion.lean)：其范围是实际像上的因子分解当且仅当反向核包含。[ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) 的范围包含有限载体、满射实现以及更新和读出的交换条件；[StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean) 处理有类型的部分操作与严格失败；[DynamicClosureMinimality](../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean) 给出相对于所声明干预族的最小干预闭合细化。这些只作为各自范围的引用，不用来替本节实例省略共同实现、端口保留、选择器或动态交换的检查，也不新增任何定理包装。

本节给出有限、确定性、固定调度 $J_1;J_2$ 下的普通数学推导。四类结论只覆盖成功的中间态；失败是额外的带类型标记，阶段标签及终端存储不计入该四类下界。这里不主张任意装配树上的同时最小性、无限完成、随机或量子版本、物理时钟、完整历史恢复，或随规模与调度变化仍成立的一致有限记忆界。本文没有新增 Lean 声明，也不声称这些具体推导已获 Lean kernel 核验；既有形式化接口的引用不改变这一边界。

## 追加锚（本行以下为增补区）

## 81. 二叶生成层与动作词边界的桥接

第 80 节给出了一个带重叠端口的有限拼接实例；Fibonacci 卷第 245—247 节则给出了二叶自由生成语法及其任务相对行为核。本节把它们接到第 20—22 节的动作词未来边界：在只观察原子组成及其 Fibonacci 未来响应的固定任务中，组成投影本身就是完整动作词行为核；一旦增加合法性、失败、记录或内部控制，行为核按声明的新增响应细化。以下仍是有限树、确定性替换和固定测试族的普通数学推导。

### 81.1 二叶载体与声明的动作族

令

$$
\mathcal T=\mu X\bigl(\{\alpha,\beta\}\sqcup(X\times X)\bigr),
\qquad
t::=\alpha\mid\beta\mid\langle t,t\rangle,
$$

并沿用

$$
\rho(\alpha)=\beta,
\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,
\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle .
$$

组成投影为

$$
c(t)=(\#\alpha,\#\beta)\in\mathbb N^2,
\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

固定一个实际可声明的旁支集 $U\subseteq\mathcal T$。令

$$
L_u(t)=\langle t,u\rangle,
\qquad
R_u(t)=\langle u,t\rangle,
\qquad
A_U=\{\rho\}\cup\{L_u,R_u:u\in U\}.
\tag{81.1}
$$

这里的 $U$ 是动作合同的一部分；把形式上所有树都当作观察者已经可以免费取得的旁支，会改变实际来源和权限任务。若某个旁支或替换在实际合同中非法，就把动作扩展为带类型失败的总化动作，并在读出中保留失败标签。

### 81.2 整个动作词族在组成边界上下降

对每个生成动作，组成满足

$$
\begin{aligned}
c(\rho(t))&=Mc(t),\\
c(L_u(t))&=c(t)+c(u),\\
c(R_u(t))&=c(u)+c(t).
\end{aligned}
\tag{81.2}
$$

令 $\lambda_\rho(z)=Mz$，令 $\lambda_{L_u}(z)=z+c(u)$、$\lambda_{R_u}(z)=c(u)+z$。按动作词先后复合，得到每个 $w\in A_U^*$ 的仿射映射 $\lambda_w$，并有

$$
\boxed{c(w[t])=\lambda_w(c(t)).}
\tag{81.3}
$$

**证明。** 空词时 $\lambda_\varepsilon=\operatorname{id}$。若式(81.3)对 $w$ 成立，再在末尾接一个生成动作，分别使用式(81.2)及仿射映射复合即可。对词长归纳完成。$\square$

这比只验证 $c\circ\rho=M\circ c$ 更强：所有声明的旁支接法及其任意有限顺序都由同一组成边界运输。由于加法交换，$L_u$ 和 $R_u$ 在这个特定任务的组成读出上相同；若任务保留左右位置、路径或记录，它们必须重新区分。

### 81.3 组成核就是该任务的完整行为核

只保留组成读出的完整动作词 profile 定义为

$$
\Gamma_U(t)(w)=\widehat c(w[t]),
\qquad w\in A_U^*,
\tag{81.4}
$$

其中 $\widehat c(\bot)=\bot$；在当前自由树总化模型中没有失败分支，加入失败只是为了与一般部分过程使用同一类型接口。

**命题 81.1（组成核与动作词核）。** 若空词属于测试族并读出 $c$，则

$$
\boxed{
\Gamma_U(t)=\Gamma_U(t')\iff c(t)=c(t').
}
\tag{81.5}
$$

若删除空词，只要 $U$ 含一个固定已知旁支 $u_0$，并保留 $L_{u_0}$ 的组成读出，结论仍成立。

**证明。** 若 $c(t)=c(t')$，式(81.3)对每个 $w$ 给出相同读数，故 profile 相同。反向在含空词的情形直接取 $w=\varepsilon$。删除空词时，取 $w=L_{u_0}$；由

$$
c(L_{u_0}(t))=c(t)+c(u_0)
$$

及 $\mathbb Z^2$ 加法的消去律，两个 profile 相同即推出 $c(t)=c(t')$。证毕。$\square$

因此

$$
\mathcal T/\ker\Gamma_U
\cong
\operatorname{im}c=\mathbb N^2\setminus\{(0,0)\}.
\tag{81.6}
$$

在这个固定任务下，树的左右次序和括号结构被有意商掉；例如 $\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 属于同一行为类。若扩大测试族以读取路径、左右位置或完整记录，式(81.5)的核必须重新计算，不能继续把 $c$ 当作充分边界。

### 81.4 Fibonacci 两读数是同一边界的另一表达

对权重 $p,q\in\mathbb Z$，令

$$
H_{p,q}=\begin{pmatrix}p&q\\q&p+q\end{pmatrix}=pI+qM,
\qquad
b_{p,q}(t)=H_{p,q}c(t).
$$

由于 $H_{p,q}$ 是 $M$ 的多项式，有

$$
H_{p,q}M=MH_{p,q}.
\tag{81.7}
$$

故 $b_{p,q}$ 上的替换与旁支运输分别为

$$
\bar\rho(b)=Mb,
\qquad
\bar L_r(b)=b+H_{p,q}c(r),
\qquad
\bar R_r(b)=H_{p,q}c(r)+b.
\tag{81.8}
$$

当 $(u,v)=(2,3)$ 时

$$
\det H_{2,3}=1,
\qquad
H_{2,3}^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
$$

所以 $b_{2,3}$ 与 $c$ 在实际像上双向恢复，并且二者诱导同一个动作词核。根据 Fibonacci 卷第 13 节，在整数线性读数这一表示类别中，两个读数达到恢复全部组成的下界；这不是对树结构、任意观察者状态或所有可能任务的容量下界。

### 81.5 四种表达与递归核的层级关系

在本节的固定任务中，可以把同一实际像上的四种表示写为

$$
\boxed{
\text{空间 }c(t)
\ \longleftrightarrow
\text{时间 }\Gamma_U(t)
\ \longleftrightarrow\
\text{边界 }b_{2,3}(t)
\ \longleftrightarrow\
\text{记忆 }m(t),
}
\tag{81.9}
$$

其中记忆 $m$ 必须是实际寄存器上的 $c$ 或 $b_{2,3}$ 的双射编码，并且更新、旁支权限和失败标签都按式(81.3)、(81.8)下降。此时四者的恢复器由 $H_{2,3}$、其逆矩阵和动作词仿射运输共同给出。

若观察者新增一项合法性、记录、参考或选择器任务，记新的 profile 为 $\Gamma'_U$。则

$$
\ker\Gamma'_U\subseteq\ker\Gamma_U=\ker c.
\tag{81.10}
$$

严格包含表示新增关系确实不能由 Fibonacci 组成边界恢复；新的最小边界应取 $\mathcal T/\ker\Gamma'_U$，而不是把失败或记录塞进原有数值坐标。反复扩大任务族得到

$$
K_0=\ker c\supseteq K_1\supseteq K_2\supseteq\cdots,
\qquad
K_\infty=\bigcap_nK_n,
\tag{81.11}
$$

这就是“关系的关系”的同一内部递归：下一层仍是对同一载体声明新的合法接续和读出，不需要增加系统外观察者。有限状态下若核链稳定，可在有限层得到最终边界；否则只能把相容有限 profile 的逆极限作为候选完成，并另证实际来源满射。

当新增任务不是对象树的读出，而是“状态—协议”联合评价时，$\Gamma'_U$ 应写成双侧 profile：状态侧是实际配置，协议侧是允许的测试、权限和选择器。仓内 `UnifiedObserverRepresentation.unified_observer_representation` 给出完整协议签名像对当前接口因子化的唯一表示；`DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` 则在两侧满射及双侧外延性条件下给出状态商与协议商的双向最小性。因而，观察者自读、动作选择和记忆更新不是在二叶边界外再放一个主体，而是把测试族从 $A_U^*$ 扩展为联合协议 profile，并重新计算同一个核塔。

### 81.6 适用范围

本节的精确同构只适用于每个项本身有限、确定性 $\rho$、固定旁支合同以及只保留组成与其动作词响应的任务；载体 $\mathcal T$ 本身仍是无限的，因此不把有限载体的基数或稳定深度定理直接套到这里。若加入左右位置、括号、共享随机来源、权限、失败原因、完整档案或观察者策略，必须把相应字段纳入联合 profile，并重新检查动态下降、共同来源和实际像闭合。本文没有把二叶生成层提升为所有关系的普适本体，也没有新增 Lean 声明；引用的 `EffectiveProtocolActionMonoid`、`ControlQuotientUniversalMinimality`、`BehaviorUpdateWordAction` 与 `DynamicClosureMinimality` 只作为已有接口的对应支点。

## 81.99 追加锚

## 82. 二叶生成层的双侧协议画像

第 81 节把组成 \(c\) 证明为固定动作词任务的完整状态边界，但它把状态读出和允许读出固定在同一个测试族里。内部观察者还需要保留协议、权限和选择器这一侧：改变可用协议会改变状态的行为核，扩大实际状态像也会改变协议之间的可区分性。

### 82.1 状态行商与协议列商

令 \(S\) 是同一实际来源上的状态像，\(P\) 是声明过的协议集合，\(\Lambda\) 是带失败值的读出集合，且
\[
L:S\times P\longrightarrow\Lambda
\]
是完整状态—协议响应。定义
\[
\begin{aligned}
s\equiv_S s'&\iff\forall p\in P,\ L(s,p)=L(s',p),\\
p\equiv_P p'&\iff\forall s\in S,\ L(s,p)=L(s,p').
\end{aligned}
\tag{82.1}
\]
第一关系合并面对全部当前协议行为相同的状态，第二关系合并在全部当前状态上行为相同的协议。

若有满射
\[
\eta:S\twoheadrightarrow B,\qquad \pi:P\twoheadrightarrow Q
\]
以及
\[
\bar L:B\times Q\longrightarrow\Lambda
\]
满足
\[
L(s,p)=\bar L(\eta(s),\pi(p)),
\tag{82.2}
\]
并且 \(\bar L\) 两侧外延：
\[
\begin{aligned}
(\forall q,\ \bar L(b,q)=\bar L(b',q))&\Longrightarrow b=b',\\
(\forall b,\ \bar L(b,q)=\bar L(b,q'))&\Longrightarrow q=q',
\end{aligned}
\tag{82.3}
\]
则 \(B\cong S/{\equiv_S}\)、\(Q\cong P/{\equiv_P}\)。所以双侧外延的精确画像同时是状态行商和协议列商；单独压缩状态侧不能自动保留协议权限和后续选择。

### 82.2 二叶组成任务的双侧画像

回到
\[
\mathcal T=\mu X\bigl(\{\alpha,\beta\}\sqcup(X\times X)\bigr).
\]
给定实际声明的旁支合同 \(U\)，取协议集合 \(P_U=A_U^*\)，其中 \(A_U\) 包含替换 \(\rho\) 和合法的左、右旁支动作。对组成任务令
\[
L_U(t,w)=c(w[t]),\qquad t\in S\subseteq\mathcal T,\quad w\in P_U.
\tag{82.4}
\]
第 81 节的运输式给出仿射映射 \(\lambda_w\)，使
\[
L_U(t,w)=\lambda_w(c(t)).
\tag{82.5}
\]
因此状态侧可以取 \(\eta(t)=c(t)\)，协议侧则按实际组成像定义
\[
w\equiv_{P_U}w'
\iff
\forall t\in S,\ \lambda_w(c(t))=\lambda_{w'}(c(t)).
\tag{82.6}
\]
两侧取商后，
\[
\bar L_U([c(t)],[w])=\lambda_w(c(t)).
\tag{82.7}
\]
这里 \(\alpha,\beta\) 是状态生成层的两个叶标签，而协议商记录的是允许如何继续作用。协议商会随旁支合同、权限、失败标签和记录规则变化；把所有形式上可写的动作词都当作免费协议，会改变实际共同来源。

### 82.3 当前读数相同不保证未来协议相同

最小有限例子取 \(S_0=\{\alpha,\beta\}\)。当前协议 \(q\) 满足
\[
q(\alpha)=q(\beta)=0.
\]
在 \(\{q\}\) 上两状态属于同一行商。加入一个仍然合法的后续协议 \(\ell\)，令
\[
\ell(\alpha)=0,\qquad \ell(\beta)=1.
\]
联合响应表为
\[
\begin{array}{c|cc}
&q&\ell\\ \hline
\alpha&0&0\\
\beta&0&1
\end{array}
\]
于是原来可合并的两态在扩大的协议族上被分开。当前读数没有区别，不代表未来续接仍然代表无关。

在自由树中，同样的障碍由
\[
t=\langle\alpha,\beta\rangle,\qquad
t'=\langle\beta,\alpha\rangle
\]
给出：\(c(t)=c(t')=(1,1)\)，但左位置协议分别返回 \(\alpha,\beta\)。因此组成边界对组成和 Fibonacci 动作词任务充分，对保留左右位置的任务不充分。

### 82.4 动态闭合和内部选择

若 \(T_a:S\rightharpoonup S\) 是状态更新，协议也因权限或控制更新为 \(u_a:P\rightharpoonup P\)，则动态边界需满足
\[
\eta\circ T_a=\bar T_a\circ\eta,\qquad
\pi\circ u_a=\bar u_a\circ\pi,
\tag{82.8}
\]
并且合法性、失败与记录读出也下降：
\[
\begin{aligned}
\operatorname{Adm}_a(s,p)
 &=\overline{\operatorname{Adm}}_a(\eta(s),\pi(p)),\\
\operatorname{Out}_a(s,p)
 &=\overline{\operatorname{Out}}_a(\eta(s),\pi(p)).
\end{aligned}
\tag{82.9}
\]
若选择器由状态决定下一协议，还必须有
\[
\mathsf{choose}(s)=\overline{\mathsf{choose}}(\eta(s)).
\tag{82.10}
\]
否则同一边界状态可能要求不同动作，静态读出虽能下降，内部运行却不能闭合。记忆更新同样必须是摘要和实际结果的函数；不能把参考、权限或选择器藏在边界外。

这些条件把观察者自读、动作选择和记忆更新留在同一接口中。它们不是给二叶结构再加一个系统外主体，而是把协议族扩大后重新计算同一个行为核。

### 82.5 适用边界与已有接口

固定状态集合上的单侧行像因子化对应 UnifiedObserverRepresentation；同时要求状态行商和协议列商、满射以及两侧外延性时，对应 DoubleExtensionalQuotientUniversality。动作词和控制器的动态运输还需显式检查式(82.8)—(82.10)；抽象接口不替具体任务证明共同来源、权限、失败标签、记录字段和实际像闭合。

本节限定于普通集合、确定性响应、声明过的协议和有限动作词。随机读数需要结果核，量子协议需要态、通道和正性条件，无限完成需要分离性、线程完备性和实际来源满射。没有新增 Lean 声明，也没有把二叶生成层提升为所有关系的普适本体。

## 82.99 追加锚

## 83. 静态保构造签名下的二原子最小性

第 82 节说明了为什么“二叶”不能直接等同于“二状态”。在静态、保构造、禁止额外解码的合同中，\(\alpha,\beta\) 这两个零元生成元确实不能再减；这是一条生成签名的相对最小性，而不是所有动态过程的状态下界。

### 83.1 静态签名

令
\[
\mathcal T_2=\mu X\bigl(\{\alpha,\beta\}\sqcup(X\times X)\bigr),
\qquad
\mathcal T_1=\mu X\bigl(\{\ast\}\sqcup(X\times X)\bigr).
\]
若 \(h:\mathcal T_1\to\mathcal T_2\) 保持二元构造器，则它由 \(t_0=h(\ast)\) 唯一决定，并满足
\[
h(\langle s,t\rangle)=\langle h(s),h(t)\rangle.
\tag{83.1}
\]

若 \(t_0=\alpha\)，结构归纳说明 \(h(u)\) 的所有叶都是 \(\alpha\)，所以 \(\beta\) 不在像中；\(t_0=\beta\) 时对称。若 \(t_0=\langle r,s\rangle\)，保构造闭包始终以二元构造为根，永远不会产生零元叶，故 \(\alpha,\beta\) 都不在像中。三种情形覆盖 \(t_0\)，因此 \(h\) 不可能满射。带两个常数和同一构造器的恒等解释达到满射，于是
\[
\boxed{
\text{静态保构造生成 }\mathcal T_2
\text{ 至少需要两个零元生成元和一个二元构造器。}
}
\tag{83.2}
\]
删除二元构造器则只能生成叶，不能覆盖复合项。

### 83.2 与一粒动态种子的区别

加入
\[
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle
\]
后，从 \(\alpha\) 出发先用 \(\rho\) 取得 \(\beta\)，再用有序配对和 \(\rho\) 的有限组合，可以生成任意有限的 \(\alpha/\beta\) 二叉树。这不与式(83.2)矛盾，因为式(83.2)禁止额外替换和解码。

因此要区分
\[
\boxed{
\text{静态零元数}=2,\qquad
\text{加入 }\rho\text{ 后的动态种子数}=1,\qquad
\text{组成未来边界的线性维数}=2.
}
\tag{83.3}
\]
三者分别回答静态签名、动态生成和指定线性读出的不同问题。

### 83.3 静态对称与动态方向

静态自由代数有叶交换自同构
\[
\tau(\alpha)=\beta,\qquad
\tau(\beta)=\alpha,\qquad
\tau(\langle s,t\rangle)=\langle\tau(s),\tau(t)\rangle,\qquad
\tau^2=\mathrm{id}.
\]
但 \(\tau\) 不与 \(\rho\) 交换：
\[
\tau\rho(\alpha)=\alpha,\qquad
\rho\tau(\alpha)=\langle\beta,\alpha\rangle.
\tag{83.4}
\]
所以静态生成层可以交换两个叶，而 Fibonacci 动力学为它们赋予方向角色。把 \(\alpha,\beta\) 强行商成一个无向原子，会同时改变原来的替换、配对或读出合同。

### 83.4 范围

式(83.2)支持“FIBONACCI_ATOMIC_RELATION_GENERATION 更接近生成底座”的判断，但只在静态保构造签名下成立。编码、商、额外操作和带状态解码器都可能用一个符号携带两个叶；那已经改变了签名或任务接口，必须重新计算行为核和动态充分边界。本文没有把两个叶提升为现实关系的普适本体，也没有新增 Lean 声明。

## 83.99 追加锚

## 84. 有限呈示下的坐标支撑与反向存活边界递推

§20、§26 和 §29 已分别给出总化动作词、共同未来核以及失败分支的完整语义；§81—§83 又给出动作运输、协议侧和二叶生成层。本节不再重复一般未来核的构造，而把它特化到一个**有限、分阶段、显式呈示**的合同，使坐标支撑能够反向计算。新增内容是：如何从这个有限核选择可执行坐标字段，以及如何把它应用回 §80。§83 的生成元数仍是另一层问题。以下是普通数学推导和有限检查，不是新增 Lean 核验，也不作全球原创性声明。

### 84.1 既有未来核的有限阶段呈示

**定义 84.1（有限合同呈示）。** 固定 $N\in\mathbb N$，在阶段 $j=0,\ldots,N$ 取有限坐标集 $I_j$ 及同一实际来源上的有限状态像

$$
S_j\subseteq\prod_{i\in I_j}X_{j,i}.
\tag{84.1}
$$

若相同坐标元组因未记录历史而有不同未来响应，必须先把该历史补入 $I_j$；否则它不是本节所说的确定性呈示。失败原因、权限和须保留的记录也只有在声明任务要求区分时才进入状态标签。

对 $j<N$ 固定一组**声明的候选动作** $A_j$。本节采用 all-actions 合同：未来实验可以尝试 $A_j$ 中的每个动作，非法尝试必须总化为带类型失败。对每个动作给出有限结果标签集 $Y_{j,a}$、两两不交的分支域 $D_{j,a,y}\subseteq S_j$ 及

$$
T_{j,a,y}:D_{j,a,y}\longrightarrow S_{j+1}.
\tag{84.2}
$$

这些分支连同声明的失败标签覆盖 $S_j$；若任务只允许 selector 选择的动作，就把允许动作族改成该 selector 合同，不能把 all-actions 结论转用于更窄任务。内部结果标签若未被任务观察，应先在总化响应中汇总，不能因为枚举方便而把隐藏标签加入行为核。

令 $Q_j$ 只包含任务声明要保留的当前输出、合法性、失败、记录和选择器读数；若某个分支可用性本身要被观察，才把相应指示函数 $\delta_{j,a,y}=\mathbf1_{D_{j,a,y}}$ 放入 $Q_j$。因此 $\mathbf Q_j(s)=(q(s))_{q\in Q_j}$ 是本合同的当前联合响应，$Q_N$ 是终端联合响应。停机若需放入固定时域，只能填充为不新增查询的吸收记录；阶段编号若由调度外部给定，不计入观察者记忆。

### 84.2 有限未来核是既有动作词核的阶段特化

把每个 $(a,y)$ 的域指示和保留结果看作总化动作词的首步标签，定义有限 horizon 核

$$
\begin{aligned}
sK_Nt&\iff\mathbf Q_N(s)=\mathbf Q_N(t),\\
sK_jt&\iff\mathbf Q_j(s)=\mathbf Q_j(t)\ \land\\
&\quad\forall a\in A_j\ \forall y\in Y_{j,a},\quad
s\in D_{j,a,y}\iff t\in D_{j,a,y},\\
&\quad\text{且在该共同分支上 }T_{j,a,y}(s)K_{j+1}T_{j,a,y}(t).
\end{aligned}
\tag{84.3}
$$

这里的 $K_j$ 正是 §20、§26 的完整未来行为核在阶段 $j$ 的 $N-j$ 截断；它只量化本定义声明的有限动作、结果和查询，不声称无限时域或普遍关系核。阶段标签若要由内部选择器读取，必须已进入 $Q_j$ 或状态。

令 $M_j=S_j/K_j$、$q_j(s)=[s]_{K_j}$。有限响应树的归纳给出

$$
\begin{aligned}
\mathbf Q_j&=\overline{\mathbf Q}_j\circ q_j,&
\pi_j&=\bar\pi_j\circ q_j,\\
q_{j+1}\circ T_{j,a,y}&=\bar T_{j,a,y}\circ q_j,&
\bar T_{j,a,y}([s])&=[T_{j,a,y}(s)].
\end{aligned}
\tag{84.4}
$$

其中最后两式只在共同、合法的分支上解释；非法分支已由前一行的类型标签比较。若 $m_j:S_j\to B_j$ 是任意能恢复本合同全部有限未来响应的确定性编码，则

$$
\ker m_j\subseteq K_j,
\qquad q_j=d_j\circ m_j,
\qquad d_j:m_j[S_j]\twoheadrightarrow M_j.
\tag{84.5}
$$

因此 $M_j$ 是本有限合同的未来充分商；它自身带有式(84.4)的可更新结构。式(84.5)只对“能恢复全部响应”的编码给出下界；若还要求任意 $m_j$ 自身有更新下降，则必须另加该条件，不能从编码充分性单独推出。

**证明。** 在有限阶段树上反向归纳：末端比较 $Q_N$；前一层先比较当前保留响应和总化分支标签，再比较每个共同分支的后继类。这是 §20/§26 的未来核证明在阶段标签展开后的有限呈示。归纳同时给出式(84.4)的代表元无关性。若两个状态被 $m_j$ 合并而其有限响应树不同，解码器对同一记忆必须给出两种响应，矛盾；令 $d_j(m_j(s))=[s]$ 即得唯一满射。$\square$

### 84.3 语义支撑与反向寄存器规则

**定义 84.3（支撑与前像支撑）。** 对 $D\subseteq S_j$、函数族 $f$ 和坐标投影 $\eta_L(s)=s|_L$，定义语义支撑族

$$
\operatorname{Supp}_D(f)=
\{L\subseteq I_j:\ \forall s,t\in D,\quad
\eta_L(s)=\eta_L(t)\Rightarrow f(s)=f(t)\}.
\tag{84.6}
$$

函数族的相等逐项解释。选取一个经核对的支撑，记为 $\operatorname{supp}_D(f)$；这不是默认存在唯一最小集合。有限表可枚举所有子集并检查全部状态对，再用预先固定的顺序选取一个支撑。定义分支的前像支撑为所选集合

$$
\operatorname{pre}_{j,a,y}(L)
=\operatorname{supp}_{D_{j,a,y}}(\eta_L\circ T_{j,a,y}).
\tag{84.7}
$$

定义域本身的依赖由 $Q_j$ 负责，不能因只在 $D_{j,a,y}$ 内求支撑而忘掉分支是否可用。空定义域可选空支撑。

**命题 84.4（反向存活的充分性与删字段见证）。** 按选定支撑令

$$
\boxed{
\begin{aligned}
L_N&=\operatorname{supp}_{S_N}(\mathbf Q_N),\\
L_j&=\operatorname{supp}_{S_j}(\mathbf Q_j)
\ \cup\!\!\bigcup_{a\in A_j,\ y\in Y_{j,a}}
\operatorname{pre}_{j,a,y}(L_{j+1}).
\end{aligned}}
\tag{84.8}
$$

则 $\ker\eta_{L_j}\subseteq K_j$，且 $\eta_{L_j}$ 上的查询、选择器和更新可执行下降：

$$
q_j=d_j\circ\eta_{L_j},\qquad
\eta_{L_{j+1}}\circ T_{j,a,y}
=\widehat T_{j,a,y}\circ\eta_{L_j}
\quad\text{于 }D_{j,a,y}.
\tag{84.9}
$$

对 $i\in L_j$，从这一投影删去 $i$ 后仍充分，当且仅当不存在一对实际状态 $s,t$ 满足

$$
\eta_{L_j\setminus\{i\}}(s)=\eta_{L_j\setminus\{i\}}(t),
\qquad \neg(sK_jt).
\tag{84.10}
$$

若这样的状态对存在，命题84.2给出一个声明的有限区分实验；它是该字段相对于当前投影不可删的见证。

**证明。** 末端由支撑定义成立。若两态在 $L_j$ 上相等，它们有相同的 $Q_j$，故分支定义域一致；每个启用分支的前像支撑又给出后继在 $L_{j+1}$ 上相等。归纳假设及式(84.3)给 $sK_jt$。相同投影得到相同后继投影，也直接给式(84.9)中的良定义更新；查询和选择器同理。删字段判据就是 $\ker\eta_{L_j\setminus\{i\}}\subseteq K_j$ 的否定与否；原投影充分保证见证两态必在字段 $i$ 上不同。$\square$

支撑必须相对于实际像判断。例如 $S=\{(0,0),(1,1)\}$ 上的读出 $f(x,y)=x$ 同时由 $\{x\}$、$\{y\}$ 支撑，但不由其空交集支撑；这两个实际状态已给反例。只搜索“保持其他全部坐标不动、改变一坐标”的状态对，在这个相关像上也会漏掉区别。即使实际像是完整二比特乘积，末端只读 $x\mathbin{\mathrm{xor}}y$ 时，两个坐标都不能从坐标投影中删除，但一个奇偶位已有两值精确商，而原投影有四值。因此式(84.8)给充分的寄存器实现，不保证坐标数或消息数最小。语法上读取的变量只有在所有控制、定义域和副作用依赖已计入时才给充分支撑；变量名出现并不证明语义不可删。

### 84.4 作为有限实例：§80 的两次拼接由同一递推定位字段寿命

**命题 84.5（中间八态到四值边界）。** 这是命题84.4在 §80 合同上的有限实例，而非新的普遍下界。取 §80 的成功中间态 $v=(x,h,y)\in\mathbb B^3$。下一步候选仍为全部 $a=(y',z)\in\mathbb B^2$，保留 §80 的 $\sigma$、合法性和 $\rho_a$，内部选择器取 $\pi(v)=(y,0)$，额外档案读出为空。终端读取输出比特或严格失败。终端唯一值字段存活，反向式(84.8)可取

$$
L_{\mathrm{mid}}=\{x,y\},\qquad
vK_{\mathrm{mid}}v'
\iff (x,y)=(x',y'),\qquad
M_{\mathrm{mid}}\cong\mathbb B^2.
\tag{84.11}
$$

**证明。** $J_2$ 的合法性及选择器只读 $y$，合法输出只读 $x$ 和当前动作输入 $z$；后继也只保留这个输出。失败响应不读取 $h$。于是当前查询支撑和全部后继前像支撑的并可取 $\{x,y\}$。式(84.9)就是 §80.6 的下降等式。

删除 $y$ 会合并 $v=(0,0,0)$ 与 $v'=(0,0,1)$；动作 $(0,0)$ 对前者合法并输出 $0$，对后者失败。删除 $x$ 会合并 $(0,0,0)$ 与 $(1,0,0)$；同一合法动作 $(0,0)$ 的输出分别为 $0,1$。这两对都是实际来源的联合像。更一般地，当前读出 $\sigma$ 恢复 $x$，声明的选择器 $\pi(v)=(y,0)$ 恢复 $y$，故联合查询相等必使 $(x,y)=(x',y')$。于是任意未来充分编码至少区分全部四个 $(x,y)$，而该编码恰好做到；每类含两个 $h$ 值。在完整来源 $\mathbb B^{\{x,h,y,z\}}$ 上，每类则含四个 $h,z$ 组合。$\square$

§80.5 的空间赋值、带动作标签的时间响应树、合法端口边界和双寄存器记忆都由 $(x,y)$ 生成并恢复它，故原表的恢复器在这同一个四态实际像上仍互逆；通过这些双射运输式(84.9)就得到各自更新。中间失败另外占一个有类型的类，不计入这四态，也不把失败填成正常位。这里复用 §80 的恢复器，不把该实例的四态结论提升为任意协议的容量界。

$h$ 的寿命终点在 $J_1$ 已完成相等性检查之后。检查之前必须保留足以判断 $h_A=h_C$ 的关系；检查之后，当前合同再无 $h$ 的消费者。若新增档案读出 $h$ 或把选择器改为 $(h,0)$，则 $(0,0,0)$ 与 $(0,1,0)$ 虽有相同 $(x,y)$，新增响应却不同，递推必须保留额外区别。这里没有从“当前不输出 $h$”推出“以后永远不需 $h$”。§81 的组成任务和 §82 的协议侧也应按各自新增查询重新计算；本节未改变它们的动作族或生成签名。

### 84.5 同时存活槽数是另一项资源

另设固定有限二叉表达式树的破坏式求值合同：每个叶只装入一次，每个内部节点只在两个子结果都在场时执行一次，原子地覆写其中一槽并释放另一槽。中间结果不能复制、重算、提前丢弃、外存溢出、借代数律改树或与别的结果合包；树的左右语义保留，但求值次序可选并可交错。每个节点结果占一槽，槽的字母表与位宽另计。输入装载前的外部来源、程序和控制栈不计入槽数，根结果占一槽。

在这个独立合同中，最小峰值槽数是经典 Strahler／表达式树寄存器递推：[^boundary84-register]

$$
s(\mathrm{leaf})=1,\qquad
s(v)=
\begin{cases}
\max\{s(v_l),s(v_r)\},&s(v_l)\ne s(v_r),\\
s(v_l)+1,&s(v_l)=s(v_r).
\end{cases}
\tag{84.12}
$$

这一已知中间工具只用于区分本节两种资源。其树归纳如下。子树需求为 $p,q$，先算左或先算右分别达到 $\max\{p,1+q\}$、$\max\{q,1+p\}$；较大者先算给式(84.12)的上界。任一全树求值限制到某个子树，仍是该子树的合法求值，故至少需 $\max\{p,q\}$ 槽。若 $p=q=k$ 而全程只有 $k$ 槽，每个子树都必须在某时刻独占至少 $k$ 槽。取两个子树首次达到此值的较早时刻；另一子树此前不能已经开始，因为已开始的子树在根合并之前始终至少留下一个活结果。等另一子树达到 $k$ 时，先前子树至少仍有一个活结果，矛盾。这也覆盖交错调度，给 $k+1$ 的下界。

与 §79 的语义容量对照，四叶平衡 XOR 树的每个非空切面只需一个奇偶位，$\kappa_A=2$，但式(84.12)给根需求 $3$ 槽。四叶梳形树在“每个叶出现一次、根输出保留有序四比特元组”的特定任务下满足 $\kappa_A=2^{|A|}$；根有 $16$ 种输出，却只需 $2$ 槽：先保留已形成的元组，再装下一叶，合并后释放一槽。元组槽的位宽随长度增长，不能把两槽说成两比特。两例都使用同一完整四比特输入域；容量直接沿用 §79 的定义。它们分离同时存活槽数与消息／端口 profile 的标签数，不给复制、重算、编码改写或其他执行模型下的普适下界。

[^boundary84-register]: Ravi Sethi and J. D. Ullman, *The Generation of Optimal Code for Arithmetic Expressions*, Journal of the ACM 17(4), 1970, 715–728, [doi:10.1145/321607.321620](https://doi.org/10.1145/321607.321620)。这里只借表达式树的寄存器分配背景；式(84.12)按本节明确的槽合同给出了独立证明。

### 84.6 有限枚举与开放边界

以下 Python 只使用标准库，检查 §80 的全部状态与候选动作、式(84.8)的具体支撑以及独立求值合同。`F` 是区别于正常输出的失败标签。`inputs` 枚举任意局部消息对及带失败输入；只有匹配的子集是 §80 同一完整来源的限制。槽数检查直接搜索全部可达活结果前沿，允许任意叶装载和任意已就绪兄弟合并，以最小峰值为代价；它不把式(84.12)自身当作搜索转移规则。前沿所覆盖的叶记录了已消耗输入，保证没有复制或重算。

```python
from itertools import product, combinations
from functools import lru_cache
from heapq import heappush, heappop

B = (0, 1)
F = "failure"
actions = tuple(product(B, repeat=2))
success = tuple(product(B, repeat=3))  # (x,h,y)
mid = success + (F,)
inputs = tuple(product(actions + (F,), repeat=2))

def j1(pair):
    a, c = pair
    if a == F or c == F or a[0] != c[0]:
        return F
    return (a[1], a[0], c[1])

def mem(v):
    return F if v == F else (v[0], v[2])

def step(v, a):
    return F if v == F or v[2] != a[0] else v[0] ^ a[1]

def queries(v):
    sigma, selector = (F, "stop") if v == F else (v[0], (v[2], 0))
    # output/result tags determine branch domains; record is empty.
    return (sigma, selector, tuple((step(v, a) != F, step(v, a), ())
                                  for a in actions))

def proj(v, indices):
    return tuple(v[i] for i in sorted(indices))

def supports(states, indices, read):
    return all(proj(s, indices) != proj(t, indices) or read(s) == read(t)
               for s in states for t in states)

def support(states, width, read):
    for size in range(width + 1):
        for indices in combinations(range(width), size):
            if supports(states, indices, read):
                return frozenset(indices)
    raise AssertionError("full coordinates must support the readout")

# Backward response signatures at the three stages; terminal query is identity.
k2 = {s: s for s in B + (F,)}
k1 = {v: (queries(v), tuple(k2[step(v, a)] for a in actions)) for v in mid}
k0 = {p: (j1(p) != F, mem(j1(p)), k1[j1(p)]) for p in inputs}
assert tuple(len(set(k.values())) for k in (k0, k1, k2)) == (5, 5, 3)
assert all((k1[s] == k1[t]) == (mem(s) == mem(t)) for s in mid for t in mid)
assert sum(j1(p) != F for p in inputs) == 8
plain_pairs = tuple(product(actions, repeat=2))
assert len(plain_pairs) == 16 and sum(j1(p) == F for p in plain_pairs) == 8
for p in inputs:
    for a in actions:
        v, r = j1(p), mem(j1(p))
        expected = F if r == F or r[1] != a[0] else r[0] ^ a[1]
        assert step(v, a) == expected
for x, h, y, z in product(B, repeat=4):
    assert step(j1(((h, x), (h, y))), (y, z)) == x ^ z

# Terminal field {0}; preimage supports are checked separately on each result domain.
L = support(success, 3, queries)
for a in actions:
    for result in B + (F,):
        domain = tuple(v for v in success if step(v, a) == result)
        L |= support(domain, 3, lambda v: (step(v, a),))
assert L == frozenset((0, 2))
assert not supports(success, (0,), lambda v: k1[v])  # deleting y
assert not supports(success, (2,), lambda v: k1[v])  # deleting x
assert step((0, 0, 0), (0, 0)) == 0
assert step((0, 0, 1), (0, 0)) == F
assert step((1, 0, 0), (0, 0)) == 1
assert len({(k1[v], v[1]) for v in success}) == 8  # h record/selector added
assert all(step(v, (v[2], 0)) == v[0] for v in success)

# A delayed read tests the preimage term without any immediate state query.
delayed = tuple(product(B, repeat=2))
assert support(delayed, 2, lambda v: ()) == frozenset()
assert support(delayed, 2, lambda v: (v[1],)) == frozenset((1,))
diagonal = ((0, 0), (1, 1))
assert supports(diagonal, (0,), lambda v: v[0])
assert supports(diagonal, (1,), lambda v: v[0])
assert not supports(diagonal, (), lambda v: v[0])
assert support(delayed, 2, lambda v: v[0] ^ v[1]) == frozenset((0, 1))
assert len({v[0] ^ v[1] for v in delayed}) == 2

def spatial(u):
    return (("X", u[0]), ("Y", u[1]))
def temporal(u):
    return tuple(step((u[0], 0, u[1]), a) for a in actions)
def time_inverse(r):
    y = 0 if r[0] != F else 1
    return (r[2*y], y)
def boundary(u):
    return (u[0], frozenset((u[1],)))
encoders = (spatial, temporal, boundary, lambda u: u)
decoders = (lambda r: (dict(r)["X"], dict(r)["Y"]), time_inverse,
            lambda r: (r[0], next(iter(r[1]))), lambda r: r)
for encode, decode in zip(encoders, decoders):
    assert len({encode(u) for u in actions}) == 4
    for u in actions:
        assert decode(encode(u)) == u
        assert encode(decode(encode(u))) == encode(u)

@lru_cache(None)
def trees(n):
    if n == 1:
        return (None,)
    return tuple((l, r) for k in range(1, n)
                 for l in trees(k) for r in trees(n-k))

def strahler(t):
    if t is None:
        return 1
    l, r = map(strahler, t)
    return max(l, r) + (l == r)

def slots(t):
    children, coverage, leaves = [], [], []
    def build(u):
        if u is None:
            i = len(children)
            children.append(None)
            coverage.append(1 << len(leaves))
            leaves.append(i)
            return i
        l, r = map(build, u)
        i = len(children)
        children.append((l, r))
        coverage.append(coverage[l] | coverage[r])
        return i
    root = build(t)
    best, todo = {0: 0}, [(0, 0)]
    while todo:
        peak, state = heappop(todo)
        if best[state] != peak:
            continue
        if state == 1 << root:
            return peak
        used = 0
        for i, covered in enumerate(coverage):
            if state >> i & 1:
                used |= covered
        nexts = [state | (1 << i) for i in leaves if not (used & coverage[i])]
        for i, pair in enumerate(children):
            if pair is not None:
                l, r = pair
                if state >> l & 1 and state >> r & 1:
                    nexts.append((state & ~(1 << l) & ~(1 << r)) | (1 << i))
        for ns in nexts:
            np = max(peak, bin(ns).count("1"))
            if np < best.get(ns, 10**9):
                best[ns] = np
                heappush(todo, (np, ns))
    raise AssertionError("root is unreachable")

checked = 0
for n in range(1, 8):
    for t in trees(n):
        assert slots(t) == strahler(t)
        checked += 1
assert checked == 197
balanced = ((None, None), (None, None))
comb = (((None, None), None), None)
assert (slots(balanced), slots(comb)) == (3, 2)

# §79 response classes, computed directly from all completions.
def capacity(indices, task):
    indices = tuple(indices)
    rest = tuple(i for i in range(4) if i not in indices)
    rows = set()
    for local in product(B, repeat=len(indices)):
        row = []
        for external in product(B, repeat=len(rest)):
            values = dict(zip(indices, local))
            values.update(zip(rest, external))
            row.append(task(tuple(values[i] for i in range(4))))
        rows.add(tuple(row))
    return len(rows)
for size in range(1, 5):
    for indices in combinations(range(4), size):
        assert capacity(indices, lambda v: sum(v) % 2) == 2
        assert capacity(indices, lambda v: v) == 2**size
print("PASS: 16 sources; J1 16+9 failure-input pairs; 100 chains; "
      "36 mid/actions; classes 5/5/3; support and four inverses; "
      "197 trees; slots 3/2; XOR/tuple cut capacities")
```

本有限检查的覆盖为：16 个完整来源，16 个普通 $J_1$ 消息对及 9 个至少一端失败的消息对，合计 100 个两步候选链；9 个含失败的中间态乘 4 个动作；三阶段响应类数依次为 $5,5,3$，成功中间态单独为四类。小树枚举覆盖 1—7 叶的全部 197 棵有序满二叉树；两项四比特任务还枚举全部非空切面及其补全。有限检查通过不替代命题84.2、84.4的任意有限合同归纳，也不替代式(84.12)的树归纳。

开放边界有明确的类型：扩大未来查询或改变内部策略会改变 $K_j$ 与字段寿命；无限时域需另证稳定或实际来源的完成条件；随机或量子分支需另给结果律及其更新语义。语义最小商不保证最便宜的取得、编码或运算，坐标支撑搜索也未给高效复杂度界。四种表达的互逆仍限于 §80 的声明任务及实际像，不能恢复未保留的原始历史、物理时长或所有可能观察。本文未进行消化、Lean 或内核验证。

## 84.99 追加锚

## 85. 生成语法边界的可压缩性与 lumpability

第 81—84 节分别处理二叶生成层、协议画像、静态保构造和有限动作词边界。本节给出它们与边界响应递推之间的直接接口：只有当细层局部核在同一边界纤维上具有相同的聚合响应时，细层过程才可以被压成边界核。

### 定义 85.1（生成项、边界映射与细层核）

令 $\mathcal T_{\mathrm F}$ 是二叶生成项集，$\eta_\Sigma:\mathcal T_{\mathrm F}\to B_\Sigma$ 是某个切面的边界摘要。对一次合法接续 $e:\Sigma\to\Sigma'$，令 $Z_e$ 是被消去的内部变量，细层权重为

$$
W_e(t,z,t')
$$

取值于同一个半环 $(K,\oplus,\otimes)$。给定细层响应 $H_\Sigma(t)$，其精确推进为

$$
H_{\Sigma'}(t')=
\bigoplus_{t,z}H_\Sigma(t)\otimes W_e(t,z,t').
$$

### 定理 85.2（纤维聚合条件与边界递推）

若对任意 $t_1,t_2$ 满足 $\eta_\Sigma(t_1)=\eta_\Sigma(t_2)$，以及任意 $z,b'\in B_{\Sigma'}$，都有

$$
\bigoplus_{\eta_{\Sigma'}(t')=b'}W_e(t_1,z,t')
=
\bigoplus_{\eta_{\Sigma'}(t')=b'}W_e(t_2,z,t'),
\tag{85.1}
$$

则由下式定义的代表无关边界核 $\overline W_e(b,z,b')$ 对所有细层权重 $H_\Sigma$ 都给出正确的边界聚合

$$
\overline H_\Sigma(b)=
\bigoplus_{\eta_\Sigma(t)=b}H_\Sigma(t)
$$

满足

$$
\boxed{
\overline H_{\Sigma'}(b')
=
\bigoplus_{b,z}\overline H_\Sigma(b)\otimes
\overline W_e(b,z,b').
}
\tag{85.2}
$$

证明。式（85.1）使

$$
\overline W_e(b,z,b')
:=
\bigoplus_{\eta_{\Sigma'}(t')=b'}W_e(t,z,t')
$$

与代表元 $t$ 无关，故这个聚合定义的边界核代表元无关。把细层递推按 $\eta_\Sigma(t)=b$ 和 $\eta_{\Sigma'}(t')=b'$ 分组，利用 $\oplus,\otimes$ 的分配律即可得到（85.2）。在非消去半环中，可能存在不同系数给出同一个线性作用；本定理固定的是上述按纤维求和的规范核，而不是抽象系数表示的唯一性。$\square$

若（85.1）失败，则不存在对所有细层输入都正确的边界核。取在同一边界值上分别集中于 $t_1,t_2$ 的两个输入，某个 $b'$ 的下一响应不同；任何只读取 $\overline H_\Sigma(b)$ 的更新都会把这两种响应合并。因此，失败不是“压缩算法暂时不够好”，而是当前边界没有截住仍影响联合实现的关系。

### 推论 85.3（行为商是可压缩性的安全边界）

若 $\eta_\Sigma$ 的纤维包含于声明任务的完整行为核 $\sim_{\mathcal C}$，并且局部核、合法性、失败、记录和选择器都在该核上保持常值，则式（85.1）成立，边界递推可自治执行。反之，只要存在同一边界纤维中的一对细层项在某个声明续接上给出不同完整响应，式（85.1）必失败。

因此，Fibonacci 的二维组成边界只在加性数量任务中满足（85.1）；一旦加入括号、来源、权限、失败或时钟字段，必须把相应字段并入 $\eta_\Sigma$，或改用完整行为商。这里的“两个通道”是一个可验证的任务合同，不是所有过程的固定边界容量。

## 85.99 追加锚

## 86. 观察标签投影后的精确纤维聚合判据

第85节的式(85.1)逐个保留内部标签 $z$，而式(85.2)的最终输出已经对 $z$ 求和。这两种任务有不同的必要条件。本节保留第85节的充分方向，并限定其“条件失败则不存在边界核”的反向断言：只有对合同实际保留的标签比较聚合行，才能得到充要条件。对于全部点输入都可用的有限有单位半环模型，边界核的系数也由这些点输入唯一确定，不需要消去律。

### 定义 86.1（同源联合核与保留标签）

固定有限非空集合 $S,S',Z,Y$，以及有单位半环 $(K,+,\cdot,0,1)$。加法交换，乘法不要求交换；以下乘积始终保持“输入权重在左、核权重在右”的顺序。给定摘要映射，并将它们的陪域限制到实际像：

$$
q:S\longrightarrow B=q[S],\qquad
q':S'\longrightarrow B'=q'[S'].
$$

给定同一实际来源的一步联合核 $W:S\times Z\times S'\to K$，以及合同声明的保留标签投影 $\pi:Z\to Y$。不要求 $\pi$ 满射，未实现标签的求和为零。$W$ 同时指定标签与后继的权重，不能由分别取得的标签边缘和后继边缘任意拼接；一般半环下也不假定概率归一化。

对任意输入 $H:S\to K$，定义

$$
\begin{aligned}
A_\pi(s,y,b')
&=\sum_{\substack{z\in Z\\\pi(z)=y}}
  \sum_{\substack{s'\in S'\\q'(s')=b'}}W(s,z,s'),\\
(P_qH)(b)&=\sum_{\substack{s\in S\\q(s)=b}}H(s),\\
G_\pi(H)(y,b')&=\sum_{s\in S}H(s)A_\pi(s,y,b').
\end{aligned}
\tag{86.1}
$$

$G_\pi$ 的输出保留 $y$ 与 $b'$ 的联合权重。$\pi=\operatorname{id}_Z$ 是逐标签保留的合同；$Y=\{\ast\}$、$\pi(z)=\ast$ 是完全收缩标签的合同。其余投影给出部分保留的任务，不在推导中暗自改变。

### 定理 86.2（精确聚合的充要条件与唯一核）

在定义86.1的条件下，存在唯一函数 $L_\pi:B\times Y\times B'\to K$，使

$$
G_\pi(H)(y,b')
=\sum_{b\in B}(P_qH)(b)L_\pi(b,y,b')
\quad\text{对所有 }H:S\to K,\ y\in Y,\ b'\in B',
\tag{86.2}
$$

当且仅当

$$
q(s)=q(t)\quad\Longrightarrow\quad
A_\pi(s,y,b')=A_\pi(t,y,b')
\quad\text{对所有 }s,t\in S,\ y\in Y,\ b'\in B'.
\tag{86.3}
$$

此时唯一核由实际来源确定：

$$
L_\pi(q(s),y,b')=A_\pi(s,y,b').
\tag{86.4}
$$

证明。若(86.3)成立，对每个 $b\in B$ 选取 $q(s_b)=b$，令 $L_\pi(b,y,b')=A_\pi(s_b,y,b')$。纤维常值保证与代表选择无关。对有限和按 $q$ 纤维分组并用分配律，得到

$$
\begin{aligned}
\sum_{s\in S}H(s)A_\pi(s,y,b')
&=\sum_{b\in B}\sum_{q(s)=b}H(s)L_\pi(b,y,b')\\
&=\sum_{b\in B}\left(\sum_{q(s)=b}H(s)\right)L_\pi(b,y,b').
\end{aligned}
$$

反过来，设某个 $L_\pi$ 对全部输入满足(86.2)。对任意 $s\in S$，取点输入 $\delta_s(s)=1$，其余位置为 $0$。则 $P_q\delta_s$ 在 $q(s)$ 处为 $1$，其余为 $0$；代入(86.2)即得(86.4)。若 $q(s)=q(t)$，右侧核值相同，故(86.3)成立。又因每个 $b\in B$ 都有实际代表，(86.4)决定 $L_\pi$ 的全部系数，因此唯一。证明没有相减、约分或消去；即使不另设 $0\ne1$，同一论证也成立。证毕。

取 $\pi=\operatorname{id}_Z$，(86.3)就是式(85.1)的逐标签条件，因而它对这个合同既充分又必要。取常值 $\pi$，精确的必要条件只比较 $\sum_z\sum_{q'(s')=b'}W(s,z,s')$；式(85.1)仍充分，却不再必要。任意指定投影的充要条件都是对应的(86.3)，不能把未经投影的式(85.1)作为全部合同的必要条件。

同样，在本节的有限、有单位、全输入条件下，第85.2节关于“非消去半环可能有不同系数给出同一线性作用”的附注不适用：点输入已经逐项分离系数。若把 $B$ 扩成含未实现值的陪域，或把允许输入限制到不足以提供这些点探针的族，则本证明的唯一性或必要性步骤不再自动成立；那是另一份合同。

### 命题 86.3（共同画像、记忆与实际像恢复）

定义当前切面与一步响应的联合画像

$$
\sigma_\pi:S\longrightarrow B\times K^{Y\times B'},\qquad
\sigma_\pi(s)=\bigl(q(s),A_\pi(s,-,-)\bigr),
\qquad Q_\pi=\sigma_\pi[S].
\tag{86.5}
$$

对任意映射 $f$，记 $\ker(f)=\{(s,t):f(s)=f(t)\}$。给定同一来源上的记忆 $m:S\to M$，存在唯一解码器 $d:m[S]\to Q_\pi$ 满足

$$
d(m(s))=\sigma_\pi(s)\quad(s\in S)
\quad\Longleftrightarrow\quad
\ker(m)\subseteq\ker(\sigma_\pi),
\tag{86.6}
$$

其中左侧的量词是“存在唯一这样的 $d$”。该解码器存在时自动满射；它是双射，当且仅当

$$
\ker(m)=\ker(\sigma_\pi).
\tag{86.7}
$$

证明。解码器存在时，$m(s)=m(t)$ 必推出 $\sigma_\pi(s)=\sigma_\pi(t)$。核包含成立时，以 $d(m(s)):=\sigma_\pi(s)$ 定义；包含关系保证代表无关，定义域的每一点均为实际记忆，故唯一；目标的每一点也有实际来源，故满射。若两核相等，则相同画像必有相同记忆，故 $d$ 单射；若 $d$ 单射，则 $\sigma_\pi(s)=\sigma_\pi(t)$ 迫使 $m(s)=m(t)$，给出反向包含。证毕。

因此，$\sigma_\pi$ 是同时保留当前 $q$ 与全部指定一步响应行的最粗摘要，最小性按核包含比较、唯一性限于实际像重命名。定理86.2恰对应 $\ker(q)=\ker(\sigma_\pi)$：原边界已足够时，画像没有增加状态类；不足时，画像指出必须区分的来源对。若目标根本不要求恢复当前 $q$，单独的响应行可能允许更粗摘要，不能沿用这里的最小性称号。

同一来源上的空间、时间、边界或记忆读数 $e_i:S\to E_i$，只有在各自满足 $\ker(e_i)=\ker(\sigma_\pi)$ 时，才都通过 $Q_\pi$ 在实际像上互为坐标。仅有 $\ker(e_i)\subseteq\ker(\sigma_\pi)$ 只保证单向恢复共同画像，读数可能还携带额外信息。这里恢复的是指定画像，既不恢复未记录的原始状态，也不从一步权重推出已发生路径或实际累计时钟。

### 命题 86.4（标签的再投影与画像关系的复合）

固定同一 $S,S',q,q',W$，取有限非空标签集 $Y_1,Y_2$ 及映射 $\pi_1:Z\to Y_1$、$r:Y_1\to Y_2$，令 $\pi_2=r\circ\pi_1$。定义画像上的标签合并映射

$$
\begin{aligned}
C_r:B\times K^{Y_1\times B'}&\longrightarrow B\times K^{Y_2\times B'},\\
C_r(b,a)&=(b,r_\ast a),\\
(r_\ast a)(y_2,b')&=\sum_{\substack{y_1\in Y_1\\r(y_1)=y_2}}a(y_1,b').
\end{aligned}
\tag{86.8}
$$

有限纤维分组给出

$$
A_{\pi_2}(s,y_2,b')
=\sum_{r(y_1)=y_2}A_{\pi_1}(s,y_1,b'),\qquad
\sigma_{\pi_2}=C_r\circ\sigma_{\pi_1},\qquad
\ker(\sigma_{\pi_1})\subseteq\ker(\sigma_{\pi_2}).
\tag{86.9}
$$

$C_r$ 限制为满射 $Q_{\pi_1}\to Q_{\pi_2}$。存在实际像上的解码器 $D:Q_{\pi_2}\to Q_{\pi_1}$，使 $D(\sigma_{\pi_2}(s))=\sigma_{\pi_1}(s)$ 对所有 $s$ 成立，当且仅当 $C_r|_{Q_{\pi_1}}$ 单射；也等价于(86.9)中的两个核相等。这一解码器存在时唯一且为该限制映射的逆。

证明。$\pi_2^{-1}(y_2)$ 是各 $\pi_1^{-1}(y_1)$ 在 $r(y_1)=y_2$ 上的不交并，得到(86.9)。若 $C_r$ 把两个实际画像合成同一点，任何 $D$ 都无法同时恢复两者；若限制映射单射，它已满射，故有唯一逆。再取 $r_2:Y_2\to Y_3$，重复分组得到 $C_{r_2\circ r}=C_{r_2}\circ C_r$，而恒等标签映射给恒等画像映射。证毕。

这给出了“观察关系之间的关系”的具体结构：继续投影只会合并画像类，复合由有限和承担；是否可逆看实际实现的画像集合，而非要求 $r$ 全局单射，也非要求整个函数空间上的 $C_r$ 单射。细标签合同满足(86.3)时，粗标签合同也满足它，且粗核由细核按 $r$ 求和得到；反向一般不成立。

### 反例 86.5（有序二叶的隐藏标记与声明记录）

取 $K=\mathbb Q_{\ge0}$，以及同一有限实际来源

$$
\begin{gathered}
S=\{u,v\},\qquad u=\langle\alpha,\beta\rangle,\quad
v=\langle\beta,\alpha\rangle,\qquad q(u)=q(v)=(1,1),\\
S'=\{r\},\qquad q'(r)=(1,0),\qquad Z=\{0,1\},\\
W(u,0,r)=1,\quad W(u,1,r)=0,\quad
W(v,0,r)=0,\quad W(v,1,r)=1.
\end{gathered}
\tag{86.10}
$$

这里 $r$ 是本例的后继状态符号，与命题86.4的标签合并函数无关。这个核由同一个确定性规则给出：$u$ 产生标签 $0$，$v$ 产生标签 $1$，两者都到达 $r$；每一来源行总质量都是 $1$。这是有序二叶项上的声明过程，不声称它就是 Fibonacci 替换本身。

令 $\pi_{\mathrm c}:Z\to\{\ast\}$ 为常值映射，则

$$
\begin{aligned}
A_{\pi_{\mathrm c}}(u,\ast,(1,0))
&=A_{\pi_{\mathrm c}}(v,\ast,(1,0))=1,\\
G_{\pi_{\mathrm c}}(H)(\ast,(1,0))&=H(u)+H(v).
\end{aligned}
\tag{86.11}
$$

所以只有一个来源边界值的精确核 $L_{\pi_{\mathrm c}}((1,1),\ast,(1,0))=1$ 对所有输入都成立。然而逐标签行分别是

$$
\bigl(A_{\operatorname{id}}(u,0,(1,0)),A_{\operatorname{id}}(u,1,(1,0))\bigr)=(1,0),\qquad
\bigl(A_{\operatorname{id}}(v,0,(1,0)),A_{\operatorname{id}}(v,1,(1,0))\bigr)=(0,1).
\tag{86.12}
$$

这直接使式(85.1)失败，却没有破坏完全收缩标签后的(86.11)。相反，逐标签合同下 $G_{\operatorname{id}}(H)$ 的两坐标就是 $(H(u),H(v))$；点输入 $\delta_u,\delta_v$ 具有相同 $P_qH$，却给不同联合响应，故不存在仅由原边界聚合得到的逐标签核。于是 $|Q_{\pi_{\mathrm c}}|=1$、$|Q_{\operatorname{id}}|=2$，从两个实际画像到一个画像的 $C_r$ 不单射。

若 $z$ 只是合同明确隐藏的内部标记，(86.11)已经完成本例的声明任务。若 $z$ 被声明为记录、时钟增量，或某个保留字段需要由它确定，则必须保留足以确定该字段的投影并重查(86.3)；本例对两个不同标签至少需要两个来源画像类。保留标签的权重律仍不等于观察者已取得本次标签；本例的确定性使来源画像决定标签，随机模型中的一般画像只决定分支权重。物理时长、取得过程和累计存储仍需各自的合同。

### 86.6 来源、后续切面与适用边界

本节是仓内结果的具体综合及第85节必要条件的修正，不主张新的通用商定理或经文献检索确认的原创结果。[Process Geometry 第29节、命题31.20及第52节](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)分别提供联合标签核、不可读标签先求和与细标签额外条件、生成解释像和共同商的背景；[Fibonacci 第245—249节](FIBONACCI_ATOMIC_RELATION_GENERATION.md)限定生成叶子、组成摘要、允许操作和行为类的区别；[Joint Clocks 第31—32节](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md)限定时钟载体、实际纯轨道与四表达互恢复。式(86.10)保留有序配对差别，不能据两个生成叶子推出所有任务只有两个行为类。

既有形式化锚仅作范围明确的引用：[EffectiveImageKernelCriterion.refinement_iff_kernel_inclusion_on_effective_images](../../../D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean)对应命题86.3的实际像因子化；[DynamicsDescent.dynamics_descends_iff](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean)处理满射摘要下的确定性自映射下降；[DynamicClosureMinimality.dynamic_closure_is_least](../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)要求候选细化对声明干预闭合；[ControlledBehaviorUniversality.controlled_behavior_universal_property](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean)要求有限实现、满射及更新和读出交换。这些引用不表示本节的半环加权实例、反例或全部解释已被 Lean 核验。

全部结论限于有限和、同源联合核、固定 $q,q'$ 与明确的 $\pi$。必要性使用任意细点输入；仅在一份固定初始分布或受限准备族上恰好正确，不能推出(86.3)。无限载体需要另给求和存在与分组合法性的条件。这里的 $\sigma_\pi$ 只为当前一步和指定目标切面最小；把目标摘要换成下一步所需的更细画像后，原条件可能失效。未来接续必须对每个声明动作及每个切面重新检查联合核、合法性、失败、记录、时钟及选择器的保持；需要完整未来行为时，还须相应的动态闭包条件。

恢复定理只谈实际像上的函数存在与唯一，不保证解码可计算、已取得、可在预算内实施，也不赋予任意拼接来源或旁支的权限。共同画像足以支持这一项声明任务，并不把一般空间、物理时间、边界与记忆无条件等同。本节只追加理论正文，未进行 Lean 编译或内核验证，也未进行消化结算。

## 86.99 追加锚

## 87. 递归三阶共同核心：关系、关系的关系与四种表示

本节取第86节同源联合核的有限确定性特例，把事件的关系及后继也纳入共同商。[Fibonacci §§247—249](FIBONACCI_ATOMIC_RELATION_GENERATION.md)提供生成层与行为边界的区分：二叶自由语法及有序配对给出生成方式；加入替换后的种子数、固定加性读出的维数和完整行为类数是不同问题。这里的“三阶”指状态、事件间关系及保存二者接续的共同结构，不指物理维数，也不由两个生成叶推出两个行为类。

### 定义 87.1（有类型的同源事件模型与总化响应）

取有限非空集合 $\Omega,S_0,D_0,I$，以 $S_0$ 表示状态的环境载体，$D_0$ 表示事件的环境载体，$I$ 表示接口类型。给定

$$
\operatorname{in},\operatorname{out}:D_0\to I,\qquad
 D_0=\bigsqcup_{i,j\in I}D^0_{i,j},\qquad
 D^0_{i,j}=\{d:\operatorname{in}(d)=i,\ \operatorname{out}(d)=j\}.
$$

实际来源由一个联合映射给出：

$$
j=(\iota_S,\iota_D):\Omega\to S_0\times D_0,\qquad
J=j[\Omega],\qquad S=\iota_S[\Omega],\quad D=\iota_D[\Omega].
\tag{87.1}
$$

其中 $\iota_S:\Omega\to S_0$、$\iota_D:\Omega\to D_0$，并在下文把实际像重新记为

$$
S:=\iota_S[\Omega]\subseteq S_0,\qquad
D:=\iota_D[\Omega]\subseteq D_0.
$$

所以这里的 $S,D$ 已经是同一来源的实际像；没有假设 $J=S\times D$。$D$ 是事件域，$d\in D$ 是当前事件，$e\in D$ 是待尝试事件；$d$ 本身不是接口，$\operatorname{out}(d)$ 才是其输出接口。

一个配置是 $x=(s,d)\in J$；$d$ 是当前事件，当前接口由 $\operatorname{out}(d)$ 给出，尝试事件记为 $e\in D$。另给第二阶关系

$$
\Delta\subseteq\{(d,e)\in D\times D:
\operatorname{out}(d)=\operatorname{in}(e)\}.
\tag{87.2}
$$

$(d,e)\in\Delta$ 表示声明允许的接口接续关系，不自动授予状态 $s$ 中的执行权限。$J$ 和 $\Delta$ 都不能用各自边缘的笛卡尔积替换。

$\Delta$ 是独立声明的第二阶关系合同；接口类型相容只是它的必要索引条件，不由类型函数自动推出全部关系边。

取有限标签集 $Y,M,P_{\mathrm{state}},H,F_{\mathrm{fail}},R_{\mathrm{deny}}$，令

$$
L=Y\times M\times P_{\mathrm{state}}\times H
$$

分别承载输出、记录、权限状态与声明的时钟增量标签；$F_{\mathrm{fail}}$ 承载执行失败原因，$R_{\mathrm{deny}}$ 承载来源、类型、关系或权限拒绝原因。设 $L$ 非空。声明确定性总响应

$$
\widehat T:S\times D\times D\longrightarrow
\mathsf{Ok}(L\times S\times D)
\sqcup\mathsf{Fail}(F_{\mathrm{fail}}\times L)
\sqcup\mathsf{Deny}(R_{\mathrm{deny}}\times L).
\tag{87.3}
$$

按固定优先级检查 $(s,d)\in J$、类型相容及 $(d,e)\in\Delta$；域、类型、关系或权限条件不满足时返回相应的 $\mathsf{Deny}$ 标签；通过这些检查后仍可能在执行阶段返回 $\mathsf{Fail}$。成功值 $\mathsf{Ok}(\ell,s',d')$ 同时给出状态后继与事件后继，不要求 $d'=e$。失败和拒绝保留其记录、权限和增量标签后终止；若任务允许错误后继续，须把它建模为到某个明确错误状态的成功转移，另行检查下降条件。

### 定义 87.2（固定索引的轨迹、状态画像与权限／接续画像）

所有尝试词取自 $D^*$，包括会被拒绝的词；不按代表元删去非法词。总化可见轨迹不直接暴露原始后继 $s',d'$，而以它们继续执行：

$$
\begin{aligned}
\widehat{\operatorname{Tr}}(s,d,\varepsilon)&=\varepsilon,\\
\widehat{\operatorname{Tr}}(s,d,ew)&=
\begin{cases}
(\mathsf{ok},\ell)\cdot\widehat{\operatorname{Tr}}(s',d',w),
 &\widehat T(s,d,e)=\mathsf{Ok}(\ell,s',d'),\\
[(\mathsf{fail},f,\ell)],&\widehat T(s,d,e)=\mathsf{Fail}(f,\ell),\\
[(\mathsf{deny},p,\ell)],&\widehat T(s,d,e)=\mathsf{Deny}(p,\ell).
\end{cases}
\end{aligned}
\tag{87.4}
$$

点号为序列连接，方括号表示单项序列。给定当前声明读出 $o:S\to O$，定义

$$
\begin{aligned}
\Gamma(s)&=\left(o(s),
 \bigl(\mathbf1_J(s,d),\widehat{\operatorname{Tr}}(s,d,w)\bigr)_{d\in D,\,w\in D^*}\right),\\
\Pi(d)&=\left(\operatorname{in}(d),\operatorname{out}(d),
 \bigl(\mathbf1_J(s,d),\widehat{\operatorname{Tr}}(s,d,w)\bigr)_{s\in S,\,w\in D^*},
 \bigl(\widehat{\operatorname{Tr}}(s,e,udv)\bigr)_{s\in S,\,e\in D,\,u,v\in D^*}\right),\\
s\sim_S t&\iff\Gamma(s)=\Gamma(t),\qquad
 d\sim_D e\iff\Pi(d)=\Pi(e).
\end{aligned}
\tag{87.5}
$$

$\Pi$ 同时检查事件作为当前接口及作为任意词中一次尝试的角色，包含权限、失败和全部声明续接的可见响应；所有画像使用共同的索引集。只比较出度、当前权限或成功输出都不是这个画像。有限载体上的画像可以含所有有限词坐标，但不因此宣称存在已实现的无限执行。若只保留长度不超过 $n$ 的坐标，应另记 $\Gamma_n,\Pi_n$；它们的核不自动对下一步闭合。

### 假设 87.3（关系饱和、后继相容与实际来源闭合）

记商映射为 $q_S:S\to S/{\sim_S}$、$q_D:D\to D/{\sim_D}$。在所选画像核上要求下列条件；同样的条件也可检查一个较粗的候选摘要。

1. 类型、实际域和第二阶关系在相应纤维上常值。即 $d\sim_D d'$ 时类型相同，且

   $$
   \begin{aligned}
   s\sim_S t,\ d\sim_D d'&\Longrightarrow
   ((s,d)\in J\iff(t,d')\in J),\\
   d\sim_D d',\ e\sim_D e'&\Longrightarrow
   ((d,e)\in\Delta\iff(d',e')\in\Delta).
   \end{aligned}
   \tag{87.6}
   $$

   第二行称为 $\Delta$ 饱和，等价于 $\Delta$ 是若干产品等价类的并。类型和 $J$ 的条件已由(87.5)保证，仍列出以明确较粗候选摘要的义务。

2. 在实际输入及其成功后继属于 $J$ 的范围内，定义 $\widehat q$ 为

   $$
   \begin{aligned}
   \widehat q(\mathsf{Ok}(\ell,s',d'))&=\mathsf{Ok}(\ell,\kappa(s',d')),\\
   \widehat q(\mathsf{Fail}(f,\ell))&=\mathsf{Fail}(f,\ell),\\
   \widehat q(\mathsf{Deny}(r,\ell))&=\mathsf{Deny}(r,\ell).
   \end{aligned}
   $$

   要求

   $$
   (s,d),(t,d')\in J,\quad s\sim_S t,\quad d\sim_D d',\quad e\sim_D e'
   \Longrightarrow
   \widehat q\bigl(\widehat T(s,d,e)\bigr)
   =\widehat q\bigl(\widehat T(t,d',e')\bigr).
   \tag{87.7}
   $$

   其中 $\kappa(s',d')$ 在成功分支上有定义，正是由(87.8)保证的。因而成功分支不仅标签相同，两个后继分量也分别等价。可见轨迹相同本身不替代这项分量条件。若还声明控制选择器 $h:J\to D$，须另有 $q_D\circ h$ 在 $(q_S,q_D)|_J$ 的纤维上常值；使用额外档案的选择器须把该档案加入同源配置。

3. 为每个尝试 $e$ 指定实际来源上的成功后继见证 $U_e\subseteq\Omega\times\Omega$，并要求

   $$
   \begin{gathered}
   \forall\omega\in\Omega,\ e\in D,\quad
   \widehat T(\iota_S(\omega),\iota_D(\omega),e)
        =\mathsf{Ok}(\ell,s',d')\\
   \Longrightarrow\quad
   \exists\omega'\in\Omega:\quad
   (\omega,\omega')\in U_e\ \land\ j(\omega')=(s',d').
   \end{gathered}
   \tag{87.8}
   $$

   这是逐个实际来源的接续提升条件，强于仅有 $s'\in S$、$d'\in D$，也强于独立找两个边缘见证。它保证成功后继在 $J$ 中，且有限执行可沿见证 $U_e$ 逐步实现；$U_e$ 本身不自动成为商核心中的权限关系。若递归升层需要保存来源级权限，必须另定义其商关系并检查代表无关性；失败或拒绝无需虚构成功后继。

### 命题 87.4（递归共同核心的一个充分构造）

在定义87.1—87.2及假设87.3下，令

$$
\begin{aligned}
S^\#&=S/{\sim_S},\qquad D^\#=D/{\sim_D},\\
\kappa&=(q_S,q_D)|_J:J\to Q=\kappa[J],\\
\overline\Delta(q_D(d),q_D(e))&\iff(d,e)\in\Delta.
\end{aligned}
\tag{87.9}
$$

则 $\overline\Delta$ 及下面的总响应代表无关，并唯一确定在这些实际像上：

$$
\begin{aligned}
\overline T &:Q\times D^\#\to
 \mathsf{Ok}(L\times Q)\sqcup\mathsf{Fail}(F_{\mathrm{fail}}\times L)
 \sqcup\mathsf{Deny}(R_{\mathrm{deny}}\times L),\\
\overline T(\kappa(s,d),q_D(e))&=\widehat q\bigl(\widehat T(s,d,e)\bigr).
\end{aligned}
\tag{87.10}
$$

其中成功输出的后继对确实在 $Q$。以(87.4)的同一递归式定义商轨迹，则对每个 $(s,d)\in J$ 和有限词 $w$，

$$
\widehat{\operatorname{Tr}}(s,d,w)
=\overline{\operatorname{Tr}}(\kappa(s,d),q_D^*(w)),
\tag{87.11}
$$

$q_D^*$ 表示逐字取商。故

$$
\mathcal C=(S^\#,D^\#,Q,\overline\Delta,\overline T)
\tag{87.12}
$$

是保存 $\Delta$ 与总响应商合同的三阶共同结构，$Q$ 是其配置核心；$U_e$ 仍只是实际来源上的成功提升见证，除非另行构造其商关系，否则不属于 $\mathcal C$ 的权限数据。

证明。(87.6)保证关系下降；(87.7)保证总响应及两个成功后继类与代表无关；(87.8)保证下一配置仍有同源联合见证。(87.11)对词长归纳：空词相同，成功步使用两个相同后继类继续，失败与拒绝步保留相同标签并停止。每个商输入都有实际代表，故上述交换式决定全部商值，唯一性只相对于固定的商映射及合同。证毕。

这是充分条件的组合，不主张整组条件对每种粗任务都必要。单独的 $\Delta$ 饱和恰保证原关系真值的精确下降。与第86节的连接也有范围：本节响应可写为确定性点质量核；换成加权分支后，应按所保留的标签及联合后继类聚合，再检验式(86.3)的行常值条件。聚合行相同不能推出每条细分支具有同一个确定性后继，也不能从两个后继边缘相同推出联合行相同。

### 命题 87.5（四种读数在实际像上的恢复条件）

在命题87.4的条件下，令同源读数

$$
E_i:J\to X_i,\qquad
 i\in\{\mathrm{sp},\partial,\mathrm{mem},\mathrm{time}\},\qquad
E_{\mathrm{time}}(s,d)=\theta(s)
\tag{87.13}
$$

分别表示空间、边界、记忆与状态侧时间读数。这里 $\theta:S\to X_{\mathrm{time}}$ 是声明的当前时间显示。对 $J$ 上的映射 $f$，记 $\ker(f)=\{(x,x'):f(x)=f(x')\}$。有

$$
\begin{aligned}
E_i=\bar E_i\circ\kappa\text{，某个 }\bar E_i:Q\to E_i[J]
 &\iff\ker(\kappa)\subseteq\ker(E_i),\\
\kappa=R_i\circ E_i\text{，某个 }R_i:E_i[J]\to Q
 &\iff\ker(E_i)\subseteq\ker(\kappa).
\end{aligned}
\tag{87.14}
$$

因此，若四个读数均满足

$$
\ker(E_i)=\ker(\kappa),
\tag{87.15}
$$

则它们既通过配置核心因子化，又各自完整恢复这个核心；$\bar E_i$ 是实际像间的双射，唯一互恢复映射为

$$
R_{ij}=\bar E_j\circ(\bar E_i)^{-1}:E_i[J]\to E_j[J].
\tag{87.16}
$$

证明。(87.14)分别以 $\bar E_i(\kappa(x)):=E_i(x)$ 和 $R_i(E_i(x)):=\kappa(x)$ 定义，核包含恰保证代表无关；实际像保证唯一性与满射。两核相等时二者互逆，从而得到(87.16)。证毕。

条件(87.15)对“恰好编码指定核心”充要，对“四种读数彼此可恢复”只是充分：四者也可能共同遗失核心信息或共同保留更多信息。保存动态结构还须保留 $D^\#$ 中的尝试标签，并使各表示中的执行器与(87.10)交换；仅有静态双射不能认证任意外加执行器。若执行器由 $\overline T$ 经这些双射运输定义，交换性随定义成立。

尤其，若同一 $s$ 可与两个不同的 $D^\#$ 类联合出现，则仅依赖 $s$ 的 $E_{\mathrm{time}}$ 无法满足(87.15)。若合同只要求状态核心，可将(87.14)中的 $J,\kappa$ 换成 $S,q_S$，但这不再恢复独立的事件侧信息。全部恢复只针对实际像，不恢复已被商掉的原始来源。

累计时钟是另一份合同：还须指定初值 $t_0$、增量解释 $c:H\to A$（$A$ 为加法幺半群）、实际已执行的标签序列 $\ell_1,\ldots,\ell_n$ 及其取得和保存方式，才能沿该实际历史定义

$$
\operatorname{Clock}(\ell_1\cdots\ell_n)
=t_0+c(\operatorname{pr}_H\ell_1)+\cdots+c(\operatorname{pr}_H\ell_n).
\tag{87.17}
$$

即使当前状态核心足以预测下一响应，也不自动存储初值、过去执行词或累计值。对额外历史载体上的时钟恢复，应另查其读数核是否包含于 $\ker(\operatorname{Clock})$；不能以状态侧的(87.15)代替。

### 命题 87.6（未饱和候选商的有限反例）

取

$$
S=\{\ast\},\quad D=\{a,b,c\},\quad
\Delta=\{(a,c)\},\quad
q_D^0(a)=q_D^0(b)=A_0,\quad q_D^0(c)=C_0.
\tag{87.18}
$$

所有接口取同一类型，取 $\Omega=D$、$j(d)=(\ast,d)$，所以 $J=S\times D$。固定标签 $\ell_0$，令

$$
\widehat T(\ast,d,e)=
\begin{cases}
\mathsf{Ok}(\ell_0,\ast,c),&(d,e)=(a,c),\\
\mathsf{Deny}(\mathrm{notRelated},\ell_0),&\text{其余情形}.
\end{cases}
\tag{87.19}
$$

取 $U_c=\{(a,c)\}$，其余 $U_e=\varnothing$，则成功分支满足实际来源闭合。然而原关系和带失败值的后继

$$
N(d,e)=
\begin{cases}
c,&(d,e)\in\Delta,\\
\bot,&(d,e)\notin\Delta
\end{cases}
\quad:\ D\times D\to D\sqcup\{\bot\}
\tag{87.20}
$$

均不能精确下降到候选商 $D/{\ker(q_D^0)}$。

证明。商输入 $(A_0,C_0)$ 同时代表 $(a,c)$ 和 $(b,c)$，但前者属于 $\Delta$、后者不属于；相应后继分别为 $c$ 和 $\bot$，总响应分别成功和拒绝。代表无关性因此失败。这里单独的状态后继是常值 $\ast$，失效的是保留合法性及成功／拒绝的关系后继，不能用常值状态分量掩盖。证毕。

反例中的 $q_D^0$ 是遗漏关系信息的候选摘要，不是(87.5)的完整 $\Pi$：后者已由尝试 $c$ 区分 $a,b$。若明确隐藏关系与拒绝标签，须重新声明粗任务；其响应可能可聚合，但不能称原 $\Delta$ 或(87.20)已经下降。

### 87.7 递归使用的范围

共同结构可作为下一层的输入对象；每次升层仍须指定类型、实际联合像、总化响应与测试词，并重新检查(87.6)—(87.8)。这使封装后的关系可以继续被比较和接续，不能把未实现的商坐标组合补成实际来源。有限视界的充分性不自动延伸到所有未来，所有有限词的相等也不自动提供无限实际线程、取得算法或资源界。

空间、边界、记忆与状态时间在此只是同一来源上的声明读数；它们与共同核心的关系由(87.14)—(87.16)限定。该构造不赋予这些读数拓扑、度量、物理时空或新的操作权限，累计时钟仍遵守独立的历史合同。

## 87.99 追加锚

## 88. 实际域上的状态—事件同步细化与指定共同核

第87节的下降定理以分量相容为条件，本节在其有限确定性模型中构造满足条件的最大等价关系对。关键是同步检查状态、当前事件和待尝试事件三个位置，并把下一轮所需的两个后继分量一同保留。所得最小性只比较遵守同一合同的独立分量编码；它不把任意联合记忆、取得成本或物理实现纳入同一个极值问题。

### 定义 88.1（固定实际来源与分量种子）

沿用定义87.1的有限实际像 $S,D,J=j[\Omega]\subseteq S\times D$、接口类型、有类型的接续关系 $\Delta$、完整标签集 $L$ 与总响应 $\widehat T$。始终假设原有来源见证 $U_e\subseteq\Omega\times\Omega$ 满足式(87.8)。于是每个实际配置的成功后继仍在 $J$；细化只能区分已有对象，不能补出缺失的来源见证。若(87.8)未满足，下面的签名仍可比较，但实际来源闭合、共同核上的成功更新及来源提升结论不随之成立。

以原始读出和类型为种子，令

$$
a_0(s)=o(s),\qquad b_0(d)=(\operatorname{in}(d),\operatorname{out}(d)),\qquad
R_0=\ker a_0,\quad E_0=\ker b_0.
\tag{88.1}
$$

可选地声明一个内部选择器 $h:J\to D$；是否包含它在细化开始前固定。未声明 $h$ 时，以下所有选择器坐标和义务均省去，不能据此得到任意外加选择器的下降。

### 定义 88.2（掩蔽响应与同步签名）

设第 $n$ 轮签名为 $a_n:S\to A_n$、$b_n:D\to B_n$。在一个不交和中使用唯一的 $\mathsf{Outside}$ 标记，定义

$$
V_n(s,d,e)=
\begin{cases}
\mathsf{Outside},&(s,d)\notin J,\\
\mathsf{Ok}(\ell,a_n(s'),b_n(d')),
 &(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Ok}(\ell,s',d'),\\
\mathsf{Fail}(f,\ell),
 &(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Fail}(f,\ell),\\
\mathsf{Deny}(r,\ell),
 &(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Deny}(r,\ell).
\end{cases}
\tag{88.2}
$$

这里 $\ell$ 保留输出、记录、权限状态、时钟增量的全部声明字段；失败与拒绝的原因也逐字保留。域外只有一个标记，原总响应在 $J$ 外采用的拒绝原因或标签约定不属于本节的实际域合同。域内即使类型、关系或权限检查失败，也保留完整拒绝值，不把它改成 $\mathsf{Outside}$。

若声明了 $h$，令 $H_n(s,d)=b_n(h(s,d))$ 当 $(s,d)\in J$，否则为 $\mathsf{Outside}$；其值域取 $B_n\sqcup\{\mathsf{Outside}\}$，域内值使用该不交和的注入。同步定义

$$
\begin{aligned}
a_{n+1}(s)=&\bigl(a_n(s),\ (\mathbf1_J(s,d))_{d\in D},\\
 &\quad(V_n(s,d,e))_{(d,e)\in D^2},\ (H_n(s,d))_{d\in D}\bigr),\\
b_{n+1}(d)=&\bigl(b_n(d),\ (\mathbf1_J(s,d))_{s\in S},\\
 &\quad(\mathbf1_\Delta(d,e),\mathbf1_\Delta(e,d))_{e\in D},\\
 &\quad(V_n(s,d,e))_{(s,e)\in S\times D},\\
 &\quad(V_n(s,e,d))_{(s,e)\in S\times D},\ (H_n(s,d))_{s\in S}\bigr),\\
R_n&=\ker a_n,\qquad E_n=\ker b_n.
\end{aligned}
\tag{88.3}
$$

式中 $H_n$ 坐标仅在声明选择器时出现。所有坐标由同一固定集合中的实际元素索引，不选择等价类代表来改变测试集。两种新签名都只读取旧轮 $a_n,b_n$，且保留自己的整个旧签名。嵌套值域 $A_n,B_n$ 随轮次改变；停止条件是两个核同时不再改变，不是嵌套元组的字面相等，也不是只检查一侧的分区。

### 定义 88.3（可接受的分量等价关系对）

按关系包含逐分量比较等价关系对。称 $(R,E)$ 可接受，若 $R\subseteq R_0$、$E\subseteq E_0$，且满足以下同一实际域合同。

1. $J$ 对 $R\times E$ 饱和，$\Delta$ 对 $E\times E$ 饱和：

   $$
   \begin{aligned}
   sRt,\ dEd'&\Longrightarrow
      (\mathbf1_J(s,d)=\mathbf1_J(t,d')),\\
   dEd',\ eEe'&\Longrightarrow
      (\mathbf1_\Delta(d,e)=\mathbf1_\Delta(d',e')).
   \end{aligned}
   \tag{88.4}
   $$

2. 对所有 $(s,d),(t,d')\in J$ 及 $e,e'\in D$，若 $sRt,dEd',eEe'$，则两个总响应的分支相同、完整标签相同；在 $\mathsf{Fail}$ 或 $\mathsf{Deny}$ 分支原因相同；在成功分支

   $$
   \widehat T(s,d,e)=\mathsf{Ok}(\ell,u,v),\quad
   \widehat T(t,d',e')=\mathsf{Ok}(\ell,u',v')
   \ \Longrightarrow\ uRu',\ vEv'.
   \tag{88.5}
   $$

3. 若声明了 $h$，还要求 $sRt,dEd'$ 且 $(s,d),(t,d')\in J$ 时，$h(s,d)\,E\,h(t,d')$。

这里第2项要求匹配整个带标记响应，式(88.5)只展开其成功后继部分。种子包含保证原始读出和事件类型保持；来源条件(87.8)是固定模型的前提，不是可以靠挑选 $R,E$ 代替的义务。对角关系对总是可接受。

### 定理 88.4（同步稳定、最大分量合同与轮数界）

序列(88.3)满足 $R_{n+1}\subseteq R_n$、$E_{n+1}\subseteq E_n$。存在首个同时稳定的指标

$$
N=\min\{n:(R_{n+1},E_{n+1})=(R_n,E_n)\},\qquad
N\le |S|+|D|-|S/R_0|-|D/E_0|.
\tag{88.6}
$$

记稳定对为 $(R_\infty,E_\infty)=(R_N,E_N)$。它是种子以下最大的可接受等价关系对：每个可接受 $(R,E)$ 都满足 $R\subseteq R_\infty$、$E\subseteq E_\infty$，且所有后续轮保持此对。

证明。保留旧签名立即给出两个包含。先核对本算子的序方向：对任意等价关系对 $(R,E)$，以商映射 $q_R,q_E$ 充当旧签名，按(88.2)—(88.3)取新核，记为 $\Phi(R,E)$。新核只取决于旧核，不依赖其标签命名。若 $R\subseteq\widetilde R$、$E\subseteq\widetilde E$，则旧值相等蕴含较粗旧值相等；相同成功后继类在较粗商中仍相同，其他分支、原因、标签、域及关系真值保持不变，选择器同理。因此

$$
\Phi(R,E)\subseteq\Phi(\widetilde R,\widetilde E),\qquad
\Phi(R,E)\subseteq(R,E).
\tag{88.7}
$$

这是本节算子的直接单调性证明，不使用第31节关系侧的反单调断言。由核决定下一核也说明，一旦两侧同时固定，之后永久固定。

现取任意可接受对。归纳证明它在每轮核之下。初始即种子条件。设 $R\subseteq R_n,E\subseteq E_n$。对 $sRt$，固定实际 $d,e$ 比较状态签名：域真值相同；域外均为唯一标记，域内由第2项获得相同分支、原因和标签，成功后继的 $R,E$ 关系再由归纳假设给出相同 $a_n,b_n$ 值。选择器亦由第3项给出相同 $b_n$ 值。连同旧签名可得 $sR_{n+1}t$。对 $dEd'$，固定 $s,e$，分别把 $d,d'$ 放在当前事件和待尝试事件位置；同样的响应论证、$J$ 饱和、$\Delta$ 两个方向的饱和以及选择器条件，给出 $dE_{n+1}d'$。于是任何可接受对都在所有迭代之下。

反过来，设第 $n$ 轮两核同时稳定。$R_n$ 相关的状态在 $a_{n+1}$ 中有相同域行，$E_n$ 相关的事件在 $b_{n+1}$ 中有相同域列；依次替换 $s,d$ 得到 $J$ 的产品饱和。$b_{n+1}$ 同时保留 $\Delta$ 的行和列，依次替换其两位置得到 $\Delta$ 饱和。对实际输入及 $sR_nt,dE_nd',eE_ne'$，依次比较

$$
(s,d,e)\longrightarrow(t,d,e)\longrightarrow(t,d',e)
\longrightarrow(t,d',e').
\tag{88.8}
$$

$J$ 饱和保证中间配置仍实际存在。第一步用 $a_{n+1}$ 的响应行，第二步用 $b_{n+1}$ 的当前事件坐标，第三步用其待尝试事件坐标；得到三个位置替换前后的 $V_n$ 相等。由标记的不交性，分支、原因和完整标签一致；成功时两个后继分别有相同 $a_n,b_n$ 值，正是(88.5)。选择器按状态、当前事件两步替换证明。故稳定对可接受，与前述归纳合起来给出最大性。

最后令 $c_n=|S/R_n|+|D/E_n|$。它非减，每个未同时稳定的轮次至少严格增加 $1$，且 $c_n\le |S|+|D|$。所以最迟在(88.6)给出的指标处出现同时稳定；在此前恰有 $N$ 次严格增长，从而 $c_0+N\le c_N\le |S|+|D|$。证毕。

这个界计算达到稳定核以前的严格细化轮数；确认第 $N$ 轮稳定仍需与第 $N+1$ 轮比较。它不是运行时间或取得成本界。有效执行还需要可枚举的有限载体、可求值的 $o,J,\Delta,\widehat T$ 表和可选 $h$，以及签名所用值的可判定相等关系；集合论上的有限性本身不提供这些算法。

### 定理 88.5（共同核、实际像上的最小性与有限提升）

令

$$
\begin{aligned}
S^\#&=S/R_\infty,\qquad D^\#=D/E_\infty,\\
q_S&:S\to S^\#,\qquad q_D:D\to D^\#,\\
\kappa&=(q_S,q_D)|_J,\qquad Q=\kappa[J].
\end{aligned}
\tag{88.9}
$$

则 $J=(q_S,q_D)^{-1}[Q]$，且 $\overline\Delta(q_D(d),q_D(e))\iff(d,e)\in\Delta$ 代表无关；原始读出、类型、完整响应与已声明的选择器也都下降到这些实际商，成功后继在 $Q$ 中。具体地，令 $\mathcal R(X)=\mathsf{Ok}(L\times X)\sqcup\mathsf{Fail}(F_{\mathrm{fail}}\times L)\sqcup\mathsf{Deny}(R_{\mathrm{deny}}\times L)$。对映射 $g:X\to Z$，$\mathcal R(g)$ 只把成功后继 $x$ 换成 $g(x)$，保留其余全部字段。把实际域上的响应记为 $T_J:J\times D\to\mathcal R(J)$，有唯一

$$
\overline T:Q\times D^\#\to\mathcal R(Q),\qquad
\overline T(\kappa(x),q_D(e))=\mathcal R(\kappa)(T_J(x,e)).
\tag{88.10}
$$

任取独立编码 $\alpha:S\to A$、$\beta:D\to B$，若其核对可接受，则存在唯一的满射

$$
\begin{aligned}
p_S &: \alpha[S]\to S^\#,& p_S(\alpha(s))&=q_S(s),\\
p_D &: \beta[D]\to D^\#,& p_D(\beta(d))&=q_D(d),\\
p_J &: (\alpha,\beta)[J]\to Q,&
p_J(\alpha(s),\beta(d))&=\kappa(s,d).
\end{aligned}
\tag{88.11}
$$

因此本共同核在这类保合同的分量编码之间最粗。配置因子 $p_J$ 是 $(p_S,p_D)$ 在联合实际像上的限制，不把未实现的编码对补成配置。

证明。定理88.4逐项提供假设87.3的分量条件，原有 $U_e$ 提供其来源条件，所以命题87.4的关系下降及响应下降论证适用。此处使用该条件定理的证明，不预设本节核等于定义87.2的 $\Gamma,\Pi$ 核；两者对域外总化值和成功后继分量采用不同合同，等同需要另证。最大性给出 $\ker\alpha\subseteq R_\infty$、$\ker\beta\subseteq E_\infty$，故(88.11)代表无关；实际像使这些映射满射且唯一。

对每个 $x\in J,w\in D^*$，命题87.4的词长归纳还给出

$$
\widehat{\operatorname{Tr}}(x,w)
=\overline{\operatorname{Tr}}(\kappa(x),q_D^*(w)).
\tag{88.12}
$$

更具体地，给定有限商尝试词，为各字母选实际代表 $e_1,\ldots,e_m$，并取任意满足指定初始核心的 $\omega_0\in\Omega$。每个成功步由(87.8)选出 $\omega_{i+1}$，满足 $(\omega_i,\omega_{i+1})\in U_{e_{i+1}}$ 且 $j(\omega_{i+1})$ 为该实际成功后继。响应相容保证其商响应正是指定商步；失败或拒绝保留标签后停止。这给出每条有限商执行的逐步实际提升，不把所有有限提升合称为已取得的无限线程。证毕。

这种最小性既不是任意 $m:J\to M$ 的联合记忆最小性，也不是存储、计算或物理代价的最优性。生成语法有两个叶子，不能据此限制 $|S^\#|,|D^\#|$ 或 $|Q|$。

### 定理 88.6（同一继承合同下再次取商的幂等性）

在 $S^\#,D^\#$ 上重新运行同一构造时，初始观察与类型必须继承原始 $o,\operatorname{in},\operatorname{out}$：例如 $\bar o(q_S(s))=o(s)$；实际域为 $Q$，关系为 $\overline\Delta$，响应为 $\overline T$，选择器为已声明时的 $\bar h(\kappa(x))=q_D(h(x))$。域外仍统一屏蔽，不加入原总响应的域外差别。保留完整标签及所有这些运输后的合同数据，则再次稳定后的两个等价关系均为对角关系，故最终共同核只差唯一的实际像重命名。

证明。取继承模型中任意可接受对 $(\rho,\eta)$，拉回到原载体：

$$
sR^+t\iff q_S(s)\,\rho\,q_S(t),\qquad
dE^+e\iff q_D(d)\,\eta\,q_D(e).
\tag{88.13}
$$

继承的原始观察和类型使 $R^+\subseteq R_0,E^+\subseteq E_0$。关系饱和与式(88.10)把商上的分支、标签、原因、后继及选择器条件拉回，故 $(R^+,E^+)$ 是原模型的可接受对。其必然包含 $(R_\infty,E_\infty)$，而原最大性给出反向包含。因此两者相等；$q_S,q_D$ 满射，迫使 $\rho,\eta$ 都是对角关系。对角对自身可接受，故它就是继承模型的最大可接受对。

来源仍可取原来的 $\Omega$ 和 $j^\#=\kappa\circ j$；商尝试类 $c$ 的成功见证可取 $U_c^\#=\bigcup_{q_D(e)=c}U_e$。任取该类的实际代表并用(87.8)，即可验证继承模型的来源闭合。这只是原来源关系的按尝试类汇集，并未把 $U_e$ 宣称为 $Q$ 上的权限关系。证毕。

幂等性说的是闭合后的核心，不要求第二次运行从原始观察种子出发就零轮稳定。新增测试、改变关系、增补标签或加入选择器都会改变合同，需要重新闭合；不能借本结论跨合同认定核不变。

### 定理 88.7（四种读数的精确编码与完整响应共轭）

取同一实际域上的读数 $r_i:J\to X_i$，$i\in\{\mathrm{sp},\partial,\mathrm{mem},\mathrm{time}\}$，并记 $X_i^{\mathrm{act}}=r_i[J]$。每个读数恰好编码本节指定核心，当且仅当

$$
\ker r_i=\ker\kappa\quad\text{在 }J\text{ 上}.
\tag{88.14}
$$

此时存在唯一双射 $\phi_i:Q\to X_i^{\mathrm{act}}$ 使 $r_i=\phi_i\circ\kappa$，互恢复映射及其复合满足

$$
\theta_{ij}=\phi_j\circ\phi_i^{-1},\qquad
\theta_{ii}=\operatorname{id},\qquad
\theta_{jk}\circ\theta_{ij}=\theta_{ik}.
\tag{88.15}
$$

保持同一个尝试事件商 $D^\#$，定义运输执行器

$$
\begin{aligned}
T_i(z,c)&=\mathcal R(\phi_i)
       \bigl(\overline T(\phi_i^{-1}(z),c)\bigr),\\
T_j(\theta_{ij}(z),c)&=\mathcal R(\theta_{ij})(T_i(z,c)).
\end{aligned}
\tag{88.16}
$$

第二式是完整带标记响应的共轭：成功后继、失败原因、拒绝原因和全部标签同时运输，尝试类 $c$ 不变。若另行声明执行器 $F_i:X_i^{\mathrm{act}}\times D^\#\to\mathcal R(X_i^{\mathrm{act}})$，其动态正确性还须满足一步交换式

$$
F_i(r_i(x),q_D(e))=\mathcal R(r_i)(T_J(x,e))
\quad(x\in J,e\in D).
\tag{88.17}
$$

证明。实际像上的因子化判据分别用于 $r_i$ 与 $\kappa$：两方向的核包含给出互逆因子，得到(88.14)—(88.15)。运输规则保留标签，并满足 $\mathcal R(g\circ f)=\mathcal R(g)\circ\mathcal R(f)$，代入即得(88.16)。由于 $\kappa$ 与 $q_D$ 满射，式(88.17)恰迫使 $F_i=T_i$；只知道静态双射不能保证这一步。有限轨迹的交换随后按成功递推、失败或拒绝停止归纳。若有选择器，在表示 $i$ 中运输为 $\bar h\circ\phi_i^{-1}$，仍输出同一个 $D^\#$。证毕。

这说明空间、边界、记忆和时间只有在核条件及执行合同成立时才是此核心的不同坐标。彼此可恢复仍可共同丢失 $Q$，并不蕴含(88.14)。若时间读数只有 $r_{\mathrm{time}}(s,d)=\vartheta(s)$，而 $(s,d),(s,e)\in J$ 且 $q_D(d)\ne q_D(e)$，则两时间值相等但两核心值不同，故它不能恢复 $Q$。当前时间显示也不是累计历史；式(87.17)仍需初值、增量解释、实际执行标签序列及其保存合同。

### 命题 88.8（跨分量传播达到轮数界）

取 $S=\{0,1,2\}$、$D=\{0,1\}$、$J=S\times D$、$\Delta=D\times D$，接口只有一个类型，不声明选择器。令 $a_0=(0,0,1)$、$b_0=(0,0)$，固定完整标签 $\ell_0$，并设

$$
\widehat T(s,d,e)=\mathsf{Ok}(\ell_0,f(s,d,e),0),\qquad
f(s,d,e)=\begin{cases}e,&s=0,\\2,&s=1,2.\end{cases}
\tag{88.18}
$$

取 $\Omega=J$、$j=\operatorname{id}$，$U_e$ 为 $(s,d)\mapsto(f(s,d,e),0)$ 的确定性图。其后继均在 $J$，每个实际来源都满足(87.8)。以按首次出现次序编号的数字串表示核分区，则同步迭代为

$$
(001,00)\longrightarrow(012,00)\longrightarrow(012,01)
\longrightarrow(012,01).
\tag{88.19}
$$

证明。第一轮，状态 $0$ 的两个尝试后继在 $a_0$ 下均读作 $0$，状态 $1,2$ 的后继均读作 $1$；因此 $0,1$ 分开，$1,2$ 又由保留的原观察分开，状态核成为对角。当前事件不影响响应；作为尝试事件的 $0,1$ 在旧轮中分别使状态 $0$ 到达状态 $0,1$，而二者旧读出相同，故事件核这一轮仍为 $00$。第二轮使用已经分开的 $a_1(0),a_1(1)$，待尝试事件坐标遂区分两个事件；两侧至此都是对角，下一轮不再分裂。于是首个同时稳定指标 $N=2$，恰好达到 $3+2-2-1=2$ 的界。若第一轮只看未改变的事件核就停止，会漏掉第二轮必须保留的尝试区别。证毕。

此例的 $Q$ 有六个实际配置。四个取值于各自单点集的常值读数虽可彼此唯一恢复，却都不能恢复这六点核心；其共同遗失的信息不会因四种命名而重新出现。例子区分的是成功后继分量合同，全部外显成功标签在此甚至相同。

### 88.9 数学来源与形式化边界

本节是第87节有限分量合同的仓内综合推导，未作经外部文献核对的原创性主张。固定动作集的背景来自 [ControlledSignatureStabilization.controlled_signature_algorithm_correctness](../../../D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization.lean)：其参数为 $\mathrm{update}:U\to Y\to Y$、$\mathrm{readout}:Y\to O$，要求 $Y$ 为有限可枚举类型、$U,O$ 有限、三者非空且读出满射；结论连接递归签名、有限词观察与永久稳定。它不同时细化动作 $U$ 的等价类，也未包含本节的实际域掩蔽。

[ControlledFiniteStability.controlled_finite_stability](../../../D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.lean)在 $Y,U,O$ 均有限可枚举且非空、读出满射的条件下，给出固定动作更新的最大共同不变等价关系及 $|Y/\!\sim_\infty|-|O|\le |Y|-|O|$ 所控制的稳定深度。这里的有限类数计数沿用这一论证结构，但式(88.6)计数两个分量，三位置替换与同时稳定仍由本节证明承担，不能直接替换一个类型参数便视为已有结论。

[DynamicClosureMinimality.dynamic_closure_is_least](../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)对任意类型上的概念及固定干预族，要求候选概念细化原概念且其纤维受所有干预保持，才得动态闭包经候选因子化；它支持“最小性相对于闭合候选”的边界，不给任意联合记忆赋予本节分量最小性。[EffectiveImageKernelCriterion.refinement_iff_kernel_inclusion_on_effective_images](../../../D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean)对同一来源上的两个任意读数，以细读数核包含于粗读数核刻画实际像之间唯一因子，正是式(88.11)、(88.14)的因子化依据，无有限性或环境陪域满射的附加要求。

这些引用限定数学依赖的范围；本节的双分量掩蔽构造、商上幂等性和具体例子没有新增 Lean 编译或内核验证。加权响应、无限载体、来源级权限关系的商化，以及物理时空解释，均不由上述确定性有限合同推出。

## 88.99 追加锚

## 89. 分量核心的标量测试语义与当前核心的持续取得障碍

本节给第88节的指定分量核心一份精简的标量测试语义，并与保持配置完整、只沿具名尝试运行的未来行为比较。二者的任务合同不同：前者允许在数学测试中逐槽固定其他实际边缘元素；后者只延续当前实际配置。测试值可因子化、实际操作能取得测试值及表示具有闭合更新，是三个分别需要条件的结论。

### 定义 89.1（同一模型与两种载体的测试）

严格沿用定义87.1、定义88.1的有限非空实际边缘 $S,D$、同源实际像 $J=j[\Omega]\subseteq S\times D$、类型 $\operatorname{type}(d)=(\operatorname{in}(d),\operatorname{out}(d))$、接续关系 $\Delta$、完整标签 $L=Y\times M\times P_{\mathrm{state}}\times H$、失败原因 $F_{\mathrm{fail}}$、拒绝原因 $R_{\mathrm{deny}}$、总响应 $\widehat T$ 及原始读出 $o:S\to O$。原来源上的每个 $U_e$ 均满足(87.8)，特别是实际成功后继仍在 $J$。可选选择器 $h:J\to D$ 是否属于合同，须在构造前固定；未声明时省去以下所有 $h$ 测试和义务。

这里“有类型单孔”的类型只指 $S,D$ 两种载体排序。它不按权限、$\Delta$ 或接口类型相容性筛选代入：尝试槽遍历全部具名 $e\in D$，包括返回 $\mathsf{Deny}$ 的尝试。非孔槽固定为相应实际边缘中的任意元素；固定后的配置若不在 $J$，用掩蔽值记录，不把它补为实际配置。

标量测试指只有一个输入槽的映射，每个测试各有自己的结果载体：$p:S\to A_p$ 或 $q:D\to B_q$；不要求所有测试共用数值域，也不要求其环境陪域有限。其实际像因输入载体有限而有限。对一族测试定义共同核

$$
\ker\mathcal P=\{(x,x'):\ \forall p\in\mathcal P,\ p(x)=p(x')\}.
\tag{89.1}
$$

各结果载体中的下列分支均使用不交标记；即使某个旧测试值本身是带标记对象，也作为新标记内部的值保留。

### 定义 89.2（掩蔽标量响应与有限秩语法）

以 $\mathcal P_S^0=\{o\}$、$\mathcal P_D^0=\{\operatorname{type}\}$ 为种子。对 $p:S\to A_p$ 与 $q:D\to B_q$ 定义

$$
C_S[p](s,d,e)=
\begin{cases}
\mathsf{Outside},&(s,d)\notin J,\\
\mathsf{Ok}(\ell,p(u)),&(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Ok}(\ell,u,v),\\
\mathsf{Fail}(f,\ell),&(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Fail}(f,\ell),\\
\mathsf{Deny}(r,\ell),&(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Deny}(r,\ell),
\end{cases}
\tag{89.2}
$$

$$
C_D[q](s,d,e)=
\begin{cases}
\mathsf{Outside},&(s,d)\notin J,\\
\mathsf{Ok}(\ell,q(v)),&(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Ok}(\ell,u,v),\\
\mathsf{Fail}(f,\ell),&(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Fail}(f,\ell),\\
\mathsf{Deny}(r,\ell),&(s,d)\in J,\ \widehat T(s,d,e)=\mathsf{Deny}(r,\ell).
\end{cases}
\tag{89.3}
$$

$\ell$ 的全部四类字段、$f$ 与 $r$ 均原样保留；域内拒绝与 $\mathsf{Outside}$ 不同。令 $\mathcal C_n$ 为全部 $C_S[p]$（$p\in\mathcal P_S^n$）和 $C_D[q]$（$q\in\mathcal P_D^n$）组成的有限索引族，按以下规则同时生成下一秩：

$$
\begin{aligned}
\mathcal P_S^{n+1}={}&\mathcal P_S^n
 \cup\{s\mapsto C(s,d,e): C\in\mathcal C_n,\ d,e\in D\},\\
\mathcal P_D^{n+1}={}&\mathcal P_D^n
 \cup\{d\mapsto C(s,d,e),\ d\mapsto C(s,e,d):
                  C\in\mathcal C_n,\ s\in S,\ e\in D\}\\
 &\cup\{d\mapsto\mathbf1_\Delta(d,e),\ d\mapsto\mathbf1_\Delta(e,d):e\in D\}.
\end{aligned}
\tag{89.4}
$$

若声明了 $h$，还对每个旧测试 $q\in\mathcal P_D^n$ 定义

$$
H[q](s,d)=
\begin{cases}
\mathsf{Outside},&(s,d)\notin J,\\
\mathsf{In}(q(h(s,d))),&(s,d)\in J,
\end{cases}
\tag{89.5}
$$

并在(89.4)两行分别加入全部 $s\mapsto H[q](s,d)$（$d\in D$）及 $d\mapsto H[q](s,d)$（$s\in S$）。所有新测试只用上一秩测试，旧测试全部保留；因此每秩为有限族，重复测试无需强行去重。有限秩测试指这两条递归中任一有限阶段产生的测试。

无需另加显式 $J$ 测试：$D$ 非空、种子族非空且一直保留，故任选固定尝试后，掩蔽响应是否为 $\mathsf{Outside}$ 就给出域真值。此语法不添加原始身份测试，也不调用旧签名的整体读数 oracle；指定种子本身是否分离原始元素由 $o,\operatorname{type}$ 决定。它不赋予复制、重置、重新准备或分量重组的执行原语。这里给出的是约去冗余域坐标后的统一充分模式，不声称每个具体模型都需要其中每一项原语。

### 定理 89.3（标量共同核恰为同步核）

对每个 $n\ge0$，测试族与式(88.3)使用相同种子、相同实际模型及相同选择器约定时，同时有

$$
\ker\mathcal P_S^n=R_n,\qquad
\ker\mathcal P_D^n=E_n.
\tag{89.6}
$$

因此取定理88.4的首个同时稳定指标 $N$，秩 $N$ 的两个有限测试族已分别刻画所有有限秩测试的共同核，且 $N$ 满足原界(88.6)。每个有限秩测试都通过对应的秩 $N$ 测试值元组的实际像因子化。

证明。对 $n$ 同时归纳。零秩正是两种种子核。假设结论在 $n$ 成立。比较任意两组三槽输入时，全部 $\mathcal C_n$ 值相等，恰好等于 $V_n$ 值相等：$\mathsf{Outside}$ 与域内分支不交；域内所有测试均保完整响应头，即分支、$\ell$ 及适用的原因。成功时，全部状态旧测试相等恰恢复 $a_n(u)=a_n(u')$，全部事件旧测试相等恰恢复 $b_n(v)=b_n(v')$，这正是 $V_n$ 的两个旧后继签名相等。反向由同一个 $V_n$ 值立即得到每个标量响应相等。种子族非空使响应头和域外标记始终被检测，即使某侧旧测试全是常值也如此。

固定非孔槽后，(89.4)的状态测试遂恰恢复 $a_{n+1}$ 中所有 $V_n$ 坐标；保留旧测试恰恢复旧状态签名。固定任一 $e\in D$，$C_S[o](s,d,e)$ 的外部标记还恢复每个 $\mathbf1_J(s,d)$，故(88.3)中额外写出的域行不再增加核条件。事件侧同理恢复域列；当前事件和尝试事件两个槽分别恢复 $V_n(s,d,e)$ 与 $V_n(s,e,d)$ 两组坐标，$\Delta$ 的两个方向也逐项一致。若有 $h$，全部 $H[q]$ 相等恰恢复 $H_n$ 相等，状态和当前事件两个截面恰对应原有选择器坐标。于是得到下一秩的两个等式。

再用定理88.4的永久同时稳定：低于 $N$ 的测试已保留在第 $N$ 族中，高于 $N$ 的族与它同核，故全部有限秩测试都在该核上常值。实际像因子化给末项；不需另证一条通用最小化定理。证毕。

两个事件槽承担不同的替换义务，统一模式不能只留其中一个：第88.8节的模型只通过尝试槽传播事件区别，本节下述命题89.6则只通过当前事件槽产生首次事件分裂。个别模型可有冗余，不能由此删掉一般合同的槽位。秩计算递归测试的构造层数；它既不是一条实际执行的步数，也不是取得、存储或求值成本。

### 89.4 任意联合记忆所需保存的测试

令 $\pi_S:J\to S$、$\pi_D:J\to D$ 为两投影，把秩 $N$ 测试提升为同一实际来源上的族

$$
\mathcal L_N=
 \{p\circ\pi_S:p\in\mathcal P_S^N\}
 \cup\{q\circ\pi_D:q\in\mathcal P_D^N\}.
\tag{89.7}
$$

定理89.3与(88.9)给出 $\ker\mathcal L_N=\ker\kappa$。因此，对于任意联合记忆 $m:J\to M$，不要求它分解为两个分量编码，已有的有效像因子化判据在此恰给

$$
\begin{aligned}
&\text{每个 }t\in\mathcal L_N\text{ 均通过 }m[J]\text{ 因子化}\\
\iff{}&\ker m\subseteq\ker\kappa\\
\iff{}&\exists!\rho:m[J]\to Q,\quad\rho\circ m=\kappa.
\end{aligned}
\tag{89.8}
$$

其中最后的 $\rho$ 自动满射。理由是逐测试因子化恰说同一 $m$ 值给同一测试值；取共同核得中间项。按 $\rho(m(x))=\kappa(x)$ 定义时，核包含保证代表无关；$m[J]$ 与 $Q=\kappa[J]$ 保证唯一性及满射。这是在指定测试任务下直接使用既有判据，不把第88.5节的分量最小性扩大为任意任务的联合记忆最小性。

(89.8)只保证从已有 $m$ 恢复 $Q$。若 $m$ 比核心更细，其额外区别未必在成功后继上闭合，也未必允许以同一个尝试类 $D^\#$ 为输入。因此不能仅从恢复器制造 $m$ 自身的正确更新；仍须检查第88.7节的完整执行器交换条件，即把(88.17)中的 $r_i,F_i$ 换为 $m,F_m$。即使全部标量测试在数学上有定义，也尚未给出从未知当前配置实际取得它们的操作。

### 定义 89.5（保持配置完整的普通未来行为及比较）

本项比较固定不含选择器的合同。令 $\rho_0(s,d)=(o(s),\operatorname{type}(d))$。对实际 $x=(s,d)\in J$ 和每个原始具名词 $w\in D^*$，定义记录 $W(x,w)$，其中 $\mathsf{Obs},\mathsf{Ok},\mathsf{Fail},\mathsf{Deny}$ 是不交可见标记，方括号为有限序列：

$$
\begin{aligned}
W(x,\varepsilon)&=[\mathsf{Obs}(\rho_0(x))],\\
W(x,ew)&=
\begin{cases}
[\mathsf{Obs}(\rho_0(x)),\mathsf{Ok}(\ell)]\cdot W(y,w),
 &T_J(x,e)=\mathsf{Ok}(\ell,y),\\
[\mathsf{Obs}(\rho_0(x)),\mathsf{Fail}(f,\ell)],
 &T_J(x,e)=\mathsf{Fail}(f,\ell),\\
[\mathsf{Obs}(\rho_0(x)),\mathsf{Deny}(r,\ell)],
 &T_J(x,e)=\mathsf{Deny}(r,\ell),
\end{cases}\\
B(x)&=(W(x,w))_{w\in D^*}.
\end{aligned}
\tag{89.9}
$$

所以 $B$ 保留根观察、全部具名尝试的完整标签与原因、每次成功后的根观察，并在失败或拒绝时停止。它不直接读取原始后继身份，不提供 $J,\Delta$ 检查器，也不提供分量路由、替换、重置或重新准备。全部词作为数学索引，不表示同一未知配置的所有反事实分支可同时执行。

由第88.5节的下降与种子保持，对词长归纳即有

$$
\ker\kappa\subseteq\ker B,\qquad
\psi:Q\twoheadrightarrow B[J],\quad\psi(\kappa(x))=B(x).
\tag{89.10}
$$

具体地，核心相同给相同根观察；同一个原始尝试 $e$ 有同一个 $q_D(e)$，所以一步下降给相同完整响应头。失败或拒绝同时停止；成功后继仍实际且核心相同，归纳继续。有效像判据遂给唯一满射 $\psi$。它是双射，当且仅当 $\ker\kappa=\ker B$；结合(89.7)，这又当且仅当全部提升的有限秩标量测试在 $B$ 纤维上常值，等价地只检查有限族 $\mathcal L_N$ 即可。这里比较的是两份指定任务，不断言普通运行总需要较大的分量核心。

### 命题 89.6（四点核心、三类未来与持续的当前核心歧义）

取 $S=\{0,1\}$、$D=\{a,b\}$、$J=S\times D$、$\Delta=D\times D$，只有一种接口类型，$o(s)=s$，不声明选择器。固定一个完整标签 $\ell_0$，令

$$
\widehat T(s,d,e)=\mathsf{Ok}(\ell_0,f_d(s),d),\qquad
f_a(s)=s,\quad f_b(s)=1\quad(e\in\{a,b\}).
\tag{89.11}
$$

尝试名 $e$ 遍历两者，但不再影响响应。下表给出全部八个响应；每格都保留完整的同一个 $\ell_0$。

| 89.6 当前配置 | 尝试 $a$ 的响应 | 尝试 $b$ 的响应 |
| --- | --- | --- |
| 89.6a：$(0,a)$ | $\mathsf{Ok}(\ell_0,0,a)$ | $\mathsf{Ok}(\ell_0,0,a)$ |
| 89.6b：$(0,b)$ | $\mathsf{Ok}(\ell_0,1,b)$ | $\mathsf{Ok}(\ell_0,1,b)$ |
| 89.6c：$(1,a)$ | $\mathsf{Ok}(\ell_0,1,a)$ | $\mathsf{Ok}(\ell_0,1,a)$ |
| 89.6d：$(1,b)$ | $\mathsf{Ok}(\ell_0,1,b)$ | $\mathsf{Ok}(\ell_0,1,b)$ |

取 $\Omega=J$、$j=\operatorname{id}$，并令 $U_e$ 为 $(s,d)\mapsto(f_d(s),d)$ 的图。每个后继都在 $J$，且这个后继自身就是(87.8)要求的来源见证，所以全部原来源成功条件成立。

按 $S$ 的次序 $0,1$ 和 $D$ 的次序 $a,b$，用首次出现编号表示分区，则分量迭代为

$$
(01,00)\longrightarrow(01,01)\longrightarrow(01,01),\qquad |Q|=4.
\tag{89.12}
$$

普通联合配置则按 $(0,a),(0,b),(1,a),(1,b)$ 排序；从根读出出发，逐轮保留旧类及每个具名尝试的完整响应头和后继旧类，得到

$$
0011\longrightarrow0122\longrightarrow0122,\qquad |B[J]|=3.
\tag{89.13}
$$

证明。$o$ 已分开两个状态。事件种子只有一类，但固定状态 $0$、尝试 $a$ 后，当前事件为 $a,b$ 的下一状态读数分别为 $0,1$，故第一轮分开事件；两侧至此离散，之后稳定。联合根读出先只区分状态。一步成功使 $(0,a)$ 仍读 $0$，$(0,b)$ 改读 $1$，故它们分裂；$(1,a),(1,b)$ 对每个尝试都各自自环，完整标签和观察始终相同。前两配置与后二者由根观察分开，前两者由一步观察分开，后二者由词长归纳始终不分，故恰有三类。

再取任何确定性自适应协议：初始保留记录与控制器相同，只能读取(89.9)中的实际观察与响应，根据已获记录选择下一个具名 $a,b$ 或停止，并按共同确定规则更新记录与控制器。从 $(1,a)$ 与 $(1,b)$ 开始，初始观察相同；若某阶段记录相同，下一选择及停止决定相同。执行任一尝试都返回相同 $\ell_0$、相同新观察，且两配置分别保持原来的自环，故新记录仍相同。按阶段归纳，任意有限阶段的选择、转录和停止均相同。若协议在某阶段输出当前核心，两个执行只能给同一输出，但其实际当前核心一直不同，因而不能在二者上都精确；继续尝试不会消除这份歧义。此结论不要求控制器记忆有限。

语义测试

$$
d\longmapsto C_S[o](0,d,a),\qquad
a\longmapsto\mathsf{Ok}(\ell_0,0),\quad
b\longmapsto\mathsf{Ok}(\ell_0,1)
\tag{89.14}
$$

确能区分事件。然而要把它用于未知的当前事件，须保留那个事件并把它与状态 $0$ 重组；在原完整配置上选择具名尝试 $a$ 或 $b$ 并不执行这种重组。即使 $J$ 是全乘积，关系上存在 $(0,d)$ 也不提供从 $(1,d)$ 取得它的操作。两种当前核心在所有已获相同记录之后仍不同，所以障碍是持续取得当前核心的不足，不能解释为只丢失了某段初始历史。证毕。

### 89.7 四表达的回接与数学归属

对空间、时间、边界和记忆的同源读数 $r_i:J\to X_i$，恢复本节指定核心要求 $\ker r_i\subseteq\ker\kappa$，等价于各自保存(89.7)全部测试；恰好表达这个核心则要求第88.7节的 $\ker r_i=\ker\kappa$。后者给实际像之间唯一互恢复映射，动态共轭仍用(88.16)，外加执行器仍须(88.17)。四者只有静态互恢复，可以共同合并命题89.6中的两个当前核心；它也不说明运行中已取得那些读数。由两生成叶 $\alpha,\beta$ 产生对象，并不额外提供对未知当前分量的分解或重组操作。

本节是第87—88节模型上的 repo-derived 普通理论推导，无原创性主张。其单孔机制的既有归属是 [StrictOneHoleContexts.contextual_equivalence_is_greatest](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)：该声明在单一载体 $X$ 上，使用任意符号族的有限元数部分操作 $(\operatorname{Fin}(\operatorname{arity}(f))\to X)\to\operatorname{Option}(X)$，每个孔的其余槽允许全部 $X$ 参数，严格传播未定义值；结论是所有单孔上下文观察的等价关系为读出核以下的最大强同余。它不要求 $X$ 有限，但没有直接陈述本节两种排序、多个标量结果载体及完整标签的掩蔽构造；式(89.6)的桥接由这里的同时归纳承担，该排序带标记实例未作 Lean 编译。

[EffectiveImageKernelCriterion.refinement_iff_kernel_inclusion_on_effective_images](../../../D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean)对同一实际来源上的任意两个读数，给核包含与两个有效像间唯一因子的等价；无需有限性，也无需读数满射到原环境陪域。式(89.8)、(89.10)直接复用这一因子化机制，满射性来自目标取实际像。[ControlledSignatureStabilization.controlled_signature_algorithm_correctness](../../../D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization.lean)只作固定动作背景：它使用 $\mathrm{update}:U\to Y\to Y$、$\mathrm{readout}:Y\to O$，要求 $Y$ 有限可枚举、$U,O$ 有限、三者非空及读出满射；它不提供两分量同时取商的证明。本节有限秩结论直接采用定理88.4，而未改写该固定动作定理的适用范围。

前述访问限制、全部非孔参数及同源组合条件，分别接续 [Process Geometry 的定理3.4—3.6](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)；测试纤维常值与完整响应的比较接续该卷命题45.2至推论45.5；生成与四表达的区分接续该卷第52节，并以第88.7节的指定核心及执行器条件为准。这里没有从有限测试语义推出操作权限、物理取得方法、容量或通信界，也没有把普通证明或有限例子计作新增内核结果。

## 89.99 追加锚

## 90. 周期未来的同源向前取得、核心运输与 Fibonacci 七问六问

第89节区分了语义测试的存在与在同一未知配置上取得测试结果。本节给一个正向的访问条件：可见正未来有共同已知周期，且可以准确计数地向前等待。最早相位等待与查询、等待分账的机制复用[Transport Memory Completion 第6.8—6.9节](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，特别是 AS.2 的原始响应解码与 AS.3 的严格正等待；那里跨阈值周期的原始符号须重标记，不能直接当作相等。本节另证明任意确定性查询协议的同源模拟、初始与当前未来核心的运输，并接到 Fibonacci 的实际来源上。以下均为 repo-derived 普通数学推导，无原创性或新增 Lean 核验主张。

### 定义 90.1（可选读取的确定性单来源接口）

设 $X$ 为状态域，$A\subseteq X$ 为非空实际制备域，$T:X\to X$ 为全定义确定性更新，$o:X\to Y$ 为精确读数。未知来源 $x\in A$ 在一次执行开始时固定。读数可选择取得；未读取时不附送信息。控制器在两种模型中获得同一已知初始资料 $a(x)$，目标也固定为同一初始量 $h(x)$。所有选择、有限计算、停止及输出只依赖这些资料、已取得答案和自己命令的准确累计步数。

重置模型每问选择 $k\in\mathbb N_{>0}$，从同一个原始 $x$ 的重置副本返回 $o(T^k x)$；不能换成满足同一粗条件的另一个来源。向前模型只持有一个制备，查询时刻严格递增为 $0<t_1<t_2<\cdots$，只执行所命令的 $T$ 步后读取。两个模型都没有免费根读数或中间读数，没有从 tick、延迟、许可、失败标签等取得的来源旁路。读数不改变状态，计算与读取均不暗中推进来源；每个有限等待合法，没有硬截止，等待步数与读取次数分别收费。这里陈述条件接口，不声称实际硬件已满足它。

给定控制器已知的共同整数 $P>0$，要求

$$
f_x(k):=o(T^kx),\qquad f_x(k+P)=f_x(k)
\quad(x\in A,\ k\ge1).
\tag{90.1}
$$

不要求 $X$ 或 $A$ 有限，不要求 $T^Px=x$，也不要求控制器免费持有未知 $f_x$ 的观察表。所用计数、取余和原协议计算须在同一计算约定下可执行。将所有实际来源上至多 $m$ 问即可正确停止的确定性协议之最小 $m$ 记为 $D_{\mathrm{reset}}(A,a;h)$ 或 $D_{\mathrm{forward}}(A,a;h)$；若没有统一有限界，记为 $+\infty$，包括无法识别的情形。给定资料的空纤维另约定费用为零；非空纤维零问则要求目标已由资料确定。空域约定与一个实际来源的零问成功不同。

### 定理 90.2（同一原始来源上的逐问模拟）

在定义90.1下，每个重置协议都有一个向前协议，逐来源保持虚拟查询名、答案、分支选择、停止与输出，且每问恰用一次读取。若原协议在相应分支选 $k_1,k_2,\ldots$，取

$$
t_0=0,\qquad
t_i=t_{i-1}+1+\bigl((k_i-t_{i-1}-1)\bmod P\bigr).
\tag{90.2}
$$

这里先在整数中作减法，再取 $\{0,\ldots,P-1\}$ 中的 Euclidean 余数，不是自然数截断减法。执行 $t_i-t_{i-1}$ 步后读取，将所得答案交给仍使用虚拟名 $k_i$ 的原控制器；物理计数 $t_i$ 与虚拟查询名分别保留。有

$$
1\le t_i-t_{i-1}\le P,\qquad t_i\le iP,\qquad
o(T^{t_i}x)=f_x(k_i).
\tag{90.3}
$$

反向，每个向前协议均可由重置协议按其累计正时刻查询并保持同一初始任务的转录。因此

$$
D_{\mathrm{forward}}(A,a;h)=D_{\mathrm{reset}}(A,a;h)
\quad\text{于 }\mathbb N\cup\{+\infty\}.
\tag{90.4}
$$

证明。余数范围给严格正间隔及上界，求和给 $t_i\le iP$，且 $t_i\equiv k_i\pmod P$。两个正整数同余时，较大者是较小者加非负整数倍 $P$，反复用(90.1)即给相同答案。对读取次数归纳：初始资料相同；若前 $i-1$ 份虚拟记录相同，确定性使停止判断相同，或选择同一 $k_i$。式(90.2)只用已知 $P,k_i,t_{i-1}$，其等待合法，答案由(90.1)相同，故第 $i$ 份记录及下一选择仍相同。这一论证始终使用从开始固定的那个 $x$，没有按分支重新选择来源。

反向维护向前控制器的虚拟累计计数。它要在绝对正时刻 $u_i$ 读取时，从同一个 $x$ 的重置副本问 $u_i$；没有来源旁路或暗中演化，故该答正是向前执行在该处的答案。相同的归纳保持选择、最终计数和输出；纯等待或内部计算只需在模拟控制器中计入。于是对每个有限 $m$，两模型的至多 $m$ 问可行性等价，给(90.4)，并覆盖零问、空域约定及无统一有限界。证毕。

式(90.2)复用 AS.3 的最早严格后继相位，不作为新的调度发明。这里保持的是原协议的虚拟查询转录；两模型的物理时刻、逐副本工作量和实际动作档案不相同。至多 $mP$ 是该向前适配器的充分等待界，不是最优等待定理。查询数相等不推出总工作、截止可行性或控制器容量相等；控制器及取得过程的存储也不包含在未来类的计数中。

### 定理 90.3（正未来核心上的可逆运输）

令

$$
\widehat A=\{T^t x:x\in A,\ t\in\mathbb N\},\qquad
q(y)=(o(T^ky))_{k\ge1},\qquad Q=q[\widehat A].
\tag{90.5}
$$

取实际像 $Q$，定义移位 $(\sigma f)(k)=f(k+1)$。则 $\sigma:Q\to Q$ 良定义，对 $y\in\widehat A$、$t\in\mathbb N$ 有

$$
q(T^t y)=\sigma^t q(y),\qquad \sigma^P=\operatorname{id}_Q,
\qquad \sigma^{-1}=\sigma^{P-1}.
\tag{90.6}
$$

核心的输出可用正未来的完整解码器表示；已知 $P$ 时也可用等价的 $P$ 项周期表表示，表须由协议取得或推导，并非初始赠予。若最终累计步数为 $t$，保留相位 $\phi=t\bmod P$ 后，初始与当前核心满足

$$
q_{\mathrm{current}}=\sigma^\phi q(x),\qquad
q(x)=\sigma^{(-\phi)\bmod P}q_{\mathrm{current}}.
\tag{90.7}
$$

以停止时当前核心为目标、同时保留最终计数相位的向前最优读取数，等于以初始 $q(x)$ 为目标的重置最优读取数。

证明。$\widehat A$ 前向封闭；若 $y=T^t x$，则 $o(T^ky)=f_x(k+t)$，而 $k+t\ge1$，故 $y$ 的正未来也满足共同周期。于是 $q(Ty)(k)=q(y)(k+1)$，既证明移位在实际像中封闭，也给任意 $t$ 的运输式。逐坐标用周期性得 $\sigma^P f=f$；这同时给左右逆 $\sigma^{P-1}$，无需源状态有物理逆。式(90.7)随即成立。识别初始核心的协议停止后用已计相位计算当前核心，读取数不增；识别当前核心且保留相位的协议用逆移位计算初始核心，读取数也不增。再用定理90.2给两方向最优值相等。即使协议在末次读取后再作已计等待，同一论证仍以最终 $t$ 成立。证毕。

$q$ 仅保留正未来，不含免费 $o(y)$；式(90.6)只给移位在核心 $Q$ 上的逆，不给 $T$ 或 $q$ 的逆。一个已知初始资料纤维无需前向封闭，(90.5)正是为了避免在该纤维内臆造自主移位。由核心和相位恢复初始核心，也不等于恢复原始状态、生成树或未知的制备前历史。

### 命题 90.4（仅保持正未来的读后更新也足够）

上述读数不改变物理状态是一个充分接口条件。一个受限放宽是：读取状态 $y$ 时先返回 $o(y)$，随后作更新 $R(y)$；另有一个同时在 $T,R$ 下封闭的实际域 $B\supseteq A$，其每个正未来都满足同一 $P$，且

$$
q(Ry)=q(y)\quad(y\in B).
\tag{90.8}
$$

若仍没有未计演化或额外响应，且下次读取前必执行正数个 $T$ 步，则定理90.2的模拟和定理90.3的核心运输仍成立；不必要求 $Ry=y$。

证明。把第 $i$ 次读取前、后的状态记为 $y_i^-,y_i^+$。归纳维持读取后核心 $q(y_i^+)=\sigma^{t_i}q(x)$，初始取 $q(x)$。若下一间隔为 $d\ge1$，读取前答案为 $q(y_i^+)(d)=f_x(t_i+d)$；执行这 $d$ 步后的核心为 $\sigma^d q(y_i^+)$，读后再由(90.8)保持。故所得答案与未扰动的同源 $T$ 轨迹完全相同，按(90.2)调度仍实现原查询。逆向同样可按累计时刻模拟；最终核心仍为 $\sigma^tq(x)$。闭合域与正间隔保证每次使用的 $q$ 均有定义且该读数确属其正未来。证毕。

这个放宽只涉及保持本节指定 $q$ 的更新；它没有给任意破坏性读取提供恢复方法，也未增加一般扰动理论的假设。

### 定理 90.5（Fibonacci gcd5040 的无重置七问与六问）

采用 [Fibonacci Atomic Relation Generation 定义120.1、122.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md)的实际来源，包含结构零：

$$
v=(a,b)\in\mathbb N^2,\qquad
T(v)=Mv=(b,a+b),\qquad
o(v)=\gcd((2,3)v,5040).
\tag{90.9}
$$

读数契约取定义90.1。因此在执行 $t\ge1$ 次替换后才读取时，所得恰为该卷的 $g_t=\gcd((2,3)M^t v,5040)$，不是 $g_{t+1}$；本节的 $o$ 与定理120.10中直接读下一数量的机器读出相差这个索引约定。引理122.2给共同已知周期 $P=120$，无需整数数量或组成向量返回。

目标取 gcd 正未来核心。未供应初始数量时，向前确定性最坏读取数恰为七。若免费供应初始 $n=2a+3b$，实际制备域为

$$
A_n=\{(a,b)\in\mathbb N^2:2a+3b=n\},
$$

则对每个 $n$，包括空域约定，

$$
D_{\mathrm{forward}}(n)=D_{\mathrm{reset}}(n)=D(n),\qquad
\sup_{n\in\mathbb N}D_{\mathrm{forward}}(n)=6,\qquad
D_{\mathrm{forward}}(25920)=6.
\tag{90.10}
$$

保留最终计数相位时，以上数值也适用于停止时当前未来核心。七问及统一六问适配器分别至多执行 $840$、$720$ 次 $T$；这些是充分总步数上界。

证明。式(90.9)给全定义更新和每个正时刻的正确读出。引理122.2的周期证明来自定理120.3的局部相位：所需秩 $3,6,6,12;4,12;5;8$ 全部整除120，饱和零及无命中标签恒定。这是 gcd 周期，不是矩阵或整数轨道周期。全域在 $T$ 下封闭；每个 $A_n$ 是初始条件，其运行改用(90.5)的前向闭包，不要求当前数量仍为 $n$，也不免费供应每个后继的准确数量。

定理122.6、122.7的合法共同时刻策略给七问和六问上界，定理90.2逐来源运输它们并给 $7\cdot120$、$6\cdot120$ 的总等待界。其局部 CRT 相容性由原策略承担；虚拟 $k_i$ 运输到同余的物理 $t_i$ 后，全部局部响应同时保持。免费使用的是已给的初始 $n$ 所决定的资料；调度没有暗中读取未知当前 $n$。

下界从定理122.8、122.9经反向模拟传来。前者构造八个非负实际来源，其非7部分恒为720，而模7部分各只在一个不同的模8相位升高；沿六问均不升高的路径仍有至少两个来源存活。后者在同一 $n=25920$ 上取

$$
v_j=(2160(6-j),1440j),\quad j=0,\ldots,6,
$$

其 $z=38880+720j$ 都落在实际 $I_{25920}=[38880,43200]$，对应七个非零模8相位。五问每问至多排除一个，仍有两个不同未来。两个论证都可在路径末尾各选一个存活来源并从开头固定它；确定性归纳使它真实复现整条路径，绝非中途换源。若向前读取数低于相应下界，反向模拟便给违反这两个定理的同源重置策略。因此等号成立。定理90.3再给当前核心版本。证毕。

定理120.10的局部标签运输在这里为 $\tau\mapsto\tau-t\pmod{r_h}$，而 $d,h$ 及常值标签保持；这是(90.6)在其标签中的表达。该定理的 $42840$ 只数任意实际初始化的预测核心，不含调度相位、完整计数、取得中候选信息或控制器工作空间，不能用作七问六问的下界理由。定理121.3、121.4的连续首段八步、最坏已知数量七步要求读取首段每一个位置，是另一合同。定理122.10等其它实际纤维退化直接由(90.10)运输，毋须逐一重列公式；没有因此确定尚未知的完整 $D(n)$。这里识别的始终是 gcd 未来，不恢复精确整数、树或未知历史年龄。

### 命题 90.6（四个实际制备的严格二问—三问分离）

取实际字集 $W=\{000,100,001,011\}$、总状态域 $X=W\times\mathbb N$，初始域 $A=W\times\{0\}$，总更新

$$
T(w,s)=(w,s+1).
\tag{90.11}
$$

年龄 $s=0$ 已知，字 $w$ 未知，目标为 $w$，没有根读取或其它资料。读数 $o(w,0)=0$ 仅为使函数全定义，不是免费信息。对 $s\ge1$ 考虑两种精确、非扰动读出：周期读出 $o_{\mathrm{per}}(w,s)=w_{1+((s-1)\bmod3)}$，以及尾部归零读出 $o_{\mathrm{tail}}(w,s)=w_s$（$1\le s\le3$）、$o_{\mathrm{tail}}(w,s)=0$（$s>3$）。四个制备的正未来在两种模型中都两两不同。

周期读出满足 $P=3$，重置和向前最优读取数均为二；尾部归零读出的重置最优读取数仍为二，向前最坏读取数恰为三。两种物理状态轨道都从不重复。

证明。两种读出都允许重置先问位置3。答案0留下 $000,100$，再问位置1分开；答案1留下 $001,011$，再问位置2分开。每次只有二元答案，深度一最多两个叶，而四个实际目标不同，故两问最优。周期向前适配的物理时刻分别为 $(3,4)$、$(3,5)$，逐来源给同一答案，达到二问下界。

对归零尾，任何成功向前协议的第一次读取必须在年龄1：若先在2读，$000,100$ 从该处起直到所有未来都相同；若先在3读，两对 $\{000,100\}$、$\{001,011\}$ 各自始终相同；若首读更晚，全部未来只剩0。先在1读且答案0的实际分支留下 $000,001,011$ 三个来源。只再读一次的二元答案不能识别三个目标；更具体地，年龄2只分出 $011$，年龄3只分出 $000$，故该分支最坏仍需读取2和3。依次读取1、2、3确能识别全部四字，所以向前最坏恰三。年龄每步严格增加，故无物理状态返回；周期情形的二问模拟只依赖可见未来返回。证毕。

此例没有共享墙钟：如另给“年龄至多3”的截止，它是每个制备自其初始年龄0起的限制。周期模型的重置策略仍可在每个副本年龄至多3内完成，向前二问提升的4、5则不合法；向前读取1、2、3可行且两问不足。截止内两种读出逐时相同，故上述首次读取与三候选论证仍适用。这说明无截止假设不能从查询数等价中删去。

共同周期是本节统一模拟的充分条件，不是每个具体任务费用相等的必要条件。例如只取归零尾的 $000,100$ 两个制备，初始年龄仍为0，两种模型都在年龄1一问识别，且零问不能区分两个目标；$100$ 的正未来 $1000\cdots$ 没有正周期。这个受限任务的相等不提供一般模拟。

### 90.7 四表达的共同目标及来源边界

在同一实际执行历史域 $H$ 上先固定需要恢复的目标。若任务包括相位，可取

$$
\kappa_{90}(\eta)=\bigl(q_{\mathrm{current}}(\eta),\ t(\eta)\bmod P\bigr).
\tag{90.12}
$$

空间、时间、边界和记忆的读数 $r_i:H\to Z_i$ 应按第88.7、89.7节比较这个同一目标：核包含刻画能够恢复，核相等才给实际像上的精确互恢复；另有执行器时仍需一步交换条件，不能由静态双射自动推出。这里复用既有核与实际像判据，不另立一个同名包装定理。物理时刻及相位来自实际执行计数；它不是从语义观察表中免费获得的时钟。

相位本身不识别当前核心：同一 $t$ 下，命题90.6的不同周期字仍有不同核心。当前核心也不普遍识别模 $P$ 相位，因为各个 profile 可以有小于 $P$ 的真周期；例如 Fibonacci 的结构零及模5040饱和来源给恒为5040的未来，同一恒值核心可出现在不同模120相位。即使核心与相位都保留，也不恢复完整圈数：将同一个来源再推进 $P$ 步，二者相同而累计步数增加 $P$。这些成对实际历史说明(90.12)与原始年龄、完整档案是不同目标。

本节的 $q$ 没有替代第89节更细的分量核心 $\kappa$。命题89.6中 $(1,a)$、$(1,b)$ 的完整普通未来都是同一个常值行为，周期已为1，两个当前分量核心仍始终不同；等待不能制造分量重组权限。定理90.2只运输原本可用的同源时间查询，不把不可取得的语义上下文转成动作。

数学机制的来源范围如下。钉版 Mathlib 的 `Function.Periodic.map_mod_nat` 位于 `Mathlib/Data/Nat/Periodic.lean`，对 $\mathbb N$ 上的周期函数给 $f(n\bmod P)=f(n)$；在本节可先用 $F_x(j)=f_x(j+1)$ 转成其从零编号的形式。它只承担周期余数恒等式，不提供协议、操作权限或同源模拟。[EffectiveImageKernelCriterion.refinement_iff_kernel_inclusion_on_effective_images](../../../D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean)对任意类型上的同源读数给实际像唯一因子与核包含的等价，既不要求有限域，也不免费取得这些读数。[ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity](../../../D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.lean)讨论有限状态、动作、读数的确定性部分动作系统及非空初始支持上档案恢复累计费用的判据；它不自动恢复未知原点、制备前年龄，也没有为本节的无限状态域提供时钟。以上均为源码层面的归属说明，本节没有声称编译了这些定理的新实例。

文献背景为 Ronald L. Rivest 与 Robert E. Schapire，*Inference of Finite Automata Using Homing Sequences*，STOC 1989，[原文](https://people.csail.mit.edu/rivest/pubs/RS89.pdf)第3—4.1节。其 homing 根据执行序列及输出确定到达态，与回到一个规定状态的 reset 区分；其学习设置还包含 teacher 与强连通等条件。这解释了“确定到达态”与“从同一原始来源重问”的区别，不充当定理90.2的同源、逐查询等价证明。AS.2—AS.3的等待机制、Fibonacci 第120—122节的局部分类及查询界和既有因子化判据均按各自范围复用；本节增量是它们之间明确保留来源、计数和资源边界的普通综合推导。

## 90.99 追加锚

## 91. 初始—当前核心对的最小运输记录与同源续接

### 91.1 变更后的目标与实际支持

本节把式(90.12)的目标 $(q_{\mathrm{current}},t\bmod P)$ 明确改为**有序的初始—当前核心对**；这是改变保留要求，不是声称在保持原钟任务的同时压缩；当某轨道的真周期小于 $P$ 时，这些历史上的钟信息确有损失。沿用定义90.1的确定性、同源、准确计数、任意有限向前等待及付费不扰动读取合同，没有免费当前物理读数。令非空初始域为 $A$，并取前向封闭实际域及正未来

$$
\widehat A=\{T^t x:x\in A,\ t\in\mathbb N\},\qquad
q(y)=(o(T^ky))_{k\ge1},\qquad Q=q[\widehat A].
\tag{91.1}
$$

另行假设 $Q$ 有限非空，且控制器知道一个 $P>0$，使移位 $\sigma:Q\to Q$ 满足 $\sigma^P=\operatorname{id}_Q$。移位定义为 $(\sigma f)(k)=f(k+1)$；逐坐标有 $q(T^t y)=\sigma^tq(y)$，前向封闭保证它始终在实际像中。定理90.3给其逆 $\sigma^{P-1}$，不要求 $T$ 在物理域上可逆。记

$$
B=q[A],\qquad q_0=q(x),\qquad c=\sigma^tq_0,\qquad
\kappa_{91}(x,t)=(q_0,c).
\tag{91.2}
$$

满初始支持 $B=Q$ 是以下全局计数和全来源时钟必要性的附加前提；仅有 $Q=q[\widehat A]$ 不保证它。有限 $Q$ 也不是仅从共同周期推出的，因为输出字母集尚未假设有限。

### 91.2 端点对、轨道位移与闭合最小记录

先取 $B=Q$。令 $d(c)$ 为 $\sigma^{d(c)}c=c$ 的最小正整数，令 $\mathcal O$ 遍历 $\sigma$ 的轨道。端点对实际像与位移坐标分别为

$$
\begin{aligned}
R&=\{(q_0,c):q_0\in Q,\ c=\sigma^tq_0\text{ 对某个 }t\in\mathbb N\}
  =\bigsqcup_{\mathcal O}(\mathcal O\times\mathcal O),\\
E&=\{(c,\bar r):c\in Q,\ \bar r\in\mathbb Z/d(c)\mathbb Z\}.
\end{aligned}
\tag{91.3}
$$

**定理 91.2（端点对的精确记录）。** $d$ 在每个轨道上恒定且整除 $P$。下列映射互逆，其中 $\bar r$ 是满足 $c=\sigma^r q_0$ 的唯一模 $d(c)$ 位移：

$$
R\longrightarrow E,\quad(q_0,c)\longmapsto(c,\bar r),
\qquad
E\longrightarrow R,\quad(c,\bar r)\longmapsto(\sigma^{-r}c,c).
\tag{91.4}
$$

旧记录 $(c,\bar t_P)$ 可良定义地压为 $(c,\bar t_{d(c)})$。新记录支持闭合更新

$$
(q_0,c)\longmapsto(q_0,\sigma c),\qquad
(c,\bar r)\longmapsto(\sigma c,\overline{r+1}),
\tag{91.5}
$$

而完整记录实际像的最小基数为

$$
|R|=|E|=\sum_{c\in Q}d(c)=\sum_{\mathcal O}|\mathcal O|^2.
\tag{91.6}
$$

证明。若 $\sigma^n c=c$，以 $n=ad(c)+s$、$0\le s<d(c)$ 作除法，消去整圈得到 $\sigma^s c=c$，最小性迫使 $s=0$。反向 $d(c)\mid n$ 显然给返回，负整数也由可逆性得到同一判据。取 $n=P$ 得整除。若 $c'=\sigma^j c$，则 $\sigma^n c'=c'$ 等价于 $\sigma^n c=c$，故周期恒定；一个轨道恰有 $d(c)$ 个元素。

两端属于同一轨道是出现为端点对的必要条件；反向，在有限循环中每个目标端点都由一个非负幂到达，满支持允许每个起端。这证明(91.3)的不交并。若两个整数 $r,s$ 都把 $q_0$ 送到 $c$，消去幂后有 $d(c)\mid r-s$；反向同余给相同端点，所以位移类唯一。更换 $r$ 的代表不改变 $\sigma^{-r}c$，故(91.4)良定义，两次复合分别返回原对和原坐标。又因 $d(c)\mid P$，两个模 $P$ 的代表也有相同的模 $d(c)$ 余数，证明旧记录的压缩良定义。

一步后 $d(\sigma c)=d(c)$ 且 $\sigma^{-(r+1)}\sigma c=\sigma^{-r}c=q_0$，证明(91.5)在同一坐标域闭合。任意确定性记录若能只由自身恢复 $\kappa_{91}$，便不能把任何两个不同的 $R$ 元素合为一个值，哪怕两对的当前端点不同。选每个对的一条实际历史，就得到 $|R|$ 个不同记录值；记录允许更细或无限，也不能减去这个下界。记录对本身或(91.4)的坐标，同时解码两端并按(91.5)更新，达到下界。每个当前 $c$ 恰有 $d(c)$ 个位移，或每个轨道贡献 $|\mathcal O|^2$ 对，给(91.6)。证毕。

这是端点对实际像与 $E$ 的双射，也可说是历史按相同端点对取商后的双射；$Q\times\mathbb N\to E$ 不是双射，整圈年龄已经丢失。最小性复用既有同源实际像的核判据，本节不把一般因子化或轨道商重新作为新通用理论。

### 91.3 受限制备、合法取得与继续域

对任意 $B=q[A]$，正确的两种实际像是

$$
R_B=\{(b,c):b\in B,\ c\in\operatorname{Orb}(b)\},\qquad
E_B=\{(c,\bar r)\in E:\sigma^{-r}c\in B\},\qquad
|R_B|=\sum_{b\in B}d(b).
\tag{91.7}
$$

证明。不同初始 $b$ 给互不相交的首坐标纤维，每条纤维有 $d(b)$ 个当前端点；(91.4)限制到它们即给 $R_B\leftrightarrow E_B$。式(91.5)保持初始端点，故这个限制仍闭合。对每个 $b\in B$，固定一个实际代表 $x_b\in A$；任意 $(b,c)\in R_B$ 都由这个同一个 $x_b$ 上的某个非负步数实现。各历史选择来源以后始终固定它，没有在过程中换源。证毕。

表示的初始化还须有取得桥。若实际协议已取得精确初始核心 $q_0$ 并计数到 $t$，可算出 $(q_0,\sigma^tq_0)$；若已取得当前核心 $c$ 并保留足够的运输资料，例如 $t\bmod P$，可算出 $(\sigma^{-t}c,c)$，再压成 $E_B$。在多初始核心的同轨道支持上，单独的当前核心一般不能恢复缺失的初始核心；91.5节给实际反例。数学上写出 $q_0$ 或整张未来表不等于已经取得它。

若协议在每个实际来源的某个有限时刻 $s(x)$ 取得所需核心和运输资料，取得后允许任意进一步的计数等待，则继续域的对像仍恰为 $R_B$：固定 $x_b$，对每个所需位移类选择 $u\ge0$ 使 $s(x_b)+u$ 落在该类，便到达对应当前端点。没有新增对能离开(91.7)。因此第一次停止边界可以较小，但取得加任意继续的容量须取完整的 $R_B$。若有截止或取得不能完成，这一继续结论的前提便不满足。

最小记录计入以后解码或更新使用的全部执行依赖资料；档案、钟、隐藏控制态、缓存或当前传感器都不能在记录外免费补信息。固定模型表、程序及 rank/unrank 的描述和计算成本，以及取得时的候选存储、算术、命令计数和瞬时工作区，另行核算。(91.6)—(91.7)只给取得后的联合表示容量与所示一步更新，不给最优取得空间；任意额外策略状态若跨步保留也须计入。

### 91.4 全来源全时刻的独立时钟

以下重新明确取 $B=Q$，要求对所有 $q_0\in Q$ 及所有 $t\in\mathbb N$ 恢复初始核心，不能仅要求在某个来源依赖的停止时刻成立。令

$$
D=\operatorname{ord}(\sigma)=\operatorname{lcm}_{c\in Q}d(c).
\tag{91.8}
$$

此等式由91.2节的返回判据成立：$\sigma^n=\operatorname{id}$ 当且仅当每个 $d(c)\mid n$。这里源无关的钟函数记为 $r:\mathbb N\to C$，有别于(91.4)的位移代表。存在由 $(\sigma^tq_0,r(t))$ 恢复 $q_0$ 的统一解码器，当且仅当

$$
r(t)=r(u)\ \Longrightarrow\ D\mid(t-u)\qquad(t,u\in\mathbb N),
\tag{91.9}
$$

差在整数中计算。

证明。若(91.9)成立，取某钟值的任一实现时刻 $t$，定义解码为 $\sigma^{-t}c$；换成同钟值的 $u$ 时，$D\mid t-u$ 保证结果不变，且对真实输入准确返回 $q_0$。反向，若 $r(t)=r(u)$ 而 $D\nmid t-u$，存在某个周期 $d$ 不整除 $t-u$。在该轨道选当前 $c$，分别选两个实际初始代表 $x_t,x_u\in A$，满足 $q(x_t)=\sigma^{-t}c$、$q(x_u)=\sigma^{-u}c$。这两个初始核心不同；分别固定来源并推进 $t,u$ 步后，当前核心都是 $c$、钟值相同，统一解码矛盾。此比较使用两条各自固定来源的历史。证毕。

将时刻 $0,\ldots,D-1$ 代入(91.9)得到至少 $D$ 个不同钟值；$t\bmod D$ 达到下界，且有闭合更新 $z\mapsto z+1\bmod D$。满支持还使每个 $(c,\bar t_D)$ 都实际出现，故完整“当前核心乘最小通用钟”的像有 $|Q|D$ 个值。相比之下，(91.4)按当前轨道只保留所需位移，且仍同时保留两端。

更细的钟能解码初始核心不保证自身可自主更新。例如 $r(t)=(t\bmod D,\mathbf1_{\{t=D\}})$ 满足(91.9)，但 $D-1$ 与 $3D-1$ 同钟值，下一步 $D$ 与 $3D$ 的钟值不同，故不存在统一的 $r(t)\mapsto r(t+1)$。受限 $B$，特别是单一已知初始核心或固定 $n$ 制备纤维，不承担本节的全来源必要性。

### 91.5 两环分离与年龄损失

取长度2的环 $a_0\mapsto a_1\mapsto a_0$ 和长度3的环 $b_0\mapsto b_1\mapsto b_2\mapsto b_0$，准许全部初始准备，并用能区分各点的读出使正未来核心恰为这五点。由(91.6)、(91.8)有

$$
|Q|=5,\qquad |R|=2^2+3^2=13,\qquad D=6,\qquad |Q|D=30.
\tag{91.10}
$$

模3的钟失败：从 $a_0$ 推进6步和从 $a_1$ 推进3步，都到 $a_0$ 且钟值为零，初始核心却不同。这同时证明当前核心单独不足。若初始支持改为单点 $\{b\}$，对像只需 $d(b)$ 个值；初始核心已经固定，不需另钟来恢复它，所计的 $d(b)$ 个区别是不同当前端点。

同一来源在 $t$ 和 $t+d(q_0)$ 有相同端点对，年龄却相差正数；若 $P>d(q_0)$，这两个时刻还给不同的旧模 $P$ 钟。若给物理状态另加一个不被观察且每步递增的自然数年龄坐标，以上核心与计数全部不变，而物理状态从不返回。因此商上的逆位移不提供物理回返、倒流或初始物理状态的恢复。

### 91.6 Fibonacci gcd5040 的周期重数与联合容量

取 [Fibonacci Atomic Relation Generation](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 定义120.1、定理120.3—120.5及120.10的来源与局部分类：

$$
v=(a,b)\in\mathbb N^2,\qquad T(v)=Mv=(b,a+b),\qquad
q(v)=\bigl(\gcd((2,3)M^kv,5040)\bigr)_{k\ge1}.
\tag{91.11}
$$

包含零来源，且全部非负来源都可制备，故 $A=\widehat A=\mathbb N^2$、$B=Q$。本节的 $q$ 是整个正未来，不是原卷用作行向量的 $(2,3)$。令观察坐标 $(n,z)=(2a+3b,3a+5b)$，局部含量用 $\delta_p$ 表示，以免与内禀周期 $d(c)$ 混淆。原分类的非恒定标签 $(\delta_p,h,\tau)$ 满足

$$
\nu_p(g_k)=\delta_p+
 \sum_{j=1}^{h}\mathbf1_{\{k\equiv\tau\pmod{r_j}\}},
\qquad r_j\mid r_h,\qquad k\ge1,
\tag{91.12}
$$

其中指数截断于相应素数幂，$g_k$ 为(91.11)第 $k$ 项。饱和标签和无命中标签为常值。

每个非恒定标签的准确周期是 $r_h$。证明：式(91.12)的每项以 $r_h$ 为周期；最高达到的指数 $\delta_p+h$ 恰在一个模 $r_h$ 的剩余类出现。若 $\ell>0$ 是任何周期，选一个正的最高命中时刻 $k$，则 $k+\ell$ 也必须在该类，故 $r_h\mid\ell$。常值标签的准确周期为1。于是局部周期重数为

$$
\begin{aligned}
m_{16}&=\{1:1,\ 3:3,\ 6:24,\ 12:12\},&
m_9&=\{1:1,\ 4:4,\ 12:12\},\\
m_5&=\{1:2,\ 5:5\},&
m_7&=\{1:1,\ 8:8\}.
\end{aligned}
\tag{91.13}
$$

这些重数由原来的秩提升分类直接计得，特别保留模8的停滞。二进秩为 $3,6,6,12$；模2、4轨道全满，模4到8每个轨道父点恰有一个轨道提升及一个退出提升，模8到16的轨道父点则两个提升都在轨道。对剩余精度 $m=1,2,3,4$，分别得到：3个周期3标签；6个周期6标签；6个末层与6个退出的周期6标签；12个周期12末层标签及6个周期6退出标签。加上一个饱和常值，周期6的重数恰为 $6+(6+6)+6=24$。三进两层轨道全满且秩为4、12，分别贡献4、12个相位及一个饱和标签；模5五点轨道外的唯一无命中标签和饱和标签都是常值；模7八点轨道全满再加饱和标签。这证明(91.13)，无需以枚举代替停滞提升论证。

任意四个局部标签确能共同实现：按定理120.4各取一个局部 $(n,z)$ 剩余代表，CRT 合成模5040的剩余对，再用整数互逆变换

$$
\binom n z=\begin{pmatrix}2&3\\3&5\end{pmatrix}\binom a b,\qquad
\binom a b=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}\binom n z
\tag{91.14}
$$

取得 $(a,b)$ 的模5040剩余并选非负代表。这一个实际来源实现全部局部标签；零标签也在内，并不要求这些来源共享某个确切 $n$。两个联合标签不同则某个素数的指数未来不同，整个 gcd 未来也不同；每个局部指数又可从 gcd 逐项恢复。因此联合周期准确是局部周期的 lcm：局部周期的公倍数使 gcd 重复，任何 gcd 周期也必须是全部局部周期的倍数。这给

$$
|Q|=40\cdot17\cdot7\cdot9=42840,\qquad
\operatorname{ord}(\sigma)=\operatorname{lcm}(12,12,5,8)=120.
\tag{91.15}
$$

后一个等号同时有上下界：所有局部周期整除120，而周期12、5、8的标签可共同实现，产生一个周期120的核心。闭合移位就是定理120.10的相位 $\tau\mapsto\tau-1$，不表示整数矩阵轨道返回。

为简短计算，先合并16、9两轴，令 $a(u)=\sum_{\operatorname{lcm}(s,t)=u}m_{16}(s)m_9(t)$；相乘整理得

$$
\{u:a(u)\}=\{1:1,\ 3:3,\ 4:4,\ 6:24,\ 12:648\}.
\tag{91.16}
$$

模5的周期与这些 $u$ 及8互素，故乘上该轴时周期加权和的因子为 $2+5\cdot5=27$，逆周期加权和的因子为 $2+5/5=3$。再合入模7的常值及八个周期8标签，得到

$$
\begin{aligned}
|R|
 &=27\sum_u a(u)\bigl(u+8\operatorname{lcm}(u,8)\bigr)
   =27\cdot137866=3722382,\\
\#\operatorname{Orb}(\sigma)
 &=3\sum_u a(u)\left(\frac1u+\frac8{\operatorname{lcm}(u,8)}\right)
   =3\cdot291=873.
\end{aligned}
\tag{91.17}
$$

第一行把每个核心按其周期加权，正是(91.6)；第二行在每条长度 $d$ 的轨道上给每个核心权重 $1/d$，一条轨道共贡献1。这是短的加权 lcm 乘积计算，不需要完整联合周期直方图。

满支持下，当前核心与模120通用钟的完整乘积有 $42840\cdot120=5140800$ 个实际值。对整个联合记录作固定宽度编码，有

$$
2^{21}<3722382\le2^{22},\qquad
2^{22}<5140800\le2^{23},\qquad
2^{15}<42840\le2^{16}.
\tag{91.18}
$$

因此新对任务需22位联合表示容量，完整当前核心加模120钟需23位，当前核心单独仍需16位。这些是整个联合像的定宽容量，不是分寄存器位数之和、计算机内存界或取得工作区界；两种22/23位任务保留的钟信息不同。

### 91.7 取得后的同源继续读取

Fibonacci 命题127.7已给定理127.4递增查询策略的单副本取得桥：使用付费、精确、不扰动的当前读出 $R_{\mathrm{cur}}(s)=\gcd((2,3)s,5040)$，在正的指定步数处读取；全域至多7读和8次替换，免费已知初始 $n$ 的纤维统一至多6读和7次替换。其递增时刻使两读之间始终有正步数，跳过位置不附送观察，也未免费读取初始当前值。已知 $n$ 只提供其原合同中的初始资料。取得初始核心并保留命令计数后，91.3节的初始化与继续因而适用。Boundary90 的840、720仍是通用周期适配器的充分总步数界；原卷127.7给上述更小的构造界，两者都没有证明工作量最优。停止时刻的计数不能凭借上述7/6读取数或22位容量免费取得。

还可复用 AS.3 的正后继相位给一个可选重读安排。已保留 $(c,\bar r)\in E_B$，取其标准代表 $0\le r<d=d(c)$，在同一固定来源上再执行

$$
\delta=1+\bigl((k-r-1)\bmod d\bigr),\qquad1\le\delta\le d,\qquad k\ge1,
\tag{91.19}
$$

个命令步，然后付费不扰动读取，即得到原来源的第 $k$ 个正未来答案。证明：整数余数给 $r+\delta\equiv k\pmod d$；若当前实际累计步数是 $t$，(91.4)给 $t\equiv r\pmod d$，故 $t+\delta\equiv k\pmod d$。两指标均正，正未来的周期性给 $o(T^{t+\delta}x)=q(x)(k)$。中间每一步按(91.5)更新，读取后保留 $(\sigma^\delta c,\overline{r+\delta})$，所以可逐次继续；同源及正间隔始终保持。证毕。

这里取余前作整数减法，不作自然数截断减法。调度只给一个充分的物理重读安排，不声称等待最优或必要；若只需预测答案，已经取得的核心就能解码 $q(x)(k)$，无需再读。调度算术、临时计数及实际等待、读取各自收费，不由记录基数包办。

### 91.8 四表达的回接、来源与未解边界

在同一实际历史域 $H$ 上，空间、时间、边界和记忆的读数 $s_i:H\to Z_i$ 能恢复本节对目标，当且仅当 $\ker s_i\subseteq\ker\kappa_{91}$；要恰好表达该目标，则须 $\ker s_i=\ker\kappa_{91}$。这直接沿用第89.7、90.7节及 [EffectiveImageKernelCriterion](../../../D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean) 的实际像判据：定义恢复器为 $s_i(\eta)\mapsto\kappa_{91}(\eta)$，核包含保证代表无关；反向由解码施加到相同读数得到核包含。核相等时反向恢复器也良定义，两个复合在实际像上恒等。仅各自能恢复对目标，仍允许它们携带彼此不同的额外信息，不能推出互恢复。

若还有实际执行更新 $U$ 及表示更新 $U_i$，还须验证 $s_iU=U_i s_i$；核相等给出的静态双射不代替执行器的这项条件。对(91.4)本节已由(91.5)给出交换的更新；其它四表达只能在各自履行同一条件时接入。生成器 $\alpha,\beta$ 描述生成规则，不决定指定操作、准备和目标下的记录基数。第89.6节中普通未来相同而分量核心不同的障碍仍在：本节恢复正未来对，没有提供分量重组权限。

本节所据源版本为仓库修订 93e6b0757877e79433c423486912842d248ee09b。Boundary 第45节的联合/分开编码区别、第51节的完整持久状态计数、第89—90节的目标核与周期运输，以及 [Transport Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) 第2、6.8—6.9节、[Joint Relations Clocks](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md) 第14—15、31节，分别承担任务商、实际支持、取得与等待分账、保钟/删钟任务及更新闭合的已有接口；没有把这些一般机制作为新结果。Fibonacci 的局部标签、实际 CRT 来源和取得界依上述原卷条目，周期加权的对容量由本节普通推导给出。

[ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) 的泛性质另要求有限来源、有限实现、满射实现映射及更新/读出的交织；这里不把无限物理来源直接当作它的已编译实例。上述 Lean 源码只作归属，不构成本节的新 Lean 应用或认证。所有结论限定于已声明的有限周期正未来任务，不恢复绝对年龄、制备前历史、精确整数或原始组成，不给物理统一、取得空间最优性或原创优先权。更一般的空间、时间、边界与记忆的最小关系结构及可取得条件，仍须分别建立。

## 91.99 追加锚

## 92. 破坏性动作下保留原来源的有限任务取得

第89节的全部反事实测试与第91节的端点对表示，都不自动提供一条成功的取得路径。本节固定已知有限确定模型，以初始任务标签和当前候选的关系给出精确判据；重点是动作可能在尚未区分标签时合并来源。所用机制属于经典自适应区别树及有限到达博弈，不是新的通用控制理论。第93节再把一个满足可逆剩余运输的具体合同接到 Fibonacci 原子接枝。

### 92.1 实际来源、合法尝试与成功报告

固定有限集 $S,A,Y$、非空初始支持 $B\subseteq S$ 及任务 $k:B\to K$，只需有限实际标签集 $K_B=k[B]$。一次执行开始时选定未知的 $b\in B$，以后不换源。已知模型为每个状态的尝试菜单 $\mathcal A(s)\subseteq A$，以及在 $a\in\mathcal A(s)$ 时总定义的响应、后继

$$
\lambda(s,a)\in Y,\qquad \delta(s,a)\in S.
\tag{92.1}
$$

响应可以带互不混淆的 $\mathsf{Ok},\mathsf{Deny},\mathsf{Fail}$ 及原因；静默命令也返回固定的无信息符号。允许尝试与尝试后成功不同：仅当 $a\in\mathcal A(s)$ 时才有可执行的拒绝或失败分支；菜单外动作没有可偷取的拒绝读数。失败后是否可继续由已声明的后继决定，不能暗设失败无扰动。终态集合 $T\subseteq S$ 满足 $\mathcal A(s)=\varnothing$；其中可包括成功后可报告的状态和不可挽回的失败态。非终态也可能没有合法尝试。

另固定报告权限 $\mathsf{Stop}(s,z)$，$z\in K_B$。成功停止须报告 $z=k(b)$，且当前态允许该报告；单纯终止、拒绝或失败不计成功。若某失败终态禁止任何成功报告，就令其所有 $\mathsf{Stop}(s,z)$ 为假；若合同允许依据失败读数仍作正确报告，则明确给相应权限。报告本身不改变来源，也不读取额外信息。以下策略须在全部相容当前态上合法，不能先冒险越域再根据结果筛去非法来源。

控制器从共同已知的 $B,k$ 与模型表开始，只用自己的动作、实际响应及保留记录选择下一尝试或停止；表已知不等于未知当前态已知。没有免费初始观察、重置、复制、外部时钟或未记录演化。任何实际等待须列为动作；若权限依赖额外阶段或时钟，必须先纳入模型状态及其已知部分，重新满足本节有限合同。一次尝试计一层，报告不计尝试层；这是单位动作成本，不是物理时延或付费传感器次数的通用公式。

### 92.2 初始标签—当前态的精确转录不变量

对一个实际可能的动作响应历史 $h$，令 $B_h$ 是从一开始固定为该来源、执行同一历史动作时恰产生全部响应的 $b\in B$，令 $s_h(b)$ 是其当前态。初始没有读取，所以 $B_\varepsilon=B$、$s_\varepsilon(b)=b$。保留关系

$$
R_h=\{(k(b),s_h(b)):b\in B_h\}\subseteq K_B\times S,
\qquad C_h=\pi_S R_h.
\tag{92.2}
$$

这不是两个边缘集合的独立组合。对非空关系 $R$，定义共同合法菜单与实际响应后继

$$
\begin{aligned}
\mathcal A(R)&=\bigcap_{s\in\pi_S R}\mathcal A(s),\\
F_{a,y}(R)&=\{(\ell,\delta(s,a)):(\ell,s)\in R,\ \lambda(s,a)=y\},\qquad a\in\mathcal A(R).
\end{aligned}
\tag{92.3}
$$

只保留非空的 $F_{a,y}(R)$。每个合法动作至少有一个非空响应分支，因为 $R\ne\varnothing$ 且(92.1)在该菜单上总定义。

**命题 92.1（每条转录由固定原来源实现）。** 若 $a\in\mathcal A(R_h)$ 且观察到 $y$，则

$$
B_{hay}=\{b\in B_h:\lambda(s_h(b),a)=y\},\qquad
s_{hay}(b)=\delta(s_h(b),a),\qquad R_{hay}=F_{a,y}(R_h).
\tag{92.4}
$$

特别是，关系递推保留全部且仅有相容的初始标签—当前态对。

证明。空历史成立。归纳步中，动作在全部相容态上有定义；确定响应筛去恰好不能复现 $y$ 的来源，留下的每个来源由自己的确定后继推进。取带标签像正得(92.3)，反向每个后继对也有一个旧来源见证。重复的相同对可以删除，因为后续菜单、响应、后继与报告权限都只依赖当前态，任务值也已相同。于是它们对本任务有相同合法继续；这没有允许把来源换成另一个只满足边缘条件的对象。证毕。

### 92.3 最小吸引子的准确成功条件

在非空关系组成的有限域上设

$$
\begin{aligned}
W_0&=\{R:\exists z\in K_B\ \forall(\ell,s)\in R,
                   \ \ell=z\ \land\ \mathsf{Stop}(s,z)\},\\
W_{n+1}&=W_n\cup
 \{R:\exists a\in\mathcal A(R)\ \forall y\in Y,
       \ F_{a,y}(R)\ne\varnothing\Rightarrow F_{a,y}(R)\in W_n\},\\
W_*&=\bigcup_{n\ge0}W_n.
\end{aligned}
\tag{92.5}
$$

$W_0$ 只含可以合法共同成功报告的关系。标签纯但禁止报告的失败叶不在其中。无合法动作又不在 $W_0$ 的节点是失败死锁；它不会因为后继量词为空而自动获胜，因为(92.5)先要求存在一个合法动作。

**定理 92.2（有限单执行取得的充要条件）。** 从 $R_\varepsilon=\{(k(b),b):b\in B\}$ 出发，存在对每个实际 $b$ 都合法、有限停止并准确报告 $k(b)$ 的确定性策略，当且仅当 $R_\varepsilon\in W_*$。更精确地，$R\in W_n$ 当且仅当从该信息关系有一棵所有叶均合法成功、最坏至多 $n$ 次尝试的自适应树；首次进入 $W_n$ 的指标就是最小最坏尝试数。

证明。对 $n$ 归纳。零层只能立即报告，恰为 $W_0$。至多 $n+1$ 层的成功树或者已有更小深度，或者先选一个共同合法动作，且每个非空响应子树均至多 $n$ 层成功；这正是(92.5)。反向选取其中的动作及每个非空孩子的成功树即可拼接。每个节点的动作响应和报告都由既有记录确定，命题92.1保证真实来源恰沿自己的分支运行。按最小秩选动作时各孩子秩严格下降，因此确实有限停止。

还须把逐来源有限停止提升为统一有限深度。给定一份逐来源成功策略，每个 $b\in B$ 产生唯一有限路径，记长度为 $n_b$。有限非空 $B$ 给 $N=\max_{b\in B}n_b<\infty$。删掉没有来源实现的分支后，策略树是这有限条路径的并，深度至多 $N$；其各叶有正确的共同标签和权限。因此归纳结论给 $R_\varepsilon\in W_N$。这里不能对无限初始支持仅凭逐点终止取同一个最大值。证毕。

把响应当作对手选择时，也没有增强为允许对手途中换源。沿任意无限非空分支，命题92.1给递减非空有限集

$$
B\supseteq B_{h_1}\supseteq B_{h_2}\supseteq\cdots.
\tag{92.6}
$$

其交非空：有限 $B$ 中若每个元素最终被删，取全部删除时刻的最大值就会出现空集。固定交中的一个 $b$，它从开始到每个有限前缀都真实复现该分支。故无限不成功分支是一个固定实际来源上的不终止，而非轮流借用不同来源。由于关系域有限，$W_n$ 最终稳定；在 $W_*$ 外，每个合法动作都有一个仍在外部的非空分支。沿它继续，或者遇到不能成功报告的停止／死锁，或者给(92.6)的无限失败来源。这也说明为什么“存在一个有利响应”不足以代替所有实际响应条件。

此处最小吸引子的秩归纳直接复用 [FiniteHorizonReachability.finite_horizon_reachability](../../../D5/S3/ConceptDynamics/Control/FiniteHorizonReachability.lean) 的到达结构：状态取关系，动作取共同合法尝试，后继集取全部非空响应关系，目标取 $W_0$。该源码要求每个动作的后继集非空，已由(92.3)核对；实际固定来源语义及逐点终止到统一深度的桥由本节证明承担。此为源码归属和普通数学应用，没有编译新的 Lean 实例。

### 92.4 初态、当前态与端点的不同停止谓词

(92.5)识别初始 $k(b)$。若任务改成当前状态，则成功叶须满足 $|\pi_S R|=1$，并在这个唯一当前态有合法的报告权限；此时不要求初始标签唯一。若任务为 $(k(b),s_h(b))$，成功叶须 $|R|=1$，仍须检查对该有序对的报告权限。三个任务的输出域、报告权限分别固定后，再用相同递推；不能用一次当前态 homing 宣告初态恢复。物理终态也不是上述三个成功条件之一，除非合同恰好允许所需报告。

**命题 92.3（获胜关系的方向与安全合并）。** 对初始标签任务，每个获胜关系必是从当前候选到初始标签的部分函数图，即

$$
(\ell,s),(\ell',s)\in R\quad\Longrightarrow\quad\ell=\ell'.
\tag{92.7}
$$

同一标签可以关联多个当前态，故不要求 $\ell\mapsto s$ 为函数。同标签的来源合并可以安全；异标签在同一响应下合并则不可挽回。

证明。若同一 $s$ 带两个不同标签，两来源从此在每个共同选择下有相同响应、后继、权限和控制记录。归纳至任何停止时，它们只能收到同一个输出，不能都正确。因此该关系没有成功策略。相同标签、相同当前态的重复对则由命题92.1可以合并。条件(92.7)只是必要条件：两不同状态各自恒输出同一符号且自环、标签不同，始终无碰撞，也始终无法取得任何区分进展。证毕。

在身份任务 $k(b)=b$、所有状态均允许报告任一身份的专门合同中，可把规划压到当前集合 $C$，同时对每个选择加入同响应单射守卫

$$
\lambda(s,a)=\lambda(t,a),\quad\delta(s,a)=\delta(t,a),\quad s,t\in C
\quad\Longrightarrow\quad s=t.
\tag{92.8}
$$

保留共同合法性，以单点 $C$ 为成功叶，后继为 $C_{a,y}=\{\delta(s,a):s\in C,\lambda(s,a)=y\}$。从初始对角关系起，守卫保证存活来源到当前态单射；每次删去其他响应后，原身份解码器 $d_h:C_h\to B_h$ 按

$$
d_{hay}(\delta(s,a))=d_h(s)\quad\text{当 }\lambda(s,a)=y
\tag{92.9}
$$

更新。反向，任何身份成功策略都不能让同响应异来源合并，所以满足守卫。于是当前集合加守卫足够决定此专门合同的可行规划，但执行与最终初态输出仍须保留随历史改变的 $d_h$ 或等价运输资料。若报告权限依赖原身份，不能未经补充就把它从规划状态中删除。

例如 $B=S=\{0,1\}$，一个静默动作 $u$ 交换两态，另一个合法读取逐态返回 $0,1$ 且不扰动。空历史与仅执行 $u$ 的历史都有 $C=\{0,1\}$，前者解码为 $d(s)=s$，后者为 $d(s)=1-s$。同样的后续当前读数 $0$ 分别要求报告原身份 $0,1$。动作名和交换次数来自自己的已执行记录，却仍是必须保存的区别；它们不在模型表已知这个事实中免费存在。

### 92.5 三个生成对象的最小反例

取三个实际来源名 $0=\alpha$、$1=\beta$、$2=\langle\alpha,\beta\rangle$，三者互异，身份任务为 $k(i)=i$。另外声明两个处处允许的探针 $a,b$，全部状态都允许正确报告。下表每格为“响应，后继态”；两个探针不由配对构造或递归关系 $\rho$ 自动提供。

| 92.5 来源／当前态 | 探针 $a$ | 探针 $b$ |
| --- | --- | --- |
| 92.5a：$0=\alpha$ | $(0,1)$ | $(0,2)$ |
| 92.5b：$1=\beta$ | $(0,1)$ | $(1,1)$ |
| 92.5c：$2=\langle\alpha,\beta\rangle$ | $(1,2)$ | $(0,2)$ |

**命题 92.4（两两可区分但不能共同取得初态）。** 此完整确定接口中，每对初态都有区分词，当前态可在一次尝试后准确取得，初始身份却没有成功自适应策略；没有共同 reset 词。把任务改为 $k(0)=k(1)\ne k(2)$ 后，探针 $a$ 一次取得任务。

证明。$0,1$ 由 $b$ 的响应区分，$0,2$ 由 $a$ 区分，$1,2$ 由任一探针区分。首选 $a$ 的响应0把初态0和1合到当前1；首选 $b$ 的响应0把初态0和2合到当前2。两种首选各有异标签碰撞，此后任何动作响应都相同，命题92.3排除成功；零步也不能报告三个不同身份。然而首选 $a$ 的响应0、1分别确定当前1、2，首选 $b$ 的响应0、1分别确定当前2、1，故当前态的获胜秩恰为1。两个动作都分别固定当前态1和2，任何词都保持二者相异，不能把全部初态送到同一态。这区分了 homing 与 reset，也区分了两两存在区分词和存在一棵共同成功树。

粗任务中，$a$ 的响应0虽合并两个来源，却只合并同一任务标签，响应1给另一个标签；两叶均合法，所以恰一问成功。一个标签同时可能对应多个当前态并不构成失败。

三来源对“两两可区分但无共同身份识别树”的分离是最少的，限定于上述完整确定、任意时刻可正确报告、无截止的合同。单来源可立即报告；两来源若有区分词，沿该词执行直到第一次不同响应，便识别来源。它们不可能在首次不同响应以前同响应合并，否则确定性使后续再无区别。故两来源总有成功树。这个最小性不移用于有禁用动作、强制失败终止或限制报告的其它合同。证毕。

### 92.6 构造存储、后续使用与既有范围

可用来源索引的部分图 $b\mapsto s_h(b)$，以一个额外符号表示已排除来源。非空支持的这种图至多

$$
(|S|+1)^{|B|}-1
\tag{92.10}
$$

个；它映到(92.2)，足以计算全部响应纤维和报告条件。若直接枚举任意任务标签关系，其名义域至多 $2^{|K_B||S|}-1$；这是另一种幂集构造上界，不是(92.10)的同一种计数。实际可达关系可以更少，获胜部分函数又受(92.7)限制；均不由此取得最小控制器空间定理。有限关系加选定的降秩动作表给一个有限实现，但动作位置、计数器、改变中的逆解码、终止输出及工作区都须按实现分别计入；固定模型与策略表的描述成本也不能冒充运行中零成本的信息来源。

[Context Geometry 第17节](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)已有固定来源与当前态的联合条件接口，第55—56节已有一个可逆加一轨道上的取得和完整驻定控制容量；本节没有重报它们的概率创新、精确读数或容量式。[Process Geometry 第32.3节](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)已有对全部支撑合法的菜单以及非空真实后继；[Transport Memory Completion 第6.9—6.10节](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)已有读后候选的最小—最大递推和不可删去的符号解码基准。这里把这些条件放在可合并状态的初始任务取得合同中，给出共同成功树的判据和三点分离，未另求那些模型的控制容量。

Linzhe Zhang、Changming Xu，[*Certified Task-Conditioned Active Observability*, arXiv:2609.28520v1](https://arxiv.org/pdf/2609.28520v1)，§3.1、Theorem 3.1 与 Appendix A.2，直接采用有限的“固定任务标签、已推进当前态”对及标签纯的分离树。本节采用其有限确定、无噪声、单位成本专门情形；(92.1)的允许尝试、终态和报告权限另由92.1—92.3的证明处理，不把每个纯失败叶纳入该文的成功基例。Petra van den Bos、Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2)，定义12—14、17、20，提供测试树／无环测试自动机与区别观察的背景；本文没有移用其非确定系统的存在性结论。Ronald L. Rivest、Robert E. Schapire，[*Inference of Finite Automata Using Homing Sequences*](https://people.csail.mit.edu/rivest/pubs/RS89.pdf)，§3—4.1，说明到达态 homing 与 reset 的区别；其未知模型学习、teacher 和强连通假设不属于本节已知模型合同。

取得 $k(b)$ 只解决停止边界上的任务。若要在后来继续恢复空间、时间、边界、记忆的同源读数，仍用第88.7、89.4、91.8节的目标核包含／相等及执行器交换条件；取得一个初始标签不保证其自身有闭合当前更新。这里保留 $\alpha,\beta$ 为生成叶，也保留生成、语义充分与实际取得的层次区别。

## 93. Fibonacci 原子接枝的同源连续查询与剩余补偿

### 93.1 正向组成接口与目标

固定 $H\ge1$，未知实际来源一次选定为 $v\in\mathbb N^2$，包括零；实际运行始终在非负整数组成上进行。沿用 [Fibonacci Atomic Relation Generation 第130、133节](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad q=(2,3),\quad
R(v)=Mv,\quad G(v)=v+\alpha,\quad\alpha=(1,0),\quad M\alpha=\beta=(0,1).
\tag{93.1}
$$

每个物理命令是一次正向 $R$ 或 $G$；“零次”只表示省去该段。命令在全部组成上合法，没有免费响应。付费读取当前 $o_H(s)=\gcd(qs,H)$，精确且不扰动；读取、内部计算均不暗中推进来源，没有免费 $n=qv$、初始 gcd、中间读数、外部时钟或来源旁路。允许任意有限命令工作量，没有硬截止。自己的命令位置、重复计数及相应存储须保留并计费。连续模型从同一个 $v$ 开始，只使用这一份不断推进的来源。

目标是**原始** $v\bmod H$，全部组成剩余均由非负代表实际实现。对照的重置模型严格取原卷定义133.1：每问从同一个原始 $v$ 执行一个有限正向词，只读取末端，空词也收费。连续模型允许两次收费读取之间执行空词；立即重复读取没有免费信息。输出为确定性控制器根据已取得响应及自己的记录计算的剩余对。此组成合同不把零组成当成非空二元语法树；若要另行实现树上的接枝或恢复树，须增加那一层的实现条件。

### 93.2 有限剩余置换的正词逆

令 $Q_H=(\mathbb Z/H\mathbb Z)^2$、$\pi_H(s)=s\bmod H$。两生成元诱导 $\bar R(x)=Mx$、$\bar G(x)=x+\alpha$；$\det M=-1$ 使 $\bar R$ 为置换，$\bar G$ 的逆为减去 $\alpha$。固定控制器已知的 $L\ge1$，满足

$$
M^L=I\pmod H.
\tag{93.2}
$$

可以使用原卷定理130.2的有限存在界 $L=(H^2)!$：一个 $H^2$ 点置换的每个循环长度都整除该阶乘；也可以使用另行验证的矩阵阶或其倍数。$H=1$ 时 $L=1$ 即可。

对按时间从左至右执行的词 $W=a_1\cdots a_m$，定义正向补偿词

$$
\iota(R)=R^{L-1},\qquad \iota(G)=G^{H-1},\qquad
W^\dagger=\iota(a_m)\cdots\iota(a_1).
\tag{93.3}
$$

**命题 93.1（只在剩余上复原的实际执行）。** 对每个实际 $s\in\mathbb N^2$，在同一来源上执行 $W$ 再执行 $W^\dagger$，以及反向次序，都给

$$
\pi_H(W^\dagger(W(s)))=\pi_H(s),\qquad
\pi_H(W(W^\dagger(s)))=\pi_H(s).
\tag{93.4}
$$

证明。每个正向生成元满足 $\pi_H(a(s))=\bar a(\pi_H(s))$。式(93.2)给 $\bar R^{-1}=\bar R^{L-1}$，而 $\bar G^H=\operatorname{id}$ 给 $\bar G^{-1}=\bar G^{H-1}$。逆复合按反序排列，逐生成元消去得到(93.4)。所有实际中间步骤仍是非负整数上的(93.1)，取模只用于证明和控制；从未把物理状态覆盖为一个小剩余代表。证毕。

反序不能省略。例如 $H=2,L=3,s=(0,0),W=RG$，执行 $W$ 后为 $(1,0)$。正确补偿 $GR^2$ 得 $(2,2)$，模2回到 $(0,0)$；错误同序 $R^2G$ 得 $(2,1)$，模2仍为 $(0,1)$。正确词也没有把整数组成回到原点。这里补偿的是两坐标剩余的置换，既不是整数时间倒流，也不恢复树或原物理状态。

### 93.3 逐原来源、逐付费读取的双向模拟

**定理 93.2（重置与连续的准确读取等价）。** 在93.1的合同及(93.2)下，每个重置确定性协议都有一个连续协议，逐原始来源保持原协议的响应序列、虚拟查询选择、停止决定及最终答案，付费读取数完全相同。反向，每个连续协议也有这样的重置模拟。因此，以全部实际来源上原始组成剩余的精确恢复为目标，两模型的最小最坏付费读取数相等。

证明重置到连续。首次虚拟查询前，当前组成的剩余已经是 $\pi_H(v)$。归纳假设下一查询开始时也如此。虚拟协议根据旧响应选择词 $W_i$，连续控制器在当前实际组成上执行这个词，随后付费读取一次。生成元及 gcd 均只依赖剩余，故本次答恰为 $o_H(W_i(v))$，与从原始 $v$ 重问相同；即使 $W_i$ 是空词，这次读数仍收费。若原协议据此停止，就立即给相同输出；若要下一问，执行已知的 $W_i^\dagger$ 而不读取，式(93.4)把当前剩余恢复为 $\pi_H(v)$，保持归纳不变量。补偿后仍是同一份不断变化的整数来源，没有复制或重新选择初态。

相同响应使原控制器选择同一后续词、停止和输出。原协议每条有限分支只有有限多个有限词，正词补偿也有限，所以逐来源有限停止得到保持。模拟保持的是虚拟决策，不要求两种物理动作档案或停止物理时刻相同。

反向，保留连续控制器的虚拟内部记录。它第 $i$ 次读取前的全部实际正向命令串接为 $U_i$；其中包含此前各次读取之间的命令，但没有把读取当作来源变换。重置模型第 $i$ 问从同一个原始 $v$ 执行 $U_i$，只读末端。由于所有较早读取都不扰动，真实连续状态正是 $U_i(v)$，故本答完全相同。逐问归纳便保持虚拟控制记录、后续决策、停止和输出。若连续协议在末次读取后再作纯命令才停止，可在模拟控制器中完成这段确定计算与记账，不增加读取；此处目标仍是原始组成剩余。无读取的协议也按同一规则模拟。

两个方向对每个有限读取上界分别保持可行性，因而保持其最小值；若不存在统一有限界，两边也同时为 $+\infty$。反向的累计词等式明确用到了读取不扰动；不能把任意未知读后更新删掉再串接命令。证毕。

如果要求模拟结束后剩余也回到初始值，可在最后一问后再执行一次补偿，仍不增加付费读取，但会增加实际命令；该额外要求不是本定理的停止任务。仅需返回原始剩余时，不必承担这段尾部工作。

### 93.4 第133节的准确问数在连续合同中的继承

**推论 93.3（原子接枝的无重置准确问数）。** 记连续模型的最小最坏读取数为 $Q_{\mathrm{cont}}(H)$。在93.1全部条件下，原卷定理133.5、推论133.6与定理93.2给

$$
Q_{\mathrm{cont}}(1)=0,\qquad
Q_{\mathrm{cont}}(H)=Q(H)=2\max_{p^e\parallel H}e(p-1)\quad(H>1),
\qquad Q_{\mathrm{cont}}(5040)=12.
\tag{93.5}
$$

证明。原卷两阶段分别取得同一 $v$ 的 $n=qv$、$z=qMv$ 模 $H$，用同一个方向的查询词把各素数幂平移经 CRT 合成；其末端完整 gcd 不要求免费中间观察。每个这样的词可以在本节连续来源上执行并补偿，因此上界直接运输。若存在更少读取的连续策略，反向模拟给同样少读取、对每个原始非负来源都准确的重置策略，违反原卷下界，故等号成立。原卷的困难素数幂轴由一个预先固定的共同实际来源族实现；本节逐来源的模拟没有将其换成可随分支改变的来源。$H=1$ 时目标只有一个剩余对，无须读取或命令，给零。对 $5040$，各 $e(p-1)$ 为 $4,4,4,6$，故十二。证毕。

这继承的是第133节完整组成剩余任务的精确问数，不是重新证明其仿射赋值下界；第90—91节的 gcd 正未来核心任务及其七／六问不变。第91.6节的120是纯替换在 gcd 行为核心上的阶，不能代入(93.2)当成完整剩余对的矩阵阶。取得后若还需输出当前组成剩余，保留累计仿射运输 $\bar U$ 后可算 $\bar U(\pi_H(v))$；反过来用它的逆恢复初始剩余。这份随执行改变的运输或等价逆解码仍须计入存储，不由十二次读取自动赠予。

### 93.5 命令、控制记录与表示范围

对任一虚拟词，记其替换和接枝数为 $r(W),g(W)$，则上述补偿具有明确的有限工作界

$$
|W^\dagger|=(L-1)r(W)+(H-1)g(W),\qquad
|W|+|W^\dagger|=Lr(W)+Hg(W).
\tag{93.6}
$$

这是选定补偿构造的计数，没有最短词主张。用第133.2节的 $W(k,c)$，每问有 $r(W)=L+k\le L+1$、$g(W)\le2(H-1)$。于是令 $B_H=\max_{p^e\parallel H}e(p-1)$，即使末问也补偿，继承策略的正向命令总数仍有充分界

$$
2B_H\bigl(L(L+1)+2H(H-1)\bigr)\quad(H>1).
\tag{93.7}
$$

阶乘选择证明有限，未给高效执行或最优命令数。一般模拟器须保存虚拟协议状态、当前词及反序执行位置或能生成该逆序的等价控制、重复计数器、已取得前缀、响应解码与瞬时算术区；若输出还需当前端点或完整累计费用，对应运输和计数也分别保存。固定 $H,L$ 的第133节构造有有限深度、有限响应及有限词长，因而这些记录可用有限控制实现，但本节既不求其最小状态数，也不承诺对所有 $H$ 的统一有界空间。实际整数组成可持续增长，不计作观察器已经持有的精确坐标。

[Transport Memory Completion 第2节](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)已经讨论已允许逆边、已知端口的群运输与任务商；本节不新增群作用最小化理论，而是在没有物理逆命令的(93.1)中给出可实际执行的有限正词补偿，并与原卷第133节的查询合同作双向连接。Context 第55—56节和本卷第90—91节已有单置换下的等待、解码基准及端点保留；这里的 $R,G$ 可以不交换，必须反序补偿，并保留完整剩余对的条件，不能只改一个周期常数。数学上有完整行为核心与在一次执行中取得它之间的缺口，在这一组成合同下由93.2填上；破坏性动作的一般情形仍须检查92.3的获胜条件。

第92—93节以仓库修订 `7a17f87be3276fa3836f79fec963c3c13b573865` 的上述理论与具名声明为输入，是普通理论综合与明确合同下的推导，不主张新的一般数学、物理统一或新增 Lean/kernel 核验。关于空间、时间、边界和记忆，只在同一实际来源、同一目标、核判据及闭合执行器条件下回接第91.8节；本节没有恢复完整语法树、精确无界组成、绝对年龄或制备前历史，也没有完成长期的最小关系结构研究。

## 93.99 追加锚

## 94. 保留已执行运输的 Fibonacci 同源标量编译

### 94.1 连续来源与有限运输字段

本节沿用93.1的全部合同：固定一次未知实际来源 $v_0\in\mathbb N^2$，含零；当前来源 $s$ 始终是这一份来源经正向命令得到的非负整数向量。只有 $R(s)=Ms$ 与 $G(s)=s+\alpha$ 是来源命令，其中

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
q=(2,3),\qquad \alpha=(1,0),\qquad M\alpha=\beta=(0,1).
$$

每次当前 $\gcd(qs,H)$ 读取收费、精确且不扰动；命令不附送观察，读取与计算不暗中推进来源，没有免费坐标、时间侧信道或硬截止。命令重复次数及其控制存储须计费。控制器已知 $H\ge1$ 和一个充分周期 $L\ge1$，满足 $M^L\equiv I\pmod H$；不要求 $L$ 最小。目标仍是原始 $v_0\bmod H$。

在第81节的组成仿射下降与 Fibonacci 第130节的实际词归纳上，保留由自己已执行命令计算的字段

$$
r\in\mathbb Z/L\mathbb Z,\qquad t\in(\mathbb Z/H\mathbb Z)^2,
\qquad s\equiv M^r v_0+t\pmod H.
\tag{94.1}
$$

**命题 94.1（不读取坐标的运输更新）。** 初始字段为 $(r,t)=(0,0)$；逐原语更新

$$
R:(r,t)\longmapsto(r+1,Mt),\qquad
G:(r,t)\longmapsto(r,t+\alpha)
\tag{94.2}
$$

保持(94.1)，其中各字段分别取模 $L,H$。

证明。初始 $s=v_0$。若已满足(94.1)，实际执行 $R$ 给 $Ms\equiv M^{r+1}v_0+Mt$；实际执行 $G$ 给 $s+\alpha\equiv M^rv_0+t+\alpha$。因 $M^L\equiv I$，约化 $r$ 不改变等式。读取不扰动来源，故保持字段。归纳只使用命令名及旧字段；它没有测量 $s$，也没有把 $s$ 改写为模代表。证毕。

### 94.2 下一原来源测试的正词

请求用相位 $j\in\mathbb Z/L\mathbb Z$ 与平移 $c\in\mathbb Z/H\mathbb Z$ 指定原来源响应

$$
\gcd(qM^jv_0+c,H).
\tag{94.3}
$$

这里 $M^j$ 取任一非负指数代表，$c$ 取任一整数代表，gcd 因同余而与代表无关；所以也涵盖任意给定的非负整数指数与整数平移。请求可以依赖此前已付费取得的响应。所有 $\bmod$ 以下取最小非负代表。由当前字段计算

$$
\begin{aligned}
d&=(j-r)\bmod L,&u&=M^dt\bmod H,\\
c'&=(c-qu)\bmod H,&A&=(-c')\bmod H,&B&=c'.
\end{aligned}
\tag{94.4}
$$

**命题 94.2（保留运输的单问编译）。** 按时间从左至右，在当前实际 $s$ 上执行

$$
R^d,\quad G^A,\quad R^{L-1},\quad G^B,\quad R,
\tag{94.5}
$$

然后且仅然后付费读取一次，恰得(94.3)。这是先对齐线性相位，再用 Fibonacci 命题133.2已有的 $W(0,c')$；将其阶乘周期换成满足 $M^L\equiv I$ 的任意已知 $L$，原词证明仍适用。读取后字段为

$$
(r',t')=\bigl(j\bmod L,\ u+(A,B)\bmod H\bigr).
\tag{94.6}
$$

证明。直接按实际整数操作复合，终态严格等于

$$
s'=M^{d+L}s+A M^L\alpha+B M\alpha\in\mathbb N^2.
\tag{94.7}
$$

这里等式在整数上成立，未把 $M^L$ 当作整数单位矩阵。取模后，(94.1)及 $d+r\equiv j\pmod L$ 给

$$
\begin{aligned}
s'&\equiv M^jv_0+u+A\alpha+B\beta,\\
qs'&\equiv qM^jv_0+qu+2A+3B
     \equiv qM^jv_0+qu+c'
     \equiv qM^jv_0+c\pmod H.
\end{aligned}
\tag{94.8}
$$

整数同余给与 $H$ 相同的 gcd；读后不扰动，故(94.6)可继续使用。$A,B,d$ 非负，全部中间命令均合法，$c-qu$ 的减法只在控制器的剩余运算中进行。即使 $c'=0$，本构造也保留字面的 $R^{L-1},R$，从而恰计 $L$ 次替换；此时没有接枝。证毕。

### 94.3 自适应同源保持与逐分支计数

**定理 94.3（原来源标量协议的在线执行）。** 对任一仅按已付费响应选择下一 $(j,c)$ 的确定性标量协议，逐次使用(94.4)—(94.5)，就在一份持续推进的实际来源上保持全部虚拟查询、响应、停止决定及原答案。每次虚拟测试对应恰一次实际付费读取。原协议在某来源上有限停止时，编译后也有限停止，无须在末尾复原来源剩余。

证明。固定一个实际 $v_0$，从空响应历史开始归纳。两个控制器的虚拟协议状态相同；若已决定停止，输出同一答案。否则相同历史给相同请求 $(j,c)$，当前实际来源与自己的字段满足(94.1)，命题94.2给这一原来源的准确响应，并保持下一次所需不变量。故虚拟协议状态再次相同。每问仅增加有限个正向命令和一次读取，因而保持逐来源有限停止。归纳全过程使用同一个 $v_0$，不按分支另选来源，也不执行物理重置。保持的是协议决策与响应，不是物理动作档案或停止的物理时刻。证毕。

对一条有 $Q$ 次读取的有限实际分支，令 $d_i,c'_i$ 为该次编译的值，$N_R,N_G$ 为执行的原语数。字面保留零平移的 $R^L$ 块给准确计数

$$
\begin{aligned}
N_R&=QL+\sum_{i=1}^{Q}d_i,\\
N_G&=H\,\bigl|\{i:1\le i\le Q,\ c'_i\ne0\}\bigr|\le QH.
\end{aligned}
\tag{94.9}
$$

因为 $c'_i=0$ 时 $A_i+B_i=0$，否则 $A_i=H-c'_i$、$B_i=c'_i$，和恰为 $H$。空分支的和为零。省去零平移时的 $R^L$ 可进一步减少命令，但(94.9)的等号专用于保留该块的版本。这里没有第93节每问后的逆词重放；有限运输字段也不意味着任意虚拟协议都有有限总存储或统一停止界。

### 94.4 两阶段取得的充分命令界

令 $H>1$，并记

$$
B_H=\max_{p^e\parallel H}e(p-1).
$$

采用 Fibonacci 第133.2—133.3节的完整策略：先固定共同相位 $j=0$，在各素数幂上按既有逐位过程选择局部平移，以 CRT 合成每轮一个 $c$，取得 $n=qv_0\bmod H$；再固定共同相位 $j=1$ 取得 $z=qMv_0\bmod H$。已完成轴使用已知饱和平移，两阶段所有响应仍属于同一实际来源。输出

$$
v_0\equiv(5n-3z,\,-3n+2z)\pmod H.
\tag{94.10}
$$

**推论 94.4（两阶段的相位费用只付一次）。** 上述具体策略的任一实际分支都有 $Q\le2B_H$，编译后的原语满足

$$
\sum_i d_i=1,\qquad
N_R=QL+1,\qquad N_G\le QH,\qquad
N_R+N_G\le2B_H(L+H)+1.
\tag{94.11}
$$

证明。第133节的逐位策略每阶段从零个已知位开始；$H>1$ 时至少有一根非平凡素数幂轴，其首位至少需要一次测试，故两个阶段均有读取。又 $M\not\equiv I\pmod H$，所以满足合同的 $L>1$。初始 $r=0$，第一阶段每问后仍有 $r=0$，故各 $d_i=0$。进入第二阶段的第一问有 $d_i=(1-0)\bmod L=1$，其后 $r=1$，余下各问的 $d_i=0$。第133节每阶段至多 $B_H$ 轮；代入(94.9)即得(94.11)。$H=1$ 则直接输出唯一剩余对，不读也不执行命令，三项费用均为零。证毕。

最小最坏读取数 $2B_H$ 继承自 Fibonacci 定理133.5与本卷定理93.2—推论93.3；本节只为其两阶段实现给出上述命令保证，没有新的查询最优性证明或命令最优性结论。式(93.7)仍是旧补偿实现的有效充分界。比较两式是在同一合同、同一 $L$ 下比较构造保证，不从上界差推断每个来源上的实际加速。

### 94.5 模5040的充分周期证书与界值

对 $H=5040$，可取 $L=240$。由 $M$ 的递推先算 $M^{15}$，然后逐次平方；下列各式均在模5040下：

$$
\begin{aligned}
M^{15}&\equiv\begin{pmatrix}377&610\\610&987\end{pmatrix},&
M^{30}&\equiv\begin{pmatrix}149&440\\440&589\end{pmatrix},\\
M^{60}&\equiv\begin{pmatrix}4121&2160\\2160&1241\end{pmatrix},&
M^{120}&\equiv\begin{pmatrix}1441&0\\0&1441\end{pmatrix},\\
M^{240}&\equiv I.
\end{aligned}
\tag{94.12}
$$

每个后项是前项的平方约化，最后用 $1441^2\equiv1\pmod{5040}$。这证明240是充分周期，不声称其最小性。$1441\not\equiv1\pmod{5040}$ 已排除把120直接用于(94.1)的完整剩余运输；第91.6节的120仍只承担其 gcd 正未来核心的周期。

此处 $B_{5040}=\max(4,4,4,6)=6$，故每条实际分支同时满足

$$
Q\le12,\qquad N_R\le2881,\qquad N_G\le60480,\qquad
N_R+N_G\le63361.
\tag{94.13}
$$

相同 $L=240$ 代入旧式(93.7)为

$$
12\bigl(240\cdot241+2\cdot5040\cdot5039\bigr)=610211520.
\tag{94.14}
$$

式(94.13)是对每个共同实际分支成立的上界，故可以相加；未声称 $N_R,N_G$ 的各自上界同时取到，也未从数值比较取得运行时间、最短词或物理效率结论。

### 94.6 运输存储与取得后的双向恢复

对固定 $H,L$，用分字段二进制编码保存 $r,t_1,t_2$，可为这些字段分配

$$
\lceil\log_2L\rceil+2\lceil\log_2H\rceil
\tag{94.15}
$$

位；大小为1的域取零位。这是本构造的字段预算，不是最小控制器容量，也不包括固定模型常量及程序描述、虚拟协议状态、阶段、循环计数器、CRT 前缀、响应解码、临时算术区或累计费用。模5040、$L=240$ 时该分配为 $8+2\cdot13=34$ 位，仅指这三个字段。无需保存完整逆词档案或整张剩余置换表；$M^dt\bmod H$ 可由已知矩阵的有限模运算生成，其运算和工作区仍须计入。

在本节两阶段消费者的已完成查询边界上，$r$ 就是上一已完成查询的阶段值：第一阶段为0，第二阶段为1。阶段转移控制保留这一区别时可复用该字段，不必再存一份 $r$；进入第二阶段前的待查询状态与第二阶段已有完成查询的状态仍须分清。执行词内部的命令位置、重复计数及临时更新不因此免费。对固定 $H,L$，两阶段的读取深度和每问词长均有上界，且响应集有限，所以其整个控制过程存在有限实现；该结论不扩展到任意无限或无界存储的虚拟协议。

若已取得某一端的组成剩余，且保留收费核算的运输字段或等价解码资料，则在取得时及随后有记录的执行中，可以计算

$$
x_{\mathrm{now}}=M^rx_0+t,\qquad
x_0=M^{(-r)\bmod L}(x_{\mathrm{now}}-t)
\quad\text{于 }(\mathbb Z/H\mathbb Z)^2.
\tag{94.16}
$$

逆式只是剩余解码，没有执行负命令；字段自身也没有取得未知 $x_0$ 或 $x_{\mathrm{now}}$。这里的有限相位不恢复完整圈数、绝对时钟、制备前历史或语法树。要把空间、时间、边界与记忆接成同一目标的互恢复，仍须满足第81、90—91节已有的实际像、目标核及更新交换条件。

### 94.7 实际整数增长与工作层次

**命题 94.5（实际组成的充分宽度）。** 令 $S_0=(v_0)_1+(v_0)_2$，一段实际执行含 $N_R$ 次 $R$、$N_G$ 次 $G$。则末态坐标和满足

$$
S_{\mathrm{end}}\le2^{N_R}(S_0+N_G).
\tag{94.17}
$$

每个实际组成坐标及坐标和，都可使用以下安全非负整数二进制宽度；它也覆盖这段执行的每个前缀：

$$
1+N_R+\left\lceil\log_2(S_0+N_G+1)\right\rceil.
\tag{94.18}
$$

证明。对当前非负坐标 $(a,b)$，$R$ 将和 $a+b$ 变为 $a+2b\le2(a+b)$，$G$ 将和加一。对前缀中的计数 $r_*,g_*$ 归纳保持 $S\le2^{r_*}(S_0+g_*)$：$R$ 步将右侧乘二；$G$ 步用 $1\le2^{r_*}$。终点给(94.17)，每个前缀的计数不超过总计数，故同一总界适用。置 $X=S_0+N_G$，有 $X<2^{\lceil\log_2(X+1)\rceil}$；乘以 $2^{N_R}$ 后即可用(94.18)编码，并在全零情形保留一位。证毕。

由于 $S_0$ 无界，单凭 $H$ 不能界定精确来源所需的位数；模 $H$ 相同的非负来源可有任意大的初始坐标。本节的控制器不因保留运输便持有这些精确整数。实际二进制加法与矩阵作用、传感器形成 $qs$ 并求 gcd 的成本、控制器模算术各须按自己的数值宽度和实现计费；(94.18)没有给它们统一的精确位运算时间公式。

若在第81节的树模型中实现 $R$，它表示整树替换，$G$ 还需合法提供原子旁支；非空树本身不实现零组成。一次组成原语不等于常数次局部树改写。显式树的节点生成、遍历和保存工作，以及真实装置的时间、等待和读取成本，都未由 $N_R+N_G$ 或有限字段位数界定。

### 94.8 所据结果与结论范围

来源固定为仓库修订 `a6d75172f480affc187464a44804b58a172c5de6`：本卷第81节承担动作词的组成仿射下降，第90—91节承担同源等待、运输与任务容量的既有区分，第93节承担连续合同、正词补偿及读取最优值的继承；[Fibonacci Atomic Relation Generation](FIBONACCI_ATOMIC_RELATION_GENERATION.md)第130节提供实际正词与完整剩余商，第133节提供标量测试词、共同方向的 CRT 两阶段策略及其问数。

本节的增量是将已执行的 $(r,t)$ 直接用于下一原来源测试的平移修正，给出整数端点、逐响应同源保持和该两阶段消费者的充分原语界。它是上述明确合同下的仓库综合推导，没有另立一般仿射或群理论、状态容量定理、查询最优性结果或原创优先权。正文未作新增 Lean/kernel 核验或消化结算；公式证明与有界数值核对不替代形式认证。更一般的最小关系结构、完整树及无界精确来源恢复、绝对时间和物理统一均不由本节取得。

## 94.99 追加锚

## 95. 未记录替换下的自主关系与实际 gcd 取得边界

第94节的运输不变量要求来源的每次变化都有记录。本节允许指定替换在命令间无记录地发生，分别求出仍能自主更新的最细语义关系，以及原 gcd 接口实际能够取得什么。Fibonacci 卷第33、38节已有缺陷群与 Smith 分解，第130—133节已有接枝闭包和收费取得；这里复用这些机制，补上隐藏事件与单份实际来源之间的条件。以下是普通数学推导，未作新增 Lean/kernel 核验。

### 95.1 原语之间的隐藏事件与来源合同

固定已知整数 $H\ge1$、$d\ge1$，一次执行开始时选定未知实际来源 $s_0\in\mathbb N^2$，自然数包含零。当前 $s$ 始终是这一份来源经下列实际非负整数操作得到的向量：

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
\alpha=(1,0),\quad\beta=M\alpha=(0,1),\quad q=(2,3),
\qquad R(s)=Ms,\quad G(s)=s+\alpha,\quad E(s)=M^ds.
\tag{95.1}
$$

$R,G$ 是控制器知道已经完成的命令；$E$ 是不报告的隐藏事件。在已完成的原子原语之间以及每次读取之前，允许任意有限非负批数 $E^k$，包括零批。原子原语只指一次 $R$、一次 $G$ 或一次读取，复合正词不是原子操作；单个原语或读取内部没有隐藏步。每次读取付费、精确、不扰动，返回当时的 $o_H(s)=\gcd(qs,H)$，包括 $\gcd(0,H)=H$。完成信号只标记该原语完成，不携带历时、整数大小或错误批数。没有时钟、错误日志、坐标读出、大小侧信道或免费中间观察；本地记录可以保存自己的全部命令与已付费响应，但不能读取隐藏日程。

所有已请求原语完成、每个间隙只有有限批事件，是本节执行合同的一部分，不是本节证明的调度公平性或性能结论。隐藏批数不受统一上界限制。控制器只能使用上述完成和响应作决定；等待本身不增加可见资料。这里没有把未知当前整数替换为较小的模代表。

记 $V=(\mathbb Z/H\mathbb Z)^2$，并沿用 $M,E,R,G$ 表示它们的模作用。$V$ 只是实际来源的语义投影：每个剩余向量都有一个预先选定的非负整数提升，选定后始终沿该实际来源执行。全部 $s_0$ 都在范围内；不假设某个确切 $n=qs_0$ 的来源纤维在 $R,G,E$ 下不变。若改成受限制备或另给初始资料，以下全来源最细性和取得不可能性须重新检查。

### 95.2 最细的误差不变自主商

本节先只要求一个当前态表示 $\eta:V\to B$ 满足

$$
\eta R=\bar R\eta,\qquad
\eta G=\bar G\eta,\qquad
\eta E=\eta,
\tag{95.2}
$$

其中 $\bar R,\bar G$ 是实际像 $\eta[V]$ 上的确定更新。此处不要求从 $\eta$ 解码传感器响应，也不假设 $B$ 是群或 $\eta$ 线性。称其为误差不变自主表示；它只依赖当前剩余，不包含额外历史。令

$$
N=(E-I)V=(M^d-I)V,\qquad
\pi:V\longrightarrow V/N.
\tag{95.3}
$$

**定理 95.1（受控原子接枝迫使余不变量关系）。** 对任意满足(95.2)的表示，都有

$$
x-y\in N\ \Longrightarrow\ \eta(x)=\eta(y).
\tag{95.4}
$$

因而存在唯一满射 $f:V/N\to\eta[V]$，使 $\eta=f\pi$。$\pi$ 自己满足(95.2)，其诱导操作为 $[x]\mapsto[Mx]$、$[x]\mapsto[x+\alpha]$。所以模 $N$ 的同余是这些表示中最细的相等核；这里“最细”表示保留最多可自主更新且不受隐藏事件影响的当前态区别，不是最少传感器次数。

证明。写 $x\sim y$ 当且仅当 $\eta(x)=\eta(y)$。由(95.2)，此关系在 $R,G$ 下保持。它也在这两个模置换的逆下保持：$V$ 有限，$M$ 可逆，故某个正整数 $L$ 满足 $M^L=I$；$G^H=I$。因此逆分别等于 $R^{L-1}$、$G^{H-1}$，反复使用关系保持性即可。共轭 $RGR^{-1}$ 是平移 $x\mapsto x+\beta$；$G$ 是 $\alpha$ 平移。这两向及其逆生成 $V$ 的全部平移，所以 $\sim$ 是平移不变的等价关系。

置 $K=\{z:z\sim0\}$。平移不变性给 $x\sim y$ 当且仅当 $x-y\in K$；若 $u,v\in K$，则 $u+v\sim v\sim0$，且 $-u\sim0$，故 $K$ 是加法子群。由 $Ex\sim x$ 得 $(E-I)x\in K$，于是 $N\subseteq K$，证明(95.4)。令 $f([x])=\eta(x)$ 即良定义、满射且唯一。

另一方面，$M$ 与 $E-I$ 交换且 $MV=V$，故 $MN=N$。模 $N$ 的相等在 $M$ 及任意平移下保持，且 $Ex-x\in N$，所以 $\pi$ 确实具有所述更新和误差不变性。$H=1$ 时同一证明给单点商。证毕。

证明中用有限置换的逆，只是在相等关系上作代数推理。若在物理执行的 $R^{L-1}$ 各步间插入未知 $E$，它不自动抵消实际来源的既有误差；整数来源也没有因模周期而回返。因此这段证明不提供免费的物理逆协议。$V/N$ 是经典余不变量商；缺陷矩阵的计算复用 [Fibonacci 第33、38节](FIBONACCI_ATOMIC_RELATION_GENERATION.md)，不是新的一般同余或 Smith 定理。

任意历史／候选集合观察者不必是当前态映射 $\eta$，传感器读数也未被要求经 $\eta$ 下降。因此定理95.1既不是这类观察者的容量下界，也不是完整传感器行为商；特别不能由其因子化直接推出某个协议已经取得 $\pi(s)$。

### 95.3 几个足以分开情形的缺陷

以下直接使用已有整数缺陷的模约化：若 $E-I$ 的 Smith 因子为 $s_1,s_2$，则

$$
V/N\cong
\mathbb Z/\gcd(H,s_1)\mathbb Z
\oplus
\mathbb Z/\gcd(H,s_2)\mathbb Z.
\tag{95.5}
$$

其依据是第33节的 $\mathbb Z^2/((E-I)\mathbb Z^2+H\mathbb Z^2)$ 及 Smith 坐标逐轴约化；同一个公式也涵盖合数 $H$，无需重新证明标准形。

- $d=1$ 时 $\det(M-I)=-1$，$d=2$ 时 $M^2-I=M$。两者都整数可逆，故 $N=V$，自主商为单点。
- $d=3$ 时 $M^3-I=2M$，故 $N=2V$，商为 $(\mathbb Z/\gcd(H,2)\mathbb Z)^2$。
- $d=4$ 时 $M^4-I=\begin{pmatrix}1&3\\3&4\end{pmatrix}$，Smith 因子为 $(1,5)$，正是 Fibonacci 第38节的四步缺陷；商为 $\mathbb Z/\gcd(H,5)\mathbb Z$。
- $H=5040,d=120$ 时，式(94.12)给 $E\equiv1441I$，故 $N=1440V=720V$，商为 $(\mathbb Z/720\mathbb Z)^2$。这是同一来源的完整组成剩余商计算，不把 gcd 正未来的120周期当成完整模5040恒等。

这四项分别展示完全塌缩、共同坐标保留、斜向关系保留和既有大模数实例；它们不改变定理95.1的全参数陈述。

### 95.4 共同坐标模数上的正向取得桥

定义正整数

$$
D=\gcd\bigl(H,(E-I)_{11},(E-I)_{12},(E-I)_{21},(E-I)_{22}\bigr).
\tag{95.6}
$$

对任意 $h\mid H$，$E\equiv I\pmod h$ 当且仅当 $h$ 整除 $E-I$ 的所有矩阵项，亦即 $h\mid D$。所以 $D$ 是使隐藏事件在完整两坐标上恒等的最大共同约化模数。$N$ 包含于模 $D$ 约化的核，因此 $V/N$ 决定 $s\bmod D$；反向不普遍成立，下一节给 $D=1$ 而 $V/N$ 非平凡的实例。

**命题 95.2（带隐藏事件的共同坐标取得）。** 在95.1的实际来源合同下，可仅使用原 gcd 传感器与已声明正向命令，确定性地取得初始 $s_0\bmod D$。当 $D>1$，记

$$
B_D=\max_{p^e\parallel D}e(p-1),\qquad M^{L_D}\equiv I\pmod D,
\tag{95.7}
$$

其中 $L_D\ge1$ 是已知充分周期；例如有限置换给出 $L_D=(D^2)!$。存在实现，对每个来源及每份允许隐藏日程都有

$$
Q\le2B_D,\qquad
N_R+N_G\le2B_D(L_D+D)+1.
\tag{95.8}
$$

这里只数付费读取和自己命令的原语数。$D=1$ 时唯一剩余对已知，零读取、零命令即可。

证明。一次实际读取的响应 $y=\gcd(qs,H)$ 可作本地后处理

$$
\gcd(y,D)=\gcd(\gcd(qs,H),D)=\gcd(qs,D),
\tag{95.9}
$$

因为 $D\mid H$。这没有取得免费读数，而是对已经付费的同一响应再求 gcd。模 $D$ 时，每个隐藏批 $E^k$ 都是恒等，即使发生于复合正词内部的两个原语之间，也不改变模投影。令控制器仅按自己完成的 $R,G$ 更新第94节的字段 $(r,t)$，分别取模 $L_D,D$；初始取 $(0,0)$。逐事件归纳得到

$$
s\equiv M^r s_0+t\pmod D:
\quad R:(r,t)\mapsto(r+1,Mt),\quad
G:(r,t)\mapsto(r,t+\alpha),\quad E^k:(r,t)\mapsto(r,t).
\tag{95.10}
$$

读取不扰动，故也保持该式。第94.2—94.4节的正词编译及 Fibonacci 第133.2—133.3节的两阶段策略遂能原样在模 $D$ 上执行：先取得 $qs_0$，再取得 $qMs_0$，用 $(n,z)\mapsto(5n-3z,-3n+2z)$ 恢复组成剩余。每次后处理响应与该同一初始来源的虚拟测试严格相等，允许按此前响应自适应选下一请求。式(94.11)以 $H,L$ 换成 $D,L_D$ 就给(95.8)。有限个命令与读取之间只有有限隐藏批，且原语按合同完成，故该实现有限结束。证毕。

这是充分界。完整 gcd 模 $H$ 响应可能比(95.9)携带更多信息，所以不把原无隐藏合同的最优问数移植为此处的下界。隐藏替换次数、实际整数增长与每次读取的算术宽度不在(95.8)内；这些成本没有统一界，不能沿用94.7只计已命令 $N_R$ 的增长或运行时间保证。保留运输字段及策略、阶段、循环计数和本地运算仍须按第94.6节分别收费。

### 95.5 模五上的斜向幸存关系

取 $H=5,d=4$，在 $\mathbb F_5^2$ 上令

$$
c=\ell(s)=2a+b,\qquad r=q(s)=2a+3b.
\tag{95.11}
$$

这两个是联合坐标，不是两个已取得的传感器值。矩阵 $\begin{pmatrix}2&1\\2&3\end{pmatrix}$ 的行列式为 $4\ne0$，故 $(a,b)\leftrightarrow(c,r)$ 可逆；具体逆为 $a=2c+r$、$b=3r-3c$，均在模五中。直接代入(95.1)得

$$
R(c,r)=(3c,c+3r),\qquad
G(c,r)=(c+2,r+2),\qquad
E(c,r)=(c,r+3c).
\tag{95.12}
$$

$E-I$ 的像在这些坐标中恰为 $\{(0,r):r\in\mathbb F_5\}$，所以 $N=\ker\ell$，$V/N\cong\mathbb F_5$，商标签就是 $c$。同时矩阵 $M^4-I$ 含有项1，故 $D=1$。两完整坐标都不能以非平凡共同模数保留，但斜向关系 $2a+b\bmod5$ 仍自主更新；它不等于单独 $a$ 或单独 $b$ 的约化。

原传感器只返回

$$
o_5(s)=\begin{cases}5,&r=0,\\1,&r\ne0.\end{cases}
\tag{95.13}
$$

它不经 $c$ 下降：实际来源 $(0,0)$ 与 $(1,3)$ 都有 $c=0$，响应却分别为5与1；将前者换成非零的 $(5,5)$ 仍成立。反向，同样的响应1也可以对应不同 $c$，例如 $(0,1)$ 与 $(0,2)$。所以商标签与单次原始读数不是同一接口。以下进一步处理任意确定性历史协议，不能仅靠这两个单次碰撞宣布取得不可能。

### 95.6 五个固定来源的共同转录障碍

**定理 95.3（斜向初始标签不能保证有限取得）。** 在95.1的 $H=5,d=4$ 合同下，不存在仅用所声明命令、传感器及任意历史记忆的确定性协议，使其对每个实际初始来源、每份允许隐藏日程都在有限执行后准确输出 $c_0=\ell(s_0)$。即使只准许在读取之前插入隐藏事件，且每次批数至多四，结论仍成立。

证明。预先固定五个非零实际来源

$$
s_i=(0,i+5),\qquad i=0,1,2,3,4.
\tag{95.14}
$$

它们各自的初始标签是 $i$；这五份执行从始至终分别使用自己的 $s_i$，不在归纳步骤中替换来源。构造一个共同可见转录，使五个来源都有一份实际隐藏日程实现它。空转录时控制器的已知信息和初始程序状态相同。沿共同转录，全部自己命令相同，式(95.12)使当前五个标签始终形如

$$
c_i=u i+t,\qquad u\in\mathbb F_5^\times,\quad t\in\mathbb F_5,
\tag{95.15}
$$

初始 $(u,t)=(1,0)$。已命令 $R$ 把它改为 $(3u,3t)$，$G$ 改为 $(u,t+2)$；隐藏 $E$ 不改 $c_i$。因此每个读取之前恰有一个下标 $i_*$ 的当前 $c_{i_*}=0$。

维持各来源当前实际整数向量。若下一决定是命令，就让五份执行完成该同一命令，其前后均选零隐藏批；(95.15)保持。若下一决定是读取，先取零标签见证 $i_*$ 此刻的真实响应 $y\in\{1,5\}$。隐藏事件在其 $c=0$ 纤维上固定模五的 $r$，故这份响应不能随意选择，但确有这一个实际 $y$。

对另四个见证，当前 $c_i\ne0$，所以在读取前插入 $E^{k_i}$ 会把

$$
r_i\longmapsto r_i+3k_i c_i,\qquad k_i\in\{0,1,2,3,4\},
\tag{95.16}
$$

遍历全部五个剩余。若 $y=5$ 就取使其为零的 $k_i$；若 $y=1$ 就取使其为任一非零剩余的 $k_i$。给 $i_*$ 取零批。于是五份实际执行都返回同一个 $y$。每个 $k_i$ 有限且不超过四；实际操作是非负整数矩阵 $M^{4k_i}$，所以得到真实非负来源后继。读取不扰动，它们的实际后继可继续用于下一归纳步。

控制器的全部历史、内存、命令完成和响应均相同，确定性使下一决定相同。由此逐步延长共同转录，始终保留原来五个固定来源。若协议在这条转录上有限停止，其输出只能是一个共同值，却被要求分别等于五个不同的初始标签，矛盾。若从不停止，所构造的每份无限日程在每个间隙至多四批且每个请求均完成，给出合法的不终止执行，也违背逐日程有限结束；若协议停留在永不结束的本地计算，同样已经违反有限结束要求。证毕。

这个证明未假设某个候选纤维在每个 $R/G$/读出下都变成整个下一纤维。零 $c$ 纤维的响应不能由 $E$ 任意调整，正是先取该固定见证的实际响应，再耦合另四份执行的原因。也没有用一串只分别可实现的有限前缀冒充同一来源的完整历史：每步从该来源此前保留的真实后继继续，因而每个索引都得到一份相容的完整日程。不同见证允许不同隐藏日程，因为协议要求对每份允许日程正确；它们不被解释为一个物理系统同时具有五个来源。

定理95.3允许无限制的确定性历史存储，故障碍不是字段太少，而是声明接口在这些日程下不能提供标签区别。它不涉及随机协议的几乎处处或期望终止，也没有把隐藏批数变为随机独立噪声；这些是另一个合同。隐藏事件若只允许于更少时刻，或提供额外时间／大小读数，必须另行分析。

### 95.7 已取得端点与保留运输的相互恢复

在同一模五合同中，控制器可以从自己的命令维护 $(u,t)$，初始 $(1,0)$，更新为

$$
R:(u,t)\mapsto(3u,3t),\qquad
G:(u,t)\mapsto(u,t+2),\qquad
E^k:(u,t)\mapsto(u,t).
\tag{95.17}
$$

于是对每条实际执行都有

$$
c_{\mathrm{now}}=u c_0+t,\qquad
c_0=u^{-1}(c_{\mathrm{now}}-t).
\tag{95.18}
$$

证明只需按事件归纳使用(95.12)；$u$ 始终非零，故逆式良定义。若一个端点标签已经实际提供，并保留这些运输资料，两式就互相恢复初始和当前端点。仅知道 $(u,t)$ 没有提供任一未知端点。进一步，任何在原接口上保证有限取得当前 $c_{\mathrm{now}}$ 的协议，都可额外记录(95.17)并用逆式取得 $c_0$，与定理95.3矛盾；这里已允许任意历史存储，额外记录不超出其范围。

若改变接口，另外提供一次精确当前 $c$ 读取，并将它也规定为付费、不扰动、读取内部无隐藏步，则这一次读取配合保留的 $(u,t)$ 足以解码两端。它是新增传感器条件下的充分构造，不是原 gcd 响应的后处理；也没有证明最小运输字段、最佳读取数或最小取得工作区。

本例中的当前空间关系是 $2a+b\bmod5$，自主边界是它的余不变量类，路径资料是已命令的仿射运输，记忆保存运输及已经取得的端点。式(95.18)精确给出这些表达在何种联合资料下互相恢复。隐藏事件的次数、完整经过时间、整数来源和整棵语法树不由它恢复。空间关系、路径和记忆各自单独都不被宣称为其他所有表达；还须有实际取得桥，才能接回第91.8节的同源目标核和更新交换条件。

### 95.8 既有结果、来源与保留的研究边界

本节所据第90—94节的实际来源、付费当前传感器、运输与正词编译见本卷；缺陷矩阵和有限精度余核见 [Fibonacci Atomic Relation Generation 第33、38节](FIBONACCI_ATOMIC_RELATION_GENERATION.md)，实际接枝和取得见同卷第130—133节。上游第149—151节讨论的是五窗表示、共轭坐标与紧性边界；精确编码或注入格表示不会自行供应本节缺少的 gcd 传感器取得桥。

[Transport Memory Completion 第7、9—11节](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)已经区分已知调度、隐藏调度族、原始末读、补充标签及共同日程下的恢复。那些章节保留了各自的时钟端口和终端接口，不能把其可用时刻或标签免费接入95.1。本节也不重作一般隐藏调度容量公式；增量是具体 $M^d$ 缺陷与原子接枝的自主同余、共同模数上的实际正向取得，以及模五五个固定来源的阻碍证明。

仓内 [EffectiveImageKernelCriterion](../../../D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean) 给实际像上的核包含与因子化地址；[ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) 的 `controlled_behavior_universal_property` 还要求读出交织。95.2没有该传感器交织假设，95.5已给其失败实例，所以不能把这一定理作为本节余不变量商已经具有完整行为的证据。这些是已存在代码的适用范围说明，不是本节的新 Lean 应用、编译或冻结声明。

Petra van den Bos 与 Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*](https://arxiv.org/abs/1907.11034)，只用作对抗式状态识别的文献背景；这里核对的是原始摘要页题名与作者，没有从未核对的定理正文推断本算术实例。余不变量、缺陷群、Smith 约化和观察纤维论证均为成熟方法；本节是仓库特定合同下的综合推导，不作新的一般理论或原创优先权主张。

命题95.2给出共同坐标模数的充分取得桥，定理95.3严格限定一个实际斜向商无法由原接口保证有限取得的情形；二者没有分类所有 $H,d$ 的可取得任务，没有给一般隐藏日程下的最优费用，也没有完成长期的最小关系结构研究。全部新增结论仍是理论正文及所列证明，未作 Lean 核验或消化结算，不主张物理统一。

## 95.99 追加锚

## 96. 奇素数幂反射的全类固定源障碍

第95节的模五结果区分了幸存的斜向余不变量与实际取得。本节加入一族不同的奇数 $d$、奇素数幂反射障碍，使用已有原语之后的 $G$ 前切口，并把“一个类有一个见证”与“观察者已经取得该类”严格分开。这里的隐藏事件仍按第95.1节的实际来源合同发生：来源是一份固定的非负整数向量，$R=M$、$G=+\alpha$ 和每次读取都继续作用在这份来源的当前后继上；不把当前向量替换成新的模代表。读取付费、精确且不扰动，隐藏事件没有时钟、大小或次数读数。

### 96.1 反射合同与全类结论

固定奇素数 $p$、整数 $e\ge1$ 和奇数 $d\ge1$，置

$$
H=p^e,\qquad E=M^d,\qquad
V_H=(\mathbb Z/H\mathbb Z)^2,\qquad
Q_H=V_H/(E-I)V_H.
\tag{96.1}
$$

假设

$$
 p\mid\det(E-I).
\tag{96.2}
$$

沿用第95.1节的传感器 $q=(2,3)$ 和三个实际操作。控制器是任意确定性的历史协议，初始控制记忆相同，可以保存全部已经取得的命令和响应；没有免费时间、复位、大小信号或预装的来源相关资料。每个原子命令之间以及每次读取之前可插入隐藏的 $E$ 批。以下构造只使用第95.1节允许日程中的一个对抗性子族：每个实际使用的切口至多插入一次 $E$；若协议的第一个原语是 $R$ 或 $G$，则在这个首原语之前不插入；所有 $R$ 之前均不插入；在已经执行过至少一个原语之后的每个 $G$ 前，以及任何读取（包括首原语为读取时的第一次读取）前可以插入一次。读取内部没有隐藏事件。这些日程由对手选择，观察者不能选择隐藏事件；在这个子族上已无法保证完成的任务，在完整的第95.1节允许日程族上也无法保证完成。

**定理 96.1（奇素数幂的全类固定源障碍）。** 在上述合同下，可以预先为 $Q_H$ 的每个完整类 $x$ 选择一个固定的非负整数来源 $s_x$，选择与控制器无关，并使其模 $p$ 的反射坐标满足下文的归一化条件。对任意确定性协议和任意类 $x$，在同一份固定来源 $s_x$ 上存在一份满足切口合同的隐藏日程，使协议得到的每一次读取都等于 $1$。因此，若 $f:Q_H\to Y$ 非恒定，则不存在一个协议对每个实际来源和每份允许日程都保证有限终止并正确输出 $f([s_0])$。

量词中的日程可以随 $x$ 改变；定理没有声称所有类共用一个隐藏事件序列。固定的是每一类的实际来源，以及该来源在整条执行中的连续后继。

### 96.2 模 $p$ 的反射共轭

**引理 96.2（负特征线与可观测性）。** 在 $\mathbb F_p$ 上，$E$ 有一维的 $+1$ 特征线和一维的 $-1$ 特征线。存在非零左特征形式 $w$ 及非零标量倍数，使

$$
 wE=-w,\qquad w(\alpha)=1,\qquad wM=\mu w
\quad(\mu\in\mathbb F_p^\times).
\tag{96.3}
$$

并且 $q$ 在 $E$ 的负特征线上不恒为零；换言之，对任意非零负特征向量 $v$，$qv\ne0$。

**证明。** $\det M=-1$，而 $d$ 奇，所以 $\det E=-1$。由 (96.2) 及二维行列式恒等式

$$
\det(E-I)=1-\operatorname{tr}(E)+\det(E)=-\operatorname{tr}(E)
$$

得 $\operatorname{tr}(E)=0$。Cayley–Hamilton 因而给出 $E^2=I$。由于 $p$ 奇，$+1$ 与 $-1$ 不同，两个特征空间各为一维。

$M$ 与 $E$ 交换，故 $M$ 保持两条特征线。若 $\alpha$ 落在 $+1$ 线，则 $M\alpha$ 也在该线，和精确的行列式恒等式 $\det[\alpha,M\alpha]=1$ 矛盾。因此 $\alpha$ 在负线上的分量非零，负线上的左特征形式可缩放为 $w(\alpha)=1$；$M$ 在该线上的作用是某个非零标量 $\mu$，得到 (96.3)。

若 $q$ 在负线恒为零，则 $qM$ 也在负线上恒为零，因为 $M$ 保持负线。于是 $q$ 与 $qM$ 的共同核含有非零向量，和

$$
\det\begin{pmatrix}2&3\\3&5\end{pmatrix}=1
$$

矛盾。这证明传感器在负线上非零。证毕。

### 96.3 每个完整商类的归一化实际来源

对 $z\in V_H$，将 $w(z)$ 先约化到 $\mathbb F_p$。由于 $2$ 在 $\mathbb F_p$ 中可逆，取唯一的

$$
 k\equiv\frac{w(z)-1}{2}\pmod p,\qquad
 r=z+k(E-I)\alpha\pmod H.
\tag{96.4}
$$

这里把 $k$ 视为模 $p^e$ 的一个固定提升。由 $wE=-w$ 和 $w(\alpha)=1$，有

$$
 w((E-I)\alpha)=-2,\qquad w(r)=w(z)-2k=1.
\tag{96.5}
$$

同时 $r-z\in(E-I)V_H$，所以 $r$ 与 $z$ 属于同一个完整的 $Q_H$ 类。对每个类选择一个这样的 $r$，再选择一次非负整数提升 $s_x\in\mathbb N^2$；这个提升在整条执行中固定。它不是每一步读取前的代表替换，也不是给观察者的额外资料。

这一步是全类覆盖的关键。它没有把 $Q_H$ 先约化成 $V_p/(E-I)V_p$，也没有假设高位代表可由低位代表逐次修正；(96.4) 直接在完整的模 $p^e$ 商类中选点，随后只用其模 $p$ 的 $w$ 值控制传感器。

### 96.4 保持负坐标非零并耦合全一转录

在实际非负整数轨迹上只记录 $w(s)\in\mathbb F_p$。初始归一化给出 $w(s_x)=1$。$R$ 后

$$
 w(Ms)=\mu w(s),
\tag{96.6}
$$

所以非零性被保持。若当前 $G$ 是协议的第一个原语，按合同不在它之前放隐藏事件；此时 $w=1$，故该 $G$ 后为 $2\ne0$。若 $G$ 之前已经执行过任意原语（特别是 $R$ 之后的第一次 $G$），则若当前 $w\ne-1$，放零个 $E$；若 $w=-1$，放一个 $E$，使其先变成 $1$，再由 $G$ 变成 $2$。这至多使用一个允许的隐藏事件，并保持 $w\ne0$。

读取前先看当前 $qs$ 是否为模 $p$ 的单位。若是，放零个 $E$。若不是，考虑模 $p$ 的分解 $s=v_++v_-$，其中 $v_-$ 在负特征线上。由 $w(s)\ne0$，有 $v_-\ne0$。若同时 $qs=0$ 和 $qEs=0$，相减得到 $2qv_-=0$；引理96.2又给 $qv_-\ne0$，矛盾。因此 $qEs\ne0$。此时在读取前放一个 $E$，读取 $Es$；其 $q$ 值不被 $p$ 整除，所以

$$
\gcd(qEs,p^e)=1.
\tag{96.7}
$$

读取不扰动，下一原子命令继续作用于同一实际后继。若协议的第一个原子就是读取，上述读取规则仍只使用该读取切口的一次 $E$；若第一个原子是 $R$ 或 $G$，则不在这个首原语之前插入事件。所有 $R$ 前均无事件，每个已有原语之后的 $G$ 都按上文的通用规则处理，包括先前只执行过 $R$ 或读取时的第一次 $G$。于是首次命令时序与后续时序均满足合同。

把这项选择对每个读取逐步执行，就得到一份完整的实际隐藏日程。每个 $E$ 都是对当前非负整数向量施加真实的 $M^d$，没有把向量换成别的模代表；每个后继都从同一份来源的先前后继继续。因此这里构造的是相容的完整历史，而不是分别可实现的有限前缀。

### 96.5 全一响应的取得不可能性

对每个 $x\in Q_H$，由 96.3 选定 $s_x$，由 96.4 选出一份使所有读取等于 $1$ 的日程。确定性协议在这些执行中看到相同的命令完成信号和相同的响应串，因此保持相同的内部记忆、下一命令和停止决定。若它在共同转录上有限停止，输出只能是一个共同值；当 $f$ 非恒定时，这不可能同时等于所有 $f(x)$。若它不停止，至少有一个固定来源上的允许日程违反“每份日程有限结束”的要求；无限本地计算也已经是失败。此即定理96.1。

这个论证只使用逐类的固定源族和逐类的相容日程，不把观察者的等待能力、隐藏事件选择能力或代表重置能力偷渡成接口。它也没有把“每个类存在一个见证”改写成“观察者已经取得了该类”。

### 96.6 商的大小、已有 Smith 结果与两个精度实例

模 $p$ 下 (96.2) 使 $E-I$ 秩为一；因此 $E-I$ 至少有一个模 $p$ 的单位项。对完整整数矩阵的 Smith 因子，第一因子与 $p^e$ 互素，第二因子的 $p$-赋值由

$$
\det(E-I)=-L_d
\tag{96.8}
$$

给出，其中 $L_d$ 是 [Fibonacci 卷第38节](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 使用的 Lucas 数（$d$ 奇）。复用第95.3节的 Smith 约化，得到

$$
Q_H\cong\mathbb Z/p^{\min(e,v_p(L_d))}\mathbb Z.
\tag{96.9}
$$

这是对类数的已有代数计算；本节新增的是对每个完整类选择固定实际源并构造全一转录，而不是一个新的商定理。

当 $d=5,p=11$ 时

$$
M^5=\begin{pmatrix}3&5\\5&8\end{pmatrix},\qquad
L_5=11,\qquad |Q_{11^e}|=11.
$$

在模 $11$ 的坐标

$$
 c=3a+b,\qquad w_0=-4a+b
$$

中，$E(c,w_0)=(c,-w_0)$，$R(c,w_0)=(4c,8w_0)$，$G(c,w_0)=(c+3,w_0-4)$。这里 $w_0(\alpha)=7$，只是引理96.2中归一化形式 $w$ 的非归一化展示。对 $i=0,\ldots,10$，取

$$
 s_i=\bigl((8i-1)\bmod11,\ (3-i)\bmod11\bigr).
\tag{96.10}
$$

则 $c(s_i)=i$ 且 $w_0(s_i)=7$，覆盖全部 $11$ 个类；每个 $H=11^e$ 的提升仍使用各自一次选定的非负代表。

更高精度的检查取 $d=55$、$p=11$、$H=121$。此时

$$
L_{55}=312119004989,\qquad v_{11}(L_{55})=2,\qquad |Q_{121}|=121.
$$

行向量

$$
\lambda=(1,37)\pmod{121}
$$

满足 $\lambda(E-I)=0$，且 $\lambda$ 对 $V_{121}$ 满射；因此 $a+37b\pmod{121}$ 是完整 $121$ 类的标号。这个例子排除了把高位商静默替换成只有 $11$ 类的场上约化。

### 96.7 运输资料、条件逆与接口边界

在 $Q_H$ 上，隐藏 $E$ 作用为恒等。若控制器把已完成的 $R,G$ 及其平移资料保存在仿射字段 $(A,t)$，则

$$
 x_{\rm now}=A x_0+t,
\tag{96.11}
$$

其中初值 $(A,t)=(I,0)$，更新为

$$
 R:(A,t)\mapsto(MA,Mt),\qquad
 G:(A,t)\mapsto(A,t+[\alpha]),\qquad
 E:(A,t)\mapsto(A,t).
\tag{96.12}
$$

$A$ 在商上可逆。因此，一旦某个端点 $x_0$ 或 $x_{\rm now}$ 已经由一个真实取得接口提供，保留的运输资料给出条件逆

$$
 x_0=A^{-1}(x_{\rm now}-t),\qquad
 x_{\rm now}=Ax_0+t.
\tag{96.13}
$$

运输资料本身没有提供任一未知端点。原始 gcd 响应也没有自动下降到 $Q_H$；例如 $d=5,H=11$ 时，$(0,0)$ 与 $(2,5)=(E-I)\alpha$ 属于同一商类，而其 gcd 响应分别为 $11$ 与 $1$。若另加一个付费、精确、不扰动的商读数 $x\in Q_H$，它与 (96.12) 组成一个充分接口；这是新增传感器条件，不是原 gcd 响应的后处理。因而“自主边界”“实际已取得的记忆”“保留的路径运输”仍是三个不同接口对象。

### 96.8 反例边界与假设范围

第一命令的时序不能省略。$d=5,p=11$ 时，来源 $s_0=(10,0)$ 的 $w_0=4\ne0$，但若协议的第一个原语为 $G$，执行后为 $(11,0)$；此后任意 $E^k$ 都保持模 $11$ 的零向量，立即读取不可能为 $1$。在“协议首原语为 $G$ 时其前无事件”的合同下，归一化切片排除了这个见证。即使把隐藏事件只准许在读取前，$s_0=\alpha$ 连续十次 $G$ 后为 $(11,0)$，任意读取前的 $E^k$ 仍给非单位 gcd；所以本节不把读前调度误报成更强的全合同结论。

$E$ 只在模 $p$ 上是反射。$d=5,H=121$ 时

$$
E^2=M^{10}=\begin{pmatrix}34&55\\55&89\end{pmatrix}\pmod{121}\ne I.
$$

$p=2$ 被明确排除：归一化所需的 $2k=w(z)-1$ 以及 $+1/-1$ 特征线分裂在特征二中失效；本节不从奇素数结论推出二进正向取得或二进障碍。复合模数也不能把各素数的局部相位独立拼成一个共同日程：$d=15,H=341=11\cdot31$、$s=(1,212)$ 时

$$
qs=638\equiv297\pmod{341},\qquad qEs\equiv310\pmod{341},\qquad
\gcd(qs,341)=11,\quad \gcd(qEs,341)=31,
$$

且 $E^2=I\pmod{341}$。每个素数分量各自存在单位相位，并不产生一个对复合 gcd 同时为单位的相位。这只是必要反例，不是复合取得的分类。

本节也没有声称所有非恒定任务都需要同一个协议独立于类的同一日程，或声称全类商是原 gcd 的最小传感器。它没有给出满足 (96.2) 的素数无穷性、随机协议、最小记忆、最小问数或物理统一结论；这些均留在相应合同下的开放边界。

### 96.9 与原目标的关系及背景

本节把空间表达写成 $Q_H$ 的余不变量，把时间／命令路径写成 (96.12) 的仿射运输，把记忆写成实际保留的 $(A,t)$，并明确：只有当一个端点真正取得时，(96.13) 才给出条件相互恢复。全一转录说明原始 gcd 接口不能保证取得非恒定初始商任务；它不否定另加商读数、共同坐标读数或外部端点记录后的充分构造。

对抗式状态识别的兼容性与区分测试可参照 Petra van den Bos 与 Frits Vaandrager 的 *State Identification for Labeled Transition Systems with Inputs and Outputs*（arXiv:1907.11034v2）；该文的模型假设没有被等同为本节隐藏事件合同。Lucas 数的整除与赋值背景可参照 T. Lengyel, *The Order of the Fibonacci and Lucas Numbers*, Fibonacci Quarterly 33(3) (1995)，本节只使用 [Fibonacci 卷第38节](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 已有的迹恒等式和 (96.2) 假设。关于不完全自适应区分序列，可参照 Turker、Hierons、Barlas 与 El-Fakih, *Incomplete Adaptive Distinguishing Sequences for Non-Deterministic FSMs*, IEEE TSE 49(9) (2023), DOI 10.1109/TSE.2023.3291137；这些工作不供应本节的端点取得 oracle，也不授予复位或隐藏事件读数。

以上结论是第95节合同上的理论补充。它不新增 Lean、物理统一或消化结算声明；第95节的模五结果仍按其原始读前调度范围解释，本节只给出奇素数幂反射合同下的全类固定源障碍。

## 96.99 追加锚

## 97. 合数共同相位的空因果证书与固定源全一语言

第96.8节给出复合模数上两个素数分量不能独立选择相位的反例。本节在同一个 $H=341,d=15$ 实例中，求出维持全一读取的最大因果不变量为空，并给出逐协议全一日程的准确固定源判据。这里复用第92节保留初始来源与当前后继的区分，以及第95—96节的实际来源、共同隐藏相位和运输合同；空因果证书不裁定实际取得，逐词可实现也不预设一个在线相位选择器。

### 97.1 实际切口合同与局部商坐标

一次执行开始时固定未知 $s_0\in\mathbb N^2$，自然数包含零。取

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
\alpha=(1,0),\quad q=(2,3),\quad H=341=11\cdot31,\quad
E=M^{15}=\begin{pmatrix}377&610\\610&987\end{pmatrix}.
\tag{97.1}
$$

控制器请求 $R(s)=Ms$、$G(s)=s+\alpha$ 或付费、精确、不扰动的读取 $\gcd(qs,341)$。隐藏批 $E^k$ 只在已完成原语的切口及读取之前发生，每个切口的 $k\ge0$ 有限。首原语若为 $R$ 或 $G$，其前没有隐藏事件；若首原语就是读取，其前允许隐藏批。每个请求的原语均完成，原语内部没有隐藏事件；不另加公平性假设。没有复位、时钟、坐标、大小或相位传感器。控制器确定性、可有任意记忆，初始可见资料相同且与来源无关。实际整数后继始终从这份 $s_0$ 连续生成。

以下有限计算在 $V=(\mathbb Z/341\mathbb Z)^2$ 上进行，$|V|=116281$。直接计算给

$$
E\equiv\begin{pmatrix}36&269\\269&305\end{pmatrix},\qquad
E^2\equiv I\pmod{341}.
\tag{97.2}
$$

这里的对合仅是模341恒等，实际整数矩阵 $E^2$ 不等于 $I$。整数 $E-I$ 的各项最大公因数为2，行列式为 $-1364$，故 Smith 因子为 $(2,682)$。复用95.3的约化，完整自主商 $V/(E-I)V$ 有341类。令

$$
c=a+81b,\qquad w=a+261b\pmod{341}.
\tag{97.3}
$$

坐标矩阵的行列式为180，且 $180^{-1}=36\pmod{341}$；其逆可写为 $b=36(w-c)$、$a=c-81b$。逐项代入得

$$
E(c,w)=(c,-w),\qquad R(c,w)=(81c,261w),\qquad
G(c,w)=(c+1,w+1),\qquad qs=270c+73w.
\tag{97.4}
$$

于是 $(E-I)V$ 在这些坐标中恰为 $\{0\}\times\mathbb Z/341\mathbb Z$，因为 $-2$ 是单位。因此 $c$ 标记完整341类，而 $w$ 是本节计算共同相位的辅助坐标；这不是新增传感器。式(95.6)的共同坐标模数为 $D=\gcd(341,376,610,610,986)=1$，所以命题95.2在此只给平凡共同坐标。以上均是第95节商计算与第96节反射坐标在此实例中的局部算术应用。

### 97.2 最大共同因果不变量

记 $u(s)$ 表示 $\gcd(qs,341)=1$。本小节讨论已经完成至少一个原语后的切口，下一原语之前可用任一相位 $E^\epsilon$，$\epsilon\in\{0,1\}$。称 $K\subseteq V$ 为共同因果全一不变量，若

$$
EK=K,\qquad K\subseteq K_0:=\{s:u(s)\ \lor\ u(Es)\},\qquad
s\in K\Longrightarrow Rs\in K\ \land\ (Gs\in K\ \lor\ GEs\in K).
\tag{97.5}
$$

这里相位选择者先知道本次原语，再选择它之前的相位，但不能依据未来原语修订此前选择。$EK=K$ 使读取时选到的单位相位仍留在 $K$。由于 $RE=ER$，两个 $R$ 后继 $Rs,REs$ 属于同一 $E$ 轨道；两个 $G$ 后继则是 $Gs,GEs$，不能替换成相互独立的素数分量选择。

定义递减序列

$$
K_{n+1}=\{s\in K_n:Rs\in K_n\ \land\ (Gs\in K_n\ \lor\ GEs\in K_n)\}.
\tag{97.6}
$$

**命题 97.1（本实例的最大因果证书）。** 每个 $K_n$ 都是 $E$ 闭的；其稳定值 $K_\infty$ 是满足(97.5)的最大集合。本实例中 $K_{29}=K_{30}=\varnothing$，故不存在非空的共同因果全一不变量。

证明。$K_0$ 的定义在 $s,Es$ 互换下不变。若 $K_n$ 是 $E$ 闭的，$R(Es)=E(Rs)$ 使(97.6)的 $R$ 条件不变，而 $G(Es),GE(Es)$ 正好交换 $Gs,GEs$，故 $K_{n+1}$ 仍是 $E$ 闭的。有限递减序列必稳定，稳定值满足(97.5)。任何满足(97.5)的 $K$ 都包含于 $K_0$，并由归纳包含于每个 $K_n$，所以包含于稳定值。空集结论由下一小节覆盖全部 $V$ 的有限计算给出。证毕。

这个条件也刻画已经过启动阶段、面对任意下一原语的在线全一相位选择。若 $K$ 非空，按(97.5)选取留在 $K$ 的相位即可逐步继续。反向，允许选择者知道真实当前剩余并使用任意历史记忆，若它能从某点应对全部未来原语，则同一 $E$ 轨道的另一点可通过下一切口的相位补偿使用同一策略；首个原语的成功继续又分别给出(97.5)的三个条件。因此所有这种可胜点的集合也是(97.5)的一个不变量。$K_\infty=\varnothing$ 排除了这种对所有未来共用的在线选择器，包括带历史记忆的选择器。

### 97.3 全状态计算与删除秩的精确含义

式(97.6)的 $|K_0|,\ldots,|K_{29}|$ 依次为

$$
\begin{aligned}
(&114600,113996,113382,112755,112100,111410,110672,109881,\\
&109020,108052,106970,105720,104260,102526,100477,98566,\\
&96180,93226,89521,84730,78417,70105,59205,45472,\\
&29538,14398,4118,424,12,0).
\end{aligned}
\tag{97.7}
$$

再迭代一次仍为零。把 $V\setminus K_0$ 的秩定义为0，把 $K_{j-1}\setminus K_j$ 的秩定义为 $j\ge1$，记为 $\rho$。全部状态的秩恰覆盖 $0,\ldots,29$，且

$$
\begin{aligned}
\rho(Es)&=\rho(s),\\
\rho(s)=0&\Longrightarrow\neg u(s)\land\neg u(Es),\\
\rho(s)>0&\Longrightarrow
\rho(Rs)<\rho(s)\ \lor
\bigl(\rho(Gs)<\rho(s)\land\rho(GEs)<\rho(s)\bigr).
\end{aligned}
\tag{97.8}
$$

正秩条件就是该点被(97.6)删去的局部理由。下面的完整 Python 3 标准库程序同时计算全部轮次、逐轮检查 $E$ 闭性，并对每个状态检查(97.8)；它不搜索全部状态子集。

```python
from math import gcd

H = 341
N = H * H
states = [divmod(i, H) for i in range(N)]
def idx(a, b):
    return (a % H) * H + b % H

e = [idx(36*a + 269*b, 269*a + 305*b) for a, b in states]
r = [idx(b, a+b) for a, b in states]
g = [idx(a+1, b) for a, b in states]
unit = bytearray(gcd(2*a + 3*b, H) == 1 for a, b in states)
assert N == 116281
assert all(e[e[i]] == i and r[e[i]] == e[r[i]] for i in range(N))
orbits = sum(i <= e[i] for i in range(N))
assert orbits == 58311
keep = bytearray(unit[i] or unit[e[i]] for i in range(N))
rank = [-1 if keep[i] else 0 for i in range(N)]
counts = [sum(keep)]
assert all(keep[i] == keep[e[i]] for i in range(N))
for step in range(1, 31):
    nxt = bytearray(keep[i] and keep[r[i]] and
                   (keep[g[i]] or keep[g[e[i]]]) for i in range(N))
    assert all(nxt[i] == nxt[e[i]] for i in range(N))
    for i in range(N):
        if keep[i] and not nxt[i]:
            rank[i] = step
    keep = nxt
    counts.append(sum(keep))
expected = (114600, 113996, 113382, 112755, 112100, 111410,
            110672, 109881, 109020, 108052, 106970, 105720,
            104260, 102526, 100477, 98566, 96180, 93226,
            89521, 84730, 78417, 70105, 59205, 45472,
            29538, 14398, 4118, 424, 12, 0, 0)
assert tuple(counts) == expected and not any(keep)
assert set(rank) == set(range(30))
for i in range(N):
    assert rank[i] == rank[e[i]]
    if rank[i] == 0:
        assert not unit[i] and not unit[e[i]]
    else:
        assert (rank[r[i]] < rank[i] or
                (rank[g[i]] < rank[i] and rank[g[e[i]]] < rank[i]))
print("K0..K30 =", tuple(counts))
print("states =", N, "E-orbits =", orbits, "ranks = 0..29; local checks passed")
```

同一删除还可在 $58311$ 个 $E$ 轨道上独立核对：用 $(c,\{w,-w\})$ 表示轨道，$R$ 有唯一后继轨道，$G$ 有由 $w+1$ 与 $1-w$ 给出的至多两个后继轨道。先删除两个相位均非单位的轨道，再沿反向边传播：$R$ 后继已删即删，或全部 $G$ 后继已删即删。此反向边删除也留下零个轨道，与(97.7)的稳定空集一致。

若可以看到当前隐藏轨道，(97.8)给出一个下降规则：正秩时选使所有允许相位后继降秩的 $R$ 或 $G$，到零秩后读取便为非单位。这个选命令的规则依赖当前隐藏轨道，实际观察者没有该传感器；所以它不是本接口上的取得策略。它也不提供一个对所有来源、所有相位日程都迫使非单位读取的有限固定词。此处证明的是共同在线证书失败，不能把依状态变化的秩决策当成已获许可的可见历史决策。

### 97.4 启动标志与有限安全词

为表达比共同在线选择更弱的逐协议日程，设字母表 $\Sigma=\{R,G,T\}$，其中 $T$ 表示一次付费读取且要求输出为1。状态是 $(s,b)\in V\times\{0,1\}$：$b=0$ 表示尚未执行原语，$b=1$ 表示至少一个原语已完成。对本次字母 $X$ 定义

$$
P(b,X)=
\begin{cases}
\{0\},&b=0,\ X\in\{R,G\},\\
\{0,1\},&\text{其余情形}.
\end{cases}
\tag{97.9}
$$

每条边使用一个 $\epsilon\in P(b,X)$，并把标志更新为1。具体后继为

$$
\begin{aligned}
(s,b)\xrightarrow{R}(ME^\epsilon s,1),\qquad
(s,b)\xrightarrow{G}(E^\epsilon s+\alpha,1),\\
(s,b)\xrightarrow{T}(E^\epsilon s,1)
\quad\text{仅当 }u(E^\epsilon s).
\end{aligned}
\tag{97.10}
$$

全部状态接受空词。记 $L_{\rm init}(r)$ 为从 $(r,0)$ 出发有一条完整路径的有限词集合；每个 $T$ 都沿其单位边，命令没有额外读数。这个存在路径语义允许同一词的相位选择依赖后面的字母；它尚未给出对不同词共用的在线规则。

### 97.5 一个固定实际来源上的逐协议全一桥

**命题 97.2（本合同的固定源全一判据）。** 固定 $r\in V$，并在协议选定之前一次选定任意非负整数提升 $s_r\equiv r\pmod{341}$。以下两项等价：

1. $L_{\rm init}(r)=\Sigma^*$，即每个有限词都被接受。
2. 对每个满足97.1接口的确定性协议，存在一份允许的隐藏日程，使从同一份 $s_r$ 开始的全部实际读取都为1；协议可以停止、无限请求原语，或在有限次原语后停留于本地计算。

这个等价对任意一次选定的提升成立，不允许随协议、读取或前缀重新选择来源。

证明。先核对模路径与实际轨迹。若给定(97.10)的一串相位位，就在相应允许切口实际施加 $E^0$ 或 $E^1$，随后执行所请求的整数 $R,G$ 或读取。所有矩阵及加法保持非负性；每一步的约化正是(97.10)，故归纳得到每次实际 gcd 与模状态的 gcd 相同。这里没有以小的标准代表替代任何实际后继，连续两次实际 $E$ 也没有被宣布抵消。

反向，一份实际日程在相邻原语之间的有限批可合并到下一原语前，用总指数模2给出同一模路径；读取之前的批同样合并。首个 $R/G$ 前没有可合并的事件，首个 $T$ 前则允许，恰好是(97.9)。没有后续原语时，末尾隐藏批不改变已经取得的读取转录；构造见证日程时可令这些批为零。这里合并仅用于转录和模语义，不宣称实际整数批数为偶数就没有物理变化。

若第二项成立，给定任一有限词，令协议预先执行这个词的原语而不依响应改变命令，随后停止。它的全一日程投影为一条接受路径，所以第一项成立。

若第一项成立，固定一份协议，并沿所有读取均回答1的分支运行它。确定性、共同初始资料及无时间侧信道使这一分支固定一个有限或无限的原语词。若只有有限多个原语，第一项给出相容的有限相位串，上述实际提升实现该前缀；其后的停止或本地计算不需要新读取。若有无限多个原语，对于这个已固定的无限词，以从同一个 $(r,0)$ 出发的所有成功有限相位前缀作树。树包含空前缀，前缀封闭，每个节点至多有两个孩子，且每个深度非空，因为对应的有限词被接受。由 König 引理存在一条无限分支。沿这条分支逐步施加实际 $E^0/E^1$ 和原语，从始至终都使用同一个 $s_r$ 的后继，得到一份相容的无限日程。每个切口至多一个事件，每个请求按合同完成；没有使用复位、额外公平性或无限批事件。证毕。

此证明中的日程可随整份协议改变，有限词的见证也可随其后续字母改变。König 引理只把同一个根、同一个无限词的有限前缀接为一条分支，并不把不同未来词的见证拼成一个在线选择器。因此命题97.1与命题97.2没有相反结论：前者排除一个对所有未来统一的因果选择，后者保持 $\forall\text{协议}\ \exists\text{相容日程}$ 的原量词。

### 97.6 全类固定源族与仍待确定的取得缺口

令

$$
U_{\rm init}=\{r\in V:L_{\rm init}(r)=\Sigma^*\}.
\tag{97.11}
$$

由命题97.2，存在一个覆盖完整341个自主商类、在协议之前一次选定来源、且对每份协议逐源容许全一日程的族，当且仅当

$$
c(U_{\rm init})=\mathbb Z/341\mathbb Z.
\tag{97.12}
$$

确实，若像为全类，逐类选取 $r_x\in U_{\rm init}$ 并固定一个整数提升即可；反向，把任何满足该族条件的实际来源约化，命题97.2的必要方向使其落在 $U_{\rm init}$，各类遂都在像中。不同类可使用不同日程，观察者的初始资料仍相同。

$U_{\rm init}$ 及其像在这里尚未求出，(97.7)没有判定(97.12)。即使某些初始剩余不在 $U_{\rm init}$，它们各自的拒绝词也可不同；不能交换量词，宣布已有一个有限词对所有初始来源都迫使非单位读数。即使(97.12)失败，也只排除这一种全类全一转录障碍，仍未构造保证有限取得商标签的协议。反之，若日后证成(97.12)，第96.5节的同转录论证才可用于本合数实例的非恒定初始商任务。

类零给出一个精确的下一问题：当 $c_0=0$ 且第一原语为 $T$ 时，两个相位的传感器值为 $\pm73w$；因73为模341单位，首读可为1当且仅当 $w$ 为单位，故仅此必要筛选留下 $\varphi(341)=300$ 个候选。哪些候选接受每一个有限词，仍待确定；这不是对后续全部原语的充分条件。

回到第92节，实际取得还须保持初始标签与真实当前后继的联合相容性，并对全部可见响应分支作合法决策；第92节的确定后继合同不能直接替代本节隐藏相位的多后继语义。回到95.7与96.7，若某端点已真实取得，(97.4)给出的可逆商更新及已保留的命令运输仍满足既有的端点条件恢复关系。这里不另立运输定理，也不从运输记录单独解出未知端点。因而本节对空间关系、边界、路径和记忆的增量是定位这一合数实例的取得缺口：自主商明确、共同在线全一证书已被排除，而逐协议全一族与实际端点取得均未决。

### 97.7 文献对应与结论范围

Udi Boker 与 Karoliina Lehtinen，[*Good for Games Automata*，arXiv:1906.11624v2](https://arxiv.org/abs/1906.11624v2)，第3节、定义5前的 history-determinism 说明及定义5，明确要求非确定选择只依已经读到的词，并对所有未来一致。这里借用这一既有的在线选择与逐词接受的区分来解释97.2—97.5的量词，不把其一般理论当作本节新增成果，也不直接导入其自动机定理裁定(97.12)。

Petra van den Bos 与 Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*，arXiv:1907.11034v2](https://arxiv.org/abs/1907.11034v2)，第2节、定义1及其前文，要求每个状态在同一已观察标签下至多有一个后继，称为 observable nondeterminism。本接口不满足这个假设：在剩余 $s=(1,0)$ 请求 $T$，零相位与一次相位都输出1，却分别留下 $(1,0)$ 与 $Es=(36,269)$；它们是不同剩余，且 $\gcd(2,341)=\gcd(879,341)=1$。故该文的状态识别结论不能直接用于这里；把两后继当作可观察选择也会添加原合同没有的相位信息。

本节复用成熟的 Smith 约化、有限安全不变量及 König 引理，新增的是所列算术接口上的空证书和启动时序下的固定实际来源桥。正文论证与穷举程序均不作为 Lean/kernel 核验，不主张原创优先权、一般复合模数分类、实际取得策略、最优读取数或长期研究目标已经完成。没有新增复位、公平性、时钟或端点传感器假设。

## 97.99 追加锚

## 98. 共同隐藏相位下的两读数含量与条件端点恢复

第97节的完整自主商有341类，但其共同坐标模数为1。下面在同一实际接口中取得一个四值整除不变量，并将其接到95.7、96.7的保留运输：某些实际执行由此取得完整商端点。这个不变量的取得不要求它本身是商坐标，也不要求它在接枝下自主。

### 98.1 实际来源、探针起点与共同含量

完全沿用97.1的合同。一次执行固定未知 $s_0\in\mathbb N^2$，自然数包含零，且

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
q=(2,3),\qquad \alpha=(1,0),\qquad
E=M^{15}=\begin{pmatrix}377&610\\610&987\end{pmatrix},\qquad H=341.
\tag{98.1}
$$

$R(s)=Ms$，$G(s)=s+\alpha$；本节的 $T$ 表示一次付费、精确、不扰动的读取 $\gcd(qs,341)$，并不限定其答案为1。每个允许切口的隐藏批 $E^k$ 都有有限 $k\ge0$；首原语为 $R/G$ 时其前没有隐藏事件，首原语为 $T$ 时其前允许隐藏批。后续批只在97.1准许的切口发生，原语均完成且内部没有隐藏事件。控制器确定性，初始可见资料和记忆与来源无关；没有复位、时钟、坐标、大小或相位读数，也不增加公平性或可指定的等待操作。

**定义 98.1（当前共同含量）。** 对实际整数状态 $s=(a,b)$，置

$$
\delta(s)=\gcd(a,b,341)\in\{1,11,31,341\}.
\tag{98.2}
$$

记 $s_*$ 为开始执行探针 $T,R,T$ 时、其首读前隐藏批尚未发生的实际状态；$s_{\rm end}$ 为第二次读取完成时的实际状态。$s_*$ 可以是较长协议的当前后继，因而 $\delta(s_*)$ 与协议初始值 $\delta(s_0)$ 必须区分。若整个协议从这个探针开始，则 $s_*=s_0$；若此前含有 $G$，两者没有一般相等关系。所有这些状态属于同一份实际来源的连续轨迹。

### 98.2 两次付费读取取得含量

**定理 98.2（任意共同日程下的两读数解码）。** 对每个实际非负来源、每个合法探针起点及每份允许的隐藏日程，依次执行 $T,R,T$，取得响应 $y_0,y_1$ 后有

$$
m:=\gcd(y_0,y_1)=\delta(s_*)=\delta(s_{\rm end}).
\tag{98.3}
$$

解码器只使用已取得的两个因数，不读取隐藏指数、整数线性观察值或来源坐标。

证明。$M$ 的行列式为 $-1$，$E=M^{15}$ 也有整数逆。因此任意整数向量 $z$ 与 $Mz$、$Ez$ 的两坐标分别生成同一个整数理想；加入生成元341后仍相同，故 $R$ 和每个 $E^k$ 都保持 $\delta$。不扰动的 $T$ 也保持它。这是既有整数幺模含量不变性的应用。

令 $u$ 为第一次读取真正发生时的整数状态。允许首读前有未知批，故 $u=E^{k_0}s_*$，而 $\delta(u)=\delta(s_*)$。在两读之间只有一次 $R$ 及允许的有限隐藏批，没有 $G$。由于 $ME=EM$ 且读取不扰动，第二次实际读取状态必为

$$
u'=ME^k u\qquad(k\ge0),\qquad
y_0=\gcd(qu,341),\quad y_1=\gcd(qME^ku,341).
\tag{98.4}
$$

$k$ 是这些批的总指数，可以任意大，控制器无需知道它。复用97.1的 $E^2\equiv I\pmod{341}$，只在证明中按 $k$ 的奇偶约化，得到两个观察矩阵

$$
C_0=\begin{pmatrix}q\\qM\end{pmatrix}
=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
C_1=\begin{pmatrix}q\\qME\end{pmatrix}
=\begin{pmatrix}2&3\\4181&6765\end{pmatrix}.
\tag{98.5}
$$

有 $\det C_0=1$、$\det C_1=987$，而

$$
987\cdot161-341\cdot466=1.
\tag{98.6}
$$

所以两矩阵在 $\mathbb Z/341\mathbb Z$ 上均可逆；奇相位的逆可取 $161\operatorname{adj}(C_1)$ 模341。$C_1$ 不是整数幺模矩阵，此处不主张它保持不含341的整数 gcd。

具体地，记 $\varepsilon=k\bmod2$。$C_\varepsilon u$ 的两坐标都是 $u_1,u_2$ 的整数线性组合，故

$$
\bigl((C_\varepsilon u)_1,(C_\varepsilon u)_2,341\bigr)
\subseteq (u_1,u_2,341)
\tag{98.7}
$$

作为 $\mathbb Z$ 中的理想成立。取上述模逆的整数代表，把 $u$ 表成 $C_\varepsilon u$ 的整数线性组合再加341的倍数，给出反向包含。两理想相等，其正生成元相等。式(98.4)的第二个线性观察值与 $(C_\varepsilon u)_2$ 模341相同，且 $\gcd(\gcd(x,341),\gcd(z,341))=\gcd(x,z,341)$，于是

$$
\gcd(y_0,y_1)=\gcd(qu,qME^ku,341)
=\gcd(u_1,u_2,341)=\delta(s_*).
\tag{98.8}
$$

探针中所有实际操作保持 $\delta$，遂得终态等式。即使第二次读取后又发生允许的隐藏批，等式仍成立，直到另一次可能改变含量的 $G$。

这个推导包括 $s_*=(0,0)$：两响应均为341。也包括坐标严格为正但都被341整除的状态，其响应同样均为341。首读是整个协议的首原语时，$k_0$ 已处理其未知相位；若协议先执行 $R/G$，则首先按97.1执行该无前置隐藏事件的原语，后来选定的 $s_*$ 仍适用同一证明。全程没有将实际后继换成较小的模代表；$E^2\equiv I$ 只用于读数的模计算，不删除任何真实整数事件。证毕。

### 98.3 初始含量的尖锐最坏读取数

**定理 98.3（任意至多一读协议的下界）。** 在97.1合同下，要求对每个初始来源及每份允许日程都有限结束并准确输出 $\delta(s_0)$。即使允许任意确定性记忆、本地计算及任意合法 $R/G$ 命令，也不存在每次执行至多付费读取一次的正确协议。结合从初始状态直接执行定理98.2的探针，最优最坏付费读取数恰为2。下界在仅允许严格正坐标的来源域上仍成立。

证明。固定任意候选协议，取所有隐藏批均为零的合法日程。第一读之前没有来源相关的可见输入，故共同初始记忆、确定性及无时间侧信道使其本地计算、命令序列和停止决定对所有来源相同。

若它在零读时停止，所有来源得到同一输出，而 $(0,0)$ 与 $(1,0)$ 的初始含量分别为341与1，不可能都正确。严格正域可改用 $(341,341)$ 与 $(1,1)$。若它在第一读之前无限计算或无限发出无读数命令，则已违反总有限结束。因此剩下的情形有一个固定的有限读前词。

复用 Fibonacci 卷定理130.2证明中的整数词归纳，这个词对每个来源的实际作用为

$$
s\longmapsto M^r s+\tau,\qquad r\ge0,\quad \tau\in\mathbb N^2,
\tag{98.9}
$$

其中 $r,\tau$ 只依赖该词。空词取 $(r,\tau)=(0,0)$；追加 $R$ 更新为 $(r+1,M\tau)$，追加 $G$ 更新为 $(r,\tau+\alpha)$，故任意多次交错命令都已包括。令 $\ell=qM^r=(\ell_1,\ell_2)$。$q=(2,3)$ 本原，$M^r$ 有整数逆，所以 $\gcd(\ell_1,\ell_2)=1$：任何同时整除两分量的数，经乘 $M^{-r}$ 也整除2与3。

用 $[x]_{341}$ 表示 $0,\ldots,340$ 中的标准代表，取一次固定来源

$$
v=\bigl([\ell_2]_{341},[-\ell_1]_{341}\bigr)\in\mathbb N^2.
\tag{98.10}
$$

它满足 $\ell v\equiv0\pmod{341}$，且 $\delta(v)=1$；否则11或31同时整除 $\ell_1,\ell_2$，矛盾。因此初始来源 $0$ 与 $v$ 的目标分别为341与1，但唯一一次读取分别为

$$
\gcd(q\tau,341),\qquad
\gcd(\ell v+q\tau,341),
\tag{98.11}
$$

两响应相等，包含了任意读前接枝留下的共同平移 $q\tau$。

两次执行在该读取后仍具有相同的可见历史和内部记忆。至多一读的假设排除了任何第二读；其后的 $R/G$ 完成信号、本地计算、输出和停止决定继续相同。真实隐藏状态可以不同，但没有允许的传感器使控制器据此分支。若这个共同后缀不结束，则违反总有限性；若结束，给出的同一个值不能同时等于两个不同初始含量。这既覆盖读取前的提前停止，也覆盖读取后的任意无读数后缀。

严格正域取固定的两个来源 $b=(341,341)$ 与 $b+v$。它们均有严格正坐标，目标分别为341与1；读数的线性差仍为 $\ell v\equiv0\pmod{341}$，故同一论证成立。把对应数量的 $\alpha,\beta$ 叶子任意二元括合，就实现这些正组成的非空树，因此排除结构零不消除下界。若再限制已知初始数量、特定准备子集或来源相关的初始资料，必须重新检查见证对是否仍在同一允许域内，本定理不提供那种限制域的下界。证毕。

这里最小化的只是统一协议的最坏付费读取数。它不声称每个来源都必须读取两次：从协议初始状态直接读取若得到 $y_0=1$，则 $\delta(s_0)\mid y_0$，已经可以输出1并停止。定理也不最小化记忆、命令次数、整数运算量或经过时间。

### 98.4 含量证书与保留运输给出的端点

**命题 98.4（取得含量后的条件商恢复）。** 以97.1的完整商坐标

$$
c(s)=a+81b\pmod{341}
\tag{98.12}
$$

记协议初始类 $c_0$ 与当前类 $c_{\rm now}$。控制器从协议开始保留 $(A,t)=(1,0)$，对全部已完成命令更新

$$
R:(A,t)\mapsto(81A,81t),\qquad
G:(A,t)\mapsto(A,t+1),\qquad
E^k,T:(A,t)\mapsto(A,t)
\pmod{341}.
\tag{98.13}
$$

在任何一次 $T,R,T$ 探针结束时，用定理98.2取得 $m$，并将探针中的 $R$ 也计入运输字段，则

$$
c_{\rm now}=Ac_0+t\pmod{341},\qquad
c_0\equiv-A^{-1}t\pmod m.
\tag{98.14}
$$

当 $m=341$ 时，这实际认证完整当前商类 $c_{\rm now}=0$，并恢复完整初始商类 $c_0=-A^{-1}t\pmod{341}$。当 $m=11$ 或31时，本证书给出显示的相应同余；$m=1$ 时该同余没有限制。

证明。97.1给出 $c(Es)=c(s)$、$c(Rs)=81c(s)$、$c(Gs)=c(s)+1$，不扰动的 $T$ 不改变 $c$。逐事件归纳即得第一式，正是95.7、96.7的运输关系在此完整商中的应用。因 $\gcd(81,341)=1$，$A$ 始终是模341单位，并在每个 $m\mid341$ 上可逆。定理98.2给 $m\mid a_{\rm now},b_{\rm now}$，故 $c_{\rm now}\equiv0\pmod m$；将第一式约化并求逆即得第二式。$m=341$ 时，零同余正是完整商的零类。它不表示当前整数向量等于零。

这里仅说明含量证书与保留运输给出的同余；完整读数对、准备条件或更长历史还可能提供额外信息。证毕。

这个条件有严格正且初始含量不同的实例。取协议初始来源 $s_0=(340,341)$，第一个原语为 $G$，然后执行 $T,R,T$。首 $G$ 前无隐藏事件，故实际到达 $(341,341)$；其后任意隐藏批、探针的 $R$ 和读取都保持含量341。因此对每份允许日程，两读数均为341，$m=341$。整个词只含一次 $G$ 和一次 $R$，所以探针结束时 $A=t=81$，由(98.14)恢复

$$
c_0\equiv-81^{-1}81=-1\equiv340\pmod{341},\qquad
\delta(s_0)=1.
\tag{98.15}
$$

这里取得的是当前含量，并经保留运输恢复初始商类；没有把当前含量冒作初始含量。该实例证明条件恢复有实际执行见证，不保证所有来源都会达到 $m=341$。

### 98.5 该不变量的两个界限

**命题 98.5（含量不下降为商函数，也不在接枝下自主）。** 不存在函数 $f:\mathbb Z/341\mathbb Z\to\{1,11,31,341\}$ 使 $\delta=f\circ c$ 对全部实际来源成立；也不存在仅由 $\delta(s)$ 决定 $\delta(Gs)$ 的统一更新函数。

证明。$(0,0)$ 与 $(260,1)$ 都有 $c=0$，因为 $260+81=341$；其含量分别为341与1，否定第一项。对第二项，$(1,1)$ 与 $(340,341)$ 的含量同为1，而施加首个 $G$ 后分别为 $(2,1)$ 与 $(341,341)$，含量为1与341。首 $G$ 前无隐藏事件，故这也是合法实际执行的反例。证毕。

于是 $\delta$ 是原 gcd 接口可取得、在 $R/E$ 下不变的量，却不是完整自主商的坐标，也不能独自承担 $G$ 的更新。第98.4节使用的是同一实际执行上的含量证书与运输资料的联合约束。四个含量值、两次读取、两个组成坐标、两类叶生成元及341个商标签计量不同对象，不能互相替代。

### 98.6 复用范围与研究边界

共同含量的代数复用 [Fibonacci 卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 定理120.3、引理127.2证明中的相邻观察理想不变性，以及引理137.3对未知含量和饱和零的处理；读前词的实际仿射形式复用定理130.2。那些已知索引的查询表及原始线性观察值的两读数逆式并不直接证明本节隐藏相位下的取得：前者掌握实际查询时刻，后者供应更强的数值传感器。这里需要额外核对(98.4)—(98.8)在每个共同相位上都成立。

整数幺模变换保持坐标 gcd 是经典事实。A. Tamir，[*On Totally Unimodular Matrices*，Networks 6 (1976)，定理8及证明，印刷页379—380](https://www.math.tau.ac.il/~atamir/uni_76.pdf)，以向量 gcd 的保持性质刻画整数幺模矩阵；此处只复用这一性质，不将其推广冒充新发现，也不把整数逆的结论错用于 $C_1$。模逆连同生成元341的理想等式已在98.2中单独说明。

若只重述上述含量代数或95.7、96.7的条件运输，仍没有从本接口取得端点的操作。此处补入的是 $T,R,T$ 对实际来源的统一解码、允许任意读前及读后 $R/G$ 的一读下界，以及 $m=341$ 时接上既有运输的实际端点证书。它们都限定于97.1的合同。

这些结论没有分类97.6的 $U_{\rm init}$ 及 $c(U_{\rm init})$，没有判定一般强制取得问题，也没有构造对全部来源保证取得完整341类商标签的协议。关系空间由该商表达，命令路径由保留的仿射运输表达，记忆携带实际取得的含量与运输；只有上述证书条件满足时，它们才给出所列端点恢复，不能恢复完整整数来源、隐藏事件次数或经过时间。本节保留这些未决边界，不主张原创优先权、物理统一、Lean/kernel 核验、消化结算或长期研究目标完成。

## 98.99 追加锚

## 99. 无接枝接口中初始含量取得的素数秩充要条件

**定义 99.1（一般步长的单源 $R/T$ 合同）。** 将97.1的参数推广为已知整数 $H>1,d\ge1$，并将控制字母表限制为 $R,T$。一次执行开始时选定未知实际来源 $s_0=(a,b)^{\mathsf T}\in\mathbb N^2$，自然数包含零，置

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q=(2,3),\qquad E=M^d,
\qquad \delta_H(s)=\gcd(s_1,s_2,H).
\tag{99.1}
$$

命令 $R(s)=Ms$；$T$ 是一次付费、精确、不扰动的读取，响应为 $\gcd(qs,H)$，包括 $\gcd(0,H)=H$。隐藏批 $E^k$ 只在已完成原语的切口及读取之前发生，每个切口的 $k\ge0$ 有限。若首原语为 $R$，其前没有隐藏事件；若首原语为 $T$，其前允许隐藏批。每个请求的原语均完成，原语内部没有隐藏事件；不另加公平性假设。实际整数后继始终由这一份 $s_0$ 连续生成，不能复位或替换成新的剩余代表。

控制器可以作任意确定性本地计算、保存任意记忆，并依已有命令及付费响应自适应选择下一命令、停止与输出。初始可见资料及记忆与来源无关；完成信号仅表示原语完成，不提供历时、大小或隐藏批数。没有 $G$、指定等待操作、复位、时钟、坐标、大小、相位或调度器读出。称一个协议**取得初始含量**，若对每个允许来源及每份合法隐藏日程，它都在有限执行后停止并准确输出 $\delta_H(s_0)$；无限本地计算或无限命令序列均不满足取得要求。这个定义不预设统一历时上界。

取 $F_0=0,F_1=1$，对素数 $p$ 记 $z(p)=\min\{n>0:p\mid F_n\}$。这里的正秩存在及其整除律采用 [Fibonacci 卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §142.1中的约定与论证。仓内 FibonacciRank.fibonacci_entry_point 的准确前提是一个已给定的正指标、该指标处的整除及最小性；素数上的存在性见 FibonacciAtomic.TimeSampling.pairwise_recovery_maximum 证明中的局部 ranks，不将它称为另一个已导出的存在性定理。所用经典秩律为

$$
p\mid F_n\quad\Longleftrightarrow\quad z(p)\mid n\qquad(n\ge0).
\tag{99.2}
$$

John Vinson，[*The Relation of the Period Modulo m to the Rank of Apparition of m in the Fibonacci Sequence*，Fibonacci Quarterly 1(2) (1963)，37–45页](https://www.fq.math.ca/Scanned/1-2/vinson.pdf)，第37页式(3)给出这一整除律并归功于 Wall。本节只将它用于下面的操作合同，不另立秩律或 Smith 分类。

**定理 99.2（任意确定性 $R/T$ 协议的取得二分）。** 在定义99.1的合同下，以下两项等价：存在取得初始含量的协议；以及

$$
\forall\,p\text{ 为素数},\quad p\mid H\ \Longrightarrow\ \gcd(d,z(p))>1.
\tag{99.3}
$$

条件成立时，固定协议 $T,R,T$ 取得响应 $y_0,y_1$ 后输出 $\gcd(y_0,y_1)$ 即可。条件失败时，可在协议选定前固定两个严格正整数来源，用一个因果隐藏规则使它们在任意确定性协议下具有相同可见历史而初始含量不同。因此等价式在来源域缩为 $\mathbb N_{>0}^2$ 时仍成立。

证明。先复用共同含量与两行观察的代数。[Fibonacci 卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 定理120.10证明中的局部理想不变性，以及本卷98.2，给出 $M$ 及其幂保持 $\delta_H$；这是 $\det M=-1$ 的整数幺模性质。该卷定理44.1–44.2给出两时刻行列式及其 Smith 缺陷。因 $q=(F_3,F_4)$，在这里所需的两行矩阵为

$$
C_t=\begin{pmatrix}q\\qM^t\end{pmatrix},\qquad \det C_t=F_t\qquad(t\ge1).
\tag{99.4}
$$

假设(99.3)成立，令 $u$ 为首读实际发生时的整数状态。未知首读前批数只使 $u=E^{k_0}s_0$，故 $\delta_H(u)=\delta_H(s_0)$。两读之间只有一次 $R$ 和各合法切口的有限隐藏批；由 $ME=EM$ 及 $T$ 不扰动，第二读实际状态准确等于

$$
M^{1+dK}u,\qquad K\in\mathbb N,
\tag{99.5}
$$

其中 $K$ 是这段实际执行中全部隐藏批数之和。对每个素因子 $p\mid H$，令 $g_p=\gcd(d,z(p))>1$。若 $z(p)\mid1+dK$，则 $g_p$ 同时整除 $dK$ 和 $1+dK$，从而整除1，矛盾。因此(99.2)给 $p\nmid F_{1+dK}$，对全部素因子合起来得到 $\gcd(F_{1+dK},H)=1$。

于是 $C_{1+dK}$ 模 $H$ 可逆。复用98.2的含模数生成元理想论证，在 $\mathbb Z$ 中有

$$
\bigl(qu,qM^{1+dK}u,H\bigr)=(u_1,u_2,H).
\tag{99.6}
$$

左侧生成元是右侧生成元的整数线性组合；模逆的整数代表连同 $H$ 给反向包含。取正生成元即得

$$
\gcd(y_0,y_1)=\gcd(qu,qM^{1+dK}u,H)
=\delta_H(u)=\delta_H(s_0).
\tag{99.7}
$$

这对 $H$ 的所有素数幂因子同时成立，不需要素数幂秩的提升公式。零来源使两读数均为 $H$；任一分量的含量饱和也已包含在理想等式中。未知含量及饱和零的处理与 Fibonacci 卷引理137.3相容，但这里没有假定观察者掌握该引理中时间表的标签。解码器只计算两个已读因数的 gcd，不需要知道 $K$ 或 $C_{1+dK}$ 的逆。两个 $T$ 和一个 $R$ 共三个已完成原语给出统一的原语数上界；隐藏工作量、整数大小及经过时间没有由此得到统一上界。

反过来，设有素数 $p\mid H$ 满足 $\gcd(d,z(p))=1$。置

$$
h=H/p,\qquad w=(3,2p-2)^{\mathsf T},\qquad
s_* = hw,\qquad s_H=(H,H)^{\mathsf T}.
\tag{99.8}
$$

二者均严格为正，且 $\gcd(3,2p-2,p)=1$：否则 $p$ 同时整除3与2，矛盾。所以 $\delta_H(s_*)=h$、$\delta_H(s_H)=H$。来源只依赖 $H$ 及所选 $p$，不依赖协议、未来命令或隐藏历史。

写 $qM^n=(A_n,B_n)$。式(99.4)给 $2B_n-3A_n=F_n$；$n=0$ 时直接代入也成立。因此对每个 $n\ge0$，

$$
qM^nw=3A_n+(2p-2)B_n=-F_n+2pB_n,
\qquad T(M^ns_*)=h\gcd(F_n,p).
\tag{99.9}
$$

这里直接用 $\gcd(hx,hp)=h\gcd(x,p)$，不要求 $h$ 与 $p$ 互素。若 $p^e\parallel H$，乘以 $h$ 已使其它素数分量饱和，并在 $p$ 分量只留下最高一层差别。

现在给出一个在线规则。调度器从实际累计 $M$ 指数 $n=0$ 开始，只在每次 $T$ 前安排隐藏事件，其余所有切口取零批；每个完成的 $R$ 令 $n\leftarrow n+1$。在控制器已经请求 $T$ 后，选择

$$
k=[-n d^{-1}]_{z(p)}\in\{0,\ldots,z(p)-1\},\qquad
n\leftarrow n+dk,
\tag{99.10}
$$

其中 $d^{-1}$ 是模 $z(p)$ 的逆，方括号取最小非负代表。实际执行这 $k$ 次 $E$ 后才读取。于是 $z(p)\mid n$，(99.2)、(99.9)使响应恒为 $H$。这个 $k$ 是一个作用于完整整数来源的共同批数，并非对不同素数分量分别选相位；它只依赖已有累计指数及当前请求。首原语为 $R$ 时，其前零批；首原语为 $T$ 时，$n=0$ 给 $k=0$。所有批均有限，且没有事件放进原语内部。

在 $s_H$ 上施加同一规则，它的每个实际后继仍是 $H$ 的坐标倍数，响应也恒为 $H$。逐已完成原语归纳：两次执行从相同初始可见资料出发，得到相同响应和完成信号，故任意确定性本地计算、记忆、后续命令及停止决定始终相同。每条轨迹始终准确为 $M^ns_*$ 或 $M^ns_H$；没有在中途改选来源、复位或以模代表替换实际整数状态。

规则(99.10)在每个前缀只用过去信息，所以所有有限前缀相容；若执行无限延续，同一递归规则仍定义整条合法日程，无需紧致性或额外公平性。若协议停止，相同输出不能同时等于 $h<H$ 和 $H$；若共同执行在本地计算、无读数命令后缀或无限读取中不停止，则已经违反有限取得。任意自适应协议因而均被这对预先固定的来源排除。证毕。

**命题 99.3（合数实例与素数幂诊断）。** 对 $H=341,d=15$，定理99.2恢复98.2从初始状态开始的取得结论；对 $H=4,d=2$，不存在定义99.1的取得协议，尽管 $\gcd(d,z(4))>1$，其中 $z(4)$ 表示最小正 Fibonacci 零指标。若把目标定义延伸至 $H=1$，则目标恒为1，零次读取即可取得。

证明。$341=11\cdot31$，$F_{10}=55$、$F_{30}=832040$。在10的正真因子 $1,2,5$ 处 Fibonacci 数均不被11整除；在30的正真因子 $1,2,3,5,6,10,15$ 处均不被31整除。由(99.2)，$z(11)=10,z(31)=30$，对应的 gcd 分别为5和15，满足(99.3)。

另一方面，$z(2)=3,z(4)=6$，故 $\gcd(2,z(2))=1$ 而 $\gcd(2,z(4))=2$。失败见证为 $h=2,s_*=(6,4),s_H=(4,4)$，两初始含量分别为2和4，按(99.10)可使每次响应均为4。这说明判据必须逐素因子使用 $z(p)$；仅检查素数幂或整个模数的秩会漏掉这一障碍。最后 $\gcd(a,b,1)=1$ 对所有来源成立。证毕。

定理99.2将固定参数下的两读取得与固定源障碍合成一般 $H,d$ 的充要条件；承重的秩、行列式、Smith 与理想事实均沿用上述来源。它只分类无 $G$ 合同中的初始含量取得，不分类完整整数来源、完整自主商 $Q_H$ 或最小记忆，也不对允许接枝的全部 $R/G/T$ 协议作不可能性推断。$d=0$ 不在合同内。

## 99.99 追加锚

## 100. 零商类固定源全一语言的十模板有限证书

第97.6节留下的式(97.12)是待判定断言。本节在其原有完整 $R/G/T$ 合同下证明零类中没有全词接受的初始剩余，因而判定该断言为假。这是否定此前开放的全类覆盖条件，不是反驳命题97.1、97.2或一条已经成立的定理；也不由此宣布完整自主商已经可以取得。

### 100.1 固定来源、原语合同与结论

完全采用97.1、97.4：$H=341$，$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$，$E=M^{15}$，$\alpha=(1,0)^{\mathsf T}$，$q=(2,3)$。一次执行在协议之前固定未知 $s_0=(a_0,b_0)^{\mathsf T}\in\mathbb N^2$，包含零来源；所有实际整数后继连续由这一份来源生成。控制器的全部外部原语恰为 $R(s)=Ms$、$G(s)=s+\alpha$ 和付费、精确、不扰动的当前读取 $T(s)=\gcd(qs,341)$。隐藏有限批 $E^k$ 只能发生在已声明切口：首原语为 $R/G$ 时其前无事件，首原语为 $T$ 时其前可有事件；已完成原语之间及读取前可有有限批，原语内部没有事件。每个请求按合同完成，不改变公平性，也不增加复位、免费时钟、来源或相位 oracle。初始可见资料与来源无关。

仍用97.3的可逆模坐标

$$
c=a+81b,\qquad w=a+261b,\qquad
b=36(w-c),\quad a=c-81b\pmod{341}.
\tag{100.1}
$$

$c$ 是完整自主商的标签，$w$ 只用于数学论证。词从左到右执行；作为97.4的字母，$T$ 只保留实际响应为1的边，实际读取原语本身仍返回完整 gcd。

**定理 100.1（零类无全词接受根）。** 对97.11定义的集合，有

$$
U_{\rm init}\cap\{z\in V:c(z)=0\}=\varnothing.
\tag{100.2}
$$

更具体地，对每个预先固定、满足 $c(s_0)=0$ 的非负整数来源，存在一个有限词 $W_{w(s_0)}$，使从该来源执行此词的每份合法隐藏日程都至少产生一次非单位读取。量词为

$$
\forall s_0\in\mathbb N^2\ (c(s_0)=0\ \Longrightarrow
\exists W\ \forall h\in\mathcal H(s_0,W)
\exists i\ [W_i=T\ \land\ \gcd(qs_i(h),341)>1]),
\tag{100.3}
$$

其中 $s_i(h)$ 是第 $i$ 个原语真正读取时的实际状态，$\mathcal H(s_0,W)$ 是原合同允许的日程集。下面给出的151个词组成一个充分见证族，每词至多209个原语、76次付费读取、5次接枝。界只针对这个词族，不主张最优。

### 100.2 共同符号轨道与十五轮扫描

由97.4逐项代入，有

$$
E(c,w)=(c,-w),\quad R(c,w)=(81c,261w),\quad
G(c,w)=(c+1,w+1),\quad qs=270c+73w.
\tag{100.4}
$$

这里及本节有限证书的所有坐标运算均模341。记 $[w]=\{w,-w\}$，以 $(c,[w])$ 表示一个共同 $E$ 轨道，记其规范代表 $\nu(w)=\min(w\bmod341,-w\bmod341)$。符号是模341上的一个全局选择；不允许在模11、模31两个分量各选一个符号。

在已经完成至少一个原语的切口，下一原语前两个相位均合法。因而在轨道层面，$R$ 的唯一后继是 $(81c,[261w])$，$G$ 的后继是 $(c+1,[w+1])$ 与 $(c+1,[1-w])$，重合时只记一次。$T$ 恰在

$$
u_+(c,w)\ \lor\ u_-(c,w),\qquad
u_\pm(c,w):\Longleftrightarrow\gcd(270c\pm73w,341)=1
\tag{100.5}
$$

时留下同一轨道。此处的次序必须是先选读前相位、再检验该相位是否为单位、最后才投影到轨道。读取后原始 NFA 只留下通过检验的具体状态；另一个非单位状态不能被加回本次读取的成功后继。轨道记法之所以能用于下一步，是因为下一合法切口又允许施加 $E^0/E^1$，从任一已留下的相位均可到达该轨道的任一相位。它不把这种未来选择解释为当前免费读取。

这些轨道转移只用于启动之后。启动标志为0且首字母为 $R/G$ 时只能使用零相位，不能先作轨道闭包。下面所有初始见证词以 $T$ 开始，严格使用97.9对首读开放相位的例外，然后才进入上述轨道语义。

**引理 100.2（扫描是轨道上的部分恒等）。** 置 $C=(RT)^{15}$。对于启动后的轨道 $(c,[w])$，定义

$$
D(c,w)=\{t\in\{1,\ldots,15\}:
\gcd(270\cdot81^tc+73\cdot261^tw,341)>1\ \land
\gcd(270\cdot81^tc-73\cdot261^tw,341)>1\}.
\tag{100.6}
$$

$C$ 在此轨道上有全一接受路径，当且仅当 $D(c,w)=\varnothing$；有路径时终态轨道恰为 $(c,[w])$，否则没有终态。

证明。每次 $R$ 后的轨道由(100.4)唯一确定；第 $t$ 次读取之前恰为 $(81^tc,[261^tw])$，与过去相位无关。第 $t$ 次 $T$ 能继续，当且仅当两个共同相位至少一个为单位。若所有十五个位置都能继续，在每个合法读前切口选择一个通过的相位便给出同一根上的一条相容路径；不需要跨素数分量选择相位。若某个位置两相位均失败，则此前的所有分支在这里被删除。最后，直接算得

$$
81^{15}=1,\qquad261^{15}=-1\pmod{341},
\tag{100.7}
$$

所以幸存路径回到同一共同符号轨道。这里恒等的对象是模轨道，既不是原始 NFA 中的每一个具体状态，也不是实际整数来源。证毕。

### 100.3 十个模板及全部分支证书

对有限指数列 $J=(j_1,\ldots,j_m)$ 定义

$$
B(J)=R^{j_1}GC\,R^{j_2}GC\cdots R^{j_m}GC.
\tag{100.8}
$$

用下列十个代表和共36个指数即可；每个模板从启动后的 $(0,[r])$ 开始。

| 模板 | 代表 $r$ | 指数列 $J_r$ |
| --- | --- | --- |
| 100.A1 | 1 | $(4,3,6,13)$ |
| 100.A2 | 2 | $(4,1,12,10)$ |
| 100.A3 | 3 | $(10,13,9)$ |
| 100.A4 | 4 | $(0,9,5,13)$ |
| 100.A5 | 5 | $(2,0,9)$ |
| 100.A6 | 7 | $(14,13)$ |
| 100.A7 | 8 | $(4,8,0,12)$ |
| 100.A8 | 14 | $(1,9,12,8,9)$ |
| 100.A9 | 16 | $(13,7,8,10)$ |
| 100.A10 | 19 | $(2,10,6)$ |

下表给出每次 $R^jG$ 后、$C$ 前的完整两分支。第一列按模板及块序号编号；$c$ 是这两分支共同的当前商坐标。分支项 $v:t$ 表示规范 $w$ 代表为 $v$，且 $t=\min D(c,v)$ 是首次两相位同时失败的位置；$v:\mathrm{pass}$ 表示 $D(c,v)$ 为空，即全部十五个位置均存在单位相位。末列是执行整个 $C$ 后留下的规范 $w$ 集合，$c$ 不变。于是该表既列出被删分支的具体算术见证，也列出需逐位置通过的全部幸存分支。

| 块 | $j$ | $c$ | $C$ 前的分支及判据 | $C$ 后的代表集 |
| --- | --- | --- | --- | --- |
| 100.A1.1 | 4 | 1 | $102:\mathrm{pass},\quad 104:13$ | $\{102\}$ |
| 100.A1.2 | 3 | 164 | $149:\mathrm{pass},\quad 151:14$ | $\{149\}$ |
| 100.A1.3 | 6 | 19 | $157:7,\quad 159:\mathrm{pass}$ | $\{159\}$ |
| 100.A1.4 | 13 | 205 | $79:3,\quad 81:12$ | $\varnothing$ |
| 100.A2.1 | 4 | 1 | $134:\mathrm{pass},\quad 136:5$ | $\{134\}$ |
| 100.A2.2 | 1 | 82 | $148:7,\quad 150:\mathrm{pass}$ | $\{150\}$ |
| 100.A2.3 | 12 | 81 | $101:13,\quad 103:\mathrm{pass}$ | $\{103\}$ |
| 100.A2.4 | 10 | 104 | $80:3,\quad 82:12$ | $\varnothing$ |
| 100.A3.1 | 10 | 1 | $139:\mathrm{pass},\quad 141:11$ | $\{139\}$ |
| 100.A3.2 | 13 | 263 | $144:\mathrm{pass},\quad 146:4$ | $\{144\}$ |
| 100.A3.3 | 9 | 86 | $83:14,\quad 85:10$ | $\varnothing$ |
| 100.A4.1 | 0 | 1 | $3:14,\quad 5:\mathrm{pass}$ | $\{5\}$ |
| 100.A4.2 | 9 | 48 | $144:14,\quad 146:\mathrm{pass}$ | $\{146\}$ |
| 100.A4.3 | 5 | 148 | $7:\mathrm{pass},\quad 9:5$ | $\{7\}$ |
| 100.A4.4 | 13 | 244 | $107:5,\quad 109:3$ | $\varnothing$ |
| 100.A5.1 | 2 | 1 | $53:1,\quad 55:\mathrm{pass}$ | $\{55\}$ |
| 100.A5.2 | 0 | 2 | $54:3,\quad 56:\mathrm{pass}$ | $\{56\}$ |
| 100.A5.3 | 9 | 95 | $80:1,\quad 82:10$ | $\varnothing$ |
| 100.A6.1 | 14 | 1 | $114:10,\quad 116:\mathrm{pass}$ | $\{116\}$ |
| 100.A6.2 | 13 | 263 | $35:6,\quad 37:5$ | $\varnothing$ |
| 100.A7.1 | 4 | 1 | $141:11,\quad 143:\mathrm{pass}$ | $\{143\}$ |
| 100.A7.2 | 8 | 10 | $21:12,\quad 23:\mathrm{pass}$ | $\{23\}$ |
| 100.A7.3 | 0 | 11 | $22:1,\quad 24:\mathrm{pass}$ | $\{24\}$ |
| 100.A7.4 | 12 | 45 | $160:8,\quad 162:9$ | $\varnothing$ |
| 100.A8.1 | 1 | 1 | $96:\mathrm{pass},\quad 98:7$ | $\{96\}$ |
| 100.A8.2 | 9 | 48 | $55:\mathrm{pass},\quad 57:8$ | $\{55\}$ |
| 100.A8.3 | 12 | 131 | $98:\mathrm{pass},\quad 100:12$ | $\{98\}$ |
| 100.A8.4 | 8 | 157 | $26:\mathrm{pass},\quad 28:11$ | $\{26\}$ |
| 100.A8.5 | 9 | 219 | $71:13,\quad 73:10$ | $\varnothing$ |
| 100.A9.1 | 13 | 1 | $51:\mathrm{pass},\quad 53:1$ | $\{51\}$ |
| 100.A9.2 | 7 | 39 | $117:14,\quad 119:\mathrm{pass}$ | $\{119\}$ |
| 100.A9.3 | 8 | 11 | $88:1,\quad 90:\mathrm{pass}$ | $\{90\}$ |
| 100.A9.4 | 10 | 276 | $107:9,\quad 109:7$ | $\varnothing$ |
| 100.A10.1 | 2 | 1 | $136:5,\quad 138:\mathrm{pass}$ | $\{138\}$ |
| 100.A10.2 | 10 | 57 | $38:\mathrm{pass},\quad 40:6$ | $\{38\}$ |
| 100.A10.3 | 6 | 53 | $80:15,\quad 82:9$ | $\varnothing$ |

表中每一行都由(100.4)、(100.6)直接计算。特别地，没有在某个非最终块悄悄舍去第二条幸存支路：26个非最终块各留下恰一轨道，十个最终块均留下空集，共检查72个扫描输入分支。例如模板 $r=1$ 的首块在 $c=1$ 给 $[102]$、$[104]$，后者在第13读被删除，前者通过全部十五读；最后一块在 $c=205$ 给 $[79]$、$[81]$，分别在第3读和第12读删除。因此每个 $B(J_r)$ 都拒绝其代表轨道。100.5的程序从原始 $(a,b,\mathrm{startup})$ 转移重新生成整表，另以(100.6)核对每个分支的十五个位置；表内数值不作为程序的输入。

### 100.4 覆盖全部零类根并提升到实际来源

先核对覆盖。模341有

$$
261^{30}=1,\qquad261^6=47,\qquad261^{10}=67,\qquad261^{15}=340.
\tag{100.9}
$$

30的任一真因子都整除6、10或15，后三个幂均不为1，故261的乘法阶恰为30。记 $\mathcal R=\{1,2,3,4,5,7,8,14,16,19\}$。对上表十个代表直接枚举各30次幂，得到

$$
(\mathbb Z/341\mathbb Z)^\times
=\bigsqcup_{r\in\mathcal R}r\langle261\rangle,
\qquad \varphi(341)=(11-1)(31-1)=300.
\tag{100.10}
$$

每个陪集有30元，十个陪集两两不交；程序独立核对不交性及其并恰为全部单位。又因 $261^{15}=-1$，对每个单位 $w$，恰有唯一一对

$$
(r,k)\in\mathcal R\times\{0,\ldots,14\},\qquad
261^kw\in\{r,-r\}\pmod{341}.
\tag{100.11}
$$

同一陪集保证存在；若两个指数相差小于15却给相同符号轨道，则相应幂为 $1$ 或 $-1=261^{15}$，由阶30知两指数相同。因此这是300个单位按全局正负号配成的150种选择。

现在给出定理100.1的见证。初始 $c=0$ 时，首个 $T$ 前线性量 $qs$ 的两相位剩余为 $\pm73w$。73为单位，故全部41个非单位 $w$ 都被词 $T$ 拒绝，包括 $w=0$；这里 $41=31+11-1$。若 $w$ 为单位，首读的两个相位均通过，启动标志变为1。取(100.11)中的 $(r,k)$，置

$$
W_w=T\,R^kB(J_r).
\tag{100.12}
$$

$R^k$ 将其轨道送至 $(0,[r])$，每个相位仍按341共同选择；随后100.3的完整分支表使终态集合为空。即使 $k=0$ 或模板首指数为0，先前的 $T$ 已使后续 $G$ 前的相位选择合法。故所有341个初始根各有一个拒绝词。不同单位符号对给150个不同的词，加非单位的 $T$ 共151个。

还须将拒绝剩余路径接回实际合同。对任意已经固定的非负整数提升 $s_0$，任意合法日程在相邻原语之间的有限批可合并到下一原语之前；用总指数模2得到97.9—97.10的一个相位。首个 $R/G$ 前必须为零，首个 $T$ 前允许两种奇偶，正是同一个启动约定。每份实际日程由此给出一个合法相位串。逐原语归纳，其全部已读响应为1的前缀投影为相应 NFA 路径，实际 gcd 与投影的 gcd 相等；一旦实际响应非单位，该 $T$ 边就被过滤。若整词的实际读取全为1，投影便是一条完整接受路径。证书终态为空排除了这种可能，所以对这个词的每份实际日程都有非单位读取。

反向，任何有限接受相位串都能通过在对应允许切口实际施加 $E^0$ 或 $E^1$ 提升到这同一份 $s_0$ 上：$M,E,G$ 保持非负性，且每一步继续操作此前的实际整数后继。这也说明轨道转移没有凭空添加物理能力。约化只合并了有限模语义，实际 $E^2\ne I$；偶数批隐藏事件仍然是实际历史的一部分，其次数、整数增长及经过时间没有被删除或恢复。证明的否定方向覆盖任意有限批数，不是仅覆盖批数0、1的特殊日程。

若初始剩余属于 $U_{\rm init}$，按定义就应接受其所有有限词，尤其应接受(100.12)或 $T$，矛盾。故(100.2)成立，且 $0\notin c(U_{\rm init})$，从而式(97.12)为假。命题97.2的固定来源桥仍然成立；这里补上的正是其零类语言判定。证毕。

对 $J_r$ 长度 $m$，完整词的计数为

$$
|W_w|=1+k+31m+\sum_{i=1}^m j_i,\qquad
N_T=1+15m,\qquad N_G=m.
\tag{100.13}
$$

十个模板及 $0\le k\le14$ 给最大值 $(209,76,5)$，由 $r=14,k=14$ 的词同时达到。提前遇到空集可以停止验证，但这些上界计算整个已指定词。它们不限制隐藏事件总数、整数宽度或实际历时。

### 100.5 从原始转移直接重放的有限核验

下面是可独立运行的 Python 3.9 标准库程序；必须启用断言，即不用 `-O`。唯一给定的模板数据是上面的指数表。程序由整数矩阵重新计算 $E=M^{15}$，逐原语枚举97.9允许的相位，以原始坐标和启动标志保存候选状态。`step` 在读前施加相位，随后才过滤 $T$，从不在读取过滤后补作 $E$ 闭包。轨道函数只用于核对表格及扫描恒等式，341个初始根的整词重放直接调用原始转移。它不是使用预先计算的宏转移表或搜索结果替代证书。

每步候选集恰为该前缀所有全一模路径的终态集：初始单根成立，归纳步枚举所有合法相位和原语后继，且仅删除非单位读取。合并相同的 $(a,b,\mathrm{startup})$ 不丢失未来可能性，因为97.10的下一步只依赖这个状态及下一字母。由100.4的实际投影桥，空集便证明给定词下所有有限隐藏历史均不能全一。反之，有限长度搜索没有找到拒绝词，不能证明某根接受所有长度的词；本程序验证已给定的完整拒绝证书，不作这样的未发现推论。

```python
from math import gcd
from time import monotonic
import json

if not __debug__:
    raise RuntimeError("Run without -O: assertions are the certificate checks")
deadline = monotonic() + 120
H = 341
J = {1: (4, 3, 6, 13), 2: (4, 1, 12, 10),
     3: (10, 13, 9), 4: (0, 9, 5, 13), 5: (2, 0, 9),
     7: (14, 13), 8: (4, 8, 0, 12),
     14: (1, 9, 12, 8, 9), 16: (13, 7, 8, 10),
     19: (2, 10, 6)}
M, I = ((0, 1), (1, 1)), ((1, 0), (0, 1))
def mul(A, B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))
E = I
for _ in range(15):
    E = mul(E, M)
assert E == ((377, 610), (610, 987))
assert mul(E, E) != I
assert tuple(tuple(x % H for x in row) for row in mul(E, E)) == I
def apply(A, a, b):
    return ((A[0][0]*a + A[0][1]*b) % H,
            (A[1][0]*a + A[1][1]*b) % H)
def coord(a, b):
    return ((a + 81*b) % H, (a + 261*b) % H)
def source(c, w, startup):
    b = 36*(w-c) % H
    return ((c-81*b) % H, b, startup)
def canon(w):
    return min(w % H, -w % H)
def orbits(S):
    return {(coord(a, b)[0], canon(coord(a, b)[1]))
            for a, b, startup in S}

# Literal (97.9)-(97.10): phase BEFORE action; T filters BEFORE returning.
edges = 0
def step(S, letter):
    global edges
    if monotonic() > deadline:
        raise TimeoutError("120 second replay bound")
    out = set()
    for a, b, startup in S:
        phases = (0,) if startup == 0 and letter in "RG" else (0, 1)
        for epsilon in phases:
            edges += 1
            x, y = (a, b) if epsilon == 0 else apply(E, a, b)
            if letter == "R":
                out.add((y, (x+y) % H, 1))
            elif letter == "G":
                out.add(((x+1) % H, y, 1))
            elif letter == "T":
                if gcd(2*x + 3*y, H) == 1:
                    out.add((x, y, 1))
            else:
                raise ValueError(letter)
    return out
def run(S, word):
    for letter in word:
        S = step(S, letter)
        if not S:
            break
    return S

# Linear identities are checked on an integer basis; G adds alpha=(1,0).
assert 180*36 % H == 1 and gcd(73, H) == 1
for a, b in ((1, 0), (0, 1)):
    c, w = coord(a, b)
    assert coord(*apply(E, a, b)) == (c, -w % H)
    assert coord(*apply(M, a, b)) == (81*c % H, 261*w % H)
    assert (2*a+3*b) % H == (270*c+73*w) % H
assert coord(1, 0) == (1, 1)
assert pow(81, 15, H) == 1 and pow(261, 15, H) == H-1
assert min(n for n in range(1, 31) if pow(261, n, H) == 1) == 30
units = {w for w in range(H) if gcd(w, H) == 1}
cosets = [{r*pow(261, k, H) % H for k in range(30)} for r in J]
assert all(len(A) == 30 for A in cosets)
assert all(not A & B for i, A in enumerate(cosets) for B in cosets[i+1:])
assert set().union(*cosets) == units and len(units) == 300

C = "RT"*15
blocks = {r: "".join("R"*j + "G" + C for j in exps)
          for r, exps in J.items()}
trace_rows, tested_branches = [], 0
for r, exps in J.items():
    S = {source(0, r, 1)}
    for i, j in enumerate(exps, 1):
        before = run(S, "R"*j + "G")
        O = sorted(orbits(before))
        assert len(O) == 2 and len({c for c, w in O}) == 1
        entries, expected = [], set()
        for c, w in O:
            tested_branches += 1
            bad = [t for t in range(1, 16)
                   if all(gcd(270*pow(81, t, H)*c +
                              sign*73*pow(261, t, H)*w, H) > 1
                          for sign in (-1, 1))]
            actual = orbits(run({source(c, w, 1)}, C))
            assert actual == (set() if bad else {(c, w)})
            expected |= actual
            entries.append(str(w) + ":" + (str(bad[0]) if bad else "pass"))
        S = run(before, C)
        assert orbits(S) == expected
        assert len(expected) == (0 if i == len(exps) else 1)
        row = (r, i, j, O[0][0], entries,
               sorted(w for c, w in expected))
        trace_rows.append(row)
        print("trace", row)
    assert not S

# Replay every complete assigned word from its own initial (a,b,0) root.
words, lengths, reads, grafts = set(), [], [], []
root_edges = edges
rejected = 0
for w in range(H):
    if w in units:
        choices = [(r, k) for r in J for k in range(15)
                   if pow(261, k, H)*w % H in (r, -r % H)]
        assert len(choices) == 1
        r, k = choices[0]
        word = "T" + "R"*k + blocks[r]
    else:
        word = "T"
    # Costs are computed from the WHOLE word, even if run exits early.
    words.add(word)
    lengths.append(len(word))
    reads.append(word.count("T"))
    grafts.append(word.count("G"))
    root = source(0, w, 0)
    assert coord(*root[:2]) == (0, w)
    assert not run({root}, word), (w, word)
    rejected += 1
assert len(J) == 10 and sum(map(len, J.values())) == 36
assert len(trace_rows) == 36 and tested_branches == 72
assert rejected == 341 and len(words) == 151
assert (max(lengths), max(reads), max(grafts)) == (209, 76, 5)
print(json.dumps({"roots_rejected": rejected, "unit_roots": len(units),
                  "nonunit_roots": H-len(units), "distinct_words": len(words),
                  "templates": len(J), "exponents": len(trace_rows),
                  "scan_branches": tested_branches,
                  "max_word": max(lengths), "max_reads": max(reads),
                  "max_grafts": max(grafts), "root_phase_edges": edges-root_edges,
                  "total_phase_edges": edges,
                  "powers_261_6_10_15": [pow(261, n, H) for n in (6, 10, 15)]},
                 sort_keys=True))
```

重放结果为：十个模板的36行、72个扫描输入分支全部通过上述核对；341个初始根全部被各自指定词拒绝，其中单位根300个、非单位根41个；不同词151个，整词最大计数为209个原语、76读、5次接枝。程序还独立验证(100.7)、阶30和十陪集覆盖，设有120秒核验期限。本节的证明状态是正文推导加显式有限算术证书，未作 Lean/kernel 核验。

### 100.6 来源依赖的量词与保留边界

(100.3)中的词依赖未知来源的模 $w$，这种数学选择没有成为观察者可用的查询或决策。它没有把 $\forall s_0\ \exists W\ \forall h$ 交换成 $\exists W\ \forall s_0\ \forall h$，也没有将这151个词当作可在同一初始来源上逐个重试的实验：执行一个词后来源已经改变，而合同没有复位。本文既不声称存在统一拒绝词，也不声称不存在；同样未给出自适应识别协议、完整 $Q_{341}$ 取得或其不可能性，另340个初始商类的 $U_{\rm init}$ 成员资格仍未判定。式(97.12)失败只排除那一种覆盖全类的固定源全一障碍。

承重的实际来源、启动 NFA 及模路径提升复用第97节；第98节的含量取得、条件端点恢复与第99节无接枝接口的秩判据各保留原合同，不代替此处含 $G$ 的分支证书。[Fibonacci 卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)第33、38节的缺陷与 Smith 结构、第130节的固定实际接枝及整数词语义是既有供应项，模周期没有在这里被升级为实际复位。既有 [ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) 处理确定更新并要求读出交织，不直接裁定本节带隐藏相位的 NFA 语言；本节没有编译或宣称获得其新 Lean 应用。新增内容是共同符号扫描、十模板覆盖及它们对零类固定源量词的有限证书证明，不主张新的通用自动机定理或未经文献核查的原创优先权。

对于关系、边界和记忆的原问题，这里确定的是：自主商的语义存在与原接口的实际取得之间，不能再用式(97.12)所设想的全类全一族充当障碍。已取得端点加保留运输所给的恢复关系仍按95.7、96.7、98.4解释；本证书不额外取得任一端点，不恢复隐藏时间，也不主张物理统一、最小词、最少读取或长期目标已经完成。

## 100.99 追加锚
## 101. 整纤维全词接受与逐协议固定源的取得障碍

本节接续100.6留下的共同词问题。在完全相同的 $H=341,d=15$ 原接口中，每个初始商类的整个剩余纤维都接受每个有限 $R/G/T$ 词，其中每个 $T$ 要求响应1。因此不存在一个有限共同词，能对零类的所有来源及全部合法日程迫使非单位响应。进一步，对每份固定的确定性协议，每个商类都有一个固定实际来源及一份相容日程实现该协议的全一分支；这足以排除对任何非恒定初始商任务的保证有限精确取得。本节不改判第100节的逐根拒绝结论：这里的根允许依赖整份词或协议。证据是下述普通数学论证及可从正文独立生成、检查的有限证书，未作 Lean/kernel 核验。

### 101.1 相同来源合同与饱和信念

完全沿用97.1及97.9—97.10。一次执行先固定未知 $s_0=(a,b)\in\mathbb N^2$，自然数包含零；实际操作是 $R(s)=Ms$、$G(s)=s+(1,0)$，$T$ 为付费、精确、不扰动的 $\gcd((2,3)s,341)$ 读取。$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$，隐藏批为 $E^k$，$E=M^{15}=\left(\begin{smallmatrix}377&610\\610&987\end{smallmatrix}\right)$；每个 $k\ge0$ 有限，只在已声明切口发生。首原语为 $R/G$ 时其前没有隐藏事件，首原语为 $T$ 时其前允许隐藏批。原语内部没有隐藏事件，每个请求完成；完成信号不报告历时。控制器可作任意确定性本地计算、保存任意记忆，但初始可见资料与来源无关，没有复位、坐标、大小、时钟、相位、可指定等待或免费观察。实际后继连续来自同一份 $s_0$，不换成模代表。

复用97.3—97.4，在 $Z=\mathbb Z/341\mathbb Z$ 上写

$$
\begin{aligned}
c&=a+81b,& w&=a+261b,\\
E(c,w)&=(c,-w),& R(c,w)&=(81c,261w),\\
G(c,w)&=(c+1,w+1),& qs&=270c+73w.
\end{aligned}
\tag{101.1}
$$

$c$ 标记完整自主商，$w$ 只是证明坐标。$E^2=I$ 仅在模341上成立，整数 $E^2\ne I$。令 $u(s)$ 表示本次 gcd 为1，定义 $\operatorname{Sat}(B)=B\cup EB$。对纤维内集合用 $(c,S)$ 表示 $\{(c,w):w\in S\}$；饱和恰好是 $S=-S$。在已完成原语后的合法切口，饱和包含实际允许的零或一次隐藏事件，不是增加一次读取。若只关心终端接受，$\operatorname{Sat}(B)\ne\varnothing$ 当且仅当 $B\ne\varnothing$，所以末尾饱和既不增加通过条件，也不补读一个 $T$。

**定义 101.1（共同相位安全集与整纤维）。** 置

$$
\begin{aligned}
A_c&=\{w\in Z:\exists\epsilon\in\{0,1\},\
 \gcd(270c+(-1)^\epsilon73w,341)=1\},\\
I_x&=\{(c,w):c=x,\ w\in Z\}.
\end{aligned}
\tag{101.2}
$$

$A_c=-A_c$。其中一个 $\epsilon$ 必须同时使模11与模31分量成为单位；不能让两个素因子各选自己的符号。例如原坐标 $(a,b)=(1,212)$ 的两个相位 gcd 分别为11、31，故它不安全，即使每个素因子分别都能选出不被自己整除的相位。

**引理 101.2（饱和集合的原语像与启动）。** 对 $S=-S$，启动完成后的全一信念转移恰为

$$
\begin{aligned}
\Phi_R(c,S)&=(81c,261S),\\
\Phi_G(c,S)&=(c+1,(S+1)\cup(S-1)),\\
\Phi_T(c,S)&=(c,S\cap A_c).
\end{aligned}
\tag{101.3}
$$

三种转移均对集合包含单调。首个 $R/G$ 也可对整个 $I_x$ 及其中任何 $E$ 闭子集使用这三个式子中相应的一式，但实现时首动作前只取相位零；首个 $T$ 使用合同允许的两相位。

证明。后续原语前的相位把输入变为 $\operatorname{Sat}(B)$，已饱和时不改变输入集合。$R$ 与 $E$ 交换，故其像已经饱和。$G$ 的直接像为 $S+1$，饱和再给 $-(S+1)=S-1$。$T$ 先留下实际满足 $u$ 的相位，再饱和；一对 $\{w,-w\}$ 留下，当且仅当至少一个共同符号使完整 gcd 为1。这得到(101.3)。像、并集和与固定集合求交均单调。启动的 $R/G$ 不需要偷偷插入相位：输入子集本身 $E$ 闭，其中每个点已是一个允许的初始根，直接相位零的像再作动作后饱和即可。首读允许相位，正好给第三式。证毕。

### 101.2 有限族证书及包含方向

**定义 101.3（信念下界证书）。** 对每个 $c\in Z$ 给有限非空族 $\mathcal F_c$，每个成员 $S\subseteq Z$ 非空且 $S=-S$，并要求

$$
\begin{aligned}
S\in\mathcal F_c&\Longrightarrow 261S\in\mathcal F_{81c},\\
S\in\mathcal F_c&\Longrightarrow\exists S'\in\mathcal F_{c+1},\quad
 S'\subseteq(S+1)\cup(S-1),\\
S\in\mathcal F_c&\Longrightarrow S\subseteq A_c.
\end{aligned}
\tag{101.4}
$$

族成员是当前可达信念的下界，不是要保留的全部初始根。第三项使 $T$ 原样保留该成员。程序用补集 $h=Z\setminus S$ 的341位整数编码；对 $G$，像的补集是

$$
F=(h+1)\cap(h-1).
\tag{101.5}
$$

候选成员 $S'=Z\setminus h'$ 可作下界的正确条件是 $F\subseteq h'$，即 $S'\subseteq Z\setminus F$；反向包含不够。验证器既检查补集方向，也检查幸存集合方向。

**命题 101.4（本实例的有限证书）。** 下列两段程序生成并验证一个满足(101.4)的族：25个规范 $c$ 纤维中共有19,844个基础补集掩码，经15个 $R$ 旋转展开后恰有297,660个不同成员，覆盖全部341个当前 $c$ 类；成员最小大小为294。基础 JSON 的 SHA-256 为 `8870a41115f6ce30c34f9414eb64774c314a7e0410c7204ff443744a16c6c03f`。

证明。构造只负责提供候选；结论依赖独立验证器逐项检查(101.4)，不依赖搜索过程被信任。为说明候选怎样从小程序重建，令 $\rho(c,S)=(81c,261S)$。由于 $81^{15}=1$、$261^{15}=-1$，$\rho^{15}$ 在对称集合上为恒等。算术预处理先计算

$$
D_c=\{w:\exists j\in\{0,\ldots,14\},\
261^jw\notin A_{81^jc}\}.
\tag{101.6}
$$

它是15个旋转读取位置的共同失败域；这是从(101.2)计算出的域，不是另一个外部输入表。构造从 $(0,Z\setminus D_0)$ 开始，按 $R$ 旋转归一化，并对每个保留成员的15个旋转生成 $G$ 像，再删去目标 $D_c$。对应补集为 $D_c\cup F$。每个规范纤维保留按包含极大的补集：若新补集包含于旧补集，旧成员已给出更小的可用下界；若旧补集包含于新补集，则用新成员替换旧成员。队列必须真正耗尽；空幸存集、记录上限、边上限或闹钟触发都以失败退出，不得把失败记为闭合。

验证器不读构造器种子、归一化表或扫描域。它从原整数矩阵计算 $E$，对全部 $341^2=116281$ 个原坐标状态独立核对坐标逆、共同相位、$R/G/T$ 饱和像，并从原 gcd 计算 $A_c$。随后展开给定的补集，检查对称、非空、安全、覆盖及所有成员的三种闭包义务。最后还逐类核对整纤维的首次动作。运行得到每种义务297,660项，总计892,980项，且所有精确计数与摘要断言通过。于是(101.4)成立。这里的294是一个成员所含的**当前剩余**数量；多条历史可汇合到同一剩余，本证书不声称每个词保留294个不同的初始根。证毕。

### 101.3 从当前信念下界到所有有限词

**定理 101.5（每个整初始纤维接受所有有限词）。** 在97.9—97.10的精确启动语义下，令 $L_{\rm init}(r)$ 如第97节，则

$$
\forall x\in Z,\qquad
\bigcup_{r\in I_x}L_{\rm init}(r)=\{R,G,T\}^*.
\tag{101.7}
$$

因此特别不存在 $W$，使零类每个初始来源在每份合法隐藏日程下执行 $W$ 都产生一次非1响应。

证明。固定 $x$ 及有限词 $W$。空词从任一根接受。非空时先在 $\mathcal F_x$ 中取一成员 $S_0\subseteq Z$；它包含于整个初始纤维。若首字母是 $R/G$，使用引理101.2的相位零启动论证；若为 $T$，使用允许的首读相位。由(101.4)，其饱和实际可达信念中仍含一个非空族成员。此后归纳：若成员 $S$ 包含于当前饱和可达信念 $B$，单调性给 $\Phi_X(S)\subseteq\Phi_X(B)$；$R$ 的像本身是成员，$G$ 的像包含一个成员，$T$ 原样保留成员。故每个前缀都有非空饱和可达信念。终端饱和不改变非空性，所以 $W$ 有一条真实启动 NFA 接受路径，每次 $T$ 均沿单位边。整个路径从 $I_x$ 中的某一个根开始，并没有在中途换根。证毕。

式(101.7)是完整语言证书的结论，不是有限搜索未找到拒绝词的推断；搜索仅用来给出可独立穷尽核验的有限不变量。零类首读留下300个单位根这一事实仍成立，但单独这一筛选并不足以推出(101.7)。

### 101.4 一个预选实际提升与固定协议的相容路径

**引理 101.6（有限模路径的单源提升）。** 固定一个根 $r$，一次选定任意非负整数提升 $s_r\equiv r\pmod{341}$。从 $(r,0)$ 出发的任意有限接受路径，均可从同一份 $s_r$ 连续实现，实际每个读取等于1。

证明。复用97.2的模路径提升：在路径使用的允许切口按相位位实际施加 $E^0$ 或 $E^1$，随后执行整数原语。首 $R/G$ 的位必须是零。每一步均保持非负性，其模约化与给定路径相同，故 gcd 与模读取一致。绝不约化实际后继、实际消去两次 $E$ 或重置来源。所有根都可预选严格正提升，例如先取两个坐标的标准代表，再各加341；所有正提升在这些操作下也保持正性。末尾饱和可省去，不补一个读取。证毕。

**定理 101.7（逐协议、逐类的固定实际来源）。** 对97.1合同中的任意固定确定性协议 $P$ 及任意 $x\in Z$，存在一个实际来源 $s_0$ 和一份合法隐藏日程 $\sigma$，使

$$
\forall P\ \forall x\ \exists s_0\ \exists\sigma,\qquad
 c(s_0)=x\quad\text{且 }P(s_0,\sigma)\text{ 的全部 }T\text{ 响应为1}.
\tag{101.8}
$$

结论对来源域 $\mathbb N^2$ 或 $\mathbb N_{>0}^2$ 均成立；来源和日程可以依赖整份 $P$，但执行中来源固定。

证明。先为 $I_x$ 的341个剩余根各固定一个实际提升。沿 $P$ 的全一响应分支运行其确定性本地计算。共同初始资料、无时钟或其他侧信道保证原语词与内部计算分支由 $P$ 唯一确定。

若该分支只请求有限多个原语，得到有限词 $W$，包括空词。定理101.5给某个根的一条完整接受路径；引理101.6从这个根的预选提升实现它。此后若 $P$ 停止，则实际执行也停止；若 $P$ 在有限原语后永远作本地计算，则实际执行也停留在相同内部计算分支。这两种情况都不需要额外观察或新来源。

若全一分支请求无限多个原语，把这些字母固定为一个无限词。用一个虚根接341个已选剩余根，再接每个根的所有合法接受相位前缀，构成前缀封闭的树。虚根有341个孩子；根选定以后，每个节点至多两个孩子，启动 $R/G$ 处至多一个。定理101.5使每个有限深度非空，故由 König 引理存在一条无限分支。这条分支一次选出一个根和一整条相容相位路径，而非对每个长度重新选择来源。逐步沿其固定提升执行，引理101.6的归纳给出无限实际轨迹：每个被用切口至多一次 $E$，每个原语按合同完成。无限路径不存在有限时刻内的无限批要求；也不引入新公平性。证毕。

不能只说“每个前缀有一个来源”就直接宣告存在无限执行；上面的有限根集、固定提升与有限分支树正是所需桥梁。它也没有给观察者提供选根或取得标签的算法。

### 101.5 初始商任务的取得不可能性及量词边界

**推论 101.8（任意非恒定初始商函数均不能保证有限取得）。** 设 $Y$ 为任意输出集合，$f:Z\to Y$ 非恒定。在上述原接口中，不存在确定性协议对每个实际来源、每份合法隐藏日程都在有限执行后停止并准确输出 $f(c(s_0))$；不要求保证中预设统一时间或统一原语数上界。

证明。假设有这样的 $P$。定理101.7为每个类实现同一全一可见分支。若该分支停止，输出某个固定 $y$；因 $f$ 非恒定，存在类 $x$ 满足 $f(x)\ne y$，其见证执行便输出错误。若该分支不停止，则无论它无限请求原语，还是仅请求有限多个原语后无限内部计算，定理101.7都提供一个合法的不停止执行，违反保证有限终止。证毕。

第100节与本节分别给出

$$
\begin{aligned}
&\forall r\in I_0\ \exists W_r\ \forall\sigma:
 \text{从 }r\text{ 执行 }W_r\text{ 时有一次非1读取},\\
&\forall W\ \forall x\ \exists r\in I_x\ \exists\sigma:
 \text{从 }r\text{ 执行 }W\text{ 的全部读取为1}.
\end{aligned}
\tag{101.9}
$$

两者没有矛盾：对每个根有自己的拒绝词，不推出一个词拒绝整个纤维；对每个词有可接受的根，不推出一个根接受所有词。事实上第100节已排除 $I_0\cap U_{\rm init}$ 的成员，所以仍不能声称 $c(U_{\rm init})=Z$，也不能声称 $\exists r\ \forall P$。本节取得障碍所需的是(101.8)的 $\forall P\ \forall x\ \exists s_0\ \exists\sigma$。它不要求不同类共用一个日程，不把见证变成对所有未来统一的在线相位选择器，与97.1的空因果不变量相容。协议可以保存任意记忆；这里没有推出记忆大小下界、最优操作数或随机协议结论。

### 101.6 自足的生成与独立验证程序

以下恰有两个 Python 程序块，依次保存为同一**全新临时目录**中的 `construct.py` 与 `check.py`，依次执行 `python3 construct.py`、`python3 check.py`。只需 Python 3.9或更新版本的标准库和支持 `SIGALRM` 的 POSIX 环境；必须开启断言，两个程序都会拒绝 `python -O`。构造器只写该目录中的 `closure-family.json`，验证器唯一的数据输入就是这个生成文件。不需仓库、外部两兆字节表、隐藏扫描域、其他构造程序或类锚点文件。摘要是输出封印及复现核对，不代替闭包证明。

每个程序从开始起各受硬120秒闹钟约束。构造器最多记录100,000个已入队搜索记录（包括已被支配删除的记录），最多生成1,500,000条闭包边；本实例实际为28,838个记录、410,475条边，队列余项为零。每条生成边是一个保留成员的某个 $R^j$ 后接 $G$ 再作安全筛选的候选。算术与扫描预处理、补集比较、位排列及索引位运算不计入这个**闭包边计数**，但全都受总闹钟约束。验证器另计原坐标算术预处理、索引构建及892,980项闭包验证，不能把搜索边预算说成全部计算成本。达到任一上限而未完成时只能报告失败；不得提高上限来复现本结论。

```python
"""Bounded certificate construction without tables or third-party packages."""
from collections import deque
from math import gcd
from pathlib import Path
import hashlib, json, signal, time

if not __debug__:
    raise RuntimeError("assertions required: do not use python -O")

def expired(signum, frame):
    raise TimeoutError("120 second constructor bound")

signal.signal(signal.SIGALRM, expired)
signal.alarm(120)
t0 = time.monotonic()
H = 341
ALL = (1 << H)-1
cp = [pow(81,j,H) for j in range(15)]
wp = [pow(261,j,H) for j in range(15)]
tables = [[1 << (k*w % H) for w in range(H)] for k in wp]
bad = [sum(1 << w for w in range(H)
           if any(gcd(270*(cp[j]*c % H)+73*(wp[j]*w % H),H) != 1
                  and gcd(270*(cp[j]*c % H)-73*(wp[j]*w % H),H) != 1
                  for j in range(15)))
       for c in range(H)]

def perm(h,j):
    if j == 0:
        return h
    out = 0
    while h:
        b = h & -h
        out |= tables[j][b.bit_length()-1]
        h ^= b
    return out

canonical = []
for c in range(H):
    orbit = [c*k % H for k in cp]
    m = min(orbit)
    canonical.append((m,[j for j,d in enumerate(orbit) if d == m]))

def normalize(c,h):
    m, js = canonical[c]
    return m,max(perm(h,j) for j in js)

families = {m:{} for m,_ in canonical}
first = normalize(0,bad[0])
assert first[1] != ALL, "empty initial survivor"
families[first[0]][first[1]] = None
todo = deque([first])
records, transitions = 1,0
preprocessing_seconds = time.monotonic()-t0
search_start = time.monotonic()
while todo:
    c,h = todo.popleft()
    if h not in families[c]:
        continue
    for j in range(15):
        if transitions >= 1500000:
            raise RuntimeError("closure edge cap exhausted")
        rh = perm(h,j)
        target = (cp[j]*c+1) % H
        plus = ((rh << 1) & ALL) | (rh >> (H-1))
        minus = (rh >> 1) | ((rh & 1) << (H-1))
        nc,nh = normalize(target,bad[target] | (plus & minus))
        transitions += 1
        assert nh != ALL, 'empty survivor encountered'
        family = families[nc]
        if any(nh & old == nh for old in family):
            continue
        if records >= 100000:
            raise RuntimeError("search record cap exhausted")
        dominated = [old for old in family if old & nh == old]
        for old in dominated:
            del family[old]
        family[nh] = None
        todo.append((nc,nh))
        records += 1
# Reaching this point requires genuine queue exhaustion; no break path.
assert not todo
assert records <= 100000 and transitions <= 1500000
assert (records, transitions) == (28838, 410475)
assert len(families) == 25
assert sum(map(len, families.values())) == 19844
assert all(families.values())
payload = {str(c):[str(h) for h in family] for c,family in families.items()}
data = json.dumps(payload).encode("utf-8")
seal = hashlib.sha256(data).hexdigest()
assert seal == "8870a41115f6ce30c34f9414eb64774c314a7e0410c7204ff443744a16c6c03f"
# No external table, seed file, scan-domain file, or imported constructor.
out = Path(__file__).parent / "closure-family.json"
assert not out.exists(), "use a fresh directory"
tmp = out.with_suffix(".json.tmp")
tmp.write_bytes(data)
tmp.replace(out)
report = {"status":"closed", "records":records, "closure_edges":transitions,
          "base_members":19844, "base_fibers":25, "pending":len(todo),
          "certificate_bytes":len(data), "certificate_sha256":seal,
          "preprocessing_seconds":preprocessing_seconds,
          "closure_seconds":time.monotonic()-search_start,
          "seconds":time.monotonic()-t0, "external_data_inputs":[]}
print(json.dumps(report, sort_keys=True))
signal.alarm(0)
```

第二段独立从原坐标建立安全集与原语作用；其包含查询用目标纤维的位索引完成，不调用构造器的扫描或剪枝程序。

```python
"""Independent finite-certificate validator; Python standard library only."""
from pathlib import Path
from math import gcd
import hashlib, json, signal, time

if not __debug__:
    raise RuntimeError("assertions required: do not use python -O")

def expired(signum, frame):
    raise TimeoutError("120 second validator bound")

signal.signal(signal.SIGALRM, expired)
signal.alarm(120)
start = time.monotonic()
root = Path(__file__).parent
H = 341
U = (1 << H) - 1

def mm(A, B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))

M = ((0, 1), (1, 1))
E = ((1, 0), (0, 1))
for _ in range(15):
    E = mm(M, E)
assert E == ((377, 610), (610, 987))
assert mm(E, E) != ((1, 0), (0, 1))

def act(A, s):
    return tuple(sum(A[i][j]*s[j] for j in range(2)) % H for i in range(2))

def coord(s):
    a, b = s
    return (a + 81*b) % H, (a + 261*b) % H

def inverse(c, w):
    b = 36*(w-c) % H
    return (c-81*b) % H, b

def unit(s):
    return gcd(2*s[0] + 3*s[1], H) == 1

def saturate(states):
    return states | {act(E, s) for s in states}

safe = [0]*H
raw_checks = 0
for a in range(H):
    for b in range(H):
        s = a, b
        c, w = coord(s)
        assert inverse(c, w) == s
        e = act(E, s)
        assert act(E, e) == s
        assert coord(e) == (c, -w % H)
        assert coord(act(M, s)) == (81*c % H, 261*w % H)
        assert (2*a+3*b) % H == (270*c+73*w) % H
        orbit = {s, e}
        # First R/G use no pre-phase: every member of this initial orbit
        # is an independently permitted root. Post-saturation is only
        # a representation at the next legal cut.
        rnext = saturate({act(M, x) for x in orbit})
        gnext = saturate({((x[0]+1) % H, x[1]) for x in orbit})
        tnext = saturate({x for x in orbit if unit(x)})
        assert {coord(x) for x in rnext} == {(81*c % H, 261*v % H) for v in (w, -w)}
        assert {coord(x) for x in gnext} == {((c+1) % H, (v+d) % H) for v in (w, -w) for d in (-1, 1)}
        passes = unit(s) or unit(e)
        assert {coord(x) for x in tnext} == ({(c, w), (c, -w % H)} if passes else set())
        if passes:
            safe[c] |= 1 << w
        raw_checks += 1

assert raw_checks == H*H == 116281
arithmetic_seconds = time.monotonic()-start
bad = (1, 212)
assert (gcd(2*bad[0]+3*bad[1], H), gcd(2*act(E,bad)[0]+3*act(E,bad)[1], H)) == (11, 31)
bc, bw = coord(bad)
assert not (safe[bc] >> bw) & 1

cp = [pow(81, j, H) for j in range(15)]
wp = [pow(261, j, H) for j in range(15)]
assert pow(81,15,H) == 1 and pow(261,15,H) == H-1
tables = [[1 << (w*k % H) for w in range(H)] for k in wp]

def push(mask, table):
    out = 0
    while mask:
        bit = mask & -mask
        out |= table[bit.bit_length()-1]
        mask ^= bit
    return out

negative = [1 << (-w % H) for w in range(H)]
data = (root/'closure-family.json').read_bytes()
certificate = json.loads(data)
assert isinstance(certificate, dict) and len(certificate) == 25
assert {int(c) for c in certificate} == {min(c*k % H for k in cp) for c in range(H)}
assert all(isinstance(v, list) and v for v in certificate.values())
base = [(int(c), int(h)) for c, holes in certificate.items() for h in holes]
assert len(base) == len(set(base)) == 19844
families = [dict() for _ in range(H)]
minimum = H
for i, (c, holes) in enumerate(base):
    assert 0 <= c < H and 0 <= holes <= U
    assert holes != U, "empty survivor encountered"
    assert push(holes, negative) == holes
    for j in range(15):
        d, out = c*cp[j] % H, push(holes, tables[j])
        survivors = U ^ out
        assert survivors and not (survivors & (U ^ safe[d]))
        families[d].setdefault(out, (i, j))
        minimum = min(minimum, bin(survivors).count('1'))
assert all(families)
expanded = sum(map(len, families))
assert expanded == 15*len(base) == 297660
assert minimum == 294

# For every output fiber, a bitset index identifies all beliefs that
# exclude each residue. Intersecting these indices finds a covering
# complement containing every forbidden residue.
indexes = []
for family in families:
    masks = list(family)
    posting = [0]*H
    for i, mask in enumerate(masks):
        while mask:
            bit = mask & -mask
            posting[bit.bit_length()-1] |= 1 << i
            mask ^= bit
    indexes.append((masks, posting, (1 << len(masks))-1))

indexing_seconds = time.monotonic()-start-arithmetic_seconds
validation_start = time.monotonic()
rchecks = gchecks = tchecks = 0
witness_digest = hashlib.sha256()
for c, family in enumerate(families):
    dest, posting, initial = indexes[(c+1) % H]
    for holes in family:
        rholes = push(holes, tables[1])
        assert rholes in families[81*c % H]
        rchecks += 1
        # Complement of the saturated image (S+1) union (S-1).
        plus = ((holes << 1) & U) | (holes >> (H-1))
        minus = (holes >> 1) | ((holes & 1) << (H-1))
        forbidden = plus & minus
        choices = initial
        pending = forbidden
        while pending and choices:
            bit = pending & -pending
            choices &= posting[bit.bit_length()-1]
            pending ^= bit
        assert choices, ('G closure', c, holes)
        idx = (choices & -choices).bit_length()-1
        witness = dest[idx]
        assert forbidden & ~witness == 0
        # Check the survivor-set direction explicitly.
        assert (U ^ witness) & forbidden == 0
        witness_digest.update(f'{c}:{holes}:{witness}\n'.encode())
        gchecks += 1
        survivors = U ^ holes
        assert survivors & safe[c] == survivors
        tchecks += 1
assert rchecks == gchecks == tchecks == expanded
assert rchecks+gchecks+tchecks == 892980 <= 1500000

# Entire-fiber first-letter calculation: all 341 roots in every class.
startup = 0
for c in range(H):
    full = {inverse(c, w) for w in range(H)}
    assert saturate(full) == full
    assert {coord(x)[0] for x in full} == {c}
    assert len(saturate({act(M, x) for x in full})) == H
    assert len(saturate({((x[0]+1) % H,x[1]) for x in full})) == H
    assert len(saturate({x for x in full if unit(x)})) == bin(safe[c]).count('1')
    startup += 1

assert startup == 341
assert sum(bool(f) for f in families) == 341
assert bin(safe[0]).count("1") == 300
seal = hashlib.sha256(data).hexdigest()
assert seal == "8870a41115f6ce30c34f9414eb64774c314a7e0410c7204ff443744a16c6c03f"
report = {"independent_check":"passed", "integer_E":E,
          "raw_states":raw_checks, "base_members":len(base),
          "base_fibers":len(certificate), "expanded_members":expanded,
          "R_checks":rchecks, "G_checks":gchecks, "T_checks":tchecks,
          "coverage_classes":sum(bool(f) for f in families),
          "startup_full_fibers":startup,
          "minimum_current_survivors":minimum, "zero_class_safe_roots":300,
          "certificate_sha256":seal,
          "independent_witness_sha256":witness_digest.hexdigest(),
          "arithmetic_seconds":arithmetic_seconds,
          "indexing_seconds":indexing_seconds,
          "validation_seconds":time.monotonic()-validation_start,
          "seconds":time.monotonic()-start,
          "external_data_inputs":["closure-family.json"]}
print(json.dumps(report, sort_keys=True))
signal.alarm(0)
```

### 101.7 方法来源、供应关系与研究范围

本实例用补集包含来压缩集合搜索，采用成熟的反链方法；一般自动机的集合单调性、有限闭包及 König 引理不作为本节新算法或新定理主张。关于反链方法的背景文献，参见 Martin De Wulf、Laurent Doyen、Thomas A. Henzinger、Jean-François Raskin，*Antichains: A New Algorithm for Checking Universality of Finite Automata*，[CAV 2006，17–30页，DOI:10.1007/11817963_5](https://doi.org/10.1007/11817963_5)。此处仅作方法背景书目引用：作者、题名、年份与页码已由出版元数据核对，未核对该文正文的具体定理。本节的闭包正确性由101.2—101.5及独立程序直接给出，不依赖把文献的某个算法或定理直接套入本实例。

Udi Boker 与 Karoliina Lehtinen，[*Good for Games Automata: From Nondeterminism to Alternation*，arXiv:1906.11624v2](https://arxiv.org/abs/1906.11624v2)，第3节 history-determinism 的说明与定义5，要求选择只依已经读到的词并对不同未来一致。本节只复用这个在线选择与逐词存在接受路径的区别，不从该文推导本实例的闭包或取得障碍。式(101.8)允许日程依赖整份协议，不声称得到 history-deterministic 的选择器。

本卷97.1供应准确坐标与接口，97.2供应同一实际整数提升的执行桥；第100节供应零类逐根拒绝这一量词对照。[Fibonacci 卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)第38节的闭合缺陷、第130节的实际正向接枝词是既有代数背景；第133节的终端查询允许同源重置，不能迁入这里作为免费重试。第98节两读数取得的是共同含量，第99节研究一般 $H,d$ 的无接枝 $R/T$ 含量判据，两者都不等于本节的初始商标签 $c_0$，也未被本节推翻。已取得端点加保留运输的条件恢复仍按95.7、96.7、98.4；本节没有另行取得端点或隐藏时间。

仓内 [ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) 的 `controlled_behavior_universal_property` 以确定更新及读出交织为前提，不能直接替代这里共同相位下的非确定语言证书；这里只读其声明，没有编译或宣称新的 Lean 应用。新增成果是这个准确 $341,15$ 实例的整纤维有限闭包证书，以及在固定协议、固定实际来源和任意记忆条件下的取得桥。它说明自主商作为关系结构可以存在而原传感器仍无法保证取得其非恒定初始函数；不主张一般 $H$ 分类、最小证书、算法原创优先权、物理统一、随机协议结论或长期研究目标已经完成。

产地：本节为 codex-cli 的 THEORY-ONLY 实施，复用已完成的候选构造代码并在本文公开自足生成器及独立原坐标验证器；恢复标识为 `6abca92e2b72653bc33a2dd2`。正文只承载数学结果、程序和范围，不把既往评审意见当作证明。

## 101.99 追加锚

## 102. 原语完成后报告批奇偶仍不能保证取得初始商

本节只加强97.1的观察接口：每个原语完成时，报告其前隐藏批的奇偶。下面用两个预先固定的正整数来源及一个共同因果日程规则，证明完整初始商仍不能保证有限取得。第101节隐藏相位的全一证明不是本节前提；这里的共同响应可以是31。

### 102.1 报告时序与固定来源

仍取

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
E=M^{15}=\begin{pmatrix}377&610\\610&987\end{pmatrix},\quad
\alpha=(1,0),\quad q=(2,3),\quad H=341=11\cdot31.
$$

控制器先选定一个原语 $A\in\{R,G,T\}$，随后在该原语前执行有限隐藏批 $E^k$，再完成已选定的原语：$R(s)=Ms$、$G(s)=s+\alpha$，$T$ 付费返回精确的 $\gcd(qs,341)$ 且不扰动来源。只有完成后才报告 $\epsilon=k\bmod2$，控制器取得本次全部响应后再选择下一原语，不能因本次奇偶改选已经选定的动作。首原语为 $R/G$ 时规定 $k=0$；首原语为 $T$ 时允许任意有限 $k\ge0$。原语内部没有隐藏事件，每个请求均完成；不另加公平日程、复位、额外查询、来源相关时钟或完整坐标观察。

每次执行从一个固定未知实际来源连续推进，初始可见资料相同且与来源无关；确定性控制器允许任意内部记忆及本地计算。模剩余只用于证明，不能替换当前实际整数来源。按97.1置

$$
c=a+81b,\qquad w=a+261b\pmod{341}.
$$

预先选定实际正整数来源

$$
s_A=(186,124),\qquad s_B=(310,217),\qquad
(c,w)(s_A)=(0,155),\quad(c,w)(s_B)=(155,0).
$$

两原向量模31均为 $(0,0)$；模11的商坐标分别为 $(0,1)$ 与 $(1,0)$，初始目标 $c_0$ 分别为0与155。以下在 $\mathbb F_{11}$ 中把两当前坐标写成 $(c,w)$、$(\bar c,\bar w)$，避免与固定批指数15混用。由97.4约化得

$$
E(c,w)=(c,-w),\quad R(c,w)=(4c,8w),\quad
G(c,w)=(c+1,w+1),\quad qs=6c+7w.
$$

**引理 102.2（共同符号保持双源相容）。** 令

$$
B=c\bar w+\bar c w,\qquad
(c-\bar c)(w-\bar w)B\ne0.
$$

对于任一已经选定的下一原语，可只依当前这对坐标及该原语选择同一个实际 $k\in\{0,1\}$，使原语完成后仍满足此不变量；若原语为 $T$，还使两次局部标量均为模11单位。

证明。记共同符号 $\sigma=(-1)^k$。同时施加 $E$ 时，$c-\bar c$ 不变，$w-\bar w$ 与 $B$ 各变号，故保持不变量。

对于 $R$ 总选 $k=0$。两坐标差分别乘单位4、8，$B$ 乘单位32，因而仍非零。

对于 $G$，施加共同符号后再接枝，两后继为 $(c+1,\sigma w+1)$、$(\bar c+1,\sigma\bar w+1)$。坐标差仍非零，新交叉项为

$$
B_\sigma=\sigma(B+w+\bar w)+(c+\bar c+2).
$$

若 $B_+=B_-=0$，因2在 $\mathbb F_{11}$ 可逆，有 $c+\bar c+2=0$ 及 $B+w+\bar w=0$。代入 $\bar c=-c-2$ 得

$$
(c+1)(\bar w-w)=0.
$$

由 $w\ne\bar w$ 推出 $c=-1$，继而 $\bar c=-1$，与 $c\ne\bar c$ 矛盾。因此若 $B_+\ne0$ 就选 $k=0$，否则选 $k=1$。

对于 $T$，置

$$
P_+=(6c+7w)(6\bar c+7\bar w),\qquad
P_-=(6c-7w)(6\bar c-7\bar w).
$$

两式相减得

$$
P_+-P_-=2\cdot6\cdot7\,B\ne0.
$$

故至少一个乘积非零。若 $P_+\ne0$ 就选 $k=0$，否则选 $k=1$；对应的两个标量都非零，强于仅使整除指示相同。读取后的状态只经历共同的 $E^k$，所以不变量仍成立。证毕。

**定理 102.3（后报奇偶下的固定双源取得障碍）。** 在102.1接口中，不存在确定性协议对所有实际来源及所有合法日程保证有限停止并准确输出完整初始 $c_0\in\mathbb Z/341\mathbb Z$。同一反例也排除任何满足 $f(0)\ne f(155)$ 的初始任务 $f(c_0)$。上述两个来源在协议之前固定；引理102.2给出一个对所有确定性协议通用的共同因果日程规则，使两执行的全部动作、奇偶及 gcd 历史相同。

证明。初始局部对 $(0,1),(1,0)$ 的 $B=1$，两坐标差均非零。启动逐项核对：首个 $R$ 取 $k=0$ 并由引理保持不变量；首个 $G$ 取 $k=0$ 后得到 $(1,2),(2,1)$，其 $B=5\ne0$；首个 $T$ 在 $k=0$ 时两标量为7、6，故引理的优先零规则也选 $k=0$。因此同一见证甚至满足更严格的“所有首原语一律 $k=0$”，并未利用首读独有的启动自由。

之后每一步，在两份实际整数来源上执行引理所选的同一个 $k\in\{0,1\}$，再执行共同的原语。每个整数后继均由这两个固定来源连续产生；$M,E$ 及接枝保持其严格正性。$E^2\equiv I\pmod{341}$ 只解释奇偶的模作用，没有在整数轨迹中取消 $E^2$、重选提升或复位。共同的 $k$ 是全局选择，不能在11与31分量上各选一个符号。

由于两来源最初模31相等，且每步实际批数及原语相同，它们的当前原向量始终模31相等。在每个 $T$，引理保证两标量都不被11整除，而模31的整除状态相同。因此完整 gcd 响应相同，且属于 $\{1,31\}$。每步报告的奇偶也相同。

从相同初始可见资料归纳，任意确定性控制器的整个可见历史及内部状态相同，故下一动作、停止决定及最终答案都相同。日程规则只使用当前双源状态和刚选定的动作，不读取未来协议；这给出“先固定两来源及同一个规则，再对所有协议”的量词次序。若协议停止，同一个答案不可能同时等于0与155，亦不可能同时等于分离二者的两个函数值；不发任何命令就停止也如此。若不在有限执行及本地计算后停止，则不满足有限取得要求。证毕。

同一证明还覆盖原语完成后报告准确批数 $k$ 的接口，因为构造中两执行的实际 $k$ 逐次相同。它不覆盖按来源另加事件读数，也不把奇偶提前至动作选择前；这里没有改变动作选择时序。

### 102.4 保留运输与真正取得的区别

第94节的运输记录及95.7的条件恢复仍然成立。具体地，对一个假定初始剩余 $v$，记录当前仿射候选映射 $F(v)$；收到本次奇偶后分别更新为

$$
R:\ F\longmapsto ME^\epsilon F,\qquad
G:\ F\longmapsto E^\epsilon F+\alpha,\qquad
T:\ F\longmapsto E^\epsilon F
\quad(\bmod341).
$$

从 $F(v)=v$ 出发，这恰好追踪实际端点的模运输。已观察标签恢复的是条件确定的候选更新；它没有把可区分的查询交给控制器，因为本次动作已经选定，而下次仍可能有新的批。已知两个假定端点之间的可逆映射，并不提供任一未知端点。102.3的双源始终同转录，正好显示运输记忆不能自行完成取得。

Petra van den Bos 与 Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2#S3.SS2)，§3.2 “Compatibility” 说明对抗系统可使相容状态无法区分，并以共同后继关系定义相容性。这里已核对该版本原文小节，只将其作为成熟的相容性背景，不移用编号定理或其模型的识别算法；本实例的共同响应与因果规则由102.2—102.3直接证明。

### 102.5 有限算术复核

以下 Python 标准库代码枚举全部 $11^4=14,641$ 个有序四元组，其中11,100个满足不变量；逐一核对选定的 $R/G/T$ 符号及局部后继，并从原始整数 $M,q$ 核对坐标、来源提升与启动。预算为14,641个枚举项及33,300个不变量内的成对原语检查，不枚举模341的全对局或信念幂集。程序是本有限实例的复核；任意长度执行及任意记忆的结论依赖上面的归纳证明。

```python
from itertools import product
from math import gcd

def rot(s):
    a, b = s
    return b, a + b

def advance(s, action, k):
    for _ in range(15 * k):
        s = rot(s)
    if action == "R":
        s = rot(s)
    elif action == "G":
        s = (s[0] + 1, s[1])
    return s

def cw(s, modulus):
    a, b = s
    return ((a + 81 * b) % modulus, (a + 261 * b) % modulus)

def scalar(s):
    return 2 * s[0] + 3 * s[1]

def invariant(p):
    c, w, d, z = p  # d is the second c-coordinate, not the batch exponent.
    return ((c - d) * (w - z) * (c * z + d * w)) % 11 != 0

def choose(p, action):
    c, w, d, z = p
    if action == "R":
        return 0
    plus = ((c * z + d * w + w + z + c + d + 2) if action == "G"
            else (6 * c + 7 * w) * (6 * d + 7 * z))
    return 0 if plus % 11 else 1

raw = {cw(s, 11): s for s in product(range(11), repeat=2)}
assert len(raw) == 121
for (c, w), s in raw.items():
    assert scalar(s) % 11 == (6 * c + 7 * w) % 11
    assert cw(advance(s, "T", 1), 11) == (c, -w % 11)
    assert cw(rot(s), 11) == (4 * c % 11, 8 * w % 11)
    assert cw(advance(s, "G", 0), 11) == ((c + 1) % 11, (w + 1) % 11)

examined = valid = checks = 0
for p in product(range(11), repeat=4):
    examined += 1
    if not invariant(p):
        continue
    valid += 1
    for action in "RGT":
        k = choose(p, action)
        a = advance(raw[p[:2]], action, k)
        b = advance(raw[p[2:]], action, k)
        assert invariant(cw(a, 11) + cw(b, 11)), (p, action, k)
        if action == "T":
            assert scalar(a) * scalar(b) % 11 != 0, (p, action, k)
        checks += 1

sources = ((186, 124), (310, 217))
assert [cw(s, 341) for s in sources] == [(0, 155), (155, 0)]
assert all(a > 0 and b > 0 and a % 31 == b % 31 == 0 for a, b in sources)
assert advance((1, 0), "T", 1) == (377, 610)
assert advance((0, 1), "T", 1) == (610, 987)
initial = cw(sources[0], 11) + cw(sources[1], 11)
assert invariant(initial)
for action in "RGT":
    assert choose(initial, action) == 0
    a, b = [advance(s, action, 0) for s in sources]
    assert invariant(cw(a, 11) + cw(b, 11))
    assert tuple(x % 31 for x in a) == tuple(x % 31 for x in b)
    if action == "G":
        assert cw(a, 11) + cw(b, 11) == (1, 2, 2, 1)
    if action == "T":
        assert (scalar(a) % 11, scalar(b) % 11) == (7, 6)
        assert gcd(scalar(a), 341) == gcd(scalar(b), 341) == 31
assert (examined, valid, checks) == (14641, 11100, 33300)
print(examined, valid, checks)
```

### 102.6 适用边界与来源

本节仅否定此接口对完整 $c_0$ 及分离0与155的函数的保证；不能据此断言每个非恒定函数均不可取得。第100节迫使某次非单位的来源相关词与本证明不冲突，因为31本来就是非单位响应。第101节保留其隐藏相位合同与量词，本节没有借用其全一语言结论。

[Fibonacci 卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)第38、130节供应闭合缺陷及实际正向接枝的代数背景；第133节的取得合同允许同源重置，本节没有该权限。最小成功接口仍未确定：尚缺能够打破这对来源相容性的操作条件、在该条件下可实际执行的有限协议及界。本节不增设此类查询，不推广到一般 $H$，不作物理统一、原创优先权或 Lean 核验主张。

产地：codex-cli 的 THEORY-ONLY 实施，恢复标识 `6abcb8e78ffcf3fbe6a5e83d`；交付为本算术实例的正文证明与有限复核代码。

## 102.99 追加锚

## 103. 先报告相位再承诺原语的初始商取得

第102节即使把首批固定为零、把每批准确次数在所选动作后交给控制器，仍有固定双源的共同转录。本节改变的是报告与动作承诺的先后关系：在每次原语选择前报告已经完成的批奇偶，并保护此报告到该原语完成的区间。下面在同一连续实际来源上给出初始 $c_0\bmod341$ 的确定性取得协议。有限证书只用模11、模31的两张规范对表；从双候选到全部初始标签的桥由显式候选删除不变量承担。

### 103.1 先报告的准确合同与控制记忆

固定一次未知 $s_0=(a_0,b_0)\in\mathbb N^2$，含零，此后来源始终是它的实际整数后继。取

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
E=M^{15}=\begin{pmatrix}377&610\\610&987\end{pmatrix},\quad
\alpha=(1,0),\quad q=(2,3),\quad H=341=11\cdot31.
\tag{103.1}
$$

第一轮先宣布 $k_1=0$，然后控制器选择首个原语。每个后续轮次 $i$，调度器先选择有限整数 $k_i\ge0$，在当前实际来源上执行 $E^{k_i}$，再宣布 $\epsilon_i=k_i\bmod2$；控制器收到报告后才选择恰一个 $R,G,T$。从宣布到该原语完成没有新的 $E$。其中 $R(s)=Ms$，$G(s)=s+\alpha$，$T$ 返回精确的 $\gcd(qs,341)$ 且不扰动来源。每份已给出的 offer 必须由一个原语消耗；不允许拒绝、免费重新要一次报告或在同一 offer 下执行两个原语。完成一个原语后可决定停止；若继续，就进入下一轮。

每个请求均完成，每批有限；不加统一批数界、完成时限、公平性或额外时钟。控制器初始资料与来源无关，只有完成信号、已宣布的奇偶、自己的命令和实际付费 gcd 响应可作外部输入。允许任意确定性本地计算和任意内部记忆：形式上，可取任意内部配置集 $Z$、固定初始配置 $z_0$，由配置与新报告计算动作，由配置、动作及完成响应计算下一配置，并在完成切口计算是否停止及答案。所有内部工作带和程序位置都包含在 $Z$ 中；内部计算永不返回的执行不算有限取得。这里的存在性构造将给出有限、可执行的这种配置表示，并不把一般控制器预限为小自动机。

保护区间涵盖控制器处理该报告和所选原语完成；计算不附送观察，不按计算耗时偷取来源信息。没有 reset、复制、坐标或整数大小传感器，也没有另加可选择的等待动作。实际状态从不被剩余代表替换。第102节的负结论还覆盖首轮全为零及动作后准确批数，故这里的正负对照不靠未明说的启动优势。

### 103.2 带初始标签的可逆候选运输

复用97.1的坐标，并把等式理解为模341等式：

$$
\begin{aligned}
c&=a+81b,&w&=a+261b,\\
b&=36(w-c),&a&=c-81b,\\
E(c,w)&=(c,-w),&R(c,w)&=(81c,261w),\\
G(c,w)&=(c+1,w+1),&qs&=270c+73w.
\end{aligned}
\tag{103.2}
$$

坐标矩阵行列式为180，$180\cdot36\equiv1\pmod{341}$。$E^2\equiv I$ 只在剩余环成立，整数矩阵 $E^2\ne I$。因此任意允许的有限批 $E^k$ 投影为已报告的共同符号 $(-1)^\epsilon$，无需知道 $k$ 本身。

对于 $p=11,31$，置 $\lambda=81\bmod p$、$\mu=261\bmod p$、$A=270\bmod p$、$B=73\bmod p$、$n=(p-1)/2$：

| 103.2 局部模数 | $\lambda$ | $\mu$ | $A$ | $B$ | $n$ |
| --- | --- | --- | --- | --- | --- |
| 103.2a：11 | 4 | 8 | 6 | 7 | 5 |
| 103.2b：31 | 19 | 13 | 22 | 11 | 15 |

**引理 103.1（初始标签不会被运输合并）。** 给定同一已宣布历史，对每个尚存初始候选保留不可变标签 $c_0$ 和当前候选 $(c,w)$。存在由记录计算的共同 $u\in\mathbb F_p^\times,t\in\mathbb F_p$，使全部候选满足

$$
c=u c_0+t.
\tag{103.3}
$$

报告符号和 $T$ 不改 $u,t$；$R$ 更新为 $(\lambda u,\lambda t)$；$G$ 更新为 $(u,t+1)$。初始 $(u,t)=(1,0)$。所以不同初始 $c_0$ 的候选始终有不同的当前 $c$。对已知符号和所选原语，整个局部状态更新也是置换。

证明。逐动作代入(103.2)；$\lambda,\mu$ 及 $\pm1$ 均为单位，平移可逆，读取的状态作用为恒等。筛选可删除候选，但不会改变余下候选所带的标签或等式。这里的 $u,t$ 是假定来源到当前态的运输关系，不是任何未知端点的读数。证毕。

### 103.3 不同标签对的规范轨道与六层秩

考虑不同当前 $c$ 的候选对 $x=(c,w),y=(d,z)$。两素数中 $\lambda$ 的阶均为 $n$，$n$ 为奇数，$\mu^n=-1$。所以 $-1$ 不在阶为 $n$ 的 $\langle\lambda\rangle$ 中，且

$$
\mathbb F_p^\times=\langle\lambda\rangle\ \sqcup\ -\langle\lambda\rangle.
\tag{103.4}
$$

每个非零差 $\delta=c-d$ 恰有一个 $(\mathrm{swap},h)$，$0\le h<n$，满足 $(-1)^{\mathrm{swap}}\lambda^h\delta=1$。对调候选并同时作 $R^h$ 后，差成为1；再从共同反射的两个 $(w,z)$ 中选字典序较小者。记所得规范化为 $C_p(x,y)=(c,w,z)$，代表对 $((c,w),(c-1,z))$。它是共同旋转、共同反射及对调的轨道代表；$R^n=E$ 是模 $p$ 的恒等式，包括 $p=11,n=5$，不是原始整数动作的相等。

共同反射仅固定 $(w,z)=(0,0)$，故规范域

$$
\mathcal C_p=\{(c,w,z):(w,z)\le_{\rm lex}(-w,-z)\},\qquad
|\mathcal C_p|=p(p^2+1)/2
\tag{103.5}
$$

分别有671和14911条记录。规范化没有给两个候选分别选择符号，也没有给两个素数分别控制实际相位。

对 $v\in\mathcal C_p$ 的代表对作 $j$ 次共同 $R$，$0\le j<n$，得到 $(x_j,y_j)$。令 $E_\sigma(c,w)=(c,\sigma w)$，$\sigma\in\{1,-1\}$，定义

$$
\begin{aligned}
D(v,j,\sigma)&\Longleftrightarrow
 [A(x_j)_c+B\sigma(x_j)_w=0]\ \ne
 [A(y_j)_c+B\sigma(y_j)_w=0],\\
H(v,j,\sigma)&=C_p(GE_\sigma x_j,GE_\sigma y_j),\\
W_0&=\varnothing,\\
W_{r+1}&=W_r\cup\{v:\exists j<n\ \forall\sigma\in\{1,-1\},
 D(v,j,\sigma)\ \lor\ H(v,j,\sigma)\in W_r\}.
\end{aligned}
\tag{103.6}
$$

方括号表示真假位，不是额外观察。$G$ 保持 $c$ 差非零，故 $H$ 总有定义。首次进入 $W_r$ 的指标记作 $\rho(v)$；按上一层选最小可用 $j(v)$。本有限实例的完整层数为：

| 103.3 证书域 | 秩1 | 秩2 | 秩3 | 秩4 | 秩5 | 秩6 | 未获秩 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 103.3a：$\mathcal C_{11}$ | 57 | 83 | 148 | 192 | 168 | 23 | 0 |
| 103.3b：$\mathcal C_{31}$ | 467 | 977 | 2380 | 6412 | 4664 | 11 | 0 |

**命题 103.2（两张表的严格门条件）。** 两域均有 $W_6=\mathcal C_p$。对每条存储记录及两个符号，各自或者满足 $D(v,j(v),\sigma)$，或者满足

$$
0<\rho(H(v,j(v),\sigma))<\rho(v)\le6.
\tag{103.7}
$$

证明。103.8的有界程序完整生成(103.5)及(103.6)，逐层同步更新，不使用同层刚加入的值。103.9从原始 $M,E,G,q$ 独立检查全部记录、唯一规范化及存储门的两个符号。它检查1342与29822个选定符号义务，其中917与23984个必须使用严格 $G$ 下降，合计31164与24901。每个等式、域覆盖、层计数与严格不等式均为程序内的断言；没有以稳定次数代替全域获胜检查。此为显式有限算术证书与正文证明，未作 Lean/kernel 核验。证毕。

### 103.4 把规范门实现为逐 offer 的双候选协议

**引理 103.3（每次比较恰以一读结束）。** 任意两个不同初始 $c_0$ 的当前候选，在任意后续共同相位日程下，有一个使用已报告符号的确定性比较过程，至多 $6n$ 个实际原语后执行一次 $T$，使两个预测的模 $p$ 整除位不同。过程中至多 $6(n-1)$ 次 $R$、5次 $G$，恰一次末尾 $T$。

证明。在已完成原语的切口，或第一轮开始前，规范化当前选定对，记其归一化旋转数 $h$、规范记录 $v$ 和门 $j(v)$。计划执行

$$
t_*=(h+j(v))\bmod n,\qquad 0\le t_*<n
\tag{103.8}
$$

次实际 $R$，每次单独消耗一个 offer。旋转期间不因报告而改选 $R$；所有候选仍按每次真实报告更新。共同 $E$ 与 $R$ 交换，规范反射、对调以及把 $h+j$ 减去 $n$ 所差的 $R^n=E$，都只留下一个共同符号及可忽略的候选对调。因此，在旋转完成后的下一份 offer，实际跟踪对恰处在(103.6)所检查的某一个符号分支。若 $t_*=0$，就直接使用本阶段第一份 offer 作这一判断，没有空耗轮次。

先应用这份已宣布的符号，计算两个候选的预测零位：不同就选 $T$；相同就选 $G$。保护区间保证选择后不再改变该分支。前者给一次真实读取，后者由(103.7)使重新规范化的秩严格下降。所有预测只读控制器中的假设记录，没有读取实际坐标。

从最大秩6起，最多经历六个阶段，每阶段至多 $n-1$ 次 $R$ 加一个 $G$ 或 $T$。秩1时不能作 $G$ 下降到正的更小秩，故一定读出并结束；此前至多5次 $G$。无 offer 被拒绝、重发或免费等待。即使对手在观察到既往动作后选择下一符号，也只能选择已全称检查的两个分支之一。证毕。

此证明的量词是先选旋转门，再覆盖旋转期间的全部符号，最后收到门前报告后选择 $G/T$。它没有把 $\exists j\,\forall\sigma$ 偷换成未获许可的符号选择，也没有把整个旋转块当成一个受保护原语。

### 103.5 全标签消除、实际槽不变量与同源 CRT

**定理 103.4（初始商的保证有限取得）。** 在103.1的合同下，存在对每个固定 $s_0\in\mathbb N^2$ 及每份合法日程都有限停止、准确输出 $c_0=a_0+81b_0\pmod{341}$ 的确定性协议。一个充分成本向量为

$$
N_T\le1080,\qquad N_R\le83520,\qquad N_G\le5400,\qquad
N_{\rm offer}=N_R+N_G+N_T\le90000.
\tag{103.9}
$$

证明。初始化两个数组。模 $p$ 数组有 $p^2$ 个槽，依固定字典序以所有初始 $(c_0,w_0)\in\mathbb F_p^2$ 编号；每槽保存这个初始身份、初始目标 $c_0$、当前候选 $(c,w)$ 和存活位。初始当前候选就是初始坐标。每轮对两个数组的全部存活槽都先应用同一个已宣布的 $E^\epsilon$，再应用同一个实际选择的 $R/G/T$。若为 $T$ 且真实返回 $y$，恰保留满足

$$
[A c+B w=0]=[p\mid y]
\tag{103.10}
$$

的槽。读取不改变当前候选。

归纳得到实际槽不变量：真实 $s_0$ 在模 $p$ 的初始槽从未被删，且其当前候选恰是同一实际整数来源的当前投影。初始成立；报告与动作步由(103.2)保持；读取时实际槽满足(103.10)，所以仍存活。这同时保证两个数组永不为空。

更强地，完整相容剩余关系由这两个带标签数组的笛卡尔积经 CRT 准确表示。初始全部模341剩余对与两个局部域的积双射，并各有非负整数提升。给定同一可见历史，每步状态作用逐分量确定；平方自由的341使完整 gcd 恰由两根素数的整除位确定，筛选也逐分量分解。每个共同奇偶历史都可用实际 $k=\epsilon$ 实现，首项取零，不另含来源限制。因此归纳既不遗漏真实来源，也不把不相容的局部响应拼在一起。实际运行仍只有一个来源、一个全局批数及一个原语；笛卡尔表示不授予独立调度两根素数的能力。

先以模11为活动数组，再以模31为活动数组。若活动数组的所有存活槽已有相同初始 $c_0$，就保存此标签并转入下一阶段；否则按固定槽序选两个不同初始标签的槽，运行引理103.3。引理103.1保证它们的当前 $c$ 不同，故规范表适用。比较的末尾读数使这两个预测位不同，真实位至少删去其中一个槽；即使两个所选槽都不是真实来源，也仍至少删去一个。实际槽则由不变量保留。比较间严格减少存活槽数，因而每根轴最多 $p^2-1$ 次比较就达到标签纯。

两个数组在每个旋转、接枝、报告和读取上都更新，包括另一根轴活动期间；已经取得的初始标签不会因为当前态继续移动而改名。模11阶段至多120次比较，模31阶段至多960次，全部读取至多1080次。取得 $x=c_0\bmod11$、$y=c_0\bmod31$ 后输出

$$
x+11\bigl(17(y-x)\bmod31\bigr)\pmod{341},
\tag{103.11}
$$

因为 $11\cdot17\equiv1\pmod{31}$。实际槽保证这是原来固定来源的初始标签。

每次模11比较至多30个原语，模31比较至多90个。分别累计 $R,G,T$ 给

$$
\begin{aligned}
N_R&\le120\cdot6\cdot4+960\cdot6\cdot14=83520,\\
N_G&\le5(120+960)=5400,\\
N_T&\le120+960=1080,\\
120\cdot30+960\cdot90&=90000.
\end{aligned}
\tag{103.12}
$$

控制器具体保留两张共15582条的只读秩／门表、两数组共 $121+961=1082$ 个候选槽，以及活动素数、所选槽编号、旋转剩余计数、已取得标签、当前报告、程序位置和有限模算术工作区。也可显式保留(103.3)的字段。每次选槽、规范化、更新及读后筛选都是有限域上的有界确定计算；不需要保存实际整数坐标。此处的记录数和槽数不是完整比特存储最优值，控制字段及工作区也不被省略为零成本。

有界轮次、有限本地计算与合同中的每次请求完成一起给逐日程的有限终止；没有由此推出统一物理时间界。协议在使两个标签都纯的已完成读取后停止，不领取一份用不上的 offer。证毕。

这一步是带初始标签的全候选取得证明，复用92.2的关系记账和94.1的运输思想。双候选可区分本身没有被冒充为取得；关键补项是异标签不合并、实际槽不丢失和每次真实读取严格删除候选。

### 103.6 第102节固定双源的六轮分离

对第102节的 $s_A=(186,124)$、$s_B=(310,217)$，初始标签为0与155，使用如下短协议。第一份报告为0，选 $G$；第二轮选 $R$；第三轮若 $\epsilon_3\ne\epsilon_2$ 就选 $T$ 并结束，否则选 $G$，随后第四、第五轮都选 $R$，第六轮选 $T$。

模11的启动后候选为 $(1,2),(2,1)$。若第二、第三轮奇偶不同，第三轮报告后为 $(4,6),(8,3)$，两个 $6c+7w$ 分别为0、3。若奇偶相同，第三轮接枝后为 $(5,6),(9,9)$。此后两次旋转以及全部后续共同符号，使最后报告后的候选为

$$
(3,\pm10),\qquad(1,\pm4)
\tag{103.13}
$$

且两个符号必须相同。两个标量在正号下为0、1，在负号下为3、0，总会分离。原来源模31相等，所以所有共同动作及报告历史下其模31当前态仍相等；局部11位不同因而迫使完整 gcd 不同。

103.9另从未约化的整数来源执行 $k=\epsilon$ 的所有分支，检查18个终端分支、固定首轮之后的34条 offer 边，末端响应均为 $(11,1)$ 或 $(1,11)$。固定的首轮 $0/G$ 另有一条边；若连它一起计，整棵执行树为35条边。两个叶在第3轮、十六个叶在第6轮，每条路径恰有一次 $T$。任意更大但同奇偶的有限批由(103.2)投影到同一模读数，因此覆盖全部允许批数。这只是展示旧双源不变量不能原样跨越新的动作承诺切口；一般取得仍由定理103.4证明。

### 103.7 证书的范围、运行与失败判据

以下两个 Python 3.9+ 标准库程序可在一个新建空目录中分别保存为 `generate103.py`、`validate103.py`，依次运行 `python3 generate103.py`、`python3 validate103.py`。第一个生成两份完整 JSON 证书；第二个只读它们，并从原始整数矩阵独立规范化和复核，不导入生成器。证书的固定 SHA256 同时拒绝缺失、重复、截断、换序或改动的文件；数学断言还独立核对其内容。

生成器的有限域记录数为15582，生成的 $G$ 后继、$T$ 谓词和旋转边合计1135100，另有749828次已存门扫描；扫描不会生成新状态或新边。校验器对全部 $p^2$ 原坐标核对坐标逆、三个原语、读数和局部 $R^n=E$，再检查全部31164个选定符号义务，原矩阵应用数为1357610。两程序各有120秒硬期限、10万记录和150万生成边／原矩阵应用上限；生成器另限一千万次门扫描及恰六次严格增层。没有全模341成对博弈或信念幂集枚举。

正常运行必须完成全部断言并以退出码0结束；`python -O`、耗尽期限或计数上限都必须失败，不能把部分证书当成功结果。可用 `python3 generate103.py --edge-cap 1`、`python3 validate103.py --edge-cap 1` 检查耗尽路径。一个独立的数学负控是仅在校验器副本中把 `source` 的返回值 `(c-81*y)%p,y` 改成 `(c-81*y+1)%p,y`，保留证书原样；原坐标逆断言必须拒绝它。另把证书任一秩改成0，完整文件校验必须拒绝；不以这一字节检查替代上述数学负控。

### 103.8 有界规范证书生成器

```python
# Save as generate103.py; run with standard Python 3.9+ in an empty directory.
import argparse, hashlib, json, math, signal, time
from collections import Counter
if not __debug__:
    raise SystemExit('assertions required: do not use python -O')
ap = argparse.ArgumentParser()
ap.add_argument('--seconds', type=float, default=120)
ap.add_argument('--record-cap', type=int, default=100000)
ap.add_argument('--edge-cap', type=int, default=1500000)
a = ap.parse_args()
assert 0 < a.seconds <= 120 and math.isfinite(a.seconds)
assert 0 < a.record_cap <= 100000 and 0 < a.edge_cap <= 1500000
start = time.monotonic()
def timeout(*_):
    raise TimeoutError('time bound exhausted')
signal.signal(signal.SIGALRM, timeout)
signal.alarm(math.ceil(a.seconds))
records = edges = scans = 0
def guard():
    assert time.monotonic()-start < a.seconds, 'time bound exhausted'
    assert records <= a.record_cap, 'record bound exhausted'
    assert edges <= a.edge_cap, 'edge bound exhausted'
    assert scans <= 10000000, 'rank scan bound exhausted'
expected = {11: [57,83,148,192,168,23],
            31: [467,977,2380,6412,4664,11]}
outputs = []; summaries = []
for p in (11,31):
    n = (p-1)//2; lam, mu = 81%p, 261%p; A, B = 270%p, 73%p
    assert min(j for j in range(1,p) if pow(lam,j,p)==1) == n
    assert pow(mu,n,p)==p-1 and n%2==1
    norm = {}
    for delta in range(1,p):
        choices = [(sw,j,pow(lam,j,p),pow(mu,j,p))
                   for sw in (0,1) for j in range(n)
                   if (-1 if sw else 1)*delta*pow(lam,j,p)%p==1]
        assert len(choices)==1
        norm[delta] = choices[0]
    def canon(c,w,d,z):
        sw,j,l,m = norm[(c-d)%p]
        if sw: c,w,d,z = d,z,c,w
        c,w,d,z = l*c%p,m*w%p,l*d%p,m*z%p
        assert (c-d)%p==1
        w,z = min((w,z),(-w%p,-z%p))
        return c,w,z
    states = [(c,w,z) for c in range(p) for w in range(p)
              for z in range(p) if (w,z)<=(-w%p,-z%p)]
    records += len(states); guard()
    assert len(states)=={11:671,31:14911}[p]
    idx = {s:i for i,s in enumerate(states)}
    assert len(idx)==len(states)
    successors = []; separates = []
    for c,w,z in states:
        guard(); d = (c-1)%p; row = []; bits = []
        for j in range(n):
            rowj = []; bitj = []
            for sig in (1,-1):
                w1,z1 = sig*w%p,sig*z%p
                bitj.append(((A*c+B*w1)%p==0)!=((A*d+B*z1)%p==0))
                rowj.append(idx[canon((c+1)%p,(w1+1)%p,
                                      (d+1)%p,(z1+1)%p)])
                edges += 2  # one T predicate and one G pair transition
            row.append(rowj); bits.append(bitj)
            c,w,d,z = lam*c%p,mu*w%p,lam*d%p,mu*z%p
            edges += 1  # one common R orientation transition
            guard()
        successors.append(row); separates.append(bits)
    rank = [0]*len(states); policy = [-1]*len(states); layers = []
    for depth in range(1,7):
        additions = []
        for i in range(len(states)):
            if rank[i]: continue
            for j in range(n):
                scans += 1
                if all(separates[i][j][e] or rank[successors[i][j][e]]>0
                       for e in (0,1)):
                    additions.append((i,j)); break
        guard()
        assert additions, 'no strict progress'
        assert len(additions)==expected[p][depth-1]
        for i,j in additions:
            assert rank[i]==0
            rank[i],policy[i] = depth,j
        layers.append(len(additions))
    assert all(1<=r<=6 for r in rank) and max(rank)==6
    assert layers==expected[p] and sum(layers)==len(states)
    checks = descents = 0
    for i,r in enumerate(rank):
        j = policy[i]
        for e in (0,1):
            checks += 1
            if not separates[i][j][e]:
                assert 0<rank[successors[i][j][e]]<r
                descents += 1
    assert (checks,descents)=={11:(1342,917),31:(29822,23984)}[p]
    data = {'p':p,'states':states,'rank':rank,'policy':policy}
    raw = (json.dumps(data,separators=(',',':'))+'\n').encode('ascii')
    assert len(raw)<=1000000
    outputs.append((p,raw))
    summaries.append({'p':p,'records':len(states),'layers':layers,
                      'selected_signs':checks,'strict_G_descents':descents,
                      'sha256':hashlib.sha256(raw).hexdigest()})
assert records==15582 and edges==1135100
assert sum(x['selected_signs'] for x in summaries)==31164
assert sum(x['strict_G_descents'] for x in summaries)==24901
guard()
for p,raw in outputs:
    with open('orbit%d.certificate.json'%p,'wb') as f: f.write(raw)
print(json.dumps({'tables':summaries,'records':records,'generated_edges':edges,
                  'rank_gate_scans':scans,'seconds':time.monotonic()-start}))
```

### 103.9 独立原坐标校验器及六轮整数重放

```python
# Save as validate103.py beside the two generated certificates.
import argparse, hashlib, json, math, signal, time
from collections import Counter
if not __debug__:
    raise SystemExit('assertions required: do not use python -O')
ap = argparse.ArgumentParser()
ap.add_argument('--seconds', type=float, default=120)
ap.add_argument('--edge-cap', type=int, default=1500000)
a = ap.parse_args()
assert 0<a.seconds<=120 and math.isfinite(a.seconds)
assert 0<a.edge_cap<=1500000
start = time.monotonic(); edges = records = 0
def timeout(*_): raise TimeoutError('time bound exhausted')
signal.signal(signal.SIGALRM, timeout); signal.alarm(math.ceil(a.seconds))
def guard():
    assert time.monotonic()-start<a.seconds, 'time bound exhausted'
    assert edges<=a.edge_cap, 'edge bound exhausted'
    assert records<=100000, 'record bound exhausted'
def mul(A,B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in (0,1))
                       for j in (0,1)) for i in (0,1))
def raw(A,s):
    return tuple(sum(A[i][j]*s[j] for j in (0,1)) for i in (0,1))
def app(A,s,p):
    global edges
    edges += 1; guard()
    return tuple(v%p for v in raw(A,s))
M = ((0,1),(1,1)); I = ((1,0),(0,1)); E = I
for _ in range(15): E = mul(E,M)
assert E==((377,610),(610,987)) and mul(E,E)!=I
assert tuple(tuple(v%341 for v in row) for row in mul(E,E))==I
assert 180*36%341==1
expected = {
    11:(671,[57,83,148,192,168,23],917,
        'dae82f4d5541e7f9efd8b6608108ade5e0d9c14e1543a6297c03eb2d106e41b9'),
    31:(14911,[467,977,2380,6412,4664,11],23984,
        '6bdc4b9798bc5575460a365dcf4ef2d429ffcbf7d7649baf92bcfbc3310fbba1')}
def unique_object(pairs):
    d = {}
    for k,v in pairs:
        assert k not in d, 'duplicate JSON key'
        d[k] = v
    return d
results = []
for p in (11,31):
    count,layers,want_g,digest = expected[p]; n = (p-1)//2
    with open('orbit%d.certificate.json'%p,'rb') as f: blob=f.read(1000001)
    assert len(blob)<=1000000, 'certificate byte bound'
    assert hashlib.sha256(blob).hexdigest()==digest, 'certificate bytes changed'
    data = json.loads(blob,object_pairs_hook=unique_object)
    assert set(data)=={'p','states','rank','policy'} and type(data['p']) is int
    assert data['p']==p
    states,rs,js = data['states'],data['rank'],data['policy']
    assert all(type(x) is list for x in (states,rs,js))
    assert len(states)==len(rs)==len(js)==count
    assert all(type(s) is list and len(s)==3 and
               all(type(v) is int and 0<=v<p for v in s) for s in states)
    assert all(type(r) is int and 1<=r<=6 for r in rs)
    assert all(type(j) is int and 0<=j<n for j in js)
    keys = [tuple(s) for s in states]
    domain = [(c,w,z) for c in range(p) for w in range(p) for z in range(p)
              if (w,z)<=((-w)%p,(-z)%p)]
    assert keys==domain and len(set(keys))==count
    assert [Counter(rs)[r] for r in range(1,7)]==layers
    records += count; guard(); ranks = dict(zip(keys,rs))
    def coords(s):
        x,y = s
        return (x+81*y)%p,(x+261*y)%p
    def source(c,w):
        y = (w-c)*pow(180,-1,p)%p
        return (c-81*y)%p,y
    # Check the inverse and all raw single-state transitions, independently
    # of the generator's diagonal transition and successor arrays.
    Mn = I
    for _ in range(n): Mn = mul(Mn,M)
    assert tuple(tuple(v%p for v in row) for row in Mn)==tuple(
        tuple(v%p for v in row) for row in E)  # local R^n=E only
    for x in range(p):
        for y in range(p):
            s = (x,y); c,w = coords(s)
            assert source(c,w)==s and coords(source(x,y))==(x,y)
            assert coords(app(M,s,p))==(81*c%p,261*w%p)
            assert coords(app(E,s,p))==(c,-w%p)
            assert coords(((x+1)%p,y))==((c+1)%p,(w+1)%p)
            assert (2*x+3*y)%p==(270*c+73*w)%p
    # Scan raw rotations; do not use the generator's delta lookup.
    def canonical(x,y):
        hits = []
        for h in range(n):
            cx,wx = coords(x); cy,wy = coords(y)
            for sw in (0,1):
                c,w,d,z = (cy,wy,cx,wx) if sw else (cx,wx,cy,wy)
                if (c-d)%p==1:
                    w,z = min((w,z),(-w%p,-z%p))
                    hits.append((c,w,z))
            x,y = app(M,x,p),app(M,y,p)
        assert len(hits)==1, 'normalization not unique'
        return hits[0]
    for delta in range(1,p):
        x,y = source(delta,0),source(0,0)
        canonical(x,y)  # all nonzero differences admit exactly one rotation/swap
    checks = descents = 0
    for (c,w,z),r,j in zip(keys,rs,js):
        x,y = source(c,w),source((c-1)%p,z)
        assert canonical(x,y)==(c,w,z)
        for _ in range(j): x,y = app(M,x,p),app(M,y,p)
        for eps in (0,1):
            u,v = (app(E,x,p),app(E,y,p)) if eps else (x,y)
            bx = (2*u[0]+3*u[1])%p==0
            by = (2*v[0]+3*v[1])%p==0
            if bx==by:
                u = ((u[0]+1)%p,u[1]); v = ((v[0]+1)%p,v[1])
                assert 0<ranks[canonical(u,v)]<r, 'gate lacks strict descent'
                descents += 1
            checks += 1
    assert checks==2*count and descents==want_g
    results.append({'p':p,'records':count,'selected_signs':checks,
                    'strict_G_descents':descents,'layers':layers})
assert records==15582
assert sum(x['selected_signs'] for x in results)==31164
assert sum(x['strict_G_descents'] for x in results)==24901
# Raw integer replay of the short separator; k=epsilon, without reducing states.
sources = ((186,124),(310,217))
assert tuple((x+81*y)%341 for x,y in sources)==(0,155)
assert all((sources[0][i]-sources[1][i])%31==0 for i in (0,1))
def step(s,act):
    return raw(M,s) if act=='R' else (s[0]+1,s[1]) if act=='G' else s
initial = tuple(step(s,'G') for s in sources)  # fixed first offer epsilon_1=0
assert tuple(((x+81*y)%11,(x+261*y)%11) for x,y in initial)==((1,2),(2,1))
leaves = offered = 0; lengths = Counter(); reads = Counter()
def walk(pair,offers,actions):
    global leaves,offered
    guard(); r = len(actions)+1
    assert 2<=r<=6 and offered<=34 and leaves<=18
    for eps in (0,1):
        offered += 1; assert offered<=34
        now = tuple(raw(E,s) for s in pair) if eps else pair
        assert all((now[0][i]-now[1][i])%31==0 for i in (0,1))
        act = ('R' if r in (2,4,5) else
               'T' if r==6 or eps!=offers[1] else 'G')
        new = tuple(step(s,act) for s in now)
        if act=='T':
            ys = tuple(math.gcd(2*x+3*y,341) for x,y in new)
            assert ys in ((11,1),(1,11))
            assert actions.count('T')==0
            leaves += 1; lengths[r] += 1; reads[ys] += 1
        else:
            walk(new,offers+[eps],actions+act)
walk(initial,[0],'G')
assert leaves==18 and offered==34 and lengths=={3:2,6:16}
guard()
print(json.dumps({'validation':results,'raw_matrix_applications':edges,
                  'separator_leaves':leaves,'poststartup_offered_edges':offered,
                  'fixed_startup_edges':1,'separator_lengths':dict(lengths),
                  'seconds':time.monotonic()-start}))
```

### 103.10 供应结果、文献边界与所得关系

本文所据仓库快照为 `1c37fc8b581a44332dda71e54a2071867a67beea`。第92节供应初始标签—当前态关系及异标签合并的风险，第94节供应不读取坐标的运输记录；第95—100节分别保留其隐藏事件、素数反射、共同相位、含量取得、受限字母表及固定源语言的原合同。[Fibonacci Atomic Relation Generation](FIBONACCI_ATOMIC_RELATION_GENERATION.md)第130节供应实际正词的仿射下降，第133节供应在其既有接口中保持共同实际词及目标的 CRT 取得。这里只沿用同源、共同操作和目标标签的证明纪律，没有把第133节的 reset 或收费查询最优值移到本节。

仓内 [FiniteHorizonReachability.finite_horizon_reachability](../../../D5/S3/ConceptDynamics/Control/FiniteHorizonReachability.lean) 已给有限获胜层与有界到达策略的抽象对应，其每个动作的后继须非空。这里每个门有两个已列出的符号分支，局部秩只实例化这种成熟的有限到达结构；初始标签的永久保存、原始整数来源的实现及全候选删除由103.2—103.5直接证明。没有新增、编译或声称已核验该实例的 Lean 声明。

Petra van den Bos、Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2)，2019年10月22日版本，第2节、第3节及第6节，提供 observable nondeterminism、相容性与自适应区别测试的背景。该文讨论对抗系统中无法区分的相容态；第6节定义16的 injective 条件要求有关转移保持不相容性，或由不共享的输出直接区分。定理6.1还假定所有不同状态对都不相容，并将自适应区别图的存在与构造中只作 injective splits 联系起来。这些条件不能用两两存在测试代替，更不能直接补出一个全候选测试。本节并未把相位置于选择前的保护合同识别为该文全部博弈假设，也未未经证明就移用不相容性保持或测试存在性结论。所需的、针对初始任务标签的保持与删除桥已在上文逐项给出；该文只支持方法背景。

得到的关系是：一份被报告的共同相位，使候选运输可计算；保护到单个动作完成的切口，使该运输可用于选择真正有区别的下一步；保留初始标签的候选关系，把逐对进展接为同一实际来源的有限取得。这给一个具体的记忆、时序和观察边界之间的充分桥。90000原语／offer及1080读是本构造的充分界，不是最小值、最佳已知界或不存在更小构造的断言。

所得只有初始 $c_0\bmod341$。它没有恢复初始整数、完整语法树、全部记忆、绝对时钟或物理几何；没有给隐藏 $k$、实际整数宽度、gcd 位成本或物理历时的统一界。一般 $H$ 的分类、最小成功接口、最优计算或存储、物理统一和持续的最小关系结构目标均不由此完成。本节是现有供应结果下的具体综合推导及可复现有限证书，不作原创优先权或新增 Lean/kernel 认证主张。

## 103.99 追加锚

## 104. 先报告相位的差锥障碍、精确终端门与非线性陷阱缺口

第103节的模11、31构造已有各自的有限进展证书。本节纠正一种更宽的推广候选：仅由“奇数半阶旋转、非零传感器系数”不能推出初始坐标的保证取得。先在一般奇素域给固定双源障碍，再在排除该障碍的半阶族中证明终端门和无线性陷阱引理；进入终端门所需的非线性陷阱排除仍是未证命题。这些结论不改判第103节的具体实例。

### 104.1 抽象奇素域与准确的先报告合同

先独立定义模模型。令 $p$ 为奇素数，$\lambda,\mu,A,B\in\mathbb F_p^\times$，状态域为 $\mathbb F_p^2$，操作及读数为

$$
E_\sigma(c,w)=(c,\sigma w),\qquad
R(c,w)=(\lambda c,\mu w),\qquad
G(c,w)=(c+1,w+1),\qquad
T(c,w)=[Ac+Bw=0],\quad \sigma\in\{1,-1\}.
\tag{104.1}
$$

方括号只取真假位。初始未知来源 $(c_0,w_0)$ 在执行前固定；第一份 offer 的符号固定为 $+1$。以后每轮，对手依共同既往历史选择并施加一个共同 $E_\sigma$，**先宣布符号，再由控制器选择恰一个 $R,G,T$**。报告到该原语完成之间没有新反射；每个请求完成，每份 offer 必须消耗。$R,G$ 仅给无信息的完成信号，$T$ 付费、不扰动。控制器初始记忆与来源无关，允许任意确定性内部记忆和有限本地计算；无限内部计算不算取得。没有免费 offer、等待、逆动作、复位、相位选择或坐标读数。

给定非恒定 $f:\mathbb F_p\to Y$，取得任务是对所有固定初始来源及所有合法日程都有限停止，正确输出 $f(c_0)$。比较双源时始终使用同一个已宣布符号、同一个动作和两条从预先固定来源连续生成的历史。候选坐标只在控制器内部预测，不是实际传感器输入。

一般模模型不预设 Fibonacci 实现。要接到实际整数及原子接枝，还须另有坐标共轭、每步共同操作的提升及读数投影。第103节已经为其 $M,E,G,q,H=341$ 给出这些桥；下文的模3反例没有这些桥。

### 104.2 差锥上的共同标量消除

**定理 104.1（平方相等的旋转阻断每个非恒定初始任务）。** 在104.1的模型中，若 $\lambda^2=\mu^2$，则对每个非恒定 $f:\mathbb F_p\to Y$，不存在保证取得 $f(c_0)$ 的确定性协议。把 $G$ 替换或扩充为任意族静默共同平移 $s\mapsto s+t$，结论仍成立。

证明。选 $c_1,c_2$ 使 $f(c_1)\ne f(c_2)$，并在协议运行前固定两个来源

$$
s_1=(c_1,0),\qquad s_2=(c_2,A(c_1-c_2)/B).
\tag{104.2}
$$

对当前对 $(c,w),(d,z)$ 记 $u=c-d,v=w-z$，使用差锥

$$
\mathcal D:\qquad u\ne0,\qquad (Au)^2=(Bv)^2.
\tag{104.3}
$$

$A,B$ 非零保证 $v\ne0$。共同反射不改两个平方；$R$ 将它们分别乘 $\lambda^2,\mu^2$，故保持相等及非零；任意共同平移不改差，$T$ 不改状态。于是差锥对所有这些操作封闭。

在每份 offer 前选

$$
\sigma=-\frac{Au}{Bv}.
\tag{104.4}
$$

差锥给 $\sigma^2=1$；奇特征中它恰是允许的两个符号之一。此选择使

$$
Ac+B\sigma w=Ad+B\sigma z.
\tag{104.5}
$$

(104.2)处 $v=-Au/B$，所以第一份符号恰为 $+1$，无论首个动作是什么。以后对手只需用两个固定来源及既往共同动作、符号更新当前对，再按(104.4)出 offer；不依赖尚未选择的当前动作，也不更换来源。

收到同一符号后，两执行有相同控制记忆，因而选择相同动作。若选 $T$，(104.5)给相同零位；若选静默命令，完成响应相同。差锥保持，归纳给完整可见历史、停止决定及输出相同。共同有限答案不能同时等于两个不同任务值；不终止也违反保证有限取得。初始直接停止同样失败。证毕。

等式(104.5)比零位相等更强：即使把 $T$ 扩大成返回完整标量的传感器，这个负例仍成立。后续正向引理仍只使用(104.1)的零位；这里没有授予完整标量访问。

### 104.3 模3反例与代数满秩的不足

**推论 104.2（原半阶条件不足）。** 考虑推广候选

$$
p=2n+1\text{ 为素数},\qquad n\text{ 为奇数},\qquad
\operatorname{ord}(\lambda)=n,\qquad
\mu=-\lambda^{-1},\qquad A B\ne0.
\tag{104.6}
$$

这些条件不足以保证任何给定非恒定初始 $c_0$ 任务的取得。取

$$
p=3,\quad n=1,\quad \lambda=1,\quad\mu=-1=2,\quad A=B=1.
\tag{104.7}
$$

全部条件成立，而 $\lambda^2=\mu^2$。例如固定来源 $(0,0),(1,2)$ 的初始零位均为真，初始标签不同。这里还可把共同日程写成：首轮给正号；以后恰在前一个已完成动作是 $R$ 时给负号，在前一个动作是 $G$ 或 $T$ 时给正号。因为 $R=E_{-1}$，每个选择切口的两来源差始终为 $(1,-1)$，故两个完整标量相等。这是先出 offer 的合法规则。

该系统在合作调度下有普通代数可控性。平移向量 $t=(1,1)$ 与 $Rt=(1,-1)$ 的列式行列式为 $-2\ne0$；取全部 offer 为正，$G$ 与时间顺序的 $R,G,R$ 分别实现这两个平移，重复非负次数即生成整个平面。线性传感器的两行 $q=(1,1)$、$qR=(1,-1)$ 也有非零行列式。前者允许合作日程，后者只断言形式线性行满秩；它们没有消除敌对先报告日程中的共同抵消，更没有把两次零位变成完整标量观测。

在(104.6)内，

$$
\lambda^2=\mu^2\ \Longleftrightarrow\ \lambda^4=1
\ \Longleftrightarrow\ n=1\ \Longleftrightarrow\ p=3.
\tag{104.8}
$$

中间等价使用 $n$ 为奇数且为 $\lambda$ 的准确阶。因此必须至少排除 $n=1$ 才能提出全族的正向保证；$n>1$ 只排除此障碍，不是已证充分条件。模3的 $\lambda=1$ 不满足 $\lambda^2-\lambda-1=0$，故(104.7)不能提升为这里所讨论的 Fibonacci 矩阵 $M$ 反例。第103节的11、31参数分别有 $(\lambda/\mu)^2=3,28$，均不为1，不受定理104.1反驳。

### 104.4 奇数半阶中的精确旋转终端门

本小节以后，除另有说明外，在(104.6)上增加 $n>1$。令 $Q=\langle\lambda\rangle$。有限域乘法群循环，故 $Q$ 是全部非零平方组成的阶 $n$ 子群；$n$ 奇使 $-1\notin Q$。置

$$
\kappa=\mu/\lambda=-\lambda^{-2}.
\tag{104.9}
$$

$\lambda^{-2}$ 的阶为 $n$，$\kappa^n=-1$，$\kappa$ 的阶为 $2n$。因此 $0\le j<n$ 的 $n$ 个对跖集合 $\{\kappa^j,-\kappa^j\}$ 两两不交，合起来恰为 $\mathbb F_p^\times$。

**定理 104.3（含原点和坐标轴的终端充要条件）。** 对当前候选 $(c,w),(d,z)$，假设 $c\ne d$。存在某个 $0\le j<n$，使 $j$ 次实际 $R$ 后的一次 $T$ 对两个可能的累计共同符号都分离该对，当且仅当

$$
J:=cz+dw=0,\qquad
\neg\bigl(w=z=0\ \text{且}\ cd\ne0\bigr).
\tag{104.10}
$$

该协议恰有一次 $T$，原语及 offer 总数为 $j+1\le n$。

证明。$R$ 与反射交换。约去传感器中的非零因子 $\lambda^j$，两个零位来自

$$
Ac+\sigma B\kappa^j w,\qquad Ad+\sigma B\kappa^j z,
\quad \sigma\in\{1,-1\}.
\tag{104.11}
$$

必要性：如果同一个候选在两个符号下都为零，相加、相减及 $2AB\kappa^j\ne0$ 使该候选为原点，因而 $J=0$。否则两个符号分别使两个不同候选为零；将相应方程交叉相乘相加即得 $J=0$。当 $w=z=0,cd\ne0$ 时两个读数永远非零，故必须排除此情形。

充分性先处理原点。若 $(c,w)=(0,0)$，则 $d\ne0$。当 $z=0$，任意 $j$ 都分离；当 $z\ne0$，恰有一个对跖类含 $-Ad/(Bz)$，选另一个类即可让第二候选在两个符号下均非零。另一个类存在正是用到 $n>1$。第二候选为原点时对称。

若两者均非原点，$J=0$ 和排除条件迫使 $c,d,w,z$ 全部非零：例如 $c=0$ 迫使 $w=0$ 而成为原点；$w=0$ 迫使 $z=0$ 而落入排除情形，其余对称。两个斜率根

$$
r_1=-Ac/(Bw),\qquad r_2=-Ad/(Bz)
$$

由 $J=0$ 满足 $r_2=-r_1$，且非零、不同。对跖分划给唯一 $j$ 使 $\{\kappa^j,-\kappa^j\}=\{r_1,r_2\}$；每个共同符号恰使一个候选为零。以上覆盖所有轴退化。

实现时预选该 $j$，逐 offer 执行 $j$ 个 $R$，再在下一份 offer 下执行 $T$。中间符号任意，全部累计为(104.11)的一个共同符号，故都成功；若 $j=0$，首份 offer 就被 $T$ 消耗。没有免费旋转或跳过 offer。证毕。

**推论 104.4（规范终端层的闭式计数）。** 按103.3的共同旋转及逻辑交换，把 $c-d$ 规范为1，再模共同反射 $(w,z)\sim(-w,-z)$。全部规范对数为 $p(p^2+1)/2$，其中满足定理104.3的数目为

$$
N_{\rm term}(p)=\frac{p^2-p+4}{2}.
\tag{104.12}
$$

证明。固定 $c$ 后，$d=c-1$，方程 $cz+(c-1)w=0$ 是非零齐次线性方程，恰有 $p$ 个解。共同取负只固定零向量，其解轨道数为 $(p+1)/2$。对全部 $c$ 求和，再删去 $c\notin\{0,1\}$ 的 $p-2$ 个禁用零向量类，即得(104.12)。全部 $(w,z)$ 的取负轨道数则为 $(p^2+1)/2$。证毕。

式(104.12)在11、31分别给57、467；这里只闭式解释第103节的终端层，不重证其余秩层，也不证明任意初始对能被迫进入此层。

### 104.5 固定差层中的联合读出与接枝

对任意 $c-d\ne0$，因 $\mathbb F_p^\times=Q\sqcup(-Q)$，可用共同 $R$ 的幂及逻辑交换两个名字，将第一坐标差写成1。选择一次第二坐标符号方向，把代表写成

$$
P_\delta(c,w)=\bigl((c,w),(c-1,w-\delta)\bigr),\qquad
\delta\in\mathbb F_p.
\tag{104.13}
$$

这是坐标记账，不执行逆旋转或交换实际来源。控制器保留代表到实际候选对的共同线性框架及名字对应；反射在此框架中记录，不能在两个候选之间分别选择。每一层有 $p^2$ 个 $(c,w)$。

给 $0\le j<n$，令 $x=\lambda^{-j}\in Q$。把实际旋转期间以及末份 offer 的反射合成 $\sigma$，并置

$$
\epsilon=\sigma(-1)^j,\qquad y=\epsilon/x,\qquad
\ell_{x,\epsilon}(c,w)=Ay c+Bx w.
\tag{104.14}
$$

**引理 104.5（读出与后继使用同一符号）。** 在框架 $E_\sigma R^j$ 中，候选对的两个实际零位恰为

$$
[\ell_{x,\epsilon}(c,w)=0],\qquad
[\ell_{x,\epsilon}(c,w)-(Ay+Bx\delta)=0].
\tag{104.15}
$$

若这一份 offer 下选 $G$，只在记账中逆用同一个已知框架，代表后继恰为

$$
P_\delta(c+x,w+\epsilon/x).
\tag{104.16}
$$

证明。$R^j$ 的对角元为 $1/x,(-1)^j x$，故实际标量是 $Ac/x+B\epsilon xw$。乘单位 $\epsilon$ 后恰为 $\ell_{x,\epsilon}$，不改变零位；对第二候选作同样计算得到(104.15)。实际接枝增加 $(1,1)$，框架逆像为

$$
(E_\sigma R^j)^{-1}(1,1)=(x,\epsilon/x).
\tag{104.17}
$$

两候选加同一向量，故差 $(1,\delta)$ 不变；并且同一个协向量在此步向量上的值为 $(A+B)\epsilon$。证毕。

若阶段开始时实际框架为 $E_\eta R^h$，把 $h$ 约到 $0,\ldots,n-1$，余下符号用 $R^n=E_{-1}$ 吸收入 $\eta$。为到目标 $j$，只需执行 $(j-h)\bmod n$ 次真实 $R$，至多 $n-1$ 次，每次消耗自己的 offer。末份报告决定(104.14)的 $\epsilon$；预测零位不同就选 $T$，否则选 $G$ 并按(104.16)更新代表及框架。每阶段至多 $n$ 个实际原语，无物理逆操作。特别不能以某个符号让零位相同，再以另一个符号让后继安全：这是同一份 offer 上的两个联合义务。

安全域的旋转对称也不需要免费旋转。令 $L$ 为后续每份 offer 都可取任意符号时，有限双候选分离博弈的最大安全域，定义在全部异第一坐标候选对上。其条件是存在一个 offer 符号，使当前 $T$ 不分离、且每个可选动作的后继仍在 $L$。下一 offer 可补偿一次共同反射，所以 $EL=L$。对 $v\in L$，某个符号使 $RE_\sigma v\in L$；由交换性与反射不变性得 $Rv\in L$。$R$ 可逆且域有限，故 $RL=L$，也就有 $R^{-1}L=L$。交换候选名字同样保持安全。因而若有非空 $L$，先规范第一坐标差，再取其一个非空 $\delta$ 截面，得到下面(104.18)的 $K$。这里的 $L$ 用于任意后续相位，不能把其存在自动当成满足首份正号的固定初始反例；定理104.1已经单独核对启动条件。

### 104.6 线支撑不可能承载安全平移

称非空 $K\subseteq\mathbb F_p^2$ 满足固定差层的安全条件，若

$$
\begin{gathered}
\forall(c,w)\in K\ \forall x\in Q\ \exists\epsilon\in\{1,-1\}:\\
\bigl[ A\epsilon c/x+Bxw=0\bigr]
 =\bigl[A\epsilon(c-1)/x+Bx(w-\delta)=0\bigr]
\quad\text{且}\quad
(c+x,w+\epsilon/x)\in K.
\end{gathered}
\tag{104.18}
$$

这是104.5所给阶段博弈的准确安全条件：控制器先选相对旋转门，对手给其实际累计符号，零位不同就结束，相同则接枝续行。每次的同一 $\epsilon$ 必须同时满足读出相等和安全后继。

**引理 104.6（无仿射线支撑的安全集）。** 当 $n>1$ 时，非空 $K$ 即使只满足(104.18)中的后继条件，也不可能包含于一条仿射直线。

证明。反设 $K\subseteq v_0+D$，其中 $D$ 是一维方向空间；取 $v\in K$。对每个 $x\in Q$，某个 $\epsilon$ 使 $v+(x,\epsilon/x)\in K$，所以 $(x,\epsilon/x)\in D$。$x\ne0$ 排除竖直方向，写 $D$ 的斜率为 $m$，便有

$$
m=\epsilon/x^2,\qquad m^2x^4=1\qquad(x\in Q).
\tag{104.19}
$$

取 $x=1$ 得 $m^2=1$，再取 $x=\lambda^{-1}$ 得 $\lambda^4=1$。$\lambda$ 的准确阶 $n$ 为奇数，故 $n\mid4$ 迫使 $n=1$，矛盾。证毕。

此引理排除单条仿射线上的陷阱，包括单点；它没有排除曲线、若干直线的并、二维子集或其他非线性 $K$，也没有使用读出等式来完成全域排除。

### 104.7 Fibonacci 子族的一个明确未证引理

为接近第103节的两个因子，进一步限制参数为

$$
\begin{gathered}
p=2n+1\text{ 为奇素数},\quad n>1\text{ 为奇数},\quad
\operatorname{ord}(\lambda)=n,\quad \lambda^2-\lambda-1=0,\\
\mu=1-\lambda=-\lambda^{-1},\quad \lambda\ne\mu,\\
A=\frac{3-2\mu}{\lambda-\mu},\qquad
B=\frac{2\lambda-3}{\lambda-\mu},\qquad AB\ne0.
\end{gathered}
\tag{104.20}
$$

这些公式来自 $c=a+\lambda b,w=a+\mu b$ 下的 $2a+3b=Ac+Bw$，并给 $A+B=2$；不是独立任选的传感器。第103节的 $(p,\lambda,\mu,A,B,n)=(11,4,8,6,7,5)$ 和 $(31,19,13,22,11,15)$ 均满足(104.20)。对该子族的单根素数，$M$ 在这组坐标下为 $R$，$M^n$ 投影为反射；多个素数要共用实际隐藏事件，仍须另核对共同指数，不能从逐素数共轭自动取得。

待证的**非线性陷阱排除命题**为：对每个满足(104.20)的参数组、每个 $\delta\in\mathbb F_p$，都不存在满足(104.18)的非空 $K$。这条命题尚未证明；本节没有声称它为真，也没有用 $n>1$ 替代其证明。其量词保持“对每点、每个 $x$，存在一个同时履行两个义务的符号”，而非两个分别存在的符号。

只有条件性后果已经明确：**如果**上述排除对某参数组的全部 $\delta$ 成立，在每个差层从 $W_0=\varnothing$ 递推

$$
W_{r+1}=W_r\cup\{v:\exists x\in Q\ \forall\epsilon\in\{1,-1\},
 D_\delta(v,x,\epsilon)\ \lor\ v+(x,\epsilon/x)\in W_r\},
\tag{104.21}
$$

其中 $D_\delta$ 表示(104.15)的两零位不同。若稳定时补集非空，否定加入条件恰给(104.18)；所以排除成立才推出 $W_{p^2}=\mathbb F_p^2$。每次未稳定至少新增一点，故至多 $p^2$ 层。选使秩下降的 $x$，由104.5得到至多 $np^2$ 个原语、恰一次末尾 $T$ 的双候选分离。这只是成熟有限到达博弈的条件实例，不能由形式递推本身宣布全域获胜。

再保留每个初始槽的不可变 $c_0$ 及当前态，复用103.2—103.5的关系桥：共同运输满足 $c=u c_0+t,u\ne0$，异标签不合并，实际槽永不被真实读数删除；每次选两个异标签槽的分离测试至少删去其中一个。仅在上述排除成立的条件下，至多 $p^2-1$ 次比较给每根素数的充分界

$$
N_{\rm primitive}\le np^2(p^2-1),\qquad N_T\le p^2-1.
\tag{104.22}
$$

(104.22)不是已取得的全族正向界，也不是第103节的改进界。对实际整数、原子来源或共同复合模数的结论仍须满足同源提升和完整响应桥；不能按不同素数自由拼接各自日程或重新选取实际来源。

### 104.8 小规模算术核对与可辨别的负控

以下 Python 3.9+ 标准库程序只检查模3差锥的全标量相等及一步封闭、11和31的终端充要条件与计数、同一符号的读出／接枝恒等式。它逐个扫描规范对，不保存大证书，不计算第103节其他秩层，也不搜索(104.18)的全部集合。保存为 `validate104.py`，在新建空目录运行 `python3 validate104.py`，正常退出码为0；应得到36个差锥对、规范对数671和14911、终端数57和467、484476次有界检查。程序同时限制120秒及150万次检查；保留的候选／旋转记录少于100条。

`--mutate-terminal` 故意漏去横轴排除项，必须在模11的 $(c,w,z)=(2,0,0)$ 被终端充要断言拒绝；`--mutate-epsilon` 故意把后继第二分量的符号强制为正，必须被联合符号断言拒绝；`--edge-cap 1` 必须因检查上限失败。三者的预期退出码均为1，不能把它们的失败当成正向验证。`python -O` 被显式拒绝。有限检查只交叉核对上述实例及恒等式，参数化证明由104.2—104.6承担，非线性陷阱命题保持未证。

```python
import argparse
import json
import signal
import time
from itertools import product

if not __debug__:
    raise SystemExit('assertions must be enabled')
args = argparse.ArgumentParser()
args.add_argument('--mutate-terminal', action='store_true')
args.add_argument('--mutate-epsilon', action='store_true')
args.add_argument('--edge-cap', type=int, default=1500000)
opt = args.parse_args()
start = time.monotonic()
signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
signal.alarm(120)
edges = 0

def tick():
    global edges
    edges += 1
    assert edges <= opt.edge_cap, 'edge cap'
    assert time.monotonic() - start < 120, 'deadline'

def inv(a, p):
    return pow(a % p, -1, p)

# Exhaust all invariant pairs, not a finite sample of histories.
p = 3
states = list(product(range(p), repeat=2))
cone_pairs = 0
for (c, w), (d, z) in product(states, repeat=2):
    u, v = (c-d) % p, (w-z) % p
    if not (u and (u*u-v*v) % p == 0):
        continue
    cone_pairs += 1
    sigma = -u * inv(v, p) % p
    assert sigma in (1, p-1)
    a, b = (c, sigma*w % p), (d, sigma*z % p)
    assert (a[0]+a[1]-b[0]-b[1]) % p == 0
    # Identity (T), R, and every common translation.
    successors = [(a, b), ((a[0], -a[1] % p), (b[0], -b[1] % p))]
    successors += [(((a[0]+h) % p, (a[1]+k) % p),
                    ((b[0]+h) % p, (b[1]+k) % p)) for h, k in states]
    for aa, bb in successors:
        tick()
        uu, vv = (aa[0]-bb[0]) % p, (aa[1]-bb[1]) % p
        assert uu and (uu*uu-vv*vv) % p == 0, 'cone closure'
assert cone_pairs == 36
assert -((0-1) % 3) * inv(0-2, 3) % 3 == 1
assert (1+2) % 3 == 0
assert (1*2-1*1) % 3 != 0  # translation columns and sensor rows

counts = {}
for p, lam, mu, A, B in [(11, 4, 8, 6, 7), (31, 19, 13, 22, 11)]:
    n = (p-1)//2
    assert n > 1 and n % 2 == 1
    assert next(k for k in range(1, p) if pow(lam, k, p) == 1) == n
    assert (lam*lam-lam-1) % p == 0 and (mu*lam+1) % p == 0
    assert mu == (1-lam) % p
    assert A == (3-2*mu)*inv(lam-mu, p) % p
    assert B == (2*lam-3)*inv(lam-mu, p) % p and (A+B) % p == 2
    rotations = [(pow(lam, j, p), pow(mu, j, p)) for j in range(n)]
    antipodes = [{mm*inv(ll, p) % p, -mm*inv(ll, p) % p}
                 for ll, mm in rotations]
    assert len(set.union(*antipodes)) == p-1
    total = terminal = 0
    for c, w, z in product(range(p), repeat=3):
        if (w, z) > (-w % p, -z % p):
            continue
        total += 1
        d = (c-1) % p
        gate = False
        for ll, mm in rotations:
            signs = []
            for sigma in (1, -1):
                tick()
                r = (A*ll*c+B*sigma*mm*w) % p
                s = (A*ll*d+B*sigma*mm*z) % p
                signs.append((r == 0) != (s == 0))
            gate |= all(signs)
        excluded = w == z == 0 and c*d % p != 0
        formula = (c*z+d*w) % p == 0 and (opt.mutate_terminal or not excluded)
        assert gate == formula, ('terminal iff', p, c, w, z, gate, formula)
        terminal += gate
    assert total == p*(p*p+1)//2
    assert terminal == (p*p-p+4)//2
    assert terminal == {11: 57, 31: 467}[p]
    counts[p] = {'canonical_pairs': total, 'terminal_pairs': terminal}
    # Check the joint covector and G increment on every state/orientation/sign.
    # The two inputs of each pair are independently covered as states.
    for c, w in product(range(p), repeat=2):
        for j, (ll, mm) in enumerate(rotations):
            x = inv(ll, p)
            for sigma in (1, -1):
                tick()
                epsilon = sigma * (-1)**j
                y = epsilon * inv(x, p) % p
                scalar = (A*ll*c+B*sigma*mm*w) % p
                assert (epsilon*scalar) % p == (A*y*c+B*x*w) % p
                actual = ((ll*c+1)*inv(ll, p) % p,
                          (sigma*mm*w+1)*inv(sigma*mm, p) % p)
                trial_y = inv(x, p) if opt.mutate_epsilon else y
                assert actual == ((c+x) % p, (w+trial_y) % p), 'joint epsilon'
                assert (A*y*x+B*x*y) % p == (A+B)*epsilon % p
signal.alarm(0)
print(json.dumps({'cone_pairs': cone_pairs, 'counts': counts,
                  'edge_checks': edges, 'retained_records_upper_bound': 100,
                  'elapsed_seconds': round(time.monotonic()-start, 6)}, sort_keys=True))
```

### 104.9 复用范围与保留的取得缺口

第92节的初始标签—当前态关系、第94节的运输记录、第96节的反射障碍、第99节受限 $R/T$ 含量判据和第102节的动作后报告反例，各保留其原始接口。这里的相位必须先于动作选择；因此不能把那些负结论直接搬来。Fibonacci 卷第130节提供实际正词及接枝的整数语义，第133节提供其同源重置合同下的取得；它们不供应本节未声明的重置。第103节的11／31有限进展、同源全标签消除及整数提升仍是其自身的结果。

仓内 [FiniteHorizonReachability.finite_horizon_reachability](../../../D5/S3/ConceptDynamics/Control/FiniteHorizonReachability.lean) 给有限获胜层与有界到达策略的抽象对应，前提是每个动作的后继非空。在(104.21)中可加一个成功汇点，把两个符号各自送往成功点或相应接枝后继，满足这个前提；该通用对应不替代非线性陷阱排除，也没有在此新增或编译 Lean 实例。

Petra van den Bos、Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2)，第6节的 injective 条件及相容性讨论只作背景。其状态不相容和保持条件须按具体系统核对；没有凭该文标题或通用自适应测试结论移入全族取得。这里给的是普通有限域推导、明确反例及小规模算术交叉核对，无原创优先权、物理统一或新增 Lean/kernel 认证主张。

所得结构将缺口集中到(104.18)：被宣布的相位同时约束“这一读能否分离”和“这一接枝去往何处”。终端斜率分划与无线支撑引理减少了需要解释的障碍，但未排除一般安全子集；空间坐标的生成、运输记忆和先报告时序本身仍不等于未知初始关系的普遍取得。

## 104.99 追加锚
## 105. 共同符号下的零差层分离与非线性安全集的必要条件

最小关系恢复要求把可生成的坐标、保留的运输关系与真正取得的初始信息分开。本节在104.7的 Fibonacci 子族内排除零差层安全集，并给出至多六个付费阶段的双候选分离；对一般差层，只得到每条竖直纤维和消失多项式的必要条件。任意非零差层的安全集排除仍未解决，以下部分结果不构成全族取得定理。所有证明均为普通数学论证，没有新增 Lean 声明或核验主张。

先澄清104.3的差向量记号：对那里依次显示的来源 $(0,0),(1,2)$，沿104.2的“第一减第二”约定，差为 $(-1,1)=(2,1)\pmod3$；那里写出的 $(1,-1)$ 取的是第二减第一。共同取负不改变差锥 $(Au)^2=(Bv)^2$，也不改变抵消比 $-Au/(Bv)$，故相应反例与定理不变。

### 105.1 参数、同源合同与唯一的分支符号

本节固定素数 $p>3$，并要求全部下列条件：

$$
\begin{gathered}
n=(p-1)/2\text{ 为奇数},\qquad
\lambda^2-\lambda-1=0,\qquad \operatorname{ord}(\lambda)=n,\\
\mu=1-\lambda=-\lambda^{-1},\qquad s=\lambda-\mu\ne0,\\
A=(3-2\mu)/s,\qquad B=(2\lambda-3)/s,\qquad AB\ne0,\qquad
Q=\langle\lambda\rangle\subset\mathbb F_p^\times.
\end{gathered}
\tag{105.1}
$$

$Q$ 是非零平方子群，阶为奇数 $n$；$-1$ 非平方，平方和四次方映射均置换 $Q$。还有

$$
\begin{aligned}
s^2&=5,& A+B&=2,& A-B&=4/s,&AB&=1/5,\\
A&=\lambda^3/s,& B&=\lambda^{-3}/s,&A/B&=\lambda^6.
\end{aligned}
\tag{105.2}
$$

这些是直接代入 $\lambda^2=\lambda+1$ 的恒等式；例如 $\lambda^3=2\lambda+1$、$\lambda^{-3}=2\lambda-3$。$n=1$ 会给 $p=3$；若 $n=3$，则 $\lambda^3=1=2\lambda+1$，与 $\lambda\ne0$ 矛盾。因此 $n\ge5,p\ge11$。这里不主张满足(105.1)的素数有无穷多个。

采用104.1的准确接口：执行前固定一个未知来源；首份 offer 为正号，以后每份 offer 先在同一实际来源上施加共同反射并宣布其符号，控制器再选择恰一个 $R,G,T$。反射到该原语完成之间受保护。$R(c,w)=(\lambda c,\mu w)$，$G(c,w)=(c+1,w+1)$，$T$ 付费、精确、不扰动，只提供 $[Ac+Bw=0]$。每个请求完成、每份 offer 必须消耗。没有免费旋转、逆动作、额外读数、复位、自由等待、时钟或公平性假设。候选是控制器中的假设；实际来源只沿实际执行连续演化。

将一对不同第一坐标的候选记成

$$
P_\delta(c,w)=((c,w),(c-1,w-\delta)).
$$

共同旋转与逻辑交换名字可选择这一代表，实际执行仍保留代表到当前候选的框架。对 $x\in Q$、$\epsilon\in\{1,-1\}$，定义

$$
\begin{aligned}
L_\epsilon&=A\epsilon c/x+Bxw,&
L'_\epsilon&=A\epsilon(c-1)/x+Bx(w-\delta),\\
v_\epsilon&=(c+x,w+\epsilon/x),&
D_\delta(c,w;x,\epsilon)&=([L_\epsilon=0]\ne[L'_\epsilon=0]).
\end{aligned}
\tag{105.3}
$$

**定义 105.1（相关安全条件）。** 非空 $K\subseteq\mathbb F_p^2$ 在差层 $\delta$ 安全，是指

$$
\forall(c,w)\in K\ \forall x\in Q\ \exists\epsilon\in\{1,-1\}:\quad
\bigl([L_\epsilon=0]=[L'_\epsilon=0]\bigr)
\ \land\ v_\epsilon\in K.
\tag{105.4}
$$

一个符号同时承担两个合取项，不能分别选取。其物理记账来自104.5：框架 $E_\sigma R^j$ 对角元为 $(1/x,\epsilon x)$，其中 $x=\lambda^{-j}$、$\epsilon=\sigma(-1)^j$。实际标量 $Ac/x+B\epsilon xw$ 乘单位 $\epsilon$ 后为 $L_\epsilon$；实际接枝 $(1,1)$ 的框架逆像为 $(x,\epsilon/x)$。逆像只用来更新记忆，没有实施逆操作。

### 105.2 每条竖直纤维至少两点

**引理 105.2（无单点竖直纤维）。** 在(105.1)下，对任意 $\delta$，满足(105.4)的非空 $K$ 投影到全部第一坐标，且每条纤维 $K_c=\{w:(c,w)\in K\}$ 至少有两点。因此 $|K|\ge2p$。

证明。固定 $x=1$ 连续选择安全后继，每步第一坐标加1。前 $p$ 个状态的第一坐标遍历 $\mathbb F_p$，故每条纤维非空。

反设 $K_{c_0}=\{w_0\}$。任取 $x\in Q$，从 $(c_0,w_0)$ 连续走 $p$ 次该 $x$ 的安全后继，符号为 $\epsilon_0,\ldots,\epsilon_{p-1}$。末态第一坐标返回 $c_0$，单点纤维迫使第二坐标也返回，因而 $\sum_i\epsilon_i=0\pmod p$。把符号视作整数，$p$ 个符号之和是 $[-p,p]$ 内的奇数，其可能的 $p$ 倍数只有 $-p,p$。所以全部符号相同，记为 $\epsilon$。

这条路径的状态为 $(c_0+kx,w_0+k\epsilon/x)$。第 $k$ 步的两个测试标量为

$$
L_k=A\epsilon c_0/x+Bxw_0+k\epsilon(A+B),\qquad
L_k-D,\qquad D=A\epsilon/x+Bx\delta.
\tag{105.5}
$$

因 $A+B=2\ne0$，$0\le k<p$ 时 $L_k$ 遍历整个域。在 $L_k=0$ 的一步，读出相等要求 $D=0$。所以每个 $x\in Q$ 都必须容许某个符号使

$$
A\epsilon+B\delta x^2=0.
\tag{105.6}
$$

若 $\delta=0$，这与 $A\ne0$ 矛盾。若 $\delta\ne0$，平方得到 $x^4=A^2/(B^2\delta^2)$；四次方映射置换 $Q$，故至多一个 $x\in Q$ 满足，不能覆盖 $n>1$ 个 $x$。单点纤维不可能存在。证毕。

**定理 105.3（零差层无安全集）。** 在(105.1)下，$\delta=0$ 时不存在满足(105.4)的非空 $K$。

证明。记 $h=1/2$。若 $w\ne0$，则 $A^2/(4B^2w^2)\in Q$，故有 $x\in Q$ 使

$$
x^4=A^2/(4B^2w^2).
\tag{105.7}
$$

令 $t_0=A/(2x)$、$u=Bxw$，则 $u=\pm t_0\ne0$。在 $(h,w)$，两标量是 $u+\epsilon t_0$ 与 $u-\epsilon t_0$；每个符号都恰使一个为零，另一个为非零。因此 $(h,w)$ 不能属于安全集。安全集的 $h$ 纤维只能包含0，这与引理105.2同时要求该纤维非空且至少两点矛盾。证毕。

### 105.3 零差候选的六阶段构造

定理105.3本身不给短动作词。以下另用完整 Fibonacci 条件构造一个不依赖未来符号的三接枝回路，随后将它编译成付费协议。

**引理 105.4（三接枝回路）。** 在(105.1)下存在 $t\in\mathbb F_p$，使

$$
t\in Q,\quad 1+t\notin Q\cup\{0\},\quad t^2+t+1\ne0,
\tag{105.8}
$$

并且 $x_1=1,x_2=t,x_3=-(1+t)$ 都在 $Q$、和为0，而对全部八个符号三元组都有

$$
\epsilon_1+\epsilon_2/t-\epsilon_3/(1+t)\ne0.
\tag{105.9}
$$

证明。令 $\chi$ 为二次特征，$\chi(0)=0$，并令 $\mathcal T=\{t:\chi(t)=1,\chi(1+t)=-1\}$。先计算

$$
\sum_t\chi(t(t+1))=-1,\qquad |\mathcal T|=(p+1)/4\ge3.
\tag{105.10}
$$

第一式可直接计数 $u^2=t(t+1)$：它等价于 $(2t+1-2u)(2t+1+2u)=1$。每个非零第一因子唯一决定第二因子，再唯一确定 $t,u$，所以共有 $p-1$ 对；另一方面对每个 $t$ 有 $1+\chi(t(t+1))$ 个 $u$。第二式把 $4|\mathcal T|$ 写成 $\sum_t(1+\chi(t))(1-\chi(1+t))$；在 $t=0,-1$ 的项均为0，其余项准确检测 $\mathcal T$，展开即得 $p+1$。

从 $\mathcal T$ 删去 $t^2+t+1$ 的至多两个根，仍有一个 $t$。因 $-1$ 与 $1+t$ 都非平方，$-(1+t)\in Q$。将(105.9)左侧乘非零的 $t(1+t)/\epsilon_1$，所得四种可能是

$$
t^2+t+1,\quad t^2+3t+1,\quad t^2-t-1,\quad t^2+t-1.
\tag{105.11}
$$

第一种已排除。后三种的根分别为

$$
\{-\lambda^2,-\lambda^{-2}\},\quad
\{\lambda,-\lambda^{-1}\},\quad
\{\lambda^{-1},-\lambda\}.
\tag{105.12}
$$

第一对及每个带负号的根都非平方。剩下的 $\lambda$ 与 $\lambda^{-1}$ 虽在 $Q$，却分别满足 $1+\lambda=\lambda^2\in Q$、$1+\lambda^{-1}=\lambda\in Q$，也不在 $\mathcal T$。所以四种值都非零，证明(105.9)。此处的根分解使用 Fibonacci 恒等式；本节不将这条回路推广到仅有奇数半阶的任意参数。证毕。

**定理 105.5（至多 $6n$ 个付费原语的零差双候选分离）。** 在(105.1)及105.1的先报告合同下，已知两个当前候选的第一坐标不同、第二坐标相同。仅以候选预测和已宣布历史选择实际动作，可在所有合法符号日程下，用至多 $6n$ 个原语分离这两个候选的零位预测；其中至多五个 $G$、恰一个 $T$，且至多 $6(n-1)$ 个 $R$。这是一对候选的分离，未要求其中某个就是实际来源。

证明。先在控制器中选规范代表，使第一坐标差为1，第二坐标差仍为0。若原第一坐标差不在 $Q$，交换两个候选名字使其在 $Q$，再选 $k$ 使 $\lambda^k$ 乘这个差为1。这里只将代表定义为共同 $R^k$ 的坐标像，实际框架反向记为 $R^{-k}$，不执行任何额外原语；初始框架偏移将在下面的第一阶段支付。

选引理105.4的 $t$。在规范态 $(c,w)$ 置 $a=h-c$：若 $a=0$，不接枝；若 $a\in Q$，做目标 $x=a$ 的一次接枝；若 $a$ 非平方，依次做

$$
x=a/(1+t),\qquad x'=at/(1+t).
\tag{105.13}
$$

这两数均为平方且和为 $a$。每次接枝在代表中加 $(x,\epsilon/x)$，因此无论符号怎样，至多两次接枝后第一坐标到达 $h$。

此时若 $w\ne0$，跳过回路；若 $w=0$，依次做 $x=1,t,-(1+t)$ 的三次接枝。第一坐标返回 $h$，第二坐标由(105.9)保证非零。最后选择(105.7)的 $x$，旋转到相应框架后做一次 $T$，两个可能符号都给不同零位。

具体付费实现如下。控制器保留 $E_\eta R^h$ 框架，把指数模 $n$ 约化，利用 $R^n=E_{-1}$ 将商的奇偶吸收入 $\eta$。阶段目标 $x=\lambda^{-j}$ 唯一确定 $j\bmod n$。执行 $(j-h)\bmod n$ 个实际 $R$，每个消耗当轮 offer，并累计已经报告的共同符号；到目标后，下一份 offer 用于规定的 $G$ 或最终 $T$。末份报告连同累计框架确定(105.3)的同一个 $\epsilon$。每阶段至多 $n-1$ 个 $R$ 加一个 $G/T$，最多五个接枝阶段加一个测试阶段，所以原语总数至多 $6n$。初始虚拟规范化偏移已包含在第一阶段的旋转差中，不能再当作免费物理操作，也不需另加一段实际规范化。

所有中间 offer 由所规定的 $R/G$ 消耗。即使某个中间测试已经能够分离，协议也可继续规定的接枝，不额外执行 $T$。论证允许每阶段两个有效符号，因而包括首份 offer 固定正号的实际限制。若首阶段无需旋转，首份正号直接被相应 $G/T$ 消耗。没有预选未来相位或丢弃不利报告。证毕。

### 105.4 安全集不能藏在低次数零点集中

**定理 105.6（消失多项式的次数下界）。** 设 $X\subseteq\mathbb F_p^\times$ 含1，$m=|X|$。若非空 $K\subseteq\mathbb F_p^2$ 满足

$$
\forall v\in K\ \forall x\in X\ \exists\epsilon\in\{1,-1\}:\quad
v+(x,\epsilon/x)\in K,
\tag{105.14}
$$

则每个在 $K$ 上消失的非零多项式 $F\in\mathbb F_p[C,W]$，其总次数 $d$ 都满足 $4d\ge m$。特别地，(105.4)的安全集要求

$$
d\ge\lceil n/4\rceil=\lceil(p-1)/8\rceil.
\tag{105.15}
$$

证明。$x=1$ 的后继闭合使 $K$ 投影到全部第一坐标，所以 $|K|\ge p$。反设 $4d<m$；非零常数不能在非空集上消失，故 $d>0$。对 $v=(c,w)\in K$，考虑 Laurent 多项式的乘积

$$
P_v(Z)=Z^{2d}F(c+Z,w+Z^{-1})F(c+Z,w-Z^{-1}).
\tag{105.16}
$$

每个限制的指数介于 $-d$ 与 $d$，所以 $P_v$ 是次数至多 $4d$ 的普通多项式。对每个 $x\in X$，后继条件使至少一个因子为零。故 $P_v$ 有 $m>4d$ 个不同根，必为零多项式。Laurent 多项式环是整环，所以有一个符号 $e(v)$ 使 $F(c+Z,w+e(v)/Z)$ 恒等于0。

代入同态的核恰是

$$
(H_{v,e}),\qquad H_{v,e}(C,W)=(C-c)(W-w)-e:
\quad \mathbb F_p[C,W]/(H_{v,e})\cong\mathbb F_p[Z,Z^{-1}].
\tag{105.17}
$$

该同构把 $C-c$ 送到 $Z$、$W-w$ 送到 $e/Z$，反向用 $(C-c)^{-1}=e(W-w)$，所以核的描述与素性都成立。于是不可约二次式 $H_{v,e(v)}$ 整除 $F$。不同中心 $v$ 给不同的首项系数为1的不可约因子：$C,W$ 的系数分别恢复 $-w,-c$。唯一分解性因而给 $2|K|\le d$，与 $|K|\ge p$ 及 $d<m/4\le(p-1)/4$ 矛盾。

这里从乘积恒等为零推出一个因子恒等为零，并未把原来的 $\forall x\exists\epsilon$ 改成策略上的 $\exists\epsilon\forall x$；也没有断言整条双曲线包含于 $K$。所得到的是 $F$ 的因子。证毕。

**推论 105.7（低次评价单射与点数界）。** 在(105.1)、(105.4)下，令 $r=\lfloor(n-1)/4\rfloor$。总次数至多 $r$ 的多项式到 $K$ 上函数的评价映射是单射，所以

$$
|K|\ge\binom{r+2}{2},\qquad
|K|\ge\max\{2p,\binom{r+2}{2}\}.
\tag{105.18}
$$

证明。评价核中的非零多项式会违反 $4r<n$ 和定理105.6；定义域维数为 $(r+1)(r+2)/2$，函数空间维数为 $|K|$。再用引理105.2。证毕。

这些是必要条件，能排除总定义次数 $d$ 满足 $4d<n$ 的曲线或曲线之并，却不排除高次数、稠密或不规则的 $K$。低次评价单射也不提供取得策略，不能将代数复杂度下界解释为非零差层的全域排除。

### 105.5 分开选择两个符号会丢失问题

**命题 105.8（终端补集满足放松条件但不满足原条件）。** 在(105.1)下，对 $\delta\ne0$ 置

$$
J_\delta(c,w)=(2c-1)w-c\delta,\qquad
\mathcal L_\delta=\{(c,w):J_\delta(c,w)\ne0\}.
\tag{105.19}
$$

其大小是 $p^2-p+1$。对每个 $v\in\mathcal L_\delta$、每个 $x\in Q$，分别存在一个测试相等的符号和一个使后继仍在 $\mathcal L_\delta$ 的符号。这个分开存在的条件不足以推出(105.4)；$\mathcal L_1$ 中有明确的同符号失败点。

证明。104.4的终端充要条件用于 $((c,w),(c-1,w-\delta))$，恰为 $J_\delta=0$。因 $\delta\ne0$，其横轴例外不存在。在 $c\ne1/2$ 时方程唯一解为 $w=c\delta/(2c-1)$；在 $c=1/2$ 时无解，故终端集恰有 $p-1$ 点，补集是 $p^2-p+1$ 点。

终端门的要点亦可从(105.3)看出：乘单位后两测试为 $c+\rho w$、$c-1+\rho(w-\delta)$，其中 $\rho=\epsilon(B/A)x^2$。随 $x$ 变化，$\{\rho,-\rho\}$ 划分全部非零斜率。两非轴零点斜率互为相反数等价于 $J_\delta=0$；若一候选为原点，只需避开另一候选至多一个零斜率对，$n>1$ 保证可选。坐标轴情形由104.3的排除项覆盖。因此非终端点对每个 $x$ 都至少有一个测试相等的符号。

再令 $u=2c-1,v=2w-\delta$，则 $J_\delta=(uv-\delta)/2$。如果两个后继都终端，便有

$$
(u+2x)(v+2/x)=\delta=(u+2x)(v-2/x).
\tag{105.20}
$$

相减迫使 $u+2x=0$，代回又迫使 $\delta=0$，矛盾。因此至少一个后继仍在补集。

为看清这两个符号不能拼接，取 $\delta=x=1$、$v_*=(-A^{-1},-B^{-1})$。由(105.2)直接得到

$$
\begin{array}{c|c|c|c}
\epsilon&L_\epsilon&L'_\epsilon&J_1(v_*+(1,\epsilon))\\ \hline
+1&-2&-4&0\\
-1&0&A-B&2B/A
\end{array}
\qquad J_1(v_*)=4/(AB)\ne0.
\tag{105.21}
$$

所有标为非零的量在(105.1)下确实非零。正号使测试相等，却只能走入终端集；负号使后继在补集，却立即分离测试。因此 $v_*\in\mathcal L_1$ 而 $\mathcal L_1$ 在此点不满足(105.4)。这不是原问题的安全集反例，而是丢弃共同符号相关性的反例。证毕。

### 105.6 从双候选到初始标签的桥及剩余量词

定理105.5使用的是当前候选关系。若控制器保留所有初始剩余候选，每个槽都携带不可变标签 $c_0$ 及当前预测态，并按同一实际动作和已宣布共同符号更新，则第一坐标始终满足 $c=u c_0+b$、$u\ne0$：$R$ 乘 $u,b$，$G$ 给 $b$ 加1，反射与 $T$ 不改变此关系。真实来源的槽不被其真实响应删除；一次选定双候选的不同预测测试至少删去两者之一，即使两者都不是真实槽也成立。这是103.2—103.5已有的标签运输桥。

但定理105.5只保证不同 $c$、相同 $w$ 的对；候选库中尚有不同第二坐标的对。不得假定每次都能找到零差对，也不得将可自由生成坐标等同于普遍识别初始标签。一般待证命题仍是：对每个满足(105.1)的参数组及每个 $\delta\in\mathbb F_p^\times$，不存在满足(105.4)的非空 $K$。本节既未证明这条命题，也未构造其反例。反例若要否定实际取得，还必须给同一固定来源的因果实现、正确首份正号及不同初始标签。

只有在全部差层排除另获证明后，104.7的有限到达递推才给每对至多 $p^2$ 个阶段、每阶段至多 $n$ 个原语；候选槽至多 $p^2$ 个，逐对删除才给

$$
N_{\rm primitive}\le np^2(p^2-1),\qquad N_T\le p^2-1.
\tag{105.22}
$$

这是保留原条件的条件性界，不是由本节部分引理取得的新全族界。所需记忆包括初始标签、当前候选库、相位／符号、共同仿射运输及控制位置；没有最小记忆、实际历时、隐藏工作量或整数位长界。

实际 Fibonacci 桥须逐对象声明。对 $M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$、$\alpha=(1,0)$、$q=(2,3)$，坐标 $c=a+\lambda b,w=a+\mu b$ 可逆，$M$ 作用为 $R$、接枝为 $(1,1)$、$qs=Ac+Bw$。若实际隐藏事件声明为 $E=M^d$ 且 $d$ 是 $n$ 的奇倍数，则其模 $p$ 作用是共同反射。仍需声明先报告与保护完成合同，以及实际读数对零位的投影；模代表从不替换实际非负整数来源。现有 $H=341,E=M^{15}$ 的物理装置只供应第103节的11、31两个因子。一般(105.1)参数的物理应用需要各自声明相容仪器，不能把这个固定装置自动扩展到所有素数。

若多个素数共享一个实际装置，所有候选必须随同一个实际 $R$ 次数和同一个全局符号演化；可顺序运行局部策略，并保留先前取得的初始标签，但不能独立指定各素数相位。第92节的初始／当前区分、第94节运输、第96节共同事件边界、第99节受限接口和第102节报告时序均保留。仓内 [finite_horizon_reachability](../../../D5/S3/ConceptDynamics/Control/FiniteHorizonReachability.lean) 供应有界策略与有限获胜层的既有抽象对应，不供应(105.4)的全域排除；这里没有编译其新实例。空间、时间、边界、记忆互相恢复还需要共同核心及更新／读出桥，局部双候选分离没有完成这一更广目标。

### 105.7 一个有界实例对回路、成本和共同符号的核对

以下 Python 3.9+ 标准库程序仅取新增参数 $p=19,\lambda=5$，先核对(105.1)。它遍历此实例的规范零差态、初始框架指数及阶段符号，检查(105.13)的到达、三接枝回路和最终测试，按真正需要的旋转数累计成本；另由原始 Fibonacci 矩阵重复作用核对(105.3)的读出及接枝逆像。宏内任意多个报告的作用由其累计符号表示，矩阵核对同时覆盖两个累计符号。程序不枚举候选集合，不运行第103节秩表，不做341模数的双候选乘积，也不以此实例裁定一般 $\delta$。

将本小节唯一的 Python 围栏原样保存为 `validate105.py`，在新建空目录运行 `python3 validate105.py`。`--mutate-epsilon` 将接枝逆像中的负号改成正号，应被 `joint epsilon` 断言拒绝；`--degenerate-loop` 改选 $t=7$，它满足平方／非平方条件但违反(105.8)的三次单位根排除，应被 `loop nonzero` 断言拒绝。两项是有意破坏公式或假设的负控。`--edge-cap 1` 应拒绝检查超限；`python3 -O validate105.py` 应拒绝关闭断言。每次运行设置120秒上限、至多150万次计数操作及至多10万条同时保留记录；断言承担验证，必须启用。有限核对不替代105.2—105.5的参数化证明。本例正常输出给 $A=16,B=5,t=1$，6,498组原坐标映射、12,870条终端历史，最大原语数33、最大接枝数5、每条终端历史一次测试；计数操作162,620次。这里的实例最大值33不是一般参数的最优界。

```python
import argparse
import json
import signal
import time
from itertools import product

if not __debug__:
    raise SystemExit('assertions must be enabled')
parser = argparse.ArgumentParser()
parser.add_argument('--mutate-epsilon', action='store_true')
parser.add_argument('--degenerate-loop', action='store_true')
parser.add_argument('--edge-cap', type=int, default=1500000)
opt = parser.parse_args()
if not 1 <= opt.edge_cap <= 1500000:
    raise SystemExit('invalid edge cap')

def expired(*_):
    raise RuntimeError('120-second cap')

signal.signal(signal.SIGALRM, expired)
signal.alarm(120)
start = time.monotonic()
edges = 0

def tick():
    global edges
    edges += 1
    assert edges <= opt.edge_cap, 'edge cap'

p, lam = 19, 5
n = (p - 1) // 2
inv = lambda a: pow(a % p, -1, p)
mu = (1 - lam) % p
Q = {pow(lam, j, p) for j in range(n)}
assert p > 3 and all(p % k for k in range(2, 5))
assert n % 2 == 1 and len(Q) == n and pow(lam, n, p) == 1
assert (lam * lam - lam - 1) % p == 0
assert Q == {a * a % p for a in range(1, p)}
s = (lam - mu) % p
A, B = (3 - 2 * mu) * inv(s) % p, (2 * lam - 3) * inv(s) % p
assert A and B and (A + B) % p == 2
assert A * B % p == inv(5) and (A - B) % p != 0
Tset = [t for t in sorted(Q) if (1 + t) % p not in Q | {0}]
assert len(Tset) == (p + 1) // 4
chosen = next(t for t in Tset if (t*t + t + 1) % p)
t = 7 if opt.degenerate_loop else chosen
assert t in Tset
loop = (1, t, -(1 + t) % p)
assert all(x in Q for x in loop) and sum(loop) % p == 0
for signs in product((1, -1), repeat=3):
    tick()
    assert sum(e * inv(x) for x, e in zip(loop, signs)) % p, 'loop nonzero'

# Check the pulled-back translation against raw integer-matrix actions.
def raw(c, w):
    return ((lam*w - mu*c) * inv(s) % p, (c-w) * inv(s) % p)

def Mpower(a, b, k):
    for _ in range(k):
        a, b = b, (a+b) % p
    return a, b

mapping_checks = 0
for j in range(n):
    x = pow(lam, -j, p)
    for sigma in (1, -1):
        epsilon = sigma * (-1)**j
        y = epsilon * inv(x) % p
        for c, w in product(range(p), repeat=2):
            tick()
            a, b = Mpower(*raw(c, w), j + (n if sigma == -1 else 0))
            assert (2*a + 3*b) % p == epsilon * (A*y*c + B*x*w) % p
            cg, wg = (a+1+lam*b) % p, (a+1+mu*b) % p
            pulled = (cg * inv(pow(lam, j, p)) % p,
                      wg * inv(sigma * pow(mu, j, p)) % p)
            trial_y = inv(x) if opt.mutate_epsilon else y
            assert pulled == ((c+x) % p, (w+trial_y) % p), 'joint epsilon'
            mapping_checks += 1

# Stack entries are live protocol histories, not an attractor table.
j_of = {pow(lam, -j, p): j for j in range(n)}
half = inv(2)
leaves = 0
peak = 0
max_cost = max_g = 0
for c0, w0, h0 in product(range(p), range(p), range(n)):
    a = (half-c0) % p
    if not a:
        plan = ()
    elif a in Q:
        plan = (a,)
    else:
        plan = (a * inv(1+t) % p, a*t * inv(1+t) % p)
    assert all(x in Q for x in plan) and sum(plan) % p == a
    stack = [(c0, w0, h0, plan, False, 0, 0)]
    while stack:
        peak = max(peak, len(stack))
        assert len(stack) + len(Q) + len(Tset) + len(j_of) + 32 <= 100000
        c, w, h, todo, loop_used, cost, gs = stack.pop()
        if todo:
            x, rest = todo[0], todo[1:]
            j = j_of[x]
            paid = (j-h) % n + 1
            for epsilon in (1, -1):
                tick()
                stack.append(((c+x) % p, (w+epsilon*inv(x)) % p,
                              j, rest, loop_used, cost+paid, gs+1))
            continue
        assert c == half
        if not w:
            assert not loop_used, 'loop nonzero'
            stack.append((c, w, h, loop, True, cost, gs))
            continue
        x = next(x for x in sorted(Q)
                 if (4*B*B*w*w*pow(x, 4, p)-A*A) % p == 0)
        total = cost + (j_of[x]-h) % n + 1
        for epsilon in (1, -1):
            tick()
            left = (A*epsilon*c*inv(x)+B*x*w) % p
            right = (A*epsilon*(c-1)*inv(x)+B*x*w) % p
            assert (left == 0) != (right == 0), 'terminal test'
        assert gs <= 5 and total <= 6*n
        assert total-gs-1 <= 6*(n-1)
        max_cost, max_g = max(max_cost, total), max(max_g, gs)
        leaves += 1

# Test the two separate existentials and their same-sign obstruction.
def J(c, w, delta):
    return ((2*c-1)*w-c*delta) % p

for delta in range(1, p):
    nonterminal = 0
    for c, w in product(range(p), repeat=2):
        if not J(c, w, delta):
            continue
        nonterminal += 1
        for x in Q:
            tests, successors = [], []
            for epsilon in (1, -1):
                tick()
                z = (A*epsilon*c*inv(x)+B*x*w) % p
                zp = (A*epsilon*(c-1)*inv(x)+B*x*(w-delta)) % p
                tests.append((z == 0) == (zp == 0))
                successors.append(J(c+x, w+epsilon*inv(x), delta) != 0)
            assert any(tests) and any(successors)
    assert nonterminal == p*p-p+1
c, w = -inv(A) % p, -inv(B) % p
assert J(c, w, 1) == 4*inv(A*B) % p
assert ((A*c+B*w) % p, (A*(c-1)+B*(w-1)) % p) == ((-2) % p, (-4) % p)
assert ((-A*c+B*w) % p, (-A*(c-1)+B*(w-1)) % p) == (0, (A-B) % p)
assert J(c+1, w+1, 1) == 0 and J(c+1, w-1, 1) == 2*B*inv(A) % p
signal.alarm(0)
print(json.dumps({'p': p, 'lambda': lam, 'n': n, 'A': A, 'B': B,
                  't': t, 'mapping_checks': mapping_checks,
                  'protocol_leaves': leaves, 'max_paid_primitives': max_cost,
                  'max_G': max_g, 'T_per_leaf': 1,
                  'peak_live_stack': peak, 'counted_operations': edges,
                  'retained_records_upper_bound': peak+len(Q)+len(Tset)+len(j_of)+32,
                  'elapsed_seconds': round(time.monotonic()-start, 6)}, sort_keys=True))
```

### 105.8 证明的承重范围

新进展是零差层的结构排除及有界分离协议，以及一般安全集的纤维与代数复杂度约束。第103节11／31的有限取得仍用其原证据；第104节终端门和一般有限到达桥在此直接复用。没有由论文标题、平均关联估计或一次有限计算移入新的全族定理，也没有原创优先权主张。非零差层需要同时控制测试可用性与同一分支的后继；终端补集的放松反例说明，这一联合关系不能省略。一般取得与更广的最小关系恢复目标继续保留其未证义务。

## 105.99 追加锚

## 106. 相关种子、逐纤维回路与保留相位的结构边界

本节沿用105.1的 Fibonacci 参数与先报告合同，推进非零差层的几个必要条件和局部分离证书。结果是普通数学：逐纤维的边覆盖界、统一的相关种子界、两类陷阱排除，以及忘记相位后的逆像重数。它们各有明确消费者；一般非零 $\delta$ 下排除所有非空精确安全集的命题仍未证明，也未由本节反驳。原始来源、初始标签与当前候选的关系仍按92.2、94.1及103.2保存，空间坐标的代数表达不自动成为观察者取得的信息。

### 106.1 参数与精确联合关系

除106.4中特别标明的较弱计数假设外，固定(105.1)：$p>3$ 为素数，$n=(p-1)/2$ 为奇数，$\lambda^2-\lambda-1=0$，$\operatorname{ord}(\lambda)=n$，$\mu=1-\lambda=-\lambda^{-1}$，$Q=\langle\lambda\rangle$ 为非零平方子群。记 $\chi(0)=0$，$\chi$ 为二次特征；$-1$ 非平方，平方与四次方映射均置换 $Q$。沿用 $A,B$，置 $S=A-B$、$a=A/B$。105.1已经给出

$$
A+B=2,\quad AB=1/5,\quad S=4/(2\lambda-1),\quad
a=\lambda^6\in Q,\quad n\ge5,\quad p\ge11.
$$

在固定差层写 $v=(c,w)$，代表候选对 $((c,w),(c-1,w-\delta))$。为避免符号被拆开，统一使用

$$
\begin{aligned}
L_e(v,x)&=Ae c/x+Bxw,\\
L'_e(v,x)&=Ae(c-1)/x+Bx(w-\delta),\\
Z_e(v,x)&\Longleftrightarrow [L_e(v,x)=0]=[L'_e(v,x)=0],\\
h_e(x)&=(x,e/x),\qquad J_\delta(c,w)=(2c-1)w-c\delta.
\end{aligned}
\tag{106.1}
$$

精确安全集是非空 $K$ 满足 $\forall v\in K\,\forall x\in Q\,\exists e\in\{1,-1\}$，同时有 $Z_e(v,x)$ 和 $v+h_e(x)\in K$。此处的一个 $e$ 承担测试与后继两个义务。只使用后继条件时，会明确说明这是必要条件；它不能单独证明相关游戏的安全或失败。

### 106.2 每条纤维上的缩放回路和边重数

**定理 106.1（逐纤维的边覆盖约束）。** 取105.4的 $t$，置

$$
D=\{e_1+e_2/t-e_3/(1+t):e_i\in\{1,-1\}\},\qquad
q=|D|/2\le4.
\tag{106.2}
$$

则 $D=-D$ 且 $0\notin D$。若 $K$ 满足精确安全条件，甚至只满足其中的后继条件，则每条纤维 $F_c=\{w:(c,w)\in K\}$ 非空，并且

$$
\forall w\in F_c\ \forall s\in Q,\qquad
(w+D/s)\cap F_c\ne\varnothing.
\tag{106.3}
$$

令 $m=|F_c|$，有

$$
q\binom m2\ge n\left\lceil\frac m2\right\rceil,
\qquad m\ge1+\left\lceil\frac nq\right\rceil.
\tag{106.4}
$$

若 $\chi(2)=-1$，可选 $t=1$ 并取 $q=3$；本节不在其他情形自动使用这个改进。

证明。105.4证明了存在 $t\in Q$，使 $\chi(1+t)=-1$ 且(106.2)的全部值非零；同时取负全部三个符号证明对称性，至多八个值证明 $q\le4$。对每个 $s\in Q$，三个预定阶段

$$
x_1=s,\quad x_2=st,\quad x_3=-s(1+t)
\tag{106.5}
$$

都属于 $Q$，和为零。连续应用后继条件，三个实际选中的符号给末态 $(c,w+d/s)$，$d\in D$；安全要求在每一步用其自身的同一个符号，未另选测试符号。故(106.3)成立。重复 $x=1$ 的后继令第一坐标遍历素域，证明所有纤维非空。

在 $F_c$ 上定义简单无向图 $\Gamma_s$：不同的 $w,z$ 相连当且仅当 $s(z-w)\in D$。对称性保证无向，零被排除保证不是自环，(106.3)保证无孤立点。固定一对不同顶点，每个对踵对 $\{d,-d\}\subset D$ 在 $d/(z-w),-d/(z-w)$ 中恰给一个平方尺度，因为 $-1$ 非平方；不同对踵对给不同尺度。因此该无序边恰在 $q$ 个图中出现，重数并非八种符号路径的条数：不同路径产生同一个 $d$ 时只计一次。每个无孤立点图至少有 $\lceil m/2\rceil$ 条边，跨 $n$ 个尺度求和即得第一式。对单个顶点也有 $n\le q(m-1)$，给第二式。

当 $m$ 为偶数时第一式化为 $q(m-1)\ge n$；当 $m$ 为奇数时，它要求

$$
q m(m-1)\ge n(m+1),
\tag{106.6}
$$

严格强于单顶点界。在本族 $n\ge5,q\le4$，每条纤维至少三点，因而排除所有两点纤维；奇数情形还可能继续排除三点纤维。若 $\chi(2)=-1$，$t=1$ 满足105.4的条件，且 $D=\{\pm1/2,\pm3/2,\pm5/2\}$。$p\ge11$ 保证六个值不同且非零，故此时 $q=3$。证毕。

### 106.3 一个接近获胜的列足以完成比较

**命题 106.2（有条件的列完成消费者）。** 固定 $\delta$。假设已经实际证明，在某列 $c=h$，每个 $w\notin B_0$ 都有覆盖全部符号历史、至多 $r$ 个阶段且恰一次 $T$ 的分离策略，其中残余 $B_0\subseteq\mathbb F_p$ 已知。若

$$
q(|B_0|-1)<n,
\tag{106.7}
$$

则全部规范候选对可用至多 $r+5$ 个阶段分离，仍恰一次 $T$。一个阶段包括至多 $n-1$ 个付费 $R$，随后一个 $G$ 或 $T$；在已实现接口中总成本至多 $n(r+5)$ 个付费原语，初始规范化偏移并入第一阶段。

证明。对 $w\in B_0$，每个 $z\in B_0\setminus\{w\}$ 恰禁止 $q$ 个满足 $s(z-w)\in D$ 的尺度。禁止尺度少于 $n$，故可选 $s\in Q$，使 $(w+D/s)\cap B_0=\varnothing$。执行(106.5)的三个 $G$ 阶段；全部八种有效符号三元组都结束在同列的已认证区域。随后接其策略，给列内至多 $r+3$ 阶段。

任意第一坐标 $c$ 到 $h$ 至多再用两个 $G$：写 $b=h-c$，$b=0$ 不接枝，$b\in Q$ 用 $x=b$；若 $b$ 非平方，用 $x=b/(1+t)$、$x'=bt/(1+t)$，二者为平方且和为 $b$。第一坐标增量与符号无关。两个对齐阶段加三个回路阶段给 $r+5$，并未新增 $T$。证毕。

奇数边覆盖也有实质消费者。若对每个 $1\le k\le |B_0|$ 均有

$$
q\binom k2<n\lceil k/2\rceil,
\tag{106.8}
$$

则残余上某个 $\Gamma_s$ 必有孤立顶点。它的三个回路阶段全部结束在当前残余外，故可认证并删除这一顶点；逐次删除，以已经认证的点作延续，得到至多 $r+3|B_0|+2$ 阶段。空残余直接使用已有策略。条件须对所有实际可能的剩余大小成立，不能只验初始大小。它确有比(106.7)多接纳的情形：$n=5,q=3,|B_0|=3$ 时(106.8)对 $k=1,2,3$ 成立，而(106.7)失败。两种条件均为充分条件。所需的获胜列补集尚未由传感器关系统一给出，不能把这一假设当作免费观察或已得结论。

### 106.4 终端目标与同符号的混合传感器种子

**引理 106.3（含退化端点的终端门）。** 在 $\delta\ne0$ 时，$H_\delta=\{J_\delta=0\}$ 恰是能选一个相位、对两个符号都由一次 $T$ 分离的集合。它有 $p-1$ 点，参数为

$$
(C,W)=\left(C,\frac{\delta C}{2C-1}\right),\qquad C\ne1/2.
\tag{106.9}
$$

证明。零测试可写成 $c+uw=0$ 与 $c-1+u(w-\delta)=0$，其中 $u=e(B/A)x^2$。平方置换奇阶 $Q$，因此相位与两个符号提供全部非零斜率的对踵对。在 $H_\delta$ 上，除 $(0,0),(1,\delta)$ 外，两候选的零斜率分别为 $-(2C-1)/\delta$ 与 $(2C-1)/\delta$，不同且互为负数。选这一对，两个符号各恰使一个候选为零。两个端点有一个候选为原点，始终读零；另一候选至多禁止一个相位，$n>1$ 提供可避开的相位。$C=1/2$ 无解，证明计数。反之，除原点候选外，每个候选至多提供一个非零零斜率；两个符号均分离要求两个零斜率为不同对踵值，消去分母正得 $J_\delta=0$。坐标轴上的非原点候选可能没有非零零斜率，不能贡献第二个分离符号；上述两个原点端点已包含在内。故没有漏出的退化终端。证毕。

**定理 106.4（统一非终端相关种子界）。** 本定理只需 $p>3$、$p\equiv3\pmod4$、$Q$ 为非零平方子群，以及 $AB(A-B)\delta\ne0$。定义

$$
C_\delta=\{v\notin H_\delta:\exists x\in Q,\ e\in\{1,-1\},\quad
Z_e(v,x),\quad\neg Z_{-e}(v,x),\quad v+h_e(x)\in H_\delta\}.
\tag{106.10}
$$

同一个 $e$ 的测试相等且后继终端，另一个符号直接分离。则

$$
|C_\delta|\ge\max\{0,\lceil p-9-2\sqrt p\rceil\}.
\tag{106.11}
$$

因此 $p\ge19$ 时该集合非空；在105.1的 Fibonacci 子族，它对每个非零 $\delta$ 均非空，较小的 $p=11$ 由下面的五个证书补足。任何精确安全集均避开 $H_\delta\cup C_\delta$。

证明。先让证明参数 $X$ 遍历全部非零域元素，$e$ 遍历两个符号。从(106.9)的终端目标取前驱

$$
c=C-X,\qquad w=W-e/X.
$$

要求相反符号的第一候选读零，即 $-Ae c/X+BXw=0$。清除非零分母后得到关于终端坐标 $C$ 的二次式

$$
F_e(X,C)=2AC^2-(Be\delta X^2+2SX+A)C+SX=0.
\tag{106.12}
$$

$F_e(X,1/2)=-Be\delta X^2/2\ne0$，所以清分母没有引入 $C=1/2$ 的伪根。记 $b=Be\delta$。剔除下列三类关联：$bX^2=A$；$c=0$；$2Ac=A+bX^2$。其余关联满足 $w=ae c/X^2$。符号 $-e$ 的两读数是 $0$ 与 $Ae/X-BX\delta$，后者因第一类已排除而非零；符号 $e$ 的两读数是 $2Ae c/X$ 与 $Ae(2c-1)/X-BX\delta$，因第二、三类已排除而都非零。并且

$$
J_\delta(c,w)=c\bigl(ae(2c-1)/X^2-\delta\bigr)\ne0,
\qquad (c,w)+h_e(X)=(C,W)\in H_\delta.
$$

因此两个合取项确实共享 $e$。

若 $X\in Q$，直接输出 $v=(c,w),x=X$；若 $X$ 非平方，输出另一个起始候选对 $v'=(1-c,\delta-w),x=-X\in Q$，仍保留 $e$。映射 $I(c,w)=(1-c,\delta-w)$ 满足 $J_\delta(Iv)=J_\delta(v)$、$I(v+h_e(X))=Iv+h_e(-X)$；在 $Iv,-X$ 上的两读数是原来的两读数交换次序。因此得到合法平方相位的种子，第二候选承担相反符号的零。这里构造的是另一对起始候选，绝不执行免费的物理取负、交换来源或相位反转。

下面只给(106.11)的一个计数证明。二次式的判别式为

$$
\mathcal D_e(X)=(bX^2+2SX+A)^2-8ASX.
\tag{106.13}
$$

它有平方首项 $b^2$ 和非零常数 $A^2$，不是常数倍的平方，甚至在代数闭包中也不是平方。若它是平方，选平方根首项为 $b$；比较三次系数使平方根为 $bX^2+2SX+\ell$，比较一次系数给 $\ell=-A$，二次系数再给 $4bA=0$，矛盾。非平方常数乘平方也不可能，因为首项已经是平方。

对这类四次式有

$$
\sum_{X\in\mathbb F_p}\chi(\mathcal D_e(X))\ge-1-2\sqrt p.
\tag{106.14}
$$

精确文献桥如下。先除以平方 $b^2$，得到首一四次式 $f=X^4+a_3X^3+a_2X^2+a_1X+a_0$。在 $f$ 无重根时，Bogdan Nica，[*On quadratic character sums over quartics*，arXiv:2507.09991v1](https://arxiv.org/html/2507.09991v1)，定理2.2、式(6)给出的原陈述是

$$
\sum_X\chi(f(X))=-1+\sum_T\chi(g(T)),\quad
g(T)=T^3+a_2T^2+(a_1a_3-4a_0)T+a_0(a_3^2-4a_2)+a_1^2.
\tag{106.15}
$$

这里 $p>3$ 满足文章的特征限制，$f$ 首一和无重根是逐项假设，$-1$ 不得丢掉。若 $g$ 无重根，$y^2=g(T)$ 的光滑射影模型为椭圆曲线，且有一个有理无穷远点，所以点数为 $p+1+\sum_T\chi(g(T))$。经典 Hasse 界给特征和至少 $-2\sqrt p$。可核对的文献陈述是 Agathocleous–Joux–Taufer，[*Elliptic curves over Hasse pairs*，arXiv:2406.03399v1](https://arxiv.org/html/2406.03399v1)，定理2.1所引 Waterhouse 迹分类：把其 $q=p^a$ 取为 $p$、指数取1、$p>3$，非空椭圆曲线类的迹只可能属于其(a)或(e)，二者都满足 $|t|\le2\sqrt p$。本处不需要点数是素数幂、不需要 Hasse pair，也不借用曲线存在性来填补奇异情形。

若 $g$ 有重根，它是 $(T-r)^2(T-s)$ 或 $(T-r)^3$，其中重复根在本域；前者的特征和为 $-\chi(r-s)$，后者为0。故仍有(106.14)，但不把奇异三次式称为椭圆曲线。若 $f$ 本身有重根，四次且非平方迫使 $f=h^2k$，$h$ 为首一一次式，$k$ 为首一无重根二次式，允许 $h$ 的根也是 $k$ 的根。理由是偶数总次数的奇重数部分只能有次数2；若有重复的不可约二次因子，则四次式是平方，已经排除。无重根二次式满足 $\sum_X\chi(k(X))=-1$，这可由完成平方后计数 $(u-v)(u+v)=d\ne0$ 得到；乘 $h^2$ 只在 $h$ 的一个根处删除一个值，故 $\sum\chi(f)\ge-2$。这也强于所需下界。全部重根情况都已单独覆盖。

固定 $e,X\ne0$ 时，$2A\ne0$，所以二次式有 $1+\chi(\mathcal D_e(X))$ 个不同 $C$ 根，重根算一次。因 $\mathcal D_e(0)=A^2$，两符号的原始关联数至少

$$
2\bigl(p-2-1-2\sqrt p\bigr)=2p-6-4\sqrt p.
\tag{106.16}
$$

三类剔除合计至多12次关联。第一类 $e\delta X^2=a$ 恰有两个 $(X,e)$：$-1$ 非平方使两符号仅一个可取平方根，每个至多两个 $C$ 根，故至多4。第二类 $c=0$ 使 $w=0$，终端后继条件化为 $e\delta X^2-2X+1=0$，每符号至多两个 $X$，故至多4。第三类在 $c\ne0$ 时令 $J_\delta(c,w)=0$；把 $c=(ae+\delta X^2)/(2ae)$ 代入其终端后继条件，得到 $e\delta X^2+2aX+a^2=0$，故至多4。与 $c=0$ 重叠者已由第二类计入；相互重复剔除只使并集上界更宽，不会增加12。

每个输出点的重数至多2。非零坐标的一个候选恰有一个零传感器选择 $(x,e)$：两个符号决定平方类，平方在奇阶 $Q$ 上为双射。平方 $X$ 的构造由输出的第一候选唯一确定，非平方折叠的构造由输出的第二候选唯一确定；每一类还由 $C=c+X$ 唯一恢复终端目标。剩下关联数至少 $2p-18-4\sqrt p$，除以2、取整数上整并与零比较，即得(106.11)。$p-9-2\sqrt p$ 在 $p\ge19$ 为正且递增。

本族 $p\ge11$，$p<19$ 且 $p\equiv3\pmod4$ 的唯一可能是11。该域 $A=6,B=7$；下列 $(\delta;c,w,x,e)$ 分别是五个证书：

$$
\begin{gathered}
(1;9,3,1,+1),\quad(2;1,4,1,+1),\quad(3;9,0,9,+1),\\
(4;2,1,5,-1),\quad(5;2,6,9,+1).
\end{gathered}
\tag{106.17}
$$

逐个代入(106.1)得到 $J_\delta(v)=9,2,6,6,8$，均非零；符号 $e$ 的两读数依次为 $(9,7),(1,3),(6,7),(4,6),(9,5)$，相反符号的两读数为 $(0,10),(0,3),(5,0),(0,4),(10,0)$，且全部同 $e$ 后继满足 $J_\delta=0$。对 $-\delta$ 用 $(c,-w,x,-e)$：读数共同取负，$J$ 共同取负，故覆盖全部十个非零差值。最后，安全集不能含终端点；在种子上 $-e$ 测试分离，$e$ 的后继终端，两个符号均不能履行安全合取。证毕。

### 106.5 种子的付费执行和初始标签消费者

**命题 106.5（每个种子至多两阶段、恰一次读）。** 对 $v\in C_\delta$ 及其证书 $(x,e)$，先用至多 $n-1$ 个实际 $R$ 对齐 $x$，消耗并记录每份 offer。到目标相位后，若已宣布的有效符号为 $-e$，执行 $T$；若为 $e$，执行 $G$，进入 $H_\delta$，再用至多 $n-1$ 个 $R$ 对齐引理106.3的终端相位并执行 $T$。每条执行至多 $2n$ 个付费原语、至多一个 $G$、恰一个 $T$。

证明。保留的共同线性框架在 $j$ 个旋转和累计反射 $\eta$ 后为 $\operatorname{diag}(\lambda^j,\eta\mu^j)$。置 $x=\lambda^{-j}$、$\epsilon=\eta(-1)^j$，框架为 $\operatorname{diag}(1/x,\epsilon x)$。物理标量乘单位 $\epsilon$ 后正是 $L_\epsilon$；物理接枝的框架逆像正是 $h_\epsilon(x)$。因此报告给测试和接枝的是同一个有效符号。两个分支由(106.10)和引理106.3保证分离；每个阶段至多 $n-1$ 个旋转加一个 $G/T$。首份正号是已覆盖的两个符号之一，不能重发或放弃。初始虚拟规范化的偏移按103.4并入第一目标相位；逆框架只更新候选记忆，未实施逆动作。证毕。

在既有物理装置 $E=M^{15},T=\gcd(2a+3b,341)$ 上，这一执行桥只用于11、31两个分量。一般素数的(106.11)属于抽象规范游戏，$\gcd341$ 不提供其他素数的整除位，$M^{15}$ 也不自动在其他域实现所需反射。模31候选必须在模11活动期间接收同一个实际命令和报告，反之亦然，不存在独立素数时序。

每个存活槽保留不可变初始 $c_0$ 与共同 $c=u c_0+t$，$u\ne0$；$R$ 更新 $(u,t)$ 为 $(\lambda u,\lambda t)$，$G$ 更新为 $(u,t+1)$，报告和 $T$ 不改变它。来自同一实际来源的槽不会被正确零位筛选删除；一次证书比较删除至少一个不同标签的所选槽。这给可识别种子的局部取得消费者。它没有证明任意两个不同标签都能找到这种证书，也没有据此完成全标签取得。

### 106.6 无平移周期和无二次标量带

**定理 106.6（精确安全集的加法稳定子平凡）。** 在本族，对任意 $\delta$，非空精确安全集没有非零加法周期 $r$，即 $K+r=K$ 只能有 $r=0$。

证明。固定一个非例外相位 $x$，使

$$
D_+D_-\ne0,\qquad D_e=Ae/x+Bx\delta.
\tag{106.18}
$$

若 $\delta=0$，每个相位非例外；若 $\delta\ne0$，例外条件为 $x^4=a^2/\delta^2$，四次方置换奇阶 $Q$，故至多一个相位例外。$n>1$ 保证可选非例外相位。

反设周期 $r=(u,v)\ne0$。素域性质给 $K+tr=K$ 对全部 $t\in\mathbb F_p$ 成立。对符号 $s$ 置 $q_s=L_{-s}(r,x)=-Asu/x+Bxv$、$z_s=\det(r,h_s)=su/x-vx$。至少一个 $s$ 使 $q_sz_s\ne0$。若 $u=0$ 或 $v=0$，由 $A,B,x$ 非零立即成立；否则令 $t=vx^2/u$，符号 $+$ 失败要求 $t\in\{1,a\}$，符号 $-$ 失败要求 $t\in\{-1,-a\}$。两集合不交，因为域特征非2，$a\ne0,-1$，其中 $a\ne-1$ 正是 $A+B\ne0$。这也覆盖 $a=1$ 时集合缩为单点的退化。

选此 $s$。任取 $y\in K$，整条 $y+\mathbb F_p r$ 在 $K$；因 $q_s\ne0$，其中一点使 $L_{-s}=0$。其第二读数为 $-D_{-s}\ne0$，故只能选 $s$ 的安全后继。再减去周期位移，得到 $y+h_s\in K$。有限性把 $K+h_s\subseteq K$ 提升为相等。$z_s\ne0$ 使 $r,h_s$ 张成整个平面，故非空 $K$ 必为全平面。然而原点在该非例外相位的两个符号都读数不等，矛盾。证毕。

消费者是直接拒绝任何非恒定线性坐标的集合谓词，包括任意多条平行直线的并、或对一个线性坐标施加特征谓词。数学周期在证明中用于矛盾，不授予控制器一次免费的物理平移。

**定理 106.7（无次数至多二的共同标量带）。** 不存在非空精确安全集形如

$$
K=\{(c,w):w-f(c)\in U\},\qquad U\subseteq\mathbb F_p,\quad\deg f\le2.
\tag{106.19}
$$

证明。$U=\varnothing$ 不满足非空前提。若 $f$ 为常数、一次式或零多项式，$(1,f(c+1)-f(c))$ 是非零周期，已由定理106.6排除；这包括 $U=\mathbb F_p$ 的全平面。设 $f(c)=a_2c^2+a_1c+a_0$，$a_2\ne0$。取 $u_0\in U$，后继的两个残余为

$$
u_0-[f(c+x)-f(c)]\pm1/x.
$$

对固定 $x\ne0$，$f(c+x)-f(c)=2a_2xc+a_2x^2+a_1x$ 遍历全域。后继闭合因而要求每个 $t$ 至少有 $t+1/x$、$t-1/x$ 之一在 $U$。若两个不同 $u,v$ 都不在 $U$，取允许的平方相位使 $\{1/x,-1/x\}=\{(u-v)/2,-(u-v)/2\}$；因 $Q\sqcup(-Q)=\mathbb F_p^\times$ 总可取到。以 $t=(u+v)/2$ 得矛盾，故 $U$ 至多漏一个值。

若没有漏值，仍是全平面。若只漏 $b$，补集为图 $w=f(c)+b$。$\delta\ne0$ 时它与 $H_\delta$ 的交点满足 $(2c-1)(f(c)+b)-c\delta=0$；这是次数至多3的非零多项式，因为在 $c=1/2$ 值为 $-\delta/2\ne0$，故至多三个根。$H_\delta$ 有 $p-1$ 点，至少 $p-4>0$ 个终端点在 $K$，与安全矛盾。$\delta=0$ 已被定理105.3排除，不把非零差的清分母论证延伸过去。证毕。

这排除任意选取平行抛物线的并，其定义乘积可以有很高次数；它不假定一般 $K$ 都能写成(106.19)。系数 $a_2=0$、空 $U$、全 $U$、只漏一点与零差层已经分别处理。$A,B,A+B$ 非零和 $n>1$ 是上面周期论证的实际假设，不能删去后声称同一排除仍成立。

### 106.7 忘记相位后至多三重的强制逆像

**命题 106.8（第一传感器强制关系的完整逆像）。** 在 $cw\ne0$ 时，恰有一个 $(x,e)\in Q\times\{1,-1\}$ 使 $L_e(v,x)=0$：$e=-\chi(cw)$，$x^2=-ae c/w$。定义

$$
\mathcal F(c,w)=(c+x,w-e/x).
\tag{106.20}
$$

若 $v$ 属精确安全集且 $w-c\delta\ne0$，符号 $e$ 分离，安全性只能使用相反符号，故 $\mathcal F(v)$ 也在该集。目标 $(C,W)$ 的全部逆像恰为

$$
v=(C-x,W+e/x),\quad x\in Q,\quad e\in\{1,-1\},\quad
BeWx^2+(B-A)x+AC=0,
\tag{106.21}
$$

并要求 $(C-x)(W+e/x)\ne0$。忘记相位的 $\mathcal F$ 在全域至多三对一，此界可达。

证明。$a\in Q$ 和 $-1$ 非平方使零方程唯一选择 $e$，奇阶 $Q$ 的平方双射再唯一选择 $x$。在该零方程下，另一候选读数为 $-Ae/x-Bx\delta=(Bx/c)(w-c\delta)$，等价于 $w-c\delta\ne0$ 时非零；所以(106.20)是同一符号约束所迫的后继。代入目标逆像形式并乘 $x/e$ 即得(106.21)；反向代入加上非零坐标条件恢复定义中的唯一零分支，因此没有多算未知相位。

若 $CW\ne0$，二次式判别式和根积分别是

$$
\Delta_e=S^2-4eAB CW=4(4-eCW)/5,\qquad
\text{根积}=aeC/W.
\tag{106.22}
$$

恰一个符号的根积非平方，其二次式最多一个平方根，另一个最多两个；重复根仍只算一个，故总数至多3。若 $C=0,W\ne0$，非零根是 $x=S/(BeW)$，两个符号给相反值，最多一个在 $Q$。若 $W=0,C\ne0$，根固定为 $x=AC/S$，两符号最多给两个逆像。$(C,W)=(0,0)$ 只剩 $-Sx=0$，没有允许根。这涵盖所有降次情形。

界的可达证书为 $p=11,A=6,B=7,\delta=1$、目标 $(2,5)$：逆像 $(1,4),(8,7),(10,9)$ 分别使用 $(e,x)=(-1,1),(-1,5),(+1,3)$。三者 $cw\ne0,w-c\delta\ne0,J_\delta\ne0$，相反符号测试相等且达到目标。它们是不同相位历史，并非同一物理动作字把不同来源合并。证毕。

非单射也有无需枚举的证书：取不同 $x,z\in Q$、任意 $e$，令 $C=Sxz/[A(x+z)]$、$W=S/[Be(x+z)]$。因 $-1$ 非平方，$x+z\ne0$；(106.21)的两个根是 $x,z$，给两个不同逆像。其非零坐标条件只可能被 $Ax+Bz=0$ 破坏，但 $x/z$ 为平方、$-B/A$ 非平方，故不会发生。第二传感器对应平移后的逆式

$$
Be(W-\delta)x^2+(B-A)x+A(C-1)=0.
\tag{106.23}
$$

消费者须保留每条边的 $(x,e)$，并同时处理 $cw=0$、$(c-1)(w-\delta)=0$ 和静默线 $w=c\delta$。至多三重的逆像计数不能冒充扩张估计。相反，每份固定实际历史由可逆矩阵与平移组成，始终单射；103.1的初始标签运输未被这些跨历史碰撞推翻。

### 106.8 一个实际单传感器控制器的五十原语周期

**命题 106.9（固定正来源上的特定控制器失败）。** 在既有341装置、所有隐藏批均为零时，从固定正来源 $(93,93)$ 和 $(62,62)$ 分别执行同一无限字 $(T,G,R,R,R)^\infty$，两份执行的每次 gcd 相同而初始标签不同。这只反驳这个控制器，不是全相位精确安全集，也不反驳103的取得协议。

证明。两初始标签 $a+81b\pmod{341}$ 为124、310，模31的两初态同为零。模11初始候选为 $((3,1),(2,8))$，差层 $\delta=4$。第 $k$ 次 $T$ 前有 $3k$ 个实际 $R$；拉回已记录框架得到 $x=\lambda^{-3k}$、有效符号 $(-1)^k$。这些是记忆中的运输计算。规范第一候选在十次比较处依次为

$$
\begin{gathered}
(3,1),(4,2),(9,4),(1,8),(5,5),\\
(3,10),(4,9),(9,7),(1,3),(5,6),
\end{gathered}
\tag{106.24}
$$

相位为 $1,5,3,4,9,1,5,3,4,9$，实际规范后继符号为 $+,-,+,-,+,-,+,-,+,-$。逐个代入，各点 $J_4\ne0$，实际符号的两标量都非零；相反符号令第一标量为零。在 $(3,1)$，$w=c\delta$，两候选零位对两个符号都相等；其他九点的相反符号分离，因此所列后继被第一传感器关系强制。按静默点所列分支继续，(106.20)闭合此十点周期，排除把这个规则及这份静默延续赋予严格下降秩的办法。

直接用原始整数矩阵、绝不重新选模代表，十个 $T$ 的共同 gcd 为

$$
(31,1,1,31,1,1,1,1,1,1).
\tag{106.25}
$$

周期为何永远继续也有代数证明。按103.2，$M^{30}\equiv I\pmod{341}$，且

$$
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
\det(I-M^3)=-4
$$

是模341的单位。几何和恒等式给 $\sum_{j=0}^9M^{3j}=0$。$G$ 后三个 $R$ 的仿射作用为 $s\mapsto M^3s+M^3\alpha$；十次复合的平移为 $\sum_{j=1}^{10}M^{3j}\alpha=0$，故两剩余状态各自返回初态。$T$ 不改变状态，因此(106.25)无限重复。实际正整数来源继续增长，周期只在剩余和 gcd 层成立。一个周期恰十个 $T$、十个 $G$、三十个 $R$，共五十个付费原语与五十份已消耗 offer；每批 $k=0$，首份正号合法。十点甚至未投影到全部第一坐标，已不满足精确安全集的全相位要求。证毕。

### 106.9 可复用的有界关联与原始整数核验

以下程序有两个独立用途：核验显式混合关联的例外数与输出重数，并从固定正整数来源重放局部证书和特定失败字。它只用已经考察过的11、19、31，不作素数分类、全341候选乘积、安全集幂集或全局获胜秩枚举。关联计数逐个检查相同符号的测试与后继；五个11证书及其符号对称像的付费执行覆盖全部后续二元报告分支，首批固定零。负对照拒绝符号拆分、伪称十点全相位安全、错误种子符号及超预算；所有关键检查使用显式异常，优化运行也不能删去。另以一个非静默点和一个静默点核验106.8的负号及未改动的逆像式(106.21)。时限异常独立于负对照预期的核验异常，不能被 `rejected` 捕获；真实 `SIGALRM` 在其回调内触发时也以非零退出结束。每次运行限120秒、100000记录、1500000边，并限制原始整数位数；超限和核验失败均非零退出。数值核验支持这里的证书，通用下界由106.4的证明和文献条件承担。

```python
import json
import math
import signal
from collections import Counter


class CheckFailure(RuntimeError):
    pass


class DeadlineExceeded(RuntimeError):
    pass


def require(ok, message):
    if not ok:
        raise CheckFailure(message)


class Budget:
    def __init__(self, records=100000, edges=1500000):
        self.records = self.edges = 0
        self.record_cap, self.edge_cap = records, edges

    def charge(self, records=0, edges=0):
        self.records += records
        self.edges += edges
        require(self.records <= self.record_cap, "record cap")
        require(self.edges <= self.edge_cap, "edge cap")


budget = Budget()


def timeout(signum, frame):
    raise DeadlineExceeded("120 second cap")


def rejected(function):
    try:
        function()
    except CheckFailure:
        return
    raise CheckFailure("negative control accepted")


def chi(t, p):
    t %= p
    if not t:
        return 0
    return 1 if pow(t, (p - 1) // 2, p) == 1 else -1


def jvalue(c, w, d, p):
    return ((2 * c - 1) * w - c * d) % p


def readings(c, w, d, x, e, A, B, p):
    inv = pow(x, -1, p)
    return ((A * e * c * inv + B * x * w) % p,
            (A * e * (c - 1) * inv + B * x * (w - d)) % p)


def equal(c, w, d, x, e, A, B, p):
    u, v = readings(c, w, d, x, e, A, B, p)
    return (u == 0) == (v == 0)


def seed(c, w, d, x, e, A, B, p):
    require(d % p != 0 and e in (-1, 1), "seed parameters")
    require(chi(x, p) == 1, "nonsquare physical phase")
    require(jvalue(c, w, d, p) != 0, "terminal seed")
    require(equal(c, w, d, x, e, A, B, p), "equal sign")
    require(not equal(c, w, d, x, -e, A, B, p), "opposite split")
    require(jvalue(c + x, w + e * pow(x, -1, p), d, p) == 0,
            "same sign terminal successor")


def forced_reading_audit():
    for d, c, w, x, e, expected, wrong_expected in (
            (1, 1, 10, 9, 1, 6, 0), (4, 3, 1, 1, -1, 0, 10)):
        budget.charge(records=1)
        inv = pow(x, -1, 11)
        first, second = readings(c, w, d, x, e, 6, 7, 11)
        require(first == 0, "forced reading premise")
        require(second == (-6 * e * inv - 7 * x * d) % 11 == expected,
                "forced second reading sign")
        require(second == 7 * x * pow(c, -1, 11) * (w - c * d) % 11,
                "forced reading factorization")
        wrong = (6 * e * inv - 7 * x * d) % 11
        require(wrong == wrong_expected and wrong != second, "old sign regression")
        require((second == 0) == ((w - c * d) % 11 == 0), "silent line")
        C, W = (c + x) % 11, (w - e * inv) % 11
        require((7 * e * W * x * x + (7 - 6) * x + 6 * C) % 11 == 0,
                "unchanged forced inverse")
    return 2


def incidence_audit():
    parameters = max_bad = max_multiple = 0
    for p, lam in ((11, 4), (19, 5), (31, 19)):
        mu = (1 - lam) % p
        inv = pow((lam - mu) % p, -1, p)
        A, B = (3 - 2 * mu) * inv % p, (2 * lam - 3) * inv % p
        S, a = (A - B) % p, A * pow(B, -1, p) % p
        for d in range(1, p):
            raw = bad = 0
            outputs = Counter()
            character_sums = []
            for e in (-1, 1):
                b = B * e * d % p
                character_sum = sum(chi((b * X * X + 2 * S * X + A) ** 2
                                        - 8 * A * S * X, p) for X in range(p))
                budget.charge(records=p)
                require(character_sum >= -1 - 2 * math.sqrt(p), "character bound")
                character_sums.append(character_sum)
                for X in range(1, p):
                    roots = 0
                    for C in range(p):
                        budget.charge(records=1)
                        polynomial = (2 * A * C * C
                                      - (b * X * X + 2 * S * X + A) * C + S * X)
                        if polynomial % p:
                            continue
                        roots += 1
                        raw += 1
                        require((2 * C - 1) % p != 0, "spurious denominator root")
                        W = d * C * pow((2 * C - 1) % p, -1, p) % p
                        c, w = (C - X) % p, (W - e * pow(X, -1, p)) % p
                        if ((b * X * X - A) % p == 0 or c == 0
                                or (2 * A * c - A - b * X * X) % p == 0):
                            bad += 1
                            continue
                        if chi(X, p) == 1:
                            x, out = X, (c, w)
                        else:
                            x, out = (-X) % p, ((1 - c) % p, (d - w) % p)
                        seed(*out, d, x, e, A, B, p)
                        budget.charge(edges=2)
                        outputs[out] += 1
                    disc = (b * X * X + 2 * S * X + A) ** 2 - 8 * A * S * X
                    require(roots == 1 + chi(disc, p), "quadratic root count")
            require(raw == 2 * (p - 2) + sum(character_sums), "incidence identity")
            require(bad <= 12, "exceptional incidence count")
            multiple = max(outputs.values(), default=0)
            require(multiple <= 2, "fold multiplicity")
            require(2 * len(outputs) >= raw - bad, "output count")
            require(len(outputs) >= max(0, math.ceil(p - 9 - 2 * math.sqrt(p))),
                    "seed lower bound")
            parameters += 1
            max_bad, max_multiple = max(max_bad, bad), max(max_multiple, multiple)
    return {"parameters": parameters, "max_bad": max_bad,
            "max_output_multiplicity": max_multiple}


def rotate(v):
    a, b = v
    return b, a + b


def reflect(v):
    a, b = v
    return 377 * a + 610 * b, 610 * a + 987 * b


def coord(v, p):
    a, b = v
    return (a + 81 * b) % p, (a + 261 * b) % p


def lift(c, w):
    b = (w - c) * pow(4, -1, 11) % 11
    a = (c - 4 * b) % 11
    # A fixed positive lift, zero modulo 31, chosen once per execution.
    return tuple(31 * (t * pow(31, -1, 11) % 11) or 341 for t in (a, b))


def paid_seed(c, w, d, x, e):
    seed(c, w, d, x, e, 6, 7, 11)
    initial = (lift(c, w), lift((c - 1) % 11, (w - d) % 11))
    labels = tuple(coord(v, 11)[0] for v in initial)
    require(labels[0] != labels[1], "initial labels")
    phases = {pow(4, -j, 11): j for j in range(5)}
    leaves, max_paid = 0, 0

    def walk(sources, c, w, phase, eta, remaining, terminal,
             paid, nr, ng, u, t):
        nonlocal leaves, max_paid
        for k in ((0,) if paid == 0 else (0, 1)):
            budget.charge(records=1, edges=2)
            state = tuple(reflect(v) for v in sources) if k else sources
            sign = eta * (-1 if k else 1)
            epsilon = sign * (-1 if phase % 2 else 1)
            current_x = pow(4, -phase, 11)
            base = ((c, w), ((c - 1) % 11, (w - d) % 11))
            for i, actual in enumerate(state):
                require(max(a.bit_length() for a in actual) <= 8192, "integer cap")
                expected = (pow(4, phase, 11) * base[i][0] % 11,
                            sign * pow(8, phase, 11) * base[i][1] % 11)
                require(coord(actual, 11) == expected, "retained physical frame")
                require(expected[0] == (u * labels[i] + t) % 11, "label transport")
            actual_zeros = tuple((2 * a + 3 * b) % 11 == 0 for a, b in state)
            predicted = tuple(z == 0 for z in
                              readings(c, w, d, current_x, epsilon, 6, 7, 11))
            require(actual_zeros == predicted, "same sign reading bridge")
            if remaining:
                walk(tuple(rotate(v) for v in state), c, w, (phase + 1) % 5,
                     -sign if phase == 4 else sign, remaining - 1, terminal,
                     paid + 1, nr + 1, ng, 4 * u % 11, 4 * t % 11)
            elif terminal or epsilon == -e:
                require(actual_zeros[0] != actual_zeros[1], "paid T split")
                values = tuple(math.gcd(2 * a + 3 * b, 341) for a, b in state)
                require(values[0] != values[1], "actual gcd split")
                require(paid + 1 <= 10 and nr <= 8 and ng <= 1, "paid bound")
                leaves += 1
                max_paid = max(max_paid, paid + 1)
            else:
                require(epsilon == e and current_x == x, "selected seed branch")
                require(actual_zeros[0] == actual_zeros[1], "G tests agree")
                nc, nw = (c + x) % 11, (w + e * pow(x, -1, 11)) % 11
                require(jvalue(nc, nw, d, 11) == 0, "paid terminal successor")
                target = next(y for y in sorted(phases)
                              if all(not equal(nc, nw, d, y, s, 6, 7, 11)
                                     for s in (-1, 1)))
                aligned = (phases[target] - phase) % 5
                next_sources = tuple((a + 1, b) for a, b in state)
                walk(next_sources, nc, nw, phase, sign, aligned, True,
                     paid + 1, nr, ng + 1, u, (t + 1) % 11)

    walk(initial, c, w, 0, 1, phases[x], False, 0, 0, 0, 1, 0)
    require(leaves > 0, "empty replay")
    return leaves, max_paid


def cycle_audit():
    initial = ((93, 93), (62, 62))
    state = initial
    require(tuple((a + 81 * b) % 341 for a, b in state) == (124, 310),
            "cycle initial labels")
    vertices = ((3, 1), (4, 2), (9, 4), (1, 8), (5, 5),
                (3, 10), (4, 9), (9, 7), (1, 3), (5, 6))
    expected = (31, 1, 1, 31, 1, 1, 1, 1, 1, 1)
    values = []
    for k in range(10):
        budget.charge(records=1, edges=10)
        c, w = vertices[k]
        x, e = pow(4, -3 * k, 11), (-1) ** k
        require(jvalue(c, w, 4, 11) != 0, "cycle terminal")
        require(equal(c, w, 4, x, e, 6, 7, 11), "cycle actual sign")
        require(readings(c, w, 4, x, -e, 6, 7, 11)[0] == 0, "forced zero")
        require((w - 4 * c) % 11 == 0 or
                not equal(c, w, 4, x, -e, 6, 7, 11), "forced successor")
        for i, actual in enumerate(state):
            base = (c, w) if i == 0 else ((c - 1) % 11, (w - 4) % 11)
            require(coord(actual, 11) == (pow(4, 3 * k, 11) * base[0] % 11,
                                         pow(8, 3 * k, 11) * base[1] % 11),
                    "cycle raw matrix frame")
        ys = tuple(math.gcd(2 * a + 3 * b, 341) for a, b in state)
        require(ys == (expected[k], expected[k]), "ten read pattern")
        values.append(ys[0])  # T is paid and does not alter either source.
        state = tuple((a + 1, b) for a, b in state)
        for _ in range(3):
            state = tuple(rotate(v) for v in state)
    require(tuple(tuple(t % 341 for t in v) for v in state) == initial,
            "50 primitive residue period")
    return vertices, values


def claims_audit(vertices):
    # Reject an erroneous promotion of the selected cycle to an all-phase K.
    for c, w in vertices:
        for x in (1, 3, 4, 5, 9):
            require(any(equal(c, w, 4, x, e, 6, 7, 11) and
                        ((c + x) % 11, (w + e * pow(x, -1, 11)) % 11) in vertices
                        for e in (-1, 1)), "cycle is not all-phase safe")


def main():
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(120)
    try:
        formula_regressions = forced_reading_audit()
        incidences = incidence_audit()
        certificates = ((1, 9, 3, 1, 1), (2, 1, 4, 1, 1), (3, 9, 0, 9, 1),
                        (4, 2, 1, 5, -1), (5, 2, 6, 9, 1))
        histories = max_paid = 0
        for d, c, w, x, e in certificates:
            for sign in (1, -1):
                count, cost = paid_seed(c, sign * w % 11, sign * d % 11, x, sign * e)
                histories += count
                max_paid = max(max_paid, cost)
        for c, w, e, x in ((1, 4, -1, 1), (8, 7, -1, 5), (10, 9, 1, 3)):
            require(readings(c, w, 1, x, e, 6, 7, 11)[0] == 0, "sharp forbidden sign")
            require(equal(c, w, 1, x, -e, 6, 7, 11), "sharp permitted sign")
            require(((c + x) % 11, (w - e * pow(x, -1, 11)) % 11) == (2, 5),
                    "sharp inverse target")
        vertices, values = cycle_audit()
        rejected(lambda: seed(9, 3, 1, 1, -1, 6, 7, 11))
        rejected(lambda: claims_audit(vertices))
        rejected(lambda: Budget(records=0).charge(records=1))
        # At v=(9,3), separated existentials pass, but no same-sign branch
        # both agrees and remains in the terminal complement.
        branches = [(equal(9, 3, 1, 1, e, 6, 7, 11),
                     jvalue(10, 3 + e, 1, 11) != 0) for e in (-1, 1)]
        require(any(z for z, h in branches) and any(h for z, h in branches),
                "negative control premise")
        rejected(lambda: require(any(z and h for z, h in branches),
                                 "independent sign relaxation"))
        print(json.dumps({"incidences": incidences, "paid_seed_histories": histories,
                          "formula_regressions": formula_regressions,
                          "max_paid_seed_primitives": max_paid,
                          "cycle_paid_primitives": 50, "cycle_gcd": values,
                          "negative_controls": 4, "records": budget.records,
                          "edges": budget.edges}, sort_keys=True))
    finally:
        signal.alarm(0)


if __name__ == "__main__":
    main()
```

程序保留的有限数据是(106.17)、(106.24)、(106.25)及三重逆像证书；它不从工人意见或有限算术实例推导一般定理。原始矩阵执行在每一轮检查保留框架和初始标签，坐标拉回始终只发生在内存中。

### 106.10 精确的剩余传感器到纤维传播义务

对于非例外符号，定义该列禁止测试值

$$
\mathcal B_e(c,x)=\{-Ae c/(Bx^2),\ \delta-Ae(c-1)/(Bx^2)\}
$$

当 $Ae/x+Bx\delta\ne0$；若该差为零，令 $\mathcal B_e(c,x)=\varnothing$，因为两标量恒等。精确安全条件等价于每个 $c,x$ 的逐点包含

$$
K_c\subseteq
\bigl((K_{c+x}-1/x)\setminus\mathcal B_+(c,x)\bigr)
\ \cup\
\bigl((K_{c+x}+1/x)\setminus\mathcal B_-(c,x)\bigr).
\tag{106.26}
$$

两项各保留自己的符号，不能先合并边缘再选后继。106.4提供 $O(p)$ 个已经有相关分离证书的点，但总数并不保证某一列的获胜补集满足106.7或106.8，也不迫使任意 $K$ 与种子相交。由排除 $H_\delta\cup C_\delta$ 得到的总量上界仍允许稠密集合；106.1的逐纤维下界与106.6–106.7的形状排除也没有消除稠密、无周期、各列不规则的候选。105.8的终端补集满足放松后继条件，说明只反复改进这种放松条件不能替代传感器约束。

一个具体充分目标是：从(106.26)及两个候选的强制逆像，证明对每个非零 $\delta$，至少一列除已知残余 $B_0$ 外均有恰一读的有限分离证书，并使 $q(|B_0|-1)<n$，或满足逐大小的奇偶剪除条件。106.2才会完成剩余比较；这一目标不是成功策略的必要条件，目前也未证明。另一条结算路线须给出真正全相位的精确 $K$，再证明启动及固定实际来源的实现桥；单传感器周期不承担这个义务。种子、纤维关系、实际时间字与初始标签记忆在此只建立了这些有条件对应，尚未互相恢复到一般取得结论。持续的关系恢复目标及一般非零差层排除保持未证；本节没有新增 Lean/kernel 核验、原创性、全素数族取得或整体完成主张。

## 106.99 追加锚

## 107. 双候选种子的纤维上界、全长回返障碍与跨列分离

本节检验第106节留下的具体组合路线：先取得全部“一次混合门后终端”的证书，再靠只看终点的回返字放大到接近完整的一列。双候选传感器确实产生种子，但种子的每列含量受到统一常数约束；中间列不能由任何长度的预定回返字继续扩大。在模31的一个已允许实例，全部第二层都对这种终点规则封闭。与此同时，实际跨列门能越过这一闭包。因此这里排除的是一类证书传播方法，一般非零差层的精确安全集排除仍未解决。

### 107.1 同一符号的第二层与两个候选的三次式

沿用105.1、106.1，固定素数 $p>3$、奇数 $n=(p-1)/2$，要求

$$
\lambda^2-\lambda-1=0,\quad \operatorname{ord}(\lambda)=n,\quad
\mu=1-\lambda=-\lambda^{-1},\quad
A=\frac{3-2\mu}{\lambda-\mu},\quad B=\frac{2\lambda-3}{\lambda-\mu},\quad
\delta\ne0.
$$

$Q$ 为非零平方子群，$a=A/B$；105.1已给 $AB\ne0$、$a=\lambda^6\in Q$、$n\ge5$。记

$$
\begin{aligned}
L_e(v,x)&=Ae c/x+Bxw,& L'_e(v,x)&=Ae(c-1)/x+Bx(w-\delta),\\
\operatorname{Sep}_e(v,x)&\Longleftrightarrow [L_e(v,x)=0]\ne[L'_e(v,x)=0],&
h_e(x)&=(x,e/x),\\
J_\delta(c,w)&=(2c-1)w-c\delta,& H_\delta&=\{J_\delta=0\}.
\end{aligned}
\tag{107.1}
$$

精确安全仍是 $\forall v\in K\,\forall x\in Q\,\exists e$，同时有 $\neg\operatorname{Sep}_e(v,x)$ 和 $v+h_e(x)\in K$。候选对始终为 $((c,w),(c-1,w-\delta))$，两个存在符号不能各管一半义务。

**定义 107.1（完整的第二获胜层）。** 取104.21的 $W_0=\varnothing$。由106.3，$W_1=H_\delta$；置

$$
W_2=H_\delta\cup\{v:\exists x\in Q\ \forall e\in\{1,-1\},\quad
\operatorname{Sep}_e(v,x)\ \lor\ v+h_e(x)\in H_\delta\}.
\tag{107.2}
$$

这里的“完整”只针对式(107.2)的门族：一个终端门，或一个接枝门后接终端门。它不声称列举了任意 $R/G/T$ 协议的全部获胜态，也不声称最优成本。106.5已经给每点至多 $2n$ 个付费原语、至多一次 $G$、恰一次 $T$ 的实现。

**定理 107.2（双三次式是第二层的充要刻画）。** $v=(c,w)\notin H_\delta$ 属于 $W_2$，当且仅当存在 $x\in Q,e\in\{1,-1\}$，满足以下两族之一：

$$
\begin{aligned}
\text{第一族：}\quad&w=ae c/x^2,\quad c\ne0,\\
f_e(c,x)&=(2c+2x-1)(ac+x)-e\delta x^2(c+x)=0;\\[2mm]
\text{第二族：}\quad&w=\delta+ae(c-1)/x^2,\quad c\ne1,\\
g_e(c,x)&=(2c+2x-1)(a(c-1)+x)+e\delta x^2(c+x-1)=0.
\end{aligned}
\tag{107.3}
$$

两族均须保留过滤条件

$$
J_\delta(c,w)\ne0,\qquad e\delta x^2\ne a.
\tag{107.4}
$$

其中 $-e$ 为分离符号，$e$ 为读数相同且后继终端的符号。全部精确安全集避开 $W_2$。

证明。106.3给出 $H_\delta$ 恰是两个符号均能测试分离的终端区域；每列除 $c=1/2$ 外恰有一点，该中间列为空。两个接枝后继的第一坐标相同，第二坐标相差 $2/x\ne0$，因而不能同时在 $H_\delta$。所以 $v\notin H_\delta$ 满足(107.2)时，恰有一个分离符号 $-e$，另一个符号 $e$ 的后继在 $H_\delta$。

在 $-e$ 下，若第一候选读零，则 $w=ae c/x^2$；第二读数为 $Ae/x-Bx\delta$，非零恰给(107.4)的第二条件。$c=0$ 会使 $v=(0,0)\in H_\delta$，故排除。代入同一个 $e$ 的后继，有

$$
J_\delta(v+h_e(x))=\frac{e}{x^2}f_e(c,x).
\tag{107.5}
$$

若 $-e$ 下第二候选读零，则 $w=\delta+ae(c-1)/x^2$；第一读数为 $-Ae/x+Bx\delta$，同样给(107.4)，而 $c=1$ 会成为终端 $(1,\delta)$。代入后继得到 $J_\delta(v+h_e(x))=e g_e(c,x)/x^2$。这证明必要性，且两候选零位的所有可能都已覆盖。

反向看第一族，$-e$ 的零与非零已核对；符号 $e$ 的第一读数为 $2Ae c/x\ne0$，第二读数为 $Ae(2c-1)/x-Bx\delta$。后者乘 $cx/B$ 恰为 $x^2J_\delta(c,w)\ne0$，故两个零位相同。第二族在 $e$ 下的第二读数为 $2Ae(c-1)/x\ne0$；第一读数 $Ae(2c-1)/x+Bx\delta$ 乘 $(c-1)x/B$ 也等于 $x^2J_\delta(c,w)\ne0$。三次式分别保证同 $e$ 后继终端，于是两族都给(107.2)。轴点及共同零位的例外没有从定义域中删去，而是由这几个过滤条件处理。

安全集不能含终端点；在其余第二层点，$-e$ 已分离，$e$ 的后继又在终端集，故没有符号能同时履行安全合取。证毕。

式(107.3)中第二族的最后一项为正号；106.8的“第一候选在 $e$ 下读零”则使第二读数为 $-Ae/x-Bx\delta$。二者使用的零分支命名不同，不能把后一处的负号迁错到第二族。

### 107.2 每列十一点、轴列六点、中间列四点

**定理 107.3（实际第二层的逐纤维上界）。** 写 $(W_2)_c=\{w:(c,w)\in W_2\}$，则

$$
|(W_2)_c|\le11,\qquad |(W_2)_0|,|(W_2)_1|\le6,\qquad
|(W_2)_{1/2}|\le4.
\tag{107.6}
$$

证明只需 $p\equiv3\pmod4$ 为素数、$p>3$ 和 $AB\delta\ne0$，不需要 $a=\lambda^6$。

证明。先取 $c\notin\{0,1,1/2\}$。$f_e(c,X)$ 是三次式，首项系数 $-e\delta$，常数项 $ac(2c-1)\ne0$。若其三个不同根都在 $Q$，三根之积必须为平方；由韦达关系，该积是

$$
eac(2c-1)/\delta.
$$

两符号给相反乘积，$-1$ 非平方，故恰有一个乘积非平方；该符号最多有两个不同平方根，另一个最多三个。两符号合计至多五个 $(x,e)$。每个根只确定一个 $w$，过滤及输出重合只能减少点数。$g_e(c,X)$ 的首项系数为 $e\delta$，常数项为 $a(c-1)(2c-1)\ne0$，根积为 $-ea(c-1)(2c-1)/\delta$；同理第二族至多五点。再加一个终端点即得11。多项式的不同根数不超过次数，可由逐次除以 $X-r$ 得到，重根不多计。

在 $c=0$ 第一族不产生非终端点，第二族上述非零根积论证仍成立；在 $c=1$ 对称，故两轴列均至多 $5+1=6$。

中间列无需把两族分别计数。对第一族取 $(X,W)=(x,w)$；对第二族取 $(X,W)=(-x,\delta-w)$。由于 $c=1-c=1/2$，两种写法都满足

$$
W=\frac{ae}{2X^2},\qquad
f_e(1/2,X)=X\bigl[a+2X-e\delta X(X+1/2)\bigr]=0.
\tag{107.7}
$$

第一族的 $X$ 属 $Q$，第二族的 $X$ 属非平方，两类互不交叠且穷尽非零域元素。去掉不允许的根 $X=0$，方括号对每个 $e$ 是首项系数 $-e\delta\ne0$ 的二次式，所以总共至多四根、四个输出点。该列没有终端点，得到上界4。这里的反射换元仅是证明的双射，不授予物理取负、交换来源或免费改相位。证毕。

**推论 107.4（直接数值列完成条件不能由第二层供应）。** 对本族 $p\ge19$，若某列已认证的点全部来自 $W_2$，则106.7的严格大小条件不能成立；106.8在初始残余大小处的严格边数条件也不能成立。

证明。对任意零位移被排除的三步回返形状，其八个符号和组成对称非零集合 $D$。下面107.5证明 $|D|\ge6$，故 $q=|D|/2\in\{3,4\}$。记该列残余大小为 $m$。由(107.6)，$m\ge p-11$，从而

$$
q(m-1)\ge3(p-12)\ge (p-1)/2=n.
$$

又有 $\binom m2/\lceil m/2\rceil\ge m-2$：偶数 $m$ 时左边为 $m-1$，奇数时为 $m(m-1)/(m+1)$。因此

$$
\frac{q\binom m2}{\lceil m/2\rceil}\ge3(p-13)\ge n.
\tag{107.8}
$$

故106.8所要求的“所有剩余大小”已经在初始大小处失败。两次最后的不等式对 $p\ge19$ 成立。证毕。

这些仍只是对两项充分判据的供应限制。其他获胜证书加入后，前提“仅来自 $W_2$”失效；大小判据失败也不等于实际尺度图没有孤立点。特别不能把全局 $O(p)$ 个种子误读为某一列接近全满。

### 107.3 任意长度的预定回返字与中间列闭包

**定理 107.5（全长度的终点传播障碍）。** 令 $p>3$ 为素数、$-1$ 非平方，$Q$ 为非零平方。预定回返字是有限相位列 $x_1,\ldots,x_k\in Q$，满足 $\sum_i x_i=0$，在接收该字各符号之前就确定全部相位，并在每个相位执行 $G$。不使用中途传感器分离。其位移集合

$$
D(x_1,\ldots,x_k)=\left\{\sum_{i=1}^k e_i/x_i:e_i\in\{1,-1\}\right\}
\tag{107.9}
$$

或者含0，或者至少有六个元素。因此，对某列中至多五点的已认证集合 $C$，该列内尚未认证的点不能凭“所有该字终点均在 $C$”被加入。任意迭代这种终点规则仍得到 $C$；各字之间可以依全部已记录历史选择下一整字。

证明。先给所需的两点和集增长。若 $U\subsetneq\mathbb F_p$ 非空，$b\ne0$，则

$$
|(U+b)\cup(U-b)|\ge |U|+1.
$$

否则两个同样大小的平移集合必须相等，使 $U+2b=U$。素域中非零 $2b$ 生成整个加法群，于是非空 $U$ 为全域，矛盾。迭代给 $r$ 个自由非零带符号加数至少 $\min(p,r+1)$ 个和。这是 Cauchy–Davenport 的两元素特例；完整证明在此，不以未验证的文献假设补足。

空字有位移0；长度1不能回返，长度2要求 $x_2=-x_1$，与两者均平方矛盾。假设 $0\notin D$。$D=-D$，故其大小为偶数。$k\ge5$ 时增长界至少为6；$k=4$ 时至少为5，偶性使其至少为6。$k=3$ 时相位不能全部相等，否则 $3x_1=0$。选两个不同的倒数 $b_1,b_2\in Q$；因 $-1$ 非平方，它们也不互为负数，四个和 $\pm b_1\pm b_2$ 不同。加上第三个两点集合后至少有五点，偶性再次给六点。这覆盖全部长度。

从高度 $w\notin C$ 出发，若 $0\in D$，起点本身就是一个未认证终点；否则至少六个不同终点不能全部放进至多五点的 $C$。所以没有第一次新加入，归纳给任意次迭代。对手也可在每个已确定的整字后选择一个仍在补集的符号序列，再对下一字继续。此论证没有要求字间策略无记忆。证毕。

**推论 107.6（第二层中间列对所有预定回返字封闭）。** 在107.1的参数下，$C=(W_2)_{1/2}$ 的终点规则闭包恰为 $C$。对106.5的任意零位移被排除的形状与尺度，中间列残余上的尺度图每点至少保留两个邻点，故连精确的孤立点删除也不能开始。

证明。由107.3，$|C|\le4$，应用107.5。对三步尺度图，全部邻点为 $w+D/s$，有至少六个不同点且不含 $w$；删去至多四个认证点仍有至少两个。证毕。

这条负结论在每个接枝符号都可以由后续报告实现的切口成立。允许在字内根据符号更改后续相位、在中途用 $T$ 终止，或用跨列后继作认证，就不再满足(107.9)的独立符号和集前提。中间列补集也不是精确 $K$：一个非零 $x$ 的接枝立即离开该列。

### 107.4 模31完整第二层及真正正号启动的受限失败

**命题 107.7（一个完整第二层的全长停滞实例）。** 取

$$
p=31,\quad \lambda=19,\quad\mu=13,\quad A=22,\quad B=11,\quad a=2,\quad\delta=1.
\tag{107.10}
$$

此时 $|W_2|=64$，各列至多五点，且 $(W_2)_0=\{0,28\}$。所以全部 $W_2$ 对107.5的终点规则封闭，任意长度、任意次字间自适应迭代均不能开始扩充。

证明。$19^2-19-1=0$、$19^{15}=1$，而 $19^3=8$、$19^5=5$，所以准确阶为15，满足本族。下列列表按 $c=0,1,\ldots,30$ 给完整纤维；107.7后的有界程序分别由直接零位／同符号后继与两三次式重建整个集合，逐点相等。

$$
\begin{gathered}
\{0,28\},\{1,24\},\{11,29\},\{6,13,21\},\{5,9,11,14,26\},\{4,11,24\},\{9\},\\
\{14,21,22,25\},\{9,15\},\{6\},\{1,25\},\{2,26,30\},\{14\},\{3,4\},\\
\{12,19,24\},\{8,24,30\},\{5,18\},\{7,14,24\},\{19,20\},\{29\},\{18\},\\
\{30\},\{3,7\},\{8,26\},\{17\},\{2,10\},\{23\},\{28\},\{27\},\{6,15,19\},\{12,21\}.
\end{gathered}
\tag{107.11}
$$

列表共64点且最大列大小为5，应用107.5即可；不需枚举任意长度的字。为使启动论证不依赖整张列表，零列另有符号证明。$w\ne0$ 时第一候选在该列永不读零，只需第二族：

$$
\begin{aligned}
g_+(0,x)&=x^3+x^2-5x+2=(x-4)(x^2+5x+15),\\
g_-(0,x)&=-x^3+3x^2-5x+2=-(x-24)(x^2+21x+13).
\end{aligned}
\tag{107.12}
$$

两个二次因子的判别式为27、17，二者与24均非平方：各自15次幂为 $-1\pmod{31}$。唯一允许的根是 $x=4,e=+$，输出 $w=28$。该点在此相位的正号读数为 $(23,20)$，负号为 $(23,0)$，正号后继 $(4,5)$ 在 $H_1$。再加终端 $(0,0)$，得零列恰为两点。证毕。

**命题 107.8（固定正来源、首份正号下的同一受限障碍）。** 在既有 $H=341,E=M^{15},T=\gcd(2a+3b,341)$ 装置中，预先固定两个正整数来源

$$
s_A=(308,253),\qquad s_B=(121,253).
\tag{107.13}
$$

它们使“只用预定回返字进入零列 $W_2$ 证书”的受限策略失败，且不需要首份负号或更换来源。这不反驳一般 $R/G/T$ 取得。

证明。模341的坐标 $(a+81b,a+261b)$ 分别为 $(0,187),(154,0)$，模31即 $((0,1),(-1,0))$；模11原向量均为零。不可变初始标签分别为0、154，两初始 gcd 均为11，因为标量分别为1375、1001。候选是同一初始模型中的两个假设，控制器并未获赠实际坐标。

任意非空回返字至少有三次接枝。如果首个实际原语是 $G$，则其相位为1、符号固定正；剩下 $k-1$ 个自由符号由上述和集增长至少产生 $\min(31,k)\ge3$ 个不同终点。它们仍不能全部落入两点集 $\{0,28\}$。如果先用一个或多个 $R$ 消耗首份正号，则以后全部接枝符号均可自由实现，107.5适用。往后的每个回返切口也适用。因此从 $(0,1)$ 开始，每次已承诺的整字都有一个合法符号序列，使返回的高度仍不在 $\{0,28\}$。

实际执行沿用104.5的共同框架。若已执行 $r$ 个 $R$，累计隐藏批奇偶为 $b$，框架为

$$
\operatorname{diag}(\lambda^r,(-1)^b\mu^r)
 =\operatorname{diag}(1/x,e x),\qquad x=\lambda^{-r},\quad e=(-1)^{r+b}.
\tag{107.14}
$$

每个目标相位至多需要14个真实 $R$，再消耗一份 offer 执行 $G$；所有中间 offer 均由其 $R$ 消耗并记录。每个后来目标 offer 的批奇偶可令有效 $e$ 取所需符号，批次数0或1已经足够；更大的同奇偶有限批具有相同剩余作用。因此长 $k$ 字至多用 $15k$ 个付费原语。首份正号按前述两种情形处理，不曾跳过。

对每个已确定字选保持未认证终点的有限符号列，可逐字连接成合法日程。两条整数历史始终从(107.13)各自连续演化；模约化与 $M,E^k,+\alpha$ 交换，绝不重选剩余代表或在整数层取消 $E^2$。这些字只有静默 $R/G$，因而两执行有相同报告与完成信号，始终无法到达它所指定的终点认证库。未取得分离读数就停止，不能正确区分两个初始标签。

这里的失败只针对声明的库：它要求整字预定、没有中途 $T$，并以零列 $W_2$ 作为唯一分离入口。零列补集不是原游戏的精确安全集；其他列的更高获胜证书或传感器适应策略都被这个限制排除。第103节的实际模31正结果保留。证毕。

### 107.5 一个真正混合种子的惰性与有向前驱边界

**命题 107.9（任意单种子放大的反例）。** 在 $p=11,\lambda=4,\mu=8,A=6,B=7,\delta=1$ 下，置

$$
W=H_1\cup\{(3,9)\}.
$$

$(3,9)$ 是真正的非终端混合种子，但对于每个平方相位，把“两后继均在 $W$”的前驱加入的规则不能扩充 $W$。这不否定从完整 $W_2$ 进行联合传播。

证明。在 $(3,9),x=1$，正号两读数为 $(4,2)$，负号为 $(1,0)$；正号后继 $(4,10)$ 终端。精确算术是

$$
7\cdot10-4=66\equiv0,\qquad 5\cdot9-3=42\equiv9\pmod{11}.
$$

$H_1$ 除空列6外每列一点，$W$ 唯一的两点列是 $c=3$，高度为5、9。任意一对同相位后继若都在 $W$，只能是这两点；中点给前驱高度7，差给 $x=5$ 或6，其中仅5为平方。因此唯一前驱是 $(9,7)$，而

$$
17\cdot7-9=110\equiv0\pmod{11},
$$

已在 $H_1$。所以所有允许相位均不能加点。补集 $K_0=\mathbb F_{11}^2\setminus W$ 有110点，对每个点、每个相位均有一个后继仍在补集。逐步选择该后继证明任意有限自适应纯接枝策略树也不能强迫到达 $W$。

$K_0$ 绝非精确安全集。取 $(2,7),x=5$：正号读数为 $(1,0)$，已经分离，但后继 $(7,5)\in K_0$；负号读数为 $(5,2)$，虽相同，后继 $(7,9)\in H_1$。传感器安全符号是负号，后继安全符号是正号，其交集为空。这是不能拆分存在符号的直接证书。证毕。

**命题 107.10（混合种子的六原语固定来源实现）。** 上述种子由固定正来源 $(217,62),(62,62)$ 实现，初始标签为124、310。首个正号 offer 执行 $G$，然后四个 $R$ 和一个 $T$，共六个付费原语，在全部后续批奇偶下分离。

证明。模11初始坐标分别为 $(3,9),(2,8)$；两原向量模31均为零。首个 $G$ 后为 $(4,10),(3,9)$。四次旋转给 $4^4=3,8^4=4\pmod{11}$。全部后续反射与旋转交换，累计为 $\sigma\in\{1,-1\}$，末尾两标量为

$$
6+5\sigma,\qquad10+10\sigma.
$$

正号时为 $(0,9)$，负号时为 $(1,0)$，故 $T$ 总分离。每份 offer 均被一个实际原语消耗；任意有限隐藏批通过其奇偶实现同一剩余证明。两来源的模31相等关系受共同操作保持，模11整除位不同使完整 gcd 不同。实际整数来源保持连续，结论是局部双候选比较，不是每对标签均可到达该种子。证毕。

**命题 107.11（不能遗忘前驱的方向）。** 把合法的两后继推前驱规则改成无根三点集合的“任意两点补第三点”，会严格增加推理能力。

证明。模11相位5给有向叉

$$
(9,7)\longrightarrow (3,5),\ (3,9).
$$

前驱及第一个后继均在 $H_1$，另一个后继不在。无根规则会从前两点加入 $(3,9)$；合法规则只允许从两个后继推出前驱，而 $H_1$ 每列至多一点，根本没有两个合法同相位后继可作前提。故 $H_1$ 对合法规则封闭，无根规则却能扩大它。证毕。

Balogh–Bollobás–Morris–Riordan 的 *Linear algebra and bootstrap percolation*（[arXiv:1107.1410v2](https://arxiv.org/html/1107.1410v2)，定理1与引理3）讨论特定乘积超图和无根边的线性依赖。其无根补点操作没有实现为这里保留前驱的付费控制；命题107.11已给这种转移缺失的具体证据。这里没有加入新的物理操作或把文献的正向阈值当作本游戏的结论。

### 107.6 真正的跨列弦规则及其付费消费者

**定理 107.12（同列两证书给一个跨列前驱）。** 若同列两个不同点 $(C,u),(C,v)$ 已各有至多 $r$ 阶段、恰一次 $T$ 的分离证书，则存在唯一允许的平方相位 $x$，使前驱

$$
\left(C-x,\frac{u+v}{2}\right)
\tag{107.15}
$$

的两个接枝后继正好是这两点。该前驱有至多 $r+1$ 阶段、恰一次 $T$ 的证书。

证明。从 $x=2/(u-v)$ 及其负数中选平方者；$-1$ 非平方保证恰有一个。中点加减 $1/x$ 即为 $u,v$，故结论成立。对齐此相位后，对两个符号都可执行 $G$，再按实际后继使用其证书；也可在读数已分离时提前 $T$。同一份有效符号决定读数与后继，没有观察免费的当前坐标。每阶段至多 $n$ 个付费原语，证明所述上界。证毕。

**命题 107.13（模31跨列门越过全部第二层的回返闭包）。** 在(107.10)中，$(11,14)\notin W_2$，而相位20的两个后继为 $(0,28),(0,0)\in W_2$。它有至多三阶段、$3n=45$ 个付费原语、至多两个 $G$、恰一个 $T$ 的分离证书，且由固定正来源 $(253,77),(66,77)$、初始标签11与165实现。

证明。由(107.11)，第11列仅有 $\{2,26,30\}$，所以起点不在 $W_2$。$20^{-1}=14\pmod{31}$，两个后继立即给出。以下表中每对数字是同一符号下的两个候选标量，均模31：

| 门的状态与相位 | 正号读数及动作 | 负号读数及动作 |
| --- | --- | --- |
| $(11,14),x=20$ | $(20,19)$，$G$ 到 $(0,28)$ | $(2,28)$，$G$ 到 $(0,0)$ |
| $(0,28),x=4$ | $(23,20)$，$G$ 到 $(4,5)$ | $(23,0)$，$T$ |
| $(0,0),x=1$ | $(0,29)$，$T$ | $(0,11)$，$T$ |
| $(4,5),x=18$ | $(27,0)$，$T$ | $(0,3)$，$T$ |

这是包含全部分支的三阶段证书。目标相位20、4、1、18对应 $\lambda^{-j}$ 的指数13、3、0、1。初始先执行13个真实 $R$ 再作第一门；其正号分支再执行5个 $R$ 到第二门，继续正号时再执行13个 $R$ 到末门；第一门负号后执行2个 $R$ 即到相位1的终端门。各叶原语数为17、20或34，均不超过45。

所给来源的模31坐标为 $(11,14),(10,13)$，模11原向量均为零；模341初始标签为11、165。使用(107.14)保留所有旋转和批奇偶：物理标量乘单位 $e$ 恰为(107.1)读数，物理接枝拉回同一框架恰为 $h_e(x)$。对每次真实 $M,E^k,+\alpha$ 归纳，得到表格对任意有限批次的剩余实现；实际整数从各自原来源持续生成，不在门间复位。第一份正号由13个旋转中的第一个消耗，以后各门按报告选择表中分支。模11相等关系持续，故表中模31整除位不同保证完整 gcd 不同。

对未知实际来源，控制器初始化全部来源无关的候选槽，而不是把这两个坐标当作观测。每槽保存不可变 $c_0$，共同运输保存 $c=u c_0+t$、$u\ne0$；实际 $R$ 更新 $(u,t)$ 为 $(\lambda u,\lambda t)$，$G$ 更新为 $(u,t+1)$。报告、$T$ 不改该关系，另一素数分量也接受同一实际动作。末尾真实读数保留实际槽，并删除所选异标签槽中的至少一个。该局部比较越过了(107.2)及其全部终点回返闭包，却未供应每对标签的统一分离策略。证毕。

### 107.7 有界算术证书与尚缺的统一关系

下面的 Python 3 标准库程序重建107.2与107.3中的两个独立定义，在11、19、31及各自全部非零差值上核对终端等价、两族完整性和11／6／4上界。模31差值1的列表是用于反驳指定传播路线的单一证书。只枚举长度3、4的回返字作为可证伪核对；任意长度结论由107.5的证明承担。整数重放检查跨列政策的五个门分支，以及模11六原语字的全部后续奇偶；任意旋转间奇偶的普遍结论由共同框架归纳承担。

每次执行硬限120秒、100000条累计记录、1500000条有向检查，整数不超过8192位；不构造全341候选对乘积或安全集幂集。错误三次式符号、遗漏第二族、删除混合过滤、拆分安全符号、继承错误读数符号及更换固定来源都有会被拒绝的具体负控。核验异常、预算异常、时限异常为不同类型；预期负控只捕获核验异常，真实超时或超预算不能被当作负控成功。正文代码可直接保存执行，普通 Python 与 `python -O` 都使用同样的显式检查。正向读数为58组参数、75800条累计记录、1047438条有向检查、1800个短回返字、7个负控；模31第二层64点、最大列5，跨列五个整数叶的成本为17、17、20、34、34。有限算术证书不替代参数化证明，也不声称新的 Lean 核验。

```python
import json
import math
import signal
import time
from itertools import product


class CheckFailure(RuntimeError):
    pass


class BudgetExceeded(RuntimeError):
    pass


class DeadlineExceeded(RuntimeError):
    pass


def require(ok, message):
    if not ok:
        raise CheckFailure(message)


start = time.monotonic()
records = edges = 0


def charge(r=0, e=0):
    global records, edges
    records += r
    edges += e
    if records > 100000 or edges > 1500000:
        raise BudgetExceeded((records, edges))
    if time.monotonic() - start >= 120:
        raise DeadlineExceeded('120 seconds')


def timeout(*unused):
    raise DeadlineExceeded('120 seconds')


signal.signal(signal.SIGALRM, timeout)
signal.alarm(120)


def rejected(f):
    try:
        f()
    except CheckFailure:
        return
    raise CheckFailure('negative control accepted')


def jvalue(c, w, d, p):
    return ((2*c-1)*w-c*d) % p


def readings(c, w, d, x, e, A, B, p):
    xi = pow(x, -1, p)
    return ((A*e*c*xi+B*x*w) % p,
            (A*e*(c-1)*xi+B*x*(w-d)) % p)


def sep(c, w, d, x, e, A, B, p):
    u, v = readings(c, w, d, x, e, A, B, p)
    return (u == 0) != (v == 0)


def successor(c, w, x, e, p):
    return ((c+x) % p, (w+e*pow(x, -1, p)) % p)


def roots(p, A, B, d, Q, H, mode='correct'):
    a = A*pow(B, -1, p) % p
    W = set(H)
    for c in range(p):
        for x in Q:
            for e in (-1, 1):
                charge(r=1)
                xx = x*x
                w1 = a*e*c*pow(xx, -1, p) % p
                w2 = (d+a*e*(c-1)*pow(xx, -1, p)) % p
                f = (2*c+2*x-1)*(a*c+x)-e*d*xx*(c+x)
                sign = -1 if mode == 'wrong-second-sign' else 1
                g = (2*c+2*x-1)*(a*(c-1)+x)+sign*e*d*xx*(c+x-1)
                for which, w, polynomial, axis in ((1,w1,f,c != 0),
                                                   (2,w2,g,c != 1)):
                    if mode == 'first-only' and which == 2:
                        continue
                    if polynomial % p == 0 and (mode == 'no-filters' or
                            (axis and jvalue(c,w,d,p) != 0 and (e*d*xx-a) % p != 0)):
                        W.add((c,w))
    return W


saved = {}
parameter_count = 0
for p, lam in ((11,4), (19,5), (31,19)):
    n = (p-1)//2
    mu = (1-lam) % p
    den = pow((lam-mu) % p,-1,p)
    A, B = (3-2*mu)*den % p, (2*lam-3)*den % p
    Q = sorted({t*t % p for t in range(1,p)})
    require(n % 2 == 1 and (lam*lam-lam-1) % p == 0, 'family')
    require(next(k for k in range(1,p) if pow(lam,k,p)==1)==n, 'exact order')
    require(A*B % p != 0 and (A+B) % p == 2, 'sensor coefficients')
    for d in range(1,p):
        H = {(c,d*c*pow((2*c-1)%p,-1,p)%p)
             for c in range(p) if (2*c-1)%p}
        W = set(H)
        for c in range(p):
            for w in range(p):
                charge(r=1)
                terminal = mixed = False
                for x in Q:
                    outcomes = []
                    for e in (-1,1):
                        charge(e=1)
                        outcomes.append((sep(c,w,d,x,e,A,B,p),
                                         successor(c,w,x,e,p) in H))
                    terminal |= all(s for s,t in outcomes)
                    mixed |= all(s or t for s,t in outcomes)
                    require(not all(t for s,t in outcomes), 'two terminal successors')
                require(terminal == ((c,w) in H), 'terminal characterization')
                if mixed:
                    W.add((c,w))
        require(W == roots(p,A,B,d,Q,H), 'two cubic families equal direct gates')
        fibers = [{w for cc,w in W if cc==c} for c in range(p)]
        require(max(map(len,fibers)) <= 11, 'fiber 11')
        require(len(fibers[0]) <= 6 and len(fibers[1]) <= 6, 'axes 6')
        require(len(fibers[pow(2,-1,p)]) <= 4, 'middle 4')
        if p>=19:
            for F in fibers:
                m = p-len(F)
                for q in (3,4):
                    require(q*(m-1)>=n, 'first threshold fails')
                    require(q*m*(m-1)//2>=n*((m+1)//2), 'edge threshold fails')
        parameter_count += 1
        if d==1 and p in (11,31):
            saved[p]=(A,B,Q,H,W,fibers)

A,B,Q,H,W,fibers = saved[31]
table = [[0,28],[1,24],[11,29],[6,13,21],[5,9,11,14,26],[4,11,24],
         [9],[14,21,22,25],[9,15],[6],[1,25],[2,26,30],[14],[3,4],
         [12,19,24],[8,24,30],[5,18],[7,14,24],[19,20],[29],[18],[30],
         [3,7],[8,26],[17],[2,10],[23],[28],[27],[6,15,19],[12,21]]
require(fibers == list(map(set,table)) and len(W)==64, 'complete p31 certificate')
require(max(map(len,fibers))==5 and fibers[0]=={0,28}, 'p31 columns')
for x in range(31):
    charge(r=1)
    require((x**3+x*x-5*x+2-(x-4)*(x*x+5*x+15))%31==0, 'positive cubic factor')
    require((-x**3+3*x*x-5*x+2+(x-24)*(x*x+21*x+13))%31==0, 'negative cubic factor')
require(all(pow(z,15,31)==30 for z in (27,17,24)), 'nonsquare exclusions')
for mode in ('wrong-second-sign','first-only'):
    mutant = roots(31,A,B,1,Q,H,mode)
    rejected(lambda mutant=mutant: require(mutant==W, 'source-sensitive cubic mutation'))

# Removing the filters admits a terminal point as a purported mixed certificate.
require((2*0+2*1-1)*(2*0+1)-1*(0+1)==0, 'unfiltered cubic root')
rejected(lambda: require(jvalue(0,0,1,31)!=0, 'unfiltered mixed certificate'))

# Exhaust short return words only as falsifiers; the all-length proof is in the text.
word_count = 0
for k in (3,4):
    for prefix in product(Q,repeat=k-1):
        last = -sum(prefix)%31
        if last not in Q:
            continue
        charge(r=1)
        word = prefix+(last,)
        D={0}
        for x in word:
            xi=pow(x,-1,31)
            charge(e=2*len(D))
            D={(z+e*xi)%31 for z in D for e in (-1,1)}
        require(0 in D or len(D)>=6, 'return support')
        if word[0]==1:
            F={1}
            for x in word[1:]:
                xi=pow(x,-1,31)
                charge(e=2*len(F))
                F={(z+e*xi)%31 for z in F for e in (-1,1)}
            require(len(F)>=3, 'positive startup support')
        word_count += 1

A11,B11,Q11,H11,W11,_=saved[11]
inert=H11|{(3,9)}
require((3,9) in W11-H11 and len(inert)==11, 'mixed inert seed')
new=set()
for c,w in product(range(11),repeat=2):
    charge(r=1)
    for x in Q11:
        charge(e=2)
        if all(successor(c,w,x,e,11) in inert for e in (-1,1)):
            new.add((c,w))
require(new=={(9,7)} and new<=H11, 'all directed predecessor rules')
require((7*10-4)%11==0 and (5*9-3)%11==9 and (17*7-9)%11==0,
        'explicit multiplication')
K={(c,w) for c,w in product(range(11),repeat=2)}-inert
sensor_safe={e for e in (-1,1) if not sep(2,7,1,5,e,6,7,11)}
successor_safe={e for e in (-1,1) if successor(2,7,5,e,11) in K}
require(sensor_safe=={-1} and successor_safe=={1}, 'split signs counterexample')
rejected(lambda: require(bool(sensor_safe & successor_safe), 'false exact K'))
require((9,7) in H11 and (3,5) in H11 and (3,9) not in H11, 'directed fork')
require(successor(9,7,5,1,11)==(3,5) and successor(9,7,5,-1,11)==(3,9),
        'fork orientation')

# Corrected 106 sign: the zero-sign second reading is -A*e/x-B*x*d.
for d,c,w,x,e in ((1,1,10,9,1),(4,3,1,1,-1)):
    u,v=readings(c,w,d,x,e,6,7,11)
    require(u==0 and v==(-6*e*pow(x,-1,11)-7*x*d)%11, 'corrected 106 sign')
    rejected(lambda v=v,x=x,e=e,d=d: require(v==(6*e*pow(x,-1,11)-7*x*d)%11,
                                           'wrong inherited sign'))

A,B,Q,H,W,fibers=saved[31]
require((11,14) not in W, 'cross-column predecessor outside W2')
require({successor(11,14,20,e,31) for e in (-1,1)}=={(0,0),(0,28)}, 'chord')
gates=[((11,14),20,((20,19),(2,28))),
       ((0,28),4,((23,20),(23,0))),
       ((0,0),1,((0,29),(0,11))),
       ((4,5),18,((27,0),(0,3)))]
for (c,w),x,expected in gates:
    require(tuple(readings(c,w,1,x,e,22,11,31) for e in (1,-1))==expected,
            'paid branch table')


def rotate(v):
    a,b=v
    return b,a+b


def reflect(v):
    a,b=v
    return 377*a+610*b,610*a+987*b


def coord(v,p):
    a,b=v
    return ((a+81*b)%p,(a+261*b)%p)


for sources, expected, labels, passive in (
    (((308,253),(121,253)),((0,1),(30,0)),(0,154),11),
    (((253,77),(66,77)),((11,14),(10,13)),(11,165),11),
    (((217,62),(62,62)),((3,9),(2,8)),(124,310),31)):
    p=341//passive
    require(tuple(coord(s,p) for s in sources)==expected, 'fixed sources')
    require(tuple(coord(s,341)[0] for s in sources)==labels, 'immutable labels')
    require(all(all(t%passive==0 for t in s) for s in sources), 'passive equality')
require(tuple(math.gcd(2*a+3*b,341) for a,b in ((308,253),(121,253)))==(11,11),
        'startup reads')
rejected(lambda: require(coord((67,77),31)==(10,13), 'source mutation'))

# Five leaves for the cross-column policy; actual matrices, no modular resets.
leaf_words=[((20,-1,'G'),(1,e,'T')) for e in (-1,1)]
leaf_words += [((20,1,'G'),(4,-1,'T'))]
leaf_words += [((20,1,'G'),(4,1,'G'),(18,e,'T')) for e in (-1,1)]
paid=[]
for word in leaf_words:
    actual=((253,77),(66,77)); c,w=11,14
    j=b=cost=ng=nt=0
    u,t=1,0
    for x,e,action in word:
        goal=next(k for k in range(15) if pow(19,-k,31)==x)
        rotations=(goal-j)%15
        for unused in range(rotations):
            charge(r=1,e=2)
            actual=tuple(rotate(v) for v in actual)
            j+=1;cost+=1;u,t=19*u%31,19*t%31
        k=0 if (-1)**(j+b)==e else 1
        require(cost>0 or k==0, 'positive initial offer')
        if k:
            actual=tuple(reflect(v) for v in actual)
        b+=k;cost+=1
        for i,v in enumerate(actual):
            charge(r=1,e=1)
            require(max(ti.bit_length() for ti in v)<=8192, 'integer size')
            base=((c,w),((c-1)%31,(w-1)%31))[i]
            require(coord(v,31)==(pow(19,j,31)*base[0]%31,
                    (-1)**b*pow(13,j,31)*base[1]%31), 'physical frame')
            require(coord(v,31)[0]==(u*(11,10)[i]+t)%31, 'initial label transport')
        physical=tuple((2*a+3*b0)%31==0 for a,b0 in actual)
        require(physical==tuple(z==0 for z in readings(c,w,1,x,e,22,11,31)),
                'sensor and sign bridge')
        if action=='G':
            require(physical[0]==physical[1], 'nonseparating continuation')
            actual=tuple((a+1,b0) for a,b0 in actual)
            c,w=successor(c,w,x,e,31)
            t=(t+1)%31;ng+=1
        else:
            nt+=1
            require(physical[0]!=physical[1], 'T separates')
            gcds=tuple(math.gcd(2*a+3*b0,341) for a,b0 in actual)
            require(gcds[0]!=gcds[1], 'full gcd separation')
    require(cost<=45 and ng<=2 and nt==1, 'three paid stages')
    paid.append({'cost':cost,'gcds':gcds})

# The six-primitive modulo-11 witness covers every later parity schedule.
for schedule in product((0,1),repeat=5):
    actual=tuple((a+1,b) for a,b in ((217,62),(62,62)))
    for i,k in enumerate(schedule):
        charge(r=1,e=2)
        if k:
            actual=tuple(reflect(v) for v in actual)
        if i<4:
            actual=tuple(rotate(v) for v in actual)
    gcds=tuple(math.gcd(2*a+3*b,341) for a,b in actual)
    require(gcds[0]!=gcds[1], 'six paid primitives all parities')

charge()
signal.alarm(0)
print(json.dumps({'parameter_sets':parameter_count,'p31_W2':64,'p31_max_fiber':5,
    'p31_zero_fiber':[0,28], 'short_return_words':word_count,
    'p11_inert_predecessors':sorted(new),'paid_cross_column_leaves':paid,
    'negative_controls':7,'records':records,'edges':edges,
    'seconds':round(time.monotonic()-start,6)},sort_keys=True))
```

本节的逐列上界、两族精确刻画、指定传播库的反例及付费跨列连接，是在既有参数与104—106节结果上作的仓内综合推导（`repo-derived`），没有经过文献优先权的穷尽核查。已知加法工具只作为107.5证明中的中间步骤：Alon 的 [*Combinatorial Nullstellensatz*，定理3.2](https://www.math.tau.ac.il/~nogaa/PDFS/null2.pdf) 给素阶循环群的 Cauchy–Davenport 界；这里取第二加数集合为两个不同元素 $\{1/x,-1/x\}$，假设逐项成立。若允许中途传感器剔除符号分支或按符号改变相位，终点集合不再是同一个笛卡尔符号和集，不能继续借用这个下界。

McDonald–Sahay–Wyman 的 [*The VC dimension of quadratic residues in finite fields*，引理2.1](https://arxiv.org/html/2210.03789v2) 的特征和界要求被求和多项式不是相应幂；其全域计数不提供指定竖直列的覆盖量。第106节的总种子估计保留其完整条件，本节的纤维上界不依赖那个估计。Van den Bos–Vaandrager 的 [*State Identification for Labeled Transition Systems with Inputs and Outputs*，定义16、引理11与定理6.1](https://arxiv.org/html/1907.11034v2) 要求不同状态不相容及保持相容关系的 injective splits；已知物理历史的可逆性不自动供应全部候选对不相容。丢弃相位的候选依赖强制映射也不是一个固定物理输入。上述文献关系没有填补尚缺的算术前提。

真正剩余的命题是：在每个满足107.1的参数和非零差层中，利用两个候选的相关传感器、合法后继及所保留相位，统一产生足够的更高层证书，或者给出非空精确安全集及其合法启动、固定来源实现。到某列满足106.7／106.8只是仍有效的充分路线，不是所有取得协议的必要形式。这里已经排除了把“完整第二层加任意预定终点回返字”当作全族统一供应方案的办法，并用107.13展示了真实跨列关系能增加它无法增加的点；尚未证明该增加统一持续到全域。

第103节现有的341装置11／31全标签取得结果保留；模19及一般素数的计算和定理属于抽象域，实际取得须另给反射与传感器接口。相位在动作之前报告、每份 offer 只保护一个原语、付费不扰动测试、请求完成及固定来源，均是明确合同条件，不是本节证明出来的免费能力。所保存的是初始标签与当前坐标之间的单位仿射历史，没有恢复全部整数构成或原始有序树，也没有得到物理统一、最优记忆、一般素数族取得或持续研究目标完成的结论。

## 107.99 追加锚
## 108. 实际证书的代数包络、伴随圆锥曲线与中心的字符判据

本节接续107.2的双候选精确第二层，保留107.3的逐列十一点、轴列六点和中间列四点上界。先限制再增加一个实际门所能供应的普通列，再在差值 $\delta=\pm4$ 上求出伴随曲线与第二层的精确交集。后一个交集同时给出中心的第三层充要条件和付费比较；它只供应有限个指定点，尚未供应一般非零差层的稠密列。

### 108.1 同符号门与第二层的非竖直代数包络

**定义 108.1（参数、实际第三层与统一坐标）。** 全节固定107.1的参数：$p>3$ 为素数，$n=(p-1)/2$ 为奇数，

$$
\lambda^2-\lambda-1=0,\qquad \operatorname{ord}(\lambda)=n,\qquad
\mu=1-\lambda=-\lambda^{-1},\qquad
A=\frac{3-2\mu}{\lambda-\mu},\quad B=\frac{2\lambda-3}{\lambda-\mu},\quad \delta\ne0.
$$

由105.1，$AB\ne0$、$A+B=2$、$a=A/B=\lambda^6$，且 $Q=\langle\lambda\rangle$ 恰为非零平方子群，$n\ge5$。二次特征记作 $\chi$，有 $\chi(-1)=-1$。候选对为 $((c,w),(c-1,w-\delta))$；在同一相位 $x\in Q$ 和同一符号 $e\in\{1,-1\}$ 下，仍用

$$
L_e=Ae c/x+Bxw,\qquad L'_e=Ae(c-1)/x+Bx(w-\delta),\qquad
h_e(x)=(x,e/x),\qquad
\operatorname{Sep}_e\Longleftrightarrow[L_e=0]\ne[L'_e=0].
\tag{108.1}
$$

记 $J(c,w)=(2c-1)w-c\delta$、$H=\{J=0\}=W_1$，$W_2$ 沿用107.1，定义

$$
W_3=W_2\cup\{v:\exists x\in Q\ \forall e\in\{1,-1\},\quad
\operatorname{Sep}_e(v,x)\ \lor\ v+h_e(x)\in W_2\}.
\tag{108.2}
$$

这些是保留两个符号的阶段证书，不是任意物理协议的最小步数分层。后文仅使用一次中心化 $U=2c-1,V=2w-\delta$；于是 $2J=UV-\delta$、$H$ 为 $UV=\delta$，同符号接枝加上 $(2x,2e/x)$。精确安全集 $K$ 的条件始终是：每个 $v\in K$、每个 $x\in Q$，存在同一个 $e$ 使 $\neg\operatorname{Sep}_e(v,x)$ 且 $v+h_e(x)\in K$。

**定理 108.2（实际第二层的双十三次包络）。** 在多项式变量 $C,W$ 中置

$$
\begin{aligned}
J&=(2C-1)W-C\delta,\\
K_0&=(2C-1)W+aC(2W-\delta),\\
F_e(C,W)&=K_0^2-aeCW(J+2e)^2,\\
F(C,W)&=J\prod_{e\in\{1,-1\}}F_e(C,W)F_e(1-C,\delta-W).
\end{aligned}
\tag{108.3}
$$

则 $W_2\subseteq\{F=0\}$。$F$ 的双次数为 $(13,13)$，关于 $W$ 的首项系数为

$$
b_F(C)=a^4C^2(1-C)^2(2C-1)^9.
\tag{108.4}
$$

在代数闭包上，$F$ 没有竖直因子，即不存在 $C_0$ 使 $F(C_0,W)$ 恒为零。这里不主张逆包含。

证明。终端部分由因子 $J$ 覆盖。107.2的第一混合族满足 $Wx^2=aeC$，同 $e$ 后继终端的方程乘以 $x$ 为

$$
(2W-\delta)x^2+(J+2e)x+e(2C-1)=0.
$$

再乘 $W$，代入 $Wx^2=aeC$，得 $W(J+2e)x+eK_0=0$。平方后得 $F_e=0$；没有除以 $W$，所以 $W=0$ 的退化也在论证内。第二混合族作证明换元 $(C,W,x)\mapsto(1-C,\delta-W,-x)$ 得到镜像因子；这不授予控制者取负相位的动作。实际平方相位和107.4的分离过滤仍只决定哪些零点属于 $W_2$。

每个 $F_e$ 在两个变量上的次数均至多三。其 $W^3$ 系数为 $-aeC(2C-1)^2$，镜像因子的 $W^3$ 系数为 $ae(1-C)(2C-1)^2$。乘上 $J$ 的首项即得(108.4)，它非零；同样按 $C$ 展开所得首项系数为 $a^4W^2(\delta-W)^2(2W-\delta)^9$，也非零，故双次数恰为 $(13,13)$。

若 $C_0\ne0$，则 $F_e(C_0,0)=a^2C_0^2\delta^2\ne0$；若 $C_0=0$，则 $F_e(0,W)=W^2$，仍非零。镜像因子有相同性质。$J(C_0,W)$ 在 $C_0\ne1/2$ 时有非零一次项，在 $C_0=1/2$ 时为非零常数 $-\delta/2$。域上的多项式环无零因子，故这些因子的乘积在任何固定列都非零。证毕。

### 108.2 倒数平移结式与再一层的逐列限制

**定理 108.3（同列双后继的倒数平移界）。** 设 $f(C,W)$ 的 $C$ 次数至多 $d$、$W$ 次数为 $m\ge1$，在代数闭包上没有竖直因子，且 $W$ 首项系数 $b_f(C)$ 满足 $b_f(h)\ne0$。则满足

$$
\exists x\ne0:\quad f(h+x,w+1/x)=f(h+x,w-1/x)=0
\tag{108.5}
$$

的不同 $w$ 至多有 $2m(d+m)$ 个。加上 $x\in Q$ 或实际传感器过滤不会增大此数。

证明。把 $C$ 当作不定元，在 $\overline{\mathbb F_p(C)}$ 中写 $f=b_f\prod_{i=1}^m(W-r_i)$，根按重数计。由结式的根乘积公式，

$$
R(C,Z)=\operatorname{Res}_W(f(C,W),f(C,W-Z))
=b_f(C)^{2m}\prod_{i,j}(r_i-r_j-Z).
\tag{108.6}
$$

因此 $R$ 的 $Z$ 次数恰为 $m^2$，首项系数为 $(-1)^{m^2}b_f(C)^{2m}$。其余系数仍是 $C$ 的多项式；故

$$
\left.(C-h)^{m^2}R\left(C,\frac2{C-h}\right)\right|_{C=h}
=(-2)^{m^2}b_f(h)^{2m}\ne0.
\tag{108.7}
$$

这证明 $f(C,W)$ 与 $f(C,W-2/(C-h))$ 在 $\mathbb F_p(C)[W]$ 上互素，特别没有共同的非竖直分量。没有竖直因子的假设另外排除了固定 $C\ne h$ 的共同分量，不能从(108.7)省去这一条件。

令

$$
P_\pm(X,Y)=X^m f(h+X,Y\pm1/X).
$$

它们是普通多项式，$X$ 次数至多 $d+m$、$Y$ 次数至多 $m$，且 $P_\pm(0,Y)=(\pm1)^m b_f(h)\ne0$。故清分母没有留下 $X=0$ 分量。对 $X\ne0$ 用可逆换元 $C=h+X,W=Y+1/X$，上一段排除了其余共同分量，因而 $P_+,P_-$ 互素。于是 $E_h(Y)=\operatorname{Res}_X(P_+,P_-)$ 非零。其 Sylvester 行列式至多有 $2(d+m)$ 行，每项的 $Y$ 次数至多 $m$，故 $\deg E_h\le2m(d+m)$。式(108.5)的每个 $w$ 都使两式有公共 $X$ 根，从而 $E_h(w)=0$；非零一元多项式的不同根数不超过次数。证毕。

这个论证允许奇点和重根，不假设曲线光滑。若两个有理图分量 $W=r(C),W=t(C)$ 在上述倒数平移下有共同分量，所要求的恒等式为 $r(C)-t(C)=2/(C-h)$（或交换两图），并非普通割线关联；即使有此恒等式，仍须证明两个端点的实际证书域、$C-h\in Q$，以及中点 $(r+t)/2$ 的不同值范围。关系恒等式本身不供应这些条件。

**定理 108.4（实际第三层的普通列至多八百四十五点）。** 对所有 $h\notin\{0,1,1/2\}$，

$$
|(W_3)_h|\le845.
\tag{108.8}
$$

证明。两个符号的接枝后继均在 $W_2$ 的前驱，由108.2—108.3以 $d=m=13$ 得至多 $2\cdot13\cdot26=676$ 点。其余新门若两个符号均分离，已在 $H$；否则记 $-e$ 为分离符号，$e$ 为继续到 $W_2$ 的符号。第一候选在 $-e$ 读零给 $w=aeh/x^2$，所以实际门必满足

$$
x^{26}F(h+x,aeh/x^2+e/x)=0.
\tag{108.9}
$$

左边是次数至多 $39$ 的 $x$ 多项式，其常数项为 $b_F(h)(aeh)^{13}\ne0$，故至多有39个相位，每相位至多给一个 $w$。第二候选读零给 $w=\delta+ae(h-1)/x^2$，相应多项式为

$$
x^{26}F(h+x,\delta+ae(h-1)/x^2+e/x),
$$

次数同样至多39，常数项为 $b_F(h)(ae(h-1))^{13}\ne0$。两个候选、两个符号共至多156点。107.3已有 $|(W_2)_h|\le11\le13$；采用共同的粗界相加得 $13+676+156=845$。域外根、非平方相位及失败的分离过滤只会使此上界变松，不会生成实际证书。三列 $0,1,1/2$ 的首项或常数项消失，本结论没有覆盖它们。证毕。

**推论 108.5（早层严格数值消费者的适用边界）。** 若 $p\ge1015$、$h\notin\{0,1,1/2\}$，令 $B_h=\mathbb F_p\setminus(W_3)_h$，则106.7中零位移被排除的三步回返所用的 $q=|D|/2$ 满足

$$
q(|B_h|-1)\ge3(p-846)\ge(p-1)/2=n.
\tag{108.10}
$$

因此仅由 $W_2$ 再增加一个实际阶段，不能在这些列供应该消费者要求的严格不等式 $q(|B_h|-1)<n$。

证明。107.5已给这类回返的非零对称位移集至少六点，故 $q\ge3$；108.4给 $|B_h|\ge p-845$，代入即得(108.10)。这里限制的是指定早层、指定数值充分判据；不限制三条例外列，不限制更高层，也不把该判据变成取得协议的必要条件。尤其没有推出非空精确安全集、后来不能取得或 $p<1015$ 是取得的必要条件。证毕。

### 108.3 同一伴随扇区的闭包与实际传感器出口

**定理 108.6（伴随扇区的多对同心与非安全补集）。** 取 $s\in\{1,-1\}$、$\delta=4s$，置

$$
O_s=(1/2,2s),\qquad
v_s(u)=\left(\frac{u+1}{2},2s-\frac{2s}{u}\right),\qquad
T_s=\{v_s(u):u\in2Q\},\qquad Z_s=H\cup T_s\cup\{O_s\}.
\tag{108.11}
$$

其中 $2Q=\{2x:x\in Q\}$。$Z_s$ 有 $3n+1$ 个点，对107.12的有向双后继规则封闭；$H\cup T_s$ 的该规则闭包恰增加 $O_s$。但是 $W_2\not\subseteq Z_s$，其补集不是精确安全集。

证明。中心坐标下 $T_s$ 是 $UV=-\delta,U\in2Q$，与 $H:UV=\delta$ 不交；$O_s$ 是 $(U,V)=(0,0)$，也不在两曲线上。故点数为 $2n+n+1$。每个 $U=u\in2Q$ 的列恰有两个点，其原 $w$ 值为 $2s+2s/u$ 与 $2s-2s/u$；其余非中心列仅有终端点，中心列只有 $O_s$。

两个不同同列值 $w_1,w_2$ 的合法相位是 $\{2/(w_1-w_2),-2/(w_1-w_2)\}$ 中唯一的平方：$-1$ 非平方保证唯一。前驱是 $(c-x,(w_1+w_2)/2)$，方向不能逆转。上述双点列的合法相位恰为 $x=u/2$，前驱恰为 $O_s$，其中符号 $s$ 的后继在 $H$，符号 $-s$ 的后继在 $T_s$。所有 $n$ 个不同列对都产生同一前驱；新增中心点又不产生新的同列双点。因此闭包和封闭性均成立。特别是相位对的数目不能当作不同新前驱的数目。

下面给出实际 $W_2$ 在 $Z_s$ 外的点。写 $\eta=-s$、$t=\lambda^3$；则 $a=t^2$、$t^2=4t+1$，$\delta=-4\eta$。若 $\chi(2)=-1$，取 $x=-t/2\in Q,e=\eta$。若 $\chi(2)=1$，取 $r^2=2$，二次式 $4y^2-4y-1=0$ 的两个根 $(1\pm r)/2$ 之积为 $-1/4$，故恰有一个平方根值 $y\in Q$；取这个 $y$ 并置 $x=ty\in Q,e=-\eta$。两种情形都满足

$$
4\eta e x^2+4tx+t^2=0,\qquad
\delta=e\frac{(a-1)x+a}{x^2}.
\tag{108.12}
$$

令 $v=(-x,-e/x)$。在相位 $x$、符号 $-e$ 下，两读数依次是 $(A-B)e\ne0$ 和零。在符号 $e$ 下，两读数为 $-(A+B)e=-2e\ne0$ 与 $-2Ae(1+1/x)\ne0$；这里 $x\ne-1$，因为 $x$ 平方而 $-1$ 非平方。同一个 $e$ 的接枝后继是 $(0,0)\in H$，所以 $v\in W_2$。

同时，

$$
J(v)=e(a+1)(x+1)/x\ne0.
$$

$a+1\ne0$ 因为 $a$ 平方；又 $x+1\ne0$，故 $v\notin H$。它也不在中心列：若 $x=-1/2$，(108.12)左边变成 $\eta e+2t+1$，在 $\eta e=1$ 时为 $2(t+1)\ne0$，在 $\eta e=-1$ 时为 $2t\ne0$。

若 $v$ 在整条伴随曲线上，则 $J(v)=-\delta$，从而

$$
F_0=(a+1)x^2+2ax+a=0.
\tag{108.13}
$$

在第一种情形 $x=-t/2$，用 $t^2=4t+1$ 化简得 $F_0=3t^2/2\ne0$。在第二种情形 $x=ty$、$4y^2-4y-1=0$，有

$$
2F_0/t^2=4(3t+1)y+(2t+3).
$$

$3t+1\ne0$，否则代入 $t^2-4t-1$ 得 $4/9\ne0$。若 $F_0=0$，代入 $y=-(2t+3)/(4(3t+1))$，二次式的值为 $9/[4(3t+1)^2]\ne0$，矛盾。因此 $v$ 连整条伴随曲线也不属于，故 $v\notin Z_s$。

补集虽因双后继封闭而满足仅看后继的生存条件，却在这个 $v,x$ 上违反完整合取：符号 $-e$ 立即分离，符号 $e$ 的后继落入 $H\subset Z_s$。没有一个符号同时保持读数相容和补集后继。故该补集不是精确 $K$；上述几何闭包也没有宣称整个 $T_s$ 已有实际证书。证毕。

**定理 108.7（特殊差层的整个第二层中间纤维为空）。** 当 $\delta=4s$ 时，$(W_2)_{1/2}=\varnothing$。

证明。107.7把第一混合族写作 $(X,W)=(x,w)$，第二混合族写作 $(X,W)=(-x,\delta-w)$；两类 $X$ 分别为平方和非平方，且共同满足

$$
W=ae/(2X^2),\qquad a+2X-e\delta X(X+1/2)=0,
\qquad e\delta X^2\ne a.
\tag{108.14}
$$

若 $e=s$，二次式成为 $a-4X^2=0$，恰与最后一个分离过滤矛盾：两个读数同时为零，不能计为分离。若 $e=-s$，二次式为 $4X^2+4X+a=0$，其判别式为 $16(1-a)=-64\lambda^3$，是非平方，故无根。两候选、两个符号均已覆盖，而 $H$ 本来没有中间列点。证毕。

### 108.4 伴随点的实际资格与字符五十三

**定理 108.8（伴随扇区的精确实际第二层）。** 仍令 $\delta=4s$，置 $b=\lambda^8$、$P(U)=U^2-(1+b)U-b$。对每个 $u\in2Q$，

$$
v_s(u)\in W_2\quad\Longleftrightarrow\quad P(u)P(-u)=0,
\qquad |W_2\cap T_s|=1+\chi(53).
\tag{108.15}
$$

每个保留的点恰有一个合法的接枝到 $H$ 的相位／符号对：相位 $y=u/(2\lambda)$，继续符号 $s$；其相反符号 $-s$ 由实际传感器分离。

证明。伴随点的中心坐标为 $(u,-4s/u)$，不在 $H$。107.2说明，它若属于 $W_2$，必须有一个分离符号和一个同符号后继终端的继续分支。设后者的相位为 $y\in Q$、符号为 $e$，置 $k=y/u\ne0$。终端条件为

$$
(1+2k)(-4s+2e/k)=4s,
\quad\text{即}\quad
4k^2+(4-2e/s)k-e/s=0.
\tag{108.16}
$$

$e=s$ 时，式子分解为 $(2\lambda k-1)(2\lambda^{-1}k+1)=0$，两根为 $1/(2\lambda),-\lambda/2$。$e=-s$ 时，分解为 $(2\lambda^2k+1)(2\lambda^{-2}k+1)=0$，两根为 $-1/(2\lambda^2),-\lambda^2/2$。由于 $\chi(u)=\chi(2)$，相位 $y=ku$ 合法恰要求 $\chi(k)=\chi(2)$；只有第一个根符合，另三个都因负号具有相反特征。故唯一合法选择是 $y=u/(2\lambda),e=s$，其中心后继直接为 $(\lambda u,4s/(\lambda u))\in H$。这些代数根没有被当作控制者可以任选的符号。

在此相位，相反符号 $-s$ 的第一候选读零恰给 $w=as c/y^2$；代入 $v_s(u)$ 得

$$
u(u-1)=b(u+1),\quad\text{即 }P(u)=0.
$$

第二候选读零恰给 $w=4s+as(c-1)/y^2$；代入得 $u^2+(1+b)u-b=0$，即 $P(-u)=0$。两个传感器同时为零的必要条件是它们的差 $Bs(-a/y+4y)$ 为零，即 $u^2=b$。但与任一根方程联立都会给 $(1+b)u=0$，不可能：$u\ne0$，且 $b$ 是非零平方而 $-1$ 非平方。因此每个保留根恰有一个零读数，在 $-s$ 下实际分离。

符号 $s$ 的两读数必须相容；否则两个符号均分离会把此点放入终端集 $H$，与中心积 $-\delta\ne\delta$ 矛盾。其同 $s$ 后继已经在 $H$，所以根确实给出 $W_2$ 证书。反向由唯一合法继续分支，任何实际证书都必须满足上述某一个传感器零方程，得到充要关系。这里保留了两候选、相反分离符号、同符号继续和共同零位排除，未使用包络的逆命题。

两多项式的共同判别式为

$$
D=b^2+6b+1=53b.
\tag{108.17}
$$

确实，$\lambda-\lambda^{-1}=1$ 依次给 $\lambda^2+\lambda^{-2}=3$、$\lambda^4+\lambda^{-4}=7$、$\lambda^8+\lambda^{-8}=47$，故 $b^2+1=47b$。$p\ne53$，因为 $p\equiv3\pmod4$，所以 $D\ne0$，且 $\chi(D)=\chi(53)$。

若 $\chi(53)=-1$，两式均无域内根。若 $\chi(53)=1$，$P$ 有两个不同非零根 $\rho,\rho'$，积为 $-b$，因此二次特征相反；恰一个根，例如 $\rho$，属于 $2Q$。$P(-U)$ 的合法根则是 $-\rho'$，也恰一个。两合法根不同，否则 $\rho+\rho'=0$，与和为 $1+b\ne0$ 矛盾。映射 $u\mapsto v_s(u)$ 单射，故点数恰为 $1+\chi(53)$。由于 $n\ge5$，整个 $n$ 点伴随扇区在任何允许参数下都不包含于 $W_2$。证毕。

### 108.5 中心的真实三阶段比较及其边界

**定理 108.9（中心第三层的充要条件与付费实现）。** 对 $\delta=4s$，

$$
O_s\notin W_2,\qquad O_s\in W_3\quad\Longleftrightarrow\quad\chi(53)=1.
\tag{108.18}
$$

在104.5的预先报告相位、每份 offer 保护且消耗于一个原语、付费不扰动测试和请求完成的合同下，正条件给出同一固定来源上的比较，至多 $3n$ 个实际原语、至多两个 $G$、恰一个 $T$；所有实际 $R$ 对齐和最初标签的运输均计入。

证明。在 $O_s$，两候选互为负向量，故 $L'_e=-L_e$，每个相位和符号的零位均相同，没有立即分离分支。相位 $x$ 的两接枝后继中心积为 $4e$：符号 $s$ 到 $H$，符号 $-s$ 到 $v_s(2x)\in T_s$，后者不在 $H$。这直接给 $O_s\notin W_2$。在 $W_3$ 定义中，两个同符号后继必须都在 $W_2$；一支已经在 $H$，另一支随着 $x\in Q$ 恰遍历 $T_s$。108.8于是给出(108.18)的两个方向，也排除了额外传感器分支在本层修补负条件的可能。

设 $\chi(53)=1$。从 $P$ 的显式根 $(1+b\pm\sqrt{53b})/2$ 中选唯一属于 $2Q$ 的 $u$，取第一相位 $x=u/2$，在中心对两个实际符号都执行 $G$。符号 $s$ 到 $H$，接终端比较；符号 $-s$ 到 $v_s(u)$。后一分支选择第二相位 $y=u/(2\lambda)$：报告符号 $-s$ 时执行 $T$，108.8保证分离；报告符号 $s$ 时执行 $G$，到 $H$ 后再作终端 $T$。所以最长路径三个阶段、两个 $G$、一个 $T$，各短分支同样恰有一次 $T$。根与相位的选择只使用已知参数和候选预测，不读取未知真实来源。

每个目标相位在最后一份 offer 之前固定。从已保留的当前相位开始，$\lambda$ 的阶为 $n$，执行 $0$ 至 $n-1$ 个实际 $R$ 即可对齐；每个 $R$ 都消耗自己的 offer，并记录该次已报告的反射。接着的一份 offer 只保护所选 $G$ 或 $T$。在保留框架 $\operatorname{diag}(1/x,e x)$ 中，实际传感器为 $Ac/x+Be xw$，乘同一单位 $e$ 恰给(108.1)，实际接枝的逆像恰为 $(x,e/x)$；逆框架是运输计算，不是一次物理逆动作。所有中途反射可改变最后有效符号，但两个符号均由上述策略覆盖。因此每阶段实际费用至多 $n$，总费用至多 $3n$，没有免费旋转、免费新 offer、重置或等待时钟。

所有候选始终在同一实际动作与报告历史下更新，各保留不可改的最初标签 $c_0$ 和共同单位仿射关系 $c_{\rm current}=\alpha c_0+\beta$、$\alpha\ne0$。一次分离 $T$ 至少删除所选不同标签对中的一个，并保留实际来源槽；不要求预知所选哪一槽是真实来源，也不以新剩余代表元替换固定整数来源。首份已知正号若被前置 $R$ 消耗，也按同一规则记录。物理 $H=341,E=M^{15},T=\gcd(2a+3b,341)$ 的已有实现桥仅供11／31两个分量使用，另一分量随同一全局历史更新，不取得独立相位。一般允许素数上的结论是上述抽象接口内的比较；这里没有增加任意素数的物理桥。证毕。

**命题 108.10（一个算术反例与已知正号启动的区别）。** 在已允许的 $p=31,\lambda=19$ 下，$\chi(53)=-1$，故两个差层 $\delta=\pm4$ 的中心均不在稳健层 $W_3$。这不构成已知正号启动时的取得不可能性。

证明。$19^2=19+1$，$19^3=8\ne1$、$19^5=5\ne1$、$19^{15}=1$，故阶恰15；参数为 $\mu=13,A=22,B=11$。模31有 $53=22$，且

$$
22^2=19,\quad22^4=20,\quad22^8=28,\quad
22^{15}=28\cdot20\cdot19\cdot22=-1.
\tag{108.19}
$$

所以二次特征为负，108.9给出所述反例。它否定“这些中心总在第三层”的加强命题，没有枚举后续层。

另一方面，对任意允许素数，在 $s=1$ 且初始框架为恒等、首份 offer 已知为正时，可以立即以相位1执行 $G$；后继中心积为4，已在 $H$，再用至多 $n$ 个原语作终端比较，总计至多 $n+1$。此路线独立于 $\chi(53)$。所以稳健第三层的否定不等于这种特殊启动的动作下界，更不等于永远不能取得。证毕。

上述承重推导在107.2的实际混合门与107.12的有向规则上增加代数包络和精确伴随资格，属于仓内综合推导（`repo-derived`）；结式根公式和二次方程的通常性质仅在证明内部使用，不作原创性主张。关于107节末的文献条件，van den Bos–Vaandrager 的 [*State Identification for Labeled Transition Systems with Inputs and Outputs*，定义16](https://arxiv.org/html/1907.11034v2) 的 injective 条件保持共同存续的不同候选之不相容性，并允许输出标签并非双方共同可发时的例外；该条件不表述为保持相容性。它仍要求本题另证相应候选对不相容，不能由物理历史可逆性直接补出。

这些定理尚未证明：对每个允许素数和每个非零差值，真实的更高层同符号门必产生足够的同列联合证书，或以其他方式排除全部非空精确 $K$。正字符只供应两个伴随点和一个中心，负字符只排除相应早层证书；两者都没有供应稠密列，也没有构造带合法启动和固定来源实现的精确安全集。一般目标仍需要该高层联合供应证明，或一个满足完整安全合取及实现条件的反例。所保留的初始／当前商标签也不等于原始有序树或全部整数构成；$t::=\alpha\mid\beta\mid\langle t,t\rangle$ 的构造、替换与附加观察接口继续各有其作用。

## 108.99 追加锚

## 109. 实际付费读数、短前缀支撑与二原子来源的比较成本

本节在103.1、104.1的先报告合同内计算实际取得成本。三项结论分别针对全支持初始任务、每列每个非零差值的有限预算比较、以及两个明确的原子来源；共同基础是同一已执行历史的仿射传感器逆像。第108节的早层证书及其条件保持原范围，这里不以付费成本代替稳健阶段深度或一般取得结论。

### 109.1 同一合法日程上的仿射前缀

沿用104.4—104.5的 Fibonacci 参数：$p>3$ 为素数，$n=(p-1)/2$ 为奇数，$\lambda^2-\lambda-1=0$、$\operatorname{ord}(\lambda)=n$，$\mu=1-\lambda=-\lambda^{-1}$，以及

$$
A=\frac{3-2\mu}{\lambda-\mu},\qquad
B=\frac{2\lambda-3}{\lambda-\mu},\qquad AB\ne0,\qquad Q=\langle\lambda\rangle.
\tag{109.1}
$$

所用原语是 $R(c,w)=(\lambda c,\mu w)$、$G(c,w)=(c+1,w+1)$，以及付费且不扰动的 $T(c,w)=[Ac+Bw=0]$。每份 offer 先施加并报告共同反射 $E_\sigma(c,w)=(c,\sigma w)$，再保护并消耗于恰一个原语；首份报告已知为正。控制器只有这些报告、无信息的完成信号和实际 $T$ 响应，初始资料与未知真实来源无关，允许任意确定性内部记忆和有限本地计算。没有额外坐标读数、来源相关计时、重置或免费旋转。每个候选保留不可变的初始标签 $c_0$，真实来源在开始前一次固定。

以下固定一个合法日程：每份报告都为正，实际整数实现中取每批 $k_i=0$，包括首批。这是同一个全局零隐藏日程，不由来源或政策另选。$L$ 计全部实际 $R,G,T$ 原语，$N_T$ 单独计全任务的付费读数，$h$ 留给104.5、108.1的稳健阶段。写 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。

**引理 109.1（共同历史的仿射拉回）。** 在上述日程上，任一共同动作前缀均以同一映射运输所有初始候选：

$$
(c,w)=(\lambda^r c_0+t_c,\mu^r w_0+t_w),\qquad
\ell(c_0,w_0)=A\lambda^r c_0+B\mu^r w_0+\gamma,
\quad \gamma=At_c+Bt_w.
\tag{109.2}
$$

其中 $r$ 为已执行 $R$ 次数，$t_c,t_w$ 由记录确定。每次 $T$ 的零集是两个坐标系数均非零的仿射线，每个 $c_0$ 列恰有一个零点。若删去前缀中的不扰动 $T$ 得到 $R/G$ 词 $u$，并令 $m_k$ 为其后恰有 $k$ 个 $R$ 的接枝数，则

$$
\gamma=\sum_{k=0}^{r}m_kF_{k+3}\pmod p,\qquad m_k\ge0.
\tag{109.3}
$$

证明。空前缀有 $r=0,t_c=t_w=0$。追加 $R$ 将 $r$ 加一并把平移乘以 $(\lambda,\mu)$；追加 $G$ 把两个平移各加一；$T$ 不改状态。归纳得(109.2)，而 $A,B,\lambda,\mu$ 都是单位，故两个系数非零。删去 $T$ 只用于辨认这个已达到状态：它不扰动，且每个被删位置的隐藏作用都是恒等，不能据此把原有测试变成免费操作。

一次接枝经过后续 $k$ 个旋转，对传感器常数项贡献 $s_k=A\lambda^k+B\mu^k$。由(109.1)得 $s_0=2,s_1=3$；$\lambda,\mu$ 同为 $z^2=z+1$ 的根，故 $s_{k+2}=s_{k+1}+s_k$。于是 $s_k=F_{k+3}\pmod p$，把全部接枝贡献相加得(109.3)。候选的 $c_0,w_0$ 是假设索引，$r,t_c,t_w$ 是共同命令的运输记录，均没有增加真实来源的观察。证毕。

### 109.2 全支持初始任务的付费读数下界

**定理 109.2（非恒定任务至少 $p$ 次，完整初始坐标至少 $p+1$ 次）。** 假定初始支持为全部 $\mathbb F_p^2$。任何对每个固定初始来源及每个合法日程都保证有限正确取得非恒定任务 $f(c_0)$（$f:\mathbb F_p\to Y$）的确定性协议，在上述零隐藏日程上有一个固定来源的执行满足 $N_T\ge p$。若任务是准确取得整个 $c_0$，则有一个这样的执行满足 $N_T\ge p+1$。两项下界也适用于全部付费原语数；$p+1$ 的加强不在此断言于每个非恒定粗化。前一结论只需109.1中的第二坐标系数为单位，后一结论还使用第一坐标系数为单位。

证明。先沿每次 $T$ 都读非零的共同历史走。做过 $j<p$ 次测试后，相容初始支持恰为平面删去这 $j$ 条仿射零线。每个 $c_0$ 列至少留下 $p-j>0$ 点，所以全部初始标签仍可能；非恒定 $f$ 有至少两个不同任务值，不能在此正确停止。$R,G$ 及本地计算没有额外来源相关输入，不能进一步删除这个初始支持。

这条历史必在有限命令后到达第 $p$ 次测试。否则，在少于 $p$ 次测试的无限延续中，各有限前缀的初始相容支持是有限平面内的递降非空集合，交集非空；其中一个一次固定来源实现整个无限历史，违反保证有限取得。无限内部计算也由任何尚存来源见证失败。故在第 $p$ 次测试前选择任一相容来源，从开始重放政策和零隐藏日程即可使它实际支付这次测试。此测试的实际响应不必非零，已经得到 $p$ 次下界。

完整 $c_0$ 的加强使用如下平面事实：$p$ 条非竖直、斜率非零的仿射线，其非空补集不可能只在一个竖直列 $c_0=a$。反设如此。其他每列都被这 $p$ 个线交点覆盖，所以在那里交点必须全部不同；重复线不可能，任意两条非平行线的交点只能在列 $a$。若全部平行，则 $p$ 条不同平行线覆盖全平面，补集为空，矛盾。若有两条平行且有第三条不平行，第三条分别交它们的两个点都在列 $a$；第三条非竖直，在此列只有一个点，于是两平行线也相交，矛盾。因此只能是 $p$ 条斜率各异的线，但非零有限斜率只有 $p-1$ 个。该事实成立。

现在沿前 $p-1$ 次非零响应到第 $p$ 次 $T$。若非零响应仍可实现，选择它；其非空支持正是 $p$ 条线的补集，由上述事实至少有两个不同 $c_0$。若非零响应不可实现，则所有先前尚存来源都在第 $p$ 条线上，选择零响应不删除任何候选，而先前支持仍含全部 $c_0$。两种情形在 $p$ 次测试后均不能正确停止。选择该非空支持内一个来源一次固定；确定性使其从开始的执行复现所构造前缀，有限取得保证使它最终再做一次 $T$，否则无新观察就只能错误停止或无限继续。因此这个固定来源支付至少 $p+1$ 次测试。响应分支的选择是相容支持的存在证明，不是执行中换源或给控制器添加一个选择响应的能力。证毕。

**推论 109.3（同一实际来源族上的模341消费者）。** 对103.1—103.2的实际仪器，任何保证准确取得 $c_0\bmod341$ 的协议，有一个固定正整数来源在同一全局 $k_i=0$ 日程上至少支付32次完整 gcd 测试。

证明。在活跃模31分量使用103.2b的 $\lambda=19,\mu=13,A=22,B=11$；这些系数都是单位。允许初始活跃坐标遍取 $\mathbb F_{31}^2$，同时把被动模11的初始原坐标 $(a_0,b_0)$ 固定为 $(0,0)$。局部坐标变换 $c=a+\lambda b,w=a+\mu b$ 的行列式 $\mu-\lambda$ 非零；103.2的全模数逆变换及逐坐标 CRT 因而为每个活跃点供应一次固定整数提升。对原坐标加正的341倍数可取正代表，它们也可由具有相应 $\alpha,\beta$ 叶数的有限树供应。随后只对该实际来源执行原来的 $M$ 与接枝，不用剩余代表替换它。

在任何共同历史中，被动模11状态是已知且相同的共同命令函数。令其下一次传感器是否被11整除所给的已知因子为 $d_i\in\{1,11\}$。完整实际响应恰为

$$
\gcd(2a+3b,341)=d_i\begin{cases}31,&\text{活跃标量为零},\\1,&\text{活跃标量非零}.
\end{cases}
\tag{109.4}
$$

因此完整响应对这个来源族只增添109.2所用的活跃零位，不从被动分量增加未知来源信息。不同活跃初始 $c_0$ 对应不同全模数初始标签，故全标签取得必须取得活跃 $c_0$。109.2取 $p=31$ 得至少32次实际 $T$。两个分量始终接受同一全局命令和隐藏日程；没有独立素数相位，也不把两个局部下界相加。本结论只使用已有341实现，不给其他素数增加实际仪器桥。证毕。

### 109.3 每个非零差值、每一列的付费前缀支撑

**定理 109.4（逐列的必要支撑与政策之前的硬对）。** 从恒等初始框架开始，固定(109.1)的任一参数、任一 $\delta\ne0$ 和整数 $L\ge1$，令

$$
P_\delta(c,w)=\bigl((c,w),(c-1,w-\delta)\bigr),\qquad
B_{\rm paid}(L)=2\min\{2^L-1,\ F_{L+5}-2L-5\}.
\tag{109.5}
$$

对每个 $c\in\mathbb F_p$，可保证在 $L$ 个实际付费原语内分离的这种候选对，其 $w$ 值至多有 $B_{\rm paid}(L)$ 个。若 $p>B_{\rm paid}(L)$，则每列至少有 $p-B_{\rm paid}(L)$ 个 $w$，各自供应在政策选择之前固定的候选对，使每个 $L$ 预算确定性自适应政策在同一零隐藏日程上取得相同完整转录。因此全对的统一付费预算必须满足 $p\le B_{\rm paid}(L)$。这里“可保证”允许政策知道所选双候选库，但两种真实来源的初始政策资料相同。

证明。在预算内任一次 $T$ 之前，删去更早的不扰动测试，余下的 $R/G$ 词长度至多 $L-1$。若其中有 $r$ 个 $R$，接枝数至多 $L-1-r$。109.1给每个接枝贡献普通非负整数 $F_{k+3}$ 的模 $p$ 值，且 $0\le k\le r$，故实际常数项有一个整数代表满足

$$
0\le b\le m_r:=(L-1-r)F_{r+3},\qquad 0\le r<L.
\tag{109.6}
$$

定义扩大后的仿射族及候选读数差

$$
\ell_{r,b}(C,W)=A\lambda^r C+B\mu^r W+b,\qquad
D_r=A\lambda^r+B\mu^r\delta.
\tag{109.7}
$$

整数 $b$ 在域中取其余数。实际候选读数就是 $\ell_{r,b}(c,w)$ 与 $\ell_{r,b}(c,w)-D_r$。零位不同必有至少一个读数为零，即使 $D_r=0$ 也保留这一必要条件。区间中未被实际词实现的 $b$ 只扩大必要支撑。

取两个多项式包络。一是对(109.6)的全部整数偏移取

$$
\Pi^{\rm int}_L(C,W)=\prod_{r=0}^{L-1}\prod_{b=0}^{m_r}
\ell_{r,b}(C,W)\bigl(\ell_{r,b}(C,W)-D_r\bigr).
\tag{109.8}
$$

另一是对全部长度小于 $L$ 的 $R/G$ 词的实际仿射读数取同样两个因子的乘积，记为 $\Pi^{\rm word}_L$。词数由二字母自由词的符号计数为 $\sum_{d=0}^{L-1}2^d=2^L-1$，无需逐词或逐态枚举。每个因子的 $W$ 系数为 $B\mu^r\ne0$；因此两个乘积在每个固定 $C=c$ 都是非零一元多项式，首项系数为这些单位的乘积，不依赖 $c$。相位包络里的例外列在这里也满足该非零条件；重复词传感器、重合零点及模 $p$ 重复偏移都不破坏它。

词包络的 $W$ 次数为 $2(2^L-1)$。对区间包络，用有限和恒等式

$$
\begin{aligned}
\sum_{r=0}^{L-1}(L-1-r)F_{r+3}
&=\sum_{j=0}^{L-2}\sum_{r=0}^{j}F_{r+3}
=\sum_{j=0}^{L-2}(F_{j+5}-3)\\
&=F_{L+5}-3L-5,
\end{aligned}
\tag{109.9}
$$

其中空和为零；内和公式由 Fibonacci 递推望远镜相消即得。加上每个 $r$ 的一个常数项，总因子对数为 $F_{L+5}-2L-5$，故 $\deg_W\Pi^{\rm int}_L=2(F_{L+5}-2L-5)$。

每个保证比较成功的 $w$ 必在两个专门化包络的零集中：若在其中任一个的零集之外，则预算内每个可能的测试前缀对两个来源都读非零。任意确定性政策从相同初始资料出发，归纳得报告、动作、完成信号、测试响应、内部配置及停止决定全部相同。两种真实来源的初始标签 $c,c-1$ 不同，同一答案不能对两者都正确；不停止也不满足预算。非零一元多项式的不同根数不超过次数，因每个不同根逐次提供一个线性因子。于是可保证成功的 $w$ 数不超过两次数的较小值，即(109.5)。

在 $p>B_{\rm paid}(L)$ 时，预先选择次数较小的包络，每列其非根至少有 $p-B_{\rm paid}(L)$ 个。任取其中 $w$ 并一次固定两个初始来源；回避条件已经覆盖全部短前缀，因此同一对击败所有预算政策，而非在政策运行后才改选来源。所有预算政策使用的反例日程也都是同一个 $k_i=0$ 日程。证毕。

包络零点仅是必要条件：有零点不保证相位合法、两个零位不同或能在预算内到达它。上述硬对可随 $L,c,\delta$ 改变；没有证明它们在所有后继下封闭，也不能把有限预算的非空补集交到无穷预算而宣称得到精确安全集 $K$。对模11或31的付费双候选消费者，可以先用坐标逆变换和 CRT 给这两个活跃候选同一个被动初始分量，再沿共同日程运行；(109.4)的同被动因子论证使相同活跃响应成为相同完整 gcd 响应，并保持不同全模数初始标签。这是固定来源提升，不是额外素数上的实现。

### 109.4 两个原子来源的明确固定比较

**定理 109.5（$\beta$ 与 $\langle\alpha,\beta\rangle$ 的 Fibonacci 预算阈值）。** 在[原子生成卷第2—3节](FIBONACCI_ATOMIC_RELATION_GENERATION.md)的组成解释下，取两个实际有限来源 $t_-=\beta$、$t_+=\langle\alpha,\beta\rangle$，其组成分别为 $s_-=(0,1)$、$s_+=(1,1)$。使用所声明的局部模 $p$ 接口，在恒等初始框架及同一零隐藏日程上，若 $p>F_{L+4}$，它们不能被任何确定性自适应政策在 $L\ge1$ 个实际付费原语内分离。准确的规范初始对是

$$
\bigl((\lambda^2,\mu^2),(\lambda,\mu)\bigr)
=P_1(\lambda^2,\mu^2).
\tag{109.10}
$$

证明。在原组成坐标写 $M=\begin{pmatrix}0&1\\1&1\end{pmatrix}$、$\alpha=(1,0)$、$q=(2,3)$，则 $R(s)=Ms,G(s)=s+\alpha$。首先证明对每个恰有 $d$ 个正 $R/G$ 字母的词 $u$，

$$
q\,u(1,1)\le F_{d+5},\qquad qR^d(1,1)=F_{d+5}.
\tag{109.11}
$$

由行向量递推 $qM^r=(F_{r+3},F_{r+4})$。任何后缀 $z$ 是仿射映射 $z(s)=M^r s+t$，其中 $r$ 为后缀旋转数。由 $(1,1)$ 出发每个中间态 $(a,b)$ 都有 $a,b\ge1$。在一个 $G$ 位置保留前缀、后缀而把该 $G$ 换为 $R$，最终标量增加

$$
\begin{aligned}
qM^r\bigl(R(a,b)-G(a,b)\bigr)
&=F_{r+3}(b-a-1)+F_{r+4}a\\
&=F_{r+3}(b-1)+F_{r+2}a>0.
\end{aligned}
\tag{109.12}
$$

逐个替换仍保持所有中间态正，故全 $R$ 词达到最大值；其读数是 $F_{d+3}+F_{d+4}=F_{d+5}$，包括 $d=0$，证明(109.11)。这是统一替换论证，无词枚举。

$R,G$ 都保持逐坐标序，且从非零非负来源不会产生零向量。因此对同一词 $u$，

$$
1\le q\,u(s_-)\le q\,u(s_+)\le F_{d+5}.
\tag{109.13}
$$

预算内一个 $T$ 的前缀删去先前测试后有 $d\le L-1$，所以两个实际整数标量都在 $[1,F_{L+4}]$ 内；当 $p>F_{L+4}$ 时均不被 $p$ 整除。共同正报告、共同完成信号和相同非零位使每个自适应政策逐步选择相同动作、形成相同内部状态及停止答案。这个明确的双源在政策前已经固定，故不同初始任务值不能在预算内都被正确识别。

坐标共轭为 $c=a+\lambda b,w=a+\mu b$；它的行列式非零，满足 $CM=\operatorname{diag}(\lambda,\mu)C$、$C\alpha=(1,1)$ 及 $(A,B)C=q$。由 $1+\lambda=\lambda^2$、$1+\mu=\mu^2$ 得(109.10)，初始第一坐标差恰为1，第二差也为1；没有预备动作。首份已知正报告在恒等框架下给 $x=1,e=1$。以后即使所有隐藏批仍为零，含 $r$ 个旋转的线性框架也为

$$
\operatorname{diag}(\lambda^r,\mu^r)
=\operatorname{diag}(1/x,e x),\qquad x=\lambda^{-r}\in Q,\quad e=(-1)^r.
\tag{109.14}
$$

所以“零隐藏”不表示每个有效阶段符号都为正。将实际标量乘同一单位 $e$ 得 $Ae c/x+Bxw$，把实际接枝增量 $(1,1)$ 拉回同一框架得 $(x,e/x)$；两个候选的传感器和后继使用同一个 $e$。平移部分仍由109.1运输，初始标签不改。证毕。

这个阈值给出统一全对付费预算的另一必要条件 $p\le F_{L+4}$，它直接把两个生成来源接到观察者消费者。在 $L\ge3$ 时，这个数值阈值更强：$F_{L+4}<2^{L+1}-2$ 可由 $L=3,4$ 的严格不等式及 Fibonacci 递推归纳；置 $H_L=2(F_{L+5}-2L-5)-F_{L+4}$，则 $H_3=7$，且 $H_{L+1}-H_L=F_{L+4}+F_{L+2}-4>0$，故 $F_{L+4}<B_{\rm paid}(L)$。$L=1,2$ 时则分别是 $F_{L+4}=5,8$ 而 $B_{\rm paid}(L)=2,6$，不能称原子阈值更强。它与109.4的“每个非零 $\delta$、每列存在许多硬对”有不同量词，不能互相替代。

这里只把局部接口的 $s_-,s_+$ 称为这两棵原始树；它们在完整341仪器下未被自动断言具有相同 gcd。需要完整仪器的有限预算反例时，可为活跃 $p\in\{11,31\}$ 的这两个组成余数选择相同被动分量，并一次作 CRT 整数提升，沿同一个全局 $k_i=0$ 日程用(109.4)提升相等转录。这些提升一般是另外两棵有限树，不偷换成原来的两棵。其他允许素数仍只具有声明的局部模接口。上述组成解释也没有恢复有序树的次序和括号；生成层与任务边界的区别沿用原子生成卷第247—249节。

### 109.5 付费预算的边界与尚缺的实际供应

三种成本的对象不同。109.2的 $N_T$ 计完整初始任务树上全部测试；109.4—109.5的 $L$ 计某对比较中所有实际 $R,G,T$；$W_h$ 的 $h$ 计覆盖两个有效符号的稳健阶段。104.5的实现为每个阶段支付至多 $n-1$ 个旋转和一个 $G/T$，故一个 $h$ 阶段证书有至多 $nh$ 个实际原语的充分实现上界，非每阶段恰需 $n$ 个。把 $L=nh$ 代入付费必要阈值不能推出与 $p$ 无关的阶段支撑界 $B_{\rm phase}(h)$；$n=(p-1)/2$ 本身随参数变化。全任务至少 $p+1$ 次测试也不约束单个候选对的阶段深度，它可与许多逐对比较共存。

若试图仅从第108节的有限次数包络迭代到任意阶段，已有一个短的推法警示：令 $f(C,W)=(CW-1)(CW-3)$。它没有竖直因子，$f(0,W)=3\ne0$，但

$$
f(C,W-2/C)=(CW-3)(CW-5)
\tag{109.15}
$$

与 $f$ 共有分量 $CW-3$。对每个 $x\in Q$，前驱 $(0,2/x)$ 的同相位双后继 $(x,3/x),(x,1/x)$ 均在 $\{f=0\}$，在列零给出 $n$ 个不同前驱。这里 $W$ 首项系数为 $C^2$，恰在该列为零，不满足108.3的非零首项条件。此例只否定“有界次数且无竖直因子自动可迭代”的推法；它不是实际 $W_h$ 种子，不给实际取得的反例。

本节的普通证明由103.1—103.2的实际接口、104.5的同符号运输以及原子生成卷第2—3、247—249节的生成／组成区分直接导出；有限域直线覆盖、Fibonacci 递推和一元根界均已在证明中给出所用论证。结论是明确条件下的取得与比较成本，不含匹配上界、最优性、允许素数的无穷性、墙钟时间或物理统一主张。

一般恢复仍缺一个关于真实更高层的供应证明：对每个允许参数和每个非零 $\delta$，同符号传感器与后继联合门须实际产生足够的同列联合证书／稠密联合边界，或以其他准确论证排除全部非空精确安全集。另一条否定路线则须给非空 $K$，并对每个 $v\in K,x\in Q$ 供应同一个 $e$ 同时满足非分离和 $v+(x,e/x)\in K$，再证明已知正号启动及一次固定来源的合法实现。有限预算硬对、包络零点或成本下界均未补出这些条件；空间、时间、边界和记忆的一般互恢复问题仍保留这个实际供应或安全集缺口。

## 109.99 追加锚

## 110. 实际第三层的全列稀疏性与第四层的直接前驱界

本节沿用定义108.1的全部参数、同符号传感器和实际层，不以包络零点代替实际证书。109.1所用 Fibonacci 参数的准确出处是104.7、式(104.20)，亦见定义108.1；104.5则供应运输及付费实现。109.4在式(109.14)后的 $Ae c/x+Bxw$ 使用保留线性框架中的**当前代表**。若直接使用不可变初始坐标，实际态写成 $D(x,e)(c_0,w_0)+\tau$，其中 $D(x,e)=\operatorname{diag}(1/x,ex)$，则同一单位 $e$ 乘后的传感器为 $Ae c_0/x+Bxw_0+e\gamma$，$\gamma=A\tau_c+B\tau_w$。当前代表已经吸收 $D(x,e)^{-1}\tau$，不能在初始坐标表达式中删去该仿射项。

以下固定任意允许参数及任意 $\delta\ne0$，记 $a=A/B=\lambda^6$、$Q=\langle\lambda\rangle$。由105.1，$n\ge5,p\ge11$，$Q$ 是非零平方子群，$-1$ 非平方。$J,K_0,F_e,F$ 始终指式(108.3)，其中 $K_0=(2C-1)W+aC(2W-\delta)$；$K$ 留给精确安全集。对 $r\ge1$，实际递推为

$$
W_{r+1}=W_r\cup\{v:\exists x\in Q\ \forall e\in\{1,-1\},\quad
\operatorname{Sep}_e(v,x)\ \lor\ v+(x,e/x)\in W_r\},\qquad W_1=H=\{J=0\}.
\tag{110.1}
$$

### 110.1 Fibonacci 排除与三列的全部极部

**引理 110.1（所需四个算术排除）。** 每个允许参数都满足 $a\notin\{1,-1,1/2,-1/2\}$。

证明。$\lambda-\lambda^{-1}=1$ 给 $\lambda^2+\lambda^{-2}=3$，故

$$
a+a^{-1}=(\lambda^2+\lambda^{-2})^3-3(\lambda^2+\lambda^{-2})=18,
\qquad a^2-18a+1=0.
\tag{110.2}
$$

$a$ 平方而 $-1$ 非平方，排除 $a=-1$。若 $a=1$，则奇数准确阶 $n\mid6$，只能为1或3，与 $n\ge5$ 矛盾。代入 $a=-1/2$ 给 $41=0$，但 $p=41$ 的半阶为偶数。代入 $a=1/2$ 给 $31=0$；模31的 Fibonacci 根恰为13、19。$13^3=-4,13^5=6,13^{15}=-1$，故13不能有阶15；$19^3=8,19^6=2\ne16=1/2$。两根均不能给所需 $a$。证毕。

**引理 110.2（没有倒数平移的共同分量）。** 对每个 $h\in\mathbb F_p$，$F(C,W)$ 与 $F(C,W-2/(C-h))$ 在 $\overline{\mathbb F_p}(C)[W]$ 中互素。

证明。在 $k=\overline{\mathbb F_p}$ 上置 $t=C-h$，在 $k((t))$ 的带赋值代数闭包中考察根；“有界”指赋值非负。共同因子会给两个根 $r,s$ 满足 $r-s=2/t$。108.2的首项 $b_F(C)=a^4C^2(1-C)^2(2C-1)^9$ 在普通列为单位，除以它后是整系数首一多项式，其根均有界。因此只需处理三列。

在 $C=t$，$F_e$ 的三次项系数赋值为1，二次项系数为单位，低次项系数有界。若 $W$ 的极阶 $q$ 在 $(0,1)$ 中，二次项唯一具有最低赋值；若 $q>1$，三次项唯一最低，均不可能为根。置 $W=V/t$ 后，$t^2F_e(t,V/t)$ 在 $t=0$ 的初始式为 $V^2(1-aeV)$，其唯一非零根 $e/a$ 是单根，故唯一无界根的极部为

$$
W=\frac{e}{at}+O(1).
\tag{110.3}
$$

这里单根提升给出该支，并排除额外分数阶极部；余下两根有界。$J$ 及两个镜像因子在此列有单位首项，根均有界。在 $C=1+t$，换元 $I(C,W)=(1-C,\delta-W)$ 给相同的极部集合 $0,1/(at),-1/(at)$。两根之差为 $2/t$ 将要求 $a=\pm1$ 或 $\pm1/2$，由110.1排除。

在 $C=1/2+t$，$J$ 的唯一根恰为

$$
W=\delta/2+\delta/(4t).
\tag{110.4}
$$

每个 $F_e$ 的三次项系数赋值为2，二次项在 $t=0$ 为 $a^2\ne0$，其他系数有界。同样的最低赋值比较排除 $0<q<2$ 及 $q>2$。写 $W=k/t^2+l/t+O(1)$，$t^{-4}$ 系数为 $ak^2(a-2ek)$；唯一非零初始根 $k=ae/2$ 是单根。代入后，$t^{-3}$ 系数为 $(a^3e/2)(ae+\delta/2-l)$。所以全部无界支恰为

$$
\begin{aligned}
F_e:&\quad W=\frac{ae}{2t^2}+\frac{ae+\delta/2}{t}+O(1),\\
F_e\circ I:&\quad W=-\frac{ae}{2t^2}+\frac{ae+\delta/2}{t}+O(1).
\end{aligned}
\tag{110.5}
$$

各三次因子的另两根有界。两条二阶极支只有 $F_e$ 与 $F_{-e}\circ I$ 能消去 $t^{-2}$ 项；其 $t^{-1}$ 系数之差为 $2ae$，由 $a\ne\pm1$ 不可能为 $\pm2$。二阶极支与其他支相减仍有二阶极点；两个有界根也不可能。剩下的唯一情形是 $J$ 根与有界根相减。式(110.4)迫使 $\delta=\pm8$，且那个有界根必须**恰为**常数 $\delta/2$。然而在该水平图上

$$
J(C,\delta/2)=-\delta/2,\qquad
F_e(C,\delta/2)=\delta^2(C-1/2)^2
-\frac{aeC\delta}{2}(-\delta/2+2e)^2.
\tag{110.6}
$$

后式的 $C^2$ 系数为 $\delta^2\ne0$；镜像因子由 $C\mapsto1-C$ 也非零。因此 $F(C,\delta/2)$ 不恒为零，该水平图不是分量。所有根对均已排除。论证允许有限重根及可约因子；所用无界初始根都是单根，无需全曲线可分或光滑假设。证毕。

### 110.2 两类实际前驱与全列八百三十七点

**定理 110.3（实际第三层的全列界）。** 对每个允许参数、每个 $\delta\ne0$、每个 $h\in\mathbb F_p$，

$$
|(W_3)_h|\le837.
\tag{110.7}
$$

证明。108.2给 $W_2\subseteq\{F=0\}$、双次数 $(13,13)$ 及无竖直因子，故每列 $W_2$ 至多13点。先计两接枝后继均在 $W_2$ 的前驱。置

$$
P_\pm(X,Y)=X^{13}F(h+X,Y\pm1/X).
\tag{110.8}
$$

每式的 $X$ 次数至多26，$Y$ 次数至多13。分别除去所含的最大 $X$ 幂，得到 $\widetilde P_\pm$；不改变任何 $X\ne0$ 的零点。若仍有共同非竖直分量，可逆换元 $C=h+X,W=Y+1/X$ 会给110.2排除的共同因子；共同竖直分量 $X=x_0\ne0$ 会使 $F(h+x_0,W)$ 恒为零，与108.2矛盾。$X=0$ 已除净。因此两式互素，其关于 $X$ 的结式是非零的 $Y$ 多项式。Sylvester 行列式至多52行，每个元素的 $Y$ 次数至多13，故次数至多676。每个有非零相位的双后继前驱高度都是它的根，所以每列这类前驱至多676点。这在三条例外列同样有效。

再计一个符号分离、相反符号继续到 $W_2$ 的混合前驱。记继续符号为 $e$。在 $-e$ 下第一候选读零给 $w=aeh/x^2$，必要式为

$$
P_{h,e}^{(1)}(x)=x^{26}F(h+x,aeh/x^2+e/x)=0.
\tag{110.9}
$$

这是普通多项式：$W$ 次数至多13，足以清除 $x^{-2}$ 分母。它的准确次数从无穷远求得，且不依赖 $h$。令 $s\in\{1,-1\}$ 为因子下标，$x\to\infty$ 时

$$
\begin{aligned}
C&=x+O(1),&W&=e/x+O(x^{-2}),\\
J&=-\delta x+O(1),&K_0&=-a\delta x+O(1),\\
F_s(C,W)&=a\delta^2(a-se)x^2+O(x),\\
F_s(1-C,\delta-W)&=as\delta^3x^3+O(x^2).
\end{aligned}
\tag{110.10}
$$

四因子乘 $J$，精确给

$$
F(h+x,aeh/x^2+e/x)
=a^4\delta^{11}(a^2-1)x^{11}+O(x^{10}).
\tag{110.11}
$$

110.1使该系数非零，故(110.9)次数**恰为37**，在每列至多37个相位，每相位固定一个高度。第二候选读零给 $w=\delta+ae(h-1)/x^2$；$F\circ I=F$，且 $I$ 把其后继曲线变成第一类曲线，参数为 $h'=1-h,x'=-x$、符号仍为 $e$。由于清分母幂26为偶数，其多项式也恰为37次（首项与(110.11)相反），至多37根。这个换元只是多项式证明，不是合法相位取负动作。两个候选、两个继续符号共至多 $4\cdot37=148$ 点。

现在依(110.1)穷尽实际新点。若两个符号都不分离，两个后继必须都在 $W_2$；若恰一个分离，就是上述混合前驱；若两个都分离，由106.3已经在 $H\subseteq W_2$。加上旧层得到 $13+676+148=837$。非平方根、共同零位、继续符号的传感器失败及输出碰撞均只减少实际集合；没有从包络反向宣布获胜。证毕。

### 110.3 任意差值的六混合原像与第四层计数

**引理 110.4（每个目标至多六个实际混合前驱）。** 对任意目标 $(C,W)$，满足“一个符号分离、相反符号的同相位接枝到此目标”的非终端前驱至多六个；结论保留任意 $\delta\ne0$。

证明。这次令 $e$ 为**分离符号**，继续符号为 $-e$。若第一候选在 $e$ 下读零，则所有可能前驱都形如

$$
(c,w)=(C-x,W+e/x),\qquad x\in Q,qquad
BeW x^2+(B-A)x+AC=0.
\tag{110.12}
$$

最后一式由 $Ae c/x+Bxw=0$ 代入并乘 $ex$ 得到，没有改变继续分支的符号。若 $CW\ne0$，两符号的二次式根积分别为 $aeC/W$，特征相反。根积非平方的二次式至多有一个不同平方根值；否则两个平方根值之积将为平方。另一式至多两个，故合计至多三对 $(x,e)$。重根只算一个；实际分离过滤只减少数目。

退化目标也不增加此界。若 $C=0,W\ne0$，非零根为 $(A-B)/(BeW)$，两符号给互为负数的根，恰至多一个属于 $Q$。若 $W=0,C\ne0$，根 $AC/(A-B)$ 与符号无关，至多给两对。若 $C=W=0$，$A-B\ne0$ 排除所有非零根。这里 $A-B=4/(\lambda-\mu)\ne0$，见(105.2)。第一候选共至多三个前驱。

若在 $e$ 下第二候选读零，必须把目标换为

$$
(C',W')=(C-1,W-\delta),\qquad
Be(W-\delta)x^2+(B-A)x+A(C-1)=0.
\tag{110.13}
$$

它是第二候选 $(c-1,w-\delta)$ 到 $(C-1,W-\delta)$ 的同一个继续接枝，故上述全部非退化及退化论证原样适用，再给至多三个。两类的重叠只减数，得六。不能把第二个目标固定写成 $(C-1,W-1)$，除非已声明 $\delta=1$。证毕。

**定理 110.5（实际第四层的全局界）。** 若实际 $W_3$ 每列至多 $M$ 点，则

$$
|W_4|\le p\left[M+6M+\frac{M(M-1)}2\right].
\tag{110.14}
$$

特别地，每个允许参数及任意非零差值都满足 $|W_4|\le355725p$。

证明。写 $k_C=|(W_3)_C|$。旧点贡献 $|W_3|$，新混合点按110.4对每个继续目标计至多六个，贡献至多 $6|W_3|$。剩下的新点必须有两个同相位后继都在 $W_3$。它们是同列两个不同高度 $u,v$，无序对至多给一个合法前驱：相位必须为

$$
x\in\{2/(u-v),-2/(u-v)\}\cap Q,
\qquad (c,w)=(C-x,(u+v)/2).
\tag{110.15}
$$

由于 $-1$ 非平方，交集恰有一个元素；符号只是给两个后继定向，不能产生第二个前驱。全部同列无序对至多 $\sum_C\binom{k_C}{2}$。两个符号均分离者已在 $H$，不存在第四类。于是

$$
|W_4|\le7|W_3|+\sum_C\binom{k_C}{2}
\le p\left[7M+\binom M2\right].
\tag{110.16}
$$

代入110.3的 $M=837$，有 $7\cdot837=5859$、$\binom{837}{2}=349866$，和为355725。此计数直接针对实际前驱，未构造更重的第三层代数包络，也未忘记相位在符号之前选定。证毕。

**推论 110.6（两个准确的有限层消费者边界）。** 若允许素数满足 $p\ge1007$，没有一列实际 $W_3$ 能满足106.2、式(106.7)的严格数值充分条件。若允许素数满足 $p>355725$，则实际 $W_4\ne\mathbb F_p^2$。

证明。对106.2指定的零位移被排除的三步回返，107.5给 $|D|=2q\ge6$。令 $B_h=\mathbb F_p\setminus(W_3)_h$，110.3给

$$
q(|B_h|-1)\ge3(p-838)\ge(p-1)/2=n\qquad(p\ge1007),
\tag{110.17}
$$

故严格条件失败，包括原来的三条例外列。第二项由 $|W_4|\le355725p<p^2$。这只排除指定第三层的严格数值消费者及第四层全覆盖；不排除其他消费者、任意付费协议或后来的层。两项均条件于允许参数，不断言阈值以上有允许素数，更不断言其无穷性。证毕。

### 110.4 精确安全集的条件性固定来源启动桥

**命题 110.7（若有精确安全集，则抽象全支持任务不可保证取得）。** 在104.1的抽象原始 $R/G/T$ 接口、初始支持为全部 $\mathbb F_p^2$、首份 offer 已知为正的合同内，若任意一个非零差层存在非空精确 $K$，即满足(105.4)的同符号合取，则每个非恒定 $f:\mathbb F_p\to Y$ 都没有保证有限正确取得 $f(c_0)$ 的确定性协议。

证明。一次选定安全选择器 $s(v,x)\in\{1,-1\}$，同时保证非分离及 $v+(x,s(v,x)/x)\in K$。105.2（或重复 $x=1$ 的安全后继）给 $K$ 的每个第一坐标纤维非空。非恒定 $f$ 必有 $c$ 使 $f(c)\ne f(c-1)$，否则沿素域加法循环便恒定。选 $(c,w)\in K$，置 $\eta_0=s((c,w),1)$，在执行前固定两个抽象来源

$$
z_0=(c,\eta_0w),\qquad z_1=(c-1,\eta_0(w-\delta)).
\tag{110.18}
$$

这是选择允许来源，不是对已给来源免费反射；初始实际第二坐标差为 $\eta_0\delta$。

归纳保持两当前态为同一框架 $D(x,\eta)P_\delta(v)$，其中 $v\in K,x\in Q$。在出 offer 之前取 $e=s(v,x)$，宣布并施加 $\sigma=e/\eta$。启动时 $x=1,\eta=\eta_0$，所以 $\sigma=+1$，准确满足首份正号。报告后框架为 $D(x,e)$；两个实际测试标量乘同一单位 $e$ 就是 $L_e,L'_e$，由选择器给相同零位。不等候控制器当前动作便已选定该符号。

对报告后任意一个动作，都有同一归纳步：$G$ 给框架 $D(x,e)$ 中的代表后继 $v+(x,e/x)\in K$；$R$ 由 $\mu=-\lambda^{-1}$ 给新框架 $D(x/\lambda,-e)$，代表不变；$T$ 给相同报告，框架 $D(x,e)$、代表不变。因此任意中途旋转、测试及接枝也被覆盖，每份 offer 和每个原语均实际消耗。归纳给两个固定来源相同的全部符号、完成报告及付费测试历史，故控制器的记忆、动作、停止及答案也相同。共同答案不能等于两个不同初始任务值，不终止也违背取得保证。对每个协议，可在执行前选这对中失败的一员；没有沿路径换源，也未声称同一个来源击败全部协议。

初始标签始终固定：实际第一坐标为 $u c_0+t$，初始 $u=1,t=0$；$R$ 把 $(u,t)$ 乘 $\lambda$，$G$ 把 $t$ 加1，反射及 $T$ 不改它。代表 $c$ 不替代 $c_0$。此桥只在全抽象支持上成立；限制来源族须另证(110.18)的两个来源可实现，其他素数也没有因此得到新的整数或 CRT 提升。证毕。

本节的承重内容是108.2包络的三列极部排除、准确37次混合式及实际前驱计数，属于仓内综合推导（`repo-derived`），不是新的 Lean 核验或原创性声明。命题110.7补足104.5—104.7未给出的从任意精确 $K$ 到固定来源及正号启动的反向桥，但没有供应其存在前提。任意精确 $K$ 避开全部 $W_r$：从 $W_0=\varnothing$ 归纳，若 $v\in K$ 被某相位认证，安全合取在同一相位给一个非分离符号，其后继既在 $K$ 又被迫在旧层，矛盾。反过来，有限 $W_4$ 的真补集只保证每个相位有非分离后继在 $W_3$ 外，不保证后继仍在该补集；故有限层真性不产生精确 $K$。

一般恢复仍缺真实更高层的同列联合证书供应，或对所有非空精确 $K$ 的排除／构造。已有11／31物理桥仍须同一固定来源、共同历史及完整响应，不能把条件性大素数结论自动提升成新仪器。阶段证书按104.5具有至多 $nr$ 个付费原语的充分实现，但本节的 $r=3,4$ 限制不转换成任意政策的付费下界、无界深度或整体恢复结论。

## 110.99 追加锚

## 111. 终端锚定边界与首个非终端逃逸

**定义 111.1（实际层与终端外界）。** 沿用105.1、106.1的原假设：$p>3$ 为素数，$n=(p-1)/2$ 为奇数，$\lambda^2-\lambda-1=0$、$\operatorname{ord}(\lambda)=n$，$\mu=1-\lambda=-\lambda^{-1}$；$Q=\langle\lambda\rangle$ 是非零平方子群，$-1$ 非平方。仍取 $A=(3-2\mu)/(\lambda-\mu)$、$B=(2\lambda-3)/(\lambda-\mu)$，$AB\ne0$、$a=A/B$，并固定 $\delta\ne0$。点 $v=(c,w)$ 表示同一差层的候选对 $((c,w),(c-1,w-\delta))$，定义

$$
\begin{aligned}
L_e(v;x)&=Ae c/x+Bxw,\\
L'_e(v;x)&=Ae(c-1)/x+Bx(w-\delta),\\
\operatorname{Sep}_e(v;x)&\Longleftrightarrow[L_e(v;x)=0]\ne[L'_e(v;x)=0],\\
J_\delta(c,w)&=(2c-1)w-c\delta,\qquad H=\{J_\delta=0\},\\
W_1&=H,\\
W_{r+1}&=W_r\cup\{v:\exists x\in Q\ \forall e\in\{1,-1\},\quad
\operatorname{Sep}_e(v;x)\ \lor\ v+(x,e/x)\in W_r\}.
\end{aligned}
$$

$H$ 是引理106.3的终端集；$W_r$ 是保留同一相位、实际符号及其后继的阶段证书层，区别于108.1等处的代数包络。置

$$
E_H=H\cup\{z:\exists x\in Q\ \exists e\in\{1,-1\},\quad z+(x,e/x)\in H\}.
$$

$E_H$ 只要求某一个后继终端，是代数外界，不是证书集；其定义没有替另一符号供应分离或延续。

**命题 111.2（任意有限终端锚定仍在外界内）。** 有 $W_2\subseteq E_H$。定义终端锚定闭包

$$
\begin{aligned}
D_0&=H,\\
D_{k+1}&=D_k\cup\{v:\exists x\in Q\ \exists e_0\in\{1,-1\},\quad
v+(x,e_0/x)\in H,\\
&\hspace{38mm}\forall e\in\{1,-1\},\quad
\operatorname{Sep}_e(v;x)\ \lor\ v+(x,e/x)\in D_k\}.
\end{aligned}
$$

则对每个有限 $k\ge0$，$D_k\subseteq E_H$，并且 $D_k\subseteq W_{k+1}$。

证明。取 $W_2$ 的一个见证相位。若两个后继都不在 $H$，递推迫使两个符号都分离；引理106.3的同相位双符号终端判据于是给 $v\in H$。否则至少一个后继在 $H$，也直接给 $v\in E_H$。旧点已在 $H$，故包含成立。对 $D_k$ 归纳：基底为 $H$；每个新增点按定义都有立即的 $H$ 后继，故在 $E_H$，不受另一分支深度影响。同一递推及 $H\subseteq W_{k+1}$ 再给 $D_{k+1}\subseteq W_{k+2}$。因此任意有限深度的这类锚定不能越出 $E_H$。证毕。

**定理 111.3（终端外界的每列都是真子集）。** 对每个 $C\in\mathbb F_p$，$(E_H)_C=\{w:(C,w)\in E_H\}\ne\mathbb F_p$。

证明。写 $U=2C-1$，并在分母非零时记 $h(C)=\delta C/(2C-1)$。该列的全部高度都来自 $h(C)$ 以及每个 $x\in Q$ 的两个提案 $h(C+x)-1/x,h(C+x)+1/x$；提案允许重复，$C+x=1/2$ 时没有终端目标。

若 $U=0$，本列没有 $H$ 点，至多 $2n=p-1$ 个提案。若 $U\in-2Q$，恰有一个奇异相位 $x=-U/2\in Q$；本列的终端提案加其余相位的提案至多 $1+2(n-1)=p-2$ 个。

剩下 $U\in2Q$。此时无奇异相位，恰有 $1+2n=p$ 个带重数提案。$Q$ 是 $X^n-1$ 的根集且 $n$ 为奇数，故多项式恒等式及其对 $U$ 的对数导数给出

$$
\prod_{x\in Q}(U+2x)=U^n+2^n,\qquad
\sum_{x\in Q}\frac1{U+2x}
=\frac{nU^{n-1}}{U^n+2^n}
=\frac n{2U}=-\frac1{4U}.
$$

这里 $U\in2Q$ 给 $U^n=2^n$，而域内 $n=-1/2$。利用 $h(C)=\delta/2+\delta/(2U)$，全部提案之和为

$$
\begin{aligned}
S_C
&=h(C)+\sum_{x\in Q}\left[h(C+x)-\frac1x+h(C+x)+\frac1x\right]\\
&=\delta\left(n+\frac12\right)+\frac\delta{2U}
+\delta\sum_{x\in Q}\frac1{U+2x}\\
&=\frac\delta{4U}\ne0.
\end{aligned}
$$

常数项正由 $n=-1/2$ 抵消。一个有 $p$ 项、覆盖整个 $\mathbb F_p$ 的多重集必须每个元素恰出现一次，其和为 $0$，与上式矛盾。$0,2Q,-2Q$ 穷尽 $U$，故每列均为真子集。证毕。

**推论 111.4（中点供应的条件性障碍）。** 若选定一列中的高度集 $S\subseteq(E_H)_C$ 含两个不同元素，则它不能对中点运算封闭。因此，只靠上述终端锚定并声称可在同列反复补中点，不能成为统一的整列完成供应者。

证明。若 $u\ne v$ 属于一个中点封闭集，将高度仿射归一化为 $0,1$。归纳二分给出每个 $m$ 的全部 $j/2^m$，$0\le j\le2^m$。取 $2^m\ge p-1$，前 $p$ 个 $j$ 的剩余类经非零缩放遍历 $\mathbb F_p$，故 $S=\mathbb F_p$，与111.3矛盾。这是对所假设同列闭包的条件性否定；没有断言 $E_H$ 对真正跨列的 $\Pi$ 封闭，也没有把其补集认作精确安全集 $K$。证毕。

**命题 111.5（实际层的首个逃逸二分）。** 若 $r$ 是 $W_r\setminus E_H\ne\varnothing$ 的最小层数，取 $z\in W_r\setminus E_H$ 及其递推见证相位 $x$，则 $r\ge3$。至少一个符号不分离，并沿同一个符号进入较早的非终端子点 $W_{r-1}\cap(E_H\setminus H)$。若恰有一个不分离符号，这是另一符号分离的混合门；若两个都不分离，这是两个非终端子点的同相位 $\Pi$ 门。

证明。111.2排除前两层；最小性保证 $z$ 是新点且 $W_{r-1}\subseteq E_H$。若两符号都分离，106.3给 $z\in H$，矛盾。每个不分离符号的子点都被递推迫入 $W_{r-1}$；它不能在 $H$，否则 $z\in E_H$。非分离符号数只能为一或二，给所述二分。

具体地，定义 $\rho_Q(t)$ 为 $\{t,-t\}$ 中唯一的平方元素，$t\ne0$。两个不同同列子点 $(C,u),(C,v)$ 的唯一合法前驱是

$$
\Pi(C,u,v)=\left(C-\rho_Q\!\left(\frac2{u-v}\right),\frac{u+v}{2}\right).
$$

因为 $-1$ 非平方，相位唯一；其两个后继正好为这两个点。第一坐标确实改变，所以这是跨列前驱，不是免费同列中点。对子点已有实际证书时该有向门可给前驱证书，但公式不授予逆门、任意补第三点或免费坐标动作。首个逃逸时两个子点还必须都非终端。证毕。

**命题 111.6（模十一的边界与一次实际跨越）。** 取

$$
p=11,\quad\lambda=4,\quad\mu=8,\quad A=6,\quad B=7,\quad a=4,
\quad\delta=1,\quad Q=\{1,3,4,5,9\}.
$$

同列实际证书 $(4,10),(4,2)$ 的中点 $(4,6)$ 不在 $E_H$，但合法 $\Pi$ 前驱为 $(1,6)$。另有 $z=(10,0)\in W_3\setminus E_H$，由混合门越出终端外界；以下只给这些点的有限证书。

证明。$(4,10)\in H$ 在 $x=4$ 的正、负标量对分别为 $(0,9),(10,0)$，均分离。$(4,2)\notin H$ 在 $x=1$ 的正号对为 $(5,3)$，其后继 $(5,3)\in H$；负号对为 $(1,0)$，分离。终端 $(5,3)$ 在 $x=5$ 的正、负对为 $(1,0),(0,8)$，所以 $(4,2)$ 确为实际 $W_2$。

中点 $(4,6)$ 有 $J_1=5\ne0$，其终端后继条件是 $(5+2e)x+7e=0$。正、负号分别迫使 $x=10,6$，均非平方：$10=-1$，且 $4^2=5$、$6=-5$，而 $-1$ 非平方。因此中点不在 $H$ 或 $E_H$。两证书点的高度差为8，$2/8=3\in Q$，于是 $\Pi(4,10,2)=(1,6)$，在 $x=3$ 的两后继恰为 $(4,10),(4,2)$；这不把 $(4,6)$ 加入原列。

为给实际跨越保留两个子点的资格，先直接核对 $(4,9)$：在 $x=5$ 正号对为 $(3,2)$，后继 $(9,7)\in H$；负号对为 $(0,8)$，分离，故 $(4,9)\in W_2\setminus H$。对 $z=(10,0)$ 取 $x=5$，正号对为 $(1,0)$，分离，后继 $(4,9)$；负号对为 $(10,7)$，不分离，继续到 $(4,2)$。两个子点均为实际 $W_2$ 且均非终端，故 $z\in W_3$。又 $J_1(z)=1$，正、负号的终端后继方程分别为 $x^2-3x+3=0$、$x^2+x+8=0$，判别式8、2均非平方，故 $z\notin E_H$。这里承重的是混合门：正号已分离，其非终端后继虽有证书，却不是必须继续的分支。这是有限跨越桥，不是统一的双非终端或混合供应。证毕。

本节是接续106.3、107.1、107.12及式(110.15)的仓内理论综合推导（`repo-derived`）。终端锚定的外界和首个逃逸的必要门型没有供应统一的双非终端／混合门，没有取得满足106.2消费者的完成列，也没有构造精确 $K$、排除全部非空 $K$ 或完成一般恢复。$R/G/T$ 仍逐原语付费，每条实际执行始终来自同一固定来源，两候选按共同历史运输，初始标签不可改写；代数换元与有向前驱不授予免费逆动作。有限模十一证书不新增物理 CRT 桥，不主张 Lean 核验或整体目标完成。

## 111.99 追加锚

## 112. 完成边界、实际来源与剥离闭合

前面的二叶生成层说明关系项怎样产生；本节把它接到一个更具体的边界问题：有限观察的完成是否仍是实际来源，及一个看似足够的粗边界能否承载后续剥离。所用的 Fibonacci 来源完成、远端补偿和剥离公式见 [FIB 来源联合完成与剥离动力学](FIB_SOURCE_COMPLETION_DYNAMICS.md) 第 2—4 节。这里把它们重写成动态边界判据的一个实例。

### 定义 112.1（有限来源的联合完成）

令

$$
\Omega=\{\omega\in\{0,1\}^{\mathbb N}:\omega_j\omega_{j+1}=0\},
\qquad
G=\widehat{\mathbb Z}^{2},
\qquad
K=\Omega\times G.
$$

其中 $G$ 是按全部模数的逆极限，$\iota:\mathbb Z^2\hookrightarrow G$ 是标准嵌入。有限实际来源的联合像记为

$$
\Gamma_{\mathrm{fin}}
=\{(b,\iota(x(b))):b\text{ 合法且最终为零}\}\subset K.
$$

对合法长度 $L$ 的前缀和模数 $m\ge1$，定义有限观察

$$
Q_{L,m}(\omega,z)
=\bigl(\omega\!\upharpoonright_L,\ z\bmod m\bigr).
\tag{112.1}
$$

这里的 $z$ 是组成边界，不是把所有未读地址位都免费放入观察者记忆。

本节中组成坐标的两个单位方向记为

$$
\mathbf a=(1,0)^{\mathsf T},
\qquad
\mathbf b=M\mathbf a=(0,1)^{\mathsf T}.
$$

粗体记号用于避免与生成语法中的叶子 $\alpha,\beta$ 混淆；这里只是由叶子计数得到的坐标解释。

### 命题 112.2（有限观察的联合满像与真实来源的稠密性）

设 $W_L$ 是长度 $L$ 的合法二进制词集合。则

$$
\operatorname{im}\bigl(Q_{L,m}\!\upharpoonright_{\Gamma_{\mathrm{fin}}}\bigr)
=W_L\times(\mathbb Z/m\mathbb Z)^2.
\tag{112.2}
$$

因而 $\Gamma_{\mathrm{fin}}$ 在 $K$ 中稠密，但它是 $K$ 的真子集。特别地，任何给定的有限前缀和有限多个模读数，都同时由一个实际有限来源以及一个在任意远处还含非零位的实际有限来源实现。

**证明。** 把所有模数并入一个模 $m$。给定合法前缀 $p$ 和目标余数 $r\in(\mathbb Z/m\mathbb Z)^2$，取 $M$ 在模 $m$ 下的有限阶，并在前缀之后足够远的位置按该阶的倍数放置彼此不相邻的 $1$。分别用位置 $N+iT$ 和 $N+(A+j)T+1$ 贡献 $A\mathbf a$ 与 $B\mathbf b$，即可补出任意 $r-t_p\equiv A\mathbf a+B\mathbf b\pmod m$。若还要求在任意远处保留非零尾而 $A=B=0$，就在更高位置加入 $m$ 个相隔 $T$ 的 $\mathbf a$ 位；其总贡献为 $m\mathbf a\equiv0\pmod m$。所有新增位都可推到任意远处，且不改变给定前缀。于是每个有限基本开集都命中 $\Gamma_{\mathrm{fin}}$，得到稠密性。另一方面，$\Gamma_{\mathrm{fin}}$ 只含最终为零的地址，而 $K$ 还含无限支持地址，故为真子集。$\square$

这个结论区分了两个常被合并的对象：

$$
\text{有限观察的一致完成}=K,
\qquad
\text{实际有限来源}=\Gamma_{\mathrm{fin}}.
$$

逆极限给出相容有限读数的载体，却不自动给出实际来源的存在性。若观察者需要证明 `End` 或“未读部分全为零”，就必须增加终止证书；有限前缀和模余数本身不能承担这一读数。

### 定义 112.3（剥离过程与粗边界）

令 $\sigma$ 为地址左移，并定义完整剥离

$$
\delta(\omega,z)
=\bigl(\sigma\omega, M^{-1}(z-\omega_0\mathbf a)\bigr).
\tag{112.3}
$$

只保留当前首位和当前组成坐标的粗边界为

$$
\Pi:K\to\{0,1\}\times G,
\qquad
\Pi(\omega,z)=(\omega_0,z).
\tag{112.4}
$$

### 定理 112.4（首位—组成边界不具有剥离闭合）

不存在任何映射 $\bar\delta$ 使

$$
\Pi\circ\delta=\bar\delta\circ\Pi.
\tag{112.5}
$$

这个结论甚至不依赖连续性。

**证明。** 取

$$
p=(0^\infty,z),
\qquad
p'=(010^\infty,z).
$$

二者都合法，且 $\Pi(p)=\Pi(p')=(0,z)$。但由式(112.3)，

$$
\Pi\delta(p)=(0,M^{-1}z),
\qquad
\Pi\delta(p')=(1,M^{-1}z).
$$

同一个粗边界要求两个不同后继，故 $\bar\delta$ 不存在。$\square$

这正是边界下降条件

$$
\eta_{\Sigma'}T=\bar T\eta_\Sigma
$$

失败的具体实例。算术坐标没有丢失，失败来自下一位地址仍会影响后继；因此“当前数值加一个当前符号”并不等于动态充分状态。

### 命题 112.5（有限剥离视界与完整未来核）

对 $N\ge0$ 定义

$$
\eta_N(\omega,z)=\bigl(\omega\!\upharpoonright_{N+1},z\bigr).
\tag{112.6}
$$

则每个 $\delta^j$ 的首位读数和组成更新，在 $0\le j\le N$ 的有限任务上都因子化到 $\eta_N$；但 $\eta_N$ 对包含第 $N+1$ 次剥离首位读数的任务不充分。

**证明。** 直接迭代式为

$$
\delta^j(\omega,z)
=\left(\sigma^j\omega,
M^{-j}\left(z-\sum_{i<j}\omega_iM^i\mathbf a\right)\right).
\tag{112.7}
$$

所以前 $N+1$ 位和 $z$ 决定 $j\le N$ 的所有首位、合法性和组成读数。若两个地址在前 $N+1$ 位相同而第 $N+1$ 位不同，则它们有相同 $\eta_N$，但 $\delta^{N+1}$ 后的首位读数不同。故该任务不能在 $\eta_N$ 上定义单值后继。$\square$

这给出一个明确的核塔：有限视界可以使用有限前缀边界，完整剥离任务则要求交集

$$
\bigcap_{N\ge0}\ker\eta_N
$$

不再合并任何地址区别。若允许的脚本可以在任意深度剥离并以受守卫的添位操作读取首位，那么完整脚本迹恰好恢复全部有限前缀与全部模余数；在相应的紧致 Hausdorff 合同中，任何忠实承载全部脚本迹的连续商都必须保留 $K$ 的全部点。这个最小性只属于声明的脚本族，不是任意任务的普遍无压缩定理。

### 推论 112.6（空间、时间与记忆的同一接口）

在这个实例中，地址 $\omega$、组成坐标 $z$ 和剥离次数 $j$ 不是三套外加宇宙：

$$
\text{地址关系}\;+
\text{组成运输}\;+
\text{剥离接续}
$$

共同定义一个过程。把 $\omega$ 截成前缀是空间式边界，把 $\delta$ 的迭代索引当作时间式记录，把 $\eta_N$ 存入寄存器是记忆式表达。它们只有在对应的未来响应对边界纤维保持常值时才能互相恢复；任意一个粗化若违反式(112.5)，就只能作为当前读数摘要，不能作为可继续运行的内部状态。

本节复用了 Fibonacci 来源完成卷的普通数学结果，新增的是它与动态边界交换条件、有限视界核塔和实际来源/完成点区分的接口；没有新增 Lean 声明，也没有把完成空间 $K$ 宣称为物理时空。

## 112.99 追加锚

## 113. Fibonacci 两叶生成基与动态边界的层次

本节把母卷的 `FIBONACCI_ATOMIC_RELATION_GENERATION` 放到局部过程—边界模型的最底层。结论是：它确实比后续的数量商、素数切面和观察者边界更基础，但“只有两个不可约关系”须作语法上的精确定义。

### 定义 113.1（两叶自由关系语法）

令

$$
\mathcal T\;::=\;\alpha\mid\beta\mid\langle t,t\rangle .
\tag{113.1}
$$

等价地，$\mathcal T$ 是多项式函子

$$
X\longmapsto \{\alpha,\beta\}\sqcup(X\times X)
$$

的初始代数。这里有两个零元生成元 $\alpha,\beta$，以及一个有序二元构造器 $\langle-,-\rangle$。因此严格说，最小语法基的生成型是

$$
\boxed{\text{两个叶生成元}+\text{一个二元配对构造器}.}
$$

如果“关系”只指不可再拆的叶标签，那么可以说底层只有两类原子关系；如果“关系”还包括怎样把它们接起来，则不能删去第三项。没有指定二元构造器的解释，$\alpha,\beta$ 只是两个符号，并不自动形成过程、时间次序或算术。

### 命题 113.2（生成层、动力学层与观察层不可混同）

对任意集合 $X$、两个元素 $a,b\in X$ 和二元运算 $\mu:X\times X\to X$，存在唯一解释

$$
\operatorname{Eval}_{a,b,\mu}:\mathcal T\to X
$$

满足

$$
\operatorname{Eval}(\alpha)=a,\qquad
\operatorname{Eval}(\beta)=b,\qquad
\operatorname{Eval}(\langle s,t\rangle)=\mu(\operatorname{Eval}(s),\operatorname{Eval}(t)).
\tag{113.2}
$$

于是至少有五个不同层次：

| 层次 | 对象 | 作用 |
| --- | --- | --- |
| 生成语法 | $\alpha,\beta,\langle-,-\rangle$ | 产生有限有序关系树 |
| 合法动力学 | $\rho(\alpha)=\beta,\ \rho(\beta)=\langle\beta,\alpha\rangle$ | 指定允许的局部替换 |
| 组成摘要 | $c(t)\in\mathbb N^2$、$M$ | 忘记叶序与括号，保留两类计数 |
| 数量观察 | $q(\alpha)=2,\ q(\beta)=3$ | 选定一个外部读数商 |
| 动态边界 | $\eta$、$\mathcal H_\Sigma$ | 判断哪些历史可合并并继续接续 |

因此，Fibonacci 卷最基础的地方在于它先固定了一个可递归生成的关系语言；$M$、$q$、素数性和边界响应都是在这个语言上附加的结构。

### 定理 113.3（Fibonacci 替换是生成语法上的一个内部过程）

令 $\rho$ 由

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,
\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle
$$

定义。则 $T_j=\rho^j(\alpha)$ 满足

$$
T_{j+2}=\langle T_{j+1},T_j\rangle .
\tag{113.3}
$$

这说明 Fibonacci 结构不是先在外部放入一个数列，再把数列贴到关系上；它是同一生成语法内部的一项合法过程。组成映射 $c$ 才把这项过程投影为

$$
c(\rho(t))=Mc(t),qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

**边界：** (113.3) 只说明生成和替换；它没有说明数量商能恢复原树，也没有说明任意过程都能由 $\rho$ 产生。含引用、环、失败标签或权限条件的过程仍需在解释对象 $X$ 和合法操作中另行声明。

### 定理 113.4（两叶不能被任意动态边界合并）

设 $\eta$ 是某个任务的边界摘要，$\alpha,\beta$ 被视为两个实际初始配置。若存在允许的后续实验 $E$ 使

$$
\operatorname{Obs}(E[\alpha])\ne\operatorname{Obs}(E[\beta]),
$$

则任何动态充分边界都满足

$$
\eta(\alpha)\ne\eta(\beta).
\tag{113.4}
$$

反之，只有当所有声明的未来实验在这两个叶纤维上具有相同合法性、输出、失败标签和记录时，才可把它们放入同一行为类。

**证明。** 若 $\eta(\alpha)=\eta(\beta)$ 而 $\eta$ 对后续操作闭合，则同一个边界后继必须给出同一个指定实验结果；这与所取实验 $E$ 的两个不同读数矛盾。反向是未来行为等价的定义。$\square$

这一定理把“不可约”从直觉词变成了任务相关判据：$\alpha,\beta$ 在生成语法中是不同叶，在某个任务的行为商中是否仍不可合并，则由未来实验决定。

### 推论 113.5（数量关系不是底层等式）

母卷中的

$$
2\beta\sim_q3\alpha
$$

只能是数量观察的商关系，不能提升为 $\mathcal T$ 中的原始等式。若把它当作同时受 $\rho$ 保持的语法等式，则由

$$
\rho(\alpha)=\beta,\qquad \rho(\beta)=\langle\beta,\alpha\rangle
$$

得到相应交换组成的塌缩；在母卷给定的交换模型中最终只能得到零解。故正确的层次顺序是

$$
\boxed{
\text{两叶语法}
\;\longrightarrow\;
\text{有序配对与替换}
\;\longrightarrow\;
\text{组成投影}
\;\longrightarrow\;
\text{数量商}.
}
\tag{113.5}
$$

把最后一项误放回第一层，会把一个丢失结构的读数等价误报成来源本体的等式。

### 推论 113.6（与观察者—边界模型的接合）

在局部过程模型中，可把一棵 $t\in\mathcal T$ 解释为一个有限过程片段，把 $\langle s,t\rangle$ 解释为指定的接口拼接，把 $\rho$ 解释为一项合法局部操作。于是边界更新仍须满足

$$
\eta_{\Sigma'}T_a=\overline T_a\eta_\Sigma,
$$

或在响应核上满足

$$
P_{r'}K_e=\overline K_eP_r.
$$

仅保存 $c(t)$ 或 $q(c(t))$，一般只保留组成任务所需的关系；它们忘记了叶序、括号、失败路径和可能影响后续操作的共同来源。只有当这些被忘记的区别在声明任务的全部未来行为上恒定时，数量摘要才是合法边界。

在第 112 节的完成—剥离实例中，$\alpha,\beta$ 可以作为组成坐标的两个有限生成方向，但完成空间 $\widehat{\mathbb Z}^{\,2}$、地址的无限尾和剥离视界仍是更高层对象。两叶生成基因此是**构造起点**，不是对所有观察者状态、所有完成点或所有关系网络的完整枚举。

本节的层次判断是仓内理论综合：它复用 Fibonacci 卷 §§2–5 的自由树、替换、组成和数量商，以及本卷的动态充分边界条件；没有新增 Lean 声明，也不把两叶生成基宣称为物理时空或原胞自动机。

## 113.99 追加锚

## 114. 表示核判据与生成秩下界

本节把空间、时间、边界和记忆的互相恢复写成同一个核判据，并给出“保留两条独立组成方向”时的最小生成秩。组成读数可以精确恢复组成商，但它不自动保留有序过程的顺序与括号。

### 定义 114.1（表示核与共同载体）

令 $S$ 为共同来源，表示

$$
r_i:S\to R_i,
\qquad
K_i=\ker r_i:=\{(s,t)\in S\times S:r_i(s)=r_i(t)\}.
$$

在实际像 $r_i(S)$ 上定义候选转换

$$
t_{ij}:r_i(S)\to r_j(S),
\qquad
t_{ij}(r_i(s)):=r_j(s).
\tag{114.1}
$$

### 定理 114.2（核包含、互相恢复与动态自然性）

候选转换 (114.1) 良定义当且仅当

$$
K_i\subseteq K_j.
\tag{114.2}
$$

因此 $r_i$ 与 $r_j$ 互相可恢复（即 $t_{ij}$ 与 $t_{ji}$ 都良定义且互为逆）当且仅当

$$
K_i=K_j=:K.
\tag{114.3}
$$

在此情形，一族表示若具有同一个核，就共同因子化经过商载体 $S/K$：

$$
\bar r_i:S/K\longrightarrow r_i(S),
\qquad
\bar r_i([s])=r_i(s),
$$

且每个 $\bar r_i$ 都是双射，转换满足 $t_{ij}=\bar r_j\circ\bar r_i^{-1}$。

若 $a$ 是共同合法动作，$T_a$ 是其在 $S$ 上的作用，且各表示上的下降作用满足

$$
\bar T_{i,a}\circ r_i=r_i\circ T_a,
\qquad
\bar T_{j,a}\circ r_j=r_j\circ T_a,
$$

则互相恢复的动态自然性条件为

$$
\boxed{\quad t_{ij}\circ\bar T_{i,a}
=\bar T_{j,a}\circ t_{ij}.\quad}
\tag{114.4}
$$

若动作是部分定义的，上式还要求表示之间运输同一个合法域、失败标签、输出标签、记录和选择器：若 $D_{i,a}$ 是表示 $i$ 的合法域，则

$$
t_{ij}(D_{i,a})=D_{j,a},\qquad
O_{j,a}\circ t_{ij}=O_{i,a},\qquad
t_{ij}\circ U_{i,a}=U_{j,a}\circ t_{ij},\qquad
\pi_j\circ t_{ij}=\pi_i.
\tag{114.13}
$$

这些等式在相应的实际像上比较；失败、记录和权限也必须包含在 $O$ 或 $U$ 的标签中，不能只要求两个表示在交集上恰好都有定义。

**证明。** 若 $K_i\subseteq K_j$ 且 $r_i(s)=r_i(t)$，则 $(s,t)\in K_i$，从而 $(s,t)\in K_j$，故 $r_j(s)=r_j(t)$，所以 (114.1) 与代表元无关。反之，若 (114.1) 良定义，任取 $(s,t)\in K_i$，由 $r_i(s)=r_i(t)$ 得 $r_j(s)=t_{ij}(r_i(s))=t_{ij}(r_i(t))=r_j(t)$，故 $(s,t)\in K_j$。这证明了 (114.2) 的充要性。

若两个转换互为逆，则各自良定义，(114.2) 对 $(i,j)$ 和 $(j,i)$ 同时成立，因而 $K_i=K_j$。反过来，若 $K_i=K_j$，两转换都良定义，并且

$$
t_{ji}(t_{ij}(r_i(s)))=t_{ji}(r_j(s))=r_i(s),
\qquad
t_{ij}(t_{ji}(r_j(s)))=r_j(s),
$$

所以它们互为逆。共同因子化由核的定义给出；将下降方程代入 $t_{ij}\circ\bar T_{i,a}\circ r_i$ 与 $\bar T_{j,a}\circ t_{ij}\circ r_i$，再利用 $r_i(S)$ 上的满射性，得到 (114.4)。证毕。$\square$

这一定理应用于四种表达时，$K$ 必须是同一个任务核；若组成摘要删去了任务要求的失败、权限、顺序或括号信息，它的核就会更粗，不能据此声称动态的四表达恢复。

### 推论 114.3（有限共同任务商上的四图表恢复）

采用 §42.7 的有限实际来源：$S$ 有限，$W$ 是带完整输出、失败、记录和后继标签的有限动作词族，

$$
\Phi_W(s)=\bigl(\operatorname{Resp}(s,w)\bigr)_{w\in W},
\qquad
K=\ker\Phi_W,
\qquad
q:S\to Q=S/K.
\tag{114.14}
$$

令 $S=\bigcup_iS_i$，$S_{ij}=S_i\cap S_j$，其中 $S_i\subseteq S$ 为空间、时间、边界和记忆四个局部来源；取 $e_i:S_i\to R_i$ 满足

$$
\ker e_i=\ker(q|_{S_i}),
\qquad Q_i=q[S_i].
\tag{114.15}
$$

若 $Q_i=Q$，各实际重叠 $S_{ij}$ 对 $K$ 饱和，且所有声明后继的实际像闭合，则

$$
d_i(e_i(s))=q(s),
\qquad
t_{ij}=d_j^{-1}\circ d_i
\tag{114.16}
$$

在实际重叠像上给出四种表达之间的双射。它们满足三重重叠上的 cocycle；若再满足 (114.13) 的合法域、失败、输出、记录、选择器和后继运输，则得到 §42.7 的动态自然性。实际来源闭路上的运输为恒等；形式接口若要得到同样结论，还必须另加商上的 holonomy 平凡和来源像闭合。

若某个 $Q_i$ 只是 $Q$ 的真子集，或者实际后继把一个图表像送出其声明来源，则只能得到局部图册，不能声称四种表达在同一个全局任务商上互相恢复。

### 定义 114.3（零元原子与有序二元组合）

令 $A$ 为有限原子集合，签名只有零元原子和有序二元组合：

$$
\mathcal T_A::=a\ (a\in A)\mid\langle u,v\rangle.
$$

令 $G$ 为自由阿贝尔群，组成映射 $c:\mathcal T_A\to G$ 满足

$$
c(\langle u,v\rangle)=c(u)+c(v).
\tag{114.5}
$$

任务要求恢复两条独立组成方向，记为

$$
\operatorname{rank}_{\mathbb Z}\langle c(\mathcal T_A)\rangle\ge 2.
\tag{114.6}
$$

### 定理 114.4（生成秩下界与两原子实现）

对任意这样的签名，

$$
\operatorname{rank}_{\mathbb Z}\langle c(\mathcal T_A)\rangle\le |A|.
\tag{114.7}
$$

特别地，单原子 $A=\{\gamma\}$ 只能产生秩至多 $1$；若 $c(\gamma)$ 为零，秩更低。两原子可以达到秩 $2$：取 $A=\{\alpha,\beta\}$、$G=\mathbb Z^2$，并令

$$
c(\alpha)=(1,0),
\qquad
c(\beta)=(0,1).
\tag{114.8}
$$

此时 $c(\mathcal T_A)$ 生成整个 $\mathbb Z^2$。

**证明。** 令 $\ell_a(t)$ 为项 $t$ 中原子 $a$ 的出现次数。对项的结构作归纳，得到

$$
c(t)=\sum_{a\in A}\ell_a(t)c(a).
\tag{114.9}
$$

所以生成子群由至多 $|A|$ 个元素 $c(a)$ 生成，秩至多 $|A|$；单原子时它包含在循环群 $\mathbb Zc(\gamma)$ 中。取 (114.8) 时，两个叶项已经给出标准基，故生成子群正是 $\mathbb Z^2$，达到秩 $2$。证毕。$\square$

### 定理 114.5（已有两次数量恢复公式的 Fibonacci 特例）

这是前文已有组成—替换读数恢复的一个具体特例；它只说明代数上的恢复，不提供付费观测、来源取得或物理执行接口。在 $G=\mathbb Z^2$ 上写组成向量 $v=(a,b)^{\mathsf T}$，取

$$
q=(2,3),
\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad
qM=(3,5).
$$

两次读数的矩阵为

$$
H=\begin{pmatrix}2&3\\3&5\end{pmatrix},
\qquad
\det H=1,
\qquad
H^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
\tag{114.10}
$$

因此 $q(v)$ 与 $q(Mv)$ 唯一恢复 $v$：若读数为 $(x,y)^{\mathsf T}$，则

$$
\begin{pmatrix}a\\b\end{pmatrix}
=H^{-1}\begin{pmatrix}x\\y\end{pmatrix}
=\begin{pmatrix}5x-3y\\-3x+2y\end{pmatrix}.
\tag{114.11}
$$

**证明。** 直接乘法给出 $(2,3)M=(3,5)$，且 $10-9=1$，故 $H$ 在 $\mathbb Z^2$ 上可逆，(114.11) 即为恢复公式。$\square$

### 命题 114.6（数量与组成摘要遗忘顺序和括号）

令

$$
t_{12}=\langle\alpha,\beta\rangle,
\qquad
t_{21}=\langle\beta,\alpha\rangle.
$$

加法组成给出

$$
c(t_{12})=c(t_{21})=(1,1),
$$

所以它们的数量读数 $q(c(t))$、$q(Mc(t))$ 以及由这些读数计算出的组成未来族

$$
\bigl\{q(M^k c(t)):k\ge0\bigr\}
$$

都相同。但是有序过程读取区分它们：

$$
\operatorname{Obs}_{\mathrm{ord}}(t_{12})=(\alpha,\beta)
\ne(\beta,\alpha)=\operatorname{Obs}_{\mathrm{ord}}(t_{21}).
\tag{114.12}
$$

括号也会被遗忘。例如

$$
\langle\langle\alpha,\beta\rangle,\alpha\rangle
\quad\text{与}\quad
\langle\alpha,\langle\beta,\alpha\rangle\rangle
$$

都有组成 $(2,1)$，却有不同的二叉括号结构。故数量/组成摘要不能自动恢复完整过程；只有把顺序、括号及其他任务要求的事件标签加入共同任务核，四表达才可能按定理 114.2 动态互相恢复。

本节是理论综合，未新增 Lean。

## 114.99 追加锚

## 115. 关系的关系：箭头核与无伪拼接

第 114 节只比较同一共同来源的状态表示。可是，即使四种表示的状态核相同，表示中的事件关系仍可能不同：一个表示可以把两个动作、失败原因或记录合并，而另一个表示仍能区分它们；把相邻两条粗边拼起来时，还可能产生一个实际不存在的中间来源。本节把这两个缺口分别写成箭头核和无伪拼接条件。

### 定义 115.1（带类型的事件关系与路径复合）

对每一对接口类型 $i,j$，令 $S_i,S_j$ 为状态来源，$A_{ij}$ 为完整事件标签集。标签可以同时携带动作身份、正常输出、失败原因、记录、费用和历时；若失败本身是一次可记录事件，则它必须出现在标签中或落到显式终止状态，不能被当作缺失事件。

令

$$
E_{ij}\subseteq S_i\times A_{ij}\times S_j
\tag{115.1}
$$

为合法事件关系。相邻事件的实际路径复合定义为

$$
E_{jk}\star E_{ij}
=\left\{
(s,(a,b),t):
\exists u,\ (s,a,u)\in E_{ij},\
(u,b,t)\in E_{jk}
\right\}.
\tag{115.2}
$$

中间状态 $u$ 是同一实际来源的见证；因此 (115.2) 保留事件标签的顺序，而不是只保留两个端点。

一个表示 $\ell$ 给出端点映射

$$
r_\ell^i:S_i\to R_\ell^i,\qquad
r_\ell^j:S_j\to R_\ell^j
$$

以及标签映射 $\lambda_\ell^{ij}:A_{ij}\to\Lambda_\ell^{ij}$。其事件箭头为

$$
F_\ell^{ij}(s,a,t)
=
\bigl(r_\ell^i(s),\lambda_\ell^{ij}(a),r_\ell^j(t)\bigr),
\qquad
K_\ell^{ij}:=\ker F_\ell^{ij}.
\tag{115.3}
$$

因此，事件核同时记录端点、事件标签和后继；只比较 $\ker r_\ell^i$ 与 $\ker r_\ell^j$ 只是在比较事件的两个端点。

对可复合的实际路径，直接使用二步路径箭头（不把标签对预先压成某个单步标签集）：

$$
F_{\ell,\mathrm{path}}^{ij,jk}\bigl(s,(a,b),t\bigr)
=
\bigl(r_\ell^i(s),(\lambda_\ell^{ij}(a),\lambda_\ell^{jk}(b)),r_\ell^k(t)\bigr).
\tag{115.4}
$$

### 定理 115.2（箭头核的恢复判据）

在实际事件像上定义候选箭头转换

$$
\Theta_{\ell m}^{ij}:F_\ell^{ij}(E_{ij})\to F_m^{ij}(E_{ij}),
\qquad
\Theta_{\ell m}^{ij}\bigl(F_\ell^{ij}(e)\bigr)
=F_m^{ij}(e).
\tag{115.5}
$$

则 $\Theta_{\ell m}^{ij}$ 良定义当且仅当

$$
K_\ell^{ij}\subseteq K_m^{ij}.
\tag{115.6}
$$

两个表示在该事件接口上互相恢复，当且仅当

$$
K_\ell^{ij}=K_m^{ij}.
\tag{115.7}
$$

**证明。** 与定理 114.2 相同。若两个实际事件在 $\ell$ 中有相同箭头，则由 (115.6) 得核包含，故 (115.5) 的候选转换与代表元无关。反向取两个具有相同 $\ell$ 箭头的事件即可得到核包含。双向良定义等价于两个核互相包含，因而等价于相等。$\square$

### 命题 115.3（状态互恢复不推出事件互恢复）

取

$$
S_i=\{s\},\qquad S_j=\{x\},\qquad
E_{ij}=\{(s,a,x),(s,b,x)\}.
\tag{115.8}
$$

令两个表示在端点上都取单点映射。表示 $\ell$ 把两个标签合并为

$$
\lambda_\ell^{ij}(a)=\lambda_\ell^{ij}(b)=*,
$$

而表示 $m$ 保留两个标签：

$$
\lambda_m^{ij}(a)=a,\qquad
\lambda_m^{ij}(b)=b.
$$

于是两个状态核都为全关系，但

$$
F_\ell^{ij}(s,a,x)=F_\ell^{ij}(s,b,x),
\qquad
F_m^{ij}(s,a,x)\ne F_m^{ij}(s,b,x).
$$

所以 $K_\ell^{ij}\not\subseteq K_m^{ij}$，从合并标签恢复保留标签的箭头转换不存在。状态层的互恢复因此不足以恢复事件层；失败、记录、费用或时钟只要有一项被合并，同样会产生这个缺口。

### 定义 115.4（表示中的边复合）

对两个相邻的表示事件像，定义粗边复合 $\star_\ell$ 为集合

$$
\left\{
\bigl(r_\ell^i(s),(\lambda_\ell^{ij}(a),\lambda_\ell^{jk}(b)),r_\ell^k(t)\bigr):
e_1=(s,a,u)\in E_{ij},\
e_2=(v,b,t)\in E_{jk},\
r_\ell^j(u)=r_\ell^j(v)
\right\},
\tag{115.9}
$$

其中第一条粗边的终点等于第二条粗边的起点。这里的相等只是在中间表示 $R_\ell^j$ 中成立，并不自动给出同一个实际中间状态。

### 命题 115.5（无伪拼接条件）

对每个表示 $\ell$，实际路径的粗像总有自然包含

$$
F_{\ell,\mathrm{path}}^{ij,jk}(E_{jk}\star E_{ij})
\subseteq
F_\ell^{jk}(E_{jk})\star_\ell F_\ell^{ij}(E_{ij}).
\tag{115.10}
$$

等号成立，当且仅当每一对中间粗值相同的相邻粗边，都存在一个共同实际中间来源，使它们分别由具有相同粗像的两条实际边产生。换言之，若

$$
e_1=(s,a,u)\in E_{ij},\qquad
e_2=(v,b,t)\in E_{jk}
$$

在表示 $\ell$ 中可以拼接，即 $r_\ell^j(u)=r_\ell^j(v)$，则必须存在 $w$ 以及实际边 $e_1',e_2'$，使

$$
e_1'=(s',a',w),\qquad
e_2'=(w,b',t'),
$$

并且

$$
F_\ell^{ij}(e_1')=F_\ell^{ij}(e_1),\qquad
F_\ell^{jk}(e_2')=F_\ell^{jk}(e_2).
\tag{115.11}
$$

**证明。** 实际路径带有同一个中间见证 $u$，所以它的粗像一定属于右侧，得到 (115.10)。反向包含正是 (115.11) 所要求的共同中间见证；逐条替换即可把任意粗边对提升为一条实际路径。$\square$

### 反例 115.6（逐边恢复仍可能产生四条伪路径）

令

$$
\begin{aligned}
S_0&=\{u,v\},&
S_1&=\{p,q\},&
S_2&=\{z,w\},\\
E_{01}&=\{(u,a,p),(v,a,q)\},&
E_{12}&=\{(p,b,z),(q,c,w)\}.
\end{aligned}
\tag{115.12}
$$

取粗中间表示 $r(p)=r(q)=*$，端点表示保持区分，标签保持不变。则两层粗边为

$$
\{(u,a,*),(v,a,*)\},
\qquad
\{(*,b,z),(*,c,w)\}.
\tag{115.13}
$$

在粗图中可以拼出四条路径：

$$
(u,(a,b),z),\quad
(u,(a,c),w),\quad
(v,(a,b),z),\quad
(v,(a,c),w).
\tag{115.14}
$$

但实际路径只有

$$
(u,(a,b),z),\qquad
(v,(a,c),w).
\tag{115.15}
$$

因此逐条边的核相等仍不保证路径关系可恢复；中间共同来源或等价的无伪拼接条件是独立义务。

### 定理 115.7（关系的关系何时下降）

设一族表示在每个类型化事件接口上满足箭头核相等，在每对相邻接口上满足无伪拼接 (115.10) 的等号条件，并且标签词的串接结合。若选择器或更新依赖端点状态，还要求它们在相应状态核纤维上常值。则：

1. 该接口声明要保留的合法事件、失败标签、输出、记录、费用、历时和后继都可在箭头商上定义；若还要求恢复原始完整标签，则原始事件核必须同时被保留；
2. 长路径的复合与表示无关，且由二步复合递归得到；
3. 若选择器、writer 或观察者更新在箭头核纤维上常值，则它们在共同边界上下降。

反过来，若任务要求粗表示上的完整长度二关系（包括存在性、标签、失败、记录和后继）恰等于粗边关系的复合，则 (115.10) 的反向包含是必要的；仅要求某个较粗的读数单值，并不足以推出无伪拼接。若同一粗箭头要求两个不同的所声明标签或后继，则 (115.6) 的核包含必然失败。

这给出三层关系的最小检查顺序：

$$
\boxed{
\text{状态核}
\;\longrightarrow\;
\text{箭头核}
\;\longrightarrow\;
\text{路径无伪拼接}.
}
\tag{115.16}
$$

它与仓内 HistoryPayloadFactorization、CausalStateFactorization、TemporalComposition 和 ControlledBehaviorUniversality 的接口方向一致，但本节是理论综合，未新增 Lean 声明。

## 115.99 追加锚

## 116. 任意长度路径核、递归核塔与四表达恢复

第 115 节把状态核、事件箭头核和二步无伪拼接分开。下一步必须把“二步可以拼接”提升为任意有限长度的路径条件，并把有限观察、实际来源和四种表达放进同一条核塔。以下仍在带类型的有限或一般集合模型中讨论；没有把这些推导宣称为物理定律，也没有新增 Lean 声明。

### 116.1 类型化路径的实际纤维积

取一列接口集合

$$
S_0,S_1,\ldots,S_n
$$

以及带事件标签的关系

$$
E_i\subseteq S_{i-1}\times A_i\times S_i,
\qquad 1\le i\le n.
$$

把 $(s_{i-1},a_i,s_i)\in E_i$ 简写为 $e_i$，并记其首尾为 $\partial^-e_i=s_{i-1}$、$\partial^+e_i=s_i$。长度 $n$ 的实际路径是沿共同实际中间状态作纤维积：

$$
\boxed{
P_n
:=
E_1\mathbin{\times_{S_1}}E_2
\mathbin{\times_{S_2}}\cdots
\mathbin{\times_{S_{n-1}}}E_n
}
$$

即

$$
P_n=
\left\{
(e_1,\ldots,e_n):
\partial^+e_i=\partial^-e_{i+1}
\text{ 对所有 }i<n
\right\}.
\tag{116.1}
$$

对每个接口给出状态表示

$$
r_i:S_i\to \bar S_i,
$$

给出事件表示

$$
F_i:E_i\to \bar E_i,
$$

并要求它保持首尾：

$$
\bar\partial^-F_i(e)=r_{i-1}(\partial^-e),
\qquad
\bar\partial^+F_i(e)=r_i(\partial^+e).
\tag{116.2}
$$

因此粗路径也有纤维积

$$
\bar P_n
:=
\bar E_1\mathbin{\times_{\bar S_1}}\bar E_2
\mathbin{\times_{\bar S_2}}\cdots
\mathbin{\times_{\bar S_{n-1}}}\bar E_n.
$$

逐边表示给出路径映射

$$
\phi_n:P_n\to\bar P_n,
\qquad
\phi_n(e_1,\ldots,e_n)=\bigl(F_1(e_1),\ldots,F_n(e_n)\bigr).
\tag{116.3}
$$

式 (116.2) 保证实际相等的中间状态在粗化后仍相等，所以 (116.3) 确实落在粗纤维积中。

**定义 116.1（$n$-ary no-spurious-pasting）。** 表示族在长度 $n$ 上满足无伪拼接，若

$$
\phi_n:P_n\twoheadrightarrow\bar P_n
$$

为满射。也就是说，每条粗路径都至少有一条具有同一共同实际中间来源的提升。长度 $n$ 的实际粗路径像记为

$$
\operatorname{Im}_n:=\phi_n(P_n)\subseteq\bar P_n.
$$

### 定理 116.2（任意长度路径像判据）

对所有表示保持首尾的类型化事件，有

$$
\boxed{
\phi_n(P_n)\subseteq\bar P_n.
}
\tag{116.4}
$$

并且

$$
\boxed{
\phi_n(P_n)=\bar P_n
\quad\Longleftrightarrow\quad
\phi_n\text{ 满射}
\quad\Longleftrightarrow\quad
\text{长度 }n\text{ 的 NPS 成立}.
}
\tag{116.5}
$$

**证明草图。** 对任意实际路径，(116.2) 逐个保证相邻粗边的首尾相等，得到 (116.4)。等号与满射只是像的定义；把粗路径逐条提升为实际路径正是满射的含义。证毕。

仅有第 115 节的二步条件不能推出全部 $n$ 的 NPS。一个明确的三层反例是

$$
\begin{aligned}
S_0&=\{a\},& S_1&=\{p,q\},& S_2&=\{r,s\},& S_3&=\{b\},\\
E_1&=\{(a,\xi,p)\},&
E_2&=\{(p,\eta,r),(q,\eta,s)\},&
E_3&=\{(s,\zeta,b)\}.
\end{aligned}
\tag{116.6}
$$

把每个 $S_i$ 映到单点，把三个事件都映到各自的唯一粗边。长度二的粗路径 $(\bar E_1,\bar E_2)$ 由 $p$ 提升，$(\bar E_2,\bar E_3)$ 由 $q\to s$ 提升；所以两个相邻二步窗口都无伪拼接。但唯一的长度三粗路径要求同一条 $E_2$ 同时从 $p$ 出发并到达 $s$，不存在这样的事件。因此 $\phi_3$ 不是满射。这个例子说明二步 NPS 是局部窗口条件，不是任意长度路径核的自动递推。

**定义 116.3（强路径提升）。** 设粗状态映射 $r_i$ 与粗事件映射 $F_i$ 满足：

1. $r_0:S_0\twoheadrightarrow\bar S_0$ 满射；
2. 对每个 $i$、每个 $s\in S_{i-1}$ 以及每条粗事件 $\bar e\in\bar E_i$，若
   $$
   \bar\partial^-\bar e=r_{i-1}(s),
   $$
   则存在 $e\in E_i$ 使
   $$
   \partial^-e=s,
   \qquad F_i(e)=\bar e.
   $$

称这两个条件为强路径提升（strong path lifting）。它要求粗边不仅有某个提升，而且能从任意给定的实际当前代表继续提升。

### 命题 116.4（强路径提升是全长度 NPS 的充分条件）

若强路径提升对每个 $i$ 成立，则对所有 $n\ge1$ 都有

$$
\phi_n:P_n\twoheadrightarrow\bar P_n.
\tag{116.7}
$$

**证明草图。** 对粗路径长度归纳。长度一由 (1) 给出。假设已将前 $i-1$ 条粗边提升为实际路径并得到当前状态 $s_{i-1}$；第 (2) 条从该具体状态提升第 $i$ 条粗边，并把其尾部作为下一步状态。归纳完成后得到整条实际路径。证毕。

强路径提升是一个方便的充分条件，通常比全长度 NPS 更强；它不是必要条件。反例 (116.6) 还表明，§115 的二步无伪拼接即使在所有相邻窗口成立，也不能替代强提升或逐长度的独立证明。

### 116.2 有限 horizon profile 与递归核塔

固定一种表示 $\ell$ 的实际状态集合 $S_\ell$。每个状态 $s$ 有可访问动作集合 $A_\ell(s)$，动作的部分响应写为

$$
\operatorname{step}_\ell(s,a)=
\begin{cases}
\bigl(\mathsf{ok},y,c,\tau,\rho,s'\bigr),&a\in A_\ell(s),\\
\bigl(\mathsf{fail},f,c,\tau,\rho,s_f\bigr),&a\notin A_\ell(s),
\end{cases}
\tag{116.8}
$$

其中 $y$ 是输出，$f$ 是失败标签，$\rho$ 是本步记录，$c$ 是费用，$\tau$ 是历时或时钟增量，$s_f$ 是声明的失败后继；若失败终止，则 $s_f$ 是带类型的终止标记。失败分支也可以带记录与费用，但不能把它静默当作成功状态。动作可访问性包含权限、参考与当前档案所允许的接口。

固定一个共同的类型化协议族 $\mathsf{Strat}_h$。各表示的 $\mathsf{Strat}_{\ell,h}$ 都是这个协议族在该表示中的实现；若动作、失败或策略类型没有先给出运输，就不能直接比较不同表示的 profile 核。

为把内部选择纳入同一个对象，令 $\mathsf{Strat}_{\ell,h}$ 是深度至多 $h$ 的类型正确有限策略树。策略的下一动作只能依赖已经暴露的记录、输出、失败、费用/时钟和控制状态，不得读取隐藏的 $s$。递归执行策略 $\sigma$ 得到完整有限轨迹

$$
\operatorname{Trace}_\ell(s,\sigma)
$$

它包含每一步的合法性、失败、输出、记录、费用、历时、声明的后继以及下一步可访问策略响应和实际选择器给出的下一动作；任务若不保留完整后继，则在这里使用其声明的后继投影。

**定义 116.5（有限 horizon profile）。** 令

$$
\boxed{
\Phi_{\ell,h}(s)
:=
\left(
\operatorname{Obs}_\ell(s),
\bigl(\operatorname{Trace}_\ell(s,\sigma)\bigr)
_{\sigma\in\mathsf{Strat}_{\ell,h}}
\right)
}
\tag{116.9}
$$

其中 $\operatorname{Obs}_\ell(s)$ 是任务声明的零步当前读数，包含观察者在不执行新动作时实际可访问的状态、档案、参考和权限字段；若任务不暴露其中某项，就在这里取相应的恒定投影。因而空策略也有一个明确的零步坐标，$K_{\ell,0}$ 不会把当前读数误当成已经遗忘。

并令

$$
K_{\ell,h}:=\ker\Phi_{\ell,h}.
\tag{116.10}
$$

因此，profile 不只是当前读数；它同时测试合法域、失败类型、输出、事件记录、成本/历时、后继和由实际记录允许的下一步选择。

### 命题 116.6（有限核递减与完整核）

若停止策略通过 padding 嵌入使 $\mathsf{Strat}_{\ell,h}\subseteq\mathsf{Strat}_{\ell,h+1}$，则

$$
K_{\ell,h+1}\subseteq K_{\ell,h},
\qquad
\boxed{
K_{\ell,\infty}:=\bigcap_{h\ge0}K_{\ell,h}
}.
\tag{116.11}
$$

这里 $s\,K_{\ell,\infty}\,t$ 当且仅当所有有限深度的合法策略响应都相同，等价于所有有限策略树的完整响应相同。

**证明草图。** 更深 profile 含有更浅 profile 的全部坐标，故核只能变细。两个状态属于交集，当且仅当对每个 $h$ 的所有深度至多 $h$ 策略给出相同响应；任意有限策略都有某个有限深度，故这正是所有有限策略响应相同。证毕。

在单一确定性动作、无自适应选择器、响应只保留后继与指定读数的特例中，(116.9) 退化为有限词 profile，接到仓内已有的有限 horizon kernel 递减与完整核交接口。若事件是部分的、失败和记录带有类型、或选择器依赖内部档案，则 profile 的精确商、有限状态性和全长度自然性仍是本卷的理论接口；本节不把一般版本宣称为已有 Lean 结论。

### 116.3 逆极限、实际来源像与 ghost thread

记有限 profile 的像为

$$
R_{\ell,h}:=\operatorname{ran}\Phi_{\ell,h}.
$$

把 $h+1$ 层 profile 限制到 $\mathsf{Strat}_{\ell,h}$，并把每条轨迹截到前 $h$ 步，给出限制映射

$$
\pi_{h+1,h}:R_{\ell,h+1}\to R_{\ell,h}.
$$

也就是说，若 $z$ 是 $h+1$ 层 profile，则

$$
\pi_{h+1,h}(z)
=\left(\operatorname{Obs}_\ell(s),
\bigl(\operatorname{prefix}_h\operatorname{Trace}_\ell(s,\sigma)\bigr)
_{\sigma\in\mathsf{Strat}_{\ell,h}}\right)
$$

这里 $s$ 是任意实现 $z$ 的来源；停止/padding 嵌入保证右侧与代表无关。若某个策略在更深层没有按同一方式截断，便不能把这些 profile 放进同一个逆系统，必须先声明相应的策略运输。

定义 profile 的逆极限

$$
L_\ell:=\varprojlim_h R_{\ell,h}
$$

以及实际来源像

$$
I_\ell:=
\left\{
\bigl(\Phi_{\ell,h}(s)\bigr)_{h\ge0}:s\in S_\ell
\right\}
\subseteq L_\ell.
\tag{116.12}
$$

由 (116.11) 定义

$$
\iota_\ell:S_\ell/K_{\ell,\infty}\longrightarrow I_\ell,
\qquad
[s]\longmapsto\bigl(\Phi_{\ell,h}(s)\bigr)_h.
$$

### 定理 116.7（完成像分解）

有自然双射

$$
\boxed{
S_\ell/K_{\ell,\infty}\cong I_\ell\subseteq L_\ell.
}
\tag{116.13}
$$

**证明草图。** 若 $s$ 与 $t$ 在完整核中等价，则每个有限 profile 相同，故映射良定义；若两个等价类映到同一线程，则所有有限坐标相同，故属于 $K_{\ell,\infty}$，所以单射；$I_\ell$ 的定义给满射。每个实际线程都满足相容性，故落在 $L_\ell$。证毕。

等式 $I_\ell=L_\ell$ 是线程完备性，不能从有限层的逐层可实现性自动得到。以下条件分别给出可用的充分条件。

1. 若 $S_\ell$ 是有限集合，则 $I_\ell=L_\ell$。对一条相容线程，令
   $$
   C_h=\{s\in S_\ell:\Phi_{\ell,h}(s)=r_h\}.
   $$
   每个 $C_h$ 非空且 $C_{h+1}\subseteq C_h$；有限性使交集非空。
2. 更一般地，若 $S_\ell$ 是紧致空间、每个 $\Phi_{\ell,h}$ 的单点纤维 $C_h$ 闭，则同一族非空递减闭集的紧致交性给出
   $$
   \bigcap_h C_h\ne\varnothing,
   $$
   从而 $I_\ell=L_\ell$。这里需要实际 topology、连续性和闭纤维假设，不能只凭“每个有限层有实现”补上。

一个简单的非完备反例使用倒计时：

$$
S=\mathbb N_0,
\qquad
F(k)=\max(k-1,0),
\qquad
q(k)=\mathbf 1_{\{k>0\}}.
\tag{116.14}
$$

在这个特例中取零步当前读数 $\operatorname{Obs}_\ell(k)=*$，并在下式中省略恒定的 $*$ 坐标。以唯一动作 $F$ 产生

$$
\Phi_h(k)=\bigl(*,q(k),q(F(k)),\ldots,q(F^h(k))\bigr).
$$

对任意 $h$，取 $k>h$，就有

$$
\Phi_h(k)=(1,1,\ldots,1).
$$

故 $1^\infty$ 是 $L$ 中的相容线程；但没有有限 $k$ 使 $q(F^j(k))=1$ 对全部 $j$ 成立，因为 $F^k(k)=0$。因此

$$
\boxed{
\text{finite consistency}\not\Rightarrow\text{ actual-source realization}.
}
\tag{116.15}
$$

这个 ghost thread 不是另一个实际状态，也不是把 $\infty$ 加进 $S$ 的许可；它只显示有限 profile 的逆极限可能严格大于实际来源像。

### 116.4 空间、时间、边界、记忆的四表达

在同一个共同来源 $S$ 上，取四个表示

$$
r_{\mathrm{sp}}:S\to R_{\mathrm{sp}},\qquad
r_{\mathrm{tm}}:S\to R_{\mathrm{tm}},\qquad
r_{\mathrm{boundary}}:S\to R_{\mathrm{boundary}},\qquad
r_{\mathrm{mem}}:S\to R_{\mathrm{mem}}.
\tag{116.16}
$$

“空间”在这里记录端口、邻接或可交互位置；“时间”记录因果顺序、时钟或累积路径量；“边界”记录对外接续所需的残余响应；“记忆”记录观察者实际可访问的档案、参考、权限和控制状态。四个名字表示不同接口合同，不预先断言它们是四个独立实体。

固定共同任务的完整未来响应，定义共同未来行为核

$$
\boxed{
s\,K_*\,t
\iff
\text{所有合法有限策略对 }s,t
\text{给出相同的合法性、失败、输出、记录、费用、历时、后继与可访问选择响应}.
}
\tag{116.17}
$$

令 $K_i=\ker r_i$，并对表示的事件箭头映射 $F_i$ 令 $K_i^{\mathrm{evt}}=\ker F_i$。

这里比较 $K_i^{\mathrm{evt}}$ 与 $K_j^{\mathrm{evt}}$ 时，默认 $F_i,F_j$ 都作用在同一个实际类型化事件接口上；若两者的事件域、标签类型或失败类型不同，必须先给出它们之间的事件接口映射，不能直接比较两个不同域上的核。

**定义 116.8（四表达的动态互恢复合同）。** 在本节中，单个表达的动态互恢复是指：状态、类型化事件、任意有限长度路径及上述全部响应字段，都可以从另一表达的实际像唯一恢复；并且每个长度的粗路径复合关系恰等于实际路径像（即该合同要求相应长度的 NPS），恢复后的路径复合仍等于实际路径复合。若合同只要求状态读出或只要求实际路径像而不要求粗边复合精确，则可不称为本节的动态互恢复。

本节的四个全局映射是一个共同实际来源上的特殊情形。若改用局部图表，必须另外要求实际重叠对相应核饱和、transition 满足 cocycle、后继保持在实际来源像内，并按 §42.7 检查来源 holonomy；本节的全局 $g_{ij}$ 不替代这些局部条件。

### 定理 116.9（四表达动态互恢复判据）

在定义 116.8 的合同下，表达 $i,j$ 动态互恢复的必要条件是：

1. **状态核相等：**
   $$
   K_i=K_j;
   $$
2. **事件箭头核相等：**
   $$
   K_i^{\mathrm{evt}}=K_j^{\mathrm{evt}};
   $$
3. **任意长度 NPS：** 对所有类型化长度 $n$，两边的路径映射 $\phi_{i,n},\phi_{j,n}$ 都满足满射；
4. **响应与选择器纤维因子化：** 合法性、失败标签、输出、记录、费用、历时、策略可访问性、后继和实际选择器输出在每个相应表示纤维上保持常值，并且选择器、控制、参考、权限和 writer 更新在恢复器下自然运输。

在共同动作类型下，这一项至少包含

$$
\pi_j\circ g_{ij}=\pi_i,
\qquad
U_j\circ g_{ij}=g_{ij}\circ U_i,
\tag{116.18a}
$$

其中 $\pi_i$ 是内部下一动作选择器，$U_i$ 是控制、参考、权限和记忆 writer 的联合更新；若某个分量不属于任务合同，就把它从两边同时删去，而不能默认为免费输入。

若四项成立，则它们也是充分条件。更具体地，在实际像上定义

$$
g_{ij}:r_i(s)\longmapsto r_j(s).
\tag{116.18}
$$

它良定义且为双射，满足

$$
g_{ii}=\operatorname{id},
\qquad
g_{jk}\circ g_{ij}=g_{ik},
\qquad
g_{ji}=g_{ij}^{-1}.
\tag{116.19}
$$

所有转移、事件标签和有限路径响应都对 $g_{ij}$ 自然；例如对实际操作 $a$，

$$
g_{ij}\bigl(r_i(T_a(s))\bigr)=r_j(T_a(s)),
$$

并且 $g_{ij}$ 把 $i$ 表示中的合法/失败/记录响应送到 $j$ 表示中的对应响应。

若共同任务还要求每个表达都是**最小充分表达**，即不保留共同未来行为之外的额外区别，则在上述四项之外加入

$$
K_i=K_j=K_*.
\tag{116.19a}
$$

在这个附加合同下，$K_i=K_j=K_*$ 才是必要且充分的最小性条件。没有这项最小性要求，两种表达可以保留同一份额外标签并彼此互相恢复，此时只需 $K_i=K_j$，不应强行把它们称为共同任务的最小商。

**证明草图。** 由 $K_i=K_j$，式 (116.18) 不依赖 $s$ 的代表，并由相等核得到双射及 (116.19)。事件核相等给事件箭头的同样结论。响应与选择器纤维因子化保证每个局部动作、控制更新和后继在商上唯一下降，并给出 $\pi_j\circ g_{ij}=\pi_i$ 及相应 writer/参考运输；任意长度 NPS 保证表示中的粗路径复合没有额外伪路径，故局部自然性递归到全部有限路径。反向，若动态互恢复合同存在，两个状态（或事件）在一个表达中不可区分，当且仅当在另一表达中不可区分，故核相等；合同所要求的精确实际路径复合给每个长度的满射，若任一响应字段或选择器在纤维上变化则另一表达不能唯一恢复它，故因子化条件必要。若再要求最小充分表达，则其核按定义恰为 $K_*$。证毕。

这里的 NPS 必须与合同的路径要求一起理解。若任务只要求某个单独读数，不要求从粗边复合恢复完整路径关系，则可不要求 NPS；但那是较弱的静态合同，不能称为本节的动态互恢复。

仅有四个核的交集也不够。若

$$
\bigcap_{i\in\{\mathrm{sp,tm,boundary,mem}\}}\ker r_i=K_*,
\tag{116.20}
$$

则联合映射

$$
s\longmapsto
\bigl(r_{\mathrm{sp}}(s),r_{\mathrm{tm}}(s),r_{\mathrm{boundary}}(s),r_{\mathrm{mem}}(s)\bigr)
$$

对共同任务是充分的；这不说明任一单个表达的核等于 $K_*$，也不说明任意两个表达可互相恢复。联合充分性与单表达互恢复是两个不同量词。

同样，正向核不自动恢复过去。即使 $K_i=K_j=K_*$，若某个操作 $T_a$ 在实际来源上非单射，则从后继状态不能唯一确定前驱。双向时间恢复还需在声明的核心上满足：每个允许更新有逆更新，或限制到一个更新可逆的 periodic core，并把逆操作纳入接口。单向动态自然性不产生逆向历史。

### 命题 116.10（正费用自环阻止端点势表示）

设路径费用可加，存在 $s,a$ 使

$$
T_a(s)=s,
\qquad c(s,a)>0.
$$

则不存在只依赖端点状态的函数 $V$，使所有路径 $w$ 都满足

$$
C(w)=V(\operatorname{end}(w))-V(\operatorname{start}(w)).
\tag{116.21}
$$

**证明。** 自环的两端相同，右侧为零，而该一步路径的费用为正，矛盾。证毕。

因此时间累计量、费用或历时若存在正费用自环，不能仅由端点状态恢复。要保留它们，必须把时钟读数、累计量或路径标签加入边界，并把相应的字段放入 (116.17) 的未来响应；回到同一个空间位置不等于恢复同一个完整时间/记忆状态。

### 116.5 回接 FIB 二叶生成层与五窗读出

Fibonacci 原子关系卷 §§2–5 给出的自由二叶语法、替换、组成和数量商可写为

$$
\mathcal T=\mu X\bigl(\{\alpha,\beta\}+X\times X\bigr),
\qquad
\rho(\alpha)=\beta,
\qquad
\rho(\beta)=\langle\beta,\alpha\rangle .
\tag{116.22}
$$

这里 $\alpha,\beta$ 是两个不同的叶原子或零元生成元，不是两个裸的“关系”。有序二元配对是第三个生成构造，$\rho$ 是一项额外的内部过程；若把“关系”理解为完整的接法，就不能把这三者压缩成两个对象。母卷 §§245–249 则是后续五窗、前沿和预算分析，不是二叶生成定义。把组成映射、数量读数或五窗递归读出接到 $\mathcal T$ 上，只是选择具体的 $r_i$ 或 $\Phi_{\ell,h}$：

$$
\mathcal T
\longrightarrow
\text{组成/数量或五窗读出}
$$

可能忘记叶序、括号、来源、失败、记录和后继。因而它们不能替代事件核 $K_i^{\mathrm{evt}}$ 或路径核 $\ker\phi_n$。

特别地，五窗递归中的五个局部标签及其有限转移矩阵是一个指定任务的局部读出和状态更新；“五”来自该窗口合同的局部枚举，并不表示有五个独立不可约关系，也不保证所有任意长度路径具有共同实际来源。只有在五窗表示满足 (116.17) 的纤维常值性、事件核相等和所需长度 NPS 时，才能把它当作四表达中的一个动态边界。

因此，“FIB 更基础”应限定为**生成表示的基础性**：在固定二叶签名下，静态保构造的最小零元数是二；加入 $\rho$ 后，从单个动态种子 $\alpha$ 可以生成相应的 Fibonacci 轨道。它不推出所有关系网络只有两类不可约状态，也不推出任意观察者边界只有两维。若改用 $k$-bonacci 签名，底层叶原子可变为 $\alpha_0,\ldots,\alpha_{k-1}$；若任务保留顺序、括号、失败、权限或记录，组成摘要的核还必须进一步细化。

因此当前理论的层次应保持为：

$$
\boxed{
\text{二叶生成语法}
\longrightarrow
\text{特定数量/五窗读出}
\longrightarrow
\text{事件箭头核}
\longrightarrow
\text{任意长度路径核}
\longrightarrow
\text{共同未来行为核与实际来源像}.
}
\tag{116.23}
$$

式 (116.23) 是关系层次的组织，不是说所有层级已经在 Lean 中形式化。二叶基础、有限 horizon 核、线程完备性、四表达互恢复及一般选择器的完整版本仍按各自条件区分已知结果与理论 open；本节不改变当前仓库的 open/非 Lean 声明边界，也不把理论综合写成新增形式化核验。

## 116.99 追加锚
