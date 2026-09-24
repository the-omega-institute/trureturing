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
