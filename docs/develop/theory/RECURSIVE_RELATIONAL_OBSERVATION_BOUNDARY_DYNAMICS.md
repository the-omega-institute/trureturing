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
