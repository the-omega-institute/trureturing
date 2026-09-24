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
