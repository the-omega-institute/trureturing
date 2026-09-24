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
