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

核与陪集的机制沿用主卷定理18.4的平移同余判据；本有限模型中可直接核对：若 $h,k\sim_u0$，平移 $k$ 给 $h+k\sim_uk$，再由传递性得 $h+k\sim_u0$；把任意一对同时平移 $-z'$ 则给 (46.9)。因此没有预先假设编码是线性函数，任意满足平移闭合的确定性编码都落入这个分类。

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
