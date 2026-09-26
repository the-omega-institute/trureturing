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
