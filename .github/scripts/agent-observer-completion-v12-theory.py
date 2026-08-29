from pathlib import Path

path = Path('docs/develop/theory/FORMAL_OBSERVER_COMPLETION_REFLECTION.md')
text = path.read_text(encoding='utf-8')

old_version = '**版本：v1.1，2026-08-25**'
new_version = '**版本：v1.2，2026-08-29**'
assert text.count(old_version) == 1
text = text.replace(old_version, new_version, 1)

old_history = ('**版本史**：v1.0 初稿 → **v1.1 勘误(issue #3118)：推论 25.3 '
               '补回 Heisenberg 导数的因子 i，并将生成元记为 i·ad_H**。')
new_history = (old_history[:-1] + ' → **v1.2 理论分层与形式化取址：补入 effective-image '
               '纪律、接口运算、有限深度完成塔、agency enrichment、可见环 holonomy、'
               'completion locus 演算，并勘正公共固定点的超限迭代条件**。')
assert text.count(old_history) == 1
text = text.replace(old_history, new_history, 1)

section_0a = r'''

## 0.1 三类 completion 与 effective-image 纪律

本文使用“completion”描述三个彼此相关、类型不同的构造。后文必须按类型区分，不再仅凭术语相似性互相代换。

### A. 行为 completion

输入是动力系统与读出

$$
(X,F,q).
$$

输出是接口反射

$$
C_F(q),
$$

其目标是得到最小的 $F$-稳定信息精化。这是第 3–9 节的主对象。

### B. 结构 completion locus

输入是参数空间、规范化条件与缺陷

$$
(A,N,d,0_D).
$$

输出是零缺陷集合

$$
\operatorname{Comp}(N,d,0_D)
=
N\cap d^{-1}(\{0_D\}).
$$

它是参数空间中的子集，必要时再对 gauge 轨道取商。它不自动具有行为 reflector 的最小稳定精化性质。

### C. Agency enrichment 与 agency completion

给定当前读出 $q$ 与策略轮廓 $s$，配对读出

$$
q\vee s=(q,s)
$$

首先只是两个接口的联合精化，称为 **agency enrichment**。只有在指定动力学或控制作用后，再对 $(q,s)$ 施加行为 completion，并证明稳定性与最小性，所得

$$
C_A(q,s)
$$

才称为该作用下的 **agency completion**。

### Effective-image 纪律

任意读出 $q:X\to B$ 的 canonical codomain 是其有效像

$$
\operatorname{Im}(q).
$$

所有“唯一 factor”“最小实现”“反射单位”均在有效像上陈述。若把 factor 任意延伸到整个环境 codomain $B$，像外取值通常不唯一，因此不得把有效像上的唯一性外推为环境空间上的唯一性。

这条纪律同时适用于：

1. 一般接口的 refinement factor；
2. 线性读出 $C:V\to Y$ 的诱导动力学；
3. 行为实现的 reachable part；
4. completion-point 参数化中的 gauge-fixed carrier。
'''
marker = '\n# 1. 接口精化偏序\n'
assert text.count(marker) == 1
text = text.replace(marker, section_0a + marker, 1)

section_1a = r'''

# 1A. 接口运算与 kernel 演算

本节固定读出 $q:X\to B$，并始终把 codomain 缩到有效像后讨论唯一性。

## 定义 1A.1（后处理）

给定 $h:B\to C$，后处理接口为

$$
h_*q=h\circ q.
$$

## 定理 1A.1（数据处理的 kernel 形式）

$$
K_q\subseteq K_{h\circ q}.
$$

后处理只能合并原有读数，不能恢复已经被 $q$ 删除的状态区别。

## 定理 1A.2（精确保真判据）

$$
K_{h\circ q}=K_q
\iff
h\text{ 在 }\operatorname{Im}(q)\text{ 上单射}.
$$

因此要求 $h$ 在整个 $B$ 上单射通常过强。真正相关的是它在已实现读数上的单射性。

## 推论 1A.1（严格损失见证）

以下等价：

1. $K_q\subsetneq K_{h\circ q}$；
2. 存在 $x,y\in X$，满足 $q(x)\ne q(y)$ 且 $h(q(x))=h(q(y))$；
3. $h$ 在 $\operatorname{Im}(q)$ 上不单射。

严格信息损失因此总能由一个有效像内的碰撞见证。

## 定义 1A.2（联合读出）

对 $q:X\to B$ 与 $r:X\to C$，定义

$$
(q\vee r)(x)=(q(x),r(x)).
$$

## 定理 1A.3（联合 kernel）

$$
K_{q\vee r}=K_q\cap K_r.
$$

## 定理 1A.4（联合读出是 supremum）

在信息精化偏序中，$q\vee r$ 是 $q$ 与 $r$ 的最小公共精化：

$$
q\preceq q\vee r,
\qquad
r\preceq q\vee r,
$$

且若 $q\preceq s$、$r\preceq s$，则

$$
q\vee r\preceq s.
$$

对传感器族 $(q_i)_{i\in I}$，联合读出 $x\mapsto(q_i(x))_i$ 的 kernel 为

$$
\bigcap_{i\in I}K_{q_i}.
$$

加入新坐标只会缩小联合 kernel；若新坐标分离了旧联合 kernel 中的一对状态，则该精化严格。
'''
marker = '\n# 2. 稳定接口\n'
assert text.count(marker) == 1
text = text.replace(marker, section_1a + marker, 1)

section_7a = r'''

# 7A. 有限深度完成塔

无限行为 completion 可以由有限视界逐层逼近。

## 定义 7A.1（深度 $m$ 的行为读出）

$$
C_F^{\le m}(q)(x)
=
\big(q(x),q(Fx),\ldots,q(F^m x)\big).
$$

记其 kernel 为 $K_m$。

## 定理 7A.1（有限视界 kernel）

$$
K_m
=
\bigcap_{k=0}^{m}(F\times F)^{-k}K_q.
$$

## 定理 7A.2（一步递推）

$$
(x,y)\in K_{m+1}
\iff
q(x)=q(y)
\ \land\ 
(Fx,Fy)\in K_m.
$$

等价地，若把关系拉回记为 $(F\times F)^{-1}$，则

$$
K_{m+1}=K_q\cap(F\times F)^{-1}K_m.
$$

所以

$$
K_0\supseteq K_1\supseteq K_2\supseteq\cdots.
$$

## 定理 7A.3（极限）

$$
K_{C_F(q)}=\bigcap_{m\ge0}K_m.
$$

## 推论 7A.1（严格增长见证）

若两状态在深度 $m$ 前全部同读，而在时刻 $m+1$ 首次分离，则

$$
K_{m+1}\subsetneq K_m.
$$

这给出了 completion 每一层新增信息的局部证书。

## 定理 7A.4（有限状态停止）

若 $X$ 有限，则存在 $m_*$ 使

$$
K_{m_*}=K_{C_F(q)},
$$

并且以后永久稳定。仓库中的 `completionDepth` 给出一个由全部状态对的选择性区分时间取 supremum 得到的具体停止深度。
'''
marker = '\n# 8. 动作词与受控完成\n'
assert text.count(marker) == 1
text = text.replace(marker, section_7a + marker, 1)

section_9a = r'''

# 9A. Agency enrichment 与可见环 holonomy

本节把“自我知道当前策略”拆成接口问题与动力问题两层。

设历史或内部状态空间为 $H$，当前可见状态为

$$
q:H\to B,
$$

策略轮廓为

$$
s:H\to\Pi.
$$

## 定义 9A.1（agency enrichment）

$$
A(q,s)=q\vee s=(q,s).
$$

由定理 1A.4，它是当前状态接口与策略接口的最小公共精化。

## 定义 9A.2（策略余量见证集）

$$
R_{\mathrm{strat}}(q,s)
=
\{(x,y):q(x)=q(y),\ s(x)\ne s(y)\}.
$$

它是当前 fiber 内尚未被当前状态读出决定的策略区别集合。它通常不是等价关系，因此不得直接称为 quotient kernel。

## 定理 9A.1（当前 fiber 的互斥分解）

$$
K_q
=
K_{A(q,s)}
\ \dot\cup\ 
R_{\mathrm{strat}}(q,s).
$$

## 定理 9A.2（零策略余量判据）

以下等价：

1. $R_{\mathrm{strat}}(q,s)=\varnothing$；
2. $K_q\subseteq K_s$；
3. $s$ 在有效像上通过 $q$ 唯一因子化；
4. $A(q,s)$ 与 $q$ 具有相同 kernel。

因此“策略自可见”的精确含义是策略轮廓由当前状态接口决定。

## 定义 9A.3（真正的 agency completion）

对控制作用 $(F_a)_{a\in A}$，定义

$$
C_A^{\mathrm{agency}}(q,s)
=
C_A(A(q,s)).
$$

它读取全部有限行动词后的当前状态与策略轮廓，因而是同时保留二者的最小受控稳定精化。

### 可见环与 pointed holonomy

给定一个有限行动词 $w$ 与状态 $x$，若

$$
q(F_wx)=q(x),
$$

称 $w$ 在 $x$ 处形成 **可见环**。若同时

$$
F_wx\ne x,
$$

则称其具有非平凡 pointed holonomy。若

$$
s(F_wx)\ne s(x),
$$

则该 holonomy 对策略可见。

## 定理 9A.3（策略变化检测非平凡 holonomy）

在可见环上，策略变化推出内部状态变化：

$$
q(F_wx)=q(x)
\ \land\ 
s(F_wx)\ne s(x)
\Longrightarrow
F_wx\ne x.
$$

## 定理 9A.4（因子化消去策略 holonomy）

若 $s$ 通过 $q$ 因子化，则每个 $q$-可见环都对策略不可见：

$$
q(F_wx)=q(x)
\Longrightarrow
s(F_wx)=s(x).
$$

## 定理 9A.5（联合忠实性消去隐藏 holonomy）

若联合读出 $A(q,s)$ 单射，则

$$
q(F_wx)=q(x)
\ \land\ 
s(F_wx)=s(x)
\Longrightarrow
F_wx=x.
$$

所以 holonomy 的“隐藏性”总是相对于指定读出而言。没有基点回返条件时，只能称为 memory transport；没有路径或行动词数据时，也不能把任意自映射自动命名为 holonomy。
'''
marker = '\n# 10. 状态 kernel 与 effect 代数的反对偶\n'
assert text.count(marker) == 1
text = text.replace(marker, section_9a + marker, 1)

start = text.index('# 13. 记忆商\n')
end = text.index('\n# 14. 可观测 Krylov 塔的有限停止\n', start)
section_13 = r'''# 13. 记忆商与 effective-image 下降

当前接口 $C$ 一步删除

$$
N_0=\ker(C).
$$

其中永远不会影响未来读数的部分是 $N_\infty$。

## 定义 13.1（线性记忆余量）

$$
M(C,T)=N_0/N_\infty.
$$

它记录“当前不可见、但未来会变得可见”的方向。

令

$$
C_{\mathrm{eff}}:V\to\operatorname{ran}(C)
$$

为 $C$ 的有效像因子化。

## 定理 13.1（零记忆与有效像下降）

以下等价：

1. $M(C,T)=0$；
2. $\ker(C)$ 对 $T$ 不变；
3. 存在唯一线性映射
   $$
   \bar T_C:\operatorname{ran}(C)\to\operatorname{ran}(C)
   $$
   使
   $$
   C_{\mathrm{eff}}T=\bar T_C C_{\mathrm{eff}}.
   $$

### 证明

$M(C,T)=0$ 当且仅当 $\ker(C)=N_\infty$。而 $N_\infty$ 是 $\ker(C)$ 内最大 $T$-不变子空间，因此前两项等价。

若 kernel 不变，定义

$$
\bar T_C(Cx)=C(Tx).
$$

kernel 不变保证代表元无关，有效像满射保证唯一性。反向由交换方块立即得到 kernel 不变。∎

## 环境 codomain 勘正

若 $C$ 满射到 $Y$，则 $\operatorname{ran}(C)=Y$，上述诱导动力学在 $Y$ 上唯一。

若 $C$ 不满射，有限维下可以选择补空间把 $\bar T_C$ 延伸为某个 $A:Y\to Y$，但像外延伸通常不唯一。因此

$$
\ker(C)\text{ 不变}
$$

规范地产生的是有效像上的下降，而不是未经附加选择的整个环境空间上的唯一动力学。

## 推论 13.1（记忆维数）

有限维时：

$$
\dim M(C,T)
=
\dim O_\infty-\operatorname{rank}(C).
$$

这给出把当前读数变为精确 Markov 状态至少需要补回的独立线性区分数。
'''
text = text[:start] + section_13 + text[end:]

old_q = '在可观测商 V/N_∞ 上，W_β 正定。定义'
new_q = ('$W_β$ 消去 $N_∞$，其二次型在商 $V/N_∞$ 上良定义并正定。若要把它写成一个规范的算子，'
         '可在给定内积下识别商与 $N_∞^⊥$；未经这一识别时，应把商上的对象表述为正定二次型。定义')
assert text.count(old_q) == 1
text = text.replace(old_q, new_q, 1)

start = text.index('# 24. 局部 closure、gluing 与超限共同固定点\n')
end = text.index('\n# 25. 新研究推论\n', start)
section_24 = r'''# 24. 局部 closure、gluing 与公共固定点

设 $L$ 是一个集合大小的完备格，且

$$
\{C_i:L\to L\}_{i\in I}
$$

是一族 closure operator。每个 $C_i$ 单调、扩张且幂等。定义联合推进算子

$$
T(x)=\bigvee_{i\in I}C_i(x).
$$

从 $x_0=x$ 开始作超限迭代：

$$
x_{\alpha+1}=T(x_\alpha),
$$

$$
x_\lambda=\bigvee_{\alpha<\lambda}x_\alpha
$$

对极限序数 $\lambda$。

## 定理 24.1（最小公共固定点）

该递增链在某个序数阶段稳定；其首次稳定值 $x_*$ 满足

$$
C_i(x_*)=x_*
$$

对所有 $i$，并且是所有位于 $x$ 之上的公共固定点中的最小者。

### 证明

$T$ 单调且扩张，所以 $(x_\alpha)$ 递增。由于 $L$ 是集合，不能存在长度超过其 Hartogs 序数的严格递增链，因此某个阶段有

$$
x_{\alpha+1}=x_\alpha.
$$

此时 $T(x_*)=x_*$。对每个 $i$，扩张性与 join 定义给出

$$
x_*\le C_i(x_*)\le T(x_*)=x_*,
$$

故 $C_i(x_*)=x_*$。

若 $y\ge x$ 且所有 $C_i(y)=y$，则由超限归纳得到 $x_\alpha\le y$：后继步使用单调性，极限步使用 join。故 $x_*\le y$。∎

### 勘正 24.1

上述存在性与最小性不要求各 $C_i$ 保持有向 join。保持有向 join 的额外条件只用于降低 closure ordinal：若联合推进 $T$ 保持该迭代链的 $\omega$-join，则

$$
x_\omega=\bigvee_{n<\omega}T^n(x)
$$

已经是固定点。

## 定理 24.2（交换 closure 的一次扫描）

对有限族两两交换的 closure operator，按任意顺序复合一次即得到公共 closure；其固定点恰为各 $C_i$ 固定点集合的交。非交换时，一次逐个闭合通常不足，必须继续迭代到公共固定点。

## 解释

局部每一块闭合，不推出全局一次拼接即闭合。剩余障碍可能位于：

- closure 次序；
- transition compatibility；
- limit-stage join；
- realizability；
- 非平凡 holonomy。

这为 prime-window、observer atlas 与 transfinite residual tower 提供同一组织语言。

# 24A. Structural completion locus 演算

为避免与行为 reflector 混同，记

$$
\operatorname{Comp}(N,d,0_D)
=
\{a:a\in N,\ d(a)=0_D\}.
$$

## 定理 24A.1（合取即交）

对两个规范化条件与两个缺陷：

$$
\operatorname{Comp}
\bigl(N_1\cap N_2,(d_1,d_2),(0_1,0_2)\bigr)
=
\operatorname{Comp}(N_1,d_1,0_1)
\cap
\operatorname{Comp}(N_2,d_2,0_2).
$$

## 定理 24A.2（任意参数映射下的拉回）

对 $\alpha:A'\to A$：

$$
\operatorname{Comp}(\alpha^{-1}N,d\circ\alpha,0_D)
=
\alpha^{-1}\operatorname{Comp}(N,d,0_D).
$$

该命题只需要函数，不需要 $\alpha$ 可逆。若 $\alpha$ 是等价并同时运输 normalization 与 zero-defect 谓词，则进一步得到 completion-point carriers 的等价，这正是 covariance 版本。

## 定理 24A.3（gauge 稳定性交）

若两个 completion locus 分别在同一群作用下稳定，则它们的交仍稳定。因而多缺陷 completion 可以先取 predicate intersection，再限制群作用并取 orbit quotient。

这些集合论定理描述参数解空间的组合、拉回与 gauge 约化。它们本身不产生行为 completion 的最小稳定接口；两层发生联系还需要一个把参数映射为读出或动力系统的明确语义函子。
'''
text = text[:start] + section_24 + text[end:]

start = text.index('# 27. 建议 Lean 模块树\n')
end = text.index('\n# 28. 最终统一\n', start)
section_27 = r'''# 27. Lean owner 取址与剩余 frontier

截至 v1.2，行为 completion 的主体已经由仓库中的 canonical owner 承担，包括：

```text
D5/S3/ObserverMemory/Prediction/ItineraryCompletion.lean
D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean
D5/S3/ObserverMemory/Refinement/FactorizationCategory.lean
D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality.lean
D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionReflection.lean
D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionFunctoriality.lean
D5/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint.lean
D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.lean
D5/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality.lean
D5/S3/Observer/Completion/StructuralCompletionSignature.lean
D5/S3/Observer/Completion/CompletionPointCovariance.lean
```

因此不再创建平行的 `InterfaceOrder`、`BehaviorCompletion` 或 `MemoryTransport` 原语。本轮新增理论应沿现有 owner 补入以下缺口：

```text
D5/S3/ObserverMemory/Refinement/
  PostprocessingKernelCalculus.lean
  JointReadoutSupremum.lean

D5/S3/ObserverMemory/RefinementClosure/
  FiniteHorizonKernelRecurrence.lean
  CommutingClosureCommonFixedPoint.lean

D5/S3/Observer/Agency/Self/
  AgencyEnrichment.lean

D5/S3/Observer/Agency/Holonomy/
  VisibleLoopHolonomy.lean

D5/S3/Observer/Completion/
  CompletionLocusCalculus.lean
```

优先形式化声明为：

```text
postprocessing_kernel_le
postprocessing_kernel_eq_iff_injOn_range
postprocessing_strict_iff_range_collision
pair_readout_kernel
pair_readout_least_common_refinement
finite_horizon_kernel_succ_iff
finite_horizon_kernel_antitone
complete_kernel_eq_iInf_finite_horizon
finite_horizon_stabilizes_at_completionDepth
current_kernel_strategy_residual_partition
strategy_factorization_iff_no_residual
visible_loop_policy_change_implies_nontrivial
strategy_factorization_makes_visible_loops_invisible
faithful_joint_readout_kills_hidden_holonomy
completion_locus_pair_eq_inter
completion_locus_preimage
completion_locus_intersection_gauge_stable
commuting_closure_composition_fixed_iff
```

超限 closure ordinal、一般拓扑 completion、测度化 almost-everywhere kernel 与无限维 Gramian 收敛继续保持 open，直到其载体、宇宙层级与收敛假设被单独取址。
'''
text = text[:start] + section_27 + text[end:]

path.write_text(text, encoding='utf-8')
