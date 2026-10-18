# 搜索约化逃逸审计契约

## 1. 目的、效力与证据边界

证明逃逸 P 问的是：在固定原任务上，新结构是否使固定参照搜索者从未找到证明变为找到证明。判词相对基底、搜索者版本和预算；不声称数学原创性、绝对证明难度或 P 与 NP 的分离。有限搜索未找到不等于不存在证明。

本契约的机器结果仅为 **Observe**，不产生 Block、总分、权重、新准入门或新 DTR 状态。owner 采纳判形语义以前，现行 `CLAUDE.md` §3.2 仍承担准入。旧结算保留原基底与判据，不按新版本回写。

三种核验各有独立边界：Lean kernel 核验下面模型在明示前提下的定理；真实搜索程序满足契约的程度由集成校准及真实触发检验；契约忠实于 owner 的程度由独立评审与 owner 判定。模型编译不替代后两者。研究系统是受益方，实施者不能独自签发忠实性结论。

## 2. 原搜索问题登记

每个实际请求在首跑前固定下列输入；没有请求的声明不触发搜索或补登记机器。

这里的原搜索是取得完整原陈述 T 的证明项：输入编码为编译器恢复的类型与环境，合法解关系为 kernel 在登记公理边界内接受该项具有类型 T，允许操作为固定 R 的规则，资源单位为命令心跳。T 的参数域、实例范围与量词都保留在完整类型中。若 T 另涉及对象搜索或算法复杂度，P 侧判词只认证上述证明搜索约化，不自动认证对象搜索的加速。

| 输入 | 契约 |
| --- | --- |
| 原任务 T | 编译器完整 telescope、量词、宇宙、局部假设和目标类型；不得改成较弱特例 |
| 身份 | 源声明地址与 `statement_id`，后者只作身份地址，不证明语义新旧 |
| 基底 B | 受保护 immutable baseline 的 40 位提交、冻结成员清单及钉版依赖；候选 pin 不算既有冻结 |
| 新结构 S | 同次交付的其他声明及依赖关系；不含 T、T 的受支持别名或重述；须有编译证明 |
| 搜索配置 | R 版本、Lean/Mathlib pin、叶子策略及顺序、结构规则、心跳预算和选项 |
| 预期及对照 | 校准或受益单元的角色、预期、配对的相同任务与唯一环境差异 |

登记先于观察结果。任务、基底、S 或配置变更产生独立请求，保留旧读数；不得以同名覆盖。声明身份及源码来源可追索，但程序字节不进入复用判据。

## 3. 参照搜索者 R_v1

### 3.1 基底与隔离

B 包含钉版 Mathlib 与受保护基线上已冻结 D5 的可用声明及其必要依赖。依赖可被 kernel 检查不等于所有依赖均作为可搜索新前提暴露。当前候选、同批公开或私有 helper、候选新增冻结状态及传递泄漏均不进入基底搜索。

基底探针对交付集的 Prop 声明隐藏；不得从其值、属性、simp 表、实例、宏展开、导入模块或已加载证明缓存重新取得它们。候选定义只作为原任务的语汇按 §5 展开，不把定义中编码的答案当作基底事实。无法建立隔离时为证据不足。

配对探针只额外暴露登记的 S。T 及其别名/重述仍隐藏；S 的依赖闭包不得包含这些禁用项。不能以将 T 包进合取、结构字段、等价证书、私有常量或实例的方式获得配对成功。检查的是实际输入和编译依赖，不建立假想载荷扫描器。

### 3.2 策略与预算

R_v1 的叶子策略取自钉版 Mathlib 全量导入环境的 `register_hint` 注册清单，保留该环境的优先级与稳定枚举次序。当前配置使用 `leanprover/lean4:v4.35.0` 与 Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`；变更 pin 或策略必须另立 R 版本。实现须在校准冻结前输出解析后的完整策略清单、顺序、工具链选项和预算，不能由受益方按目标挑选子集。

结构阶段按原 telescope 引入全称参数与蕴含前提，拆分目标的合取和双向蕴含，并查找局部/允许前提的合取分量与双向蕴含方向。只作这些有限语法树上的结构操作，不作任意语义等价搜索；叶子才尝试注册策略。`intro`、`split` 等只产生子目标而未闭合，不算叶子成功。

每次叶子策略尝试独立命令、独立初始状态，使用钉版 Lean 的默认 `maxHeartbeats = 200000`（用户可见单位，每单位为一千次内部心跳），不得继承作者提高的预算。结构阶段也须终止并受同一默认命令预算约束；所有叶子都闭合才构成任务成功。每条命令的预算及总尝试数分别报告，不用墙钟速度作为数学判据。独立尝试不得互相遗留 metavariable、simp 状态或成功缓存。

不直接运行 `hint`：它在无命中时可 admit。禁止联网及 `native_decide`。候选、S 和探针生成的证明均须重新经 kernel 核验，公理闭包只能在 `propext`、`Classical.choice`、`Quot.sound` 内，无 `sorryAx`、私有 axiom 或未闭合目标。

R 的加强仅可保留全部旧尝试并增加新尝试，旧尝试保持原预算，成功集取并集；不得在同一总预算内挤掉旧策略。版本冻结及校准先于受益单元，观察其结果后禁止调参。作者实际使用的基线前提交给 R 的“前提先知”变体可作额外测量，须标明配置区别且不参与判词；它会扩大可找到范围。

### 3.3 运行结果

`found` 表示至少一次尝试取得完整、合规、通过 kernel 的证明；其余独立尝试的故障另行报告，不撤销已取得的成功。`exhausted` 表示所有规定尝试均正常结束且未找到证明，是完成的有限搜索的否定读数。没有成功证明时，任一缺件、隔离失败、实现错误、心跳超限、外部超时、取消或未决均单列原因并归证据不足，绝不冒充 `exhausted` 或非 bind-only。缺少规定尝试不能当作空清单正常耗尽。一次正常战术不适用可以继续其他尝试；未完成的策略不能静默略过。

## 4. P 侧判词与配对条件

首先核验 T 已编译，然后按 §5 检查别名与重述。判词是相对 `(B, R版本, 预算)` 的以下三态，连同完整原因输出：

| 判词 | 必要证据 |
| --- | --- |
| bind-only[R] | T 是对 B 中陈述的受支持呈现变换，或 R(B) 正常找到 T |
| 非 bind-only[R] | 同时满足下面 (a)–(d) |
| 证据不足 | 不能形成上述任一判词，具体缺口单列 |

`非 bind-only[R](T)` 当且仅当：

(a) T 不是 §5 可认证的基底别名或重述；

(b) R(B) 对原任务 T 的结果为 `exhausted`；

(c) R(B + S) 对完全相同的 T 为 `found`，S 是同次交付的其他声明，排除 T 本身、其别名/重述及经依赖闭包藏入的 T；

(d) S 中每条声明均已编译，满足公理与隔离要求。

S 中的每条声明各自按同一规则判形，递归沿有限无环依赖图使用其前置结构，不允许互为证明。容易的 helper 自身仍为 bind-only；其真实消费者及活推导路径按现行规则核对。它可以使 T 的配对搜索成功，不因此升级 helper 的判形。未知的 helper 判形如实报告，不把其未知性当作 content；(d) 的编译义务不能由未知读数代替。

T 的作者证明能够编译，而 R(B + S) 仍未找到时，为“证据不足：结构不足以闭合”；不从作者比 R 强推出 content。S 为空或只含禁用 T 时不能形成搜索约化见证。取得 S 的成本由各声明自身的编译核验承担，其使用与验证成本计入配对命令心跳，不设另一个摊销分数。

对同一呈现规则和基底，若 R 的成功集包含于 R'，则 bind-only 集单调扩大，基底未找到集合反单调缩小。**配对非 bind-only 整体不保证反单调**：加强 R 也可能首次闭合配对搜索。准确的传递规则是：已成立的非 bind-only 在 R' 仍未找到基底证明、且保留配对成功时仍成立；R' 的非 bind-only 必然意味着 R 也没有基底成功。不能把 unknown→非 bind-only 的配对进展隐去。

## 5. 别名、重述与防刷边界

呈现检查先于搜索，针对 B 中实际可用的完整陈述，产出可回放的转换依据。支持的可判规则是：新 def 展开、reducible definitional equality、绑定参数及声明改名、已知合取分量/方向投影和打包，以及明确参数对应下的运输。运输只用基底已取得的映射与等式，并须恢复完整 telescope；新造的语义等价定理不算呈现转换。规则组合必须保留全部量词、假设及目标方向；只有全部所需分量均已存在，打包才属重述。

任意 `P ↔ Q` 证明不是自动重述许可证：该证书自身可能承载新数学。超出上述呈现规则的关系不强行判等，继续搜索或报告证据不足。`statement_id` 相同或不同均不替代这项检查。

薄包装、别名、重述由已有声明恢复原任务时一律 bind-only，不因作者写出更长证明而改变。语义相同、编译器恢复的结构相同的 helper 拆分、打包或改名不改变判词；它们在搜索前按登记的呈现规则恢复，不能额外增加预算。此不变性不主张任意逻辑等价程序具有相同搜索成本。

不得用无关新引理、死依赖、私有化、拆文件、换 deposit anchor、同批新增 pin、选有利任务特例或目标泄漏制造非 bind-only。仍须核对现行活路径条件；只存在于 import/类型/元数据或被投影丢弃分量中的声明不算结构贡献。不得根据受益结果选择 R、基底、预算、S、校准名单或预期。运行失败与知识边界均不能升级。

## 6. AURIC FIB 的律族判词

复用 `LeanInformationAudit.AuricFib.Contract` 的实际 `LawFamily` 与 `LawFact`。固定同一来源族、同一声明域 D，粗坐标为 `Pyramid.X/Y/Z`，细坐标增加 `Pyramid.delta`，不以不同来源或单纯形的可达性代替族内实现。

| 判词 | 实际 LawFact 证据 |
| --- | --- |
| strict | `.separated`：存在 θ、φ∈D，粗坐标相同而 Δ 不同 |
| collapsed | `.identifiable`：所有 θ、φ∈D，粗坐标相同就有 Δ 相同 |
| unknown | 尚未取得任一合规证据；不声称已证不可判 |

strict 与 collapsed 在同族同域互斥。逻辑上“不存在分离对”等价于粗坐标决定 Δ；真实报告的 unknown 是证据缺失，不能由排中律代替取得证明。合规证据缺失时 unknown 保留；两类同时出现是合同或取得错误，不能选有利判词。定性族事实适用于无限域，不因此取得有限计数或概率率。

既有观察 o 的后处理 f(o) 与常量元数据不会切开 o 的同一纤维；加入它们不产生新的分离。定理名、证明身份等仅作元数据，不能作为真实来源状态的新读出。这里不主张完整状态 id 零增益：完整状态映射可能切开旧观察的纤维，须按真实来源与任务检验。对既有读出改名也不能重复计收益。

`.positiveWidth` 的 w>0、`.deltaSign` 的 Δ 定号和某个认证点的数值均不能替代 `.separated`。常值合法概率律族可以同时有正宽度、正 Δ 和 collapsed；模型须包含这一反例。显式任务的 mixed difference、LawPoint、simplex 继承标记、取得状态及有限性边界仍按 AURIC 现行规范解释。

## 7. 与现行规则的衔接

拟议替换只涉及 `CLAUDE.md` §3.2 的判形定义：从无界绑定/规范化读法转为上述相对 R 的三态配对判形。它不授权删除既有声明或重写旧结算；content 名称仅对应有完整配对证据的非 bind-only[R]，不对应 unknown。

§3.2 的活推导路径、有消费辅助声明、模块准入依据和 `open-problem-resolution` 例外，§3.3 用途准入，§3.9 的四槽、登记/issue 边界及既有四个 DTR Observe 判词均保持各自主责。搜索成功不补齐四槽，AURIC strict 不证明 P 侧逃逸，P 侧非 bind-only 不证明信息捕获或实用价值。

本契约 §6 细化 [AURIC FIB ATOM 逃逸审计规范](auric_fib_atom_escape_audit_spec.md) 中律族适配器的 strict/collapsed/unknown 与身份读出边界，沿用其源绑定、取得、任务和数值规范；不改普通四槽入口、输出闭键结构或准入状态。报告器只消费探针证据；R 在构建/探针阶段运行，Inspector 不兼任搜索器。无实际分析合同，不追加 FIB 取得义务。

## 8. 与 owner 字面提问的关系

“只要能写出相关 Lean 代码就是非 bind-only”若取写者为我们、能力无界，薄包装与别名同样能编译，会把它们判为 content，与“新结构让原搜索变容易”及防包装目标冲突。相反，把任意可证明结论都算既有前置的无界闭包，又会令 content 为空。两者都是退化端点。

本契约选择有限、固定、带版本、经独立校准的 R，并要求同一任务上的配对搜索约化。能写出且编译是必要证据之一，不是非 bind-only 的充分条件。这个取舍把“变容易”落到可复现观察，也保留 unknown；它不把 owner 未作出的最终采纳决定写成已授权部署。字面版与本契约版的最终语义取舍归 owner。

## 9. 模型核验、校准与集成范围

判官测试库中的模型须覆盖下表，不能以把两类非空放进假设来证明非退化。有限实例须实际执行正常规则、过滤目标结构并计算判词；它只是可执行契约实例，不声称模拟全部 Lean 战术。

证明源为 [P 侧证据模型](../../../tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/Model.lean)、[有限规则实例](../../../tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/FiniteModel.lean) 和 [实际 LawFact 测试](../../../tools/lean-inspector/LeanInformationAuditFibTests/AuricFib/SearchReduction.lean)。P 模型的编译、呈现认证与隔离标志是经外部核验的输入，不是该模型对真实搜索程序已经正确的证明。

| 标记 | 必核性质 | 对应声明 |
| --- | --- | --- |
| T1 | 无界闭包读法在所有已获证明的候选上退化 | `unbounded_closure_degenerate`、`finite_closure_degenerate` |
| T2 | 字面编译读法把可编译别名也判为 content | `literal_accepts_alias`、`finite_literal_alias_endpoint` |
| T3 | 具体有限规则系统计算得到 bind-only 与非 bind-only 两类非空，搜索成功给出原规则系统中的推导 | `concrete_nondegeneracy`、`genuine_paired_reduction`、`search_sound`、`finite_content_has_derivation` |
| T4 | 受支持包装/别名/重述为 bind-only，规范化后的 helper 拆分与改名不改判词 | `restatement_bind_only`、`all_baseline_presentations_bind`、`helper_renaming_invariant`、`helper_splitting_invariant` |
| T5 | 成功集包含时的单调方向及配对判词的限定 | `union_found_iff`、`union_exhausted_iff`、`bind_only_monotone`、`baseline_miss_antitone`、`paired_content_preserved`、`paired_content_not_globally_antitone` |
| T6 | S 中 T 及其重述的过滤防止自我配对，真实不同结构仍可闭合 | `dirty_structure_not_content`、`target_alias_cannot_close`、`mixed_target_leak_rejected` |
| A1 | 实际 LawFact 命题上的 strict/collapsed 互斥，三态证据判词穷尽 | `strict_collapsed_exclusive`、`capture_exhaustive_exclusive`、`capture_strict_iff`、`capture_collapsed_iff`、`capture_unknown_iff` |
| A2 | 后处理及身份元数据不增加原观察的分离 | `postprocessing_no_new_separation`、`full_state_identity_can_separate` |
| A3 | 合法常值律族的正宽度与正 Δ 不推出 strict | `positive_width_and_sign_not_strict` |

校准集在首跑前由实施方提名、独立评审后冻结声明全名、首次引入前的基线与预期。真实负例包含 `SubstitutionTowerClause` 别名及合成防刷实例。正例只是待核候选，不能直接当已校准名单：`archimedean_jump_decomposition`、`finite_acyclic_judging_graph_has_root`、`two_state_locality_yields_incremental_preservation`、TimeBoundedTwoPointPrice 与 MarkerHistorySearch 方向。缺经核验的正例，校准未完成。

受益单元 #18865、#18866、#18867、#18868、#18898、#18899 不得进入校准集。冻结 R 后才对其关键声明报告字面版、新契约版、旧 evaluator 三栏，保留失败及不确定原因。

判官与政策改动保存在独立 lane，经独立评审安装到受保护 integration；以实际应放/应拦触发及 required checks 验证输入、候选版本和输出。模型编译与本地检查不是集成部署证据。交付范围止于集成测试，不合 dev；准入及 CLAUDE.md 的采纳另循 owner 决定和评审 PR。
