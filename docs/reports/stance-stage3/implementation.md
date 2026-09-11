# 表态更正阶段 3：七模块十四条

已为指定十四条建立可复核来源链并改为 FromLiterature；judge (a) 14、(b) 0、(c) 0，指定范围未触及项 0。
其中十三条为 theorem，一条 quantumMutualInformation 为定义。没有新增数学命题或首次冻结。
本报告来自 Codex 实施席 K 的取回核对和单点自查，不冒领独立评审。
基线为 `60c8c31c5b135cf0ccbb52beae9e47059b2dd896`，分支 `lane/math/stance-stage3`。
用户明令不改 Lean，本次 `.lean` 改动为 0；不重判第 17 轮的总体分类。

## 范围与逐条来源链

开工时逐模块数渲染文档中的 `*Source.* Repository-derived.`，与 brief 完全相符。
[scope.json](scope.json) 列出十四条完整 GID、各自三选一判定、note 和推导链。
下表模块前缀为 `D5/S3/`；source before/after 是实际渲染条数。

| 模块 | before → after | 原有 Citation 原样保留 |
| --- | --- | --- |
| `Quantum/Divergence/DualAccountFull` | 2 → 0 | 0 |
| `Quantum/Divergence/GibbsVariationalIdentity` | 2 → 0 | 1 |
| `Quantum/Divergence/SpectralReadoutEntropyEquality` | 1 → 0 | 0 |
| `Quantum/Information/CoherentCopyCorrelationTax` | 5 → 0 | 0 |
| `Quantum/Information/CorrelatedGibbsEnergyIdentity` | 1 → 0 | 3 |
| `Quantum/Information/PartialTraceMutualInformation` | 1 → 0 | 6 |
| `QuantumBounds/FubiniStudyRecordTime` | 2 → 0 | 1 |

十四条的来源不是同名检索断言，而是以下明确陈述和标准直接推论。每项 note 都含
Verified locator 原文、两个 locator 键且恰一个非 null、已注册 Quantum 桶和核实边界。

| 声明 | note | 可核对连接 |
| --- | --- | --- |
| `dual_account_full` | `watrous2018entropicidentities` | Pinching (4.7)-(4.8), spectral calculus (1.145), relative entropy (5.85); rank-one overlap 1/d and Z-fixed state give Phi_X(rho)=I/d; substitute uniform identity into each conjunct, including d=1. |
| `entropy_freedom_segment` | `watrous2018entropicidentities` | Entropy definition 5.17 gives S>=0 on a density spectrum; Proposition 5.22 gives D>=0; uniform-reference identity supplies S+D=ln d. |
| `log_gibbs_state` | `watrous2018entropicidentities` | Spectral calculus (1.145): ln(exp h_k/Z)=h_k-ln Z for Hermitian H, Z>0. |
| `entropy_uniform_identity` | `watrous2018entropicidentities` | Definitions 5.17-5.18, (5.83), (5.85) plus spectral calculus: H=0, Z=d, G=I/d, trace rho=1. |
| `spectral_readout_entropy_eq_iff_isDiag` | `baumgratz2014coherence` | Pages 2-3 (C1′), its explicit applicability to relative coherence and (8); normalize arbitrary nonnegative A by t=Tr A, cancel ln t; t=0/empty carrier separately; repeated eigenvalues allowed. |
| `coherentCopyState_correlated_entry` | `watrous2018entropicidentities` | Matrix-unit expansion of V rho V*, V|i>=|i,i>; spectral/isometric setup in (1.145), Prop. 5.19. |
| `marginalRight_coherentCopyState` | `watrous2018entropicidentities` | Partial trace (1.120)-(1.121), (2.34); tracing |i><j| gives delta_ij, hence Delta(rho). |
| `marginalLeft_coherentCopyState` | `watrous2018entropicidentities` | Same tensor partial-trace formulas with factors interchanged; actual retained marginal equals Delta(rho). |
| `vonNeumannEntropy_coherentCopyState` | `watrous2018entropicidentities` | Proposition 5.19, (5.93), with V*V=I; includes singular states. |
| `coherent_copy_correlation_tax` | `baumgratz2014coherence` | Decomposition before (8), equation (8) + Watrous (5.91), copy marginals and isometric entropy; I=2 S(Delta rho)-S(rho)=S(Delta rho)+D(rho||Delta rho). |
| `von_neumann_entropy_unitary` | `watrous2018entropicidentities` | Proposition 5.19 / (5.93), with the isometry square and unitary. |
| `quantumMutualInformation` | `watrous2018entropicidentities` | Equation (5.91), with both subsystem states the actual partial traces (2.30)-(2.34); this entry is a definition, not a theorem. |
| `record_time_lower_bound` | `quair2026projectiveangle` | projectiveAngle_triangle phase alignment + orthogonality angle pi/2 + the two supplied displacement bounds; solve pi/2<=2 E tau/hbar. |
| `record_count_upper_bound` | `quair2026projectiveangle` | Apply the preceding lower bound N times and sum; the explicitly assumed sequential budget gives N<=4ET/(pi hbar), including N=0. |

新建 Watrous 与 Baumgratz 两篇 note；扩展已有 QuAIR note 的两个条件推论和核实边界。
三个 note 的全文分别在 [Watrous](../../../Library/Quantum/watrous2018entropicidentities.md)、
[Baumgratz](../../../Library/Quantum/baumgratz2014coherence.md)、
[QuAIR](../../../Library/Quantum/quair2026projectiveangle.md)。
Watrous 的 PDF 为作者托管的 2018 年预出版稿；不冒称逐页核对出版商印本。
Baumgratz 定位在 v3 的 (C1′)、其适用于 relative coherence 的明确陈述、(8) 前的分解和 (8)。
纸面源使用的熵底数统一换成 nats；奇异态支撑包含关系在 note 中单独核对。
谱读出允许未归一化谱、零谱、空指标和重根，note 给出缩放和零和两分支。
FS 两条仅使用给定的位移不等式和顺序接触时间预算，不宣称推导物理速度定律。

原有十一条 Citation 的完整条目（公式、正文、引文）与基线逐字节相同。
谱读出尚未带引文的说明原称等号使每行只有一个单位项；这在重根时错误。
已按原 Lean 活证明更正为“每行非零支撑上谱值等于该行均值”，再由
`U diag(x) = diag(p) U` 得对角性；常数谱配 Hadamard 酉矩阵是旧说明的反例。
这里修正叙述，不改变正式结论。

## 第 3.2 条逐声明账

[declarations.json](declarations.json) 对七模块的全部 34 条用户声明的公开 theorem
以及本次绑定的互信息定义，逐项给出 proof_shape、直接冻结依赖的 GID + statement_id、
escape_witness、admission_basis、历史登记来源及当前 axiom 闭包。
同模块的已冻结公开前置也计入直接依赖。生成的内部 theorem/结构投影不是新公开定理；
若它们被证明使用，在依赖列表中保留相应身份并将假设投影标成 hypothesis-projection。
定义依赖列在同一列表并明确标注角色；type_frozen_dependencies 另列类型侧依赖。
所有 statement_id 直接读 canonical report，未从历史输入重算旧身份。

依赖提取用当前已 elaborate 环境的 `getConstInfo` / `Expr.getUsedConstants`，
递归展开 private 常量，在 public 常量停止；原始输出和临时检查源在 attempt 的
`dependencies.jsonl`、`inspect-dependencies.txt`。检查源经 `lake env lean --stdin` 输入，
不产生任何仓内 `.lean` 编辑，不调用裸 lake build。
此常量图不自动证明语义判形或 ζ/β/ι 归约后的活性；判形另结合实际证明和历史登记。
Mathlib 前置不冒充冻结 D5 节点，RHLinalg 命名空间的 D5 前置仍按真实模块归属记录。

本次基线上各模块已经冻结，因此所有 `admission_basis` 为 null，明确解释为
`not-applicable: existing-frozen; stance-only`；不伪造三选一之外的新准入类别。
历史准入依据另列历史字段，不用于申请本次首次冻结。
以下 content 是已有证明中的构造形态，不是相对于文献的新颖性申报；其见证已在历史材料中登记。

| 模块 / 声明 | proof_shape | escape_witness |
| --- | --- | --- |
| `DualAccountFull.dual_account_full` | bind-only | null |
| `DualAccountFull.entropy_freedom_segment` | bind-only | null |
| `GibbsVariationalIdentity.log_gibbs_state` | bind-only | null |
| `GibbsVariationalIdentity.gibbs_state_zero` | bind-only | null |
| `GibbsVariationalIdentity.gibbs_state_posDef` | bind-only | null |
| `GibbsVariationalIdentity.partition_function_pos` | bind-only | null |
| `GibbsVariationalIdentity.partition_function_zero` | bind-only | null |
| `GibbsVariationalIdentity.entropy_uniform_identity` | bind-only | null |
| `GibbsVariationalIdentity.gibbs_variational_identity` | bind-only | null |
| `SpectralReadoutEntropyEquality.spectral_readout_entropy_eq_iff_isDiag` | content | All row-support equality constraints yield U diagonal(x) = diagonal(p) U, and unitarity reconstructs a diagonal conjugate. |
| `CoherentCopyCorrelationTax.coherent_copy_correlation_tax` | bind-only | null |
| `CoherentCopyCorrelationTax.marginalLeft_coherentCopyState` | bind-only | null |
| `CoherentCopyCorrelationTax.marginalRight_coherentCopyState` | bind-only | null |
| `CoherentCopyCorrelationTax.coherentCopyState_correlated_entry` | bind-only | null |
| `CoherentCopyCorrelationTax.vonNeumannEntropy_coherentCopyState` | content | The explicit copyHom transports functional calculus and preserves trace, including zero eigenvalues. |
| `CorrelatedGibbsEnergyIdentity.energy_information_identity` | bind-only | null |
| `CorrelatedGibbsEnergyIdentity.von_neumann_entropy_unitary` | bind-only | null |
| `CorrelatedGibbsEnergyIdentity.gibbs_relative_entropy_energy_difference` | bind-only | null |
| `CorrelatedGibbsEnergyIdentity.marginal_entropy_change_eq_mutual_information_change` | bind-only | null |
| `PartialTraceMutualInformation.partialTraceLeft_add` | bind-only | null |
| `PartialTraceMutualInformation.partialTraceRight_add` | bind-only | null |
| `PartialTraceMutualInformation.trace_partialTraceLeft` | bind-only | null |
| `PartialTraceMutualInformation.trace_partialTraceRight` | bind-only | null |
| `PartialTraceMutualInformation.quantumMutualInformation` | not-applicable(definition) | null |
| `PartialTraceMutualInformation.marginalLeft_productState` | bind-only | null |
| `PartialTraceMutualInformation.marginalRight_productState` | bind-only | null |
| `PartialTraceMutualInformation.partialTraceLeft_kronecker` | bind-only | null |
| `PartialTraceMutualInformation.partialTraceLeft_posSemidef` | bind-only | null |
| `PartialTraceMutualInformation.partialTraceRight_kronecker` | bind-only | null |
| `PartialTraceMutualInformation.partialTraceRight_posSemidef` | bind-only | null |
| `PartialTraceMutualInformation.vonNeumannEntropy_productState` | bind-only | null |
| `PartialTraceMutualInformation.quantumMutualInformation_productState` | bind-only | null |
| `FubiniStudyRecordTime.fs_angle_triangle` | content | Simultaneous endpoint phase alignment makes both adjacent real inner products equal their complex moduli while bounding the endpoint real overlap by its modulus. |
| `FubiniStudyRecordTime.record_time_lower_bound` | bind-only | null |
| `FubiniStudyRecordTime.record_count_upper_bound` | bind-only | null |

与旧预登记的区别明确如下：CoherentCopy 的最终 tax 在原首次冻结报告中为 content，
其拟议见证是同模块保熵定理；该前置在本次基线上已经冻结，故本次相对于冻结前置观察为
bind-only。保熵构造本身仍是 content。没有改原预登记，没有新提案，也没有据此追认新准入。
FS 时间/计数与 PartialTrace 的同模块前置如今也已冻结，故依赖列表与旧报告的
“无直接冻结公开前置”不同；形态不变。PartialTrace 保留其历史报告对移植证明的
bind-only / rule-11-upstream-wrapper 判断，尤其不把张量谱熵移植申报为本仓新逃逸。
Gibbs 的七条均延续旧报告 bind-only；DualAccount 延续 v2 的 bind-only。
谱读出的行支撑约束与矩阵重构正是原 stage B v1 的具名拟议见证。
CorrelatedGibbs 本次只观察现有冻结证明；未重新裁判或补造其历史准入依据。

## 第 3.1 条检索收据与核实边界

本次实际网络能力为 requests/curl HTTP 读取；浏览器搜索入口能返回 HTTP 200，但其内容
未必可用。没有修改宿主全局配置，也不声称穷尽搜索。以下是本次的命中和未命中范围；
旧报告中的其他检索属于历史记录，未当作本席亲验收据。

| 查什么 | 在哪查 | 本次结果 |
| --- | --- | --- |
| pinching、relative entropy、Gibbs、partial trace、mutual information、FS | 本仓 D5 七模块、其实际依赖及 Library 既有 note | 命中目标实际定义和定理，核对域与假设；用于追踪行动对应，不把仓内命名当作外文献标题。 |
| log_smul、log_exp | 钉版 Mathlib 的 ContinuousFunctionalCalculus/ExpLog/Basic.lean | 命中 `CFC.log_smul'`（144）、`CFC.log_exp`（164）。 |
| strictConvex / mul_log / map_sum_eq | Mathlib Log/NegMulLog.lean、Convex/Jensen.lean | 命中 `Real.strictConvexOn_mul_log`（137）、`StrictConvexOn.map_sum_eq_iff'`（275）。 |
| angle triangle | Mathlib Euclidean/Angle/Unoriented/TriangleInequality.lean | 命中 `InnerProductGeometry.angle_le_angle_add_angle`（192）。 |
| quantum entropy pinching mutual information Watrous | Google | HTTP 200 为 JS/interstitial 页面，未取得可用结果；不作来源证据。 |
| relative entropy coherence pinching Baumgratz | Google | 同上，未取得可用结果。 |
| Fubini Study distance triangle inequality orthogonal | Google | 同上，未取得可用结果。 |
| density matrix pinching mutually unbiased measurements maximally mixed | Bing | HTTP 200 但返回不相关结果，未使用。 |
| Gibbs state logarithm variational principle quantum relative entropy | Bing | HTTP 200 但返回不相关结果，未使用。 |
| isometry entropy preservation partial trace mutual information | Bing | HTTP 200 但返回不相关结果，未使用。 |
| Fubini Study distance triangle inequality | Bing | HTTP 200 但返回不相关结果，未使用。 |
| partial trace / spectral calculus / pinching / relative entropy / mutual information / isometry | Watrous 作者托管 PDF，全书文本定向检索后读相应内页 | 命中 (1.120)-(1.121)、(1.145)、(2.30)-(2.34)、(4.7)-(4.8)、(5.82)-(5.85)、(5.91)、(5.93)、Propositions 5.19、5.22；页码见 note。 |
| relative entropy of coherence / vanishing / diagonal | arXiv 1311.0275v3 PDF 和摘要页 | 命中 pp.2-3 的 (C1′)、其适用性、(8) 前分解和 (8)，亲读内页。 |
| projectiveAngle_triangle | QuAIR/Lean-QIT 固定提交源码 | 命中并亲读完整相位对齐证明；源码 hash 见收据。原包编译和传递公理闭包未重跑。 |

[retrieval-receipts.json](retrieval-receipts.json) 逐件记录 URL、HTTP 状态、字节数、SHA-256
和本地取回文件。正文定位均已亲读；source snippets 不承担证据。
未经本席亲验的是作者引用的更早文献、优先权、出版印本的逐页一致性，以及 QuAIR 原包编译；
各 note 末节明确以 `ASSUMED-UNVERIFIED` 标出，未把转述升格为亲验。
本席亲验标准替换与有限维代数，未声称找到了同名的 tax、dual-account 或 record-time 文献定理。

## 计数与门链

计数口径为逐行包含字面串，等同 `grep -c sorry/axiom/instance`；模块行数等同换行行数。
`axiom` 命中全部来自 `#print axioms`，故另列真正 axiom 声明数，不能把打印命令当作新增公理。

| 模块 | 行数 | sorry | axiom 字串 | axiom 声明 | instance |
| --- | --- | --- | --- | --- | --- |
| `DualAccountFull` | 141 | 0 | 2 | 0 | 0 |
| `GibbsVariationalIdentity` | 137 | 0 | 2 | 0 | 0 |
| `SpectralReadoutEntropyEquality` | 126 | 0 | 1 | 0 | 0 |
| `CoherentCopyCorrelationTax` | 200 | 0 | 1 | 0 | 0 |
| `CorrelatedGibbsEnergyIdentity` | 145 | 0 | 4 | 0 | 0 |
| `PartialTraceMutualInformation` | 335 | 0 | 5 | 0 | 0 |
| `FubiniStudyRecordTime` | 106 | 0 | 3 | 0 | 0 |

35 个报告对象的 axiom 闭包逐条均为 `[Classical.choice, Quot.sound, propext]`；
没有 sorryAx。全部七模块合计 1190 行，sorry 0、axiom 字串 18、axiom 声明 0、instance 0。
这不是以 grep 代替 kernel 判绿：如下退出码和 canonical report 承担验证。

1. 指定绝对路径 `serial-lean.sh` exit 0。哨兵：
   `SERIAL_LEAN status=complete built=1 failed=0 missing=1 tree=/Users/chronoai/trureturing-quantumobs2`。
   缺失项是构建前的工作队列计数；完成后缺失 olean 列表为空。复用已钉缓存，未重编巨型模块。
2. `make lean-report` exit 0；`LEAN_REPORT_DELTA mode=delta changed=0 added=1 removed=0 recheck=1`。
   canonical raw report SHA-256：`8dc4de0afe9cb1c054803a13c7c516f98cf74324a23d83d193f14ff5ce18c441`。
3. `make emit` exit 0，先生成七篇；说明排版和边界补充后再次 emit exit 0。
4. `make deposit ATOM_ID=00ebe34ede79d85818ef1975483cc304615967a0925f809c6746b0f49585643b GID=D5/S3/QuantumBounds/FubiniStudyRecordTime.record_time_lower_bound BASE=origin/dev`
   exit 0。`DEPOSIT_HEADER_CHECKED SL-012`；`module-already-frozen`，既有覆盖相同。
   内部打印 `COVER_INVALID ... already has coverage`，其后由 playbook 明确归因为
   `PLAYBOOK_SKIP command=cover detail=coverage-already-applied`，不是新增 coverage 失败被隐藏。
5. 指定内容检查 exit 0，使用上述精确 merge-base SHA；`^RED` 行数 0。
   `DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11356 suspected_novel=0 formula_content_slots=68 formula_statements=32 red=0 observe=5053`。
   另有 `markdown: judged=7 formula(s)=25 red=0`；完整哨兵见 [gate-receipts.log](gate-receipts.log)。
6. 用户授权的 commit → push；不建 PR。最终提交号和推送结果由 runner envelope 记录。

## 未成功的尝试与限制

- Google 三个查询得到 JS/interstitial，Bing 四个查询结果不相关；均未用作证据。
- 系统无 pdftotext、pymupdf/pypdf/bs4；在 attempt 外的临时 venv 安装 PyMuPDF、BeautifulSoup、requests 后解析成功，未加仓库依赖。
- 初次本地检索含未加引号且不存在的 `.lake/packages/lean4*`，zsh 报 no matches found；改用真实路径。
- 大篇读取有工具截断，按需分段读取所用内页/代码；不把被截断的未读内页当作已经核验。
- 临时依赖检查第一次把 private/generated 声明当公开目标，Lean 名字引号遇数字节失败（unexpected identifier after decimal point）；筛至 35 个真实公开目标。
- 第二次依赖检查未限定 `liftIO` 名字，Lean 报 unknownIdentifier；改用 `Lean.Elab.Command.liftIO` 后成功，35 行完整 JSON。两次失败日志保留。
- 初版“已带引文条目原样保留”核对器只识别 Theorem/Definition，漏了 Lemma，误将 CorrelatedGibbs 的新引文与前一旧条目拼接；补入 Lemma 分隔后十一条全部逐字相同。真实 diff 从未改旧引文条目。
- 最后一次 scribe 绑定搜索的花括号路径含空格，zsh 报 parse error near }；改用七个完整文件路径后命中全部绑定。
- 早先进度说明曾把七项合计写成缺一项的六个加数；已纠正，开工机器计数和实际目标一直为十四。
- urllib3 对宿主 LibreSSL 的支持警告不改变取回的成功 HTTP 状态；以保存字节/hash 为收据。
- deposit 的重复 coverage 提示如上原样入账；无 Lean 编译失败、无门规则删改、无本次被杀或孤儿清理。

完整构建、检索、失败检查和内容检查输出保留在用户指定 attempt 目录；
本报告与结构化附件负责可复核的逐条结算，不以单点自查冒充独立评审或 CI 已远程运行。
