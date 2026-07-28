# SPEC:飞轮从消化残余取 formalize 目标(digestion-sourced formalization)

> 由 sshx 6 席对抗共识产出(teleology/parsimony/fidelity/natural-ownership/proportional-containment/worth 全 `revise` → meta-layer convergence)。每前提对 `Meta/BACKFILL.yaml`、`Meta/StrataLint/StrataLint.Engine/Digestion/*.cs`、`packages/theory-selfgrowth/*` 源码核实。**设计文档,非实现。**

## 0. 摘要

飞轮真值 deposit 的正源是**消化账本残余**——理论卷已 digest 成 typed atom,其中 `truth=open ∧ coverage_gids=[] ∧ kind∈{定理,命题,引理,推论}` 的是待 formalize 的 grounded 目标(带理论陈述+对手轮推导,比 proposer's-choice 从零发明命题可靠得多)。本 spec 让 producer 从这个残余取目标,**取代** proposer's-choice("Deliver ONE NEW D5 result, proposer's choice"),并在 formalize 完成后把新 Lean GID 回填 atom 的 `coverage_gids`,推进消化 + 沉淀真值。

## 1. 证据级更正(sshx 多席亲核,推翻筹备期假设)

1. **`make ingest` 不自动回填 coverage(必须新建显式 cover 操作)** — `DigestionIngestor` 只给新 residual atom 初始化 `CoverageGids: []`;`IngestCommand` 只刷新 projected status;`DigestionStatusEvaluator` 只**验证账本里已存在**的 GID/coverage/scribe receipt。全 production C# **无把 coverage 设非空的赋值点**。所以"formalize 后 make ingest 自动 join atom↔GID"是**错的假设,从 spec 删除**;须新建 digestion-owned 的显式 cover 事务。
2. **候选数是 ~234,不是 264** — 264 是按 atom 首行文字 kind 统计;**权威的 ast_path kind**(封闭集 {theorem,proposition,lemma,corollary})∧ truth=open ∧ coverage 空 的严格候选是 **234**(另 ~28 atom 已有 coverage)。spec 不固化数字——候选每轮由账本派生。
3. **"ready" = dispatchability,非 provability** — 账本无难度/依赖字段。ready 只表示"结构上可发出的 exact formal-claim atom",**不表示易证**。禁伪造 tractability/worth/depth 分(那是 frontier-generation.json 被 declined 的 worth 幻数)。可证性由 formalize workflow 的成败给出。
4. **TheoryIsolation 不禁 producer 读账本** — `TheoryIsolationPolicy` 禁的是"其他程序/Lean 固化 docs/theory 路径";**BACKFILL/CAS 是消化机器的产物数据**,读它不越界。但 Lua 直解析 YAML/CAS 会复制 `BackfillInventoryLoader`/CAS/status 语义 → 应经 canonical StrataLint 只读查询,不直读。

## 2. 4 段单-owner 管线(natural-ownership 席收敛)

```
digestion query        producer (theory-selfgrowth)     formalize workflow          digestion ingest
拥有:账本/CAS 解读      拥有:tick+确定选序+去重+发单     拥有:NL陈述→Lean命题语义      拥有:BACKFILL coverage/
+ eligible 投影(只读)   ─候选投影─►                       对应+非空洞+证明交付          receipt/status 写事务(独占)
                                    ─请求(atom身份+陈述)─►                  ─completion receipt─► ─cover事务─►写账
```

**候选谓词(机器可判,单一真源=账本派生)**:`status.migration=residual ∧ status.truth=open ∧ coverage_gids=[] ∧ ast_path kind∈{theorem,proposition,lemma,corollary}` ∧ CAS 存在且 hash 匹配 ∧ alignment=seen。空集=诚实 no-op。

**选序(反 Goodhart)**:canonical FIFO(账本 `(source_id, atom_id)` ordinal)+ generation round-robin 保公平;**禁 easy-first/难度/随机**(不以难度降数学野心)。terminal-blocked 的 atom 只作执行去重暂跳过,**不从账本 residual 删除**(GitHub 历史不是第二真值队列);basis/epoch 改变后可公平重试。

## 3. 落点(具体工件)

**(1) 只读候选投影** — `Meta/StrataLint/StrataLint.Cli/Commands/DigestStatusCommand.cs` 加 `--formalize-candidates --json` 模式(或专用子命令)。复用现有 loader/CAS verifier/status evaluator,fail-closed。输出每候选:`{schema, ledger_sha256, source_id, atom_id, ast_path/kind, cas_ref, raw_sha256, atom_text(理论陈述+推导)}`,按 ordinal 稳定排序。**不落第二队列,不扫 docs/theory,不把理论编号映射为 Lean 地址**。任一全局解析/校验错误 fail-closed。

**(2) producer 换源** — `packages/theory-selfgrowth/{core.lua, departments/propose/main.lua}`:调 (1) 的投影(不直读 YAML),按选序取一个从未发出的候选;沿用 one-open-request 排他,marker 从 generation 收缩为 `digestion-atom:<atom_id>:<cas_ref>`。请求仍用 `Deliver ONE NEW D5 result:` 路由前缀,**body 携版本化 envelope**:atom_id、cas_ref、raw_sha256、**byte-exact atom 陈述+推导**、要求"产出恰好一个新 declaration-level Lean GID + Blueprint 镜像"。**修 `gh issue list --limit 100` 分页**(234 存量 attempt-count 需全历史)。空集/投影异常/超 12000-byte body 上限=诚实 no-op。

**(3) formalize 条件契约** — `blueprint-then-formalize` workflow 加 ledger-backed 条件分支:若请求带合法 digestion envelope,则**禁 proposer's-choice**,必须 formalize 该 atom 的**实质命题**(不得改弱/只取方便子句;允许 helper declaration 但须**恰好一个覆盖完整 atom 的 primary GID**);同一 PR 交付新 F 声明 + B 镜像;产出 `digestion-formalization-v1` completion receipt(绑 atom_id、cas_ref/source hash、base tree、primary GID、target hash、Blueprint declaration ref、语义忠实/非空洞机器判词)。

**(4) digestion-owned cover 事务** — `IngestCommand.cs`/`DigestionIngestor.cs` 扩 `--cover-atom <atom_id> --gid <decl_gid>`(或等价 envelope 输入)。**唯一写 BACKFILL 的路径**。原子地在**全部**下述条件通过后才写 `coverage_gids` + coverage/scribe receipt + 派生 status,否则**BACKFILL 字节不变**:
- atom 仍 `open ∧ coverage 空`,CAS/fingerprint 与 envelope 一致(未漂移);
- GID 是带 declaration selector 的 canonical GID(非 path-only/module-only),相对 base 为**新增**;
- raw Lean report 中该声明存在且 TruthDag=**Closed**,无 sorry/私有/未注册 axiom;
- verified Scribe 精确引用该 declaration;source/target/definition/emission hash 全匹配;
- 唯一映射(零/多匹配、重复绑定拒)。
**成功判据不是"coverage_gids 非空",是目标 atom 事务后 absorbed-closed 无 gap**(partial-closed 仍算失败,不假结案)。相同映射幂等,replay byte-identical。

## 4. THE 未解 gap:语义忠实/防空洞(6 席一致点名——`implement` 前必须收口)

结构门(新/Closed/无sorry/有Scribe/hash匹配)能拒空回填/旧GID/sorry/缺Blueprint,**但拦不住** `theorem t : True := trivial` 这种**忠实覆盖了错命题**的空洞——kernel/hash 不证"自然语言 atom ↔ Lean type 语义等价"(一般不可判)。spec 必须三选一并获后续一致:

- **(a) pre-committed signature(推荐主干)**:formalize workflow 在**证明前**产出机器可比对的 formal Lean signature/typed-claim receipt;cover 事务只接受与该预承诺 signature **完全相同**的 declaration。把"猜 WHAT"从证明后前移到可核对的承诺。
  - **实现状态(P0 已落)**:`digestion-formalization-v1` receipt(engine 内 `DigestionFormalizationReceipt`,closed-schema fail-closed loader)+ cover `--envelope`。receipt pin `atom_id / primary_gid / precommitted_signature{name_key,kind,type} / cas_ref / raw_sha256`;cover Gate②(c) 由 file-newness 换成 **declaration-signature match**(deposited 声明当前签名须完全等于预承诺签名)——base 无关,故消除旧 `--base <deposit-origin>` workaround,并挡"证后 swap 成 True"。receipt 的**产出/提交**(formalizer / workflow step1)与 §4(b) 空洞防护仍未做。
- **(b) 多模型对抗 attestation(补充,诚实标非证明)**:formalize 的机器共识门对抗验证"Lean statement 忠实对应 atom 且非 vacuous/trivial",产 durable receipt。**明确标记这是 attestation,非形式证明**(NL↔Lean 等价不可判);多模型独立(第14条)降空洞风险,但不冒充 kernel 保证。
- **(c) 收窄到 machine-form atoms**:若不接受 (b) 的 attestation 为信任边界,候选收窄到自带机器可解析 formal signature 的 atom——**当前可交付量可能为 0**,须诚实允许。

**收敛推荐 = (a)+(b)+负例 fixture**:pre-committed signature match(结构可判)+ 多模型对抗忠实 attestation(诚实标 attestation)+ **负例**(任意 atom 覆盖到 `theorem t : True` 必须被拒)。这是无人审下 NL↔Lean 忠实性的最佳机器可核近似,不冒领为证明。

## 5. 验收 fixtures(RED-first)

kind 排除(observation/remark/definition 不入)· CAS/ledger 漂移 fail-closed · deterministic 选序 + generation 轮转公平 · active-request 去重 · 空集/超长 body no-op · same-atom replay 不重发 · **深定理失败→零账本变更 + 下一代轮转**(不降格命题不卡死)· 旧GID/module-only GID/缺 declaration/sorryAx/未注册 axiom/缺 Scribe/hash mismatch **全拒** · **hollow `theorem t : True` 覆盖任意 atom 必拒** · happy path 唯一新 GID + atom absorbed-closed · cover replay byte-identical。

## 6. worth(值不值,worth 席)

**值得,但先建最薄的 grounded vertical slice,不按"264 ready 目标"立项完整智能选择器。** 相对 proposer's-choice:精确 atom 内容直接消除无命题的 formalize-fatal,每次成功=可结算的消化进度。234 严格候选中 203 个文本含 closed/已证标记、123 个 <500 bytes、含 Fermat/Wilson/Fibonacci 恒等式等明显可试项——**真实可交付量大概率非零,但这是启发式,机器认证 ready 数仍为 0**。成本复用现有 Lean/Scribe/status/receipt 验证可控。**先做 bounded pilot(canonical 顺序非容易度取样),观测到≥1 个过全 gate 的真实 coverage closure,才扩成持续飞轮**;若全 no-change/fatal,诚实停在空产出,不加主观 tractability 分。

## 7. 对抗轨迹 + 未解项(诚实)

6 席全 `revise`:方向(消化残余为源)对,收口 4 段管线 + owner 分离 + 反 Goodhart 选序 + 显式 cover 事务;THE gap = 语义忠实(§4)。**`implement` 前须先定 §4 的 (a)/(b)/(c) 并获后续一致**——这是本 spec 唯一未闭 conflict edge(NL↔Lean 语义等价机器不可判,是硬开放问题非机制 bug)。次要待定:投影/envelope 精确 schema+原子性、issue >100 分页、round-robin 在候选集变动下的公平性、host 能否稳定调 StrataLint 取 raw Lean report。ASSUMED-UNVERIFIED:234 中实际能无新 axiom 忠实 formalize 的数量;多模型 consensus 能否作可重放抗自证的语义判词;atom_text 加 envelope 是否全落 12000-byte body。
