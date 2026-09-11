# A373409 implementation, 2026-09-10

产地：Lean 技能；Codex 主循环单席实施、单点自查，尚无独立评审。
用户提供的 orchestrator 平方筛读数是上游输入，本席不冒领为亲验。

## 预登记与陈述回声

- 第一档：OEIS A373409 的无界 antirun 长度上界 9；文献状态待本席联网核对。
- `FullNonsquarefreeInterval l` 必须同时要求严格递增、逐项非平方自由，以及对任意
  `a ∈ l`、`b ∈ l`、`a ≤ n ≤ b`，若 `¬ Squarefree n` 则 `n ∈ l`。
  最后一项禁止稀疏抽选；空列表与单项列表也有明确语义。
- 拟议 escape_witness：4、9 的倍数给出的两族相邻障碍，及其间跨度 18 的
  十项装填必占同奇偶位置、与必含的 4 倍数冲突。原 brief 称“19 格”，
  这里区分格数 19 与端点差 18；完整论证仍为 ASSUMED-UNVERIFIED。
- 长度 9 的指定实例仅作 private 尖锐性引理，不作独立准入依据。
- 成：无界上界经 kernel 验证、make lean EXIT=0、零 sorry/私 axiom、PR 开出。
  翻：给出 kernel 反例。blocked：列路线、失败边界与最锐剩余子命题。
- 不新建理论卷、不 ingest、不自造 atom；冻结用既有 ledger-align --add 路径。

## 初始收据

- 工作树 `/Users/chronoai/trureturing-a373409`，分支 `lane/math/a373409`，初始干净。
- HEAD/base：`b1c34e4ffff0e67321c1ed9ec60b9eea741e239f`。
- 完整阅读 CLAUDE.md；读取 agents/CONTEXT.md、spec A5/A5.1 与 Meta/domains.yaml。
- Lean pin `v4.33.0`；lake-manifest mathlib rev
  `db584cd6d46c92f209a44c0f1c829460d327499d`。
- D5 检索：`rg -n -i 'A373409|A373573|A373574|A068781|antirun|nonsquarefree|non.squarefree' D5`。
  无目标精确命中；只命中 PrimeWordAntipodeParityStepBridge 的 Möbius 零值引理。
  另读 SquarefreeSquareDecomposition：讨论平方自由分解唯一性，与目标不重合。
- 初始 `.lake` 不存在；已启动 `make lean-cache-ensure`，未运行裸 lake。
- 报告目录初始直接文件数 37（`find docs/reports -maxdepth 1 -type f | wc -l`）。

## 未主张

尚未主张数学论证闭合、Lean 通过、第三方检索完成、冻结成功或 PR 已开。
尚未亲验的 OEIS 页面与外部文献均为 ASSUMED-UNVERIFIED。

## 有序库检索及缓存读数

1. D5：上述检索无目标精确命中。
2. 钉版 Mathlib：`rg -n -i 'antirun|A373409|A373573|A373574|A068781|nonsquarefree' .lake/packages/mathlib/Mathlib` 零命中。
   `Nat.squarefree_iff_prime_squarefree`、`List.pairwise_iff_getElem`、`List.isChain_iff_pairwise`
   可作基础引理；不是目标全称上界。源文件已打开。
3. 外部实取：OEIS 四个 `/internal` URL 均 HTTP 200；A373409 原文
   “Conjecture: The maximum is 9, and there is no antirun of more than 9 nonsquarefree numbers.”
   A373573/A373574 均问 “Are there only 9 terms?”。
   A068781 给 `36a+8`/`36a+9` 算术级数，没有九项装填证明。
   共同链接的 `https://oeis.org/A373403/a373403.txt` 已读，为序列对照表。
   arXiv Atom API `all:antirun` HTTP 200，totalResults=0。
   GitHub 仓库搜索 `antirun lean`：0；认证代码搜索 `A373409 language:Lean`、
   `antirun language:Lean`：各 0。`nonsquarefree language:Lean`：5 文件，进一步核对中；
   包括多项式分解代码和 LeanTriathlon 的 NonSquareFreeWeird 导入，不能把名称命中当作已有证明。
   leansearch.net 首页 HTTP 200，仅证明访问能力，不冒充已执行语义查询。
   所有原始下载保存在 runner attempt 目录。
4. 缓存：`make lean-cache-ensure` EXIT=0；`status=seeded, method=clonefile`，
   donor=/Users/chronoai/trureturing，clonefile_attempts=1，stamp_miss=null，
   mathlib_missing_olean_files=0，project_olean_state=warm，mathlib_olean_state=warm，
   archive_status=not_attempted，archive_skip_reason="project olean state is warm"。
5. 候选落点 Arith/Congruence：`find D5/S3/Arith/Congruence -type f | wc -l` = 19；
   registered domain Arith/S3，普通自然数的整除与模结构，generality=G。

数学路线细化（仍为预登记）：若取前十项 x0…x9，九个 gap 强制 x9≥x0+18。
令 q=x0/36：x0≤36q+8 时用 8/9 障碍；9≤余数≤27 时用 27/28 障碍；
28≤余数时用下一周期 44/45 障碍。只有中间情形允许跨度18，迫使
x0=36q+9、x1=36q+11；Full 强制 36q+12 在列表内，与 x1 相邻矛盾。
这沿用原拟议见证，仅明确端点，初段也由第一情形统一处理。

## 定义与障碍引理检查点

- `FullNonsquarefreeInterval` 已按三字段落盘：`increasing`、`nonsquarefree`、`full`。
  `full` 的量词覆盖任意两项之间的全部非平方自由自然数，无隐藏的上界假设。
- 热树 API 探针确认 v4.33 使用 `List.IsChain`，brief 的 `Chain'` 更新为该现役名。
  API 探针四个候选名字不存在，已改用编译器确认的
  `List.IsChain.pairwise`、`List.mem_iff_getElem`、`List.pairwise_iff_getElem`。
- `lake env lean D5/S3/Arith/Congruence/NonsquarefreeAntirun.lean` EXIT=0：
  Full 定义、no_neighbors、4/9 整除引理与 upper_of_pair 已验证。
  一条 letI 风格警告按建议改为 let；尚未声称项目 make lean 通过。
- GitHub 命中逐项收窄：打开 LeanTriathlon 的
  `LiveLeanTriathlonSorry/NonSquareFreeWeird/All.lean`（2aede420…），
  目标是 `weird_squarefree_infinite`，证明为 sorry，与本题不同。
  打开 hex-dev 的 EezTests（40585b8…）：命中为多项式分解测试。
  其余三个 hex 文件未打开，明确 ASSUMED-UNVERIFIED，不据文件名宣称完整核验。
- dominating_theorem_search：在已检索/已打开范围未找到本题的已有证明；
  这不是对全部文献的穷尽保证。Library/Arith 实测 48，不能向该桶新增笔记。

## 无界上界与尖锐性内核检查点

- 全称定理 `antirun_length_le_nine` 首次完整实现即编译成功；
  `#print axioms` 为 `[propext, Classical.choice, Quot.sound]`。
- 私有见证经历两次明确失败：`norm_num` 没有化简 Squarefree 常数；默认 `decide`
  卡在 `Nat.minSqFac` 展开。读取 Mathlib 定义后使用 `decide +kernel`（内核归约，
  不使用 native_decide），完整文件编译 EXIT=0。见证公理闭包同为标准三公理。
- `nine_term_witness` 同时验证 Full、全部相邻 gap 与长度=9；不是仅验证九项逐项非平方自由。
- 初段无需单独枚举：余数≤8 的相邻障碍已覆盖，包括自然数 0；
  这给出比正整数枚举略强的陈述，不改变题意中的正整数结论。
- 当前结果不再把障碍/装填论证标为 ASSUMED-UNVERIFIED：它已 kernel 验证。
  尚待 make lean、报告、发射、冻结与 PR；不提前主张项目门通过。

## 项目构建与逐定理判形

首次 `make lean`：EXIT=0，34.817 秒，12808 jobs，macOS 本机 clonefile 热缓存。
日志：runner attempt-1/make-lean.log；读到一条头部 digest 超100列风格警告，已缩短散文头，
将对最终字节再跑门。没有改动数学陈述或证明。

唯一手写公开 theorem：
`D5/S3/Arith/Congruence/NonsquarefreeAntirun.antirun_length_le_nine`。

- proof_shape: content。
- 直接冻结依赖（GID + statement_id）：`[]`。没有 import 任何 D5 模块；
  直接基础来自上述钉版 Mathlib，按第3.2条不计作冻结前置。
- escape_witness: 私有 `upper_of_pair`（相邻非平方自由数对构成障碍），
  与主证明中中间区间的装填等式 `hx1 : x 1 = 36*q+11` 共同承重。
- 第3.2条四项：
  1. 依赖闭包内：主 theorem 的三个分支直接调用 upper_of_pair；hx1 在其证明项内构造。
  2. 非投影可得：此前无冻结前置提供障碍或装填结论；证明结合 Full、列表索引顺序、
     两个平方整除族与九条 gap，建立新的无界限制，不是已有上界的实例化。
  3. 非定义等价：upper_of_pair 断言一般端点 b≤k；hx1 给出特定第二项的坐标；
     二者都不是 length≤9 的定义展开、别名或重述。
  4. 活推导路径：各分支从 upper_of_pair 取得末项上界；中间分支用它推出 hx1，
     再将 Full 强制的12与第二项11交给 no_neighbors。去掉障碍就没有末项上界，
     去掉装填坐标就无法识别强制项的相邻项；无被投影丢弃的分量或死项。
- admission_basis: escape-witness。
- computational_content.kind: none（公开内容是对任意有限列表和任意自然数位置的无界定理；
  常数36与9来自一般同余/装填论证，不是把一段有限搜索外推到无穷）。
  private nine_term_witness 只作题目要求的尖锐性对照，不是公开实例或独立 deposit 理由。
- question_answered：本报告开头预登记的 OEIS A373409 最大 antirun 长度问题。
- source provenance：本仓推导，引用 wiseman2024antiruns 致谢原问题；
  不主张已穷尽文献或全世界首次证明。

Scribe 仅陈述数学定义、上界、障碍证明和九项对照，不含治理分类词。
Library 根桶实测22，新增笔记落根桶；Arith桶48不新增。Blueprint/Congruence 初始38，
新增源与投影后40，均低于48。已注册域Arith和S3满足普通整数整除/同余内容。

## 最终 Lean 字节与路由

- 最终 `make lean` EXIT=0，27.068秒，日志 attempt-1/make-lean-final.log；
  proof 与私有对照均标准三公理，无 sorry/私 axiom/native_decide。
- CLI `route .lake/a373409-manifest.yaml` EXIT=0，返回
  `D5/S3/Arith/Congruence/NonsquarefreeAntirun.lean`，S3/G，与落点一致。
  首次以 `/tmp` 绝对路径调用被明确拒绝（manifest must be repository-relative），
  改用工作树内 ignored `.lake` 相对路径成功，无工具改动。
- 开PR前重复本仓检索：在 `origin/dev=e6d8bd13c0b517aa7105c30caba9583dc812a876`
  用 `git grep -n -P 'A373409|antirun_length|NonsquarefreeAntirun' origin/dev -- D5`，零命中。
- 并发期间共享 origin/dev 引用已前移；本任务 diff 以 immutable 初始base计，
  当前仅4个新增路径，没有删除他人成果。先前两点式 `git diff origin/dev` 展示的
  上游新增文件“删除”不是本 lane 的变更，不据此作删除判断。

## Lean report 收据

`make lean-report` EXIT=0，66.435秒；delta计划 `changed=0 added=1 removed=1 recheck=1`
（相对播种报告的缓存差量，不是git删除）。report SHA-256：
`6f64ece6355090401a7da368824b85fa665eae0aa09fe7e880aeb02a1315133d`。
目标模块 source SHA-256：`c8d6032c061a71c4233d33ead247cd392d951a22170a19f5fe99c3e895b9ca9b`。
主定理 statement_id：`sha256:d30f60ee3206ee9c5c098349b4ffa714e0f514b49e608886d0b62b02e6bf1c10`。
Full 定义 statement_id：`sha256:0e27b4a2b0ab46b15543f9c7c5dc079a90b9519faaac9d86651db28f1cb1faf6`。
所有声明（含生成 helper）公理集合减标准三公理为空。
完整本模块 included 声明收据保存为 runner attempt-1/declaration-receipt.json。

inspector 的 `include_in_statement=true` 也包括私有声明，不把它误报成公开 API。
补记这些声明的角色（直接冻结依赖均为[]）：

| 私有声明 | proof_shape | 角色 / admission_basis |
|---|---|---|
| no_neighbors | content | upper_of_pair 的列表顺序前置；随主定理 escape-witness |
| upper_of_pair | content | 主定理的具名障碍见证；escape-witness |
| not_squarefree_of_four_dvd | bind-only | Nat.squarefree_iff_prime_squarefree 的薄应用；主定理前置 |
| not_squarefree_of_nine_dvd | bind-only | 同上，素数3；主定理前置 |
| nine_term_witness | content（有限核验） | 仅按任务明示许可保留的private尖锐性对照，无独立准入依据 |

Full 的结构定义和生成构造器是陈述接口，不是额外公开定理。
主定理的消费者→前置方向：主定理→upper_of_pair→no_neighbors；
主定理→4/9整除引理。私有九项见证不在全称上界的推导路径上，明确不拿它充当逃逸见证。

## 发射与定义回声

- `make emit` EXIT=0，53.724秒，仅新增本题一个 Blueprint 投影。
  已亲读投影：Full 三条件、标准三公理、上界证明和九项对照与 Lean 一致。
- `/tmp/a373409-full-echo.lean` 热树编译 EXIT=0：直接从 Full.full 推出 8 必须属于
  `[4,16,36,64,100,144,196,256,324,400]`，与成员判定矛盾；没有使用主上界定理。
  同一片段验证空列表满足 Full。片段复制到 runner attempt-1/full-semantic-echo.lean。
  该有限回声只检验定义，未作为冻结模块或题目进展交付。
- `git diff --check` EXIT=0；Blueprint落点文件数40。
- `git merge-tree --write-tree HEAD origin/dev` EXIT=0，合并树
  `09bd40288f86864216b81fc8474595d759a18e99`，无冲突。
- 下一步无 atom 冻结：`make deposit` 的现役签名强制 ATOM_ID 并自动 cover，
  与任务禁止自造 atom 的要求不相容；遵循任务明定的无 atom 路径，
  先调用同一 `deposit-header-check`，再调用 canonical `ledger-align --add`。
  不新建理论卷，不运行 ingest，不制造 coverage。

## 无 atom 冻结收据

- `deposit-header-check --target D5/S3/Arith/Congruence/NonsquarefreeAntirun.lean
  --protected-base b1c34e4ffff0e67321c1ed9ec60b9eea741e239f` EXIT=0，
  `DEPOSIT_HEADER_CHECKED SL-012`。
- `ledger-align --add ... --candidate-lean-report .lake/build/stratalint/raw-lean-report.json`
  EXIT=0，12.099秒，`selectors_considered=3922 changed=0 added=1 unchanged=3921 conflicts=0`。
- Freeze event：`sha256:cbbedd981ae1435385ae7aad90134d1d1a84dcb6173d5e4ca3f238a01f880922`。
- 模块 statement_id：`sha256:d158a0355abecd8b90f95edbb61931fe1599b28c0046dfe771064abbbe146b3a`。
- 真值 DAG 直接冻结依赖 `prerequisite_frozen_node_ids=[]`，与上面的逐定理登记一致。
- 最终形态为 deposit（无 atom），没有 ingest/cover，没有改动理论卷、atom 或消化账；
  仅本题 Lean、Scribe及投影、文献笔记、报告与两个冻结工件，共7个新增文件。

## 最终未主张栏

不主张任意选出的非平方自由子列也有上界9；不主张九项对照是准入依据；
不主张用有限筛查证明全称结论；不主张OEIS已更新，也未向OEIS发送消息；
不主张已穷尽第三方文献或世界首次证明；未打开的hex文件、arXiv之外的广泛文献、
OEIS所链接的论文及Google文档均为 ASSUMED-UNVERIFIED。
不主张有独立评审票或多模型共识，不主张本席重跑了上游2,000,000平方筛；
不主张本地通过等于CI三门通过。PR身份与其机器判词在runner最终工件中记录。
任务止点按用户明确要求为PR开出；本报告不声称PR已合入dev。

## PR与编译后依赖读数

PR：<https://github.com/the-omega-institute/trureturing/pull/6699>，base=dev，未启用自动合并。

为核对第3.2条闭包条件，热树片段读取编译器 `getConstInfo` 的主 theorem，
再以 `ConstantInfo.value? (allowOpaque := true)` 和 `Expr.getUsedConstants` 检查证明项，
EXIT=0。主证明直接引用四个私有常量 `upper_of_pair`、`no_neighbors`、
`not_squarefree_of_four_dvd`、`not_squarefree_of_nine_dvd`，以及公开投影
`FullNonsquarefreeInterval.full`。这不是rg字面匹配推断的依赖。
源码与可复算API片段在runner attempt-1/proof-dependencies.lean。
首次读取默认 `value?` 返回none，因为该API默认排除opaque/theorem；
读取 Lean/Declaration.lean 的API定义后显式允许opaque成功，未改动库内证明。
九项见证不被主证明引用；它还在主 theorem及全部私有前置之后声明，故不存在向它的前向依赖。

## CI 文献定位修正

PR watcher 在 run 34394662325 / head 8d5409db0f8d42a74e92ef0ba4722bba17325b9f
返回 EXIT=2，失败步骤为 `Run complete mathematical content checks`。
本地单独执行同一 `scribe-content-checks.sh`（不是 preflight）返回 EXIT=1，
唯一 RED 为本题 Library note 的 `incomplete-library-locator`。
读取 `DescribeContentGovernance.cs` 后确认：元数据 URL 之外还必须有
`## Verified locator` 或 `## Locator` 正文小节，并绑定同一来源 URL。
已补入亲验的 OEIS internal 字段与 canonical 地址；未改 Lean、Scribe 或冻结内容。
补充后以绝对 report 路径重跑同一脚本 EXIT=0：`red=0`，
`markdown: judged=1 formula(s)=0 red=0`。
脚本的 describe-report 输出仍含大量 OPEN 投影读数（包括本题）；绝对路径没有消除它们，
因此不把路径猜测当作根因，也不把此散文检查冒充 Lean 语义验证。
继续核对下载中的完整 CI 日志；Lean 语义收据仍由前述 make lean-report 与编译器 API 承担。

上一轮结束后 `gh run view 34394662325 --log-failed` 取得失败步骤全文，
其唯一 RED 同样为本题 `incomplete-library-locator`，与本地复现一致；
该轮工程门 SUCCESS、Lean report 门 FAILURE、admission SKIPPED。
原始大日志的两次流式下载已停止；完整失败步骤保存为 attempt-1/ci-failed-step.log。
进一步读取 `StatementProjection.LoadStatements`：OPEN projection 的查找来源是
`Golden/Projection` 下两份固定的公式投影夹具，不是 canonical raw Lean report；
本题用 `StatementSource.WithoutFormula()`，因此此 OPEN 不表示声明缺失。
`DescribeReport.Build` 另从 raw report 创建 DeclarationCatalog 并解析声明；
这一检查与发射的 `✓ std3`、主定理 statement_id 收据均已通过。
后续 CI 最终判词由 runner result.json 绑定最终 head 记录，不冒领本轮失败为绿。
