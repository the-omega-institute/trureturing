# A375007 implementation — 2026-09-10

产地：`lean4` skill；Codex implementation worker 单点实施与自查，未派独立评审席。用户提供的两支构造源自分诊席；用户自报亲验的代数与 t<3000 扫描是输入，本报告不冒称由 worker 执行。外层 runner 的评审不在本席已知证据内。

## 预登记与范围

第一档。目标为所有自然数 t>24，纯商余条件
`P t := ∀ k, 1 ≤ k → k ≤ t → (t % k = ((t-k)/k) % k → k=1 ∨ k=t)`
蕴含 `Nat.Prime (t+1)`。P 不含素性，所有减法、商、余数均为 Nat 标准运算。
预登记位置：用户实施 brief 与 `Library/Words/oeis2026triage0910.md` 的 A375007 条目。

拟议 escape_witness：由合数分解 t+1=ab、2≤a≤b 构造严格内部见证。
若 a<b，k=b−1，商余分解 t=a*k+(a−1)；若 a=b=u，k=u−2，分解 t=(u+2)*k+3，阈值给 u≥6。
公开主定理拟判 `proof_shape: content`，`admission_basis: escape-witness`。
预计直接 D5 冻结依赖为空；最终以 Lean 语义报告核对。
`utility: none`：目标是无界量化的一般算术定理，不是有限枚举、检查器、数值归约或认证实例。

停止判据依 brief：成 = make lean EXIT=0、无 sorry/私 axiom、PR 已开；翻 = kernel 反例；blocked = 记录路线与最锐剩余子命题。
交付只开 PR，不声明已合入。冻结走无 atom 的 `ledger-align --add`；不建理论卷、不 ingest、不制造 coverage。

## 先库后证收据（随实测追加）

1. 已完整阅读 `CLAUDE.md`（779 行，分段读，截断处补读）、`agents/CONTEXT.md`、Lean skill。
2. 本仓执行 `rg -n 'A375007|a375007|isolated.*(quotient|remainder)|孤立.*商余' D5 Blueprint Library docs/develop`。
   命中仅 `Library/Words/oeis2026triage0910.md` 的分诊记录；D5/Blueprint 未命中目标证明。
   这是字面粗筛，不声称覆盖所有同义表述。
3. `lean-toolchain` 为 `leanprover/lean4:v4.33.0`，manifest mathlib rev 为 `db584cd6d46c92f209a44c0f1c829460d327499d`。
4. 已读 spec A5.1：七行头的第六行为 `utility: none`，在 anchors 与 digest 之间。
   `Meta/domains.yaml` 已注册 `Arith`，地层 S3。报告根目录当前直属文件 37 个。
5. mathlib 声明和外部文献：待本席实查，不采用分诊记录替代检索。

## 开工时的未主张（下文逐项更新）

- 尚未跑 Lean、尚未证明目标、尚未冻结、尚未开 PR。
- 尚未打开 OEIS/arXiv/第三方检索页；关于那些页面的输入均为 `ASSUMED-UNVERIFIED`。
- 未主张世界文献不存在证明，未主张另一条 Fortunate 型猜想，未主张序号枚举接口的形式化。
- 尚无独立模型评审或 CI 判词。

## 检索结算与热树收据

- 钉版 mathlib 实际 checkout SHA 与 manifest 一致。`rg` 搜 A375007/a375007/isolated remainder/quotient 无命中。
  已读 `Mathlib/Data/Nat/Prime/Defs.lean` 的 `Nat.minFac_prime`、`minFac_dvd`、`minFac_le_div`、`minFac_sq_le_self`、`not_prime_iff_minFac_lt`。
  命中的是分解前置，不是目标定理；将直接应用这些接口。
- 当场 GET `https://oeis.org/A375007/internal` 和 `https://oeis.org/search?q=id:A375007&fmt=text` 均 HTTP 200。
  全文 text 2417 bytes，SHA256 `3d8d2d858c9f49465c64987abf1c110a288e1c8e66d1e3c77ec02867db20b0a0`；读到版本 #9，2024-08-18。
  原句：`Conjecture: a(n) + 1 is prime for n > 6. Verified for all terms < 10^8.`
  全文未附此猜想证明；前六项确为 1,2,3,4,8,24。
- GitHub 未认证 code search 返回 401；改用已有 gh 认证后 `search/code?q=A375007 language:Lean` 成功，`total_count=0`。
  `search/repositories?q=A375007` 为 0。不限语言检索有 Maxima-enthusiast/OEISSnippets 的 `A375/A375007.wxm`，本席随后打开核对；大量其余命中只是十六进制子串，未作为相关证据。
- arXiv API `search_query=all:A375007` HTTP 200，totalResults=0。
- Bing `"A375007" proof` 返回 YouTube 无关结果；Google `"A375007" Lean proof` 返回重定向壳；DuckDuckGo 返回 HTTP 202 验证页。这三项不算有效阴性检索。
- OEIS 四个 xref 的文本均已下载，仅粗筛名称与 A375007/Conjecture 相关行；未全文细读。其外链页面一律 `ASSUMED-UNVERIFIED`。
- **判据结算**：在已读 OEIS 完整主条目、钉版 mathlib、GitHub Lean 精确检索、arXiv 精确检索范围内未找到公开完整证明（`not-found-in-searched-scope`）。维持第一档，绝不升级成世界性无证明声明。
- `make lean-cache-ensure` EXIT=0：`status=seeded, method=clonefile, donor=/Users/chronoai/trureturing, clonefile_attempts=1, stamp_miss=null, mathlib_olean_state=warm, project_olean_state=warm, archive_status=not_attempted`。
  完整 HTTP 响应与收据保留在 runner attempt 目录；报告为随提交保存的可移植检索结论。
- 落点选 `D5/S3/Arith/IsolatedQuotientRemainder.lean`；创建前 Arith 直属文件 30 个、Blueprint 对应 scribe 25 个，均低于 48。七行头遵循同域已冻实例。

## Lean 文件检查 1

- 实际打开 GitHub 的 `Maxima-enthusiast/OEISSnippets/A375/A375007.wxm`：仅 OEIS 同款 Maxima 枚举程序，无无限证明。
- 热树增量命令 `lake env lean D5/S3/Arith/IsolatedQuotientRemainder.lean` EXIT=0。
  首次检查暴露两处：`nlinarith` 不自动处理 `t-k` 的截断，以及最后一层 `r%k` 需继续化简。
  修复为在 `t=q*k+r` 内先展开 q=(q−1)+1 与乘法，再由 `omega` 推导截断减法等式；最后用 `simp only` 归约标准余数引理。
- 两个私有构造及主定理均已核验；尚未执行 make lean/lean-report，不能以文件检查代替完整门。
- route 调用曾因绝对路径、缺键、null/空 artifact 被拒；阅读 RouteTests 的字符串型 manifest 后修正为 artifact=lean。所有失败为调用数据错误，未修改工具。

## 完整构建与语义回声

- `make lean` EXIT=0，21.123 秒，12808 jobs；本次新增模块 Built 1.0s。macOS ARM 本地 donor 热树；不外推 CI 耗时。
- runner `KernelEcho.lean` 中三个 **private** 检查分别证明 `P 3 ∧ ¬Prime 4`、`P 8 ∧ ¬Prime 9`、`P 24 ∧ ¬Prime 25`，以及 P 与 brief 公式的 `Iff.rfl` 回声。
  EXIT=0；不将这些有限正例写入 D5 或独立冻结。初次 `norm_num` 未载入 Prime 扩展，改用 kernel `decide`；没有 native_decide。
- `#print axioms a375007_prime`：`[propext, Classical.choice, Quot.sound]`。
- canonical route EXIT=0，输出 GID、路径、S3 与 I 七行 skeleton 均匹配落点。
- `Library/Arith` 创建前实数 48，不能再放；笔记改用已注册 Factorization 域的首个真实工件 `Library/Factorization/ratajczak2024a375007.md`。尚未提交过超容量位置。
- generality=I 表示本条固定商余谓词及阈值的算术结果，不声称跨所有二次域；与无界量化及 utility=none 相容。

## Canonical Lean report

`make lean-report` EXIT=0，65.290 秒；delta `changed=0 added=5 removed=1 recheck=5`，为 donor 报告与本树的真实差量，不把全部 5 个说成本席新增。
报告 SHA256 `127a7450cd5b35f6f093f1bb6dc0f7678a924bf36987f650c0f18c9c5add6845`。
模块源码 SHA256 `2dae556b0fb3028ad667cc519229021e945e9d4d031abb099ceaabe6b1b5c2a6`。
公开声明只有 P 与 a375007_prime；报告也把三个私有 helper 计入模块 statement 集，不将 private 错说成报告完全排除。

| 声明 | statement_id | 公理 |
| --- | --- | --- |
| P | sha256:82d69984517207c0827ba27d7baef08df198e447d4e8b39a005afb85741d3d79 | [] |
| a375007_prime | sha256:69d007e7c4e173245ac561d2e93a19708ff0ae41d32285958fff241e4f8302f5 | Classical.choice, Quot.sound, propext |
| private unequal_factor_witness | sha256:450d58336ec1394e393c3594ca32f379b674c3bac4078a05b2ccf05dca08754a | Classical.choice, Quot.sound, propext |
| private square_factor_witness | sha256:f35f1e7d82468655a90d62be9a6b516763121f688365e150286bd61dcd471a94 | Classical.choice, Quot.sound, propext |
| private remainder_of_decomposition | sha256:2aa6f33b8bc1b8a8c700ae4e97dc08e1ff714a98f868229a1b30e87982bcaa45 | Quot.sound, propext |

`make deposit` 的现役入口强制 ATOM_ID 并在冻结后 cover；本题无 atom，按用户明示改走它内部同一 canonical `deposit-header-check` 与 `ledger-align --add`，不传假 atom。protected base 钉为 `b1c34e4ffff0e67321c1ed9ec60b9eea741e239f`。

## 判形与准入逐声明审计

唯一公开定理为 `D5/S3/Arith/IsolatedQuotientRemainder.a375007_prime`。
`proof_shape: content`; `direct_frozen_dependencies: []`（故无前置 GID/statement_id 对）；
`escape_witness: [unequal_factor_witness, square_factor_witness]`；
`admission_basis: escape-witness`。P 是定义，不冒称额外公开定理。

四项逐一回答：

1. **依赖闭包内**：runner `DependencyAudit.lean` 用 Lean 环境查询主定理，遍历
   `ConstantInfo.type.getUsedConstants` 与 `value? (allowOpaque := true)` 的常量闭包。
   EXIT=0；命中两个 witness、`remainder_of_decomposition` 及其 tactic 辅助项。
   全部 D5 依赖均来自本模块，没有任何别的 D5 冻结前置。
   初次遗漏 allowOpaque 参数仅看见类型依赖；已按 Lean API 修正，该初次读数不用于闭包结论。
2. **非投影可得**：Mathlib 因子接口只给 a、b 的积和次序，未给商余等式的严格内部解。
   新构造为 k=b−1 与 k=u−2，加上各自余数界、k<t 与减法商界；单纯实例化因子分解结论不给这些存在命题。
3. **非定义等价**：两个 helper 的结论是合数分解下内部 k 的存在性，不是 `Nat.Prime(t+1)`，不含 P，也不是主定理的别名。
4. **活推导路径**：`lt_or_eq_of_le hab` 两分支各返回一个 helper 的存在见证，随后拆出 k、严格上下界和等式，代入 h k 并由两种端点结论推出矛盾。
   所有分量均被使用；不存在把无关新命题放入合取再投影掉的项。删去任一支见证，该支就缺少传入 h 的内部解。
   这是对证明的人工语义审计，常量闭包工具本身不声称能机器决定全部四项。

模块内私有引理也逐项说明：`remainder_of_decomposition` 是标准商余改写的辅助组合（bind-only，escape_witness=null）；
两个 factor_witness 为 content，具名构造即各自 k 及三项边界/等式；全部只是主定理的前置，不独立 deposit。
方向：a375007_prime → unequal_factor_witness / square_factor_witness → remainder_of_decomposition。
所有五条 included 声明均为定义或无界符号定理，`computational_content.kind: none`；basis/consumer/instance/premises/result/claim 为 not-applicable(kind=none)。

`question_answered`：预登记 brief 中 t>24 的孤立商余条件是否强制 t+1 素性；答案是。
`dominating_theorem_search`：本仓 D5 → 钉版 Mathlib → GitHub Lean / arXiv / OEIS；`not-found-in-searched-scope`，失败页面如上不计阴性。

Scribe 初次 `make emit` EXIT=2（9.871 秒）：数字 DSL 按单个十进制数字接参，`D(24)` 非法；已修为 `D(2,4)`。
没有改 Lean、工具或任何判官来修这条内容错误。

第二次 `make emit` EXIT=2（33.140 秒）：本库 Library note loader 要求非空 strata_touched 为块列表，不接受这里的 YAML flow 列表；已按现存笔记改为块列表。对应 dangling-literature-reference 是笔记加载失败的后果。
开 PR 前再查：`git fetch origin dev` 后 `git grep -P` 在 origin/dev 的 D5/Blueprint 搜 A375007/isolated quotient/remainder 仍无命中；`git merge-tree --write-tree HEAD origin/dev` EXIT=0，结果树 `a448e4dc5a6945f871974450c2dde98ec0d2ed7d`。

## 冻结结算

- `make emit` 最终 EXIT=0，55.276 秒；仅本题一个 Blueprint 改动，已读投影公式和说明。
- canonical `deposit-header-check` EXIT=0，8.118 秒，SL-012 通过。
- canonical `ledger-align --add D5/S3/Arith/IsolatedQuotientRemainder.lean --candidate-lean-report .lake/build/stratalint/raw-lean-report.json` EXIT=0，7.240 秒。
  `selectors_considered=3922 changed=0 added=1 unchanged=3921 conflicts=0`。
- 新增冻结事件 `e9c5b8877ca890ecd3868689950127fc81d0c4ff74de5bc4ebb69569afbb953c`；成员状态片为 `Golden/Frozen/state/D5/S3/Arith/IsolatedQuotientRemainder.lean.json`。
- 没有 atom/source_id/coverage；这是无 atom 的 deposit，不是消化。没有新理论卷、ingest、普通有限正例冻结或治理改动。

完整 make lean 的 LEAN_CACHE 收据：

```text
LEAN_CACHE {"status":"present","worktree":"/Users/chronoai/trureturing-a375007","donor":null,"method":"none","reason":null,"stamp_miss":null,"pin_sha256":"sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":0,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## 当前未主张

- 未主张全球文献无证明或本席拥有发现优先权；搜索范围与失败请求如上。
- 未主张证明 OEIS 第二条 Fortunate 型猜想、无限多个序列项、或 Lean 内的单调枚举/第六项桥；已证明的是 brief 精确给出的 t>24 值形式。
- 没有把用户扫描当作本席实测，也没有将有限检查作为无限证明。
- 未访问的 xref 外链、通用搜索引擎未能取得的内容均为 ASSUMED-UNVERIFIED。
- 本席独立评审席为 0，未宣称多模型共识；PR 创建、CI 和合入情况在最终交付记录中另报。

## 实施交付

PR：https://github.com/the-omega-institute/trureturing/pull/6696 ，base=dev，head=lane/math/a375007；由 `make pr-open` 创建，未开启 auto-merge。
本席按 brief 三态判为 **成**：make lean EXIT=0、无 sorry/私 axiom、PR 已开。
这不等于宣称 PR 已 MERGED 或 CI 三门已绿：开出时机器观察为 OPEN，CI 刚启动，最终观察见 runner result.json。
差量共 7 个新增文件，未改工具/判官/理论卷/atom；`git diff --check` EXIT=0。
