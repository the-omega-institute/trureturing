# A380392 implementation — 2026-09-10

产地：`lean4` skill；Codex implementation worker 单点实施、自查，独立评审席为 0。
用户转述分诊席检索与其本人 n=1..4 枚举；这些不是本席实测。外层 runner 的评审另计。

## 预登记

第一档；目标是用户 brief 中所有 n≥1 的二元矩阵全 1 东/南单调路径平均数公式。
pathCount 必须实际计数从 (0,0) 到 (n−1,n−1) 的路径，不得定义为目标右式。
拟议 escape_witness：固定路径访问恰 2n−1 个不同格，满足该路径的矩阵与其余格的任意 Bool 赋值双射。
交换有限求和后，各路径贡献 2^((n−1)^2)，路径数为 C(2n−2,n−1)。
该见证对应用户 brief 的 ASSUMED-UNVERIFIED 结构义务；最终须由 Lean 核验。
拟判主定理 proof_shape=content，admission_basis=escape-witness；预计直接冻结依赖为空，最终以语义报告核对。
utility=none：无界量化的一般组合定理，不以有限计算或认证实例为主要内容。

停止判据：成 = make lean EXIT=0、无 sorry/私 axiom、PR 开出；翻 = kernel 反例；
blocked = 写清路线、卡点与最锐剩余子命题。发现公开完整证明则按 brief 退 note。
n=0 不进入结论；禁止反向、重复或对角步，n=1 须符合单格路径。
无 atom 冻结使用既有 ledger-align --add，不建理论卷、不 ingest、不制造 coverage。

## 开工与检索收据

- 已分段完整阅读 CLAUDE.md（779 行，截断处补读）、agents/CONTEXT.md 和 Lean skill。
- 干净工作树，分支 lane/math/a380392；base=48e95107100e503cdc52aa44cc15165b65fc3213。
- lean-toolchain=leanprover/lean4:v4.33.0；manifest mathlib pin=db584cd6d46c92f209a44c0f1c829460d327499d。
- D5 粗筛：`rg -n -i 'A380392|monotone.*path|lattice.*path|path.*expect|random.*matrix' D5`。
  唯一命中 HeartsDraft 的无关历史注释；没有目标证明命中。此为字面粗筛，不冒称语义穷尽。
- 报告目录创建前直属文件 39 个，低于 48。
- 钉版 mathlib 与第三方/OEIS/arXiv：待本席检索。

## 开工时的未主张

尚未证明、构建、冻结、开 PR。尚未打开的外部页面全部 ASSUMED-UNVERIFIED。
不主张全球不存在公开证明，不主张发现优先权，不以用户枚举替代一般证明。
不主张独立模型共识或 CI 已绿。

## 检索第 2 批

- 本工作树尚无 .lake，首次本地 mathlib 粗筛报路径不存在，未冒称零命中。已先启动 make lean-cache-ensure。
- 改读主检出已有的 mathlib 源，git rev-parse HEAD 与指定 pin 完全相等。
  rg 搜 A380392 / monotone.?path / lattice.?path / bernoulli.*path，只命中 DyckWord 文档与无关范畴路径声明；未命中目标。
- 已实际读取 spec A5.1：utility: none 是合法完整字段，位于 anchors 与 digest 之间。
- Library/Words/oeis2026triage0910.md 第 302 行含用户分诊记录；不将其当本席外网核验。

## 外部检索与缓存结算

- OEIS search text 接口八次 HTTP 403，arXiv API HTTP 429；这些失败不计阴性证据。
  改用 curl 读取 OEIS internal，主条目与全部七个直接 xref 均 HTTP 200。
- A380392 主条目全文已读：revision 16，2025-02-22；John Tyler Rascoe 于 2025-02-21
  明写平均路径数猜想，未附证明。路径仅 South/East，相邻同排或同列，不含对角。
- 已读 A001790/A101926/A002416/A086266/A261242/A369285 的 N/C/F/H 字段；
  中心二项式分子、积分分母与其他矩阵计数均未给出目标期望的证明。
  A000984 仅下载，尚未细读；xref 的外链论文未打开，ASSUMED-UNVERIFIED。
- GitHub authenticated code search `A380392 language:Lean` total_count=0。
  不限语言搜索 total_count=358，首批 30 条只有本仓分诊记录相关，其余为哈希/字符串碰撞；
  不将未翻页的结果算作全部读完。
- arXiv 网页 search query=A380392, searchtype=all，HTTP 200，明确 produced no results。
  Bing HTTP 200 仅取页，尚未核对结果内容，不用于阴性断言。
- 在已读范围未找到完整证明（not-found-in-searched-scope），维持第一档。
- make lean-cache-ensure EXIT=0，21.071 秒；status=seeded, method=clonefile,
  donor=/Users/chronoai/trureturing, clonefile_attempts=1, stamp_miss=null,
  mathlib_olean_state=warm, project_olean_state=warm, archive_status=not_attempted。
- 已读 mathlib 的 Finset.card_powersetCard、card_inter_add_card_sdiff、card_sdiff_of_subset、
  Fintype.card_pi 等前置；将直接使用，不重证其一般陈述。
- 编码约定：对 (k+1)×(k+1) 矩阵，路径以 range(2*k) 的 k 元子集记录东步位置。
  时刻 t 的两个坐标为 range(t) 与该子集交集及差集的基数；坐标和=t，故各访问格互异。
  这是用户已预登记见证的具体实现，不改变数学目标。

## Lean 片段 1：访问格互异

- 新落点 D5/S3/Arith/Paths/MonotoneOnePaths.lean；Arith 父目录递归文件数 114，
  Blueprint 镜像父目录递归文件数 218、直属 54，故新增 Paths 子桶，首次真实工件入桶。
  新桶创建前不存在（0 文件），创建后 Lean 1 文件。
- 热树增量 lake env lean 该文件 EXIT=0；只有 unnecessarySimpa 风格警告。
- Path k 是 range(2*k) 的 k 元子集，pathCell 的两个坐标为前缀交/差集基数；
  Lean 已证坐标界、rank=t、pathCell_injective、pathCells_card=2*k+1。
  首次检查因 sdiff_subset_sdiff_left 的显式参数次序错误失败，读源码签名后修正。
- pathCount 实际过滤路径，要求每个访问格为 true；零维分支仅使定义总化，不在主定理范围内。
- 主均值定理尚未实现，此片段检查不等于完整构建。

## Lean 片段 2：一般均值公式

- 热树 lake env lean D5/S3/Arith/Paths/MonotoneOnePaths.lean EXIT=0。
  主定理 mean_monotone_one_paths 已按 brief 原式闭合；仅一个 unusedSimpArgs 风格警告待清理。
- freeCellsEquiv 将满足路径所需格全真的矩阵限制到补集，逆映射对所需格填 true；
  Lean 核验双侧逆，再由 Fintype.card_congr 求得 2^(总格数−所需格数)。
- fixed_path_count 消去重复格风险，给每条路径贡献 2^(k*k)；total_path_count
  交换有限求和并直接应用 card_powersetCard，最后在 ℚ 中消去非零的 2 的幂。
- 无 sorry、无自加 axiom、无 native_decide。完整 make lean 及公理闭包检查待执行。

## Lean 片段 3：端点与每步方向

- pathCell_endpoints 证明起点 (0,0)、终点 (k,k)；pathCell_step 证明第 t 步
  在编码子集中时恰东移 1，否则恰南移 1，另一坐标不动。两者为 private 语义引理。
- 删除总括 Mathlib.Tactic，改为具体 FieldSimp/NormNum/Ring imports。
  精简暴露 Nat.cast_sum 未导入；查其源码后显式导入 Algebra.BigOperators.Ring.Finset。
- 最终该文件增量检查 EXIT=0，无警告。主定理仍为 brief 原式。

## 完整构建与叙事落点

- make lean EXIT=0，9.806 秒，12820 jobs；新增模块 Built 1.6s。
  macOS ARM donor 热树，非 CI 时长。完整日志在 runner attempt-1/make-lean.log。
- canonical route EXIT=0，返回 D5/S3/Arith/Paths/MonotoneOnePaths.lean、S3、generality I，
  与头部及镜像地址完全一致。I 表示固定二元方阵问题，不声称跨二次域通用性。
- Library/Arith 已有 48 个直属文件；Library/Words 为 24，故 note 放 Words，新增后 25。
  rascoe2025a380392 满足 bibkey 文法，Verified locator 正文逐字含 canonical URL。
- Scribe 使用 StatementSource.FromLean 直接投影主定理，说明路径编码和双重计数。
  未将治理判形词汇放入 Scribe。尚未 emit 与 Scribe 内容门，不冒称其已绿。

## 内核语义回声与依赖审计

- runner attempt-1/KernelAudit.lean 经 lake env lean 检查 EXIT=0。
  两条 private 回声对所有 1×1、2×2 矩阵作 kernel decide：
  n=1 恰为唯一格的真值指示数；n=2 恰为两条合法路径的指示数之和。
  文件仅在 runner attempt 中，不冻结有限实例，不用 native_decide。
- #print axioms mean_monotone_one_paths = [propext, Classical.choice, Quot.sound]。
- 使用 Lean 环境 ConstantInfo.type.getUsedConstants 和 value?(allowOpaque:=true)
  遍历 elaborate 后传递常量闭包，7342 个常量；D5 依赖全部属于本模块。
  命中 fixed_path_count、freeCellsEquiv、pathCells_card、pathCell_injective、pathCell_rank。
  这是 Lean 编译器语义 API 读数，不用文本粗筛冒充依赖结论。
- pathCell_endpoints/step 是独立的 private 语义核对，不在主定理活推导路径中；
  不将它们冒称主定理的 escape_witness。

## 公开定理的判形与准入

唯一公开定理：D5/S3/Arith/Paths/MonotoneOnePaths.mean_monotone_one_paths。
proof_shape: content；direct_frozen_dependencies: []（无前置 GID/statement_id 对）；
escape_witness: fixed_path_count（经 pathCells_card、pathCell_injective 与 freeCellsEquiv）；
admission_basis: escape-witness。

对 CLAUDE.md 3.2 四项逐项核对：

1. 依赖闭包内：以上 Lean 语义遍历明确命中这些具名 helper，主定理依次消费
   total_path_count → fixed_path_count → fixed_cells_count/freeCellsEquiv 与 pathCells_card。
2. 非投影可得：库中的子集/函数基数接口并未提供该编码路径访问格互异或固定路径矩阵数。
   本模块由前缀坐标构造出注入，再构造补格限制/填充的双侧逆，得到新的固定路径计数命题。
   空的 D5 冻结前置集无法单靠实例化/投影提供这些路径事实；非某条已有目标公式的改名。
3. 非定义等价：fixed_path_count 的结论是一个固定路径所支持的矩阵基数，主定理是
   对全部矩阵中全部路径计数的有理平均；两者量化对象与结论不同，不是别名或重述。
4. 活推导路径：求和交换之后，每个内和用 fixed_path_count 的等式替换；该等式的
   指数利用 pathCells_card，而后者以 pathCell_injective 把 image 的基数化为时间域基数。
   freeCellsEquiv 的两侧逆承担 Fintype.card_congr，没有无关合取分量被投影丢弃。
   去掉这些步骤，有限求和只交换索引，不能给出内和的值。此项为证明项的语义自查，
   不声称依赖遍历本身机器决定全部判形。

Path/pathCell/pathCells/pathCount 是实际组合对象定义，不冒称额外公开定理。
全部 included 声明为定义或无界符号定理，computational_content.kind=none；
basis/consumer/instance/premises/result/claim 为 not-applicable(kind=none)。
question_answered：用户预登记的 A380392 全正尺寸平均公式是否成立。
dominating_theorem_search：D5 → 钉版 mathlib → GitHub Lean/OEIS/arXiv，
not-found-in-searched-scope；失败请求和未读外链已逐项标明。

## Canonical Lean report 与开 PR 前复查

- make lean-report EXIT=0，75.760 秒；delta changed=0, added=12, removed=0, recheck=12。
  该差量是 donor 报告到本树的差量，不把 12 个模块说成本席新增。
- 报告 SHA256：4f4346c1828173949292575478fa6b5a1e35056e578cacd5a51242511271165c。
- git fetch origin dev 后，git grep -P 在 origin/dev 的 D5/Blueprint 再搜 A380392、
  mean_monotone_one_paths、monotone/lattice path；仅有无关格论叙事，无目标命中。
  当次 git merge-tree --write-tree HEAD origin/dev EXIT=0，输出树
  7451d6227043a1a28695ebd8e4cbe02901091c0e；不需要为无冲突追平移动 dev。

Included 声明的 statement_id（私有 helper 也被 inspector 纳入模块身份）：

| 声明 | statement_id |
| --- | --- |
| mean_monotone_one_paths | sha256:6971a52ccdcb12ccb9739f22a44daf9f5694dff90611cd8a94f82d6b94551215 |
| Path | sha256:0016ea644f5f00a744b084338741be497183bda99cd0829bc1dc964f235a72d5 |
| pathCell | sha256:b1e483351ff535a70201b562dc27b2a10143a5b5b6afcc825dc8742a722dc78e |
| pathCells | sha256:b1f90765ee48ae382e206398f61feb8d06dfa50f7fa2d221b288a1d15b2aef95 |
| pathCount | sha256:3a4b2333aa416be0b1bc7f9046df562dbd5960e7ef6dcce4dacda17a031e12da |
| path_subset | sha256:3b3c3ecc0f7ccb57781bace2d97a431600babcaafc2c3792e352b6802035ca89 |
| pathCell_rank | sha256:05235139481248257e60391fb00b7c5101b4200528fa6d3eb65ed9db2ebe797e |
| pathCell_step | sha256:2dce3c058e4b73fa8dca027f4f6438d7e2d0bcfdf2c83551d3d566be743e6c1d |
| freeCellsEquiv | sha256:7d11a7208c9754196af0c8c1bdde3860a97071215329a5cce320b11bf8820b7d |
| pathCells_card | sha256:973cdf9ea96d2715f6bf44e9eb3bae40730fd7150b9f25aeb6eb03600cf9d28b |
| fixed_path_count | sha256:7938912310e796fd5fc4ca507c188327e2b5f935768d212aa469f16c59dd4a63 |
| total_path_count | sha256:f020a13dd763d54f3a7490b1321241a7478fea0f4923da4fa6e02fd3fa3d46f0 |
| fixed_cells_count | sha256:b392e0cfaabb602da514d90a0e76f70aad6a9d7ea322aff3cdc3a0f5d5dd9bab |
| pathCell_endpoints | sha256:72e706bdab8580ee666d1a1509e59fc1f410dd08e28a64d36d5a6f5bc347a812 |
| pathCell_injective | sha256:3229fdf639fdb9b78b88bbadba082821944bb80c0adcec3f6e2a694d224adfd1 |
| path_card | sha256:5b456218dc910065c9ac09d096bcdae25d37859c2f069721d3fdb7fd941c021c |
| match_1 | sha256:9760f3fe8d1d8e8d5c303b46708bad01838ae6b335d13a45c3096a5bf4eae606 |
| splitter | sha256:e3f96d9a4d1ea68ca11cf45492dc05514b66724f42dc6ff3e1571730e996ce06 |

本模块 included 声明公理均为标准三公理；完整模块报告在 attempt-1/module-report.json。

make lean 的完整 LEAN_CACHE 收据：

```text
LEAN_CACHE {"status":"present","worktree":"/Users/chronoai/trureturing-a380392","donor":null,"method":"none","reason":null,"stamp_miss":null,"pin_sha256":"sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":0,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## 发射首次失败与修复

make emit 首次 EXIT=2，8.073 秒：StatementSource.FromLean 对该新声明返回
missing:D5/S3/Arith/Paths/MonotoneOnePaths.mean_monotone_one_paths。
阅读 StatementSource.Materialize 后，按其 Unprojectable 分支改用合法 FromAuthor，
手写与 Lean 同义的正尺寸公式；没有改 Lean 定理、投影器或判官。先前自动投影的计划由此修正。

第二次 make emit EXIT=2，5.628 秒：新增 authored 公式少一个右括号（CS1026）。已修正该语法错误。两次发射失败原因不同；未改变数学、工具或门。

第三次 make emit EXIT=2，29.187 秒：DSL 的 Le 紧接 n 会发射成非法 LaTeX 宏。检查整条公式的控制词边界，同时补齐 Le 与 Cdot 后的 Sp；这是同一 authored 公式的发射调试，尚未发生 deposit 或整 lane 重做。

make emit 最终 EXIT=0，67.168 秒；仅本题 1 个 Blueprint 被修改。已逐字读投影公式，与 Lean 主定理及 n≥1 限制一致。Generated/ 与 tools/Generated 的运行期投影不加入 Git。

## Scribe 内容门与冻结预检

- projections --check --report .lake/build/stratalint/raw-lean-report.json EXIT=0，11.914 秒。
  本次差量不唤醒脚本内部的 projection 分支，故显式执行该子项，不冒称已自动执行。
- bash tools/scripts/workflow/scribe-content-checks.sh .lake/build/stratalint/raw-lean-report.json
  "" 48e95107100e503cdc52aa44cc15165b65fc3213 EXIT=0，23.549 秒。
  Describe 与 Library locator 检查通过；真实 KaTeX 为 markdown: judged=1 formula(s)=1 red=0。
  既有笔记 online-doi-title-check 是非阻断 Observe，不当成联网 DOI 核验。
- canonical deposit-header-check --target D5/S3/Arith/Paths/MonotoneOnePaths.lean
  --protected-base 48e95107100e503cdc52aa44cc15165b65fc3213 EXIT=0，7.291 秒，SL-012 通过。
- make deposit 入口 require_transaction_arguments 强制 ATOM_ID 且随后 cover；本题无 atom。
  按用户明示及仓内先例，使用该入口同一 canonical deposit-header-check 与
  ledger-align --add，不制造假 atom、不绕过头部/当前 Lean report 预检。

## 无 atom 冻结收据

- canonical ledger-align --add D5/S3/Arith/Paths/MonotoneOnePaths.lean
  --candidate-lean-report .lake/build/stratalint/raw-lean-report.json EXIT=0，7.075 秒。
  输出 selectors_considered=3934 changed=0 added=1 unchanged=3933 conflicts=0。
- Freeze 事件：sha256:0f03576a6020bc4e4650c45e8d23839b2ad21d1b67c16cb343b3030784ddba07。
- 模块 statement_id：sha256:420ee5ad356e65d21336474f48adb6a383a939430411498c417864bcf40e3b9a。
- accepted 事件含本模块全部 18 条 included 声明，前置冻结节点为空；
  state 为 Golden/Frozen/state/D5/S3/Arith/Paths/MonotoneOnePaths.lean.json。
  以上身份直接读取 canonical producer 输出，不手写账本、不重算历史身份。

## 交付时的未主张

已证用户要求的全正尺寸均值定理，并消除“恰经过 2n−1 个不同格”的
ASSUMED-UNVERIFIED：访问格注入及基数已由 Lean 内核验证。
不主张 n=0 的期望约定、完整分布 T(n,k)、反向/重复/对角路径、全球文献无证明或首创性。
用户的 n=1..4 枚举读数仍归用户；本席只另做私有 n=1、n=2 全矩阵语义回声。
外链未读部分及受限检索仍按前述 ASSUMED-UNVERIFIED，不由本地形式化补作阅读证明。
独立评审席为 0，未声称多模型共识；本地检查不替代 PR 的远端 CI 判词。

## PR 交付

- PR：https://github.com/the-omega-institute/trureturing/pull/6711，base=dev。
- 使用 make pr-open HEAD=lane/math/a380392 MESSAGE=<attempt-1/pr-message.md>，
  WATCH_TIMEOUT_SECONDS=600；pr-create EXIT=0。创建时冻结提交为 6dd08e8e7a。
- 分支已持续 commit/push；此节记录 PR 创建事实后也提交推送。
- 按用户本次实施阶段定义，结果为“成”：一般定理 make lean EXIT=0、
  无 sorry/私 axiom、PR 已开出。未合并；远端 required CI 创建后尚未齐备，
  最终观察快照另存 runner result.json，不将开 PR 等同于 CI 全绿。
