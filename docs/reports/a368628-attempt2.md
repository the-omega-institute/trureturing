# A368628 attempt 2

产地：lean4 skill；Codex 主线程实施，用户给出分步路线；零独立评审席，单点核验。基线 `f838f20236e5a723d0c025ef53a80a07483008fa`，分支 `lane/math/a368628`。

## 预登记

问题：原分段平方/四次卷积定义的自然数序列是否满足 `Odd (seq n) ↔ ∃ k, 3*n+1=4^k`。本轮不新建理论卷，不 ingest，不造 atom；无 atom 冻结使用 `ledger-align --add`。

拟议 escape_witness：由原卷积推导的模二递推（三个剩余类），随后强归纳产生指数存在性。该递推不是定义的一部分。一般无界定理，`utility: none`；非有限枚举、检查器、数值归约或已认证有限实例。

停止：成须 Lean 全构建成功、无 sorry/私 axiom、开 PR；翻须 kernel 反例；blocked 须具体 Lean goal/error 与各路线读数。有限核对不计证明进展。

## 检索收据

- D5：`rg '368628|a368628' D5 Library Blueprint docs/develop`：仅既有 OEIS 分诊，未命中本题定理。
- 完整读取 `ConvolutionRecurrenceOddPowersOfTwo.lean`：公开一般 `convolution_pairing` 命中，计划 import 并实际应用。
- 完整读取 `CatalanDoubleCompositionPowersOfFour.lean`：private `quartic_support` 属不同方程；仅借强归纳证明形状，不引用其结论。
- 官方 OEIS `https://oeis.org/A368628/internal`，本轮 HTTP 200，原文仍标 Conjecture；公式 (1) 与用户的分段卷积一致。Israel 的多项式/68阶递推不声称奇偶证明。档位1；仅在已查资料范围未见证明。
- GitHub 未认证代码搜索 `A368628 language:Lean` HTTP 401，不能声称全生态搜索完成。未打开的第三方页均为 ASSUMED-UNVERIFIED。

## 构建与容量

首次 `make lean-cache-ensure` EXIT=0：status=seeded，method=clonefile，donor=/Users/chronoai/trureturing，clonefile_attempts=1，mathlib/project 均 warm，missing olean=0。未跑冷树裸 lake。

容量：`find D5/S1/Recurrence -maxdepth 1 -type f | wc -l` 为23；Invariants 递归计数25。域 Recurrence 注册 S1；选择直接目录，generality I。

## Lean 尝试

正在建立原卷积定义与第一个一般模二系数引理；尚未声明证明成功。

## 未主张

未主张全世界无已有证明、未主张不同 Hanna 序列相同、未主张数值探针等于证明、未主张独立评审或 CI 已通过。

### 编译尝试 1

热树 `lake env lean /tmp/a368628-probe.lean`：原卷积 well-founded 定义、`seq_zero`、`seq_recurrence`、一般 `pow_coeff_congr` 均成功 elaborate。退出1仅因探索用 `#check` 三个不存在的 interval 引理；具体 `Unknown identifier sum_Icc_succ_bot / sum_Icc_eq_sum_range / Finset.sum_Ico_zero_bot`。这些查询已从正式文件移除。序列不包含模二支撑规律。

钉版 Mathlib 检索命中 `PowerSeries.coeff_mul`、`coeff_expand_mul`、`coeff_expand_of_not_dvd`、`MvPowerSeries.map_frobenius_expand`；直接复用。arXiv API `all:A368628` HTTP 200，totalResults=0。

### 编译尝试 2

正式定义文件单文件编译 EXIT=0，提交 `55fbae1c3c` 已推送。配对探针实际应用 `convolution_pairing`，通过 `g=X*expand₂(f)` 把奇次平方系数变为 g 的偶次平方系数。第一次 EXIT=1，goal 为 `∑ x ∈ range (2*m), coeff x f * coeff (2*m-x) f + … = coeff m f ^ 2`，`sum_range_eq_add_Ico` 缺显式求和函数参数。修复传入该函数；不是数学障碍。完整 goal 在 attempt 工件的 Lean 日志中保存。

配对探针修复后 EXIT=0：`square_even_coeff` 实际应用既有 `convolution_pairing`；`square_odd_coeff` 经 `X*expand₂(f)` 降到 midpoint=0，不重证 involution。首次序列 cast 桥 EXIT=1：`simp only` 未把 `map(series^p)` 与 `(map series)^p` 对齐，具体两侧为 `Nat.castRingHom … (coeff … (series^p))` / `coeff … ((PowerSeries.map … series)^p)`；改为反向 `map_pow` 再 `coeff_map`。

**第一步完成**：`seq_even_index_zero (j : ℕ) : (seq (2*j+2) : ZMod 2)=0`，正式文件热树增量编译 EXIT=0；`#print axioms` 仅 `propext, Classical.choice, Quot.sound`。原卷积到自然数 cast 桥已闭合。全项目门与冻结待最终模块齐备后依序执行。

**第二步完成**：四次 Frobenius 探针 EXIT=0；正式 `seq_four_mul_add_three (j)` 编译 EXIT=0，标准三公理闭包。`square_expand` 直接用 Mathlib `map_frobenius_expand` 和 `ZMod.frobenius_zmod`；两次 expand 合成四次，再用 `coeff_expand_of_not_dvd`。认证 GitHub 代码搜索 `gh api search/code?q=A368628+language:Lean` 成功，total_count=0；替代此前401失败，检索边界仍限字面 A 号。

**第三步完成**：`seq_four_mul_add_one (j) : (seq (4*j+1) : ZMod 2) = (seq j : ZMod 2)`，正式文件增量编译 EXIT=0，标准三公理闭包。与第二步共用一般 `fourth_expand`，此步精确应用 `coeff_expand_mul`。三个无界模二递推均已闭合，下一步为指数双向强归纳。

### 强归纳尝试

首次编译只有零基例报错：`simp only` 已把 `1=1` 归约为 `True`，`iff_of_true rfl` 需要 `True` 而收到等式证明。改 `rfl` 为 `trivial`；非零所有分支（正偶、4j+3排除、4j+1指数前推/回推）均无编译错误。

本轮完整读取四个直接 xref 的 N/C/H/F/Y 字段（A368593/A368626/A368627/A368629，均 HTTP200），所查页无 A368628 奇偶证明。Israel 68阶递推文件 HTTP200，已下载；长多项式系数未逐项验证，ASSUMED-UNVERIFIED，不作为证明依赖。原目标 OEIS 页、arXiv 检索与源码检索收据仅支持所查范围未见证明。

无 atom 入口核实：`make deposit` 的 `require_transaction_arguments` 强制已有 ATOM_ID，不能用于本题；依用户明确指示使用它内部同一 writer `ledger-align --add`，另行运行相同 `deposit-header-check`。不会造 atom 满足接口。

**目标定理已通过单文件 Lean**：`a368628_odd_iff (n : ℕ) : Odd (seq n) ↔ ∃ k : ℕ, 3*n+1=4^k`。修复后 EXIT=0，六条公开定理的 `#print axioms` 均仅标准三项。尚未宣告最终“成”：全项目门、Scribe、冻结、PR 在后续完成。

### 语义回声与依赖读数

追加 private 的前四项回声，直接从自然数卷积递推计算，不使用奇偶定理。首次编译仅该 private echo 有两处 simp 未归约：`coeff 0 (mk seq ^ 4)`、`if Even 3 then … else …`；修复为显式 constantCoeff/map_pow 和奇偶分支。主定理仍闭合。编译期 `getUsedConstants` 已确认七条预登记直接依赖，包括 `square_even_coeff → ConvolutionRecurrenceOddPowersOfTwo.convolution_pairing`，复用不是闲置 import。

Private `initial_echo` 修复后正式模块编译 EXIT=0、零 warning/error，前四项 1,1,2,14 经 kernel 验证，未作为公开有限实例冻结。另独立 Python 原卷积探针 n=0..300：前十项与 brief 全等，奇指标 [0,1,5,21,85] 与谓词预测逐项相同，耗时0.599秒；只作语义回声，不计证明进展。

## 逐声明判形与准入依据

本节判形按 base 到 candidate 首次冻结的完整证明，私有 helper 展开；只列直接冻结前置，Mathlib 不计入该栏。唯一冻结数学前置记为 P：`D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.convolution_pairing`，`statement_id=sha256:cbd33875d118bc97517ffb5a2744a145bf46d7e61edab71f567ae26059725edb`，读取既有 accepted 事件 `7d9d1b753ea1e0d2b907b2e3784379a289c59ebe0601a95489ce227a5978b1a5`；模块 pin 为 `sha256:01c1cad519e2e056064c9dbb822bbb04688d12c1ea8bc8584da0bc48c4eabee7`。本模块内新前置并非 base 已冻结前置。

| 公开定理 | proof_shape | 直接冻结依赖 | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| seq_zero | bind-only | [] | null | escape-witness 模块内伴随；义务为基例，消费者 a368628_odd_iff → seq_zero |
| seq_recurrence | content | [] | private pow_coeff_congr | escape-witness |
| seq_even_index_zero | content | [P]，经 private 平方系数桥 | private pow_coeff_congr，经 binary_recurrence / seq_recurrence | escape-witness |
| seq_four_mul_add_three | content | [] | private pow_coeff_congr，经 binary_recurrence / seq_recurrence | escape-witness |
| seq_four_mul_add_one | content | [] | private pow_coeff_congr，经 binary_recurrence / seq_recurrence | escape-witness |
| a368628_odd_iff | content | [P]，经正偶指标消失 | 三条新序列系数递推，并以强归纳构造指数 | escape-witness |

`pow_coeff_congr` 的内容是任意半环、任意幂次的有限系数一致性传播，以幂次归纳及卷积的两个坐标界证明；该引理不引用仓内冻结定理。对 seq_recurrence 和三条 residue 定理逐条适用第3.2四项：(i) 它分别在本定理已 elaborate 的闭包内，seq_recurrence 直接使用，三条 residue 经 binary_recurrence 使用；(ii) 空/仅 P 的冻结前置未提供任意半环的截断一致性归纳，需新归纳步骤，非投影与参数绑定；(iii) 该一般二序列一致性命题与具体 seq 的递推或余类结论不定义等价；(iv) 用它消去有限递归的零延拓，结果实际喂给模二系数计算，没有丢弃的合取项或死代码。若只相对已证明的本模块 seq_recurrence 看，三个 residue 的剩余 Frobenius/配对计算是直接库复用；本表按要求内联回 base，故如实披露 content 的来源，而不冒领 Frobenius 为新定理。

主定理四项：(i) 三条 seq 余类引理在 getUsedConstants 的直接常量集合中；(ii) P 只给任意函数的平方配对，不能直接投影出这条新分段递归序列的余类规律与指数存在性；(iii) 每条余类递推与全称双向指数判据均不定义等价；(iv) 强归纳分别使用两条零值排除分支与 4j+1 递归分支，删去任一即对应分支无法由当前项闭合。强归纳自身还构造 k+1 并反向剥离正指数，不是冻结 iff 的换名。

两条公开 def（seq、series）是原递推构造及其系数封装，不单独作定理准入主张。全部六条公开定理回答无界符号问题，非四类计算性内容，`utility: none`；private initial_echo 不作独立正向实例冻结。伴随边另有主定理 → 三条 residue → seq_recurrence，终点为本次用户预登记目标。

## 全项目门读数

`make lean`：首次 C# 括号错误 EXIT=2 / 2.411s；第二次 FormulaDsl.D 参数要求 byte，Residue helper 用 int，EXIT=2 / 10.984s。两处均修在新增 Scribe 文件。第三次 **EXIT=0 / 59.182s / 12828 jobs**，日志含 LEAN_CACHE 收据，未更改检测或预算；旧模块的重放 warning 不归本次新模块。新模块单文件编译零 warning/error。后续 lean-report/emit/冻结/Scribe 检查按序进行。

首次 `make lean-report` EXIT=0 / 64.004s；delta recheck=1，report SHA256 `ec96a45d3db40a91bf01d610333751d79bce3d3d512d8fe427e6346e152fc648`。全构建比单文件调用额外启用了风格 linter，新模块有两处 `0<n` 空格 warning（先前“零 warning”只描述单文件读数）；已修为 `0 < n`，按源码变化重新运行 lean/lean-report，不关闭 linter。

最终格式的 `make lean` 再验 **EXIT=0 / 18.629s / 12828 jobs**；新模块无风格 warning。`git diff --check` EXIT=0。此前成功数学构建仍有效，本次重验只因源码空格改变需报告绑定最终字节。

最终源码 `make lean-report` **EXIT=0 / 60.118s**，delta changed=1 / recheck=1。六条公开定理及全部 private 声明的报告公理集合均在标准许可集内；无 sorryAx。声明身份随该空格修改不变。

首次 `make emit` EXIT=2 / 16.341s：Library 的非空 `strata_touched: [S1]` 不被本仓 note parser 接受（`strata_touched must be a list`），连带 literature reference 无法解析。改成既有 block-list 文法 `strata_touched:\n  - S1`，Verified locator 中原样 url/doi 已在；未改 Lean 源码。

第二次 emit EXIT=2 / 15.421s：list 成员须为 GID，`S1` 不是 GID。已读 `LibraryNoteCatalog.cs:218-228` 的实际 parser（`GidRef.Create(gid)`），将成员改为本模块完整 GID。前次把字段名当语义、只修 YAML 形状不够，此次按真源类型修正。

`make emit` **EXIT=0 / 50.659s**，仅发射本模块一个 Blueprint（生成器 run-local manifest 未入索引）。`deposit-header-check --target … --protected-base f838f20236e5a723d0c025ef53a80a07483008fa` **EXIT=0 / 9.658s**。当前进入同一冻结 writer，选择既有直接前置 P 并 add 本模块，避免无关全库对齐；无 atom、无 cover。

冻结成功：`ledger-align --selector <P module> --add <this module>` **EXIT=0 / 8.838s**，`selectors_considered=2 changed=0 added=1 unchanged=1 conflicts=0`。唯一新 Freeze 事件 `sha256:5ae7df099edd2b964f49c2545998be6c3c37328dfe633e7c1dc76fc5aae93b85`，对应本模块 state pin；既有前置未改。没有理论卷/atom/coverage 变更。


## 交付检查

本地 `scribe-content-checks.sh .lake/build/stratalint/raw-lean-report.json "" f838f20236e5a723d0c025ef53a80a07483008fa` **EXIT=0 / 24.560s**，`describe-report --check` 通过，真 KaTeX `markdown: judged=1 formula(s)=8 red=0`。另显式运行 `projections --check` **EXIT=0 / 11.840s**（脚本的增量条件本次不唤醒该子项，故另验，未把跳过冒充通过）。

最终主定理 statement_id：`sha256:644382e255f117a10aaa49f2edd5a8629e11da145f9a55fb35ca6bf687be2449`。模块 pin：`sha256:caf87d3426617c6f0545e97f8dd2dbc2878d58ecaa35521d5e7940afea45d083`。七个新增文件，零已有内容修改；目录容量未超限。开 PR 前再次仓内搜索目标，仅命中本实现。`git fetch origin dev` 后 dev 仍为预登记基线；`git merge-tree --write-tree HEAD origin/dev` EXIT=0、无冲突，树 `279539e6c3268787bf82fafabb54726ccf8f68ef`。`git diff --check` EXIT=0。

三条分步证明分别在提交 f9892a2311、0aeb40556a、31c09cfef8 推送；完整目标首次证明提交 eaeacbc412；冻结 fa3b58f259。均为真实 Lean 一般证明，不以有限核对计进展。PR 按本轮停止条件开启，auto-merge 不开启；不把 PR 开出冒充已合并。

## 最终交付

**成**：目标 `a368628_odd_iff` 已由 Lean 核验，最终 `make lean` EXIT=0，公理闭包仅标准三项，PR [#6718](https://github.com/the-omega-institute/trureturing/pull/6718) 已开出，目标分支 dev。数学剩余子命题：无。

PR 创建时源码提交 `638755ba199687da6516f64d2fe58ce85ed936ba`；读回状态 OPEN，工程检查与 Canonical Lean report production 正在运行，此时不主张 CI 通过。最终远端状态及逐门收据另写入 runner 指定 attempt-2 的 `implementation-report.md` 与 `result.json`。单线程实施、零独立评审席；未开启 auto-merge，未合并。
