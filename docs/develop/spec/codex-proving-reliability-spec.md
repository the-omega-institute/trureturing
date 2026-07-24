# SPEC:提升飞轮 codex 证明可靠性(deposit rate)

> 由 sshx 对抗共识产出(31 轮,6 哲学席 + 多轮 re-challenge + review triplet;每轮亲核源码)。
> 每个前提对 `/Users/auric/trureturing`、`/Users/auric/fkst-packages`、`~/newmath` 源码核实;方法论移植自 `~/newmath`(BEDC)已验证的可靠证明管线。

## 0. 摘要

飞轮 deposit rate 的限制**不是"codex 证不出"(证明前沿)**——这是被对抗过程亲核推翻的误诊。真限制是**两个已存在机制没接线 + 一个执行断点无重试**:

| | 根因(全核实) | 修复 | owner | 阶段 |
|---|---|---|---|---|
| **B** | 瞬态 pre-handoff 失败(#407=`dotnet Error 1`)不 auto-retry,真证明工作被丢 | re-implementation re-drive | 上游 fkst `impl_failure.lua` | **先做,最小最高杠杆** |
| **A** | proposer's-choice 绕过既有 frontier-generation;X_Frontier 10/11 是 `Unit:=()` placeholder(无真 obligation 可选) | 补真声明 → 只读 readiness 查询 → fail-closed 消费 | trureturing(X_Frontier + StrataLint.Cli + theory-selfgrowth) | **后做,3 个证据门 PR** |

**共识砍掉**:no-changes auto-retry、数据驱动 prompt 失败表、oracle 旁路、独立 retry controller、往 TruthNode 塞命题字段、新 binary、DAG schema 改。

## 1. 根因(对源核实)

### 1.1 Executor 断点(推翻"证明前沿"误诊)
- `fkst-packages/packages/github-devloop/core/impl_failure.lua:9`:`auto_retryable_reasons = { codex-failed, non-descendant-head }`,`max=2`。**`local-iteration-failed`/`no-changes` 不在内 → 直接 impl-failed/blocked。**
- 实证:#407(Implement #401 GoldenInt norm powers)失败于 `local-iteration-failed` + `make[1]: *** [dotnet] Error 1`——**瞬态 preflight/构建失败,非证明失败**。命题(`norm_natAbs_le_of_dvd` 等)几行可证。真证明工作被无 retry 丢弃。
- **辨析(review 亲核)**:`local-iteration-failed` 是**未分型 sum**——覆盖瞬态 runner/dotnet/infra 失败 **AND 候选自身破坏仓库**(如 Codex 写 unclassified 文件触 FILEMAP-UNCLASSIFIED)。源码无区分器。

### 1.2 Producer 断点
- `packages/theory-selfgrowth/core.lua:28/200`:开放式 **proposer's-choice**("提议任意 worthwhile 定理"),**绕过**既有 `.fkst/workflows/frontier-generation.json`(已声明"从 truth-DAG 的 **dependency-ready open edge** 选题 + 发 formal statement + deps + hint")。
- 原因:substrate `TruthNode = {RepoPath,Gid,State,ModuleName}` 无 proposition/deps 字段,**算不出 dependency-ready edge** → 契约不可执行 → 退回 proposer's-choice。
- **且**:`D5/X_Frontier/` 11 文件中 **10 个是 `def <x>Ticket : Unit := ()` placeholder**(任务票据),非真 formal open declaration → 即使有 readiness 查询,也**无机器可读 obligation 可选**。
- 已存在但未接:`make preflight`(`FKST_DEVLOOP_LOCAL_TEST_COMMAND`,deploy.env:34)= 提交前本地自验证。

## 2. 方案

### 杠杆 B —— 令瞬态 pre-handoff 失败可重试(先做 · 上游 fkst PR · 最小)

**改**:`packages/github-devloop/core/impl_failure.lua` 的 `auto_retryable_reasons` **仅新增 `["local-iteration-failed"]=true`**(`max=2` 不变;**`no-changes` 保持 non-retryable**——no-changes=codex 产空,重试是 Goodhart 浪费)。

**语义(review 勘正后的唯一自洽形 = re-implementation re-drive,锁 logical lineage 非候选身份)**:
- attempt=1 的 `local-iteration-failed` → **reset/clean attempt-1 的未提交候选**(擦掉其对 worktree 的一切改动,含破坏仓库的写入)→ 同确定性 branch **重跑 Codex 生成 gen-2**(新候选,只锁 proposal/task lineage)→ 过**同一 canonical local gate**(`make preflight`)。
- attempt=2 仍失败 → terminal(不再重试)。
- **无 false-green**:gen-2 必须过同一 gate;reset/clean 保证 gen-2 从干净基线起,破坏仓库的 attempt-1 不被 launder。
- **明确非** "same-candidate verification-only re-verify"(review 证其与 reset+re-Codex 互斥)。

**回归测试(必写)**:
1. attempt=1 `local-iteration-failed` → 恰一次 re-drive;attempt=2 → terminal。
2. reset/clean 次序:attempt-1 未提交 diff(含 untracked/ignored、FILEMAP-UNCLASSIFIED 写入)在 gen-2 前被完全擦除。
3. 破坏仓库候选不被 launder(gen-2 从干净起)。
4. `no-changes` 仍 non-retryable。
5. failure detail / lineage 不丢;durable failure marker + CAS;重复 delivery 幂等。
6. `codex-failed`/`non-descendant-head` 行为不变(保守扩展)。

### 杠杆 A —— dependency-ready 选题替换 proposer's-choice(后做 · 3 个证据门 sequential PR)

**A0(pilot · 补真声明)**:在 `D5/X_Frontier/` 为 D5/GoldenInt 建**一个**真候选——one-task-one-module、唯一 `theorem <name> : <statement> := sorry`、imports 全指向 active-frozen 节点。**替换 `Unit:=()` placeholder**;治理/工具 Unit 票不算候选。这是使 readiness 查询有意义的前提。

**A1(query · shadow)**:`Meta/StrataLint/StrataLint.Cli` 加**只读子命令 `frontier-ready`**:join ①TruthDag `DeriveState` 支持的 **declaration-level dependency-ready 集**(open frontier 声明,其 proof 依赖全 active-frozen)× ②X_Frontier 真 formal obligation。**readiness = eligibility filter ONLY**(硬 guard:排除 zero-import、`Unit`、治理/placeholder;**禁 Goodhart on ready-count / 降数学野心**;worth 另判)。先 shadow/observe(发候选,不驱动)。

**A2(consume · cutover)**:`theory-selfgrowth` **fail-closed 消费** `frontier-ready`——无合格候选(live/非 placeholder/one-task-one-module/sorry/frozen-imports)时**空 no-op**(不退回 proposer's-choice);有则消费替换选题。

**禁**:TruthNode/DAG root/hash schema 改、新 binary、readiness 复制 frontier-generation.json 声明(query 只 join TruthDag+X_Frontier 两个既有真源)。

## 3. 顺序与 worth

**B 先**:单一上游 fkst PR,不触 trureturing SL-022 保护面,直修已证的 #407 类瞬态丢弃,2 行 allowlist + re-drive 语义 + 测试 = 最小最高杠杆。
**A 后**:A0→A1→A2 三个证据门 PR(非长期双模式);A0 无真声明则 A1/A2 无意义,故严格顺序。

## 4. 纪律锚(CLAUDE.md)

- **第22条机器判**:B/A 全机器判,无人审门;readiness/retry 皆机器可核。
- **唯一真源(第6条)**:A 的 query 只 join TruthDag(依赖真源)+ X_Frontier(命题真源),不建第二真源;不复制 frontier-generation.json 声明。
- **第20条(错误驱动制度)**:B 是"出错→在产生处成机器规则"(local-iteration-failed 瞬态类 → auto-retry 规则),非无脑重试;no-changes 不入(非瞬态)。
- **保守扩展(第21条)**:B 不改 codex-failed/non-descendant 既有判;A 不翻已冻结节点(readiness 只读派生)。
- **反 Goodhart(第3/5条)**:readiness 仅 eligibility,worth 另判,防飞轮游戏"ready 数"降野心。

## 5. 对抗轨迹(可审计)

v1(4 杠杆)→ round1 毁灭(杠杆1/2 已存在)→ v2 → round2(A 不塞 TruthNode;executor gap 核实)→ v3 → round3(A=只读查询最小形)→ v4 → round4(B 只 local-iteration-failed;readiness=eligibility-only;B 先)→ v5 → round5(B=完整重实现;local-iteration-failed 未分型;X_Frontier 全 Unit placeholder)→ v6 → round6 review(B 内在矛盾 reject)→ **v7 本稿**(B=re-implementation re-drive 锁 logical lineage;A 分 3 证据门)。

**沿途被对抗亲核推翻的误诊**:①"codex 证不出=前沿"(实为 #407 瞬态 dotnet Error 1 无 retry);②"加可解性门/自验证"(实已存在 frontier-generation+make preflight);③"往 TruthNode 塞命题"(TruthDag 只拥有 graph facts);④"same-candidate verification-only"(与 reset+re-Codex 互斥)。
