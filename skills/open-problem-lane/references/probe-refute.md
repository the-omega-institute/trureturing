<!-- open-problem-lane reference: Probe (thinking-seat) brief — worked example A008365 (refutation); lane-specific lines are marked. -->

# sshx probe brief (thinking stage, bias=fidelity) — lane `op-a008365` — OEIS A008365 (Detlefs 2011): refute "13-rough numbers = {n : n^24 mod 2310 ∈ {1,421,631,841}}" — by n = 17 (13-rough, residue 1681)

You are one `thinking_panel` worker (codex-cli). Worktree `<repo>-op-a008365` (branch `lane/math/op-a008365`, fresh from `origin/dev`). OP_SCRATCH = `$OP_SCRATCH`. Preregistration issue (opened BEFORE this probe, 2026-09-14): https://github.com/the-omega-institute/trureturing/issues/7875 — read it first; if your observed witness/route differs, say so (the orchestrator re-preregisters). Time budget ≈ 3 h. Read a landed finite-certificate refutation for header/shape (`D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.lean` on dev, #7703). **OUTPUT DISCIPLINE:** run every long command as `<cmd> > $OP_SCRATCH/<name>-op-a008365.log 2>&1; echo EXIT=$?` and echo only the exit line plus `tail -5`.

## GoalArtifact (complete; cite in visible_inputs; you are `repo-prior-exposed`)
```yaml
raw_user_input: |
  使用 /sshx 最高效率推进数学形式化工作, 1席gpt pro, 其他都使用codex cli, 实现使用codex cli,
  独立复用worktree 工作, 检查主checkout lean缓存够热, 及时pr 到dev并同步, 持续到2027年.
  实施codex cli. gpt pro 传本仓库地址,搜索arvix, 找项目适合解决的开放问题, 持续然后努力解决这些开放问题.
  也没有必要吊在一个问题上, 持续搜接近的.以解决开放问题为第一要务, 可以持续搜索, 解决任何开放问题都可以,
  KPI 是解决开放问题的数量. 找一些老的, erdos上的问题试试.
normalized_goal: |
  常设循环(至 2027):GPT Pro 一席常驻搜题(arXiv + erdosproblems.com 老问题 + OEIS),codex-cli 席探针/实施/评审,
  把外部真开放陈述以 Lean 内核证明或反驳落地到 dev(Lean 模块 + Scribe 镜像 + 冻结 + Problems/ 卷宗 + 解决声明),
  KPI = 机器可数的已解决开放问题数(OPEN_PROBLEM_RESOLUTION 标记数)。任何领域皆可;不吊在单题上。
constraints:
  - 载体:1 席 nyxid-oracle(GPT Pro)搜题;其余一切席位 codex-cli;实施只用 codex-cli(用户 2026-09-13 指令,覆盖 sshx 默认布局)
  - 每席独立 worktree,可复用;本机 codex 席 ≤6–8,同一时刻一个 lean-report;主检出常驻 dev 只同步
  - 先库后证;已知结果不派席;候选进管线前答「文献里有没有」;进展以解决数计,不以模块/席位数计
  - 逃逸内容 + refutes/escape-witness 准入;禁 native_decide;禁 strict;禁 admin;merge=MERGED 才算完成
  - 通信即工件:接手/改判/结案留痕于 issue;PR 正文载产地三项
success_criteria:
  - 每轮:新增 ≥1 个机器可数的开放问题解决(Problems/<slug>.md + Scribe 解决声明 + 冻结定理)合入 dev,或如实报「本轮 0」并给淘汰读数
  - 主检出 .lake 与 dev tip 同步(make lean Built=0 后可作 donor)
  - 在飞 PR 及时合入 dev,不滞留
iteration_question: 距「又一个开放问题以内核证明/反驳落地 dev 并被机器计数」还差什么?
harness:
  provided_capabilities:
    - 宿主后台作业与完成通知(run_in_background)
    - 仓内派席器 tools/scripts/agent/seat/dispatch.sh(codex-cli)与 nyx.sh(nyxid)
    - make 器谱(worktree/lean/deposit/deposit-uncovered/cover/pr-open)与三 required check
    - 常设目标(/goal)由宿主持续驱动(boundary-owner=用户,已在 /goal 文本中确认「持续到2027年」)
  trust_boundary: 用户(τ=0 owner)可信非无误;codex/nyxid 席位不可信、其自报须亲验;机器门(CI 三门)是准入权威
  decision_ownership:
    product_governance_boundary: 用户(选题方向、载体布局、冻结面、元层)
    engineering: codex-cli 实施席 + orchestrator 亲验
    orchestration: claude 主循环(本会话 <session>)
revisions: []
```

## Target
Fetch `https://oeis.org/search?q=id:A008365&fmt=text` and quote verbatim: `%N` = "13-rough numbers: positive integers that have no prime factors less than 13." (`%A` N. J. A. Sloane) and the refuted `%C` (Gary Detlefs, Dec 30 2011) = "Conjecture: Numbers n such that n^24 is congruent to {1,421,631,841} mod 2310." Reading: {n ≥ 1 : every prime factor of n is ≥ 13} = {n ≥ 1 : n^24 mod 2310 ∈ {1, 421, 631, 841}}. REFUTE at **n = 17**: 17 is prime, so its only prime factor is 17 ≥ 13 (17 ∈ A008365), but 17^24 mod 2310 = 1681 ∉ {1, 421, 631, 841}. DISCLOSE (do not claim): the true residue set for n coprime to 2310 is {1, 421, 631, 841, 1681} (n^24 ≡ n^4 mod 11 takes the five fourth-power residues; 1681 ≡ 9 mod 11); the converse inclusion (residue in the set ⟹ 13-rough) holds but is NOT claimed. NOT claimed: the corrected five-residue characterization, other A008365 comments.

## Proof route (data — re-derive; keep public surface minimal)
Define `isRough13 (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → 13 ≤ p`, `inResidueSet (n : ℕ) : Prop := n ^ 24 % 2310 = 1 ∨ n ^ 24 % 2310 = 421 ∨ n ^ 24 % 2310 = 631 ∨ n ^ 24 % 2310 = 841`, `claim : Prop := ∀ n : ℕ, 0 < n → (isRough13 n ↔ inResidueSet n)`, PUBLIC `theorem result : ¬ claim`. Route (preregistered #7875), witness n = 17: (1) `isRough13 17`: for prime p ∣ 17, `Nat.Prime.eq_one_or_self_of_dvd` (with `Nat.prime_iff`/`norm_num : Nat.Prime 17`) gives p = 1 (impossible for a prime) or p = 17 ≥ 13; (2) `17 ^ 24 % 2310 = 1681` by `decide` or `norm_num`; (3) `¬ inResidueSet 17` by `decide` after (2) (or `norm_num [inResidueSet]`); (4) `(hclaim 17 (by decide)).mp h1` yields `inResidueSet 17`, contradiction. Orchestrator numerics (independent, sympy): 8311 mismatches for n ≤ 2·10⁵, 17 least (then 61, 71, 83, 127, …); 13-rough n ≤ 2·10⁵ realize exactly the residues {1, 421, 631, 841, 1681}. Report **form (2)** (inline finite certificate); `utility: kind=certified-instance; basis=refutes`; no `native_decide`; no `sorry`; measure kernel cost and report (expected trivial).

**REUSE RULE (user directive 2026-09-15):** any helper that is a classical characterization or a general-purpose definition/lemma (σ/τ parity, residue classifications, next-prime, modular fast doubling, 2-adic ultrametric sums, …) must be PUBLIC — with a Scribe node and a real consumer in this module — so later lanes can `import` it as a frozen prerequisite; keep private only one-off certificate steps (concrete `decide` facts). Before making it public, `git grep` origin/dev for an existing public declaration of the same statement (reuse it instead).

## Formalization
Module path: `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.lean` (Certificates bucket; count fresh — DIRECT file count, the directory has sub-buckets; `DirectoryFileLimit` = 96). Public: `isRough13`, `inResidueSet`, `claim`, `result` (four; keep helpers private or inline). std3; no `native_decide`; no `sorry`. Header 7 lines: `utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.claim; result=D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.result; claim=D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.claim`, `generality: I`, `mirror-E: none(waiver:kernel-checked-refutation)`; digest ≤ 99 chars. anchors = consumed Mathlib modules in `mathlib/module/…` form after the deletion experiment. If anything is awkward, report the exact stuck goal as `revise` (do NOT fake it). NOTE (orchestrator ruling, binding): a finite certificate whose atomic facts are newly COMPUTED by decide/norm_num is form-(2) CONTENT per the landed A049591 #7703 / A129598 #7791 / A000040 #7827 precedents — do NOT report it as bind-only.

## Header form (SL-015)
Write `anchors: [mathlib/module/Mathlib.<Module>, …]` (canonical external anchor form, one per consumed Mathlib import); bare `Mathlib.<Module>` passes header-check.sh but is red at CI admission.

## Discipline (read first, tracked in this tree)
`tools/scripts/agent/probe-brief-note.txt` — commit + push progress after every compiling unit (your lane branch is yours; the module file may live at its final path); minimal proof-shape report fields; the hard rule that you FIRST try to close the target with pinned Mathlib instantiation + normalization only, and if that succeeds you report `bind-only` and stop. ORCHESTRATOR RULING (binding, CLAUDE.md §3.2): a finite certificate whose atomic facts are newly COMPUTED here by `decide` / `norm_num` / `reduce_mod_char` (a residue, a primality/compositeness fact, an evaluated sum) is form-(2) CONTENT, not normalization — normalization only covers atomic facts already SUPPLIED by frozen or Mathlib prerequisites; do not self-report such a certificate as `bind-only`. `git status --short` must be empty at the end except for files you committed. Never touch `Golden/**`, `Meta/Digestion/**`, `Blueprint/**` (no Scribe, no deposit, no PR — this is a probe). Build: `make lean-cache-ensure` once (seeds `.lake` from the warm donor), then compile your file with `lake env lean <file>` (bare lake is allowed on a stamped hot tree; never bare `lake build`); if you need the full door use `bash tools/scripts/agent/serial-lean.sh <tree>`. You have network (verify with one `curl -sI` first; if unavailable write `capability: wait-for-capability`).

## Common steps
1. Fetch the source page and quote the conjecture VERBATIM (OEIS internal format `https://oeis.org/search?q=id:A<n>&fmt=text`); record author/date; read the entry's revision history for later comments claiming proof/refutation; identifier searches on arXiv, OpenAlex, MathOverflow, GitHub (write "not found in the checked surfaces", dated).
2. Independent Python check of the statement on a bounded range (report range and outcome; exact integers).
3. Repo dedupe on current dev: `git fetch origin`; `git grep -n -P '<distinctive terms>' origin/dev -- D5 Problems Library` (report each command + hit count; `git grep -E` has no `\b`). Check in-flight lanes: `bash tools/scripts/agent/inflight_mods.sh` if present.
4. Formalize the WHOLE statement in Lean 4 + pinned Mathlib at the final module path given below (seven-line header per `tools/scripts/agent/header-check.sh`; copy a tracked neighbour's header; `utility:` line per `tools/StrataLint.Engine/Rules/TheoryGeneration/UtilitySyntax.cs`; `anchors:` = Mathlib modules imported; no umbrella `import Mathlib`; no `native_decide`; no `sorry`; `#print axioms` of every public theorem = `[propext, Classical.choice, Quot.sound]`). `propose` only if the main statement compiles with std3 axioms and no sorry. Partial progress is a legitimate `revise`/`abstain` with the exact stuck goal.
5. Proof-shape self-judgement per CLAUDE.md §3.2 for every theorem you declared: `bind-only` vs `content`; for `content` name the escape witness and answer the four criteria (inside the dependency closure / not obtainable by instantiation-projection-normalization of Mathlib or frozen prerequisites / not definitionally equivalent to the conclusion / on the live derivation path). Bind-only helper declarations are forbidden in deliveries — fold them into `have`s inside content theorems. If the whole module is bind-only, say so: `admission_basis: none`.
6. Commit + push the module to your lane branch (`git push -u origin <branch>`), and copy the final `.lean` to `OP_SCRATCH/probes/<name>.lean`.

## Result envelope
`conclusion` = {"verdict":"propose|revise|reject|abstain","status":"proved|refuted|partial|open|already-known|duplicate","capability":"...","source_verbatim":"...","source_locator":"...","literature_check":{"searched":[...],"found":"..."},"python_check":{"range":"...","outcome":"..."},"repo_dedupe":[{"cmd":"...","hits":n}],"module_path":"...","branch":"...","head":"<sha>","main_theorem":"<name : statement>","public_declarations":[...],"print_axioms":{...},"lean_exit":n,"proof_shape":{...},"escape_witness":"...|null","admission_basis":"escape-witness|none","stuck_goal":"...|null","effort_hours_remaining":n,"not_claimed":[...],"assumed_unverified":[...],"visible_inputs":["GoalArtifact(complete)","repo-prior-exposed"]}; `log_ref` = a path.
