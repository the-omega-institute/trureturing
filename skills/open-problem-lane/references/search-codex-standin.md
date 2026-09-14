<!-- open-problem-lane reference: codex-cli search stand-in brief — worked example R25 (used when the GPT Pro pool is down); replace round id, exclusion list, output path. -->

# sshx search brief (thinking stage, bias=novelty-hunting) — codex-cli seat standing in for the GPT Pro search seat (pool outage) — find 3 old (≤2018), still-open, Lean-provable-or-refutable small conjectures (round R25-codex)

You are one `thinking_panel` worker (codex-cli) acting as the SEARCH seat because the GPT Pro pool has been unavailable for 6 hours. Worktree `<repo>-op-search-r25` (scratch; do NOT create D5 modules, do NOT commit or push anything — this is a read-only research seat except for writing your report file). OP_SCRATCH = `$OP_SCRATCH`. Write your full report to `OP_SCRATCH/search-r25-codex-report.md` and return the envelope below. Time budget ≈ 2.5 h. You have network (verify with one `curl -sI https://oeis.org` first; if unavailable, return `capability: wait-for-capability`).

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

## 任务（与 GPT Pro 搜题席同一契约，中文原文照抄）
找 3 个老的(≤2018)、至今无解、可在 Lean 4+Mathlib 数十到数百行内证明或反驳的小猜想(第二十五轮，codex 代席)

仓库(公开):https://github.com/the-omega-institute/trureturing (HEAD 0ee0ccae84)。**勿重报**(已进管线/已淘汰,A-number 列表):A000364 A000522 A001222 A004123 A005374 A006093 A006154 A006697 A008472 A008474 A014574 A018800 A026010 A027907 A028859 A034444 A034841 A034885 A036556 A038552 A038867 A039824 A048105 A049020 A051283 A051634 A056777 A057599 A060621 A060693 A062319 A063880 A064098 A064618 A065359 A065560 A066743 A066796 A066840 A067720 A068012 A069359 A069932 A070965 A072326 A072872 A075075 A076141 A076502 A077028 A077864 A078841 A079051 A079063 A080170 A080795 A081831 A082447 A083207 A083905 A084068 A084759 A087331 A087719 A088226 A089610 A090287 A091259 A091468 A091817 A092028 A093345 A093714 A096126 A096127 A096270 A096304 A097602 A099173 A100682 A100952 A104863 A105403 A107928 A110454 A110545 A113571 A116184 A117261 A119616 A119623 A120292 A122369 A122399 A122869 A124418 A126762 A127854 A128921 A129527 A129654 A129924 A131853 A133901 A135418 A135499 A140869 A143132 A146557 A146567 A152020 A155200 A157615 A158119 A158623 A159907 A160686 A163617 A163767 A172495 A173644 A174655 A175033 A175386 A175406 A175522 A175582 A176189 A177680 A178294 A179873 A181176 A183161 A187767 A187941 A189573 A192023 A199812 A204217 A208342 A208343 A209862 A215926 A225053 A225064 A226857 A227631 A231548 A245211 A245212 A245778 A245786 A246056 A246423 A247477 A249621 A249968 A249969 A254748 A258409 A260310 A261131 A267610 A267700 A268866 A270096 A270236 A275652 A275654 A276976 A277030 A280246 A280864 A283751 A286182 A286183 A286185 A288133 A292726 A296440 A297741 A297830 A301976 A302975 A304362 A306305 A306779 A306921 A309132 A318921 A319927 A320097 A320099 A323557 A324969 A325273 A325618 A326042 A326244 A327969 A328190 A328959 A329278 A329398 A332872 A334184 A334595 A335407 A335901 A335925 A338153 A338154 A342546 A347854–A347858 A389000 A046528 A129598 A008590 A045576 A078181 A091338 A257750 A262669;另已进管线或结算:Fibonacci Quarterly H-655(ii)、Kreh JIS 18 (2015) 15.5.3 Conjecture 18、Erdős 1989 Mahler 0/1 数位平方旁猜、Erdős 1981 模 d 非平方和(已知:Lagarias–Odlyzko–Shearer 1982)、Erdős 1989 连续块和 f(n)=(n+1)/2(Freud 1993 蕴含)、A215926(蕴含著名开放问题)、Erdős 1989 Mahler 0/1 数位平方旁猜(已反驳 #7668)、OEIS A319927 Ianakiev 幂和整除(已反驳 #7675)、Erdős 1985 RMJM「23 是唯一反例」连续积 squarefree-factor(在管线 #7679)、Erdős–Moser 两两成平方 7-集/Guy D15(第三档核心难题,勿报)、A319927(已反驳 #7675)、A049591(Cloitre 2002 素数间隙-约数刻画,已反驳 #7703)、A103585(Stephan 2007 period-43,已反驳 #7717)、A005590(Stephan 2003 零点分类,backlog 待 Reznick 文献核)、A102370(sloping binary,勿报)。

判据:①首次陈述 ≤2018,给出处(A-number+评注日期,或卷/期/页);②联网核对无解(读 OEIS history 的编辑讨论、追引用),写出看到的部分结果;③非著名难题;④定义可按来源字面写(排除只能经生成函数定义者);⑤优先可反驳者。

**硬预检(本仓评审规则——按已合入判例校准)**:候选须落入以下**可计数形状**之一,并在候选里写明属哪一类:
- (A) **反驳一条具名全称断言**:给出一个具体反例(单个数/元组)使某 OEIS/文献里的 `∀…` 猜想为假。**允许**用 `decide`/`norm_num`/一条一般定理实例化核验该反例——这是本仓已合入多次的 certified-instance/refutes 形(A018800、Erdős–Mahler、A319927)。反例可以是有限单点,也可以是无穷反例族(带模分类或估计,如 A100952 mod 6、A079063 渐近)。
- (B) **证明/反驳其核心步骤是非归约的**:模小素数/奇偶/素性的 case split、无穷族构造、带指数估计的构造、对全部层数/步数的归纳不变量(如 A008474、A089610、A226857、Erdős 1985 的归纳+primorial)。
**排除(本仓判 bind-only,不可计数)**:(i) 交付的核心是一条**正向恒等式**,等于某条 Mathlib 求和引理(裂项 `Finset.sum_range_sub`、几何和 `geom_sum`、单调性/子集支配)换个辅助函数的实例——初等竞赛型恒等式几乎都属此类(H-655 教训);(ii) 交付的核心是**正向地计算某定义在具体数/素数幂乘积处的值**(因子结构改写 + simp/omega),且不用于反驳任何具名断言(A187941 教训)。**注意**:同样一条 `decide`,若用于**反驳**具名 ∀ 则属 (A) 可计数,若用于**正向**证明某存在/取值则属排除(ii)——区别在于它处决的是不是一条事前存在的全称断言。
- **优先 ∀-型可反驳猜想**:OEIS 评注里形如「Conjecture: a(n) = …」「for all n」「is always」的全称句,先算前 10⁴–10⁶ 项找第一个反例;找到即 (A) 类候选。避开 ∀∃ 型(需构造)与「is there / does there exist」型(需证存在)——这些通常需要全局论证,不可计数。

**本轮另勿重报**:A129598(Karttunen 2007,已核为可反驳但源条目自相矛盾+证书重,单列 backlog)、A103585、A049591、A005590、A319927。**本轮优先「干净」候选**:反例只需单个数的有限算术(素因子/约数/同余),避免需要 totient 最小原像证明、需要历史定义考据、或源 %C 举例与交叉引用集自相矛盾的条目。

**本轮另勿重报**(已合入/在管线/backlog):A046528(Krizek 2013 σ/τ 有理幂,在管线)、A008590(Ratajczak 2017 双和偶性,在管线 PR #7785)、A046528(已合入 #7779)、A045576(Smyth 2010 蕴含,淘汰)、A078181、A091338、A257750、A262669(已淘汰)、A090825、A005590、A103585、A049591、A319927、A129598、A102370、A053176。**优先干净单点反例**(单个数的有限素因子/约数/同余算术);避开需 totient 最小原像、Bernoulli/von Staudt、历史定义考据、或 %C 举例与交叉引用集自相矛盾的条目(A129598 教训)。

本轮场所:**第二十一池(回到 OEIS 评注型全称猜想——本仓 KPI 主矿脉)**——扫 OEIS 中**至今仍标 Conjecture 且形如全称断言**的整除/同余/递推/计数评注,优先以下作者与年代(避开已反复取样的 Zumkeller/Ianakiev 已解条目):(a) **Benoit Cloitre、Ralf Stephan、Vladeta Jovovic、Reinhard Zumkeller、Amarnath Murthy** 2003–2016 的 Conjecture 评注;(b) **Michel Marcus、Antti Karttunen、Chai Wah Wu、Robert Israel、Peter Munn** 的 Conjecture/「appears to」评注;(c) OEIS 中 `keyword:conj` 或评注含「Conjecture:」的整数序列,定义可按字面写 Lean(排除仅由生成函数/浮点定义者)。每条**先算前 10⁴–10⁶ 项**找反例:找到第一个反例即 (A) 类,给出反例数与失败项;若数千项内无反例但看得出结构(模分类/无穷族),按 (B) 报;两者皆无则弃。逐条读 OEIS history 的编辑讨论排除已证/已反驳/已修正,注意 2026 OEIS Open 基准 arXiv:2608.11941 与「proved by an autonomous AI agent」评注。codex 席本轮不搜题。

每条:精确陈述(量词写全)、出处、无解核对、证明或反驳骨架(2–6 步,标出非归约步骤)、Mathlib 可及性(真实名)、行数估计。未核实者明写「未核实」;都不达标就报 0。


## Additional rules for the codex stand-in (English, binding)
- **Already handled this session (do NOT report):** A046528, A129598, A000040 (Detlefs 2014 Fibonacci–Fermat, refuted at 219781), A008590, A008578 (Gerasimova 2013 — KNOWN: Sándor 1988 / Sándor–Kovács 2015 eq. (40)), A001108 (Krizek 2016, in Stage B), A277201, A018804, A163553, A001969, A067274, A034496 (all settled in-entry), A140110 / A265310 (backlog, bind-only / heavy), A076481, A159907, A045917, A001110, A000668 σ-type Mersenne characterizations, A005809/A000172 Wolstenholme-type, A000961 Ordowski–Resta, A005117/A034444/A002326/A001220.
- **Actually COMPUTE.** For every ∀-type OEIS conjecture you consider, write and run a Python check (sympy is available) over at least the first 10⁴–10⁶ cases; report the exact command/range/outcome. A counterexample you find yourself is the best possible candidate (class A). Do not report a candidate whose only evidence is "looks plausible".
- **Read the whole entry**, including later comments (a later comment often says "The above conjecture is false/true …") and the revision history (`https://oeis.org/history?seq=A…` — note anonymous access may be limited; say so).
- **Literature shape search is mandatory for proof-type candidates** (lesson from A008578): search the inequality/identity's mathematical shape on arXiv/Crossref/Google Scholar-like surfaces, not just the A-number; if a published theorem implies the conjecture, mark it KNOWN and drop it.
- Prefer refutable ∀-claims (class A) over proof-type (class B); prefer 2000–2018 comments by Cloitre/Stephan/Jovovic/Murthy/Karttunen/Krizek/Ratajczak/Detlefs/Ordowski/Ianakiev/Yanev/Firoozbakht/Layman/Wesolowski and similar; also consider erdosproblems.com small old problems and Rényi-archive Erdős side questions if you can verify openness.
- Output for EACH candidate: verbatim %N and the conjecture line with author/date; the exact universal statement (quantifiers spelled out); your computed check (range, counterexample or zero mismatches); openness evidence (what you read, dated); a 2–6 step Lean route with the non-reductive core named; Mathlib names you verified exist; a rough line estimate. Report 0 honestly if nothing survives.

## Result envelope
`conclusion` = {"verdict":"propose|abstain","capability":"...","candidates":[{"id":"A…","class":"A|B","statement":"...","witness_or_check":"...","openness":"...","route":"...","mathlib":[...],"lines":n}],"eliminated":[{"id":"A…","reason":"..."}],"report_path":"OP_SCRATCH/search-r25-codex-report.md","visible_inputs":["GoalArtifact(complete)","repo-prior-exposed"]}; `log_ref` = a path.
