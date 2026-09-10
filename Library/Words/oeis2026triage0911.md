---
bibkey: oeis2026triage0911
authors: OEIS Foundation Inc.; Codex triage workers
year: 2026
title: 30 new OEIS candidates — third proof and dispatch triage, 0911 task
doi: null
url: https://oeis.org/
claim: Source-based triage only; no new mathematical theorem or Lean module is claimed.
strata_touched: []
license: citation-only
triage: anchor
---

# 第三轮 OEIS 分诊：新窗，判据不放宽

**落盘纪律：每完成一批即 git commit + git push。** 本轮已依此分批提交并推送，提交链可在分支历史核查。

源码基线 `9d18c01262f7dfd97eddbd07fbe0931fe832ed9a`，分支 `lane/math/oeis-triage3-0910`；Mathlib 钉版 `db584cd6d46c92f209a44c0f1c829460d327499d`，Lean v4.33.0。只写分诊文献，不建 Lean 模块、不冻结。产地为 Codex 主席与三个同模型族 codex-cli 全条目阅读席；主席综合并复核承重映射，不冒充异模型独立共识。采用 lean4 skill 的只读声明检索，无 Lean 编译或内核重验。

第一档靶的判据是「该陈述在文献中有没有证明」，不是「有没有人写过」。沿用前两轮：1 为有明确短组合/算术逃逸的候选，2 为非常规有限计算前沿，3 为尚无短逃逸的深层问题，out 为已知、错误、纯定义或不派的渐近/分布目标。published 表示所选精确目标有公开证明或反驳（公开仓内证明另明示），不是仅出现过猜想；open 仅表示所读材料仍作猜想且未找到证明；unknown 表示证明身份或目标桥未核实。数值 yes 指可作有意义的有限检验；每段另报实际规模，不把数据当证明。bind-only 风险来自钉版具名声明比较，none 只是本次检索未找到，绝非全库不存在证明。伪签名均未编译。

已完成 **30/30** 个所选候选，每条恰有一行与一段；与342条排除集的交集为 **0**。建议 **dispatch 2、note-only 21、drop 7**；文献 **open 16、published 7、unknown 7**；档位 **1:6、2:0、3:16、out:8**。两条派席为 **A398581**（严格三单位分数的首解/最大分母比较）和 **A398189**（奇n正k的剩余估值分支），合计 **2席**，互不等价。其余第一档形态因文献桥、语义或证明前置未清仍留note-only；这里没有以席位数作配额。全部30条都有本轮数值运行，逐段区分独立枚举、递推实验与仅公式/DATA回归。

校准仍为A392698“曾写作猜想”不能据此降级，A388724确有期刊证明则应降级。本轮同形对照是A399456的**已证构形密度/未证全类最优性**，以及A398189的**已证k=0及偶n分支/未找到证明的奇n正k分支**；A399385和A398300的真实公开证明则确实淘汰。此两条历史校准仅沿用brief，不另计本轮分诊。

## 采集与边界

排除集严格复原为 342 个唯一 A 号，并与前两轮 93+249 条核对相等。官方镜像钉版 `69b127f67c75990effad199e316d6e8a5183b64c`，本次远端 HEAD 仍为此版；该快照上界 A399693，没有 A400/A401 目录。因此从 A398000–A399693 的完整原文关键词窗中取得 52 个未排除命中，选 30 条实质分诊；其余 22 条未分诊，不能算 drop。关键词包括 Conjecture / It appears / permutation，查词仅用于发现，裁决读完整字段。

本次主要来源是官方 https://github.com/oeis/oeisdata 镜像的完整 `.seq`，不是 OEIS JSON 接口响应。公开定位形如 https://github.com/oeis/oeisdata/blob/69b127f67c75990effad199e316d6e8a5183b64c/seq/A399/A399084.seq 。接口尝试分列：精确 id:A399200 得 HTTP200；urllib 搜索得 HTTP403；curl 通配查询得 HTTP200/null，不据此断言无匹配；本轮未遇 HTTP429，不把上一轮的429冒充本轮读数。A399639 镜像404，精确 JSON HTTP200但仅为 allocated 占位，详见 A399381 段。

实际读取与计算发生在2026-09-10（Asia/Singapore）；0911是本任务交付物标签。30条本体与全部一跳直接A号去重为102个ID：**101个完整镜像条目、725526字节，另1个allocated占位**。三个阅读席的必读清单分别37/18/47个，合并恰覆盖102个ID；主席另外完整读了定义桥A094291。完整字段重新提取的refs与落盘清单相等，101个原文的字节数和SHA256全部核对；A399639数学内容的缺口已明确保留。原始JSON仅有实际调用所得，镜像文件未转换冒充JSON。

52个发现命中中尚未分诊的22条：A398064、A398132、A398139、A398140、A398141、A398183、A398282、A398353、A398417、A398498、A398540、A398545、A398551、A398676、A398677、A398692、A398726、A398792、A398793、A398795、A399052、A399300。这些条目的关键词命中不是完成分诊，未纳入建议计数。

外链清单 `url-inventory.json` 覆盖上述条目及额外定义桥的1320个去重href字面页面；其中未打开的1310个字面页面逐个标ASSUMED-UNVERIFIED。摘要页、DOI页与实际取得的PDF分开记账：一个未打开的摘要页可以有已阅读PDF，不能据字面URL的未打开状态反推论文未读，也不能据PDF已读宣称摘要页曾返回200。逐段点名的实际PDF/HTML/源码及各reader的来源日志才承重。

## 未主张栏

未主张检索穷尽；未主张 open 等于全球无人证明；未主张所有外链论文已全文审读；未主张 published 等于原猜想为真。凡未真正打开的外链页面一律 **ASSUMED-UNVERIFIED**，只有逐段点名打开的文献可承重。完整条目阅读与外链全文阅读分账；一跳 A 号预检含 comment/formula/xref 的全部直接引用，不递归无限追引。临时原文、脚本及日志住 runner attempt，非永久公共存档。

## 排序表

| A号 | 一句话陈述 | 档位(1/2/3/out) | 文献(open/published/unknown) | bind-only(low/med/high) | 数值可验(yes/no) | 建议(dispatch/note-only/drop) |
| --- | --- | --- | --- | --- | --- | --- |
| [A398189](https://oeis.org/A398189) | 截断指数和在奇数n、正k且k不属于14模16例外类时满足所给2进制阶公式。 | 1 | open | med | yes | dispatch |
| [A398581](https://oeis.org/A398581) | 5/k 的严格三单位分数分解中，字典序首解不取得最大 z 时必有 k≡1 mod5。 | 1 | open | low | yes | dispatch |
| [A398690](https://oeis.org/A398690) | 简化Verlinde三角和的行生成函数分子r_n是回文多项式。 | 1 | open | med | yes | note-only |
| [A398713](https://oeis.org/A398713) | u(2m−σ(m))=τ(m)−2 的最小正解为 m=2^(u+1)，u≥0。 | 1 | open | med | yes | note-only |
| [A399306](https://oeis.org/A399306) | 最小Lucas表示末尾为1或1010的整数，其A094291最大二项式乘积不是平方。 | 1 | open | med | yes | note-only |
| [A399382](https://oeis.org/A399382) | a₊(n)=min{k>0:kn+1平方自由} 的取值覆盖所有正整数。 | 1 | unknown | med | yes | note-only |
| [A398024](https://oeis.org/A398024) | 3-convex多联骨牌按半周长计数的生成函数等于条目给定的F_3。 | 3 | unknown | low | yes | note-only |
| [A398025](https://oeis.org/A398025) | 4-convex多联骨牌按半周长计数的生成函数等于条目给定的F_4。 | 3 | unknown | low | yes | note-only |
| [A398026](https://oeis.org/A398026) | 5-convex多联骨牌按半周长计数的生成函数等于条目给定的F_5。 | 3 | unknown | low | yes | note-only |
| [A398027](https://oeis.org/A398027) | 6-convex多联骨牌按半周长计数的生成函数等于条目给定的F_6。 | 3 | unknown | low | yes | note-only |
| [A398028](https://oeis.org/A398028) | 7-convex多联骨牌按半周长计数的生成函数等于条目给定的F_7。 | 3 | unknown | low | yes | note-only |
| [A398149](https://oeis.org/A398149) | 按螺旋行列和互异规则贪心填数时，每个正整数最终出现。 | 3 | open | low | yes | note-only |
| [A398270](https://oeis.org/A398270) | 每个矩形四邻域网格的最大诱导森林大小等于最大诱导树大小。 | 3 | open | med | yes | note-only |
| [A398307](https://oeis.org/A398307) | 数位和 Van Eck 变体的零点恰为列出的26个指标，最后一个为541。 | 3 | open | low | yes | note-only |
| [A398446](https://oeis.org/A398446) | 1324-avoider的最大元距末端d位时，计数对每个d均有指定次数、首项和常数项的多项式表达。 | 3 | open | med | yes | note-only |
| [A398542](https://oeis.org/A398542) | 固定132-avoider底格的两格扩展计数d(b,k)有受次数界约束的中央二项式与4^k表达式。 | 3 | open | med | yes | note-only |
| [A398603](https://oeis.org/A398603) | 允许零平方与要求两个正平方的n项等差数列，其最小末项从n=13起相等。 | 3 | open | low | yes | note-only |
| [A398604](https://oeis.org/A398604) | 两类两平方和等差数列的最优末项所配步长，从n=12起相等。 | 3 | unknown | low | yes | note-only |
| [A399307](https://oeis.org/A399307) | Lucas–Collatz 映射中每个非5倍数正整数最终进入23周期或(2,4,3,1)周期。 | 3 | open | low | yes | note-only |
| [A399308](https://oeis.org/A399308) | Lucas–Collatz 映射中每个正5倍数最终进入70周期或(5,10)周期。 | 3 | open | low | yes | note-only |
| [A399369](https://oeis.org/A399369) | 正进位差相等且算术导数相等的不同整数对只有(28,16)。 | 3 | open | low | yes | note-only |
| [A399456](https://oeis.org/A399456) | 任何平面定宽凸体的全等不重叠打包密度都不超过所给 Reuleaux 三角形密度。 | 3 | open | low | yes | note-only |
| [A398259](https://oeis.org/A398259) | 数位和 Van Eck 变体满足 c(n)/n→1；另有与 A398307 相同的26零点猜想。 | out | open | low | yes | note-only |
| [A398186](https://oeis.org/A398186) | U(r)=(4r)!/((2r)!r!²) 时，r+s+1 整除 U(r)U(s)，从而卷积除以 n 为整数。 | out | published | med | yes | drop |
| [A398300](https://oeis.org/A398300) | 无限八邻域扫雷棋盘上 n 个雷的最小非雷格数字总和为 2⌈√(28n−12)⌉。 | out | published | low | yes | drop |
| [A398383](https://oeis.org/A398383) | C6a=B(q)(5+22u+5u²)/(1−u)³ 的第n项系数被n²整除。 | out | published | low | yes | drop |
| [A398901](https://oeis.org/A398901) | C6b=B(q)(1−u)/(1+u)² 的第n项系数被n²整除。 | out | published | low | yes | drop |
| [A399084](https://oeis.org/A399084) | 贪心 floor-sqrt 序列的极大严格下降段长度是五个1后接 m,1,m,1（m≥2）。 | out | published | high | yes | drop |
| [A399381](https://oeis.org/A399381) | a₋(n)=min{k>0:kn−1平方自由} 对所有n≥1存在且无界。 | out | published | med | yes | drop |
| [A399385](https://oeis.org/A399385) | 奇阶 off-diagonally symmetric ASM 的个数等于条目给出的阶乘乘积。 | out | published | low | yes | drop |

## 逐条证据

### A399084

精确目标：对原条以历史未用性定义的 `seq`，极大下降段恰为初始五个单点，以及每个 m≥2 在 s=m²+m−1 的四段 `(s,m),(s+m,1),(s+m+1,m),(s+2m+1,1)`。文献裁决：完整读本条与一跳引用；虽 OEIS 原文仍写 Conjecture，基线已含公开冻结的 `D5.S1.Digit.GreedyFloorSqrtRunBlocks.maximal_decreasing_run_lengths`（`D5/S1/Digit/GreedyFloorSqrtRunBlocks.lean:765`），其 literal-history `seq`、`IsMaximalDecreasingRun`、`seq_eq_closedForm`/`seq_four_blocks` 与目标匹配；冻结 state 的 statement_id 为 `sha256:601488f603b60668052dfc38ee7ce71ae93d3834a0fea46d0fae74f178884908`，此处 published 指公开仓内证明，未重编译。bind-only 疑似声明：上述 exact iff 已覆盖全目标，high，不能再派桥接席。数值方案实际跑 hash-set 历史递推 100001 项，以一次线性扫描取完整下降段，1259 段全部吻合，68 项 DATA 全相等；末尾未完成段不作反例。便宜形态是在线集合+游程扫描，无需对每一步重扫全部历史。拟议逃逸：无新增目标，drop；停止条件已触发为精确冻结同题。同族合派：本轮仅此一条，零席；不得改名为闭式再派。xref 预检全部直接 A 号（完整读）：A000196、A020703、A038722；这些是背景平方根序列，决定性淘汰证据来自仓内 exact theorem。

### A398581

精确目标：S_k={(x,y,z)∈ℕ³:0<x<y<z 且 5xyz=k(yz+xz+xy)}；若 S_k 非空且其字典序最小解的 z 小于 max z，则 k≡1(mod5)，不主张逆命题或所有 k 可解。文献裁决：完整读本条与全部直引，原条仍为 Conjecture；k=5q+4,q≥1 的排除论证已给出，不能冒充所有非1剩余类证明。A257843 只是4/k类比；A075249–A075251 的首解即停代码不能承重“最大z”，k=11 的首解(3,9,99)和最大解(4,5,220)已分离。打开官方 b398581.txt，未发现全目标证明，open。bind-only 疑似声明：Mathlib 的 `div_eq_div_iff` 只消去非零分母；D5 按 Egyptian/unit-fraction 与本号检索未见目标声明（none 限此次），跨剩余类最优性尚非绑定。数值方案实际用约分 a/b=(5x−k)/(kx)，仅枚举 k/5<x<3k/5 及 `(ay−b)(az−b)=b²` 的正因子对，过滤 d<b、d≡−b(mod a)、互补因子同余和 x<y<z；同时维护 lex 与 max z，保留并列最大z语义。k=1..1500 共450000个x、685283个合法三元组；得到86项全为1mod5，57项DATA及完整86项b-file完全吻合，k=1,2无严格解，计算段7.78秒。拟议逃逸：用残差分子 a 的小值按0、2、3、4mod5比较首解与所有后续x的 z 上界，重点是尚未由原条证明的0/2/3类；不是再跑三重枚举。停止条件：一个非1类的严格首解/最大解差异即反驳；只重证4类、得到有限窗口或找到文献全证明均停止派新席。同族合派：本轮独立一席，与4/k类比不合为同一个命题。xref 预检全部直接 A 号（完整读）：A075248、A075249、A075250、A075251、A257839、A257843。

### A398307

精确目标：按 A398259 的严格历史递推 c，∀n≥1，c(n)=0 ↔ n∈{1,2,4,6,11,13,18,21,25,33,46,170,187,196,288,320,334,424,433,437,455,505,514,523,530,541}。文献裁决：完整读本条与全部直引，原条“conjectured this list is complete”仅附10^6窗口；A181391 的无限零点证明查询前项自身，本变体查询十进制数位和，不能套用。bind-only 疑似声明：Mathlib `Nat.ofDigits_digits` 仅重构数字，D5 按本号与 digit-sum/Van Eck 搜索未见此全称目标（none 限本次）；不是有限状态系统的现成周期定理。数值方案实际用实际项值→最后指标字典，先查询 digitSum(c(n−1)) 的历史 j<n−1，再插入前项；单遍1000000项恰出现这26个零点，26项DATA全吻合，n>541到10^6无新增。便宜形态是 O(N) 字典递推而不是逐次倒扫，数位和只花对数位数。拟议逃逸：证明未来全部查询键已被历史覆盖的无界归纳不变量；新键范围随n增长，不能凭窗口封闭成有限自动机。停止条件：n>541出现零点即反驳；只有有限运行不得报证成；尚无覆盖不变量故note-only。同族合派：与 A398259 的零点子猜想完全同题，若日后有逃逸只合一席；极限=1既不等价于最后零点541，也未在此证明。xref 预检全部直接 A 号（完整读）：A181391、A398259。

### A398259

精确目标：c(1)=0；n≥2 时令 s=digitSum₁₀(c(n−1))，若最近 j<n−1 满足 c(j)=s 则 c(n)=n−1−j，否则0；主目标 ∀ε>0,∃N,∀n≥N,|c(n)/n−1|<ε。文献裁决：完整读本条与全部直引，原条明列极限猜想；A398260 的数位积变体有不同长期行为，A181391 的原始 Van Eck 结论不覆盖本目标。out 是渐近目标不派，并非文献已证明；open 不降成 published。bind-only 疑似声明：Mathlib `Nat.ofDigits_digits` 与一般极限定理不提供最近历史索引 j=o(n)；D5 按本号及数位和历史递推检索未见具名全目标（none 限此次），风险low。数值方案实际以先查后写字典算1000000项，80项DATA全等；c(10^4)=9365、c(10^5)=99353、c(10^6)=999847与原条三个检查点全等，26零点同 A398307。便宜形态是流式字典；若扩大实验应另记区间内最大缺口 n−c(n)，不能只看10的幂端点。拟议逃逸：把极限转为被查询键最近出现指标的 o(n) 上界，目前未构造，note-only。停止条件：有限端点吻合不立极限；仅证最终无零不报本主目标完成；找到对应全称上界或已发表证明再改判。同族合派：有限零点子目标与 A398307 合一席、零个当前派席，极限为另一个更强长期问题，不能把两者计为两次零点成果。xref 预检全部直接 A 号（完整读）：A007953、A181391、A398260、A398307。

### A398186

精确目标：∀r,s≥0,(r+s+1)∣U(r)U(s)，蕴含 ∀n≥1,n∣Σ_{k<n}U(k)U(n−1−k)。文献裁决：完整读本条及直引，打开 Shvets https://arxiv.org/html/2607.19427v1 ，Lemma 3.2 正是逐项整除，证明以 Legendre 的每个素数幂层比较余数；主席亲读其证明及 Proposition 3.1/Corollary 3.3 的坐标映射，reader2另读全文。仅预印本证明公开，未核实同行评审。A143583 的整数组合公式与 Catalan 乘积还覆盖弱化的卷积整数性。bind-only 疑似声明：Mathlib `padicValNat_factorial`、`succ_mul_catalan_eq_centralBinom` 是邻近工具，未搜得此四倍二项式逐项整除的 exact theorem，med；论文已有证明即不派，不能拿未入mathlib当开放。数值方案实际构造整数二项式 U(r)=C(4r,2r)C(2r,r)，检查r,s≤100全部10201对余数，零反例；64项卷积中17项DATA全等。便宜形态为二项式数组+卷积和模运算，无须模形式库。拟议逃逸：当前目标无；停止条件是已读到全目标证明，不能把同论文已证加强版再派。同族合派：与 A398383/A398901 同一 K3 模形式包，若补文学桥共一组，当前零席。 xref 预检全部直接 A 号（完整读；占位另注）：A000108、A000897、A143583。

### A398383

精确目标：u=64q∏_{m≥1}(1+q^m)^24、B=Σ_{k≥1}k^5q^k/(1−q^(2k))；∀n≥1,n²∣[q^n]B(5+22u+5u²)/(1−u)³。文献裁决：本条及全部直引完整读，打开 Shvets https://arxiv.org/html/2607.19427v1 Theorem1.1式(1.5)、Theorem5.3、Corollary6.2及7.2、§8完整合并证明；主席核对目标与奇素数/2进制合并，reader2读承重全文。旧 Bönisch–Duhr–Maggio arXiv2404.04085 Appendix B.1 只猜磁性，不是降级原因；新预印本的分母恰为1证明才是原因。bind-only 疑似声明：`PowerSeries.coeff_mul` 给有限反对角卷积，未检得D5或Mathlib的此亚纯模形式整除定理，low；没有现成形式化不改变published。数值方案实际用整数截断级数至q^64；展开有理函数的第j项系数16j²+16j+5，64个n²整除及v₂(c(n))≥5v₂(n)全部通过，15项DATA全等。便宜形态与 A398901 共用u、B和幂数组，不数值求q或做浮点微分。拟议逃逸：原条的2-adic加强版也由§7覆盖，当前无；停止条件已触发为确切公开证明。同族合派：三条 K3 包只算一个文献依赖组、零当前席；换成正性或2³ʳ整除商不构成新增靶。 xref 预检全部直接 A 号（完整读；占位另注）：A096960、A398186。

### A398901

精确目标：以 A398383 段明定的u、B，∀n≥1,n²∣[q^n]B(1−u)/(1+u)²，系数允许负数；并辨明 n=2ʳm、m正奇数时v₂(c(n))≥5r的加强命题。文献裁决：本条与全部直引完整读，打开 Shvets https://arxiv.org/html/2607.19427v1 Theorem1.1、Theorem5.3的 F_{−4,2}=32C6b、Corollaries6.2/7.2与§8证明，后者初项q−40q²+1108q³确认商的归一化；reader2另读2404.04085与Löbrich–Schwagenscheidt2010.06297背景。主席亲核§8及加强版，分母统一有界不能冒充本目标分母1，降级凭新全文证明。bind-only 疑似声明：`PowerSeries.coeff_mul` 只提供系数卷积；D5/Mathlib按本号、magnetic及模形式关键词未见此exact目标，low。数值方案实际截断q^64，使用有理函数展开系数(−1)^j(2j+1)，64项n²整除和5r估值全通过，18项DATA全等；便宜形态共用 A398383 的整数级数，保留符号。拟议逃逸：2³ʳ∣a(n)已被同文覆盖，不再提作新靶；停止条件已满足为明确证明。相同模形式包三条合为一个依赖组、零派席，不能分三席搬论文。 xref 预检全部直接 A 号（完整读；占位另注）：A096960、A398186、A398383。

### A398713

精确目标：∀r≥1,T(r−1,1)=2^r，其中T(u,v)=min{m>0:u(2m−σ(m))=v(τ(m)−2)}；原评注including r=0会落到未定义的T(−1,1)，明确剔除该域外实例。文献裁决：完整读全部直引，并打开 Alekseyev https://arxiv.org/pdf/2601.17832 §5.3第10页；该文把线性f-perfect化成固定τ的σ方程，给有界搜索，没给本全称最小性。A000079说明2幂是almost perfect，并未分类所有almost perfect；不能偷用这个未知分类。bind-only 疑似声明：`ArithmeticFunction.sigma_one_apply_prime_pow` 与 `sigma_zero_apply_prime_pow` 直接验证2幂是解，却不证最小；med，若只交存在性即bind-only。数值方案实际共享σ/τ整除筛到2^18，r=1..18逐m取第一次命中，18个最小值全为2^r；对每一r的更小正m已在窗口内全部排除。便宜形态为一张筛表复用所有r，指数上界外再用论文因子树法，不能误说本轮重做其10^23计算。拟议逃逸：对亏数尝试证明(τ(m)−2)/(2m−σ(m))<log₂m或等号边界，给最小性所需上界；尚无该上界的证据，故虽是短算术候选形态仍note-only。停止条件：任一m<2^r的等式解即反驳；只有2幂代入或前18例不算完成；找到文献统一不等式则降级。同族合派：一个最小性目标，不拆成18席，也不和完全数无穷性合并。 xref 预检全部直接 A 号（完整读；占位另注）：A000005、A000040、A000079、A000203、A000396、A066229。

### A398300

精确目标：∀n≥1,min_{S⊂ℤ²,|S|=n} Σ_{x∉S}#{s∈S:‖x−s‖∞=1}=2⌈√(28n−12)⌉。文献裁决：完整读本条及A027709，打开 Vince，Electronic Journal of Combinatorics31(2)(2024)P2.5，https://doi.org/10.37236/12133 ，正式PDF Theorem18 pp15–17证明八邻域诱导子图最大边数M(n)=4n−⌈√(28n−12)⌉；主席亲读定理及证明段，reader3核对G₂定义。每个雷贡献8邻接、雷雷边扣两次，故8n−2M正是本目标；这是确切期刊证明降级，不是把Taliceo–Fleron写过猜想当证据。bind-only 疑似声明：`SimpleGraph.IsTree.card_edgeFinset` 仅树边数恒等式，D5/Mathlib按Minesweeper与king-grid未见此极值定理，low，但新形式化缺口不改变已证身份。数值方案实际整数isqrt计算公式1000项，69项DATA吻合；这是公式回归，没有独立枚举最优棋盘。便宜验法只需ceil-isqrt；若独立测小n则对有限包围盒位图计八邻域边，不能把四邻域周长A027709代入。拟议逃逸：本目标无；停止条件已触发为期刊定理覆盖。同族合派：一条、零席，不把8n−2M的改写另立新席；Vince其他图族开放问题须另采集裁决。 xref 预检全部直接 A 号（完整读；占位另注）：A027709。

### A398270

精确目标：∀n,k≥1,max{|S|:(P_n□P_k)[S]无环}=max{|S|:(P_n□P_k)[S]连通且无环}，等价fvs=nk−A360920(n,k)，只要求存在连通最优解。文献裁决：完整读本条和全部直引；A360920明写induced tree，A398270允许不连通，不能误判成补集定义恒等式。reader3打开 Alkauskas https://klevas.mif.vu.lt/~alkauskas/math/square-sequence-alkauskas.pdf 全9页（2022首稿、当前2026修订），其第3页定理及pp4–7处理方形fvs值，未覆盖所有矩形的连接性目标；MathWorld两页也未给全目标证明。bind-only 疑似声明：Mathlib `SimpleGraph.Connected.maximal_le_isAcyclic_iff_isTree` 和 `exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic` 按边包含扩成生成森林；本题必须保持诱导子图，不能随意加边，主席亲读签名后判不支配，med。数值方案实际对子集位图做并查集遇环即退，枚举1≤n≤k≤4的10种网格，最多16顶点；森林/连通树两最优值全等，10个对应DATA格点全等。便宜形态：更大矩形应逐列frontier DP，状态含边界连通分块与封闭分量数，分别优化森林和一棵树；不做2^(nk)的大板暴扫。拟议逃逸：证明极值森林可经保持顶点数的网格局部换点变为连通，或找最小反例；尚无无界换点不变量，note-only。停止条件：任一矩形forest_max>tree_max即反驳；只证补集恒等式或方形fvs公式不算完成。同族合派：与直引计数族共用图模型但命题不同，本轮一个候选、零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A354673、A360920、A398244、A398271。

### A398149

精确目标：a(1)=1；随后依逆时针方螺旋（先向右）选最小正整数，使当前所有非空行及列的和共同两两互异，证明∀v>0,∃n≥1,a(n)=v。初格行列同和1是明定初始化例外，允许数值重复，不是排列。文献裁决：完整读本条及四个直接螺旋变体，原条仍猜覆盖；其他条的邻接和、积、可见点和约束均不是本题，不提供覆盖证明。bind-only 疑似声明：Mathlib `Nat.find_min'` 可表达每步最小性，但不保证固定值最终被选；按本号与square-spiral检索D5未见具名覆盖定理（none限本次），low。数值方案实际带重数维护行和、列和的Counter；放格前只移除两条受影响的旧和，找新和都未占用的最小增量，二者也须不等。跑100000项，89项DATA全等，a(8)=7，最低未见67、最大值124；未重跑来源的1000万项。便宜形态为增量和表，无须每步重算整张棋盘。拟议逃逸：对固定v证明它不可能在每个未来螺旋位置永远被禁止；目前缺无界阻塞分析，note-only。停止条件：前缀不符先修语义；有限未见v不构成遗漏证明；找到全覆盖定理才降级。同族合派：四个直引只共用螺旋载体，不是等价题，本轮一条、零席。 xref 预检全部直接 A 号（完整读；占位另注）：A355270、A355271、A357991、A361724。

### A398024

精确目标：令c_k(n)计周长2n、只按平移等价的fixed k-convex多联骨牌；行列凸且任意两格间存在至多k次转弯的内部单调格路。固定k=3，∀n≥0,c_k(n)=[x^n]F_k(x)，其中 F_3(x)=x^2*(8*x^6 - 34*x^5 + 97*x^4 - 110*x^3 + 54*x^2 - 12*x + 1) / ((1-4*x)^2 * (1-2*x) * (2*x^2 - 4*x + 1)) - (1-3*x)^2 * x^4 / ((1-4*x)^(3/2) * (1-2*x) * (2*x^2 - 4*x + 1))，形式平方根取常数项1。文献裁决：完整读本条及全部直引；reader3打开 Conway–Guttmann https://arxiv.org/pdf/2606.13845v1 （EPTCS445，2026，pp74–86）§3.1及§4.2，正文和摘要仍称conjectured，条目后来却明确报告Prellberg已证明、正在审查；本轮搜索未取得该证明，故unknown、note-only。未取得的Prellberg证明页标ASSUMED-UNVERIFIED；不能因论文已发表就标published，也不能无视后来已证报告而派open席。bind-only 疑似声明：Mathlib `Polynomial.Chebyshev.T_add_two`、`U_add_two` 只给Chebyshev递推，`PowerSeries.coeff_mul` 只做代数系数运算；D5/Mathlib按polyomino和本组A号未见连到计数的具名声明（none限本次），low。数值方案实际逐条以精确代数级数展开给定F至x^24，n=0..24的25项DATA全吻合；这是公式回归，未独立枚举多联骨牌。便宜的独立核验应从小半周长B的行列区间形状枚举、路径方向DP做起，一次累积k=3..7；不把论文B=25报告的60CPU小时/800GB运行称便宜。拟议逃逸：先取得Prellberg证明并核对本k映射；正文通式Q₂的x²与本条特例和OEIS程序x⁴有排印差异，本目标明确取已列特例，不能静默替换。停止条件：取得覆盖本k的证明即published/drop，或独立计数差异先排除定义与排印问题；当前不派。相同k-convex生成函数家族五条合一组，若补来源只需一席，当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A005436、A128611、A398025、A398026、A398027、A398028。

### A398025

精确目标：令c_k(n)计周长2n、只按平移等价的fixed k-convex多联骨牌；行列凸且任意两格间存在至多k次转弯的内部单调格路。固定k=4，∀n≥0,c_k(n)=[x^n]F_k(x)，其中 F_4(x)=x^2*(-12*x^7 + 49*x^6 - 178*x^5 + 282*x^4 - 208*x^3 + 77*x^2 - 14*x + 1) / ((1-4*x)^2 * (x^2 - 3*x + 1) * (5*x^2 - 5*x + 1)) - x^4*(2*x^2 - 4*x + 1)^2 / ((1-4*x)^(3/2) * (x^2 - 3*x + 1) * (5*x^2 - 5*x + 1))，形式平方根取常数项1。文献裁决：完整读本条及全部直引；reader3打开 Conway–Guttmann https://arxiv.org/pdf/2606.13845v1 （EPTCS445，2026，pp74–86）§3.2及§4.2，正文和摘要仍称conjectured，条目后来却明确报告Prellberg已证明、正在审查；本轮搜索未取得该证明，故unknown、note-only。未取得的Prellberg证明页标ASSUMED-UNVERIFIED；不能因论文已发表就标published，也不能无视后来已证报告而派open席。bind-only 疑似声明：Mathlib `Polynomial.Chebyshev.T_add_two`、`U_add_two` 只给Chebyshev递推，`PowerSeries.coeff_mul` 只做代数系数运算；D5/Mathlib按polyomino和本组A号未见连到计数的具名声明（none限本次），low。数值方案实际逐条以精确代数级数展开给定F至x^24，n=0..24的25项DATA全吻合；这是公式回归，未独立枚举多联骨牌。便宜的独立核验应从小半周长B的行列区间形状枚举、路径方向DP做起，一次累积k=3..7；不把论文B=25报告的60CPU小时/800GB运行称便宜。拟议逃逸：先取得Prellberg证明并核对本k映射；正文通式Q₂的x²与本条特例和OEIS程序x⁴有排印差异，本目标明确取已列特例，不能静默替换。停止条件：取得覆盖本k的证明即published/drop，或独立计数差异先排除定义与排印问题；当前不派。相同k-convex生成函数家族五条合一组，若补来源只需一席，当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A005436、A128611、A398024、A398026、A398027、A398028。

### A398026

精确目标：令c_k(n)计周长2n、只按平移等价的fixed k-convex多联骨牌；行列凸且任意两格间存在至多k次转弯的内部单调格路。固定k=5，∀n≥0,c_k(n)=[x^n]F_k(x)，其中 F_5(x)=-x^2 * (8*x^7 - 38*x^6 + 136*x^5 - 248*x^4 + 198*x^3 - 76*x^2 + 14*x - 1) / ((1-x) * (1-3*x) * (1-4*x)^2 * (x^2 - 4*x + 1)) - (5*x^2-5*x+1)^2 * x^4 / ((1-4*x)^(3/2) * (1-x) * (1-2*x) * (1-3*x) * (x^2 - 4*x + 1))，形式平方根取常数项1。文献裁决：完整读本条及全部直引；reader3打开 Conway–Guttmann https://arxiv.org/pdf/2606.13845v1 （EPTCS445，2026，pp74–86）§3.3及§4.2，正文和摘要仍称conjectured，条目后来却明确报告Prellberg已证明、正在审查；本轮搜索未取得该证明，故unknown、note-only。未取得的Prellberg证明页标ASSUMED-UNVERIFIED；不能因论文已发表就标published，也不能无视后来已证报告而派open席。bind-only 疑似声明：Mathlib `Polynomial.Chebyshev.T_add_two`、`U_add_two` 只给Chebyshev递推，`PowerSeries.coeff_mul` 只做代数系数运算；D5/Mathlib按polyomino和本组A号未见连到计数的具名声明（none限本次），low。数值方案实际逐条以精确代数级数展开给定F至x^24，n=0..24的25项DATA全吻合；这是公式回归，未独立枚举多联骨牌。便宜的独立核验应从小半周长B的行列区间形状枚举、路径方向DP做起，一次累积k=3..7；不把论文B=25报告的60CPU小时/800GB运行称便宜。拟议逃逸：先取得Prellberg证明并核对本k映射；正文通式Q₂的x²与本条特例和OEIS程序x⁴有排印差异，本目标明确取已列特例，不能静默替换。停止条件：取得覆盖本k的证明即published/drop，或独立计数差异先排除定义与排印问题；当前不派。相同k-convex生成函数家族五条合一组，若补来源只需一席，当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A005436、A128611、A398024、A398025、A398027、A398028。

### A398027

精确目标：令c_k(n)计周长2n、只按平移等价的fixed k-convex多联骨牌；行列凸且任意两格间存在至多k次转弯的内部单调格路。固定k=6，∀n≥0,c_k(n)=[x^n]F_k(x)，其中 F_6(x)=-x^2*(20*x^9 - 127*x^8 + 524*x^7 - 1292*x^6 + 1712*x^5 - 1267*x^4 + 544*x^3 - 135*x^2 + 18*x - 1) / ((1-4*x)^2 * (x^3 - 6*x^2 + 5*x - 1) * (7*x^3 - 14*x^2 + 7*x - 1)) - (1-2*x)^2 * (x^2 - 4*x + 1)^2 * x^4 / ((1-4*x)^(3/2) * (x^3 - 6*x^2 + 5*x - 1) * (7*x^3 - 14*x^2 + 7*x - 1))，形式平方根取常数项1。文献裁决：完整读本条及全部直引；reader3打开 Conway–Guttmann https://arxiv.org/pdf/2606.13845v1 （EPTCS445，2026，pp74–86）§3.4及§4.2，正文和摘要仍称conjectured，条目后来却明确报告Prellberg已证明、正在审查；本轮搜索未取得该证明，故unknown、note-only。未取得的Prellberg证明页标ASSUMED-UNVERIFIED；不能因论文已发表就标published，也不能无视后来已证报告而派open席。bind-only 疑似声明：Mathlib `Polynomial.Chebyshev.T_add_two`、`U_add_two` 只给Chebyshev递推，`PowerSeries.coeff_mul` 只做代数系数运算；D5/Mathlib按polyomino和本组A号未见连到计数的具名声明（none限本次），low。数值方案实际逐条以精确代数级数展开给定F至x^24，n=0..24的25项DATA全吻合；这是公式回归，未独立枚举多联骨牌。便宜的独立核验应从小半周长B的行列区间形状枚举、路径方向DP做起，一次累积k=3..7；不把论文B=25报告的60CPU小时/800GB运行称便宜。拟议逃逸：先取得Prellberg证明并核对本k映射；正文通式Q₂的x²与本条特例和OEIS程序x⁴有排印差异，本目标明确取已列特例，不能静默替换。停止条件：取得覆盖本k的证明即published/drop，或独立计数差异先排除定义与排印问题；当前不派。相同k-convex生成函数家族五条合一组，若补来源只需一席，当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A005436、A128611、A398024、A398025、A398026、A398028。

### A398028

精确目标：令c_k(n)计周长2n、只按平移等价的fixed k-convex多联骨牌；行列凸且任意两格间存在至多k次转弯的内部单调格路。固定k=7，∀n≥0,c_k(n)=[x^n]F_k(x)，其中 F_7(x)=x^2*(24*x^10 - 198*x^9 + 867*x^8 - 2476*x^7 + 4072*x^6 - 3896*x^5 + 2251*x^4 - 798*x^3 + 170*x^2 - 20*x + 1) / ((1-2*x) * (1-4*x)^2 * (2*x^2 - 4*x + 1) * (2*x^4 - 16*x^3 + 20*x^2 - 8*x + 1)) - x^4*(7*x^3 - 14*x^2 + 7*x - 1)^2 / ((1-4*x)^(3/2) * (1-2*x) * (2*x^2 - 4*x + 1) * (2*x^4 - 16*x^3 + 20*x^2 - 8*x + 1))，形式平方根取常数项1。文献裁决：完整读本条及全部直引；reader3打开 Conway–Guttmann https://arxiv.org/pdf/2606.13845v1 （EPTCS445，2026，pp74–86）§3.5及§4.2，正文和摘要仍称conjectured，条目后来却明确报告Prellberg已证明、正在审查；本轮搜索未取得该证明，故unknown、note-only。未取得的Prellberg证明页标ASSUMED-UNVERIFIED；不能因论文已发表就标published，也不能无视后来已证报告而派open席。bind-only 疑似声明：Mathlib `Polynomial.Chebyshev.T_add_two`、`U_add_two` 只给Chebyshev递推，`PowerSeries.coeff_mul` 只做代数系数运算；D5/Mathlib按polyomino和本组A号未见连到计数的具名声明（none限本次），low。数值方案实际逐条以精确代数级数展开给定F至x^24，n=0..24的25项DATA全吻合；这是公式回归，未独立枚举多联骨牌。便宜的独立核验应从小半周长B的行列区间形状枚举、路径方向DP做起，一次累积k=3..7；不把论文B=25报告的60CPU小时/800GB运行称便宜。拟议逃逸：先取得Prellberg证明并核对本k映射；正文通式Q₂的x²与本条特例和OEIS程序x⁴有排印差异，本目标明确取已列特例，不能静默替换。停止条件：取得覆盖本k的证明即published/drop，或独立计数差异先排除定义与排印问题；当前不派。相同k-convex生成函数家族五条合一组，若补来源只需一席，当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A005436、A128611、A398024、A398025、A398026、A398027。

### A399456

精确目标：归一化宽为1，对任意定宽紧凸体K及局部有限、内部不相交的全等副本打包，圆盘面积占比的上极限≤D=2(π−√3)/(√15+√7−2√3)，并有已给Reuleaux构形达到D。文献裁决：完整读本条和全部直引；reader1下载 Resnikoff https://arxiv.org/pdf/1504.06733 ，摘要及pp32–33明确区分proves a certain packing density与conjecture maximum for any curve of constant width。故最大性仍open，不能因密度公式有证明就drop全目标。Wikipedia页面未打开，ASSUMED-UNVERIFIED。bind-only 疑似声明：Mathlib `Real.sq_sqrt` 只化简根式；D5/Mathlib按constant-width/Reuleaux/packing查未见此全类最优密度定理（none限本次），low。数值方案实际120位精度算D，90位DATA全部吻合；只验常数，未搜索任何凸体或打包。便宜的进一步探针是固定有限Fourier形状和格参数，解析算面积及支撑距离；它只测受限族，不能证全类最优。拟议逃逸：先找全类上界或精确超D反例；若改为格打包须另列受限目标，当前无短逃逸，note-only。停止条件：全类上界证明或严格反例；小数一致、一个最密候选构形不算完成。同族合派：独立一族、零当前席，常数的五个直引只是构成量。 xref 预检全部直接 A 号（完整读；占位另注）：A010465、A010469、A010472、A060708、A202473。

### A399385

精确目标：n≥0，阶2n+1的ASM（元素−1/0/1、每行列非零交替且总和1）满足转置对称且对角线上恰一个非零元，其个数=2^(n−1)(3n+2)!/(2n+1)!·∏_{i=1}^n(6i−2)!/(2n+2i+1)!；n=0按有理数2^(−1)解释。不是反对角线对称。文献裁决：完整读本条与两条直引；打开 Behrend–Fischer–Koutschan https://arxiv.org/pdf/2309.08446 ，主席亲核§8.7式(8.36)及由(8.23)、(8.21)、(8.22)、(8.26)给出的证明推导，正文明确此前Conj15已由Kumari Cor4.4证明。Kumari的EJC137(2026)104401出版元数据已核对，原期刊页 https://doi.org/10.1016/j.ejc.2026.104401 未全文打开，ASSUMED-UNVERIFIED；裁决承重为实际读到的BFK证明，而非元数据。bind-only 疑似声明：Mathlib `Nat.factorial_succ` 只给阶乘递推，D5/Mathlib按alternating-sign/OSASM未见目标计数声明（none限本次），low；已知文献证明仍须drop。数值方案实际精确有理阶乘乘积算n=0..13，14项DATA全等且分母均1；未独立枚举矩阵。便宜回归形态为相邻乘积比或有理约分，不能把公式展开当枚举证明。拟议逃逸：本公式无，不能随意借同文其他渐近猜想重派；停止条件是全目标公开证明已匹配。同族合派：ASM单例、零席。 xref 预检全部直接 A 号（完整读；占位另注）：A005156、A005163。

### A399381

精确目标：∀n≥1,∃k≥1,Squarefree(kn−1)，并∀M,∃n≥1,a₋(n)>M；自然数减法只在kn≥1使用，a₋(1)=2。文献裁决：完整读本条与直引，Robert Israel的2026-09-07评论已给Dirichlet存在性和CRT无界性证明：给j=1..M选互异且不除j的素数p_j，令jn≡1 modp_j²，所有前M候选都非平方自由。published在此指公开完整OEIS论证，不是期刊身份。所谓“many values”的移位相等不是全称猜想，原文自带a₋(26)=2<a₊(24)=3的反例。bind-only 疑似声明：Mathlib `Nat.chineseRemainderOfFinset`、`Nat.forall_exists_prime_gt_and_modEq`、`Nat.squarefree_iff_prime_squarefree` 是最近具名支撑；尚未找到本min目标exact声明，med，但文献证明已足够停止。数值方案实际共用平方因子筛，n=1..100000按k递增找到最小值（窗口内k≤7，搜索上限10没有未决），100项DATA全等；首现1..7的n为2、1、5、113、723、3553、62305。便宜形态一次标记p²倍数后O(1)查询，或直接用CRT构造无界见证，无需每个kn试除全部平方。拟议逃逸：当前存在/无界目标无；停止条件已触发，不能偷换为“每个值都出现”并称它也已由无界证明。同族合派：与A399382共用±平方自由族，当前本条零席。A399639预检取得完整JSON，但仅allocated for Aidan Markey、data为空；镜像404，数学条目不可读，ASSUMED-UNVERIFIED，不能声称已审读其数学内容，其余直引全读。 xref 预检全部直接 A 号（完整读；占位另注）：A005117、A007424、A008966、A399382、A399639。

### A399382

精确目标：∀K≥1,∃n≥1,a₊(n)=K，等价Kn+1平方自由且∀1≤j<K,jn+1非平方自由。文献裁决：完整读本条及直引，Greathouse的2026-08-28评论断言每个正值出现但没有给证明。A399381的Dirichlet存在性也覆盖+号；其CRT无界性不是满射性证明，不能将整条都说成未证，也不能把取值断言当已读证明。取值主目标证明身份unknown，绝非因“有人写过”而drop；移位many-values无精确量词且24/26有反例，不派。bind-only 疑似声明：`Nat.chineseRemainderOfFinset`、`Nat.forall_exists_prime_gt_and_modEq`（素数同余类定理）及平方自由判据最接近，med；不是看到mathlib有CRT就认定本满射目标已被一个声明支配。数值方案实际平方因子筛n≤100000，100项DATA全等；1..7首现n为1、3、24、49、6137、887、60923，未重跑来源到10^6的值8。便宜形态为与A399381共用筛，不逐数作昂贵分解。拟议逃逸候选：固定K，对j<K选互异素数p_j>K并CRT强制jn≡−1 modp_j²；检查Kn+1所处模K∏p_j²的剩余类互素后用Dirichlet令它为素数，从而强制最小值恰K。这是本轮提出、未编译的构造路线，尚未定位Greathouse断言的证明来源及是否被现成模式定理支配，故note-only。停止条件：取得该精确构造的公开证明即published/drop；若只剩CRT/Dirichlet绑定而无新数学义务则不派；无界或有限首现表不冒充满射。同族合派：±族如补来源共一组，本条不另派实施席。 xref 预检全部直接 A 号（完整读；占位另注）：A005117、A007424、A076986、A399381。

### A399369

精确目标：令R(n)把素因子指数按素数基数逐位进位（指数e_p≥p时将p的p份换成下一素数的一份，直到每位小于p），D(n)=n−R(n)=A376418(n)，δ(n)=Σ_{p^e∥n}e(n/p)。对1≤j<k且D(j)=D(k)>0，δ(j)=δ(k)⇒(k,j)=(28,16)。这保留原文such pair的正进位条件；若去掉>0，素数(3,2)就以D=0、δ=1反驳字面加强版。Conj1只比较A399370给的最大j，Conj2的正进位版本允许任何j，不可混同。文献裁决：完整读本条及所有直引，A379240明确说明Adamczewski arXiv2608.11941所述AI反例误读了A376418；reader1下载并读该PDF相关论述，不能将错误模型的反例记为本命题公开反驳。当前正进位目标未见证明，open。bind-only 疑似声明：Mathlib `Nat.factorization_mul` 是指数加法支撑，D5的primorial上界定理不处理此进位归一化；按本号及arithmetic-derivative/primorial检索无目标声明（none限本次），low。数值方案实际用最小素因子筛至100000、指数数组向下一素数进位，再按(D,δ)哈希存全部较小j；只发现(28,16)，两者(D,δ)=(7,32)。A399369得到4073项、前60项DATA全等，A376418与A003415前缀也全等。便宜形态是哈希碰撞，避免对每个k重扫所有j。拟议逃逸：按首次进位位数与导数变化给唯一性约束，尚无控制所有素数支持的短证据，note-only。停止条件：第二个正D碰撞即反驳；零纤维例子只反驳错误去域版本；有限无碰撞不立唯一性。同族合派：与A399370/A379240共用一族，原强弱目标最多共一探针、当前零席。 xref 预检全部直接 A 号（完整读；占位另注）：A003415、A100716、A376418、A379240、A399369、A399370。

### A399306

精确目标：∀n≥1，若A130310(n)末尾为1或1010，则 ¬IsSquare(max_{0≤j≤i≤n} C(i,j)C(n−j,n−i))，即A399306⊆A094350。最小Lucas表示按L0=2,L1=1且禁止同时选L0,L2的贪心规范；不能把“删末0无效”错作通常整数奇数。文献裁决：完整读所有直引，另取得并完整读A094291定义；Brown1969 https://www.fq.math.ca/Scanned/7-3/brown.pdf 与Chu–Luo–Miller https://arxiv.org/pdf/2004.08316 证明Lucas表示性质，没有本二项式最大值的子集结论；A399306仍明写merely a conjecture。A094291把最大位置缩到对角附近本身也标Conjecture，不能作为已证前置。bind-only 疑似声明：D5 `D5.S1.Scale.golden_lucas_succ_eq_fib_add_fib` 给Lucas/Fibonacci桥，Mathlib `Nat.choose` 是二项式定义；按A号和Lucas/maximum-binomial检索未见此包含定理，med，需跨表示与离散最优性，不能靠删位绑定。数值方案实际预制二项式三角，n=1..400对完整0≤j≤i≤n域取最大值，用isqrt判平方；153个Lucas-odd全满足，63项本条DATA及A094350的63项均吻合，A094291和A130310前缀也吻合；额外非平方含41、117、164、240、287、316、363。便宜形态为缓存C值+整数sqrt，未用原条尚猜想的对角早停程序。拟议逃逸：先证明最大值位置及其相邻比的精确阈值，再用Lucas尾部自动机刻画严格非平方；这道前置目前也未证，故note-only。停止条件：一个合法Lucas-odd的平方最大值即反驳；只复现表示唯一性、假定最大位置猜想或有限包含不算完成。同族合派：与A399307/308共用表示实现，但它是二项式优化问题，不与两条轨道全捕获命题合成同一成果；当前零席。 xref 预检全部直接 A 号（完整读；占位另注）：A000032、A054770、A094350、A130310、A342089、A399305。

### A399307

精确目标：以A130310的最小Lucas位串定义f，末尾1或1010时f(x)=2x，否则删去末0并按Lucas权重解码；∀x>0,5∤x⇒∃t≥0,f^[t](x)∈Orbit_f(23)∪{2,4,3,1}，其中23轨道恰132周期。文献裁决：完整读本条及全部直引，Brown1969与Chu–Luo–Miller2004.08316的表示定理不证此无界动力系统吸引域；有限周期表也不证每个x最终进入，open。bind-only 疑似声明：Mathlib `Function.IsPeriodicPt` 仅定义迭代固定点，D5 `golden_lucas_succ_eq_fib_add_fib` 只给权重桥；按本号及Lucas-Collatz未见全域捕获声明（none限本次），low。数值方案实际按位串生成完整132周期，最大19382，46项DATA全等；与A399308共用已知周期缓存，对起点1..10000迭代（每条未缓存路径最多10000步、值上限10^18），所有非5倍数均进入指定两周期，无未决或新周期。便宜形态是缓存已归类轨道后缀，避免重复迭代；上限命中只应记未决，本轮未命中。拟议逃逸：构造某次迭代严格下降的势函数或证明所有逆像覆盖，未有统一界，note-only。停止条件：新闭合周期可直接反驳，有限窗口不落入者需先区分长暂态，不能立刻称反例；有限全进入不立全称。同族合派：与A399308的5倍数域拼为同一映射的全正整数分类，若有势函数只合一席，当前零席。 xref 预检全部直接 A 号（完整读；占位另注）：A000032、A003124、A008884、A130310、A399305、A399306、A399308。

### A399308

精确目标：用A399307段所明定的最小Lucas删位/倍增f，∀x>0,5∣x⇒∃t≥0,f^[t](x)∈Orbit_f(70)∪{5,10}，70轨道长度122；模5域不允许省略。文献裁决：完整读全部直引，原条给122周期及5倍数不变性并提出全域猜想，未给捕获证明；已读Brown/Chu表示论文不能由表示唯一性推出轨道收敛。bind-only 疑似声明：`Function.IsPeriodicPt` 与D5 `golden_lucas_succ_eq_fib_add_fib` 不含最终到达量词；检索未见exact目标（none限此次），low。数值方案实际生成122周期，最大1863240，44项DATA全等；共同起点1..10000中的2000个正5倍数全部进入70或5周期；每条新路径10000步与10^18值上限，零未决、新周期或模类失败。便宜形态是与非5倍数域共用轨道哈希及已归类终点，有限周期的回到起点单独检查，不靠项表长度推断周期。拟议逃逸：将模5不变性加强成控制所有暂态的多步势函数，目前未有，note-only。停止条件：新的严格闭合周期或证明发散的轨道可反驳；只在预算内未进入不算反例，有限验证不能完成。两条全捕获猜想合一潜在席，A399306的二项式包含另计目标，当前零席。 xref 预检全部直接 A 号（完整读；占位另注）：A000032、A003124、A008884、A130310、A399305、A399306、A399307。

### A398189

精确派席目标：S(n,k)=Σ_{j=0}^{n−k}((n−k)!/j!)n^j，∀奇数n≥1,1≤k≤n，k奇⇒v₂(S)=0；k偶且k≢14(mod16)⇒v₂(S)=v₂(k+2)。原四分支中的k=0须优先辨明，n偶分支也保留为已证背景；不臆造14mod16例外类公式。文献裁决：完整读本条及全部直引，reader2完整读Amdeberhan–Callan–Moll https://math.colgate.edu/~integers/n21/n21.pdf ，Integers13(2013)A21；k=0已有证明，Lemma2.2的严格最小估值项在截断及缩放后还覆盖所有偶n分支。主席亲看第5页原图与Lemma2.2，未见其覆盖奇n正k的上述公式；不能按A063170已证将剩余目标错误降级。bind-only 疑似声明：`padicValNat_factorial`、`sub_one_mul_padicValNat_factorial` 可给阶乘估值，不含本奇n截断和的抵消控制；风险med，派席必须交剩余目标，不能只绑定Legendre。数值方案实际用H₀=1、H_m=n^m+mH_(m−1)反向生成每行，n=0..512，四个指定分支共127841格零反例，91项DATA全等，例外类不当反例。便宜逃逸另亲跑：剩余偶k的目标阶只为1/2/3，把H_m模16展开六步，连续六个整数乘积恒被16整除，旧历史消失；奇n的幂模16周期4。检查56个大m余数格及45个m≤5边界格，全部通过；奇k的m偶分支直接给奇性。这些只是未编译的结构探针，正式义务是证明六步截断、周期及全部n,k的提升，不能用有限表冒充全称。拟议逃逸即此模16压缩；停止条件：非例外精确反例、发现奇n正k已有证明，或实施只剩已证k=0/偶n分支。同族合派：与既有Schenker子族共用基础设施但剩余目标独立，一席；不把四分支拆四席。 xref 预检全部直接 A 号（完整读；占位另注）：A000120、A063170、A398187。

### A398690

精确目标：A(r,k)=(2k+1)^(−1)Σ_{j=0}^{2k}(−1)^(rj)sin((2j+1)π/(4k+2))^(2−r)，r_n(z)=(1−z)^(n+1)Σ_{k≥0}A(n+3,k)z^k；∀n≥0，r_n为次数n多项式且∀0≤j≤n,[z^j]r_n=[z^(n−j)]r_n。文献裁决：完整读本条和两条直引，A107735引用Mukai(2003)p483且对偶r作k→k/2，本条刻意取消该替换；不能直接把原Hilbert序列定理套来。Mukai书页本轮未取得，ASSUMED-UNVERIFIED，搜索页也未给可用证明；所读条目回文性仍Conjecture，open只限该检索范围。bind-only 疑似声明：Mathlib `Real.sin_add_int_mul_pi`、`Polynomial.Chebyshev.U_add_two` 只给三角/多项式局部恒等式，按Verlinde/palindromic检索没有本简化归一化的具名全目标（none限本次），med，泛Hilbert互反有支配风险。数值方案实际在有理圆分商环中求sin的逆元和幂，算n=0..7、k=0..9；八行全部回文，36项DATA全等，每行额外高次系数截至k=9均为0。便宜形态共用同一k的圆分多项式和逆元累积所有n，避免浮点近整数舍入；额外k用于检验插值外数据。拟议逃逸：证明A(n+3,k)对k→−1−k的延拓互反，再推出分子回文；尚未核清Mukai原书及通用Gorenstein/Hilbert桥，故note-only。停止条件：精确非对称系数对可反驳；通用定理确切覆盖该取消替换版本则drop；只测八行不派实施。同族合派：一条一个回文目标，行和等于A000831是另一个猜想，不另算派席。 xref 预检全部直接 A 号（完整读；占位另注）：A000831、A107735。

### A398603

精确目标：S₀={x²+y²:x,y≥0}、S₊={x²+y²:x,y>0}；E_S(n)=min{b:∃d>0,b−(n−1)d≥0且∀0≤j<n,b−jd∈S}，n=1按最小元素；∀n≥13,E₀(n)=E₊(n)。文献裁决：本条和全部直引完整读，reader3打开Green–Tao https://arxiv.org/pdf/math/0404188 §11第50页，仅由1mod4素数给任意长度存在性，不证最小末项一致；原条仍Conjecture。n=12时E₀=961、E₊=1445已分开，不能错降阈值；S₀∖S₊也不是所有平方，25有正平方表示。bind-only 疑似声明：Mathlib `Nat.eq_sq_add_sq_iff` 以3mod4素数的偶估值刻画S₀，`Nat.find_min'` 支撑最小元，D5/Mathlib按sum-of-two-squares/AP极值及本号未见此两最小值的最终恒等式（none限本次），low；存在性不支配最优性。数值方案实际筛两平方集合到B=3000，按末项b递增、d=1..b扫描并后退数最长连续n项，第一次命中记录全部步长；n=1..21两端点各21项DATA全等，13..21相等且12不同。便宜形态为两集合共用筛、一次(b,d)跑出所有可达长度，比逐n重新暴扫省；更大B可用位集和模类筛。拟议逃逸：限制最优S₀进程含S₀∖S₊元素的情形，或找严格端点差反例；目前无统一最优结构，note-only。停止条件：一个n≥13的经最小性核验的端点差；Green–Tao存在性、找到一条进程或前缀一致都不算全目标。同族合派：与A398604共享最优进程搜证只合一组，保留端点与步长两个断言，零当前席。 xref 预检全部直接 A 号（完整读；占位另注）：A000404、A001481、A093365、A093366、A398604。

### A398604

精确目标候选：用A398603段的E_S，在该最小末项处取最小正步长D_S(n)（n=1取0），∀n≥12,D₀(n)=D₊(n)。文献裁决：完整读全部直引；本条说corresponding steps但没明说并列时如何选，A093365程序按step递增首次命中支持最小步长规范，原条的步长等式标Conjecture；最小步长是此处显式规范，尚未证对所有n与原未规定并列语义一致，故精确目标桥标unknown，不能因已写评注就称published。bind-only 疑似声明：`Nat.eq_sq_add_sq_iff` 只刻画允许零平方的成员，`Nat.find_min'` 只给规范最小元，D5/Mathlib无本最优端点下步长等式的检索命中（none限本次），low。数值方案实际与A398603共用B=3000枚举，n=1..21每个最小末项下收集全部成功d，窗口内均唯一；两步长各21项DATA吻合，n=12..21都为84，虽n=12的端点不等。便宜形态为同一次扫描收集全部并列步长，不能只记录首个然后宣称唯一。拟议逃逸：先完成并列规范/唯一性桥，再找最优进程的统一模结构；未完成前note-only。停止条件：原语义未固定时的并列差异先停裁决；规范步长不等且最小性已核验可反驳规范版本；端点相等本身不证明步长相等。与A398603只合一个潜在搜证席、当前零席，不因两个A号而拆派。 xref 预检全部直接 A 号（完整读；占位另注）：A001481、A093365、A093366、A398603。

### A398542

精确目标：∀m≥1,∀b∈Av_m(132),∃p_b,q_b∈ℚ[X],∀k≥0,d(b,k)=p_b(k)C(2k,k)+q_b(k)4^k，deg p≤m−1、deg q≤m−2（m=1时q=0）；d计下格固定b、上格k点避免213且整体避免1324的竖向两格排列。ℚ系数为明确下游规范。文献裁决：完整读全部直引，reader2打开Bevan等 https://arxiv.org/pdf/1711.10325 Theorem3.1及§7.4，已证的是汇总domino数，不能支配固定b多项式次数界；§7.4仍说三格枚举需新思路。另读官方a398542.txt完整递推程序及2311.18227位置统计论文，未给本目标证明；原条仍猜想。bind-only 疑似声明：Mathlib `catalan_eq_centralBinom_div`、`PowerSeries.coeff_mul` 支撑一格/卷积，不含固定b分类；D5按1324/gridding未见exact目标（none限本次），med。数值方案实际独立枚举n=0..6的全排列与切线，7项L-gridding DATA全等；再对m=1..3的8个底格与k=0..6，枚举避免213的上格排列并交错，直接拒1324；用前2m−1点解有理系数，所有额外k点都满足次数界表达式。便宜形态是固定b后只枚举上格与交错位置；大参数使用来源强制下降递推，不能全排列跑到来源n=19。拟议逃逸：将强制下降状态统一化以控制生成函数极点和次数；只有小m拟合，暂无全b统一不变量，note-only。停止条件：精确额外点不符、已有统一证明，或只重证递减b的已给Catalan公式。与A398446共属1324族，建议先合一搜证席共享资料，但未证两全称目标等价，不能把一次成果记两次；当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A000108、A000139、A061552。

### A398446

精确主目标为条目评论的全d猜想：∀d≥1,∃p_d,q_d∈ℚ[X],∀n≥d+1，令M=n−1−d，T(n,n−d)=p_d(M)C(2M,M)+q_d(M)4^M，其中T按1-based最大元位置计1324-avoiders；deg p=d−1、首项1/d!；q₁=0，d≥2时deg q=d−2、首项C(d,2)/d!；p(0)−q(0)=1、p(0)+q(0)=|Av_d(1324)|。A398446本身只为d=2，不能把主目标缩成已给的d=2式。文献裁决：完整读全部直引；reader2读Norton的Joint1324.v与Avoid1324.v原文件，`max_at_n_minus_one_iff_prefix_132`只处理d=1，`max_at_second_last_central_binomial`另有限制n≤8，d=0结构桥也不是全d；2311.18227统计不同，未获精确映射。原条仅报d≤9验证，故全d目标open；外部Coq源码未编译。bind-only 疑似声明：Mathlib `catalan_eq_centralBinom_div` 对应已知末端低d情形，D5/Mathlib按1324与本号未见全d次数定理（none限本次），med。数值方案实际固定最大元在n−2的位置后只枚举(n−1)!排列，n=3..9计数2,6,23,92,373,1520,6206，与7项DATA及(nC(2n−6,n−3)+4^(n−3))/2全等；这只验d=2，不声称重验全d或来源d≤9拟合。便宜的后续形态为向1324-avoider的132-free前缀合法位置插最大元，合并按位置计数。拟议逃逸：全d统一前缀分解与次数控制，目前缺证，note-only。停止条件：全d反例/确切全d证明，或剩余工作仅d=0/1、已列d=2公式。与A398542共享一个优先搜证组但目标未证等价，当前零派席。 xref 预检全部直接 A 号（完整读；占位另注）：A000108、A000984、A061552、A391315、A395725。

## 复核与本地证据索引

最终分支只新增本Markdown。基线之后另在 `origin/dev` 的不可变读数 `f15ac1a9fbba26c28132990dd7d54cd8e1f64ad5`，对全部30个A号搜索D5、Library/Words、Problems，命中仍仅A399084的已知模块；这不是对无A号标识的所有声明作穷尽搜索。两条dispatch另查询GitHub公开代码 `A398581 language:Lean`、`A398189 language:Lean`，各返回total_count=0且incomplete_results=false；不外推为不存在无编号证明。Mathlib源实际取自主检出的 `.lake/packages/mathlib`，HEAD与上述钉版相同；按候选号、主题和邻近具名声明作只读比较，未运行Lean。

本机审计目录：`/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/oeis-triage3-0911/attempt-1`。主要工件为：`manifest.json`、`refs.json`、`excluded.json`、`selected.json`、`window.json`、`source-audit.json`、`url-inventory.json`、`bind-search-receipt.json`、`reader{1,2,3}/review.json`与原文缓存；数值脚本及结果为`numeric.py`/`numeric-results.json`、`egyptian.py`/`egyptian-results.json`、`lucas-check.py`/`lucas-results.json`、`carry-check.py`/`carry-results.json`、`small-combinatorics.py`/`small-combinatorics.json`、`ap-check.py`/`ap-results.json`、`cyclotomic-check.py`/`cyclotomic-results.json`、`poly-gf-check.py`/`poly-gf-results.json`、`gridding-check.py`/`gridding-results.json`，以及`density-results.json`和`valuation-shape-results.json`。它们是临时本地复核材料，未随单文件提交，公共定位以钉版镜像和逐段原文URL为准。

过程异常入账：初始采集器把A399456公式里的减号误当A号区间，多取A010466–A010468，已从refs/manifest和裁决移除；A399639的镜像404以真实allocated JSON登记。Python3.9缺少bit_count的中断已改用二进制计数并从完成记录续跑；A398581 b-file的urllib403改由curl取得完整正文，重新运行成功；批量写文脚本曾报编码/字符串解析错误，经显式Unicode读入修正后重跑，未声称失败时提交成功。reader1发生服务overloaded重连，最终三个CLI均turn.completed，无载体替换；同族阅读不是独立异模型评审。主席纠正了reader1把A399382存在性一并列open、把A399369零纤维纳入强版本、以及将OSASM误称反对角对称的建议；原始阅读记录保留，最终裁决以上文为准。

验证边界：完整条目散列、排除交集、30行/30段唯一性、全部直接引用、枚举字段、bibkey正则与数值结果已作机器核对，`git diff --check`通过；本轮仅文献变更，不运行Lean或全仓preflight，不声称内核/CI重验成功。未新建定理、冻结状态或外部议题。
