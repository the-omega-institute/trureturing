# Candidates screened out, with the reason

Verdicts on OEIS conjectures examined for the open-problem lane. Recorded so that neither I nor
another driver re-examines them. A kill here means the candidate fails one of the four checks in
`TARGET-GATES.md`; it does not assert that a conjecture is false.

Screened 2026-09-13 unless noted. Where a verdict came from a search seat rather than direct
inspection, the reasoning is reproduced so it can be checked rather than trusted.


早期分类表(已结算/名题伪装/有限残余/已有对象/形状排除/语料内重复/他人在做)与 R30–R46 已归档到 `SCREENED-OUT-1.md`(同判据,别重筛);本文件从 R47 起。

## R47(2026-09-18):Erdős 全库可有限判定的 41 条逐条列名与分诊

R35 量出「可有限判定的一档共 41 条」却只列了前五条,于是这一档的其余 36 条每次选题都要重取徽章。
本轮把 41 条的题号全部列出,并对每条给出它死在哪一关,以后这一档不再重新普查,也不再逐条重查。

### 语料边界

扫到 1400 号,`VERIFIABLE` 7 / `FALSIFIABLE` 25 / `DECIDABLE` 9 合计仍是 41,与 R35 的 1–1200 读数逐项相同;
1201–1400 之间只有 21 页是真条目(12 `OPEN`、4 `SOLVED`、3 `PROVED`、2 `DISPROVED`),其余 179 页返回空壳。
**该题库到 1221 号为止**,故 41 条即这一档的全部,不是某个窗口的样本。

| 徽章 | 题号 |
| --- | --- |
| `VERIFIABLE` | 7, 307, 364, 366, 647, 672, 835 |
| `FALSIFIABLE` | 23, 64, 97, 107, 114, 128, 167, 242, 287, 375, 398, 458, 488, 583, 617, 628, 699, 723, 743, 779, 982, 993, 1020, 1041, 1082 |
| `DECIDABLE` | 19, 475, 506, 547, 551, 556, 580, 742, 848 |

### 逐条死因(读数取自各题页正文与其 forum 页,2026-09-18)

已由 R34/R35 跑掉或判不可穷举的六条不重列:#287、#458、#647、#699、#779、#993(见下)。

| # | 死因 |
| --- | --- |
| 7 | 奇覆盖系统。更强的「奇且无平方因子」已由 Balister–Bollobás–Morris–Sahasrabudhe–Tiba 否定;搜索面是模的 lcm,无界。 |
| 19 | Erdős–Faber–Lovász。Kang–Kelly–Kühn–Methuku–Osthus 证得大 n,残余区间无显式截断,Hindman 已覆盖 n<10。 |
| 23 | 最好界 1.064n²(Balogh–Clemen–Lidicky)。反例需 5n 顶点的三角形无关图;n=3 即 1.4×10¹⁰ 张,再往上不可枚举。 |
| 64 | Liu–Montgomery 已证最小度大于绝对常数即成立,并因此否掉 Erdős–Gyárfás 的更强形式;残余是小最小度,无反例规模上界。 |
| 97, 982, 1082 | 几何构型,反例是实坐标,不是有限对象。#97 的三点版已被 Danzer 与 Fishburn–Reeds 否定,四点版无有限搜索面。 |
| 107 | Erdős–Szekeres「幸福结局」。 |
| 114 | 多项式 lemniscate 长度,连续量;n=2 已由 Eremenko–Hayman 证。 |
| 128 | 常数 1/50 已被 Razborov 推进到 27/1024;反例仍是任意大的三角形无关图。 |
| 167 | Tuza 猜想。Gupta(arXiv:2608.06538,2026-08-06)证到最大度 ≤ 7;无反例阶的上界。 |
| 242 | Erdős–Straus,已验到 n ≤ 10¹⁸。 |
| 364, 366 | 连续 powerful 数。#366 已验到 n < 10²²(OEIS A060355);abc 蕴涵只有有限多。 |
| 375 | Grimm 猜想。Laishram–Shorey 已验到 n ≤ 1.9×10¹⁰,且它蕴涵 p_{n+1}−p_n < p_n^{1/2−c}。 |
| 398 | Brocard–Ramanujan,已验到 10⁹;Naciri 2025 把 7-free 情形做完。 |
| 475 | 已证 t ≤ 12、p−3 ≤ t ≤ p−1,以及全部充分大素数(Kravitz;Bedert–Kravitz)。 |
| 488, 1041 | 题页已载完整 claim。 |
| 506 | Elliott 已解 n > 393(经 Purdy–Smith 更正);残余只有小 n。 |
| 547, 548 | Wood,*The Erdős–Sós Theorem*,arXiv:2609.17877(2026-09-15),其 Theorem 2 取 k=2 即给出 R(T,2) ≤ 2t−2。两条一并出局。 |
| 551 | Bondy–Erdős 证 k > n²−2,Nikiforov 证 k ≥ 4n+2,Keevash–Long–Skokan 证充分大 n。 |
| 556 | Kohayakawa–Simonovits–Skokan 证充分大奇 n,Benevides–Skokan 证充分大偶 n。 |
| 580 | Zhao 已证充分大 n;Zeraoulia 2026-07 预印本验到 19 阶。 |
| 583 | Gallai 路分解猜想,正在被系统攻击(Lovász、Chung、Pyber、Bonamy–Perrett 一长串部分结果)。 |
| 617 | 见下。 |
| 628 | Erdős–Lovász Tihany 猜想。 |
| 672 | Bennett–Bruin–Györy–Hajdu 证 4 ≤ k ≤ 11 及充分大 k 不可能。 |
| 723 | 射影平面阶,已证 n ≤ 11,n=12 的有限检查是天文数字。 |
| 742 | Murty–Simon,Füredi 已证充分大 n。 |
| 743 | 见下。 |
| 848 | Sawhney 已解充分大 N;van Doorn/Weisenberg 的上界 0.105N。 |
| 993 | 见下。 |
| 1020 | Erdős 匹配猜想。 |

### 三条看起来还没被算穿的,实际都已被算穿

题页正文不载计算前沿,forum 讨论页载,**故第一关必须读 forum 页而不止题页**。

- **#993**(树与森林的独立多项式单峰性):forum 页记有 tylersatchelorden 验完 32 顶点的全部 109,972,410,221 棵自由树、零反例,
  另有两人各自验到 29 顶点。Kadrawi–Levit(arXiv:2305.01784)在 26 顶点找到的是**非对数凹**的树,不是非单峰的。
  32 顶点以上不在本机预算内。
- **#743**(树装填猜想):Fishburn 证 n ≤ 9;forum 页另记 RajveerKapoor 验完 n=10 的全部 45,376,056 个序列、
  Guichard–Massman 验到 n=11、pawelkwaczynski 用 220 核时验完 n=12。
  Chalise–Clark–Gnang 的完整证明 arXiv:2410.13840 **已于 2026-09-01 撤稿**(Lemma 3.10 组合引理有误),故该题仍开放,但小 n 已无空隙。
- **#580**:同上,Zeraoulia 的 19 阶只是验证前沿,不是反例阶的上界。

### #307 的一条归约(把两个和的乘积化成一个映射的 2-循环)

设 `P, Q` 为有限素数集,`A = ∏P`,`B = ∏Q`。对每个 `p₀ ∈ P`,和式分子 `N_A = Σ_{p∈P} A/p` 的各项里只有 `A/p₀` 不被 `p₀` 整除,
故 `gcd(N_A, A) = 1`,即 `Σ_{p∈P} 1/p = N_A/A` 已是既约形;`B` 侧同理。于是 `N_A·N_B = A·B` 配上两个互素条件给出 `N_A ∣ B` 与 `N_B ∣ A`,
代回即 `N_A = B` 且 `N_B = A`。记 `f(n) = Σ_{p∣n} n/p`(对无平方因子的 `n`,它就是其素因子的第 `ω(n)−1` 个初等对称函数),则原问题等价于

  **存在无平方因子的 `A`,使 `f(A)` 无平方因子且 `f(f(A)) = A`** —— 即 `f` 在无平方因子整数上有一个 2-循环。

`A = B` 不可能(`P, Q` 必不交),故循环长度恰为 2。题页只记了「`P, Q` 不交、`Σ_{P∪Q} 1/p ≥ 2`、故 `|P∪Q| ≥ 60`」,未记此归约;
是否为已知未查证,记 `ASSUMED-UNVERIFIED`。它不结算该题,但把搜索面从「两个集合」压到「一个整数」,且与 `|P∪Q| ≥ 60` 相容:
`A` 需带三十余个素因子,故直接枚举仍不可行。

### #617 r=5:四条 claim 同向,已被他方认领(勘误)

Erdős–Gyárfás 证了 r=3(Chung–Liu 1978 已先证)与 r=4,并指出 r=2 为假;r=5 是第一个开放情形。
题面是「r ≥ 3 时,K_{r²+1} 的任意 r-染色都存在 r+1 个顶点,其导出 K_{r+1} 上缺至少一色」,
故一个 r=5 的反例(K₂₆ 的 5-染色使每 6 顶点五色齐现)将直接推翻整题,而 r=5 成立只是推进一个情形。

**本节原记「7 条互不相容的 claim,Conner Silverstein 称存在,公开状态未定」是错的,今按原文勘正。**
2026-09-18 读 `https://www.erdosproblems.com/forum/thread/617/proof-claims` 原文:四条 r=5 claim 方向一致,
全部主张 K₂₆ 不存在这样的染色——Nick Winter(2026-07-31,附形式化外链)、Anthony Rose(2026-07-25,
458 个 SAT 实例全 UNSAT,逐个 DRAT 证书)、Conner Silverstein(2026-07-21)、Rob Sneiderman(2026-07-18,
Kang–Pikhurko 界)。原记之误在于把 Silverstein 摘要开头的「Assume for contradiction that a five-coloring
… exists」读成了存在性主张,它是反证法的假设句。同页 Sneiderman 另有 r=6(K₃₇)、r=7(K₅₀)、r=8(K₆₅)、
r=9(K₈₂)四条 claim,均附 LRAT 证书。

**结论**:r=5 至 r=9 的有限情形在 2026 年 7 月已由多方认领,不满足「无人 claim」的选题前提,出局。
整题(∀r)仍开放,但其可有限判定的前几个情形已被扫过,剩下的是无界方向。

`tools/scripts/agent/openproblem/erdos617.py` 的编码与对照阶梯保留作为可复用工具:
每条边一个颜色的 exactly-one,加每个 6-子集 × 每色一条长 15 的子句(1625 变元 / 1,151,150 子句),
颜色置换对称性按首 r 条边破掉;自带对照为 `(r,n) = (2,5)`、`(3,9)`、`(5,25)` 必 SAT,
`(3,10)`、`(4,17)` 必 UNSAT。同型的「r-染色使每个 K_{r+1} 见全色」判定问题可直接复用它。

### 对选题函数的结论

Erdős 这条线的可结算面就是上表那 41 条,已全部列名。本轮跑掉两条(#458、#699),两条都无反例,
且两条都没有前人上界可比,故按 §3.6 ③ 都不作进展;#993 仍在预算内未跑。相较之下 OEIS 的 `%F`/`%C` 猜想线本会话产出 8 条已合入的结算。
**按每小时结算数排序,OEIS 线优先;Erdős 线按上表逐条推进,不再重新普查徽章。**

## R48–R50 与 C1(2026-09-18):arXiv 结尾栏三轮、首个 codex 本地去重搜题席,与「GPT Pro 席不能去重」的两次代价

会话内搜题轮编号(R47–R49)与本文件的节号错开一位;本节按内容记。

### 搜题轮「Kok」(ChatGPT Pro,arXiv math.CO 2025-07/08、math.GM/HO 2025-02..06 题级,期刊问题栏)

提出 Kok, arXiv:2507.16500, **Conjecture 2.12** 与 **Conjecture 2.9**。2.12 仓内已由 #7348 反驳(`JacoExponentialDominationRefutation`)——
席位无本地树,`D5/`、`Problems/` 去重未完成,orchestrator `git grep -il -P '\bjaco\b|2507\.16500'` 命中 5 个文件全是 2.12 lane。
2.9 开 lane:#8569 → PR #8588(v1,tests 席编译邻接矩阵变异证明私有定理非见证,关闭)→ PR #8614(v2,bind-only)。
同轮报 Kourovka 3.46/18.50/19.25/20.125/21.8/21.24/21.147/21.150 已被 arXiv:2607.17477 解决——不派席。
Crux 累积未解表当轮下载失败,未读。

### 搜题轮「abelian4」(ChatGPT Pro,math.CO 2025-09/10、cs.DM 2025-07/08、math.NT 2025-02/03、math.GM 2024 部分)

唯一候选 Fazekas–Mammoliti–Mercaş–Simpson, arXiv:2604.23188, **Conjecture 4**(`w = abab`,论文自己的 Table 1 印着反例行):
#8589 → PR #8603 MERGED `1bac71778f`。已结算、不派席:DeLeo–Henderschedt–Wells arXiv:2605.29166 的 lex-merge 最优性猜想已由
Ramos–Hulak–de Queiroz arXiv:2608.08431 对全部 `n` 证明(附 Isabelle/HOL 形式化);Niu arXiv:2605.04328(Fibonacci 立方 pebbling 数)已撤稿,
v2 评注指向 Mollard 2025 的先证。

### C1(codex-cli 搜题席,math.CO 2025-02..06 与 cs.DM 2025-01..06 全量清单,本地树去重)

首个用 codex 席做 arXiv 清单搜题的轮次:读 704 篇去重摘要、402 篇 PDF(结尾三分之一自动标记),**一轮出 3 个问题 / 4 条记录**,
全部经 orchestrator 亲验后开 lane:Misawa–Nishimura arXiv:2505.06893 Conjecture 3.3(`{2,4}`,#8616)、Chauve–Zhang arXiv:2505.13796 §6 结尾问句两部分
(`n=3,d=2` / `n=4,d=1`,#8618)、Göbel–Misra arXiv:2506.23936 Conjecture 5.3(`m=7`,#8621)。席位自报已在源文内结算的 6 篇
(2501.00784、2502.01161、2505.02045、2506.20296、2506.04407、2504.19031)与仓内已有卷宗的 2503.04122,均不派席。
**读数**:同日 GPT Pro 三轮各出 0–1 条,codex 一轮出 3 条;差别在能不能 `git grep`——GPT Pro 席的每条候选都要 orchestrator 再做一遍去重,
而 codex 席把去重命令与命中数写进候选记录。搜题以 codex 席为主,GPT Pro 席只做文献结算核对。

### 搜题轮 R49(ChatGPT Pro,chrono 池;math.CO 2025-11..2026-05、cs.DM 2025-09..2026-05、math.NT 2025-04..08、math.GM 2025、cs.FL/cs.GT 部分)

五条候选,两条开 lane、三条判掉:

- **开 lane**:Wenpeng Zhang, arXiv:2506.17235, §1 **Question (D)**(两个 Legendre 特征和之差的常数 `c` 只能是 0 或 2?)——`f = X²`, `g = (X+1)²`
  对每个奇素数差恒为 1(#8626);Bašić–Gottlieb–Krnc, arXiv:2606.16828, **Conjecture 2** 于印刷边界 `r = 1`(`G([1]) = 1` 而公式给 2,与同页
  Conjecture 4 的 `n = 1` 值一致;#8628)。
- **仓内已结算**:同文 **Conjecture 3** 的 `r = 7, k = 5`(`R^5_{7,6} = PS_6`,377 个位置)已由 `D5/S0/Certificates/Games/CrimGrundyRefutation` 反驳
  (`escape-witness` 依据,冻结)。席位无本地树,再一次把已落地的结果当候选。
- **已发表定理的即时实例**:Fried, arXiv:2607.07013, Conjecture 10.2(加权投票博弈由 swing table 在全部 simple games 中唯一确定)——
  swing table 经双重计数给出 Chow 参数(`Σ_S v(S)` 与各 `Σ_{S∋i} v(S)`),而 Chow(1961)定理正是「阈值函数由 Chow 参数在全部布尔函数中唯一确定」
  (arXiv:1206.0985 明写);按 R32 规则「某已发表定理的即时实例」判掉,不开 lane、不 cover。
- **不派**:Relia, arXiv:2402.19365v2, Conjecture 1(顶点覆盖算法的正确性)——席位的 9 顶点「假阴性」依赖对四个过程与匹配选取/平局规则的转写,
  论文摘要自述正确性未定;转写不确定的算法反驳不是有限判定,不派。
- 席位顺手核出的已结算:Zhang 同文 Question (A) 由 Nica arXiv:2507.09991 Example 5.3 直接证明(不触及 (D));Bouras arXiv:2509.09745 / A356247
  三条猜想 OEIS 记 Cloitre 2025 已证;arXiv:2312.16052 的 vincular 模式 Fibonacci-平方猜想已是其 2026-01 修订版的 Theorem 5。

### 方法学读数

- **GPT Pro 席不能去重,已两次把仓内已落地的结果当候选**(Kok 2.12、CRIM Conjecture 3)。它的候选一律先过 `git grep -il '<arXiv 号>|<对象名>' origin/dev -- D5 Blueprint Problems Library`,
  命中即读该模块的 `claim` 与卷宗;这一步不能交给席位。
- `chatgpt-pro-pool` 当日 `online_workers = 0`,两票排队 100 分钟 `Attempts: 0`;派前查 `nyxid oracle pool show <slug> --output json` 的 `online_workers`,
  `NYX_TIMEOUT` 两次即查任务状态,`queued + Attempts 0` 是死池不是慢。

## R52(2026-09-18):`DECIDABLE` 徽章不等于边界已知,与 size-4 Sidon-extension 的出局

**#475(Graham valid orderings)出局:有限残余没有可枚举的边界。** 页面 badge 是
`DECIDABLE / Resolved up to a finite check`,但已知结果由五段拼成,每段都带无效常数:
小 t 的 Costa–Della Fiore 2026 `t ≤ e^{c(log p)^{1/3}}`、中 t 的 Pham–Sauermann 2026
`1 ≪_α t ≤ p^{1-α}`、大 t 的 Bedert–Bucić–Kravitz–Montgomery–Müyesser 2025
`p^{1-c} ≤ t ≤ (1-o(1))p`、极大 t 的 Müyesser–Pokrovskiy 2025 `t ≥ (1-o(1))p`,
另有 `t ≤ 12` 与 `p-3 ≤ t ≤ p-1`。无一篇给出显式 p₀,故「剩下的有限检查」没有边界可跑完;
要兑现该 badge 得先把五个常数各自显式化。**判据:`DECIDABLE` 只断言原则上有限,不断言边界已知——
入管线前必须找到显式阈值,找不到即出局。** 验小素数或抽样都关不掉它(抽样本来也不是证明)。

**size-4 Sidon-extension 出局:专家社群在攻。** #707($1000)已由 Alexeev–Mixon 反驳并形式化;
残余的真开放问题是「size-4 的 Sidon 集是否总可扩成完美差集」——size 2 平凡、size 3 由 Sawin 证得总可扩、
size 5 有 {1,2,4,8,13} 与 Hall 1947 的 {1,3,9,10,13}。Müller 只证到 {0,1,3,11} 是候选反例
(所有*已知*构造够不着),缺口是排除非 Singer 型差集,挂在 prime power conjecture 上。
该方向有 PNAS 论文与专题报告,且他们自己在做自动形式化,按档位律出局。
arXiv:2604.25214(Niu,size-4 反例)已于 2026-05-14 撤稿,撤稿理由正是 Müller 的 MO 答复
早六个月证得更强,故该预印本及其后续不作为前置。

## R53(2026-09-19):徽章与 claim 页会互相矛盾,以及 #455 是目前唯一未被 claim 的活靶

**判据:题面徽章不是 claim 状态,claim 页才是。** 本轮把一份外部选靶意见逐条对站点原文复核,
出现系统性的不一致:#196、#1097、#197 的题面当天仍写着 `OPEN / cannot be resolved with a finite
computation`,而外部意见称它们已被反驳或已被 claim。去读 claim 页才判得出来——**#196 实测有
1 条 full proof claim,2026-09-14 由 Liam Kruer 与 Jensen Kohlmeyer 提交(GPT-6 Astra),
同时附证明与形式化两个外链,内容是构造一个无单调四项等差的 ℕ 排列**,故 #196 出局;题面徽章
当时尚未更新。反过来,外部意见对 #1097、#197 的断言本轮未能由站点证实,记
`ASSUMED-UNVERIFIED`,用前须自行读 claim 页。

**操作后果:claim 清查不能外包。** 该外部意见明确报告自己读不到 erdosproblems 的 claim 页、
且 arXiv 检索端点失败,并拒绝把检索失败写成「无人 claim」——这个自觉是对的,但也意味着
**清查只能由能取到页面的一侧做**:`curl https://www.erdosproblems.com/forum/thread/<n>/proof-claims`
可读,零 claim 时的字样是 `No proof claims have been submitted yet.`。派席前按此逐题实测。

**#455 是本轮唯一通过清查的活靶。** 题面:设素数 `q_1 < q_2 < ⋯` 满足 `q_{n+1} − q_n ≥ q_n − q_{n−1}`,
是否必有 `lim q_n / n² = ∞`?claim 页实测 `No proof claims have been submitted yet.`,
`Currently working on` 为空(两人标 Looks difficult)。已知结果只有 Richter [Ri76] 的
`liminf q_n/n² > 0.352⋯`。
**等价化简**(本仓推导,供后续用):令 `d_n = q_{n+1} − q_n`,由 `d` 单调不减得
`q_n ≥ (n/2)·d_{n/2}`,而 `d_m ≤ Cm` 无穷次出现即给出 `q_m ≤ q_1 + Cm²`;故原命题等价于
`d_n / n → ∞`。朴素机制只能走到 `d_n ≳ n / log n`:等间隔的一段就是素数等差数列,长度 `L` 的
一段要求公差被所有 `p ≤ L` 整除即 `d ≥ primorial(L)`,故 `d_n ≤ Cn` 时每段长 `≤ log(Cn) + O(1)`,
相异值数 `≥ n / log(Cn)`。这比 Richter 弱,**缺口正是「重复间隔段的整体稀疏性」**,不是逐段估计。
结论:唯一未被 claim 的候选,但属研究级,不按小时级管线派。

## 会话 6c2e9558(2026-09-18):期刊整卷深查五席——JIS 27–29、INTEGERS 24–26、ECA 2024–26 与 arXiv math.CO 2024

本节的席位编号是该会话内部的,与上文同名轮次无关。过关并已预登记的靶不在此列(见 #8627、#8634、#8639、#8643);
这里只记**判掉的、已结算的、算过未取的**,以及各窗口的真实覆盖面。

### 覆盖面(「打开并标记」不等于「看过」)

| 窗口 | 席 | 读数 |
| --- | --- | --- |
| Journal of Integer Sequences 27–29(2024–26) | subagent | 161 篇全开,109 篇有标记,102 篇的猜想上下文读全,11 篇做了定义级实算 |
| INTEGERS 24(2024) | codex | 122 篇全开,81 篇有标记,81/81 逐篇处置,32 篇做了定义级实算 |
| INTEGERS 25–26(2025–26) | subagent | 232 篇全开,141 篇有标记,55 篇上下文读全,17 篇(22 条陈述)实算;**51 篇只看了标记行**,未读全 |
| Enumerative Combinatorics and Applications 2024–26 | codex | 89 篇全开,46 篇有标记 |
| arXiv math.CO / cs.FL 2024-01 → 2025-01 | subagent | 五组关键词共 461 个题名、139 份 TeX 源;不匹配关键词的论文未看 |
| arXiv math.NT 2024-01 → 2024-06 | codex | 1682 条只做了机械筛,**零实算——不算覆盖**;2024-07 → 2025-03 无人看过 |

### 判掉:Brietzke, JIS 27 (2024) Art. 24.3.4, Conjecture 15(#8645,已关)

`Σ_j (d(n,4j) − d(n,4j+2)) = 2^n`(Catalan 三角 A039598)。它是 OEIS A039598 条目自身 `%C`(Wolfdieter Lang,2013-09-20)
所载一般恒等式 `x^{2n+1} = Σ_k d(n,k)·S_{2k+1}(x)` 在 `x = √2`(`N = 4`)处的特化:`S_{2k+1}(√2)/√2` 以 `1,0,−1,0` 为周期;
其发表基础是 Lang, Fibonacci Quarterly 38(5) (2000) 注 4。来源论文证了模 5 的类比、印出了给出一行证明的式 (24),却把模 4 的留作猜想。

### 已结算、不派席(席位读出;带 † 者由 orchestrator 复核过出处)

- Cohen, JIS 28 (2025) Art. 25.4.7:Conj. 65 同文自驳(`m=209, n=389`);Conj. 66 由 Ibarra arXiv:2607.09793 反驳;
  另 22 条由 Duc Hieu Le arXiv:2509.26138 结算(证 16、驳 6)。
- Greene–Higgins, JIS 28 Art. 25.7.8 Conj. 28:Hajós 群分解定理的特例(Szele 1949);Conj. 27 据称由其推出(未复核)。
- Fried, JIS 28 Art. 25.4.3(`F(n+2)+2nF(n+1)` 非 Fibonacci 数):Le arXiv:2509.26138 定理 23 / 命题 24。
- Kohen, JIS 29 Art. 26.4.2 Conj. 13:Offutt arXiv:2504.19031 §4.1 已反驳。
- Benmoussa, JIS 29 Art. 26.3.5 Conj. 2:符号印错;更正形即作者 arXiv:2511.09817v2 定理 4.1。
- Bosma–Bruin–Fokkink 等, JIS 28 Art. 25.3.8:Conj. 16(Shtrezi arXiv:2606.17447)、Conj. 17(本仓卷宗)。
- Arias de Reyna, INTEGERS 24 A19 Conj. 2:同文附录自给反例 `p=2, q=1094`。
- INTEGERS 24 A81 Conj. 2 的逆向子句:同文 Theorem 11 与 arXiv:2504.09617 已处理;A105 §5 的 rainbow 数等式:JMM 2026 摘要 58848 已宣布反驳。
- INTEGERS 25 A3(Murugan–Fathima)Conj. 1、A87(Flynn-Connolly)Conj. 1:各为同文定理的直接推论。
- INTEGERS 26:Chu 猜想(A58)、Komatsu 猜想(A63)、Erdős–Pomerance(A7, van Doorn)、Nath–Saikia–Sarma(A4)、
  OEIS A001006 的 Batalov 评论(A22 命题 3)、A97 的 Question 1 / Conj. 3(Balogh–Garcia–Liu–Yang)、A52 Conj. 5.1(文中称 [9] 已证)。
- Ballantine–Beck–Merca 的 `pre2` 单射猜想:Li, INTEGERS 26 A16 定理 1。
- ECA 2024 S2R9 Conj. 5.3(同文附录 B 反驳)、ECA 2026 S3R17 Conj. 10.2(同文标 False)、ECA 2026 S1R5 Question 1.2(同文 Thm 1.6)、
  ECA 2024 S1R4 Open Problem 6.1(Franks 等已解)。
- arXiv:2501.07463v2 的两条抛硬币猜想(Conway leading numbers / Li 1980 / Guibas–Odlyzko 1981 的推论);
  arXiv:2409.19547v4 的 pix/fix 等分布猜想(Dong–Xu arXiv:2606.00646 加有限核对);Archer–Geary 链避免计数(arXiv:2405.03268);
  Chen–Wen Conj. 1(arXiv:2412.18425)。

### 算过、不取(附理由)

- **只在边界值处失败**:Kohen INTEGERS 26 A22 Conj. 1(仅 `p ∣ a`);Zhao arXiv:2410.17057 Conj. 4.19 在 `n=2`;Bradshaw JIS 28 25.1.8 Conj. 18–19 在 `n=0`。
- **陈述不确定或读法歧义**:Gibbs–Miceli JIS 27 24.8.2 Conj. 25(`k=0,n` 处除零,「for some E」);Brietzke Conj. 14(依赖未印出的约定);
  Shunia arXiv:2407.03357 Conj. 1;Heubach–Dufour arXiv:2404.06608v3 Conj. 1(`S_2` 为印刷笔误级);Guday–Sahin INTEGERS 26 A5(`±` 号未定)。
- **成立于全部测试范围、无短证明路线**:arXiv:2401.16670 random Chomp;arXiv:2411.14488 Amalgamation Nim;metered parking(arXiv:2406.12941 / INTEGERS 25 A73);
  arXiv:2501.14640 impartial chess;Zhan–Bie INTEGERS 26 A15 Conj. 1–4;Gy INTEGERS 26 A108 Conj. 2.1、3.1;INTEGERS 25 A28、A102 Conj. 4、A23;
  INTEGERS 26 A92、A17、A55;Letouzey–Li–Steiner JIS 29 26.3.3;Merikoski–Haukkanen JIS 28 25.7.1 Conj. 5(「当」向可证,「仅当」向为一般非零性)。
- **实为名题或第三档**:Ross JIS 27 24.7.5 Conj. 17(蕴含不存在奇的非平方丰度 2/4/8/12 数);Zelinsky JIS 29 26.4.3 Conj. 1(Lehmer 型);Wagstaff JIS 28 25.7.2。
- **有明确小见证、但后续文献正文未取到,故未立**:INTEGERS 24 A94 Conj. 1(`‖n‖₂ ≤ (r+1)s + 2^r − 2`;`r=s=2, n=59` 处为 9 > 8;后续文献 Fibonacci Quarterly 64(3),
  DOI 10.1080/00150517.2025.2545251);INTEGERS 24 A116 §1 所引 Balandraud 猜想(arXiv:1702.06419 §4;`p=13, A={1,2,6,8,9}`)。
  INTEGERS 24 A60 Conj. 1(IDP 自反单纯形唯一性;`d=4` 处两个支撑向量)在检索范围内未见结算,期刊版已把 arXiv v2 的陈述收窄到非反链偏序。

### 方法学读数

- **对象有 OEIS 条目时,逐条读完 `%C` / `%F`,不要对已下载的条目做关键词检索。** Brietzke 的结算就在 orchestrator 已取回的条目里(19 条 `%C` 之一),
  用的是 Chebyshev 与正多边形对角线的语言;关键词 `2^n|4j|alternat|conjectur` 碰不到它。固定动作:对条目里每条一般恒等式问一句「它能否特化出待证陈述」。
  这次是探针的强制去重步骤接住的,代价一次探针。
- **搜题 brief 必须写明「作者自己印出、未证的猜想就是目标类」。**「具名」指有出处定位(论文 + 编号),不是挂着名家名字。同一窗口(INTEGERS 24),
  未写明时 codex 席零实算、0 候选并把该类整体排除;写明并要求逐篇处置表后,同一载体做了 32 篇实算、给出 5 条反例线索与 6 条证明梗概。差别在 brief,不在载体。
- **锚。** 每条实算先用同一份实现复现来源自己已证或已印的东西(另一条定理、一张表、一个演示图),再去算猜想;本会话全部候选与两次席位自纠的假反驳都靠它。
  pdftotext 会丢掉 vincular / consecutive 模式的下划线,两篇栈排序论文里不同的映射全印成同一个名字——以 TeX 源或渲染页为准。
- **载体分工(小样本)。** ChatGPT Pro 三次扫窗口共 0 候选(一次约 60 分钟只精读约 20 篇),但做需要浏览器的文献核对有用:能取到出版商与 ProQuest 的索引摘录,
  并分得清「打开核对」与「索引摘录」、「取不到」与「零结果」。要求其回复为 JSON 时须规定「值内不得出现双引号字符」,否则信封两次因未转义引号整体作废。

## C2(2026-09-19):codex 搜题席读最新三个月——2230 篇、332 份 PDF、1 条开 lane

窗口:arXiv `math.CO`/`cs.DM` 2026-06-01..09-18(降序,最新优先)与 `math.NT` 2025-09..2026-05;清单 1329+160+853 条,去重后摘要筛 2230 篇,PDF 读 332 篇,抽出 1179 条编号 Conjecture/Question/Problem。产出 1 条,记录在 `/tmp` 的 `screened.tsv`(过程材料不入仓)。

- **开 lane**:Dębski–Grytczuk–Naroski–Pawlik–Przybyło–Śleszyńska-Nowak, arXiv:2609.18476v1(2026-09-16),**Conjecture 2 (2)** `A2(i) = A1(i) + 1 for every i ⩾ 3`——论文自己的印刷行 `ϱ3 = (4, 3, 1, 5, 6, …)` 遗漏 2 而首项为 4,`i = 3` 即反例;正文写的观察是 `i ⩾ 4`,猜想印的是 `i ⩾ 3`(#8675)。orchestrator 按 Algorithm 1 亲算 15 行 × 4000 项,与 Table 1/2 逐项一致。
- **有限核查无反例、不派**:arXiv:2609.03081 Conjecture 3.9(`n = 9` 全部 362880 个排列);arXiv:2601.09510 Conjecture 1.1(中心二项式系数的 2-adic/3-adic 赋值,`257 ≤ n ≤ 10^7`);arXiv:2609.01562 Conjecture 7.4(`496 ≤ n ≤ 10^5`,最近点 `n = 497`);arXiv:2603.29973 Conjectures 2.2(i)/2.3(i)/2.4(i)(`n ≤ 100` 整数精确核查);arXiv:2609.06096 Conjecture 10.1(未判区间 `1001 ≤ d < 2^72`,pdftotext 把上标阈值渲染成 `272`,以 PDF 原文为准)。
- **源文内已反驳**:arXiv:2609.19372 Pachter–Sturmfels Conjecture 6.3——同文 Example 6.4 以七点图反驳 `k = 2`。

**读数**:与 C1 同形(704 篇/3 条)相比,最新三个月的 math.CO 出货率更低(2230 篇/1 条),但唯一命中的是提交两天内的论文——「新到没人看」这一档的候选来自最新月份,不来自更宽的窗口。

## R54(2026-09-19):全库 claim 状态的完整测量,与「可有限判定 ∩ 无人认领」恰为 14 条且全已死

用新器 `erdos-claim-scan.py` 逐题读 **claim 页**(不是题面),1–1221 全部取到,零条 UNKNOWN。
判据是三分:**有 claim** / **零 claim 但有人挂在 `Currently working on`** / **零 claim 且无人在做**。

| 类别 | 条数 |
| --- | --- |
| 有 proof claim | 184 |
| 零 claim,但有人在做 | 134 |
| 零 claim 且无人在做 | 903 |

对这 903 条再取题面徽章:已解者 524(PROVED 311 / DISPROVED 129 / SOLVED 84),
`OPEN`(题面明写「不能由有限计算解决」)356,`NO-BADGE` 9,
**可有限判定者恰 14 条**——#19、#107、#167、#364、#375、#398、#458、#551、#556、#583、#628、#672、#779、#1082
(FALSIFIABLE 9 / DECIDABLE 3 / VERIFIABLE 2)。这 14 条**全部在 R47 已逐条判死**,
死因同型:要么反例规模无上界,要么已被覆盖到「充分大」而残余没有显式阈值(同 R52 的
`DECIDABLE` 判据)。

**结论:以「有限反例」为路径的选靶面在本库范围内已空。** 不是筛得太严,是这一带已被扫过——
184 条有 claim 的里不少是 2026 年 7–9 月由 AI agent 提交的。剩下可走的只有「一般定理」一路,
落在那 356 条 `OPEN` 里。

**可复用的候选池**:在 903 条里取「题面 `OPEN` + 无悬赏 + 陈述里出现本仓底座对象
(Sidon / 超立方体 / powerful / 素数间隔 / 覆盖系统 / 距离 / 密度 / 表示函数 / lacunary)」,
得 **78 条**。这是当前唯一有机器可依的候选池,派席前仍须逐条核题面与文献。

**器的判据**:零 claim 的字样是 `No proof claims have been submitted yet.`;取不到的页记
`UNKNOWN` 而不是 0——未测过的页不能长得像无人认领的页。题面徽章不是 claim 状态(#196 在
2026-09-14 已有 full proof claim 而题面仍写 OPEN),所以只认 claim 页。

## R55(2026-09-19):#850 是候选池里唯一「徽章低估了它」的一条,器与对照阶梯已就位

R54 的 903 条无人认领集里再取「陈述短、无渐近记号、无悬赏」,得 88 条。其中绝大多数是名题
(平面染色数 #508、Erdős–Szekeres 一族等)。唯一形状对路的是 **#850(Erdős–Woods)**:

> 是否存在相异的 `x, y`,使 `x,y` 同素因子集、`x+1,y+1` 同、`x+2,y+2` 同?

**题面徽章写「不能由有限计算解决」,这句只对否定一侧成立**:若答案为否,确实无法有限验证;
但若答案为是,**一对显式的 `(x,y)` 就结算了它**,且那正是 §3.3 唯一放行的 `refutes` 形状
(处决「不存在这样的对」这条具名断言)。这是本轮唯一一条徽章低估了可达性的题。

**已知范围**(2026-09-19 读):Odlyzko 验到 `10^7`,McCranie 验到 `1.4×10^9`;文献另记
「`x < 100000` 时 `k=3` 已足够」。本仓读数:`k=3` 到 `2×10^5` 零对。

**器与对照阶梯**:`erdos850.py`。**关键判据是「同素因子集」不是「整除」**——
`75 = 3·5²` 与 `1215 = 3⁵·5` 支撑相同而互不整除。本器的第一版按 `y = x·m`(m 的素因子取自 x)
枚举,逻辑上漏掉正是这一对;对照阶梯当场抓出。改为按 radical 分组后,`k=2` 到 2000 的五对
`(2,8) (6,48) (14,224) (30,960) (75,1215)` 全部复现。**任何一次跑不出这五对的运行,
无论跑多远都不构成关于 `k=3` 的证据。**

**下一步与预算**:当前实现是 O(N) 内存的 Python,推不到 `1.4×10^9` 以上。要真正推进已知范围
需分段的 C 实现;该机器同时承载 base 的 CI runner,不得跑到干扰它的内存规模。未跑到超过
已知范围之前,不得称部分进展(§3.6 ③)。

## C3(2026-09-19):codex 搜题席读最新三个月的 NT/GR/RA/AC/FL/GT/CC/DS——1416 篇、5 条候选、3 条开 lane

窗口:arXiv `math.NT`、`math.GR`、`math.RA`、`math.AC`、`cs.FL`、`cs.GT`、`cs.CC`、`math.DS` 各 2026-06-01..09-18(降序);清单 1512 条去重 1416 篇,PDF 文本 1109 份(席位自报数学级筛读未穷尽,`pdf-queued` 1106 篇未逐条裁定)。

- **开 lane**:Mohan–Neetu, arXiv:2607.11194v1(2026-07-13),§6 **Conjectures 6.1/6.2/6.3**(任意 torsion-free 群的 small doubling `3k−3`/`3k−4` ⟹ ⟨S⟩ 交换)——Klein 瓶群 `Z ⋊ Z`(论文 §5 群律取 `q = −1`)中 `{e,(0,1),(1,1)}` 有 `|S²| = 6 = 3·3−3`、`e ∈ S` 而 `⟨S⟩` 非交换;论文自己的 Example 6.2(`k = 3`)拆成三个单点集反驳 6.2(#8686;orchestrator 按群律亲算三例)。Barket–Grimaldi–Hendi–Hirst–Onus–Singh, arXiv:2607.12026v1,**Conjecture 4.4**(幂零群 Cayley 图归一化 Laplacian 首个 `>1` 间隙指标 ∈ {|G|−1} ∪ {|G/Z_j|})——`Z/5`、`S = {1}` 的 `C₅` 谱 `[0,(5−√5)/4,(5−√5)/4,(5+√5)/4,(5+√5)/4]` 在 `k = 3`,允许值只有 4 与 1(#8688;orchestrator SymPy 精确复算 + 四个对照)。
- **正向证明候选、暂缓**:Hughes, arXiv:2608.27755v1 §10「Iteration-Depth No-Gap Conjecture」(插入迭代深度谱是初始区间)——席位给出固定次数合并 + 空块填充的证明草图,`{ε,a,b}` 子集全对 64 组到深度 4 通过;定义(k-插入、迭代深度)转写量大,排在反驳型 lane 之后。
- **已结算**:Das–Nath–Sarma, arXiv:2609.05302v1 Conjecture 5.1(`cφ₁₈(30n+19) ≡ cφ₁₈(30n+25) ≡ 0 (mod 16)`)已由 Saikia arXiv:2609.11813v1 Theorems 1.3–1.4 证明(同文 Conjecture 1.2 / 式 (7))。
- **载体读数**:`chrono-chatgpt-pro-pool` 当日一次 `model_unavailable`(15 次尝试),同 brief 改投 `company-chatgpt-pro` 即答;派 GPT Pro 席前 `nyxid oracle pool show` 看 `online_workers`,失败后换池不换载体。
