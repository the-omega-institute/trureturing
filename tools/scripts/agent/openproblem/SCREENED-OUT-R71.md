# Screened-out targets, round 71 onward

This file continues `SCREENED-OUT-R52.md`, which reached the per-file line budget.

## R71 — 不等式类比猜想的三个形状,两死一活(2026-09-21)

以 Joel E. Cohen, *Conjectures about Primes and Cyclic Numbers*,
**J. Integer Seq. 28 (2025), Art. 25.4.7 = arXiv:2508.08335v1** 为样本,把「把经典素数不等式
搬到一个更稀疏或更稠密的序列上」这一整类猜想按**可反驳性**分了三形,结论可复用到别的论文。

选这篇的理由是它的自报验证范围已被证伪过一次:Cohen 第 1354 行写
「For m = 1, …, 10⁶ and n = m, …, 10⁶, I found no counterexamples to Conjecture 66」,
而 Ibarra(**arXiv:2607.09793v1**,Lean 4 内核验证)给出 `m = 31, n = 3928`,
`C_σ(3959) = 697 > 696`。反例落在自报范围极深处,说明那次搜索有编码错误。

### 形状一(死):`n` 次根单调,即 Firoozbakht 类比

`q_n^{1/n} > q_{n+1}^{1/(n+1)}` 等价于 `margin(n) = log q_n − δ·gap_n > 0`,`δ = n/q_n`。
密度 `δ(x) ≈ C/(log x)^k` 的序列,最大间隔按随机模型是 `(1/δ)·log n`,故 `δ·gap_max ≈ log n`;
又 `log q ≈ log n + k·log log q`,于是

    margin_min ≈ k·log log q − log C → ∞ 。

**余量随尺度增长,任何稀疏序列都不会在可达范围内失效。** 实测两族,最紧余量都取在小 `n`,
且把上界推大一到两个数量级后**逐位不变**:

| 序列 | 上界 | 最大间隔 | 阈值 `log q/δ` | 比值 | 大 `n` 最紧余量 |
|---|---|---|---|---|---|
| SG primes | `5×10^7` | 2730 | 3861 | 0.71 | 2.0258(`n`=1121) |
| SG primes | `10^9` | 4170 | 6263 | 0.67 | 2.0258(同一处) |
| SG cyclics | `10^9` | 84 | 157 | 0.53 | 7.7831(`n`=2,042,151) |
| SG cyclics | `10^10` | 96 | ~172 | 0.56 | 7.7831(同一处) |

据此淘汰:Cohen Conjecture 43;Zhi-Wei Sun **arXiv:1208.2683v9** 的 Remark 2.6 / 2.8 / 2.10
与 Conjecture 2.12 / 2.13 同形者。

### 形状二(死):滑动平均型,即 Dusart–Mandl 类比

`(a_1+⋯+a_n)/n < a_n/2`。Cohen 第 1295 行指出这个差**被证明渐近消失**
(Campbell–Cohen 的 `lim c_n/((c_1+⋯+c_n)/n) = 2`),所以它渐近紧、值得看。
但相对余量 `(n·a_n − 2·Σa_i)/(n·a_n)` 的实测衰减只有对数级:

| 上界 | cyclics(Conj 57) | SG cyclics(Conj 58) |
|---|---|---|
| `5×10^7` | 3.309e-03 | 8.231e-03 |
| `2×10^8` | 2.986e-03 | 7.365e-03 |
| `10^9` | 2.692e-03 | 6.685e-03 |

拟合约 `∝ 1/log x`,归零需 `log x → ∞`;且这是**滑动平均**上的相对量,局部涨落吃不掉它。

### 形状三(活):计数函数的次可加性

`A(m+n) ≤ A(m) + A(n)`。障碍是「远处某个长度 `m` 的窗口比初始段 `[1,m]` 装得更多」,
初始段的优势恰是**密度比** `density(m) / density(x)`:

- 素数:密度比是 `log x / log m`,优势巨大,首个反例在 `1.5e174`(Hensley–Richards),不可达。
- 近常密度的集合(cyclic numbers、SG cyclics、squarefree 等):密度比 ≈ 1,初始段几乎没有优势,
  **普通涨落就能翻**——Cohen Conjecture 66 的反例在 `n = 3959`。

**这是目前唯一值得投算力的形状。** 选靶判据:先算该集合的密度随 `x` 的变化,
若只随 `1/log log log x` 或更慢地变,就值得跑;若像 `1/log x` 或更快地掉,直接弃。

### 本轮复算的读数(全部 orchestrator 亲跑,本机 C)

对照先行,两条八位数逐位相符:**cyclics `≤10^8` = 28,488,167**、
**SG cyclics `≤5×10^7` = 6,882,632**(这同时解出「the first 6,882,632 SG cyclics」的歧义:
是 `< 5×10^7` 的那些,不是 `< 10^8` 的 13,620,495 个,因为判定 `σ` 要用到 `2σ+1`)。
第三条:`< 3.49×10^7` 的 cyclics 最大间隔 **24**,与论文第 1118 行一致。

| 条目 | 作者自报范围 | 复算到 | 违例 |
|---|---|---|---|
| 43 / 51 / 55 / 58 | 前 6,882,632 个 SG cyclics | 1,283,204,306 个(186×) | 0 |
| 57 | 未给 | 281,222,860 个 cyclic 指标 | 0 |
| 62 | 10^6 个后继序列 | 10^7(10×) | 0 |
| 63 | 10^6 个后继序列 | 10^6 | 0 |
| 64 | `2≤m≤910664, m≤n≤999997` | `2≤m≤n≤10^6` | 0 |

**Cohen 这篇无反例。** Duc Hieu Le 的 **arXiv:2509.26138**(自称结算 22 条)**已被作者撤回**,
撤回说明逐字:"Proofs in this paper were AI-generated and I just found out some of them were
incorrect.";其点名条号不含 43/55/57/58/62/63/64。

### 一条操作教训

推到 `10^10` 那轮,检测器报出 8917 万条「违例」,逐项读见证是
`*** C43 fails at n=556531575: 7 then 25` —— 索引 5.5 亿处的 `σ` 是 7。
真因是滑动窗口变量声明成 `uint32_t`,`σ` 越过 `2^32` 回绕。**见证的量级与索引量级对不上时,
先查类型宽度,别先查数学**;搜索上界过 `2^32` 就不许出现 `uint32_t` 中间量。
回绕前那一段(`σ < 2^32`)仍是有效读数,但这只有读了见证才知道。

## R72 — 反过来的判例:翻译成标准结构后,经典定理直接给出证明(2026-09-21)

同一天里,R71 那一整套「搜反例」形状(Cohen 七条、Bates 两条、Stirling 两条)**零命中**,
而一条真正被解决的猜想没有跑任何搜索。判例记在这里,因为它改变选靶顺序。

**靶**:Ronald Greene,**J. Integer Seq. 28 (2025), Art. 25.7.8**,Conjecture 28 逐字:

> "If `G` is an abelian group of order `2^n`, then every perfect cover for `G` contains an
> element of order 2."

作者自报:"all perfect covers for groups of order up to 128 contain elements of order 2.
It would be nice to see proofs for these conjectures."

**翻译一步**:perfect cover 的定义是「`G` 的每个元素**恰好**是 `S` 的一个子集之和」,即

    G = {0, s₁} + {0, s₂} + ⋯ + {0, sₙ}

是一个**因子分解**(唯一表示)。每个因子恰 **2 个元素(素数)**且**含单位元**;
`0 ∉ S`,否则 `T` 与 `T ∪ {0}` 同和。

**经典定理**:L. Rédei, *Die neue Theorie der endlichen Abelschen Gruppen und Verallgemeinerung
des Hauptsatzes von Hajós*, Acta Math. Acad. Sci. Hungar. **16** (1965), 329–373 ——
有限阿贝尔群若被分解成含单位元、基数为素数的子集之积,则至少一个因子是子群。
于是某个 `{0, sᵢ}` 对加法封闭,`sᵢ + sᵢ ∈ {0, sᵢ}`,排除 `sᵢ` 得 `2sᵢ = 0`。∎
亦可由 **Hajós(1941)** 的 cyclic subset 形式得到。

作者的参考文献表**不含 Hajós 或 Rédei**;他引的 Bajnok–Berson–Just(Involve 15 (2022);
arXiv:2211.13675)全文亦不含,且其 "perfect restricted `s`-basis" 允许**至多 `s` 个**元素求和,
与全子集和不是同一对象。检索面有限,不作全球优先权主张。

**自建对照**:先用已知计数校准实现(`C(Z_2)=1`、`C(Z_4)=2`、`C(Z_2⊕Z_2)=3`、`C(Z_8)=8`、
`C(Z_4⊕Z_2)=16`、`C((Z_2)^3)=28`、`C(Z_16)=64`、`C(Z_8⊕Z_2)=160`、`C(Z_4⊕Z_4)=240`、
`C(Z_4⊕Z_2⊕Z_2)=400`、`C((Z_2)^4)=840`,并与 `C(Z_{2^n}) = 2^{n(n−1)/2}` 及初等阿贝尔的
`(2^n−1)(2^n−2)⋯/n!` 相符),再枚举每个 perfect cover 的元素阶多重集:
**阶 ≤ 16 的全部阿贝尔 2-群、全部 perfect cover 都含 2 阶元**,与 Rédei 的结论一致。
`Z_{2^n}` 的阶多重集被唯一确定为 `2, 4, …, 2^n` 各一个。

**选靶顺序据此调整**:见到「作者自报验到某范围 + 希望有人给证明」的组合/存在性猜想,
①先把它改写成一个有名字的结构(因子分解、覆盖、匹配、tiling、群作用、码);
②查该结构的经典定理;③查不到再考虑搜索。**不要先写搜索器。**
搜反例只在启发式预言该命题为假时划算;作者自己愿意写成猜想的,通常是真的。

按第 3.1 条与第 3.6 条①,已有文献结论**不独立首次冻结**,故本条只留判据,不产生 Lean 节点;
结算记录在 issue #9255。

## R73 — 期刊开放问题列表这条矿脉的收益率与三道筛(2026-09-21)

把 *Journal of Integer Sequences* 卷 24–28 与 *INTEGERS* 卷 24 整卷拉下来逐篇筛,共 **595 篇**,
记录实测收益率与最终收敛下来的筛法,供后续换卷时直接复用。

### 三道筛,按精度递增

1. **结构关键词**:对 `(Conjecture|Problem|Question) \d+[.:]` 后 5 行匹配
   `factoriz|tiling|cover|packing|matching|basis|subgroup|abelian group|permutation|lattice|code|design|
   Latin square|hypergraph|colouring|clique|sumset|zero-sum|Sidon|difference set`。
   JIS 卷 24–28 的 351 篇出 6 篇、INTEGERS 卷 24 的 122 篇出 3 篇。
2. **自报验证范围**:同样的编号头,邻近 ±8 行出现
   `verified|checked|confirmed|computer search|numerical evidence|tested`。595 篇出 19 条,精度明显更高——
   本轮真正可动的两个靶都是它挑出来的。
3. **存在性/构造性措辞**(最准):邻近 6 行出现
   `does there exist|is there a|are there (infinitely many|any)|can we always|can one always|
   determine (if|whether)|construct a|must (there|every|any)`。595 篇出 57 条。

### 实测收益率

JIS 卷 24–28 约 350 篇只产出 **2 个**真正可动的靶(Tenner 等的 Problem 48、Greene 的 Conjecture 28),
两个都已结算。其余命中按下列形状淘汰:

- **研究纲领形**:Insko(JIS 26)Open Problem 36/37「能否推广到超图」「是否存在某种联系」——无可结算断言。
- **无界性型 / 带 ≈ 的渐近型**:Lamont(JIS 24)「persistence 无界」、Sheydvasser(JIS 24)
  `λ₂ ≈ 2.44344296778` —— 不是有限可判也不是可构造的断言。
- **第二/三档计算前沿**:Dalton–Trifonov,*Extreme Covering Systems*,
  **J. Integer Seq. 25 (2022), Art. 22.9.1** 的 Problem 1–5(distinct covering systems)。
  Problem 1/3 问最小模为 5 时最大模 ≥ 108、模的最小公倍数 ≥ 1440,作者自述只推到 84 且
  「the result is too weak and the proof too long, to be included in this paper」;
  Problem 4 等价于 squarefree 情形最小模问题的完整解;Problem 5 求 `c = lim c(n)`,
  已知 `4 ≤ c ≤ 616000`(Harrington 的三个不交覆盖系给下界,Balister 等的 616000 给上界),
  作者只有「基于若干假设的启发式」说 `c` 是 4 或 5。三条都不是小时级靶,记判据不开线。
- **最优下界型(真但要整篇论文)**:INTEGERS 24 (2024) #A81 重述 Bhanja 等的 Conjecture 1/2——
  `k ≥ 4` 个正整数的受限带符号和集满足 `|h^∧_± A| ≥ 2hk − h² + 1`,`3 ≤ h ≤ k − 1`,
  等号仅在 `A = d·{1,3,…,2k−1}`。`h = 3` 与 `h = 4` 已证,`h ≥ 5` 开放。
  **反例路线已被穷举否定**:先用论文自报的极值集校准实现(`3 ≤ h ≤ k − 1`、`k ≤ 8` 全部恰好取到界),
  再对第一个开放情形 `k = 6, h = 5` 穷举 `[1,16]` 的全部六元子集、以及 `k = 7` 的 `h = 5, 6` 穷举 `[1,13]`:
  **零违例,且取等号的集合恰好只有 `{1,3,…,2k−1}` 的倍数**。猜想是真的,要的是证明。

### 判据一:印刷式先对自家表格

INTEGERS 24 (2024) #A104(Buck–Elder–Figueroa–Harris–Harry–Simpson,*Flattened Stirling Permutations*)
的两条猜想,**印刷式都与同文的数据表矛盾**:

- **Conjecture 1**(`|flat₃(Q_n)|` 的闭式,作者自述 computationally verified for `1 ≤ n ≤ 12`):
  印刷式在 `n = 5` 给 **64**,而同文 Table 1 给 **70**;`n = 6…10` 给 324/1336/4920/16920/55700,
  表为 374/1596/6012/20994/69842。差值恰等于式中第二个二重和,把该项系数也取 2 后 `n = 4…10` 七值全合。
- **Conjecture 2**(`|flat(Q_n^m)|` 的 Dobinski 型闭式,验到 `n ≤ 7, m ≤ 5`):
  印刷式在 `m = 2, n = 1` 给 **2**,Table 2 给 **1**;整体差一位下标,指数改成 `n − 1` 后
  `m = 2…5`、`n = 1…7` 的 28 个值全合。

**所以派任何力气之前,先把猜想式代进作者自己的数据表。** 改正后的 Conjecture 2 等价于
`|flat(Q_n^m)| = D_{m,m−1}(n−1)`(r-Dowling 数,`r = m − 1`),对应 OEIS `A007405`(`m = 2`,EGF
`exp(x + (e^{2x}−1)/2)`)、`A355164`(`m = 3`)、`A355167`(`m = 4`);`m = 2` 是该文已证的 Theorem 2,
`m ≥ 3` 开放。独立枚举器(先按 Table 2 的 28 个值校准)把数据推到 `m = 2,3` 的 `n = 9` 与 `m = 4,5` 的 `n = 8`,
新值 239355 / 2465478 / 1120768 / 3790625 全部与 r-Dowling 数相符。该文 Theorem 4 走的是 type B 集合分拆,
把 2 直接换成 m 只得 `exp(x + (e^{mx}−1)/m)`,与数据要的 `exp((m−1)x + (e^{mx}−1)/m)` 不符,
故推广不平凡:正确对象是零块元素各带 `m − 1` 种颜色的 Dowling 结构,要证需另造双射。

### 判据二:交付面决定选靶,不只是数学难度

第 3.3 条禁普通正向有限实例准入,`certified-instance` 与 `bounded-enumeration` 只可走经验证的 `refutes`。
于是**「是否存在某一个对象」这类单见证存在性问题,即使搜到见证也进不了门**——
例如 Dimitrov(JIS 28)Question 7 问是否存在一对 `(m, n)` 使 `σ₂(m) = σ₂(n) = m² + n²`。
**可交付的只有两种形状**:对无穷多参数成立的 `∀…∃…`(交付为一般定理,用途报 `none`),或反驳。
本轮两个结算都落在这两种形状里:Tenner 等的 Problem 48 是前者,CLSW 的问题 12 是后者。
选靶时这一条要排在数学难度之前判。

## R72(2026-09-22):INTEGERS vol 23/24 余量封档 + OEIS 定向扫

### 池的封档读数

INTEGERS 线上 vol26 目录 110 篇与已抓 110 篇逐一对齐,**零新增**;JIS 26/27/28(200 篇)与
INTEGERS 23–26(454 篇)已全部扫完。**Fibonacci Quarterly 自 2025-01-01 起由 Taylor & Francis
出版,当前卷与前五卷全部付费墙**,不构成可用池。

### vol 23/24 余下 29 篇的逐条处置

- **y89** *Sparse admissible sets and a problem of Erdős and Graham* —— 这是 **Erdős 问题 #429**,
  该文自身用素根幂的贪心构造**证伪**了它(存在任意稀疏的无穷 admissible 集,其任何平移都不落进素数)。
  文献已结算,不是靶。**推论:任何把 #429 列为 open 的表都是陈旧的。**
- **y113** *Rearranging small sets for distinct partial sums* —— Graham 关于 `F_p` 中 valid ordering
  的猜想(Erdős 问题 #475)。该文的 Theorem 2(整数版)在文中**已证**,Sawin 2015 亦独立证过;
  `F_p` 版只推进到 `|A| ≤ log p / log log p`,余下是研究级。
- **y31** *Primitive Pythagorean triangles with sides of certain forms* —— Question 1–4 问是否有无穷多解。
  **逐字读(不带 primitive)Question 1 由齐次缩放平凡为真**:`(x,y,p,q,r,s) → (kx,…,ks)` 保持
  勾股关系与 `x≠y`、`p≠q`,而作者自己列出的解表里就含同一组的 1×/2×/3×。作者要的是 primitive 版,
  那是研究级。照字面形式化等于把问题改宽。
  **同型风险:凡「是否存在无穷多解」的问题,先试齐次缩放再判开放性。**
- **x5** *Odd deficient-perfect numbers with four distinct prime factors* —— Conjecture 1 是对每个
  `k ≥ 5` 的有限性断言,无有效界,无路线。
- **x30** *Some 2-adic conjectures concerning polyomino tilings of Aztec diamonds* —— Conjecture 1–4 是
  铺砌计数的周期性与 2-adic 赋值断言;`M(n)`、`L(n)` 这些计数对象 Mathlib 里没有,要从零造,
  且作者自述证不动 Conjecture 1。
- **x36** *Prime divisors of aⁿ − bⁿ* —— Conjecture 1、2 属 abc 族,按经典难题同族排除。
- 其余(`x12 x18 x35 x47 x48 x50 x56 x78 x96 xg5 xg6 y1 y6 y18 y19 y21 y22 y42 y71 y74 y93 y94 y97`)
  无「作者自报验到 N 但无公式/证明 + 对象全在 Mathlib」这一高产形状的陈述。

### OEIS 定向扫(查询形状可复用)

用 `conjecture "verified for n"`、`conjecture "checked up to"`、`conjectured "no proof is known"`
三条全文查询取到 225 个条目,第一关(比对 `Problems/ D5/ Library/` 与本目录三份筛除记录)刷掉 50 条,
余 175 条全新、其中 169 条带猜想正文。**该查询形状正对高产形状,可换词复用**:
`"holds for n <"`、`"tested up to"`、`"no counterexample"`。

本轮从中结算 **A134492**(见 `Problems/fibonacci-pythagorean-perimeter-refutation.md`)。其余已算/已排除:

- **A185895**(`∏(1−xᵏ/k!)` 的 EGF 系数:与前一项变号 ⟺ n 是三角数,作者验到 1225)——
  推到 **n = 1400 零违例、无零项**。递推在 EGF 系数上是纯整数的:乘 `(1−xᵏ/k!)` 即
  `a'_n = a_n − C(n,k)·a_{n−k}`。**不是可证伪靶**,形状稳。
- **A007406**(`gcd(n, numerator(H^{(2)}_{n−1})) = n if n 素数 else 1`,作者验到 1e5)——
  算到 4000 零违例,**但作者的范围更大,此计算零增量**。改记为**可证靶**:素数方向即 Wolstenholme
  定理(`p ≥ 5` 时 `p` 整除该分子),合数方向才是内容。评估前先 grep Mathlib 有无 Wolstenholme。
- **排除**:Zhi-Wei Sun 的一大批 `a(n) > 0` 表示型猜想(A187757、A199920、A209253、A209312、A209315、
  A209320、A210444、A218754、A218825、A219026、A219052、A219185、A219791、A219838、A219842、A219864、
  A219923、A220272、A220419、A220431、A220455、A220554、A227908、A227909、A230241 等)——它们自身蕴含
  孪生素数或 Goldbach;Peter Bala 的超同余(A219562、A227845、A193236、A193237、A111984);
  A078181(条目内已给出反例 `a(6800)=6801`);A186522(条目内已由 Bang 定理证出);
  A113191(Lucas 差为完全幂,Diophantine 级);A033493(3x+1)、A152763(Catalan 除数)、A103674。

### 判据三:先看作者验到哪,再决定算不算

A007406 那一轮的 4000 项计算相对作者自报的 1e5 是**零增量**。动手复算之前先读条目里的验证范围,
只有能真正超出它才有意义;超不出就直接按「已知范围内成立」记档,把算力留给别的靶。
配套:**读数快得反常时先核信号本身**——同一轮里 Fraction 累加报 0.0s,核过首项与已知值吻合、
分子有 3462 位之后才可信(第 8.4 条)。

## R74(2026-09-22):OEIS 条目的散文不是开放性判据,成员检查才是

本轮落地 **A272170**(见 `Problems/fibonacci-second-bit-run-length.md`)。它的兄弟条目
**A271591**(tribonacci 数的同一断言)差点被当作下一个靶,实际**已被证明**,而且用的正是同一套方法
(二进制窗口 + 比值界)。由此定出这道筛。

### 两个批量结算 OEIS 猜想的语料,都可机器查

| 来源 | 位置 | 规模 |
| --- | --- | --- |
| Adamczewski, arXiv:2608.11941 | `epoch-research/LeanOpenProblems` 的 `apn/data/oeis/Isolated/oeis_<num>_conjecture_<i>.lean` | 492 条陈述 |
| 同上,逐次求解结果 | `epoch-research/LeanOpenProblems-results` 的 `runs/<run>/<id>/metadata.json` | 25 个 run;该文件**存在即已结算**,内含 `settlement` 与完整证明 |
| Tsoukalas 等, arXiv:2605.22763(AlphaProof Nexus) | `google-deepmind/alphaproof-nexus-results` 的 `APNOutputs/OEIS/oeis_<num>_conjecture_0.lean` | 38 个文件,与 `apn/data/oeis/subsets/tsoukalas_proved_38.json` 逐条对应 |

结算并集用约 25 次 git-trees API 调用即可复算:逐 run 取递归树,数 `metadata.json`。本轮复算得
492 − 170 = **322 条未解**,与 R42 前言记的读数逐字相同。

### 这道筛不可省:已结算的条目未必被标注

抽 12 条已结算陈述查 OEIS 原文,**5 条页面上没有任何结算记录**,其中 A010846、A190363 是 19 次跑
全部解出的。A271591 被标了(2026-05-28,Ralf Stephan),是少数。所以:

> **判据:候选若属这 492 条,读条目散文不足以判定它开放;必须查语料成员与 `metadata.json` 是否存在。
> 候选若不属这 492 条,这两处的缺席才是有效的否定证据。**

A272170 在四处(492 条陈述、25 个 run、38 个 Lean 文件、arXiv:2608.11941 正文)全部缺席,而 A271591
四处全部命中——后者是「这套检查看得见结算」的对照,没有对照的缺席不算读数。

### 未解的 322 条仍然封档

本轮重新走到这个池口,被 R42/R43 的判词挡回:322 条已按形状逐条算过小情形,**零反例**,判掉理由是
选择效应而非难度。R44 又从其中剔掉 9 条已结算、9 条名题蕴含。**这是第四次走到同一个池口**,
故把入口条件写死在这里:凡候选来自 OEIS Open 未解池,直接出局,不再算小情形。反驳形的产地是
刚发表、还没人算过的猜想。

### 本轮其余登记

- **A123365**(立方剩余计数恰在 `p ≡ 1 (mod 6)` 处等于 `(k+2)/3`,作者验到 2000)——已推到 2×10⁶
  零违例,可证靶,路线是 CRT + 循环单位群 + `p = 2` + 立方像的非单位部分;代价读数为多小时级。
- **Eldar 的五条连续 Niven 猜想**——Pell 情形已扫到 10¹⁰,4 连一个没有(作者只到 2×10⁸),
  连号计数 6969285 / 375913 / 5024 / **0** 指向结构性障碍,机制是 `d(k+3) = d(k+2)`。

## R75(2026-09-22):arXiv 结尾栏这条矿脉的真实产量,以及「零命中要有对照组」

本轮从 arXiv **math.NT 2024-07→2025-03**(2522 篇,排序后 373 条候选)逐条取结尾栏,命中 24 条具名
Conjecture/Question,**只落地一条**:2407.20048v2 Conjecture 5.3(v) 的反驳(见
`Problems/pisano-order-range-refutation.md`)。其余逐条判掉,判词按类型分开记。

### 判掉一:渐近型或测度型,不是小时级 Lean 靶

2412.11319(「almost all pairs」)、2411.07779(`lim` 型下界)、2412.09124(无穷多解)、2410.09215、
2411.18782、2408.14365(`∃N` 型最终不等式)、2503.00787、2503.09909、2407.08203、2502.19523、
2503.01911、2503.15175、2502.18252。

### 判掉二:已被结算

- **2502.02974 Conjecture 4.10** —— 它是 Kantarcı Oğuz 循环 fence poset 单峰性猜想的复述,
  **已由 arXiv:2508.04396(2025-08)「loop fence poset 的秩多项式单峰」证明**。
- **2501.15170 Conjecture 5.1**(Erdős–Graham 覆盖系统)—— 正文自述「A proof of this conjecture has
  been claimed in [9]」。
- **2407.18186 Conjecture 5.1** —— 作者自报已验到 `n = 10000`,超出它才有增量。

### 判掉三:小情形成立,不是反驳靶

**2408.13346**(Ballantine–Beck–Merca,分拆的初等对称多项式)Conjecture 4 与 5。用二元生成函数
`Σ_λ q^{|λ|} Π_{parts i}(1+ix) = Π_{i≥1} 1/(1 − q^i(1+ix))` 精确算到 `n=259`、`j≤9`:
Conjecture 4 的 `j≥3` 子句与 Conjecture 5 的两条**零违例**。
**实现自证**:`j=1` 的违例恰止于 `n=23`、`j=2` 恰止于 `n=17`,与作者给出的两个阈值逐字吻合。

### 判掉四:逐字读是假的,但只因为漏写了一个显式例外

**2503.08517 Conjecture 8.1**(Baruah–Sarma)逐字:「For all integers `n≥0`,`A(5n)<0`,`B(5n)<0`,
`D(5n+1)>0`」。该文的 `R(q)=(q;q⁵)∞(q⁴;q⁵)∞/[(q²;q⁵)∞(q³;q⁵)∞]` **不带 `q^{1/5}` 前因子**,
故 `A(0)=B(0)=1>0`,`n=0` 处即假。但作者在同文已证的定理里**明写** 「except `C(0)=1`」与
「except `D(0)=1`」,只是在猜想里漏写这一句。**`n≥1` 时三条到 `n=399` 零违例。**
实现自证:作者已证的八条符号模式(`A(5n+1..4)`、`B(5n+1..4)`、`C(5n)`、`D(5n)`)同范围零违例。

> **判据:反驳一个显式例外的漏写没有数学内容,不计入结算。** 这类候选记档出局,不进管线。

### 判掉五:扫描不携带信息 —— 这不等于「猜想成立」

**2501.19272 Conjecture 7.2**(cylindric partitions):两个交错高斯二项式和的 q-系数非负性,
参数 `k≥5`、`k≥i≥1`、`n≥0`。扫 `k=5..10`、`i=1..k`、`n=0..25` 零命中。
**但对照组 `k=4`(猜想明确排除的情形)也零命中。** 对照没有区分力,就分不清「猜想在范围内成立」与
「我实现的不是那个对象」,故这次扫描**不作为读数**,该候选记为未验证而非已排除。

> **判据:判掉一个候选之前,先找一个应当失败的对照;对照不失败,零命中就不是读数。**

### 本轮的两条选靶信号

- **同一对作者的 Final-Remarks 分类猜想会反复在同一个 clause 上写错边界。** Benfield–Lippard 已有两例:
  arXiv:2404.08194 Conjecture 6.5(v)(反例 `a=47, m=15`,记于 `docs/develop/theory/PERIODIC_TREE.md`
  附录 TR.15)与 arXiv:2407.20048 Conjecture 5.3(v)(本轮落地)。**可复用,但产出是勘误级**,
  汇报时按勘误报,不按数学突破报。
- **arXiv 结尾栏对「反驳形」产量低**:373 条候选、24 条具名猜想,只出一条可反驳的,且那条是印刷错误。
  原因是论文通常**不报验证范围**,而反驳的性价比恰恰取决于「能否越过作者算过的边界」——OEIS 条目报范围,
  论文不报。结尾栏真正的价值在另一条线:**把陈述翻译成标准结构,再查该结构的经典定理**(R72 的判例)。

## R76(2026-09-24):最新 OEIS 猜想一扫 + 两轮 arXiv/OEIS 搜题,只落地一条

最新录入(`sort=created`)的含猜想 OEIS 条目 196 条,剔除计算报告与名题挂靠后 162 条,仓内零命中 123 条。
**落地一条**:A394431(Irvine,n>8 时最大数位和的最小底为 ⌈(n+1)/2⌉),PR #9625,`D5/S1/Digit/MaxDigitSumBase`。
其余逐条判掉,判词按类型分开记。

### 判掉一:条目内已结算(扫描器曾漏读)

- **A396111** 两条猜想:下一行 R. Israel 写「True because a(8*k-1) = k」「True because 2*n+1 divides 16*a(n)-1」。
  扫描器当时只认结算动词,把它报成 `no-marker`;已由 #9627 补 `true/holds/valid because/since`。

### 判掉二:仓内已有通用定理或已判为推论

- **A393858 模 7、A393859 模 8**:`D5/S1/Recurrence/Invariants/ScaledReversionCongruence.coeff_congruence` 对一切 `q ≥ 1` 给出
  `a q n % (q+1) = 1`,两条只是 `q = 6, 7` 的实例化。
- **A393858 奇偶**:同 A393856 奇偶,#7483 已记为冻结内容的推论(偶数 `k` 模 2 退化为 `B + B² = X`)。
- **A319927**:仓内已冻结 9216 反例(`IanakievOddNonunitaryPowerSumRefutation`)。

### 判掉三:文献已结算

- **arXiv:2503.22067 Conjectures 15、16**(Kitaev–Zhang,t-栈可排序计数):arXiv:2507.09187(Li–Kitaev–Lin–Liu)给出双射证明;
  原文 v3(2026-09-13)仍保留 Conjecture 标签,标签不是开放证据。
- **arXiv:2411.01530 Conjecture 11**(Knor–Škrekovski–Filipovski–Dimitrov,常数指数 σ-不规则度极值):
  作者在 Discrete Math. Letters 18 (2026) 1–7(DOI 10.47443/dml.2026.041)发表反驳。
- **A389100** 子序列猜想(von Brömssen 2025-09-26 证明)、**A357569 Conjecture 1**(arXiv:2608.11941 附录 A)。

### 判掉四:漏写显式例外或只剩有限残余

- **A394666**(`n! mod (2n−1) = 0 ⇔ n > 5 且 2n−1 非素数`):逐字只在 `n = 1` 处为假(`1 mod 1 = 0`),`n ≥ 2` 到 3000 零违例;
  反驳漏写的例外无数学内容,不结算。
- **A399793**(`n ≥ 13` 时取等):`n ≥ 564` 已由 Wang 证明,只剩有限残余。

### 暂缓:结论依赖未形式化的深定理

- **A397683**(`f(m) = 0 ⇔ m` 为 3 或 7 的幂):约化后缺口只剩 `f(3^a·7^b) > 0`,显式 CRT 构造 `x ≡ 4 (mod 9)`、
  `x ≡ 3 (mod 49)` 对一切 `a, b ≥ 1` 成立(验到 `a ≤ 6, b ≤ 3`)。但素数情形 `f(p) > 0`(`p ∉ {3,7}`)依赖 Cohen 1985 的相邻原根定理
  (Weil 型特征和),钉版 mathlib 无此工具;条件式结论无开放问题结算先例,故不立项。
  可用的初等覆盖只有两族:`p ≡ ±1 (mod 5)` 取 `x² + x − 1 = 0` 的根(`x + 1 = x⁻¹`),`4 ∣ ord_p(2)` 取 `x = −1/2`。

### 暂缓:只有数值证据,无短路线

- **arXiv:2609.13764 Conjecture 8.5**(Box(12) 分布单峰,Kitaev–Qiu–Xu):穷举到 `n = 9` 单峰;最大元插入引入从右至左极大元统计,递推不闭合。
- **arXiv:2609.07118 Conjecture 2.5**(Traetta,重排权重的近交替符号矩阵):5×5 全部 843 对可行权重多重集均有解;缺「可选出相邻非零图为二分图的支撑」这一步。
- **A024162**(`a(2k−1) ≥ a(2k)`,本原不等边三角形)验到 `k ≤ 500`;**A392200**(gcd 递推上界)验到 `n ≤ 2×10⁶`。

## R77(2026-09-24):Kourovka 未加星 ≠ 开放;arXiv 2026-09 新论文结尾栏

### 判据:Kourovka 的官网解答领先于 arXiv 版 PDF

arXiv:1401.0300v46(2026-09-01)仍未加星的问题,官网(kourovka-notebook.org)已另行收录 9 月的解答。只读最新 PDF
会把已解决的题当成开放题。**查 Kourovka 题时先查官网解答页,再看 PDF 的星号。**本轮对应读数(搜题席读原文所报):

- **21.99**(Müller,传递群中两点间总有固定点数 ≠ 1 的搬运元素?)—— Muliarchyk 反例,`|G| = 46875000000`,
  作用于 23437500 点;搜题席按其构造精确复算了全部 2000 个指定搬运元素,固定点数恒为 1。
- **21.68**(Kida,semiabelian ⇒ monomial?)—— Rizzoli(2026-09-11)阶 2592 反例,文末称已有 Lean 形式化。
- **21.137**(Wilson,p 次幂集成子群 ⇒ powerful?)—— v46 已加星,`p = 2` 反例为 `S₈` 的 Sylow 2-子群(阶 128)。
- **21.53**(Gorshkov,对合类上的保色置换)—— 官网收录一份非审稿的反驳说明(`²F₄(8)`),未独立审计,不按开放准入。

### 暂缓

- **Kourovka 21.89**(MacHale,`n > 39 ⇒ p(n) ∤ n!`)—— 精确算到 `n = 10000`,整除位置恰为
  `1,2,3,7,9,10,11,12,14,15,16,17,18,19,20,21,24,28,32,33,39`;无反例、无短路线。
- **arXiv:2609.25395 Conjecture 4.1/4.2**(Lim,weak Bruhat 连接的 inversion set)—— `A₂, B₃, D₄, B₄` 全部 2-闭子集零违例,
  未越过 Dermenjian 已报的 `B₄, D₅` 范围。

### 题型不合

- **arXiv:2609.26401**(Erdős 1981 调和圈长和)—— 充分大 `k` 已证,只剩有限残余。
- **arXiv:2609.25742 Conjecture 7.1**(Raney 数零串纪录值属有限多族)—— 族数与系数未限定,有限前缀无法反驳存在量词;Problem 7.2 要组合解释,非单一命题。

### 本会话三轮搜题的收益读数

nyxid 搜题三轮(OEIS 最新条目 / arXiv 结尾栏 / Kourovka + arXiv 2026-08~09)合格候选均为 **0**;
本会话唯一落地的 A394431 来自按 `sort=created` 自扫最新 OEIS 条目。三轮的价值全在剔除收据。

## R78(2026-09-26):MathDB 勘正——Mehiri–Nadji Conjecture 2

MathDB <https://mathdb.com/p/370389> 的问题引用 Mehiri–Nadji, arXiv:2509.12756，并陈述对每个 `k >= 0`，`alpha_{2,2k+1} = (k+1)(3k+2)2^{k-1}`。页面显示唯一一条答复，标为 Shivam Patel 的 Proof，发布于 2026-08-20T10:49:01.911889Z；进度文字称完整证明的主张已发布，但仍未核验。这条有日期且匹配命题的公开证明主张命中 prior-publication gate，目标不再进入本线；此处不判定证明正确性。
