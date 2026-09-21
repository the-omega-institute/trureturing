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
