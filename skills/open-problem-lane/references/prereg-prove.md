<!-- open-problem-lane reference: Preregistration issue body — worked example A001108 (proof); posted BEFORE the probe. -->

## 档位与出处
**第一档，证明型（σ 奇偶刻画 + 两条丢番图不可能性 + 互素乘积为平方的分拆；非有限计算）**（2016 年 OEIS `%C` 猜想，至今仍标 Conjecture；本单在探针派出**之前**开出）。
- **OEIS A001108**（`%A` _N. J. A. Sloane_；`%N`: `a(n)-th triangular number is a square: a(n+1) = 6*a(n) - a(n-1) + 2, with a(0) = 0, a(1) = 1.`；数据 0, 1, 8, 49, 288, 1681, 9800, …；`https://oeis.org/search?q=id:A001108&fmt=text`，2026-09-15 逐字）。被证 `%C`（_Jaroslav Krizek_, Aug 05 2016，逐字，位于「The squares of NSW numbers (A008843) interleaved with twice squares from A084703 …」之后）：
  > Conjecture: Also numbers n such that sigma(n) = A000203(n) and sigma(n-th triangular number) = A074285(n) are both odd numbers. - _Jaroslav Krizek_, Aug 05 2016
- 读法：A001108 的成员按 `%N` 的名称即「三角数 T_n = n(n+1)/2 为完全平方的 n」（递推式是其已知的 Pell 型生成公式，非本单主张）；Krizek 断言：此集合 = {n : σ(n) 与 σ(T_n) 皆为奇数}。
- 本单目标：**证明该刻画（n ≥ 1）**——∀ n ≥ 1，T_n 是平方数 ⟺ (σ(n) 奇 ∧ σ(T_n) 奇)。**边界披露**：n = 0 是序列项（T_0 = 0 = 0²）但 Mathlib 约定 σ(0) = 0 为偶，故字面「皆奇」在 n = 0 失效；形式陈述限定 `0 < n`。**不触及**：递推式与 Pell 方程的完备性、NSW 数/A084703 交错结构、A001108 其它评注。

## 文献核对（第 3.6 条 ②）
- 搜题：**GPT Pro 池持续不可用**（12:13Z 起，第七次重试仍失败），本候选由 orchestrator 以 OEIS 全文检索（`Conjecture Krizek` 深页）本地扫得。
- orchestrator（2026-09-15）：读 A001108 当前正文——Krizek 2016 评注仍标 Conjecture、无证明/反驳注记。**仓内去重（`origin/dev = 7db666d708`）**：`A001108` 命中仅 `PellCompanionGcd`（A084068 = gcd(A001108, A001109)，不同陈述）；`A074285` 0；**已合入 `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.lean`（#…，A193351 lane）含私有引理 `square_or_twice_square_of_sigma_odd`（σ(n) 奇 ⟹ n 为平方或二倍平方）——私有、不可 import、非冻结公开前置**；本单须在模块内重证该经典事实（并证其逆），如实披露为同一经典引理的私有重证，**不将其计为逃逸见证**。`IsSquare (n*(n+1)/2)` 形 0；无同形定理。
- 独立复算（numpy σ 筛 + 平方检测）：n ≤ 2·10⁶ 零不符（T_n > 2·10⁶ 时 σ(T_n) 奇偶按经典刻画计算）；成员 ≤ 10⁶：1, 8, 49, 288, 1681, 9800, 57121, 332928，与 OEIS 数据一致。

## 拟议目标（proved）
```lean
open ArithmeticFunction in
theorem result : ∀ n : ℕ, 0 < n → (IsSquare (n * (n + 1) / 2) ↔ (Odd (σ 1 n) ∧ Odd (σ 1 (n * (n + 1) / 2))))
```
（公开面拟为唯一声明 `result`；`generality: I`；`utility: none`——符号分类证明，不命中 §3.3 四类计算性内容，同 A005590 #7742 / A008590 #7785 / A008578 #7819 证明型 lane。）

## 证明路线（探针重推导）
1. **σ 奇偶刻画（私有，经典；正向与 Lagneau 模块私有引理同形，如实披露）**：m ≥ 1 时 σ(m) 奇 ⟺ m 为平方或二倍平方。由乘法性 σ(m) = ∏ σ(p^e)，σ(p^e) = 1 + p + ⋯ + p^e 为奇 ⟺ p = 2 或 e 偶；故 σ(m) 奇 ⟺ 所有奇素因子指数皆偶 ⟺ m = 2^a·s²（a 任意）⟺ m 为平方（a 偶）或二倍平方（a 奇）。
2. (⇒) T_n = b²：σ(T_n) 奇（由 1）。又 gcd(n, n+1) = 1 且 n(n+1) = 2b²：**【非归约核心 A】** 互素两数之积为二倍平方 ⟹ {n, n+1} = {c², 2d²}（按 2 落在哪一方），故 n 为平方或二倍平方 ⟹ σ(n) 奇（由 1）。
3. (⇐) σ(n) 奇 ⟹ n = c² 或 n = 2d²；σ(T_n) 奇 ⟹ T_n = e² 或 T_n = 2f²。**【非归约核心 B】** 排除 T_n = 2f²：n(n+1) = 4f²；若 n = c²：c² | 4f² ⟹ c | 2f，记 2f = c·g，得 c² + 1 = g²——相邻平方数矛盾（c ≥ 1）；若 n = 2d²：2d²(2d²+1) = 4f² ⟹ d²(2d²+1) = 2f²，由 gcd(d², 2d²+1) = 1 得 d | f，记 f = d·g，得 2d² + 1 = 2g²——奇偶矛盾。故 T_n = e² 为平方。
4. 合成 iff。Mathlib：`ArithmeticFunction.sigma`、`isMultiplicative_sigma`、`sigma_one_apply_prime_pow`、`Nat.factorization`、`Nat.Coprime.isSquare_mul`/`Nat.coprime_mul_iff` 类引理、`Nat.sq_sub_sq'`/相邻平方（探针核实真名）。

## 预登记的逃逸见证（第 3.2 条；探针前写下）
`result` 为 content（**形态 (1)**）：活路径上的私有 content 引理——核心 A（互素积为二倍平方的分拆）与核心 B（两条丢番图不可能性 c² + 1 = g²、2d² + 1 = 2g² 的排除）；σ 奇偶刻画（引理 1）是经典事实的私有重证（其正向在仓内 Lagneau 模块已有私有同形），**不计为逃逸见证**，但其逆向（平方/二倍平方 ⟹ σ 奇）在仓内尚无。`admission_basis: escape-witness`；直接冻结依赖：无（Lagneau 的引理是私有、不可引用；本单不 import 任何 D5 模块）。探针若观测见证/路线不同将追加重新预登记。

## 用途依据（第 3.3 条）
`utility: none`（`result` 为符号分类证明）。`generality: I`。**非反驳**：Scribe `OpenProblemResolutionClaim(…, ResolutionKind.Proved)`。

## 落点（无 atom）
`D5/S3/Arith/KrizekTriangularSquareSigmaParity.lean`（Arith = 素因子分解/整除/剩余结构；σ 奇偶与平方结构；同桶已有 Lagneau A193351 与 A129598 相关注；count fresh）；`make deposit-uncovered`；卷宗 `Problems/oeis-a001108-krizek-triangular-square-sigma-parity.md`（Proved；`doi: null` + `url: https://oeis.org/A001108`；披露 n = 0 边界与私有引理重证）+ 文献注 `Library/Arith/sloane2016a001108.md`（bibkey 依 `%A` 作者 Sloane、年取可定日期的猜想年 2016，`authors: N. J. A. Sloane; Jaroslav Krizek`；`LibraryNoteRef.Create("D5/L/Arith/sloane2016a001108")`）。模块名依猜想作者 Krizek。

## 产地（第 5.2 条）
- skill 上下文：`consensus-rnd:sshx`（会话 <session>，留痕 #7333）。
- 载体与分工：候选由 orchestrator 本地 OEIS 全文扫描得出（GPT Pro 搜题席不可用）；orchestrator 逐字取 %N/%C、独立复算、去重（含私有同形引理的披露）、拟证明路线；探针 codex-cli（本单开出后派，worktree `lane/math/op-a001108`）；实施席 codex-cli；评审席 codex-cli。
- 混合方式：本地扫描（orchestrator）→ **本预登记（探针前）** → 探针 → Stage B → 三席盲评 → 合入；判卷面单一模型族，无 GPT Pro 参与（如实披露）。
