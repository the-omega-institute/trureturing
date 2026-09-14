<!-- open-problem-lane reference: Preregistration issue body — worked example A000040 (refutation); posted BEFORE the probe. -->

## 档位与出处
**第一档，反驳型（有限证书：单个合数 n = 219781 = 271·811 同时通过 Fibonacci 测试与 Fermat 测试）**（2014 年 OEIS `%F` 猜想，至今仍标 Conjecture、无反驳注记；本单在探针派出**之前**开出）。
- **OEIS A000040**（`%A` _N. J. A. Sloane_；`%N`: `The prime numbers.`；`https://oeis.org/search?q=id:A000040&fmt=text`，2026-09-14 逐字）。被反驳 `%F`（_Gary Detlefs_, May 25 2014，逐字）：
  > Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014
- 同一作者三天后的变体（May 28 2014，逐字，**本单不作形式主张**，仅在卷宗披露同一见证亦使其失效）：`Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(3*n) mod 3*n = 8}.`
- 读法：素数序列 = {5} ∪ {n ≥ 1 : n ≠ 5 ∧ (F(n) ≡ 1 或 F(n) ≡ −1 (mod n)) ∧ 2^{n−1} ≡ 1 (mod n)}，即 **∀ n ≥ 1，n 为素数 ⟺ n = 5 ∨ (n ≠ 5 ∧ (F(n) mod n ∈ {1, n−1}) ∧ 2^{n−1} mod n = 1)**。
- 本单目标：**反驳该 iff**。见证 **n = 219781 = 271·811**（合数）：F(219781) mod 219781 = 1，2^{219780} mod 219781 = 1，故 219781 落入右侧集合，但不是素数。**字面边界另行披露**：n = 2 时 2^{1} mod 2 = 0 ≠ 1，故素数 2 不在右侧集合——字面陈述在 n = 2 亦失效（退化：Fermat 测试对 2 不适用）；本单**不以 n = 2 作见证**，以实质反例 219781 反驳，卷宗写明两处。**不触及** Detlefs 同块 Sep 10 2010 的 Wilson 型刻画（已由 2026-05 编辑注记标为真）、Fibonacci/Fermat 伪素数的一般理论。

## 文献核对（第 3.6 条 ②）
- 搜题：**GPT Pro 池当日不可用**（R25 任务挂起 >2 h、R25b 三池均基础设施失败），本候选由 orchestrator 以 OEIS 全文检索（`Conjecture Detlefs` 等）本地扫得，第 5.9 条「能力缺口，其余 lane 继续」。
- orchestrator（2026-09-14）：读 A000040 当前正文——May 25 / May 28 2014 两条 `%F` 仍标 Conjecture，无「false / counterexample」注记（同块 2010 年 Wilson 型刻画在 2026-05-21 由 Rayhan Ahmed 注记为真，可见该块近期有人审过而两条 2014 猜想未被处理）。OEIS 检索 `seq:219781,252601,399001` **无结果**（无序列恰列这些 Fibonacci–Fermat 双伪素数）；`219781` 命中 22 条，含 A094401（合数 n 整除 F(n−1) 与 F(n)−1）、A093372（合数 k 满足 F(k) ≡ Legendre(k,5) ≡ 1 (mod k)）、A212424（x²−x−1 的 Frobenius 伪素数）——**219781 作为 Fibonacci 型伪素数是已知的**（卷宗如实归属为先行技术），但其对 Detlefs 刻画的反驳未见记录。
- 独立复算（Python，快速倍增与 n 步直接迭代两法一致）：n ≤ 10^6 内通过两测的**合数**恰 7 个：219781 = 271·811、252601 = 41·61·101、399001 = 31·61·211、512461 = 31·61·271、722261 = 491·1471、741751 = 431·1721、852841 = 11·31·41·61；通不过测试的素数仅 2。七个合数亦全部满足 May 28 变体 2^{3n} mod 3n = 8。
- 仓内去重（`origin/dev = 24ac7ee1ad`）：`A000040` 命中仅 triage 词表中对其它序列的引用；`Detlefs` 仅 triage 注（A034807/A049652，不同对象）；`219781` 0；`Fibonacci pseudoprime|fibMod|fastFib` 0（D5 内 `Nat.fib` 使用均为黄金塔/编码模块，无伪素数刻画）。无同形定理。

## 拟议目标（refuted，有限证书）
```lean
def fibTest (n : ℕ) : Prop := Nat.fib n % n = 1 ∨ Nat.fib n % n = n - 1
def fermatTest (n : ℕ) : Prop := 2 ^ (n - 1) % n = 1
def inDetlefsSet (n : ℕ) : Prop := n = 5 ∨ (n ≠ 5 ∧ fibTest n ∧ fermatTest n)
def claim : Prop := ∀ n : ℕ, 0 < n → (Nat.Prime n ↔ inDetlefsSet n)
theorem result : ¬ claim      -- n = 219781：inDetlefsSet 成立而 ¬ Nat.Prime 219781
```
（`result` 只需：`¬ Nat.Prime 219781`（271 ∣ 219781，norm_num）；`2 ^ 219780 % 219781 = 1`（内核 GMP 加速的 `Nat.pow`/`%`，`decide` 或 `Nat.ModEq` 计算）；`Nat.fib 219781 % 219781 = 1`——**不得**对 `Nat.fib 219781` 直接 `decide`（2·10^5 层递归），改走**模 m 快速倍增**：私有 `fibPairMod m n = (fib n % m, fib (n+1) % m)` 以二进制位数为燃料结构递归，用 Mathlib `Nat.fib_two_mul`、`Nat.fib_two_mul_add_one` 证正确性，再 `decide` 求 `fibPairMod 219781 219781` 的第一分量（约 18 步小数运算）；探针按 Mathlib 可及性定编码；禁 native_decide。）

## 数值（orchestrator 独立复算，不复用他人代码）
- 219781 = 271 · 811；F(219781) mod 219781 = 1（快速倍增 & 直接迭代一致）；2^{219780} mod 219781 = 1；2^{3·219781} mod 659343 = 8。
- n ≤ 10^6：通过两测的合数 7 个（上列），219781 最小；素数中仅 2 通不过（2^1 mod 2 = 0）。有界读数不承载证明。

## 预登记的逃逸见证（第 3.2 条；探针前写下）
`result` 为 content：**形态 (1)+(2)**——(1) 私有 content 引理 `fibPairMod` 正确性（模 m 快速倍增等于 `Nat.fib` 取模，由 `Nat.fib_two_mul` / `Nat.fib_two_mul_add_one` 经归纳建立，非单纯实例化）；(2) 公开结论由活路径上的有限证书直接产出：¬ Prime 219781、2^{219780} ≡ 1、F(219781) ≡ 1（经 (1) 计算），三者联合使 `claim 219781` 的 iff 为假。`admission_basis: escape-witness`；直接冻结依赖：无（仅 Mathlib）。探针若观测见证/路线不同（如直接 `decide` 可行、或需另一见证）将追加重新预登记。**成本提示**：`2 ^ 219780` 约 27 KB 整数，内核 GMP 计算应为秒级；探针测 decide 成本并记录。

## 用途依据（第 3.3 条）
`utility: kind=certified-instance; basis=refutes=gid:<GID>.claim; result=<GID>.result; claim=<GID>.claim`（typed refutation：单个有限见证 n = 219781，同 A049591 #7703 / A129598 #7766 判例；私有快速倍增引理是证书计算的基础设施，不改变反驳由有限计算承载的分类）。`generality: I`。Scribe `OpenProblemResolutionClaim(Refuted)`。

## 落点（无 atom）
`D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.lean`（Certificates = 内核可核验反驳证书桶；dev 48/96，另一在飞 lane A129598 将 +1，count fresh）；`make deposit-uncovered`；卷宗 `Problems/oeis-a000040-detlefs-fibonacci-fermat-prime-characterization-refutation.md`（Refuted；`doi: null` + `url: https://oeis.org/A000040`；披露 n = 2 边界、May 28 变体同样失效、219781 作为 Fibonacci 型伪素数的先行技术 A094401/A093372/A212424）+ 文献注 `Library/Arith/sloane2014a000040.md`（bibkey 依 `%A` 作者 Sloane、年取可定日期的猜想年 2014，`authors: N. J. A. Sloane; Gary Detlefs`；dev Library/Arith 51/96，另一在飞 lane 将 +1；`LibraryNoteRef.Create("D5/L/Arith/sloane2014a000040")`）。模块名依猜想作者 Detlefs。

## 产地（第 5.2 条）
- skill 上下文：`consensus-rnd:sshx`（会话 <session>，留痕 #7333）。
- 载体与分工：候选由 orchestrator 本地 OEIS 全文扫描得出（GPT Pro 搜题席当日不可用，见上）；orchestrator 逐字取 %N/%F、独立复算（两法）、读当前正文注记、OEIS 先行技术检索、去重；探针 codex-cli（本单开出后派，worktree `lane/math/op-a000040`）；实施席 codex-cli；评审席 codex-cli。
- 混合方式：本地扫描（orchestrator）→ **本预登记（探针前）** → 探针 → Stage B → 三席盲评 → 合入；判卷面无异模型共识；本候选**无 GPT Pro 参与**（如实披露）。
