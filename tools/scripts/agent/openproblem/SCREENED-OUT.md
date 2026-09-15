# Candidates screened out, with the reason

Verdicts on OEIS conjectures examined for the open-problem lane. Recorded so that neither I nor
another driver re-examines them. A kill here means the candidate fails one of the four checks in
`TARGET-GATES.md`; it does not assert that a conjecture is false.

Screened 2026-09-13 unless noted. Where a verdict came from a search seat rather than direct
inspection, the reasoning is reproduced so it can be checked rather than trusted.

## Already settled in the literature

| entry | what settles it |
| --- | --- |
| A048153 | Kutal, June 2026: closed form with class numbers of imaginary quadratic orders, giving the stronger bound `a(n) ≤ n(n−1)/2`. Also an August 2026 proof abstract. |
| A237271 | Hoft, January 2025, for conjecture 1; Kitamura, August 2026, Lean 4 proof for conjectures 4 and 5. |
| A211417 | OEIS records the conjecture as proved by an autonomous AI agent, with a Lean file, June 2026. |
| A117531 | Kutal, 22 August 2026. Note the boundary: the linked Lean development declares Stark–Heegner as a project axiom, so this is a literature settlement, not an axiom-free formalisation. |
| A180017 | Drmota and Spiegelhofer, arXiv:2501.00850, Theorem 1.2. The joint-value theorem gives every difference `s₃(n) − s₂(n) = z` infinitely often; the earlier zero-collision result alone would not. |
| A109074 | Kuperberg's proved enumeration of vertically symmetric alternating-sign matrices, Annals 156 (2002); the conjectured ratio is the consecutive ratio of that count. |
| A001157 | Fried, December 2025. |
| A000040 | Follows from Wilson's theorem. |

A mechanical sweep of 118 corpus entries against the OEIS text found 22 carrying settlement
markers. That sweep matches keywords, so it both misses and over-reports — `A130911`'s "true for
primes up to 10^19" is a verification range, `A306477` is an unclaimed prize, `A034693` reports
a stronger conjecture's verification. Treat 22 as a lower bound and read the entry before
promoting anything.

## Famous problems in disguise

The OEIS wording gives no sign of these. Each was identified by reducing the statement, not by
recognising a name.

| entry | what it actually is |
| --- | --- |
| A105020 | Exactly binary Goldbach. Reparameterising the block as `r(2n+2−r)`, both factors exceed 1, so a semiprime exists there exactly when `2n+2` is a sum of two primes. |
| A101779 | Implies infinitely many Sophie Germain primes: every witness has `k ≥ n`, so arbitrarily large `n` give arbitrarily large `k` with `2k+1` prime. |
| A119591 | Implies infinitely many Mersenne primes, by specialising to `n = 2^m`. |
| A017666 | Implies every odd perfect number is practical, which is impossible for an odd integer above 1. |
| A185150 | Stronger than Legendre: dropping the residue condition leaves "every interval `(n², (n+1)²)` contains a prime". |
| A115366 | Entails infinitely many prime values of the irreducible quadratic `k² + 3k + 1`. |
| A001359 | Wilson's theorem rewritten through the intervening product. |
| A005258 | Irreducibility of the Apéry polynomials; the entry carries Apéry, Brown and the Lucas-theorem survey. |
| A110835 | Sierpiński 1958. |
| A103151 | Self-describes as stronger than Goldbach. |

## Published, with only a finite residue left

| entry | coverage |
| --- | --- |
| A111291 | Zelinsky 2002, Theorem 14: `T(x) > cπ(x)` eventually for every fixed `c`. Only a finite range remains. |
| arXiv:1411.4092 Conj. 2.7, `n=3` | Girstmair's largest-values theorem covers all sufficiently large `b` coprime to 3; a finite range and `3 ∣ b` remain. |

## Reduced object already available

See `TARGET-GATES.md` for the method and the repository-side cases. Upstream case:
`A049473`'s Beatty clause is `Mathlib/NumberTheory/Rayleigh.lean`'s `compl_beattySeq`
instantiated at the Hölder-conjugate pair `√2, 2+√2`, and appears in no repository path.

## Shape excluded: unbounded iteration

| entry | why |
| --- | --- |
| A087207 | Orbit values explode — `a(101) = 2^25`, and near `n = 20000` the first step reaches a 681-digit number — so termination is Collatz-shaped, not a short proof. |
| A100800 | Same shape: iterate `n ↦ n + digitsum(n)` until a multiple of `n`. |
| A153330 | Adjacent Collatz total stopping times. |

## Duplicates within the corpus

`A109908` and `A109909` ask the same existence question. Note that the 2024 paper linked from
those entries, claiming a solution, was examined and its constrained-optimisation step found
defective; it is not treated as a settlement.

## Who else is working this corpus

Tom Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?",
arXiv:2608.11941, builds a benchmark of 492 open OEIS conjectures formalized in Lean from
google-deepmind/formal-conjectures and reports 147 resolved. Entries are now acquiring comments
that record such work. Expect a candidate drawn from that corpus to have been attempted.

## Screened 2026-09-15 (rounds R30 and R31)

Both rounds ran exact-integer checks and returned `abstain` with reasons rather than silence. The
eliminations below are recorded so that neither round's work is repeated.

### Already settled, with the settlement named

| entry | what settles it |
| --- | --- |
| A008676 | John W. Layman's 2009 floor conjecture is *identically equal* to Tani Akinari's 2013 formula in the same entry: for every `n >= 0` both equal `1 + floor(2n/5) - ceil(n/3)`. Checked against an independent coin-change dynamic program over `0 <= n <= 10^6`, zero mismatches. An entry still displaying `Conjecture:` is not by itself evidence of openness. |
| A001951 | Stephan's conjecture is recorded as proved by Sela Fried; OEIS comment 2025-10-24, JIS 2026 Article 26.1.8. Independently checked `n = 0..10^6`, zero mismatches. |
| A064170 | Wolfdieter Lang's 2020-05-26 proof is in the entry and the old conjecture line points at it. |
| A051293 | A later OEIS comment signed Ralf Stephan, 2026-06-18, records a proof by an autonomous AI agent and links the proof file. This is the arXiv:2608.11941 corpus effect in action. |
| A062771 | Charles R. Bower's 2005-05-20 comment confirms the old conjecture and supplies the formula. |
| A120737 / A070226 | **Settled inside this repository.** `D5/S3/Arith/DivisorCountRadicalCoincidence.radical_eq_card_divisors_of_dvd` is Ctibor O. Zizka's conjecture, and its docstring names both entries. R31 independently produced a complete Omega-counting proof and a million-term check before the repository search closed it — effort that this row exists to prevent. |

### Known erratum in the source, not an open problem

| entry | what it is |
| --- | --- |
| Stephan 2004, item (33) / A056777 | The printed `n ≡ 64 (mod 72)` is a known typo. Exact check over `2 <= n <= 10^6` finds exactly five numbers satisfying the premise — 65, 209, 11009, 38009, 680609 — all refuting the printed congruence. arXiv:2606.10331v3 (2026-07-22) states the typo on its first page and gives 65 as the least solution; the corrected version is A056777. |
| Stephan 2004, items (111) and (112) / A065359 / A036556 | Both rest on a definition Sloane corrected on 2007-01-09. A036556 is `{k : s_2(3k) odd}`, not `{k : 3 | k and s_2(k) odd}`. Under the literal printed set the checks fail at `n = 21` and `n = 63` respectively — that is the stale definition showing, not a new refutation. |
| Stephan 2004, item (35) / A063880 | The object is A063880, whose entry already carries Stephan's own 2003-07-07 congruence observation. A paper's item number is not a second open problem. |

### Boundary-value-only refutations, and why they were not promoted

| entry | reading |
| --- | --- |
| A069198 / A069197 | Cloitre's parameterized sentence "if a(2)=m, different from 2 or 5, sequence diverges" is literally false at `m = 1`, which is a fixed point (`F(2) = 1`, so the orbit is constant). But this refutes neither entry's own initial value (6 and 4), and the historical parameter domain could not be read from the revision history. R31 also found that the entry's own comment about the `m = 5` cycle disagrees with the recurrence as printed: the actual cycle is a rotation of `(5,4,3,7)`. Calibrate the source statement before treating a missing boundary value as a settlement. |

### Numerically verified, no proof route

| entry | reading |
| --- | --- |
| A076905 | Exact check `1 <= n <= 10^6` with rational root bracketing at denominator `10^40`, zero mismatches and no ambiguous rounding — but no general argument and no verified short Lean route. Numeric agreement is not a proof-type candidate. |

### Family exclusion: Paul D. Hanna's generating-function conjectures

Another driver has worked this family systematically — `dev` carries roughly eighty public
`hanna_conjecture*` theorems. More importantly, that driver's Library notes record, in prose, that
a given conjecture already follows from frozen content and is therefore *deliberately not stated*
as a theorem; see `Library/Arith/hanna2026a393856.md` and `Library/Recurrence/hanna2026a396846.md`.
Such an entry is not an available target even though OEIS still labels it `Conjecture`. The same
notes give a family argument: modulo two, `A(x - x*A(k*x)/k) = x` loses every term with `j >= 2`
whenever `k` is even, so the whole even-scaling branch shares one reduced object and a different
A-number in that branch is not a different target.

## How large a numeric check has to be

Search briefs long asked for "at least 10^4 exact checks". That is the wrong shape of rule: it is
infeasible for fast-growing sequences and it caused A079278 (Quet 2003) to be held back although
its recurrence had been verified exactly as far as anyone can compute. Scale the requirement to the
sequence's growth:

- linear or polynomial growth — 10^4 to 10^6 exact checks;
- exponential growth — as far as is affordable, reporting the exact range;
- doubly exponential growth (digit count doubling per step or faster) — **a dozen or two exact
  big-integer checks is appropriate evidence**; state that N is the ceiling at that scale rather
  than reporting the run as incomplete.

A079278's denominators illustrate the point: digit counts run
`1, 1, 2, 3, 6, 12, 25, 50, 100, 200, 401, 803, 1606, 3213, 6427, 12855, 25711, 51422, 102845, 205690, 411381`,
so `a(21)` alone has 411381 digits. The test is whether the reported range would convince a sceptic,
not whether it reaches a fixed number.

## What a browser-oracle search seat cannot do

A `nyxid-oracle` seat has no filesystem and cannot run `git grep`, so asking it to exclude
candidates that already have an equivalent public theorem in this repository asks for something it
physically cannot check. Repository deduplication is the orchestrator's step. Give such a seat the
fullest possible do-not-report list instead, and have it flag candidates for the repository check
rather than claim to have performed it.

## R32 — orchestrator 定向挖掘（2026-09-16，OEIS `%C`/`%F` 猜想行，按作者与年代）

采集口径：`https://oeis.org/search?q=author:"<name>" Conjecture&fmt=text`，作者取 Cloitre / Quet / Kimberling / Jovovic / Stephan / Murthy / Perry / Resta / Bergot / Bouhamida / Wilson v / Hasler / Shevelev，共取回 **1002** 条不重复条目；形状过滤（要求全称量词或「only/exactly/iff/divides/congruent/prime」等，排除渐近/密度/生成函数/启发式）留 **308** 条；再剔除条目正文自带结算标记（`is wrong`／`counterexample`／`proved by`／`Proof:` 等）后剩 **239** 条仍活。下列为本轮逐条判掉的部分，供后续轮次不再重复。

### 已由已发表定理即时结算（settled-with-citation，不开 lane）

- **A078712**（`%F` Michael Somos, Dec 25 2022：`if p is a prime then a(p) == 1 (mod p)`；rev #87）。该序列是 `x^3 + x^2 - 1` 之根的幂和的相反数（条目 `%F` 自己写出 Binet 形式），故 `a(p) = -tr(M^p)`，`M` 为伴随矩阵。**Zarelua（2008，Math. Notes；即 Arnold 2006 猜想）** 的整数矩阵 Gauss 同余 `tr(A^{p^k n}) ≡ tr(A^{p^{k-1} n}) (mod p^k)` 在 `k = n = 1` 即给出结论。钉版 Mathlib 亦已有 `ZMod.trace_pow_card`（`Mathlib/LinearAlgebra/Matrix/Charpoly/FiniteField.lean:60`）。识别步骤对专家是一步代入，判为已结算。
- **A001608**（`%C` Roman Witula, Feb 09 2013：`Is it true that a(n) and a(p*n) are congruent modulo p for every prime p?`；rev #486）。Perrin 数是 `x^3 - x - 1` 伴随矩阵幂的迹，同一条 Zarelua/Arnold 定理直接给出肯定回答。同上判为已结算。注意条目自身已把 `p | a(p)` 记为**已知性质**（`%C ... has property that p prime => p divides a(p)`），故这里只是同一原理的 `n` 倍版本。

### 数值排除（本轮实测，无反例，仍开放）

- **A015126**（`%C` Jianing Song, Nov 11 2022：`a(n) is always odd for odd n`）。`a(n) ≤ n` 恒成立，故对 `n ≤ N` 的判定只需 `φ` 筛到 `N`。实测 `N = 10^7`：**奇 n 中 a(n) 为偶者 0 个**。无反例，且无短证路线，留开放。
- **A393710**（`%C`：`each nonnegative positive integer occurs only finitely many times`）。`a(n) = #{(x,y,z) : x²+yz=n, 0<x<y<z}`。实测 `n ≤ 4*10^5`：取值 `v` 最后一次出现的下标为 `a(n)=0 → 1722`、`1 → 1482`、`2 → 678`、`3 → 1592`、`4 → 1610`、`5 → 4290`、`6 → 2442`；`a(n)=0` 共 31 个，最大 1722。猜想等价于 `a(n) → ∞`，需下界估计，非小时级靶。
- **A079128**（`%C`：`a(n) is divisible by n^2-1 for n>3` 与 Jovovic 2003 的 `gcd(a(n),n)=1`）。`a(n) = Σ_{d|n} μ(d)·b_d(n)`，`b_d(n)` 为全部轮长被 `d` 整除的置换数。实测 `n ≤ 60`：两条**均无反例**。素数情形 `a(p) = (p-1)·(p-1)!` 可由 `(p+1) | (p-1)!`（`p ≥ 5` 时 `p+1` 为合数）直接给出，但一般 `n` 需要置换轮型计数与 Möbius 反演，钉版 Mathlib 无该计数公式，成本超第一档。留开放。
- **A143772**（`%C` Robert G. Wilson v, Sep 08 2008：`All even numbers are terms and the only odd numbers which are terms are 1 and 3`）。**后半句有两行证明**：`m` 偶时 `g | 1+m` 与 `g | 2+m/2`，故 `g | 2(2+m/2)-(1+m) = 3`；`m` 奇时每个 `k+m/k` 为偶，故 `g` 偶。**前半句不是小时级靶**：实测 `m ≤ 3*10^5` 时偶值 `118,134,142,146,158,166,178,194`（皆为 `2p`，`p` 素）尚未出现，构造需要算术级数中的素数（Dirichlet）加 CRT 精确性控制。整条猜想是合取，只结算易的一半不构成结算，故本轮不开 lane。

### 判掉的伪候选

- **A067793**（`%C` Gary Detlefs, May 03 2012：`Odd composite n such that (n^2 + 8) mod 3 = 0`）。条目内已有 `%C Both conjectures are wrong. The first counterexample is 385. - _Robert Israel_, May 17 2017`。本轮独立复算确认：`385 = 5·7·11` 为奇合数且 `3 ∤ 385`，但 `φ(385) = 240 < 2·385/3`，故不是项。**教训：形状过滤只看含 `Conjecture` 的行会漏掉条目内别处的反驳行；批量筛选必须读全条目正文。**

### 读法歧义而判掉

- **A181741**（`%F` R. J. Mathar, Nov 18 2010：`Conjecture: equals the intersection of A000040 and A081118 or the intersection of A000040 and A089633`；rev #41）。第一个描述是对的：A081118 的 `%C` 自述即「Numbers of the form 2^t - 2^k - 1, 1 <= k < t」，与 A181741 的 `%N` 逐字同形，故该半句近乎定义性复述。第二个描述**字面为假**：A089633 允许 `k = 0`，`2 = 2^2 - 2^0 - 1` 在其中且为素数，而 A181741 的 `%S` 数据行以 `3` 开头、不含 `2`（`k ≥ 1` 时 `2^t - 2^k` 为偶，`2^t - 2^k = 3` 无解）。但源句用的是 **`or`**：可读作「二者之一成立」，那样整句为真。一个词的读法决定真假，条目也没有给出判别语境，故本条不作结算靶——按第 2.9 条，这属于「陈述本身不确定」，不是我们能替作者裁决的对象。

## 本轮的方法学教训

**批量形状过滤只读含 `Conjecture` 的行会漏掉条目内别处的结算行。** R32 的 A067793 就是这样混进候选：它的反驳写在另一行
`%C Both conjectures are wrong. The first counterexample is 385. - _Robert Israel_, May 17 2017`，
不含 `Conjecture` 一词，形状过滤看不见。修法是在过滤后**对整条正文**再扫一遍结算标记
（`is wrong` / `are wrong` / `is false` / `counterexample` / `disprov` / `proved by` / `Proof:` /
`no longer a conjecture` / `settled` 等），命中即剔除。R32 用该口径把 308 条压到 **239 条仍活**。
这一步很便宜，而漏掉它的代价是一整条 lane 的探针与预登记。
