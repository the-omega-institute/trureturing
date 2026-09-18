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

## R33(2026-09-16):作者轴与形状轴各挖一批,四条判掉,其中两条是自己造成的

本轮从两条轴取候选:作者轴(Amarnath Murthy / Benoit Cloitre / Vladeta Jovovic / Zak Seidov 的
2001–2009 条目,每人 4 页)与形状轴(`"Conjecture" "if and only if"`、`"conjecture that these are the
only"`、`"Conjecture:" "is prime if and only if"`、`"Conjecture" "are the only" divisible`、
`"Conjecture:" "divides"`,每条 3 页)。合计 85 条经形状与结算标记过滤后仍活,25 条仓内已有命中。

### 仓内已解决

- **A069208**(`%C` Werner Schulte, Jan 23 2025:multiplicative `f` 的 powerful-除数和(1)乘性、
  (2)等于 `A112526·f` 的逆 Möbius 变换)。**本仓已证**:
  `D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform.lean`,提交 `f553846c7b`。
  在派任何席之前由 §3.1 的检索挡下。判据提醒:按 A 号 grep 会漏,这条是按内容(`Powerful`)grep 才命中的。

### 文献已结算(证明行就在猜想行下面,是本轮最贵的教训)

- **A000680**(`%C` Werner Schulte, Oct 05 2025:`(2n+1) | (2n)!/2^n + 2^n ⟺ 2n+1` 素数)。
  **下一行**即 `%C The conjecture is true (see Fried link). - _Sela Fried_, Nov 24 2025`,并附
  `%H` 的 PDF 与 `arXiv:2607.24832`(pp. 2-4)。判据成立(实测 `1 ≤ n ≤ 400` 零例外),但「此前未被文献
  判定」不成立,故不满足 §3.2「开放问题结算依据」。预登记 issue #8173 已关并勘误。
- **A006472**(`%C` Werner Schulte, Oct 04 2020:`n | 2·a(n-1) + 4 ⟺ n` 素数,`a(n)=n!(n-1)!/2^(n-1)`)。
  **下一行**即 `%C For a proof of the above conjecture see Himane. ... - _Peter Bala_, Nov 06 2024`。
  判据成立(实测 `2 ≤ n ≤ 500` 零例外,`a(1..6) = 1,1,3,18,180,2700` 与 `%S` 一致),同样不满足准入。
  预登记 issue #8189 已关并勘误。

### 读法歧义而判掉

- **A062368**(`%C` R. J. Mathar, Aug 09 2012:`this is the third inverse Mobius transform of the
  sequence 4^A001221(n)`)。**陈述为真**,本轮符号复算:`(4^ω * 1 * 1 * 1)(p^e) = (e+1)(e+2)/2 +
  4·Σ_{i=0}^{e-1}(i+1)(i+2)/2 = (e+1)(e+2)(4e+3)/6`,与 `%N` 的 `a(p^e)` 逐字相同,并在
  `n = 2,4,8` 上数值核对(7 / 22 / 50)。不取的理由是条目自身的结算状态不可读:2026-07-10 Ridouane
  Oudra 加入 `%F a(n) = Sum_{d|n} 4^omega(d)*tau_3(n/d)`——这与 Mathar 的猜想是同一句话,却写成
  `%F` 断言、不带 conjecture 限定、也不带证明引用。同 A181741,一行的读法决定它是否仍开放。

### 看过但不取的(留作后续,附理由)

- **A057032**(`%C` Mikhail Kurkov, Mar 10 2022:`a(n) - 1 is prime if and only if a(n) = n + 1`)。
  姊妹条目 **A057063** 的对应判据已由 Ilya I. Bogdanov 在 MathOverflow 证出(条目内 `%C` 注明),
  但 A057032 用的是**前向**循环置换且固定 `s(1)..s(n-1)`,与 A057063 的反向置换加固定 `s(1)..s(n)`
  不同,仍标 Conjecture。不取的理由是成本:序列由「对 1,2,3,… 依次施加 P(2),P(3),P(4),… 取极限」定义,
  形式化要先构造 PS(n)、证其逐点稳定、再定义极限,不是小时级靶。
- **A156253**(`%F` Jon Maiga, Dec 09 2021:`a(n) = (a(a(n-1)) mod 2) + a(n-2) + 1`)。Kolakoski 邻域;
  条目 `%H` 已挂 Jon Maiga 2025 的 PDF《A Recurrence Related to the Kolakoski Sequence》,且 2023 年
  另有一条同形 `%F` 以断言形式写入。结算状态与 A062368 同属不可读。
- **A105801**(`%C` Giovanni Resta, Nov 17 2010:`for every k > 0 there is an index m such that all the
  a(n) with n > m have the same residue mod 3^k`)。Fibonacci-Collatz 混合动力;`k ≤ 2` 已由条目内
  「`n >= 10` 时 `a(n) ≡ 7 (mod 9)`」覆盖,更高的 `k` 依赖奇偶轨道的长期行为。
- **A321084**、**A015126**、**A069051**、**A211384**:分别归结为「该族无 base-2 Fermat 伪素数」、
  Carmichael 全序数猜想邻域、Wieferich 邻域、贪心整除递推的无界分类,均非第一档。

### 结算藏在条目自己链接的论文里(最贵的一条)

- **A181666**(`%C` Ralf Stephan, Nov 18 2010:`Also, terms of A023758 divisible by 3, divided by 3
  (conjectured)`)。**该条目 `%H` 链接的论文已经证出它**:Andreas M. Hinz、Paul K. Stockmeyer,
  *Precious Metal Sequences and Sierpinski-Type Graphs*,J. Integer Seq. 25 (2022), Article 22.4.8。
  取 PDF 转文本后的逐行读数:
    - 第 233 行 `ℓ_{2ν−1} = (1/3)(2^{2ν} − 1)`,即 `(4^ν − 1)/3` —— A181666 `%N` 的奇部形状;
    - 第 975 行指认 `2^n − 2^{n−ν}` 族「apart from the offset」就是 A023758;
    - 第 1515 行对**偶** ν 取 `(1/3)·2^{n−ν}M_ν = (1/3)(2^n − 2^{n−ν})`;
    - 第 1528 行(式 33)`B̂ = {2^i·ℓ_{2j+1} | i, j ∈ ℕ₀}`;
    - 第 1566–1569 行 `b̂(…) = (1/3)(2^N − 2^{N−2ρ}) = 2^{N−2ρ}ℓ_{2ρ−1}`,并直书
      「(This sequence b̂ is A181666.)」
  合起来即:A023758 的项被 3 整除当且仅当其 1-游程长为偶,除以 3 后所得集合恰为 A181666——正是待结算
  的那句 `%C`。该 lane 已走到冻结与三轮九席评审,由架构席以 10/10 判出,PR #8184 与预登记 #8143 关闭。
  **这条比前两条贵得多:前两条在预登记阶段就能看见,这条要读一篇 840 KB 的论文正文。**

## 本轮的方法学教训(比 R32 更贵的同一个病)

R32 已经记过「形状过滤只看含 `Conjecture` 的行会漏掉别处的结算行」,并且仓内早有
`tools/scripts/agent/openproblem/oeis-conjecture-scan.py` 执行这条——它的 `SETTLED` 正则涵盖
`Proof\s*:`、`a proof`、`the proof`、`is true`、`proved`、`follows from`、`theorem of`、
`counterexample found`。本轮 A000680 与 A006472 两条仍然栽进去,**原因是绕过了这个器、改用手写核对,
而手写核对只 grep 了猜想句**。

代价:两份完整预登记 issue、两棵 lane 工作树、两个探针席;更糟的是 A000680 的预登记被另一台驱动机接走
并合入 dev(`cec4774a0a`,带 `scribe-open-problem-resolution-v1` 标记),一条本不该计数的结算进了 KPI,
而误导它的正文出自本会话。

**修法(是器不是人):候选进预登记之前必须跑扫描器,把它的 `status` 与 `settlement_lines` 原样贴进 issue;
手写核对不能替代它。** 其次,「无证明行」是一句全称否定,写它之前要枚举过全集——这里的全集是该条目的
全部 `%C`/`%H`/`%D` 行,不是含 `Conjecture` 的那一行。结算行最常见的位置恰恰是猜想行的**下一行**,
因为提出者与证明者在同一处对话;读到猜想句就停手是最容易漏的姿势。

### 第三种藏法及其修法

前两条的结算写在条目文本里,`oeis-conjecture-scan.py` 的 `SETTLED` 正则能看见;**A181666 的结算不在
条目文本里,而在条目 `%H` 链接的论文正文里**,任何扫描条目文本的器都看不见。

本仓的 `Library/Arith/stephan2010a181666.md` 曾由 orchestrator 写下「the Hinz--Stockmeyer paper on
Sierpinski-type graphs do not treat this identity」——**写这句时没有读过那篇论文**,只看了 5 KB 的
摘要页,而正文 PDF 是 840 KB。摘要页的「Concerned with sequences … A023758 … A181666 …」列表恰恰说明
作者知道这两个序列,是**更该读全文**的信号,不是可以跳过的理由。

修法是把「全集」写清楚:一句「该陈述未被文献判定」的全称否定,其全集是
**该条目的全部 `%C`/`%H`/`%D` 行,加上每一篇 `%H` 论文的全文**。操作上:

    curl -s "https://oeis.org/search?fmt=text&q=id:<A号>" | grep -E '^%[CHD]'   # 枚举链接
    curl -sL <每个 %H 论文 URL 的 pdf> -o p.pdf && pdftotext p.pdf p.txt        # 取全文
    grep -n -F <A号> p.txt; grep -n <定义式/集合形状> p.txt                      # 按数学内容查,不只按 A 号

`%H` 为空才是「无链接论文」,当场用上面第一条命令验;例如 A079278 只有 `%D`、A249759 两者皆无。

## R34(2026-09-16):erdosproblems.com 的状态徽章,与 #647 的有限搜索

用户的常设目标里有一句「找一些老的, erdos 上的问题试试」。此前一次尝试按题面形状盲筛 1217 条得 0;
本轮改为先量该站点自己的状态词表,结论对今后的选题直接有用。

### 两段取样(逐题取页,解析状态徽章)

| 状态 | #1–60 | #600–660 |
| --- | ---: | ---: |
| `OPEN` | 25 | 27 |
| `PROVED` | 18 | 17 |
| `DISPROVED` | 11 | 7 |
| `SOLVED` | 3 | 7 |
| `VERIFIABLE` | 1 | 1 |
| `DECIDABLE` | 1 | 0 |
| `FALSIFIABLE` | 1 | 2 |

两段互相印证:约一半已判定,约 43% 是 `OPEN`,约 5% 带可有限判定的徽章。取两段不同区间是因为低编号题受关注更多,单窗口不能外推(§3.5 同形纪律)。

**两条对选题直接有用的事实:**

1. **该题库正被系统性 Lean 形式化。** 已判定的条目里多数徽章写作 `PROVED (LEAN)` / `DISPROVED (LEAN)` /
   `SOLVED (LEAN)`,并附「the proof verified in Lean」。按 §3.1 先库后证,盲扫这张表的重复风险很高;
   任何候选进管线前必须先看它自己的徽章。
2. **站点自带第二档筛子。** `VERIFIABLE`(Open, but could be proved with a finite example)、
   `FALSIFIABLE`(Open, but could be disproved with a finite counterexample)、
   `DECIDABLE`(Resolved up to a finite check)三个徽章,明说哪些问题能被有限计算触及——这正是
   §3.6 第二档的定义。而 `OPEN` 的条目一律附「This is open, and cannot be resolved with a finite
   computation」,即明确的第三档。**按徽章筛,不要按题面形状筛。**

### #647 — 有限搜索,已搜到 10^8,无命中,**不构成结算**

Erdős–Selfridge,`VERIFIABLE`,£25(折合 $44):设 τ 为除数个数函数,**是否存在 n > 24 使
`max_{m<n}(m + τ(m)) ≤ n + 2`?**

判据可由一次线性筛完成,不必对每个 n 重算窗口:`M(n) = max_{m<n}(m + τ(m))` 是前缀最大值,
筛出 τ 后 `numpy.maximum.accumulate` 一遍即可。

```
$ python3 erd647.py 100000000
N = 100000000
tau sanity: tau[1..12] = [1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6]
n=24 check: M(23) = 26  n+2 = 26  -> True
hits n>24: []  count: 0
EXIT=0
```

**阳性对照是这次读数的关键**:`n = 24` 是已知的唯一例子,它在同一判据下为真,所以那个 `count: 0` 是
「搜过了没有」而不是「判据写错了恒为假」。τ 的前十二项也与定义相符。

**为什么这不是进展**:§3.6 ③ 规定有限证书只有排除此前未排除的情形才可称部分进展。该题页未记录前人的
搜索上界,故本轮无法断言 10^8 超出了已知范围;按 §2.9 记为「已测 10^8 无命中,前人上界未知」,不写成
推进。此外 §3.3 明禁普通正向有限实例取得用途准入——即便搜到一个 n,其交付形态也须按反驳侧组织
(它反驳的是「不存在这样的 n」),不能作为 `certified-instance` 的正向实例入库。

Erdős 本人在 [Er79] 说「it is extremely doubtful」存在无穷多个这样的 n,并指出更强的形式需要
Schinzel 假设 H。把界继续往上推(分段筛可达 10^10 量级)不改变这个判断,故本轮不继续投入,
按 §2.7 预算包络换靶。

## R35(2026-09-16):erdosproblems.com 全库徽章普查(1–1200),与 #458 的等价归约

R34 只取了两段各 60 题的样本。本轮把全库 1–1200 逐页取下并解析徽章,器与读数都入仓,
以后选题不必再重取。

```
$ python3 tools/scripts/agent/openproblem/erdos-badge-scan.py \
    --start 1 --end 1200 --cache <cache> --badges VERIFIABLE,FALSIFIABLE,DECIDABLE
OPEN         582
PROVED       331
DISPROVED    137
SOLVED        98
FALSIFIABLE   25
NO-BADGE      11
DECIDABLE      9
VERIFIABLE     7
EXIT=0
```

合计 1200,与编号区间一致;`NO-BADGE` 11 条是页面无 `prize` 块的条目,按 §2.9 单列而不并入任何
一栏——**未解析出的徽章不得看起来像某个徽章**。

**可有限判定的一档共 41 条**(`VERIFIABLE` 7 + `FALSIFIABLE` 25 + `DECIDABLE` 9),
**其中 `(LEAN)` 标记为 0 条**——已 Lean 验证的徽章只出现在已判定条目上,故这 41 条都还没有被
形式化结算。这与 R34 的第 1 条观察一致:该题库正被系统性 Lean 形式化,盲扫已判定条目重复风险高,
而这一档是尚未被触及的那部分。

**`FALSIFIABLE` 才是本仓可用的那一栏。** §3.3 禁止普通正向有限实例取得用途准入,
`certified-instance` 与 `bounded-enumeration` 只能走经验证的 `refutes`;而 `FALSIFIABLE` 的定义
正是「open, but could be disproved with a finite counterexample」,反例的交付形态天然是 `refutes`。
`VERIFIABLE`(有限例子即可证明)找到例子也只能按反驳侧组织(它反驳的是「不存在这样的对象」),
`DECIDABLE`(已归约到一次有限检查)通常那次检查本身超出本机预算。

### 41 条里按可计算性排序的前五,及为何只跑了一条

| # | 徽章 | 判据的计算形状 | 处置 |
| --- | --- | --- | --- |
| 458 | FALSIFIABLE | 素数间隙内的素数幂之积,一次线性筛 | **已跑,见下** |
| 699 | FALSIFIABLE | Kummer 进位数给出 `v_p(C(n,i))`,每个 n 是 O(n²) 对 | **已跑,见下** |
| 993 | FALSIFIABLE | 枚举 n 点树 + 独立集 DP,n≈20 时 823065 棵 | 未跑 |
| 287 | FALSIFIABLE | 单位分数、相邻差 ≤2:区间补集是非相邻子集和 | **不可穷举**,见下 |
| 779 | FALSIFIABLE | 反例须遍历 `(p_n, P)` 内全部素数,P 为素数阶乘 | **不可穷举** |

#287 的不可行性是算出来的,不是感觉:相邻差 ≤2 等价于 `S = [a,b] \ M` 且 `M` 无相邻元,于是
`H(b)-H(a-1) - Σ_{m∈M} 1/m = 1`;`M` 至多取一半元素,故 `H(b)-H(a-1) ∈ [1,2]`,即 `b/a ∈ [e,e²]`。
`a=100` 时区间长约 638,其无相邻子集数是 Fibonacci(640) 量级,折半相遇也无济于事。`a` 只能扫到十几。

### #458 — 判据可化简为一行,已查到 `p_k < 2×10⁷`,无反例

Erdős–Graham,`FALSIFIABLE`:记 `[1,…,m] = lcm(1..m)`,是否对所有 `k ≥ 1` 有
`[1,…,p_{k+1}-1] < p_k·[1,…,p_k]`?

**不必物化任何 lcm。** `L(p_k) = p_k·L(p_k - 1)`,而在 `(p_k, p_{k+1})` 内 lcm 只因素数幂 `q^a`
(`a ≥ 2`)各增加一个因子 `q`,故原式等价于

  `∏ { q : q^a 是 (p_k, p_{k+1}) 内的素数幂 } < p_k`。

```
$ python3 tools/scripts/agent/openproblem/erdos458-lcm-gap-check.py 20000000
primes below 20000000: 1270607
prime powers q^a (a>=2) below 20000000: 732
  control k=1 p_k=2 p_(k+1)=3 prod=1 < p_k -> True
  control k=2 p_k=3 p_(k+1)=5 prod=2 < p_k -> True
  control k=3 p_k=5 p_(k+1)=7 prod=1 < p_k -> True
  control k=4 p_k=7 p_(k+1)=11 prod=6 < p_k -> True
  control k=5 p_k=11 p_(k+1)=13 prod=1 < p_k -> True
  control k=6 p_k=13 p_(k+1)=17 prod=2 < p_k -> True
counterexamples (prod >= p_k): 0
EXIT=0
```

**阳性对照说明那个 0 是搜过了。** `prod` 在前六个 k 上取到 1、2、1、6、1、2 三个不同值,判据不是恒真;
`k=4` 处 `prod = 2·3 = 6`(间隙 `(7,11)` 含 8 与 9)对 `p_k = 7`,只差 1 就相等——最紧的一处在最前面,
往后 `q ≤ p_{k+1}^{1/2}` 而 `p_k` 线性增长,余量迅速拉开。

**这不是进展,按 §3.6 ③ 记。** 该题页未记录前人搜索上界,故不能声称 `2×10⁷` 超出已知范围;
按 §2.9 记为「已测 `p_k < 2×10⁷` 无命中,前人上界未知」。归约本身(等价于素数幂之积的不等式)
是可复用的结论,故留在此处;继续把界往上推不改变判断,按 §2.7 预算包络换靶。

### #699 — 已查到 `n ≤ 400`,无反例;判据的界属于「对」不属于任一下标

Erdős–Graham,`FALSIFIABLE`:是否对每个 `1 ≤ i < j ≤ n/2` 都存在素数 `p ≥ i` 使
`p | gcd(C(n,i), C(n,j))`?

Kummer 定理给出 `v_p(C(n,i))` = 以 p 为基数做 `i + (n-i)` 的进位数,于是「p 整除 C(n,i)」不必造出
任何二项式系数;每个 i 做一个素数位图,配对时取交。

```
$ python3 tools/scripts/agent/openproblem/erdos699-binomial-gcd-check.py 400
control (stronger demand p>=j) first failure: (6, 1, 3)
  n<=100 ok / n<=200 ok / n<=300 ok / n<=400 ok
result: no counterexample for n <= 400
EXIT=0
```

**`p ≥ i` 这个界是「对」的性质,不是任一下标自己的性质。** 若把它写成每行位图只保留 `p ≥` 自己的
下标,算出来的其实是更强的 `p ≥ j`,它在 `(n,i,j) = (6,1,3)` 处就假——`gcd(C(6,1), C(6,3)) = gcd(6,20) = 2`,
`p = 2` 满足 `p ≥ i = 1` 但不满足 `p ≥ j = 3`。这条更强判据因此正好用作阳性对照,器里以断言钉住:
**扫不出反例的判据必须先证明它能失败**。

同 §3.6 ③:该题页未记录前人搜索上界,故 `n ≤ 400` 不作进展,按 §2.9 记为「已测 `n ≤ 400` 无命中,
前人上界未知」。

### 对选题函数的结论

Erdős 这条线的可结算面就是上表那 41 条,已全部列名。本轮跑掉两条(#458、#699),两条都无反例,
且两条都没有前人上界可比,故按 §3.6 ③ 都不作进展;#993 仍在预算内未跑。相较之下 OEIS 的 `%F`/`%C` 猜想线本会话产出 8 条已合入的结算。
**按每小时结算数排序,OEIS 线优先;Erdős 线按上表逐条推进,不再重新普查徽章。**

## R36(2026-09-17):A034448 与 A257750 —— 结算就写在猜想行下一行,而扫描器读不出来

**A034448**(unitary sigma)。猜想行 `%F Conjecture: a(n) = sigma(n^2/rad(n))/sigma(n/rad(n)).
- _Velin Yanev_, Aug 20 2017`。数值上它是对的:`1 ≤ n ≤ 20000` 零反例,证明也确实简单 ——
逐素因子 `(p^{2e}-1)/(p^e-1) = p^e+1` 加乘性,`p ≤ 97, e ≤ 8` 全对。

**但它早已被结算,而且就写在紧接着的下一行**:

> `%F This conjecture is easily verified since all the functions involved are multiplicative and
> proving it for prime powers is straightforward. - _Juan José Alba González_, Mar 19 2021`

**A257750**(Quasi-Carmichael)。`%C Conjecture: It is always smaller than the square root of the
corresponding Quasi-Carmichael number.`,下一行:

> `%C The conjecture that b < sqrt(n) is false. Look at n = 87061 = 13*37*181, 87365 = 5*101*173,
> and 96473 = 13*41*181. Their b values are 299, 331, and 351, while the corresponding sqrt(n)
> values are 295, 295, and 310, respectively.`

两条都被 `oeis-conjecture-scan.py` 报成 `no-marker`,A034448 差一步就被预登记。

**器的两个缺陷,已同 PR 修掉,不是逐例登记**:

1. **词表只认「证明」族**(`proved|a proof|is true|was shown|follows from|counterexample found|…`),
   收不到「easily verified」「straightforward」这一族,也收不到条目自己用「is false」写下的反驳。
2. **更深的一层**:结算评论通常会点名它所结算的东西,于是那一行本身含 `conjectur`,被当成**新的一条猜想**,
   而被它结算的那条的搜索窗口恰好在它之前截断 —— 结果是标记贴在结算句自己身上,真猜想仍报无标记。
   现在带结算标记的行不再算作新猜想的开始,除非它用显式的 `Conjecture:` 引入一条。

**判据不变**:无标记**不等于**开放,它只是「值得读」的过滤;读全条目、下载每篇 `%H` 论文、数值核对、
预登记仍然手工。这两条的教训是反过来的那一侧 —— **有标记却没读出来,代价是派席去证一个已经了结的东西**。

## R37(2026-09-17):Erdős 1984 的 `f(n)=n` 非素数幂问题 —— Erdős 自己 1992 年答了,见证值搜 OEIS 一次即中

搜题席(ChatGPT Pro)按「读 Erdős 原始论文里没编号的顺带问题」这条路找回一条候选,`settlement_probability`
自估 0.8,并且带着一个可直接核的见证:

> P. Erdős, *On two unconventional number theoretic functions and on some related problems*,
> Calcutta Math. Soc. jubilee volume (1984),p. 115,Theorem 2 之后的一句无编号问题,逐字:
> **"In fact, are there integers n for which n ≠ p^α and f(n)=n ?"**
> 其中 `f(n) = Σ_{p | n} p^{⌊log_p n⌋}`。

本次亲跑核实见证为真:`228 = 2²·3·19`,`2⁷=128 ≤ 228 < 256`、`3⁴=81 ≤ 228 < 243`、`19 ≤ 228 < 361`,
`128+81+19 = 228`,而 228 不是素数幂。30 万以内的非素数幂不动点恰为 `228, 3115, 190233`。
席位另指出 OEIS **A339378** 的 `%F` 行印着 `a(n) = n iff n = p^k , p prime, k >= 1`(2020-12-07 加入、无出处),
被 228 直接推翻。

**决定性的一步只花了一次查询**:拿三个见证值去搜 OEIS —— `https://oeis.org/search?fmt=text&q=228,3115,190233`
—— 命中 **A302755**「Strongly prime-additive numbers」,其 `%C` 写着
「The first 3 terms were given in the paper by Erdős & Hegyvári. They were found by P. Massias.」

下载并读了那篇论文(Paul Erdős and Norbert Hegyvári, *On prime-additive numbers*,
Studia Sci. Math. Hungar. 27 (1992) 207–212,`https://real-j.mtak.hu/5469/1/StudScientMath_27.pdf`),
p. 207 逐字给出 `2²·3·19 = 228 = 2⁷+3⁴+19`、`5·7·89 = 3115 = 5⁴+7⁴+89`、`3²·23·919 = 190233 = 3¹¹+23³+919`
(found by P. Massias),随后才定义 strongly prime-additive。**1984 年的问题由 Erdős 本人 1992 年答掉了。**

于是两半都出局:

- **Erdős 的问题**:已解决,不是开放问题,按第 3.6 条「已知结果不派席」。
- **A339378 的 `%F` 行**:它确实是假的,但推翻它的事实已经发表(Erdős–Hegyvári 1992 / A302755),
  所以那是数据库勘误,不是开放问题的结算。

**同篇论文里仍开放、但本线用不上的部分**(记下来免得再看一遍):「infinitely many strongly prime-additive
numbers」「infinitely many prime-additive numbers」以及 prime-additive 计数远多于 strongly 的猜测,全是
无穷性/渐近断言,有限见证不可结算;唯一形状可被有限反驳的是「前 `2r+1` 个素数之积**总是** prime-additive」,
本次亲跑 `r = 0..4`(`2, 30, 2310, 510510, 223092870`)全部找到表示,且表示随 r 迅速变多,不是可结算靶。

**这条教给管线的东西写进了 `TARGET-GATES.md` 第 ① 关**:查「是否已被结算」不能只 curl 猜想自己那条
OEIS 条目 —— 结算常常记在**另一条**由见证值索引的条目里。有具体见证时,先拿见证值搜 OEIS。

## R38–R40(2026-09-17):三条搜题/筛题线的判掉与两条自筛

### 自筛(orchestrator,按记忆里的候选队列)

- **A062549**(Irvine 2023-04-01,`a(n)` 是最小的 `m` 使 `!n ∣ m!`,猜想 `a(n) = gpf(!n)` 对 `n > 2`):条目数据按 `!(n+1)` 索引
  (`a(2) = 4` 对应 `!3 = 4 = 2²`),而 `n > 2` 恰好排除了唯一的平方例;`n ≤ 35`(`!n` 至 39 位,`sympy.factorint`)无反例。余下是
  「`!n` 无使 `v_p(gpf!) < v_p(!n)` 的素因子幂」的无穷断言,有限见证不可结算。判掉:第三关。
- **A342039**(`a(n) ≥ prime(n) − 1`)、**A376336**(Ramanujan τ,`a(n) ≤ n²`):b-file 分别验到远处/`n ≤ 10000`,反驳需大规模计算
  A307437 / τ,无小见证。判掉:第三关。

### R39(ChatGPT Pro,转向 2025–26 arXiv 结尾猜想与问题栏)

返回 3 候选、4 已结算。开 lane 的两条:PNim Conjecture 2(#8467)、Pudelko Conjecture 8 `n = 0`(#8469)。

- **Crux Mathematicorum Problem 5144(ii)**(Bataille,52(5),2026-05,p. 241:「Prove or disprove: ∀ n, ⌊⁵√n + ⁵√(n+1)⌋ = ⌊⁵√(32n+5)⌋」;
  席位给出 `n = 525` 反例,`3499⁵ < 525·10¹⁵`、`3501⁵ < 526·10¹⁵` 的精确证书):**不是开放问题**——解答征集截止 2026-07-15,
  提出者持有解答,刊出只是排期;与 Problem 2623 的区别是后者在累积未解表里挂了 25 年。判掉:第三关(档位)。数学未复算。
- 已结算(席位所读,orchestrator 未复核):Brugidou arXiv:2509.20959 Conjecture 4.3 在 v2 摘要自记「已删除,因为为假」;
  Fokkink–Joshi arXiv:2506.13337 结算 Kimberling 的 A304499 / A304502 猜想;Crux MA337 已在 2026-03 期 p. 114 刊出解答。

### R40(codex 筛题席,过 R32 池的四关)

池 376 条:`SCREENED-OUT` 剔 3、仓内已落地剔 15、在飞剔 2、与 Adamczewski *OEIS Open*(arXiv:2608.11941,492 条记录/444 个 A 号)
重合剔 22;OEIS 对 `id:` 查询限流(HTTP 429)使完整读过的只有 82 条。提出 3 条,开 lane 两条:A344083(#8470)、A280258(#8471)。

- **A190302**(Fröhlich 2018:`a(n) < 6`,验到 `n = 10022141`):交叉引用条目 **A187285** 的 `%C`(Greathouse 2011-03-07)
  早已断言「`a(n) ∈ {n, 2n, 3n, 4n, 5n}`」,即同一事实以已知面貌写在猜想提出的七年前;证明是三行(取 `h = ⌈10^{d+1}/n⌉ ≤ 5`)。
  判掉:第一关——结算写在**被引条目**里,不在猜想自己的条目里,这是 R37「见证值索引到另一条目」之外的第二种藏法。
- 第一关判掉(条目自身载结算,席位读全文;orchestrator 未逐条复核):A048715(Adams-Watters 2009 证明)、A129995(「it is now
  known」)、A182134(limsup 子句由 Maier 定理结算)、A202137(Israel 2018:CRT 易证)、A208244(Somu–Tran 2024 证明 `a(n) > 0`)、
  A267999(Ordowski 2018 给出蕴含)、A276976 / A270096(Schinzel 证明)、A289559(MathOverflow 证明)、A323739(Neder 2019 证明)、
  A103777(同一 `%C` 行的整除断言已蕴含)。
- 第三关判掉:A074980 / A074981 / A075788–A075791(Pillai 型「famous hard problem」)、A081091(三比特素数无穷性)、A106044 /
  A144256(Legendre 猜想)、A185351(等价于无奇完全数)、A192789(Erdős–Straus)、A231201 / A281976(悬赏)、A212320(socialist prime)。

### 方法学读数

- 一条猜想的「已结算」有三处可藏:自己条目的后续行(扫描器可读)、由见证值索引的另一条目(R37)、**被它交叉引用的条目**(R40 的
  A190302)。第三处的判据:凡候选的 `%Y`/`%F` 引到的条目,其 `%C` 要一并读。
- OEIS `id:` 查询在一分钟内数十次即 429;筛题席批量读条目须节流,`oeis-conjecture-scan.py` 批量模式在 429 下中止且无 JSON 输出。

## R41–R45(2026-09-17/18):OEIS Open 数据集、R32 池全读、与一条已被自己仓库半结算的论文

### R41(ChatGPT Pro):定位 Adamczewski *OEIS Open* 的机器可读面

arXiv:2608.11941 的数据在两处:`google-deepmind/formal-conjectures` 的 `auto_oeis` 分支(Lean 陈述,一条记录一个文件)与
`epoch-research/LeanOpenProblems-results`(19 次求解跑的逐记录结果)。orchestrator 亲算:492 条记录里 19 次跑的「已解」并集 170 条,
余 **322 条未解**(`oeis-open-unsolved.json`;形状计数 universal 95 / iff 63 / threshold 104 / existence-or-asymptotic 50 /
famous-equivalent 2 / other 8)。这 322 条是一个已被多套求解器碾过一遍的池,下两轮只在它上面做「算小情形找反例」。

### R42 / R43(codex 筛题席):322 条未解记录逐条从定义算小情形

- R42 读 49 条、算 25 条,提出 6 条(A135508、A323359、A323386、A076141、A064313、A378143),自报结算概率 0.02–0.38,
  全部「小情形成立」——没有一条给出反例;已结算 2 条:A117531(`%C` Kutal 2026-08-22,Heegner 数论证)、A180017(本文件 R-早期已记
  Drmota–Spiegelhofer arXiv:2501.00850)。
- R43 对全部 322 条按形状生成检查程序(`/tmp/op-screen-r43/results.tsv`):**holds 223 + 沿用 R42 的 holds 22 = 245 条小情形成立,
  skipped-shape 61(存在性/渐近/等价名题,有限计算不可判),unknown 16(未跑或范围内无判),反例 0**。
- 判掉:整条矿脉。理由不是「难」,是**选择效应**——留在 OEIS Open 未解池里的猜想已经被作者、后续评注者与 19 次机器求解各算过一遍,
  小范围反例在进池之前就被筛光了;在这里再算一次是第 2.7 条的查表复制器。反驳形的产地应是**刚发表、还没人算过的**猜想
  (R39/R45 的 arXiv 结尾栏),不是被反复过筛的公开池。

### R44(codex 筛题席,过 R32 池余下 330 条的四关)

池 376:`SCREENED-OUT` 剔 29、仓内已落地剔 15、在飞剔 2,余 330 条在第一关**全部读完**(用 `oeis/oeisdata` 快照
`956668977564dbec38a657dafa875f021b4d052b` 取交叉引用条目,绕开 `id:` 查询的 429)。已结算 9 条:A078128(自身 `%F` 的渐近式蕴含)、
A219055 / A261876(Adamczewski 证明/反证)、A237695(Tao 2015)、A245474 / A300949(猜想行下一行就是证明)、A271513(论文全跑已接受)、
A293715(Mills 反例 `A007755(34) = (2^16+1)^2`)、A330719(交叉引用 A330718 把同一同余写成已知事实)。第三关剔 9 条(Polignac、Firoozbakht、
孪生素数蕴含、奇多完全数、USD 3500 悬赏、奇完全数蕴含、Lehmer 商余)。提出 3 条:

- **A273871 Conjecture 1**(Krizek 2016:`p ∈ A273871 ⟹ ∀ k ≥ 0, (p−1)²+1 ∣ (4^k)^{p−1} − 1`)与 **A274000 的同形猜想**:探针后判掉——
  两者的**父条目** A273870 与 A273999 的 `%C` 第一行(同一作者、同一天)把同一事实写成 「Also, numbers m such that
  (4^k)^(m−1) ≡ 1 (mod (m−1)²+1) for all k ≥ 0」,即在素数子序列里叫「Conjecture」的句子在母序列里是**已断言的事实**;数学是
  `Nat.pow_sub_one_dvd_pow_sub_one` 一步(bind-only)。这是 R40 A190302 之后**第二、三次**「结算写在被引条目里」,规则升级为筛题
  第一关的固定动作:候选 `%Y`/`%C` 引到的每个条目,其 `%N`/`%C` 前三行一并读,同一断言以事实面貌出现即出局。
- **A245212**(`σ(2n) = σ(n) + 2n` 恰当 `n` 是 2 的幂,自报 p=0.3):小情形至 2²⁰ 无反例,`σ` 乘性 + 奇部分论证是 Mathlib 现成引理的
  组合;未开 lane(bind-only 且不是「刚发表」形)。

### R45(ChatGPT Pro,arXiv 2025–26 结尾栏):Bhagat–Kulkarni–Larsson–Murali arXiv:2510.24280v2

席位提出同文 **Problem 6** 的有限反例 `S={4,22,35,38}, h=161`。仓内去重:**Problem 6 已由 #6780 冻结的
`D5/S0/Certificates/SelfInterestConventionDeviationGain` 结算**(见证 `S={7,12,13,38,50}`,`h=122/172`),席位在 SCREENED-OUT 里搜
`2510.24280` 无命中就报「repo-wide dedupe incomplete」——去重必须搜 D5/Blueprint,不能只搜本文件。但同一见证同时推翻同文的
**Conjecture 4**(FvF 逐坐标不劣于 AvA:`o_FvF(161) = (84,77)`,`o_AvA(161) = (83,78)`,Bob 在 AvA 下多得 1),而 #6780 的正文明写
「Nothing about Conjecture 4 … is established here」。orchestrator 用两个结构不同的评估器复算一致,并以论文 Table 1 与 #6780 内核核验值校准;
3 元集 `max S ≤ 40, h ≤ 300` 与 4 元集 `max S ≤ 30, h ≤ 200` 无更小反例(作者抽样 `max S ≤ 25`)。开 lane:#8521(复用冻结的 `outcome`)。

### 方法学读数

- 「结算写在被引条目里」现在有三例(A190302、A273871、A274000),从 R40 的一条观察升为第一关的固定动作(见上)。
- 仓内去重有两层:文献标识(arXiv 号 / A 号)与**对象**(同一定义、同一见证);席位只搜本文件是第 3.1 条的失败形。一篇论文有多条猜想时,
  仓内结算了其中一条不等于其余的都结算了——逐条读 `Blueprint` 正文里的「Nothing about … is established」句。
- 被多套求解器过筛过的公开池(OEIS Open)对反驳形几乎零产出(322 条 0 反例);反驳形的矿脉是新发表且未被计算过的猜想。

## R46(2026-09-18):arXiv 2025–26 结尾栏、OEIS 新条目与一条答案印在同一篇论文另一页的问题

### R46(ChatGPT Pro,arXiv math.NT 2025-09 → 2026-09 与 math.CO / cs.DM 2026-06 → 2026-09 结尾栏,OEIS `keyword:new` 猜想)

提出 **Nathanson, *Problems in additive number theory, VII*, arXiv:2605.26425, Problem 12(2)**(printed page 9:
「(2) If A ∈ \binom{Z}{k} with min(A)<0, then ℓ_h(A) < n_h^♭(k).」):取 `h=2, k=3, A={−1,1,2}` 得 `2A={−2,0,1,2,3,4}`,
`ℓ_2(A)=4=n_2^♭(3)`(三元非负集覆盖 `[0,5]` 须含 0,1,再由第三元 `t` 分 `t≤3` 缺 5、`t≥4` 缺 3),严格不等式为 `4<4`。
席位注明该论文第 7 页已把同一个集合及其和集印作反射例子,只是没有把它认作 Problem 12(2) 的答案——「答案印在同一篇论文的另一页」。
仓内去重(orchestrator,`origin/dev`):`Nathanson|2605\.26425|segmentLength|nonnegativeMaximum|h-basis` 在 D5/Blueprint/Problems/Library
无命中;结论形 `sSup {n` 仅 `D5/S1/Words/FibonacciMapBound.lean` 一处(词长上确界,无关)。开 lane:#8540 → PR #8561。
Problem 12(1)(非严格不等式)未结算,不在交付面。

已结算、不派席(席位读出,orchestrator 复核出处):

- **arXiv:2606.17447**(Shtrezi):Theorem 1 对全部 `g ≥ 2` 证明贪心 `{1,g,g+1}` 三和无关序列的 Conjecture 16。仓内
  `Problems/greedy-three-sumfree-two-parameter.md` 已明写「Conjecture 16 … deliberately out of scope」,该卷宗结算的是两参数成员公式,
  不是 Conjecture 16;两者都不再是候选。
- **arXiv:2607.10763**(Shi):已证 Bueno 等人的模乘法矩阵秩猜想。
- **arXiv:2608.19886**(Mao–Zhao):已在 `l=4` 反驳 Chung–Graham–Spiro 的 `D_l = U_l`(9 ∈ U_4 ∖ D_4);这条小反例已经发表,不能再算一次。

算过、无反例、不提出:

- **OEIS A399308**(Lucas 表示动力系统):席位独立实现并跑全部正整数起点至 10⁶,只见既知的四个循环,无逃逸轨道;交叉引用
  A399306 / A399307 取不到,源筛未完成。
- **OEIS A397806 / A397807**(2026 TFJM 题):在猜想限定的区间族内精确计数复现 `n ≤ 9` 的极大值,`n = 7, 8, 9` 的无限制搜索无改进;
  猜想本身未证,不提出。

席位未取得的读数:GitHub 目录枚举、递归树 API 与代码搜索在该席全部失败,只能逐文件取 raw;精确钉版的仓内去重由 orchestrator 完成(见上),
席位自报的「无命中」不作读数。

### 方法学读数

- 「答案印在同一篇论文的另一页」是「结算写在被引条目里」(R40/R44,三例)的论文版:一篇末尾提问的论文,其正文例子可能已经是答案。
  第一关的固定动作再加一条:候选问题所在论文里,凡与问题同对象的显式例子(表、反射例、边界例)逐个代入问题陈述。
- R46 的三条「已结算」全部来自席位读结尾栏时顺手核对的同题近作;这是搜题席该做的第一关,不是产出——它们不进 KPI,只进本文件。

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

## R36(2026-09-17):A034448 与 A257750 —— 结算就写在猜想行下一行,而扫描器读不出来

**A034448**(unitary sigma)。猜想行 `%F Conjecture: a(n) = sigma(n^2/rad(n))/sigma(n/rad(n)).
- _Velin Yanev_, Aug 20 2017`。数值上它是对的:`1 ≤ n ≤ 20000` 零反例,证明也确实简单 ——
逐素因子 `(p^{2e}-1)/(p^e-1) = p^e+1` 加乘性,`p ≤ 97, e ≤ 8` 全对。

**但它早已被结算,而且就写在紧接着的下一行**:

> `%F This conjecture is easily verified since all the functions involved are multiplicative and
> proving it for prime powers is straightforward. - _Juan José Alba González_, Mar 19 2021`

**A257750**(Quasi-Carmichael)。`%C Conjecture: It is always smaller than the square root of the
corresponding Quasi-Carmichael number.`,下一行:

> `%C The conjecture that b < sqrt(n) is false. Look at n = 87061 = 13*37*181, 87365 = 5*101*173,
> and 96473 = 13*41*181. Their b values are 299, 331, and 351, while the corresponding sqrt(n)
> values are 295, 295, and 310, respectively.`

两条都被 `oeis-conjecture-scan.py` 报成 `no-marker`,A034448 差一步就被预登记。

**器的两个缺陷,已同 PR 修掉,不是逐例登记**:

1. **词表只认「证明」族**(`proved|a proof|is true|was shown|follows from|counterexample found|…`),
   收不到「easily verified」「straightforward」这一族,也收不到条目自己用「is false」写下的反驳。
2. **更深的一层**:结算评论通常会点名它所结算的东西,于是那一行本身含 `conjectur`,被当成**新的一条猜想**,
   而被它结算的那条的搜索窗口恰好在它之前截断 —— 结果是标记贴在结算句自己身上,真猜想仍报无标记。
   现在带结算标记的行不再算作新猜想的开始,除非它用显式的 `Conjecture:` 引入一条。

**判据不变**:无标记**不等于**开放,它只是「值得读」的过滤;读全条目、下载每篇 `%H` 论文、数值核对、
预登记仍然手工。这两条的教训是反过来的那一侧 —— **有标记却没读出来,代价是派席去证一个已经了结的东西**。

## R37(2026-09-17):Erdős 1984 的 `f(n)=n` 非素数幂问题 —— Erdős 自己 1992 年答了,见证值搜 OEIS 一次即中

搜题席(ChatGPT Pro)按「读 Erdős 原始论文里没编号的顺带问题」这条路找回一条候选,`settlement_probability`
自估 0.8,并且带着一个可直接核的见证:

> P. Erdős, *On two unconventional number theoretic functions and on some related problems*,
> Calcutta Math. Soc. jubilee volume (1984),p. 115,Theorem 2 之后的一句无编号问题,逐字:
> **"In fact, are there integers n for which n ≠ p^α and f(n)=n ?"**
> 其中 `f(n) = Σ_{p | n} p^{⌊log_p n⌋}`。

本次亲跑核实见证为真:`228 = 2²·3·19`,`2⁷=128 ≤ 228 < 256`、`3⁴=81 ≤ 228 < 243`、`19 ≤ 228 < 361`,
`128+81+19 = 228`,而 228 不是素数幂。30 万以内的非素数幂不动点恰为 `228, 3115, 190233`。
席位另指出 OEIS **A339378** 的 `%F` 行印着 `a(n) = n iff n = p^k , p prime, k >= 1`(2020-12-07 加入、无出处),
被 228 直接推翻。

**决定性的一步只花了一次查询**:拿三个见证值去搜 OEIS —— `https://oeis.org/search?fmt=text&q=228,3115,190233`
—— 命中 **A302755**「Strongly prime-additive numbers」,其 `%C` 写着
「The first 3 terms were given in the paper by Erdős & Hegyvári. They were found by P. Massias.」

下载并读了那篇论文(Paul Erdős and Norbert Hegyvári, *On prime-additive numbers*,
Studia Sci. Math. Hungar. 27 (1992) 207–212,`https://real-j.mtak.hu/5469/1/StudScientMath_27.pdf`),
p. 207 逐字给出 `2²·3·19 = 228 = 2⁷+3⁴+19`、`5·7·89 = 3115 = 5⁴+7⁴+89`、`3²·23·919 = 190233 = 3¹¹+23³+919`
(found by P. Massias),随后才定义 strongly prime-additive。**1984 年的问题由 Erdős 本人 1992 年答掉了。**

于是两半都出局:

- **Erdős 的问题**:已解决,不是开放问题,按第 3.6 条「已知结果不派席」。
- **A339378 的 `%F` 行**:它确实是假的,但推翻它的事实已经发表(Erdős–Hegyvári 1992 / A302755),
  所以那是数据库勘误,不是开放问题的结算。

**同篇论文里仍开放、但本线用不上的部分**(记下来免得再看一遍):「infinitely many strongly prime-additive
numbers」「infinitely many prime-additive numbers」以及 prime-additive 计数远多于 strongly 的猜测,全是
无穷性/渐近断言,有限见证不可结算;唯一形状可被有限反驳的是「前 `2r+1` 个素数之积**总是** prime-additive」,
本次亲跑 `r = 0..4`(`2, 30, 2310, 510510, 223092870`)全部找到表示,且表示随 r 迅速变多,不是可结算靶。

**这条教给管线的东西写进了 `TARGET-GATES.md` 第 ① 关**:查「是否已被结算」不能只 curl 猜想自己那条
OEIS 条目 —— 结算常常记在**另一条**由见证值索引的条目里。有具体见证时,先拿见证值搜 OEIS。

## R38–R40(2026-09-17):三条搜题/筛题线的判掉与两条自筛

### 自筛(orchestrator,按记忆里的候选队列)

- **A062549**(Irvine 2023-04-01,`a(n)` 是最小的 `m` 使 `!n ∣ m!`,猜想 `a(n) = gpf(!n)` 对 `n > 2`):条目数据按 `!(n+1)` 索引
  (`a(2) = 4` 对应 `!3 = 4 = 2²`),而 `n > 2` 恰好排除了唯一的平方例;`n ≤ 35`(`!n` 至 39 位,`sympy.factorint`)无反例。余下是
  「`!n` 无使 `v_p(gpf!) < v_p(!n)` 的素因子幂」的无穷断言,有限见证不可结算。判掉:第三关。
- **A342039**(`a(n) ≥ prime(n) − 1`)、**A376336**(Ramanujan τ,`a(n) ≤ n²`):b-file 分别验到远处/`n ≤ 10000`,反驳需大规模计算
  A307437 / τ,无小见证。判掉:第三关。

### R39(ChatGPT Pro,转向 2025–26 arXiv 结尾猜想与问题栏)

返回 3 候选、4 已结算。开 lane 的两条:PNim Conjecture 2(#8467)、Pudelko Conjecture 8 `n = 0`(#8469)。

- **Crux Mathematicorum Problem 5144(ii)**(Bataille,52(5),2026-05,p. 241:「Prove or disprove: ∀ n, ⌊⁵√n + ⁵√(n+1)⌋ = ⌊⁵√(32n+5)⌋」;
  席位给出 `n = 525` 反例,`3499⁵ < 525·10¹⁵`、`3501⁵ < 526·10¹⁵` 的精确证书):**不是开放问题**——解答征集截止 2026-07-15,
  提出者持有解答,刊出只是排期;与 Problem 2623 的区别是后者在累积未解表里挂了 25 年。判掉:第三关(档位)。数学未复算。
- 已结算(席位所读,orchestrator 未复核):Brugidou arXiv:2509.20959 Conjecture 4.3 在 v2 摘要自记「已删除,因为为假」;
  Fokkink–Joshi arXiv:2506.13337 结算 Kimberling 的 A304499 / A304502 猜想;Crux MA337 已在 2026-03 期 p. 114 刊出解答。

### R40(codex 筛题席,过 R32 池的四关)

池 376 条:`SCREENED-OUT` 剔 3、仓内已落地剔 15、在飞剔 2、与 Adamczewski *OEIS Open*(arXiv:2608.11941,492 条记录/444 个 A 号)
重合剔 22;OEIS 对 `id:` 查询限流(HTTP 429)使完整读过的只有 82 条。提出 3 条,开 lane 两条:A344083(#8470)、A280258(#8471)。

- **A190302**(Fröhlich 2018:`a(n) < 6`,验到 `n = 10022141`):交叉引用条目 **A187285** 的 `%C`(Greathouse 2011-03-07)
  早已断言「`a(n) ∈ {n, 2n, 3n, 4n, 5n}`」,即同一事实以已知面貌写在猜想提出的七年前;证明是三行(取 `h = ⌈10^{d+1}/n⌉ ≤ 5`)。
  判掉:第一关——结算写在**被引条目**里,不在猜想自己的条目里,这是 R37「见证值索引到另一条目」之外的第二种藏法。
- 第一关判掉(条目自身载结算,席位读全文;orchestrator 未逐条复核):A048715(Adams-Watters 2009 证明)、A129995(「it is now
  known」)、A182134(limsup 子句由 Maier 定理结算)、A202137(Israel 2018:CRT 易证)、A208244(Somu–Tran 2024 证明 `a(n) > 0`)、
  A267999(Ordowski 2018 给出蕴含)、A276976 / A270096(Schinzel 证明)、A289559(MathOverflow 证明)、A323739(Neder 2019 证明)、
  A103777(同一 `%C` 行的整除断言已蕴含)。
- 第三关判掉:A074980 / A074981 / A075788–A075791(Pillai 型「famous hard problem」)、A081091(三比特素数无穷性)、A106044 /
  A144256(Legendre 猜想)、A185351(等价于无奇完全数)、A192789(Erdős–Straus)、A231201 / A281976(悬赏)、A212320(socialist prime)。

### 方法学读数

- 一条猜想的「已结算」有三处可藏:自己条目的后续行(扫描器可读)、由见证值索引的另一条目(R37)、**被它交叉引用的条目**(R40 的
  A190302)。第三处的判据:凡候选的 `%Y`/`%F` 引到的条目,其 `%C` 要一并读。
- OEIS `id:` 查询在一分钟内数十次即 429;筛题席批量读条目须节流,`oeis-conjecture-scan.py` 批量模式在 429 下中止且无 JSON 输出。

## R41–R45(2026-09-17/18):OEIS Open 数据集、R32 池全读、与一条已被自己仓库半结算的论文

### R41(ChatGPT Pro):定位 Adamczewski *OEIS Open* 的机器可读面

arXiv:2608.11941 的数据在两处:`google-deepmind/formal-conjectures` 的 `auto_oeis` 分支(Lean 陈述,一条记录一个文件)与
`epoch-research/LeanOpenProblems-results`(19 次求解跑的逐记录结果)。orchestrator 亲算:492 条记录里 19 次跑的「已解」并集 170 条,
余 **322 条未解**(`oeis-open-unsolved.json`;形状计数 universal 95 / iff 63 / threshold 104 / existence-or-asymptotic 50 /
famous-equivalent 2 / other 8)。这 322 条是一个已被多套求解器碾过一遍的池,下两轮只在它上面做「算小情形找反例」。

### R42 / R43(codex 筛题席):322 条未解记录逐条从定义算小情形

- R42 读 49 条、算 25 条,提出 6 条(A135508、A323359、A323386、A076141、A064313、A378143),自报结算概率 0.02–0.38,
  全部「小情形成立」——没有一条给出反例;已结算 2 条:A117531(`%C` Kutal 2026-08-22,Heegner 数论证)、A180017(本文件 R-早期已记
  Drmota–Spiegelhofer arXiv:2501.00850)。
- R43 对全部 322 条按形状生成检查程序(`/tmp/op-screen-r43/results.tsv`):**holds 223 + 沿用 R42 的 holds 22 = 245 条小情形成立,
  skipped-shape 61(存在性/渐近/等价名题,有限计算不可判),unknown 16(未跑或范围内无判),反例 0**。
- 判掉:整条矿脉。理由不是「难」,是**选择效应**——留在 OEIS Open 未解池里的猜想已经被作者、后续评注者与 19 次机器求解各算过一遍,
  小范围反例在进池之前就被筛光了;在这里再算一次是第 2.7 条的查表复制器。反驳形的产地应是**刚发表、还没人算过的**猜想
  (R39/R45 的 arXiv 结尾栏),不是被反复过筛的公开池。

### R44(codex 筛题席,过 R32 池余下 330 条的四关)

池 376:`SCREENED-OUT` 剔 29、仓内已落地剔 15、在飞剔 2,余 330 条在第一关**全部读完**(用 `oeis/oeisdata` 快照
`956668977564dbec38a657dafa875f021b4d052b` 取交叉引用条目,绕开 `id:` 查询的 429)。已结算 9 条:A078128(自身 `%F` 的渐近式蕴含)、
A219055 / A261876(Adamczewski 证明/反证)、A237695(Tao 2015)、A245474 / A300949(猜想行下一行就是证明)、A271513(论文全跑已接受)、
A293715(Mills 反例 `A007755(34) = (2^16+1)^2`)、A330719(交叉引用 A330718 把同一同余写成已知事实)。第三关剔 9 条(Polignac、Firoozbakht、
孪生素数蕴含、奇多完全数、USD 3500 悬赏、奇完全数蕴含、Lehmer 商余)。提出 3 条:

- **A273871 Conjecture 1**(Krizek 2016:`p ∈ A273871 ⟹ ∀ k ≥ 0, (p−1)²+1 ∣ (4^k)^{p−1} − 1`)与 **A274000 的同形猜想**:探针后判掉——
  两者的**父条目** A273870 与 A273999 的 `%C` 第一行(同一作者、同一天)把同一事实写成 「Also, numbers m such that
  (4^k)^(m−1) ≡ 1 (mod (m−1)²+1) for all k ≥ 0」,即在素数子序列里叫「Conjecture」的句子在母序列里是**已断言的事实**;数学是
  `Nat.pow_sub_one_dvd_pow_sub_one` 一步(bind-only)。这是 R40 A190302 之后**第二、三次**「结算写在被引条目里」,规则升级为筛题
  第一关的固定动作:候选 `%Y`/`%C` 引到的每个条目,其 `%N`/`%C` 前三行一并读,同一断言以事实面貌出现即出局。
- **A245212**(`σ(2n) = σ(n) + 2n` 恰当 `n` 是 2 的幂,自报 p=0.3):小情形至 2²⁰ 无反例,`σ` 乘性 + 奇部分论证是 Mathlib 现成引理的
  组合;未开 lane(bind-only 且不是「刚发表」形)。

### R45(ChatGPT Pro,arXiv 2025–26 结尾栏):Bhagat–Kulkarni–Larsson–Murali arXiv:2510.24280v2

席位提出同文 **Problem 6** 的有限反例 `S={4,22,35,38}, h=161`。仓内去重:**Problem 6 已由 #6780 冻结的
`D5/S0/Certificates/SelfInterestConventionDeviationGain` 结算**(见证 `S={7,12,13,38,50}`,`h=122/172`),席位在 SCREENED-OUT 里搜
`2510.24280` 无命中就报「repo-wide dedupe incomplete」——去重必须搜 D5/Blueprint,不能只搜本文件。但同一见证同时推翻同文的
**Conjecture 4**(FvF 逐坐标不劣于 AvA:`o_FvF(161) = (84,77)`,`o_AvA(161) = (83,78)`,Bob 在 AvA 下多得 1),而 #6780 的正文明写
「Nothing about Conjecture 4 … is established here」。orchestrator 用两个结构不同的评估器复算一致,并以论文 Table 1 与 #6780 内核核验值校准;
3 元集 `max S ≤ 40, h ≤ 300` 与 4 元集 `max S ≤ 30, h ≤ 200` 无更小反例(作者抽样 `max S ≤ 25`)。开 lane:#8521(复用冻结的 `outcome`)。

### 方法学读数

- 「结算写在被引条目里」现在有三例(A190302、A273871、A274000),从 R40 的一条观察升为第一关的固定动作(见上)。
- 仓内去重有两层:文献标识(arXiv 号 / A 号)与**对象**(同一定义、同一见证);席位只搜本文件是第 3.1 条的失败形。一篇论文有多条猜想时,
  仓内结算了其中一条不等于其余的都结算了——逐条读 `Blueprint` 正文里的「Nothing about … is established」句。
- 被多套求解器过筛过的公开池(OEIS Open)对反驳形几乎零产出(322 条 0 反例);反驳形的矿脉是新发表且未被计算过的猜想。

## R46(2026-09-18):arXiv 2025–26 结尾栏、OEIS 新条目与一条答案印在同一篇论文另一页的问题

### R46(ChatGPT Pro,arXiv math.NT 2025-09 → 2026-09 与 math.CO / cs.DM 2026-06 → 2026-09 结尾栏,OEIS `keyword:new` 猜想)

提出 **Nathanson, *Problems in additive number theory, VII*, arXiv:2605.26425, Problem 12(2)**(printed page 9:
「(2) If A ∈ \binom{Z}{k} with min(A)<0, then ℓ_h(A) < n_h^♭(k).」):取 `h=2, k=3, A={−1,1,2}` 得 `2A={−2,0,1,2,3,4}`,
`ℓ_2(A)=4=n_2^♭(3)`(三元非负集覆盖 `[0,5]` 须含 0,1,再由第三元 `t` 分 `t≤3` 缺 5、`t≥4` 缺 3),严格不等式为 `4<4`。
席位注明该论文第 7 页已把同一个集合及其和集印作反射例子,只是没有把它认作 Problem 12(2) 的答案——「答案印在同一篇论文的另一页」。
仓内去重(orchestrator,`origin/dev`):`Nathanson|2605\.26425|segmentLength|nonnegativeMaximum|h-basis` 在 D5/Blueprint/Problems/Library
无命中;结论形 `sSup {n` 仅 `D5/S1/Words/FibonacciMapBound.lean` 一处(词长上确界,无关)。开 lane:#8540 → PR #8561。
Problem 12(1)(非严格不等式)未结算,不在交付面。

已结算、不派席(席位读出,orchestrator 复核出处):

- **arXiv:2606.17447**(Shtrezi):Theorem 1 对全部 `g ≥ 2` 证明贪心 `{1,g,g+1}` 三和无关序列的 Conjecture 16。仓内
  `Problems/greedy-three-sumfree-two-parameter.md` 已明写「Conjecture 16 … deliberately out of scope」,该卷宗结算的是两参数成员公式,
  不是 Conjecture 16;两者都不再是候选。
- **arXiv:2607.10763**(Shi):已证 Bueno 等人的模乘法矩阵秩猜想。
- **arXiv:2608.19886**(Mao–Zhao):已在 `l=4` 反驳 Chung–Graham–Spiro 的 `D_l = U_l`(9 ∈ U_4 ∖ D_4);这条小反例已经发表,不能再算一次。

算过、无反例、不提出:

- **OEIS A399308**(Lucas 表示动力系统):席位独立实现并跑全部正整数起点至 10⁶,只见既知的四个循环,无逃逸轨道;交叉引用
  A399306 / A399307 取不到,源筛未完成。
- **OEIS A397806 / A397807**(2026 TFJM 题):在猜想限定的区间族内精确计数复现 `n ≤ 9` 的极大值,`n = 7, 8, 9` 的无限制搜索无改进;
  猜想本身未证,不提出。

席位未取得的读数:GitHub 目录枚举、递归树 API 与代码搜索在该席全部失败,只能逐文件取 raw;精确钉版的仓内去重由 orchestrator 完成(见上),
席位自报的「无命中」不作读数。

### 方法学读数

- 「答案印在同一篇论文的另一页」是「结算写在被引条目里」(R40/R44,三例)的论文版:一篇末尾提问的论文,其正文例子可能已经是答案。
  第一关的固定动作再加一条:候选问题所在论文里,凡与问题同对象的显式例子(表、反射例、边界例)逐个代入问题陈述。
- R46 的三条「已结算」全部来自席位读结尾栏时顺手核对的同题近作;这是搜题席该做的第一关,不是产出——它们不进 KPI,只进本文件。

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

### #617 r=5:公开状态相互矛盾,而它是纯有限判定

Erdős–Gyárfás 证了 r=3(Chung–Liu 1978 已先证)与 r=4,并指出 r=2 为假;**r=5 是第一个开放情形**。
该题的 proof-claims 页载 7 条互不相容的 claim:Nick Winter(2026-07-31)与 Rob Sneiderman(2026-07-18)称 K₂₆ 不存在平衡 5-染色,
Conner Silverstein(2026-07-21)称存在。至多一条为真,故公开状态未定。

判据是纯有限的:反例即 K₂₆ 的一个 5-染色,使每 6 个顶点的导出 K₆ 上五色齐现。
编码为每条边一个颜色的 exactly-one,加上每个 6-子集 × 每色一条长 15 的子句(1625 变元 / 1,151,150 子句),颜色置换对称性按首 r 条边破掉。
**阶梯自带对照**:`(r,n) = (2,5)` 与 `(3,9)` 必须 SAT(后者即 `K_{r²}` 由 r 阶仿射平面承载),`(3,10)` 与 `(4,17)` 必须 UNSAT(已证的两个情形),
到 `(5,25)` 仍应 SAT,`(5,26)` 才是问句。器在 `tools/scripts/agent/openproblem/erdos617.py`。

### 对选题函数的结论

Erdős 这条线的 41 条可结算面**已逐条列名并逐条给出死因**。除 #617 的 r=5 外,没有一条留下本机预算内的有限空隙:
要么是正被系统攻击的名题,要么其有限检查已被该题 forum 页记录的社区计算推到远超本机的规模。
**第一关因此再加一条固定动作:读 forum 讨论页,不止读题页。** #993 与 #743 都是题页不载而 forum 页载着计算前沿的例子,
只读题页会让人以为它们还没被算过。
