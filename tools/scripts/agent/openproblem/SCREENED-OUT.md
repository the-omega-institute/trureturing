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
| 699 | FALSIFIABLE | Kummer 进位数给出 `v_p(C(n,i))`,每个 n 是 O(n²) 对 | 未跑 |
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

### 对选题函数的结论

Erdős 这条线的可结算面就是上表那 41 条,已全部列名;其中能被本机预算内的有限搜索触及的不超过三条,
且都还没有已知上界可比。相较之下 OEIS 的 `%F`/`%C` 猜想线本会话产出 8 条已合入的结算。
**按每小时结算数排序,OEIS 线优先;Erdős 线按上表逐条推进,不再重新普查徽章。**
