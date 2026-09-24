---
bibkey: codex2026erdos699i3
authors: Independent Codex CLI mathematics seat; caller audit
year: 2026
title: "Erdos 699 i=3 Lucas/Kummer adjacent-core reduction"
doi: null
url: https://www.erdosproblems.com/699
claim: Necessary conditions and bounded exact checks for the i=3 lane; not a solution.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：`i=3` 的 Lucas/Kummer 相邻核心约化

关联 issue：#9670。当前写入 PR：#9723。

本条记录的是一份独立数学席的必要条件推导和有限核验，不是 Erdős 699 的完整证明、反例、Lean 定理或 KPI 结果。原始独立报告保存在本机临时路径；其 SHA-256 为
`9de452aec61d51260f34446954b49bd714781506660a24eeab67901636d35f0d`。

报告证明：假设 `i=3` 反例，则可写

\[
n=Mu,\quad j=tu,\quad M=2^a3^\varepsilon,\quad \varepsilon\in\{0,1\},
\]

并且 `4|M`、`u` 奇、`(M,u)=1`、`v_3(u)\ne1`、`tu>=4`，同时满足

\[
R(Mu-1)\mid t(M-t),\qquad
R(Mu-2)\mid t(M-t)(M-2t),
\]

以及

\[
(Mu-1)(Mu-2)\le\sqrt3 M^3,
\qquad u<3^{1/4}\sqrt M+2/M.
\]

这里 `R` 去掉全部 2-adic 因子，并在 3-adic 指数恰为 1 时再去掉一个 3。证明的关键是：对 `binom(n,3)` 的每个奇素因子，反例假设迫使 `binom(n,j)` 的 Lucas 逐位条件无进位；对 `n,n-1,n-2` 的低位块分别取模后得到上述整除式。高位逐位条件没有被省略，且两个低位整除式没有被错误地当成充分条件。

有限检查器 `tools/scripts/agent/openproblem/erdos699-i3-lucas-reduction-check.py` 使用标准库精确整数，覆盖直接检查 `n<=500` 和 Lucas 约化候选 `n<=2,000,000`。这些范围之外仍未证明，且无界 `M` 的候选引理尚未解决。

外部背景来源仍以官方问题页、Erdős–Szekeres 1978 原文和 Ecklund–Eggleton–Erdős–Selfridge 1978 原文为准；本条不作历史优先权或全球文献穷尽声明。

## 2026-09-24 高进位约化搜索

新增标准库程序 `tools/scripts/agent/openproblem/erdos699-highcarry-search.py`。它先用 (57) 的精确平方形式限制 `u`，再把 `R(Mu-1)` 的完整素数幂分别分配给 `t` 或 `M-t`，以 CRT 重构 `t`；主搜索不遍历 `1<=t<M/2`。程序对每个满足 `tu>=4` 的重构值都分解完整的 `C(Mu,3)`，并以 Kummer 进位数和独立的 Legendre 阶数逐素数交叉核对，再另行检验 (56) 的第二式。`q|Mu-1` 的两个余数标签和 `q|Mu-2` 的三个余数标签均被保留。

实际命令：

```text
/usr/bin/time -p python3 tools/scripts/agent/openproblem/erdos699-highcarry-search.py --amax 32 > /tmp/erdos699-highcarry-a32-final.json
```

程序 SHA-256 为 `7d227639191cb2d557c3b8919ba8b1404b01cb3493f4ea120317e7358cb9d6ec`。内部计时 38.704 秒；外部读数为 real 38.80 秒、user 32.85 秒、sys 0.15 秒。搜索覆盖 `2<=a<=32`、`epsilon in {0,1}` 共 62 行；每行输出由 (57) 精确算出的 `u` 上界。最大两行为：

| a | epsilon | M | (57) 给出的 u 上界 | 合法 u |
|---:|---:|---:|---:|---:|
| 32 | 0 | 4294967296 | 86250 | 33542 |
| 32 | 1 | 12884901888 | 149389 | 49797 |

全程共有 402255 个界内奇 `u`，其中 284528 个满足互素与三进赋值条件；检查 3162855 个 `R(Mu-1)` 素数幂分配后得到 590 个第一低块重构值，其中 528 个满足 `tu>=4`。程序对这 528 个满足 `tu>=4` 的重构值全部完成了 `C(n,3)` 分解及 Kummer/Legendre 交叉核对；其中没有一个同时满足第二低块，故本范围内 (56) 解数和忠实反例数均为 0。实际检查到的最大 `n` 为 1924862608146432；这是约化参数中的最大值，不是声称连续检查了此前到该数之间的每个 `n`。

非空控制包括 17130 个五标签模等价断言、91 个小行 CRT 与直接 `t` 枚举的一致性、八个精确分解样本，以及 `gcd(C(10,3),C(10,5))=12`。故意删去第二低块的错误谓词会接受 `(M,u,t)=(16,1,5)`，而正确谓词拒绝。放松见证 `(M,u,t)=(57,1,22)` 通过全部五类商余数测试，但 `C(57,22)` 在 `p=5,7` 的 Kummer 阶数都为 1；其 `M=57` 不属于允许的光滑形式，因此只是“低位通过而高位失败”的非空诊断，不是反例。

本轮最强的统一不变量仍是五因子素数幂分配：每个保留的 `q|Mu-1` 恰分配给 `t,M-t` 之一，每个保留的 `q|Mu-2` 恰分配给 `t,M-2t,M-t` 之一，五类两两按素数幂分离且乘积为 `R(Mu-1)R(Mu-2)`。这是 (56) 的精确分配形态，没有得到强于 (58) 的新统一恒等式或不等式，故没有另立定理候选。

此结果只是有限自审，没有 Lean 证明或独立评审；`a>=33` 未搜索。第一个仍未证明的陈述是：无界 `a` 下不存在满足完整 `i=3` 条件的合法 `(M,u,t)`。由于完整条件蕴含 (58)，证明“(58) 在全部合法参数上无解”是更强的充分排除目标，目前同样未证明。没有发现忠实反例，Erdős 699 状态不变。
