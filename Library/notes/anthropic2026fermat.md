---
bibkey: anthropic2026fermat
authors: Anthropic
year: 2026
title: Fermat's Last Theorem in Lean 4
doi: null
url: https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef
claim: Upstream Lean search reference for Fermat's Last Theorem and its Frey-Serre-Ribet-Wiles proof route.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Fermat's Last Theorem — 上游搜索参考

[Anthropic 官方仓库](https://github.com/anthropics/fermats-last-theorem)是本次
检索定位的 Claude / Anthropic 费马大定理形式化库。
本条用于搜索、定位和后续复用尽调；本次登记未引入构建依赖或移植证明。
上游 README 将其标为研究工件，并明确不维护、不接受贡献。

检索词：Claude、Anthropic、Fermat's Last Theorem、FLT、费马大定理、
Frey curve、Serre、Ribet、Wiles、Taylor-Wiles、elliptic curve、
modularity、Galois representation、Kummer、regular primes。

## 固定版本

2026-09-10 读取官方 `main` 并固定如下源码快照：

| 项目 | 上游值 |
| --- | --- |
| 提交 | `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` |
| Lean | `leanprover/lean4:v4.33.1` |
| Mathlib 标签 | `v4.33.0`（README 所述） |
| Mathlib 提交 | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Lake 包名 | `flt_e2e` |
| 许可证 | Apache-2.0；见该提交的 [LICENSE](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/LICENSE) |

版本依据是同一提交的 `lean-toolchain`、`lakefile.lean` 和
`lake-manifest.json`。未来接入须按 spec A17/A17.2 比较本仓的实际钉版。

## 证明与检索入口

- [Theorems/Thm_fermat_last_theorem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_fermat_last_theorem.lean)：
  `fermat_last_theorem`，陈述为任意自然数 `n ≥ 3` 和正自然数
  `a, b, c` 满足 `a ^ n + b ^ n ≠ c ^ n`。
- [FinalCheck.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/FinalCheck.lean)：
  默认构建入口，用 `#guard_msgs` 约束上述定理的公理输出，
  并给出 `flt_mathlib : FermatLastTheorem`。
- [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/PROOF-PATH.md)：
  上游 README 指定的证明路线与具名中间定理导航；
  `Definitions/` 放定义，`Theorems/` 放陈述，`P2M/Sol/` 放证明。
- [html/index.html](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/html/index.html)：
  上游提供的离线浏览入口，含定理名与定义名搜索。
- [verification/](https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/verification)：
  Comparator 与 nanoda 独立检查入口。

## 归属与验证记录

2026-09-10：通过 GitHub 仓库检索 `Fermat`、owner `anthropics` 定位此库；
随后核对官方 owner、默认分支、提交、许可证，并按固定提交读取 README、
版本文件、`formalization.yaml`、最终陈述文件、`FinalCheck.lean` 和 NOTICE。

上游 [NOTICE](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE)
记录对 [Imperial College London FLT](https://github.com/ImperialCollegeLondon/FLT)、
[flt-regular](https://github.com/leanprover-community/flt-regular) 和 Mathlib
的复用；逐文件归属见
[ATTRIBUTION.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md)。
后续若移植代码，须按 A17.2 保留相应许可证、NOTICE 和归属链。

上游 [README](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/README.md)
报告完整构建、Comparator 和 nanoda 通过；
[formalization.yaml](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/formalization.yaml)
自报 `sorry_count: 0`，公理为 `propext`、`Classical.choice`、`Quot.sound`，
评审状态为 `self-assessed`。本次未重跑这些验证；这是上游报告，
不是本仓新增的 kernel 验证或冻结记录。
