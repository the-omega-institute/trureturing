---
bibkey: openai2026finite
authors: OpenAI
year: 2026
title: Finite time blowup for Navier–Stokes and Euler equations
doi: null
url: https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538
claim: Upstream Lean search reference for smooth forced Navier-Stokes breakdown and unforced Euler finite-time singularity.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# NavierStokesAndEuler — 上游搜索参考

[OpenAI 官方仓库](https://github.com/openai/NavierStokesAndEuler)提供
Navier–Stokes 与 Euler 方程有限时间爆破结果的 Lean 4 形式化源码。
本条用于搜索、定位和后续复用尽调；本次登记未引入构建依赖或移植证明。

检索词：Navier-Stokes、Navier–Stokes、纳维–斯托克斯、Euler、欧拉方程、
有限时间爆破、finite time blowup、incompressible flow、smooth forcing、
periodic torus、vorticity、Comparator。

## 固定版本

2026-09-10 读取官方 `main` 并固定如下源码快照：

| 项目 | 上游值 |
| --- | --- |
| 提交 | `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` |
| Lean | `leanprover/lean4:v4.34.0-rc2` |
| Mathlib 标签 | `v4.34.0-rc2` |
| Mathlib 提交 | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| Lake 包名 | `NavierStokesAndEuler` |
| 许可证 | Apache-2.0；见该提交的 [LICENSE](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/LICENSE) |

版本依据是同一提交的 `lean-toolchain`、`lakefile.toml` 和
`lake-manifest.json`。未来接入须按 spec A17/A17.2 比较本仓的实际钉版。

## 证明入口与范围

- [NavierStokes/ComparatorSolution.lean](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/NavierStokes/ComparatorSolution.lean)：
  `NavierStokes.Comparator.navier_stokes_breakdown_R3` 与
  `NavierStokes.Comparator.navier_stokes_breakdown_periodic`。
  陈述对每个正黏性参数给出光滑初值及外力，分别处理全空间和周期情形；
  全空间陈述含动能一致有界条件。检索时须保留这些条件。
- [Euler/Solution.lean](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/Euler/Solution.lean)：
  `Euler.euler_breakdown_R3` 与
  `Euler.exists_compact_smooth_euler_singularity`。
  后者涉及无外力、光滑紧支撑无散初值、有限最大寿命、速度的 C1 范数
  上极限及涡量范数时间积分发散。
- [README](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/README.md)
  解释数学范围；
  [ComparatorChallenges](https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/ComparatorChallenges)
  提供独立陈述比对的入口。

## 检索与验证记录

2026-09-10：从用户提供的 URL 出发，以 GitHub API 核对官方 owner、
默认分支、提交及许可证；按固定提交读取 README、版本文件、
`formalization.yaml` 和上述两个证明入口文件。

上游 [formalization.yaml](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/formalization.yaml)
自报四个主要结果的 `sorry_count: 0`、公理闭包为
`propext`、`Classical.choice`、`Quot.sound`，评审状态为 `self-assessed`。
本次核对了来源与源码定位，未重跑上游构建或 Comparator；上述验证状态
是上游报告，不是本仓新增的 kernel 验证或冻结记录。
