---
bibkey: mayerknill2018unitary
authors: Karl Mayer and Emanuel Knill
year: 2018
title: Quantum process fidelity bounds from sets of input states
doi: null
url: https://arxiv.org/html/1805.04491v1
claim: "Theorem 1: a spanning family of pure input states identifies a unitary channel exactly when its nonorthogonality graph is connected."
strata_touched:
  - D5/S3/Quantum/Reduction/ProbeComponentRigidity
license: citation-only
triage: anchor
---

# Quantum process fidelity bounds from sets of input states

Theorem 1: a spanning family of pure input states identifies a unitary channel exactly when its nonorthogonality graph is connected.

The finite complex-matrix results use completely positive trace-preserving maps and all density inputs.

## Verified locator

https://arxiv.org/html/1805.04491v1

arXiv DOI: https://doi.org/10.48550/arXiv.1805.04491

## Nondisturbance rigidity

Mayer–Knill，*Quantum Process Fidelity Bounds from Sets of Input States*，
arXiv:1805.04491v1，Theorem 1。

对纯态族 $\psi_j$，把非零内积作为图的边。若该族张成有限维空间且图连通，
一个 CPTP 映射固定全部 $|\psi_j\rangle\langle\psi_j|$ 就必须是恒等映射。
Stinespring 等距写作 $V\psi_j=\psi_j\otimes\eta_j$；内积保持使每条边的
两个环境向量相同，连通性及线性张成完成证明。

在全输入概率保持的应用中，保持探针投影概率先给该纯态输入的生存率一，
由正性、迹一推出纯态固定，再应用上述结论。对任意指标族，可抽取有限张成
探针及有限连接路径。不同非正交分量的张成空间两两正交。

[AURIC Ω 第 10–11 节](../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
使用这一既有刚性，未把它作为新的连通图定理。该文献结论不提供指定五模式
两个等待设置的矩阵指数坐标下界或误差常数 $1/102$。
