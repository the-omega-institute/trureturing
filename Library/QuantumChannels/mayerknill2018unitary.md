---
bibkey: mayerknill2018unitary
authors: Karl Mayer and Emanuel Knill
year: 2018
title: Quantum process fidelity bounds from sets of input states
doi: 10.1103/PhysRevA.98.052326
url: https://arxiv.org/html/1805.04491v1
claim: "Theorem 1: a spanning family of pure input states identifies a unitary channel exactly when its nonorthogonality graph is connected."
strata_touched:
  - D5/S3/Quantum/Reduction/ProbeComponentRigidity
  - D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore
  - D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition
license: citation-only
triage: anchor
---

# Quantum process fidelity bounds from sets of input states

Theorem 1: a spanning family of pure input states identifies a unitary channel exactly when its nonorthogonality graph is connected.

The finite complex-matrix results use completely positive trace-preserving maps and all density inputs.

## Verified locator

DOI: 10.1103/PhysRevA.98.052326

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

## Infidelity transition

Mayer and Knill, arXiv:1805.04491v1, p. 4, write:

> “First, note that the lowest order term in the lower bound is of order $\sqrt{\epsilon}$. This scaling behavior matches our empirical observations from numerically solving the SDP given by Eq. (5). However, we find that for many sets of input states containing more than $d$ states, the $O(\sqrt{\epsilon})$ term vanishes and the process infidelity becomes linear in $\epsilon$ for small error. Examples include the basis states plus the totally rotated state, as well as the symmetric POVM states defined in the next section. The transition from sub-linear to linear scaling is not explained by the proof of Thm. 2 and thus remains an open question.”

The transition classification concerns a fixed finite unit spanning family with connected
nonorthogonality graph, equal input-error bounds and dimension at least two. The
line-preserving obstruction space consists of matrices $A$ satisfying
$(I-|\psi_k\rangle\langle\psi_k|)A\psi_k=0$ for every input. Scalar obstruction
space gives linear infidelity scaling; a nonscalar obstruction gives square-root
scaling. The constants depend on the family. Symmetric-POVM optimality and
uniform constants for degenerating families remain separate questions.

### Input and fidelity definitions

“Let \(\{\ket{x}\}\) be an orthonormal basis for \(\mathcal{H}\) and let \(\ket{\phi}=\frac{1}{\sqrt{d}}\sum_{x=0}^{d-1}\ket{x}\ket{x}\) be a maximally entangled bipartite state. Then the *Choi operator* is given by \(\chi=(I\otimes\mathcal{E})(\hat\phi)\).”

“\(F(\mathcal{E},U)=\bra{\phi}(I\otimes U^{\dag})\chi (I\otimes U)\ket{\phi}=\Trace{(\chi\chi_U)}\), where \(\chi_U\) is the Choi operator for the unitary \(U\).”

“Let \(\{\ket{\psi_k}\}_{k=1}^N\) be an indexed family of pure states in \(\mathcal{H}\), fix \(\boldsymbol{\epsilon}=(\epsilon_1,\ldots,\epsilon_N)\) with \(\epsilon_k\geq 0\), and let \(\mathcal{C}(\boldsymbol{\epsilon})\) be the convex set of CPTP maps \(\mathcal{E}\) such that for all \(k\), \(\bra{\psi_k}\mathcal{E}(\hat{\psi}_k)\ket{\psi_k} \ge 1-\epsilon_k\). We refer to \(\{\ket{\psi_k}\}\) as the set of input states. We wish to find \(F_{\mathrm{min}}(\boldsymbol{\epsilon})=\min_{\mathcal{E}\in\mathcal{C}(\boldsymbol{\epsilon})}F(\mathcal{E})\). Note that the minimum is achieved by compactness of the feasible set.”
