# 群作用与算术不变量：从局部换位到轨道守恒

## 动机

项目已有的“角色不变性”文档把全群不变性作为结构假说，但缺少一条可复用的证明核：为什么检查所有局部换位就足够，以及这种动态对称如何产生可检验的数值约束。本批形式化补上这条桥。

## 形式化核

对有限指标集 (I) 和统计量 (f:I\to A)，定义

\[
  \operatorname{SwapInvariant}(f) :\iff
  \forall \sigma\text{ 为换位},\ \forall i,\ f(\sigma i)=f(i).
\]

先构造保持 (f) 的置换子群

\[
  H_f=\{\sigma\in\operatorname{Sym}(I):\forall i,\ f(\sigma i)=f(i)\}.
\]

Mathlib 的 `Equiv.Perm.closure_isSwap` 给出有限对称群由换位生成，所以换位假设推出 (H_f=\operatorname{Sym}(I))。若 (I) 非空，交换固定基点与任意点的换位立即推出 (f) 为常数。

第二条核处理真正的动态作用。若群 (G) 作用于 (X)，且自然统计量满足

\[
  f(g\cdot y)=f(y),
\]

那么在有限轨道 (G\cdot x) 上每一点都可写成 (g\cdot x)，故

\[
  \sum_{y\in G\cdot x}f(y)=|G\cdot x|\,f(x),
  \qquad |G\cdot x|\mid\sum_{y\in G\cdot x}f(y).
\]

这不是把一个已有声明重新绑定：它把群生成、动态轨道和自然数整除放在同一条内核证明中。

## Aha moment：数值反证接口

对 `Fin n` 的全换位对称自然统计量，形式化得到

\[
  n\mid\sum_{i<n}f(i).
\]

因此任何候选计数若给出不被 (n) 整除的总和，就不可能来自所声称的全角色对称。这个判据可以直接用于有限 residue 类计数、Fibonacci/Pisano 周期块以及其它有限状态轨道：先验证动作下的不变量，再用整除性筛掉错误的全局猜想。

## 边界

空指标集没有基点，故“统计量为常数”的结论明确要求非空。轨道定理只要求给定轨道有 `Fintype`，不假设作用自由；稳定子可以很大，整除因子相应变小。这里没有把具体 Fibonacci 或 Pisano 周期强行塞进抽象定理，后续实例应先检索并复用相应的周期库。

## Lean 锚点

- `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_permutation_invariant`
- `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_is_constant`
- `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_eq_card_mul_value`
- `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_dvd_card`
- `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_sum_dvd_card`
- `D5/S3/Arith/GroupActionInvariantStatistic.fin_sum_dvd_card`
