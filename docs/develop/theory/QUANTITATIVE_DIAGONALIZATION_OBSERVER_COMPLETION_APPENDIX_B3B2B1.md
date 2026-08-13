# 《投影与完成下的对角化》附录 B3B2B1
## Li–Cayley 无向深度的局部谐波放大
### Local Harmonic Amplification of Li–Cayley Unsigned Depth

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B3B2A](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B3B2A.md)。本文只证明单个镜像轨道的局部结论，不处理完整 Li 系数。

---

## 1. 相位复现

## 引理 B3B2B1.1

对任意 \(\theta\in\mathbb R\)，存在严格递增整数序列 \(n_k\to\infty\)，使
\[
\boxed{\cos(n_k\theta)\to1.}
\]

### 证明

令 \(\alpha=\theta/(2\pi)\)。若 \(\alpha\) 有理，取分母的正整数倍。若 \(\alpha\) 无理，由 Dirichlet 有理逼近，存在无界整数子序列使 \(n_k\alpha\) 模一趋于零，故 \(n_k\theta\) 模 \(2\pi\) 趋于零。 \(\square\)

---

## 2. 局部指数放大

沿用
\[
L_n(\rho)
=
4-4\cosh(n\beta)\cos(n\theta),
\]
其中
\[
C(\rho)=e^{\beta+i\theta}.
\]

## 定理 B3B2B1.2

若 \(|\beta|>0\)，则存在 \(n_k\to\infty\)，使
\[
\boxed{L_{n_k}(\rho)\to-\infty.}
\]
并且
\[
\boxed{
\frac{L_{n_k}(\rho)}{\cosh(n_k|\beta|)}\to-4.}
\]

### 证明

由引理 B3B2B1.1 取 \(n_k\) 使 \(\cos(n_k\theta)\to1\)。因 \(|\beta|>0\)，
\[
\cosh(n_k|\beta|)\to\infty.
\]
又 \(\cosh\) 为偶函数，所以
\[
\frac{L_{n_k}}{\cosh(n_k|\beta|)}
=
\frac4{\cosh(n_k|\beta|)}
-4\cos(n_k\theta)\to-4.
\]
\(\square\)

被放大的不是侧别符号 \(\operatorname{sgn}\beta\)，而是函数方程镜像商中保留的连续深度 \(|\beta|\)。

## 定理 B3B2B1.3（给定放大阈值的精确阶数）

设 \(|\beta|>0\)、\(H\ge1\)。定义
\[
t_H(\beta)
=
\frac{\operatorname{arcosh}(H)}{|\beta|}
\]
和最小整数阈值
\[
n_H(\beta)
=
\left\lceil
\frac{\operatorname{arcosh}(H)}{|\beta|}
\right\rceil.
\]
则对任意实数 \(t\ge0\)，
\[
\boxed{
\cosh(t|\beta|)\ge H
\iff
t\ge t_H(\beta).}
\]
并且对任意整数 \(n\ge0\)，
\[
\boxed{
\cosh(n|\beta|)\ge H
\iff
n\ge n_H(\beta).}
\]

### 证明

函数 \(\cosh\) 在 \([0,\infty)\) 上严格递增，且
\[
\operatorname{arcosh}:[1,\infty)\to[0,\infty)
\]
是其反函数。由于 \(t|\beta|\ge0\)，有
\[
\cosh(t|\beta|)\ge H
\iff
t|\beta|\ge\operatorname{arcosh}(H).
\]
除以正数 \(|\beta|\) 得第一式。

若 \(n\) 为整数，则第一式给出
\[
\cosh(n|\beta|)\ge H
\iff
n\ge t_H(\beta).
\]
整数 \(n\) 满足右式，当且仅当
\[
n\ge\lceil t_H(\beta)\rceil=n_H(\beta).
\]
\(\square\)

## 推论 B3B2B1.4（小深度下的严格倒数尺度）

固定 \(H>1\)。则
\[
\boxed{
\frac{\operatorname{arcosh}(H)}{|\beta|}
\le
n_H(\beta)
<
rac{\operatorname{arcosh}(H)}{|\beta|}+1.}
\]
因此当 \(|\beta|\downarrow0\) 时，
\[
\boxed{
|eta|\,n_H(eta)
\longrightarrow
\operatorname{arcosh}(H).}
\]

### 证明

第一组不等式是上取整函数的标准性质
\[
x\le\lceil x\rceil<x+1.
\]
乘以 \(|\beta|\) 得
\[
\operatorname{arcosh}(H)
\le
|eta|n_H(eta)
<
\operatorname{arcosh}(H)+|eta|.
\]
令 \(|\beta|\downarrow0\)，由夹逼定理得到极限。 \(\square\)

所以“检测阶与深度倒数同阶”不再只是启发式：对任意固定双曲放大阈值 \(H>1\)，其最小整数阶具有精确首项
\[
n_H(\beta)
\sim
\frac{\operatorname{arcosh}(H)}{|\beta|}.
\]
该结论仍只控制径向双曲因子；若还要求具体 Li 贡献为负并达到指定幅度，则必须同时控制相位复现和其他零点贡献。

---

## 3. 结论

1. 任意非零 Li–Cayley 无向深度都可被整数谐波子序列放大；
2. 放大率由 \(\cosh(n|\beta|)\) 控制；
3. 达到固定双曲阈值 \(H\) 的最小整数阶精确为
   \[
   \left\lceil\operatorname{arcosh}(H)/|\beta|\right\rceil;
   \]
4. 该结论不区分临界线左侧与右侧；
5. 它是单轨道局部结论，不自动推出完整 Li 系数变负。

---

## 形式化状态

B3B2B1.1—B3B2B1.4 均为完整纸面证明，尚未新增为 Lean 真源。
