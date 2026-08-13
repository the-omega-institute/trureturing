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

## 推论 B3B2B1.3（自然阶尺度）

当 \(|\beta|\ll1\) 时，使双曲因子显著离开常数量级需要
\[
n|\beta|\gtrsim1.
\]
因此局部自然阶尺度为
\[
\boxed{n\asymp|\beta|^{-1}.}
\]

这只是局部尺度估计，不含相位对齐成本，也不含其他零点贡献。

---

## 3. 结论

1. 任意非零 Li–Cayley 无向深度都可被整数谐波子序列放大；
2. 放大率由 \(\cosh(n|\beta|)\) 控制；
3. 该结论不区分临界线左侧与右侧；
4. 它是单轨道局部结论，不自动推出完整 Li 系数变负。

---

## 形式化状态

B3B2B1.1—B3B2B1.3 均为完整纸面证明，尚未新增为 Lean 真源。
