# 《投影与完成下的对角化》附录 B3B2B2
## 从局部 Li 放大到全局系数：支配条件与联合截断
### From Local Li Amplification to Global Coefficients: Dominance and Joint Truncation

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B3B2B1](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B3B2B1.md)。本文精确写出从单个离线镜像轨道的局部负增长到完整 Li 系数变负所需的余项条件，并重申固定阶截断收敛不足以支持增长探针阶数。
>
> 本文不证明所述余项条件对 Riemann zeta 成立。文中使用序关系 \(<,\ge\) 时，均显式工作于反射—共轭对称求和规范下的实 Li 系数与实轨道贡献。

---

## 1. 全局支配条件

在反射—共轭对称的求和规范下，设
\[
\lambda_n\in\mathbb R
\]
为完整 Li 系数，
\[
L_n(\rho)\in\mathbb R
\]
为一个候选离线镜像四元轨道的贡献，并定义实余项
\[
R_n=\lambda_n-L_n(\rho)\in\mathbb R.
\]
设
\[
C(\rho)=e^{\beta+i\theta},
\qquad |\beta|>0.
\]

## 定理 B3B2B2.1（全局支配条件）

若沿附录 B3B2B1 的相位复现子序列 \(n_k\)，有
\[
\boxed{
\frac{|R_{n_k}|}{\cosh(n_k|\beta|)}\to0,}
\]
则
\[
\boxed{\lambda_{n_k}<0}
\]
对充分大的 \(k\) 成立。

### 证明

附录 B3B2B1 给出
\[
\frac{L_{n_k}(\rho)}{\cosh(n_k|\beta|)}\to-4.
\]
由假设，
\[
\frac{R_{n_k}}{\cosh(n_k|\beta|)}\to0.
\]
所以在实数中
\[
\frac{\lambda_{n_k}}{\cosh(n_k|\beta|)}
=
\frac{L_{n_k}+R_{n_k}}{\cosh(n_k|\beta|)}
\to-4.
\]
因此该比值最终小于零。分母 \(\cosh(n_k|\beta|)\) 严格为正，故最终 \(\lambda_{n_k}<0\)。 \(\square\)

该定理把缺口收紧为一个明确比较：其余全部轨道和正则化项是否低于离线轨道的双曲尺度。

## 推论 B3B2B2.2（任何全阶非负理论都需要同阶抵消）

若 \(\lambda_n\ge0\) 对全部 \(n\) 成立，而存在 \(|\beta|>0\) 的离线轨道，则沿每个使该轨道相位复现的子序列，不可能有
\[
\frac{|R_{n_k}|}{\cosh(n_k|\beta|)}\to0.
\]

### 证明

否则由定理 B3B2B2.1 得到最终负 Li 系数，与全阶非负性矛盾。 \(\square\)

这不是抵消机制的构造，而是对任何潜在抵消机制必须达到的最小指数规模约束。

---

## 2. 截断与增长探针

令 \(\lambda_{n,T}\in\mathbb R\) 为高度 \(T\) 的反射—共轭对称有限截断。固定 \(n\) 时的收敛
\[
\lambda_{n,T}\to\lambda_n
\]
不自动允许选择 \(n=n(T)\to\infty\)。

## 定理 B3B2B2.3（联合一致控制允许对角选阶）

设 \(N_T\subseteq\mathbb N\)，且 \(n(T)\in N_T\)。若
\[
\boxed{
\sup_{n\in N_T}
|\lambda_{n,T}-\lambda_n|\to0,}
\]
则
\[
\boxed{
|\lambda_{n(T),T}-\lambda_{n(T)}|\to0.}
\]

### 证明

对每个 \(T\)，
\[
|\lambda_{n(T),T}-\lambda_{n(T)}|
\le
\sup_{n\in N_T}|\lambda_{n,T}-\lambda_n|.
\]
右侧趋于零。 \(\square\)

## 命题 B3B2B2.4（逐点收敛不足）

存在实阵列 \(x_{n,T}\) 与实极限 \(x_n\)，使每个固定 \(n\) 都有 \(x_{n,T}\to x_n\)，但取 \(n(T)=T+1\) 时误差恒为一。

### 证明

定义
\[
x_n=0,
\qquad
x_{n,T}=
\begin{cases}
0,&n\le T,\\
1,&n>T.
\end{cases}
\]
固定 \(n\) 后最终 \(T\ge n\)，故收敛到零；但
\[
x_{T+1,T}=1.
\]
\(\square\)

## 推论 B3B2B2.5（有限验证的逻辑边界）

任何利用高阶 Li 谐波检测高位离线深度的论证，都必须提供关于探针阶数 \(n\) 与截断高度 \(T\) 的联合余项界。逐个固定阶验证不能替代该界。

---

## 3. 素数端接口

显式公式把零点端、素数幂端、极点端与 Archimedean 端连接。附录 B3A 中有限 CRT 平移的角色严格单位模；离线 Cayley 模式则出现
\[
e^{n|\beta|}
\]
级非酉增长。

若要从素数端排除离线深度，需要在与 Li 探针匹配的测试函数类中证明：素数端和 Archimedean 端不能沿相位复现阶数提供同阶双曲抵消。

当前仓库中：

- `LiCausalTrichotomy` 使用一侧 Laguerre 因果包；
- `WeilIdentity` 的测试函数要求偶、光滑、紧支撑；
- 这两类测试函数尚未由内部定理直接识别；
- 现有显式公式输入不含 Weil 正性或 RH。

所以测试类桥接与联合余项控制是两个独立问题。

---

## 4. 闭合结论

### 结论 B3B2B2-A

局部离线轨道变成完整负 Li 系数的充分条件，是其余实贡献相对于 \(\cosh(n|\beta|)\) 为低阶。

### 结论 B3B2B2-B

若坚持全部实 Li 系数非负，则任何离线轨道都要求其余贡献在相位复现阶数上实现同阶指数抵消。

### 结论 B3B2B2-C

固定阶截断收敛不足以支持增长阶探针；必须证明 \((n,T)\) 联合一致控制。

### 结论 B3B2B2-D

真正的 RH 承重缺口不是“是否存在局部放大探针”，而是完整零点端或素数端为什么不能持续实现同阶抵消。

---

## 形式化状态

B3B2B2.1—B3B2B2.5 均为完整纸面证明，尚未新增为 Lean 真源。
