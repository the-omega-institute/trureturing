# 《投影与完成下的对角化》附录 B3A
## CRT 素数账本、循环平移与有限谐波角色
### CRT Prime Ledgers, Cyclic Translation, and Finite Harmonic Characters

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B1](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B1.md) 与 [附录 B2A](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B2A.md)。本文证明：欧几里得 \(+1\) 构造不是逐坐标布尔取反，而是整个中国剩余余空间中的生成循环平移；布尔取反正是该结构在模 \(2\) 时的最小特例。

---

## 摘要

对有限素数账本 \(S\)，令
\[
M=\prod_{p\in S}p,
\qquad
R_S=\prod_{p\in S}\mathbb Z/p\mathbb Z.
\]
本文证明中国剩余映射
\[
\Gamma_S:\mathbb Z/M\mathbb Z\to R_S
\]
把加一平移共轭为
\[
\mathbf x\mapsto\mathbf x+\mathbf1.
\]
该平移是长度 \(M\) 的单循环。欧几里得步
\[
M\longmapsto M+1
\]
在剩余空间中正是
\[
\mathbf0\longmapsto\mathbf1,
\]
从而同时离开每个已有素数的零剩余超平面。随后因子分解从该逃逸余类中提取账本外的素因子。

本文进一步证明有限加法角色
\[
\chi_{\mathbf k}(\mathbf x)
=
\prod_{p\in S}
\exp\!\left(\frac{2\pi i k_px_p}{p}\right)
\]
将 \(+\mathbf1\) 平移对角化为单位根相位。完整角色族分离全部 CRT 余量，而零角色只保留商平均。由此，素数账本逃逸获得精确谐波表达。

---

# 1. 中国剩余坐标

设 \(S\) 为非空有限素数集合，定义
\[
M=\prod_{p\in S}p,
\qquad
R_S=\prod_{p\in S}\mathbb Z/p\mathbb Z.
\]
定义
\[
\Gamma_S:\mathbb Z/M\mathbb Z\to R_S,
\qquad
[x]_M\mapsto([x]_p)_{p\in S}.
\]

## 定理 B3A.1（CRT 加法同构）

\(\Gamma_S\) 是加法群同构。

### 证明

它显然良定义并保持加法。若
\[
\Gamma_S([x])=\Gamma_S([y]),
\]
则每个 \(p\in S\) 都整除 \(x-y\)。这些素数两两互素，所以其乘积 \(M\) 整除 \(x-y\)，故 \([x]_M=[y]_M\)。因此 \(\Gamma_S\) 单射。

定义域基数为 \(M\)，值域基数为
\[
\prod_{p\in S}p=M.
\]
有限集合间单射且基数相同，故为双射。 \(\square\)

## 定理 B3A.2（加一平移的共轭）

\[
\boxed{
\Gamma_S([x+1]_M)
=
\Gamma_S([x]_M)+\mathbf1.}
\]

### 证明

逐坐标有
\[
[x+1]_p=[x]_p+1.
\]
\(\square\)

## 推论 B3A.3（\(+\mathbf1\) 是单循环生成元）

平移
\[
T(\mathbf x)=\mathbf x+\mathbf1
\]
在 \(R_S\) 上形成一个长度为 \(M\) 的循环，遍历全部余量。

### 证明

在 \(\mathbb Z/M\mathbb Z\) 中，\([1]_M\) 的加法阶为 \(M\)。由定理 B3A.2，共轭平移具有同样轨道结构。 \(\square\)

因此 CRT 余空间不是许多互不相干的素数坐标；对角向量 \(\mathbf1\) 生成整个乘积群。

---

# 2. 布尔取反是模二加一

在 \(\mathbb Z/2\mathbb Z\) 中，
\[
0+1=1,
\qquad
1+1=0.
\]

## 命题 B3A.4（布尔补是循环平移）

把 `false` 识别为 \(0\)、`true` 识别为 \(1\)，则布尔取反恰为
\[
\boxed{x\mapsto x+1\pmod2.}
\]

### 证明

检查两个元素即可。 \(\square\)

注意：模二算术负号 \(x\mapsto-x\) 是恒等映射，因为 \(-1=1\pmod2\)。所以布尔“取反”对应的是唯一非零平移，而不是算术乘以 \(-1\)。

一般模 \(m\) 的自然推广不是二值补，而是循环后继
\[
x\mapsto x+1\pmod m.
\]

---

# 3. 欧几里得步的余空间解释

## 定理 B3A.5（零余量到单位余量）

\[
\boxed{
\Gamma_S([M]_M)=\mathbf0,
\qquad
\Gamma_S([M+1]_M)=\mathbf1.}
\]

### 证明

\(M\) 被每个 \(p\in S\) 整除，所以全部坐标为零。加一后，每个坐标为一。 \(\square\)

## 推论 B3A.6（同时整除逃逸）

对全部 \(p\in S\)，
\[
\boxed{p\nmid M+1.}
\]

### 证明

\([M+1]_p=1\neq0\)。 \(\square\)

## 定理 B3A.7（账本外素因子）

若素数 \(q\mid M+1\)，则
\[
\boxed{q\notin S.}
\]

### 证明

若 \(q\in S\)，则 \(q\mid M\) 且 \(q\mid M+1\)，于是 \(q\mid1\)，矛盾。 \(\square\)

因此严格过程是
\[
\boxed{
\text{CRT 生成平移逃逸}
+
\text{整数因子分解}
=
\text{账本外素数见证}.}
\]

对角/余量步骤产生的是一个同时避开旧素数零坐标的整数；素性来自后续不可约分解。

---

# 4. CRT 加法角色

对
\[
\mathbf k=(k_p)_{p\in S}\in R_S
\]
定义
\[
\chi_{\mathbf k}(\mathbf x)
=
\prod_{p\in S}
\exp\!\left(
\frac{2\pi i k_px_p}{p}
\right).
\]

## 定理 B3A.8（平移成为角色相位）

\[
\boxed{
\chi_{\mathbf k}(\mathbf x+\mathbf1)
=
\Omega_{\mathbf k}\chi_{\mathbf k}(\mathbf x),}
\]
其中
\[
\Omega_{\mathbf k}
=
\prod_{p\in S}
\exp\!\left(
\frac{2\pi i k_p}{p}
\right).
\]

### 证明

逐坐标展开：
\[
\begin{aligned}
\chi_{\mathbf k}(\mathbf x+\mathbf1)
&=
\prod_p
\exp\!\left(
\frac{2\pi i k_p(x_p+1)}p
\right)\\
&=
\left(\prod_pe^{2\pi i k_p/p}\right)
\left(\prod_pe^{2\pi i k_px_p/p}\right).
\end{aligned}
\]
\(\square\)

## 定理 B3A.9（角色族分离余量）

若 \(\mathbf x\neq\mathbf y\)，则存在 \(\mathbf k\) 使
\[
\chi_{\mathbf k}(\mathbf x)
eq\chi_{\mathbf k}(\mathbf y).
\]

### 证明

存在 \(p\) 使 \(x_p\neq y_p\)。取 \(k_p=1\)、其余坐标为零。角色比值为
\[
\exp\!\left(
\frac{2\pi i(x_p-y_p)}p
\right)
eq1.
\]
\(\square\)

## 推论 B3A.10（完整角色谱忠实）

映射
\[
\mathbf x\longmapsto
(\chi_{\mathbf k}(\mathbf x))_{\mathbf k\in R_S}
\]
为单射。

### 证明

由定理 B3A.9，任意两个不同余量至少被一个角色区分。 \(\square\)

零角色 \(\mathbf k=0\) 恒为一，完全看不见平移；完整角色谱则忠实记录余量。

---

# 5. 平移算子的 Fourier 对角化

令 \(\mathcal H_S=\mathbb C^{R_S}\)，定义平移算子
\[
(Uf)(\mathbf x)=f(\mathbf x+\mathbf1).
\]

## 定理 B3A.11（角色是平移本征函数）

\[
\boxed{
U\chi_{\mathbf k}
=
\Omega_{\mathbf k}\chi_{\mathbf k}.}
\]

### 证明

这正是定理 B3A.8。 \(\square\)

有限素数账本的 \(+1\) 逃逸因此可被完整对角化：每个角色只获得一个单位根相位。

## 定理 B3A.12（平移严格酉）

对标准内积
\[
\langle f,g\rangle
=
\sum_{\mathbf x\in R_S}\overline{f(\mathbf x)}g(\mathbf x),
\]
有
\[
\boxed{\|Uf\|=\|f\|.}
\]

### 证明

\(\mathbf x\mapsto\mathbf x+\mathbf1\) 是有限集合置换，所以变量替换给出
\[
\sum_{\mathbf x}|f(\mathbf x+\mathbf1)|^2
=
\sum_{\mathbf y}|f(\mathbf y)|^2.
\]
\(\square\)

这与 Li–Cayley 离线模式形成重要对比：有限 CRT 角色始终单位模；零点离开临界线后，圆周角色的解析延拓会获得指数径向权。

---

# 6. 余量超平面与同时逃逸

对每个 \(p\in S\)，定义零坐标集合
\[
H_p=\{\mathbf x\in R_S:x_p=0\}.
\]
整数 \(n\) 被 \(p\) 整除，当且仅当 \(\Gamma_S([n])\in H_p\)。

## 定理 B3A.13（单位向量避开全部旧素数超平面）

\[
\boxed{
\mathbf1\notin\bigcup_{p\in S}H_p.}
\]

### 证明

\(\mathbf1\) 的每个坐标均为 \(1\neq0\)。 \(\square\)

因此欧几里得逃逸是从交集
\[
\bigcap_{p\in S}H_p=\{\mathbf0\}
\]
经一个生成平移到达所有零超平面之外。

这一结构比“每个坐标取反”更准确：对模 \(p>2\)，\(0\mapsto1\) 只是从零纤维移动到一个指定非零余量，而不是交换两个唯一值。

---

# 7. 闭合结论

### 结论 B3A-A

布尔取反是 \(C_2\) 上的 \(+1\)；一般余结构的基本操作是循环平移，不必是对合。

### 结论 B3A-B

\[
\boxed{
\mathbb Z/M\mathbb Z
\cong
\prod_{p\in S}\mathbb Z/p\mathbb Z}
\]
把整数加一变成全部素数坐标同时加一。

### 结论 B3A-C

欧几里得 \(M+1\) 是 CRT 余空间中
\[
\boxed{\mathbf0\mapsto\mathbf1}
\]
的生成平移；账本外素数由后续因子分解提取。

### 结论 B3A-D

有限加法角色将该平移对角化为单位根相位，完整角色族忠实分离全部余量。

### 结论 B3A-E

有限素数账本中的谐波演化严格酉；任何指数放大必须来自有限余环之外的连续或解析延拓方向。

---

## 形式化状态

B3A.1—B3A.13 均为完整纸面证明，尚未新增为 Lean 真源。其 Lean 化可优先复用 Mathlib 的有限环、CRT、有限 Fourier 及仓库既有 PrimeForms/CRT 模块。
