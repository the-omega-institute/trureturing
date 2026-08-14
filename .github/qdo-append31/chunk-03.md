## 31.5 MUB 对角塔：每个新坐标系抽出一个正交经典切片

设

\[
\mathcal B_1,\ldots,\mathcal B_m
\]

两两互相无偏。定义

\[
\boxed{
S_m
=
\bigoplus_{\ell=1}^{m}
\mathcal D_{\mathcal B_\ell}^0
\subseteq
\operatorname{Herm}_d^0,
}
\]

以及余空间

\[
\boxed{
R_m=S_m^\perp.
}
\]

由定理 31.5，直和为正交直和。因此

\[
\boxed{
\dim S_m=m(d-1),
}
\]

\[
\boxed{
\dim R_m
=
d^2-1-m(d-1)
=
(d-1)(d+1-m).
}
\]

由此定义状态无关的维数逃逸率

\[
\boxed{
r_m^{\mathrm{dim}}
=
\frac{\dim R_m}{d^2-1}
=
1-\frac{m}{d+1}.
}
\]

以及已完成比例

\[
\boxed{
v_m^{\mathrm{dim}}
=
\frac{\dim S_m}{d^2-1}
=
\frac{m}{d+1}.
}
\]

这给出一个有限量子系统中的精确“观察完成速度”：

> 每增加一个最大互补锐利坐标系，恰好增加 \(1/(d+1)\) 的线性状态自由度覆盖。

注意这不是物理时间速度，而是上下文精化深度。

对状态

\[
X_\rho=\rho-\frac Id
\]

定义状态相关余质量

\[
\boxed{
r_m^{(2)}(\rho)
=
\|P_{R_m}X_\rho\|_2^2.
}
\]

### 定理 31.8（概率偏差—余质量 Pythagoras 恒等式）

令

\[
p_{\ell j}
=
\operatorname{Tr}
\left(
\rho P_j^{\mathcal B_\ell}
\right).
\]

则

\[
\boxed{
\operatorname{Tr}(\rho^2)-\frac1d
=
\sum_{\ell=1}^{m}
\sum_{j=1}^{d}
\left(
p_{\ell j}-\frac1d
\right)^2
+
r_m^{(2)}(\rho).
}
\]

#### 证明

\(\mathbb E_{\mathcal B_\ell}X_\rho\) 是 \(X_\rho\) 在第 \(\ell\) 个无迹对角平面上的正交投影，并且

\[
\mathbb E_{\mathcal B_\ell}X_\rho
=
\sum_j
\left(
p_{\ell j}-\frac1d
\right)
P_j^{\mathcal B_\ell}.
\]

因为各对角平面彼此正交，

\[
P_{S_m}X_\rho
=
\sum_{\ell=1}^m
\mathbb E_{\mathcal B_\ell}X_\rho.
\]

又

\[
\left\|
\mathbb E_{\mathcal B_\ell}X_\rho
\right\|_2^2
=
\sum_j
\left(
p_{\ell j}-\frac1d
\right)^2.
\]

最后应用

\[
\|X_\rho\|_2^2
=
\|P_{S_m}X_\rho\|_2^2
+
\|P_{R_m}X_\rho\|_2^2.
\]

\(\square\)

所以每个新坐标系所捕获的并不是“又一份重复概率”，而是一个与此前全部 MUB 对角平面正交的二次状态分量。

### 推论 31.9（单步概率创新）

增加第 \(m+1\) 个 MUB 上下文时，

\[
\boxed{
r_m^{(2)}(\rho)
-
r_{m+1}^{(2)}(\rho)
=
\sum_j
\left(
p_{m+1,j}-\frac1d
\right)^2.
}
\]

这正是第 28 节商余塔递推

\[
R_m
=
\mathcal D_{\mathcal B_{m+1}}^0
\oplus
R_{m+1}
\]

在量子状态层析中的具体实现。

---

## 31.6 完整 MUB 集、最小层析深度与显式状态重构

任意秩一正交基测量只产生 \(d-1\) 个独立概率参数，而一般密度矩阵具有 \(d^2-1\) 个实参数。因此，仅使用非退化正交基测量时，信息完备至少需要

\[
\boxed{
\frac{d^2-1}{d-1}
=
d+1
}
\]

组测量上下文。

### 定理 31.10（完整 MUB 集达到最小基层析深度）

若存在

\[
d+1
\]

组两两 MUB

\[
\mathcal B_1,\ldots,\mathcal B_{d+1},
\]

则

\[
\boxed{
\operatorname{Herm}_d^0
=
\bigoplus_{\ell=1}^{d+1}
\mathcal D_{\mathcal B_\ell}^0.
}
\]

因此

\[
R_{d+1}=\{0\},
\]

而全部基概率唯一确定 \(\rho\)。

#### 证明

各子空间两两正交，每个维数为 \(d-1\)，总维数为

\[
(d+1)(d-1)=d^2-1,
\]

恰等于 \(\operatorname{Herm}_d^0\) 的维数。 \(\square\)

### 推论 31.11（显式 MUB 重构公式）

在完整 MUB 集下，

\[
\boxed{
\rho
=
\frac Id
+
\sum_{\ell=1}^{d+1}
\sum_{j=1}^{d}
\left(
p_{\ell j}-\frac1d
\right)
P_j^{\mathcal B_\ell}.
}
\]

#### 证明

右侧第二项正是 \(X_\rho\) 在所有正交对角平面上的分量之和。 \(\square\)

### 推论 31.12（完整 MUB 的 purity 概率恒等式）

\[
\boxed{
\sum_{\ell=1}^{d+1}
\sum_{j=1}^{d}
\left(
p_{\ell j}-\frac1d
\right)^2
=
\operatorname{Tr}(\rho^2)-\frac1d.
}
\]

等价地，

\[
\boxed{
\sum_{\ell=1}^{d+1}
\sum_{j=1}^{d}
p_{\ell j}^2
=
1+\operatorname{Tr}(\rho^2).
}
\]

所以完整 MUB 概率族不仅重构状态，还把整体 purity 精确分解为各局部经典坐标图的二次偏差总和。

当 \(d\) 为素数幂时已知存在完整 \(d+1\) 组 MUB。对于一般非素数幂维数，特别是 \(d=6\)，完整集存在性截至本文版本仍是开放问题。因此本节不能把 \(d+1\) MUB 塔假定为所有维数中的普适物理结构。在缺乏完整 MUB 时，可以使用一般信息完备 POVM、互补 frame 或非正交上下文，并以 Gram–Schur 创新代替严格正交增量。

---
