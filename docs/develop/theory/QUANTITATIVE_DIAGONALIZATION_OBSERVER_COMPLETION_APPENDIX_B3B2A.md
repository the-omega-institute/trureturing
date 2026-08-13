# 《投影与完成下的对角化》附录 B3B2A
## Li–Cayley 临界线的全谐波酉性
### Full Harmonic Unitarity on the Li–Cayley Critical Interface

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B3B1](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B3B1.md)。本文只处理 Li–Cayley 镜像轨道的局部几何，不宣称证明完整 Li 正性或 Riemann 假设。

---

## 1. Li–Cayley 径向坐标

定义
\[
C(s)=1-\frac1s.
\]
主论文已证明
\[
\Re s=\frac12
\iff
|C(s)|=1,
\]
并且镜像
\[
\mathfrak m(s)=1-\overline s
\]
满足
\[
C(\mathfrak m(s))=\frac1{\overline{C(s)}}.
\]
写
\[
C(s)=e^{\beta_C(s)+i\theta_C(s)},
\qquad
\beta_C(s)=\log|C(s)|.
\]

## 定理 B3B2A.1（临界线是全谐波酉界面）

下列条件等价：

1. \(\Re s=1/2\)；
2. \(\beta_C(s)=0\)；
3. 对全部 \(n\ge1\)，\(|C(s)^n|=1\)；
4. 对某个 \(n\ge1\)，\(|C(s)^n|=1\)。

### 证明

前两项由主论文得到。又
\[
|C(s)^n|=e^{n\beta_C(s)}.
\]
实指数函数单射，所以后两项与 \(\beta_C(s)=0\) 等价。 \(\square\)

因此，临界线不仅对应 Cayley 坐标单位模，也对应全部正阶谐波同时保持单位模。

## 定理 B3B2A.2（镜像反不变性）

\[
\boxed{
\beta_C(1-\overline s)=-\beta_C(s).}
\]

### 证明

由
\[
C(1-\overline s)=1/\overline{C(s)}
\]
取模并取对数。 \(\square\)

离线镜像点具有相反的内外极性，却具有相同无向深度 \(|\beta_C|\)。

---

## 2. 四元轨道的双曲公式

对零点候选 \(\rho\)，写
\[
C(\rho)=e^{\beta+i\theta}.
\]
其镜像四元坐标为
\[
z,
\quad
\overline z,
\quad
z^{-1},
\quad
\overline z^{-1}.
\]
定义
\[
L_n(\rho)
=
4-
\left(
z^n+\overline z^{\,n}+z^{-n}+\overline z^{-n}
\right).
\]

## 定理 B3B2A.3（双曲 Li 公式）

\[
\boxed{
L_n(\rho)
=
4-4\cosh(n\beta)\cos(n\theta).}
\]

### 证明

由
\[
z^n+\overline z^{\,n}
=2e^{n\beta}\cos(n\theta)
\]
和
\[
z^{-n}+\overline z^{-n}
=2e^{-n\beta}\cos(n\theta)
\]
相加，使用
\[
e^{n\beta}+e^{-n\beta}=2\cosh(n\beta).
\]
\(\square\)

## 推论 B3B2A.4（四元贡献不读取左右极性）

\[
\boxed{L_n(\beta,\theta)=L_n(-\beta,\theta).}
\]

### 证明

\(\cosh\) 为偶函数。 \(\square\)

函数方程镜像已经将“临界线左侧/右侧”商成同一轨道。四元探针读取的是无向深度 \(|\beta|\) 与相位 \(\theta\)。

## 推论 B3B2A.5（临界线非负）

若 \(\beta=0\)，则
\[
\boxed{
L_n
=4-4\cos(n\theta)
=8\sin^2\!\left(\frac{n\theta}{2}\right)
\ge0.}
\]

---

## 3. 镜像商中的 RH 表述

定义
\[
Q_C(\rho)
=
\left(
|\beta_C(\rho)|,
\frac{C(\rho)}{|C(\rho)|}
\right).
\]

## 命题 B3B2A.6

Riemann 假设等价于：每个非平凡零点的镜像商深度均为零，
\[
\boxed{|\beta_C(\rho)|=0.}
\]

### 证明

\[
|\beta_C|=0
\iff
\beta_C=0
\iff
|C(\rho)|=1
\iff
\Re\rho=1/2.
\]
\(\square\)

这一定理只是 RH 的坐标等价表述，不是 RH 的证明。

---

## 4. 结论

1. 临界线是全部 Cayley 谐波同时酉的唯一界面；
2. 函数方程镜像翻转径向符号并保留相位；
3. 四元 Li 贡献只依赖无向深度与相位；
4. RH 等价于全部非平凡零点的镜像商深度为零。

---

## 形式化状态

B3B2A.1—B3B2A.6 均为完整纸面证明，尚未新增为 Lean 真源。
