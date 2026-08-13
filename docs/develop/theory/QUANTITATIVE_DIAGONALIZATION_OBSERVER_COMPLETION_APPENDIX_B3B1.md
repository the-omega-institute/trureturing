# 《投影与完成下的对角化》附录 B3B1
## 从有限角色到复化谐波：单位圆界面与镜像商
### From Finite Characters to Complexified Harmonics: The Unit-Circle Interface and Mirror Quotient

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B3A](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B3A.md)。B3A 中有限 CRT 角色始终单位模；本附录证明圆周角色向 \(\mathbb C^*\) 延拓后，径向坐标产生非酉指数权。

---

## 1. 有限角色是圆周角色的采样

令
\[
\mu_m=\{z\in S^1:z^m=1\},
\qquad
\omega=e^{2\pi i/m}.
\]
映射 \(r\mapsto\omega^r\) 将 \(C_m\) 与 \(\mu_m\) 同构。

## 命题 B3B1.1

有限角色
\[
\chi_n(r)=\omega^{nr}
\]
是圆周角色
\[
z\mapsto z^n
\]
在 \(\mu_m\) 上的限制。

### 证明

\[
(\omega^r)^n=\omega^{nr}.
\]
\(\square\)

有限余量相位因此是连续圆周谐波的精确有限采样。

---

## 2. 圆周角色的复化

任意 \(z\in\mathbb C^*\) 可写为
\[
z=e^{\beta+i\theta},
\qquad
\beta=\log|z|.
\]

## 定理 B3B1.2（角色复化）

\[
\boxed{z^n=e^{n\beta}e^{in\theta},}
\qquad
\boxed{|z^n|=e^{n\beta}.}
\]

### 证明

\[
(e^{\beta+i\theta})^n=e^{n(\beta+i\theta)}.
\]
\(\square\)

## 定理 B3B1.3（全模式单位模界面）

下列条件等价：

1. \(\beta=0\)；
2. \(|z|=1\)；
3. 对全部 \(n\ge1\)，\(|z^n|=1\)；
4. 对某个 \(n\ge1\)，\(|z^n|=1\)。

### 证明

由 \(|z^n|=e^{n\beta}\) 及实指数函数单射得到。 \(\square\)

## 推论 B3B1.4（离界面的指数方向）

若 \(\beta>0\)，则 \(|z^n|\to\infty\)；若 \(\beta<0\)，则 \(|z^{-n}|\to\infty\)。

所以单位圆是全部谐波同时保持酉性的唯一径向层。

---

## 3. 镜像对合

定义
\[
J(z)=\frac1{\overline z}.
\]

## 定理 B3B1.5（镜像翻转径向余量）

在对数极坐标中，
\[
\boxed{J(\beta,\theta)=(-\beta,\theta).}
\]
其固定点集恰为单位圆。

### 证明

\[
\frac1{\overline{e^{\beta+i\theta}}}
=
\frac1{e^{\beta-i\theta}}
=e^{-\beta+i\theta}.
\]
固定条件为 \(\beta=-\beta\)，即 \(\beta=0\)。 \(\square\)

## 定理 B3B1.6（镜像轨道商）

映射
\[
q(z)=
\left(
|\log|z||,
\frac z{|z|}
\right)
\]
在 \(J\)-轨道上常值并分离不同轨道，因此
\[
\boxed{
\mathbb C^*/\langle J\rangle
\cong
[0,\infty)\times S^1.}
\]

### 证明

对数极坐标给出同胚
\[
\mathbb C^*\cong\mathbb R\times S^1.
\]
在该坐标中，\(J\) 只把 \(\beta\) 变为 \(-\beta\)。实轴关于反射的商由 \(|\beta|\) 参数化，相位不变。 \(\square\)

被商掉的是“单位圆内/外”的极性，保留的是无向深度与角相位。

---

## 4. 镜像对称谐波迹

## 定理 B3B1.7

若 \(z=e^{\beta+i\theta}\)，则
\[
\boxed{
z^n+\overline z^{\,n}+z^{-n}+\overline z^{-n}
=
4\cosh(n\beta)\cos(n\theta).}
\]

### 证明

\[
z^n+\overline z^{\,n}
=2e^{n\beta}\cos(n\theta),
\]
\[
z^{-n}+\overline z^{-n}
=2e^{-n\beta}\cos(n\theta).
\]
相加并使用
\[
e^{n\beta}+e^{-n\beta}=2\cosh(n\beta).
\]
\(\square\)

## 推论 B3B1.8（谐波迹只依赖镜像商）

四项谐波迹在 \(\beta\mapsto-\beta\) 下不变，所以只依赖
\[
(|\beta|,e^{i\theta}).
\]

镜像配对删除侧别极性，却保留距界面的连续深度。

---

## 5. 有限与连续谐波字典

有限循环余量：
\[
r\in C_m
\longmapsto
\omega^{nr}\in S^1.
\]

圆周相位：
\[
e^{i\theta}
\longmapsto
e^{in\theta}.
\]

复化相位：
\[
e^{\beta+i\theta}
\longmapsto
e^{n\beta}e^{in\theta}.
\]

因此统一骨架为
\[
\boxed{
\text{余坐标}
\longrightarrow
\text{角色相位}
\longrightarrow
\text{复化谐波}.}
\]
有限余环只产生单位根；复化以后增加连续径向权。

---

## 6. 结论

### 结论 B3B1-A

有限角色是圆周角色的精确采样，不是与连续结构无关的原始离散符号。

### 结论 B3B1-B

单位圆是全部谐波同时单位模的唯一界面。

### 结论 B3B1-C

镜像 \(J(z)=1/\overline z\) 保持相位、翻转径向余量；其商保留 \((|\beta|,e^{i\theta})\)。

### 结论 B3B1-D

镜像对称谐波通过 \(\cosh(n|\beta|)\) 读取无向深度，而不读取内外侧别。

---

## 形式化状态

B3B1.1—B3B1.8 均为完整纸面证明，尚未新增为 Lean 真源。
