# 《投影与完成下的对角化》附录 B1Z
## 周期核可见性、瞬态盲区与有限动力学 ζ
### Periodic-Core Visibility, Transient Blindness, and the Finite Dynamical Zeta Function

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B1](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B1.md)。B1 对有限置换证明了“幂固定点谱—循环谱—对角逃逸谱”的等价。本附录推广到任意有限自映射，并证明一条严格边界：固定点敏感的对角逃逸统计只能读取周期核，不能读取进入周期以前的瞬态树。
>
> 本文中的 \(\zeta_\tau\) 是有限动力系统的 Artin–Mazur 型形式幂级数，不是 Riemann zeta 函数。

---

## 摘要

设有限集合 \(Y\) 上有任意自映射 \(\tau:Y\to Y\)。由于 \(Y\) 有限，存在 \(N\) 使下降链
\[
Y\supseteq\tau(Y)\supseteq\tau^2(Y)\supseteq\cdots
\]
稳定。稳定像
\[
P_\tau=\tau^N(Y)
\]
称为周期核。本文证明 \(\tau|_{P_\tau}\) 是置换，而且对全部 \(r\ge1\)，
\[
\operatorname{Fix}(\tau^r)
=
\operatorname{Fix}((\tau|_{P_\tau})^r).
\]
因此固定点敏感的逃逸数量
\[
N_r=(q^n-|\operatorname{Fix}(\tau^r)|)^n
\]
只依赖周期核的循环结构；所有流入周期的瞬态树在该统计中不可见。

本文随后定义有限动力学 zeta
\[
\zeta_\tau(t)
=
\exp\!\left(
\sum_{r\ge1}
\frac{F_r}{r}t^r
\right),
\qquad
F_r=|\operatorname{Fix}(\tau^r)|,
\]
并证明
\[
\boxed{
\zeta_\tau(t)
=
\prod_{d\ge1}(1-t^d)^{-c_d},}
\]
其中 \(c_d\) 为周期核中长度 \(d\) 的循环数。若 \(U_\tau\) 是周期核上的置换算子，则
\[
\boxed{
\zeta_\tau(t)=\det(I-tU_\tau)^{-1}.}
\]
所以在已知 \(q,n\ge1\) 时，完整逃逸谱、幂固定点谱、循环谱、有限动力学 zeta 和置换特征行列式互相确定；但它们共同忽略瞬态树。

---

# 1. 有限自映射的稳定像

设 \(Y\) 为有限集合，\(\tau:Y\to Y\)。定义
\[
Y_k=\tau^k(Y).
\]
则
\[
Y_{k+1}\subseteq Y_k.
\]

## 定理 B1Z.1（稳定像存在）

存在 \(N\ge0\)，使
\[
Y_N=Y_{N+1}=Y_{N+2}=\cdots.
\]

### 证明

基数序列
\[
|Y_0|\ge|Y_1|\ge|Y_2|\ge\cdots
\]
是非负整数的下降序列，故最终恒定。若
\[
|Y_N|=|Y_{N+1}|
\]
且 \(Y_{N+1}\subseteq Y_N\)，则两集合相等。之后反复作用 \(\tau\) 保持相等。 \(\square\)

定义周期核
\[
P_\tau=Y_N
\]
，其中 \(N\) 取任一稳定指标。

## 定理 B1Z.2（周期核上的限制是置换）

\[
\tau|_{P_\tau}:P_\tau\to P_\tau
\]
是双射。

### 证明

稳定性给出
\[
\tau(P_\tau)=P_\tau,
\]
所以限制映射满射。有限集合上的满射必为单射。 \(\square\)

## 定理 B1Z.3（周期核恰由周期点组成）

对 \(y\in Y\)，下列条件等价：

1. \(y\in P_\tau\)；
2. 存在 \(r\ge1\) 使 \(\tau^r(y)=y\)。

### 证明

若 \(y\in P_\tau\)，由于 \(\tau|_{P_\tau}\) 是有限置换，\(y\) 位于其某个有限循环上，因此为周期点。

反之，若 \(\tau^r(y)=y\)，则对任意 \(k\ge0\)，可取整数 \(m\) 使 \(mr\ge k\)。有
\[
y=\tau^{mr}(y)\in\tau^k(Y)=Y_k.
\]
所以 \(y\) 属于全部 \(Y_k\)，特别属于稳定像 \(P_\tau\)。 \(\square\)

---

# 2. 幂固定点只读取周期核

## 定理 B1Z.4（固定点谱的周期核约化）

对每个 \(r\ge1\)，
\[
\boxed{
\operatorname{Fix}(\tau^r)
=
\operatorname{Fix}((\tau|_{P_\tau})^r).}
\]

### 证明

若 \(\tau^r(y)=y\)，定理 B1Z.3 给出 \(y\in P_\tau\)，所以它属于右侧。反向包含显然，因为限制映射与原映射在 \(P_\tau\) 上一致。 \(\square\)

## 推论 B1Z.5（逃逸谱的瞬态盲区）

设 \(|A|=n\ge1\)、\(|Y|=q\)，并以 \(\tau^r\) 作为值扭曲。则第 \(r\) 阶逃逸表数量
\[
N_r=(q^n-|\operatorname{Fix}(\tau^r)|)^n
\]
只依赖周期核置换 \(\tau|_{P_\tau}\) 的循环类型。

### 证明

由定理 B1Z.4，幂固定点数完全由周期核限制给出，再代入仓库既有逃逸计数。 \(\square\)

## 定理 B1Z.6（相同周期核谱给出相同逃逸谱）

设 \(\tau,\sigma:Y\to Y\) 为同一有限值集上的两个自映射。若它们的周期核具有相同循环长度计数，则
\[
\boxed{N_r(\tau)=N_r(\sigma)}
\]
对全部 \(r\ge1\) 成立，即使它们的瞬态树完全不同。

### 证明

相同循环计数由附录 B1 的幂固定点公式给出相同 \(F_r\)。两映射的 \(q,n\) 相同，故逃逸公式相同。 \(\square\)

## 例 B1Z.7（不可辨认的瞬态结构）

在集合
\[
Y=\{0,1,2,3\}
\]
上定义两个映射：
\[
\tau:\quad0\mapsto0,\ 1\mapsto0,\ 2\mapsto1,\ 3\mapsto2,
\]
以及
\[
\sigma:\quad0\mapsto0,\ 1\mapsto0,\ 2\mapsto0,\ 3\mapsto0.
\]
二者的周期核都只有固定点 \(0\)，所以对全部 \(r\ge1\)，
\[
|\operatorname{Fix}(\tau^r)|
=
|\operatorname{Fix}(\sigma^r)|=1.
\]
但 \(\tau\) 的瞬态部分是一条长度三的链，\(\sigma\) 则是三个点直接流入固定点。它们的全部固定点敏感逃逸统计仍完全相同。

因此逃逸谱不是有限自映射的完整同构不变量；它是周期核的不变量。

---

# 3. 有限动力学 zeta

令
\[
F_r=|\operatorname{Fix}(\tau^r)|.
\]
在形式幂级数环 \(\mathbb Q[[t]]\) 中定义
\[
\boxed{
\zeta_\tau(t)
=
\exp\!\left(
\sum_{r=1}^{\infty}
\frac{F_r}{r}t^r
\right).}
\]

设周期核置换中长度 \(d\) 的循环数为 \(c_d\)。

## 定理 B1Z.8（Euler 乘积型循环公式）

\[
\boxed{
\zeta_\tau(t)
=
\prod_{d\ge1}(1-t^d)^{-c_d}.}
\]

### 证明

附录 B1 给出
\[
F_r=\sum_{d\mid r}d\,c_d.
\]
所以
\[
\begin{aligned}
\sum_{r\ge1}\frac{F_r}{r}t^r
&=
\sum_{r\ge1}\frac1r
\sum_{d\mid r}d\,c_d\,t^r\\
&=
\sum_{d\ge1}c_d
\sum_{m\ge1}\frac{t^{dm}}m\\
&=
-\sum_{d\ge1}c_d\log(1-t^d).
\end{aligned}
\]
指数化得到所述乘积。由于只有有限多个 \(c_d\) 非零，右侧是有限个有理因子的乘积。 \(\square\)

这是一种真正的“周期不可约对象—整体 zeta”关系：每个原始循环贡献一个 \((1-t^d)^{-1}\) 因子。

## 推论 B1Z.9（zeta 只依赖周期核）

若两个有限自映射具有相同周期核循环谱，则它们的有限动力学 zeta 相同，而不论瞬态树如何。

---

# 4. 置换行列式公式

令 \(P_\tau\) 为周期核，取复向量空间
\[
V=\mathbb C^{P_\tau}.
\]
令置换算子 \(U_\tau\) 作用于基向量为
\[
U_\tau e_y=e_{\tau(y)}.
\]

## 引理 B1Z.10（单循环行列式）

若 \(U_d\) 是长度 \(d\) 循环的置换矩阵，则
\[
\boxed{
\det(I-tU_d)=1-t^d.}
\]

### 证明

长度 \(d\) 循环的特征值恰为全部 \(d\) 次单位根 \(\omega_d^k\)。因此
\[
\det(I-tU_d)
=
\prod_{k=0}^{d-1}(1-t\omega_d^k).
\]
多项式恒等式
\[
\prod_{k=0}^{d-1}(x-\omega_d^k)=x^d-1
\]
取 \(x=t^{-1}\) 并乘以 \(t^d\)，得到
\[
\prod_k(1-t\omega_d^k)=1-t^d.
\]
该式作为多项式恒等式在 \(t=0\) 也成立。 \(\square\)

## 定理 B1Z.11（有限动力学 zeta 的行列式表示）

\[
\boxed{
\zeta_\tau(t)
=
\det(I-tU_\tau)^{-1}.}
\]

### 证明

按循环分解，\(U_\tau\) 是各循环置换矩阵的块对角和。由引理 B1Z.10，
\[
\det(I-tU_\tau)
=
\prod_d(1-t^d)^{c_d}.
\]
取倒数并使用定理 B1Z.8。 \(\square\)

## 推论 B1Z.12（逃逸谱恢复有限动力学 zeta）

在 \(q,n\ge1\) 已知时，完整逃逸谱 \((N_r)_{r\ge1}\) 唯一确定：

1. 幂固定点谱 \((F_r)\)；
2. 周期循环谱 \((c_d)\)；
3. 有限动力学 zeta \(\zeta_\tau(t)\)；
4. 置换行列式 \(\det(I-tU_\tau)\)。

### 证明

由
\[
N_r=(q^n-F_r)^n
\]
和 \(n\ge1\)，取唯一非负整数 \(n\) 次根恢复 \(F_r\)。附录 B1 的 Möbius 反演恢复 \(c_d\)。定理 B1Z.8 与 B1Z.11 给出后两项。 \(\square\)

这里也修正了附录 B1 中循环恢复结论的隐含边界：必须假设地址数 \(n\ge1\)；当 \(n=0\) 时，全部函数空间退化，逃逸计数不能承载固定点信息。

---

# 5. 迹公式

## 定理 B1Z.13（固定点数等于置换迹）

\[
\boxed{
F_r=\operatorname{Tr}(U_\tau^r).}
\]

### 证明

在标准基中，置换矩阵 \(U_\tau^r\) 的第 \(y\) 个对角元为一，当且仅当 \(\tau^r(y)=y\)，否则为零。对角元求和即为固定点数。 \(\square\)

因此
\[
\boxed{
\log\zeta_\tau(t)
=
\sum_{r\ge1}
\frac{\operatorname{Tr}(U_\tau^r)}r t^r.}
\]

这给出一个有限模型中的完整链：
\[
\boxed{
\text{周期点}
\longleftrightarrow
\text{算子幂迹}
\longleftrightarrow
\text{行列式}
\longleftrightarrow
\zeta.}
\]

该链与解析数论中的“素数/闭轨—迹—行列式—零点”具有结构相似性，但本文没有声称有限动力学 zeta 等于 Riemann zeta。

---

# 6. 可见性边界

## 定理 B1Z.14（逃逸谱的精确可见内容）

在有限值集大小 \(q\) 与非空地址数 \(n\) 固定时，固定点敏感对角逃逸谱所包含的全部动力学信息，恰为周期核置换的循环谱。

### 证明

一方面，推论 B1Z.12 表明逃逸谱恢复循环谱。另一方面，定理 B1Z.6 表明任何具有同一周期循环谱、但瞬态树不同的映射都给出同一逃逸谱。因此它不包含比循环谱更多的有限自映射信息。 \(\square\)

所以这套定量对角统计具有清楚的“界面”：

- 能看见哪些周期、周期长度及其重数；
- 看不见一个点在进入周期前走了多少步；
- 看不见瞬态树的分支形状与入度结构。

若希望对角理论同时读取瞬态结构，必须引入不同的探针，例如首次返回时间、前像计数、迁移核或整个函数图，而不能只依赖 \(\operatorname{Fix}(\tau^r)\)。

---

# 7. 闭合结论

### 结论 B1Z-A

任意有限自映射都分成周期核与流入该核的瞬态树；稳定像上的限制是置换。

### 结论 B1Z-B

对角逃逸谱只读取周期核：
\[
\boxed{
N_r=(q^n-|\operatorname{Fix}(\tau^r)|)^n.}
\]
瞬态树对全部 \(N_r\) 完全不可见。

### 结论 B1Z-C

完整逃逸谱在 \(q,n\ge1\) 已知时恢复周期循环谱，也恢复有限动力学 zeta：
\[
\boxed{
\zeta_\tau(t)
=
\prod_d(1-t^d)^{-c_d}.}
\]

### 结论 B1Z-D

周期核置换满足
\[
\boxed{
\zeta_\tau(t)
=
\det(I-tU_\tau)^{-1},
\qquad
F_r=\operatorname{Tr}(U_\tau^r).}
\]

### 结论 B1Z-E

“对角化可恢复动力学”必须加限定：它恢复的是周期谱，而不是完整有限函数图。该盲区是结构性的，不是证明技术不足。

---

## 形式化状态

B1Z.1—B1Z.14 均为完整纸面证明，尚未新增为 Lean 真源。其未来形式化可复用仓库既有固定点敏感逃逸计数、有限置换、矩阵迹与行列式基础。
