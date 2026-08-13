# 《投影与完成下的对角化》附录 B2B
## Hilbert 角色扇区与连续态的离散概率读出
### Hilbert Character Sectors and Discrete Probabilistic Readout of Continuous States

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B2A](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B2A.md)。B2A 建立代数 Fourier 投影；本附录加入 Hilbert 结构，证明这些投影给出正交扇区与归一化离散概率。
>
> 本文不宣称角色扇区自动构成物理超选择扇区；若允许跨扇区可观测量或动力学，扇区仍可相干叠加。

---

## 1. 正交 Fourier 投影

设 \(\mathcal H\) 为复 Hilbert 空间，\(T\) 为酉算子，满足
\[
T^m=I.
\]
固定
\[
\omega=e^{2\pi i/m},
\qquad
P_\ell=
\frac1m\sum_{r=0}^{m-1}\omega^{-\ell r}T^r.
\]
附录 B2A 已证明
\[
P_\ell^2=P_\ell,
\quad
P_\ell P_k=0\ (\ell\neq k),
\quad
\sum_\ell P_\ell=I,
\quad
TP_\ell=\omega^\ell P_\ell.
\]

## 定理 B2B.1（Fourier 投影自伴）

\[
\boxed{P_\ell^*=P_\ell.}
\]
因此每个 \(P_\ell\) 是正交投影。

### 证明

由 \(T^*=T^{-1}\)，
\[
\begin{aligned}
P_\ell^*
&=
\frac1m\sum_{r=0}^{m-1}
\overline{\omega^{-\ell r}}(T^r)^*\\
&=
\frac1m\sum_r\omega^{\ell r}T^{-r}.
\end{aligned}
\]
令 \(s=-r\) 模 \(m\)，则
\[
\omega^{\ell r}T^{-r}
=
\omega^{-\ell s}T^s.
\]
故总和等于 \(P_\ell\)。结合幂等性即为正交投影。 \(\square\)

## 推论 B2B.2（角色子空间两两正交）

若 \(v\in\operatorname{im}P_\ell\)、\(w\in\operatorname{im}P_k\) 且 \(\ell\neq k\)，则
\[
\langle v,w\rangle=0.
\]

### 证明

写 \(v=P_\ell v\)、\(w=P_kw\)。则
\[
\langle v,w\rangle
=
\langle P_\ell v,P_kw\rangle
=
\langle v,P_\ell P_kw\rangle=0.
\]
\(\square\)

---

## 2. 连续态的角色概率

对单位向量 \(v\in\mathcal H\)，定义
\[
p_\ell(v)=\|P_\ell v\|^2.
\]

## 定理 B2B.3（角色概率归一化）

\[
\boxed{
p_\ell(v)\ge0,
\qquad
\sum_{\ell=0}^{m-1}p_\ell(v)=1.}
\]

### 证明

非负性由范数平方得到。又由
\[
v=\sum_\ell P_\ell v
\]
及各分量正交，Pythagoras 定理给出
\[
1=\|v\|^2
=
\sum_\ell\|P_\ell v\|^2.
\]
\(\square\)

## 定理 B2B.4（循环作用只改变扇区相位）

对任意整数 \(r\)，
\[
\boxed{
P_\ell T^rv
=
\omega^{\ell r}P_\ell v,}
\]
从而
\[
\boxed{p_\ell(T^rv)=p_\ell(v).}
\]

### 证明

由 \(TP_\ell=\omega^\ell P_\ell\) 归纳得第一式。单位根不改变范数，故第二式成立。 \(\square\)

这说明有限对称在角色扇区内表现为相位，而扇区权重是对称不变量。

## 推论 B2B.5（二值偶—奇概率）

当 \(m=2\) 时，
\[
P_+=\frac{I+T}{2},
\qquad
P_- =\frac{I-T}{2},
\]
并且
\[
\boxed{
\left\|\frac{I+T}{2}v\right\|^2
+
\left\|\frac{I-T}{2}v\right\|^2
=1.}
\]

二值“正/负”结果来自偶、奇投影的概率，而不是从整个连通单位球面到 \(\{+,-\}\) 的连续确定标签。

---

## 3. 密度矩阵版本

设 \(\rho\) 为正半定、迹为一的密度算子。定义
\[
p_\ell(\rho)=\operatorname{Tr}(\rho P_\ell).
\]

## 定理 B2B.6（混态角色概率）

\[
\boxed{
p_\ell(\rho)\ge0,
\qquad
\sum_\ell p_\ell(\rho)=1.}
\]

### 证明

因 \(P_\ell\) 为正投影，\(\operatorname{Tr}(\rho P_\ell)\ge0\)。又
\[
\sum_\ell p_\ell(\rho)
=
\operatorname{Tr}\!\left(
\rho\sum_\ell P_\ell
\right)
=
\operatorname{Tr}(\rho)=1.
\]
\(\square\)

## 定理 B2B.7（对称共轭保持角色概率）

令
\[
\rho_r=T^r\rho T^{-r}.
\]
则
\[
\boxed{p_\ell(\rho_r)=p_\ell(\rho).}
\]

### 证明

因 \(P_\ell\) 是 \(T\) 的多项式，故与 \(T\) 交换。利用迹循环性：
\[
\begin{aligned}
p_\ell(\rho_r)
&=
\operatorname{Tr}(T^r\rho T^{-r}P_\ell)\\
&=
\operatorname{Tr}(\rho T^{-r}P_\ell T^r)\\
&=
\operatorname{Tr}(\rho P_\ell).
\end{aligned}
\]
\(\square\)

---

## 4. 去相干与扇区经典化

定义角色去相干通道
\[
\mathcal D_T(\rho)
=
\sum_{\ell=0}^{m-1}P_\ell\rho P_\ell.
\]

## 定理 B2B.8（角色去相干保持概率并删除跨扇区项）

1. \(p_\ell(\mathcal D_T(\rho))=p_\ell(\rho)\)；
2. 对 \(\ell\neq k\)，
   \[
   P_\ell\mathcal D_T(\rho)P_k=0.
   \]

### 证明

第一式：
\[
\begin{aligned}
\operatorname{Tr}(\mathcal D_T(\rho)P_\ell)
&=
\sum_j\operatorname{Tr}(P_j\rho P_jP_\ell)\\
&=
\operatorname{Tr}(P_\ell\rho P_\ell)\\
&=
\operatorname{Tr}(\rho P_\ell).
\end{aligned}
\]
第二式：
\[
P_\ell\mathcal D_T(\rho)P_k
=
\sum_jP_\ell P_j\rho P_jP_k=0
\]
当 \(\ell\neq k\)。 \(\square\)

去相干不是创造扇区概率，而是保留对角扇区权重并删除不同角色之间的相干项。

## 推论 B2B.9（扇区概率与扇区相干是不同信息）

两个状态可以具有完全相同的 \(p_\ell\)，却因跨扇区块
\[
P_\ell\rho P_k,
\qquad\ell\neq k
\]
不同而成为不同量子态。

### 证明

\(p_\ell\) 只读取块 \(P_\ell\rho P_\ell\) 的迹，不读取非对角块。角色去相干前后的状态便给出一般实例：概率相同，非对角块不同。 \(\square\)

因此“离散扇区”只描述一部分信息；经典化还涉及跨扇区相干是否仍可访问。

---

## 5. 扭曲对角的概率影子

设评价表取值于 Hilbert 空间，
\[
\Delta_{T^r}(E)(a)=T^rE(a,a).
\]
若每个对角值归一化，定义其角色概率
\[
p_{\ell,a}(E)=\|P_\ell E(a,a)\|^2.
\]

## 定理 B2B.10（扭曲对角保持角色概率，改变角色相位）

\[
\boxed{
p_{\ell,a}(\Delta_{T^r}E)=p_{\ell,a}(DE)}
\]
而角色振幅满足
\[
\boxed{
P_\ell\Delta_{T^r}E(a)
=
\omega^{\ell r}P_\ell DE(a).}
\]

### 证明

第二式来自附录 B2A；第一式由取范数平方得到。 \(\square\)

所以只观察扇区概率的观察者会把循环扭曲视为不可见；能够测量扇区相对相位的观察者才保留余坐标动力学。

这再次强化：
\[
\boxed{
\text{自然性、概率保持与相位忠实性是三种不同性质。}}
\]

---

## 6. 连续到离散的准确结构

设单位球或密度矩阵空间连通。不存在非恒定连续确定映射直接把每个状态送到有限标签集，但存在连续概率映射
\[
\rho\longmapsto
(p_0(\rho),\ldots,p_{m-1}(\rho))
\]
进入概率单纯形。

由此得到三层：

1. 连续状态 \(\rho\)；
2. 连续角色概率向量 \(p(\rho)\)；
3. 一次测量产生的离散标签 \(\ell\)。

若状态位于单一角色子空间，概率退化为一个顶点，结果确定；一般状态位于多个角色扇区的叠加中，结果只能概率化。

---

## 7. 边界：何时成为超选择扇区

若允许的全部可观测量 \(A\) 都满足
\[
[A,T]=0,
\]
则由 Fourier 分解，
\[
P_\ell AP_k=0
\qquad(\ell\neq k).
\]

## 命题 B2B.11（对称不变可观测量不耦合不同角色）

若 \([A,T]=0\)，则 \(A\) 保持每个 \(V_\ell\)，即
\[
AP_\ell=P_\ell A,
\]
并且
\[
P_kAP_\ell=0
\quad(k\neq\ell).
\]

### 证明

\(P_\ell\) 是 \(T\) 的多项式，所以与任何和 \(T\) 交换的 \(A\) 交换。于是
\[
P_kAP_\ell
=P_kP_\ell A=0.
\]
\(\square\)

只有在可观测代数与动力学都不能连接不同扇区时，角色标签才具有超选择意义。单独的 Fourier 分解尚不足以推出这一物理结论。

---

## 8. 闭合结论

### 结论 B2B-A

有限阶酉对称把连续 Hilbert 空间规范分解为有限正交角色扇区。

### 结论 B2B-B

离散角色概率为
\[
\boxed{p_\ell=\operatorname{Tr}(\rho P_\ell)}
\]
并连续依赖状态；单次离散结果来自概率读出。

### 结论 B2B-C

扭曲对角只改变每个扇区的相位，不改变扇区概率。

### 结论 B2B-D

去相干保留扇区概率、删除跨扇区相干；概率信息与相位信息必须分开。

### 结论 B2B-E

角色扇区只有在允许的可观测量与动力学均不耦合它们时，才成为物理超选择扇区。

---

## 形式化状态

B2B.1—B2B.11 均为完整纸面证明，尚未新增为 Lean 真源。仓库现有有限矩阵、投影、密度矩阵与退相干模块可作为未来形式化消费者。
