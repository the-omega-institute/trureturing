# 《投影与完成下的对角化》附录 B2A
## 循环 Fourier 角色与线性扇区
### Cyclic Fourier Characters and Linear Sectors

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> 本文接续 [附录 B1](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION_APPENDIX_B1.md)。B1 证明点集余坐标依赖截面；本附录证明，有限阶复线性对称具有不依赖截面的规范 Fourier 扇区。

---

## 摘要

设 \(T^m=I\)，\(\omega=e^{2\pi i/m}\)。定义
\[
P_\ell=
\frac1m\sum_{r=0}^{m-1}\omega^{-\ell r}T^r.
\]
本文证明
\[
P_\ell P_k=\delta_{\ell k}P_\ell,
\qquad
\sum_\ell P_\ell=I,
\qquad
TP_\ell=\omega^\ell P_\ell.
\]
因此连续向量空间规范地分解为有限角色子空间。对扭曲对角算子，还成立
\[
P_\ell\Delta_{T^r}
=
\omega^{\ell r}P_\ell D.
\]
不变扇区是商影子，非平凡扇区保存循环余信息。

---

# 1. 集合层角色编码

沿用自由循环作用 \(C_m\curvearrowright X\)，设
\[
\kappa(T^rx)=\kappa(x)+r,
\qquad
\omega=e^{2\pi i/m}.
\]

## 定义 B2A.1

\[
\psi_\ell(x)=\omega^{\ell\kappa(x)},
\qquad
0\le\ell<m.
\]

## 定理 B2A.2（平移成为角色相位）

\[
\boxed{
\psi_\ell(T^rx)
=
\omega^{\ell r}\psi_\ell(x).}
\]

### 证明

\[
\psi_\ell(T^rx)
=
\omega^{\ell(\kappa(x)+r)}
=
\omega^{\ell r}\psi_\ell(x).
\]
\(\square\)

零角色 \(\ell=0\) 只读取商不变量；原始角色 \(\ell=1\) 分离全部循环余量。

## 推论 B2A.3（对角角色律）

若
\[
D(E)(a)=E(a,a),
\qquad
\Delta_r(E)(a)=T^rE(a,a),
\]
则
\[
\boxed{
\Psi_{\ell,A}(\Delta_rE)
=
\omega^{\ell r}\Psi_{\ell,A}(DE).}
\]

布尔情形 \(m=2\) 时，唯一非平凡相位为 \(-1\)。

---

# 2. 有限循环 Fourier 变换

对 \(f:C_m\to\mathbb C\)，定义
\[
\widehat f(\ell)
=
\frac1m\sum_{r=0}^{m-1}f(r)\omega^{-\ell r}.
\]
令
\[
(S_tf)(r)=f(r+t).
\]

## 引理 B2A.4（单位根正交）

\[
\sum_{r=0}^{m-1}\omega^{ar}
=
\begin{cases}
m,&m\mid a,\\0,&m\nmid a.
\end{cases}
\]

### 证明

第一种情形每项为一；第二种情形由有限几何级数
\[
\frac{1-(\omega^a)^m}{1-\omega^a}=0
\]
得到。 \(\square\)

## 定理 B2A.5（平移的 Fourier 对角化）

\[
\boxed{
\widehat{S_tf}(\ell)
=
\omega^{\ell t}\widehat f(\ell).}
\]

### 证明

令 \(u=r+t\)：
\[
\begin{aligned}
\widehat{S_tf}(\ell)
&=
\frac1m\sum_rf(r+t)\omega^{-\ell r}\\
&=
\frac1m\sum_uf(u)\omega^{-\ell(u-t)}\\
&=
\omega^{\ell t}\widehat f(\ell).
\end{aligned}
\]
\(\square\)

## 推论 B2A.6（零频是盲商影子）

轨道平均
\[
\operatorname{Av}(f)=\widehat f(0)
\]
满足
\[
\operatorname{Av}(S_tf)=\operatorname{Av}(f).
\]
全部平移信息位于非零模式。

---

# 3. 复线性空间的规范 Fourier 投影

设 \(V\) 为复向量空间，线性算子 \(T:V\to V\) 满足 \(T^m=I\)。定义
\[
\boxed{
P_\ell
=
\frac1m\sum_{r=0}^{m-1}\omega^{-\ell r}T^r.}
\]

## 定理 B2A.7（Fourier 投影代数）

1. \(TP_\ell=\omega^\ell P_\ell\)；
2. \(P_\ell^2=P_\ell\)；
3. \(P_\ell P_k=0\) 当 \(\ell\neq k\)；
4. \(\sum_{\ell=0}^{m-1}P_\ell=I\)。

### 证明

指标循环给出
\[
\begin{aligned}
TP_\ell
&=
\frac1m\sum_r\omega^{-\ell r}T^{r+1}\\
&=
\omega^\ell P_\ell.
\end{aligned}
\]
因此
\[
\begin{aligned}
P_\ell P_k
&=
\frac1m\sum_r\omega^{-\ell r}T^rP_k\\
&=
\frac1m\sum_r\omega^{(k-\ell)r}P_k.
\end{aligned}
\]
由引理 B2A.4，\(k=\ell\) 时为 \(P_k\)，否则为零。最后
\[
\sum_\ell P_\ell
=
\frac1m\sum_r
\left(\sum_\ell\omega^{-\ell r}\right)T^r
=I.
\]
\(\square\)

## 定理 B2A.8（角色特征空间分解）

令
\[
V_\ell=\ker(T-\omega^\ell I).
\]
则
\[
\boxed{
\operatorname{im}P_\ell=V_\ell,
\qquad
V=\bigoplus_{\ell=0}^{m-1}V_\ell.}
\]

### 证明

\(TP_\ell=\omega^\ell P_\ell\) 给出像包含于特征空间。若 \(Tv=\omega^\ell v\)，则
\[
P_\ell v
=
\frac1m\sum_r\omega^{-\ell r}\omega^{\ell r}v=v.
\]
所以二者相等。投影两两消去且和为恒等，故为直和。 \(\square\)

## 推论 B2A.9（二值偶—奇分解）

当 \(m=2\) 时，
\[
P_+=\frac{I+T}{2},
\qquad
P_- =\frac{I-T}{2},
\]
并且
\[
v=v_++v_-,
\qquad
Tv=v_+-v_-.
\]

线性“取反”不是给整个向量贴一个正负标签，而是保持偶分量、翻转奇分量。

---

# 4. 扭曲对角的角色扇区律

设 \(E:A\times A\to V\)，并定义
\[
\Delta_{T^r}(E)(a)=T^rE(a,a).
\]

## 定理 B2A.10

\[
\boxed{
P_\ell\Delta_{T^r}(E)
=
\omega^{\ell r}P_\ell D(E)}
\]
逐坐标成立。

### 证明

由定理 B2A.7，
\[
P_\ell T^r=\omega^{\ell r}P_\ell.
\]
作用于每个对角值即可。 \(\square\)

## 推论 B2A.11（盲自然性）

\[
P_0\Delta_{T^r}(E)=P_0D(E)
\]
对全部 \(r\) 成立。只保留不变扇区会得到完美交换，但删除全部余信息。

## 定理 B2A.12（全角色读出忠实）

映射
\[
v\mapsto(P_0v,\ldots,P_{m-1}v)
\]
由
\[
v=\sum_\ell P_\ell v
\]
唯一恢复原向量。

### 证明

定理 B2A.7 已证明投影和为恒等。 \(\square\)

因此对角自然性必须与角色保真度同时审计：零频自然但盲，全频自然且忠实。

---

# 5. 一般有限置换的线性角色谱

若置换 \(\tau:Y\to Y\) 的循环长度不统一，令 \(m\) 为全部长度的最小公倍数，则其在线性化空间 \(\mathbb C^Y\) 上的置换算子满足 \(T^m=I\)。

## 定理 B2A.13（单个循环的 Fourier 特征值）

长度为 \(d\) 的循环在线性化后恰出现全部 \(d\) 次单位根，各重数一。

### 证明

在循环基 \(e_0,\ldots,e_{d-1}\) 上，\(Te_r=e_{r+1}\)。令 \(\zeta=e^{2\pi i/d}\)，则
\[
v_k=\sum_{r=0}^{d-1}\zeta^{-kr}e_r
\]
满足
\[
Tv_k=\zeta^kv_k.
\]
这些 \(v_k\) 构成离散 Fourier 基。 \(\square\)

因此点集循环谱、幂固定点谱、对角逃逸谱与线性角色谱，是同一有限扭曲的四种等价视图。

---

# 6. 结论

### 结论 B2A-A

\[
\boxed{r\in C_m\mapsto\omega^r\in S^1}
\]
把离散余量编码成连续相位。

### 结论 B2A-B

\[
\boxed{V=\bigoplus_\ell V_\ell}
\]
是有限阶连续线性对称的规范离散扇区分解，不依赖点集截面。

### 结论 B2A-C

\[
\boxed{P_\ell\Delta_{T^r}=\omega^{\ell r}P_\ell D}
\]
说明对角扭曲在每个角色扇区中只是相位乘法。

### 结论 B2A-D

不变扇区 \(P_0\) 是线性商影子；非平凡扇区共同保存被商掉的循环余信息。

---

## 形式化状态

B2A.1—B2A.13 均为完整纸面证明，尚未新增为 Lean 真源。
