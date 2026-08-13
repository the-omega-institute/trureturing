# 《投影与完成下的对角化》附录 B1
## 循环谱、商余正规形与覆盖障碍
### Cycle Spectra, Quotient–Remainder Normal Forms, and Covering Obstructions

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> **文档地位。** 本文是主论文 [《投影与完成下的对角化》](./QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md) 的证明型附录。本文新增命题均有纸面证明，但尚未因此成为 Lean 真源。
>
> **承接关系。** 主论文附录 A 已处理二值对合。本附录证明：布尔取反只是 \(C_2\) 余坐标平移；任意有限可逆扭曲都由循环轨道组成，自由 \(m\)-周期扭曲具有模 \(m\) 的商—余正规形。

---

## 摘要

设有限置换 \(\tau:Y\to Y\)。本文首先证明其幂固定点数
\[
F_r=|\operatorname{Fix}(\tau^r)|
\]
与循环长度谱互相确定：
\[
F_r=\sum_{d\mid r}d\,c_d,
\qquad
c_d=\frac1d\sum_{e\mid d}\mu(d/e)F_e.
\]
结合仓库既有的精确对角逃逸公式，得到扭曲幂的逃逸谱
\[
N_r=
\left(q^n-\sum_{d\mid r}d\,c_d\right)^n.
\]
因此，定量对角化能够编码整个有限扭曲的周期类型，而不仅判断一次扭曲是否有不动点。

随后对自由循环作用 \(C_m\curvearrowright X\)，本文证明下列数据等价：轨道商的截面、循环余坐标 \(\kappa(Tx)=\kappa(x)+1\)、以及集合正规形
\[
X\cong(X/C_m)\times C_m.
\]
在 Hausdorff 拓扑空间上，自由有限循环作用给出 \(m\) 重覆盖；全局连续余坐标存在当且仅当覆盖平凡。若 \(X\) 连通且 \(m>1\)，只能存在局部余坐标及其交叠处的 \(C_m\)-值 cocycle，而不存在全局连续离散命名。

---

# 1. 有限置换的循环谱

设 \(Y\) 为有限集合，\(\tau:Y\to Y\) 为置换。记
\[
c_d(\tau)
=
\text{长度恰为 \(d\) 的循环个数}.
\]
于是
\[
|Y|=\sum_{d\ge1}d\,c_d.
\]
对正整数 \(r\)，定义
\[
F_r(\tau)=|\operatorname{Fix}(\tau^r)|.
\]

## 定理 B1.1（幂固定点公式）

对任意 \(r\ge1\)，
\[
\boxed{
F_r(\tau)=\sum_{d\mid r}d\,c_d(\tau).
}
\]

### 证明

在长度为 \(d\) 的循环上，\(\tau^r\) 固定某个点，当且仅当沿循环前进 \(r\) 步回到原点，即 \(d\mid r\)。此时整个循环的 \(d\) 个点都被固定；否则一个固定点也没有。对全部循环求和即得。 \(\square\)

## 定理 B1.2（Möbius 恢复循环谱）

设 \(\mu\) 为 Möbius 函数。则
\[
\boxed{
c_d(\tau)
=
\frac1d\sum_{e\mid d}\mu\!\left(\frac de\right)F_e(\tau).
}
\]

### 证明

令 \(a_d=d\,c_d\)。定理 B1.1 给出
\[
F_r=\sum_{d\mid r}a_d.
\]
于是
\[
\begin{aligned}
\sum_{e\mid d}\mu\!\left(\frac de\right)F_e
&=
\sum_{e\mid d}\mu\!\left(\frac de\right)
\sum_{k\mid e}a_k\\
&=
\sum_{k\mid d}a_k
\sum_{\substack{e\mid d\\k\mid e}}
\mu\!\left(\frac de\right).
\end{aligned}
\]
令 \(e=kf\)，内层和为
\[
\sum_{f\mid d/k}\mu\!\left(\frac{d/k}{f}\right),
\]
仅在 \(k=d\) 时等于 \(1\)，否则等于 \(0\)。故总和为 \(a_d=d\,c_d\)。 \(\square\)

所以全部 \(F_r\) 与全部 \(c_d\) 包含同一信息。

---

# 2. 对角逃逸谱

令地址集 \(A\) 与值集 \(Y\) 满足
\[
|A|=n,
\qquad
|Y|=q.
\]
对评价表 \(E:A\times A\to Y\)，定义
\[
\Delta_r(E)(a)=\tau^r(E(a,a)).
\]
仓库既有定理给出：扭曲有 \(k\) 个不动点时，逃逸评价表数量为 \((q^n-k)^n\)。

## 定理 B1.3（循环型逃逸谱）

第 \(r\) 次扭曲的逃逸评价表数量为
\[
\boxed{
N_r
=
\left(
q^n-
\sum_{d\mid r}d\,c_d(\tau)
\right)^n.
}
\]

### 证明

定理 B1.1 给出 \(\tau^r\) 的不动点数
\[
F_r=\sum_{d\mid r}d\,c_d.
\]
代入既有精确逃逸公式即得。 \(\square\)

## 推论 B1.4（逃逸谱恢复循环类型）

固定 \(n,q\) 后，全部 \(N_r\) 决定全部 \(c_d\)。

### 证明

因
\[
N_r=(q^n-F_r)^n
\]
且 \(q^n-F_r\) 为非负整数，\(N_r\) 的唯一非负整数 \(n\) 次根给出
\[
F_r=q^n-N_r^{1/n}.
\]
再用定理 B1.2。 \(\square\)

这说明“对角逃逸统计”能够读取扭曲的周期结构。

## 定理 B1.5（Burnside 平均）

若有限群 \(G\) 作用于有限集合 \(Y\)，则
\[
\boxed{
\frac1{|G|}
\sum_{g\in G}|\operatorname{Fix}(g)|
=|Y/G|.
}
\]

### 证明

双重计数
\[
\Omega=\{(g,y):g\cdot y=y\}.
\]
按 \(g\) 计数得到固定点数之和。按 \(y\) 计数得到
\[
\sum_y|\operatorname{Stab}(y)|.
\]
一个轨道 \(O\) 中每个稳定子大小为 \(|G|/|O|\)，故该轨道总贡献为 \(|G|\)。全部轨道贡献 \(|G|\,|Y/G|\)。 \(\square\)

## 推论 B1.6（平均逃逸下界）

设 \(n\ge1\)，并记
\[
N_g=(q^n-|\operatorname{Fix}(g)|)^n.
\]
则
\[
\boxed{
\frac1{|G|}\sum_gN_g
\ge
(q^n-|Y/G|)^n.
}
\]

### 证明

函数 \(\varphi(x)=(q^n-x)^n\) 在 \([0,q]\) 上凸；\(n=1\) 时线性，\(n\ge2\) 时
\[
\varphi''(x)=n(n-1)(q^n-x)^{n-2}\ge0.
\]
由 Jensen 不等式和定理 B1.5 即得。 \(\square\)

商大小控制平均固定负载，而完整固定点谱控制每个扭曲方向的逃逸数量。

---

# 3. 自由循环作用的商—余正规形

令
\[
C_m=\mathbb Z/m\mathbb Z,
\qquad m\ge2.
\]
设双射 \(T:X\to X\) 满足 \(T^m=\operatorname{id}\)，并且作用自由：
\[
T^rx=x\Longrightarrow r=0\text{ 于 }C_m.
\]
令 \(B=X/C_m\)，商映射为 \(\pi:X\to B\)。

## 定义 B1.7（循环余坐标）

循环余坐标是函数
\[
\kappa:X\to C_m
\]
满足
\[
\boxed{
\kappa(T^rx)=\kappa(x)+r.
}
\]

## 定理 B1.8（截面—余坐标对应）

下列数据自然一一对应：

1. 截面 \(s:B\to X\)，满足 \(\pi s=\operatorname{id}\)；
2. 循环余坐标 \(\kappa:X\to C_m\)。

### 证明

给定截面 \(s\)。每个 \(x\) 唯一写成
\[
x=T^rs(\pi x),
\]
存在性来自同轨道，唯一性来自自由性。定义 \(\kappa_s(x)=r\)，立即有
\[
\kappa_s(T^tx)=\kappa_s(x)+t.
\]

反之，给定 \(\kappa\)。每个轨道中存在唯一余坐标为零的点：
\[
T^{-\kappa(x)}x
\]
余坐标为零；若 \(y,T^ry\) 均为零余量，则 \(r=0\)。选取该唯一点即得截面。两种构造互逆。 \(\square\)

## 推论 B1.9（循环商—余正规形）

选定截面后，
\[
\Phi_s:B\times C_m\to X,
\qquad
\Phi_s(b,r)=T^rs(b)
\]
为双射，并且
\[
\boxed{T(b,r)=(b,r+1).}
\]

布尔取反即 \(m=2\) 的特例；一般有限“换过来”是循环余量平移，而非必然只有正负两个值。

## 定理 B1.10（命名规范变换）

若 \(s,t\) 为两个截面，则存在唯一
\[
g:B\to C_m
\]
使
\[
t(b)=T^{g(b)}s(b).
\]
对应余坐标满足
\[
\boxed{
\kappa_t(x)=\kappa_s(x)-g(\pi x).
}
\]

### 证明

同一自由轨道中 \(T^rs(b)\) 唯一遍历全部元素，故 \(g\) 唯一。将
\[
t(\pi x)=T^{g(\pi x)}s(\pi x)
\]
代入 \(x\) 的两种正规表达即可得到余坐标公式。 \(\square\)

命名只改变各纤维中哪个余量被称为零，不改变商对象。

---

# 4. 非自由作用与奇异界面

## 定理 B1.11（轨道—稳定子纤维）

有限群 \(G\) 作用于 \(X\) 时，
\[
G/\operatorname{Stab}(x)
\longrightarrow Gx,
\qquad
g\operatorname{Stab}(x)\mapsto gx
\]
为双射，因此
\[
\boxed{|Gx|=|G|/|\operatorname{Stab}(x)|.}
\]

### 证明

若两个陪集相同，则它们作用于 \(x\) 的结果相同；反之若 \(gx=hx\)，则 \(h^{-1}g\) 属于稳定子，故陪集相同。 \(\square\)

稳定子增大时，纤维缩小。对合的固定界面正是稳定子从平凡群跃迁为整个 \(C_2\) 的奇异层。一般有限对称的“界面”应理解为稳定子类型变化的分层，而不是预设的二值边界。

---

# 5. 拓扑覆盖与全局余坐标障碍

设 \(X\) 为 Hausdorff 空间，\(T\) 为同胚并自由生成 \(C_m\) 作用，\(B=X/C_m\) 取商拓扑。

## 定理 B1.12（自由有限循环商是覆盖）

\[
\pi:X\to B
\]
是 \(m\) 重覆盖映射。

### 证明

固定 \(x\)。有限轨道
\[
x,Tx,\ldots,T^{m-1}x
\]
各点不同。由 Hausdorff 性，可选两两不交的开邻域 \(V_r\ni T^rx\)。令
\[
U=\bigcap_{r=0}^{m-1}T^{-r}(V_r).
\]
则各 \(T^rU\subseteq V_r\) 两两不交，并且
\[
\pi^{-1}(\pi(U))=igsqcup_rT^rU.
\]
右侧开，故 \(\pi(U)\) 开；每个限制 \(T^rU\to\pi(U)\) 为开连续双射，因而是同胚。 \(\square\)

## 定理 B1.13（连续余坐标、连续截面与平凡覆盖等价）

下列条件等价：

1. 存在连续截面 \(s:B\to X\)；
2. 存在连续循环余坐标 \(\kappa:X\to C_m\)，其中 \(C_m\) 离散；
3. 存在保持投影和作用的同胚
   \[
   X\cong B\times C_m.
   \]

### 证明

截面通过
\[
(b,r)\mapsto T^rs(b)
\]
给出覆盖平凡化；覆盖局部平凡性保证该双射及其逆连续。乘积平凡化的第二坐标给出连续余坐标。

反之，若有连续 \(\kappa\)，则
\[
X_0=\kappa^{-1}(0)
\]
为开闭集，每条轨道恰交 \(X_0\) 一点。限制 \(\pi|_{X_0}\) 为连续双射；它是开映射，因为对 \(O\subseteq X_0\) 开，
\[
\pi^{-1}(\pi(O))=igsqcup_rT^rO
\]
开。故其逆为连续截面。 \(\square\)

## 推论 B1.14（连通空间无全局连续有限余坐标）

若 \(X\) 非空连通且 \(m>1\)，则不存在全局连续截面或连续 \(C_m\)-值余坐标。

### 证明

否则 \(X\cong B\times C_m\)。右侧至少有两个非空开闭分量，与连通性矛盾。 \(\square\)

连续对象可以具有逐纤维的离散余量，却不一定允许全局连续命名。

---

# 6. 局部截面与 cocycle

取覆盖 \((U_i)\) 及局部连续截面 \(s_i:U_i\to X\)。

## 定理 B1.15（局部过渡余量）

交集 \(U_i\cap U_j\) 上存在唯一局部常值函数
\[
g_{ij}:U_i\cap U_j\to C_m
\]
使
\[
\boxed{s_j=T^{g_{ij}}s_i.}
\]
并满足
\[
g_{ii}=0,
\qquad
g_{ji}=-g_{ij},
\qquad
g_{ik}=g_{jk}+g_{ij}.
\]

### 证明

两个截面值位于同一自由轨道，故余量存在唯一。覆盖的局部分片使该余量在足够小邻域中恒定。其余等式由截面复合及自由性直接推出。 \(\square\)

## 定理 B1.16（全局命名的 coboundary 判据）

存在全局连续截面，当且仅当存在局部常值 \(h_i:U_i\to C_m\) 使
\[
\boxed{g_{ij}=h_i-h_j.}
\]

### 证明

若该式成立，令
\[
s_i'=T^{h_i}s_i.
\]
新过渡余量为
\[
g'_{ij}=h_j+g_{ij}-h_i=0,
\]
所以局部截面粘合成全局截面。

反之，若有全局截面 \(s\)，写 \(s_i=T^{a_i}s\)，则
\[
g_{ij}=a_j-a_i.
\]
取 \(h_i=-a_i\) 即得。 \(\square\)

这给出“连续对象中离散余量”的严格形式：全局标签可能不存在，但局部标签通过有限群 cocycle 被一致地粘合。

---

# 7. 多方向循环对角逃逸

设 \(C_m\) 自由作用于值集 \(Y\)，生成元为 \(T\)。定义
\[
\Delta_r(E)(a)=T^r(E(a,a)).
\]

## 定理 B1.17（全部非零余量均确定性逃逸）

若 \(r\neq0\)，则
\[
\boxed{
\Delta_r(E)
otin\operatorname{range}(a\mapsto E(a,-))
}
\]
对任意评价表成立。

### 证明

若 \(\Delta_r(E)=E(a,-)\)，比较第 \(a\) 个坐标得
\[
T^r(E(a,a))=E(a,a),
\]
与自由性矛盾。 \(\square\)

## 定理 B1.18（\(m-1\) 个不同逃逸方向）

若 \(A\neq\varnothing\)，则 \(r\mapsto\Delta_r(E)\) 在 \(C_m\) 上单射。因此每个评价表具有 \(m-1\) 个两两不同的非零循环逃逸对象。

### 证明

若 \(\Delta_r(E)=\Delta_s(E)\)，取任意 \(a_0\in A\)，得到
\[
T^{r-s}(E(a_0,a_0))=E(a_0,a_0).
\]
自由性给出 \(r=s\)。 \(\square\)

## 定理 B1.19（商影子保持，余坐标平移）

若 \(\pi:Y\to Y/C_m\) 为轨道商，\(\kappa:Y\to C_m\) 为余坐标，并逐点延拓为 \(\Pi_A,K_A\)，则
\[
\boxed{
\Pi_A\Delta_r(E)=\Pi_AD(E),
}
\]
\[
\boxed{
K_A\Delta_r(E)=K_AD(E)+r.
}
\]

### 证明

逐坐标使用
\[
\pi(T^ry)=\pi(y),
\qquad
\kappa(T^ry)=\kappa(y)+r.
\]
\(\square\)

---

# 8. 闭合结论

### 结论 B1-A

任意有限可逆扭曲都由循环组成；固定点只是长度一循环，布尔取反只是自由长度二循环。

### 结论 B1-B

\[
\boxed{
N_r=
\left(q^n-\sum_{d\mid r}d\,c_d\right)^n
}
\]
使定量对角逃逸谱能够恢复扭曲的整个循环类型。

### 结论 B1-C

自由循环作用在选定命名后具有
\[
\boxed{
X\cong(X/C_m)\times C_m,
\qquad
T(b,r)=(b,r+1).
}
\]
这里的“余”是有限 torsor 坐标，不限于正负比特。

### 结论 B1-D

连续全局余坐标存在当且仅当有限覆盖平凡。连通非平凡覆盖中的余坐标只能局部存在，并由 \(C_m\)-值 cocycle 记录命名错位。

### 结论 B1-E

自由 \(m\)-循环不是只有一个对角取反方向，而有 \(m-1\) 个不同的确定性逃逸方向。

---

## 形式化状态

B1.1—B1.19 均为完整纸面证明，尚未新增为 Lean 真源。其 Lean 化应优先复用仓库现有固定点敏感逃逸计数，而不另造重复的对角核心。
