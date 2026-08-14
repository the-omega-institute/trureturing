\left|
1-\zeta\left(\frac12+it\right)
A_N\left(\frac12+it\right)
\right|^2
\frac{dt}{\frac14+t^2},
}
\]

其中下确界遍历长度不超过 \(N\) 的 Dirichlet 多项式

\[
A_N(s)=\sum_{a\le N}c_aa^{-s}.
\]

因此 Nyman–Beurling 最终余质量可以写成

\[
\boxed{
\|Q_\infty\chi\|^2
=
\lim_{N\to\infty}
\inf_{A_N}
\frac1{2\pi}
\int_{-\infty}^{\infty}
|1-\zeta(s)A_N(s)|^2
\frac{dt}{|s|^2},
\quad
s=\frac12+it.
}
\]

于是

\[
\boxed{
\mathrm{RH}
\iff
\zeta(s)
\text{ 在该加权临界线空间中拥有 Dirichlet 多项式近逆}.
}
\]

这不是逐点逼近 \(1/\zeta(s)\)。临界线零点处逐点逆不存在，而 \(L^2\) 判据只要求加权均方误差趋零。真正困难的是证明存在一列显式 Dirichlet 多项式，使这一全局均方误差具有趋零上界。

该公式还把 Gram 矩阵写成零点与素数共同作用的相关矩阵：

\[
\boxed{
(G_N)_{ab}
=
\frac1{2\pi}
\int_{-\infty}^{\infty}
\frac{
\left|
\zeta\left(\frac12+it\right)
\right|^2
}{
\frac14+t^2
}
a^{-\frac12-it}
b^{-\frac12+it}
\,dt.
}
\]

所以第 29.6 节的正交创新并非纯粹数值线性代数对象；它编码了临界线上的 \(|\zeta|^2\) 加权频率相关。

---

## 29.8 为什么有限数值逼近仍然不是证明

若某个有限 \(N\) 给出

\[
d_N\ll1,
\]

它只提供上界

\[
\|Q_\infty\chi\|
\le d_N,
\]

不能给出严格等式

\[
\|Q_\infty\chi\|=0.
\]

即使计算得到一条长序列

\[
d_{N_1}>d_{N_2}>\cdots
\]

并呈现明显趋零趋势，仍可能存在一个不可见的正极限

\[
d_\infty
=
\|Q_\infty\chi\|
>0.
\]

另一方面，第 28 节的算子范数障碍

\[
\|I-P_{S_N}\|_{\mathrm{op}}=1
\]

并不直接否定 Nyman–Beurling 路线，因为 RH 只要求逼近一个固定目标 \(\chi\)，不要求 \(P_{S_N}\) 在整个单位球上一致逼近恒等算子。

正确边界是：

\[
\boxed{
\text{全空间一致逼近不可能，}
}
\]

但

\[
\boxed{
\text{单一目标的强逼近仍可能成立。}
}
\]

要把数值证据升级为证明，必须构造一列可验证系数 \(c_{a,N}\)，并给出完全无条件的显式误差界

\[
\boxed{
\left\|
\chi-\sum_{a\le N}c_{a,N}f_a
\right\|_2^2
\le
\varepsilon_N,
\qquad
\varepsilon_N\longrightarrow0.
}
\]

或者在 Mellin 图像中证明

\[
\boxed{
\frac1{2\pi}
\int_{\mathbb R}
|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2
\frac{dt}{\frac14+t^2}
\le
\varepsilon_N
\longrightarrow0.
}
\]

任何真正建立该估计的无条件论证都会通过强 Nyman–Beurling 判据证明 RH；因此不能把目标误差趋零作为未经证明的“正则性假设”重新命名。

---

## 29.9 Weil 正性：有限压缩向无限极限传递所需的 form-core 条件

设 \(\mathcal D\) 为 Weil 测试函数的稠密定义域，\(q_W\) 为对应 Hermitian 二次型。经典 Weil 判据把 RH 与适当测试类上的全局正性联系：

\[
\boxed{
\mathrm{RH}
\iff
q_W(f)\ge0
\quad
\text{对全部允许测试 }f.
}
\]

仓库 `WeilIdentity` 已形式化零点和、素数项、极点项与 Archimedean 项之间的显式公式，但明确没有附加正性或 RH 断言。

若要把第 28 节的正交塔用于 Weil 正性，必须先在**不假设 RH** 的情况下给出一个 Hilbert 空间 \(\mathscr H_W\) 与可闭二次型 \(q_W\)，再选择递增有限维子空间

\[
S_1^W\subseteq S_2^W\subseteq\cdots\subseteq\mathcal D.
\]

只证明每个有限压缩非负：

\[
q_W(f)\ge0
\qquad
(f\in S_N^W)
\]

还不够。需要证明

\[
\bigcup_NS_N^W
\]

在二次型范数中是 form core。

### 定理 29.9（form-core 正性传递）

设 \(q\) 是稠密定义、闭合且下半有界的 Hermitian 二次型。若

\[
\mathcal C=\bigcup_NS_N
\]

是 \(q\) 的 form core，并且

\[
q(f)\ge0
\qquad
(f\in\mathcal C),
\]

则

\[
\boxed{
q(f)\ge0
\qquad
(f\in\operatorname{Dom}q).
}
\]

#### 证明

对任意 \(f\in\operatorname{Dom}q\)，由 form-core 性存在 \(f_n\in\mathcal C\)，使 \(f_n\to f\) 于二次型范数。闭合二次型在该拓扑下连续，故

\[
q(f_n)\to q(f).
\]

每个 \(q(f_n)\ge0\)，于是 \(q(f)\ge0\)。 \(\square\)

这揭示了有限 Weil 矩阵路线的准确缺口：

\[
\boxed{
\text{有限压缩正性}
+
\text{Hilbert 范数稠密}
\quad
\text{仍不足};
}
\]

必须有

\[
\boxed{
\text{二次型范数稠密／form-core 完备性}.
}
\]

此外，若把相关算子按壳层写成

\[
A_{N+1}
=
\begin{pmatrix}
A_N&C_N\\
C_N^*&D_N
\end{pmatrix},
\]

仅有

\[
A_N\ge0,
\qquad
D_N\ge0
\]

不能推出整个块矩阵非负。最简单的反例是

\[
\begin{pmatrix}
1&2\\
2&1
\end{pmatrix},
\]

其两个对角块均正，但存在特征值 \(-1\)。

在 \(A_N\) 可逆的理想情形，正确的新增壳层条件是 Schur 余量

\[
\boxed{
D_N-C_N^*A_N^{-1}C_N\ge0.
}
\]

半正定情形需把逆替换为 Moore–Penrose 逆，并加入相应的像空间兼容条件。

这正是第 28 节“加入动力学后必须保留全部 \(P_iTP_j\) 块”的 RH 版本：只检查每个壳层自身的正性，会遗漏跨壳层耦合制造的负方向。

---

## 29.10 三条路线的逻辑地位

### 零点 Cayley 塔

它给出最直接的等价：

\[
\mathrm{RH}
\iff
C^*C-I=0.
\]

优点是零点离线深度、镜像反号、Li 放大与有限高度盲区全部透明。缺点是 \(C\) 直接由零点构造，因此只是诊断坐标，不是独立证明机制。

### Nyman–Beurling 目标余塔

它给出：

\[
\mathrm{RH}
\iff
P_{R_\infty}\chi=0.
\]

生成元 \(f_a\) 完全显式，有限阶段可由 Gram–Schur 算法计算，逻辑上非循环。真正缺口是无条件证明目标余质量趋零。

### Weil 压缩塔

它试图把 RH 变成一个全局正算子或正二次型命题。该路线最接近谱解释，但必须解决：

\[
\text{无条件 Hilbert 实现},
\]

\[
\text{二次型可闭性},
\]

\[
\text{form-core 完备性},
\]

\[
\text{跨壳层耦合},
\]

\[
\text{最终余块正性}.
\]

不能先用 Weil 正性定义内积，再以所得 Hilbert 范数证明 Weil 正性；那会把 RH 作为正定性的前提隐藏进空间构造中。

---

## 29.11 本框架识别出的真正“证明心脏”

第 28 节本身提供的是完备的记账语言：

\[
S_N,
\qquad
E_{N+1},
\qquad
R_N,
\qquad
R_\infty,
\qquad
P_iTP_j.
\]

它不会凭空生成 RH 所需的解析估计。用于 RH 后，缺失心脏可以被压缩成以下三种等价风格之一。

### 目标余质量消失

证明

\[
