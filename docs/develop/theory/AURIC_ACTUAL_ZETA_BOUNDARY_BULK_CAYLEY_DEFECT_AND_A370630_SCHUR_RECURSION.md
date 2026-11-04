# AURIC 实际 ζ 边界—体 Cayley 缺陷与 A370630 Schur 递归（编者拟题）

> **编者说明与来源界限。** 标题为编者描述性拟题；所供原文未署作者姓名、标题、版本或成文日期。下方作者正文保留原文的开场、九节、全部证明、例子、表格、公式、链接与结尾；数学外层定界符转换为美元形式，锚点和单独标明的相邻“编者条件注”属于编辑结构。作者正文中的“本轮”“读取并核对”“项目已有”“新增”、固定提交及观测时点、v44 稿查找结果，均是原作者的历史陈述，不表示编者重演了那些动作。本文是理论参考输入；纸面论证与源码阅读不等于新的 Lean 编译、依赖闭包审计、原生门实现、物理或经验认证。RH 仍未获无条件证明。

导航：[开场](#opening) · [一](#section-1) · [二](#section-2) · [三](#section-3) · [四](#section-4) · [五](#section-5) · [六](#section-6) · [七](#section-7) · [八](#section-8) · [九](#section-9)。

<style>
#auric-zeta-paper .katex-display > .katex { width: max-content; min-width: 100%; }
#auric-zeta-paper .katex-display > .katex > .katex-html > .katex-tag { position: static; display: inline-block; margin-left: 1em; }
#auric-zeta-paper code, #auric-zeta-paper a { overflow-wrap: anywhere; }
#auric-zeta-paper .table-scroll { overflow-x: auto; }
</style>

<div id="auric-zeta-paper">

<!-- author-begin -->
<!-- editor-anchor -->
<a id="opening"></a>
<!-- /editor-anchor -->

可以把这条联系推进到一个**精确的边界—体定理**：

> **将项目中的实际 ζ 函数读出作 Cayley 变换，再用 AURIC 的三轴球面表示，临界线上的读出无条件落在赤道；黎曼猜想等价于整个右半平面的实际延拓始终落在指定的北半球。**

还可以进一步把你提出的“结果、误差、总量守恒”落实为一个严格恒等式：

$$
\boxed{
\text{边界的反全纯误差}
=
\text{体内违反全纯条件的加权能量}.
}
$$

这份误差非负、归一化、有稳定界，而且**它等于零恰好等价于 RH**。

下面给出定义、定理和证明，并把它接回项目的边界消元、维度提升与 A370630 递归。需要先明确证明范围：**这一轮能够证明这些连接定理及误差恒等式；还没有证明实际 ζ 数据的那份误差必然为零，因此还不能宣布 RH 已被证明。**

---

<!-- editor-anchor -->
<a id="heading-1"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-1"></a>
<!-- /editor-anchor -->
## 一、先对齐项目本轮真正增加了什么

本轮核对固定在 `dev` 提交 [`b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3`](https://github.com/the-omega-institute/trureturing/tree/b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3)，时间为 **2026-10-31 09:34 UTC**。

与你这一问题直接相关的内容有：

<!-- editor-table -->
<div class="table-scroll">

| 项目内容 | 已经提供的数学工具 | 本轮如何使用 |
|---|---|---|
| [量子关系 v42](https://github.com/the-omega-institute/trureturing/blob/b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md) | 两个反射的关系、Pauli 三轴、完整 Gram 相容条件 | 把三轴表示与实际关系的正性分开辨认 |
| [边界几何 XI，§§271–273](https://github.com/the-omega-institute/trureturing/blob/b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_XI.md) | 同一个历史概率律上的反射正性商，以及扩大历史空间后的酉平移 | 明确升维必须保留同一组相关函数 |
| [ActualZeroLaplace](https://github.com/the-omega-institute/trureturing/blob/b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3/D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.lean) | 实际零点的加权 resolvent、完整总质量和 Laplace 恒等式 | 固定本轮算术对象与归一化，避免换成模型核 |
| **新增的** [ActualKernelLocalPositivity](https://github.com/the-omega-institute/trureturing/blob/b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3/D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.lean) | 同一个短窗口内，实际算术核对任意有限互异节点严格正定 | 提供无条件的局部起点 |

</div>
<!-- /editor-table -->

最后一项的正式声明确实是：

$$
\exists\,\delta\in(0,\log2),\quad
\forall m,\quad
\forall\text{互异 }t_1,\ldots,t_m,
$$

$$
\max_{i,j}|t_i-t_j|\le\delta
\quad\Longrightarrow\quad
[K(t_i-t_j)]_{i,j=1}^{m}\succ0.
$$

它没有把 RH 或外供正性作为前提。本轮读取并核对了源码声明与证明正文，**没有运行 Lean，也没有独立审计全部依赖**。

你另一段讨论中的 v44“球面提升—Poisson 延拓—有效度量”思路，我恢复到了相关定义摘要；完整 v44 稿未在这次核对的仓库路径中找到。因此下面把所需步骤直接写出纸面证明。

---

<!-- editor-anchor -->
<a id="heading-2"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-2"></a>
<!-- /editor-anchor -->
## 二、固定同一个实际算术对象

所有零点求和都按解析重数计入。令

$$
a_\rho=\rho-\frac12,\qquad
b_\rho=\frac1{\rho(1-\rho)},
$$

并固定总量

$$
\boxed{
S=\sum_\rho b_\rho
=2+\gamma_E-\log(4\pi)>0.
}
$$

沿用前面研究的完整算术核：

$$
K(t)=e^{-|t|/2}\,\mathcal A(e^{|t|}),
$$

其中

$$
\begin{aligned}
\mathcal A(x)
={}&x(1+\gamma_E-\log x)-\log(2\pi)\\
&+\sum_{m\ge1}\frac{x^{-2m}}{2m(2m+1)}
+\sum_{p^j\le x}\log p\left(\frac{x}{p^j}-1\right).
\end{aligned}
$$

因此，全部素数幂层与平凡零点项都保留着。它的零点表达为

$$
K(t)=\sum_\rho b_\rho e^{a_\rho t},
\qquad K(0)=S.
$$

定义实际亚纯函数

<!-- editor-anchor -->
<a id="eq-2-1"></a>
<!-- /editor-anchor -->

$$
\boxed{
F(z)=\sum_\rho\frac{b_\rho}{z-a_\rho}.
}
\tag{2.1}
$$

在 $\Re z>\tfrac12$，

<!-- editor-anchor -->
<a id="eq-2-2"></a>
<!-- /editor-anchor -->

$$
F(z)=\int_0^\infty e^{-zt}K(t)\,dt.
\tag{2.2}
$$

项目已有的 resolvent 恒等式，平移变量后恰好给出

<!-- editor-anchor -->
<a id="eq-2-3"></a>
<!-- /editor-anchor -->

$$
\boxed{
F(z)=
\frac{
Sz-(\xi'/\xi)(\frac12+z)
}{
z^2-\frac14
}.
}
\tag{2.3}
$$

这里 $z=\pm\tfrac12$ 是可去点。真正的极点恰在 $z=a_\rho$，留数为相应重数乘以 $b_\rho$，不会消失。

采用标准定义

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
$$

以及 $\xi(s)=\xi(1-s)$ 和共轭对称性，得到

<!-- editor-anchor -->
<a id="eq-2-4"></a>
<!-- /editor-anchor -->

$$
F(-z)=-F(z),\qquad
F(\bar z)=\overline{F(z)}.
\tag{2.4}
$$

这些 ξ 函数的定义与反射关系是标准事实。[dlmf.nist.gov](https://dlmf.nist.gov/25.4?utm_source=chatgpt.com)

特别地，在虚轴正则点，

<!-- editor-anchor -->
<a id="eq-2-5"></a>
<!-- /editor-anchor -->

$$
\boxed{\Re F(iy)=0.}
\tag{2.5}
$$

还有一个不能丢掉的归一化：

<!-- editor-anchor -->
<a id="eq-2-6"></a>
<!-- /editor-anchor -->

$$
\boxed{\lim_{x\to+\infty}xF(x)=S.}
\tag{2.6}
$$

因为 $\sum_\rho|b_\rho|<\infty$，且 $x\ge1$ 时

$$
\left|\frac{x}{x-a_\rho}\right|
\le\frac{x}{x-\frac12}\le2,
$$

所以控制收敛即可证明。

这里的“边界”将指 $\Re z=0$，即原变量的临界线；“体”指右半平面 $\Re z>0$。

<!-- editor-note:actual-sources -->
<div class="editor-note" id="note-actual-sources">

**编者条件注（actual-sources）。** 本节的实际对象对应固定提交中的 `ActualZeroLaplace.actualCoeff`、`actualH`、`actualCoeff_hasSum`、`actual_resolvent_hasSum`、`actualH_laplace`；最后两个声明原域为 $\Re s>1$，用 $s=\tfrac12+z$ 才得到这里的 $\Re z>\tfrac12$。同目录 `WholeFormula.actual_integrated_explicit_formula` 在每个实 $t>0$ 给出 $\mathrm{actualH}(t)=U(e^t)-\log(2\pi)+\mathrm{trivialT}(t)$；`CompleteMangoldtLaplace.U_eq_complete_ramps` 和 `TrivialZeroLaplace.trivialT` 保留全部素数幂斜坡与平凡零点项。因此此处 $K(t)=e^{-t/2}\mathrm{actualH}(t)$（$t>0$），在零点由连续性和原总质量补齐，负半轴由零点反射配对补齐。重数是 `ActualReciprocalSquareBounds.ActualZeroOccurrence` 的实际解析重数，绝对收敛与总量由 `actual_complex_pairWeight_hasSum` 及该 occurrence 传输供应；$S$ 不作重新归一化。以上是源码的对象与适用域对应，并非新编译或完整依赖审计。

</div>
<!-- /editor-note -->

---

<!-- editor-anchor -->
<a id="heading-3"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-3"></a>
<!-- /editor-anchor -->
## 三、定理一：RH 恰好是 AURIC 球面提升的半球条件

<!-- editor-anchor -->
<a id="heading-4"></a>
<!-- /editor-anchor -->
### 定义：实际 Cayley 读出与三轴提升

令

<!-- editor-anchor -->
<a id="eq-3-1"></a>
<!-- /editor-anchor -->

$$
\boxed{
C(z)=\frac{S-F(z)}{S+F(z)}.
}
\tag{3.1}
$$

把这个复关系读出写成二元纯态：

$$
\rho_C
=
\frac1{1+|C|^2}
\begin{pmatrix}
1&\bar C\\
C&|C|^2
\end{pmatrix}.
$$

其三轴坐标为

<!-- editor-anchor -->
<a id="eq-3-2"></a>
<!-- /editor-anchor -->

$$
\mathbf r(C)=
\frac{
(2\Re C,\ 2\Im C,\ 1-|C|^2)
}{
1+|C|^2
}.
\tag{3.2}
$$

于是无条件有

$$
\rho_C\succeq0,\qquad
\operatorname{tr}\rho_C=1,\qquad
|\mathbf r(C)|^2=1.
$$

这正是你所说的：**一个二元复关系，在归一化后可以用三个坐标及一个球面约束表示。**

将[式（3.1）](#eq-3-1)代入，第三轴变成

<!-- editor-anchor -->
<a id="eq-3-3"></a>
<!-- /editor-anchor -->

$$
\boxed{
r_3(z)=
\frac{2S\,\Re F(z)}{S^2+|F(z)|^2}.
}
\tag{3.3}
$$

<!-- editor-anchor -->
<a id="heading-5"></a>
<!-- /editor-anchor -->
### 定理 1

对上述实际算术函数：

1. 临界边界无条件满足
   $$
|C(iy)|=1,\qquad r_3(iy)=0.
$$
2. 以下条件等价：
   $$
\mathrm{RH};
$$
   $$
F\text{ 在右半平面全纯，且 }\Re F\ge0;
$$
   $$
C\text{ 在右半平面全纯，且 }|C|\le1;
$$
   $$
\boxed{
r_3(z)\ge0
\quad\text{对右半平面的全部实际正则点成立}.
}
$$

<!-- editor-anchor -->
<a id="heading-6"></a>
<!-- /editor-anchor -->
### 证明

**先证明边界。**

由 $F(iy)$ 为纯虚数，

$$
|S-F(iy)|=|S+F(iy)|,
$$

所以 $|C(iy)|=1$。

若 $F$ 在某个临界线点有极点，则

$$
C(z)=-1+\frac{2S}{S+F(z)},
$$

该点对 $C$ 可去，延拓值为 $-1$。所以边界单位模性质覆盖所有有限虚轴点。

<!-- editor-note:cayley-endpoints -->
<div class="editor-note" id="note-cayley-endpoints">

**编者条件注（cayley-endpoints）。** [式（3.1）](#eq-3-1)作为有限复数公式先要求 $F$ 正则且 $S+F\ne0$；[式（3.2）](#eq-3-2)的有限坐标也先在这一域使用。若 $F=-S$，$C$ 有极点，但其射影球面值连续延拓为南极 $(0,0,-1)$，[式（3.3）](#eq-3-3)仍给 $r_3=-1$；若 $F$ 有极点，则 $C=-1$ 可去，球面值为 $(-1,0,0)$。所以“全部实际正则点”的第三轴可用[式（3.3）](#eq-3-3)在全部 $F$ 正则点读取；边界零点另按上述可去延拓读取。反向的 Schur 条件还要排除 $C\equiv-1$：由[式（2.6）](#eq-2-6)，正实无穷远处 $C\to1$，故 $C$ 非该常值；最大模原理于是排除盘内取值 $-1$，使 $F=S(1-C)/(1+C)$ 全纯。北半球是闭半球表述，RH 下内部实际为严格北半球。

</div>
<!-- /editor-note -->

**再证明 RH 推出半球条件。**

RH 成立时，

$$
a_\rho=i\gamma_\rho,\qquad
b_\rho=\frac1{\frac14+\gamma_\rho^2}>0.
$$

故对 $x>0$，

<!-- editor-anchor -->
<a id="eq-3-4"></a>
<!-- /editor-anchor -->

$$
\boxed{
\Re F(x+iy)
=
\sum_\rho
\frac1{\frac14+\gamma_\rho^2}
\frac{x}{x^2+(y-\gamma_\rho)^2}
>0.
}
\tag{3.4}
$$

于是 $r_3>0$，且

$$
|S+F|^2-|S-F|^2=4S\Re F>0,
$$

给出 $|C|<1$。

**最后证明反向。**

假设存在离线零点。零点关于临界线的对称性保证存在某个

$$
z_0=a_\rho,\qquad \Re z_0>0.
$$

这种对称性及临界带的位置是标准零点事实。[dlmf.nist.gov](https://dlmf.nist.gov/25.10?utm_source=chatgpt.com)

在 $z_0$ 附近，

$$
F(z)=\frac{q}{z-z_0}+O(1),\qquad q\ne0.
$$

取

$$
z=z_0-\varepsilon q,\qquad \varepsilon>0
$$

足够小，则仍有 $\Re z>0$，但

$$
F(z)=-\frac1\varepsilon+O(1),
$$

从而 $\Re F(z)<0$，即 $r_3(z)<0$。

因此整个实际算术体的半球条件排除了所有离线零点。证毕。

<!-- editor-anchor -->
<a id="heading-7"></a>
<!-- /editor-anchor -->
### 这个定理怎样解释你的直觉？

三轴表示已经把 RH 所需的关键符号放到了一个明确坐标上：

$$
\boxed{\text{第三轴的方向，记录实际算术延拓的正性。}}
$$

球面归一化本身允许南、北两个半球。它保证表示合法；还需要算术论证保证实际像始终处于指定半球。

这里还要保留维数的准确含义：复平面有两个实自由度，球面也有两个内在自由度。若进一步加入混合半径 $t\in[0,1]$，

$$
\rho(t,C)=\frac12\bigl(I+t\,\mathbf r(C)\cdot\sigma\bigr),
$$

才得到整个三维 Bloch 体；这个半径是一份额外数据。

---

<!-- editor-anchor -->
<a id="heading-8"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-4"></a>
<!-- /editor-anchor -->
## 四、定理二：边界误差等于体内的反全纯能量

这一节把你的“结果—误差—总量守恒”直接变成实际 ζ 数据的定理。

<!-- editor-anchor -->
<a id="heading-9"></a>
<!-- /editor-anchor -->
### 1. 从临界边界到单位圆

用

$$
\tau(w)=\frac{1+w}{1-w}
$$

把单位盘 $\mathbb D$ 映到右半平面。在单位圆上，

$$
\tau(e^{i\theta})=i\cot\frac\theta2.
$$

定义实际边界相位

$$
g(e^{i\theta})
=
C\!\left(i\cot\frac\theta2\right).
$$

由定理 1，无条件有

$$
|g|=1\quad\text{几乎处处}.
$$

单位圆上的点 $1$ 对应无穷远；单点如何赋值不影响以下积分。

令 $U$ 为 $g$ 的 Poisson 延拓：

<!-- editor-anchor -->
<a id="eq-4-1"></a>
<!-- /editor-anchor -->

$$
U(w)=
\frac1{2\pi}\int_0^{2\pi}
\frac{1-|w|^2}{|e^{i\theta}-w|^2}
g(e^{i\theta})\,d\theta.
\tag{4.1}
$$

由于 Poisson 核非负且积分为一，

$$
|U(w)|\le1.
$$

这一步无条件给出稳定的调和延拓。

<!-- editor-anchor -->
<a id="heading-10"></a>
<!-- /editor-anchor -->
### 2. 定义两份正交能量

令

$$
\widehat g(n)
=
\frac1{2\pi}
\int_0^{2\pi}g(e^{i\theta})e^{-in\theta}\,d\theta.
$$

定义

$$
E_{\mathrm{hol}}
=
\sum_{n\ge0}|\widehat g(n)|^2,
$$

<!-- editor-anchor -->
<a id="eq-4-2"></a>
<!-- /editor-anchor -->

$$
\boxed{
E_{\mathrm{anti}}
=
\sum_{n<0}|\widehat g(n)|^2.
}
\tag{4.2}
$$

这里正、负 Fourier 模式是 $L^2$ 中的正交分解。因此 Parseval 恒等式给出

<!-- editor-anchor -->
<a id="eq-4-3"></a>
<!-- /editor-anchor -->

$$
\boxed{
E_{\mathrm{hol}}\ge0,\qquad
E_{\mathrm{anti}}\ge0,\qquad
E_{\mathrm{hol}}+E_{\mathrm{anti}}=1.
}
\tag{4.3}
$$

这确实是：

- 两个读出；
- 一个总量关系；
- 固定归一化；
- 正交分解。

其二元能量态可以写为

$$
\sqrt{E_{\mathrm{hol}}}\,|0\rangle
+
\sqrt{E_{\mathrm{anti}}}\,|1\rangle,
$$

对应三轴

$$
\left(
2\sqrt{E_{\mathrm{hol}}E_{\mathrm{anti}}},
\,0,\,
E_{\mathrm{hol}}-E_{\mathrm{anti}}
\right),
$$

平方和等于一。

<!-- editor-anchor -->
<a id="heading-11"></a>
<!-- /editor-anchor -->
### 定理 2A：边界—体误差恒等式

取

$$
\partial=\frac12(\partial_x-i\partial_y),\qquad
\bar\partial=\frac12(\partial_x+i\partial_y),
$$

以及普通面积测度 $dA=dx\,dy$。则

<!-- editor-anchor -->
<a id="eq-4-4"></a>
<!-- /editor-anchor -->

$$
\boxed{
E_{\mathrm{anti}}
=
\frac1\pi\int_{\mathbb D}
\log\frac1{|w|^2}
\,|\bar\partial U(w)|^2\,dA(w).
}
\tag{4.4}
$$

同时，

<!-- editor-anchor -->
<a id="eq-4-5"></a>
<!-- /editor-anchor -->

$$
\boxed{
|\widehat g(0)|^2+
\frac1\pi\int_{\mathbb D}
\log\frac1{|w|^2}
\left(
|\partial U|^2+|\bar\partial U|^2
\right)dA
=1.
}
\tag{4.5}
$$

<!-- editor-anchor -->
<a id="heading-12"></a>
<!-- /editor-anchor -->
#### 证明

Poisson 展开为

$$
U(w)=\widehat g(0)
+\sum_{k\ge1}\widehat g(k)w^k
+\sum_{k\ge1}\widehat g(-k)\bar w^{\,k}.
$$

所以

$$
\bar\partial U(w)
=
\sum_{k\ge1}k\widehat g(-k)\bar w^{\,k-1}.
$$

对固定 $r<1$，角向正交性给出

$$
\int_0^{2\pi}
|\bar\partial U(re^{i\theta})|^2\,d\theta
=
2\pi\sum_{k\ge1}
k^2|\widehat g(-k)|^2r^{2k-2}.
$$

再用

$$
\int_0^1
r^{2k-1}\log\frac1{r^2}\,dr
=
\frac1{2k^2},
$$

以及非负项的 Tonelli 换序，得到[式（4.4）](#eq-4-4)。

对 $\partial U$ 同理。两式相加并使用 Parseval，得到[式（4.5）](#eq-4-5)。证毕。

<!-- editor-anchor -->
<a id="heading-13"></a>
<!-- /editor-anchor -->
### 定理 2B：这份误差为零，当且仅当 RH

<!-- editor-anchor -->
<a id="eq-4-6"></a>
<!-- /editor-anchor -->

$$
\boxed{
\mathrm{RH}
\iff
E_{\mathrm{anti}}=0
\iff
\bar\partial U\equiv0.
}
\tag{4.6}
$$

<!-- editor-anchor -->
<a id="heading-14"></a>
<!-- /editor-anchor -->
#### 证明

若 RH 成立，定理 1 给出 $C\circ\tau$ 是单位盘上的有界全纯函数。它的边界值就是 $g$，所以其 Poisson 表示为

$$
U=C\circ\tau.
$$

因此 $U$ 全纯，全部负 Fourier 系数消失。

反过来，若 $E_{\mathrm{anti}}=0$，则

$$
U(w)=\sum_{n\ge0}\widehat g(n)w^n
$$

全纯，且 $|U|\le1$。

现在必须证明它确实匹配**实际算术延拓**。

在任一避开单位圆点 $1$ 的小边界弧上，实际 $C\circ\tau$ 都局部全纯：普通点由 $F$ 的边界纯虚性保证分母不为零；临界零点处则由

$$
C=-1+\frac{2S}{S+F}
$$

消去奇点。

因此 $U$ 与 $C\circ\tau$ 在这条边界弧上连续同值。二者之差跨弧反射后，解析唯一性给出局部恒等，继而由亚纯恒等原理得到

$$
U=C\circ\tau
$$

于整个盘内。

<!-- editor-note:arc-uniqueness -->
<div class="editor-note" id="note-arc-uniqueness">

**编者条件注（arc-uniqueness）。** 这里使用局部连续边界数据的 Poisson 收敛：在避开 $1$ 的闭子弧上，$g$ 是实际 $C\circ\tau$ 的解析、连续迹，故有界 $g$ 的 Poisson 积分在该子弧连续取同值；远弧部分的 Poisson 核趋零，近弧用连续性控制。这补足了 $U$ 的边界连续性，而不要求 $g$ 在无穷远对应点连续。当负频能量为零时，两全纯函数之差在弧上连续为零，局部拉直圆弧后用零实边值的 Schwarz 反射及恒等原理，先得局部恒等；再用实际亚纯函数的恒等原理扩展到整个连通盘。该步骤识别的是同一个实际算术延拓，并未任选一个 Schur 函数替代它。

</div>
<!-- /editor-note -->

于是实际 $C$ 是右半平面的 Schur 函数，定理 1 推出 RH。证毕。

<!-- editor-anchor -->
<a id="heading-15"></a>
<!-- /editor-anchor -->
### 3. 误差读出本身确实稳定

记 $P_-$ 为负频正交投影。则

$$
\sqrt{E_{\mathrm{anti}}(g)}=\|P_-g\|_2.
$$

故任意两份边界数据满足

<!-- editor-anchor -->
<a id="eq-4-7"></a>
<!-- /editor-anchor -->

$$
\boxed{
\left|
\sqrt{E_{\mathrm{anti}}(g)}
-
\sqrt{E_{\mathrm{anti}}(h)}
\right|
\le\|g-h\|_2.
}
\tag{4.7}
$$

这给出了你要求的“误差也受稳定约束”：它是明确的正交投影误差，不会放大边界的 $L^2$ 扰动。

但稳定与消失仍是两个命题。例如一般边界数据

$$
g(e^{i\theta})=e^{-i\theta}
$$

满足单位模、归一化与 Poisson 稳定，其延拓却是

$$
U(w)=\bar w,\qquad E_{\mathrm{anti}}=1.
$$

这个例子说明：**要证明 RH，真正需要完成的是实际 ζ 边界的全纯相容性。**

同样，递归尾项

$$
R_N=\sum_{k>N}|\widehat g(-k)|^2\longrightarrow0
$$

只说明误差展开收敛，因为

$$
E_{\mathrm{anti}}
=
\sum_{k=1}^{N}|\widehat g(-k)|^2+R_N.
$$

它不会自动把已经读出的误差能量消除。

---

<!-- editor-anchor -->
<a id="heading-16"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-5"></a>
<!-- /editor-anchor -->
## 五、定理三：原归一化下，临界边界是否恢复全部质量也等价于 RH

还有一份更直接的算术“结果—误差—总量”分解。

定义临界线谱测度

<!-- editor-anchor -->
<a id="eq-5-1"></a>
<!-- /editor-anchor -->

$$
\mu_\partial
=
\sum_{\Re\rho=\frac12}
\frac1{\frac14+\gamma_\rho^2}\,
\delta_{\gamma_\rho}.
\tag{5.1}
$$

它无条件为有限正测度。

<!-- editor-anchor -->
<a id="heading-17"></a>
<!-- /editor-anchor -->
### 定理 3

在局部分布意义下，

<!-- editor-anchor -->
<a id="eq-5-2"></a>
<!-- /editor-anchor -->

$$
\boxed{
\frac1\pi\Re F(\varepsilon+iy)\,dy
\xrightarrow[\varepsilon\downarrow0]{}
\mu_\partial.
}
\tag{5.2}
$$

而且

<!-- editor-anchor -->
<a id="eq-5-3"></a>
<!-- /editor-anchor -->

$$
\boxed{
S-\mu_\partial(\mathbb R)
=
\sum_{\Re\rho\ne\frac12}
\Re\frac1{\rho(1-\rho)}
\ge0,
}
\tag{5.3}
$$

等号成立当且仅当 RH。

<!-- editor-anchor -->
<a id="heading-18"></a>
<!-- /editor-anchor -->
### 证明

对临界零点，局部极点项的实部为

$$
\Re\frac{b_\rho}{\varepsilon+i(y-\gamma_\rho)}
=
\frac1{\frac14+\gamma_\rho^2}
\frac{\varepsilon}
{\varepsilon^2+(y-\gamma_\rho)^2}.
$$

除以 $\pi$ 后就是逼近 Dirac 质量的 Poisson 核。

对任何紧支撑测试函数，只需考虑有界高度内有限多个极点。其余项在该邻域正规收敛；去掉临界极点后的全纯部分在虚轴上实部为零。因此得到[式（5.2）](#eq-5-2)。

<!-- editor-note:local-mass -->
<div class="editor-note" id="note-local-mass">

**编者条件注（local-mass）。** [式（5.2）](#eq-5-2)是对每个紧支撑测试函数的局部分布收敛。固定紧高度区间后，可选足够薄的右侧邻带避开有限个离线极点，再分离其中有限个临界极点；正规收敛尾项和去极点后的解析余项在边界实部为零。这个论证不声称所有 $\varepsilon>0$ 的整轴密度非负，也不从局部收敛交换整轴总质量；[式（5.3）](#eq-5-3)的全局质量结算另由实际 $\sum|b_\rho|<\infty$ 以及逐项正实部完成。

</div>
<!-- /editor-note -->

再写 $\rho=\beta+i\gamma$。直接计算：

<!-- editor-anchor -->
<a id="eq-5-4"></a>
<!-- /editor-anchor -->

$$
\boxed{
\Re\frac1{\rho(1-\rho)}
=
\frac{\beta(1-\beta)+\gamma^2}
{
[\beta(1-\beta)+\gamma^2]^2
+\gamma^2(1-2\beta)^2
}
>0.
}
\tag{5.4}
$$

利用绝对收敛，把总质量 $S$ 分成在线与离线两部分，即得[式（5.3）](#eq-5-3)。存在任何离线零点，右侧就严格为正。证毕。

因此可以定义

$$
d_\partial
=
1-\frac{\mu_\partial(\mathbb R)}S,
$$

使

<!-- editor-anchor -->
<a id="eq-5-5"></a>
<!-- /editor-anchor -->

$$
\boxed{
\frac{\mu_\partial(\mathbb R)}S+d_\partial=1,
\qquad
d_\partial\ge0,
\qquad
\mathrm{RH}\iff d_\partial=0.
}
\tag{5.5}
$$

这份缺口必须相对于**原总量 $S$** 定义。若将临界线测度另除以它自身的总质量，就会把待证缺口藏进新的归一化。

这里的 $d_\partial$ 与上一节的 $E_{\mathrm{anti}}$ 是两种不同缺陷；已经证明的是它们的零条件都等价于 RH，没有声称它们的数值相等。

---

<!-- editor-anchor -->
<a id="heading-19"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-6"></a>
<!-- /editor-anchor -->
## 六、定理四：完整的边界二元关系能够生成自伴的高维体

前面的定理把目标放在一个标量函数上。现在证明：怎样从边界关系真正构造高维 Hilbert 空间，以及递归时究竟需要验证什么。

<!-- editor-anchor -->
<a id="heading-20"></a>
<!-- /editor-anchor -->
### 定义：边界关系核与全部阶数矩阵

令

$$
f(w)=iF(-iw).
$$

它在原点附近全纯、在实轴取实值，并且为奇函数。写成

$$
f(w)=\sum_{n\ge0}\alpha_nw^n.
$$

<!-- editor-note:real-domain -->
<div class="editor-note" id="note-real-domain">

**编者条件注（real-domain）。** “在实轴取实值”限于实轴上实际 $f$ 的正则点，原点附近先选一个不含实际极点的圆盘；不对实极点赋有限值。由[式（2.4）](#eq-2-4)，对实正则 $w$ 有 $\overline{iF(-iw)}=iF(-iw)$，因而局部 Taylor 系数均为实数。原点的正则性可由固定实际零点源的 `actual_height_gt_ten` 保证。下面的 $L$、幂级数与实节点先在该共同解析邻域内使用。

</div>
<!-- /editor-note -->

定义二元边界关系

<!-- editor-anchor -->
<a id="eq-6-1"></a>
<!-- /editor-anchor -->

$$
L(s,t)=
\begin{cases}
\dfrac{f(s)-f(t)}{s-t},&s\ne t,\\[1ex]
f'(t),&s=t,
\end{cases}
\tag{6.1}
$$

以及 Hankel 矩阵

<!-- editor-anchor -->
<a id="eq-6-2"></a>
<!-- /editor-anchor -->

$$
\boxed{
\mathsf H_N=(\alpha_{i+j+1})_{i,j=0}^{N}.
}
\tag{6.2}
$$

<!-- editor-anchor -->
<a id="heading-21"></a>
<!-- /editor-anchor -->
### 定理 4

以下条件等价：

1. RH；
2. 对所有 $N$，$\mathsf H_N\succeq0$；
3. $L$ 在原点的某个实开邻域上为正定核；
4. 存在 Hilbert 空间、有界自伴算子 $A$ 和向量 $v$，使
   <!-- editor-anchor -->
<a id="eq-6-3"></a>
<!-- /editor-anchor -->

$$
\boxed{
f(w)=\alpha_0+
w\langle v,(I-wA)^{-1}v\rangle
}
\tag{6.3}
$$
   在原点附近成立，并由右式延拓到上半平面。

在 RH 下，每个 $\mathsf H_N$ 实际上都严格正定。

<!-- editor-anchor -->
<a id="heading-22"></a>
<!-- /editor-anchor -->
### 证明第一步：RH 给出 Gram 表示

RH 下，利用零点纵坐标的正负对称性，

$$
f(w)=\sum_\rho\frac{b_\rho}{\gamma_\rho-w}.
$$

因此

$$
\alpha_n=\sum_\rho\frac{b_\rho}{\gamma_\rho^{n+1}}.
$$

对任何有限系数 $c_i$，

<!-- editor-anchor -->
<a id="eq-6-4"></a>
<!-- /editor-anchor -->

$$
\begin{aligned}
\sum_{i,j=0}^{N}\bar c_ic_j\alpha_{i+j+1}
&=
\sum_\rho
\frac{b_\rho}{\gamma_\rho^2}
\left|
\sum_{i=0}^{N}c_i\gamma_\rho^{-i}
\right|^2\\
&\ge0.
\end{aligned}
\tag{6.4}
$$

非零多项式不能在无限多个不同的 $1/\gamma_\rho$ 上全部消失，所以矩阵严格正定。

同样，

$$
L(s,t)=
\sum_\rho
\frac{b_\rho}
{(\gamma_\rho-s)(\gamma_\rho-t)}
$$

也是 Gram 核。

<!-- editor-anchor -->
<a id="heading-23"></a>
<!-- /editor-anchor -->
### 证明第二步：从全部边界矩阵构造高维体

假设所有 $\mathsf H_N\succeq0$。

在多项式空间上定义半内积：

$$
\langle x^i,x^j\rangle=\alpha_{i+j+1}.
$$

商掉零范数空间并完备化，得到 Hilbert 空间。

定义乘法算子

$$
Xp=xp.
$$

它对称。零范数空间在 $X$ 下不变，因为

$$
\|Xp\|^2
=
\langle p,X^2p\rangle
\le\|p\|\,\|X^2p\|.
$$

现在证明这个升维过程具有实际的有界控制。

固定多项式 $p$，令

$$
M_n=\|X^np\|^2.
$$

Cauchy–Schwarz 给出

<!-- editor-anchor -->
<a id="eq-6-5"></a>
<!-- /editor-anchor -->

$$
M_n^2\le M_{n-1}M_{n+1}.
\tag{6.5}
$$

所以 $M_n$ 对数凸。

另一方面，对任意小于 $f$ 解析半径的 $r>0$，Cauchy 系数估计给出

<!-- editor-anchor -->
<a id="eq-6-6"></a>
<!-- /editor-anchor -->

$$
M_n\le C_{p,r}r^{-2n}.
\tag{6.6}
$$

若

$$
M_1>r^{-2}M_0,
$$

则由对数凸性，各相邻比值不能下降，从而

$$
M_n\ge
M_0\left(\frac{M_1}{M_0}\right)^n,
$$

与[式（6.6）](#eq-6-6)矛盾。因此

$$
\|Xp\|\le r^{-1}\|p\|.
$$

故 $X$ 延拓为有界自伴算子 $A$。

<!-- editor-note:all-order-domain -->
<div class="editor-note" id="note-all-order-domain">

**编者条件注（all-order-domain）。** 本构造使用所有 $N\ge0$ 的 Hankel 半正定性。Cauchy 系数界中的 $r$ 固定为小于同一解析半径的正数，$C_{p,r}$ 可依赖 $p,r$，算子界 $r^{-1}$ 则与 $p$ 无关。若 $M_0=0$，零范数不变性已给 $M_1=0$；若反设 $M_1>r^{-2}M_0>0$，对数凸性归纳保证后续各项为正，方可使用比值。完成后的有界对称算子定义在整个 Hilbert 空间，故自伴；对 $\Im w>0$，$I-wA$ 可逆，[式（6.3）](#eq-6-3)在该半平面给全纯延拓。实际 $f$ 与它在原点圆盘的上半部分同值，亚纯唯一性才排除实际上半平面极点。[式（6.8）](#eq-6-8)与有限差分也在这一共同解析邻域内取极限；任何一个有限截断都不能替代全部阶数条件。

</div>
<!-- /editor-note -->

取 $v=[1]$，则

$$
\langle v,A^kv\rangle=\alpha_{k+1},
$$

由幂级数得到[式（6.3）](#eq-6-3)。

进一步，

<!-- editor-anchor -->
<a id="eq-6-7"></a>
<!-- /editor-anchor -->

$$
\boxed{
\Im f(w)
=
\Im w\,
\|(I-wA)^{-1}v\|^2
\ge0
\qquad(\Im w>0).
}
\tag{6.7}
$$

所以构造出来的是整个上半平面的全纯正性延拓。

若实际 $f$ 存在上半平面极点，解析唯一性就会迫使它与上述全纯函数在极点附近一致，使该极点可去；这与实际非零留数矛盾。于是没有离线零点，得到 RH。

<!-- editor-anchor -->
<a id="heading-24"></a>
<!-- /editor-anchor -->
### 证明第三步：二元核与全部阶数相容性等价

原点附近有

<!-- editor-anchor -->
<a id="eq-6-8"></a>
<!-- /editor-anchor -->

$$
L(s,t)=
\sum_{i,j\ge0}\alpha_{i+j+1}s^it^j.
\tag{6.8}
$$

所有 $\mathsf H_N\succeq0$ 时，截断式是正定核，收敛极限仍为正定核。

反之，若 $L$ 是正定核，对采样点作有限差分，再令步长趋于零，可得到导数 Gram：

$$
\frac1{i!j!}
\partial_s^i\partial_t^jL(0,0)
=
\alpha_{i+j+1}.
$$

它是半正定矩阵的极限，所以所有 $\mathsf H_N\succeq0$。证毕。

<!-- editor-anchor -->
<a id="heading-25"></a>
<!-- /editor-anchor -->
### 这是真正的“边界关系生成高维体”

这里每一个矩阵元素都是两个边界模式之间的关系：

$$
\langle x^i,x^j\rangle=\alpha_{i+j+1}.
$$

全部相容时，它们生成：

$$
\text{Hilbert 空间}
\;\longrightarrow\;
\text{自伴算子 }A
\;\longrightarrow\;
\text{酉算子 }
(A-iI)(A+iI)^{-1}.
$$

而且 RH 下 $\operatorname{rank}\mathsf H_N=N+1$，所以忠实承载这些关系的维数确实必须随递归深度增长。

**三轴可以组织每一步的二元接口；完整关系所需的上下文会不断增加。**

这也解释了一个容易混淆的地方：项目新增的 $K(t)$ 短时间窗正性，和这里的 $L(s,t)$ 局部正性是不同命题。后者虽然只写在一个小边界区间上，却包含了**全部阶数**的 Taylor 相容条件，已经具有 RH 的完整强度。

---

<!-- editor-anchor -->
<a id="heading-26"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-7"></a>
<!-- /editor-anchor -->
## 七、递归升维的精确条件：Schur 剩余必须保持非负

<!-- editor-anchor -->
<a id="heading-27"></a>
<!-- /editor-anchor -->
### 1. 一般边界—体扩张定理

设完整实际关系矩阵为

$$
\mathcal G=
\begin{pmatrix}
A&C^*\\
C&D
\end{pmatrix}.
$$

则

<!-- editor-anchor -->
<a id="eq-7-1"></a>
<!-- /editor-anchor -->

$$
\boxed{
\mathcal G\succeq0
\iff
A\succeq0,\quad
C\ker A=\{0\},\quad
D-CA^\dagger C^*\succeq0.
}
\tag{7.1}
$$

这里 $A^\dagger$ 是 Moore–Penrose 逆。

<!-- editor-note:finite-schur -->
<div class="editor-note" id="note-finite-schur">

**编者条件注（finite-schur）。** [式（7.1）](#eq-7-1)在有限维复 Hermitian 分块矩阵上使用：$A=A^*$、$D=D^*$，$C$ 可为矩形，$A^\dagger$ 是该有限矩阵的 Moore–Penrose 逆。此时 $C\ker A=0$ 等价于 $\operatorname{ran}C^*\subseteq\operatorname{ran}A$；这个范围条件使配方交叉项正确，也覆盖奇异块和零块。新增维数 $\operatorname{rank}R$ 是在已有 $A$ 的最小 Gram 实现上、保持全部交叉关系时的最小增量。这里未宣称无界算子或非闭值域的无限维版本。

</div>
<!-- /editor-note -->

证明的核心是配方：

$$
\begin{aligned}
\binom{x}{y}^{\!*}\mathcal G\binom{x}{y}
={}&
(x+A^\dagger C^*y)^*
A(x+A^\dagger C^*y)\\
&+
y^*(D-CA^\dagger C^*)y.
\end{aligned}
$$

零模条件 $C\ker A=0$ 则来自：一个零范数方向不可能与其他向量有非零 Hilbert 内积。

新增正交方向的 Gram 恰为

$$
R=D-CA^\dagger C^*,
$$

所以最少需要增加的维数是

$$
\operatorname{rank}R.
$$

这给出了“维度提升”的完整条件，而不仅是表示方式。

<!-- editor-anchor -->
<a id="heading-28"></a>
<!-- /editor-anchor -->
### 2. 边界消元的有效度量会保留实际符号

这与 v44 中的有效度量思路直接相接。设

$$
L=
\begin{pmatrix}
A&B^*\\
B&D
\end{pmatrix}=L^*,
$$

取实数 $\lambda$，并要求 $D-\lambda I$ 可逆。

内部响应为

$$
h=-(D-\lambda I)^{-1}Bg.
$$

定义提升

$$
E_\lambda g=
\binom{g}{h},
$$

以及有效边界算子

$$
\Lambda(\lambda)
=
A-\lambda I-B^*(D-\lambda I)^{-1}B.
$$

直接计算：

<!-- editor-anchor -->
<a id="eq-7-2"></a>
<!-- /editor-anchor -->

$$
\boxed{
G_\lambda
=
E_\lambda^*E_\lambda
=
I+B^*(D-\lambda I)^{-2}B
=
-\Lambda'(\lambda)
\succ0.
}
\tag{7.2}
$$

于是

$$
V_\lambda=E_\lambda G_\lambda^{-1/2}
$$

是等距提升。但它对实际形式的作用为

<!-- editor-anchor -->
<a id="eq-7-3"></a>
<!-- /editor-anchor -->

$$
\boxed{
V_\lambda^*(L-\lambda I)V_\lambda
=
G_\lambda^{-1/2}
\Lambda(\lambda)
G_\lambda^{-1/2}.
}
\tag{7.3}
$$

可逆合同变换保留正、负惯性指数。因此有效度量确实修正了升维后的归一化，却不会消除原实际形式中的负方向。

<!-- editor-note:compressed-inertia -->
<div class="editor-note" id="note-compressed-inertia">

**编者条件注（compressed-inertia）。** 本小节仍取有限维 Hermitian $L$、实 $\lambda$ 且 $D-\lambda I$ 可逆。[式（7.3）](#eq-7-3)的可逆合同只发生在边界空间上的 $\Lambda(\lambda)$ 与压缩形式 $V_\lambda^*(L-\lambda I)V_\lambda$ 之间；二者的正、负惯性相同。矩形等距映射 $V_\lambda$ 并非整个体空间上的可逆合同，因而不能据此声称保留全体 $L-\lambda I$ 的惯性或每个负方向。全体惯性另有 Schur 分解 

$$
\operatorname{In}(L-\lambda I)=\operatorname{In}(D-\lambda I)+\operatorname{In}(\Lambda(\lambda))
$$

。原句中“不会消除”的准确局部范围是 $\Lambda$ 已有的负方向及其提升像，不能把内部块遗漏的负方向算进边界压缩。

</div>
<!-- /editor-note -->

<!-- editor-anchor -->
<a id="heading-29"></a>
<!-- /editor-anchor -->
### 3. 把它应用到边界 Hankel 递归

若

$$
\mathsf H_N=
\begin{pmatrix}
\mathsf H_{N-1}&v_N\\
v_N^*&\alpha_{2N+1}
\end{pmatrix},
\qquad
\mathsf H_{N-1}\succ0,
$$

定义

<!-- editor-anchor -->
<a id="eq-7-4"></a>
<!-- /editor-anchor -->

$$
\boxed{
\kappa_N=
\alpha_{2N+1}
-v_N^*\mathsf H_{N-1}^{-1}v_N.
}
\tag{7.4}
$$

那么

<!-- editor-anchor -->
<a id="eq-7-5"></a>
<!-- /editor-anchor -->

$$
\alpha_{2N+1}
=
\underbrace{
v_N^*\mathsf H_{N-1}^{-1}v_N
}_{\text{已有边界解释的部分}}
+
\underbrace{\kappa_N}_{\text{新增正交部分}}.
\tag{7.5}
$$

若 $\kappa_N\ge0$，这一层可以忠实地提升为新的正交方向。

若 $\kappa_N<0$，任何保持这些实际关系的正 Hilbert 提升都不存在。

<!-- editor-note:hankel-start -->
<div class="editor-note" id="note-hankel-start">

**编者条件注（hankel-start）。** 逆矩阵递归的层数为 $N\ge1$，必须先给 $\mathsf H_0=(\alpha_1)\succeq0$（严格递归先取 $\alpha_1>0$），并在每一步实际满足所写的前驱 $\mathsf H_{N-1}\succ0$。若某层剩余为零，下一层不能继续直接使用普通逆；须回到[式（7.1）](#eq-7-1)的伪逆与范围条件。仅逐层写 $\kappa_N\ge0$ 而没有初层和奇异相容条件，不构成全部 Hankel 正性的无条件证明；末节[式（9.2）](#eq-9-2)也按这个递归域理解。

</div>
<!-- /editor-note -->

所以递归证明需要控制的算术量已经非常具体：

$$
\boxed{\kappa_N\ge0\quad\text{对全部层数成立}.}
$$

---

<!-- editor-anchor -->
<a id="heading-30"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-8"></a>
<!-- /editor-anchor -->
## 八、A370630 的遍历性质怎样真正接进来？

项目已经证明 A370630 是正整数的排列。我们直接使用这个结果，不再把遍历性当作待证条件。

记该排列为 $a_1,a_2,\ldots$，令

$$
x_j=\log a_j,
$$

$$
\mathsf M_N=[K(x_i-x_j)]_{i,j=1}^{N},
$$

$$
b_N=(K(x_i-x_{N+1}))_{i=1}^{N}.
$$

当 $\mathsf M_N\succ0$ 时，定义

<!-- editor-anchor -->
<a id="eq-8-1"></a>
<!-- /editor-anchor -->

$$
\boxed{
r_N=S-b_N^*\mathsf M_N^{-1}b_N.
}
\tag{8.1}
$$

<!-- editor-anchor -->
<a id="heading-31"></a>
<!-- /editor-anchor -->
### 定理 5：整数遍历上的忠实递归提升判据

<!-- editor-anchor -->
<a id="eq-8-2"></a>
<!-- /editor-anchor -->

$$
\boxed{
\mathrm{RH}
\iff
\text{从 }\mathsf M_1=(S)\text{ 出发，每一步 }r_N>0.
}
\tag{8.2}
$$

<!-- editor-anchor -->
<a id="heading-32"></a>
<!-- /editor-anchor -->
### 证明

先用实际核的已建立等价关系：

$$
\mathrm{RH}\iff K\text{ 在全实轴上正定}.
$$

<!-- editor-note:global-k-bridge -->
<div class="editor-note" id="note-global-k-bridge">

**编者条件注（global-k-bridge）。** 这里给出实际对象上的有界纸面桥，避免用短窗口结论代替全轴结论。按本卷“actual-sources”注的固定供应者，实际 $K$ 的完整零点展开和[式（2.2）](#eq-2-2)已固定。RH 下 $a_\rho=i\gamma_\rho$、$b_\rho>0$，故任意有限二次型为 $\sum_\rho b_\rho|\sum_j c_j e^{-i\gamma_\rho t_j}|^2\ge0$，绝对总质量允许换序，得到全轴正定。反之，全轴正定的二阶主矩阵给 $|K(t)|\le K(0)=S$。于是 $\int_0^\infty e^{-zt}K(t)\,dt$ 在整个 $\Re z>0$ 全纯：在任一紧子集上用 $S e^{-\eta t}$ 控制，被求导项用 $S t^m e^{-\eta t}$ 控制。它在 $\Re z>\tfrac12$ 由[式（2.2）](#eq-2-2)等于实际 $F$；亚纯恒等原理遂使实际 $F$ 的整个右半平面极点可去。但每个实际离线零点经反射都产生右半平面的非零留数极点，矛盾，故 RH。此桥只说明等价，不证明全轴正性，也不是 `ActualKernelLocalPositivity.exists_window_posDef` 的既有声明。A370630 的精确一基序列供应者是同一固定提交的 `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.lean` 中 `a`、`IsGreedyPermutation` 和 `result`；其正整数满射、正项互异及最小合资格递归均在该声明中，未在此重证或重新编译。

</div>
<!-- /editor-note -->

在 RH 下，有限互异节点的 Gram 实际上严格正定。理由是实际核有局部行为

<!-- editor-anchor -->
<a id="eq-8-3"></a>
<!-- /editor-anchor -->

$$
K(h)=S+\frac12|h|\log|h|+O(|h|),
\tag{8.3}
$$

且在非零点附近局部 Lipschitz。

若一个有限 Gram 有非零零向量 $c$，全局正性及 Cauchy–Schwarz 会给

$$
\sum_jc_jK(s-x_j)=0
\quad\text{对全部 }s.
$$

在 $s=x_j$ 附近，只有第 $j$ 项具有 $|h|\log|h|$ 的尖点；其余变化为 $O(|h|)$。因此逐一得到 $c_j=0$，矛盾。

于是 Schur 补给出每个 $r_N>0$。

反过来，若每步剩余都为正，则所有前缀矩阵 $\mathsf M_N\succ0$。

取任意有限实点 $t_1,\ldots,t_m$，令

$$
n_i(M)=\lfloor Me^{t_i}\rfloor.
$$

则

$$
\log n_i(M)-\log n_j(M)\to t_i-t_j.
$$

每个有限整数集合 $\{n_i(M)\}$ 都出现在 A370630 的某个有限前缀。因此对应 Gram 半正定；由连续性取极限，得到

$$
[K(t_i-t_j)]\succeq0.
$$

所以 $K$ 全局正定，进而 RH 成立。证毕。

<!-- editor-anchor -->
<a id="heading-33"></a>
<!-- /editor-anchor -->
### 每一步的 AURIC 二元提升

令

$$
p_N=\frac{b_N^*\mathsf M_N^{-1}b_N}{S}.
$$

则

$$
p_N+\frac{r_N}{S}=1.
$$

如果 $0\le p_N\le1$，新向量可以写成

$$
\frac{v_{N+1}}{\sqrt S}
=
\sqrt{p_N}\,\widehat w_N
+
\sqrt{1-p_N}\,e_{N+1},
$$

其中 $\widehat w_N$ 位于旧空间，$e_{N+1}$ 与旧空间正交。

<!-- editor-note:projection-endpoints -->
<div class="editor-note" id="note-projection-endpoints">

**编者条件注（projection-endpoints）。** 在 $p_N>0$ 时，$\widehat w_N$ 是实际旧空间投影除以其范数；在 $p_N=0$ 时该投影为零，$\widehat w_N$ 可任取旧空间单位向量，其系数为零，不能把零向量直接归一化。$p_N=1$ 时新正交分量为零，$e_{N+1}$ 可在附加的一维空间选取作表示，但最小 Gram 实现不增加维数。给出的 $2\times2$ 酉矩阵只是在这个已指定二维平面上的数学表示，不取得任何原生门、物理实现或跨上下文相容性权限。

</div>
<!-- /editor-note -->

在这个二维平面上，

$$
U_N=
\begin{pmatrix}
\sqrt{p_N}&-\sqrt{1-p_N}\\
\sqrt{1-p_N}&\sqrt{p_N}
\end{pmatrix}
$$

确实是酉矩阵。

所以，你提出的“两个读出、守恒、归一化、三轴、递归酉提升”，在这里全部有严格实现。

其中仍需证明的是

$$
p_N<1.
$$

相邻 Zeckendorf 展开共享一项提供了特殊的遍历组织；实际新读出还必须与所有旧读出保持关系，因此 $b_N$ 的全部分量都需要保留。

<!-- editor-anchor -->
<a id="heading-34"></a>
<!-- /editor-anchor -->
### 一个新的稳定性结论：不能要求统一的正余量

即使 RH 成立，也必有

<!-- editor-anchor -->
<a id="eq-8-4"></a>
<!-- /editor-anchor -->

$$
\boxed{\liminf_{N\to\infty}r_N=0.}
\tag{8.4}
$$

证明很直接。考虑整数 $n,n+1$ 中后出现的那个读出。它投影到全部旧空间的能量，至少等于投影到已出现的相邻整数向量的能量。因此相应步骤满足

$$
r_{N(n)}
\le
S-\frac{K(\log(1+1/n))^2}{S}.
$$

由[式（8.3）](#eq-8-3)，

<!-- editor-anchor -->
<a id="eq-8-5"></a>
<!-- /editor-anchor -->

$$
\boxed{
r_{N(n)}
\le
S-\frac{K(\log(1+1/n))^2}{S}
\sim\frac{\log n}{n}.
}
\tag{8.5}
$$

所以真正可要求的是每个有限步骤保持正性，不能额外要求所有步骤都有同一个固定正间隙。后者甚至与 RH 下实际核的近邻几何不相容。

<!-- editor-note:later-neighbor -->
<div class="editor-note" id="note-later-neighbor">

**编者条件注（later-neighbor）。** 这里所有余量和投影比较均在 RH 或等价的完整前缀严格正定条件下。写 $j(m)$ 为整数 $m$ 在这个实际排列中的位置，则 $N(n)=\max(j(n),j(n+1))-1$；当 $n\to\infty$ 时 $N(n)\to\infty$，因为任一有限前缀只含有限多个整数。这些索引可重复，取趋于无穷的子序列即可。相应最小平方残差不超过只投影到已出现相邻向量的残差；$K$ 为实偶函数，所以[式（8.5）](#eq-8-5)的平方就是模平方。连续性给上界趋零，原点尖点再给其右端 $\sim(\log n)/n$；该等价量是上界，不是 $r_{N(n)}$ 本身的渐近等式。结合每步 $r_N>0$，所得恰是条件性的 $\liminf r_N=0$。

</div>
<!-- /editor-note -->

---

<!-- editor-anchor -->
<a id="heading-35"></a>
<!-- /editor-anchor -->
<!-- editor-anchor -->
<a id="section-9"></a>
<!-- /editor-anchor -->
## 九、这次把证明推进到了哪个明确位置？

现在，“边界—体—升维—误差—酉性”已经连接到同一个实际算术对象，形成以下等价链：

<!-- editor-anchor -->
<a id="eq-9-1"></a>
<!-- /editor-anchor -->

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\text{实际球面提升在右半平面保持 }r_3\ge0\\
&\iff
\text{实际边界的 Poisson 延拓全纯}\\
&\iff E_{\mathrm{anti}}=0\\
&\iff \mu_\partial(\mathbb R)=S\\
&\iff \mathsf H_N\succeq0\quad\forall N\\
&\iff \text{A370630 实际 Gram 递归每步均可正交提升}.
\end{aligned}
}
\tag{9.1}
$$

这些条件之间的连接已经给出证明。最后的算术任务，可以选择其中最适合项目递归结构的一项固定下来，例如

<!-- editor-anchor -->
<a id="eq-9-2"></a>
<!-- /editor-anchor -->

$$
\boxed{
\alpha_{2N+1}
-
v_N^*\mathsf H_{N-1}^{-1}v_N
\ge0
\quad\text{对全部 }N,
}
\tag{9.2}
$$

并在可能出现零模时加入[式（7.1）](#eq-7-1)的交叉关系相容条件。

项目已有的历史空间酉提升为这条路线提供了重要范例，但它的具体相关函数是

$$
\langle F,e^{-|t|H}F\rangle,
$$

其平移谱为 Cauchy 密度的混合；RH 下实际算术核的谱则是

$$
\sum_\rho
\frac{\delta_{\gamma_\rho}}
{\frac14+\gamma_\rho^2}.
$$

前者在非零部分产生绝对连续谱，后者是纯点谱。因此要完成算术桥，还需要证明构造出的体保存这里指定的实际 $F$、$K$ 与全部交叉关系。项目所用的反射正性与酉扩张机制，在相应数学文献中也明确依赖所给的正性结构。[arxiv.org](https://arxiv.org/pdf/1312.6161?utm_source=chatgpt.com)

一旦[式（9.2）](#eq-9-2)或等价的 $E_{\mathrm{anti}}=0$ 得到无条件证明，就能得到 RH，再由 Robin 定理推出

$$
\sigma(n)<e^{\gamma_E}n\log\log n
\qquad\text{对所有整数 }n>5040.
$$

Robin 的这个全整数等价条件已有严格定理支持。[arxiv.org](https://arxiv.org/pdf/1211.6944?utm_source=chatgpt.com)

**目前尚未完成的正是这个全层算术正性命题。** 归一化、误差不放大、局部严格正性和维度提升，已经为它提供了准确的表示与递归结构；这一轮进一步把“需要消除的误差”明确识别为实际边界的反全纯能量，并证明了它的稳定性、总量守恒，以及它与 RH 的精确等价关系。
<!-- author-end -->

</div>
