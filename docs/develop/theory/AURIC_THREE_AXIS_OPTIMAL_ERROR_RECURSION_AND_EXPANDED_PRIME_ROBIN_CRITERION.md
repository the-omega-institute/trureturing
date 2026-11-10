# AURIC 三轴最优误差递推与扩展素数 Robin 判据

你的想法中，**“误差本身也应进入同一套关系、约束与归一化体系”可以严格实现，而且能得到可组合的误差定理。** 进一步接到项目的约数乘积结构上，还能推出一条更强的 Robin 充分判据。

需要先校准一个关键点：**误差有界、误差足够小、演化保持酉性，是三个不同条件。** 酉性能保证已有误差在同一演化中不被放大；要证明 Robin 的严格不等式，还须保证全部新增误差小于待判定的正负余量。

下面沿着你的方向，把这件事写成定义、定理和证明。重点结果有两个：

- **目标读出与误差上界服从同一个三轴归一化递推，并有最优的统一误差界。**
- 对 $\Lambda=\log\log n\ge100$，可以证明

$$
  \boxed{
  \log\frac{\sigma(n)}{e^\gamma n\log\log n}
  <
  \frac{0.0094243}{\Lambda^3}
  +\frac2{\Lambda^4}
  -
  D_{\frac{\log n}{8\Lambda^3}}(n),
  }

$$
  其中 $D_Y(n)$ 是下面定义的、可在三轴上逐素数累计的非负量。

第二条是实际的数论估计；它仍有明确的适用范围和覆盖边界。

---

<a id="section-1"></a>

## 一、把“酉性”接到项目已有的精确结构上

<a id="section-1-1"></a>

### 1. 项目确实提供了真正的酉表示

项目《稳定关系边界与三维闭合》§6 使用标量—方向载体

$$
q=(s,u),\qquad u\in\mathbb R^3,
$$
以及四元数乘法

$$
(s,u)\odot(t,v)
=
\bigl(st-\langle u,v\rangle,\;sv+tu+u\times v\bigr).
$$

其范数为

$$
N(q)=s^2+\|u\|^2,
$$
并满足

$$
N(q_1\odot q_2)=N(q_1)N(q_2).
$$

项目还给出 Pauli 矩阵实现

$$
\Phi(q)=sI-i\,u\cdot\sigma.
$$
这些是项目中已经明确建立的结构。[项目来源：§6](https://github.com/the-omega-institute/trureturing/blob/fe7b34d6b30cf7ef13938bcf35fef00afc8dbd1a/docs/develop/theory/AURIC_FIB_STABLE_RELATION_BOUNDARY_THREE_DIMENSIONAL_CLOSURE.md)

由 Pauli 关系

$$
(u\cdot\sigma)^2=\|u\|^2I
$$
直接得到

$$
\begin{aligned}
\Phi(q)^\dagger\Phi(q)
&=(sI+i\,u\cdot\sigma)(sI-i\,u\cdot\sigma)\\
&=(s^2+\|u\|^2)I.
\end{aligned}
$$

因此：

<!-- editorial-note:start unitary-representation -->
**【编者局部说明：表示与酉性的边界】** 这里的酉性结论依赖所写出的四元数乘法、范数乘法性和具体的 Pauli 表示；逐步把一个向量除以自身长度并不单独给出酉算子。误差递推只保证旧误差由酉传播保持范数，新引入的误差仍须按每个 $j\ge0$ 的步次记账；[第三节](#section-3)几何预算分配的指标另从 $j=1$ 起。
<!-- editorial-note:end unitary-representation -->

$$
\boxed{
N(q)=1
\quad\Longrightarrow\quad
\Phi(q)^\dagger\Phi(q)=I.
}
$$

**这里，归一化与酉性之间的联系成立，是因为同时给出了特定的线性矩阵表示与乘法关系。**

仅仅把某个向量每一步除以自己的长度，并不能自动证明更新是酉算子。

<a id="section-1-2"></a>

### 2. 酉性怎样控制误差

设真实状态与近似状态之间的误差满足

$$
e_{j+1}=U_je_j+\eta_j,\qquad U_j^\dagger U_j=I.
$$

这里 $\eta_j$ 表示第 $j$ 步新引入的误差。展开递推并使用保范数性，得到

$$
\boxed{
\|e_N\|
\le
\|e_0\|+\sum_{j=0}^{N-1}\|\eta_j\|.
}
$$

这说明：**酉传播保住已有误差的大小，新增误差仍须累计记账。**

两个简单例子可以确定边界：

- $e_{j+1}=\tfrac12e_j$ 使误差趋于零，但这个更新不是酉的。
- 精确更新为 $I$，近似更新为平面旋转 $R_\varepsilon$。两者每一步都酉，状态始终归一化，但从同一单位向量出发，经过 $N$ 步后的差可以达到

$$
  2\left|\sin\frac{N\varepsilon}{2}\right|.

$$

所以，证明所需的是**统一的小误差预算**。仅仅证明“不趋于无穷大”还不够。

项目对三轴也保留了相应条件：当前三读出要决定全部后续读出，必须对允许的更新保持闭合；项目 §8 还给出了隐藏方向经正交更新重新返回读口的反例。[项目来源：三轴预测闭合 §8](https://github.com/the-omega-institute/trureturing/blob/fe7b34d6b30cf7ef13938bcf35fef00afc8dbd1a/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)

---

<a id="section-2"></a>

## 二、定义一个目标量与误差都能使用的 AURIC 递推

沿用项目的金字塔

$$
\mathcal P
=
\{(X,Y,Z)\ge0:X+Z\le1,\ Y+Z\le1\}.
$$
其定义来自项目的金字塔基础公式。[项目来源：§3](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

<a id="definition-1"></a>

### 定义 1：归一化累计运算

对两个读出

$$
q,b\in[0,1],
$$
定义

$$
q\star b=q+(1-q)b.
$$

对应三个读出

<a id="eq-1"></a>

$$
\boxed{
(X,Y,Z)
=
\bigl(q,\;(1-q)b,\;(1-q)(1-b)\bigr).
}
\tag{1}
$$

它们满足

$$
X,Y,Z\ge0,\qquad X+Y+Z=1,
$$
因此位于 $\mathcal P$ 的三角截面内。

三个坐标的意义是：

| 读出轴 | 数值 | 含义 |
|---|---:|---|
| $X$ | $q$ | 此前已累计的部分 |
| $Y$ | $(1-q)b$ | 本次新增的部分 |
| $Z$ | $(1-q)(1-b)$ | 本次之后剩余的部分 |

更新后的累计值就是

$$
q'=X+Y=1-Z.
$$

这给出了你所说的“两个读出、一个约束、归一化方案”的具体实现。

<a id="theorem-1"></a>

### 定理 1：该运算与对数加法精确相容

设

$$
q_0=0,\qquad q_j=q_{j-1}\star b_j.
$$

则

<a id="eq-2"></a>

$$
\boxed{
q_m=1-\prod_{j=1}^m(1-b_j).
}
\tag{2}
$$

若所有 $b_j<1$，则

<a id="eq-3"></a>

$$
\boxed{
-\log(1-q_m)
=
\sum_{j=1}^m-\log(1-b_j).
}
\tag{3}
$$

**证明。**

由定义，

$$
1-q_j=(1-q_{j-1})(1-b_j).
$$
归纳得到[式（2）](#eq-2)；两边取负对数得到[式（3）](#eq-3)。证毕。

<!-- editorial-note:start log-endpoint -->
**【编者局部说明：对数共轭的端点】** [式 (3)](#eq-3) 的逐项取对数只在每个 $b_j<1$ 时使用；在 $b=1$ 时，$q\star1=1$ 是吸收端点，而 $-\log(1-q)$ 取到 $+\infty$。因此交换、结合的有限实数表述在 $[0,1)$ 上由对数共轭给出，端点 $1$ 以吸收运算延拓；不能把有限对数等式无条件延伸到端点。
<!-- editorial-note:end log-endpoint -->

这也证明了 $\star$ 的交换律与结合律：它通过映射

$$
q\longmapsto-\log(1-q)
$$
与非负实数加法对应。

**加法、乘法、对数约束和三轴归一化，在这里已经成为同一套精确演算。**

<a id="section-2-3"></a>

### 该递推的酉实现

从单位振幅

$$
v=
\bigl(\sqrt q,\;0,\;\sqrt{1-q}\bigr)
$$
出发，施加

$$
W_b=
\begin{pmatrix}
1&0&0\\
0&\sqrt{1-b}&\sqrt b\\
0&-\sqrt b&\sqrt{1-b}
\end{pmatrix}.
$$

直接计算可得

$$
W_b^\top W_b=I,
$$
以及

$$
W_bv
=
\bigl(
\sqrt q,\;
\sqrt{(1-q)b},\;
\sqrt{(1-q)(1-b)}
\bigr).
$$

三个分量的平方恰好是[式（1）](#eq-1)。

这里的类型关系很清楚：

> **酉性作用于平方根振幅；AURIC 三轴记录各正交通道的平方范数。**

若要保留多步过程中“在哪一步发生了损失”的全部历史，可以为每一步保留一个新的正交通道。三轴仍可读取“旧累计、新增、剩余”三个总量。若直接丢弃历史后反复复用同一个小酉矩阵，则必须重新证明闭合，不能默认得到[式（2）](#eq-2)。

---

<a id="section-3"></a>

## 三、核心定理：误差本身服从完全相同的三轴递推

这是对你本次判断最直接的严格支持。

<a id="theorem-2"></a>

### 定理 2：归一化累计的最优误差界

定义

$$
F(b_1,\ldots,b_m)
=
1-\prod_{j=1}^m(1-b_j).
$$

设真实输入与近似输入满足

$$
b_j,\widehat b_j\in[0,1],
\qquad
|b_j-\widehat b_j|\le\varepsilon_j\le1.
$$

那么

<a id="eq-4"></a>

$$
\boxed{
|F(b)-F(\widehat b)|
\le
E_m
:=
1-\prod_{j=1}^m(1-\varepsilon_j)
\le
\sum_{j=1}^m\varepsilon_j.
}
\tag{4}
$$

在只知道这些逐项误差界的条件下，第一个上界是最优的。

<a id="section-3-2"></a>

### 证明

令

$$
\ell_j=\min(b_j,\widehat b_j),\qquad
u_j=\max(b_j,\widehat b_j),\qquad
\delta_j=u_j-\ell_j.
$$

由于 $F$ 对每个输入单调递增，

$$
|F(b)-F(\widehat b)|
\le F(u)-F(\ell).
$$

右侧等于

$$
D(\ell,\delta)
=
\prod_j(1-\ell_j)
-
\prod_j(1-\ell_j-\delta_j).
$$

固定 $\delta$，对任一 $\ell_j$ 求偏导：

$$
\frac{\partial D}{\partial\ell_j}
=
-\prod_{i\ne j}(1-\ell_i)
+
\prod_{i\ne j}(1-\ell_i-\delta_i)
\le0.
$$

因此最大值在所有 $\ell_j=0$ 时取得：

$$
D(\ell,\delta)
\le1-\prod_j(1-\delta_j)
\le1-\prod_j(1-\varepsilon_j).
$$

最后，

$$
1-\prod_j(1-\varepsilon_j)\le\sum_j\varepsilon_j
$$
可直接归纳证明。

取

$$
b_j=\varepsilon_j,\qquad \widehat b_j=0,
$$
第一个误差界取等号，故它是最优的。证毕。

<a id="section-3-3"></a>

### 推论：误差与目标量具有同一种组合结构

令 $E_0=0$，则

<a id="eq-5"></a>

$$
\boxed{
E_{j+1}=E_j+(1-E_j)\varepsilon_{j+1}.
}
\tag{5}
$$

因此误差也对应三轴

<a id="eq-6"></a>

$$
\boxed{
\bigl(
E_j,\;
(1-E_j)\varepsilon_{j+1},\;
(1-E_j)(1-\varepsilon_{j+1})
\bigr).
}
\tag{6}
$$

它们同样非负、和为 $1$，同样位于 AURIC 金字塔的三角截面内。

这已经超过了“误差可以表示在三轴上”：

**我们同时得到了误差的组合律、守恒关系、全局上界和达到上界的例子。**

<a id="section-3-4"></a>

### 什么才是“长期稳定”的正确条件

如果每一步的误差界都是同一个 $\varepsilon>0$，那么

$$
E_m=1-(1-\varepsilon)^m\longrightarrow1.
$$

它始终有界，却会逐渐失去精确判定能力。

若希望始终满足 $E_m\le E_*<1$，真正需要控制的是

<a id="eq-7"></a>

$$
\boxed{
\sum_j-\log(1-\varepsilon_j)
\le-\log(1-E_*).
}
\tag{7}
$$

例如分配

$$
\varepsilon_j\le E_*2^{-j}
$$
就保证所有有限步都有 $E_m\le E_*$。

同理，归一化值收敛也不必表示其原始尺度有界。取 $b_j=\tfrac12$，则

$$
q_m=1-2^{-m}\to1,
\qquad
-\log(1-q_m)=m\log2\to\infty.
$$

因此，对无限过程必须检查**被归一化前的目标是什么，以及最终需要保住什么尺度或符号**。

---

<a id="section-4"></a>

## 四、把这个递推精确接到 Robin 判据

以下所有对数均为自然对数。

定义

$$
R(n)=\frac{\sigma(n)}{e^\gamma n\log\log n}.
$$

Robin 判据是
<!-- editorial-note:start arithmetic-domain -->
**【编者局部说明：Robin 比值的定义域与算术记号】** 下文把 $n$ 取为正整数；$\sigma(n)=\sum_{d\mid n,\ d>0}d$ 是正约数之和，$\gamma$ 是 Euler–Mascheroni 常数，$v_p(n)$ 是素数 $p$ 在 $n$ 的素因数分解中的指数。在涉及 $R(n)$、阈值和其对数的地方限定 $n\ge3$，从而 $\log\log n>0$ 且 $R(n)>0$；$n=2$ 会使无条件写下的正值与对数域失效，不能支持不加限定的 iff。Robin 的目标范围仍是 $n>5040$。本节的 Numdam 链接所供文献是 Choie、Lichiardopol、Moree、Solé (2007) 的论文，不把它署为 Robin 原始文献。
<!-- editorial-note:end arithmetic-domain -->

$$
\mathrm{RH}
\iff
R(n)<1\quad\text{对所有整数 }n>5040.
$$
这是 Robin 判据的标准形式。[文献来源](https://www.numdam.org/item/10.5802/jtnb.591.pdf)

<a id="definition-2"></a>

### 定义 2：局部素数幂读出

对每个素数 $p$，令

$$
a_p=v_p(n),\qquad
b_p(n)=p^{-a_p-1}.
$$

若 $p\nmid n$，这里取 $a_p=0$，因此

$$
b_p(n)=\frac1p.
$$

对任意 $Y\ge2$，定义

<a id="eq-8"></a>

$$
\boxed{
D_Y(n)
=
-\sum_{p\le Y}\log(1-b_p(n)),
}
\tag{8}
$$
以及

<a id="eq-9"></a>

$$
\boxed{
Q_Y(n)
=
1-\prod_{p\le Y}(1-b_p(n))
=
1-e^{-D_Y(n)}.
}
\tag{9}
$$

由[定理 1](#theorem-1)，$Q_Y(n)$ 可以逐素数按

$$
q'=q+(1-q)b_p(n)
$$
累计。

这里的 $b_p$ 是**整数素数幂结构带来的算术修正量**；计算它时产生的误差，则由上一节的 $\varepsilon_p$ 单独记录。

<a id="theorem-3"></a>

### 定理 3：Robin 的精确归一化阈值形式

设 $P$ 是 $n$ 的最大素因子，定义

$$
\mathcal M(P)=\prod_{p\le P}\left(1-\frac1p\right)^{-1}.
$$

则

<a id="eq-10"></a>

$$
\boxed{
R(n)
=
\frac{\mathcal M(P)}
{e^\gamma\log\log n}
\bigl(1-Q_P(n)\bigr).
}
\tag{10}
$$

因此

<a id="eq-11"></a>

$$
\boxed{
R(n)<1
\iff
Q_P(n)>
1-\frac{e^\gamma\log\log n}{\mathcal M(P)}.
}
\tag{11}
$$

**证明。**

约数和的乘法公式给出

$$
\frac{\sigma(n)}n
=
\prod_{p\le P}
\frac{1-p^{-a_p-1}}{1-p^{-1}}.
$$

其中未整除 $n$ 的素数对应因子为 $1$，因此包含它们不会改变乘积。于是

$$
\frac{\sigma(n)}n
=
\mathcal M(P)\prod_{p\le P}(1-b_p(n))
=
\mathcal M(P)(1-Q_P(n)).
$$

除以 Robin 的右侧即得。证毕。

这与项目 FULL_STOCK §457–458 中“完整 Euler 修正支付连续包络偏差”的结构一致。项目也明确要求这些修正来自**同一个实际整数的指数向量**。[项目来源：§457–458](https://github.com/the-omega-institute/trureturing/blob/fe7b34d6b30cf7ef13938bcf35fef00afc8dbd1a/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_FULL_STOCK.md)

<a id="section-4-3"></a>

### 有误差时怎样认证

记[式（11）](#eq-11)的阈值为 $\tau(n)$。如果

$$
|Q_P-\widehat Q_P|\le E,
\qquad
\tau(n)\le\widehat\tau+\eta,
$$
那么

<a id="eq-12"></a>

$$
\boxed{
\widehat Q_P-E>\widehat\tau+\eta
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{12}
$$

这就把“稳定”落实到了真正需要的位置：**误差扣除之后，仍然越过严格阈值。**

如果希望连这个正负判定也放进三轴，可取

$$
c=\widehat Q_P-\widehat\tau,\qquad e=E+\eta,
$$
并定义

$$
u=\frac{(c,e,1)}{\sqrt{1+c^2+e^2}}.
$$

第三坐标保留已知锚点 $1$，所以

$$
c=\frac{u_1}{u_3},\qquad e=\frac{u_2}{u_3}.
$$
认证条件就是

$$
u_1>u_2.
$$

再用

$$
(X,Y,Z)=\left(\frac14,\frac14,\frac14\right)+\frac18u
$$
映入 AURIC 金字塔内部。这样，**误差大小和待证符号都被保留了**。

---

<a id="section-5"></a>

## 五、继续推进数论：同时控制“补足后的残差”和“尺度漂移”

前面的表示定理本身还不供应素数分布估计。下面加入一个无条件的外部数论输入，推出新的充分判据。

<a id="section-5-1"></a>

### 使用的已知输入

Axler 的《On Robin’s inequality》定理 1.3 给出：对所有 $m>5040$，

<a id="eq-13"></a>

$$
\boxed{
R(m)
<
1+\frac{A_0}{(\log\log m)^3},
\qquad
A_0=0.0094243.
}
\tag{13}
$$

这里使用的是直接关于 $\sigma(m)/m$ 的界；该定理的有限例外均不超过 $5040$。[原文：Theorem 1.3](https://arxiv.org/pdf/2110.13478v3)

<a id="theorem-4"></a>

### 定理 4：双误差修复恒等式与上界

设 $n>5040$，记

$$
\Lambda=\log\log n.
$$

选一个所有素因子均不超过 $Y$ 的正整数乘子 $M$。则

<a id="eq-14"></a>

$$
\boxed{
\log R(n)
<
\frac{A_0}{\Lambda^3}
-D_Y(n)
+D_Y(nM)
+\frac{\log M}{\Lambda\log n}.
}
\tag{14}
$$

最后两项是两个明确的非负误差读出：

$$
E_{\mathrm{res}}=D_Y(nM),
\qquad
E_{\mathrm{scale}}
=\frac{\log M}{\Lambda\log n}.
$$

<a id="section-5-3"></a>

### 证明

由于 $M$ 只增加 $Y$ 以下的素数指数，

$$
\log\frac{\sigma(nM)/(nM)}{\sigma(n)/n}
=
D_Y(n)-D_Y(nM).
$$

令

$$
\delta
=
\log\log(nM)-\Lambda
=
\log\left(1+\frac{\log M}{\log n}\right).
$$

于是得到精确恒等式

$$
\log R(n)
=
\log R(nM)
+\log\frac{\Lambda+\delta}{\Lambda}
-D_Y(n)+D_Y(nM).
$$

由[式（13）](#eq-13)，

$$
\log R(nM)
<
\frac{A_0}{(\Lambda+\delta)^3}
\le\frac{A_0}{\Lambda^3}.
$$

另外，

$$
\log\frac{\Lambda+\delta}{\Lambda}
\le\frac{\delta}{\Lambda}
\le\frac{\log M}{\Lambda\log n}.
$$

合并即得。证毕。

<!-- editorial-note:start certificate-domains -->
**【编者局部说明：继承的证书假设】** [定理 4](#theorem-4) 使用同一个实际的 $n$ 与同一个乘子 $M$：$n>5040$、$\Lambda=\log\log n>0$、$Y\ge2$，且 $M$ 为 $Y$-smooth 正整数（允许 $M=1$）；残差 $D_Y(nM)$ 与尺度项 $\log M/(\Lambda\log n)$ 必须由这个同一个 $nM$ 一起支付。[定理 5](#theorem-5) 继承这些条件，并额外要求 $\Lambda\ge100$。
<!-- editorial-note:end certificate-domains -->

这里形成了一个实际的误差控制问题：

- 增加素数指数，能让 $E_{\mathrm{res}}$ 变小；
- 增加指数也会提高 $\log M$，使 $E_{\mathrm{scale}}$ 增大；
- 必须在同一个 $M$ 上同时控制两者。

这正好符合你提出的方向：**误差不能分别凭直觉宣称很小，必须进入共同约束。**

---

<a id="section-6"></a>

## 六、本轮的强化定理：把素数范围扩大到 $\log n/[8(\log\log n)^3]$

<a id="theorem-5"></a>

### 定理 5：分层修复的 Robin 充分判据

设

$$
\Lambda=\log\log n\ge100,
\qquad
Y=\frac{\log n}{8\Lambda^3}.
$$

则

<a id="eq-15"></a>

$$
\boxed{
\log R(n)
<
\frac{A_0}{\Lambda^3}
+\frac2{\Lambda^4}
-D_Y(n).
}
\tag{15}
$$

因此

<a id="eq-16"></a>

$$
\boxed{
D_Y(n)\ge
\frac{A_0}{\Lambda^3}+\frac2{\Lambda^4}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{16}
$$

下面给出完整证明。

<a id="section-6-2"></a>

### 第一步：小素数补多次，大素数补一次

取

$$
X=\Lambda^5,
\qquad
k=\left\lceil\frac{4\log\Lambda}{\log2}\right\rceil,
$$
并定义

<a id="eq-17"></a>

$$
\boxed{
M=
\left(\prod_{p\le Y}p\right)
\left(\prod_{p\le X}p^k\right).
}
\tag{17}
$$

在 $\Lambda\ge100$ 时有 $X\le Y$。

因此：

- $p\le X$ 的指数增加 $k+1$；
- $X<p\le Y$ 的指数增加 $1$。

<!-- editorial-note:start floor-ceiling-endpoints -->
**【编者局部说明：分层步骤的端点】** [定理 5](#theorem-5) 的 $k=\left\lceil4\log\Lambda/\log2\right\rceil$ 是整数，且 $X=\Lambda^5$、$Y=\log n/(8\Lambda^3)$ 都是实数阈值；$\Lambda\ge100$ 时由论文给出的起点与正导数不等式得到 $X\le Y$。第二步取 $N=\lfloor X\rfloor$，所以对实数范围 $X<p\le Y$ 的素数有 $p\ge N+1$，望远镜积的端点正是 $N$。
<!-- editorial-note:end floor-ceiling-endpoints -->

这种分层避免了让所有素数都承担同样高的补足成本。

<a id="section-6-3"></a>

### 第二步：控制补足后的残差

对于 $p\le X$，补足后

$$
p^{-v_p(nM)-1}\le p^{-k-2}.
$$

故

<a id="eq-18"></a>

$$
\sum_{p\le X}-\log(1-p^{-v_p(nM)-1})
\le\log\zeta(k+2)
<2^{-k-1}
\le\frac1{2\Lambda^4}.
\tag{18}
$$

这里的 $\zeta$ 估计只发生在实数 $s>1$ 的绝对收敛区域。具体地，对 $s\ge3$，

$$
\zeta(s)-1
<
2^{-s}+\int_2^\infty x^{-s}\,dx
\le2^{1-s},
$$
再用 $\log\zeta(s)<\zeta(s)-1$ 即可。它不涉及 RH。

对于 $X<p\le Y$，补一次已保证

$$
p^{-v_p(nM)-1}\le p^{-2}.
$$

令 $N=\lfloor X\rfloor$。利用望远镜积

$$
\prod_{m=N+1}^{L}\left(1-\frac1{m^2}\right)
=
\frac{N(L+1)}{(N+1)L},
$$
可得

<a id="eq-19"></a>

$$
\begin{aligned}
\sum_{X<p\le Y}-\log(1-p^{-v_p(nM)-1})
&\le
\sum_{m>N}-\log(1-m^{-2})\\
&=
\log\left(1+\frac1N\right)\\
&<\frac1N
\le\frac1{2\Lambda^4}.
\end{aligned}
\tag{19}
$$

合并[式（18）](#eq-18)与[式（19）](#eq-19)：

<a id="eq-20"></a>

$$
\boxed{
D_Y(nM)<\Lambda^{-4}.
}
\tag{20}
$$

<a id="section-6-4"></a>

### 第三步：控制尺度漂移

记

$$
\vartheta(x)=\sum_{p\le x}\log p.
$$

<!-- editorial-note:start theta-real-x -->
**【编者局部说明：实数 $x$ 的 dyadic theta 界】** [式 (21)](#eq-21) 对任意实数 $x\ge2$ 使用；先在整数二进区间上由中心二项式系数控制 $\vartheta(2m)-\vartheta(m)$，再用包含 $x$ 的二进区间覆盖得到同一常数的实数阈值界。尺度估计中的 $40\Lambda^8\log\Lambda\le e^\Lambda$ 在 $\Lambda=100$ 验证，并由所写导数为正延伸到全部 $\Lambda\ge100$；这是端点加单调性的纸面估计，不是数值搜索。
<!-- editorial-note:end theta-real-x -->

一个足够使用的初等界是

<a id="eq-21"></a>

$$
\vartheta(x)<4x\log2.
\tag{21}
$$

其证明很短：所有 $m<p\le2m$ 的素数都整除 $\binom{2m}{m}$，所以

$$
\vartheta(2m)-\vartheta(m)
\le\log\binom{2m}{m}
\le2m\log2.
$$
在二进区间上求和即可得到[式（21）](#eq-21)。

因此

$$
\begin{aligned}
\log M
&=\vartheta(Y)+k\vartheta(X)\\
&\le4Y+20X\log\Lambda\\
&=\frac{e^\Lambda}{2\Lambda^3}
  +20\Lambda^5\log\Lambda.
\end{aligned}
$$

在 $\Lambda\ge100$ 时，

$$
40\Lambda^8\log\Lambda\le e^\Lambda.
$$
例如对两边比值取对数，其导数为

$$
1-\frac8\Lambda-\frac1{\Lambda\log\Lambda}>0,
$$
而起点 $\Lambda=100$ 已满足不等式。这个估计也保证了前面使用的 $X\le Y$。

于是

$$
\log M\le\frac{e^\Lambda}{\Lambda^3}
=\frac{\log n}{\Lambda^3},
$$
所以

<a id="eq-22"></a>

$$
\boxed{
\frac{\log M}{\Lambda\log n}\le\Lambda^{-4}.
}
\tag{22}
$$

<a id="section-6-5"></a>

### 第四步：代回共同预算

把[式（20）](#eq-20)和[式（22）](#eq-22)代入[定理 4](#theorem-4)：

$$
\log R(n)
<
\frac{A_0}{\Lambda^3}
-D_Y(n)
+\frac1{\Lambda^4}
+\frac1{\Lambda^4}.
$$

这就是[式（15）](#eq-15)，定理得证。

**与此前只控制 $p\le\Lambda^4$ 的结果相比，这里在相同的预算下，把素数范围扩大到了**

$$
\boxed{
p\le\frac{\log n}{8(\log\log n)^3}.
}
$$

---

<a id="section-7"></a>

## 七、把新定理写成你提出的三轴误差证书

定义

$$
B(\Lambda)
=
\frac{A_0}{\Lambda^3}+\frac2{\Lambda^4}.
$$

由于

$$
Q_Y(n)=1-e^{-D_Y(n)},
$$
[式（16）](#eq-16)等价于下列充分条件：

<a id="eq-23"></a>

$$
\boxed{
Q_Y(n)\ge1-e^{-B(\Lambda)}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{23}
$$

<!-- editorial-note:start approximate-certificate-inputs -->
**【编者局部说明：[第七节](#section-7)证书的输入与精确读出】** 本节继承[定理 5](#theorem-5) 的 $\Lambda=\log\log n\ge100$，并始终对同一个实际整数 $n$ 使用同一个 $Y=\log n/(8\Lambda^3)$。应用[定理 2](#theorem-2) 时，对每个 $p\le Y$ 须有 $b_p(n),\widehat b_p\in[0,1]$、$0\le\varepsilon_p\le1$，并满足下文所写的逐项绝对误差界。这里 $\widehat Q_Y:=1-\prod_{p\le Y}(1-\widehat b_p)$ 是这些近似输入的精确有限乘积读出：从 $\widehat q_0=0$ 起，按同一素数集合逐项使用 $\widehat q'=\widehat q+(1-\widehat q)\widehat b_p$ 的同一递推。[式 (24)](#eq-24) 中的 $\widehat Q_Y$、$E_Y$ 与 $1-e^{-B(\Lambda)}$ 均指精确数学量；若实际求值还引入读出、误差预算、$B(\Lambda)$ 或阈值的舍入误差，须另行提供认证界，以读出的认证下界、误差预算与阈值的认证上界作比较。局部输入的认证误差不自动提供这些额外求值的认证界。
<!-- editorial-note:end approximate-certificate-inputs -->

如果各个局部读出有认证误差

$$
|b_p-\widehat b_p|\le\varepsilon_p,
$$
则由[定理 2](#theorem-2)，

$$
|Q_Y-\widehat Q_Y|
\le
E_Y
=
1-\prod_{p\le Y}(1-\varepsilon_p).
$$

因此得到完整的、带误差的证书：

<a id="eq-24"></a>

$$
\boxed{
\widehat Q_Y-E_Y
\ge1-e^{-B(\Lambda)}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{24}
$$

这里允许“$\ge$”：因为[定理 5](#theorem-5) 的总上界本身是严格小于。

这条链条中的每个对象都有明确作用：

| 对象 | 数学作用 |
|---|---|
| $b_p=p^{-v_p(n)-1}$ | 真实整数的局部素数幂读出 |
| $Q_Y$ | 按三轴守恒递推累计的算术修正 |
| $\varepsilon_p$ | 局部取得或计算误差 |
| $E_Y$ | 按同一个递推累计的全局误差界 |
| $1-e^{-B(\Lambda)}$ | 已证明足以推出 Robin 的阈值 |

**归一化、酉实现、误差传播和严格不等式，在这里已经接成了一条可以逐步核验的证明链。**

---

<a id="section-8"></a>

## 八、为什么这还没有完成 RH，以及剩余目标应怎样表述

<a id="section-8-1"></a>

### 1. 潜在反例必须满足更强的指数约束

若 $\Lambda\ge100$ 且 $R(n)\ge1$，[定理 5](#theorem-5) 强迫

$$
D_Y(n)<B(\Lambda).
$$

又因为

$$
-\log(1-x)\ge x,
$$
必有

<a id="eq-25"></a>

$$
\boxed{
\sum_{p\le Y}p^{-v_p(n)-1}
<
B(\Lambda).
}
\tag{25}
$$

例如，对任意 $2\le x\le Y$ 和整数 $j\ge1$，

<a id="eq-26"></a>

$$
\boxed{
\#\{p\le x:v_p(n)<j\}
<
B(\Lambda)x^j.
}
\tag{26}
$$

证明是：每一个被计数的素数都满足

$$
p^{-v_p(n)-1}\ge p^{-j}\ge x^{-j},
$$
再应用[式（25）](#eq-25)。

所以，潜在反例必须在一个相当大的素数范围内，具备非常充足的小素数和低层素数幂。

<a id="section-8-2"></a>

### 2. 不能把充分判据直接升级为全称命题

这里还能明确证明一个边界：**并非所有整数的 $D_Y(n)$ 都会超过[式（16）](#eq-16)的预算。**

考虑

$$
n=m!.
$$

初等积分估计给出

$$
\log(m!)\sim m\log m,\qquad
\Lambda\sim\log m,
$$
从而本轮的截断点满足

$$
Y\sim\frac{m}{8(\log m)^2}.
$$

对每个 $p\le Y$，

$$
v_p(m!)
\ge\left\lfloor\frac mp\right\rfloor
\ge\left\lfloor\frac mY\right\rfloor.
$$

因此

$$
D_Y(m!)
<
Y\,2^{-\lfloor m/Y\rfloor}.
$$

而

$$
\frac mY\sim8(\log m)^2,
$$
所以对任意固定 $A>0$，都有

<a id="eq-27"></a>

$$
\boxed{
D_Y(m!)=o(\Lambda^{-A}).
}
\tag{27}
$$

这意味着这族整数最终不会满足[式（16）](#eq-16)的充分条件。它们需要由其他余量来认证，例如前面研究的价格偏离损失、完整支撑估计或完整的

$$
\Delta_K(n)-G(K)
$$
分解。

<!-- editorial-note:start factorial-boundary -->
**【编者局部说明：阶乘族的非覆盖边界】** [第八节](#section-8)的 $n=m!$ 只证明局部充分条件最终失效：$D_Y(m!)=o(\Lambda^{-A})$ 对每个固定 $A>0$，因而这族整数不会被[式 (16)](#eq-16) 的预算自动认证。它不是 Robin 反例，也不否定其他余量、完整支撑估计或 $\Delta_K(n)-G(K)$ 分解；本文没有给出统一的 $D_Y\ge B$ 或 RH 结论。
<!-- editorial-note:end factorial-boundary -->

**因此，下一步不能把“所有整数的局部修正都超过预算”当作待证引理；这个命题本身已经被上述家族排除了。**

<a id="section-8-3"></a>

### 3. 对你的原判断，现在可以给出更精确的定理化表述

可以成立的表述是：

> **在指定的算术任务中，若两个读出及其关系允许保留尺度与符号的归一化，并且组合操作对这些读出闭合，那么目标量和误差预算可以共同表示为 AURIC 三轴上的守恒递推；其振幅层可以采用酉实现。若累计误差小于已建立的正负余量，该读出就能给出可靠的严格证明。**

其中，“已建立的正负余量”仍然必须来自数论。

本轮已经证明了：

$$
\boxed{
\text{三轴守恒递推}
\;+\;
\text{最优误差传播界}
\;+\;
\text{扩大素数范围的 Robin 充分判据}.
}
$$

仍需解决的是：对尚未被这个判据覆盖的实际整数，如何利用同一来源的完整指数结构，证明最终的有符号余量为正。项目中的 FIB 关系若要在这里继续发挥作用，需要进一步给出这些**带素数权重的指数约束或余量下界**。酉性与归一化已经能保证证书的组织和可靠传播；RH 所要求的全称严格正性，还需要这一层新的算术估计。
