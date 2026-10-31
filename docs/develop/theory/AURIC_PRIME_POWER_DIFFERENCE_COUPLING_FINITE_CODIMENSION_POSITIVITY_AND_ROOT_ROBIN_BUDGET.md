# AURIC：素数幂差分耦合、有限余维正性与 Robin 根尺度预算

> **来源与阅读范围。** 下列“原稿正文”完整保留所供作者原文；源文件 SHA-256 为 <span style="display:inline-block;max-width:100%;overflow-wrap:anywhere"><code>2b7f13b7220d23cd9948d55ae1769af3042e03628ed5771948aaea8dd2b22858</code></span>。标题与导航为编排文字，数学定界符作可移植 Markdown 转写，原编号、固定链接及行距保留。原稿后的[编者附注](#editorial-notes)另列定义补足、纸面核对和限制；“上一轮”的必要核公式及 Robin 恒等式不以待发布稿件为依赖。本文没有新增 Lean、数值或原生取得认证。

导航：[一](#section-1) · [二](#section-2) · [三](#section-3) · [四](#section-4) · [五](#section-5) · [六](#section-6) · [七](#section-7) · [八](#section-8) · [九](#section-9) · [附注](#editorial-notes)

> **编号排版。** 原稿的 38 个公式编号逐一显示在对应公式下方的独立文本行，编号 (1)–(38) 与公式前的 `eq-1`–`eq-38` 锚点一一对应；点击编号即回到该公式。原稿的 `\tag{n}` 仅转为下方的 `(n)`，公式内部内容不变。比对原稿时，将这行编号还原为该公式末尾的 `\tag{n}`；其余数学与正文按原顺序比对。

<a id="author-manuscript"></a>

<!-- author-source-start -->
继续。这一轮可以把上一轮的“短窗口内全部正定”，推进成一个更强的结论：

> **在任意固定长度的对数区间内，完整实际核的所有高矩方向都能无条件证明严格为正；每个有限样本的全部潜在非正性，可以精确压缩到一个维数有统一上界的低矩 Schur 核心。**

同时，还能证明一条直接联系你最初所说的“素数、斐波那契项、斐波那契素数项”的关系：

> **对实际核进行三点指数差分后，远距离读出的首项耦合，恰好由两个整数之比是否为素数幂决定。**

最后，Robin 分解中的正预算也可以从上一轮的 $1/(T\log T)$ 下界，加强到


<a id="display-1"></a>

$$
\frac{1}{\sqrt T\log T}
$$


这一尺度，并给出明确常数。

以下给出纸面定义、定理与证明。它们进一步缩小了尚未解决的部分，但仍未完成 RH 的全局证明。

---

<a id="section-1"></a>

## 一、固定实际核，保留全部素数来源

沿用上一轮的实际核


<a id="display-2"></a>

$$
\mathscr K(t)=e^{-|t|/2}\mathcal F(e^{|t|}),
$$


其中


<a id="display-3"></a>

$$
\begin{aligned}
\mathcal F(x)
={}&x(1+\gamma-\log x)-\log(2\pi)\\
&+\sum_{k\ge1}\frac{x^{-2k}}{2k(2k+1)}
+\sum_{p^j\le x}\log p\left(\frac{x}{p^j}-1\right).
\end{aligned}
$$


记


<a id="display-4"></a>

$$
S=\mathscr K(0)=2+\gamma-\log(4\pi)>0.
$$


上一轮已从这个公式证明


<a id="display-5"></a><a id="eq-1"></a>

$$
\boxed{
\mathscr K(h)
=
S+\frac h2\log h
+\frac{\gamma-1+\log(2\pi)}2h
+O(h^2|\log h|)
}
\qquad(h\downarrow0).
$$

<p align="center" data-equation-number="1"><a href="#eq-1">(1)</a></p>


下面使用的每个关系矩阵，都由这个同一实际核产生。

为使素数来源更清楚，令


<a id="display-6"></a>

$$
\Lambda(m)=
\begin{cases}
\log p,&m=p^j,\\
0,&\text{其他情形},
\end{cases}
$$


并定义


<a id="display-7"></a>

$$
c_k=\frac1{2k(2k+1)},\qquad
\lambda_k=2k+\frac12,
$$



<a id="display-8"></a>

$$
P(t)=\sum_{k\ge1}c_ke^{-\lambda_k|t|}.
$$


对 $t\ge0$，实际核可以精确写为


<a id="display-9"></a><a id="eq-2"></a>

$$
\boxed{
\mathscr K(t)
=
N(t)+P(t)
+\sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}\,
g(t-\log m),
}
$$

<p align="center" data-equation-number="2"><a href="#eq-2">(2)</a></p>


其中


<a id="display-10"></a>

$$
N(t)=(1+\gamma-t)e^{t/2}
-\log(2\pi)e^{-t/2},
$$



<a id="display-11"></a>

$$
g(u)=
\begin{cases}
2\sinh(u/2),&u\ge0,\\
0,&u<0.
\end{cases}
$$


对每个固定 $t$，式 (2) 的素数和实际只有有限项。

项目的[有限零点 Gram 层级](https://github.com/the-omega-institute/trureturing/blob/1a5020ef545f364fd70cf83f8829c38302284b1b/Blueprint/D5/S3/Weil/FiniteZeroGramHierarchy.md)已经明确区分了“给定正 Gram 分解”与“证明实际算术关系具有正性”。下面始终先处理实际二次型，再对已经证明为正的部分作归一化。

---

<a id="section-2"></a>

## 二、三点指数差分：把远距离耦合还原为实际素数幂关系

### 定义 1：指数差分读出

对 $h>0$，定义


<a id="display-12"></a><a id="eq-3"></a>

$$
\boxed{
\Delta_hf(t)
=
f(t+h)-2\cosh(h/2)f(t)+f(t-h).
}
$$

<p align="center" data-equation-number="3"><a href="#eq-3">(3)</a></p>


相应的带符号读出为


<a id="display-13"></a>

$$
\omega_{t,h}
=
\delta_{t-h}
-2\cosh(h/2)\delta_t
+\delta_{t+h}.
$$


它满足两个精确约束：


<a id="display-14"></a><a id="eq-4"></a>

$$
\boxed{
\int e^{u/2}\,d\omega_{t,h}(u)=0,
\qquad
\int e^{-u/2}\,d\omega_{t,h}(u)=0.
}
$$

<p align="center" data-equation-number="4"><a href="#eq-4">(4)</a></p>


因此


<a id="display-15"></a>

$$
\Delta_he^{t/2}=\Delta_he^{-t/2}=0.
$$


这一步直接使用了对数坐标与乘法尺度之间的关系。

### 引理 1：双差分消去背景项

当所有取样点位于正半轴时，


<a id="display-16"></a>

$$
\Delta_hN(t)
=
-2h\sinh(h/2)e^{t/2},
$$


所以


<a id="display-17"></a><a id="eq-5"></a>

$$
\boxed{\Delta_h^2N(t)=0.}
$$

<p align="center" data-equation-number="5"><a href="#eq-5">(5)</a></p>


这里 $\Delta_h^2$ 表示连续施加两次 $\Delta_h$。

**证明。** 指数项 $e^{\pm t/2}$ 被一次差分消去，而直接展开可得


<a id="display-18"></a>

$$
\Delta_h(te^{t/2})
=
2h\sinh(h/2)e^{t/2}.
$$


第二次差分再消去剩余的 $e^{t/2}$。证毕。

### 引理 2：素数幂项只留下一个有限窗口

定义


<a id="display-19"></a>

$$
\tau_h(u)=
\begin{cases}
2\sinh((h-|u|)/2),&|u|\le h,\\
0,&|u|>h,
\end{cases}
$$


以及


<a id="display-20"></a>

$$
\upsilon_h(u)=\Delta_h\tau_h(u).
$$


直接使用双曲函数加法公式，得到


<a id="display-21"></a>

$$
\Delta_hg=\tau_h,
$$


从而


<a id="display-22"></a>

$$
\operatorname{supp}\upsilon_h\subset[-2h,2h],
\qquad
\upsilon_h(0)=-2\sinh h.
$$


因此，对于 $d>2h$，


<a id="display-23"></a><a id="eq-6"></a>

$$
\boxed{
\Delta_h^2\mathscr K(d)
=
\Gamma_h(d)
+
\sum_{|\log m-d|\le2h}
\frac{\Lambda(m)}{\sqrt m}
\,\upsilon_h(d-\log m),
}
$$

<p align="center" data-equation-number="6"><a href="#eq-6">(6)</a></p>


其中


<a id="display-24"></a><a id="eq-7"></a>

$$
\Gamma_h(d)
=
\sum_{k\ge1}
c_ke^{-\lambda_kd}
\left[
2\cosh(\lambda_kh)-2\cosh(h/2)
\right]^2
>0.
$$

<p align="center" data-equation-number="7"><a href="#eq-7">(7)</a></p>


对固定 $d>0$，还有


<a id="display-25"></a>

$$
\Gamma_h(d)=O(h^4).
$$


因为方括号为 $O(\lambda_k^2h^2)$，而在 $h<d/4$ 时，平方后的级数受一个指数衰减的可求和级数控制。

式 (6) 很关键：**背景项被精确消去，剩余算术关系全部来自**


<a id="display-26"></a>

$$
e^{d-2h}\le p^j\le e^{d+2h}
$$


**中的实际素数幂。** 这些项的符号仍完整保留。

---

<a id="section-3"></a>

## 三、定理：跨任意固定有限尺度的差分关系趋于正交

取任意固定的互异中心


<a id="display-27"></a>

$$
t_1,\ldots,t_m.
$$


它们之间的距离可以任意大。定义差分关系矩阵


<a id="display-28"></a><a id="eq-8"></a>

$$
\boxed{
W_h(i,j)
=
\Delta_h^2\mathscr K(t_i-t_j).
}
$$

<p align="center" data-equation-number="8"><a href="#eq-8">(8)</a></p>


这就是对每个中心采用 $\omega_{t_i,h}$ 后，由原实际核得到的二次型矩阵。

### 定义 2：素数幂比值矩阵

定义实对称矩阵 $\mathsf A$：


<a id="display-29"></a>

$$
\mathsf A_{ii}=0,
$$



<a id="display-30"></a><a id="eq-9"></a>

$$
\boxed{
\mathsf A_{ij}
=
\begin{cases}
\dfrac{\log p}{p^{r/2}},
&e^{|t_i-t_j|}=p^r,\ r\ge1,\\[2mm]
0,&\text{否则}.
\end{cases}
}
$$

<p align="center" data-equation-number="9"><a href="#eq-9">(9)</a></p>


### 定理 1：真实关系的算术极限

当 $h\downarrow0$ 时，


<a id="display-31"></a><a id="eq-10"></a>

$$
\boxed{
\frac{W_h}{2h}
-\log(1/h)I_m
\longrightarrow
(1-\gamma-\log\pi)I_m-\mathsf A
}
$$

<p align="center" data-equation-number="10"><a href="#eq-10">(10)</a></p>


在矩阵算子范数中成立。

因此，任意固定有限组中心的 $W_h$，在充分小的 $h>0$ 下都严格正定。

### 证明

先看非对角项。固定


<a id="display-32"></a>

$$
d=|t_i-t_j|>0.
$$


素数幂对数在每个有界区间内只有有限个。因此，当 $h$ 足够小时：

- 若 $e^d$ 不是素数幂，式 (6) 中的窗口为空，于是

  <a id="display-33"></a>

  $$
  W_h(i,j)=\Gamma_h(d)=O(h^4).
  $$


- 若 $e^d=p^r$，窗口内仅有这一项，于是

  <a id="display-34"></a>

  $$
  W_h(i,j)
  =
  \Gamma_h(d)
  -2\sinh(h)\frac{\log p}{p^{r/2}}.
  $$


所以


<a id="display-35"></a>

$$
\frac{W_h(i,j)}{2h}\longrightarrow-\mathsf A_{ij}.
$$


再看对角项。记 $c=\cosh(h/2)$，则精确地


<a id="display-36"></a>

$$
W_h(i,i)
=
(4c^2+2)S-8c\mathscr K(h)+2\mathscr K(2h).
$$


将式 (1) 代入，得到


<a id="display-37"></a><a id="eq-11"></a>

$$
\boxed{
W_h(i,i)
=
2h\log(1/h)
+
2(1-\gamma-\log\pi)h
+
O(h^2|\log h|).
}
$$

<p align="center" data-equation-number="11"><a href="#eq-11">(11)</a></p>


固定维数下，逐项收敛推出算子范数收敛。因此


<a id="display-38"></a>

$$
\lambda_{\min}\!\left(\frac{W_h}{2h}\right)
=
\log(1/h)+1-\gamma-\log\pi
-\lambda_{\max}(\mathsf A)+o(1).
$$


右端在 $h\downarrow0$ 时趋于正无穷，所以 $W_h\succ0$。证毕。

### 归一化后的稳定性

所有对角项相等，记为


<a id="display-39"></a>

$$
V_h=W_h(i,i).
$$


则


<a id="display-40"></a><a id="eq-12"></a>

$$
\boxed{
G_h:=\frac{W_h}{V_h}\longrightarrow I_m.
}
$$

<p align="center" data-equation-number="12"><a href="#eq-12">(12)</a></p>


更精确地，


<a id="display-41"></a>

$$
G_h
=
I_m-\frac{\mathsf A}{\log(1/h)}
+o\!\left(\frac1{\log(1/h)}\right).
$$


这说明：**对任意固定有限组远距离位置，适当的差分读出在归一化后可以达到统一良好的条件数。**

同时必须保留其总量：


<a id="display-42"></a><a id="eq-13"></a>

$$
\boxed{
V_h\sim2h\log(1/h)\longrightarrow0.
}
$$

<p align="center" data-equation-number="13"><a href="#eq-13">(13)</a></p>


归一关系稳定，与未归一信号大小，是这里需要同时记录的两个量。

---

<a id="section-4"></a>

## 四、这怎样分类素数、斐波那契项与斐波那契素数项？

令


<a id="display-43"></a>

$$
t_i=\log m_i,
$$


其中 $m_i$ 是互异正整数。那么式 (9) 的条件变为


<a id="display-44"></a><a id="eq-14"></a>

$$
\boxed{
\frac{\max(m_i,m_j)}{\min(m_i,m_j)}
\text{ 是整数素数幂。}
}
$$

<p align="center" data-equation-number="14"><a href="#eq-14">(14)</a></p>


因此，最初的 $<5040$ 分类问题现在具有一个统一的解析解释。以下结论也适用于任意其他有限上界。

| 取样标签 | $\mathsf A$ 中的关系 | 差分关系的首项 |
|---|---|---|
| 两个不同素数 $p,q$ | 比值不是整数，故无边 | $W_h(i,j)=O(h^4)$ |
| 两个不同斐波那契素数 | 同样无边 | $W_h(i,j)=O(h^4)$ |
| 两个不同的正斐波那契值 | 较大值除以较小值为 $p^r$ 时有边 | $-2h\,\log p/p^{r/2}$ |
| $1$ 与正整数 $m>1$ | 恰当 $m$ 为素数幂时有边 | $-2h\,\Lambda(m)/\sqrt m$ |

这里的斐波那契值按数值去重，避免把相同的 $1$ 当成两个不同节点。

于是我们得到了一个明确区别：

**素数之间的乘法原子关系，主要通过它们与 $1$、素数幂及合数的联系显现；两个不同素数本身，在上述差分读出的首项中没有直接耦合。**

对于项目已经证明的 A370630 贪心排列，可以把它作为这些整数顶点进入关系矩阵的顺序。项目的[Zeckendorf 贪心排列定理](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)保证所有正整数最终都进入；进入后，实际乘法耦合按式 (14) 填写。

这使三个环节有了各自严格的作用：


<a id="display-45"></a>

$$
\text{Zeckendorf 贪心遍历}
\;\longrightarrow\;
\text{实际整数取样}
\;\longrightarrow\;
\text{素数幂比值关系}.
$$


### 接回 AURIC 的三轴递归

加入一个新中心 $x$，令它与旧中心的素数幂边权组成向量 $\mathbf a$，并设


<a id="display-46"></a>

$$
\ell_h=\log(1/h)+1-\gamma-\log\pi.
$$


由定理 1，


<a id="display-47"></a>

$$
\frac{W_h}{2h}=\ell_hI-\mathsf A+o(1),
\qquad
\frac{\mathbf w_h}{2h}=-\mathbf a+o(1),
$$


其中 $\mathbf w_h$ 是新旧关系列。

已有空间解释的归一比例为


<a id="display-48"></a>

$$
p_h=\frac{\mathbf w_h^*W_h^{-1}\mathbf w_h}{V_h}.
$$


展开逆矩阵，得到


<a id="display-49"></a><a id="eq-15"></a>

$$
\boxed{
p_h
=
\frac{\|\mathbf a\|^2}{\ell_h^2}
+O(\ell_h^{-3}),
\qquad
Z_h=1-p_h\longrightarrow1.
}
$$

<p align="center" data-equation-number="15"><a href="#eq-15">(15)</a></p>


选定一个旧中心 $t_j$，再定义


<a id="display-50"></a>

$$
X_h=\left|\frac{w_{h,j}}{V_h}\right|^2,
\qquad
Y_h=p_h-X_h.
$$


则精确地


<a id="display-51"></a><a id="eq-16"></a>

$$
\boxed{
X_h,Y_h,Z_h\ge0,
\qquad
X_h+Y_h+Z_h=1.
}
$$

<p align="center" data-equation-number="16"><a href="#eq-16">(16)</a></p>


它们分别对应选定旧方向、其余旧方向、新增正交剩余。按项目的原五模式次序，可以使用


<a id="display-52"></a>

$$
\left(
0,\frac{w_{h,j}}{V_h},
\sqrt{Z_h},\sqrt{Y_h},0
\right)
$$


编码该步的三个占据读出，同时保存符号、完整矩阵与总量 $V_h$。这是项目[三轴误差几何](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/docs/develop/theory/AURIC_THREE_AXIS_ERROR_GEOMETRY_UNITARY_COMPATIBILITY_AND_ENDOGENOUS_STABILITY_V35.md)在这些已证明为正的实际差分关系上的具体应用。

---

<a id="section-5"></a>

## 五、更强的定理：任意固定窗口只剩有限维非正可能性

上一节证明的是特定差分读出。现在处理窗口内的**全部实际关系方向**。

### 定义 3：实际二次型与矩约束

固定任意 $D>0$，取有限原子复测度


<a id="display-53"></a>

$$
\mu=\sum_{i=1}^{m}a_i\delta_{t_i},
\qquad t_i\in[0,D].
$$


定义


<a id="display-54"></a>

$$
Q_{\mathscr K}(\mu)
=
\sum_{i,j}\overline{a_i}a_j
\mathscr K(t_i-t_j).
$$


若总质量为零，即 $\sum_i a_i=0$，定义其原函数


<a id="display-55"></a>

$$
F_\mu(t)=\mu((-\infty,t]).
$$


它是紧支撑的阶梯函数，并满足


<a id="display-56"></a>

$$
F_\mu\in L^2(\mathbb R),
\qquad
F_\mu'=\mu
$$


——最后一个等式按分布理解。

### 定理 2：任意固定窗口的有限余维正性

对任意 $D>0$ 和任意 $\kappa>0$，存在有限整数 $N=N(D,\kappa)$，使得


<a id="display-57"></a><a id="eq-17"></a>

$$
\boxed{
\int t^j\,d\mu(t)=0,
\qquad j=0,\ldots,N
}
$$

<p align="center" data-equation-number="17"><a href="#eq-17">(17)</a></p>


必然推出


<a id="display-58"></a><a id="eq-18"></a>

$$
\boxed{
Q_{\mathscr K}(\mu)
\ge\kappa\|F_\mu\|_2^2.
}
$$

<p align="center" data-equation-number="18"><a href="#eq-18">(18)</a></p>


若 $\mu\ne0$，则右端严格为正。

这里不要求 $D$ 小于上一轮的局部正定半径。

### 证明第一步：其余实际项只有有限扰动成本

写


<a id="display-59"></a>

$$
\mathscr K=P+R.
$$


由式 (2)，在任何有界区间内，$R$ 连续、分段光滑，一阶导数只有有限次有限跳跃：它们来自 $0$ 和实际素数幂对数。

所以 $R''$ 是局部有限总变差的符号测度。

取光滑紧支撑函数 $\chi$，使它在包含 $[-D,D]$ 的开邻域上等于一。令


<a id="display-60"></a>

$$
R_D=\chi R,
\qquad
M_D=\|R_D''\|_{\mathrm{TV}}<\infty.
$$


所有节点差都在 $[-D,D]$ 内，因此


<a id="display-61"></a>

$$
Q_{\mathscr K}(\mu)=Q_P(\mu)+Q_{R_D}(\mu).
$$


分部积分两次：


<a id="display-62"></a>

$$
Q_{R_D}(\mu)
=
-\langle R_D''*F_\mu,F_\mu\rangle.
$$


有限测度卷积的 $L^2$ 范数界给出


<a id="display-63"></a><a id="eq-19"></a>

$$
\boxed{
|Q_{R_D}(\mu)|
\le M_D\|F_\mu\|_2^2.
}
$$

<p align="center" data-equation-number="19"><a href="#eq-19">(19)</a></p>


这个公式对原子测度也成立：先光滑化 $F_\mu$，进行普通分部积分，再用 $L^2$ 收敛与 $R_D$ 的连续性取极限。

### 证明第二步：正核的高频权重趋于无穷

采用 Fourier 变换


<a id="display-64"></a>

$$
\widehat F(\xi)=\int F(t)e^{-i\xi t}\,dt.
$$


由于


<a id="display-65"></a>

$$
\widehat{e^{-\lambda|\cdot|}}(\xi)
=
\frac{2\lambda}{\lambda^2+\xi^2},
$$


有


<a id="display-66"></a><a id="eq-20"></a>

$$
Q_P(\mu)
=
\frac1{2\pi}
\int_{\mathbb R}
m(\xi)|\widehat F_\mu(\xi)|^2\,d\xi,
$$

<p align="center" data-equation-number="20"><a href="#eq-20">(20)</a></p>


其中


<a id="display-67"></a>

$$
m(\xi)
=
2\sum_{k\ge1}
c_k\lambda_k
\frac{\xi^2}{\lambda_k^2+\xi^2}.
$$


若 $|\xi|\ge\lambda_J$，则


<a id="display-68"></a>

$$
m(\xi)\ge\sum_{k=1}^{J}c_k\lambda_k
\ge\frac14\sum_{k=1}^{J}\frac1k.
$$


因此


<a id="display-69"></a><a id="eq-21"></a>

$$
\boxed{m(\xi)\longrightarrow+\infty.}
$$

<p align="center" data-equation-number="21"><a href="#eq-21">(21)</a></p>


可以选择有限的 $R_0>0$，使


<a id="display-70"></a><a id="eq-22"></a>

$$
m(\xi)\ge2(M_D+\kappa)
\qquad(|\xi|\ge R_0).
$$

<p align="center" data-equation-number="22"><a href="#eq-22">(22)</a></p>


### 证明第三步：有限个矩条件抑制低频部分

由式 (17) 分部积分，得到


<a id="display-71"></a>

$$
\int
\left(t-\frac D2\right)^jF_\mu(t)\,dt=0,
\qquad j=0,\ldots,N-1.
$$


因此，在 $\widehat F_\mu$ 的积分中可以减去前 $N$ 项 Taylor 多项式。纯虚参数的 Taylor 余项满足


<a id="display-72"></a>

$$
\left|
e^{-iu}-\sum_{j=0}^{N-1}\frac{(-iu)^j}{j!}
\right|
\le\frac{|u|^N}{N!}.
$$


于是对 $|\xi|\le R_0$，


<a id="display-73"></a>

$$
|\widehat F_\mu(\xi)|
\le
\sqrt D\,
\frac{(DR_0/2)^N}{N!}\,
\|F_\mu\|_2.
$$


从而


<a id="display-74"></a>

$$
\frac1{2\pi}\int_{-R_0}^{R_0}
|\widehat F_\mu(\xi)|^2\,d\xi
\le
\varepsilon_N\|F_\mu\|_2^2,
$$


其中


<a id="display-75"></a><a id="eq-23"></a>

$$
\boxed{
\varepsilon_N=
\frac{DR_0}{\pi}
\frac{(DR_0/2)^{2N}}{(N!)^2}
\longrightarrow0.
}
$$

<p align="center" data-equation-number="23"><a href="#eq-23">(23)</a></p>


选择有限 $N$，使 $\varepsilon_N\le\frac12$。

由 Plancherel 等式，至少一半的 $L^2$ 质量位于 $|\xi|\ge R_0$。结合式 (20)、(22)，


<a id="display-76"></a>

$$
Q_P(\mu)\ge(M_D+\kappa)\|F_\mu\|_2^2.
$$


再减去式 (19) 的全部扰动成本：


<a id="display-77"></a>

$$
Q_{\mathscr K}(\mu)\ge\kappa\|F_\mu\|_2^2.
$$


最后，若 $F_\mu=0$ 几乎处处，则其分布导数 $\mu=0$，故非零 $\mu$ 对应严格正值。证毕。

这种“消去有限个低频条件后取得正性”的结构，与 Yoshida、Suzuki 对相关 Weil／screw 二次型的研究相近；上面的证明直接作用于这里的实际核和有限原子读出。[arxiv.org](https://arxiv.org/pdf/2206.03682?utm_source=chatgpt.com)

---

<a id="section-6"></a>

## 六、将全部未知符号精确压缩到低矩 Schur 核心

取任意互异节点


<a id="display-78"></a>

$$
t_1,\ldots,t_m\in[0,D],
$$


并令


<a id="display-79"></a>

$$
H=[\mathscr K(t_i-t_j)].
$$


定义矩矩阵


<a id="display-80"></a>

$$
V=
\begin{pmatrix}
1&\cdots&1\\
t_1&\cdots&t_m\\
\vdots&&\vdots\\
t_1^N&\cdots&t_m^N
\end{pmatrix}.
$$


定理 2 表明


<a id="display-81"></a><a id="eq-24"></a>

$$
\boxed{
a^*Ha>0
\quad
(a\in\ker V,\ a\ne0).
}
$$

<p align="center" data-equation-number="24"><a href="#eq-24">(24)</a></p>


由于节点互异，


<a id="display-82"></a>

$$
\operatorname{rank}V=\min(m,N+1).
$$


### 推论 1：非正方向的数量有统一有限上界


<a id="display-83"></a><a id="eq-25"></a>

$$
\boxed{
H\text{ 的负特征值与零特征值总数}
\le N+1.
}
$$

<p align="center" data-equation-number="25"><a href="#eq-25">(25)</a></p>


**证明。** 若非正特征子空间的维数大于 $\operatorname{rank}V$，它与 $\ker V$ 必有非零交。交中的向量一方面二次型非正，另一方面由式 (24) 严格为正，矛盾。证毕。

这个上界依赖窗口长度 $D$，但不依赖节点数 $m$。

### 推论 2：精确 Schur 压缩

取 $Z$ 的列为 $\ker V$ 的一组基，取 $U$ 的列补足为全空间基。定义


<a id="display-84"></a>

$$
A=Z^*HZ,\qquad
B=Z^*HU,\qquad
C=U^*HU.
$$


已知


<a id="display-85"></a>

$$
A\succ0.
$$


因此可以形成实际低矩核心


<a id="display-86"></a><a id="eq-26"></a>

$$
\boxed{
\mathcal S_{\mathrm{low}}
=
C-B^*A^{-1}B.
}
$$

<p align="center" data-equation-number="26"><a href="#eq-26">(26)</a></p>


分块合同变换给出


<a id="display-87"></a>

$$
\begin{pmatrix}
A&B\\
B^*&C
\end{pmatrix}
\sim
\begin{pmatrix}
A&0\\
0&\mathcal S_{\mathrm{low}}
\end{pmatrix}.
$$


于是


<a id="display-88"></a><a id="eq-27"></a>

$$
\boxed{
H\succeq0
\iff
\mathcal S_{\mathrm{low}}\succeq0.
}
$$

<p align="center" data-equation-number="27"><a href="#eq-27">(27)</a></p>


而且两者的负方向数、零方向数完全相同。

**这就是本轮对全局拼接问题最直接的推进：每个固定窗口内，无论加入多少节点，已经证明为正的高矩部分都可以被严格消去，剩余符号全部集中到至多 $N+1$ 维的实际核心。**

核心仍随节点配置变化；这里没有把无限多个样本的核心替换成一个已经知道为正的矩阵。

### 正块的误差阈值

排序节点，令


<a id="display-89"></a>

$$
h_{\min}=\min_i(t_{i+1}-t_i).
$$


对 $a\in\ker V$，设 $A_i=\sum_{j\le i}a_j$。总质量为零，所以


<a id="display-90"></a>

$$
\|F_{\mu_a}\|_2^2
=
\sum_{i=1}^{m-1}
(t_{i+1}-t_i)|A_i|^2
\ge
\frac{h_{\min}}4\|a\|_2^2.
$$


因此


<a id="display-91"></a><a id="eq-28"></a>

$$
\boxed{
a^*Ha
\ge
\frac{\kappa h_{\min}}4\|a\|_2^2
\qquad(a\in\ker V).
}
$$

<p align="center" data-equation-number="28"><a href="#eq-28">(28)</a></p>


任何满足


<a id="display-92"></a>

$$
\|E\|_{\mathrm{op}}
<
\frac{\kappa h_{\min}}4
$$


的厄米误差，都不会破坏这个已证明正块的正性。完整矩阵的符号则继续由式 (26) 的实际核心决定。

---

<a id="section-7"></a>

## 七、Robin 正预算加强到平方根尺度

现在回到原整数 $n$，始终保持


<a id="display-93"></a>

$$
T=\log n,
\qquad
R(n)=\frac{\sigma(n)}
{e^\gamma n\log\log n}.
$$


沿用已经建立的精确分解


<a id="display-94"></a><a id="eq-29"></a>

$$
\boxed{
-\log R(n)
=
\mathcal D(n)+I_\psi(T)+\mathcal B(T),
\qquad
\mathcal D(n)\ge0.
}
$$

<p align="center" data-equation-number="29"><a href="#eq-29">(29)</a></p>


其中


<a id="display-95"></a>

$$
I_\psi(T)
=
\frac{\psi(T)-T}{T\log T}
+\gamma+\log\log T
-\sum_{p^j\le T}\frac1{jp^j},
$$


而


<a id="display-96"></a>

$$
\mathcal B(T)=\sum_p\mathcal B_p(T),
$$



<a id="display-97"></a>

$$
\mathcal B_p(T)
=
\sum_{j\ge1}
\left[
\min(z_p,\lambda_{p,j})
-\min(z_p,\nu_{p,j})
\right],
$$



<a id="display-98"></a>

$$
z_p=\frac{\log p}{T\log T},
\quad
\lambda_{p,j}
=
\log\frac{1-p^{-j-1}}{1-p^{-j}},
\quad
\nu_{p,j}=\frac1{jp^j}.
$$


各 $\mathcal B_p(T)\ge0$，并且 $p\ge T$ 时为零。全部素数层仍然保留在定义中。

项目的[严格 Euler 层根尺度修正](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/Blueprint/D5/S3/Arith/Robin/EulerLayerRootCorrection.md)已经建立了保留全部指数层的根尺度结构。下面进一步给出一个完全初等、带明确阈值的预算下界。

### 定理 3：显式平方根尺度正预算


<a id="display-99"></a><a id="eq-30"></a>

$$
\boxed{
T\ge2^{19}
\quad\Longrightarrow\quad
\mathcal B(T)>
\frac{\log2}{64\sqrt2\,\sqrt T\log T}.
}
$$

<p align="center" data-equation-number="30"><a href="#eq-30">(30)</a></p>


### 证明第一步：所需的初等素数计数界

记


<a id="display-100"></a>

$$
\vartheta(x)=\sum_{p\le x}\log p,
\qquad c=\log2.
$$


我们需要


<a id="display-101"></a><a id="eq-31"></a>

$$
\vartheta(x)\le2cx\qquad(x\ge1),
$$

<p align="center" data-equation-number="31"><a href="#eq-31">(31)</a></p>


以及


<a id="display-102"></a><a id="eq-32"></a>

$$
\vartheta(x)\ge\frac c2x
\qquad(x\ge2^{10}).
$$

<p align="center" data-equation-number="32"><a href="#eq-32">(32)</a></p>


式 (31) 由中央二项式系数归纳得到：


<a id="display-103"></a>

$$
\vartheta(2m)-\vartheta(m)
\le\log\binom{2m}{m}\le2mc,
$$



<a id="display-104"></a>

$$
\vartheta(2m+1)-\vartheta(m+1)
\le\log\binom{2m+1}{m}\le2mc.
$$


对于下界，逐素数估值表明


<a id="display-105"></a>

$$
\binom{m}{k}\mid\operatorname{lcm}(1,\ldots,m).
$$


因为二项式系数之和为 $2^m$，至少一个不小于 $2^m/(m+1)$，故


<a id="display-106"></a>

$$
\psi(x)\ge(x-1)c-\log(x+1).
$$


再由


<a id="display-107"></a>

$$
\psi(x)-\vartheta(x)
=
\sum_{j\ge2}\vartheta(x^{1/j})
\le
2c\left[\sqrt x+(\log_2x)x^{1/3}\right],
$$


得到


<a id="display-108"></a>

$$
\frac{\vartheta(x)}{cx}
\ge
1-\frac{1+\log_2(x+1)}x
-\frac2{\sqrt x}
-\frac{2\log_2x}{x^{2/3}}.
$$


对 $x\ge2^{10}$，被减去的总量严格小于


<a id="display-109"></a>

$$
\frac3{256}+\frac1{16}+\frac5{16}
=
\frac{99}{256}<\frac12.
$$


这证明了式 (32)。

### 证明第二步：选取有明确正贡献的实际素数层

置


<a id="display-110"></a>

$$
y=\sqrt{2T},\qquad X=T-1.
$$


当 $T\ge2^{19}$ 时，


<a id="display-111"></a>

$$
y\ge2^{10},\qquad X\ge8y.
$$


对实际素数 $y<p\le X$，有


<a id="display-112"></a>

$$
z_p>\frac1{p^2}.
$$


同时，


<a id="display-113"></a>

$$
\lambda_{p,1}
=
\log(1+p^{-1})
>
\frac1{p+1}\ge\frac1T>z_p,
$$


所以第一层的两个截断项恰好相消。

第二层满足


<a id="display-114"></a>

$$
\lambda_{p,2}
=
\log\left(1+\frac1{p(p+1)}\right)
>
\frac1{p^2+p+1}.
$$


因为这些素数都大于 $4$，


<a id="display-115"></a>

$$
\frac1{p^2+p+1}\ge\frac3{4p^2}.
$$


所有后续层的真实贡献也为正，因此


<a id="display-116"></a><a id="eq-33"></a>

$$
\boxed{
\mathcal B_p(T)>\frac1{4p^2}.
}
$$

<p align="center" data-equation-number="33"><a href="#eq-33">(33)</a></p>


于是，只要该区间非空，


<a id="display-117"></a><a id="eq-34"></a>

$$
\mathcal B(T)>
\frac14\sum_{y<p\le X}\frac1{p^2}.
$$

<p align="center" data-equation-number="34"><a href="#eq-34">(34)</a></p>


下一步同时证明区间内确实存在素数。

### 证明第三步：加权分部积分

定义


<a id="display-118"></a>

$$
A(u)=\vartheta(u)-\vartheta(y).
$$


由式 (31)—(32)，


<a id="display-119"></a>

$$
A(u)\ge\frac c2(u-4y)_+.
$$


Stieltjes 分部积分给出


<a id="display-120"></a>

$$
\begin{aligned}
\sum_{y<p\le X}\frac{\log p}{p^2}
&=
\frac{A(X)}{X^2}
+2\int_y^X\frac{A(u)}{u^3}\,du\\
&\ge
\frac c2
\left[
\frac{X-4y}{X^2}
+2\int_{4y}^X\frac{u-4y}{u^3}\,du
\right]\\
&=
\frac c{8y}-\frac c{2X}>0.
\end{aligned}
$$


所以区间确实含有素数。又因为 $\log p\le\log T$，


<a id="display-121"></a>

$$
\sum_{y<p\le X}\frac1{p^2}
\ge
\frac1{\log T}
\left(\frac c{8y}-\frac c{2X}\right).
$$


结合式 (34)，得到更精确的下界


<a id="display-122"></a><a id="eq-35"></a>

$$
\boxed{
\mathcal B(T)>
\frac{c}{32y\log T}
\left(1-\frac{4y}{X}\right).
}
$$

<p align="center" data-equation-number="35"><a href="#eq-35">(35)</a></p>


最后 $X\ge8y$，故括号至少为 $1/2$。代入 $y=\sqrt{2T}$，式 (30) 成立。证毕。

---

<a id="section-8"></a>

## 八、这个下界对原整数 Robin 判据意味着什么？

令


<a id="display-123"></a>

$$
c_0=\frac{\log2}{64\sqrt2},
\qquad
Q(T)=\sqrt T\log T\,I_\psi(T).
$$


由式 (29)—(30)，对 $T=\log n\ge2^{19}$，


<a id="display-124"></a>

$$
-\log R(n)
>
\mathcal D(n)+
\frac{Q(T)+c_0}{\sqrt T\log T}.
$$


因此得到两个严格推论：


<a id="display-125"></a><a id="eq-36"></a>

$$
\boxed{
Q(T)\ge-c_0
\quad\Longrightarrow\quad
R(n)<1,
}
$$

<p align="center" data-equation-number="36"><a href="#eq-36">(36)</a></p>


以及


<a id="display-126"></a><a id="eq-37"></a>

$$
\boxed{
R(n)\ge1
\quad\Longrightarrow\quad
Q(T)<
-c_0-\sqrt T\log T\,\mathcal D(n).
}
$$

<p align="center" data-equation-number="37"><a href="#eq-37">(37)</a></p>


所以，在这个范围内，任何弱 Robin 反例都必须产生一个越过固定负阈值的归一化带符号尾项。

若进一步有一个带确定误差的读出


<a id="display-127"></a>

$$
|\widehat Q(T)-Q(T)|\le\varepsilon,
$$


则


<a id="display-128"></a><a id="eq-38"></a>

$$
\boxed{
\widehat Q(T)\ge\varepsilon-c_0
\quad\Longrightarrow\quad
R(n)<1.
}
$$

<p align="center" data-equation-number="38"><a href="#eq-38">(38)</a></p>


这正好落实“结果、误差、归一尺度一起保存”的要求：误差界直接参与接纳条件。

式 (36) 是充分条件，尚未证明它对全部 $T$ 成立。完整全局目标仍须保留实际的 $\mathcal D(n)$ 与全部 $\mathcal B(T)$。

---

<a id="section-9"></a>

## 九、现在剩下的是哪一个具体证明任务？

本轮已经把问题推进到以下状态：

| 部分 | 当前可证明的范围 |
|---|---|
| 短窗口的原始关系 | 所有有限方向严格正定 |
| 任意固定有限组远距离差分读出 | 充分小尺度下严格正定，归一关系趋于单位矩阵 |
| 任意固定长度窗口的完整关系 | 消去有限个普通矩后严格正定 |
| 全部潜在非正性 | 每个有限样本可精确压缩到低矩 Schur 核心 |
| Robin 正预算 | 有明确的 $1/(\sqrt T\log T)$ 严格下界 |

AURIC 三轴在这里承担每一步的归一读出；完整低矩核心保存各步之间尚未消去的共同约束。

还不能直接交换的两个量词是：


<a id="display-129"></a>

$$
\forall\text{固定有限配置}\ \exists\text{足够小尺度},
$$


与


<a id="display-130"></a>

$$
\exists\text{统一控制}\ \forall\text{整数配置}.
$$


例如，当取样标签包含 $1$ 和越来越多的素数时，素数幂比值矩阵包含一个加权星图，其最大特征值为


<a id="display-131"></a>

$$
\left(
\sum_{p\le M}\frac{(\log p)^2}{p}
\right)^{1/2}\longrightarrow\infty.
$$


这说明有限图证明中的常数确实随配置增长，不能直接把有限配置的小尺度极限当成全整数统一界。

**下一项核心数学任务已经更集中：证明式 (26) 中的实际低矩 Schur 核心，在所有窗口、所有节点配置下均非负；或者在 Robin 分解中证明实际带符号尾项始终被完整正预算覆盖。**

本轮尚未解决这条最终符号不等式，但已经证明：在每个固定尺度内，递归增加再多节点，新增的大量高矩方向都具有无条件正性，真正需要继续攻克的只在那个维数受控、且保留全部实际算术关系的核心中。
<!-- author-source-end -->

---

<a id="editorial-notes"></a>

## 编者附注：定义补足、纸面核对与适用边界

以下附注与上方原稿分列；原稿的表达、证明、38 个编号及结尾均保留。这里补足的是同一组公式的定义、推导细节和边界，不把纸面核对或固定版本源码阅读称为新的 Lean 核验，也不声称 RH、全局核心正性或实际原生制备、控制与取得已经完成。

<a id="note-a"></a>

### A. 核的常数、尖点与“上一轮”的局部结论

原稿没有给“上一轮”另附可定位的整篇来源。其所需核、尖点和局部正性可以直接从本篇已列公式补足，不依赖待发布的文稿。全文的 $\gamma$ 是 Euler 常数，$\log$ 是自然对数，$\sigma(n)=\sum_{d\mid n}d$，$\psi(x)=\sum_{p^j\le x}\log p$。对 $h>0$，把 $1/[2k(2k+1)]$ 拆成 $1/(2k)-1/(2k+1)$ 并求和，得到

$$
P(h)=e^{-h/2}+\sinh(h/2)\log(1-e^{-h})
-\cosh(h/2)\log(1+e^{-h}).
$$

因此 $P(0)=1-\log2$。在 $0<h<\log2$ 时没有素数幂项，$\mathscr K(h)=N(h)+P(h)$；展开上式中的解析因子和 $\log(1-e^{-h})=\log h+O(h)$，即得原稿[式 (1)](#eq-1)，常数恰为 $S=2+\gamma-\log(4\pi)$。这里的余项可由同一显式式子微分控制，并有

$$
\mathscr K'(h)=\tfrac12\log h+O(1),\qquad
\mathscr K''(h)=\frac1{2h}+O(|\log h|).
$$

$S>0$ 也无需数值程序：积分的梯形估计给 $\gamma>H_4-\log4-1/8$；级数 $\log2=2\sum_{r\ge0}[(2r+1)3^{2r+1}]^{-1}$ 的前三项及几何尾界给 $\log2<233/336$，故 $\gamma>4/7$。又 $\pi<22/7$，而 $\sum_{r=0}^{6}(18/7)^r/r!>88/7$，所以 $\log(4\pi)<18/7$，从而 $S>0$。这些只是有限有理式比较与指数、对数的标准级数界。

取足够小的 $b>0$，使 $\mathscr K>0,\ \mathscr K'<0,\ \mathscr K''>0$ 于 $(0,b]$。在 $b$ 以外沿切线延长至零，再恒取零，得到一个偶的连续凸减延拓 $K_b$。它在正半轴的二阶导数测度 $\eta$ 非负，满足

$$
K_b(t)=\int_{(0,\infty)}(r-|t|)_+\,d\eta(r).
$$

每个三角核的 Fourier 变换为 $2(1-\cos(r\xi))/\xi^2$（在 $\xi=0$ 连续取值）。$\eta$ 在 $(0,b)$ 有严格正密度，故所得谱密度处处为正；非零有限原子测度的指数多项式不可能几乎处处为零，其二次型严格为正。于是差距均不超过 $b$ 的任意有限互异节点具有严格正定 Gram 矩阵。这补足第九节表格中的短窗口行；它不提供所有窗口的正性。

在[式 (2)](#eq-2)中，$m=p^j$ 的单项确为

$$
\frac{\log p}{\sqrt m}\,2\sinh((t-\log m)/2)
=\log p\,(e^{t/2}/m-e^{-t/2})\quad(t\ge\log m).
$$

故系数、层数和端点都与原来的 $\mathcal F$ 相同，等号端点的项为零；每个有界 $t$ 范围只涉及有限多个实际素数幂。

<a id="note-b"></a>

### B. 差分、定量余项与三轴投影

三点权重关于中心对称，所以对两个变量分别读出确实得到 $\Delta_h^2\mathscr K(t_i-t_j)$，没有把第二个差分误作反号。[式 (4)](#eq-4)把两个指数矩同时消去；$te^{t/2}$ 的一次差分为 $2h\sinh(h/2)e^{t/2}$，因此双差分消去 $N$ 的条件是全部五个差距取样点在正半轴，即在式 (6) 中使用 $d>2h$。负差距由偶性处理，不在穿过原点时套用该消去式。

对 $g$，在 $u<-h,\ -h\le u\le0,\ 0\le u\le h,\ u>h$ 四段用双曲加法式可直接得到 $\Delta_hg=\tau_h$；边界 $\pm h$ 连续为零。继而 $\upsilon_h$ 支撑于 $[-2h,2h]$，在 $\pm2h$ 为零，在零点为 $-2\sinh h$。这也说明闭窗口不会引入端点歧义。

[式 (7)](#eq-7)的每项严格正。需区别固定 $k$ 的 Taylor 估计与对整个无穷和的支配：对 $\lambda\ge1/2$，

$$
0\le2\cosh(\lambda h)-2\cosh(h/2)
\le\lambda^2h^2e^{\lambda h}.
$$

故 $0<h<d/4$ 时每项除以 $h^4$ 受 $c_k\lambda_k^4e^{-\lambda_k d/2}$ 支配，后者可求和。由此得到原稿所需的 $\Gamma_h(d)=O(h^4)$，并在与零分离的紧距离集上一致。

对固定有限配置，可同时选取一个正尺度，排除每个距离旁除等距素数幂外的所有其他素数幂。素数幂作为整数只有一个底素数和指数表示；矩阵按无序距离对称填边，不重复计入倒数。精确对角式给[式 (11)](#eq-11)的常数 $1-\gamma-\log\pi$。更定量地，令 $M_h=W_h/(2h)$、$v_h=V_h/(2h)$，对原有有限配置及一个互异新中心有

$$
M_h=\ell_hI-\mathsf A+O(h|\log h|),\qquad
v_h=\ell_h+O(h|\log h|),\qquad
\frac{\mathbf w_h}{2h}=-\mathbf a+O(h^2).
$$

其中非对角误差来自 $\sinh h/h=1+O(h^2)$ 和 $\Gamma_h/(2h)=O(h^3)$。固定维数下这些也是算子范数界。因为 $h|\log h|$ 与 $h^2$ 均比 $\ell_h^{-1}$ 更快趋零，Neumann 展开给 $M_h^{-1}=\ell_h^{-1}I+O(\ell_h^{-2})$，代入 $p_h=(\mathbf w_h/(2h))^*M_h^{-1}(\mathbf w_h/(2h))/v_h$，即得原稿[式 (15)](#eq-15)的 $O(\ell_h^{-3})$；只写 $o(1)$ 本身并不足以保证这个速率。

所有归一化、逆矩阵和[式 (16)](#eq-16)都取在包括新中心的完整 Gram 矩阵已经严格正定的共同小尺度上。把新向量投影到旧向量张成空间，$p_h$ 是投影范数平方与新向量范数平方之比。再投影到选定旧向量的一维子空间，得到 $X_h\le p_h<1$；差额是 $Y_h$，正交余量是 $Z_h$。故三者非负、和为一。这是在同一个 Gram 实现中的嵌套投影，不能用三个互不相关的最优值拼接。

在整数取样中，不同素数（含不同斐波那契素数）的比值不为整数，斐波那契值只按数值去重；这里没有使用任何未证的斐波那契素数分布结论。所列五元向量只编码原五模式 $(N,2,3,5,25)$ 下的三个对易占据读口，保留第二分量的符号及原矩阵、总量；它不是固定逻辑 qubit 编码、完整相干态取得或原生控制的证明。V35 第三节明确区分这些读口与 Pauli 轴。

<a id="note-c"></a>

### C. 原子测度、Fourier 恒等式与全部扰动成本

重合原子先合并，零系数可删。$F_\mu$ 使用原稿的右连续约定，端点的单点值不影响 $L^2$；总质量为零时其支撑包含于 $[0,D]$，分布导数包括端点原子。取实偶光滑截断 $\chi$，则 $R_D$ 实偶且连续，其二阶分布导数是有限总变差测度：非零素数幂对数在每个紧区间内只有有限个，原点的一阶跳跃也有限。使用明确的共轭约定，分部积分恒等式为

$$
Q_{R_D}(\mu)=-\int_{\mathbb R}\overline{F_\mu(t)}\,
(R_D''*F_\mu)(t)\,dt.
$$

Young 的有限测度卷积界给[式 (19)](#eq-19)。将 $F_\mu$ 与同一个光滑近似单位卷积时，其导数是 $\mu$ 的光滑化；$L^2$ 收敛控制右边，连续核在有限原子差距邻域上的一致连续性控制左边，因此原子情形的极限合法。

对每个指数核，Fourier 反演与 $\widehat\mu(\xi)=i\xi\widehat F_\mu(\xi)$ 给出非负能量积分。由于 $\sum c_k<\infty$，$P$ 的核级数一致收敛，有限原子二次型可逐项取和；这些能量均非负，Tonelli 再交换求和、积分，得到[式 (20)](#eq-20)。该积分对原子测度仍有限，因为它等于连续有界核的有限原子二次型。$m(0)=0$，每个有限 $\xi$ 的尾和收敛，$m$ 关于 $|\xi|$ 单调。若 $|\xi|\ge\lambda_J$，每个前 $J$ 项的比例至少为 $1/2$，且 $c_k\lambda_k\ge1/(4k)$，故谐和下界确使 $m\to\infty$。

矩条件 $0,\ldots,N$ 经分部积分给 $F_\mu$ 的 $0,\ldots,N-1$ 次矩为零；平移到 $D/2$ 只作多项式线性组合，不丢掉端点条件。对实 $u$ 的积分型 Taylor 余项由 $|e^{-isu}|=1$ 控制，恰为 $|u|^N/N!$，不需附加 $e^{|u|}$。支撑长度为 $D$，所以 Cauchy–Schwarz 给原稿的 $\sqrt D$；低频区间长度为 $2R_0$，连同 Fourier 约定给出[式 (23)](#eq-23)的确切因子 $DR_0/\pi$。阶乘压过固定指数，故可取有限 $N\ge1$ 令 $\varepsilon_N\le1/2$。Plancherel 的另一半质量乘 $2(M_D+\kappa)$，再扣掉全部 $M_D$，留下 $\kappa\|F_\mu\|_2^2$。若原函数几乎处处为零，其分布导数为零，故非零测度得到严格正值。

这里 $N$ 只依赖固定 $D,\kappa$ 及已固定的核、截断，不依赖原子个数或位置；它没有统一控制所有 $D$。Suzuki 的论文讨论相关 Weil／screw 正性和子空间问题；本篇这一原子高矩估计的证明是上面的直接推导，不把论文的 RH 条件结论当作无条件前提。

<a id="note-d"></a>

### D. Schur 核心、空块与误差所用的范数

互异节点的 Vandermonde 秩是 $\min(m,N+1)$，所以非正谱子空间若超过这个秩，就与严格正的 $\ker V$ 相交，给出原稿的维数界。$[Z\ U]$ 可逆，分块消元是合同而非特征值相等；Sylvester 惯性律保留负与零特征值个数，正块被消去后恰剩实际 $\mathcal S_{\mathrm{low}}$。若 $\ker V=\{0\}$，采用零维正块及零维逆算子的约定，交叉项为零，$\mathcal S_{\mathrm{low}}=C$，结论仍成立。

原稿最小间距的讨论用于 $m\ge2$。置 $A_0=A_m=0$，则 $a_i=A_i-A_{i-1}$，故

$$
\sum_{i=1}^m|a_i|^2\le4\sum_{i=1}^{m-1}|A_i|^2.
$$

这与阶梯函数在相邻节点间的值给[式 (28)](#eq-28)。$m=1$ 时 $\ker V=\{0\}$，没有需要保护的非零高矩方向，也不定义空集合的最小间距。

阈值 $\kappa h_{\min}/4$ 使用原节点系数空间的 Euclidean 范数和其中的厄米误差 $E$；选 $Z$ 为正交单位基时，它也是该正块坐标中的阈值。对任意非正交基，正确的坐标陈述是 $A\succeq(\kappa h_{\min}/4)Z^*Z$，不能把同一数值直接当作 $A$ 的最小特征值。误差保护的是这个子空间的正性，完整受扰矩阵仍须用其自身重新计算的 Schur 核心判号。

<a id="note-e"></a>

### E. 完整逐素数预算的前缀证明与同一整数恒等式

[式 (29)](#eq-29)的实对数定义域取整数 $n\ge3$，所以 $T=\log n>1$、$\log T>0$。第八节只使用更窄的 $T\ge2^{19}$，并没有把 $T$ 与另一个整数的参数混用。补足原稿省略的定义，令 $(x)_+=\max(x,0)$、$q=1/(T\log T)$、$\alpha_p=v_p(n)$，并写

$$
L(n)=\log\frac{\sigma(n)}n
=\sum_p\sum_{j=1}^{\alpha_p}\lambda_{p,j},\qquad
\mathcal P(q)=\sum_{p,j\ge1}(\lambda_{p,j}-q\log p)_+,
$$

$$
\mathcal D(n)=\mathcal P(q)-\bigl(L(n)-qT\bigr).
$$

这里 $\mathcal P(q)$ 就是原定义中记作 $P(q)$ 的价格包络；用不同字体避免与第一节的核 $P(t)$ 混淆。这不是新选的松弛量。$\lambda_{p,j}$ 随 $j$ 严格递减且 $\lambda_{p,j}<p^{-j}$，所以包络只有有限项；对每个 $p$ 的实际前 $\alpha_p$ 项，逐项有 $\lambda_{p,j}-q\log p\le(\lambda_{p,j}-q\log p)_+$。又 $\sum_p\alpha_p\log p=\log n=T$，从而 $\mathcal D(n)\ge0$。

先完整检查 $\mathcal B_p$，不能只看其第一层。固定 $p$，$\lambda_j,\nu_j$ 是递减的正序列，且

$$
\sum_{j\ge1}\lambda_j=\sum_{j\ge1}\nu_j=-\log(1-p^{-1})=:L_p.
$$

对每个有限 $r\ge1$，令 $\Lambda_r=\sum_{j=1}^r\lambda_j$、$U_r=\sum_{j=1}^r\nu_j$。望远镜求和及几何尾界给

$$
U_r-\Lambda_r
=-\log(1-p^{-(r+1)})-\sum_{j\ge r+1}\frac{p^{-j}}j>0,
$$

因为后一个尾和至多为 $p^{-(r+1)}/[(r+1)(1-p^{-1})]\le p^{-(r+1)}$，而前一项严格大于 $p^{-(r+1)}$。两条完整总和相同。对任意 $z>0$，只有有限项大于 $z$，故

$$
\sum_j(\lambda_j-z)_+=\max_{r\ge0}(\Lambda_r-rz)
\le\max_{r\ge0}(U_r-rz)=\sum_j(\nu_j-z)_+.
$$

用 $\min(z,a)=a-(a-z)_+$ 和相同总和，得 $\mathcal B_p\ge0$。$z=0$ 时两侧截断和都为零，可直接约定。对 $p\ge T>1$，$p\log p\ge T\log T$ 给 $z_p\ge1/p$，每个 $\nu_{p,j}\le1/p$，每个 $\lambda_{p,j}\le\lambda_{p,1}=\log(1+1/p)<1/p$。因此两列的全部截断项都未被截短，完整相减恰为 $L_p-L_p=0$。第一层确为负，恰由更高层抵消；它不反驳原稿的 $\mathcal B_p=0$。这也证明 $\mathcal B(T)$ 只有有限多个非零逐素数项。总和相等的消去先在每个素数内部完成；不把遍及所有素数的两列未截断总和分别求和后作无穷减无穷。

再定义仅用于核对的有限 Euler 包络

$$
\mathcal E(q)=\sum_{p,j\ge1}(\nu_{p,j}-q\log p)_+.
$$

因 $u\mapsto u\log u$ 在 $u>1$ 严格递增，$\nu_{p,j}\ge q\log p$ 当且仅当 $p^j\le T$。等号项的正部为零，所以使用 $\le T$ 的原稿端点约定给出同一个和：

$$
\mathcal E(q)=\sum_{p^j\le T}\frac1{jp^j}-q\psi(T),\qquad
\mathcal B(T)=\mathcal E(q)-\mathcal P(q).
$$

将这两个有限包络与 $\mathcal D(n)$ 代入，所有包络和 $q\psi(T),qT$ 项逐一消去：

$$
\begin{aligned}
\mathcal D(n)+I_\psi(T)+\mathcal B(T)
&=\gamma+\log\log T-L(n)\\
&=-\log\frac{\sigma(n)}{e^\gamma n\log\log n}.
\end{aligned}
$$

这证明的正是同一个 $n$、同一个 $T$ 的式 (29)，不以 EulerLayerRootCorrection 的根尺度极限代替缺失的恒等式证明。该固定来源保留全部实际指数层，提供结构背景；它既不替代这里的前缀论证，也不证明最终带符号尾项不等式。

<a id="note-f"></a>

### F. 初等素数界、严格常数与端点

[式 (31)](#eq-31)的偶数归纳用 $\vartheta(2m)\le\vartheta(m)+2mc$；奇数归纳用 $\vartheta(2m+1)\le\vartheta(m+1)+2mc$。奇数二项式上界来自两个相等中央项占总和 $2^{2m+1}$ 的一部分。对实 $x$ 取整即得同一上界。对 $\binom{m}{k}$ 的每个素数估值，Legendre 公式中的每一个整部差是零或一，非零项最多 $\lfloor\log_p m\rfloor$，故确整除 $\operatorname{lcm}(1,\ldots,m)$。取 $m=\lfloor x\rfloor$，从最大二项式项得到原稿的 $\psi(x)$ 下界。

$\psi-\vartheta$ 的 $j\ge2$ 和只有有限项，第二层用 $\sqrt x$，其余每项用 $x^{1/3}$、个数用 $\log_2x$ 作上界。在 $x\ge2^{10}$，三个比例 $(1+\log_2(x+1))/x$、$2/\sqrt x$、$2\log_2x/x^{2/3}$ 都递减；在左端分别严格小于 $3/256$、等于 $1/16$、严格小于 $5/16$，所以总和严格小于 $99/256<1/2$。这核对了[式 (32)](#eq-32)的整个实数定义域，没有用有限数表代替统一估计。

$T\ge2^{19}$ 给 $y\ge2^{10}$。函数 $(T-1)/\sqrt{2T}$ 在 $T>1$ 严格递增，在左端已经大于 $8$，故 $X\ge8y$。对 $y<p\le X$，有 $p^2>2T$、$\log p>\frac12\log T$，所以 $z_p>p^{-2}$；又 $p\le T-1$ 给 $\lambda_{p,1}>1/(p+1)\ge1/T>z_p$，而 $\nu_{p,1}>\lambda_{p,1}$，第一层恰相消。

对所有 $j\ge2$、$p\ge2$，

$$
\lambda_{p,j}>\frac{p-1}{p^{j+1}-1}>\frac1{jp^j}=\nu_{p,j},
$$

其中第二个严格不等式来自 $j(p-1)\ge p$ 及分母中的 $-1$；同时 $\lambda_{p,j}<p^{-j}$。因此所选区间内 $j\ge2$ 的两列均未被截短，每一层的差都严格正。尤其 $p>4$ 给 $p^2+p+1\le4p^2/3$，所以第二层单独就严格超过 $1/(4p^2)$。这说明[式 (33)](#eq-33)用的是完整逐素数和，并保留了所有高层。

$A(y)=0$ 使用包含 $p\le y$ 的 $\vartheta(y)$，故 Stieltjes 和准确对应 $(y,X]$，包括 $p=X$ 的可能端点。$A\ge0$ 与上下素数界合成 $A(u)\ge(c/2)(u-4y)_+$。分部积分的边界和积分共同给 $c/(8y)-c/(2X)$；$X\ge8y$ 使它严格为正，从而区间非空，不预先假设素数存在。随后 $\log p\le\log T$ 和 $1-4y/X\ge1/2$ 保留原稿所有严格方向，给出[式 (30)](#eq-30)的常数 $\log2/(64\sqrt2)$。

在[式 (36)](#eq-36)–[式 (38)](#eq-38)中，$Q(T)$ 始终是实际带符号的 $\sqrt T\log T\,I_\psi(T)$。由式 (30) 的严格下界和 $\mathcal D(n)\ge0$，$Q\ge-c_0$ 足以推出 $-\log R>0$；若 $R\ge1$，则严格有 $Q<-c_0-\sqrt T\log T\,\mathcal D(n)$。误差条件使用 $Q\ge\widehat Q-\varepsilon$，所以恰是 $\widehat Q\ge\varepsilon-c_0$。这些都只在声明的 $T=\log n\ge2^{19}$ 范围内成立，未证明该充分条件覆盖所有整数。

<a id="note-g"></a>

### G. 配置增长、固定来源的作用与未解边界

只取 $1$ 和互异素数时，邻接矩阵就是权重 $\log p/\sqrt p$ 的星图，非零特征值为这组权重的 Euclidean 范数及其相反数。其发散可仅用本篇的初等界核对：$x\ge2^{10}$ 时

$$
\vartheta(8x)-\vartheta(x)\ge2cx,\qquad
\sum_{x<p\le8x}\frac{(\log p)^2}{p}
\ge\frac{\log x}{8x}\bigl(\vartheta(8x)-\vartheta(x)\bigr)
\ge\frac c4\log x\longrightarrow\infty.
$$

故“固定有限配置存在小尺度”不能交换成“同一尺度控制所有配置”。任意固定窗口的有限余维结论、每个样本的 Schur 等价及任意窗口全局正性是三个不同层次；前两个不证明第三个。Robin 路线的完整 $\mathcal D,\mathcal B$ 和带符号尾项也均保留。

固定来源的核对范围如下：原稿链接的 FiniteZeroGramHierarchy 区分给定正权 Gram 构造与实际算术正性；ZeckendorfGreedyPermutation 的结论是实际最小未用规则遍历全部正整数，本文只借其遍历次序；V35 第三节的读口是对易占据量；EulerLayerRootCorrection 的定理保留严格阈值、全部指数层与根尺度极限，不提供本篇未解的符号不等式。这些是原稿所钉版本的非空源码阅读，不是重新编译，也不是对其余历史核查的认证。

Kedlaya 的 [Notes on analytic number theory，第七章](https://kskedlaya.org/ant/part-2-4.html)定义 7.1 及[第九章](https://kskedlaya.org/ant/chap-von-mangoldt.html)定理 9.9 对显式公式使用整数点半权的 $\psi$。本文仍用完整的 $p^j\le T$ 端点；不能把那种半权约定的整数点等式直接移入这里的 $I_\psi$。上面的有限包络恒等式不依赖这种移用，也没有以无符号估计替换实际带符号尾项。

相关原始论文为 Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, [arXiv:2206.03682](https://arxiv.org/abs/2206.03682)。论文第 4.2–4.3 节、定理 4.3 关于 $g=-\Psi$、$G_g$、相应厄米形式的正性及 Yoshida 子空间的讨论提供比较背景；这里只主张结构相近，不主张本篇原子矩条件与论文的条件相同。Robin 全局判据与 RH 的等价不用于推导本篇的有限范围恒等式和充分条件。实际低矩核心的所有配置非负性、全部整数的带符号尾项覆盖以及物理取得接口仍是未完成任务。
