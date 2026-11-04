# 三轴对数读出、Fibonacci 窗口与 Robin 判据（编者拟题）

> **编者说明。** 本标题为描述性拟题；作者原文未提供标题、版本或日期。下文保留原文的开场、对话语气及全部论述，补充的符号约定与适用范围均标为“编者注”。较长编号式仅增加分行排版，保留全部原有公式内容及编号。

**可以。更精确地说，三个稳定读出轴可以作为运算的生成元：乘法经过 $\log$ 变成线性组合，加法经过 $\log$ 变成确定的非线性约束；隐藏对角读出则成为三轴上的联合函数。这样不需要增加第四条几何轴。**

这也使上一轮关于“联合信息”的限制更清楚：**三轴上的完整函数结构，可以表达联合关系；如果只保留三个轴的平均值，才可能丢失联合关系。**

下面把这个想法落实到原生 Fibonacci 窗口，并接到 Robin 判据。

<a id="section-1"></a>

## 一、直接建立三个稳定读出的对数表示

> **编者注（对数与表示范围）。** 全文的 $\log$ 为自然对数。这里的正交轴是在指定坐标空间及欧氏内积中的表示；三个环境坐标受一个相容约束，不是三个可任意独立赋值的状态量，也不据此推导物理空间维数。

对于这里的 Fibonacci 数量窗，按你的槽位标记写成

$$
F[1]=a,\qquad F[2]=b,\qquad F[3]=c,
$$

其中

$$
a>0,\qquad b>0,\qquad c=a+b.
$$

首窗就是

$$
(a,b,c)=(2,3,5).
$$

定义三个对数读出：

$$
\boxed{
U_1=\log a,\qquad
U_2=\log b,\qquad
U_3=\log c.
}
$$

于是，加法关系精确变成

<a id="eq-1"></a>

$$
\boxed{
\begin{gathered}
e^{U_3}=e^{U_1}+e^{U_2},
\\
\qquad
U_3=\log(e^{U_1}+e^{U_2}).
\end{gathered}
}
\tag{1}
$$

这给出一个三维坐标空间中的相容曲面：

$$
\mathcal S
=
\left\{
(U_1,U_2,U_3):
e^{U_3}=e^{U_1}+e^{U_2}
\right\}.
$$

每个正数加法原子 $(a,b,a+b)$ 对应曲面上唯一一点，逆映射就是逐坐标取指数。

因此，这里有：

$$
\boxed{\text{三个读数，一个相容约束，两个连续自由度。}}
$$

三个坐标轴可以彼此正交；轴上读数受到算术关系约束，并不妨碍这种正交表示。

### 隐藏加法和乘法都能从同一组三轴读出

原生的隐藏共同选择是

$$
F[1,3]=a+c.
$$

所以

<a id="eq-2"></a>

$$
\boxed{
\log F[1,3]
=
\log(e^{U_1}+e^{U_3}).
}
\tag{2}
$$

而另一种操作 $a\times c$ 给出

<a id="eq-3"></a>

$$
\boxed{
\log(ac)=U_1+U_3.
}
\tag{3}
$$

对首窗而言：

| 操作 | 普通数值 | 对数读出 |
|---|---:|---|
| 稳定关系 $2+3$ | $5$ | $U_3=\log(e^{U_1}+e^{U_2})$ |
| 同窗共同选择 $2+5$ | $7$ | $\log(e^{U_1}+e^{U_3})$ |
| 两块相乘 $2\times5$ | $10$ | $U_1+U_3$ |

这里的 $2+5=7$ 与 $2\times5=10$，具有同一组输入坐标，输出函数不同。仓库本身也明确区分了“加法成块”与“块间乘法”。[项目 Robin 几何文档，§6](https://github.com/the-omega-institute/trureturing/blob/0972668e4ec8cf34be642edcd12a3e975f9dfcb1/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)

<a id="theorem-1"></a>

### 定理 1：全部正数加乘表达式都能精确搬到对数域

定义

$$
u\oplus v:=\log(e^u+e^v),
\qquad
u\odot v:=u+v.
$$

那么

$$
\log(a+b)=\log a\oplus\log b,
$$

$$
\log(ab)=\log a\odot\log b.
$$

这些运算保留原来的结合律、交换律和分配律。例如：

$$
\begin{aligned}
u\odot(v\oplus w)
&=u+\log(e^v+e^w)\\
&=\log(e^{u+v}+e^{u+w})\\
&=(u\odot v)\oplus(u\odot w).
\end{aligned}
$$

因此，任意有限的正数加乘表达式，都可以逐节点精确转换到对数表示中。证毕。

这就把你说的“满足 $\log$ 的运算约束”落实成了一个完整的代数接口。加法的非线性仍保留在 $\oplus$ 中。

本节的有限坐标适用于正数。原生空窗数量 $0$ 若直接取对数，对应扩展边界 $-\infty$；不能把它当作有限的对数原点。

---

<a id="section-2"></a>

## 二、为什么三个轴确实足够表达五模式？

> **编者注（函数值记号）。** 下文 $f_0$、$f_i$ 与 $f_{13}$ 分别表示读出在空窗、仅第 $i$ 槽占位及两端共同占位上的值；混合律另有归一化约束，完整五模式概率律有四个自由参数。

这里需要区分**三个轴函数**与**三个线性分量**。

按照 $F[1],F[2],F[3]$ 的顺序，令占位函数为

$$
\xi_1,\xi_2,\xi_3\in\{0,1\}.
$$

中间位置排斥两端，故

$$
\xi_1\xi_2=0,\qquad
\xi_2\xi_3=0,
$$

而两端可以共同出现：

$$
\xi_1\xi_3\in\{0,1\}.
$$

五个模式如下：

| 模式 | $(\xi_1,\xi_2,\xi_3)$ | 首窗数量 |
|---|---|---:|
| $F[null]$ | $(0,0,0)$ | $0$ |
| $F[1]$ | $(1,0,0)$ | $2$ |
| $F[2]$ | $(0,1,0)$ | $3$ |
| $F[3]$ | $(0,0,1)$ | $5$ |
| $F[1,3]$ | $(1,0,1)$ | $7$ |

<a id="theorem-2"></a>

### 定理 2：三个轴函数生成全部五模式读出

对五模式上的任意实值读出 $f$，都存在唯一展开

<a id="eq-4"></a>

$$
\boxed{
\begin{gathered}
f=c_0+c_1\xi_1+c_2\xi_2+c_3\xi_3
\\
+c_{13}\xi_1\xi_3.
\end{gathered}
}
\tag{4}
$$

**证明。** 分别在五个模式上评价，得到

$$
c_0=f_0,
$$

$$
c_i=f_i-f_0\qquad(i=1,2,3),
$$

$$
c_{13}=f_{13}-f_1-f_3+f_0.
$$

这些系数既存在又唯一。证毕。

这与仓库已有的五函数展开完全一致，只是采用了你的槽位排列。[项目基础公式文档，§2](https://github.com/the-omega-institute/trureturing/blob/0972668e4ec8cf34be642edcd12a3e975f9dfcb1/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

> **编者注（固定来源的槽位对应）。** 上引文档定义 2.1 按低—高—中排列 $(x,y,z)$；本文按低—中—高排列，因此 $(x,y,z)=(\xi_1,\xi_3,\xi_2)$，来源中的联合项 $xy$ 对应 $\xi_1\xi_3$。此对应保持五个模式及其函数代数。

所以，准确的结构是：

$$
\boxed{
\text{三条轴函数}
\quad\Longrightarrow\quad
\text{包含联合项的五维函数空间}.
}
$$

其中 $\xi_1\xi_3$ 是三轴上的非线性函数，并不要求第四条几何轴。

这正好支持你的表示方向：**只要允许三轴上的非线性运算，五模式的全部数值读出都已经能够表达。**

---

<a id="section-3"></a>

## 三、还可以把它旋转成“尺度、比例、加乘关系”三个正交方向

在对数坐标空间上采用标准欧氏内积，定义

<a id="eq-5"></a>

$$
\boxed{
\begin{gathered}
S=\frac{U_1+U_2+U_3}{\sqrt3},
\\
\quad
D=\frac{U_2-U_1}{\sqrt2},
\\
\quad
H=\frac{2U_3-U_1-U_2}{\sqrt6}.
\end{gathered}
}
\tag{5}
$$

对应的基向量是

$$
e_S=\frac{(1,1,1)}{\sqrt3},
\qquad
e_D=\frac{(-1,1,0)}{\sqrt2},
\qquad
e_H=\frac{(-1,-1,2)}{\sqrt6}.
$$

它们正交归一，而且

$$
\boxed{e_S\times e_D=e_H.}
$$

因此，这确实是一组带指定手性的正交轴。

<a id="theorem-3"></a>

### 定理 3：加法相容性成为一个与整体尺度无关的曲面

在 $c=a+b$ 的条件下，

<a id="eq-6"></a>

$$
\boxed{
H=
\sqrt{\frac23}
\log\left(2\cosh\frac D{\sqrt2}\right).
}
\tag{6}
$$

**证明。** 令

$$
s=\frac{U_1+U_2}{2},
\qquad
d=\frac{U_2-U_1}{2}.
$$

则

$$
U_1=s-d,\qquad U_2=s+d,
$$

所以

$$
U_3
=
\log(e^{s-d}+e^{s+d})
=
s+\log(2\cosh d).
$$

再用

$$
D=\sqrt2\,d,\qquad
H=\sqrt{\frac23}(U_3-s)
$$

即可。证毕。

三个方向的意义由此明确：

| 方向 | 数学含义 |
|---|---|
| $S$ | 整体对数尺度 |
| $D$ | 输入比例，$D=\frac1{\sqrt2}\log(b/a)$ |
| $H$ | 和与几何平均之间的关系，$H=\sqrt{\frac23}\log\frac{a+b}{\sqrt{ab}}$ |

> **编者注（缩放范围与经典归属）。** 下述缩放取 $\lambda>0$。本节的正交变换、双曲余弦恒等式及算术—几何平均不等式是经典数学原料；这里展示它们在本组读出中的对应。

若整体放大

$$
(a,b,c)\mapsto(\lambda a,\lambda b,\lambda c),
$$

则

$$
S\mapsto S+\sqrt3\log\lambda,
\qquad D\mapsto D,
\qquad H\mapsto H.
$$

因此，整体尺度增长沿 $S$ 方向移动，比例与加乘关系保持不变。

另外，

$$
H''(D)
=
\frac1{\sqrt6}
\operatorname{sech}^2\frac D{\sqrt2}>0.
$$

所以比例方向上的相容曲线严格凸，并且

$$
H\ge\sqrt{\frac23}\log2,
$$

等号当且仅当 $a=b$。这正是

$$
a+b\ge2\sqrt{ab}
$$

的对数几何形式。

### 加法结果与乘法结果都能成为线性读出

由逆变换可得

$$
\boxed{
\log(a+b)
=
\frac S{\sqrt3}+\sqrt{\frac23}H,
}
$$

<a id="eq-7"></a>

$$
\boxed{
\log(ab)
=
\frac{2S}{\sqrt3}-\sqrt{\frac23}H.
}
\tag{7}
$$

这一步尤其贴合你的想法：

> **在相容曲面上，加法结果和乘法结果都可以由同一组三个正交坐标线性读出；运算的非线性被保存在状态必须满足的曲面约束中。**

不过，$S,D,H$ 不能任意独立赋值。要代表同一个实际加法原子，必须满足式 $(6)$。

---

<a id="section-4"></a>

## 四、Fibonacci 递推在这个表示里变成“尺度增长、形状收敛”

> **编者注（下标与收缩域）。** 本节采用 $F_0=0$、$F_1=F_2=1$、$F_{n+2}=F_{n+1}+F_n$ 的标准 Fibonacci 下标。因而本节 $n=1$ 的三项为 $(1,1,2)$，前述原生首窗 $(2,3,5)$ 对应 $n=3$。对 $n\ge1$，相邻比值不小于一，故 $\rho_n\ge0$；$T$ 把非负半轴映入自身，中值定理的收缩估计及 $T^3$ 的界都在此域使用。黄金比例极限是经典 Fibonacci 递推的结论；本节给出所用对数坐标中的推导。

取连续三项

$$
(a_n,b_n,c_n)=(F_n,F_{n+1},F_{n+2}),
\qquad n\ge1.
$$

定义对数比例

$$
\rho_n=\log\frac{F_{n+1}}{F_n}.
$$

由 Fibonacci 递推，

$$
\frac{F_{n+2}}{F_{n+1}}
=
1+\frac{F_n}{F_{n+1}},
$$

于是

<a id="eq-8"></a>

$$
\boxed{
\rho_{n+1}
=
T(\rho_n)
=
\log(1+e^{-\rho_n}).
}
\tag{8}
$$

<a id="theorem-4"></a>

### 定理 4：形状坐标收敛到黄金比例

固定点满足

$$
e^\rho=1+e^{-\rho}.
$$

令 $r=e^\rho>0$，则

$$
r^2=r+1,
$$

所以

$$
\rho_*=\log\varphi,
\qquad
\varphi=\frac{1+\sqrt5}{2}.
$$

同时，在 $\rho\ge0$ 上，

$$
T'(\rho)=-\frac1{1+e^\rho},
\qquad
|T'(\rho)|\le\frac12.
$$

标准 Fibonacci 初态给出 $\rho_1=0$，因此由中值定理，

<a id="eq-9"></a>

$$
\boxed{
|\rho_n-\log\varphi|
\le
2^{-(n-1)}\log\varphi.
}
\tag{9}
$$

这给出了一个明确的收敛界。

相应地，

$$
D_n\longrightarrow\frac{\log\varphi}{\sqrt2},
$$

$$
H_n\longrightarrow\sqrt{\frac32}\log\varphi.
$$

而尺度方向满足

$$
S_{n+1}-S_n\longrightarrow\sqrt3\log\varphi.
$$

因此，Fibonacci 递推可以精确描述为：

$$
\boxed{
\text{比例形状趋于固定值，整体沿尺度轴继续增长。}
}
$$

对于原生每次跨三个 Fibonacci 下标的窗口，形状更新是 $T^3$，其收缩因子至多为 $1/8$。

这里的黄金结构直接来自递推与对数相容关系，具有完整的证明。

---

<a id="section-5"></a>

## 五、取平均以后，需要保留哪一种联合信息？

对单个确定模式，$\xi_1\xi_3$ 可以直接由两条轴相乘得到。

若考虑五模式概率律，则记

$$
X_i=\mathbb E[\xi_i],
\qquad
\kappa=\mathbb E[\xi_1\xi_3].
$$

一般而言，

$$
\boxed{
\mathbb E[\xi_1\xi_3]
\ne
\mathbb E[\xi_1]\mathbb E[\xi_3].
}
$$

因此，完整三轴函数与三个轴均值，保存的信息不同。仓库的同均值纤维正是由这一联合参数刻画的。[项目基础公式文档，§4](https://github.com/the-omega-institute/trureturing/blob/0972668e4ec8cf34be642edcd12a3e975f9dfcb1/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

> **编者注（概率语义）。** 这里的期望均取同一个五模式概率律；“一般而言”的不等号表示两种期望之间没有普遍相等的恒等式，并非声称每一个律都不相等。下文模式的凸组合表示对应的点质量混合；非线性期望是需要实际取得的额外观察，不能由均值的后处理补回。上引基础文档 §4 的同均值纤维使用同一联合参数。

### 一个对数读出可以直接检测联合项

原生数量是

$$
Q=2\xi_1+3\xi_2+5\xi_3.
$$

为了连空窗 $Q=0$ 也保留，选择处处有定义的观察函数

$$
L=\log(1+Q).
$$

由五模式展开，精确得到

<a id="eq-10"></a>

$$
\boxed{
\begin{gathered}
L=
\\
\xi_1\log3+\xi_2\log4+\xi_3\log6
\\
+\xi_1\xi_3\log\frac49.
\end{gathered}
}
\tag{10}
$$

所以

$$
\mathbb E[L]
=
X_1\log3+X_2\log4+X_3\log6
+\kappa\log\frac49.
$$

因为联合项的系数非零，实际取得 $\mathbb E[L]$ 后，就能结合三个轴均值反解 $\kappa$。

例如，比较两种混合：

$$
\mu_A=\tfrac12F[null]+\tfrac12F[1,3],
$$

$$
\mu_B=\tfrac12F[1]+\tfrac12F[3].
$$

两者的三个轴均值都是

$$
(X_1,X_2,X_3)=\left(\frac12,0,\frac12\right),
$$

数量均值也都是 $7/2$。但

$$
\mathbb E_{\mu_A}L=\frac12\log8,
\qquad
\mathbb E_{\mu_B}L=\frac12\log18.
$$

因此，对数非线性读出能够区分它们。

**这提供了一个积极的恢复机制：在三轴上保留或实际读取非线性函数，就能检测原先被均值压缩掉的联合信息。** 仅对已知均值取对数，则不会增加信息。

### 与 $7$ 和 $10$ 的区别直接对应

> **编者注（整数计数域）。** 本段取 $u,v,w,k\in\mathbb Z_{\ge0}$、$0\le k\le\min(u,w)$，使四种块的重数 $(u-k,v,w-k,k)$ 均为非负整数。这是下引 Robin 几何文档假设 6.2 的计数域（其中联合计数记作 $\kappa$）；本文以 $k$ 区别于概率联合矩 $\kappa$。

在乘法块配置中，若三个位置计数为 $(u,v,w)$，其中共同加法块 $[2+5]$ 出现 $k$ 次，那么

$$
N=2^{u-k}3^v5^{w-k}7^k,
$$

故

<a id="eq-11"></a>

$$
\boxed{
\begin{gathered}
\log N
=
\\
u\log2+v\log3+w\log5
\\
-k\log\frac{10}{7}.
\end{gathered}
}
\tag{11}
$$

这里的

$$
\log\frac{10}{7}
=
\log(2\cdot5)-\log(2+5)
$$

正是加法与乘法之间的对数差。$k$ 是实际联合块次数；它与上面的概率参数 $\kappa$ 类型不同，但承担相似的关系记录作用。[项目 Robin 几何文档，§6](https://github.com/the-omega-institute/trureturing/blob/0972668e4ec8cf34be642edcd12a3e975f9dfcb1/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)

---

<a id="section-6"></a>

## 六、接到 Robin：对数三轴还能给出一个实际的不等式

> **编者注（算术符号与经典归属）。** 本节 $n$ 为正整数，$\sigma(n)=\sum_{d\mid n}d$ 为正约数和，$\gamma$ 为 Euler–Mascheroni 常数；式 (12) 的范围是整数 $n>5040$。素数求和遍历实际分解中有限的 $p\mid n$，$a_p=v_p(n)$。Robin 的全称判据归于 G. Robin，*Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*（1984），此处沿原文固定 Robin 几何文档假设 2.2 经 Choie 等 v2 的摘要及 §1 所作归属使用。有限约数乘积式与 Jensen 凹性不等式是以下推导的经典原料。

对

$$
Z(n)=\frac{\sigma(n)}n,
$$

可以定义三个目标读出

$$
X=\log n,\qquad
Y=\log Z(n),\qquad
W=\log\sigma(n).
$$

它们满足

$$
\boxed{W=X+Y.}
$$

Robin 不等式则变成

<a id="eq-12"></a>

$$
\boxed{
\begin{gathered}
Y<\gamma+\log\log X,
\\
\qquad X>\log5040.
\end{gathered}
}
\tag{12}
$$

其中，加法和乘法同时出现在

$$
X=\sum_p a_p\log p,
$$

$$
Y=
\sum_p
\log\left(
\sum_{j=0}^{a_p}e^{-j\log p}
\right).
$$

外层素数方向相乘，变成对数求和；每个方向内部的约数相加，变成 $\log\sum\exp$。

这些目标坐标与原生占位坐标属于不同读出，需要通过实际整数的素因子和指数相接。仓库的连续指数坐标图已经提供了这一接口。[项目 Robin 几何文档，§13](https://github.com/the-omega-institute/trureturing/blob/0972668e4ec8cf34be642edcd12a3e975f9dfcb1/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)

> **编者注（连续图与整数乘积式的边界）。** 上引定义 13.1 固定 $m>5040$，并要求与三个选定素数互素；其连续图只在所声明的开域有效。下述定理 5 则取任意正整数 $m$、非负整数 $a_i$（$i=1,2,3$），以及原文所述的互异素数和互素条件。其等式依据是同一固定来源命题 3.2 的一般约数乘积式，$m=1$ 时用 $Z(1)=1$；后面的 $m=7$ 例子不套用 §13 的 $m>5040$ 前提。

<a id="theorem-5"></a>

### 定理 5：固定对数总量时，有限指数损失受到一个明确约束

考虑三个不同素数 $p_1,p_2,p_3$，并写

$$
n=m\,p_1^{a_1}p_2^{a_2}p_3^{a_3},
\qquad
\gcd(m,p_1p_2p_3)=1.
$$

令

$$
q_i=p_i^{a_i+1},
\qquad
K=(q_1q_2q_3)^{1/3}.
$$

那么

<a id="eq-13"></a>

$$
\boxed{
\begin{gathered}
Z(n)
<
Z(m)
\\
\prod_{i=1}^3\frac{p_i}{p_i-1}
\left(1-\frac1K\right)^3.
\end{gathered}
}
\tag{13}
$$

**证明。** 定义

$$
g(t)=\log(1-e^{-t}),\qquad t>0.
$$

其二阶导数为

$$
g''(t)=-\frac{e^t}{(e^t-1)^2}<0.
$$

所以 $g$ 严格凹。由 Jensen 不等式，

$$
\frac13\sum_{i=1}^3g(\log q_i)
\le
g\left(\frac13\sum_{i=1}^3\log q_i\right)
=
g(\log K).
$$

取指数，

$$
\prod_{i=1}^3\left(1-\frac1{q_i}\right)
\le
\left(1-\frac1K\right)^3.
$$

等号要求 $q_1=q_2=q_3$。但三个不同素数的正整数幂不可能相等，因此对实际整数指数严格不等。

最后使用

$$
Z(n)
=
Z(m)
\prod_{i=1}^3
\frac{1-1/q_i}{1-1/p_i},
$$

即可。证毕。

这表明：**在固定 $\sum_i\log q_i$ 时，三个截断因子的乘积由“阈值相等”的连续配置给出上界；整数素数幂的不同来源迫使实际配置偏离等号。**

### $5040$ 为什么接近这种平衡？

取

$$
m=7,\qquad
(p_1,p_2,p_3)=(2,3,5),
\qquad
(a_1,a_2,a_3)=(4,2,1).
$$

于是

$$
(q_1,q_2,q_3)=(32,27,25),
$$

且

$$
K=(32\cdot27\cdot25)^{1/3}
=21600^{1/3}.
$$

三个下一层素数幂 $32,27,25$ 已经较接近共同阈值。这说明 $5040$ 的指数结构与对数尺度下的边际平衡存在具体联系。

> **编者注（有限指数损失的定义与推广范围）。** 下文取整数 $n\ge2$，故 $r=\omega(n)\ge1$。沿原文固定 Robin 几何文档定义 9.1，采用同一个实际整数分解的指数，定义
>
> $D_{\rm cap}(n)=-\sum_{p\mid n}\log\bigl(1-p^{-(v_p(n)+1)}\bigr).$
>
> 将原文的凹函数 $g$ 以等权应用于全部 $r$ 个正数 $(v_p(n)+1)\log p$，它们的总和是 $\log(n\,\operatorname{rad}(n))$；Jensen 不等式再乘以负数 $-r$ 即得式 (14)。$r=1$ 时为等号；$r\ge2$ 时，互异素数的正整数幂不相等，故严格。$n=1$ 的 $r=0$ 不在式 (14) 的定义域内。

同一证明还可以推广到全部素因子。若

$$
r=\omega(n),\qquad
\operatorname{rad}(n)=\prod_{p\mid n}p,
$$

则上一轮的有限指数损失满足

<a id="eq-14"></a>

$$
\boxed{
\begin{gathered}
D_{\rm cap}(n)
\ge
\\
-r\log\left(
1-(n\,\operatorname{rad}(n))^{-1/r}
\right).
\end{gathered}
}
\tag{14}
$$

当 $r\ge2$ 时严格不等。这是一条可以代入 Robin 差额公式的实际下界。

但要完成 RH，还需要证明这种有限指数损失，加上缺失素数与整体尺度的贡献，始终足以压住全素数乘积的偏差。式 $(14)$ 给出了其中一项明确的控制，并未自动决定总差额的正号。

**因此，你提出的方向可以正式落实为：三轴生成全部读出函数；对数把乘法展开成线性尺度，把加法保存在相容曲率中；联合关系以非线性项保留；再利用曲率、凹性与整数格点约束产生不等式。** 其中最后一步，才是这套表示向 Robin 证明真正提供估计的地方。
