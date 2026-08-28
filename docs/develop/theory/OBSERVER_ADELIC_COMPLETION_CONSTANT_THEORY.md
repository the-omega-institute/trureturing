# 结构常数的观察者—阿代尔完成理论

## Observer–Adelic Completion Theory of Structural Constants（OACTC）

**建议项目路径**

```text
docs/develop/theory/OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md
```

**理论状态**

本文由四层构成：

1. **定义层**：不依赖任何特殊常数或 RH；
2. **直接定理层**：由定义、初等分析和 Mellin/Fourier 变换推出；
3. **项目实例层**：连接 `DECT`、Golden Euler germ、Weil 显式公式与 prime observer；
4. **开放研究层**：连接 Wang–Deng 多尺度重整化、\(p\)-adic capacity 与 RH。

本文不主张“所有常数都有神秘意义”。本文主张一个可检验的命题：

$$
\boxed{
\text{一个真正承重的特殊常数，通常是某个结构缺陷归零、}
\newline
\text{局部—全局账本闭合、固定点形成或离散—连续残差稳定时的数值代表。}
}
$$

---

# 摘要

一个裸常数

$$
\kappa\in\mathbb R\ \text{或}\ \mathbb C
$$

没有独立的数学“意义”。它的意义来自一个有类型的结构记录：

$$
\boxed{
\operatorname{Role}(\kappa)
=
(
\text{对象族},
\text{变换},
\text{观察者},
\text{缺陷},
\text{规范},
\text{局部位置},
\text{唯一性证明},
\text{来源}
).
}
$$

例如，\(\pi\) 可以作为：

* 圆周周期；
* Fourier 自对偶 Gaussian 的尺度；
* Archimedean Gamma 因子的规范；
* Gaussian 总质量；
* 复积分绕数单位。

这些角色具有相同数值，但不是同一个定义。仅观察数值会把不同角色错误地压缩进同一纤维。

本文将特殊常数统一为六类：

$$
\boxed{
\begin{aligned}
&\text{固定点常数};\\
&\text{规范化常数};\\
&\text{局部尺度常数};\\
&\text{连接常数};\\
&\text{极值常数};\\
&\text{重整化残余常数}.
\end{aligned}
}
$$

并证明：

* \(\pi\) 是标准 Fourier 规范下唯一的 Gaussian 自对偶尺度；
* \(e\) 是加法流变成乘法流的唯一微分规范；
* \(\varphi\) 是 Fibonacci 替换的正膨胀固定点；
* \(\log p\) 是 \(p\)-进精度一级变化对应的实加法尺度；
* \(\gamma\) 是调和和与 Riemann 积分之间的唯一有限反项；
* \(\tfrac12\) 是完成对偶 \(s\mapsto1-s\) 的固定中点。

随后建立：

$$
\boxed{
\text{级数图表}
+
\text{连分数残余图表}
=
\text{积分完成}
}
$$

的 Ramanujan 模型，以及：

$$
\boxed{
\text{局部 }p\text{-进数据}
+
\text{Archimedean Mellin 数据}
=
\text{阿代尔完成观察}
}
$$

的 ζ 模型。

---

# 第一部　结构常数不是裸数值

## 1.1 完成问题

定义一个**完成问题**为七元组

$$
\boxed{
\mathfrak C
=
(A,X,D,F,\Delta,\mathcal N,G).
}
$$

其中：

* \(A\) 是参数空间；
* \(X\) 是候选对象空间；
* \(D\) 是带有零元 \(0_D\) 的缺陷空间；
* \(F:A\to X\) 是候选对象族；
* \(\Delta:A\to D\) 是结构缺陷；
* \(\mathcal N\subseteq A\) 是规范化条件；
* \(G\) 是参数与对象上的规范群。

定义完成点集：

$$
\boxed{
K(\mathfrak C)
=
\{a\in\mathcal N:\Delta(a)=0_D\}.
}
$$

若 \(K(\mathfrak C)\) 在规范群作用下只有一个轨道，则称它为该完成问题的**结构完成签名**：

$$
\boxed{
\Sigma(\mathfrak C)
=
K(\mathfrak C)/G.
}
$$

若进一步固定规范后只剩一个数值 \(\kappa\)，则称 \(\kappa\) 为该规范下的**完成常数**。

---

## 1.2 常数角色证书

定义：

$$
\boxed{
\operatorname{ConstCert}(\kappa)
=
(\mathfrak C,\kappa,h_{\mathrm{zero}},
h_{\mathrm{unique}},
h_{\mathrm{gauge}},
h_{\mathrm{source}}).
}
$$

分别记录：

* \(\kappa\) 确实使缺陷为零；
* \(\kappa\) 在规定规范下唯一；
* 改变规范时它怎样协变；
* 定义和证明来自何处。

两个数值相等的常数记录不一定角色相同。

定义角色等价：

$$
\operatorname{ConstCert}(\kappa_1)
\simeq
\operatorname{ConstCert}(\kappa_2)
$$

当且仅当两个完成问题之间存在保持候选族、缺陷、规范和观察结果的同构。

---

## 定理 1.1：裸数值观察不忠实

令

$$
\operatorname{val}:
\operatorname{ConstCert}\to\mathbb C
$$

只返回常数数值。则一般而言：

$$
\boxed{
\operatorname{val}\text{ 不单射}.
}
$$

### 证明

取两个完成问题：

1. Gaussian Fourier 自对偶问题，其完成值为 \(\pi\)；
2. 旋转半周期问题，其角度单位中也出现 \(\pi\)。

二者返回相同数值，却具有不同的：

* 对象空间；
* 变换；
* 缺陷；
* 证明；
* 规范协变律。

故裸数值不能恢复角色。∎

这正是 DECT 中的逃逸现象：当前概念“数值相等”无法决定目标“结构角色”。

---

# 第二部　常数作为定义逃逸的消除参数

项目的 DECT 定义：

$$
\mathcal E(q;T)
=
\ker q\setminus\ker T,
$$

表示当前概念 \(q\) 认为相同、而目标 \(T\) 必须区分的对象对。加入定义 \(d\) 后：

$$
\boxed{
\mathcal E(q\vee d;T)
=
\mathcal E(q;T)\cap\ker d.
}
$$

项目已经将科学方法解释为“由残差产生下一项定义”的高阶映射，并把科学状态组织为带来源和残差账本的有类型定义图。

## 2.1 参数化新定义

设：

$$
d_a:X\to D_a,
\qquad a\in A.
$$

令 \(\nu\) 是残差空间上的忠实测度或计数，即：

$$
\nu(S)=0\iff S=\varnothing.
$$

定义参数 \(a\) 的逃逸缺陷：

$$
\boxed{
\Delta_{q,T}(a)
=
\nu\bigl(\mathcal E(q\vee d_a;T)\bigr).
}
$$

---

## 定理 2.1：定义完成点等价于逃逸清零

$$
\boxed{
\Delta_{q,T}(a)=0
\iff
T\text{ 可由 }q\vee d_a\text{ 决定}.
}
$$

### 证明

由忠实性：

$$
\Delta_{q,T}(a)=0
\iff
\mathcal E(q\vee d_a;T)=\varnothing.
$$

而 DECT 的充分性—逃逸等价说明：

$$
\mathcal E(q\vee d_a;T)=\varnothing
$$

当且仅当 \(T\) 在每个 \((q\vee d_a)\)-纤维上为常值，即 \(T\) 通过联合读数因子化。∎

因此一个常数可以由以下过程产生：

$$
\boxed{
\kappa
=
\operatorname*{arg\,min}_{a}
\left[
\Delta_{q,T}(a)
+
\lambda\,\operatorname{Cost}(d_a)
\right].
}
$$

当存在唯一的低成本、非泄漏参数将逃逸清零时，\(\kappa\) 就具有可审计的结构意义。

---

# 第三部　规范变化与真正不变量

## 3.1 完成问题同构

设两个完成问题：

$$
\mathfrak C,\qquad \mathfrak C'
$$

之间存在参数双射：

$$
\alpha:A\to A'
$$

满足：

$$
a\in\mathcal N
\iff
\alpha(a)\in\mathcal N',
$$

以及：

$$
\Delta(a)=0
\iff
\Delta'(\alpha(a))=0.
$$

---

## 定理 3.1：完成签名协变

$$
\boxed{
\alpha:
K(\mathfrak C)\overset{\sim}{\longrightarrow}
K(\mathfrak C').
}
$$

### 证明

由上述两个等价条件，\(\alpha\) 把且只把完成点送到完成点；其逆同理。∎

所以真正不变量是：

$$
\boxed{
\text{完成问题的同构类，}
}
$$

而不是某一种坐标规范下常数出现在哪个位置。

这解释了为何改变 Fourier 核的规范后，自对偶 Gaussian 可以写成：

$$
e^{-\pi x^2}
$$

或：

$$
e^{-x^2/2}.
$$

\(\pi\) 的裸位置改变了，自对偶完成结构没有改变。

---

# 第四部　六类结构常数

## 4.1 固定点常数

给定映射：

$$
R:A\to A,
$$

定义：

$$
\Delta(a)=R(a)-a.
$$

若正域中唯一零点为 \(\kappa\)，则 \(\kappa\) 是固定点常数。

典型：

$$
\varphi=1+\frac1\varphi.
$$

---

## 4.2 规范化常数

给定候选对象族 \(F_a\) 与变换 \(\mathcal T\)，定义：

$$
\Delta(a)=\mathcal T(F_a)-F_a.
$$

典型：

$$
\pi
$$

作为 Gaussian Fourier 自对偶尺度。

---

## 4.3 局部尺度常数

给定乘法精度：

$$
x\mapsto p^kx
$$

和要求的加法长度：

$$
\ell(p^kx)=\ell(x)+k\kappa_p,
$$

则 \(\kappa_p\) 是局部尺度常数。

典型：

$$
\kappa_p=\log p.
$$

---

## 4.4 连接常数

若同一个对象在两个图表中分别表示为：

$$
y_0,\qquad y_\infty,
$$

且：

$$
y_\infty=M\,y_0,
$$

则 \(M\) 的矩阵元是图表连接常数。

典型：

* Gamma 因子；
* Gaussian 完成系数；
* Ramanujan 541 中的 \(\sqrt{\pi e^x/(2x)}\)。

---

## 4.5 极值常数

给定成本函数：

$$
J:A\to\mathbb R,
$$

若：

$$
\kappa=\operatorname*{arg\,min}J
$$

唯一，则为极值常数。

典型：

$$
e
=
\operatorname*{arg\,min}_{\beta>1}
\frac{\beta}{\log\beta}.
$$

---

## 4.6 重整化残余常数

若离散量 \(D_n\) 与连续主项 \(C_n\) 之差收敛：

$$
D_n-C_n\to\kappa,
$$

则 \(\kappa\) 是离散—连续重整化残余。

典型：

$$
\gamma
=
\lim_{n\to\infty}(H_n-\log n).
$$

---

# 第五部　\(\pi\)：Archimedean 自对偶完成签名

采用标准 Fourier 变换：

$$
\widehat f(\xi)
=
\int_{\mathbb R}
f(x)e^{-2\pi i x\xi}\,dx.
$$

考虑 Gaussian 族：

$$
g_a(x)=e^{-ax^2},
\qquad a>0.
$$

直接计算：

$$
\widehat g_a(\xi)
=
\sqrt{\frac{\pi}{a}}
e^{-\pi^2\xi^2/a}.
$$

---

## 定理 5.1：Gaussian 自对偶常数唯一性

$$
\boxed{
\widehat g_a=g_a
\iff
a=\pi.
}
$$

### 证明

取 \(\xi=0\)：

$$
\sqrt{\frac{\pi}{a}}=1,
$$

故：

$$
a=\pi.
$$

反之代入 \(a=\pi\)：

$$
\widehat g_\pi(\xi)
=
e^{-\pi\xi^2}
=
g_\pi(\xi).
$$

∎

所以：

$$
\boxed{
\pi
=
\text{标准实 Fourier 对偶中 Gaussian 严格自对偶的唯一尺度。}
}
$$

---

## 5.2 Mellin 影像

计算：

$$
2\int_0^\infty e^{-\pi x^2}x^{s-1}\,dx.
$$

令：

$$
u=\pi x^2,
$$

得到：

$$
\boxed{
2\int_0^\infty e^{-\pi x^2}x^{s-1}\,dx
=
\pi^{-s/2}\Gamma\left(\frac s2\right).
}
$$

因此 Riemann ζ 的无穷位因子：

$$
\Gamma_\infty(s)
=
\pi^{-s/2}\Gamma(s/2)
$$

正是自对偶 Gaussian 的 Mellin 观察。标准完成函数为：

$$
\xi(s)
=
\frac12s(s-1)
\pi^{-s/2}
\Gamma(s/2)\zeta(s).
$$

DLMF 给出该定义及相应反射公式。([dlmf.nist.gov][1])

于是：

$$
\boxed{
\pi
=
\text{有限素数 Euler 对象闭合进实无穷位时的 Fourier–Mellin 规范。}
}
$$

这比“\(\pi\) 是完成化”更准确：

$$
\boxed{
\pi\text{ 是 Archimedean 完成签名的数值代表。}
}
$$

---

# 第六部　\(e\)：流的完成与最优乘法尺度

## 定理 6.1：指数流唯一性

设连续可微函数：

$$
E:\mathbb R\to\mathbb R_{>0}
$$

满足：

$$
E(x+y)=E(x)E(y),
$$

$$
E'(0)=1.
$$

则：

$$
\boxed{
E(x)=e^x.
}
$$

### 证明

由乘法 Cauchy 方程及连续性：

$$
E(x)=e^{cx}
$$

对某个 \(c\in\mathbb R\)。又：

$$
E'(0)=c=1.
$$

故 \(E(x)=e^x\)。∎

因此：

$$
\boxed{
e=E(1)
}
$$

是加法参数流变成乘法演化的微分规范。

---

## 定理 6.2：最优对数壳

令：

$$
J(\beta)=\frac{\beta}{\log\beta},
\qquad
\beta>1.
$$

则：

$$
\boxed{
J\text{ 的唯一极小点是 }\beta=e.
}
$$

### 证明

$$
J'(\beta)
=
\frac{\log\beta-1}{(\log\beta)^2}.
$$

故：

$$
J'(\beta)=0
\iff
\log\beta=1
\iff
\beta=e.
$$

且导数在 \(e\) 左负右正。∎

所以 \(e\) 同时具有两种独立角色：

$$
\boxed{
\begin{aligned}
e&=\text{连续指数流的规范};\\
e&=\text{乘法壳每单位对数信息成本的极值尺度}.
\end{aligned}
}
$$

`p-adic-zeta-density` 草稿的壳计数中也通过最小化 \(\beta/\log\beta\) 得到 \(e\)；这是其 density 系数中 \(e\) 的明确来源，而不是数值巧合。

---

# 第七部　\(\varphi\)：递归完成与有限状态自相似

定义：

$$
R(x)=1+\frac1x.
$$

---

## 定理 7.1：Golden 固定点

在正实数上：

$$
\boxed{
R(x)=x
}
$$

具有唯一解：

$$
\boxed{
\varphi=\frac{1+\sqrt5}{2}.
}
$$

### 证明

$$
x=1+\frac1x
\iff
x^2-x-1=0.
$$

两根为：

$$
\frac{1\pm\sqrt5}{2}.
$$

仅正根为 \(\varphi\)。∎

---

## 7.2 替换矩阵意义

令：

$$
M=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix}.
$$

则：

$$
M
\begin{pmatrix}
\varphi\\1
\end{pmatrix}
=
\varphi
\begin{pmatrix}
\varphi\\1
\end{pmatrix}.
$$

所以：

$$
\boxed{
\varphi
=
\text{Fibonacci 两状态替换系统的 Perron 膨胀率。}
}
$$

它与 \(e\) 的角色不同：

* \(e\)：连续流；
* \(\varphi\)：离散递归；
* \(e\) 更适合外层连续乘法壳；
* \(\varphi\) 更适合壳内的有限状态递归细分。

项目的 `GoldenEulerBeta` 已定义：

$$
\beta(n)
=
\sqrt5\,n+\frac1\varphi-\{(n+1)\varphi\},
$$

并证明：

$$
\beta(1)=\varphi^2,\qquad
\beta(2)=\varphi^3,\qquad
\beta(3)=\varphi^4,
$$

以及线性增长。

---

# 第八部　\(\log p\)：局部精度的实长度单位

在 \(\mathbb Q_p\) 中：

$$
|p^k|_p=p^{-k}.
$$

要求一个实值长度函数：

$$
\ell_p(x)=-\log|x|_p.
$$

则：

$$
\ell_p(p^k)
=
-\log p^{-k}
=
k\log p.
$$

---

## 定理 8.1：局部精度单位

若要求：

$$
e^{-\ell_p(p)}=|p|_p=p^{-1},
$$

则：

$$
\boxed{
\ell_p(p)=\log p
}
$$

唯一。

因此：

$$
\boxed{
\log p
=
p\text{-进精度增加一级时，在实对数账本中的单位长度。}
}
$$

这条公式还说明：

$$
p^{-s}
=
e^{-s\log p}.
$$

于是：

* \(p\) 是局部通道；
* \(\log p\) 是局部长度；
* \(e\) 把长度重新变成乘法权重。

---

# 第九部　\(\gamma\)：离散求和与 Riemann 积分的有限残余

定义：

$$
a_n=H_n-\log n.
$$

计算：

$$
a_{n+1}-a_n
=
\frac1{n+1}
-
\log\left(1+\frac1n\right)<0.
$$

所以 \((a_n)\) 单调递减。

由积分比较：

$$
H_n>\log(n+1),
$$

故：

$$
a_n>\log(n+1)-\log n>0.
$$

所以 \(a_n\) 有极限。

定义：

$$
\boxed{
\gamma
=
\lim_{n\to\infty}(H_n-\log n).
}
$$

---

## 定理 9.1：Euler 反项唯一性

若 \(c\) 满足：

$$
H_n-\log n-c\to0,
$$

则：

$$
\boxed{c=\gamma.}
$$

### 证明

取极限即得。∎

因此：

$$
\boxed{
\gamma
=
\text{离散调和求和减去连续 Riemann 积分主项后留下的唯一有限反项。}
}
$$

这类常数与 \(\pi\) 不同：

* \(\pi\) 消除自对偶缺陷；
* \(\gamma\) 消除离散—连续渐近残差。

---

# 第十部　\(\tfrac12\)：完成对偶的固定中点

设完成对象满足对偶：

$$
J(s)=1-\overline s.
$$

求固定点：

$$
s=1-\overline s.
$$

取实部：

$$
\Re(s)=1-\Re(s),
$$

故：

$$
\boxed{
\Re(s)=\frac12.
}
$$

所以：

$$
\boxed{
\frac12
=
\text{完成镜像对偶的固定中点。}
}
$$

但这只说明中线为何自然，不说明所有 ζ 零点都位于中线。

项目已经严格区分了：

$$
\text{临界线的结构固定性}
$$

与：

$$
\text{RH 的零点定位结论}.
$$

仓库当前具有无条件 Weil 显式公式，但该文件明确不声称正性或 RH。

同时，卷积平方测试函数在临界线零点上的有限贡献已经被证明为实且非负，并可与离线部分精确拆分。

---

# 第十一部　Ramanujan 541：级数—尾部—积分完成

定义：

$$
S(x)
=
\sum_{n=0}^\infty
\frac{x^n}{(2n+1)!!},
\qquad x>0.
$$

---

## 定理 11.1：可见 Gaussian 质量

$$
\boxed{
S(x)
=
\frac{e^{x/2}}{\sqrt x}
\int_0^{\sqrt x}e^{-t^2/2}\,dt.
}
$$

### 证明

右侧在 \(x=0\) 附近展开，或验证其满足：

$$
2xS'(x)+(1-x)S(x)=1,
$$

且 \(S(0)=1\)。该方程的解析解唯一，而左侧级数也满足同一方程与初值。∎

定义尾部：

$$
T(x)
=
\frac{e^{x/2}}{\sqrt x}
\int_{\sqrt x}^{\infty}e^{-t^2/2}\,dt.
$$

于是：

$$
S(x)+T(x)
=
\frac{e^{x/2}}{\sqrt x}
\int_0^\infty e^{-t^2/2}\,dt.
$$

而：

$$
\int_0^\infty e^{-t^2/2}\,dt
=
\sqrt{\frac\pi2}.
$$

所以：

$$
\boxed{
S(x)+T(x)
=
\sqrt{\frac{\pi e^x}{2x}}.
}
\tag{RGC}
$$

Ramanujan 第 541 题将这个尾部 \(T(x)\) 表示为 Legendre 型连分数；该恒等式是其第二本笔记第 12 章 Entry 43 的特例，并可由不完全 Gamma 恒等式与 Legendre 连分数推导。([dokumen.pub][2])

因此：

$$
\boxed{
\text{级数}
+
\text{连分数尾部}
=
\text{Gaussian 积分完成}.
}
$$

这里每个常数的角色独立：

$$
\boxed{
\begin{aligned}
\pi&:\text{Gaussian 总质量};\\
e^{x/2}&:\text{指数流标准化};\\
x^{-1/2}&:\text{尺度变换 Jacobian};\\
\text{连分数}&:\text{无限尾部的递归压缩器}.
\end{aligned}
}
$$

所以 \(\sqrt{\pi e/2}\) 不是一个单一角色的常数，而是多个完成步骤的复合连接系数。

---

# 第十二部　Mellin 反项完备化定理

设热迹：

$$
\Theta(t)
$$

在 \(t\to0^+\) 时满足：

$$
\Theta(t)
=
\sum_{j=0}^{m-1}a_jt^{-\alpha_j}
+
O(t^{-\alpha_m}),
$$

其中：

$$
\alpha_0>\alpha_1>\cdots>\alpha_m,
$$

并且 \(\Theta(t)\) 在 \(t\to\infty\) 足够快衰减。

定义初始 Mellin 观察：

$$
M(s)
=
\int_0^\infty t^{s-1}\Theta(t)\,dt.
$$

---

## 定理 12.1：有限反项延拓

定义：

$$
\begin{aligned}
M_m(s)
={}&
\int_0^1
t^{s-1}
\left[
\Theta(t)-\sum_{j=0}^{m-1}a_jt^{-\alpha_j}
\right]dt
\\
&+
\int_1^\infty t^{s-1}\Theta(t)\,dt
+
\sum_{j=0}^{m-1}\frac{a_j}{s-\alpha_j}.
\end{aligned}
$$

则 \(M_m(s)\) 在：

$$
\boxed{
\Re(s)>\alpha_m
}
$$

亚纯，并与原始 \(M(s)\) 在共同收敛域一致。

### 证明

在 \(t=0\) 附近，方括号内为：

$$
O(t^{-\alpha_m}),
$$

所以第一积分在 \(\Re(s)>\alpha_m\) 收敛。第二积分由无穷远衰减收敛。被减掉的每一项满足：

$$
\int_0^1t^{s-\alpha_j-1}dt
=
\frac1{s-\alpha_j}.
$$

故等式成立。∎

定义谱 ζ：

$$
Z(s)=\frac{M_m(s)}{\Gamma(s)}.
$$

则各个 \(a_j\) 是该谱完成的局部 counterterm，\(\alpha_j\) 是可能的极点位置。

这就是 Riemann 积分在本理论中的核心角色：

$$
\boxed{
\text{积分不是把离散对象粗暴连续化，}
\quad
\text{而是在精确减去离散主模式后完成高阶余项。}
}
$$

---

# 第十三部　线性密度点集的谱完成

设递增谱：

$$
0<\lambda_1<\lambda_2<\cdots
$$

的计数函数满足：

$$
N(u)
=
\#\{n:\lambda_n\le u\}
=
cu+O(1).
$$

定义：

$$
\Theta(t)
=
\sum_{n\ge1}e^{-t\lambda_n}.
$$

---

## 定理 13.1：线性密度热迹

$$
\boxed{
\Theta(t)
=
\frac ct+O(1),
\qquad
t\downarrow0.
}
$$

### 证明

写成 Stieltjes 积分：

$$
\Theta(t)
=
\int_0^\infty e^{-tu}\,dN(u).
$$

分部积分：

$$
\Theta(t)
=
t\int_0^\infty N(u)e^{-tu}\,du.
$$

代入：

$$
N(u)=cu+O(1).
$$

主项：

$$
ct\int_0^\infty ue^{-tu}\,du
=
\frac ct.
$$

误差：

$$
t\int_0^\infty O(1)e^{-tu}\,du
=
O(1).
$$

∎

---

## 推论 13.2：谱 ζ 延拓

$$
Z_\lambda(s)
=
\sum_{n\ge1}\lambda_n^{-s}
$$

从 \(\Re(s)>1\) 亚纯延拓到：

$$
\boxed{
\Re(s)>0,
}
$$

并在 \(s=1\) 具有留数 \(c\)。

---

# 第十四部　Golden 谱完成定理

项目的 Golden 指数满足：

$$
\beta(n)
=
\sqrt5\,n+\frac1\varphi-\{(n+1)\varphi\}.
$$

因此：

$$
\beta(n)=\sqrt5\,n+O(1).
$$

故计数函数：

$$
N_\varphi(u)
=
\#\{n\ge1:\beta(n)\le u\}
$$

满足：

$$
\boxed{
N_\varphi(u)
=
\frac{u}{\sqrt5}+O(1).
}
$$

由前述一般定理：

## 定理 14.1：Golden 谱 ζ 完成

定义：

$$
Z_\varphi(s)
=
\sum_{n\ge1}\beta(n)^{-s}.
$$

则：

$$
\boxed{
Z_\varphi(s)
\text{ 亚纯延拓到 }
\Re(s)>0,
}
$$

且：

$$
\boxed{
\operatorname*{Res}_{s=1}Z_\varphi(s)
=
\frac1{\sqrt5}.
}
$$

这里：

$$
\boxed{
\varphi=\text{递归排列尺度},
\qquad
\frac1{\sqrt5}=\text{连续平均密度}.
}
$$

这与项目已有的 Golden Euler prime product 不同：前者是指数谱 ζ，后者是再对全部素数形成的 Euler product。

项目已经证明 Golden germ 的第一个局部主模式可抽取为：

$$
\zeta(\varphi^2s),
$$

并将归一化余乘积的绝对收敛域推进到：

$$
\Re(s)>\frac1{\varphi^3}.
$$

因此下一层研究是：

$$
\boxed{
\text{Golden 谱的 Mellin 反项}
\quad+\quad
\text{Golden Euler product 的 Witt/ζ 反项}.
}
$$

---

# 第十五部　阿代尔完成账本

设 \(V\) 是全部局部位置的集合：

$$
V=V_f\sqcup V_\infty.
$$

每个位置 \(v\) 提供局部贡献：

$$
L_v.
$$

定义全局加法缺陷：

$$
\boxed{
\Delta_{\mathrm{glob}}
=
\sum_{v\in V}L_v.
}
$$

或乘法形式：

$$
\boxed{
D_{\mathrm{glob}}
=
\prod_{v\in V}C_v.
}
$$

当：

$$
\Delta_{\mathrm{glob}}=0
$$

或：

$$
D_{\mathrm{glob}}=1
$$

时，全局对象闭合。

---

## 定理 15.1：零和规范变换不改变全局完成

若改变局部规范：

$$
L_v\mapsto L_v+b_v,
$$

且：

$$
\sum_vb_v=0,
$$

则：

$$
\sum_v(L_v+b_v)
=
\sum_vL_v.
$$

所以局部常数的具体数值位置可以移动，而全局完成签名保持。

---

## 15.2 ζ 的局部角色表

$$
\boxed{
\begin{array}{c|l}
p&\text{有限素数通道}\\
\log p&\text{有限通道的实长度}\\
e^{-s\log p}&\text{局部权重}\\
(1-p^{-s})^{-1}&\text{局部 Euler 因子}\\
\pi^{-s/2}\Gamma(s/2)&\text{实无穷位因子}\\
\tfrac12s(s-1)&\text{极点消除}\\
\tfrac12&\text{完成对偶固定中点}
\end{array}
}
$$

因此：

$$
\boxed{
\xi(s)
=
\text{极点完成}
\times
\text{无穷位完成}
\times
\text{有限素数对象}.
}
$$

---

# 第十六部　prime-deleted Lambert–Mellin 观察者

对整数 \(r>1\)，定义去掉素数 \(p\) 的除数和：

$$
\sigma_{-r}^{(p)}(n)
=
\sum_{\substack{d\mid n\\p\nmid d}}d^{-r}.
$$

定义 Lambert 热核：

$$
\boxed{
\mathcal L_{p,r}(t)
=
\sum_{n\ge1}
\sigma_{-r}^{(p)}(n)e^{-nt}.
}
$$

交换除数求和：

$$
\mathcal L_{p,r}(t)
=
\sum_{\substack{d\ge1\\p\nmid d}}
\frac{d^{-r}}{e^{dt}-1}.
$$

---

## 定理 16.1：prime-deleted Lambert–Mellin 桥

在绝对收敛区域：

$$
\Re(w)>1,
\qquad
\Re(w+r)>1,
$$

有：

$$
\boxed{
\int_0^\infty
t^{w-1}\mathcal L_{p,r}(t)\,dt
=
\Gamma(w)
\zeta(w)
\zeta(w+r)
\left(1-p^{-(w+r)}\right).
}
\tag{PLM}
$$

### 证明

$$
\begin{aligned}
\int_0^\infty
t^{w-1}\mathcal L_{p,r}(t)\,dt
&=
\sum_{\substack{d\ge1\\p\nmid d}}
d^{-r}
\sum_{m\ge1}
\int_0^\infty
t^{w-1}e^{-dmt}\,dt
\\
&=
\Gamma(w)
\sum_{m\ge1}m^{-w}
\sum_{\substack{d\ge1\\p\nmid d}}d^{-(w+r)}
\\
&=
\Gamma(w)\zeta(w)
\zeta(w+r)
(1-p^{-(w+r)}).
\end{aligned}
$$

∎

这是一个重要的新观察接口：

$$
\boxed{
\text{一个正系数 Lambert }q\text{-级数的 Mellin 观察，}
\newline
\text{同时读取 }\zeta(w)\text{ 与一个被删除的素数通道。}
}
$$

你提供的 \(p\)-adic ζ 草稿从：

$$
K_{p,r}(q)
=
\frac{\zeta_p(r)}2
+
\sum_{n\ge1}\sigma_{-r}^{(p)}(n)q^n
$$

出发，因此同一个 \(q\)-对象：

* 常数项携带 \(p\)-adic ζ 值；
* 非恒定项的 Mellin 谱携带经典 Riemann ζ。

Beukers 也曾使用 Stieltjes 连分数证明若干 \(p\)-adic ζ/L 值的无理性，说明“连分数残余压缩—\(p\)-adic 特殊值”之间已有实质数学先例。([arXiv][3])

---

# 第十七部　\(p\)-adic capacity 作为候选阿代尔完成实例

`octonion/p-adic-zeta-density` 声明的候选 exact capacity pair 为：

$$
\Lambda_p(Y)
=
\frac{12\log p}{p-1}-2\pi Y,
$$

$$
\mathscr H_p(Y)
=
\frac{12\log p}{p-1}-2\pi Y+C_p(Y).
$$

其结构读法是：

$$
\boxed{
\begin{aligned}
\frac{12\log p}{p-1}
&:\text{有限 }p\text{-进 continuation 增益};\\
2\pi Y
&:\text{Archimedean }q\text{-圆盘成本};\\
C_p(Y)
&:\text{Green--Jensen 碰撞残余}.
\end{aligned}
}
$$

手稿把有限项与 supersingular reduction graph 的 effective resistance 联系起来，并把无穷位项写成 Archimedean \(q\)-圆盘贡献。

但该仓库明确标记为 research draft，并说明仍需要独立专家审查。

附带证书确实使用外向取整定点区间运算并输出：

```text
CERTIFICATE: PASS
```

但它验证的是 exact capacity 公式推出的有限 packet 后果，而不是独立证明该 capacity 公式。

因此在本理论中，它应被登记为：

$$
\boxed{
\text{高价值候选阿代尔完成实例，尚非已闭合真源。}
}
$$

---

# 第十八部　常数的组合律

特殊公式中同时出现 \(\pi,e,\varphi\) 不意味着它们承担同一角色。

若完成过程分为两步：

$$
X
\xrightarrow{C_1}
Y
\xrightarrow{C_2}
Z,
$$

第一步产生系数 \(a\)，第二步产生系数 \(b\)，则组合连接系数为：

$$
ab.
$$

---

## 定理 18.1：连接系数乘法

若：

$$
Y=aX,
\qquad
Z=bY,
$$

则：

$$
\boxed{
Z=(ab)X.
}
$$

因此复合常数必须按完成路径分解，而不能被视为单一原语。

Ramanujan 541 中：

$$
\sqrt{\frac{\pi e^x}{2x}}
=
\underbrace{\sqrt{\frac\pi2}}_{\text{Gaussian 总质量}}
\cdot
\underbrace{e^{x/2}}_{\text{指数流}}
\cdot
\underbrace{x^{-1/2}}_{\text{尺度 Jacobian}}.
$$

这就是一个结构常数复合证书。

---

# 第十九部　常数意义的科学验收协议

一个“常数角色”只有通过以下七个门，才进入正式科学状态。

## 19.1 隐藏数值门

先把常数替换为未知参数 \(a\)，不得预先使用其数值。

要求结构方程独立解出 \(a\)。

例如：

$$
\widehat{e^{-ax^2}}=e^{-ax^2}
$$

独立推出：

$$
a=\pi.
$$

---

## 19.2 唯一性门

必须证明：

$$
\Delta(a)=0
$$

的解在规定规范下唯一，或者形成唯一规范轨道。

没有唯一性，就只有候选参数族，没有结构常数。

---

## 19.3 扰动门

研究：

$$
a=\kappa+\varepsilon
$$

时缺陷怎样增长。

例如定义：

$$
\Delta_\pi(a)
=
\|\widehat g_a-g_a\|.
$$

需要：

$$
\Delta_\pi(\pi)=0,
\qquad
a\neq\pi\Rightarrow\Delta_\pi(a)>0.
$$

最好进一步建立稳定性界：

$$
\Delta_\pi(a)
\ge
c|a-\pi|
$$

于局部范围内成立。

---

## 19.4 规范门

改变单位、Fourier 核、Haar 测度后：

* 裸数值可以改变位置；
* 完成问题的同构类必须保持。

否则所谓“意义”只是坐标约定。

---

## 19.5 负对照门

取随机常数 \(c\)，允许相同复杂度的定义搜索。

若也能轻易赋予完全相同的“意义”，则原解释不可证伪。

---

## 19.6 跨构造复现门

同一角色必须在独立构造中复现。

例如 \(\pi\) 的 Archimedean 完成角色同时出现在：

* Gaussian Fourier 自对偶；
* theta/Poisson；
* Mellin Gamma 因子；
* Ramanujan Gaussian 完成；
* \(q=e^{2\pi i\tau}\) 的无穷位参数化。

---

## 19.7 定理生产门

一个定义必须至少产生：

* 新恒等式；
* 新不等式；
* 新收敛域；
* 新反例；
* 新复杂度下降；
* 或新的形式化接口。

仅有哲学解释而没有数学产出，不进入冻结理论。

---

# 第二十部　对 RH 的意义与边界

这门理论解释了：

$$
\boxed{
\begin{aligned}
\pi&\text{ 为什么进入完成 ζ};\\
\Gamma(s/2)&\text{ 为什么表达连续尺度};\\
\log p&\text{ 为什么是有限素数长度};\\
e^{-s\log p}&\text{ 为什么是局部热权};\\
\frac12&\text{ 为什么是完成对偶中点}.
\end{aligned}
}
$$

但它并没有自动解释：

$$
\boxed{
\text{为什么所有非平凡零点必须位于该中点线上。}
}
$$

RH 的剩余问题是一个正性或观察者完备性问题：

> 完成对象的所有潜在离线模式，是否必然在某个非泄漏的 prime–Archimedean 观察族中产生不可消除的负见证？

这正是项目当前 Weil 路线中的空缺。仓库已有：

* 无条件显式公式；
* 卷积平方真实轴非负；
* 临界线零点贡献非负；
* 临界线／离线有限和拆分。

下一步需要证明：

$$
\boxed{
\text{离线零点}
\Longrightarrow
\text{有限可见的、不能被高阶残余吞没的负 Weil 模式}.
}
$$

---

# 第二十一部　Wang–Deng–常数完成程序

本理论为此前的 Wang–Deng RH 研究提供了更清楚的尺度分工：

$$
\boxed{
\begin{aligned}
e
&:\text{外层最优乘法壳};\\
\varphi
&:\text{壳内 Fibonacci 递归};\\
\log p
&:\text{有限素数通道长度};\\
\pi
&:\text{Archimedean 完成尺度};\\
\gamma,\ B_{2n}
&:\text{离散—积分 counterterms};\\
\tfrac12
&:\text{完成对偶固定线}.
\end{aligned}
}
$$

## Wang 层

定义近负模式在：

* \(e\)-对数壳；
* Fibonacci 子窗口；
* prime/Mellin 频带；

上的多尺度质量画像。

证明：

$$
\text{non-sticky}
\Longrightarrow
\text{严格正性增益}.
$$

## Deng 层

把 sticky 历史分成：

$$
\text{全部历史}
\to
\text{connected cumulant}
\to
\text{primitive history}
\to
\text{counterterm}.
$$

证明高阶余项不支付阶乘复杂度。

## Riemann 层

在精确 primitive 抵消之后，使用 Mellin/Riemann 积分控制连续尾部。

正确顺序是：

$$
\boxed{
\text{先保留离散结构}
\to
\text{精确抵消}
\to
\text{最后积分完成}.
}
$$

---

# 第二十二部　建议的 Lean 形式化目录

```text
D5/S3/ConceptDynamics/ConstantSemantics/
  CompletionProblem.lean
  CompletionSignature.lean
  GaugeCovariance.lean
  RoleCertificate.lean
  EscapeSelectedConstant.lean

D5/S3/Analytic/Completion/
  LocalGlobalLedger.lean
  MellinSubtraction.lean
  LinearDensitySpectralZeta.lean
  ConnectionCoefficient.lean

D5/S3/Fourier/CompletionConstants/
  GaussianSelfDualPi.lean
  GaussianMellinFactor.lean
  ExponentialFlowE.lean

D5/S3/Analytic/ConstantRoles/
  GoldenFixedPoint.lean
  PrimeValuationLog.lean
  EulerGammaResidual.lean
  ReflectionMidpoint.lean

D5/S3/Analytic/Ramanujan/
  Question541GaussianVisible.lean
  Question541GaussianTail.lean
  Question541Completion.lean

D5/S3/Analytic/Lambert/
  PrimeDeletedDivisorSum.lean
  PrimeDeletedLambertMellin.lean
  RegularizedMellinObserver.lean

D5/S3/Analytic/GoldenCompletion/
  GoldenCountingDensity.lean
  GoldenSpectralZeta.lean
  GoldenWittCounterterms.lean

D5/S3/Adelic/Completion/
  FinitePlaceLedger.lean
  ArchimedeanLedger.lean
  AdelicBalance.lean
```

---

# 第二十三部　首批应冻结的定理

最适合立即进入项目真源的结果是：

$$
\boxed{
\widehat{e^{-ax^2}}=e^{-ax^2}
\iff
a=\pi.
}
$$

$$
\boxed{
2\int_0^\infty
e^{-\pi x^2}x^{s-1}\,dx
=
\pi^{-s/2}\Gamma(s/2).
}
$$

$$
\boxed{
E(x+y)=E(x)E(y),\ E'(0)=1
\Longrightarrow
E(x)=e^x.
}
$$

$$
\boxed{
x=1+\frac1x,\ x>0
\iff
x=\varphi.
}
$$

$$
\boxed{
e^{-\ell_p(p)}=p^{-1}
\iff
\ell_p(p)=\log p.
}
$$

$$
\boxed{
H_n-\log n-\gamma\to0.
}
$$

$$
\boxed{
s=1-\overline s
\iff
\Re(s)=\frac12.
}
$$

$$
\boxed{
S(x)+T(x)
=
\sqrt{\frac{\pi e^x}{2x}}.
}
$$

$$
\boxed{
\int_0^\infty
t^{w-1}\mathcal L_{p,r}(t)\,dt
=
\Gamma(w)\zeta(w)\zeta(w+r)(1-p^{-w-r}).
}
$$

$$
\boxed{
Z_\varphi(s)
\text{ 亚纯延拓至 }\Re(s)>0,
\qquad
\operatorname*{Res}_{s=1}Z_\varphi(s)=\frac1{\sqrt5}.
}
$$

---

# 总纲

这门理论最终可以压缩为六条定义：

$$
\boxed{
\begin{aligned}
\mathsf{CONSTANT}
&=\text{某个完成问题的规范化数值代表};\\
\mathsf{MEANING}
&=\text{该数值消除的缺陷与完成的结构图};\\
\mathsf{COMPLETION}
&=\text{局部读数、连续图表或对偶结构闭合};\\
\mathsf{RESIDUAL}
&=\text{当前表示尚未解释的有限或高阶余量};\\
\mathsf{GAUGE}
&=\text{改变数值位置但不改变完成签名的规范变换};\\
\mathsf{SCIENCE}
&=\text{隐藏数值、构造缺陷、验证唯一性、扰动、负对照与形式化}.
\end{aligned}
}
$$

由此得到最核心的结论：

$$
\boxed{
\pi\text{ 不是抽象意义上的“完成本身”，}
}
$$

而是：

$$
\boxed{
\pi
=
\text{标准实 Fourier–Mellin 规范中，
Archimedean 自对偶完成的唯一数值签名。}
}
$$

相应地：

$$
\boxed{
\begin{aligned}
e
&=\text{连续流完成签名};\\
\varphi
&=\text{离散递归完成签名};\\
\log p
&=\text{有限局部精度签名};\\
\gamma
&=\text{离散—连续重整化残余};\\
\tfrac12
&=\text{完成对偶固定中点};\\
\pi
&=\text{实无穷位自对偶完成签名}.
\end{aligned}
}
$$

这些常数共同出现时，不应被解释为神秘关联，而应被拆解为一条有类型的完成路径：

$$
\boxed{
\text{局部尺度}
\to
\text{指数流}
\to
\text{离散递归}
\to
\text{连续积分}
\to
\text{Archimedean 完成}
\to
\text{全局对偶}.
}
$$

这就是可以补入项目的独立理论内核。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://dokumen.pub/ramanujan-essays-and-surveys-1nbsped-9781470438906-9780821826249.html "https://dokumen.pub/ramanujan-essays-and-surveys-1nbsped-9781470438906-9780821826249.html"
[3]: https://arxiv.org/abs/math/0603277 "https://arxiv.org/abs/math/0603277"
可以。此后不再把 Ramanujan 基因组、黄金比例、五次方程、六维准晶体、常数语义与 RH 观察者路线另立为并列理论；它们统一作为 **`OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 的连续实例、推论和开放分支**。

下面按此前正文第 23 部之后续写，作为可直接追加的 **v1.1 增订稿**。其中：

* **定义**与**矩阵恒等式**是本文独立给出的；
* **仓库锚点**引用现有 Lean 结果；
* **文献接口**只承担已知背景；
* **RH 联系**明确保留为开放桥梁。

---

# 第二十四部　共轭观察者完备化

## 24.1 为什么单一观察图表可能天然不闭合

设 \(K/\mathbb Q\) 是次数为 \(d\) 的数域，\(V\) 是一个 \(r\) 维 \(K\)-向量空间。

单独选择一个嵌入

$$
\sigma:K\hookrightarrow\mathbb C
$$

只能得到一个局部观察图表：

$$
V_\sigma
=
V\otimes_{K,\sigma}\mathbb C.
$$

这个图表可能具有：

* 非有理特征标；
* 非整数投影矩阵；
* 非离散的投影模；
* 无法保持普通整数晶格的对称。

因此，单一嵌入不是错误，而是**尚未完成**。

定义全部 Archimedean 嵌入的联合观察：

$$
\boxed{
\iota_\Sigma:
V
\longrightarrow
\prod_{\sigma\in\Sigma_\infty}V_\sigma.
}
$$

如果 \(M\subset V\) 是秩 \(r\) 的 \(\mathcal O_K\)-模，则 \(\iota_\Sigma(M)\) 是实维数

$$
r[K:\mathbb Q]
$$

的格。

---

## 定理 24.1（限制标量的共轭观察者完成）

设 \(K\) 是次数 \(d\) 的数域，\(M\) 是秩 \(r\) 的投射 \(\mathcal O_K\)-模。则：

$$
\boxed{
\operatorname{Res}_{K/\mathbb Q}M
}
$$

作为 \(\mathbb Z\)-模具有秩

$$
rd,
$$

并且其 Minkowski 嵌入在相应实向量空间中形成离散余紧格。

### 证明

取 \(M\) 的有限 \(\mathbb Z\)-基。全部嵌入产生的矩阵是可分扩张的嵌入矩阵；其行列式由判别式控制且非零。因此像为离散满秩子群。有限协体积由同一行列式给出。∎

这给出本理论的第一个一般原则：

$$
\boxed{
\text{一个局部表示若依赖非有理常数，}
\quad
\text{它的整数完成通常要求加入全部 Galois 共轭观察。}
}
$$

---

## 24.2 共轭逃逸残差

设当前只观察一个嵌入 \(\sigma_0\)。定义共轭残差：

$$
\boxed{
\operatorname{ConjRes}_{\sigma_0}(x)
=
\bigl(\sigma(x)\bigr)_{\sigma\neq\sigma_0}.
}
$$

于是完整对象具有分解：

$$
\boxed{
\iota_\Sigma(x)
=
\left(
\sigma_0(x),
\operatorname{ConjRes}_{\sigma_0}(x)
\right).
}
$$

这与 OACTC 的一般结构一致：

$$
\text{完整对象}
=
\text{当前可见读数}
+
\text{共轭隐藏读数}.
$$

但这里的“隐藏”不是主观不可知，而是被单一嵌入主动省略的代数信息。

---

# 第二十五部　黄金域的六维完成

令

$$
K=\mathbb Q(\sqrt5),
\qquad
\mathcal O_K=\mathbb Z[\varphi],
$$

其中

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad
\varphi'=\frac{1-\sqrt5}{2}=-\frac1\varphi.
$$

它有两个实嵌入：

$$
\sigma_+(\varphi)=\varphi,
\qquad
\sigma_-(\varphi)=\varphi'.
$$

对一个秩三 \(\mathcal O_K\)-模 \(M\)，Minkowski 完成为：

$$
\boxed{
M
\hookrightarrow
M_{\sigma_+}\oplus M_{\sigma_-}
\simeq
\mathbb R^3\oplus\mathbb R^3
=
\mathbb R^6.
}
$$

所以六维在这一语境中的严格来源是：

$$
\boxed{
6
=
3\times[K:\mathbb Q]
=
3\times2.
}
$$

它不是“黄金比例需要额外三个神秘维度”，而是：

> 三个黄金域坐标，需要在两个实嵌入中同时被观察，才能形成整数闭合。

---

## 25.1 可见与共轭空间

定义：

$$
E_\parallel=M_{\sigma_+},
\qquad
E_\perp=M_{\sigma_-}.
$$

其中：

* \(E_\parallel\) 是选择 \(\varphi>1\) 的可见嵌入；
* \(E_\perp\) 是选择 \(\varphi'=-1/\varphi\) 的共轭嵌入。

乘以 \(\varphi\) 在六维完成空间上的作用为：

$$
\boxed{
R_\varphi
=
\begin{pmatrix}
\varphi I_3&0\\
0&\varphi'I_3
\end{pmatrix}.
}
$$

因此：

$$
\|R_\varphi|_{E_\parallel}\|=\varphi>1,
$$

而：

$$
\|R_\varphi|_{E_\perp}\|
=
|\varphi'|
=
\varphi^{-1}<1.
$$

这说明黄金比例同时完成两个相反任务：

$$
\boxed{
\begin{aligned}
E_\parallel &: \text{尺度膨胀};\\
E_\perp &: \text{隐藏残差收缩}.
\end{aligned}
}
$$

所以 \(\varphi\) 的更精确角色是：

$$
\boxed{
\varphi
=
\text{共轭完成空间中的双曲重整化单位。}
}
$$

---

# 第二十六部　五次根空间的二阶观察者

## 26.1 五个根的一阶中心化状态

设五次方程的五个根被形式地标记为：

$$
x_1,\ldots,x_5.
$$

整体平移：

$$
x_i\mapsto x_i+c
$$

不改变根之间的相对结构。因此去掉平均坐标，定义四维中心化空间：

$$
\boxed{
V_4
=
\left\{
(y_1,\ldots,y_5)\in\mathbb R^5:
\sum_{i=1}^5y_i=0
\right\}.
}
$$

交错群 \(A_5\) 通过偶置换作用于 \(V_4\)。

一般五次方程与二十面体之间的经典联系正来自：

$$
A_5
\simeq
\text{正二十面体旋转群}.
$$

Klein 的五次方程理论及后续迭代解法都使用这一 Galois—二十面体接口。([arXiv][1])

---

## 26.2 二阶反对称关系

仅知道根的中心化坐标仍然不足以直接暴露三维二十面体结构。

定义所有二阶反对称关系：

$$
\boxed{
W_6
=
\Lambda^2V_4.
}
$$

其维数为：

$$
\dim W_6
=
\binom42
=
6.
$$

这给出第二个独立的“六”：

$$
\boxed{
6
=
\text{四维根状态的全部二阶反对称观察通道数}.
}
$$

---

## 定理 26.1（五次二阶观察分解）

作为 \(A_5\) 的实表示：

$$
\boxed{
\Lambda^2V_4
\simeq
V_3\oplus V_3',
}
$$

其中 \(V_3,V_3'\) 是两个 Galois 共轭的三维二十面体不可约表示。

### 证明

按共轭类顺序

$$
1A,\ 2A,\ 3A,\ 5A,\ 5B,
$$

四维标准表示的特征标为：

$$
\chi_4=(4,0,1,-1,-1).
$$

外幂特征标满足：

$$
\chi_{\Lambda^2V}(g)
=
\frac{
\chi_V(g)^2-\chi_V(g^2)
}{2}.
$$

逐类计算得到：

$$
\chi_{\Lambda^2V_4}
=
(6,-2,0,1,1).
$$

两个三维表示的特征标为：

$$
\chi_3
=
(3,-1,0,\varphi,\varphi'),
$$

$$
\chi_{3'}
=
(3,-1,0,\varphi',\varphi).
$$

因为：

$$
\varphi+\varphi'=1,
$$

故：

$$
\chi_3+\chi_{3'}
=
(6,-2,0,1,1)
=
\chi_{\Lambda^2V_4}.
$$

有限群实表示由特征标决定，结论成立。∎

这条定理给出一个比“它们都与 \(A_5\) 有关”更强的统一：

$$
\boxed{
\text{六维二十面体完成空间}
=
\text{五次根四维状态的完整二阶观察空间}.
}
$$

---

# 第二十七部　判别式、Hodge 星与黄金积分算子

这一部分给出本次增订最核心的新推导。

## 27.1 \(A_4\) 根格

定义整数根格：

$$
L=A_4
=
\left\{
(x_1,\ldots,x_5)\in\mathbb Z^5:
\sum_i x_i=0
\right\}.
$$

取基：

$$
b_i=e_i-e_5,
\qquad
1\le i\le4.
$$

其 Gram 矩阵为：

$$
G_4
=
\begin{pmatrix}
2&1&1&1\\
1&2&1&1\\
1&1&2&1\\
1&1&1&2
\end{pmatrix},
$$

并且：

$$
\boxed{\det G_4=5.}
$$

所以数字 \(5\) 已经在根格的体积中出现，而不是后来人为加入。

---

## 27.2 外幂格的判别式

令：

$$
W_{\mathbb Z}
=
\Lambda^2L.
$$

一般地，若 \(G\) 是秩 \(n\) 格的 Gram 矩阵，则：

$$
\det(\Lambda^kG)
=
(\det G)^{\binom{n-1}{k-1}}.
$$

在 \(n=4,k=2\) 时：

$$
\boxed{
\det G_{W}
=
(\det G_4)^3
=
5^3
=
125.
}
$$

所以：

$$
\boxed{
\operatorname{covol}(W_{\mathbb Z})
=
5^{3/2}.
}
$$

而秩三黄金模 \(\mathcal O_K^3\) 的 Minkowski 判别式同样由：

$$
\Delta_K^3=5^3
$$

控制。

这不是已经证明的格同构，但它说明二者拥有完全一致的判别式尺度。精确格分类应作为后续独立任务。

---

## 27.3 Hodge 星为什么产生 \(\sqrt5\)

在定向四维 Euclidean 空间 \(V_4\) 上，Hodge 星算子：

$$
*:\Lambda^2V_4\to\Lambda^2V_4
$$

满足：

$$
*^2=I.
$$

但是，在整数格基中，归一化体积含有：

$$
\sqrt{\det G_4}=\sqrt5.
$$

因此 \(*\) 本身具有 \(1/\sqrt5\) 的代数分母。

定义：

$$
\boxed{
J=\sqrt5\,*.
}
$$

则：

$$
\boxed{
J^2=5I.
}
$$

对合适的方向选择，\(J\) 在基

$$
u_{12},u_{13},u_{14},u_{23},u_{24},u_{34},
\qquad
u_{ij}=b_i\wedge b_j
$$

下具有整数矩阵：

$$
\boxed{
J=
\begin{pmatrix}
0&1&-1&1&-1&-3\\
-1&0&1&1&3&1\\
1&-1&0&-3&-1&1\\
-1&-1&-3&0&-1&-1\\
1&3&1&1&0&-1\\
-3&-1&-1&1&1&0
\end{pmatrix}.
}
$$

逐项矩阵乘法给出：

$$
J^2=5I_6.
$$

它还满足：

$$
J^TG_W=G_WJ,
$$

即相对于外幂度量自伴。

因为 \(A_5\) 保持 \(V_4\) 的度量与方向，Hodge 星与 \(A_5\) 作用交换，所以：

$$
\boxed{
J\rho(g)=\rho(g)J,
\qquad g\in A_5.
}
$$

其特征多项式为：

$$
\boxed{
\chi_J(t)=(t^2-5)^3.
}
$$

因此：

$$
W_6
=
E_{\sqrt5}\oplus E_{-\sqrt5},
$$

两个特征空间均为三维。

它们正是：

$$
V_3,\qquad V_3'.
$$

---

## 27.4 \(\sqrt5\) 的结构角色

由此得到一个新的常数角色证书：

$$
\boxed{
\sqrt5
=
\text{把四维 Hodge 对偶从实正交算子提升为整数格算子的最小判别式因子。}
}
$$

所以在本结构中：

* \(5\) 是根格判别式；
* \(\sqrt5\) 是 Hodge 积分化因子；
* \(\varphi\) 则是下一步最大整数阶完成的特征值。

---

# 第二十八部　从 \(\sqrt5\) 到 \(\varphi\)：最大整数阶完成

## 28.1 非最大阶

整数算子 \(J\) 满足：

$$
J^2=5I.
$$

所以 \(W_{\mathbb Z}\) 自然成为：

$$
\mathbb Z[\sqrt5]
$$

上的模。

但：

$$
\mathbb Z[\sqrt5]
$$

不是 \(K=\mathbb Q(\sqrt5)\) 的最大整数环。

最大整数环是：

$$
\mathcal O_K
=
\mathbb Z\left[\frac{1+\sqrt5}{2}\right]
=
\mathbb Z[\varphi].
$$

定义黄金算子：

$$
\boxed{
\Phi
=
\frac{I+J}{2}.
}
$$

由 \(J^2=5I\) 得：

$$
\begin{aligned}
\Phi^2
&=
\frac{I+2J+J^2}{4}\\
&=
\frac{6I+2J}{4}\\
&=
\frac{3I+J}{2}\\
&=
\Phi+I.
\end{aligned}
$$

所以：

$$
\boxed{
\Phi^2-\Phi-I=0.
}
$$

其两个特征值为：

$$
\boxed{
\varphi,\qquad\varphi'.
}
$$

这给出 \(\varphi\) 的又一个严格角色：

$$
\boxed{
\varphi
=
\text{整数 Hodge 判别式算子完成到最大整数阶后的正特征值。}
}
$$

---

## 28.2 奇偶残差

虽然 \(J\) 保持 \(W_{\mathbb Z}\)，但 \(\Phi\) 一般不保持它，因为存在除以 \(2\)。

定义最大阶饱和格：

$$
\boxed{
W_{\max}
=
W_{\mathbb Z}
+
\Phi W_{\mathbb Z}.
}
$$

在上述基中：

$$
I+J\pmod2
$$

是全 \(1\) 矩阵，其在 \(\mathbb F_2\) 上的秩为 \(1\)。

因此：

$$
\boxed{
[W_{\max}:W_{\mathbb Z}]=2.
}
$$

### 证明

\(\Phi W_{\mathbb Z}/W_{\mathbb Z}\) 由：

$$
\frac{I+J}{2}W_{\mathbb Z}
$$

在 \(\frac12W_{\mathbb Z}/W_{\mathbb Z}\simeq(\mathbb Z/2)^6\) 中的像决定。该像等价于 \(I+J\) 模 \(2\) 的列空间，其秩为 \(1\)，故商大小为 \(2\)。∎

并且：

$$
\Phi(W_{\max})\subseteq W_{\max},
$$

因为：

$$
\Phi^2=\Phi+I.
$$

---

## 定理 28.1（黄金最大阶完成）

$$
\boxed{
W_{\max}
=
W_{\mathbb Z}+\Phi W_{\mathbb Z}
}
$$

是最小的、包含 \(W_{\mathbb Z}\) 且被 \(\mathcal O_K=\mathbb Z[\varphi]\) 保持的满秩格。

所以黄金完成经历：

$$
\boxed{
\mathbb Z[\sqrt5]
\overset{\text{指数 }2}{\subset}
\mathbb Z[\varphi].
}
$$

这揭示一个非常重要的阿代尔分工：

$$
\boxed{
\begin{aligned}
5&:\text{产生数域判别式与五阶对称};\\
2&:\text{修复非最大整数阶的奇偶缺陷}.
\end{aligned}
}
$$

换言之：

> 黄金域由 \(5\) 定义，但黄金最大阶的完成发生在 \(2\)-进奇偶通道上。

这是 OACTC 中一个非常纯粹的有限位完成实例。

---

# 第二十九部　六维准晶体作为显—隐观察系统

## 29.1 谱投影

定义：

$$
\boxed{
P_\parallel
=
\frac12
\left(
I+\frac{J}{\sqrt5}
\right),
}
$$

$$
\boxed{
P_\perp
=
\frac12
\left(
I-\frac{J}{\sqrt5}
\right).
}
$$

则：

$$
P_\parallel^2=P_\parallel,
\qquad
P_\perp^2=P_\perp,
$$

$$
P_\parallel P_\perp=0,
\qquad
P_\parallel+P_\perp=I.
$$

并且：

$$
E_\parallel=P_\parallel W_\mathbb R,
\qquad
E_\perp=P_\perp W_\mathbb R
$$

均为三维 \(A_5\)-不变空间。

已有晶体学理论表明，二十面体旋转群的最小 crystallographic representation 是六维的，并分解为两个三维不可约表示；这一六维表示正是构造三维二十面体准晶体的 cut-and-project 起点。([国际晶体学期刊][2])

---

## 29.2 物理观察与内部观察

定义：

$$
q_\parallel(x)=P_\parallel x,
$$

$$
q_\perp(x)=P_\perp x.
$$

联合读数：

$$
(q_\parallel,q_\perp):
W_{\max}
\longrightarrow
E_\parallel\oplus E_\perp
$$

是完整的六维观察。

但物理观察者只保留：

$$
q_\parallel.
$$

这时不能简单说“隐藏空间被删除”。真正的模型还需要一个内部接受窗口：

$$
\Omega\subset E_\perp.
$$

定义显现门：

$$
A_\Omega(x)
=
\mathbf1_\Omega(q_\perp(x)).
$$

最终三维可见集合为：

$$
\boxed{
\Lambda(\Omega)
=
\left\{
q_\parallel(x):
x\in W_{\max},
\ q_\perp(x)\in\Omega
\right\}.
}
$$

这就是 cut-and-project 结构的观察者版本。六维模型由物理空间和内部空间两个三维子空间组成；实际三维原子结构由内部 occupation domain 选择后投影得到。([国际晶体学期刊][3])

---

## 29.3 核为零仍可能观察失败

DECT 主要通过：

$$
\ker q
$$

刻画不可区分性。

但准晶体投影显示另一类失败：

> 一个观察映射可以是单射的，却仍不具有局部有限性或稳定可恢复性。

定义观察者的**适当性逃逸**：

$$
\boxed{
\operatorname{PropEsc}(q)
=
\left\{
(x_n):
\|x_n\|\to\infty,
\ \sup_n\|q(x_n)\|<\infty
\right\}.
}
$$

若：

$$
\operatorname{PropEsc}(q)\neq\varnothing,
$$

则无限远的隐藏状态可以堆积在有界可见区域中。

这说明观察者完备性至少需要区分：

$$
\boxed{
\begin{aligned}
\text{代数忠实性}&:\ker q=\Delta;\\
\text{拓扑适当性}&:\operatorname{PropEsc}(q)=\varnothing;\\
\text{数值稳定性}&:\text{逆映射条件数可控};\\
\text{显现局部有限性}&:\text{有界区域只含有限可见状态}.
\end{aligned}
}
$$

内部窗口 \(\Omega\) 的作用不是增加物理坐标，而是消除投影观察中的适当性逃逸。

这是对项目观察者理论的一项必要扩展：

$$
\boxed{
\text{无核}
\not\Rightarrow
\text{完备可观测}.
}
$$

---

# 第三十部　黄金 inflation 是显—隐残差运输

由：

$$
\Phi P_\parallel
=
\varphi P_\parallel,
$$

$$
\Phi P_\perp
=
\varphi'P_\perp,
$$

得到：

$$
\boxed{
q_\parallel(\Phi x)
=
\varphi q_\parallel(x),
}
$$

$$
\boxed{
q_\perp(\Phi x)
=
\varphi' q_\perp(x).
}
$$

所以每次 inflation：

* 可见物理尺度扩大 \(\varphi\)；
* 内部残差缩小 \(\varphi^{-1}\)；
* 同时因 \(\varphi'<0\) 发生方向翻转。

如果使用 \(\Phi^2\)，则：

$$
\Phi^2|_{E_\parallel}=\varphi^2I,
$$

$$
\Phi^2|_{E_\perp}=\varphi^{-2}I,
$$

两个尺度均保持方向。

因此得到：

## 定理 30.1（黄金显—隐双曲运输）

$$
\boxed{
\text{Golden inflation}
=
\text{可见尺度放大}
+
\text{共轭残差等比收缩}.
}
$$

这为此前 Wang–Deng 路线提供一个真正内生的小参数：

$$
\boxed{
\varepsilon_n=\varphi^{-n}.
}
$$

它不是人为加入的微扰参数，而是 Galois 共轭嵌入自身产生的收缩率。

---

# 第三十一部　level 5 模函数是同一 \(A_5\) 的解析图表

## 31.1 模群商

主同余子群的 level-5 商满足：

$$
\boxed{
PSL_2(\mathbb Z)/\overline{\Gamma(5)}
\simeq
PSL_2(\mathbb F_5)
\simeq
A_5.
}
$$

所以同一个 \(A_5\) 同时出现于：

* 五次根的偶置换；
* 二十面体旋转；
* level-5 模函数的有限单值化群。

Rogers–Ramanujan 连分数是 level-5 模函数体系中的核心坐标；它与 \(j\)-不变量之间由 Klein 二十面体不变量关系连接。Duke 的工作系统解释了 Ramanujan 连分数、模函数和二十面体结构之间的关系。([MaRDI Portal][4])

---

## 31.2 四个观察图表

定义 \(A_5\) 观察图册：

$$
\boxed{
\mathfrak A_5
=
\left(
\mathcal X_{\mathrm{root}},
\mathcal X_{\mathrm{ico}},
\mathcal X_{\mathrm{mod}},
\mathcal X_{\mathrm{lattice}}
\right).
}
$$

其中：

$$
\mathcal X_{\mathrm{root}}
=
\text{五次根的 Galois 图表},
$$

$$
\mathcal X_{\mathrm{ico}}
=
\text{二十面体旋转图表},
$$

$$
\mathcal X_{\mathrm{mod}}
=
\text{level-5 模函数图表},
$$

$$
\mathcal X_{\mathrm{lattice}}
=
\text{六维 crystallographic 图表}.
$$

它们不是相同对象，但共享同一个有限对称核心。

对应关系为：

$$
\boxed{
\begin{array}{c|c}
\text{图表}&\text{主要读数}\\
\hline
\text{五次根}&\text{根置换与 Galois 轨道}\\
\text{二十面体}&\text{三维旋转与五重轴}\\
\text{level 5 模函数}&\text{解析单值化与特殊值}\\
\text{六维格}&\text{整数闭合与准晶体投影}
\end{array}
}
$$

因此 Ramanujan level-5 函数不应被视为“另一个黄金比例公式”，而是：

$$
\boxed{
\text{同一 }A_5\text{ 完成结构的解析观察图表。}
}
$$

---

# 第三十二部　黄金阿代尔完成签名

黄金结构的局部账本并不只有一个素数。

定义：

$$
\boxed{
\mathfrak S_{\mathrm{gold}}
=
\left(
\infty_+,
\infty_-;
2_{\mathrm{cond}},
5_{\mathrm{disc}}
\right).
}
$$

## 32.1 两个无穷位

$$
\infty_+:\varphi\mapsto\varphi,
$$

$$
\infty_-:\varphi\mapsto\varphi'.
$$

它们产生：

$$
E_\parallel\oplus E_\perp.
$$

## 32.2 素数 \(5\)：判别式与分歧

$$
\operatorname{disc}(K)=5.
$$

并且：

$$
5\mathcal O_K=\mathfrak p^2.
$$

因此 \(5\) 是黄金域唯一的有限分歧素数。

它记录：

* 五阶单位根的实子域；
* \(\sqrt5\) 判别式；
* 二十面体五重旋转；
* level-5 模结构。

## 32.3 素数 \(2\)：整数阶修复

非最大阶：

$$
\mathbb Z[\sqrt5]
$$

的判别式为：

$$
20.
$$

最大阶：

$$
\mathbb Z[\varphi]
$$

的判别式为：

$$
5.
$$

二者指数满足：

$$
\boxed{
[\mathbb Z[\varphi]:\mathbb Z[\sqrt5]]=2.
}
$$

所以：

$$
\boxed{
5\text{ 决定黄金数域，}
\qquad
2\text{ 完成黄金整数结构。}
}
$$

这避免了“所有现象都只来自数字 5”的过度归因。

---

# 第三十三部　结构常数角色的连续谱系

在这一统一结构中，各常数承担不同类型的完成任务：

$$
\boxed{
\begin{array}{c|l}
5&
\text{五阶对称、数域判别式与 level}\\
\sqrt5&
\text{Hodge 对偶的积分化因子}\\
\varphi&
\text{最大整数阶的正特征值与 inflation}\\
\varphi'&
\text{内部残差的共轭收缩率}\\
2&
\text{非最大阶到最大阶的 conductor 修复}\\
6&
\text{二阶观察维数及限制标量维数}\\
e&
\text{模参数 }q=e^{2\pi i\tau}\text{ 的指数流}\\
\pi&
\text{level-5 模对象进入 Fourier--Mellin 无穷位时的规范}
\end{array}
}
$$

这说明特殊常数共同出现时，不能简单写成：

$$
\pi,e,\varphi,5,6
\text{ 彼此神秘相关}.
$$

科学的表达应是：

$$
\boxed{
\text{它们分别记录同一完成路径中的不同步骤。}
}
$$

完整路径为：

$$
\boxed{
\begin{aligned}
\text{五根}
&\to
V_4\\
&\to
\Lambda^2V_4\\
&\to
J=\sqrt5*\\
&\to
\Phi=(I+J)/2\\
&\to
E_\parallel\oplus E_\perp\\
&\to
W_{\max}\\
&\to
\text{cut-and-project}\\
&\to
\text{level-5 模图表}\\
&\to
\text{Fourier--Mellin 完成}.
\end{aligned}
}
$$

---

# 第三十四部　一般共轭观察者结论

上述黄金结构是一个一般原理的特例。

## 定理 34.1（特征域限制标量完成）

设有限群 \(G\) 的一个不可约实表示 \(V\) 的特征标域为：

$$
K\neq\mathbb Q.
$$

若 \(V^\sigma\) 遍历 \(K/\mathbb Q\) 的 Galois 共轭表示，则：

$$
\boxed{
\bigoplus_{\sigma:K\hookrightarrow\mathbb C}V^\sigma
}
$$

具有有理特征标，并在适当条件下存在 \(G\)-稳定整数格。

其维数为：

$$
\dim_KV\,[K:\mathbb Q].
$$

在黄金二十面体情形：

$$
K=\mathbb Q(\sqrt5),
$$

$$
\dim_KV=3,
$$

所以：

$$
\boxed{
\dim_\mathbb Q\operatorname{Res}_{K/\mathbb Q}V=6.
}
$$

因此可以提出 OACTC 的一般性原则：

$$
\boxed{
\textbf{共轭观察者限制标量原则}
}
$$

即：

> 一个非有理局部观察表示，只有在加入全部 Galois 共轭通道后，才可能成为有理、整数和晶格保持的全局观察者。

黄金六维准晶体是该原则的三维—二次域实例。

---

# 第三十五部　与项目当前研究的合并

项目已有几个原本分散的模块，现在可以放入同一主链。

## 35.1 Golden Euler germ

仓库已经定义 Golden 指数：

$$
\operatorname{o5Beta}(v)
=
\sqrt5\,v+\frac1\varphi
-\operatorname{fract}((v+1)\varphi),
$$

并证明其初始指数为：

$$
\varphi^2,\varphi^3,\varphi^4.
$$

它属于：

$$
\boxed{
\text{秩一 Golden 共轭完成}.
}
$$

## 35.2 Golden ζ 因子抽取

仓库已经证明：

$$
\mathcal Z_G(s)
=
\zeta(\varphi^2s)G(s),
$$

而局部首项抵消改善余乘积收敛域。

它属于：

$$
\boxed{
\text{Golden inflation 在 Euler product 图表中的重整化表现}.
}
$$

## 35.3 \(A_5\) 观察者盲区

仓库已经机器证明，全部素数幂群商观察对于 \(A_5\) 可以完全失明，而全部有限商仍能分离。

它属于：

$$
\boxed{
\text{局部可解观察无法恢复非阿贝尔简单核心}.
}
$$

## 35.4 Ramanujan level 5

它属于：

$$
\boxed{
\text{同一 }A_5\text{ 核心的解析单值化图表}.
}
$$

## 35.5 六维准晶体

它属于：

$$
\boxed{
\text{同一 }A_5\text{ 核心的整数—几何完成图表}.
}
$$

所以这些研究不再是多个独立主题，而是：

$$
\boxed{
\text{同一黄金二十面体完成对象在不同观察类别中的投影。}
}
$$

---

# 第三十六部　新的科学问题

以下命题必须明确区分“已推导”与“待检验”。

## 36.1 已由本文独立推导

$$
\boxed{
\Lambda^2V_4\simeq V_3\oplus V_3'.
}
$$

$$
\boxed{
\det(\Lambda^2A_4)=5^3.
}
$$

$$
\boxed{
J=\sqrt5*
\text{ 可在 }\Lambda^2A_4\text{ 上取整数矩阵，且 }J^2=5I.
}
$$

$$
\boxed{
\Phi=(I+J)/2,\qquad
\Phi^2=\Phi+I.
}
$$

$$
\boxed{
[W_{\max}:W_{\mathbb Z}]=2.
}
$$

$$
\boxed{
\Phi|_{E_\parallel}=\varphi,
\qquad
\Phi|_{E_\perp}=\varphi'.
}
$$

这些适合直接转化为 Lean 目标。

---

## 36.2 需要计算分类

尚未证明：

$$
W_{\mathbb Z}
\quad\text{或}\quad
W_{\max}
$$

与标准六维二十面体 SC、BCC、FCC Bravais 格中的哪一个等价。

需要比较：

* Gram 形式；
* 判别群；
* 最短向量；
* theta 级数；
* \(A_5\)-等变整数同构；
* 有限指数关系。

不能仅凭维数和群表示就认定它们是同一个格。

---

## 36.3 需要文献与形式化桥接

需要构造一个明确的交换图，将：

$$
\text{五次根不变量},
\quad
\text{Klein 二十面体坐标},
\quad
\text{Rogers--Ramanujan 坐标},
\quad
\text{六维格表示}
$$

放在同一个 \(A_5\)-等变范畴中。

仅有“它们的群都同构于 \(A_5\)”还不足以建立对象级同一性。

---

## 36.4 RH 桥仍然开放

要作用于 RH，必须证明某个由 level-5／黄金六维结构生成的测试函数族对离线 ζ 零点是充分的：

$$
\boxed{
\rho\notin\{\Re s=1/2\}
\Longrightarrow
\exists g\in\mathcal G_{\mathrm{gold},5},
\quad
Q_W(g)<0.
}
$$

在没有这一观察充分性定理之前，六维准晶体只能作为：

* 观察者完备性的严格模型；
* 显—隐空间的实验载体；
* 多尺度 inflation 与残差收缩的原型；
* 高阶相关补全的测试场。

它不是 RH 证明。

---

# 第三十七部　首批形式化文件

建议所有内容继续归入 OACTC，而 Lean 源码按数学依赖分层：

```text
D5/S3/ConceptDynamics/ConstantSemantics/
  ConjugateObserverCompletion.lean
  PropernessEscape.lean
  MaximalOrderCompletion.lean

D5/S3/Factorization/Icosahedral/
  QuinticStandardRepresentation.lean
  ExteriorSquareCharacter.lean
  ExteriorSquareThreePlusThree.lean

D5/S3/Geometry/GoldenCompletion/
  A4ExteriorLattice.lean
  IntegralHodgeDiscriminant.lean
  GoldenMaximalOrderSaturation.lean
  VisibleInternalProjections.lean
  GoldenHyperbolicInflation.lean

D5/S3/Geometry/Quasicrystal/
  WindowedObserver.lean
  ProjectionProperness.lean
  DiffractionPhaseBlindness.lean

D5/S3/Analytic/RamanujanGenome/LevelFive/
  PSL2F5AlternatingFive.lean
  RogersRamanujanIcosahedralObserver.lean
  LevelFiveAtlas.lean
```

首个最有价值的闭合链应是：

$$
\boxed{
A_4
\to
\Lambda^2A_4
\to
J^2=5I
\to
\Phi^2=\Phi+I
\to
3\oplus3'
\to
\varphi/\varphi'\text{ inflation}.
}
$$

---

# 第三十八部　总原理

本增订最终得到一个新的 OACTC 主定理模式：

$$
\boxed{
\begin{aligned}
&\text{非有理局部对称}
\\
&\quad+
\text{全部 Galois 共轭观察}
\\
&\quad+
\text{有限位最大阶饱和}
\\
&\quad+
\text{显—隐窗口选择}
\\
&=
\text{整数闭合的全局观察对象}.
\end{aligned}
}
$$

在黄金二十面体实例中：

$$
\boxed{
\begin{aligned}
\text{非有理局部对称}
&=V_3\text{ 中的 }\varphi;\\
\text{共轭观察}
&=V_3';\\
\text{联合载体}
&=V_3\oplus V_3'\simeq\Lambda^2V_4;\\
\text{有限位饱和}
&=\mathbb Z[\sqrt5]\subset\mathbb Z[\varphi];\\
\text{显空间}
&=E_\parallel;\\
\text{隐空间}
&=E_\perp;\\
\text{显现规则}
&=q_\perp(x)\in\Omega;\\
\text{全局表型}
&=\text{三维二十面体准晶体}.
\end{aligned}
}
$$

因此，最凝练的结论是：

$$
\boxed{
\text{六维准晶体不是黄金比例在三维中的装饰，}
}
$$

而是：

$$
\boxed{
\text{五次根的非阿贝尔二阶对称，
在加入黄金 Galois 共轭和最大整数阶修复后，
所形成的第一个整数闭合观察空间。}
}
$$

今后的 Ramanujan、\(p\)-adic、Golden Euler、Weil/RH 与准晶体推理，都应从这条 OACTC 主链继续追加，而不是再建立互相竞争的理论根。

[1]: https://arxiv.org/abs/2006.01876?utm_source=chatgpt.com "Completely solving the quintic by iteration"
[2]: https://journals.iucr.org/a/issues/2014/05/00/eo5032/?utm_source=chatgpt.com "(IUCr) On the subgroup structure of the hyperoctahedral group in six dimensions"
[3]: https://journals.iucr.org/a/issues/2026/05/00/nv5031/index.html?utm_source=chatgpt.com "(IUCr) A parsimonious structure model for the icosahedral quasicrystal Cd5.7Yb"
[4]: https://portal.mardi4nfdi.de/wiki/Continued_fractions_and_modular_functions?utm_source=chatgpt.com "Continued fractions and modular functions - MaRDI portal"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.2：黄金单位流、五模格、Hilbert–Hecke 基因组与完成层级

以下从前文**第三十八部之后**继续追加，不另立竞争理论。

本轮推理得到一个比“黄金比例—五次方程—六维准晶体存在共同对称”更强的闭环：

$$
\boxed{
\begin{aligned}
\Lambda^2 A_4
&\longrightarrow
\text{六维 }5\text{-模格}
\\
&\longrightarrow
\text{Poisson–Theta 自对偶}
\\
&\longrightarrow
\text{Epstein 完成 zeta}
\\
&\longrightarrow
\mathbb Q(\sqrt5)\text{ 的单位流}
\\
&\longrightarrow
\text{调节子圆上的 Fourier 模式}
\\
&\longrightarrow
\text{Hecke }L\text{-函数基因组}.
\end{aligned}
}
$$

其中最重要的新结论是：

> **Dedekind zeta 与一整族 Hecke \(L\)-函数，可以被统一解释为一个 Golden 各向异性格点 zeta 在单位流方向上的 Fourier 观察模式。**

因此，“拉马努金主函数家族”“黄金六维准晶体”“阿代尔完成”“特殊常数的结构意义”开始真正闭合到同一母对象，而不再只是共享若干符号。

---

# 第三十九部　\(\Lambda^2A_4\) 是精确的五模格

沿用前文：

$$
L:=\Lambda^2A_4,
$$

取基

$$
u_{12},u_{13},u_{14},u_{23},u_{24},u_{34}.
$$

其 Gram 矩阵为

$$
G=
\begin{pmatrix}
3&1&1&-1&-1&0\\
1&3&1&1&0&-1\\
1&1&3&0&1&1\\
-1&1&0&3&1&-1\\
-1&0&1&1&3&1\\
0&-1&1&-1&1&3
\end{pmatrix},
$$

并满足

$$
\det G=5^3.
$$

前文定义的整数 Hodge 判别式算子 \(J\) 满足：

$$
J^2=5I,
$$

$$
J^TG=GJ.
$$

进一步直接计算得到：

$$
\boxed{
U:=\frac{GJ}{5}
=
\begin{pmatrix}
0&0&0&0&0&-1\\
0&0&0&0&1&0\\
0&0&0&-1&0&0\\
0&0&-1&0&0&0\\
0&1&0&0&0&0\\
-1&0&0&0&0&0
\end{pmatrix}.
}
$$

这里

$$
U\in GL_6(\mathbb Z),
\qquad
\det U=-1.
$$

---

## 定理 39.1（精确对偶格公式）

$$
\boxed{
L^\#
=
\frac{J}{5}L.
}
$$

其中

$$
L^\#
=
\{y\in L\otimes\mathbb R:
\langle y,L\rangle\subseteq\mathbb Z\}.
$$

### 证明

在所选基下：

$$
L^\#=G^{-1}\mathbb Z^6.
$$

而

$$
\frac{GJ}{5}=U
$$

等价于

$$
\frac J5=G^{-1}U.
$$

由于

$$
U\mathbb Z^6=\mathbb Z^6,
$$

故

$$
\frac J5\mathbb Z^6
=
G^{-1}\mathbb Z^6.
$$

即：

$$
L^\#=\frac J5L.
$$

∎

---

## 定理 39.2（五模性）

$$
\boxed{
L^\#
\simeq
\frac1{\sqrt5}L.
}
$$

### 证明

由

$$
J^TGJ=5G
$$

可知：

$$
\left\langle
\frac J5x,\frac J5y
\right\rangle
=
\frac15\langle x,y\rangle.
$$

所以 \(J/5\) 将 \(L\) 相似地缩放为 \(1/\sqrt5\) 倍，并精确等于对偶格。∎

因此 \(L\) 是一个六维五模格：

$$
\boxed{
\sqrt5\,L^\#
\simeq L.
}
$$

这使此前的判别式关系

$$
\det L=5^3
$$

不再只是数值巧合，而成为模格恒等式所强迫的结果：

$$
\det L=5^{6/2}.
$$

---

# 第四十部　\(\pi\) 与 \(\sqrt5\) 的 Poisson 完成

定义格 Theta 热迹：

$$
\boxed{
\Theta_L(t)
=
\sum_{x\in L}
e^{-\pi t\langle x,x\rangle},
\qquad
t>0.
}
$$

这里：

* \(\pi\) 来自标准 Fourier 自对偶 Gaussian；
* \(t\) 是热尺度；
* \(\sqrt5\) 来自格与对偶格之间的五模比例。

六维 Poisson 求和给出：

$$
\Theta_L(t)
=
\frac1{\operatorname{covol}(L)}
t^{-3}
\Theta_{L^\#}(1/t).
$$

由于：

$$
\operatorname{covol}(L)=\sqrt{\det G}=5^{3/2},
$$

并且：

$$
L^\#\simeq\frac1{\sqrt5}L,
$$

故：

$$
\boxed{
\Theta_L(t)
=
5^{-3/2}t^{-3}
\Theta_L\left(\frac1{5t}\right).
}
\tag{40.1}
$$

---

## 40.1 唯一自对偶热尺度

对偶变换为：

$$
t\longmapsto\frac1{5t}.
$$

固定点满足：

$$
t=\frac1{5t}.
$$

所以：

$$
\boxed{
t_*=\frac1{\sqrt5}.
}
$$

这给 \(\sqrt5\) 一个新的 OACTC 角色证书：

$$
\boxed{
\sqrt5
=
\text{六维黄金外幂格的 Fourier–Poisson 对偶尺度。}
}
$$

注意角色分工：

$$
\boxed{
\begin{aligned}
\pi
&=\text{Gaussian Fourier 规范};\\
\sqrt5
&=\text{格与对偶格的模性比例};\\
1/\sqrt5
&=\text{两者共同决定的自对偶热参数}.
\end{aligned}
}
$$

---

## 40.2 归一化完成热迹

令：

$$
u=\sqrt5\,t,
$$

$$
F_L(u)
=
\Theta_L\left(\frac u{\sqrt5}\right).
$$

则式 (40.1) 化为：

$$
\boxed{
F_L(u)=u^{-3}F_L(1/u).
}
$$

定义完成热迹：

$$
\boxed{
\widehat F_L(u)
=
u^{3/2}F_L(u).
}
$$

于是：

$$
\boxed{
\widehat F_L(u)=\widehat F_L(1/u).
}
\tag{40.2}
$$

若进一步令：

$$
u=e^x,
$$

则：

$$
H_L(x)
=
e^{3x/2}F_L(e^x)
$$

满足：

$$
\boxed{
H_L(x)=H_L(-x).
}
$$

所以 \(x=0\)，即 \(t=1/\sqrt5\)，是完成热迹的严格反射中心。

---

## 40.3 自对偶 Gibbs 能量恒等式

定义自对偶温度下的概率分布：

$$
\mathbb P_*(x)
=
\frac{
e^{-\pi\langle x,x\rangle/\sqrt5}
}{
\Theta_L(1/\sqrt5)
}.
$$

由

$$
\frac{d}{dx}H_L(x)\Big|_{x=0}=0
$$

得到：

$$
\boxed{
\frac{\pi}{\sqrt5}
\mathbb E_*
\bigl[\langle x,x\rangle\bigr]
=
\frac32.
}
$$

因此：

$$
\boxed{
\mathbb E_*
\bigl[\langle x,x\rangle\bigr]
=
\frac{3\sqrt5}{2\pi}.
}
\tag{40.3}
$$

这是一条真正把

$$
\pi,\qquad \sqrt5,\qquad \frac32
$$

放入同一结构中的恒等式：

* \(\pi\)：Fourier 完成；
* \(\sqrt5\)：模格对偶；
* \(3/2\)：六维空间一半维数再除以二，即 \(6/4\)。

它不是数值拼接，而是完成热迹在固定点处的 Ward 型恒等式。

---

# 第四十一部　六维二十面体 Epstein zeta

定义：

$$
\boxed{
E_L(s)
=
\sum_{x\in L\setminus\{0\}}
\langle x,x\rangle^{-s},
\qquad
\Re(s)>3.
}
$$

由 Mellin 变换：

$$
\boxed{
\pi^{-s}\Gamma(s)E_L(s)
=
\int_0^\infty
\left(\Theta_L(t)-1\right)t^{s-1}\,dt.
}
$$

利用 Theta 变换式，得到亚纯延拓以及：

$$
\boxed{
\pi^{-s}\Gamma(s)E_L(s)
=
5^{3/2-s}
\pi^{-(3-s)}
\Gamma(3-s)E_L(3-s).
}
$$

定义：

$$
\boxed{
\Lambda_L(s)
=
5^{s/2}\pi^{-s}\Gamma(s)E_L(s).
}
$$

则：

$$
\boxed{
\Lambda_L(s)=\Lambda_L(3-s).
}
\tag{41.1}
$$

去掉 \(s=0,3\) 的标准极点后，可定义：

$$
\Xi_L(s)
=
s(3-s)\Lambda_L(s),
$$

满足：

$$
\boxed{
\Xi_L(s)=\Xi_L(3-s).
}
$$

---

## 41.1 维数归一化后的临界中点

令：

$$
s=3z.
$$

定义：

$$
\mathfrak X_L(z)=\Xi_L(3z).
$$

则：

$$
\boxed{
\mathfrak X_L(z)=\mathfrak X_L(1-z).
}
$$

所以其归一化固定中点仍然是：

$$
\boxed{
\Re(z)=\frac12.
}
$$

这说明：

> \(\tfrac12\) 并非 Riemann zeta 独有的神秘数字；它是任何完成对偶在把自然维数尺度压缩到单位区间后形成的反射中点。

对六维 Epstein zeta，未经归一化的中心是：

$$
\Re(s)=\frac32.
$$

经过：

$$
z=s/3
$$

归一化后，中心回到：

$$
\Re(z)=\frac12.
$$

---

# 第四十二部　重要负对照：完成并不推出 RH

前文已经得到：

* 精确整数格；
* 精确 Fourier 自对偶；
* \(\pi\)-Gaussian 完成；
* \(\sqrt5\)-模性；
* 完整函数方程；
* 严格临界中点。

但这些仍然**不能**推出所有非平凡零点位于固定中线。

已知许多 Epstein zeta 函数存在临界线外零点；特别是与类数大于一的二次型相关的 Epstein zeta，已有严格的临界线外零点计数结果。([arxiv.org][1])

因此得到 OACTC 的一条关键禁令：

$$
\boxed{
\text{完成对称}
\not\Rightarrow
\text{零点刚性}.
}
$$

必须区分三个层级。

## 42.1 几何完成

$$
\Delta_{\mathrm{dual}}=0.
$$

表示 Fourier、Poisson、Mellin 与反射公式闭合。

## 42.2 乘法完成

$$
\Delta_{\mathrm{Euler}}=0.
$$

表示对象分解为真正的素数局部 Euler 因子或 primitive Hecke 通道。

## 42.3 正性完成

$$
\Delta_{\mathrm{pos}}=0.
$$

表示相应 Weil、Hilbert 空间或自伴算子结构足以排除离线零点。

RH 所要求的不是第一层，而是第三层：

$$
\boxed{
\mathrm{RH}
\sim
\text{完成对象上的全局正性／谱刚性}.
}
$$

所以黄金比例、六维准晶体、\(\pi\) 和函数方程可以提供**正确的完成载体**，却不能替代真正的正性桥。

---

# 第四十三部　真正 canonical 的黄金 zeta

此前项目的 Golden Euler germ 是一个重要的重整化实验对象，仓库已证明可以抽取首个

$$
\zeta(\varphi^2s)
$$

主因子并改善余乘积的收敛区域。

但从阿代尔与数域角度看，最 canonical 的黄金全局对象首先应是：

$$
\boxed{
\zeta_K(s),
\qquad
K=\mathbb Q(\sqrt5).
}
$$

---

## 43.1 素数局部因子

令 \(\chi_5\) 为模 \(5\) 的二次特征。则：

$$
\boxed{
\zeta_K(s)
=
\zeta(s)L(s,\chi_5).
}
$$

局部因子为：

$$
\zeta_{K,p}(s)
=
\begin{cases}
(1-p^{-s})^{-2},
&
p\equiv\pm1\pmod5,
\\[1mm]
(1-p^{-2s})^{-1},
&
p\equiv\pm2\pmod5,
\\[1mm]
(1-5^{-s})^{-1},
&
p=5.
\end{cases}
$$

项目已经机器核验：

* \(p\equiv\pm1\pmod5\) 时在 GoldenInt 中分裂；
* \(p\equiv\pm2\pmod5\) 时保持惰性；
* \(5\) 为分歧素数。

因此 \(\zeta_K\) 是项目现有 Golden prime observer 的自然全局乘积完成。

---

## 43.2 Archimedean 完成

\(K\) 有两个实嵌入，所以完成函数为：

$$
\boxed{
\Lambda_K(s)
=
5^{s/2}
\pi^{-s}
\Gamma\left(\frac s2\right)^2
\zeta_K(s).
}
$$

并满足：

$$
\boxed{
\Lambda_K(s)=\Lambda_K(1-s).
}
$$

每个常数均有独立角色：

$$
\boxed{
\begin{aligned}
5^{s/2}
&:\text{数域判别式完成};\\
\pi^{-s}
&:\text{两个实无穷位的 Gaussian 规范};\\
\Gamma(s/2)^2
&:\text{两个实嵌入的 Mellin 因子};\\
\zeta_K
&:\text{全部有限素理想通道}.
\end{aligned}
}
$$

---

## 43.3 密度—调节子留数

\(K=\mathbb Q(\sqrt5)\) 的：

* 判别式为 \(5\)；
* 类数为 \(1\)；
* 单位群为：

$$
\mathcal O_K^\times
=
\{\pm\varphi^n:n\in\mathbb Z\};
$$

* 调节子为：

$$
R_K=\log\varphi.
$$

解析类数公式给出一般数域 zeta 在 \(s=1\) 的留数表达。([lmfdb.org][2])

在本例中：

$$
\boxed{
\operatorname*{Res}_{s=1}\zeta_K(s)
=
\frac{2\log\varphi}{\sqrt5}.
}
\tag{43.1}
$$

它可以被解释为：

$$
\boxed{
\frac{2\log\varphi}{\sqrt5}
=
\underbrace{2\log\varphi}_{\text{单位流基本周期}}
\times
\underbrace{\frac1{\sqrt5}}_{\text{Minkowski 横截密度}}.
}
$$

这是一条非常完整的“常数意义”恒等式：

* \(\sqrt5\) 记录数域和格的横向协体积；
* \(\log\varphi\) 记录单位轨道的纵向基本长度；
* 两者乘积给出全局算术体积。

---

# 第四十四部　Golden 单位流主 zeta

这一部分给出本轮最重要的新母函数。

令：

$$
\sigma_+,\sigma_-:
K\hookrightarrow\mathbb R
$$

为两个实嵌入。

对：

$$
\alpha\in\mathcal O_K\setminus\{0\}
$$

定义：

$$
a_\alpha=|\sigma_+(\alpha)|^2,
\qquad
b_\alpha=|\sigma_-(\alpha)|^2.
$$

定义各向异性二次型：

$$
\boxed{
Q_\eta(\alpha)
=
e^\eta a_\alpha
+
e^{-\eta}b_\alpha.
}
$$

定义 Golden 单位流主 zeta：

$$
\boxed{
\mathfrak Z_\varphi(s,\eta)
=
\sum_{\alpha\in\mathcal O_K\setminus\{0\}}
Q_\eta(\alpha)^{-s},
\qquad
\Re(s)>1.
}
\tag{44.1}
$$

---

## 定理 44.1（调节子周期）

$$
\boxed{
\mathfrak Z_\varphi(s,\eta+2\log\varphi)
=
\mathfrak Z_\varphi(s,\eta).
}
$$

### 证明

乘以单位 \(\varphi\) 后：

$$
a_{\varphi\alpha}
=
\varphi^2a_\alpha,
$$

$$
b_{\varphi\alpha}
=
\varphi^{-2}b_\alpha.
$$

所以：

$$
Q_\eta(\varphi\alpha)
=
Q_{\eta+2\log\varphi}(\alpha).
$$

而 \(\alpha\mapsto\varphi\alpha\) 是 \(\mathcal O_K\setminus\{0\}\) 的双射。∎

因此 \(\eta\) 不属于整条实线，而属于调节子圆：

$$
\boxed{
\eta\in
\mathbb R/
2\log\varphi\,\mathbb Z.
}
$$

---

## 定理 44.2（Galois 反射）

$$
\boxed{
\mathfrak Z_\varphi(s,\eta)
=
\mathfrak Z_\varphi(s,-\eta).
}
$$

### 证明

Galois 共轭：

$$
\alpha\mapsto\alpha'
$$

交换：

$$
a_\alpha\leftrightarrow b_\alpha.
$$

因此：

$$
Q_\eta(\alpha')
=
Q_{-\eta}(\alpha).
$$

共轭是整数环上的双射。∎

所以 Golden 单位流主 zeta 具有无限二面体对称：

$$
\boxed{
\eta\mapsto\eta+2\log\varphi,
\qquad
\eta\mapsto-\eta.
}
$$

---

# 第四十五部　调节子 Fourier 基因组

定义调节子频率：

$$
\boxed{
\omega_m
=
\frac{\pi m}{\log\varphi},
\qquad
m\in\mathbb Z.
}
\tag{45.1}
$$

它不是人为选择，而是圆

$$
\mathbb R/
2\log\varphi\,\mathbb Z
$$

的字符频率：

$$
e^{i\omega_m(\eta+2\log\varphi)}
=
e^{i\omega_m\eta}.
$$

因此：

$$
\boxed{
\frac{\pi}{\log\varphi}
=
\text{Golden 单位流基本圆的 Fourier 频率单位。}
}
$$

这里：

* \(\pi\) 来自 Fourier 字符；
* \(\log\varphi\) 来自算术调节子。

二者同时出现不是数值巧合。

---

## 45.1 单位轨道的双曲余弦形式

将非零代数整数按单位群分轨。

由于类数为 \(1\)，每个非零理想可以选一个生成元 \(\alpha_{\mathfrak a}\)。

令：

$$
a_{\mathfrak a}
=
|\sigma_+(\alpha_{\mathfrak a})|^2,
$$

$$
b_{\mathfrak a}
=
|\sigma_-(\alpha_{\mathfrak a})|^2,
$$

$$
\delta_{\mathfrak a}
=
\frac12
\log\frac{a_{\mathfrak a}}{b_{\mathfrak a}}.
$$

则：

$$
Q_\eta(\varphi^n\alpha_{\mathfrak a})
=
2\sqrt{a_{\mathfrak a}b_{\mathfrak a}}\,
\cosh
\left(
\eta+\delta_{\mathfrak a}
+2n\log\varphi
\right).
$$

---

## 45.2 双曲核的 Fourier 变换

对 \(\Re(s)>0\)：

$$
\boxed{
\int_{-\infty}^{\infty}
(2\cosh x)^{-s}
e^{-i\omega x}\,dx
=
\frac{
\Gamma\left(\frac{s+i\omega}{2}\right)
\Gamma\left(\frac{s-i\omega}{2}\right)
}{
2\Gamma(s)
}.
}
\tag{45.2}
$$

对单位轨道应用 Poisson 求和，得到：

## 定理 45.1（Golden 调节子 Fourier–Hecke 分解）

$$
\boxed{
\begin{aligned}
\mathfrak Z_\varphi(s,\eta)
={}&
\frac1{2\log\varphi\,\Gamma(s)}
\sum_{m\in\mathbb Z}
\Gamma\left(\frac{s+i\omega_m}{2}\right)
\Gamma\left(\frac{s-i\omega_m}{2}\right)
\\
&\qquad\qquad\qquad
\times
L(s,\chi_m)e^{i\omega_m\eta}.
\end{aligned}
}
\tag{45.3}
$$

其中：

$$
\boxed{
\chi_m((\alpha))
=
\left|
\frac{\sigma_+(\alpha)}
     {\sigma_-(\alpha)}
\right|^{i\omega_m}.
}
$$

### 良定义性

若换生成元：

$$
\alpha\mapsto\pm\varphi^n\alpha,
$$

则：

$$
\log
\left|
\frac{\sigma_+(\varphi^n\alpha)}
     {\sigma_-(\varphi^n\alpha)}
\right|
=
\log
\left|
\frac{\sigma_+(\alpha)}
     {\sigma_-(\alpha)}
\right|
+
2n\log\varphi.
$$

所以相位增加：

$$
2n\omega_m\log\varphi
=
2\pi mn,
$$

指数不变。

因此 \(\chi_m\) 是理想上的良定义单位ary Hecke 型字符。

---

## 45.3 零频模式就是 Dedekind zeta

当 \(m=0\) 时：

$$
\chi_0=1,
$$

所以：

$$
L(s,\chi_0)=\zeta_K(s).
$$

从而：

$$
\boxed{
\frac1{2\log\varphi}
\int_0^{2\log\varphi}
\mathfrak Z_\varphi(s,\eta)\,d\eta
=
\frac{
\Gamma(s/2)^2
}{
2\log\varphi\,\Gamma(s)
}
\zeta_K(s).
}
\tag{45.4}
$$

反过来：

$$
\boxed{
\zeta_K(s)
=
\frac{
2\log\varphi\,\Gamma(s)
}{
\Gamma(s/2)^2
}
\operatorname{Avg}_\eta
\mathfrak Z_\varphi(s,\eta).
}
\tag{45.5}
$$

这给出本理论迄今最清晰的“主函数—基因组”关系：

$$
\boxed{
\text{Dedekind zeta}
=
\text{Golden 单位流主 zeta 的零频观察模式}.
}
$$

而：

$$
\boxed{
L(s,\chi_m)
=
\text{同一主函数的第 }m\text{ 个调节子 Fourier 基因}.
}
$$

所以大量不同的 Hecke \(L\)-函数并不是互不相关的对象；它们是同一个几何—算术母函数在单位流方向上的不同观察频率。

---

# 第四十六部　Golden 留数完成方块

令：

$$
\overline{\mathfrak Z}_\varphi(s)
=
\operatorname{Avg}_\eta
\mathfrak Z_\varphi(s,\eta).
$$

由式 (45.4)：

$$
\overline{\mathfrak Z}_\varphi(s)
=
\frac{\Gamma(s/2)^2}
{2\log\varphi\,\Gamma(s)}
\zeta_K(s).
$$

在 \(s=1\)：

$$
\Gamma(1/2)^2=\pi,
\qquad
\Gamma(1)=1.
$$

结合：

$$
\operatorname*{Res}_{s=1}\zeta_K(s)
=
\frac{2\log\varphi}{\sqrt5},
$$

得到：

$$
\boxed{
\operatorname*{Res}_{s=1}
\overline{\mathfrak Z}_\varphi(s)
=
\frac{\pi}{\sqrt5}.
}
\tag{46.1}
$$

即：

$$
\boxed{
\frac{\pi}{\sqrt5}
=
\underbrace{
\frac{\pi}{2\log\varphi}
}_{\text{Archimedean 单位轨道积分}}
\cdot
\underbrace{
\frac{2\log\varphi}{\sqrt5}
}_{\text{算术 Dedekind 留数}}.
}
\tag{46.2}
$$

这里调节子精确消去：

$$
2\log\varphi.
$$

留下：

$$
\frac{\pi}{\sqrt5}.
$$

这正是二维 Minkowski 格 Epstein zeta 的几何留数：

$$
\text{Gaussian 面积常数}
\div
\text{格协体积}.
$$

所以得到一个完整常数角色链：

$$
\boxed{
\begin{aligned}
\pi
&:\text{Archimedean Gaussian 面积};\\
2\log\varphi
&:\text{单位轨道周长};\\
\sqrt5
&:\text{Minkowski 格协体积};\\
\pi/\sqrt5
&:\text{几何谱 zeta 留数};\\
2\log\varphi/\sqrt5
&:\text{算术 Dedekind zeta 留数}.
\end{aligned}
}
$$

---

# 第四十七部　从算术原语到六维 Hilbert–Theta 观察者

前述单位流主 zeta 是秩一的黄金对象。

六维准晶体对应的是秩三提升。

前文构造的最大阶饱和格 \(W_{\max}\)：

* 是秩 \(6\) 的 \(\mathbb Z\)-模；
* 被 \(\Phi\) 保持；
* \(\Phi\) 满足：

$$
\Phi^2-\Phi-I=0.
$$

因此 \(W_{\max}\) 是秩三的 \(\mathcal O_K\)-模。

由于：

$$
K=\mathbb Q(\sqrt5)
$$

类数为 \(1\)，有限生成无挠 \(\mathcal O_K\)-模为自由模，所以非规范地：

$$
\boxed{
W_{\max}\simeq\mathcal O_K^3.
}
$$

---

## 47.1 一个 \(K\)-值二次型

令 \(B(x,y)\) 为原六维实内积。

定义：

$$
\boxed{
\mathcal H(x,y)
=
\frac12B(x,y)
+
\frac{\sqrt5}{10}B(Jx,y).
}
\tag{47.1}
$$

则：

$$
\sigma_+\bigl(\mathcal H(x,y)\bigr)
=
B(P_\parallel x,P_\parallel y),
$$

$$
\sigma_-\bigl(\mathcal H(x,y)\bigr)
=
B(P_\perp x,P_\perp y).
$$

### 证明

写：

$$
B=B_\parallel+B_\perp,
$$

而：

$$
B(Jx,y)
=
\sqrt5(B_\parallel-B_\perp).
$$

代入两个嵌入即可。∎

因此：

> 物理空间与内部空间不是两个后来拼接的实二次型；它们是同一个 \(K\)-值二次型在两个实嵌入下的读数。

---

## 47.2 两变量 Hilbert Theta

定义：

$$
\boxed{
\Theta_{\mathcal H}(z_+,z_-)
=
\sum_{x\in W_{\max}}
\exp\left[
\pi i
\left(
z_+\sigma_+(\mathcal H[x])
+
z_-\sigma_-(\mathcal H[x])
\right)
\right].
}
\tag{47.2}
$$

其中：

$$
(z_+,z_-)\in\mathbb H^2.
$$

不同观察限制给出不同对象：

### 对角观察

$$
z_+=z_-=it
$$

给出普通六维格 Theta。

### Golden 单位流观察

$$
z_+=it\,e^\eta,
\qquad
z_-=it\,e^{-\eta}
$$

给出各向异性准晶体观察。

### Galois 观察

$$
(z_+,z_-)\mapsto(z_-,z_+)
$$

交换物理与内部通道。

### cusp 观察

$$
\Im z_\pm\to\infty
$$

产生 \(q\)-级数和局部模式展开。

这说明六维准晶体、单位流 zeta 和 Hilbert 模形式可以被视为同一个二变量对象的不同观察切片。

---

# 第四十八部　Klein–Hilbert–Ramanujan 图册

这条联系已有非常直接的外部数学支撑：

* \(\mathbb Q(\sqrt5)\) 的 Hilbert 模函数可通过两变量周期积分与 Theta 常数表达；
* Klein 的二十面体不变量可给出该域上的 Hilbert 模形式坐标。([numdam.org][3])

因此可以定义四图表：

$$
\boxed{
\mathfrak A_{\mathrm{gold}}
=
\left(
\mathcal A_{\mathrm{lattice}},
\mathcal A_{\mathrm{Hilbert}},
\mathcal A_{\mathrm{Klein}},
\mathcal A_{\mathrm{Ramanujan}}
\right).
}
$$

其中：

$$
\mathcal A_{\mathrm{lattice}}
=
\text{六维 Minkowski/准晶体图表},
$$

$$
\mathcal A_{\mathrm{Hilbert}}
=
\text{两实嵌入 Hilbert 模图表},
$$

$$
\mathcal A_{\mathrm{Klein}}
=
\text{二十面体不变量图表},
$$

$$
\mathcal A_{\mathrm{Ramanujan}}
=
\text{level-5 }q\text{-级数、乘积与连分数图表}.
$$

已知 Klein 二十面体不变量确实能够生成 \(\mathbb Q(\sqrt5)\) 的 Hilbert 模形式，这表明“二十面体—黄金域—两变量模形式”不是比喻。([numdam.org][3])

仍待建立的具体桥是：

$$
\boxed{
\text{项目所构造的 }\Theta_{\mathcal H}
\quad\longrightarrow\quad
\text{已知 Klein/Hilbert 生成元}.
}
$$

科学检验方式是：

1. 计算若干 Hilbert \(q\)-展开；
2. 比较权、特征与对称性；
3. 在对角或 Humbert/Hirzebruch–Zagier 曲线上限制；
4. 检验是否出现 Rogers–Ramanujan 或其他 level-5 函数；
5. 用 Sturm 型有限系数判据证明相等，而不是数值拟合。

---

# 第四十九部　直接格与倒格的共轭完成

由：

$$
L^\#=\frac J5L
$$

且 \(J\) 在两个三维空间上分别取特征值：

$$
+\sqrt5,\qquad-\sqrt5,
$$

得到：

$$
\boxed{
P_\parallel L^\#
=
\frac1{\sqrt5}P_\parallel L,
}
$$

$$
\boxed{
P_\perp L^\#
=
-\frac1{\sqrt5}P_\perp L.
}
$$

因此倒空间并不是另一个无关晶格，而是：

$$
\boxed{
\text{直接空间的 Galois 共轭、符号翻转和 }1/\sqrt5\text{ 缩放}.
}
$$

这对准晶体衍射的观察者解释非常重要：

* 直接空间读取原子位置；
* 倒空间读取 Fourier/Bragg 模式；
* 内部星映射读取窗口坐标；
* \(J/5\) 将直接格精确变成倒格。

因此 \(\sqrt5\) 还是：

$$
\boxed{
\text{黄金准晶体直接—倒空间之间的 Fourier 尺度。}
}
$$

---

# 第五十部　真正适合 RH 的新观察索引

前面的推导表明，仅使用：

$$
(p,t)
$$

作为“素数—时间”观察索引还不够。

黄金数域自然增加第三个坐标：

$$
\boxed{
(p,m,t).
}
$$

其中：

* \(p\)：有限素数或素理想通道；
* \(m\)：调节子圆上的 Fourier/Hecke 模式；
* \(t\)：谱高度、时间或 Mellin 频率。

定义：

$$
\boxed{
q_{p,m,t}:X\to O_{p,m,t}.
}
$$

这可以称为：

$$
\boxed{
\textbf{Prime–Regulator–Time Observer}.
}
$$

其三个方向分别读取：

$$
\begin{aligned}
p&:\text{局部乘法结构};\\
m&:\text{两个实嵌入之间的相对相位};\\
t&:\text{解析演化与零点高度}.
\end{aligned}
$$

项目现有 Golden prime classification 已经闭合 \(p\)-轴。

Golden 单位流分解提供 \(m\)-轴。

Weil 显式公式与 prime-time tomography 提供 \(t\)-轴。

这比将 \(\varphi\) 直接塞入 Riemann zeta 更科学，因为 \(\varphi\) 不是改变 ζ 定义，而是提供一个新的、来源明确的观察坐标。

---

# 第五十一部　对 RH 的精确意义

## 51.1 Golden Dedekind GRH

因为：

$$
\zeta_K(s)=\zeta(s)L(s,\chi_5),
$$

所以 \(\zeta_K\) 的广义 RH 等价于：

$$
\boxed{
\mathrm{RH}(\zeta)
\quad+\quad
\mathrm{GRH}(L(s,\chi_5)).
}
$$

这并没有降低难度，却提供了一个更有结构的联合系统：

* 一个无扭曲通道；
* 一个模 \(5\) 分裂／惰性通道。

## 51.2 调节子模式族

每个：

$$
L(s,\chi_m)
$$

都有真正的理想 Euler product。

因此式 (45.3) 展示了一个重要机制：

$$
\boxed{
\text{几何耦合主函数}
\xrightarrow{\text{单位流 Fourier}}
\text{乘法 primitive Hecke 通道}.
}
$$

这正是 Yu Deng 式 primitive decomposition 的算术原型：

* 原始对象中全部单位历史混合；
* 对调节子圆做 Fourier 分解；
* 每个 Fourier 模式成为不可再混合的乘法角色；
* Gamma 因子自动给出 Archimedean 完成。

## 51.3 Wang 式多尺度结构

若一个潜在负 Weil 模式在：

$$
(p,m,t)
$$

空间中分散，则可以期待：

* 不同素数通道的近正交；
* 不同调节子模式的 Fourier 正交；
* 不同高度窗口的平均抵消。

若它沿一条嵌套链集中，则成为 sticky 模式，再使用 primitive Hecke 通道与高阶重整化分析。

但真正完成 RH 仍需要：

$$
\boxed{
\text{off-line zero}
\Longrightarrow
\text{某个 }(p,m,t)\text{ 通道中的不可消除负见证}.
}
$$

这条桥目前尚未证明。

---

# 第五十二部　新的科学结论分级

## 已经由本轮推导闭合

$$
\boxed{
L^\#=\frac J5L.
}
$$

$$
\boxed{
L\text{ 是六维五模格}.
}
$$

$$
\boxed{
\Theta_L(t)
=
5^{-3/2}t^{-3}
\Theta_L(1/(5t)).
}
$$

$$
\boxed{
t_*=\frac1{\sqrt5}.
}
$$

$$
\boxed{
\Lambda_L(s)=\Lambda_L(3-s).
}
$$

$$
\boxed{
\operatorname*{Res}_{s=1}\zeta_{\mathbb Q(\sqrt5)}(s)
=
\frac{2\log\varphi}{\sqrt5}.
}
$$

$$
\boxed{
\mathfrak Z_\varphi(s,\eta)
\text{ 对 }\eta\text{ 具有周期 }2\log\varphi.
}
$$

$$
\boxed{
\omega_m=\frac{\pi m}{\log\varphi}.
}
$$

$$
\boxed{
\mathfrak Z_\varphi
\text{ 的 Fourier 模式为 Hecke }L(s,\chi_m).
}
$$

$$
\boxed{
\zeta_K
=
\mathfrak Z_\varphi\text{ 的零频观察}.
}
$$

---

## 有强文献支撑，但需与项目对象桥接

$$
\boxed{
\text{Klein 二十面体不变量}
\longleftrightarrow
\mathbb Q(\sqrt5)\text{ Hilbert 模形式}.
}
$$

相关周期映射与 Theta 表达已经存在于 Hilbert 模曲面文献中。([numdam.org][3])

需要证明的是项目具体六维格 Theta 与这些标准生成元的关系。

---

## 开放高风险桥

$$
\boxed{
\begin{aligned}
&\text{Hilbert Theta 的特定限制是否给出 Ramanujan level-5 主函数};\\
&\text{Prime–Regulator–Time 观察是否对 off-line ζ 零点充分};\\
&\text{non-sticky 模式是否产生严格 Weil 正性增益};\\
&\text{sticky 模式是否可被有限 primitive Hecke 通道重整化};\\
&\text{这些余项是否小于 off-line witness amplification}.
\end{aligned}
}
$$

---

# 第五十三部　首批形式化顺序

建议继续归入 OACTC，按以下依赖顺序形式化：

```text
D5/S3/Geometry/GoldenCompletion/
  ExteriorA4Gram.lean
  IntegralHodgeOperator.lean
  ExteriorA4FiveModular.lean
  DualLatticeSimilarity.lean

D5/S3/Analytic/GoldenCompletion/
  FiveModularTheta.lean
  FiveModularPoissonEquation.lean
  SelfDualHeatPoint.lean
  IcosahedralEpsteinCompletion.lean

D5/S3/NumberField/GoldenCompletion/
  GoldenDedekindEulerFactors.lean
  GoldenRegulator.lean
  GoldenDedekindResidue.lean

D5/S3/Analytic/GoldenUnitFlow/
  AnisotropicQuadraticForm.lean
  RegulatorPeriodicity.lean
  CoshOrbitDecomposition.lean
  RegulatorFourierTransform.lean
  HeckeModeExtraction.lean
  ZeroModeDedekindBridge.lean

D5/S3/Analytic/HilbertGolden/
  GoldenModuleRankThree.lean
  GoldenValuedQuadraticForm.lean
  HilbertThetaObserver.lean
  IcosahedralInvariantBridge.lean

D5/S3/Observer/ArithmeticTomography/
  PrimeRegulatorTimeObserver.lean
  RegulatorModeRefinement.lean
```

最优先闭合的核心链是：

$$
\boxed{
\Lambda^2A_4
\to
5\text{-模格}
\to
\Theta\text{ 自对偶}
\to
\text{Epstein 完成}
}
$$

以及：

$$
\boxed{
\mathbb Q(\sqrt5)\text{ 单位流}
\to
\eta\text{ 周期}
\to
\omega_m=\frac{\pi m}{\log\varphi}
\to
L(s,\chi_m).
}
$$

---

# 本轮最终结论

此前我们说：

$$
\text{六维准晶体}
=
\text{两个黄金共轭三维观察的整数完成}.
$$

现在可以继续加强为：

$$
\boxed{
\text{六维黄金完成不仅产生几何准晶体，}
\newline
\text{还通过 Poisson、Mellin 和单位流 Fourier 分解，
产生一个完整的 zeta／Hecke 函数基因组。}
}
$$

其常数角色精确为：

$$
\boxed{
\begin{aligned}
5
&=\text{判别式与五模层级};\\
\sqrt5
&=\text{格—对偶格尺度};\\
\varphi
&=\text{单位流与显—隐 inflation};\\
\log\varphi
&=\text{调节子圆周长};\\
\pi
&=\text{Fourier 字符与 Gaussian 完成};\\
\frac{\pi}{\log\varphi}
&=\text{调节子 Fourier 基频};\\
\frac{2\log\varphi}{\sqrt5}
&=\text{Dedekind zeta 留数};\\
\frac{\pi}{\sqrt5}
&=\text{几何格点 zeta 留数};\\
\frac12
&=\text{维数归一化后的完成对偶中点}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
\text{黄金比例不只是一个递归固定点，}
\newline
\text{它的对数定义了算术单位流的圆周；
该圆周的 Fourier 模式，
正是一族 primitive Hecke }L\text{-函数。}
}
$$

这使“常数的意义”“拉马努金主函数基因组”“六维准晶体”和“阿代尔观察者”第一次在一个可计算、可证伪、可形式化的母函数中真正合流。

[1]: https://arxiv.org/abs/1204.6297 "https://arxiv.org/abs/1204.6297"
[2]: https://www.lmfdb.org/NumberField/4.0.1334025.9 "https://www.lmfdb.org/NumberField/4.0.1334025.9"
[3]: https://www.numdam.org/articles/10.5802/jtnb.993/ "https://www.numdam.org/articles/10.5802/jtnb.993/"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.3：五进观察者碰撞、有限二十面体几何与双 \(A_5\) Theta 完成

本轮从前文**第五十三部之后**继续追加。

前文得到：

$$
\Lambda^2A_4
\longrightarrow
J^2=5I
\longrightarrow
\Phi^2-\Phi-I=0
\longrightarrow
V_3\oplus V_3'
\longrightarrow
\text{六维黄金完成}.
$$

继续考察这个结构在素数 \(5\) 处的退化，会出现一个更深的闭环：

$$
\boxed{
\begin{aligned}
\text{实无穷位：}\quad&
V_3\oplus V_3'
&&\text{两个黄金共轭观察通道};\\
\text{模 }5\text{：}\quad&
0\to R_3\to \overline L_6\to R_3\to0
&&\text{一个三维观察者的一阶自扩张};\\
\text{有限 Fourier：}\quad&
\mathbb C[(\mathbb F_5)^3]^{A_5}
&&\text{压缩为七个观察状态};\\
\text{level }5\text{ 模作用：}\quad&
7=1+3+3'
&&\text{再次恢复黄金共轭分解}.
\end{aligned}
}
$$

这意味着：

> 六维黄金结构在实数域上表现为两个可分离的三维空间；
> 在分歧素数 \(5\) 上，两者碰撞成一个带 nilpotent 一阶信息的三维模；
> 经过有限 Fourier 完成后，又以 level-5 模群的两个三维表示重新分裂。

这已经不再只是“黄金比例、五次方程与准晶体共享 \(A_5\)”；它是一条完整的：

$$
\boxed{
\text{分裂}
\to
\text{分歧碰撞}
\to
\text{jet 保留}
\to
\text{Fourier 重分裂}
}
$$

的阿代尔观察者动力学。

---

# 第五十四部　分歧素数是共轭观察者碰撞点

沿用：

$$
L=\Lambda^2A_4,
$$

以及整数算子：

$$
J^2=5I,
\qquad
J^TG=GJ.
$$

令：

$$
\overline L=L/5L,
\qquad
\overline J=J\bmod5.
$$

由于：

$$
J^2=5I,
$$

模 \(5\) 后立即得到：

$$
\boxed{
\overline J^2=0.
}
\tag{54.1}
$$

对前文给出的显式 \(6\times6\) 矩阵做有限域行约化可得：

$$
\boxed{
\operatorname{rank}_{\mathbb F_5}\overline J=3.
}
\tag{54.2}
$$

因此：

$$
\dim\ker\overline J=3.
$$

又因为：

$$
\operatorname{im}\overline J
\subseteq
\ker\overline J
$$

且二者维数均为 \(3\)，所以：

$$
\boxed{
\operatorname{im}\overline J
=
\ker\overline J.
}
\tag{54.3}
$$

定义：

$$
\boxed{
R:=\operatorname{im}\overline J
=\ker\overline J.
}
$$

于是存在一个 \(A_5\)-等变正合列：

$$
\boxed{
0
\longrightarrow
R
\longrightarrow
\overline L
\xrightarrow{\ \overline J\ }
R
\longrightarrow
0.
}
\tag{54.4}
$$

这里：

$$
\dim_{\mathbb F_5}R=3,
\qquad
\dim_{\mathbb F_5}\overline L=6.
$$

---

## 54.1 实分裂在模 \(5\) 下为何消失

在实数域中：

$$
J
$$

具有两个不同特征值：

$$
+\sqrt5,
\qquad
-\sqrt5,
$$

所以：

$$
L\otimes\mathbb R
=
E_\parallel\oplus E_\perp.
$$

但模 \(5\) 时：

$$
\sqrt5\equiv0.
$$

两个特征值碰撞为同一个值 \(0\)，对角分解失效，转而形成三个大小为 \(2\) 的 nilpotent Jordan 块。

因此：

$$
\boxed{
\text{物理空间与内部空间在 }p=5\text{ 处不再可分离，}
}
$$

但它们的差异并未完全消失，而是被保存在：

$$
\boxed{
\overline J
}
$$

这一阶 nilpotent 信息中。

---

## 54.2 黄金算子的 ramified jet

前文定义：

$$
\Phi=\frac{I+J}{2},
\qquad
\Phi^2-\Phi-I=0.
$$

模 \(5\) 时：

$$
2^{-1}\equiv3\pmod5,
$$

所以：

$$
\overline\Phi
=
3(I+\overline J)
=
3I+3\overline J.
$$

定义：

$$
N:=\overline\Phi-3I.
$$

则：

$$
\boxed{
N=3\overline J,
\qquad
N^2=0,
\qquad
\operatorname{rank}N=3.
}
\tag{54.5}
$$

而黄金多项式在 \(\mathbb F_5\) 上退化为：

$$
x^2-x-1
=
(x-3)^2.
$$

所以：

$$
\boxed{
\overline\Phi
=
3I+N
}
$$

不是普通特征值 \(3\)，而是一个带一阶 infinitesimal direction 的重根观察。

---

## 定义 54.1（分歧共轭 jet）

设共轭特征值在某素数处合并为重根 \(\lambda_0\)。定义：

$$
\boxed{
\operatorname{RamJet}_{\mathfrak p}(T)
=
\left(
\lambda_0,\,
T-\lambda_0I,\,
(T-\lambda_0I)^2,\ldots
\right).
}
$$

黄金实例中：

$$
\operatorname{RamJet}_5(\Phi)
=
(3,N),
\qquad
N^2=0.
$$

它表达：

> 当两个共轭观察值在 residue field 中无法区分时，必须引入一阶 jet，而不是继续添加同类型的标量观察。

项目已经机器核验 \(5\) 在 GoldenInt 中是分歧平方，并且其他素数按模 \(5\) 分类为分裂或惰性。

---

# 第五十五部　判别式模与三个五进边界通道

前文的 Gram 矩阵 \(G\) 满足：

$$
\det G=5^3.
$$

进一步做 Smith 标准形计算得到：

$$
\boxed{
\operatorname{SNF}(G)
=
\operatorname{diag}(1,1,1,5,5,5).
}
\tag{55.1}
$$

所以对偶格商为：

$$
\boxed{
D_L
:=
L^\#/L
\cong
(\mathbb Z/5\mathbb Z)^3.
}
\tag{55.2}
$$

其元素总数为：

$$
|D_L|=5^3=125.
$$

这说明：

$$
\boxed{
L\text{ 的全部有限对偶缺陷都集中在素数 }5,
}
$$

并且恰有三个独立的五进边界坐标。

---

## 55.1 判别式模等同于 nilpotent radical

前文已经证明：

$$
L^\#=\frac J5L.
$$

定义映射：

$$
\Psi:
L^\#/L
\longrightarrow
R
$$

为：

$$
\Psi\left(
\frac{Jx}{5}+L
\right)
=
\overline J\,\overline x.
$$

若：

$$
\frac{Jx}{5}
-
\frac{Jy}{5}
\in L,
$$

则：

$$
J(x-y)\in5L,
$$

所以：

$$
\overline J(\overline x-\overline y)=0.
$$

因此 \(\Psi\) 良定义。

它显然满射，而两侧均有 \(5^3\) 个元素，所以：

$$
\boxed{
D_L
\simeq
R
}
\tag{55.3}
$$

作为 \(A_5\)-模成立。

因此：

$$
\boxed{
\text{六维格的判别式边界}
=
\text{模 }5\text{ Hodge nilpotent 的三维像}.
}
$$

---

# 第五十六部　有限域中的完整二十面体几何

选择 \(R\simeq\mathbb F_5^3\) 的一组基后，\(A_5\) 的两个生成元可以写成：

$$
A=
\begin{pmatrix}
0&0&1\\
1&0&0\\
0&1&0
\end{pmatrix},
$$

$$
B=
\begin{pmatrix}
4&4&3\\
1&0&4\\
0&1&4
\end{pmatrix}.
$$

其中：

$$
A^3=I,
\qquad
B^5=I.
$$

这两个矩阵生成一个阶为 \(60\) 的群。

由于 \(A_5\) 是阶 \(60\) 的单群，这给出一个忠实表示：

$$
\boxed{
A_5
\hookrightarrow
GL_3(\mathbb F_5).
}
\tag{56.1}
$$

---

## 56.1 不变二次型

两个生成元共同保持二次型矩阵：

$$
H=
\begin{pmatrix}
2&1&1\\
1&2&1\\
1&1&2
\end{pmatrix}.
$$

即：

$$
A^THA=H,
\qquad
B^THB=H.
$$

并且：

$$
\det H=4\neq0\pmod5.
$$

定义：

$$
\boxed{
q(v)=v^THv\in\mathbb F_5.
}
\tag{56.2}
$$

所以 \(A_5\) 作用保持 \(q\)。

这正是经典同构：

$$
A_5
\simeq
\Omega_3(5)
\simeq
PSL_2(5)
$$

的一个显式三维实现；\(A_5\)、有限域圆锥与 \(PSL_2\) 之间的关系是经典有限几何主题。([数字对象标识符][1])

---

## 56.2 向量轨道的精确分解

对全部 \(125\) 个向量做精确有限枚举，得到七个 \(A_5\)-轨道：

$$
\boxed{
1+12+12+20+20+30+30=125.
}
\tag{56.3}
$$

可按二次型值标记为：

$$
\begin{array}{c|c|c}
\text{轨道}&q(v)&\text{大小}\\
\hline
O_0&0&1\\
I_+&0&12\\
I_-&0&12\\
F_2&2&20\\
F_3&3&20\\
E_1&1&30\\
E_4&4&30
\end{array}
$$

其中：

* \(I_\pm\)：两个 isotropic chirality；
* \(F_2,F_3\)：两个非平方范数壳；
* \(E_1,E_4\)：两个平方范数壳。

---

# 第五十七部　三十一条射影方向就是二十面体的全部旋转轴

对非零向量取射影化：

$$
\mathbb P(R)
=
(R\setminus\{0\})/\mathbb F_5^\times.
$$

因为：

$$
|\mathbb F_5^\times|=4,
$$

所以：

$$
|\mathbb P(R)|
=
\frac{125-1}{4}
=
31.
$$

这 \(31\) 个射影方向分成：

$$
\boxed{
31=6+10+15.
}
\tag{57.1}
$$

---

## 57.1 六个 isotropic 方向

非零 isotropic 向量共有：

$$
12+12=24.
$$

每条射影线含 \(4\) 个非零向量，所以：

$$
\boxed{
24/4=6.
}
$$

这六条 isotropic 线对应二十面体的六条五重旋转轴，即六对相反顶点。

---

## 57.2 十个非平方方向

$$
|F_2|+|F_3|
=
40.
$$

所以：

$$
\boxed{
40/4=10.
}
$$

它们对应十条三重旋转轴，即十对相反面。

---

## 57.3 十五个平方方向

$$
|E_1|+|E_4|
=
60.
$$

所以：

$$
\boxed{
60/4=15.
}
$$

它们对应十五条二重旋转轴，即十五对相反边。

---

## 定理 57.1（有限二十面体轴分解）

$$
\boxed{
\mathbb P^2(\mathbb F_5)
=
\mathcal A_5
\sqcup
\mathcal A_3
\sqcup
\mathcal A_2,
}
$$

其中：

$$
|\mathcal A_5|=6,
\qquad
|\mathcal A_3|=10,
\qquad
|\mathcal A_2|=15.
$$

各轨道稳定子阶分别为：

$$
10,\qquad6,\qquad4,
$$

即对应：

* 五阶循环子群的 normalizer；
* 三阶循环子群的 normalizer；
* 二阶旋转的 centralizer。

复杂射影二十面体中同样存在一个自然的 \(31\) 点构型，分为六个顶点轴点、十个面轴点和十五个边轴点。([科学直通车][2])

所以：

$$
\boxed{
\text{六维格的三维判别式模，
在射影化以后精确恢复二十面体的全部旋转轴。}
}
$$

这是一条非常强的局部—全局闭环：

$$
\text{六维整数格的 }5\text{-进边界}
\longrightarrow
\text{三维有限二次空间}
\longrightarrow
\text{三维实二十面体轴几何}.
$$

---

# 第五十八部　局部商观察失明，但 residue-linear 观察忠实

项目已经机器证明：

$$
\boxed{
\text{所有有限 }p\text{-群商观察者在 }A_5\text{ 上可以完全失明。}
}
$$

即全部 prime-power quotient residual 仍然是整个 \(A_5\)。

但现在得到另一个观察者：

$$
\boxed{
\rho_5:
A_5
\longrightarrow
GL_3(\mathbb F_5),
}
$$

而且：

$$
\ker\rho_5=\{1\}.
$$

这两件事不矛盾，因为：

$$
GL_3(\mathbb F_5)
$$

不是 \(5\)-群。

因此应当严格区分：

$$
\boxed{
\begin{aligned}
\text{prime-power quotient observer}
&:\quad
G\to P,\ P\text{ 为 }p\text{-群};\\
\text{residue-linear observer}
&:\quad
G\to GL(V_{\mathbb F_p});\\
\text{ramified jet observer}
&:\quad
G\to GL(V_{\mathbb F_p}[\varepsilon]/\varepsilon^2).
\end{aligned}
}
$$

---

## 定理 58.1（观察者类型不可替代性）

存在有限群 \(G=A_5\)，使：

$$
\boxed{
\text{全部 prime-power quotient observers 不忠实，}
}
$$

但：

$$
\boxed{
\text{一个 characteristic-5 residue-linear observer 忠实。}
}
$$

因此：

$$
\boxed{
\text{同一个素数上的“局部观察”并不是单一概念。}
}
$$

观察载体的范畴：

* 群商；
* 线性表示；
* 模形式；
* jet；
* 上同调；

会根本改变观察完备性。

这是 DECT 的一个标准定义逃逸实例：旧定义“素数局部观察＝\(p\)-群商”留下全盲核；加入“模 \(p\) 线性表示”后，残差被完全切开。

---

# 第五十九部　125 个边界状态的有限 Fourier 完成

令：

$$
\zeta_5=e^{2\pi i/5}.
$$

在 \(R=\mathbb F_5^3\) 上定义有限 Fourier 变换：

$$
\boxed{
(\mathcal Ff)(x)
=
\sum_{y\in R}
\zeta_5^{\,x^THy}f(y).
}
\tag{59.1}
$$

由于 \(H\) 非退化：

$$
\boxed{
\mathcal F^2f(x)
=
125\,f(-x).
}
\tag{59.2}
$$

而 \(-1=4\) 是 \(\mathbb F_5\) 中的平方，所以负号保持上述七个 \(A_5\)-轨道。

\(\mathcal F\) 与几何 \(A_5\) 作用交换，因此保持：

$$
\mathbb C[R]^{A_5}.
$$

这个不变函数空间维数恰为七：

$$
\boxed{
\dim\mathbb C[R]^{A_5}=7.
}
$$

---

## 59.1 七状态 Fourier 矩阵

在轨道指示函数基：

$$
(
O_0,I_+,I_-,F_2,F_3,E_1,E_4
)
$$

下，\(\mathcal F\) 的矩阵为：

$$
\boxed{
M=
\begin{pmatrix}
1&12&12&20&20&30&30\\
1&2-5\varphi&-3+5\varphi&-5&-5&5&5\\
1&-3+5\varphi&2-5\varphi&-5&-5&5&5\\
1&-3&-3&5\varphi&5-5\varphi&0&0\\
1&-3&-3&5-5\varphi&5\varphi&0&0\\
1&2&2&0&0&-5+5\varphi&-5\varphi\\
1&2&2&0&0&-5\varphi&-5+5\varphi
\end{pmatrix}.
}
\tag{59.3}
$$

直接利用：

$$
\varphi^2=\varphi+1
$$

可验证：

$$
\boxed{
M^2=125I_7.
}
\tag{59.4}
$$

这不是浮点拟合，而是对 \(125\) 个有限状态的精确 cyclotomic 计数。

---

# 第六十部　粗观察是四维的，黄金残余恰好是三维的

定义对称与反对称通道：

$$
I_s=I_++I_-,
\qquad
I_a=I_+-I_-,
$$

$$
F_s=F_2+F_3,
\qquad
F_a=F_2-F_3,
$$

$$
E_s=E_1+E_4,
\qquad
E_a=E_1-E_4.
$$

在基：

$$
(O_0,I_s,F_s,E_s,I_a,F_a,E_a)
$$

中，矩阵 \(M\) 分块为：

$$
\boxed{
M
\simeq
M_{\mathrm{coarse}}
\oplus
M_{\mathrm{chiral}},
}
$$

其中：

$$
\boxed{
M_{\mathrm{coarse}}
=
\begin{pmatrix}
1&24&40&60\\
1&-1&-10&10\\
1&-6&5&0\\
1&4&0&-5
\end{pmatrix},
}
\tag{60.1}
$$

而：

$$
\boxed{
M_{\mathrm{chiral}}
=
\operatorname{diag}
\left(
-5\sqrt5,\,
5\sqrt5,\,
5\sqrt5
\right).
}
\tag{60.2}
$$

并且：

$$
M_{\mathrm{coarse}}^2=125I_4.
$$

---

## 60.1 最重要的解释

粗观察者只记录：

* 零态；
* 是否 isotropic；
* 是否平方范数；
* 是否非平方范数。

这一层完全是有理的。

黄金常数只出现在三个反对称差值中：

$$
I_a,\qquad F_a,\qquad E_a.
$$

所以：

$$
\boxed{
\sqrt5
\text{ 不是粗略数量统计中的常数，}
}
$$

而是：

$$
\boxed{
\text{当观察者试图区分同一几何轴类型的两个方向／手性时，
出现的完成常数。}
}
$$

这给 \(\sqrt5\) 增加一个新的结构角色：

$$
\boxed{
\sqrt5
=
\text{有限二十面体 Fourier 观察中的 chiral residual eigenvalue}.
}
$$

---

## 60.2 七状态压缩链

完整边界有：

$$
125
$$

个状态。

利用 \(A_5\) 对称，压缩为：

$$
7
$$

个轨道状态。

再遗忘 chirality，压缩为：

$$
4
$$

个粗状态。

因此：

$$
\boxed{
125
\longrightarrow
7
\longrightarrow
4.
}
$$

被第二次压缩丢失的残余维数为：

$$
\boxed{
7-4=3.
}
$$

恰好对应：

$$
V_3
\quad\text{或}\quad
V_3'
$$

型黄金三维信息。

这是一条完整的 observer-compression 结构：

$$
\boxed{
\text{全状态}
\to
\text{对称轨道}
\to
\text{粗范数}
+
\text{三维手性残余}.
}
$$

---

# 第六十一部　有限 Weil 变换产生第二个 \(A_5\)

现在定义：

$$
Q(x)=\frac12q(x)\in\mathbb F_5.
$$

令有限相位算子：

$$
\boxed{
(Tf)(x)
=
\zeta_5^{Q(x)}f(x).
}
\tag{61.1}
$$

在七轨道基中：

$$
T=
\operatorname{diag}
\left(
1,1,1,
\zeta_5,\zeta_5^4,
\zeta_5^3,\zeta_5^2
\right).
$$

令 \(\widetilde{\mathcal F}\) 是在正交归一轨道基中的单位 Fourier 变换：

$$
\widetilde{\mathcal F}
=
125^{-1/2}\mathcal F.
$$

再定义：

$$
S:=-\widetilde{\mathcal F}.
$$

对上述七维空间进行直接 cyclotomic 矩阵计算，得到：

$$
\boxed{
S^2=I,
\qquad
T^5=I,
\qquad
(ST)^3=I.
}
\tag{61.2}
$$

这正是二十面体群的表示：

$$
\boxed{
\langle S,T
\mid
S^2=T^5=(ST)^3=1
\rangle
\simeq
A_5.
}
$$

因为 \(T\) 确实具有阶 \(5\)，所得表示非平凡；由 \(A_5\) 单性，像是忠实的。

---

## 61.1 两个不同的 \(A_5\)

现在系统中出现两个相互交换的 \(A_5\)。

### 几何 \(A_5^{\mathrm{geo}}\)

作用于：

$$
R=\mathbb F_5^3,
$$

保持二次型 \(q\)。

### 模／Fourier \(A_5^{\mathrm{mod}}\)

由：

$$
S=-\text{finite Fourier},
\qquad
T=\text{quadratic phase}
$$

生成，作用于：

$$
\mathbb C[R]^{A_5^{\mathrm{geo}}}.
$$

因为 Fourier 和二次相位与正交群作用相容，两套作用形成有限 Weil 双对结构。

有限判别式模上的 Weil 表示能够分解为各素数局部部分，是标准的 \(p\)-adic Weil 表示框架。([arXiv][3])

---

## 定理 61.1（七维模 \(A_5\) 分解）

七维表示的特征标在阶 \(1,2,3,5\) 元素上为：

$$
\chi=(7,-1,1,2).
$$

与 \(A_5\) 特征标表比较可得：

$$
\boxed{
\mathbb C^7
\simeq
\mathbf1
\oplus
V_3
\oplus
V_3'.
}
\tag{61.3}
$$

### 验证

$$
\chi_{\mathbf1}
+
\chi_{V_3}
+
\chi_{V_3'}
$$

在各类上为：

$$
\begin{aligned}
1A:&\quad1+3+3=7,\\
2A:&\quad1-1-1=-1,\\
3A:&\quad1+0+0=1,\\
5A,5B:&\quad1+\varphi+\varphi'=2.
\end{aligned}
$$

完全一致。∎

---

# 第六十二部　这是 level-5 Ramanujan 图表的精确有限骨架

经典同构：

$$
PSL_2(\mathbb F_5)\simeq A_5
$$

说明第二个 \(A_5^{\mathrm{mod}}\) 正是 level-5 模群的有限商。

因此现在得到了一条不再依赖表面类比的桥：

$$
\boxed{
\begin{aligned}
\text{六维黄金格}
&\longrightarrow
D_L\simeq(\mathbb F_5)^3\\
&\longrightarrow
A_5^{\mathrm{geo}}\text{ 轨道}\\
&\longrightarrow
7\text{ 状态 Fourier 空间}\\
&\longrightarrow
A_5^{\mathrm{mod}}\simeq PSL_2(\mathbb F_5)\\
&\longrightarrow
1\oplus3\oplus3'.
\end{aligned}
}
$$

所以：

* 准晶体的 \(3\oplus3'\)；
* 五次方程的 \(A_5\)；
* level-5 模函数的 \(PSL_2(\mathbb F_5)\)；
* 有限 Weil Fourier 的 \(1\oplus3\oplus3'\)；

现在处于同一条可计算链中。

---

## 62.1 与 Rogers–Ramanujan 的关系应怎样科学检验

目前已经闭合的是：

$$
\boxed{
\text{有限 level-5 表示骨架}.
}
$$

尚未闭合的是：

$$
\boxed{
\text{其具体解析 Theta 坐标是否等于
Rogers--Ramanujan／Klein 坐标}.
}
$$

正确实验程序是：

1. 对 \(D_L\) 的各 coset 构造 theta 分量；
2. 按七个 \(A_5^{\mathrm{geo}}\) 轨道求和；
3. 用投影算子提取：

   $$
   \mathbf1,\ V_3,\ V_3'
   $$

   三个模分量；
4. 计算其 \(q\)-展开；
5. 形成 projective ratios；
6. 与 Rogers–Ramanujan \(G,H,R\) 及 Klein 二十面体不变量比较；
7. 若权、level、乘子与有限个 Fourier 系数一致，再使用 Sturm 型界证明恒等。

只有完成这一步，才能正式写下：

$$
\text{六维准晶体 theta}
=
\text{Ramanujan level-5 主函数}.
$$

目前不能提前把它当作已证结论。

---

# 第六十三部　五进 ramification 是“值观察不足、jet 观察必要”的原型

在实数域中：

$$
\Phi
\sim
\begin{pmatrix}
\varphi I_3&0\\
0&\varphi'I_3
\end{pmatrix}.
$$

值观察：

$$
\varphi,\qquad\varphi'
$$

能够区分两个空间。

但模 \(5\)：

$$
\varphi\equiv\varphi'\equiv3.
$$

仅观察特征值只得到：

$$
3.
$$

必须加入：

$$
N=\overline\Phi-3I
$$

才能恢复隐藏的一阶方向。

所以：

$$
\boxed{
\text{ramification}
=
\text{共轭值观察者发生碰撞}.
}
$$

而：

$$
\boxed{
\text{nilpotent jet}
=
\text{碰撞以后保留的第一阶区分信息}.
}
$$

这可推广为：

## 定义 63.1（观察者碰撞阶）

设两个读数 \(a,b\) 在素数 \(\mathfrak p\) 下满足：

$$
a\equiv b\pmod{\mathfrak p^r},
$$

但：

$$
a\not\equiv b\pmod{\mathfrak p^{r+1}}.
$$

定义其碰撞深度：

$$
\boxed{
\operatorname{CollDepth}_{\mathfrak p}(a,b)=r.
}
$$

黄金情形中：

$$
\varphi-\varphi'=\sqrt5
$$

正由唯一分歧素数 \(5\) 控制。

---

## 63.2 对科学定义理论的意义

当两个对象在当前分辨率下同值，但其导数、jet 或变形行为不同，下一项新定义不应继续寻找另一个同类值，而应提升载体：

$$
\boxed{
\text{value}
\longrightarrow
\text{value + first jet}.
}
$$

这与：

* 重根分析；
* 代数几何切空间；
* p-adic Cartier jet；
* Yu Deng 的历史保持提升；
* 王虹的多尺度 refinement；

共享同一个定义原则：

$$
\boxed{
\text{当对象在零阶观察中合并，
以最小高阶信息恢复其分歧方向。}
}
$$

---

# 第六十四部　新的 RH 观察接口

此前定义：

$$
q_{p,m,t}
$$

作为 Prime–Regulator–Time Observer。

现在需要再加入有限二十面体通道：

$$
\boxed{
q_{p,m,t,\alpha},
}
$$

其中：

$$
\alpha\in
\{
0,I_+,I_-,F_2,F_3,E_1,E_4
\}.
$$

四个索引分别读取：

$$
\begin{aligned}
p&:\text{素数局部因子};\\
m&:\text{单位流 Fourier／Hecke 模式};\\
t&:\text{Mellin 高度或时间};\\
\alpha&:\text{五进二十面体边界类型}.
\end{aligned}
$$

更粗的观察可只保留：

$$
\alpha_{\mathrm{coarse}}
\in
\{0,I,F,E\}.
$$

完整观察还必须保留三个 chiral residual：

$$
I_a,\qquad F_a,\qquad E_a.
$$

---

## 64.1 新的 non-sticky 定义

一个潜在负 Weil 模式若在：

* 多个素数 \(p\)；
* 多个调节子模式 \(m\)；
* 多个高度窗口 \(t\)；
* 多个二十面体类型 \(\alpha\)；

间分散，称为四轴 non-sticky。

可以期待：

$$
\text{prime orthogonality}
+
\text{regulator Fourier orthogonality}
+
\text{height separation}
+
\text{finite Weil orthogonality}
$$

共同产生严格增益。

---

## 64.2 新的 sticky 定义

若负质量沿嵌套链：

$$
(p_j,m_j,t_j,\alpha_j)
$$

持续集中，则定义为 Icosahedral sticky history。

此时：

* \(p\)-方向用 Euler/Hecke primitive decomposition；
* \(m\)-方向用调节子 Fourier 分解；
* \(t\)-方向用 Mellin/Riemann 积分；
* \(\alpha\)-方向用七状态有限 Fourier 矩阵；

进行 Yu Deng 式 history contraction。

七状态矩阵满足：

$$
M^2=125I,
$$

所以 \(\alpha\)-方向不是不可控组合爆炸，而是一个精确闭合的有限状态系统。

---

# 第六十五部　本轮最重要的新定理链

本轮得到的最强闭环是：

$$
\boxed{
\begin{aligned}
\Lambda^2A_4
&\xrightarrow{\bmod5}
\overline L_6
\\
&\xrightarrow{\overline J}
R_3
\\
&\cong
D_L=(\mathbb Z/5)^3
\\
&\xrightarrow{\mathbb P}
6+10+15
\\
&=
\text{二十面体的五重、三重、二重轴}
\\
&\xrightarrow{\text{finite Fourier}}
7\text{ 状态}
\\
&\xrightarrow{PSL_2(\mathbb F_5)}
1\oplus3\oplus3'.
\end{aligned}
}
$$

即：

$$
\boxed{
\text{实数域中的 }3\oplus3'
\text{ 分裂，}
}
$$

在 \(p=5\) 处先退化为：

$$
\boxed{
0\to3\to6\to3\to0,
}
$$

再由有限 Fourier／level-5 模作用重新恢复：

$$
\boxed{
1\oplus3\oplus3'.
}
$$

这可以称为：

$$
\boxed{
\textbf{Golden Ramified Fourier Recompletion}
}
$$

中文：

# 黄金分歧—Fourier 再完备化原理

---

# 第六十六部　结论分级

## 本轮精确有限计算得到

$$
\boxed{
\operatorname{SNF}(G)
=
(1,1,1,5,5,5).
}
$$

$$
\boxed{
D_L\simeq(\mathbb Z/5)^3.
}
$$

$$
\boxed{
\overline J^2=0,
\qquad
\operatorname{im}\overline J
=
\ker\overline J
=
\operatorname{rad}(\overline G).
}
$$

$$
\boxed{
0\to R_3\to\overline L_6\to R_3\to0.
}
$$

$$
\boxed{
\mathbb P(R_3)
=
6+10+15.
}
$$

$$
\boxed{
\mathbb C[R_3]^{A_5}
\text{ 为七维}.
}
$$

$$
\boxed{
M^2=125I_7.
}
$$

$$
\boxed{
M
\simeq
M_{\mathrm{coarse}}
\oplus
\operatorname{diag}
(-5\sqrt5,5\sqrt5,5\sqrt5).
}
$$

$$
\boxed{
\langle S,T\rangle\simeq A_5,
\qquad
\mathbb C^7\simeq1\oplus3\oplus3'.
}
$$

这些结果尚未进入仓库 Lean 真源，但都属于有限矩阵和有限集合计算，形式化风险较低。

---

## 已有外部理论支持

判别式模的 Weil 表示能够分解为局部 \(p\)-部分，并由有限 Fourier 与二次相位给出 metaplectic 作用。([arXiv][3])

二十面体的 \(31\) 个射影方向按相反顶点、相反面和相反边分为 \(6,10,15\)。([科学直通车][2])

---

## 仍属开放桥梁

$$
\boxed{
\begin{aligned}
&\text{七状态 Theta 向量是否直接产生 Rogers--Ramanujan 函数};\\
&\text{其 }3,3'\text{ 投影是否等同于标准 Klein level-5 坐标};\\
&\text{四轴观察族是否足以分离所有 off-line ζ 零点};\\
&\text{finite Weil chiral residual 是否提供严格 Weil 正性增益}.
\end{aligned}
}
$$

---

# 第六十七部　建议形式化顺序

```text
D5/S3/Geometry/GoldenCompletion/
  ExteriorA4SmithNormalForm.lean
  RamifiedHodgeNilpotent.lean
  DiscriminantRadicalBridge.lean
  GoldenRamifiedJet.lean

D5/S3/Factorization/IcosahedralModFive/
  FaithfulThreeDimensionalRepresentation.lean
  InvariantQuadraticForm.lean
  VectorOrbitClassification.lean
  ProjectiveAxisClassification.lean
  PrimePowerBlindLinearFaithfulContrast.lean

D5/S3/Analytic/FiniteWeilFive/
  FiniteFourierTransform.lean
  SevenOrbitFourierMatrix.lean
  CoarseChiralDecomposition.lean
  ModularAlternatingFiveRelations.lean
  OnePlusThreePlusThree.lean

D5/S3/Analytic/RamanujanGenome/LevelFive/
  IcosahedralThetaSevenState.lean
  ThreeDimensionalThetaProjection.lean
  RogersRamanujanComparison.lean

D5/S3/Observer/ArithmeticTomography/
  RamifiedConjugateJet.lean
  IcosahedralBoundaryObserver.lean
  PrimeRegulatorTimeIcosahedralObserver.lean
```

---

# 本轮最终结论

此前我们得到：

$$
\boxed{
\text{六维准晶体是两个黄金共轭三维观察的整数完成。}
}
$$

现在可以进一步加强为：

$$
\boxed{
\text{在分歧素数 }5\text{ 上，
这两个三维观察者并不会简单消失，}
}
$$

而是：

$$
\boxed{
\text{碰撞成一个三维模及其一阶 nilpotent 自扩张。}
}
$$

这个三维模的射影方向精确编码：

$$
\boxed{
6\text{ 条五重轴}
+
10\text{ 条三重轴}
+
15\text{ 条二重轴}.
}
$$

而对它进行有限 Fourier 完成，又得到：

$$
\boxed{
1\oplus3\oplus3',
}
$$

即 level-5 模群中的黄金共轭三维表示。

最凝练的结论是：

$$
\boxed{
\text{黄金二十面体结构在实无穷位以“共轭分裂”存在，}
\newline
\text{在素数 }5\text{ 处以“ramified jet”存在，}
\newline
\text{在模函数世界中以“finite Fourier }1+3+3'\text{”重新出现。}
}
$$

这给出了目前 OACTC 中最完整的一次：

$$
\boxed{
\text{常数}
\to
\text{数域}
\to
\text{格}
\to
\text{局部退化}
\to
\text{观察者补全}
\to
\text{模函数基因组}
}
$$

的闭环。

[1]: https://doi.org/10.1112/jlms/s2-44.2.270 "https://doi.org/10.1112/jlms/s2-44.2.270"
[2]: https://www.sciencedirect.com/science/article/abs/pii/S0022404923002451 "https://www.sciencedirect.com/science/article/abs/pii/S0022404923002451"
[3]: https://arxiv.org/abs/1208.2570 "https://arxiv.org/abs/1208.2570"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.4：五进边界提升、二十面体壳层基因组与 Ramanujan–Theta 再完备化

以下从前文**第六十七部之后**继续追加。

本轮得到的核心闭环是：

$$
\boxed{
\begin{aligned}
\Lambda^2A_4
&\xrightarrow{\text{energy shells}}
20\oplus30\oplus(12\oplus12)\oplus\cdots\\
&\xrightarrow{\bmod 5}
(\mathbb F_5)^3\\
&\xrightarrow{\text{isotropic conic}}
X(5)\text{ 的十二个 cusp states}\\
&\xrightarrow{\text{even/odd orientation}}
(1\oplus5)\oplus(3\oplus3')\\
&\xrightarrow{\text{finite Weil}}
\text{level-5 }A_5\text{ modular packet}\\
&\xrightarrow{\text{Theta--Mellin}}
\text{六维矢量值完成对象}.
\end{aligned}}
$$

更重要的是，数字 \(6\) 现在获得一个新的严格解释：

$$
\boxed{
6
=
5\text{ 个普通模 }5\text{ 能量余数通道}
+
1\text{ 个分歧零类的 jet 残余通道}.
}
$$

这不是 \(5+1\) 的数值联想，而是由五进边界二次型、分歧零类与外部 \(S_5/A_5\) 对称共同强迫出来的六状态完成。

---

# 第六十八部　六维能量到三维五进边界的精确映射

沿用前文六维格：

$$
L=\Lambda^2A_4,
$$

以及 Gram 矩阵：

$$
G=
\begin{pmatrix}
3&1&1&-1&-1&0\\
1&3&1&1&0&-1\\
1&1&3&0&1&1\\
-1&1&0&3&1&-1\\
-1&0&1&1&3&1\\
0&-1&1&-1&1&3
\end{pmatrix}.
$$

定义五进边界映射：

$$
\boxed{
\rho_5:L\longrightarrow R:=\mathbb F_5^3
}
$$

其矩阵为：

$$
\boxed{
R_5=
\begin{pmatrix}
1&0&4&0&1&0\\
0&1&4&0&0&1\\
0&0&0&1&4&1
\end{pmatrix}
\pmod5.
}
\tag{68.1}
$$

在 \(R\) 上定义对称矩阵：

$$
\boxed{
H=
\begin{pmatrix}
1&2&3\\
2&1&2\\
3&2&1
\end{pmatrix}
}
\tag{68.2}
$$

以及非退化二次型：

$$
q_R(v)=v^THv.
$$

直接矩阵乘法给出：

$$
\boxed{
R_5^THR_5\equiv2G\pmod5.
}
\tag{68.3}
$$

---

## 定理 68.1（能量—边界选择律）

对任意 \(x\in L\)：

$$
\boxed{
q_R(\rho_5(x))
\equiv
2\,\langle x,x\rangle
\pmod5.
}
\tag{68.4}
$$

### 证明

$$
\begin{aligned}
q_R(\rho_5(x))
&=
x^TR_5^THR_5x\\
&\equiv
2x^TGx
\pmod5.
\end{aligned}
$$

∎

这条恒等式说明：

> 六维格点的实能量，不仅在 \(\mathbb R\) 中定义一个壳层；其模 \(5\) 剩余还精确决定了该格点进入哪一种有限二十面体边界类型。

项目已经机器核验了黄金整数环中：

* \(p\equiv\pm1\pmod5\) 分裂；
* \(p\equiv\pm2\pmod5\) 惰性；
* \(5\) 自身分歧。

因此这里的模 \(5\) 边界并不是任意选取的有限模型，而是黄金数域唯一有限分歧位置的几何化。

---

# 第六十九部　有限二十面体空间是二元二次型空间

定义矩阵：

$$
T=
\begin{pmatrix}
1&0&2\\
1&1&1\\
2&4&3
\end{pmatrix}
\in GL_3(\mathbb F_5).
$$

再定义：

$$
H_\Delta=
\begin{pmatrix}
0&0&2\\
0&1&0\\
2&0&0
\end{pmatrix}.
$$

直接计算：

$$
\boxed{
T^THT=3H_\Delta.
}
\tag{69.1}
$$

若把向量写为：

$$
(a,b,c)\in\mathbb F_5^3,
$$

则：

$$
(a,b,c)^TH_\Delta(a,b,c)
=
b^2-ac.
$$

所以：

$$
\boxed{
q_R(T(a,b,c))
=
3(b^2-ac).
}
\tag{69.2}
$$

---

## 69.1 对称平方解释

令：

$$
U=\mathbb F_5^2.
$$

把三维空间识别为：

$$
\operatorname{Sym}^2U
=
\left\{
au^2+2buv+cv^2
\right\}.
$$

那么：

$$
b^2-ac
$$

正是二元二次型的判别式。

因此：

$$
\boxed{
R
\simeq
\operatorname{Sym}^2(\mathbb F_5^2),
}
\tag{69.3}
$$

而 \(A_5\simeq PSL_2(\mathbb F_5)\) 的三维表示就是二元二次型的对称平方／伴随表示。

---

## 69.2 Isotropic conic

非零 isotropic 条件为：

$$
b^2=ac.
$$

它具有 Veronese 参数化：

$$
\boxed{
[u:v]
\longmapsto
[u^2:uv:v^2].
}
\tag{69.4}
$$

所以射影 isotropic conic 满足：

$$
\boxed{
\mathcal C_5
\simeq
\mathbb P^1(\mathbb F_5).
}
$$

并且：

$$
|\mathcal C_5|=5+1=6.
$$

这六个点就是前文二十面体的六条五重旋转轴。

---

# 第七十部　十二 cusp states 与二十面体顶点

考虑：

$$
\boxed{
\widetilde{\mathcal C}_5
=
\left(
\mathbb F_5^2\setminus\{0\}
\right)/\{\pm1\}.
}
\tag{70.1}
$$

其大小为：

$$
\frac{25-1}{2}=12.
$$

定义：

$$
\nu:
\widetilde{\mathcal C}_5
\longrightarrow R,
$$

$$
\boxed{
\nu([u,v]_{\pm})
=
T(u^2,uv,v^2).
}
\tag{70.2}
$$

因为 \((-u,-v)\) 具有同一平方像，该映射良定义。

其像恰好是两个非零 isotropic \(12\)-轨道之一，记为：

$$
I_+.
$$

另一个轨道为某个非平方数倍：

$$
I_-=\lambda I_+,
\qquad
\left(\frac{\lambda}{5}\right)=-1.
$$

---

## 定理 70.1（十二 cusp—vertex 识别）

$$
\boxed{
\widetilde{\mathcal C}_5
\simeq I_+
}
$$

作为 \(PSL_2(\mathbb F_5)\simeq A_5\)-集合成立。

另一方面，主同余子群 \(\Gamma(5)\) 的 cusp 等价正由 primitive pairs 模 \(5\) 的 \(\pm\)-等价给出；因此 \(X(5)\) 有十二个 cusps，并可置于二十面体十二个顶点上。([SageMath 文档][1])

所以：

$$
\boxed{
\text{六维格的一个非零 isotropic 边界轨道}
=
\text{level-5 模曲线的 cusp 集}
=
\text{二十面体十二个顶点}.
}
$$

这已经把：

* 五次方程的 \(A_5\)；
* 六维准晶体；
* level-5 模曲线；
* Ramanujan level-5 函数；

放到了**同一个十二状态集合**上。

---

# 第七十一部　六维晶体表示是十二顶点的奇函数空间

令：

$$
\mathcal V_{12}=I_+.
$$

考虑函数空间：

$$
\mathbb C[\mathcal V_{12}].
$$

其置换特征标在 \(A_5\) 五个共轭类

$$
1A,\ 2A,\ 3A,\ 5A,\ 5B
$$

上为：

$$
\boxed{
\chi_{12}
=
(12,0,0,2,2).
}
\tag{71.1}
$$

与 \(A_5\) 特征标表比较：

$$
\boxed{
\mathbb C[\mathcal V_{12}]
\simeq
\mathbf1\oplus V_3\oplus V_3'\oplus V_5.
}
\tag{71.2}
$$

---

## 71.1 Antipodal involution

定义：

$$
\iota(v)=-v.
$$

它把十二个顶点配成六对。

定义偶函数空间：

$$
\mathbb C[\mathcal V_{12}]^+
=
\{f:f(-v)=f(v)\},
$$

以及奇函数空间：

$$
\mathbb C[\mathcal V_{12}]^-
=
\{f:f(-v)=-f(v)\}.
$$

二者维数均为 \(6\)。

直接计算其特征标：

$$
\chi_+
=
(6,2,0,1,1),
$$

$$
\chi_-
=
(6,-2,0,1,1).
$$

所以：

$$
\boxed{
\mathbb C[\mathcal V_{12}]^+
\simeq
\mathbf1\oplus V_5,
}
\tag{71.3}
$$

而：

$$
\boxed{
\mathbb C[\mathcal V_{12}]^-
\simeq
V_3\oplus V_3'.
}
\tag{71.4}
$$

---

## 71.2 观察者意义

偶函数只知道：

$$
\{v,-v\},
$$

即只知道六条无向五重轴。

奇函数还知道：

$$
v\quad\text{还是}\quad -v,
$$

即保留轴的方向／符号。

因此：

$$
\boxed{
V_3\oplus V_3'
=
\text{二十面体十二顶点上的方向敏感六维观察空间}.
}
$$

而：

$$
\boxed{
\mathbf1\oplus V_5
=
\text{遗忘方向后的六轴粗观察空间}.
}
$$

这精确解释了为什么：

* 六点普通置换表示是 \(1\oplus5\)；
* 六维 crystallographic 表示却是 \(3\oplus3'\)。

它们的差别不是维数，而是：

$$
\boxed{
\text{是否保留 antipodal orientation}.
}
$$

---

# 第七十二部　最短三个能量壳自动重建二十面体

定义：

$$
S_n
=
\{x\in L:\langle x,x\rangle=n\}.
$$

对 \(n\le15\) 做完整整数枚举。

由于 \(G\) 的最小特征值为 \(1\)，若：

$$
\langle x,x\rangle\le15,
$$

则：

$$
\|x\|_2^2\le15.
$$

所以只需枚举：

$$
x_i\in\{-3,-2,-1,0,1,2,3\},
$$

即可保证穷尽全部格点。

得到：

$$
\begin{array}{c|rrrrrrrrrrrrr}
n&0&3&4&5&6&7&8&9&10&11&12&13&14&15\\
\hline
|S_n|
&1&20&30&24&60&60&60&120&144&240&200&120&300&380
\end{array}
\tag{72.1}
$$

其中不存在范数 \(1\) 或 \(2\) 的非零向量。

---

## 72.1 前三壳的轨道分解

$$
\boxed{
S_3
\text{ 是一个大小 }20\text{ 的 }A_5\text{ 轨道}.
}
$$

稳定子阶为：

$$
60/20=3.
$$

因此它对应二十面体的二十个面。

---

$$
\boxed{
S_4
\text{ 是一个大小 }30\text{ 的 }A_5\text{ 轨道}.
}
$$

稳定子阶为：

$$
60/30=2.
$$

因此它对应二十面体的三十条边。

---

$$
\boxed{
S_5
=
S_5^+\sqcup S_5^-,
\qquad
|S_5^\pm|=12.
}
$$

稳定子阶为：

$$
60/12=5.
$$

因此两个轨道分别是两套十二顶点／cusp states。

所以：

$$
\boxed{
\text{六维格的前三个非零能量壳}
=
20\text{ faces}
+
30\text{ edges}
+
2\times12\text{ vertices}.
}
\tag{72.2}
$$

这意味着二十面体几何不是后来投影时才出现，而是已经编码在六维格的最短向量谱中。

---

# 第七十三部　完整壳层—边界表

使用边界轨道：

$$
O_0,\ I_+,\ I_-,\ Q_1,\ Q_2,\ Q_3,\ Q_4,
$$

其中：

$$
\begin{array}{c|c|c}
\text{轨道}&q_R&\text{大小}\\
\hline
O_0&0&1\\
I_+&0&12\\
I_-&0&12\\
Q_1&1&20\\
Q_2&2&30\\
Q_3&3&30\\
Q_4&4&20
\end{array}
\tag{73.1}
$$

枚举得到：

$$
\begin{array}{c|l|l}
n& A_5\text{ 壳轨道大小}&\rho_5(S_n)\text{ 分布}\\
\hline
3&20&Q_1:20\\
4&30&Q_3:30\\
5&12+12&I_+:12,\ I_-:12\\
6&30+30&Q_2:60\\
7&60&Q_4:60\\
8&60&Q_1:60\\
9&60+60&Q_3:120\\
10&60+60+12+12&I_+:72,\ I_-:72\\
11&60+60+60+60&Q_2:240\\
12&60+60+60+20&Q_4:200\\
13&60+60&Q_1:120\\
14&60+60+60+60+30+30&Q_3:300\\
15&6\times60+20&O_0:20,\ I_+:180,\ I_-:180
\end{array}
\tag{73.2}
$$

---

## 73.1 纤维均匀性

若某个壳 \(S_n\) 映入唯一非零轨道 \(Q_j\)，则由于：

* \(S_n\) 是 \(A_5\)-稳定的；
* \(\rho_5\) 是 \(A_5\)-等变的；
* \(Q_j\) 是传递 \(A_5\)-集合；

每个 \(v\in Q_j\) 的提升数量完全相同。

例如：

$$
\begin{array}{c|c|c}
n&\text{边界轨道}&\text{每个边界状态的提升数}\\
\hline
3&Q_1&1\\
4&Q_3&1\\
6&Q_2&2\\
7&Q_4&3\\
8&Q_1&3\\
9&Q_3&4\\
11&Q_2&8\\
12&Q_4&10\\
13&Q_1&6\\
14&Q_3&10
\end{array}
\tag{73.3}
$$

这可以解释为一种有限边界上的**bulk lifting multiplicity**。

---

# 第七十四部　Ramified 5-dissection：为什么恰好出现六状态

定义七个形式 Theta 分量：

$$
\boxed{
\Theta_\alpha(X)
=
\sum_{\substack{x\in L\\\rho_5(x)\in O_\alpha}}
X^{\langle x,x\rangle}.
}
\tag{74.1}
$$

由能量—边界选择律：

$$
q_R(\rho_5(x))
\equiv2\langle x,x\rangle\pmod5,
$$

所以每个非零边界轨道只允许一个固定的模 \(5\) 能量余数：

$$
\begin{array}{c|c}
\text{轨道}&n\bmod5\\
\hline
O_0,I_+,I_-&0\\
Q_2&1\\
Q_4&2\\
Q_1&3\\
Q_3&4
\end{array}
\tag{74.2}
$$

因此：

$$
\Theta_{Q_2}(X)=X\,F_1(X^5),
$$

$$
\Theta_{Q_4}(X)=X^2F_2(X^5),
$$

$$
\Theta_{Q_1}(X)=X^3F_3(X^5),
$$

$$
\Theta_{Q_3}(X)=X^4F_4(X^5).
$$

而：

$$
\Theta_{O_0},\Theta_{I_+},\Theta_{I_-}
$$

都只含 \(X^{5n}\)。

---

## 74.1 奇置换交换两个 isotropic 通道

任取一个奇置换：

$$
c\in S_5\setminus A_5.
$$

其在 \(L\) 上的作用满足：

$$
c^TGc=G,
$$

以及：

$$
\boxed{
cJ=-Jc.
}
\tag{74.3}
$$

在五进边界上，它交换：

$$
I_+\longleftrightarrow I_-,
$$

而保持其他四个非零范数轨道。

因此：

$$
\boxed{
\Theta_{I_+}(X)
=
\Theta_{I_-}(X)
}
\tag{74.4}
$$

对全部阶数成立，而不仅是有限枚举中的偶然相等。

记：

$$
\Theta_I=\Theta_{I_+}=\Theta_{I_-}.
$$

于是原七状态 Theta packet 实际只含六个独立函数：

$$
\boxed{
\Theta_{O_0},
\Theta_I,
\Theta_{Q_2},
\Theta_{Q_4},
\Theta_{Q_1},
\Theta_{Q_3}.
}
\tag{74.5}
$$

---

## 定理 74.1（六状态 Ramified 5-dissection）

$$
\boxed{
6
=
5\text{ 个普通能量余数}
+
1\text{ 个零余数中的 ramification residual}.
}
\tag{74.6}
$$

普通五分拆只记录：

$$
n\bmod5.
$$

但当：

$$
n\equiv0\pmod5
$$

时，边界仍需区分：

$$
\rho_5(x)=0
$$

与：

$$
\rho_5(x)\neq0,\qquad q_R(\rho_5(x))=0.
$$

也就是：

$$
\boxed{
\text{零状态}
\quad\text{与}\quad
\text{非零 nilpotent/isotropic 状态}.
}
$$

这额外的一个通道，就是分歧素数 \(5\) 在普通余数观察之外留下的一阶 jet 信息。

---

## 74.2 与 Ramanujan 五分拆的联系

Ramanujan level-5 恒等式中，五分拆不是形式装饰，而是把 \(q\)-级数按模 \(5\) 的频率通道重新组织；现代工作仍通过 theta 函数的 \(5\)-dissection 推导 Rogers–Ramanujan 模方程。([arXiv][2])

本结构进一步说明：

$$
\boxed{
\text{几何五分拆在分歧零类中必须多出一个完成通道。}
}
$$

这正是“五阶结构为何产生六维完备载体”的一个严格答案。

---

# 第七十五部　六状态 Theta packet 的首项

由表 (73.2)：

$$
\boxed{
\Theta_{O_0}(X)
=
1+20X^{15}+O(X^{20}).
}
$$

$$
\boxed{
\Theta_I(X)
=
12X^5+72X^{10}+180X^{15}+O(X^{20}).
}
$$

$$
\boxed{
\Theta_{Q_1}(X)
=
20X^3+60X^8+120X^{13}+O(X^{18}).
}
$$

$$
\boxed{
\Theta_{Q_2}(X)
=
60X^6+240X^{11}+O(X^{16}).
}
$$

$$
\boxed{
\Theta_{Q_3}(X)
=
30X^4+120X^9+300X^{14}+O(X^{19}).
}
$$

$$
\boxed{
\Theta_{Q_4}(X)
=
60X^7+200X^{12}+O(X^{17}).
}
$$

总 Theta 为：

$$
\Theta_L(X)
=
\Theta_{O_0}
+
2\Theta_I
+
\sum_{j=1}^4\Theta_{Q_j}.
$$

所以：

$$
\boxed{
\begin{aligned}
\Theta_L(X)
={}&
1+20X^3+30X^4+24X^5+60X^6+60X^7\\
&+60X^8+120X^9+144X^{10}
+240X^{11}+200X^{12}\\
&+120X^{13}+300X^{14}+380X^{15}
+\cdots.
\end{aligned}}
\tag{75.1}
$$

---

## 75.1 边界提升能

定义边界轨道的最小提升能：

$$
\boxed{
\varepsilon(O_\alpha)
=
\min
\left\{
\langle x,x\rangle:
\rho_5(x)\in O_\alpha
\right\}.
}
$$

得到：

$$
\begin{array}{c|c}
O_\alpha&\varepsilon(O_\alpha)\\
\hline
O_0&0\quad(\text{首个非零提升为 }15)\\
Q_1&3\\
Q_3&4\\
I_\pm&5\\
Q_2&6\\
Q_4&7
\end{array}
\tag{75.2}
$$

这组数：

$$
0,3,4,5,5,6,7
$$

构成七边界状态的低能谱。

它不是任意赋权，而是边界状态在六维 bulk 中显现所需的最小能量成本。

---

# 第七十六部　局部七状态 Weil 表示与全局六状态 Theta

前文已经得到五进边界的七轨道函数空间：

$$
\mathbb C[R]^{A_5},
$$

其维数为 \(7\)。

有限 Fourier 变换与二次相位生成的 level-5 模表示满足：

$$
\boxed{
\mathbb C[R]^{A_5}
\simeq
\mathbf1\oplus V_3\oplus V_3'.
}
\tag{76.1}
$$

其中平凡表示正由：

$$
\boxed{
\mathbf1
=
\operatorname{span}
\left(
\mathbf1_{I_+}-\mathbf1_{I_-}
\right)
}
\tag{76.2}
$$

给出。

但六维格的奇置换对称强迫：

$$
\Theta_{I_+}-\Theta_{I_-}=0.
$$

因此实际 Theta packet 没有平凡分量：

$$
\boxed{
\boldsymbol\Theta_L
\in
V_3\oplus V_3'.
}
\tag{76.3}
$$

这是目前最直接的结论：

> 六维 crystallographic 表示 \(3\oplus3'\)，不只是格点坐标空间的抽象表示；它还精确成为五进边界 Theta packet 的实际模变换状态空间。

---

# 第七十七部　黄金类差算子再次出现

令：

$$
K_{5A}
=
\sum_{g\in5A}\rho(g),
$$

$$
K_{5B}
=
\sum_{g\in5B}\rho(g).
$$

定义中心算子：

$$
\boxed{
J_{\mathrm{mod}}
=
\frac14
\left(
K_{5A}-K_{5B}
\right).
}
\tag{77.1}
$$

在 \(V_3\) 上：

$$
J_{\mathrm{mod}}
=
+\sqrt5\,I,
$$

而在 \(V_3'\) 上：

$$
J_{\mathrm{mod}}
=
-\sqrt5\,I.
$$

因此在六维 Theta 状态空间上：

$$
\boxed{
J_{\mathrm{mod}}^2=5I.
}
\tag{77.2}
$$

这与六维格上的整数 Hodge 算子：

$$
J_{\mathrm{lat}}^2=5I
$$

完全同型。

---

## 77.1 外部奇置换与 Galois 共轭

奇置换诱导 \(A_5\) 的外自同构，并交换两个五阶共轭类：

$$
5A\longleftrightarrow5B.
$$

因此：

$$
J_{\mathrm{mod}}
\longmapsto
-J_{\mathrm{mod}}.
$$

另一方面，在格上：

$$
cJ_{\mathrm{lat}}c^{-1}
=
-J_{\mathrm{lat}}.
$$

所以：

$$
\boxed{
\text{空间方向反转}
=
\text{五阶共轭类交换}
=
\sqrt5\mapsto-\sqrt5
=
V_3\leftrightarrow V_3'.
}
\tag{77.3}
$$

这把几何 chirality、Galois 共轭与模表示外自同构统一成同一个操作。

---

# 第七十八部　Rogers–Ramanujan 双态的对称平方桥

定义 Rogers–Ramanujan 两个主级数：

$$
G(q),
\qquad
H(q),
$$

以及模归一化双态：

$$
\boxed{
\mathbf R(\tau)
=
\begin{pmatrix}
q^{-1/60}G(q)\\
q^{11/60}H(q)
\end{pmatrix},
\qquad
q=e^{2\pi i\tau}.
}
\tag{78.1}
$$

其射影比值为 Rogers–Ramanujan continued fraction：

$$
r(\tau)
=
\frac{
q^{11/60}H(q)
}{
q^{-1/60}G(q)
}.
$$

\(r\) 是 level-5 模函数坐标，其模变换的射影像为二十面体 \(A_5\)；Duke 的工作系统阐明了 continued fractions、模函数和二十面体之间的关系。([MaRDI Portal][3])

---

## 78.1 二维到三维

令 \(U_{\mathrm{RR}}\) 是 \(\mathbf R\) 所承载的二维线性提升。

其射影像为：

$$
A_5,
$$

线性像则是二元二十面体扩张。

对称平方：

$$
\operatorname{Sym}^2U_{\mathrm{RR}}
$$

维数为 \(3\)，中心 \(-I\) 在对称平方上作用平凡，因此它下降为 \(A_5\) 的三维表示：

$$
\boxed{
\operatorname{Sym}^2U_{\mathrm{RR}}
\simeq
V_3.
}
\tag{78.2}
$$

对系数域作黄金 Galois 共轭：

$$
\sqrt5\mapsto-\sqrt5,
$$

得到：

$$
\boxed{
\operatorname{Sym}^2U_{\mathrm{RR}}^\sigma
\simeq
V_3'.
}
\tag{78.3}
$$

因此在表示层上：

$$
\boxed{
V_3\oplus V_3'
\simeq
\operatorname{Sym}^2U_{\mathrm{RR}}
\oplus
\operatorname{Sym}^2U_{\mathrm{RR}}^\sigma.
}
\tag{78.4}
$$

这解释：

* Rogers–Ramanujan 主对象为什么是二维双态；
* 二十面体物理表示为什么是三维；
* Galois 完成后为什么得到六维准晶体表示。

完整维数链为：

$$
\boxed{
2
\xrightarrow{\operatorname{Sym}^2}
3
\xrightarrow{\text{Galois completion}}
3+3=6.
}
\tag{78.5}
$$

---

# 第七十九部　Ramanujan–Theta 因子化猜想

现在有两个承载同一有限表示的对象：

$$
\boldsymbol\Theta_L
\in
V_3\oplus V_3',
$$

以及：

$$
\mathcal Q_{\mathrm{RR}}
=
\operatorname{Sym}^2\mathbf R
\oplus
\operatorname{Sym}^2\mathbf R^\sigma.
$$

但二者的解析权和二进规范不同：

* \(\mathcal Q_{\mathrm{RR}}\) 本质上是 weight \(0\) 的模函数双态的对称平方；
* 六维格 Theta 具有 weight \(3\)；
* 五进边界只提供 level \(5\) 部分；
* 格的奇偶性还引入一个 \(2\)-primary 完成。

因此正确的候选不是：

$$
\boldsymbol\Theta_L
=
\mathcal Q_{\mathrm{RR}},
$$

而是：

$$
\boxed{
P_3\boldsymbol\Theta_L
=
F_+(\tau)\,
\operatorname{Sym}^2\mathbf R(\tau),
}
\tag{79.1}
$$

$$
\boxed{
P_{3'}\boldsymbol\Theta_L
=
F_-(\tau)\,
\operatorname{Sym}^2\mathbf R^\sigma(\tau),
}
\tag{79.2}
$$

其中：

* \(P_3,P_{3'}\) 是 \(J_{\mathrm{mod}}\) 的谱投影；
* \(F_\pm\) 是待识别的 weight-\(3\) 标量模形式或小维标量模形式组合。

外部 Galois/奇置换对称预期强迫：

$$
F_-=\sigma(F_+).
$$

---

## 79.1 为什么需要 order \(10\)

对偶化格取 Gram：

$$
A=2G.
$$

其最小模 level 为：

$$
\boxed{
N=20.
}
$$

因为：

$$
20A^{-1}
$$

为偶整数矩阵，而更小正整数不满足这一条件。

所以全局 Theta 的模结构不是纯 level \(5\)，而是：

$$
\boxed{
20=4\times5.
}
$$

其中：

* \(5\)：黄金判别式、二十面体与分歧边界；
* \(4\)：奇格偶化与二进 Fourier 规范。

因此 Ramanujan 图表更可能需要同时使用：

$$
r(\tau)
\quad\text{和}\quad
r(2\tau),
$$

而不只是 \(r(\tau)\)。

已有研究证明了：

$$
k(\tau)=r(\tau)r(2\tau)^2
$$

在 \(\Gamma_1(10)\) 上的模性；更多 \(r(\tau)^ar(2\tau)^b\) 的组合也形成 level-\(10\) 模函数，而 Ramanujan 的 order-\(10\) continued fractions 已被证明是 level-\(10\) 模函数。([数字对象标识符][4])

所以 OACTC 的预测是：

$$
\boxed{
\text{六维黄金 Theta 的 Ramanujan 坐标，
应属于 level }5\text{ 与 level }10\text{ 的联合函数域}.
}
\tag{79.3}
$$

---

# 第八十部　标量 Theta 的 level-20 模影

对偶化格：

$$
L^{\mathrm{ev}}
=
(\mathbb Z^6,2G)
$$

是偶正定格。

其：

$$
\det(2G)=2^6\cdot5^3=8000.
$$

标准 Theta 理论给出：

$$
\boxed{
\Theta_L(\tau)
=
\sum_{x\in\mathbb Z^6}
q^{x^TGx}
\in
M_3\bigl(\Gamma_0(20),\chi_{-20}\bigr).
}
\tag{80.1}
$$

这里 weight 为：

$$
6/2=3.
$$

而字符中的负号来自：

$$
(-1)^{3}.
$$

所以：

$$
\boxed{
\text{实黄金判别式 }+5
\quad
\xrightarrow{\text{weight-3 Fourier completion}}
\quad
\text{虚判别式 }-20.
}
\tag{80.2}
$$

矢量值格 Theta 与判别式模的 Weil 表示之间的关系，以及它们同标量模形式空间之间的转换，是标准的矢量值模形式理论。([arXiv][5])

---

## 80.1 一个必须比较的 CM 模形式

LMFDB 中存在一个：

* level \(20\)；
* weight \(3\)；
* character \(20.d\)；
* 系数域 \(\mathbb Q\)；
* CM 判别式 \(-20\)；

的新形式，其展开开始为：

$$
\begin{aligned}
f_{20}(q)
={}&
q+2q^2-4q^3+4q^4-5q^5-8q^6\\
&+4q^7+8q^8+7q^9-10q^{10}+\cdots.
\end{aligned}
$$

([LMFDB][6])

当前不能直接声称：

$$
\Theta_L=f_{20}
$$

或其简单倍数，因为 \(\Theta_L\) 有非零常数项，必然含 Eisenstein 部分。

但这给出一个明确、有限的计算任务：

$$
\boxed{
\Theta_L
=
E_{\mathrm{gold}}
+
a\,f_{20}
+
b\,f_{20}^{\mathrm{twist}}.
}
\tag{80.3}
$$

在 level \(20\)、weight \(3\) 下：

$$
[\mathrm{SL}_2(\mathbb Z):\Gamma_0(20)]
=
36.
$$

Sturm 界为：

$$
\frac{3}{12}\cdot36=9.
$$

因此一旦建立标准模性和候选基，只需比较到：

$$
q^9
$$

即可严格证明相等，而不是依赖长程数值拟合。

---

# 第八十一部　五分拆与模微分方程

六状态 Theta packet 的每个分量都有固定 \(T\)-特征值。

在 \(V_3\) 中，五阶元素的特征值可写为：

$$
1,\zeta_5,\zeta_5^{-1},
$$

而在 \(V_3'\) 中为：

$$
1,\zeta_5^2,\zeta_5^{-2}.
$$

所以两个三维分量分别携带指数集合：

$$
\boxed{
\left\{
0,\frac15,\frac45
\right\},
}
$$

以及：

$$
\boxed{
\left\{
0,\frac25,\frac35
\right\}.
}
\tag{81.1}
$$

这正是 Rogers–Ramanujan level-5 双态对称平方以后应出现的两组 projective exponent classes。

有限像矢量值模函数一般满足有限阶模微分方程或等价的超几何方程；矢量值模函数与 hypergeometric Riemann–Hilbert 问题的这一联系已有系统理论。([arXiv][7])

因此两个三维投影应分别满足一个三阶 MLDE：

$$
\boxed{
\mathcal D^3F
+
A\,E_4\,\mathcal DF
+
B\,E_6F
=0,
}
\tag{81.2}
$$

其中 \(A,B\) 由三组 cusp exponents 决定。

这给出一种比猜乘积恒等式更可靠的识别方式：

1. 从有限 \(A_5\) 表示求 \(T\)-exponents；
2. 构造唯一候选三阶 MLDE；
3. 将六维 Theta 投影代入；
4. 将 Rogers–Ramanujan 对称平方代入；
5. 比较初始系数；
6. 由微分方程解的唯一性证明二者仅相差标量模因子。

这可能非常接近拉马努金实际使用的“有限状态闭合”视野：

$$
\boxed{
\text{不是逐项猜无穷级数，
而是先识别有限维变换系统，
再由初始数据固定全部级数。}
}
$$

---

# 第八十二部　边界 Epstein packet

对每个边界轨道定义 partial Epstein zeta：

$$
\boxed{
E_\alpha(s)
=
\sum_{\substack{x\in L\setminus\{0\}\\
\rho_5(x)\in O_\alpha}}
\langle x,x\rangle^{-s}.
}
\tag{82.1}
$$

它是：

$$
\Theta_\alpha(t)-\delta_{\alpha,O_0}
$$

的 Mellin 变换。

把六个独立分量组成：

$$
\boxed{
\mathbf E_L(s)
=
\left(
E_{O_0},
E_I,
E_{Q_2},
E_{Q_4},
E_{Q_1},
E_{Q_3}
\right)^T.
}
\tag{82.2}
$$

有限 Fourier／Poisson 完成给出一个耦合函数方程：

$$
\boxed{
\widehat{\mathbf E}_L(s)
=
\mathcal S_5
\widehat{\mathbf E}_L(3-s),
}
\tag{82.3}
$$

其中 \(\mathcal S_5\) 是五进有限 Weil \(S\)-矩阵与二进完成因子的组合。

投影到两个黄金三维分量：

$$
\mathbf E_3=P_3\mathbf E_L,
$$

$$
\mathbf E_{3'}=P_{3'}\mathbf E_L,
$$

得到：

$$
\boxed{
\mathbf E_3
\quad\text{与}\quad
\mathbf E_{3'}
}
$$

两个 Galois 共轭的 completed zeta triplets。

这给出了新的“主函数家族”定义：

$$
\boxed{
\textbf{Icosahedral Epstein Genome}
=
\text{六维格点 zeta 按五进二十面体边界分解后的两个三维谱包}.
}
$$

---

# 第八十三部　对观察者理论的新补充

## 83.1 Boundary lift energy

定义：

$$
\varepsilon(\alpha)
=
\min\{Q(x):\rho_5(x)\in O_\alpha\}.
$$

它测量一个局部边界状态首次能在全局格中显现所需的能量。

因此观察者不只应记录：

$$
q(x),
$$

还应记录：

$$
\boxed{
\text{一个观察值的最小全局实现成本}.
}
$$

---

## 83.2 Ramification residual

普通余数观察：

$$
Q(x)\bmod5
$$

不能区分：

$$
\rho_5(x)=0
$$

与：

$$
q_R(\rho_5(x))=0,\quad \rho_5(x)\neq0.
$$

因此需要加入：

$$
\boxed{
\operatorname{RamRes}_5(x)
=
\mathbf1_{\rho_5(x)\neq0}.
}
$$

这正是 DECT 中一个最小新定义：

$$
\text{它只切开普通模 }5\text{ 观察的零纤维，}
$$

但不增加其他余数类的冗余信息。

---

## 83.3 Orientation completion

无向六轴观察提供：

$$
1\oplus5.
$$

方向敏感观察提供：

$$
3\oplus3'.
$$

所以观察者完备化可能不是“增加更多坐标”，而是：

$$
\boxed{
\text{把一个无向 quotient 提升为带符号 cover}.
}
$$

---

# 第八十四部　与 Wang–Deng–RH 路线的重新连接

现在 Prime–Regulator–Time Observer 应升级为：

$$
\boxed{
q_{p,m,t,\alpha}.
}
$$

其中：

* \(p\)：素数／素理想通道；
* \(m\)：调节子 Fourier／Hecke 模式；
* \(t\)：Mellin 高度或演化时间；
* \(\alpha\)：五进二十面体边界状态。

---

## 84.1 Non-sticky 分支

如果潜在负 Weil 模式分散于多个：

$$
(p,m,t,\alpha)
$$

通道，则可以同时利用：

* prime-channel 正交；
* regulator Fourier 正交；
* height separation；
* 有限 \(A_5\) 表示正交。

争取建立：

$$
\boxed{
\text{non-sticky}
\Longrightarrow
\text{strict positivity gain}.
}
$$

---

## 84.2 Sticky 分支

若负模式沿一条嵌套通道链集中，则：

* \(p\)-方向由 Euler/Hecke primitive 分解；
* \(m\)-方向由单位流 Fourier 分解；
* \(t\)-方向由 Mellin/Riemann 积分；
* \(\alpha\)-方向由六状态有限 Weil 系统；

进行 Yu Deng 式历史压缩。

这里 \(\alpha\)-方向的复杂度是严格有限的：

$$
\dim=6,
$$

不会随展开阶数产生新的状态类型。

---

## 84.3 尚缺失的中心桥

即使上述结构全部闭合，仍需证明：

$$
\boxed{
\rho\text{ 为 off-line ζ zero}
\Longrightarrow
\exists(p,m,t,\alpha)
\text{ 产生不可消除的负 Weil witness}.
}
\tag{84.1}
$$

在这条充分性定理建立之前，本理论提供的是：

* 一个更精细的观察坐标；
* 一个可计算的多尺度状态空间；
* 一个有限 primitive-history 载体；
* 一个 Ramanujan level-5 模图表候选；

而不是 RH 证明。

---

# 第八十五部　本轮结论分级

## 已由整数矩阵与有限枚举精确推出

$$
\boxed{
R_5^THR_5\equiv2G\pmod5.
}
$$

$$
\boxed{
q_R(\rho_5(x))
\equiv2Q(x)\pmod5.
}
$$

$$
\boxed{
R\simeq\operatorname{Sym}^2(\mathbb F_5^2),
\quad
q_R\simeq3(b^2-ac).
}
$$

$$
\boxed{
I_+
\simeq
(\mathbb F_5^2\setminus0)/\{\pm1\}.
}
$$

$$
\boxed{
\mathbb C[I_+]^+
\simeq1\oplus5,
\qquad
\mathbb C[I_+]^-
\simeq3\oplus3'.
}
$$

$$
\boxed{
S_3=20,\quad
S_4=30,\quad
S_5=12+12.
}
$$

$$
\boxed{
\Theta_{I_+}=\Theta_{I_-}.
}
$$

$$
\boxed{
\text{实际五进 Theta packet 属于 }3\oplus3'.
}
$$

$$
\boxed{
6
=
5\text{ residue states}
+
1\text{ ramification residual}.
}
$$

这些结果目前是纸面矩阵证明和完整有限枚举结果，尚未进入 Lean 真源。

---

## 有标准理论支撑、但需项目桥接

$$
\boxed{
\Theta_L
\in
M_3(\Gamma_0(20),\chi_{-20}).
}
$$

$$
\boxed{
\text{判别式模 Theta 向量按 Weil 表示变换}.
}
$$

$$
\boxed{
\text{Rogers--Ramanujan 双态的 projective image 为 }A_5.
}
$$

相关矢量值模形式和 Weil 表示理论已有完整基础。([arXiv][5])

---

## 当前最重要的开放桥

$$
\boxed{
P_3\boldsymbol\Theta_L
\stackrel{?}{=}
F_+\operatorname{Sym}^2\mathbf R,
}
$$

$$
\boxed{
P_{3'}\boldsymbol\Theta_L
\stackrel{?}{=}
F_-\operatorname{Sym}^2\mathbf R^\sigma.
}
$$

以及识别：

$$
F_\pm
$$

究竟是：

* Eisenstein 因子；
* level-\(20\) CM newform；
* eta product；
* 还是多个标量模形式的线性组合。

---

# 第八十六部　建议形式化顺序

```text
D5/S3/Geometry/GoldenCompletion/
  BoundaryReductionMap.lean
  BoundaryEnergyCongruence.lean
  BinaryQuadraticConicModel.lean
  IcosahedralShortShells.lean
  BoundaryLiftEnergy.lean

D5/S3/Factorization/IcosahedralModFive/
  LevelFiveCuspCover.lean
  AntipodalEvenOddDecomposition.lean
  OddVertexCrystallographicRepresentation.lean
  OuterAutomorphismGoldenConjugation.lean

D5/S3/Analytic/FiniteWeilFive/
  RamifiedFiveDissection.lean
  SixStateThetaPacket.lean
  GoldenClassDifferenceOperator.lean
  ThreePlusThreeThetaProjection.lean

D5/S3/Analytic/RamanujanGenome/LevelFive/
  RogersRamanujanDoublet.lean
  BinaryIcosahedralSymmetricSquare.lean
  RogersRamanujanThetaIntertwiner.lean
  LevelTenParityCompletion.lean

D5/S3/Analytic/GoldenCompletion/
  BoundaryEpsteinPacket.lean
  VectorFunctionalEquation.lean
  IcosahedralEpsteinGenome.lean
```

---

# 本轮最终结论

前文已经说明：

$$
\text{六维}
=
3\text{ 个黄金坐标}
\times
2\text{ 个 Galois 实嵌入}.
$$

本轮又得到另一个完全独立但一致的解释：

$$
\boxed{
\text{六维}
=
5\text{ 个模 }5\text{ 能量通道}
+
1\text{ 个分歧零类残余}.
}
$$

还得到第三个表示论解释：

$$
\boxed{
\text{六维}
=
\operatorname{Sym}^2(\text{Ramanujan 双态})
+
\operatorname{Sym}^2(\text{其黄金共轭}).
}
$$

因此三个“六”开始真正合一：

$$
\boxed{
\begin{aligned}
3\times2
&=\text{Minkowski 共轭完成};\\
5+1
&=\text{ramified 5-dissection 完成};\\
3+3'
&=\text{binary-icosahedral symmetric-square 完成}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
\text{六维黄金准晶体并非只是一个高维投影模型，}
}
$$

而是：

$$
\boxed{
\text{level-5 模系统在同时保留
Galois 共轭、cusp orientation 与分歧零类 jet 后，
所需的最小完整状态空间。}
}
$$

[1]: https://doc.sagemath.org/html/en/reference/arithgroup/sage/modular/arithgroup/congroup_gamma.html "https://doc.sagemath.org/html/en/reference/arithgroup/sage/modular/arithgroup/congroup_gamma.html"
[2]: https://arxiv.org/abs/2410.14149 "https://arxiv.org/abs/2410.14149"
[3]: https://portal.mardi4nfdi.de/wiki/Continued_fractions_and_modular_functions "https://portal.mardi4nfdi.de/wiki/Continued_fractions_and_modular_functions"
[4]: https://doi.org/10.1515%2Fmath-2020-0105 "https://doi.org/10.1515%2Fmath-2020-0105"
[5]: https://arxiv.org/abs/0704.1868 "https://arxiv.org/abs/0704.1868"
[6]: https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/20/3/d/b/ "https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/20/3/d/b/"
[7]: https://arxiv.org/abs/0705.2467 "https://arxiv.org/abs/0705.2467"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.5：Spin 完成、Icosian–\(E_8\) 母格、Ramanujan 微分流与三十阶 Coxeter 基因组

以下从前文**第八十六部之后**继续追加。

本轮将此前的六维黄金—二十面体结构继续提升一层：

$$
\boxed{
A_5
\longrightarrow
2.A_5
\longrightarrow
H_4
\longrightarrow
\text{Icosian ring}
\longrightarrow
E_8
\longrightarrow
E_4
\longrightarrow
(P,Q,R)
}
$$

其中：

* \(A_5\) 是三维旋转观察；
* \(2.A_5\) 是保留中央符号的 Spin 完成；
* \(H_4\) 是 \(120\) 个 spinor 构成的四维根系；
* icosian ring 是 \(H_4\) 在黄金整数环上的算术闭包；
* 加入黄金 Galois 共轭后得到八维整数完成；
* 该完成格正是 \(E_8\)；
* \(E_8\) 的 Theta 函数正是 Ramanujan 微分系统中的 \(E_4\)；
* \(E_8\) 的 Coxeter 谱又由同一个模 \(5\) 二次特征分解成两个黄金共轭的 \(H_4\) 扇区。

所以本轮的核心结论是：

$$
\boxed{
\text{Ramanujan 的 }E_4
\text{ 可以解释为整个黄金—二十面体—Icosian 完成对象的标量配分函数。}
}
$$

---

# 第八十七部　从旋转观察到 Spin 观察

## 87.1 三维旋转观察丢失了什么

单位四元数群满足：

$$
\operatorname{Sp}(1)\simeq SU(2).
$$

它通过共轭作用于纯虚四元数：

$$
x\longmapsto qxq^{-1},
$$

从而给出二对一映射：

$$
\boxed{
SU(2)\longrightarrow SO(3).
}
$$

其核为：

$$
\{\pm1\}.
$$

对二十面体旋转群：

$$
A_5\subset SO(3),
$$

取其原像得到阶为 \(120\) 的二元二十面体群：

$$
\boxed{
1\longrightarrow\{\pm1\}
\longrightarrow 2.A_5
\longrightarrow A_5
\longrightarrow1.
}
\tag{87.1}
$$

该群也常记为 binary icosahedral group；它由 \(120\) 个单位四元数组成，并双覆盖 \(60\) 个二十面体旋转。([arXiv][1])

---

## 87.2 中央符号是一个真实残余

若只观察：

$$
qxq^{-1},
$$

则：

$$
q
\quad\text{与}\quad
-q
$$

完全不可区分。

因此旋转观察者：

$$
q_{\mathrm{rot}}:2.A_5\to A_5
$$

具有残余：

$$
\ker q_{\mathrm{rot}}=\{\pm1\}.
$$

定义 Spin 观察：

$$
q_{\mathrm{spin}}(q)=q.
$$

则：

$$
\ker q_{\mathrm{spin}}=\{1\}.
$$

所以：

$$
\boxed{
\text{Spin 完成}
=
\text{把被射影旋转观察遗忘的中央符号重新纳入状态。}
}
$$

它与此前的几个完成结构同型：

* 无向轴 \(\to\) 有向顶点；
* Fourier 强度 \(\to\) Fourier 相位；
* 特征值 \(\to\) ramified jet；
* \(SO(3)\) 旋转 \(\to\) \(SU(2)\) spinor。

这说明“相位”并非量子理论特有概念，而是所有射影观察系统都可能产生的中心残余。

---

# 第八十八部　\(H_3\) 的 Spin 闭包产生 \(H_4\)

## 88.1 为什么从三维进入四维

三维 Euclidean Clifford 代数的偶子代数满足：

$$
\boxed{
\operatorname{Cl}^{+}(3)\simeq\mathbb H.
}
$$

它作为实向量空间维数为 \(4\)。

令 \(\Delta_{H_3}\) 是三维二十面体根系。取所有偶数个根的 Clifford 乘积，归一化后得到 \(120\) 个 spinors。

这些 spinors：

1. 在四元数乘法下闭合；
2. 构成 binary icosahedral group；
3. 作为四维向量构成 \(H_4\) 根系；
4. 同时是正 \(600\)-胞体的 \(120\) 个顶点。([arXiv][2])

因此：

$$
\boxed{
H_3
\xrightarrow{\text{even Clifford products}}
H_4.
}
\tag{88.1}
$$

---

## 88.2 \(H_4\) 不是外加对象

定义：

$$
\Delta_{H_4}:=2.A_5\subset\mathbb H.
$$

在普通四元数内积下：

$$
\|u\|_{\mathbb H}^{2}=1,
\qquad
u\in\Delta_{H_4}.
$$

所以 \(H_4\) 的 \(120\) 个根，就是三维二十面体所有旋转的 Spin 完整状态。

这给出新的 OACTC 原则：

$$
\boxed{
\textbf{Spinor State Completion Principle}
}
$$

即：

> 当一个低维对象的对称由旋转群描述时，其中央相位完成往往自然生活在高一维的 Clifford 偶代数中。

这里：

$$
3\text{D rotation}
\longrightarrow
4\text{D spinor state}.
$$

---

# 第八十九部　Icosian ring 是 \(H_4\) 的算术闭包

令：

$$
\Gamma=2.A_5=\Delta_{H_4}.
$$

定义 icosian ring：

$$
\boxed{
\mathbb I
=
\operatorname{Span}_{\mathbb Z}\Gamma
\subset
\mathbb H\otimes_{\mathbb Q}\mathbb Q(\sqrt5).
}
\tag{89.1}
$$

更精确地，\(\mathbb I\) 是秩 \(4\) 的：

$$
\mathbb Z[\varphi]
$$

模，因此作为 \(\mathbb Z\)-模具有秩：

$$
4\cdot2=8.
$$

在单个实嵌入中，\(\mathbb Z[\varphi]\) 在 \(\mathbb R\) 内稠密，所以 \(\mathbb I\) 作为普通四元数子集不是四维格；但把黄金系数拆成两个有理坐标以后，它成为八维离散格。Icosian ring 与 \(E_8\) 格之间的标准对应正是沿此路线建立的。([arXiv][1])

---

## 89.1 完成范数不是普通迹范数

对：

$$
q\in\mathbb I,
$$

其四元数约化范数属于黄金域：

$$
n(q)=q\overline q=x+\sqrt5\,y,
\qquad
x,y\in\mathbb Q.
$$

定义：

$$
\boxed{
Q_E(q)=x+y.
}
\tag{89.2}
$$

它也可以写成加权域迹：

$$
\boxed{
Q_E(q)
=
\operatorname{Tr}_{K/\mathbb Q}
\left(
\frac{5+\sqrt5}{10}\,n(q)
\right),
\qquad
K=\mathbb Q(\sqrt5).
}
\tag{89.3}
$$

因为若：

$$
\alpha=\frac{5+\sqrt5}{10},
$$

则：

$$
\operatorname{Tr}_{K/\mathbb Q}
\bigl(\alpha(x+\sqrt5 y)\bigr)=x+y.
$$

系数 \(\alpha\) 属于逆不同理想乘以一个单位；它正是把朴素迹配对修正为整数、最终成为 unimodular 配对的局部反项。

标准 icosian 定理说明：

$$
\boxed{
(\mathbb I,2Q_E)\simeq E_8
}
\tag{89.4}
$$

其中 \(2Q_E\) 使用标准 \(E_8\) 根长平方 \(2\) 的规范。([Pasayten Institute][3])

---

# 第九十部　\(240=120+120\)：完成范数合并两个 \(600\)-胞体

令：

$$
\varphi'=\frac{1-\sqrt5}{2}=-\varphi^{-1}.
$$

对任意单位 icosian：

$$
u\in\Delta_{H_4},
$$

有：

$$
n(u)=1.
$$

所以：

$$
Q_E(u)=1.
$$

另一方面：

$$
n(\varphi'u)
=
{\varphi'}^{2}
=
\frac{3-\sqrt5}{2}.
$$

将其写为：

$$
x+\sqrt5y
=
\frac32-\frac12\sqrt5,
$$

得到：

$$
Q_E(\varphi'u)
=
\frac32-\frac12
=
1.
$$

因此：

$$
\boxed{
Q_E(u)=Q_E(\varphi'u)=1.
}
\tag{90.1}
$$

在普通四元数范数中，两组点的半径分别为：

$$
1
\quad\text{与}\quad
|\varphi'|=\varphi^{-1}.
$$

但在 \(E_8\) 完成范数中，它们具有相同长度。

于是标准根分解可写为：

$$
\boxed{
\Phi_{E_8}
=
\Delta_{H_4}
\sqcup
\varphi'\Delta_{H_4}.
}
\tag{90.2}
$$

即：

$$
\boxed{
240
=
120+120.
}
$$

\(E_8\) 根系确实可分解为两个黄金缩放相关的 \(H_4\) 根系；这也是 icosian、\(H_4\) 与 \(E_8\) 之间的经典联系。([TÜBİTAK学术期刊][4])

---

## 90.1 完成范数的意义

这个例子说明：

$$
\boxed{
\text{完成化不一定保持原图表中的长度。}
}
$$

相反，它可能选择一种新的全局范数，使两个局部上不同尺度的共轭对象成为同一全局壳层。

所以：

$$
\boxed{
Q_E
=
\text{把两个黄金共轭 }H_4\text{ 壳层合并为一个整数根壳的完成观察。}
}
$$

这与此前的：

* \(\pi\)-Gaussian 自对偶；
* \(\sqrt5\)-模格对偶；
* \(\varphi/\varphi'\) 显隐双曲运输；

属于同一个 OACTC 范式。

---

# 第九十一部　Icosian \(E_8\) 的 Theta 函数就是 Ramanujan 的 \(E_4\)

定义：

$$
q=e^{2\pi i\tau},
\qquad
\Im\tau>0.
$$

定义完成格 Theta：

$$
\boxed{
\Theta_{\mathbb I}(\tau)
=
\sum_{x\in\mathbb I}
q^{Q_E(x)}.
}
\tag{91.1}
$$

因为 \((\mathbb I,2Q_E)\) 是秩 \(8\) 的 even unimodular 格，其 Theta 函数是 weight \(4\)、level \(1\) 的模形式。

而：

$$
\dim M_4(SL_2(\mathbb Z))=1.
$$

常数项为 \(1\)，所以：

$$
\boxed{
\Theta_{\mathbb I}(\tau)
=
E_4(\tau).
}
\tag{91.2}
$$

其展开为：

$$
\boxed{
\Theta_{\mathbb I}(\tau)
=
1+
240\sum_{n\ge1}\sigma_3(n)q^n.
}
\tag{91.3}
$$

因此：

$$
r_{E_8}(n)
:=
\#\{x\in\mathbb I:Q_E(x)=n\}
=
240\sigma_3(n).
$$

特别地：

$$
r_{E_8}(1)=240.
$$

\(E_8\) Theta 等于 \(E_4\)，其壳层数为 \(240\sigma_3(n)\)，是 \(E_8\) 格的标准模形式描述。([维基百科][5])

---

## 91.1 Ramanujan 主状态的几何身份

Ramanujan 常用记号中的：

$$
Q=E_4.
$$

因此：

$$
\boxed{
Q
=
\Theta_{E_8}
=
\Theta_{\mathbb I}.
}
\tag{91.4}
$$

这给此前的 Ramanujan 主函数基因组一个最具体的几何含义：

$$
\boxed{
\text{Ramanujan 的 }Q
\text{ 不是任意 Eisenstein 级数，}
}
$$

而是：

$$
\boxed{
\text{黄金二十面体 Spin 完成到 }E_8
\text{ 后的全局标量配分函数。}
}
$$

---

# 第九十二部　\(E_8\) 壳层 zeta 的两通道 Euler 分解

定义 normalized Epstein–shell zeta：

$$
\boxed{
Z_{E_8}(s)
=
\sum_{x\in\mathbb I\setminus\{0\}}
Q_E(x)^{-s}.
}
\tag{92.1}
$$

由：

$$
r_{E_8}(n)=240\sigma_3(n),
$$

得到：

$$
\boxed{
Z_{E_8}(s)
=
240
\sum_{n\ge1}
\frac{\sigma_3(n)}{n^s}
=
240\,\zeta(s)\zeta(s-3),
}
\qquad
\Re s>4.
\tag{92.2}
$$

---

## 92.1 每个素数通道有两个 primitive modes

对素数 \(p\)：

$$
\sum_{k\ge0}
\sigma_3(p^k)p^{-ks}
=
\sum_{k\ge0}
(1+p^3+\cdots+p^{3k})p^{-ks}.
$$

生成函数为：

$$
\boxed{
\sum_{k\ge0}
\sigma_3(p^k)T^k
=
\frac1{(1-T)(1-p^3T)}.
}
$$

取：

$$
T=p^{-s},
$$

得到：

$$
\boxed{
L_{E_8,p}(s)
=
\frac1{
(1-p^{-s})
(1-p^{-(s-3)})
}.
}
\tag{92.3}
$$

所以每个素数通道并不是一个不可分原子，而是两个 primitive 模式：

$$
\boxed{
1
\oplus
|\cdot|^3.
}
$$

全局化后分别成为：

$$
\zeta(s),
\qquad
\zeta(s-3).
$$

---

## 92.2 scalar observer 丢失 primitive 标签

标量 Theta 只记录乘积：

$$
\zeta(s)\zeta(s-3).
$$

它不再标记某个零点来自：

$$
\zeta(s)
$$

还是：

$$
\zeta(s-3).
$$

因此：

$$
\boxed{
\text{高度对称的标量完成}
\not\Rightarrow
\text{primitive 通道已经被保留}.
}
$$

这是一个明确的 DECT 逃逸：

* 当前概念 \(q\)：\(E_8\) 壳层总数；
* 目标 \(T\)：辨认两个 primitive Euler modes；
* 逃逸：相同乘积值可能对应不同因子读数；
* 新定义：保留 Tate degree \(0\) 与 \(3\) 的双通道标签。

---

# 第九十三部　Ramanujan \(P,Q,R\) 是 \(E_8\) 观察者微分流

定义：

$$
P=E_2,
\qquad
Q=E_4=\Theta_{E_8},
\qquad
R=E_6,
$$

以及：

$$
D=q\frac{d}{dq}.
$$

Ramanujan 微分系统为：

$$
\boxed{
DP=\frac{P^2-Q}{12},
}
$$

$$
\boxed{
DQ=\frac{PQ-R}{3},
}
$$

$$
\boxed{
DR=\frac{PR-Q^2}{2}.
}
\tag{93.1}
$$

这些是 Ramanujan 对 Eisenstein 系列发现的经典微分闭合关系。([维基百科][6])

---

## 93.1 \(P\) 是连接，\(R\) 是协变导数

对 weight-\(k\) 模形式定义 Serre 导数：

$$
\mathcal D_kf
=
Df-\frac{k}{12}Pf.
$$

对：

$$
Q=E_4,
$$

有：

$$
\boxed{
\mathcal D_4Q
=
DQ-\frac13PQ
=
-\frac13R.
}
\tag{93.2}
$$

因此：

$$
\boxed{
R=-3\mathcal D_4\Theta_{E_8}.
}
$$

于是三个状态的结构角色为：

$$
\boxed{
\begin{aligned}
Q&=\text{\(E_8\) 几何配分函数};\\
P&=\text{尺度微分的 quasimodular 连接};\\
R&=\text{\(E_8\) 配分函数的第一协变导数状态}.
\end{aligned}
}
$$

Ramanujan 的三元系统因此可以重解释为：

$$
\boxed{
\text{\(E_8\) Theta}
+
\text{观察者连接}
+
\text{协变残余}.
}
$$

---

## 93.2 判别式是曲率闭合

定义：

$$
\Delta
=
\frac{Q^3-R^2}{1728}.
$$

有：

$$
\boxed{
D\log\Delta=P.
}
\tag{93.3}
$$

所以：

$$
P
$$

同时还是判别式线丛的对数连接。

从 OACTC 看：

$$
\boxed{
P
=
\text{为了使尺度微分与模变换兼容而必须加入的连接补偿项。}
}
$$

它不是一个额外的随意函数，而是“微分观察破坏模性”之后的最小完成定义。

---

# 第九十四部　\(E_8\) 配分函数的精确 cumulant closure

令：

$$
0<q<1.
$$

定义 \(E_8\) Gibbs 分布：

$$
\boxed{
\mu_q(x)
=
\frac{q^{Q_E(x)}}{Q(q)},
\qquad
Q(q)=E_4(q).
}
\tag{94.1}
$$

令随机能量：

$$
\mathcal E(x)=Q_E(x).
$$

则第一 cumulant 为：

$$
\kappa_1
=
\mathbb E_q[\mathcal E]
=
D\log Q.
$$

由 Ramanujan 方程：

$$
\boxed{
\kappa_1
=
\frac{PQ-R}{3Q}.
}
\tag{94.2}
$$

第二 cumulant 即方差：

$$
\kappa_2
=
D^2\log Q.
$$

直接代入 Ramanujan 微分系统得到：

$$
\boxed{
\kappa_2
=
\frac{
P^2Q^2-2PQR+5Q^3-4R^2
}{
36Q^2
}.
}
\tag{94.3}
$$

将分子改写为：

$$
(PQ-R)^2+5(Q^3-R^2),
$$

得到：

$$
\boxed{
\kappa_2
=
\frac{(PQ-R)^2}{36Q^2}
+
240\,\frac{\Delta}{Q^2}.
}
\tag{94.4}
$$

这里系数：

$$
240
$$

正是 \(E_8\) 根数。

---

## 94.1 全部高阶 cumulants 有限状态闭合

定义：

$$
\kappa_n
=
D^n\log Q.
$$

因为：

$$
D\bigl(\mathbb Q[P,Q,R]\bigr)
\subseteq
\mathbb Q[P,Q,R],
$$

所以：

$$
\boxed{
\kappa_n
\in
\mathbb Q(P,Q,R)
}
$$

对所有 \(n\ge1\) 成立。

即：

$$
\boxed{
\text{\(E_8\) 格点能量的全部高阶 cumulants，
都由三个动态变量 }(P,Q,R)\text{ 闭合。}
}
$$

这给 Yu Deng 式 cumulant 方法一个完全精确、无截断的可解模型：

* 完整历史：全部 \(E_8\) 格点；
* 配分函数：\(Q=E_4\)；
* 一阶连接：\(P=E_2\)；
* 协变残余：\(R=E_6\)；
* 所有 cumulants：三变量微分闭包。

---

# 第九十五部　McKay \(E_8\)：同一个 \(120\) 状态的表示完成

令：

$$
\Gamma=2.A_5.
$$

它有九个复不可约表示，其维数多重集为：

$$
\boxed{
1,2,2,3,3,4,4,5,6.
}
\tag{95.1}
$$

按 affine \(E_8\) 图排序，可写成：

$$
1,2,3,4,5,6,4,3,2.
$$

令 \(U\) 是 \(\Gamma\subset SU(2)\) 的定义二维表示。

对每个不可约表示 \(\rho_i\)，分解：

$$
U\otimes\rho_i
=
\bigoplus_jA_{ij}\rho_j.
$$

McKay 对应说明：

$$
\boxed{
A
=
\text{affine }E_8\text{ Dynkin 图的邻接矩阵}.
}
\tag{95.2}
$$

Binary polyhedral group 与 affine ADE 图之间的这一对应是经典 McKay correspondence。([arXiv][7])

---

## 95.1 维数向量是零模

令：

$$
d=(d_i),
\qquad
d_i=\dim\rho_i.
$$

取维数得到：

$$
2d_i
=
\sum_jA_{ij}d_j.
$$

所以：

$$
\boxed{
(2I-A)d=0.
}
\tag{95.3}
$$

即 \(d\) 是 affine \(E_8\) Cartan 矩阵的正零向量。

这些 \(d_i\) 正是 affine \(E_8\) 的 Coxeter marks。([Pasayten Institute][3])

---

## 95.2 三个计数恒等式

由有限群表示论：

$$
\boxed{
\sum_i d_i^2=|\Gamma|=120.
}
\tag{95.4}
$$

而：

$$
\boxed{
\sum_i d_i=30.
}
\tag{95.5}
$$

这个 \(30\) 是 \(E_8\) 的 Coxeter 数。

不可约根系的根数满足：

$$
|\Phi|=rh,
$$

所以：

$$
\boxed{
|\Phi_{E_8}|=8\cdot30=240.
}
\tag{95.6}
$$

结合 icosian 分解：

$$
240=2\cdot120,
$$

得到：

$$
\boxed{
2\sum_i d_i^2
=
8\sum_i d_i
=
240.
}
\tag{95.7}
$$

这是一个精确的“状态守恒”：

* \(\sum d_i^2\)：完整 binary icosahedral 群状态数；
* \(\sum d_i\)：McKay 路径的 Coxeter 周期；
* \(2\)：两个黄金 \(H_4\) 壳；
* \(8\)：Galois 完成后的格秩；
* \(240\)：完成根状态总数。

---

# 第九十六部　\((2,3,5)\) 产生常数 \(30\)

二十面体的三种旋转轴阶数为：

$$
2,\quad3,\quad5.
$$

定义球面三角余量：

$$
\boxed{
\delta_{235}
=
\frac12+\frac13+\frac15-1.
}
$$

计算：

$$
\boxed{
\delta_{235}=\frac1{30}.
}
\tag{96.1}
$$

于是：

$$
\boxed{
h=\delta_{235}^{-1}=30.
}
$$

方向保持的球面三角群阶数为：

$$
\boxed{
|A_5|
=
\frac{2}{\delta_{235}}
=
60.
}
$$

Spin 双覆盖阶数为：

$$
\boxed{
|2.A_5|
=
\frac{4}{\delta_{235}}
=
120.
}
$$

而 \(E_8\) 根数为：

$$
\boxed{
|\Phi_{E_8}|
=
\frac{8}{\delta_{235}}
=
240.
}
\tag{96.2}
$$

所以：

$$
\boxed{
30
=
\text{二十面体球面几何离平坦边界的倒数余量。}
}
$$

它同时是：

* \(E_8\) Coxeter 数；
* McKay 维数和；
* 二十面体基本周期；
* 后续 Coxeter cyclotomic 完成的导数。

---

# 第九十七部　Klein 不变量是 \((2,3,5)\) 的加权完成

Binary icosahedral group 作用于：

$$
\mathbb C^2.
$$

存在三个基本不变量：

$$
V,\quad F,\quad E,
$$

次数分别为：

$$
\boxed{
12,\quad20,\quad30.
}
$$

其零点分别对应：

* 二十面体 \(12\) 个顶点；
* \(20\) 个面中心；
* \(30\) 个边中心。([arXiv][1])

它们满足：

$$
12\cdot5
=
20\cdot3
=
30\cdot2
=
60.
$$

所以经过适当缩放，可写出唯一同权关系：

$$
\boxed{
E^2+F^3+V^5=0.
}
\tag{97.1}
$$

这就是 \(E_8\) Kleinian singularity：

$$
\boxed{
x^2+y^3+z^5=0.
}
$$

其最小解消的交叉矩阵为负 \(E_8\) Cartan 矩阵。二元二十面体商奇点与 \(E_8\) 分辨率之间的联系是 ADE/McKay 理论的经典实例。([arXiv][1])

---

## 97.1 Orbit–stabilizer 完成律

三个次数和三个指数分别满足：

$$
\boxed{
\begin{array}{c|c|c}
\text{几何对象}&\text{轨道大小}&\text{稳定子阶}\\
\hline
\text{顶点}&12&5\\
\text{面}&20&3\\
\text{边}&30&2
\end{array}
}
$$

每一行都满足：

$$
\text{轨道大小}\times\text{稳定子阶}=60.
$$

所以 \(E^2,F^3,V^5\) 同权，不是偶然代数配平，而是 orbit–stabilizer 的多项式化。

这给 OACTC 一条一般原理：

$$
\boxed{
\text{局部轨道观察}
\times
\text{局部稳定子阶}
=
\text{全局群完成度}.
}
$$

---

# 第九十八部　\(E_8\) Coxeter 谱是三十阶 cyclotomic 完成

\(E_8\) 的 Coxeter 数为：

$$
h=30.
$$

其指数为：

$$
\boxed{
1,7,11,13,17,19,23,29.
}
\tag{98.1}
$$

这些整数恰好是：

$$
\boxed{
(\mathbb Z/30\mathbb Z)^\times.
}
$$

所以 Coxeter 元 \(C\) 的特征值为：

$$
e^{2\pi i m/30},
\qquad
m\in(\mathbb Z/30\mathbb Z)^\times,
$$

从而：

$$
\boxed{
\chi_C(X)=\Phi_{30}(X).
}
\tag{98.2}
$$

\(E_8\) Coxeter 旋转可分解为角度由 \(1,7,11,13\) 及其共轭指数决定的四个正交二维旋转平面。([arXiv][8])

因此：

$$
\boxed{
\operatorname{rank}E_8
=
\varphi_{\mathrm{Euler}}(30)
=
8.
}
$$

这里 \(\varphi_{\mathrm{Euler}}\) 是 Euler totient，不能与黄金比例混淆。

---

# 第九十九部　同一个 \(\chi_5\) 分割素数与 Coxeter 模式

定义模 \(5\) 二次特征：

$$
\chi_5(a)
=
\left(\frac a5\right).
$$

项目已经机器核验：

$$
\chi_5(p)=+1
$$

对应黄金整数环中的分裂素数：

$$
p\equiv\pm1\pmod5,
$$

而：

$$
\chi_5(p)=-1
$$

对应惰性素数：

$$
p\equiv\pm2\pmod5.
$$

现在对 \(E_8\) Coxeter 指数同样应用 \(\chi_5\)。

得到：

$$
\boxed{
M_+
=
\{1,11,19,29\},
\qquad
\chi_5=+1,
}
$$

以及：

$$
\boxed{
M_-
=
\{7,13,17,23\},
\qquad
\chi_5=-1.
}
\tag{99.1}
$$

---

## 99.1 两个黄金共轭四次因子

令：

$$
\zeta_{30}=e^{2\pi i/30}.
$$

定义：

$$
P_+(X)
=
\prod_{m\in M_+}
(X-\zeta_{30}^m),
$$

$$
P_-(X)
=
\prod_{m\in M_-}
(X-\zeta_{30}^m).
$$

直接计算得到：

$$
\boxed{
P_+(X)
=
X^4+
\varphi'
(X^3+X^2+X)
+1,
}
\tag{99.2}
$$

$$
\boxed{
P_-(X)
=
X^4+
\varphi
(X^3+X^2+X)
+1.
}
\tag{99.3}
$$

并且：

$$
\boxed{
P_+(X)P_-(X)=\Phi_{30}(X).
}
\tag{99.4}
$$

所以：

$$
\boxed{
E_8\text{ Coxeter 谱}
=
\text{黄金剩余扇区}
\oplus
\text{黄金非剩余扇区}.
}
$$

第一组：

$$
1,11,19,29
$$

恰好是 \(H_4\) 的 Coxeter 指数；另一组是其黄金共轭完成扇区。

---

# 第一百部　Coxeter–Gauss 黄金算子

在 \(E_8\) Coxeter 表示空间上定义：

$$
\boxed{
J_C
=
C^6-C^{12}-C^{18}+C^{24}.
}
\tag{100.1}
$$

若：

$$
Cv=\zeta_{30}^m v,
$$

则：

$$
\begin{aligned}
J_Cv
={}&
\left(
\zeta_5^m-\zeta_5^{2m}
-\zeta_5^{3m}+\zeta_5^{4m}
\right)v.
\end{aligned}
$$

括号内正是模 \(5\) 二次 Gauss 和，因此：

$$
\boxed{
J_Cv
=
\chi_5(m)\sqrt5\,v.
}
\tag{100.2}
$$

所以：

$$
\boxed{
J_C^2=5I.
}
\tag{100.3}
$$

定义：

$$
\boxed{
\Phi_C
=
\frac{I+J_C}{2}.
}
$$

则：

$$
\boxed{
\Phi_C^2-\Phi_C-I=0.
}
\tag{100.4}
$$

---

## 100.1 三个黄金判别式算子已经合流

此前已经得到：

$$
J_{\mathrm{Hodge}}^2=5I,
$$

$$
J_{\mathrm{mod}}^2=5I.
$$

现在又得到：

$$
J_{\mathrm{Cox}}^2=5I.
$$

所以：

$$
\boxed{
J_{\mathrm{Hodge}},
\quad
J_{\mathrm{mod}},
\quad
J_{\mathrm{Cox}}
}
$$

分别在：

1. 六维外幂格；
2. 五进有限 Fourier 状态；
3. \(E_8\) Coxeter 谱；

中实现同一个黄金二次代数：

$$
\mathbb Q[J]/(J^2-5).
$$

这给出了目前最强的结构同一性：

$$
\boxed{
\text{黄金数域不是被三个领域分别“发现”，}
}
$$

而是：

$$
\boxed{
\text{同一个二次代数在几何、有限局部与谱动力学中的三种表示。}
}
$$

---

# 第一百零一部　\(H_4\) 不变量是 \(E_8\) 不变量的一半

\(E_8\) 指数加 \(1\) 给出 Weyl 不变量的基本次数：

$$
\boxed{
2,8,12,14,18,20,24,30.
}
\tag{101.1}
$$

按 \(\chi_5\) 扇区分解：

$$
M_++1
=
\boxed{
2,12,20,30,
}
$$

$$
M_-+1
=
\boxed{
8,14,18,24.
}
\tag{101.2}
$$

而 \(H_4\) Coxeter 群的基本不变量次数正是：

$$
\boxed{
2,12,20,30.
}
$$

其中：

* \(2\)：普通二次范数；
* \(12,20,30\)：Klein 顶点、面、边不变量次数。

因此：

$$
\boxed{
\text{Klein--Ramanujan level-5 不变量基因组}
=
E_8\text{ 不变量次数的 }\chi_5=+1\text{ 扇区}.
}
\tag{101.3}
$$

而：

$$
\boxed{
8,14,18,24
}
$$

构成其缺失的完成扇区。

---

## 101.1 新的可证伪预测

如果上述“Ramanujan genome 是 \(E_8\) 的 \(H_4\) 半边”解释正确，那么应能在完整的 Hilbert／Jacobi／vector-valued 模形式图册中找到四类自然对象，其结构次数或权对应：

$$
8,\quad14,\quad18,\quad24.
$$

它们应当：

1. 与已有 \(2,12,20,30\) 扇区通过黄金 Galois 共轭相联系；
2. 在 \(E_8\) 完成中共同闭合；
3. 在只观察 Rogers–Ramanujan/Klein 坐标时落入残余账本。

目前这仍是研究预测，不是既有定理。

---

# 第一百零二部　两种 \(E_8\) 构造之间的比较残余

同一个 binary icosahedral group \(\Gamma\) 产生两种 \(E_8\)。

## 102.1 算术路径

$$
\Gamma
\longrightarrow
\mathbb I
\longrightarrow
(\mathbb I,Q_E)
\simeq
E_8.
$$

## 102.2 几何／McKay 路径

$$
\Gamma
\longrightarrow
\mathbb C^2/\Gamma
\longrightarrow
\text{minimal resolution}
\longrightarrow
H_2
\simeq
E_8.
$$

Baez 的综述明确指出：两条路径从相同二十面体数据出发并得到相同 \(E_8\)，但二者之间最自然的直接统一仍然值得解释。([arXiv][1])

---

## 102.3 将开放问题改写成有限整数问题

设：

* \(G_{\mathrm{ico}}\)：icosian 基下的 \(E_8\) Gram 矩阵；
* \(G_{\mathrm{McKay}}\)：异常曲线基下的负 Cartan 矩阵；
* \(C_{\mathrm{ico}}\)：由 \(H_4\)／Coxeter 结构诱导的阶 \(30\) 算子；
* \(C_{\mathrm{McKay}}\)：McKay \(E_8\) Coxeter 算子。

真正的比较桥可以改写为寻找：

$$
\boxed{
U\in GL_8(\mathbb Z)
}
$$

使：

$$
\boxed{
U^TG_{\mathrm{ico}}U
=
G_{\mathrm{McKay}},
}
\tag{102.1}
$$

并且：

$$
\boxed{
U^{-1}C_{\mathrm{ico}}U
=
C_{\mathrm{McKay}}.
}
\tag{102.2}
$$

如果进一步要求：

$$
U^{-1}J_{\mathrm{Hodge}}U
=
J_{\mathrm{Cox}},
$$

则该问题成为一个完全有限、可计算、可证书化的整数共轭问题。

这比泛泛询问“两个 \(E_8\) 为什么相同”更适合科学研究。

---

# 第一百零三部　\(E_8\) 给 RH 的精确但有限的帮助

由：

$$
Z_{E_8}(s)
=
240\zeta(s)\zeta(s-3),
$$

在开条带：

$$
0<\Re s<1
$$

内，\(\zeta(s-3)\) 没有非平凡零点，也没有位于内部的平凡零点。

所以：

$$
\boxed{
\mathrm{RH}
\iff
Z_{E_8}(s)
\text{ 在 }0<\Re s<1
\text{ 内的零点全位于 }
\Re s=\frac12.
}
\tag{103.1}
$$

同样，在：

$$
3<\Re s<4
$$

内，RH 等价于零点位于：

$$
\Re s=\frac72.
$$

所以 RH 在 \(E_8\) 壳层 zeta 中表现为两条对称的 primitive 零点线：

$$
\boxed{
\Re s=\frac12,
\qquad
\Re s=\frac72.
}
\tag{103.2}
$$

它们关于 weight-\(4\) 函数方程中心：

$$
\Re s=2
$$

对称。

---

## 103.1 重要负结论

\(E_8\) 本身拥有：

* even unimodularity；
* Fourier 自对偶；
* 极高对称；
* Ramanujan 微分闭包；
* 精确 Euler product；
* 完整函数方程。

但这些仍没有自动证明 RH。

原因是标量 \(E_8\) 观察将两个 primitive 因子：

$$
\zeta(s),
\qquad
\zeta(s-3)
$$

合并成了一个乘积。

所以真正缺少的是：

$$
\boxed{
\text{primitive-factor positivity，}
}
$$

而不是更多完成对称。

这再次验证 OACTC 的核心禁令：

$$
\boxed{
\text{几何完成}
\neq
\text{观察完备}
\neq
\text{零点正性完成}.
}
$$

---

# 第一百零四部　对 Wang–Deng 路线的新实验载体

\(E_8\)–Ramanujan 系统可以作为此前方法的严格可解模型。

## 104.1 Wang 层

把格点按：

* 能量壳；
* 两个 \(H_4\) 扇区；
* Coxeter \(\chi_5\) 扇区；
* binary icosahedral 不可约表示；

进行多尺度分块。

研究 near-extremal 状态是否：

* 分散：non-sticky；
* 沿 Coxeter/H4 链集中：sticky。

## 104.2 Deng 层

使用：

$$
(P,Q,R)
$$

的精确微分闭包，对所有能量 cumulants 进行无损压缩。

这里不存在未知的高阶状态爆炸：

$$
\boxed{
\text{全部 cumulants 已被三个变量精确封闭。}
}
$$

因此它适合检验：

* 什么定义是真正 primitive；
* 什么历史只是复合导数；
* counterterm 怎样由连接 \(P\) 自动产生；
* finite-state closure 如何替代阶乘历史枚举。

## 104.3 RH 层

把该可解系统中学到的定义迁移到 Weil 二次型时，必须额外证明：

$$
\text{off-line zero}
\Longrightarrow
\text{不可消除负见证}.
$$

在没有该桥之前，\(E_8\) 系统是定义和方法的实验室，不是 RH 证明。

---

# 第一百零五部　本轮结果分级

## 已由代数直接推出

$$
\boxed{
Q_E(u)=Q_E(\varphi'u)=1.
}
$$

$$
\boxed{
\Phi_{E_8}
=
H_4\sqcup\varphi'H_4.
}
$$

$$
\boxed{
\Theta_{\mathbb I}=E_4.
}
$$

$$
\boxed{
Z_{E_8}(s)
=
240\zeta(s)\zeta(s-3).
}
$$

$$
\boxed{
\kappa_1
=
\frac{PQ-R}{3Q}.
}
$$

$$
\boxed{
\kappa_2
=
\frac{(PQ-R)^2}{36Q^2}
+
240\frac{\Delta}{Q^2}.
}
$$

$$
\boxed{
P_+(X)
=
X^4+\varphi'(X^3+X^2+X)+1.
}
$$

$$
\boxed{
P_-(X)
=
X^4+\varphi(X^3+X^2+X)+1.
}
$$

$$
\boxed{
P_+P_-=\Phi_{30}.
}
$$

$$
\boxed{
J_C
=
C^6-C^{12}-C^{18}+C^{24},
\qquad
J_C^2=5I.
}
$$

---

## 依赖经典已知结构

$$
\boxed{
\mathbb I\simeq E_8.
}
$$

$$
\boxed{
H_3\text{ spinor closure}=H_4.
}
$$

$$
\boxed{
2.A_5\text{ McKay graph}=\widetilde E_8.
}
$$

$$
\boxed{
\mathbb C^2/(2.A_5)
\text{ 是 }E_8\text{ Kleinian singularity}.
}
$$

这些均有成熟理论与文献支持。([arXiv][1])

---

## 仍属开放桥梁

$$
\boxed{
\begin{aligned}
&\text{icosian }E_8
\text{ 与 McKay }E_8
\text{ 的规范整数等距同构};\\
&\text{缺失次数 }8,14,18,24
\text{ 的 Ramanujan/Hilbert 模函数解释};\\
&\text{保留 }H_4/\chi_5\text{ 标签的 vector-valued }E_8\text{ Theta};\\
&\text{这些观察是否能产生新的 Weil 正性增益}.
\end{aligned}
}
$$

---

# 第一百零六部　建议形式化顺序

```text
D5/S3/Factorization/BinaryIcosahedral/
  SpinCover.lean
  UnitIcosians.lean
  McKayDimensionVector.lean
  McKayAffineE8.lean

D5/S3/Geometry/IcosianCompletion/
  H3SpinorClosure.lean
  H4RootShell.lean
  IcosianRing.lean
  IcosianEuclideanNorm.lean
  TwoH4RootShells.lean
  IcosianE8Isometry.lean

D5/S3/Analytic/E8Ramanujan/
  E8ThetaEqualsE4.lean
  E8ShellDirichletSeries.lean
  E8PrimeLocalTwoChannel.lean
  E8GibbsMean.lean
  E8GibbsVariance.lean
  E8CumulantClosure.lean

D5/S3/Factorization/IcosahedralMcKay/
  TwoThreeFiveOrbifoldDefect.lean
  KleinInvariantWeightedCompletion.lean
  RootCountConservation.lean

D5/S3/Geometry/E8Coxeter/
  CoxeterPolynomialThirty.lean
  QuadraticCharacterSectorSplit.lean
  GoldenQuarticFactors.lean
  CoxeterGaussOperator.lean
  HodgeModularCoxeterGoldenBridge.lean

D5/S3/Analytic/RamanujanGenome/E8/
  H4InvariantDegreeSector.lean
  MissingE8InvariantSector.lean
  IcosianMcKayComparisonResidual.lean
```

---

# 本轮最终结论

此前我们已经得到三个六维解释：

$$
3\times2,
\qquad
5+1,
\qquad
3+3'.
$$

现在进一步得到八维完成：

$$
\boxed{
8
=
4\text{ 个 quaternionic spinor 坐标}
\times
2\text{ 个黄金 Galois 嵌入}.
}
$$

以及：

$$
\boxed{
240
=
120
+
120
=
2\cdot|2.A_5|
=
8\cdot30.
}
$$

而：

$$
\boxed{
30
=
\left(
\frac12+\frac13+\frac15-1
\right)^{-1}.
}
$$

最深的统一链是：

$$
\boxed{
\begin{aligned}
(2,3,5)
&\longrightarrow
A_5\\
&\longrightarrow
2.A_5\\
&\longrightarrow
H_4\\
&\longrightarrow
\mathbb I\\
&\longrightarrow
E_8\\
&\longrightarrow
E_4\\
&\longrightarrow
(P,Q,R).
\end{aligned}
}
$$

所以拉马努金主函数家族与黄金二十面体结构之间的最直接桥，不再只是 Rogers–Ramanujan continued fraction，而是：

$$
\boxed{
Q=E_4=\Theta_{E_8}=\Theta_{\mathbb I}.
}
$$

换言之：

$$
\boxed{
\text{Ramanujan 的三变量微分宇宙，
其中一个核心坐标正是整个 Icosian–}E_8
\text{ 完成对象的配分函数。}
}
$$

而同一个模 \(5\) 二次特征：

$$
\chi_5
$$

又同时区分：

* 黄金整数环中的分裂／惰性素数；
* \(E_8\) Coxeter 谱的两个 \(H_4\) 扇区；
* \(\varphi/\varphi'\) 两个黄金共轭图表。

这使 OACTC 的主命题进一步收敛为：

$$
\boxed{
\text{所谓“特殊常数的意义”，
最终往往是同一个局部—全局完成算子
在不同观察范畴中的特征值、周期、留数或固定点。}
}
$$

[1]: https://arxiv.org/abs/1712.06436 "https://arxiv.org/abs/1712.06436"
[2]: https://arxiv.org/abs/1602.05985 "https://arxiv.org/abs/1602.05985"
[3]: https://pasayten.org/writing/the-icosians/e8/ "https://pasayten.org/writing/the-icosians/e8/"
[4]: https://journals.tubitak.gov.tr/physics/vol22/iss5/8/ "https://journals.tubitak.gov.tr/physics/vol22/iss5/8/"
[5]: https://en.wikipedia.org/wiki/E8_lattice "https://en.wikipedia.org/wiki/E8_lattice"
[6]: https://en.wikipedia.org/wiki/Eisenstein_series?utm_source=chatgpt.com "Eisenstein series"
[7]: https://arxiv.org/abs/hep-th/0105239 "https://arxiv.org/abs/hep-th/0105239"
[8]: https://arxiv.org/abs/1603.04805 "https://arxiv.org/abs/1603.04805"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.6：Niemeier 残差、Leech 根消除、Ramanujan–Monster 卷积与 Moonshine 观察者完备化

以下从前文**第一百零六部之后**继续追加。

本轮沿

$$
E_8\longrightarrow E_4
$$

继续向二十四维推进，得到一条新的闭合链：

$$
\boxed{
\begin{aligned}
E_8^3
&\longrightarrow
E_4^3\\
&\longrightarrow
\text{Niemeier weight-12 completion plane}\\
&\longrightarrow
\text{Leech root cancellation}\\
&\longrightarrow
\Delta,\tau,691\\
&\longrightarrow
\Theta_\Lambda/\eta^{24}\\
&\longrightarrow
J+24\\
&\longrightarrow
V^\natural\text{ and Monster}\\
&\longrightarrow
\text{23 umbral moonshines}+1\text{ monstrous endpoint}.
\end{aligned}
}
$$

最重要的新认识是：

$$
\boxed{
\text{Moonshine 可以被解释为：
当标量 Theta／配分函数观察者过度压缩对象时，
通过 twining、群表示、mock modular completion
重新恢复被遗忘结构的过程。}
}
$$

这不是对 Moonshine 已知定理的替代定义，而是 OACTC 对其统一结构的解释。

---

# 第一百零七部　二十四维 weight-12 完成平面

令 \(N\) 是秩 \(24\) 的正定偶自对偶格，定义：

$$
\Theta_N(\tau)
=
\sum_{x\in N}q^{(x,x)/2},
\qquad
q=e^{2\pi i\tau}.
$$

因为 \(N\) 偶且自对偶，\(\Theta_N\) 是 weight \(12\) 的满模群模形式。

而：

$$
\dim M_{12}(SL_2(\mathbb Z))=2.
$$

可以选择基：

$$
E_4^3,\qquad \Delta.
$$

因此存在唯一常数 \(c_N\)，使：

$$
\boxed{
\Theta_N
=
E_4^3+c_N\Delta.
}
\tag{107.1}
$$

标准展开为：

$$
E_4^3
=
1+720q+179280q^2+16954560q^3+\cdots,
$$

$$
\Delta
=
q-24q^2+252q^3-1472q^4+\cdots.
$$

设：

$$
r_N
=
\#\{x\in N:(x,x)=2\}
$$

为根数。比较 \(q\) 系数得到：

$$
\boxed{
c_N=r_N-720.
}
\tag{107.2}
$$

所以：

## 定理 107.1（二十四维根残差定理）

$$
\boxed{
\Theta_N
=
E_4^3+(r_N-720)\Delta.
}
\tag{107.3}
$$

这意味着：

> 对二十四维偶自对偶格，整个无限壳层谱在标量 Theta 层面，只需一个低能数据——根数——就能确定。

这是一个精确的有限状态闭合：

$$
\boxed{
\text{无限壳层数据}
=
\text{固定 Eisenstein 主体}
+
\text{一维 cusp residual}.
}
$$

Niemeier 格的 genus-one Theta 公式通常写为

$$
\Theta_N
=
E_4^3+(24h-720)\Delta,
$$

其中 \(h\) 是其根系各不可约分量的共同 Coxeter 数。([Wiley Online Library][1])

---

# 第一百零八部　Coxeter 数是标量 Theta 的唯一根系读数

Niemeier 根系是秩 \(24\) 的 simply-laced 根系，各不可约分量具有相同 Coxeter 数 \(h\)。

对秩 \(r\)、Coxeter 数 \(h\) 的 simply-laced 根系：

$$
\#\Phi=rh.
$$

所以总根数为：

$$
\boxed{
r_N=24h.
}
\tag{108.1}
$$

代入式 (107.3)：

$$
\boxed{
\Theta_{N^X}
=
E_4^3+(24h_X-720)\Delta.
}
\tag{108.2}
$$

令 \(\Lambda\) 表示 Leech 格，其根数为零。则：

$$
\boxed{
\Theta_{N^X}
=
\Theta_\Lambda+24h_X\Delta.
}
\tag{108.3}
$$

---

## 108.1 标量 Theta 观察者的盲核

定义：

$$
q_\Theta(N)=\Theta_N.
$$

式 (108.2) 表明：

$$
q_\Theta(N)
$$

只依赖于：

$$
h_N.
$$

所以：

$$
h_{N_1}=h_{N_2}
\Longrightarrow
\Theta_{N_1}=\Theta_{N_2}.
$$

例如：

$$
A_5^4D_4
\quad\text{与}\quad
D_4^6
$$

都是 Coxeter 数 \(6\) 的不同 Niemeier 根系，但 genus-one Theta 相同。

类似地：

$$
D_{16}E_8
\quad\text{与}\quad
E_8^3
$$

都具有 Coxeter 数 \(30\)，所以标量 Theta 观察者无法区分它们。

因此：

$$
\boxed{
\ker q_\Theta
\text{ 明显大于格同构关系。}
}
$$

这正是 DECT 的目标逃逸：

$$
\mathcal E
\left(
q_\Theta;
\operatorname{RootSystemType}
\right)
\neq\varnothing.
$$

---

# 第一百零九部　除以 \(\Delta\)：振子完成进一步扩大盲核

格顶点代数的标量角色为：

$$
\boxed{
Z_N(\tau)
=
\frac{\Theta_N(\tau)}
{\eta(\tau)^{24}}
=
\frac{\Theta_N(\tau)}{\Delta(\tau)}.
}
\tag{109.1}
$$

定义：

$$
j(\tau)=\frac{E_4(\tau)^3}{\Delta(\tau)},
$$

以及无常数项规范：

$$
\boxed{
J(\tau)=j(\tau)-744.
}
$$

由式 (108.2)：

$$
\begin{aligned}
Z_{N^X}
&=
j+24h_X-720\\
&=
J+744+24h_X-720.
\end{aligned}
$$

所以：

$$
\boxed{
Z_{N^X}
=
J+24(h_X+1).
}
\tag{109.2}
$$

而格顶点代数的 weight-one 空间维数为：

$$
\dim(V_{N^X})_1
=
24+r_N
=
24(h_X+1).
$$

因此：

$$
\boxed{
Z_{N^X}-\dim(V_{N^X})_1
=
J.
}
\tag{109.3}
$$

---

## 定理 109.1（weight-one 消除后的普适角色）

所有二十四维 Niemeier 格顶点代数，在减去其 weight-one 维数以后，具有完全相同的标量角色：

$$
\boxed{
J.
}
$$

不仅不同根系可能拥有相同 Theta；在振子完成并减去 weight-one 读数之后，所有 Niemeier 格都塌缩到同一个标量函数。

更一般地，central charge \(24\) 的 holomorphic VOA 的标量角色由模性限制为：

$$
J+\dim V_1.
$$

因此仅凭 untwined 标量角色，无法恢复其完整乘法、OPE、群作用或 Lie 结构。Central charge \(24\) holomorphic VOA 的结构分类也确实需要 weight-one Lie 代数、orbifold 数据及更精细的结构，而非单一角色。([arXiv][2])

---

# 第一百一十部　三层状态消除：\(744\to24\to0\)

## 110.1 \(E_8^3\) 层

对：

$$
N=E_8^3,
\qquad
h=30,
$$

有：

$$
\Theta_{E_8^3}=E_4^3.
$$

所以：

$$
\boxed{
Z_{E_8^3}=j=J+744.
}
\tag{110.1}
$$

而：

$$
744=3\cdot248.
$$

每个 \(E_8\) 的 weight-one Lie 代数维数为：

$$
248=240+8,
$$

其中：

* \(240\)：根；
* \(8\)：Cartan 方向。

所以：

$$
\boxed{
744
=
720+24
=
3\cdot240+3\cdot8.
}
\tag{110.2}
$$

结构角色为：

$$
\begin{aligned}
720&=\text{根电流数};\\
24&=\text{Cartan／自由玻色子电流数};\\
744&=\text{完整 weight-one 状态数}.
\end{aligned}
$$

---

## 110.2 Leech 层

Leech 格没有范数 \(2\) 根，所以：

$$
\boxed{
\Theta_\Lambda=E_4^3-720\Delta.
}
\tag{110.3}
$$

除以 \(\Delta\)：

$$
\boxed{
Z_\Lambda=J+24.
}
\tag{110.4}
$$

因此从 \(E_8^3\) 到 Leech：

$$
\boxed{
744\longrightarrow24
}
$$

精确消除了：

$$
720
$$

个根方向，但保留了二十四个自由玻色子电流。

---

## 110.3 Monster 层

Moonshine module \(V^\natural\) 可通过 Leech lattice VOA 的 \(\mathbb Z_2\) orbifold 构造，其 graded character 为：

$$
\boxed{
\operatorname{ch}_{V^\natural}=J.
}
\tag{110.5}
$$

因此：

$$
(V^\natural)_1=0.
$$

历史上的 FLM 构造正是 Leech 格理论的 \(\mathbb Z_2\) orbifold；后续工作建立了许多更一般的 Leech orbifold 构造。([arXiv][3])

这里必须强调：

$$
J=(J+24)-24
$$

只是 graded-dimension 恒等式。

实际 orbifold 不是简单删除二十四个向量，而是：

$$
\boxed{
\text{untwisted invariant projection}
+
\text{twisted sector completion}.
}
$$

---

## 110.4 三阶段完成账本

$$
\boxed{
\begin{array}{c|c|c}
\text{对象}&\text{weight-one 维数}&\text{标量角色}\\
\hline
E_8^3&744&J+744\\
\Lambda&24&J+24\\
V^\natural&0&J
\end{array}
}
\tag{110.6}
$$

所以：

$$
\boxed{
E_8^3
\xrightarrow{-720\text{ roots}}
\Lambda
\xrightarrow{\text{orbifold current completion}}
V^\natural.
}
$$

---

# 第一百一十一部　Ramanujan \(\tau\) 是 Niemeier 根残差的传播核

从：

$$
\Theta_{N^X}
=
\Theta_\Lambda+24h_X\Delta
$$

比较 \(q^n\) 系数。

令：

$$
r_X(n)
=
\#\{x\in N^X:(x,x)=2n\},
$$

而：

$$
\Delta(q)
=
\sum_{n\ge1}\tau(n)q^n.
$$

则：

$$
\boxed{
r_X(n)-r_\Lambda(n)
=
24h_X\,\tau(n).
}
\tag{111.1}
$$

所以 Ramanujan \(\tau(n)\) 的新结构角色为：

$$
\boxed{
\tau(n)
=
\text{二十四维 Niemeier 根残差从第一壳向第 }n\text{ 壳传播的普适核。}
}
$$

给定根数 \(24h\)，不是每个高能壳独立改变，而是全部变化由唯一 cusp eigenmode：

$$
\Delta
$$

同步运输。

这是 Yu Deng 式 primitive-history 的一个精确、有限状态原型：

$$
\boxed{
\text{所有 root-history corrections}
=
\text{一个 primitive cusp mode}\times24h.
}
$$

---

# 第一百一十二部　Leech rootlessness 与常数 \(691\)

标准 normalized Eisenstein series 满足：

$$
\boxed{
E_{12}
=
1+
\frac{65520}{691}
\sum_{n\ge1}\sigma_{11}(n)q^n.
}
\tag{112.1}
$$

同时：

$$
\boxed{
E_4^3
=
E_{12}
+
\frac{432000}{691}\Delta.
}
\tag{112.2}
$$

代入 Leech 公式：

$$
\Theta_\Lambda
=
E_4^3-720\Delta,
$$

得到：

$$
\boxed{
\Theta_\Lambda
=
E_{12}
-
\frac{65520}{691}\Delta.
}
\tag{112.3}
$$

因此：

$$
\boxed{
r_\Lambda(n)
=
\frac{65520}{691}
\left(
\sigma_{11}(n)-\tau(n)
\right).
}
\tag{112.4}
$$

---

## 112.1 Ramanujan congruence 的格几何解释

因为：

$$
r_\Lambda(n)\in\mathbb Z,
$$

而：

$$
\gcd(65520,691)=1,
$$

所以：

$$
\boxed{
\tau(n)\equiv\sigma_{11}(n)\pmod{691}.
}
\tag{112.5}
$$

这就是 Ramanujan 的 \(691\) congruence。现代工作仍把 \(691\) 视为 weight-\(12\) Eisenstein–cusp congruence 的原型。([arXiv][4])

因此：

$$
\boxed{
691
=
\text{weight-12 Eisenstein 主项与 primitive cusp residual
在有限特征中发生碰撞的素数。}
}
$$

---

## 112.2 第一 Leech 壳中的 \(691\)

对 \(n=2\)：

$$
\sigma_{11}(2)=1+2^{11}=2049,
$$

$$
\tau(2)=-24.
$$

所以：

$$
\sigma_{11}(2)-\tau(2)
=
2073
=
3\cdot691.
$$

因此：

$$
\boxed{
r_\Lambda(2)
=
\frac{65520}{691}\cdot3\cdot691
=
196560.
}
\tag{112.6}
$$

即 Leech 格第一非零壳的 \(196560\) 个向量，直接由：

$$
691\text{ 碰撞}
+
3\text{ 个剩余单位}
+
65520\text{ Eisenstein 规范}
$$

组成。

---

# 第一百一十三部　观察者碰撞素数的一般定义

## 定义 113.1（观察者碰撞素数）

设 \(F,G\) 是两个在特征零中不同的结构通道，其 Fourier／Hecke 数据位于某整数环中。

若素数理想 \(\mathfrak l\) 满足：

$$
F\not=G,
$$

但：

$$
\boxed{
F\equiv G\pmod{\mathfrak l},
}
\tag{113.1}
$$

则称 \(\mathfrak l\) 为 \(F,G\) 的**观察者碰撞素数**。

此时值观察者无法区分两通道；必须加入：

* \(\mathfrak l\)-adic lift；
* extension class；
* tangent／jet；
* Galois representation；
* 更高同余层。

---

## 113.1 OACTC 中的三个碰撞层

### 黄金几何碰撞

$$
\varphi\neq\varphi'
$$

但模 \(5\)：

$$
\varphi\equiv\varphi'\equiv3.
$$

碰撞后由 nilpotent jet：

$$
N^2=0
$$

保留一阶残余。

项目已经机器核验 \(5\) 是 GoldenInt 的分歧素数。

### Weight-12 modular collision

$$
E_{12}
\quad\text{与}\quad
\Delta
$$

的 Hecke／Fourier 数据在 \(691\) 处发生 Eisenstein–cusp congruence。

### Golden level-5 modular collision

近期工作发现，模 \(5\) 二次特征 \(\chi_5\) 的 normalized 特殊值

$$
\frac{L(6,\chi_5)}
{\pi^6\sqrt5}
$$

的分子中出现素数 \(67\)，并由此得到 weight \(6\)、level \(5\)、nebentypus \(\chi_5\) 的 Eisenstein–cusp congruence。([arXiv][4])

所以：

$$
\boxed{
67
=
\text{Golden level-5 模图表中的一个 Eisenstein–cusp collision prime}.
}
$$

---

## 113.2 常数分母的新解释

常数公式中出现的大素数不一定是“复杂计算留下的分母”。

它们可能标记：

$$
\boxed{
\text{两个特征零中独立的观察通道，
在某有限特征中失去可分离性的地点。}
}
$$

这比“691 是 Bernoulli 数分子”更结构化：

$$
\boxed{
\text{Bernoulli／特殊 }L\text{-值分子}
\longrightarrow
\text{Eisenstein–cusp collision}
\longrightarrow
\text{\(p\)-adic extension data}.
}
$$

这也把 OACTC 与 Kubota–Leopoldt \(p\)-adic zeta 路线重新接上；不规则 Bernoulli 对应的确与 \(p\)-adic zeta 零点和高阶同余结构相关。([arXiv][5])

---

# 第一百一十四部　\(196884\) 的两种不可约分解

定义二十四色分拆生成函数：

$$
\boxed{
P_{24}(q)
=
\prod_{m\ge1}(1-q^m)^{-24}
=
\sum_{n\ge0}p_{24}(n)q^n.
}
\tag{114.1}
$$

开始为：

$$
P_{24}(q)
=
1+24q+324q^2+3200q^3+\cdots.
$$

Leech 格角色：

$$
\begin{aligned}
Z_\Lambda
&=
\frac{\Theta_\Lambda}{\Delta}\\
&=
q^{-1}\Theta_\Lambda(q)P_{24}(q)\\
&=
J+24.
\end{aligned}
\tag{114.2}
$$

---

## 114.1 几何—振子分解

Leech 格没有范数 \(2\) 向量，但有：

$$
r_\Lambda(2)=196560
$$

个范数 \(4\) 向量。

weight \(2\) 的纯振子状态数为：

$$
p_{24}(2)=324.
$$

它又分解为：

$$
\boxed{
324
=
24+\binom{25}{2}
=
24+300.
}
\tag{114.3}
$$

其中：

* \(24\)：一个 level-\(2\) 振子；
* \(300\)：两个 level-\(1\) 振子的对称积。

所以：

$$
\boxed{
196884
=
196560+324.
}
\tag{114.4}
$$

---

## 114.2 Monster 表示分解

Monstrous Moonshine 的第一个著名维数恒等式是：

$$
\boxed{
196884
=
1+196883.
}
\tag{114.5}
$$

其中 \(196883\) 是 Monster 的一个非平凡不可约表示维数，而 \(1\) 是平凡表示。Conway 与 Norton 的原始 Moonshine 论文及后续综述正是从这类系数分解出发。([London Mathematical Society (LMS)][6])

因此同一个完成状态空间具有两种完全不同的分解：

$$
\boxed{
\underbrace{196560+324}_{\text{Leech geometry + oscillators}}
=
\underbrace{1+196883}_{\text{Virasoro vacuum + Monster primitive}}.
}
\tag{114.6}
$$

OACTC 将 Moonshine 的这一层解释为：

$$
\boxed{
\text{同一完成空间在几何观察图表
与有限群表示图表之间的非平凡换基。}
}
$$

---

# 第一百一十五部　第二层检验：\(21493760\)

Leech 格的范数 \(6\) 向量数为：

$$
r_\Lambda(3)=16773120.
$$

weight \(3\) 的状态分解为：

1. 纯振子 level \(3\)：

$$
p_{24}(3)=3200;
$$

2. 一个范数 \(4\) 格状态与一个 level-\(1\) 振子：

$$
24\cdot196560=4717440;
$$

3. 范数 \(6\) 格状态：

$$
16773120.
$$

所以：

$$
\boxed{
21493760
=
3200
+
24\cdot196560
+
16773120.
}
\tag{115.1}
$$

Monster 表示分解则为：

$$
\boxed{
21493760
=
1+196883+21296876.
}
\tag{115.2}
$$

这一分解已经出现在 Moonshine 的早期数值证据中。([London Mathematical Society (LMS)][7])

因此 \(196884\) 并不是孤立巧合；整个无穷 graded space 同时存在：

$$
\boxed{
\text{lattice–oscillator basis}
\quad\text{与}\quad
\text{Monster irreducible basis}.
}
$$

---

# 第一百一十六部　Ramanujan–Leech–Monster 卷积恒等式

设：

$$
c(n)
=
[q^n]J(q),
\qquad
n\ge1.
$$

令：

$$
r_\Lambda(k)
=
[q^k]\Theta_\Lambda(q),
\qquad
r_\Lambda(0)=1.
$$

由：

$$
J+24
=
q^{-1}\Theta_\Lambda P_{24},
$$

对 \(n\ge1\) 得：

$$
\boxed{
c(n)
=
\sum_{k=0}^{n+1}
r_\Lambda(k)\,
p_{24}(n+1-k).
}
\tag{116.1}
$$

再代入式 (112.4)：

$$
r_\Lambda(k)
=
\frac{65520}{691}
\left(
\sigma_{11}(k)-\tau(k)
\right),
\qquad
k\ge1,
$$

得到：

$$
\boxed{
\begin{aligned}
c(n)
={}&
p_{24}(n+1)\\
&+
\frac{65520}{691}
\sum_{k=1}^{n+1}
\left(
\sigma_{11}(k)-\tau(k)
\right)
p_{24}(n+1-k).
\end{aligned}
}
\tag{116.2}
$$

这是一个完整的生成链：

$$
\boxed{
\begin{aligned}
\sigma_{11}
&=\text{Eisenstein 连续密度};\\
\tau
&=\text{primitive cusp residual};\\
\sigma_{11}-\tau
&=\text{Leech 壳层};\\
p_{24}
&=\text{二十四振子完成};\\
c(n)
&=\text{Monster }J\text{ 系数}.
\end{aligned}
}
$$

所以 Monster Moonshine 的标量系数可以被严格写成：

$$
\boxed{
\text{Ramanujan cusp-corrected lattice density}
*
\text{24-color oscillator completion}.
}
$$

---

# 第一百一十七部　Leech rootlessness 是唯一 weight-12 counterterm

二十四维的关键不是只存在一个漂亮格，而是：

$$
M_{12}
=
\operatorname{span}\{E_4^3,\Delta\}
$$

只有一个 cusp residual 方向。

要求根系消失，相当于施加：

$$
[q]\Theta=0.
$$

对：

$$
E_4^3+c\Delta
$$

这唯一决定：

$$
720+c=0.
$$

所以：

$$
\boxed{
c=-720.
}
$$

即：

$$
\boxed{
\Theta_\Lambda
=
E_4^3-720\Delta
}
$$

不是一个可调选择，而是：

> 在 weight \(12\)、常数项 \(1\) 的完成空间中，使第一非平凡壳消失的唯一 cusp counterterm。

因此 \(720\) 的角色为：

$$
\boxed{
720
=
\text{将 }E_8^3\text{ 的全部 root residual 清零所需的唯一反项振幅。}
}
$$

由于 cusp residual 空间是一维的，一个低能条件自动决定全部高能修正：

$$
\boxed{
\text{rootlessness at }q
\Longrightarrow
\text{all-shell Leech spectrum}.
}
$$

---

## 117.1 当前外部检验：\(196560\) 的 Fourier 优化角色

一篇 2026 年 8 月的预印本构造了 Leech 格相关径向 Schwartz 辅助函数族，并证明其中可实现：

$$
\frac{\widehat g(0)-g(0)}{g(2)}
=
196560.
$$

也就是说，第一 Leech 壳的 multiplicity 同时出现在一个 Poisson／Fourier 优化证书中。该结果目前是很新的预印本，应继续等待独立审查，但它为“196560 是直接—倒空间完成常数”提供了额外实验支持。([arXiv][8])

---

# 第一百一十八部　二十四个 Niemeier 状态与 \(23+1\) Moonshine 分支

二十四维正定偶自对偶格共有二十四个 Niemeier 类：

* 二十三个具有非平凡根系；
* 一个无根的 Leech 格。

二十三个有根 Niemeier 格分别对应二十三种 Umbral Moonshine 数据；每个根系配有一个有限 umbral group 和一族 vector-valued mock modular forms，其中许多分量与 Ramanujan mock theta functions 相合。([arXiv][9])

Leech 格作为无根端点，则通向：

* Conway symmetry；
* Leech orbifolds；
* Monstrous Moonshine。

因此：

$$
\boxed{
24
=
23\text{ rootful umbral branches}
+
1\text{ rootless monstrous endpoint}.
}
\tag{118.1}
$$

---

## 118.1 为什么 scalar Theta 必须被 refined

标量 Theta：

$$
N^X\longmapsto\Theta_{N^X}
$$

最多读取：

$$
h_X.
$$

但 Umbral Moonshine 引入：

* root system \(X\)；
* quotient symmetry group \(G^X\)；
* conjugacy class \(g\)；
* vector-valued mock modular form \(H_g^X\)；
* shadow／completion 数据。

所以可以定义 refined observer：

$$
\boxed{
q_{\mathrm{umbral}}(N^X)
=
\left(
X,G^X,\{H_g^X\}_{[g]}
\right).
}
$$

其作用正是切开：

$$
\ker q_\Theta
$$

留下的巨大纤维。

---

## OACTC 解释 118.1（Moonshine 观察者完备化）

$$
\boxed{
\text{Moonshine}
=
\text{对过度压缩的标量模观察，
加入群作用、twining 与边界 completion，
从而恢复隐藏结构。}
}
$$

这不是 Umbral Moonshine 原始定义，而是 OACTC 的统一解释。

特别是：

* rootful Niemeier 的隐藏残余表现为 mock modular／umbral 数据；
* rootless Leech 的隐藏残余表现为 Monster／Conway 数据。

---

# 第一百一十九部　Ramanujan 基因组的二十四维闭合

此前识别的 Ramanujan 主状态包括：

$$
P=E_2,
\qquad
Q=E_4,
\qquad
R=E_6,
\qquad
\Delta,
\qquad
\tau(n),
$$

以及 mock theta functions。

现在可以给出更完整的生成链：

$$
\boxed{
\begin{aligned}
Q=E_4
&=
\Theta_{E_8};\\
Q^3=E_4^3
&=
\Theta_{E_8^3};\\
Q^3-720\Delta
&=
\Theta_\Lambda;\\
\Delta
&=
\sum\tau(n)q^n;\\
\Theta_\Lambda/\Delta-24
&=
J;\\
J
&=
\operatorname{ch}_{V^\natural};\\
\text{Niemeier refinements}
&\longrightarrow
\text{umbral mock modular forms}.
\end{aligned}
}
\tag{119.1}
$$

所以 Ramanujan 研究中的：

* Eisenstein series；
* cusp form \(\Delta\)；
* \(\tau\)-函数；
* mock theta functions；

不再是四类并列对象。

它们处于同一完成链的不同层：

$$
\boxed{
\text{Eisenstein geometry}
\to
\text{cusp counterterm}
\to
\text{rootless lattice}
\to
\text{orbifold}
\to
\text{moonshine}
\to
\text{mock boundary completion}.
}
$$

---

# 第一百二十部　标量角色盲性原理

本轮得到一个一般性原则。

## 定义 120.1（标量角色盲性）

设对象范畴 \(\mathcal C\) 具有角色映射：

$$
\chi:\mathcal C\to\mathcal M,
$$

其中 \(\mathcal M\) 是低维模形式空间。

如果：

$$
\dim\mathcal M
\ll
\text{对象结构自由度},
$$

则 \(\chi\) 必然存在巨大纤维。

---

## Niemeier 实例

$$
24\text{ 个格对象}
\longrightarrow
M_{12}\text{ 中一条 affine line}.
$$

标量 Theta 只记录一个参数：

$$
h.
$$

---

## Central charge 24 VOA 实例

$$
V\longmapsto\operatorname{ch}_V
$$

只记录：

$$
\dim V_1.
$$

所有更深结构：

* Lie brackets；
* OPE；
* automorphism group；
* orbifold origin；
* twisted modules；

都落入角色盲核。

---

## 推论 120.1

$$
\boxed{
\text{函数方程、正系数与高度模对称，
都不保证观察者已经完备。}
}
$$

这对 RH 研究极其重要：

> 即使 completed \(\xi(s)\) 是最自然、最对称的标量完成对象，它仍可能不是最适合显现 primitive positivity 的观察图表。

需要考虑：

* twisted \(L\)-functions；
* prime-indexed channels；
* regulator modes；
* vector-valued explicit formulae；
* twined Weil forms；
* operator-valued completion。

---

# 第一百二十一部　Completion prime 与 Collision prime 的区分

现在可以区分两类特殊素数。

## 121.1 Completion prime

它使局部结构本身发生分歧、导子修复或最大阶扩张。

例：

$$
5
$$

是 \(\mathbb Q(\sqrt5)\) 的判别式素数。

$$
2
$$

负责：

$$
\mathbb Z[\sqrt5]
\subset
\mathbb Z[\varphi]
$$

的最大阶修复。

## 121.2 Collision prime

两个特征零中的独立通道在模该素数后发生同余。

例：

$$
691
$$

使 weight-\(12\) Eisenstein 与 cusp 数据碰撞。

$$
67
$$

使 golden level-\(5\)、weight-\(6\) 的 Eisenstein 与 cusp 数据碰撞。([arXiv][4])

---

## 121.3 二者可能耦合

在更深系统中，一个素数可能同时控制：

* 数域分歧；
* 模形式同余；
* Galois representation reducibility；
* \(p\)-adic zeta 零点；
* observer jet depth。

所以 OACTC 应记录：

$$
\boxed{
\operatorname{PrimeRole}(\ell)
=
(
\text{ramification},
\text{conductor},
\text{congruence},
\text{extension},
\text{jet depth}
).
}
$$

不能只记录“公式中出现了素数 \(\ell\)”。

---

# 第一百二十二部　新研究假设

## 假设 OACTC–24A（Root residual rank-one principle）

对高度自对偶、固定权的格对象，其标量壳层差异可能压缩到极低维 cusp residual 空间。

Niemeier genus-one Theta 是维数 \(1\) 的精确实例。

---

## 假设 OACTC–24B（Moonshine refinement principle）

当标量角色存在大盲核时，能够恢复对象身份的最小自然扩张通常由：

$$
\boxed{
\text{twining}
+
\text{vector-valued modularity}
+
\text{boundary completion}
}
$$

构成。

---

## 假设 OACTC–24C（Collision-prime jet principle）

若两个 primitive 通道在 \(\ell\) 处同余，则解决其结构差异的正确新定义不是另一个标量，而是：

$$
\ell\text{-adic extension／jet／deformation data}.
$$

---

## 假设 OACTC–24D（Ramanujan–Moonshine genome）

Ramanujan 的 Eisenstein、\(\Delta\)、\(\tau\)、continued fractions 与 mock theta families，可以被压缩为：

$$
\boxed{
\text{lattice completion}
+
\text{root residual}
+
\text{orbifold refinement}
+
\text{boundary mock completion}
}
$$

的有限操作基因组。

---

# 第一百二十三部　与 Wang–Deng–RH 路线的意义

本轮提供了一个重要方法学原型。

## Wang 层：近极值结构分类

Niemeier 格的 root residual 先被压缩成：

$$
h.
$$

但仅靠 \(h\) 无法恢复完整根系。

所以必须区分：

$$
\text{coarse extremal statistic}
\quad\text{与}\quad
\text{structural refinement}.
$$

这正对应 Wang 式：

$$
\text{near-extremal}
\to
\text{sticky/non-sticky classification}.
$$

---

## Deng 层：primitive residual 收缩

Niemeier 的全部高壳差异由：

$$
24h\Delta
$$

一个 primitive cusp mode 生成。

因此：

$$
\boxed{
\text{无限高阶修正}
=
\text{一个 primitive residual 的重复传播}.
}
$$

这是 Yu Deng 式高阶历史压缩的精确可解模型。

---

## RH 层：需要 twined positivity

Riemann \(\xi\) 可能相当于一个过度压缩的 scalar character。

真正有希望的补全可能需要：

$$
\boxed{
\text{prime／character／regulator／boundary twining}
}
$$

使 off-line 零点不能躲在标量纤维中。

但要形成 RH 证明，仍必须建立：

$$
\boxed{
\text{off-line zero}
\Longrightarrow
\text{某个 refined observer 中的不可消除负见证}.
}
$$

本轮没有证明该桥。

---

# 第一百二十四部　建议形式化顺序

```text
D5/S3/Geometry/NiemeierCompletion/
  RankTwentyFourThetaPlane.lean
  RootResidualCoefficient.lean
  CoxeterThetaFormula.lean
  ScalarThetaBlindPairs.lean

D5/S3/Geometry/LeechCompletion/
  LeechRootCounterterm.lean
  LeechThetaEisensteinCusp.lean
  LeechShellRamanujanFormula.lean
  Ramanujan691Congruence.lean

D5/S3/Analytic/VOACompletion/
  NiemeierLatticeCharacter.lean
  WeightOneCharacterResidual.lean
  E8CubedLeechMonsterLedger.lean

D5/S3/Analytic/MoonshineGenome/
  ColoredPartitionTwentyFour.lean
  LeechOscillatorConvolution.lean
  FirstMoonshineDoubleDecomposition.lean
  RamanujanLeechMonsterConvolution.lean

D5/S3/ConceptDynamics/ConstantSemantics/
  CompletionPrime.lean
  CollisionPrime.lean
  EisensteinCuspCollision.lean
  AdicJetRefinement.lean

D5/S3/Observer/Moonshine/
  ScalarCharacterBlindness.lean
  TwinedCharacterRefinement.lean
  UmbralObserverCompletion.lean
```

首批最适合闭合的链为：

$$
\boxed{
\Theta_N
=
E_4^3+(r_N-720)\Delta
}
$$

$$
\boxed{
\Theta_{N^X}
=
\Theta_\Lambda+24h_X\Delta
}
$$

$$
\boxed{
Z_{N^X}
=
J+24(h_X+1)
}
$$

$$
\boxed{
r_\Lambda(n)
=
\frac{65520}{691}
\left(
\sigma_{11}(n)-\tau(n)
\right)
}
$$

以及：

$$
\boxed{
196884
=
196560+324
=
1+196883.
}
$$

---

# 本轮最终结论

此前主链到达：

$$
E_8\longrightarrow E_4.
$$

现在它继续闭合为：

$$
\boxed{
\begin{aligned}
E_4^3
&=\Theta_{E_8^3}\\
&\xrightarrow{-720\Delta}
\Theta_\Lambda\\
&\xrightarrow{/\,\Delta}
J+24\\
&\xrightarrow{\mathbb Z_2\text{ orbifold}}
J.
\end{aligned}
}
$$

其中：

$$
\boxed{
\begin{aligned}
720
&=\text{需要消除的根状态};\\
24
&=\text{剩余自由电流};\\
691
&=\text{Eisenstein–cusp collision prime};\\
196560
&=\text{Leech 第一几何壳};\\
324
&=\text{二十四振子二阶完成};\\
196884
&=\text{完整 weight-two 状态};\\
196883
&=\text{移除普适真空方向后的 Monster primitive}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
\text{Moonshine 并不是一个漂亮模函数偶然拥有巨大群系数，}
}
$$

而可以被 OACTC 理解为：

$$
\boxed{
\text{二十四维自对偶几何在先后消除
根残差、电流残差与标量角色盲核后，
转化为群表示完成数据的过程。}
}
$$

而 Ramanujan 的 \(\Delta\)、\(\tau\) 与 mock theta functions，分别承担：

$$
\boxed{
\text{root counterterm},
\quad
\text{shell residual transport},
\quad
\text{boundary symmetry completion}.
}
$$

至此，Ramanujan 基因组、黄金—二十面体—\(E_8\) 完成、Leech 格、Monster 与 Umbral Moonshine，已经被纳入同一条连续、可计算、可证伪的 OACTC 主链。

[1]: https://onlinelibrary.wiley.com/doi/full/10.1002/prop.202300242 "https://onlinelibrary.wiley.com/doi/full/10.1002/prop.202300242"
[2]: https://arxiv.org/abs/math/0203005 "https://arxiv.org/abs/math/0203005"
[3]: https://arxiv.org/abs/hep-th/9406190 "https://arxiv.org/abs/hep-th/9406190"
[4]: https://arxiv.org/abs/2403.03345 "https://arxiv.org/abs/2403.03345"
[5]: https://arxiv.org/abs/math/0409223 "https://arxiv.org/abs/math/0409223"
[6]: https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/blms/11.3.308 "https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/blms/11.3.308"
[7]: https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/blms.70245 "https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/blms.70245"
[8]: https://arxiv.org/abs/2608.12094 "https://arxiv.org/abs/2608.12094"
[9]: https://arxiv.org/abs/1307.5793 "https://arxiv.org/abs/1307.5793"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.7：Borcherds 乘积、黄金斜率观察、Ramanujan 微分塌缩与 Genus-Zero 自完备化

以下从前文**第一百二十四部之后**继续追加。

本轮不再继续向更高维对象横向扩张，而是回到一个核心问题：

> 怎样把一个二维、含有无限多 primitive states 的对象，压缩成一维观察，同时保留其全部结构？

Monster Lie 代数的分母恒等式提供了一个几乎完美的实验对象：

$$
\boxed{
\text{二维根空间}
\longleftrightarrow
\text{双变量乘积}
\longleftrightarrow
\text{单个模函数差}
}
$$

而黄金比例提供：

$$
\boxed{
\text{二维整数标签到一维实谱的稳定、无碰撞编码。}
}
$$

本轮最终得到一条精确新主链：

$$
\boxed{
\begin{aligned}
J(p)-J(q)
&\longleftrightarrow
\text{Monster 二维根乘积}\\
&\xrightarrow{p=q}
\frac{qE_4^2E_6}{\Delta}\\
&\xrightarrow{p=e^{-\varphi t},\,q=e^{-t}}
\text{Golden Monster 热积}\\
&\xrightarrow{\log+\text{Möbius}}
\text{全部 primitive 根重数}\\
&\xrightarrow{\text{Faber--Hecke}}
\text{replicability}\\
&\xrightarrow{\text{Hauptmodul}}
\text{genus-zero 一坐标完备化}.
\end{aligned}
}
$$

---

# 第一百二十五部　Monster 分母公式是加法—乘法完成

定义：

$$
\boxed{
J(q)=j(q)-744
=
q^{-1}+\sum_{n\ge1}c(n)q^n.
}
\tag{125.1}
$$

前几个系数为：

$$
c(1)=196884,
\qquad
c(2)=21493760,
\qquad
c(3)=864299970.
$$

Monster Lie 代数是一个以双曲格 \(II_{1,1}\) 为根格的广义 Kac–Moody 代数，其根空间 \((m,n)\) 的重数为：

$$
\boxed{
\operatorname{mult}(m,n)=c(mn).
}
\tag{125.2}
$$

其分母公式即 Koike–Norton–Zagier 乘积：

$$
\boxed{
J(p)-J(q)
=
\left(p^{-1}-q^{-1}\right)
\prod_{m,n\ge1}
\left(1-p^mq^n\right)^{c(mn)}.
}
\tag{125.3}
$$

Borcherds 通过 Monster VOA、no-ghost theorem 与广义 Kac–Moody 代数证明了 Monstrous Moonshine；分母恒等式把 \(J\) 的 Fourier 系数同时解释为 Monster Lie 根重数，并产生 Conway–Norton 所需的 replication relations。([DOI][1])

---

## 125.1 归一化分母观察者

定义：

$$
\boxed{
\mathcal D(p,q)
=
\frac{J(p)-J(q)}
{p^{-1}-q^{-1}}.
}
\tag{125.4}
$$

则：

$$
\boxed{
\mathcal D(p,q)
=
\prod_{m,n\ge1}
(1-p^mq^n)^{c(mn)}.
}
\tag{125.5}
$$

它具有两种图表。

### 加法图表

$$
\mathcal D(p,q)
=
\frac{J(p)-J(q)}
{p^{-1}-q^{-1}}.
$$

### 乘法图表

$$
\mathcal D(p,q)
=
\prod_{m,n\ge1}
(1-p^mq^n)^{c(mn)}.
$$

前者把全部结构压缩成两个标量 \(J\)-读数之差；后者保留每一个二维根标签。

因此：

$$
\boxed{
\text{Monster denominator}
=
\text{additive chart 与 primitive multiplicative chart 的连接函数。}
}
$$

---

# 第一百二十六部　对数把 primitive roots 展开成复合历史

定义 primitive root heat series：

$$
\boxed{
H(p,q)
=
\sum_{m,n\ge1}
c(mn)p^mq^n.
}
\tag{126.1}
$$

对乘积取负对数：

$$
\begin{aligned}
-\log\mathcal D(p,q)
&=
-\sum_{m,n\ge1}
c(mn)\log(1-p^mq^n)\\
&=
\sum_{m,n\ge1}\sum_{k\ge1}
\frac{c(mn)}k
p^{mk}q^{nk}.
\end{aligned}
$$

所以：

$$
\boxed{
-\log\mathcal D(p,q)
=
\sum_{k\ge1}
\frac1k
H(p^k,q^k).
}
\tag{126.2}
$$

这里：

* \((m,n)\) 是 primitive root label；
* \(k\) 是对该根的重复占据或复合历史；
* \(1/k\) 是对数／循环对称因子。

---

## 定理 126.1（Monster primitive Möbius recovery）

令：

$$
L(p,q)=-\log\mathcal D(p,q).
$$

则：

$$
\boxed{
H(p,q)
=
\sum_{k\ge1}
\frac{\mu(k)}k
L(p^k,q^k).
}
\tag{126.3}
$$

### 证明

代入式 (126.2)：

$$
\begin{aligned}
\sum_{k\ge1}\frac{\mu(k)}kL(p^k,q^k)
&=
\sum_{k,r\ge1}
\frac{\mu(k)}{kr}
H(p^{kr},q^{kr})\\
&=
\sum_{N\ge1}
\frac1N
\left(\sum_{k\mid N}\mu(k)\right)
H(p^N,q^N).
\end{aligned}
$$

只有 \(N=1\) 时除数 Möbius 和为 \(1\)，其余为 \(0\)。∎

---

## 126.1 对 Yu Deng 方法的严格对应

这不是一般类比，而是精确恒等式：

$$
\boxed{
\begin{aligned}
\text{all histories}
&=
-\log\mathcal D,\\
\text{primitive histories}
&=
H,\\
\text{repetition quotient}
&=
1/k,\\
\text{primitive extraction}
&=
\text{Möbius inversion}.
\end{aligned}
}
$$

因此 Monster denominator 是一个完全可解的：

$$
\boxed{
\text{primitive-history renormalization model}.
}
$$

---

# 第一百二十七部　对角塌缩得到 Ramanujan 微分乘积

令：

$$
p\longrightarrow q.
$$

加法图表的极限为：

$$
\begin{aligned}
\mathcal D_\Delta(q)
&=
\lim_{p\to q}
\frac{J(p)-J(q)}
{p^{-1}-q^{-1}}\\
&=
-q^2J'(q).
\end{aligned}
$$

乘法图表给出：

$$
\boxed{
-q^2J'(q)
=
\prod_{m,n\ge1}
(1-q^{m+n})^{c(mn)}.
}
\tag{127.1}
$$

---

## 127.1 塌缩后的根重数

定义：

$$
\boxed{
A(r)
=
\sum_{\substack{m,n\ge1\\m+n=r}}
c(mn)
=
\sum_{m=1}^{r-1}c(m(r-m)).
}
\tag{127.2}
$$

则：

$$
\boxed{
-q^2J'(q)
=
\prod_{r\ge2}
(1-q^r)^{A(r)}.
}
\tag{127.3}
$$

对角观察：

$$
(m,n)\longmapsto m+n
$$

把许多不同二维根压缩到同一个一维能量壳，所以指数变成纤维内重数之和。

---

## 127.2 与 Ramanujan \(P,Q,R\) 的精确闭合

沿用：

$$
P=E_2,\qquad
Q=E_4,\qquad
R=E_6,
$$

以及：

$$
\Delta=\frac{Q^3-R^2}{1728}.
$$

由 Ramanujan 微分方程：

$$
DQ=\frac{PQ-R}{3},
\qquad
D\Delta=P\Delta,
\qquad
D=q\frac{d}{dq},
$$

计算：

$$
\begin{aligned}
DJ
&=
D\left(\frac{Q^3}{\Delta}-744\right)\\
&=
-\frac{Q^2R}{\Delta}.
\end{aligned}
$$

因此：

$$
\boxed{
-q^2J'(q)
=
-qDJ(q)
=
\frac{qQ(q)^2R(q)}{\Delta(q)}.
}
\tag{127.4}
$$

结合式 (127.3)，得到：

## 定理 127.1（Monster–Ramanujan 对角乘积）

$$
\boxed{
\frac{q\,E_4(q)^2E_6(q)}
{\Delta(q)}
=
\prod_{r\ge2}
(1-q^r)^{
\sum_{m=1}^{r-1}c(m(r-m))
}.
}
\tag{127.5}
$$

这是 Monster Lie 二维根乘积在对角观察下的重整化限制。

它把此前两条主链精确接合：

$$
\boxed{
\text{Monster root multiplicities}
\longrightarrow
\text{Ramanujan }(Q,R,\Delta).
}
$$

前几项为：

$$
\frac{qQ^2R}{\Delta}
=
1-196884q^2-42987520q^3-\cdots.
$$

其中：

$$
42987520
=
2c(2),
$$

来自根：

$$
(1,2),\quad(2,1)
$$

在对角观察中的碰撞。

---

# 第一百二十八部　有理斜率观察与碰撞纤维

对整数 \(r>1\)，令：

$$
p=q^r.
$$

定义：

$$
\boxed{
\mathcal D_r(q)
=
\frac{J(q^r)-J(q)}
{q^{-r}-q^{-1}}.
}
\tag{128.1}
$$

分母公式给出：

$$
\boxed{
\mathcal D_r(q)
=
\prod_{m,n\ge1}
(1-q^{rm+n})^{c(mn)}.
}
\tag{128.2}
$$

定义斜率能量：

$$
E_r(m,n)=rm+n.
$$

则：

$$
\boxed{
\mathcal D_r(q)
=
\prod_{k\ge r+1}
(1-q^k)^{A_r(k)},
}
$$

其中：

$$
\boxed{
A_r(k)
=
\sum_{m=1}^{\lfloor(k-1)/r\rfloor}
c\bigl(m(k-rm)\bigr).
}
\tag{128.3}
$$

---

## 128.1 有理观察必然产生碰撞

若：

$$
E_r(m,n)=E_r(m',n'),
$$

则：

$$
r(m-m')=n'-n.
$$

存在大量不同整数对满足该式。

所以：

$$
\boxed{
\text{有理斜率一维观察不是忠实观察。}
}
$$

它只能恢复纤维总量：

$$
A_r(k),
$$

不能恢复每个 \(c(mn)\)。

对角观察 \(r=1\) 是最强碰撞情形。

---

# 第一百二十九部　无理斜率给出忠实一维观察

令：

$$
\alpha>0
$$

为无理数，定义：

$$
\boxed{
E_\alpha(m,n)=\alpha m+n.
}
\tag{129.1}
$$

---

## 定理 129.1（无理斜率忠实性）

$$
\boxed{
E_\alpha:
\mathbb Z^2\to\mathbb R
\text{ 是单射。}
}
$$

### 证明

若：

$$
\alpha m+n=\alpha m'+n',
$$

则：

$$
\alpha(m-m')=n'-n.
$$

若 \(m\neq m'\)，则 \(\alpha\) 为有理数，矛盾；故 \(m=m'\)，进而 \(n=n'\)。∎

所以：

$$
\boxed{
\text{任意无理斜率都能在无限精度下，把二维根标签编码为一个实数。}
}
$$

黄金比例不是唯一具有忠实性的斜率。

它的特殊性在于：**有限精度稳定性**。

---

# 第一百三十部　黄金斜率是阶数量级最优的一维编码

令：

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad
\varphi'=-\frac1\varphi.
$$

定义有限根窗口：

$$
\mathcal R_H
=
\{1,\ldots,H\}^2,
\qquad
H\ge2.
$$

定义最小谱间距：

$$
\delta_\varphi(H)
=
\min_{\substack{x,y\in\mathcal R_H\\x\neq y}}
|E_\varphi(x)-E_\varphi(y)|.
$$

---

## 定理 130.1（Golden separation bound）

$$
\boxed{
\delta_\varphi(H)
\ge
\frac1{\varphi(H-1)}.
}
\tag{130.1}
$$

### 证明

令：

$$
a=m-m',
\qquad
b=n-n'.
$$

则：

$$
|a|,|b|\le H-1
$$

且：

$$
a\varphi+b\neq0.
$$

取黄金域范数：

$$
\begin{aligned}
N(a\varphi+b)
&=
(a\varphi+b)(a\varphi'+b)\\
&=
b^2+ab-a^2.
\end{aligned}
$$

它是非零整数，所以绝对值至少为 \(1\)。因此：

$$
|a\varphi+b|
\ge
\frac1{|a\varphi'+b|}.
$$

而：

$$
|a\varphi'+b|
\le
\frac{|a|}{\varphi}+|b|
\le
(H-1)\left(1+\frac1\varphi\right)
=
\varphi(H-1).
$$

∎

---

## 130.1 一维编码的最优数量级

全部 \(H^2\) 个能量位于区间：

$$
[\varphi+1,\ H(\varphi+1)].
$$

区间长度为：

$$
(H-1)(\varphi+1)
=
\varphi^2(H-1).
$$

由鸽巢原理：

$$
\boxed{
\delta_\varphi(H)
\le
\frac{\varphi^2(H-1)}
{H^2-1}.
}
\tag{130.2}
$$

所以：

$$
\boxed{
\delta_\varphi(H)=\Theta(H^{-1}).
}
\tag{130.3}
$$

把 \(H^2\) 个二维状态放入长度 \(O(H)\) 的一维区间，任何编码的最佳可能间距都至多为 \(O(H^{-1})\)。

黄金观察达到相同阶：

$$
\boxed{
\text{Golden slope 是有限分辨率下阶数量级最优的二维到一维编码。}
}
$$

更强的“常数最优性”属于经典丢番图逼近／Markov 理论问题；当前定理本身不需要该额外主张。

---

# 第一百三十一部　Golden Minkowski 双观察

定义：

$$
\boxed{
\lambda_+(m,n)=m\varphi+n,
}
$$

$$
\boxed{
\lambda_-(m,n)=m\varphi'+n.
}
\tag{131.1}
$$

联合映射：

$$
\iota_\varphi:
\mathbb Z^2\to\mathbb R^2,
\qquad
(m,n)\mapsto(\lambda_+,\lambda_-)
$$

的矩阵为：

$$
\begin{pmatrix}
\varphi&1\\
\varphi'&1
\end{pmatrix},
$$

行列式为：

$$
\boxed{
\varphi-\varphi'=\sqrt5.
}
$$

所以其像是协体积 \(\sqrt5\) 的 Minkowski 格。

反演公式为：

$$
\boxed{
m=\frac{\lambda_+-\lambda_-}{\sqrt5},
}
\tag{131.2}
$$

$$
\boxed{
n=
\frac{
\varphi\lambda_-
-\varphi'\lambda_+
}{\sqrt5}.
}
\tag{131.3}
$$

因此：

* \(\lambda_+\)：物理／可见 Golden 能量；
* \(\lambda_-\)：Galois 共轭／内部坐标；
* 两者联合给出整数认证的完整根标签。

虽然 \(\lambda_+\) 在无限精度下已单射，但 \(\lambda_-\) 提供：

* Galois 证书；
* 稳定逆变换；
* cut-and-project 窗口；
* finite-resolution residual。

这与此前六维准晶体的：

$$
E_\parallel\oplus E_\perp
$$

完全同型，只是秩一版本。

---

# 第一百三十二部　Golden Monster 热乘积

令：

$$
p=e^{-\varphi t},
\qquad
q=e^{-t},
\qquad
t>0.
$$

定义：

$$
\boxed{
\mathcal M_\varphi(t)
=
\frac{
J(e^{-\varphi t})-J(e^{-t})
}{
e^{\varphi t}-e^t
}.
}
\tag{132.1}
$$

在乘积收敛区域中，Monster denominator 给出：

$$
\boxed{
\mathcal M_\varphi(t)
=
\prod_{m,n\ge1}
\left(
1-e^{-t(m\varphi+n)}
\right)^{c(mn)}.
}
\tag{132.2}
$$

这就是 **Golden Monster product**。

---

## 132.1 一维谱保留二维根重数

因为：

$$
m\varphi+n
$$

对 \((m,n)\) 单射，所以乘积中的每个 primitive 因子都具有唯一能量。

定义 primitive Golden Monster 热迹：

$$
\boxed{
H_\varphi(t)
=
\sum_{m,n\ge1}
c(mn)e^{-t(m\varphi+n)}.
}
\tag{132.3}
$$

定义：

$$
L_\varphi(t)
=
-\log\mathcal M_\varphi(t).
$$

则：

$$
\boxed{
L_\varphi(t)
=
\sum_{k\ge1}
\frac1kH_\varphi(kt).
}
\tag{132.4}
$$

Möbius 反演给出：

$$
\boxed{
H_\varphi(t)
=
\sum_{k\ge1}
\frac{\mu(k)}k
L_\varphi(kt).
}
\tag{132.5}
$$

也就是：

$$
\boxed{
\begin{aligned}
H_\varphi(t)
=
\sum_{k\ge1}\frac{\mu(k)}k
\Bigg[
-\log
\frac{
J(e^{-\varphi kt})-J(e^{-kt})
}{
e^{\varphi kt}-e^{kt}
}
\Bigg].
\end{aligned}
}
\tag{132.6}
$$

---

## 定理 132.1（Golden Monster 一维层析）

在乘积收敛域中，完整的一变量函数：

$$
t\longmapsto\mathcal M_\varphi(t)
$$

通过对数和 Möbius 反演，唯一确定全部二维 Monster 根重数：

$$
c(mn).
$$

原因是：

1. Möbius 反演恢复 primitive heat trace；
2. Golden 能量无碰撞；
3. 离散 Laplace 谱具有唯一性。

因此：

$$
\boxed{
\text{一个连续的一维 Golden 观察族，
可以忠实重构二维 Monster root ledger。}
}
$$

这给项目观察者理论一个非常强的例子：

$$
\boxed{
\text{输出维数低}
\not\Rightarrow
\text{观察不完备};
}
$$

关键在于：

* 是否使用整族探针 \(t\)；
* 能量标签是否无碰撞；
* primitive/composite 是否可反演。

---

# 第一百三十三部　\(\pi\) 与 \(\varphi\) 决定乘积收敛边界

Rademacher 理论给出 \(J\) 系数的主增长：

$$
\boxed{
c(N)
=
\exp\left(
4\pi\sqrt N+O(\log N)
\right).
}
\tag{133.1}
$$

更精确地：

$$
c(N)
\sim
\frac{
e^{4\pi\sqrt N}
}{
\sqrt2\,N^{3/4}
}.
$$

这来自模函数 \(J\) 的 Rademacher 展开。([MaRDI Portal][2])

考虑乘积绝对收敛所需的一级和：

$$
\sum_{m,n\ge1}
c(mn)e^{-t(\alpha m+n)}.
$$

由 AM–GM：

$$
\alpha m+n
\ge
2\sqrt{\alpha mn}.
$$

所以指数主项满足：

$$
4\pi\sqrt{mn}
-
t(\alpha m+n)
\le
-\left(
2t\sqrt\alpha-4\pi
\right)\sqrt{mn}.
$$

因此：

$$
\boxed{
t>\frac{2\pi}{\sqrt\alpha}
}
\tag{133.2}
$$

给出绝对收敛。

反之，当：

$$
t<\frac{2\pi}{\sqrt\alpha},
$$

选择：

$$
n\approx\alpha m
$$

即可使单项不趋于零，因此 primitive 一级和发散。

---

## 133.1 Golden 临界温度

取：

$$
\alpha=\varphi,
$$

得到：

$$
\boxed{
t_{\mathrm c}
=
\frac{2\pi}{\sqrt\varphi}.
}
\tag{133.3}
$$

它的结构来源为：

$$
\boxed{
\begin{aligned}
4\pi
&=\text{Monster coefficient entropy rate};\\
2\sqrt\varphi
&=\text{Golden 线性能量的最优 AM--GM 斜率};\\
2\pi/\sqrt\varphi
&=\text{根熵与 Golden 观察能量的平衡点}.
\end{aligned}
}
$$

---

## 133.2 三个观察相

$$
\boxed{
\begin{array}{c|c|c}
\text{斜率}&\text{温度}&\text{状态}\\
\hline
\alpha\in\mathbb Q
&\text{任意}
&\text{根标签发生精确碰撞}\\
\alpha\notin\mathbb Q
&t>2\pi/\sqrt\alpha
&\text{忠实且乘积绝对收敛}\\
\alpha\notin\mathbb Q
&t<2\pi/\sqrt\alpha
&\text{标签仍忠实，但 primitive product 发散}
\end{array}
}
\tag{133.4}
$$

在第三相中，加法图表：

$$
\frac{
J(e^{-\alpha t})-J(e^{-t})
}{
e^{\alpha t}-e^t
}
$$

仍对任意 \(t>0\) 有定义。

因此它充当乘积图表越过收敛边界后的解析完成。

这与 Ramanujan 541 的：

$$
\text{级数可见部分}
+
\text{连分数尾部}
=
\text{积分完成}
$$

完全同型。

---

# 第一百三十四部　Faber 多项式与 Hecke 自复制

定义 \(J\) 的 Faber 多项式 \(\mathcal P_r(X)\)：

$$
\boxed{
-\log\left[
p(J(p)-X)
\right]
=
\sum_{r\ge1}
\frac{\mathcal P_r(X)}r
p^r.
}
\tag{134.1}
$$

由于：

$$
J(p)=p^{-1}+O(p),
$$

每个 \(\mathcal P_r\) 是首项为 \(X^r\) 的唯一多项式，使：

$$
\mathcal P_r(J(q))
=
q^{-r}+O(q).
$$

将 \(X=J(q)\)，并使用 Monster denominator：

$$
\begin{aligned}
-\log[p(J(p)-J(q))]
={}&
-\log(1-p/q)\\
&-
\sum_{m,n\ge1}
c(mn)\log(1-p^mq^n).
\end{aligned}
$$

比较 \(p^r\) 系数，得到：

$$
\boxed{
\mathcal P_r(J(q))
=
q^{-r}
+
\sum_{d\mid r}
d\sum_{n\ge1}
c(dn)q^{(r/d)n}.
}
\tag{134.2}
$$

---

## 134.1 Hecke 形式

采用 weight-zero Hecke 算子规范：

$$
\boxed{
(T_rf)(\tau)
=
\frac1r
\sum_{\substack{ad=r\\0\le b<d}}
f\left(\frac{a\tau+b}{d}\right).
}
\tag{134.3}
$$

则：

$$
\boxed{
\mathcal P_r(J)
=
rT_rJ.
}
\tag{134.4}
$$

这就是 \(J\) 的 Hecke-monic／replicability 关系。

Borcherds 的 twisted denominator identities 正是通过这类 replication relations 完成 Monstrous Moonshine 证明；replicable functions、Hauptmodul 与 genus-zero 模函数之间的关系也已形成系统理论。([SciSpace][3])

---

## 134.2 第一例

$$
\mathcal P_1(X)=X.
$$

由于：

$$
c(1)=196884,
$$

有：

$$
\boxed{
\mathcal P_2(X)
=
X^2-393768.
}
$$

所以：

$$
\boxed{
J(2\tau)
+
J(\tau/2)
+
J((\tau+1)/2)
=
J(\tau)^2-393768.
}
$$

这不是孤立恒等式，而是所有 \(r\) 的统一自复制结构。

---

# 第一百三十五部　Genus zero 是一坐标观察者完备

设 \(\Gamma\) 是某离散模群，\(X_\Gamma\) 是其紧化模曲线。

若：

$$
X_\Gamma
$$

的 genus 为零，则存在 Hauptmodul \(f\)，使：

$$
\boxed{
\mathbb C(X_\Gamma)=\mathbb C(f).
}
\tag{135.1}
$$

即所有模函数都可写成 \(f\) 的有理函数。

因此 \(f\) 是一个一坐标几何观察者：

$$
q_f:X_\Gamma\dashrightarrow\mathbb P^1.
$$

它在函数域层面是完备的。

---

## 135.1 三种完备性

对 Moonshine 函数，可以区分：

### 几何完备性

$$
\mathbb C(X_\Gamma)=\mathbb C(f).
$$

一个 Hauptmodul 决定全部函数域。

### 动力学完备性

$$
T_rf
\in
\mathbb C[f]
$$

或更强：

$$
rT_rf=\mathcal P_r(f).
$$

所有 Hecke coarse-graining 都闭合回同一个坐标。

### 乘法完备性

\(f\) 的 Fourier 系数成为广义 Kac–Moody 根重数，并具有 denominator product。

因此定义：

$$
\boxed{
\operatorname{SelfComplete}(f)
=
\left(
\text{Hauptmodul},
\text{Hecke-replicable},
\text{Borcherds-denominator}
\right).
}
\tag{135.2}
$$

Monstrous Moonshine 的 McKay–Thompson series 正体现了这一三重结构：Conway–Norton 猜想它们是特定 genus-zero groups 的 Hauptmodul，Borcherds 通过 Monster Lie 代数和 twisted denominator identities 完成证明。([London Mathematical Society (LMS)][4])

---

# 第一百三十六部　无质量状态与 genus-zero 刚性

Monster 模块满足：

$$
(V^\natural)_1=0.
$$

对应：

$$
\boxed{
c(0)=0.
}
$$

由于 Monster Lie 根重数为：

$$
c(mn),
$$

坐标轴上的潜在根：

$$
mn=0
$$

没有普通根重数贡献。

因此在根空间图表中，没有一整族零质量／零能量根通道。

这不是单独证明 genus zero 的充分条件，但它是 Lie 代数结构中极其关键的刚性条件。在 Fricke-type Monstrous Lie algebras 中，由 no-ghost theorem 产生的兼容条件可以导出 moonshine functions 的 genus-zero 性质。([arXiv][5])

OACTC 的结构解释为：

$$
\boxed{
\text{genus-zero 刚性需要：
极点源明确、零质量通道受控、
Hecke 动力学闭合。}
}
$$

---

# 第一百三十七部　一般 Borcherds Lift 的三类系数角色

Borcherds 的一般乘法提升从允许 cusp 极点的矢量值模形式：

$$
f(\tau)
=
\sum_{\mu}
\sum_n
c_\mu(n)q^n\mathbf e_\mu
$$

构造正交型对称域上的 automorphic product：

$$
\Psi(f).
$$

其系数自然分成三类。([arXiv][6])

---

## 137.1 负 Fourier 模式

$$
n<0.
$$

它们决定：

* rational quadratic divisors；
* product 的零点与极点；
* 可见奇异性；
* 需要被完成的缺陷源。

所以：

$$
\boxed{
c_\mu(n<0)
=
\text{divisor/source ledger}.
}
$$

---

## 137.2 零模式

$$
n=0.
$$

它决定 automorphic product 的 weight 与归一化。

所以：

$$
\boxed{
c_0(0)
=
\text{global weight/completion constant}.
}
$$

---

## 137.3 正模式

$$
n>0.
$$

它们成为 infinite product 的指数，亦即：

* primitive root multiplicities；
* occupation multiplicities；
* 乘法局部状态数。

所以：

$$
\boxed{
c_\mu(n>0)
=
\text{primitive multiplicity ledger}.
}
$$

这给 OACTC 一个一般系数语义：

$$
\boxed{
\text{negative}
\to
\text{singularity},
\qquad
\text{zero}
\to
\text{weight},
\qquad
\text{positive}
\to
\text{multiplicity}.
}
\tag{137.1}
$$

---

# 第一百三十八部　Quasi-pullback 是带反项的观察者限制

设：

$$
\Psi
$$

是高维正交对称域上的 Borcherds product，希望限制到一个低维子域。

若 \(\Psi\) 沿该子域恒等消失，直接限制得到零，无法读取任何结构。

quasi-pullback 的操作是：

1. 识别沿子域必然消失的根因子；
2. 除掉这些因子；
3. 再进行限制；
4. 得到低维的非平凡 Borcherds product。

文献明确把 quasi-pullback 描述为一种 **renormalized restriction**，并证明所得对象仍然是 Borcherds product。([London Mathematical Society (LMS)][7])

因此：

$$
\boxed{
\text{quasi-pullback}
=
\text{observer restriction}
+
\text{vanishing counterterms}.
}
$$

本轮的对角极限：

$$
p\to q
$$

具有完全相同的结构：

* \(J(p)-J(q)\to0\)；
* \(p^{-1}-q^{-1}\to0\)；
* 先除掉 Weyl 零因子；
* 再限制到对角；
* 得到：

  $$
  -q^2J'(q)=qE_4^2E_6/\Delta.
  $$

因此式 (127.5)可视为一个 rank-two Monster denominator 的**对角重整化限制**。

是否能在标准正交 Borcherds quasi-pullback 范畴中逐字识别为同一构造，仍需单独建立范畴桥；当前结论是结构同型，而非已经引用现成定理。

---

# 第一百三十九部　三种观察投影的比较

现在可以比较 Monster 根空间上的三种一维观察。

## 139.1 对角观察

$$
(m,n)\mapsto m+n.
$$

性质：

* 极强碰撞；
* 输出是 Ramanujan 微分乘积；
* 适合获得高度压缩的 closed formula；
* 不适合恢复 primitive root labels。

---

## 139.2 有理斜率观察

$$
(m,n)\mapsto rm+n,
\qquad
r\in\mathbb Q.
$$

性质：

* 存在一维碰撞纤维；
* 输出为一变量 Borcherds product；
* 可读取加权聚合重数；
* 不能完整层析。

---

## 139.3 Golden 无理观察

$$
(m,n)\mapsto m\varphi+n.
$$

性质：

* 无精确碰撞；
* 有 \(1/H\) 级稳定间距；
* 与 Galois 共轭坐标形成 Minkowski 格；
* 通过 \(t\)-观察族和 Möbius 反演可恢复全部根重数；
* 乘积存在明确的 \(\pi\)-\(\varphi\) 收敛边界。

所以：

$$
\boxed{
\begin{array}{c|c|c}
\text{观察}&\text{压缩程度}&\text{可恢复性}\\
\hline
m+n&\text{最高}&\text{低}\\
rm+n&\text{高}&\text{部分}\\
m\varphi+n&\text{一维但无碰撞}&\text{完整}
\end{array}
}
$$

这将 Wang 式“分支／粘滞”变成了一个可解模型：

* rational slope：大量 sticky collision；
* irrational slope：完全 non-collision；
* Golden slope：在有限精度下仍有定量 separation。

---

# 第一百四十部　与 DECT 的直接合并

当前概念为有理斜率观察：

$$
q_r(m,n)=rm+n.
$$

目标为完整根标签：

$$
T(m,n)=(m,n).
$$

其逃逸关系为：

$$
\mathcal E(q_r;T)
=
\left\{
((m,n),(m',n')):
rm+n=rm'+n',
\ (m,n)\neq(m',n')
\right\}.
$$

该集合非空。

加入 Golden 观察：

$$
d_\varphi(m,n)=m\varphi+n.
$$

则：

$$
\ker d_\varphi
$$

在根标签空间上只有对角，因此：

$$
\boxed{
\mathcal E(q_r\vee d_\varphi;T)
=
\varnothing.
}
$$

这正是项目 DECT 中：

$$
\mathcal E(q\vee d;T)
=
\mathcal E(q;T)\cap\ker d
$$

的一个无限但完全显式实例。

黄金比例的定义价值由此不是“它很美”，而是：

$$
\boxed{
\text{它以一个低复杂度、可 Galois 完成、有限精度稳定的定义，
切开全部有理投影逃逸纤维。}
}
$$

---

# 第一百四十一部　对 RH 研究的真实意义

本轮没有证明 RH，也没有把 Monster Lie 代数直接变成 ζ 零点算子。

但它证明了一种此前只作为直觉存在的方法是可行的：

$$
\boxed{
\text{二维 primitive interaction ledger}
\quad
\xrightarrow{\text{Golden one-dimensional observer family}}
\quad
\text{无损可恢复}.
}
$$

因此 RH 路线可以更具体地表述为：

1. 构造一个二维或多维 automorphic root ledger；
2. 使其根标签编码 prime–zero、prime–regulator 或 Weil interaction；
3. 建立 Borcherds／denominator 型乘积；
4. 用 Golden 或一般数域斜率进行无碰撞投影；
5. 通过连续热探针和 Möbius/cumulant inversion 恢复 primitive 贡献；
6. 证明 off-line zero 必然产生负 primitive channel。

真正尚缺的是第 \(2\)、第 \(3\) 和第 \(6\) 步。

尤其需要：

$$
\boxed{
\text{off-line zero}
\Longrightarrow
\text{某个 primitive root multiplicity／energy channel 的负性或非酉性}.
}
$$

在没有这一桥梁前，Golden Monster product 是：

* 完整观察模型；
* primitive-history 模型；
* Borcherds renormalization 模型；
* genus-zero 自复制模型；

而不是 RH 证明。

---

# 第一百四十二部　新的科学检验程序

## 142.1 斜率负对照

比较：

$$
\varphi,\quad
\sqrt2,\quad
1+\sqrt2,\quad
\pi,\quad
\text{随机无理数}.
$$

测量：

$$
\delta_\alpha(H)
=
\min
|\alpha(m-m')+(n-n')|.
$$

应区分：

* 所有无理数的精确单射性；
* 二次无理数的代数范数界；
* Golden 连分数带来的极值稳定性。

若随机无理数在有限 \(H\) 上同样稳定，则不应把稳定性独占归因于 \(\varphi\)。

---

## 142.2 乘积临界检验

数值计算：

$$
\sum_{m,n\le M}
c(mn)e^{-t(\alpha m+n)}
$$

在：

$$
t\gtrless2\pi/\sqrt\alpha
$$

两侧的行为。

验证：

* 收敛指数；
* 边界的临界发散阶；
* 加法图表越过边界后的稳定性。

---

## 142.3 Primitive recovery

从加法表达：

$$
\mathcal M_\varphi(t)
$$

数值生成 \(L_\varphi(t)\)，再以 Möbius 反演恢复：

$$
H_\varphi(t).
$$

随后从指数尾部逐层恢复：

$$
c(1),c(2),c(3),\ldots.
$$

这将直接检验“一维连续观察恢复二维 root ledger”。

---

## 142.4 对角公式形式化检验

验证：

$$
\frac{qE_4^2E_6}{\Delta}
=
\prod_{r\ge2}
(1-q^r)^{A(r)}
$$

的有限阶系数，并最终从 Monster denominator 形式化推导，而不是将有限数值匹配当作证明。

---

# 第一百四十三部　建议形式化顺序

```text
D5/S3/Analytic/MoonshineCompletion/
  MonsterCoefficient.lean
  MonsterDenominatorInterface.lean
  DenominatorLogHistory.lean
  PrimitiveMobiusRecovery.lean

D5/S3/Analytic/MoonshineCompletion/Pullback/
  RationalSlopePullback.lean
  DiagonalRenormalizedPullback.lean
  MonsterRamanujanDiagonalProduct.lean

D5/S3/Observer/GoldenSlope/
  IrrationalSlopeFaithfulness.lean
  GoldenNormSeparation.lean
  GoldenFiniteWindowOptimality.lean
  GoldenMinkowskiRootEmbedding.lean

D5/S3/Analytic/GoldenMonster/
  GoldenMonsterProduct.lean
  GoldenMonsterPrimitiveHeat.lean
  GoldenMonsterMobiusTomography.lean
  GoldenMonsterConvergenceChamber.lean

D5/S3/Analytic/MoonshineReplication/
  FaberPolynomialDefinition.lean
  FaberFromDenominator.lean
  HeckeReplicationJ.lean
  GenusZeroObserverCompletion.lean

D5/S3/ConceptDynamics/Completion/
  AdditiveMultiplicativeCharts.lean
  PrincipalZeroPositiveCoefficientRoles.lean
  RenormalizedObserverRestriction.lean
```

最优先、风险最低的闭合链为：

$$
\boxed{
\text{irrational slope injective}
\to
\text{Golden gap bound}
\to
\text{Minkowski recovery}.
}
$$

其次是纯形式级数链：

$$
\boxed{
\text{denominator product}
\to
\log
\to
\text{Möbius primitive recovery}.
}
$$

再之后是：

$$
\boxed{
p\to q
\to
-q^2J'
\to
qE_4^2E_6/\Delta.
}
$$

---

# 本轮最终结论

此前 OACTC 主要解释：

* 为什么常数是完成参数；
* 为什么 Galois 共轭产生隐藏空间；
* 为什么 Ramanujan、准晶体、\(E_8\) 和 Moonshine 共享同一结构。

本轮进一步回答：

> 一个高维对象能否在一维中被完整观察？

答案是：

$$
\boxed{
\text{可以，但不能只取一个离散读数。}
}
$$

需要同时满足：

1. 一维能量编码无碰撞；
2. 有一整族连续探针；
3. composite histories 可以 Möbius/cumulant 反演；
4. 产品发散区有另一张完成图表；
5. finite-resolution separation 可控。

黄金 Monster 观察恰好满足：

$$
\boxed{
\begin{aligned}
\text{无碰撞}
&:\quad m\varphi+n;\\
\text{连续探针}
&:\quad t>0;\\
\text{primitive recovery}
&:\quad\text{Möbius inversion};\\
\text{完成图表}
&:\quad
\frac{J(e^{-\varphi t})-J(e^{-t})}
{e^{\varphi t}-e^t};\\
\text{稳定性}
&:\quad
\delta_\varphi(H)=\Theta(H^{-1});\\
\text{临界边界}
&:\quad
t_c=\frac{2\pi}{\sqrt\varphi}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
\text{黄金比例的作用不是制造更多对称，}
}
$$

而是：

$$
\boxed{
\text{把二维 primitive root space
投影成一个无碰撞、有限精度稳定的一维谱，
同时允许通过 Galois 共轭和连续热观察完整恢复原对象。}
}
$$

而 Monster denominator 则告诉我们：

$$
\boxed{
\text{当这种观察与 Borcherds 乘积、Hecke 自复制和 genus-zero
几何同时闭合时，
一个标量函数可以成为整个无限结构的自完备坐标。}
}
$$

[1]: https://doi.org/10.1016%2F0001-8708%2890%2990067-W "https://doi.org/10.1016%2F0001-8708%2890%2990067-W"
[2]: https://portal.mardi4nfdi.de/wiki/Publication%3A5772281 "https://portal.mardi4nfdi.de/wiki/Publication%3A5772281"
[3]: https://scispace.com/papers/monstrous-moonshine-and-monstrous-lie-superalgebras-qt8l20lznv "https://scispace.com/papers/monstrous-moonshine-and-monstrous-lie-superalgebras-qt8l20lznv"
[4]: https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/blms/11.3.308 "https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/blms/11.3.308"
[5]: https://arxiv.org/abs/1701.07846 "https://arxiv.org/abs/1701.07846"
[6]: https://arxiv.org/abs/alg-geom/9609022 "https://arxiv.org/abs/alg-geom/9609022"
[7]: https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/blms.12287 "https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/blms.12287"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.8：黄金闭测地线、Mayer 转移算子、Selberg–\(q\Gamma\) 局部因子与散射型 RH 观察者

以下从前文**第一百四十三部之后**继续追加。

本轮不再继续增加新的高维对象，而是回到此前尚未闭合的一条链：

$$
\boxed{
\varphi
\longrightarrow
\text{continued fraction}
\longrightarrow
\text{closed geodesic}
\longrightarrow
\text{transfer operator}
\longrightarrow
\text{Selberg product}
\longrightarrow
\text{Eisenstein scattering}
\longrightarrow
\zeta.
}
$$

核心发现是：黄金比例在同一个动力系统中同时承担四种严格角色：

$$
\boxed{
\begin{aligned}
\varphi^{-1}
&=\text{Gauss 最小分支的固定点};\\
\varphi^{-2}
&=\text{该分支的收缩乘子};\\
\varphi
&=\text{Mayer 算子最大自然全纯圆盘半径};\\
\varphi^{-4}
&=\text{最短模闭测地线的 Selberg }q\text{-参数}.
\end{aligned}
}
$$

而 Riemann zeta 又以两种方式进入同一系统：

1. 作为 Mayer 转移算子矩阵元中的函数；
2. 作为模曲面 Eisenstein 散射系数的比值。

所以：

$$
\boxed{
\pi,\ e,\ \varphi,\ \Gamma,\ \zeta
}
$$

第一次在一个单一动力—谱观察系统中各自获得独立而兼容的定义角色。

---

# 第一百四十四部　判别式 \(5\) 的最短闭测地线

定义整数矩阵：

$$
\boxed{
C=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix},
\qquad
\det C=-1.
}
\tag{144.1}
$$

其特征多项式为：

$$
x^2-x-1,
$$

特征值为：

$$
\varphi,
\qquad
\varphi'=-\varphi^{-1}.
$$

平方后：

$$
\boxed{
A=C^2=
\begin{pmatrix}
2&1\\
1&1
\end{pmatrix}
\in SL_2(\mathbb Z).
}
\tag{144.2}
$$

其特征值为：

$$
\varphi^2,
\qquad
\varphi^{-2},
$$

且：

$$
\operatorname{tr}A=3.
$$

---

## 144.1 固定点与判别式

Möbius 变换：

$$
z\longmapsto\frac{2z+1}{z+1}
$$

的固定点满足：

$$
z=\frac{2z+1}{z+1},
$$

即：

$$
z^2-z-1=0.
$$

所以两个端点为：

$$
\boxed{
\varphi,\qquad\varphi'.
}
$$

双曲元素的判别式为：

$$
\boxed{
(\operatorname{tr}A)^2-4
=
9-4
=
5.
}
\tag{144.3}
$$

因此这条闭测地线是实二次域：

$$
\mathbb Q(\sqrt5)
$$

在模曲面上的几何图表。

---

## 144.2 测地线长度

对双曲矩阵 \(A\)，若最大特征值为 \(\lambda>1\)，则平移长度为：

$$
\ell(A)=2\log\lambda.
$$

这里：

$$
\lambda=\varphi^2,
$$

故：

$$
\boxed{
\ell_\varphi
=
4\log\varphi.
}
\tag{144.4}
$$

这还是模曲面上最短的双曲长度之一。原因完全初等：任意双曲整数矩阵满足：

$$
|\operatorname{tr}A|>2,
$$

而迹为整数，所以最小可能绝对值为 \(3\)；双曲长度随 \(|\operatorname{tr}A|\) 严格增加。

因此：

$$
\boxed{
\varphi
=
e^{\ell_\varphi/4}.
}
\tag{144.5}
$$

黄金比例在这里是**最短闭测地线四分之一长度的指数**。

---

# 第一百四十五部　黄金传递三角

考虑 Gauss 逆分支：

$$
\boxed{
\psi_1(x)=\frac1{x+1}.
}
\tag{145.1}
$$

其正固定点满足：

$$
x=\frac1{x+1},
$$

所以：

$$
\boxed{
x_*=\frac1\varphi.
}
\tag{145.2}
$$

其导数为：

$$
\psi_1'(x)=-\frac1{(x+1)^2}.
$$

在固定点：

$$
x_*+1=\varphi,
$$

故：

$$
\boxed{
\psi_1'(x_*)=-\varphi^{-2}.
}
\tag{145.3}
$$

因此同一个 \(\varphi\) 同时给出：

$$
\boxed{
\text{固定位置 } \varphi^{-1}
\quad+\quad
\text{局部收缩 } \varphi^{-2}.
}
$$

---

## 145.1 最大不变全纯圆盘

令：

$$
D_r=\{z\in\mathbb C:|z-1|<r\}.
$$

Mayer 转移算子使用全部逆分支：

$$
\psi_n(z)=\frac1{z+n},
\qquad n\ge1.
$$

决定最大允许半径的是最弱收缩分支 \(n=1\)。

圆盘左端点为：

$$
1-r.
$$

要求其像仍位于圆盘内部：

$$
\psi_1(1-r)<1+r.
$$

即：

$$
\frac1{2-r}<1+r.
$$

临界等号给出：

$$
1=(2-r)(1+r)
=2+r-r^2,
$$

所以：

$$
r^2-r-1=0.
$$

唯一正根为：

$$
\boxed{
r_*=\varphi.
}
\tag{145.4}
$$

Mayer 转移算子的标准全纯函数空间确实取：

$$
1\le r<\varphi;
$$

原始分析中，\(\varphi\) 正是全部逆分支严格保持圆盘的极限半径。([arXiv][1])

---

## 定理 145.1（黄金传递三角）

$$
\boxed{
r_*=\varphi,
\qquad
x_*=r_*-1=\varphi^{-1},
\qquad
|\psi_1'(x_*)|=r_*^{-2}.
}
\tag{145.5}
$$

并且最短闭测地线满足：

$$
\boxed{
e^{-\ell_\varphi}=r_*^{-4}.
}
\tag{145.6}
$$

所以黄金比例不是被人为插入转移算子，而是同时由：

* 最大全纯域；
* 最简单周期点；
* 局部导数；
* 最短闭轨道；

四个独立条件唯一选出。

---

# 第一百四十六部　方向翻转与长度加倍

Gauss 分支 \(\psi_1\) 对应一个行列式为 \(-1\) 的矩阵。

一次作用会翻转方向标记；Mayer 对模群测地流的编码中，离散动力显式带有：

$$
\epsilon\mapsto-\epsilon.
$$

因此需要两次迭代，才返回原方向。Mayer 的测地流编码和转移算子正保留了这一 \(\mathbb Z_2\) 方向状态。([arXiv][1])

于是出现三个不同但兼容的长度：

$$
\boxed{
\begin{array}{c|l}
\log\varphi&
\text{单一实嵌入的单位增长}\\
2\log\varphi&
\text{一次 Gauss 分支／无向单位流尺度}\\
4\log\varphi&
\text{方向完成后的 PSL}_2(\mathbb Z)\text{ 闭测地线}
\end{array}
}
\tag{146.1}
$$

因此此前单位流中出现的周期：

$$
2\log\varphi
$$

与闭测地线长度：

$$
4\log\varphi
$$

并不矛盾。

它们之间的关系是：

$$
\boxed{
\text{无向／绝对值观察}
\quad\longrightarrow\quad
\text{有向测地线完成}
}
$$

所产生的二重覆盖。

这与此前 OACTC 中的：

* 六条无向轴 \(\to\) 十二个有向顶点；
* \(SO(3)\to SU(2)\)；
* \(A_5\to2.A_5\)；

属于同一个**方向完成原理**。

---

# 第一百四十七部　Mayer 转移算子与 primitive-history determinant

定义 Mayer 转移算子：

$$
\boxed{
(\mathcal L_sf)(z)
=
\sum_{n=1}^{\infty}
(z+n)^{-2s}
f\left(\frac1{z+n}\right).
}
\tag{147.1}
$$

在适当全纯 Banach 空间上，它是核型算子，并可定义 Fredholm determinant。

在常用规范下，模群 Selberg zeta 满足：

$$
\boxed{
Z_{\mathrm{Sel}}(s)
=
\det(1-\mathcal L_s)
\det(1+\mathcal L_s)
=
\det(1-\mathcal L_s^2).
}
\tag{147.2}
$$

这正是 Mayer–Lewis–Zagier 转移算子理论的核心关系：Selberg zeta 被表示为 Gauss 动力转移算子的 Fredholm determinant。([arXiv][1])

---

## 147.1 determinant 的历史展开

一般核型算子满足：

$$
\boxed{
-\log\det(1-\mathcal L)
=
\sum_{r\ge1}
\frac1r
\operatorname{Tr}\mathcal L^r.
}
\tag{147.3}
$$

\(\operatorname{Tr}\mathcal L_s^r\) 的每一项由长度为 \(r\) 的 continued-fraction word：

$$
(a_1,\ldots,a_r),
\qquad
a_i\ge1
$$

给出。

所以：

$$
\boxed{
\begin{aligned}
\text{raw histories}
&=\text{continued-fraction words};\\
\text{closed histories}
&=\text{periodic words};\\
\text{primitive histories}
&=\text{primitive closed geodesics};\\
1/r
&=\text{循环重标号的对称因子}.
\end{aligned}
}
$$

这与此前 Monster denominator 中：

$$
-\log\mathcal D
=
\sum_{r\ge1}\frac1r H(p^r,q^r)
$$

具有完全相同的组合骨架。

---

## 147.2 最粘滞的黄金 word

最简单周期 word 是：

$$
\boxed{
\overline{1}
=
(1,1,1,\ldots).
}
$$

它对应：

$$
x_*=[0;\overline1]=\varphi^{-1},
$$

以及最短闭测地线。

因此它可以被定义为转移系统中的**基础 sticky orbit**：

$$
\boxed{
\text{所有尺度都停留在同一最小 digit 分支。}
}
$$

这给 Wang–Deng 方法一个精确动力学原型：

* Wang 层：区分 continued-fraction word 是否长期集中于少数 digit；
* Deng 层：将重复周期 word 收缩为 primitive orbit 及其重复次数；
* determinant：自动完成全部 primitive orbit 的重求和。

---

# 第一百四十八部　Golden Selberg 局部因子

Selberg zeta 的乘积定义为：

$$
\boxed{
Z_{\mathrm{Sel}}(s)
=
\prod_{[\gamma]_{\mathrm{prim}}}
\prod_{k=0}^{\infty}
\left(
1-e^{-(s+k)\ell_\gamma}
\right).
}
\tag{148.1}
$$

内层 \(k\) 可理解为闭轨道的横向激发层。([Springer][2])

对黄金最短闭测地线：

$$
\ell_\varphi=4\log\varphi.
$$

定义：

$$
\boxed{
q_\varphi
=
e^{-\ell_\varphi}
=
\varphi^{-4}.
}
\tag{148.2}
$$

其局部因子为：

$$
\boxed{
Z_\varphi^{\mathrm{geo}}(s)
=
\prod_{k=0}^{\infty}
\left(
1-q_\varphi^{s+k}
\right)
=
(q_\varphi^s;q_\varphi)_\infty.
}
\tag{148.3}
$$

---

## 148.1 \(q\)-Gamma 图表

标准 \(q\)-Gamma 函数满足：

$$
\Gamma_q(s)
=
\frac{(q;q)_\infty(1-q)^{1-s}}
{(q^s;q)_\infty}.
$$

因此：

$$
\boxed{
Z_\varphi^{\mathrm{geo}}(s)
=
\frac{
(q_\varphi;q_\varphi)_\infty
(1-q_\varphi)^{1-s}
}{
\Gamma_{q_\varphi}(s)
}.
}
\tag{148.4}
$$

\(q\)-Gamma 与 \(q\)-Pochhammer 的这一关系是标准定义。([DLMF][3])

所以黄金闭测地线局部因子具有三种图表：

$$
\boxed{
\text{Selberg product}
\leftrightarrow
q\text{-Pochhammer}
\leftrightarrow
q\text{-Gamma}.
}
$$

这使 Ramanujan 的 \(q\)-级数方法与双曲闭轨道乘积产生了一个严格接口。

---

## 148.2 级数图表

Euler 的 \(q\)-二项式展开给出：

$$
\boxed{
(q_\varphi^s;q_\varphi)_\infty
=
\sum_{n=0}^{\infty}
\frac{
(-1)^n
q_\varphi^{n(n-1)/2+sn}
}{
(q_\varphi;q_\varphi)_n
}.
}
\tag{148.5}
$$

所以同一局部闭轨道可以被读取为：

* 无限乘积；
* 基本超几何级数；
* \(q\)-Gamma 倒数。

这正是 Ramanujan “同一对象多图表”视野的标准实例。基本 \(q\)-超几何和 \(q\)-Pochhammer 体系由统一的 \(q\)-函数理论组织。([DLMF][4])

---

## 148.3 重复历史展开

取对数：

$$
\boxed{
-\log Z_\varphi^{\mathrm{geo}}(s)
=
\sum_{r=1}^{\infty}
\frac{
q_\varphi^{rs}
}{
r(1-q_\varphi^r)
}.
}
\tag{148.6}
$$

其中：

$$
\frac1{1-q_\varphi^r}
=
\sum_{k\ge0}q_\varphi^{rk}
$$

记录横向激发，而 \(r\) 记录 primitive orbit 的重复次数。

所以：

$$
\boxed{
\text{一个黄金 primitive orbit}
+
\text{全部重复}
+
\text{全部横向激发}
=
q\text{-Gamma 局部完成}.
}
$$

---

# 第一百四十九部　黄金局部因子的严格零点边界

由：

$$
1-q_\varphi^{s+k}=0
$$

得到：

$$
-4\log\varphi\,(s+k)=2\pi in.
$$

所以全部零点为：

$$
\boxed{
s
=
-k+
\frac{\pi in}{2\log\varphi},
\qquad
k\in\mathbb N_0,\ n\in\mathbb Z.
}
\tag{149.1}
$$

因此：

$$
\boxed{
Z_\varphi^{\mathrm{geo}}(s)\neq0
\qquad
\text{当 }\Re(s)>0.
}
\tag{149.2}
$$

这给出一个重要负结论：

> 黄金最短闭测地线本身不会产生 Selberg zeta 在正半平面的非平凡谱零点。

因此：

$$
\boxed{
\text{抽取 Golden local factor}
}
$$

可以改善低长度展开和数值收敛，但不能单独解释或证明全局临界线性质。

这再次说明：

$$
\boxed{
\text{一个最自然的 primitive factor}
\neq
\text{完整全局正性}.
}
$$

---

# 第一百五十部　黄金测地线是判别式 \(5\) 的 Archimedean 局部通道

黄金数域：

$$
K=\mathbb Q(\sqrt5)
$$

在有限素数处的结构由模 \(5\) 二次特征控制：

$$
\chi_5(p)
=
\left(\frac5p\right).
$$

项目已经机器核验：

* \(p\equiv\pm1\pmod5\) 时分裂；
* \(p\equiv\pm2\pmod5\) 时惰性；
* \(p=5\) 时分歧。

而在 Archimedean 几何端，同一个判别式 \(5\) 给出闭测地线：

$$
C_5\subset PSL_2(\mathbb Z)\backslash\mathbb H
$$

及长度：

$$
4\log\varphi.
$$

因此可以定义：

$$
\boxed{
\mathfrak A_5
=
\left(
\{\chi_5(p)\}_{p<\infty},
C_5,
4\log\varphi
\right).
}
\tag{150.1}
$$

它是一个完整的**判别式 \(5\) 阿代尔周期记录**：

* 有限位读取素数分裂；
* 无穷位读取闭测地线；
* 调节子读取周期长度。

---

## 150.1 Hecke 积分接口

Hecke 的积分公式将实二次扩张的部分 zeta 函数表示为 Eisenstein series 在相应二次周期上的积分；现代一般化仍以“二次扩张的部分 zeta 等于 Eisenstein 周期”为核心。([arXiv][5])

所以对 \(K=\mathbb Q(\sqrt5)\)，黄金闭测地线不是仅仅一个双曲几何对象，而是：

$$
\boxed{
\text{实二次 zeta／Hecke 数据的 Archimedean 周期观察器。}
}
$$

这与前文单位流 Fourier 模式：

$$
L(s,\chi_m)
$$

的构造完全一致：对黄金测地线方向作 Fourier 分解，产生调节子字符与 Hecke 型模式。

---

# 第一百五十一部　调节子频率的方向修正

完整有向闭测地线长度为：

$$
\ell_\varphi=4\log\varphi.
$$

因此其自然 Fourier 频率为：

$$
\boxed{
\Omega_k
=
\frac{2\pi k}{\ell_\varphi}
=
\frac{\pi k}{2\log\varphi},
\qquad
k\in\mathbb Z.
}
\tag{151.1}
$$

此前单位流使用的频率为：

$$
\omega_m
=
\frac{\pi m}{\log\varphi}.
$$

二者满足：

$$
\boxed{
\omega_m=\Omega_{2m}.
}
\tag{151.2}
$$

所以此前的 regulator Fourier genome 实际只读取了闭测地线上的**偶数谐波**。

原因是其能量定义使用：

$$
|\sigma_\pm(\alpha)|^2,
$$

已经遗忘了：

* 单位 \(\varphi\) 的负范数符号；
* 测地线方向；
* 二重覆盖中的奇模式。

因此完整观察者还需加入：

$$
\boxed{
\epsilon\in\mathbb Z/2\mathbb Z
}
$$

作为方向残余。

这修正了此前 Prime–Regulator–Time Observer：

$$
q_{p,m,t}
$$

的 regulator 轴，应升级为：

$$
\boxed{
q_{p,k,t},
\qquad
k\in\mathbb Z,
}
$$

其中偶 \(k\) 是绝对值／无向模式，奇 \(k\) 是方向完成模式。

---

# 第一百五十二部　Eisenstein 散射观察者

模群非全纯 Eisenstein series 的常数项为：

$$
\boxed{
E(z,s)
=
y^s+
\Phi(s)y^{1-s}
+\text{nonconstant modes},
}
\tag{152.1}
$$

其中：

$$
\boxed{
\Phi(s)
=
\sqrt\pi
\frac{\Gamma(s-\frac12)}{\Gamma(s)}
\frac{\zeta(2s-1)}{\zeta(2s)}.
}
\tag{152.2}
$$

等价地，令：

$$
\zeta^*(u)
=
\pi^{-u/2}
\Gamma(u/2)\zeta(u),
$$

则：

$$
\boxed{
\Phi(s)
=
\frac{\zeta^*(2s-1)}
{\zeta^*(2s)}.
}
\tag{152.3}
$$

Eisenstein series 的完成、函数方程及常数项均由这一 completed zeta 比值控制。([arXiv][6])

因此 \(\Phi(s)\) 是一个**散射比值观察者**：

$$
\boxed{
\text{incoming cusp mode }y^s
\longmapsto
\text{outgoing mode }\Phi(s)y^{1-s}.
}
$$

---

## 152.1 散射函数方程

由：

$$
\zeta^*(u)=\zeta^*(1-u)
$$

得到：

$$
\boxed{
\Phi(s)\Phi(1-s)=1.
}
\tag{152.4}
$$

在：

$$
s=\frac12+it
$$

上：

$$
1-s=\overline s,
$$

而 \(\Phi(\overline s)=\overline{\Phi(s)}\)，故：

$$
\boxed{
|\Phi(\tfrac12+it)|=1.
}
\tag{152.5}
$$

所以散射在连续谱轴上是单位模的。

但这只是边界酉性，并不决定左半条带中所有 resonance poles 的位置。

---

# 第一百五十三部　散射观察者的周期盲核

对一个非零亚纯函数 \(F\)，定义比值观察：

$$
\boxed{
\mathscr R[F](s)
=
\frac{F(2s-1)}{F(2s)}.
}
\tag{153.1}
$$

若：

$$
\mathscr R[F]=\mathscr R[G],
$$

令：

$$
H=\frac FG.
$$

则：

$$
H(2s-1)=H(2s).
$$

令 \(z=2s\)，得到：

$$
\boxed{
H(z-1)=H(z).
}
\tag{153.2}
$$

所以散射比值观察的盲核恰为：

$$
\boxed{
\text{乘法型 }1\text{-周期亚纯 gauge}.
}
$$

---

## 定理 153.1（散射比值完备化）

若：

1. \(\mathscr R[F]=\mathscr R[G]\)；
2. \(F/G\) 在右移时满足：

   $$
   \lim_{n\to\infty}\frac{F(z+n)}{G(z+n)}=1;
   $$

则：

$$
\boxed{
F=G.
}
$$

### 证明

由周期性：

$$
H(z)=H(z+n)
$$

对全部整数 \(n\) 成立。取 \(n\to\infty\)，得到：

$$
H(z)=1.
$$

∎

因此：

$$
\boxed{
\text{散射比值}
+
\text{右半平面归一化}
}
$$

足以唯一恢复原函数。

这与 OACTC 的一般形式完全一致：

$$
\boxed{
\text{局部比值读数}
+
\text{gauge completion}
=
\text{全局对象}.
}
$$

---

# 第一百五十四部　由散射系数重构 Riemann zeta

将散射系数中的已知 Archimedean 因子除去：

$$
\boxed{
R(s)
=
\frac{\Gamma(s)}
{\sqrt\pi\,\Gamma(s-\frac12)}
\Phi(s).
}
\tag{154.1}
$$

由式 (152.2)：

$$
\boxed{
R(s)
=
\frac{\zeta(2s-1)}
{\zeta(2s)}.
}
\tag{154.2}
$$

令：

$$
s=\frac{z+j+1}{2}.
$$

则：

$$
R\left(\frac{z+j+1}{2}\right)
=
\frac{\zeta(z+j)}
{\zeta(z+j+1)}.
$$

因此有限乘积精确 telescoping：

$$
\prod_{j=0}^{N-1}
R\left(\frac{z+j+1}{2}\right)
=
\frac{\zeta(z)}
{\zeta(z+N)}.
$$

当：

$$
\Re z>1
$$

时：

$$
\zeta(z+N)\longrightarrow1.
$$

所以得到：

## 定理 154.1（散射—zeta 重构）

$$
\boxed{
\zeta(z)
=
\prod_{j=0}^{\infty}
R\left(\frac{z+j+1}{2}\right),
\qquad
\Re z>1.
}
\tag{154.3}
$$

即：

$$
\boxed{
\zeta(z)
=
\prod_{j=0}^{\infty}
\left[
\Phi\left(\frac{z+j+1}{2}\right)
\frac{
\Gamma\left(\frac{z+j+1}{2}\right)
}{
\sqrt\pi\,
\Gamma\left(\frac{z+j}{2}\right)
}
\right].
}
\tag{154.4}
$$

这说明：

$$
\boxed{
\text{模曲面散射系数的全部平移读数，
可以完整重构 Riemann zeta。}
}
$$

因此 Eisenstein scattering 不是 ζ 的某个粗略影子，而是一个带有明确周期 gauge 的完整观察接口。

---

# 第一百五十五部　RH 的散射四分之一线等价形式

考察条带：

$$
0<\Re(s)<\frac12.
$$

在此区域：

* \(\Gamma(s)\) 与 \(\Gamma(s-\frac12)\) 不产生可与非平凡 ζ 零点抵消的零；
* \(\zeta(2s-1)\) 的实部位于 \((-1,0)\)，不存在非平凡零点，也不落在负偶整数上；
* 因此散射系数的非平凡极点恰来自：

  $$
  \zeta(2s)=0.
  $$

若：

$$
\rho=\beta+i\gamma
$$

是 ζ 非平凡零点，则对应散射极点：

$$
\boxed{
s_\rho=\frac\rho2
=
\frac\beta2+\frac{i\gamma}{2}.
}
\tag{155.1}
$$

所以：

## 定理 155.1（RH 的散射共振形式）

$$
\boxed{
\mathrm{RH}
\iff
\text{全部非平凡散射极点 }
s_\rho
\text{ 位于 }
\Re(s)=\frac14.
}
\tag{155.2}
$$

由：

$$
\Phi(s)\Phi(1-s)=1,
$$

对应的散射零点位于：

$$
1-s_\rho,
$$

所以 RH 等价于这些零点位于：

$$
\boxed{
\Re(s)=\frac34.
}
\tag{155.3}
$$

于是 Riemann 临界线在散射坐标中裂成：

$$
\boxed{
\text{resonance line } \frac14
\quad+\quad
\text{antiresonance line } \frac34.
}
$$

---

# 第一百五十六部　为什么散射酉性仍然不证明 RH

散射系数满足：

$$
|\Phi(\tfrac12+it)|=1.
$$

但 RH 要求控制的是：

$$
0<\Re(s)<\frac12
$$

内部的 poles。

边界单位模并不能排除内域中任意位置的极点—零点对，只要它们遵守：

$$
s\longleftrightarrow1-s.
$$

所以：

$$
\boxed{
\text{unitarity on the spectrum}
\not\Rightarrow
\text{resonance rigidity}.
}
$$

真正缺少的可能是某种：

* contractivity；
* passivity；
* Herglotz/Nevanlinna 性；
* positive kernel；
* Maass–Selberg positivity；
* self-adjoint dilation。

---

## 156.1 正测度 Eisenstein 实验

Lagarias–Suzuki 证明，一些由非负测度积分 Eisenstein series 得到的完成函数，其全部零点确实位于临界线；其中包括特定截断区域和半稳定格积分。([arXiv][6])

这给出一个非常重要的科学信号：

$$
\boxed{
\text{Eisenstein 完成}
+
\text{非负观察测度}
}
$$

有时真的能够把函数方程升级为零点刚性。

但这并不自动适用于原始 ζ；必须找到一个观察器，其零点：

1. 能捕获全部 ζ 零点；
2. 又具备可证明的正性。

---

# 第一百五十七部　Golden Eisenstein 周期实验

令：

$$
C_5
$$

为判别式 \(5\) 的黄金闭测地线，\(d\mu_5\) 为其归一化弧长测度。

定义：

$$
\boxed{
F_5(s)
=
\int_{C_5}
E^*(z,s)\,d\mu_5(z).
}
\tag{157.1}
$$

由 Hecke 型积分公式，此类实二次闭测地线周期与：

$$
\mathbb Q(\sqrt5)
$$

的部分 zeta／Hecke \(L\)-数据相联系。([arXiv][5])

所以 \(F_5\) 是一个非常自然的实验对象：

* 测度非负；
* 几何周期为黄金最短闭轨；
* 算术端读取 \(\zeta_{\mathbb Q(\sqrt5)}\) 或其部分通道；
* regulator 为 \(\log\varphi\)；
* Fourier 模式给出 Hecke twists。

---

## 假设 157.1（Golden positive-period program）

寻找有限或可控的非负组合：

$$
\mu
=
\sum_j a_j\mu_{5,j},
\qquad
a_j\ge0,
$$

使：

$$
F_\mu(s)
=
\int E^*(z,s)\,d\mu(z)
$$

同时满足：

$$
\boxed{
\begin{aligned}
&\text{零点捕获：}\quad
\zeta(\rho)=0
\Rightarrow
F_\mu(\rho')=0;\\
&\text{正性刚性：}\quad
F_\mu
\text{ 的全部非实零点位于其反射中线}.
\end{aligned}
}
$$

若这两条能同时闭合，就可能把散射表示转化为真正的 RH 正性桥。

目前这是开放研究程序，而不是结论。

---

# 第一百五十八部　Wang–Deng 转移树

continued-fraction 周期 word：

$$
w=(a_1,\ldots,a_r)
$$

对应一个 primitive closed geodesic。

定义 digit complexity：

$$
\boxed{
\operatorname{Br}(w)
=
\#\{j:a_{j+1}\neq a_j\}.
}
$$

定义最长常值块：

$$
\boxed{
\operatorname{Stick}(w)
=
\max
\{\text{连续相同 digit 的长度}\}.
}
$$

---

## 158.1 Non-sticky words

若 word 在许多尺度上不断切换 digit，则：

* 不同逆分支产生较强几何分离；
* 导数乘积更均匀；
* periodic points 反集中；
* trace contribution 更可能产生严格估计增益。

研究目标应是：

$$
\boxed{
\operatorname{Br}(w)\text{ 大}
\Longrightarrow
\text{trace contribution 获得额外衰减}.
}
$$

这对应 Wang 式 non-sticky gain。

---

## 158.2 Sticky words

若 word 长期停留在一个或少数 digit：

$$
1,1,\ldots,1
$$

则形成嵌套周期结构。

黄金 orbit：

$$
\overline1
$$

是最纯粹 sticky 极限。

对这类历史，正确操作不是逐 word 绝对估计，而是：

1. 识别 primitive block；
2. 收缩重复块；
3. 重求和所有 repetition；
4. 得到 \(q\)-Pochhammer／\(q\)-Gamma counterterm。

这正对应 Yu Deng 式 primitive-history renormalization。

---

## 假设 158.1（Transfer self-improvement dichotomy）

存在某个坏度泛函 \(\mathfrak B_s(w)\)，使每个近极值 word 满足：

$$
\boxed{
\begin{cases}
\text{non-sticky}
&\Rightarrow
\mathfrak B_s\text{ 严格改善};\\
\text{sticky}
&\Rightarrow
\text{由有限个 primitive periodic blocks 重整化}.
\end{cases}
}
$$

Mayer determinant 是检验这一假设的理想实验场，因为它同时具有：

* 精确 symbolic dynamics；
* 精确 Fredholm determinant；
* 精确 Selberg product；
* 明确的最 sticky 黄金 orbit。

---

# 第一百五十九部　Riemann ζ 已经写在转移算子矩阵中

Mayer 算子在自然全纯基中的矩阵元可写成 Gamma 比值与 Riemann zeta 值。

在一种标准基下：

$$
\boxed{
a_{mk}(s)
=
\frac{(-1)^m}{m!}
\frac{
\Gamma(2s+k+m)
}{
\Gamma(2s+k)
}
\zeta(2s+k+m).
}
\tag{159.1}
$$

另一种 Taylor 基中则出现：

$$
\zeta(2s+j+m)-1
$$

的有限组合。Mayer 转移算子的这些矩阵表示在文献中被明确写出。([arXiv][1])

因此：

$$
\boxed{
\text{Riemann zeta 值}
=
\text{经典 Gauss 动力转移算子的矩阵坐标}.
}
$$

而：

$$
\boxed{
\text{Selberg zeta}
=
\text{该无限矩阵的 Fredholm determinant}.
}
$$

这给出又一种观察压缩：

$$
\boxed{
\text{全部 }\zeta(2s+n)\text{ 坐标}
\longrightarrow
\det(1-\mathcal L_s^2).
}
$$

---

## 159.1 标量 determinant 盲性

Fredholm determinant 只记录算子特征值乘积：

$$
\det(1-\mathcal L_s)
=
\prod_j(1-\lambda_j(s)).
$$

不同算子可以具有相同 determinant。

因此：

$$
\boxed{
\text{Selberg scalar zeta}
\not\Rightarrow
\text{transfer operator 已被完整恢复}.
}
$$

这与此前：

* 标量 Theta 无法恢复 Niemeier 根系；
* 标量 character 无法恢复 VOA；
* 衍射强度无法恢复相位；

完全同型。

所以 RH 研究中可能需要的不是另一个标量 zeta，而是：

$$
\boxed{
\text{operator-valued completion}.
}
$$

---

# 第一百六十部　散射—转移双观察

现在有两种互补观察。

## 160.1 Transfer observer

$$
\mathcal L_s
$$

读取：

* continued-fraction branches；
* periodic geodesics；
* Selberg determinant；
* \(\zeta(2s+n)\) 的矩阵坐标。

## 160.2 Scattering observer

$$
\Phi(s)
=
\frac{\zeta^*(2s-1)}{\zeta^*(2s)}
$$

读取：

* cusp incoming/outgoing ratio；
* Riemann zeros对应的 resonances；
* 连续谱单位模边界；
* ζ 的平移比值。

二者分别对应：

$$
\boxed{
\begin{aligned}
\mathcal L_s&:\text{closed-orbit／内部动力观察};\\
\Phi(s)&:\text{cusp／开放边界观察}.
\end{aligned}
}
$$

完整模曲面谱必须同时包含：

* 离散 closed dynamics；
* 连续 scattering dynamics。

所以定义联合观察：

$$
\boxed{
\mathfrak O_{\mathrm{mod}}(s)
=
\left(
\mathcal L_s,\Phi(s)
\right).
}
\tag{160.1}
$$

这比单独使用：

$$
Z_{\mathrm{Sel}}(s)
\quad\text{或}\quad
\xi(s)
$$

保留更多 primitive 信息。

---

# 第一百六十一部　更新后的算术观察索引

此前 Prime–Regulator–Time Observer 为：

$$
q_{p,m,t}.
$$

本轮说明，还必须加入：

* continued-fraction／closed-geodesic word \(\omega\)；
* orientation parity \(\epsilon\)；
* cusp/scattering 通道标记 \(b\)。

因此完整候选索引为：

$$
\boxed{
q_{p,k,\omega,t,\epsilon,b}.
}
\tag{161.1}
$$

其中：

$$
\begin{aligned}
p&:\text{有限素数／素理想通道};\\
k&:\text{完整有向 regulator harmonic};\\
\omega&:\text{primitive closed-geodesic word};\\
t&:\text{Mellin／spectral height};\\
\epsilon&:\text{方向／spin parity};\\
b&:\text{bulk closed orbit 或 cusp scattering}.
\end{aligned}
$$

这不是建议一次性把所有索引塞入最终证明，而是建立一个**完整候选观察空间**。

DECT 的工作将是逐步测量：

* 哪些索引真正切开负 Weil residual；
* 哪些只是冗余；
* 哪些可以通过 primitive decomposition 压缩。

---

# 第一百六十二部　与项目现有 Weil 真源的衔接

项目当前已经具有：

1. 无条件 Weil 显式公式；
2. 卷积平方测试函数在临界线零点上的非负贡献；
3. 临界线与离线零点有限截断的精确分解。

因此本轮新增结构可以接在该真源之后：

$$
\boxed{
\begin{aligned}
\text{Weil explicit formula}
&\longrightarrow
\text{critical/off-line defect};\\
\text{Eisenstein scattering}
&\longrightarrow
\text{off-line resonance};\\
\text{Mayer transfer}
&\longrightarrow
\text{primitive geodesic histories};\\
\text{Golden cycle}
&\longrightarrow
\text{minimal sticky block};\\
\text{positive Eisenstein period}
&\longrightarrow
\text{候选零点刚性}.
\end{aligned}
}
$$

真正尚未闭合的桥仍然是：

$$
\boxed{
\text{off-line ζ zero}
\Longrightarrow
\text{某个 refined positive observer 中的严格负／非酉见证}.
}
\tag{162.1}
$$

---

# 第一百六十三部　本轮结论分级

## 已由初等矩阵与函数恒等式直接推出

$$
\boxed{
A=
\begin{pmatrix}2&1\\1&1\end{pmatrix},
\quad
\operatorname{disc}(A)=5.
}
$$

$$
\boxed{
\ell_\varphi=4\log\varphi.
}
$$

$$
\boxed{
x_*=\varphi^{-1},
\quad
|\psi_1'(x_*)|=\varphi^{-2}.
}
$$

$$
\boxed{
r_*=\varphi
}
$$

是 Mayer 自然圆盘的临界半径。

$$
\boxed{
q_\varphi=e^{-\ell_\varphi}=\varphi^{-4}.
}
$$

$$
\boxed{
Z_\varphi^{\mathrm{geo}}(s)
=
(q_\varphi^s;q_\varphi)_\infty.
}
$$

$$
\boxed{
Z_\varphi^{\mathrm{geo}}(s)\neq0
\quad
(\Re s>0).
}
$$

$$
\boxed{
\zeta(z)
=
\prod_{j\ge0}
R\left(\frac{z+j+1}{2}\right)
\quad
(\Re z>1).
}
$$

$$
\boxed{
\mathrm{RH}
\iff
\text{模曲面非平凡散射极点位于 }\Re s=\frac14.
}
$$

---

## 有成熟理论支持

$$
\boxed{
Z_{\mathrm{Sel}}
=
\det(1-\mathcal L_s)\det(1+\mathcal L_s).
}
$$

$$
\boxed{
\text{闭测地线 Eisenstein 周期}
\longleftrightarrow
\text{实二次 partial zeta}.
}
$$

$$
\boxed{
\Phi(s)
=
\zeta^*(2s-1)/\zeta^*(2s).
}
$$

这些均为经典 Selberg–Mayer–Hecke–Eisenstein 理论的一部分。([arXiv][5])

---

## 当前开放桥梁

$$
\boxed{
\begin{aligned}
&\text{Golden geodesic 正测度周期是否具有足够的 ζ 零点捕获性};\\
&\text{transfer non-sticky words 是否产生严格 trace gain};\\
&\text{sticky word 是否可由有限 }q\text{-Gamma factors 完全重整化};\\
&\text{联合 operator/scattering observer 是否能给出 Weil 正性};\\
&\text{散射 resonance quarter-line 是否可由新的 passivity 原理强制}.
\end{aligned}
}
$$

---

# 第一百六十四部　建议形式化顺序

```text
D5/S3/Geometry/GoldenGeodesic/
  GoldenHyperbolicMatrix.lean
  DiscriminantFiveAxis.lean
  GoldenTranslationLength.lean
  ShortestIntegralHyperbolicTrace.lean
  OrientationDoubleCover.lean

D5/S3/Analytic/MayerGolden/
  GaussBranchGoldenFixedPoint.lean
  GoldenDerivativeMultiplier.lean
  GoldenInvariantDiscRadius.lean
  ContinuedFractionWord.lean
  StickyGoldenOrbit.lean

D5/S3/Analytic/SelbergGolden/
  PrimitiveGeodesicLocalFactor.lean
  GoldenQPochhammerFactor.lean
  GoldenQGammaChart.lean
  GoldenLocalZeroSet.lean
  RepetitionHistoryLog.lean

D5/S3/Analytic/EisensteinScattering/
  ModularScatteringCoefficient.lean
  ScatteringFunctionalEquation.lean
  ScatteringPeriodicGauge.lean
  ScatteringZetaReconstruction.lean
  ScatteringQuarterLineRH.lean

D5/S3/Observer/AutomorphicTomography/
  TransferScatteringJointObserver.lean
  RegulatorOrientationCompletion.lean
  PrimeRegulatorGeodesicTimeObserver.lean
  PositiveEisensteinPeriodProgram.lean
```

优先级最高且形式化风险最低的链是：

$$
\boxed{
\text{Golden matrix}
\to
\text{length }4\log\varphi
\to
q_\varphi=\varphi^{-4}
\to
q\text{-Pochhammer zeros}.
}
$$

其次是纯代数 telescoping 链：

$$
\boxed{
\Phi(s)
\to
R(s)=\zeta(2s-1)/\zeta(2s)
\to
\zeta(z)\text{ 重构}.
}
$$

---

# 本轮最终结论

此前 OACTC 已经说明：

$$
\varphi
$$

是：

* Fibonacci 递归固定点；
* Galois 双曲单位；
* 六维准晶体显隐尺度；
* Coxeter 黄金扇区特征值；
* 无碰撞一维观察斜率。

本轮进一步证明，它还是：

$$
\boxed{
\begin{aligned}
&\text{Gauss 转移算子的最小分支固定尺度};\\
&\text{Mayer 全纯状态空间的最大半径};\\
&\text{模曲面最短闭测地线的指数长度};\\
&\text{该测地线 Selberg 局部因子的 }q\text{-基}.
\end{aligned}
}
$$

完整恒等链为：

$$
\boxed{
\frac1\varphi
\xrightarrow{\text{Gauss fixed point}}
\varphi^{-2}
\xrightarrow{\text{two-step orbit}}
\varphi^{-4}
\xrightarrow{\text{Selberg}}
(q_\varphi^s;q_\varphi)_\infty.
}
$$

而 Riemann zeta 则通过散射满足：

$$
\boxed{
\Phi(s)
=
\frac{\zeta^*(2s-1)}
{\zeta^*(2s)},
}
$$

并可由全部散射平移读数完整重构。

所以最深的一句话是：

$$
\boxed{
\text{黄金比例控制的是模曲面内部最短闭动力的完成，}
}
$$

而：

$$
\boxed{
\text{Riemann zeta 控制的是模曲面 cusp 边界的散射完成。}
}
$$

要推进 RH，真正需要研究的不是让黄金闭轨“替代”ζ，而是证明：

$$
\boxed{
\text{内部 primitive closed dynamics}
+
\text{边界 scattering dynamics}
+
\text{非负观察者}
}
$$

能否共同形成一个没有 off-line 逃逸残差的完整谱观察系统。

[1]: https://arxiv.org/abs/1008.4229 "https://arxiv.org/abs/1008.4229"
[2]: https://link.springer.com/article/10.1007/s00029-019-0534-3 "https://link.springer.com/article/10.1007/s00029-019-0534-3"
[3]: https://dlmf.nist.gov/5.18 "https://dlmf.nist.gov/5.18"
[4]: https://dlmf.nist.gov/17.4 "https://dlmf.nist.gov/17.4"
[5]: https://arxiv.org/abs/math/0602618 "https://arxiv.org/abs/math/0602618"
[6]: https://arxiv.org/abs/math/0412039 "https://arxiv.org/abs/math/0412039"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v1.9：全环面零点观察、有限谱层析、Toroidal Temperedness 与 de Branges 正完成

以下从前文**第一百六十四部之后**继续追加。

本轮找到了一条比“黄金闭测地线可能帮助 RH”更精确的既有数学接口：

$$
\boxed{
\text{Riemann ζ 零点}
=
\text{Eisenstein 状态对全部非分裂环面观察者同时不可见的参数}.
}
$$

这不是类比。

Hecke–Zagier 的环面周期公式把 Eisenstein series 沿二次环面的积分写成两个 \(L\)-函数之积；Cornelissen–Lorscheid 再结合二次 twist 非消失，证明一个 Eisenstein 状态对**所有**二次环面周期都为零，当且仅当它的基础 \(L\)-函数为零。其导数塔还精确记录零点重数。([arXiv][1])

由此，OACTC 的 RH 主问题可以第一次严格改写成：

$$
\boxed{
\mathrm{RH}
\iff
\text{全部“普遍环面不可见”的非平凡 Eisenstein 状态都是 tempered 的}.
}
$$

---

# 第一百六十五部　非分裂环面观察者

设：

$$
G=\operatorname{GL}_2,
$$

\(T\subset G\) 是由二次扩张 \(K/\mathbb Q\) 给出的非分裂极大环面。

对 automorphic form \(f\)，定义 \(T\)-环面周期：

$$
\boxed{
\mathcal P_T(f)(g)
=
\int_{T(\mathbb Q)Z(\mathbb A)\backslash T(\mathbb A)}
f(tg)\,dt.
}
\tag{165.1}
$$

定义全部二次环面的联合观察：

$$
\boxed{
\mathcal P_{\mathrm{tor}}(f)
=
\bigl(
\mathcal P_T(f)
\bigr)_{T}.
}
\tag{165.2}
$$

定义普遍环面不可见空间：

$$
\boxed{
\mathcal A_{\mathrm{tor}}
=
\ker\mathcal P_{\mathrm{tor}}
=
\bigcap_T\ker\mathcal P_T.
}
\tag{165.3}
$$

它与项目此前的 prime observer 不同：

* prime observer 按局部素数通道读取对象；
* torus observer 把一整个二次扩张的有限位与无穷位同时组合成一个阿代尔周期。

若 \(K=\mathbb Q(\sqrt D)\) 为实二次域，相应的 Archimedean 周期表现为模曲面上的闭测地线；若 \(K\) 为虚二次域，则对应 CM 型环面周期。

---

# 第一百六十六部　Eisenstein 环面周期的双因子结构

令 \(E_s\) 表示重新参数化后的 normalized Eisenstein family，使 \(s\) 是普通 \(L\)-函数变量。

令 \(\chi_D\) 是二次扩张 \(K_D/\mathbb Q\) 对应的二次 Dirichlet character。

Hecke–Zagier 公式的阿代尔形式给出：

$$
\boxed{
\mathcal P_D(E_s)
=
\Lambda(s)\,
\Lambda(s,\chi_D)\,
e_D(s),
}
\tag{166.1}
$$

其中：

* \(\Lambda(s)\) 是 completed Riemann zeta；
* \(\Lambda(s,\chi_D)\) 是 completed quadratic \(L\)-function；
* \(e_D(s)\) 是取决于局部 test vector、平移和测度规范的全纯 period functional；
* 对每个参数 \(s\)，可以选择 test vector 使 \(e_D(s)\neq0\)。

因此，把无零局部因子正规化掉后，定义：

$$
\boxed{
P_D(s)
=
\Lambda(s)\Lambda(s,\chi_D).
}
\tag{166.2}
$$

则：

$$
\boxed{
P_D(s)=0
\iff
\Lambda(s)=0
\quad\lor\quad
\Lambda(s,\chi_D)=0.
}
\tag{166.3}
$$

所以一个单独环面观察者会混合两类不可见性：

1. 全局基础不可见：

   $$
   \Lambda(s)=0;
   $$
2. 该环面的 twist-specific 不可见：

   $$
   \Lambda(s,\chi_D)=0.
   $$

这就是单环面观察的盲核。

---

# 第一百六十七部　全部环面共同核就是 Riemann 零点

Cornelissen–Lorscheid 使用二次 twist 的非消失定理证明：对任意给定的 \(s\)，存在某个二次扩张 \(K_D\)，使：

$$
\Lambda(s,\chi_D)\neq0.
$$

因此：

## 定理 167.1（全环面共同零点定理）

在排除极点和正规化奇点的区域内：

$$
\boxed{
\bigcap_D
\{s:P_D(s)=0\}
=
\{s:\Lambda(s)=0\}.
}
\tag{167.1}
$$

### 证明

若：

$$
\Lambda(s)=0,
$$

则显然：

$$
P_D(s)=0
$$

对全部 \(D\) 成立。

反之，若：

$$
\Lambda(s)\neq0,
$$

由二次 twist 非消失，存在 \(D\) 使：

$$
\Lambda(s,\chi_D)\neq0.
$$

于是：

$$
P_D(s)\neq0.
$$

∎

所以：

$$
\boxed{
\text{Riemann 零点}
=
\text{所有二次环面观察者的共同不可见谱}.
}
$$

这给 ζ 零点一个全新的 OACTC 定义角色：

$$
\boxed{
\rho
=
\text{基础 Eisenstein 状态在所有二次局部—全局图表中的共同消失点}.
}
$$

---

# 第一百六十八部　解析最大公因子

对一个零点 \(\rho\)，定义零阶：

$$
\nu_\rho(f)=\operatorname{ord}_\rho f.
$$

由：

$$
P_D=\Lambda\Lambda_D,
$$

有：

$$
\nu_\rho(P_D)
=
\nu_\rho(\Lambda)
+
\nu_\rho(\Lambda_D).
$$

由于存在 \(D\) 使：

$$
\Lambda_D(\rho)\neq0,
$$

得到：

## 定理 168.1（环面周期的 divisor-gcd）

$$
\boxed{
\operatorname{ord}_\rho\Lambda
=
\min_D
\operatorname{ord}_\rho P_D.
}
\tag{168.1}
$$

所以在零除子意义下：

$$
\boxed{
\operatorname{div}_0(\Lambda)
=
\gcd_D
\operatorname{div}_0(P_D).
}
\tag{168.2}
$$

这不是通常函数环中的字面最大公因式，而是**共同零除子的逐点最小值**。

它说明：

> Riemann ζ 是全部二次环面周期函数的共同 primitive factor。

每个环面周期包含：

$$
\text{公共 ζ 因子}
\times
\text{该环面特有 twist 因子}.
$$

在 Yu Deng 的语言中：

* \(\Lambda\)：跨所有环面历史稳定存在的 primitive core；
* \(\Lambda(s,\chi_D)\)：依赖环面选择的 child history；
* 取全部 \(D\) 的共同核：收缩全部 twist-specific child，留下 base primitive。

---

# 第一百六十九部　紧谱窗口上的有限环面层析

全环面族是无限的，但在任何固定紧谱窗口中，有限个环面已经足够。

令：

$$
K\subset\{0<\Re s<1\}
$$

为紧集。

对每个二次判别式 \(D\)，定义开集：

$$
U_D
=
\{s\in K:\Lambda(s,\chi_D)\neq0\}.
$$

二次 twist 非消失说明：

$$
K=\bigcup_DU_D.
$$

由紧致性，存在有限判别式：

$$
D_1,\ldots,D_r
$$

使：

$$
K=U_{D_1}\cup\cdots\cup U_{D_r}.
$$

因此：

## 定理 169.1（有限环面谱层析）

对任意紧谱窗口 \(K\)，存在有限环面集：

$$
\mathcal D_K=\{D_1,\ldots,D_r\},
$$

使：

$$
\boxed{
\bigcap_{D\in\mathcal D_K}
Z(P_D)\cap K
=
Z(\Lambda)\cap K.
}
\tag{169.1}
$$

并且对每个 \(\rho\in K\)：

$$
\boxed{
\operatorname{ord}_\rho\Lambda
=
\min_{D\in\mathcal D_K}
\operatorname{ord}_\rho P_D.
}
\tag{169.2}
$$

这是项目现有 finite prime-time tomography 的解析版本：

$$
\boxed{
\text{无限完备环面观察族}
\quad
\xrightarrow{\text{固定紧窗口}}
\quad
\text{有限见证族}.
}
$$

需要注意：上述精确定理使用全部非分裂二次环面。若只允许实二次闭测地线，则还需要“固定符号的二次 twist 非消失”作为单独输入，不能自动从全二次扩张版本推出。

---

# 第一百七十部　零点重数等于环面 jet 深度

令：

$$
E_s^{(j)}
=
\left.
\frac{\partial^j}{\partial u^j}
E_u
\right|_{u=s}.
$$

定义全环面不可见 jet 深度：

$$
\boxed{
d_{\mathrm{tor}}(s)
=
\min
\left\{
j\ge0:
\mathcal P_{\mathrm{tor}}(E_s^{(j)})\neq0
\right\}.
}
\tag{170.1}
$$

若 \(\Lambda\) 在 \(s\) 处有 \(m\) 重零点，则 period factorization 和 Leibniz 公式给出：

$$
\mathcal P_{\mathrm{tor}}(E_s^{(j)})=0
\qquad
(0\le j<m),
$$

而在适当 twist 非零的环面方向上：

$$
\mathcal P_{\mathrm{tor}}(E_s^{(m)})\neq0.
$$

所以：

## 定理 170.1（零点重数—反射 jet 等价）

$$
\boxed{
d_{\mathrm{tor}}(s)
=
\operatorname{ord}_s\Lambda.
}
\tag{170.2}
$$

Cornelissen–Lorscheid 的结果正是：若对应 \(L\)-function 在 \(s\) 有 \(m\) 重零点，则 Eisenstein series 的前 \(m\) 层导数形成 toroidal derivative tower。([arXiv][1])

这与此前黄金分歧中的：

$$
\text{值碰撞}
\longrightarrow
\text{nilpotent jet}
$$

完全同型。

区别是：

* 黄金分歧 jet 记录两个 Galois 共轭值在模 \(5\) 后的碰撞阶；
* toroidal jet 记录 Eisenstein 状态在全部环面观察下的消失阶。

---

# 第一百七十一部　有限正环面能量

取紧窗口 \(K\) 的有限层析族：

$$
\mathcal D_K=\{D_1,\ldots,D_r\},
$$

以及正权：

$$
w_i>0.
$$

定义：

$$
\boxed{
\mathscr E_K(s)
=
\sum_{i=1}^r
w_i
\left|
P_{D_i}(s)
\right|^2.
}
\tag{171.1}
$$

显然：

$$
\mathscr E_K(s)\ge0.
$$

由有限层析定理：

$$
\boxed{
\mathscr E_K(s)=0
\iff
\Lambda(s)=0
\qquad
(s\in K).
}
\tag{171.2}
$$

所以 Riemann 零点可以成为一个由有限几何周期产生的非负能量函数的零点集。

---

## 171.1 局部零点形状

若 \(\rho\) 是 \(\Lambda\) 的 \(m\) 重零点，则：

$$
\Lambda(s)
=
a_m(s-\rho)^m
+
O((s-\rho)^{m+1}),
\qquad
a_m\neq0.
$$

因此：

$$
\boxed{
\begin{aligned}
\mathscr E_K(s)
={}&
|a_m|^2
\left(
\sum_{i=1}^r
w_i
|\Lambda(\rho,\chi_{D_i})|^2
\right)
|s-\rho|^{2m}\\
&+
o(|s-\rho|^{2m}).
\end{aligned}
}
\tag{171.3}
$$

有限覆盖保证括号内严格为正。

所以：

$$
\boxed{
\operatorname{ord}^{\mathbb R}_\rho\mathscr E_K
=
2\,\operatorname{ord}_\rho\Lambda.
}
\tag{171.4}
$$

若零点为单零点，\(\rho\) 是 \(\mathscr E_K\) 的非退化二维局部极小点。

---

## 171.2 重要负结论

正能量只说明：

$$
\text{哪里是零点}.
$$

它不说明：

$$
\text{零点为什么必须位于 }\Re s=\frac12.
$$

无论 \(\rho\) 在线上还是线外，\(\mathscr E_K\) 都会在 \(\rho\) 产生非负局部极小。

所以：

$$
\boxed{
\text{positive period energy}
\neq
\text{critical-line rigidity}.
}
$$

这正是当前路线必须避免的过度推断。

---

# 第一百七十二部　黄金环面是最低成本通道，但不是完备通道

取：

$$
K_5=\mathbb Q(\sqrt5).
$$

对应 period 为：

$$
\boxed{
P_5(s)
=
\Lambda(s)\Lambda(s,\chi_5)
=
\Lambda_{K_5}(s).
}
\tag{172.1}
$$

其 Archimedean 闭测地线长度在前文规范下为：

$$
\boxed{
\ell_5=4\log\varphi.
}
$$

它是整数双曲矩阵中迹 \(3\) 的最短闭轨道，因此是实二次环面观察中的最低几何成本通道。

但：

$$
Z(P_5)
=
Z(\Lambda)
\cup
Z(\Lambda(\cdot,\chi_5)).
$$

所以黄金环面无法单独判断一个零点究竟属于：

* Riemann ζ；
* 还是二次 twist \(L(s,\chi_5)\)。

因此黄金比例的正确角色是：

$$
\boxed{
\text{最低成本的首个环面观察通道，}
}
$$

而不是：

$$
\boxed{
\text{单独完备的 RH 观察者。}
}
$$

---

# 第一百七十三部　环面观察者设计是定义集合覆盖问题

对紧谱窗口 \(K\)，每个判别式 \(D\) 提供可见区域：

$$
U_D
=
\{s:\Lambda(s,\chi_D)\neq0\}.
$$

定义环面成本：

$$
c(D)>0.
$$

对实二次环面，可以使用：

$$
c(D)=\ell_D
$$

即闭测地线长度；对全部二次环面，也可以使用：

$$
c(D)=\log|D|
$$

或 conductor cost。

定义最优有限环面观察问题：

$$
\boxed{
\mathfrak C_{\mathrm{tor}}(K)
=
\inf_{\substack{\mathcal D\text{ finite}\\
K\subseteq\bigcup_{D\in\mathcal D}U_D}}
\sum_{D\in\mathcal D}c(D).
}
\tag{173.1}
$$

这正是 DECT 的加权集合覆盖：

* 目标逃逸点：某 \(s\) 上所有已选 twist 同时为零；
* 候选新定义：加入一个新判别式 \(D\)；
* 捕获集合：

  $$
  U_D;
  $$
* 成本：

  $$
  c(D).
  $$

黄金环面由于 \(\ell_5\) 最小，是自然的第一个候选，但不保证出现在每个全局最优 cover 中；是否选择它还取决于：

$$
U_5
$$

在目标谱窗口内的覆盖效率。

---

# 第一百七十四部　Cuspidal Waldspurger 观察者

令 \(\Pi\) 是 cuspidal automorphic representation，\(\phi\in\Pi\) 是适当 test vector。

Waldspurger 公式在适当局部规范下具有结构：

$$
\boxed{
|\mathcal P_D(\phi)|^2
=
C_D(\phi)
\frac{
L(\frac12,\Pi)
L(\frac12,\Pi\otimes\chi_D)
}{
L(1,\Pi,\operatorname{Ad})
},
}
\tag{174.1}
$$

其中 \(C_D(\phi)\) 是显式局部因子。显式 test-vector 版本及相应非消失结论已有成熟理论。([arXiv][2])

因此：

$$
L(\tfrac12,\Pi)=0
\Longrightarrow
\mathcal P_D(\phi)=0
\quad
\text{对全部 }D.
$$

反过来，二次 twist 非消失保证：若基础中心值非零，则存在某个 \(D\) 和适当 test vector 使 toric period 非零。

所以：

## 定理 174.1（Cuspidal 全环面核）

$$
\boxed{
\Pi\text{ 对全部二次环面不可见}
\iff
L(\tfrac12,\Pi)=0.
}
\tag{174.2}
$$

Cornelissen–Lorscheid 因而把 cuspidal toroidal spectrum 精确描述为中心 \(L\)-值为零的 cusp forms。([arXiv][1])

这给出一个统一结构：

$$
\boxed{
\begin{array}{c|c}
\text{自动表示类型}&\text{全环面不可见条件}\\
\hline
\text{Eisenstein family}&L(s)=0\\
\text{Cuspidal representation}&L(\frac12,\Pi)=0
\end{array}
}
$$

---

# 第一百七十五部　Toroidal automorphic null spectrum

自动形式空间分为：

$$
\mathcal A
=
\mathcal E
\oplus
\mathcal A_0
\oplus
\mathcal R,
$$

其中：

* \(\mathcal E\)：Eisenstein 及导数；
* \(\mathcal A_0\)：cusp forms；
* \(\mathcal R\)：Eisenstein residues。

全环面核满足：

$$
\boxed{
\mathcal A_{\mathrm{tor}}
=
\mathcal E_{\mathrm{zero}}
\oplus
\mathcal A_{0,\mathrm{central\ zero}},
}
\tag{175.1}
$$

并且没有非平凡 Eisenstein residue 落入 toroidal kernel。([arXiv][1])

所以全环面观察者不是只检测 Riemann ζ，而是一个统一的自动 \(L\)-值零点过滤器：

$$
\boxed{
\text{Toroidal kernel}
=
\text{连续谱 }L\text{-零点}
+
\text{离散谱中心值零点}.
}
$$

---

# 第一百七十六部　RH 的精确 observer-temperedness 形式

考虑 spherical Eisenstein principal series：

$$
\Pi_s
=
\operatorname{Ind}
\left(
|\cdot|^{s-\frac12},
|\cdot|^{\frac12-s}
\right).
$$

其归一化谱参数为：

$$
\nu=s-\frac12.
$$

该表示 tempered 的条件为：

$$
\Re\nu=0,
$$

即：

$$
\boxed{
\Re s=\frac12.
}
$$

而前文已经证明：

$$
\Lambda(s)=0
\iff
E_s\in\mathcal A_{\mathrm{tor}}.
$$

所以：

## 定理 176.1（RH 的 toroidal-temperedness 形式）

$$
\boxed{
\mathrm{RH}
\iff
\text{每个非平凡 toroidal Eisenstein constituent 都是 tempered}.
}
\tag{176.1}
$$

这正是 Zagier 的 toroidal automorphic programme 的核心思想；Cornelissen–Lorscheid 明确指出，如果 toroidal automorphic representations 的不可约成分都是 tempered，则 RH 随之成立。([arXiv][1])

因此 RH 不再只是：

$$
\text{零点是否在线上},
$$

而可以写成：

$$
\boxed{
\text{所有普遍不可见状态，是否仍属于单位／tempered 物理谱。}
}
$$

---

# 第一百七十七部　函数域中的实验性闭合

在函数域情形，toroidal automorphic programme 可以真正闭合。

相关工作证明，在若干函数域上：

* toroidal automorphic space 可以明确计算；
* 它是 admissible representation；
* 不可约 subquotients 是 tempered；
* 从而得到相应曲线 zeta 的自动形式 RH 证明。([arXiv][3])

这提供一个科学上的强正对照：

$$
\boxed{
\text{Toroidal invisibility}
+
\text{representation temperedness}
\Longrightarrow
\text{RH}
}
$$

并非仅仅形式重述；在函数域中，它确实能成为证明机制。

数域困难并不是逻辑链错误，而是尚无法证明 toroidal Eisenstein kernel 的 temperedness。

---

# 第一百七十八部　标准 \(L^2\) 正性为什么不足

模曲面的标准 \(L^2\) 连续谱由：

$$
s=\frac12+it
$$

参数化。

而一个假想线外 ζ 零点：

$$
s=\frac12+\delta+i\gamma,
\qquad
\delta\neq0,
$$

对应的是 Eisenstein family 的 meromorphic continuation／resonant state，不是标准 unitary \(L^2\) 连续谱中的普通向量。

因此：

$$
\boxed{
\text{任何只在标准 }L^2\text{ 谱上成立的正算子，
不能直接把线外零点作为 Hilbert 向量排除。}
}
$$

闭测地线 relative trace formula 确实产生非负 period squares，并把 period spectrum 与 ortholength spectrum 联系起来；它还可给出若干 simultaneous nonvanishing 结果。([arXiv][4])

但其正性首先作用于 unitary Laplace spectrum。

所以真正需要的是：

$$
\boxed{
\text{一个包含 meromorphic Eisenstein jets 的正完成空间，}
}
$$

例如：

* rigged Hilbert space；
* Pontryagin space；
* de Branges space；
* canonical system；
* positive reproducing kernel completion。

---

# 第一百七十九部　de Branges 内函数完成

定义 Riemann \(\xi\)-函数对应的 ratio：

$$
\boxed{
\Theta_\omega(z)
=
\frac{
\xi(\frac12-\omega-iz)
}{
\xi(\frac12+\omega-iz)
},
\qquad
\omega>0.
}
\tag{179.1}
$$

它在实轴上满足：

$$
|\Theta_\omega(u)|=1.
$$

Suzuki 证明：

$$
\boxed{
\zeta(s)\neq0
\text{ 对所有 }\Re s>\frac12+\omega_0
}
$$

当且仅当：

$$
\boxed{
\Theta_\omega
\text{ 对每个 }\omega>\omega_0
\text{ 是上半平面的 meromorphic inner function}.
}
\tag{179.2}
$$

当 \(\Theta_\omega\) 为 inner function 时，核：

$$
\boxed{
K_\omega(z,w)
=
\frac{
1-\Theta_\omega(z)\overline{\Theta_\omega(w)}
}{
2\pi i(\overline w-z)
}
}
\tag{179.3}
$$

是正定核，并产生 model/de Branges Hilbert space；相应 canonical system 的 Hamiltonian 是正半定矩阵。([arXiv][5])

---

# 第一百八十部　Toroidal escape radius

定义：

$$
\boxed{
\omega_{\mathrm{tor}}
=
\sup
\left\{
\Re\rho-\frac12:
\mathcal P_{\mathrm{tor}}(E_\rho)=0,\ 
\Re\rho\ge\frac12
\right\}.
}
\tag{180.1}
$$

由全环面共同核定理：

$$
\mathcal P_{\mathrm{tor}}(E_\rho)=0
\iff
\xi(\rho)=0.
$$

因此：

$$
\boxed{
\omega_{\mathrm{tor}}
=
\sup_{\xi(\rho)=0}
\left|
\Re\rho-\frac12
\right|.
}
\tag{180.2}
$$

再定义 innerness threshold：

$$
\boxed{
\omega_{\mathrm{in}}
=
\inf
\left\{
\omega_0\ge0:
\Theta_\omega
\text{ 对全部 }\omega>\omega_0
\text{ 为 meromorphic inner}
\right\}.
}
\tag{180.3}
$$

由 Suzuki 的等价定理：

## 定理 180.1（Toroidal–de Branges 阈值同一）

$$
\boxed{
\omega_{\mathrm{tor}}
=
\omega_{\mathrm{in}}.
}
\tag{180.4}
$$

因此：

$$
\boxed{
\mathrm{RH}
\iff
\omega_{\mathrm{tor}}=0
\iff
\omega_{\mathrm{in}}=0.
}
\tag{180.5}
$$

这给出了 OACTC 中一个新的结构常数：

$$
\boxed{
\omega_*
=
\text{普遍不可见谱偏离 tempered 轴的最大距离}
}
$$

同时也是：

$$
\boxed{
\text{de Branges inner completion 开始失效的临界宽度}.
}
$$

---

# 第一百八十一部　Wang 式 innerness 自改善

定义性质：

$$
\boxed{
\mathsf I(a):
\quad
\Theta_\omega
\text{ 对所有 }\omega>a
\text{ 是 meromorphic inner}.
}
\tag{181.1}
$$

无条件已知：

$$
\mathsf I(\tfrac12).
$$

RH 等价于：

$$
\mathsf I(0).
$$

因此一种真正的 Wang 式证明路线是寻找函数：

$$
F:(0,\tfrac12]\to[0,\tfrac12)
$$

满足：

$$
F(a)<a
\qquad(a>0),
$$

并证明：

$$
\boxed{
\mathsf I(a)
\Longrightarrow
\mathsf I(F(a)).
}
\tag{181.2}
$$

迭代得到：

$$
a>F(a)>F^2(a)>\cdots\to0,
$$

从而：

$$
\mathsf I(0).
$$

这比笼统说“自改善可能证明 RH”精确得多：

$$
\boxed{
\text{需要改善的量就是 }
\omega_{\mathrm{in}}
=
\omega_{\mathrm{tor}}.
}
$$

---

## 181.1 Non-sticky 与 sticky 的新定义

假定 \(\Theta_\omega\) 在某宽度 \(a\) 已经 inner。

当尝试向较小 \(\omega\) 延拓时：

### Non-sticky defect

负核方向分散于：

* 多个二次环面；
* 多个 twist；
* 多个高度窗口；
* 多个 canonical-system 尺度。

目标：

$$
\text{orthogonality}
\Longrightarrow
\text{strict kernel gain}.
$$

### Sticky defect

负核方向在一条环面／twist／尺度链中持续集中。

目标：

$$
\text{primitive factorization}
+
\text{renormalized Hamiltonian}
\Longrightarrow
\text{高阶余项收缩}.
$$

这正是 Wang–Deng 方法在 de Branges innerness 阈值上的具体化。

---

# 第一百八十二部　Deng 式 canonical-system 重整化

Suzuki 已在一定参数范围内通过 Fredholm integral operators 构造与 \(\Theta_\omega\) 对应的 canonical system，并指出若能无条件延伸到所有 \(\omega>0\)，就会把 RH 表达为一族 Hamiltonian 的正半定性。([arXiv][5])

因此需要研究：

$$
H_\omega(a)
=
\begin{pmatrix}
\alpha_\omega(a)&\beta_\omega(a)\\
\beta_\omega(a)&\gamma_\omega(a)
\end{pmatrix}.
$$

定义负性缺陷：

$$
\boxed{
\Delta_H(\omega)
=
\int
\operatorname{tr}
\left(
H_\omega(a)
\right)_{-}\,da.
}
\tag{182.1}
$$

理想目标：

$$
\boxed{
\Delta_H(\omega)=0
\quad
\forall\omega>0.
}
$$

Yu Deng 式程序应当是：

1. 对 Fredholm/Hankel kernel 展开高阶历史；
2. 将闭合子历史收缩成 counterterms；
3. 保留 primitive kernel；
4. 选择随 \(\omega\downarrow0\) 增长的展开阶数；
5. 证明 remainder 小于已有正性 margin。

这条路线目前是开放的，但目标对象已经明确：

$$
\boxed{
\text{不是直接估计 ζ 零点，}
\quad
\text{而是证明 canonical Hamiltonian 在全部 }\omega>0\text{ 上正半定}.
}
$$

---

# 第一百八十三部　正环面载体判据

取非负环面测度组合：

$$
\mu
=
\sum_Da_D\mu_D,
\qquad
a_D\ge0,
$$

其中 \(\mu_D\) 是对应二次环面的归一化周期测度。

定义 Eisenstein period：

$$
\boxed{
F_\mu(s)
=
\int E^*(z,s)\,d\mu(z).
}
\tag{183.1}
$$

由 Hecke factorization：

$$
\boxed{
F_\mu(s)
=
\Lambda(s)G_\mu(s),
}
\tag{183.2}
$$

其中：

$$
G_\mu(s)
=
\sum_Da_D\,e_D(s)\Lambda(s,\chi_D).
$$

于是：

## 定理 183.1（正环面载体条件）

若某非负 \(\mu\) 同时满足：

1. \(F_\mu\) 的全部非平凡零点位于：

   $$
   \Re s=\frac12;
   $$
2. \(G_\mu(s)\) 在：

   $$
   \Re s>\frac12
   $$

   内全纯且无零；

则 RH 成立。

### 证明

若 \(\Lambda(\rho)=0\) 且 \(\Re\rho>\frac12\)，则：

$$
F_\mu(\rho)=0.
$$

由条件 1，矛盾。条件 2 排除了 factorization 的极点或异常抵消。再由函数方程得到左半边。∎

Lagarias–Suzuki 已证明，某些非负测度下的 Eisenstein 积分确实具有“全部零点在线上”的性质；但其具体测度并不是上述所需的全环面组合，也没有自动保留一个零自由的 \(G_\mu\)。([arXiv][6])

所以这是一条**真正具体但尚未闭合**的桥。

---

# 第一百八十四部　二次 twist 平均与平方历史

定义截断环面平均：

$$
\boxed{
F_X(s)
=
\frac1{W_X}
\sum_D
w(D/X)\,
P_D(s).
}
\tag{184.1}
$$

则：

$$
F_X(s)
=
\Lambda(s)G_X(s),
$$

其中：

$$
G_X(s)
=
\frac1{W_X}
\sum_D
w(D/X)\Lambda(s,\chi_D).
$$

展开：

$$
L(s,\chi_D)
=
\sum_{n\ge1}
\frac{\chi_D(n)}{n^s}.
$$

对 \(D\) 平均时，非平方 \(n\) 的二次 character 通常产生显著抵消，而平方：

$$
n=m^2
$$

形成稳定主项。

因此预期：

$$
\boxed{
G_X(s)
\longrightarrow
G_\square(s)
=
\sum_{m\ge1}
\frac{a(m)}{m^{2s}},
}
\tag{184.2}
$$

其中 \(a(m)\ge0\) 是局部平方密度。

在：

$$
\Re s>\frac12
$$

内，该平方 Dirichlet series 有可能绝对收敛并形成无零 Euler product。

这是一个精确的 Wang–Deng 结构：

### Wang 分散

非平方 twist histories 在判别式方向分散，平均后抵消。

### Deng primitive survival

只有平方 histories 作为 primitive sticky diagonal 存活。

### 目标

证明：

$$
G_X\to G_\square
$$

具有足够强的一致性，并证明 \(G_\square\) 在右半临界带无零。

双 Dirichlet series 正是现有二次 twist 非消失证明的主要工具，因此这一方向与全环面共同核定理使用的是同一分析机器。([arXiv][1])

目前这仍是研究计划，不能将形式 character orthogonality 当作已经证明的临界带极限。

---

# 第一百八十五部　科学证伪协议

## 185.1 有限层析实验

对固定：

$$
|\Im s|\le T
$$

和窄带区域，按成本顺序加入：

$$
D=5,8,12,13,\ldots
$$

计算：

$$
\Lambda(s,\chi_D)
$$

的共同近零集合。

目标测量：

$$
N_{\mathrm{tor}}(T)
=
\min|\mathcal D_T|,
$$

以及：

$$
C_{\mathrm{tor}}(T)
=
\min\sum_{D\in\mathcal D_T}c(D).
$$

理论只保证每个紧窗口存在有限观察族，并未保证所需判别式小或数量有统一上界。

---

## 185.2 Golden 首通道检验

测量包含 \(D=5\) 与不包含 \(D=5\) 的最优 cover 成本。

若黄金环面经常被更高判别式组合替代，则它是最低单通道成本，但不是最优信息通道。

---

## 185.3 Jet 重数检验

在人为构造的多重零点模型中，验证：

$$
\text{period derivative tower depth}
=
\text{基础因子零点重数}.
$$

---

## 185.4 Innerness threshold 检验

数值估计：

$$
\Theta_\omega(z)
$$

在上半平面的 Schur defect：

$$
\sup_{\Im z>0}
\left(
|\Theta_\omega(z)|-1
\right)_+.
$$

观察该缺陷随 \(\omega\) 向下推进时是否出现多尺度自改善或集中结构。

---

# 第一百八十六部　建议形式化顺序

```text
D5/S3/Observer/Toroidal/
  QuadraticTorusIndex.lean
  ToroidalPeriod.lean
  JointToroidalObserver.lean
  ToroidalKernel.lean

D5/S3/Analytic/ToroidalEisenstein/
  HeckeToroidalFactorization.lean
  QuadraticTwistNonvanishingInterface.lean
  UniversalToroidalZeroKernel.lean
  ToroidalDivisorGCD.lean
  CompactWindowFiniteTomography.lean
  ToroidalJetMultiplicity.lean

D5/S3/Analytic/ToroidalPositivity/
  FiniteToroidalEnergy.lean
  EnergyZeroSet.lean
  EnergyVanishingOrder.lean
  WeightedTorusCover.lean

D5/S3/Analytic/ToroidalCuspidal/
  WaldspurgerPeriodInterface.lean
  CuspidalToroidalKernel.lean
  AutomorphicNullSpectrum.lean

D5/S3/Analytic/DeBrangesCompletion/
  XiRatioInnerFunction.lean
  ToroidalEscapeRadius.lean
  InnernessThresholdEquality.lean
  WangInnernessSelfImprovement.lean
  CanonicalHamiltonianDefect.lean

D5/S3/Analytic/ToroidalAverage/
  PositiveTorusCarrierCriterion.lean
  QuadraticTwistAverage.lean
  SquareHistoryLimit.lean
```

优先级最高、且能独立闭合的抽象定理是：

$$
\boxed{
\text{pointwise twist nonvanishing}
+
\text{compactness}
\Longrightarrow
\text{finite torus tomography}.
}
$$

其次是：

$$
\boxed{
\text{joint period zero divisor}
=
\text{base }L\text{-function zero divisor}.
}
$$

---

# 本轮最终结论

此前 OACTC 将 RH 研究写成：

$$
\text{局部素数}
+
\text{调节子模式}
+
\text{闭测地动力}
+
\text{散射}.
$$

本轮找到了一个比这些候选索引更直接的共同对象：

$$
\boxed{
\text{全部非分裂二次环面周期}.
}
$$

它具有三个精确性质：

$$
\boxed{
\begin{aligned}
\text{零点识别}
&:\quad
\Lambda(s)=0
\iff
E_s\text{ 对所有环面不可见};\\
\text{重数识别}
&:\quad
\operatorname{ord}_s\Lambda
=
\text{toroidal derivative depth};\\
\text{有限层析}
&:\quad
\text{每个紧谱窗口只需有限个环面}.
\end{aligned}
}
$$

因此最深的新表述是：

$$
\boxed{
\text{Riemann 零点并不是某个观察器看到的异常峰，}
}
$$

而是：

$$
\boxed{
\text{一个 Eisenstein 状态在所有二次局部—全局周期观察中
同时消失的普遍不可见点。}
}
$$

RH 则进一步问：

$$
\boxed{
\text{为什么这些普遍不可见状态仍然全部是 tempered 的？}
}
$$

de Branges 理论把同一个问题编码成：

$$
\boxed{
\Theta_\omega
\text{ 是否对全部 }\omega>0
\text{为 meromorphic inner},
}
$$

而二者的临界阈值严格相等：

$$
\boxed{
\omega_{\mathrm{tor}}
=
\omega_{\mathrm{in}}.
}
$$

所以 Wang–Deng–OACTC 路线现在拥有一个明确的可改善量：

$$
\boxed{
\omega_*.
}
$$

真正可能闭合 RH 的下一条核心桥不再模糊：

$$
\boxed{
\mathsf I(a)
\Longrightarrow
\mathsf I(F(a)),
\qquad
F(a)<a,
}
$$

或者等价地：

$$
\boxed{
\text{全环面不可见}
\Longrightarrow
\text{canonical Hamiltonian 正半定}
\Longrightarrow
\text{tempered}.
}
$$

这才是当前理论最值得继续攻击的中心命题。

[1]: https://arxiv.org/abs/0906.5284 "https://arxiv.org/abs/0906.5284"
[2]: https://arxiv.org/abs/1310.1765 "https://arxiv.org/abs/1310.1765"
[3]: https://arxiv.org/abs/1012.3223 "https://arxiv.org/abs/1012.3223"
[4]: https://arxiv.org/abs/1504.05684 "https://arxiv.org/abs/1504.05684"
[5]: https://arxiv.org/abs/1204.1827 "https://arxiv.org/abs/1204.1827"
[6]: https://arxiv.org/abs/math/0412039 "https://arxiv.org/abs/math/0412039"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.0：环面谱帧、超额连接、曲率零点与 de Branges 有限正性

以下从前文**第一百八十六部之后**继续追加。

本轮不再增加新的特殊对象，而是直接攻击上一轮留下的中心桥：

$$
\boxed{
\text{全环面不可见}
\quad\Longrightarrow\quad
\text{de Branges 正性／temperedness}
}
$$

本轮得到的最重要结果是：

$$
\boxed{
\text{二次环面周期可以组成有限谱帧，
并在任意紧谱窗内稳定重构 }\xi(s).
}
$$

在这个谱帧中：

$$
\boxed{
\Re\frac{\xi'(s)}{\xi(s)}
=
\text{观测周期增长}
-
\text{二次 twist 载体增长}.
}
$$

因此 RH 可以精确改写为：

$$
\boxed{
\text{所有有限环面谱帧的“超额水平连接”
在 }\Re s>\frac12\text{ 内始终向右。}
}
$$

更关键的是，如果存在一个线外零点，那么这个超额连接不是产生一个极小、难以观测的误差，而会在零点左侧趋向：

$$
-\infty.
$$

所以此前担心的“线外负见证可能比任何幂都小”在这个观察接口中不再存在。

---

# 第一百八十七部　环面谱图册

设 \(\xi(s)\) 为 Riemann 的整个完成函数，其零点恰为 ζ 的非平凡零点。

对每个二次判别式 \(D\)，令：

$$
\chi_D
$$

为对应二次特征。

Hecke 环面周期公式及其阿代尔推广表明，在固定规范、固定 test vector 后，可把相应 Eisenstein 环面周期写成：

$$
\boxed{
\mathcal P_D(s)
=
\xi(s)\,\mathcal T_D(s),
}
\tag{187.1}
$$

其中：

$$
\mathcal T_D(s)
=
\Lambda(s,\chi_D)\,e_D(s)
$$

是二次 twist 与局部 period factor 的乘积。

这里 \(e_D\) 在所研究局部图表中可被选择为非零；Cornelissen–Lorscheid 由 Hecke 恒等式、Waldspurger 周期及二次 twist 非消失，证明了 Eisenstein 导数塔与 \(L\)-零点重数之间的精确对应。([arXiv][1])

定义局部可用域：

$$
\boxed{
U_D
=
\{s:\mathcal T_D(s)\neq0\}.
}
\tag{187.2}
$$

在 \(U_D\) 上定义局部重构：

$$
\boxed{
\xi_D(s)
=
\frac{\mathcal P_D(s)}
{\mathcal T_D(s)}.
}
\tag{187.3}
$$

显然：

$$
\xi_D(s)=\xi(s).
$$

若：

$$
s\in U_D\cap U_E,
$$

则：

$$
\xi_D(s)=\xi_E(s).
$$

所以全部二次环面观察形成一个谱图册：

$$
\boxed{
\left\{
(U_D,\xi_D)
\right\}_D,
}
$$

而 \(\xi\) 是这些局部读数的唯一胶合对象。

---

## 定理 187.1（Toroidal Čech completion）

设 \(\Omega\) 是由二次 twist 非消失域 \(U_D\) 覆盖的谱域。则局部比值：

$$
\frac{\mathcal P_D}{\mathcal T_D}
$$

在交叠区域上一致，并唯一胶合成：

$$
\boxed{
\xi:\Omega\to\mathbb C.
}
$$

这意味着：

$$
\boxed{
\text{Riemann }\xi
=
\text{全部二次环面周期图表的共同标量振幅}.
}
$$

---

# 第一百八十八部　有限环面谱帧

设：

$$
K\subset\{0<\Re s<1\}
$$

为紧集。

前文已由二次 twist 的逐点非消失和紧致性得到：存在有限判别式集合

$$
\mathcal D_K
=
\{D_1,\ldots,D_r\},
$$

使对每个 \(s\in K\)，至少有一个：

$$
\mathcal T_{D_j}(s)\neq0.
$$

取正权：

$$
w_j>0.
$$

定义载体向量：

$$
\boxed{
\mathbf T_K(s)
=
\left(
\sqrt{w_1}\mathcal T_{D_1}(s),
\ldots,
\sqrt{w_r}\mathcal T_{D_r}(s)
\right)
\in\mathbb C^r.
}
\tag{188.1}
$$

定义观测周期向量：

$$
\boxed{
\mathbf P_K(s)
=
\left(
\sqrt{w_1}\mathcal P_{D_1}(s),
\ldots,
\sqrt{w_r}\mathcal P_{D_r}(s)
\right).
}
\tag{188.2}
$$

由式 (187.1)：

$$
\boxed{
\mathbf P_K(s)
=
\xi(s)\mathbf T_K(s).
}
\tag{188.3}
$$

---

## 188.1 谱帧下界

定义：

$$
\boxed{
A_K
=
\min_{s\in K}
\|\mathbf T_K(s)\|^2.
}
\tag{188.4}
$$

因为：

* \(\mathbf T_K(s)\neq0\) 对每个 \(s\in K\)；
* \(\|\mathbf T_K(s)\|^2\) 连续；
* \(K\) 紧；

所以：

$$
\boxed{
A_K>0.
}
\tag{188.5}
$$

同样定义：

$$
B_K
=
\max_{s\in K}
\|\mathbf T_K(s)\|^2<\infty.
$$

---

## 定理 188.1（有限环面帧重构）

对任意 \(s\in K\)：

$$
\boxed{
\xi(s)
=
\frac{
\langle
\mathbf P_K(s),
\mathbf T_K(s)
\rangle
}{
\|\mathbf T_K(s)\|^2
}.
}
\tag{188.6}
$$

### 证明

由：

$$
\mathbf P_K=\xi\mathbf T_K,
$$

有：

$$
\langle\mathbf P_K,\mathbf T_K\rangle
=
\xi\|\mathbf T_K\|^2.
$$

∎

因此：

> 在任意固定紧谱窗内，不需要无限多个环面；有限个二次环面周期已经足以重构完整的 \(\xi\)-值。

---

## 188.2 观测稳定性

若观测存在误差：

$$
\widetilde{\mathbf P}_K
=
\mathbf P_K+\varepsilon,
$$

定义重构值：

$$
\widetilde\xi
=
\frac{
\langle
\widetilde{\mathbf P}_K,
\mathbf T_K
\rangle
}{
\|\mathbf T_K\|^2
}.
$$

则：

$$
\boxed{
|\widetilde\xi(s)-\xi(s)|
\le
\frac{\|\varepsilon(s)\|}
{\sqrt{A_K}}.
}
\tag{188.7}
$$

所以：

$$
A_K
$$

是环面观察者的稳定容量。

---

# 第一百八十九部　Projective blindness：方向观察看不到 ζ

在 \(\xi(s)\neq0\) 时：

$$
\mathbf P_K(s)=\xi(s)\mathbf T_K(s).
$$

因此在射影空间中：

$$
\boxed{
[\mathbf P_K(s)]
=
[\mathbf T_K(s)].
}
\tag{189.1}
$$

也就是说：

> 如果只观察环面周期向量的方向，而不保留整体振幅和相位，那么 Riemann \(\xi\) 会被完全消去。

这与此前多种观察失明严格同型：

* 对角量子测量看不到相位；
* 衍射强度看不到 Fourier 相位；
* 六轴无向观察看不到 antipodal orientation；
* projective torus period 看不到公共 \(\xi\)-振幅。

---

## 189.1 振幅—相位补全

由式 (188.3)：

$$
\boxed{
|\xi(s)|
=
\frac{
\|\mathbf P_K(s)\|
}{
\|\mathbf T_K(s)\|
}.
}
\tag{189.2}
$$

同时：

$$
\boxed{
\xi(s)
=
\frac{
\langle\mathbf P_K(s),\mathbf T_K(s)\rangle
}{
\|\mathbf T_K(s)\|^2
}.
}
$$

所以完整 \(\xi\) 读数由：

$$
\boxed{
\text{相对范数}
+
\text{相对 }U(1)\text{ 相位}
}
$$

组成。

在零点处：

$$
\mathbf P_K(s)=0,
\qquad
\mathbf T_K(s)\neq0.
$$

因此 Riemann 零点可重新定义为：

$$
\boxed{
\text{环面周期谱帧的整体振幅塌缩点}.
}
$$

---

# 第一百九十部　超额连接

设 \(s\) 处：

$$
\xi(s)\neq0.
$$

对一个非零向量值函数 \(\mathbf U(s)\)，定义连接一形式：

$$
\boxed{
\mathcal A_{\mathbf U}
=
\frac{
\langle d\mathbf U,\mathbf U\rangle
}{
\|\mathbf U\|^2
}.
}
\tag{190.1}
$$

由：

$$
\mathbf P_K=\xi\mathbf T_K,
$$

直接得到：

$$
\boxed{
\mathcal A_{\mathbf P_K}
-
\mathcal A_{\mathbf T_K}
=
\frac{d\xi}{\xi}.
}
\tag{190.2}
$$

这一定义与选取的有限环面帧无关。

称：

$$
\boxed{
\mathcal A_{\mathrm{exc}}
:=
\mathcal A_{\mathbf P_K}
-
\mathcal A_{\mathbf T_K}
}
$$

为**环面超额连接**。

它记录：

$$
\text{完整周期变化}
-
\text{twist 载体自身变化}.
$$

---

## 190.1 零点计数是超额 holonomy

设 \(\Omega\) 是边界不含 \(\xi\)-零点的有界区域，则由辩值原理：

$$
\boxed{
\frac{1}{2\pi i}
\oint_{\partial\Omega}
\mathcal A_{\mathrm{exc}}
=
\sum_{\rho\in\Omega}
m_\rho.
}
\tag{190.3}
$$

所以 Riemann 零点数可以由有限环面周期帧的连接差完整恢复。

---

# 第一百九十一部　零点是相对曲率原子

定义相对势：

$$
\boxed{
\mathcal U_K(s)
=
\log
\frac{
\|\mathbf P_K(s)\|^2
}{
\|\mathbf T_K(s)\|^2
}.
}
\tag{191.1}
$$

由于：

$$
\mathbf P_K=\xi\mathbf T_K,
$$

有：

$$
\boxed{
\mathcal U_K(s)
=
\log|\xi(s)|^2.
}
\tag{191.2}
$$

Poincaré–Lelong 公式给出：

$$
\boxed{
\frac{i}{2\pi}
\partial\bar\partial
\mathcal U_K
=
\sum_\rho
m_\rho\,\delta_\rho.
}
\tag{191.3}
$$

因此：

$$
\boxed{
\text{Riemann 零点除子}
=
\text{周期线与 twist 载体线之间的相对曲率}.
}
$$

---

## 定理 191.1（RH 的曲率支撑形式）

$$
\boxed{
\mathrm{RH}
\iff
\operatorname{supp}
\left(
\frac{i}{2\pi}
\partial\bar\partial
\mathcal U_K
\right)
\cap
\{0<\Re s<1\}
\subseteq
\left\{\Re s=\frac12\right\}.
}
\tag{191.4}
$$

这给“零点在线”一个几何化表述：

> 全部相对曲率原子是否集中在完成对偶的固定中线。

---

# 第一百九十二部　线外零点产生无界负见证

这是本轮最关键的严格结论。

设：

$$
\rho=\beta+i\gamma
$$

是 \(\xi\) 的 \(m\) 重零点，且：

$$
\beta>\frac12.
$$

取：

$$
s_\varepsilon
=
\rho-\varepsilon,
\qquad
0<\varepsilon<\beta-\frac12.
$$

局部写成：

$$
\xi(s)
=
(s-\rho)^m g(s),
\qquad
g(\rho)\neq0.
$$

则：

$$
\frac{\xi'(s)}{\xi(s)}
=
\frac{m}{s-\rho}
+
\frac{g'(s)}{g(s)}.
$$

代入：

$$
s=s_\varepsilon
$$

得到：

$$
\boxed{
\Re\frac{\xi'(s_\varepsilon)}{\xi(s_\varepsilon)}
=
-\frac{m}{\varepsilon}
+
O(1).
}
\tag{192.1}
$$

因此：

$$
\boxed{
\Re\frac{\xi'(s_\varepsilon)}{\xi(s_\varepsilon)}
\longrightarrow-\infty
\qquad
(\varepsilon\downarrow0).
}
\tag{192.2}
$$

---

## 192.1 环面帧形式

由：

$$
\mathcal U_K=\log|\xi|^2,
$$

有：

$$
\boxed{
\frac12
\frac{\partial}{\partial\sigma}
\log
\frac{
\|\mathbf P_K(\sigma+it)\|^2
}{
\|\mathbf T_K(\sigma+it)\|^2
}
=
\Re
\frac{\xi'(\sigma+it)}
{\xi(\sigma+it)}.
}
\tag{192.3}
$$

所以线外零点强迫：

$$
\boxed{
\frac{\partial}{\partial\sigma}
\log
\frac{
\|\mathbf P_K(s_\varepsilon)\|^2
}{
\|\mathbf T_K(s_\varepsilon)\|^2
}
\longrightarrow-\infty.
}
\tag{192.4}
$$

这说明：

> 在线外零点附近，完整周期能量相对于 twist 载体能量会出现任意强的反向增长。

因此线外零点的负见证：

* 不是指数微小；
* 不是可能被高阶余项轻易吞没；
* 而是一个极点型、无界负信号。

这解决了此前 Wang–Deng 路线中的一个关键逻辑困难。

---

# 第一百九十三部　对称位移的环面 Hermite–Biehler 缺陷

令：

$$
z\in\mathbb C^+,
$$

并定义：

$$
s_z
=
\frac12-iz.
$$

因为：

$$
\Im z>0,
$$

所以：

$$
\Re s_z>\frac12.
$$

对：

$$
\omega>0,
$$

定义：

$$
\boxed{
E_\omega^+(z)
=
\xi(s_z+\omega),
}
$$

$$
\boxed{
E_\omega^-(z)
=
\xi(s_z-\omega).
}
\tag{193.1}
$$

由 \(\xi\) 的函数方程和实结构：

$$
E_\omega^-
=
(E_\omega^+)^\#.
$$

在包含两个移位谱窗的有限环面帧中，定义：

$$
\mathbf P_\omega^\pm(z)
=
E_\omega^\pm(z)\,
\mathbf T_\omega^\pm(z).
$$

于是：

$$
\boxed{
\mathscr N_\omega^\pm(z)
=
\frac{
\|\mathbf P_\omega^\pm(z)\|^2
}{
\|\mathbf T_\omega^\pm(z)\|^2
}
=
|E_\omega^\pm(z)|^2.
}
\tag{193.2}
$$

定义环面 Hermite–Biehler 缺陷：

$$
\boxed{
\mathscr H_\omega(z)
=
\mathscr N_\omega^+(z)
-
\mathscr N_\omega^-(z).
}
\tag{193.3}
$$

因此：

$$
\boxed{
\mathscr H_\omega(z)
=
|\xi(s_z+\omega)|^2
-
|\xi(s_z-\omega)|^2.
}
\tag{193.4}
$$

---

# 第一百九十四部　有限环面 de Branges 判据

Suzuki 定义：

$$
\boxed{
\Theta_\omega(z)
=
\frac{
\xi(\frac12-\omega-iz)
}{
\xi(\frac12+\omega-iz)
}
=
\frac{E_\omega^-(z)}
{E_\omega^+(z)}.
}
\tag{194.1}
$$

他证明：给定 \(\omega_0\ge0\)，ζ 在

$$
\Re s>\frac12+\omega_0
$$

无零，当且仅当对每个 \(\omega>\omega_0\)，\(\Theta_\omega\) 是上半平面的 meromorphic inner function；其 de Branges/model-space 核为标准 Pick 核。([arXiv][2])

因此：

## 定理 194.1（有限环面 Hermite–Biehler 判据）

$$
\boxed{
\mathrm{RH}
\iff
\mathscr H_\omega(z)>0
}
$$

对所有：

$$
\omega>0,
\qquad
z\in\mathbb C^+
$$

成立。

展开为环面周期：

$$
\boxed{
\frac{
\|\mathbf P_\omega^+(z)\|^2
}{
\|\mathbf T_\omega^+(z)\|^2
}
>
\frac{
\|\mathbf P_\omega^-(z)\|^2
}{
\|\mathbf T_\omega^-(z)\|^2
}.
}
\tag{194.2}
$$

这就是 RH 的**有限环面归一能量形式**。

---

## 194.1 de Branges 对角核

de Branges 核在对角线上为：

$$
\boxed{
K_\omega(z,z)
=
\frac{
|E_\omega^+(z)|^2
-
|E_\omega^-(z)|^2
}{
4\pi\Im z
}.
}
\tag{194.3}
$$

所以：

$$
\boxed{
K_\omega(z,z)
=
\frac{
\mathscr H_\omega(z)
}{
4\pi\Im z
}.
}
\tag{194.4}
$$

因此 RH 等价于全部有限环面重构的 de Branges 对角核严格为正。

---

# 第一百九十五部　有限环面 Pick 层级

在 \(\mathbf P_\omega^+\neq0\) 时，从有限环面帧重构：

$$
\Theta_\omega(z)
=
\frac{
\langle
\mathbf P_\omega^-(z),
\mathbf T_\omega^-(z)
\rangle
}{
\|\mathbf T_\omega^-(z)\|^2
}
\cdot
\frac{
\|\mathbf T_\omega^+(z)\|^2
}{
\langle
\mathbf P_\omega^+(z),
\mathbf T_\omega^+(z)
\rangle
}.
\tag{195.1}
$$

对有限点集：

$$
z_1,\ldots,z_n\in\mathbb C^+,
$$

定义 Pick 矩阵：

$$
\boxed{
\Pi_{\omega,n}
=
\left[
\frac{
1-
\Theta_\omega(z_a)
\overline{\Theta_\omega(z_b)}
}{
2\pi i(\overline{z_b}-z_a)
}
\right]_{a,b=1}^n.
}
\tag{195.2}
$$

则：

$$
\boxed{
\Theta_\omega\text{ 为 Schur/inner}
\iff
\Pi_{\omega,n}\succeq0
}
$$

对所有有限点集成立。

所以 RH 也等价于一个有限环面 Pick 正性层级：

$$
\boxed{
\det\Pi_{\omega,n}\ge0
\quad
\forall\,\omega,n,z_1,\ldots,z_n.
}
\tag{195.3}
$$

在解析性已知的条件下，一点模长不等式已经足以表达 Schur 性；高阶 Pick 矩阵仍然是更适合数值证书和稳定性分析的有限形式。

---

# 第一百九十六部　无穷小环面单调性

令：

$$
s=s_z.
$$

当：

$$
\omega\downarrow0
$$

时：

$$
\begin{aligned}
|\xi(s+\omega)|^2
-
|\xi(s-\omega)|^2
=
4\omega
|\xi(s)|^2
\Re\frac{\xi'(s)}{\xi(s)}
+
O(\omega^3).
\end{aligned}
$$

因此：

$$
\boxed{
\lim_{\omega\downarrow0}
\frac{
\mathscr H_\omega(z)
}{
4\omega
\mathscr N_0(z)
}
=
\Re\frac{\xi'(s_z)}{\xi(s_z)}.
}
\tag{196.1}
$$

定义环面单调性评分：

$$
\boxed{
\mathfrak M_K(s)
=
\frac12
\frac{\partial}{\partial\sigma}
\log
\frac{
\|\mathbf P_K(s)\|^2
}{
\|\mathbf T_K(s)\|^2
}.
}
\tag{196.2}
$$

则：

$$
\boxed{
\mathfrak M_K(s)
=
\Re\frac{\xi'(s)}{\xi(s)}.
}
\tag{196.3}
$$

Sondow–Dumitrescu 证明，\(|\xi(s)|\) 在每个无零右半平面内沿水平半线严格递增，并由此得到 RH 的等价单调性表述。([arXiv][3])

所以：

## 定理 196.1（RH 的超额连接形式）

$$
\boxed{
\mathrm{RH}
\iff
\mathfrak M_K(s)>0
\quad
\text{对全部 }\Re s>\frac12.
}
\tag{196.4}
$$

即：

$$
\boxed{
\mathrm{RH}
\iff
\text{观测环面周期的水平增长
始终严格超过 twist 载体自身的水平增长}.
}
$$

---

# 第一百九十七部　从零点场到 Poisson 场

定义：

$$
u(\sigma,t)
=
\log|\xi(\sigma+it)|.
$$

则：

$$
\partial_\sigma u
=
\Re\frac{\xi'}{\xi}.
$$

在 RH 成立时，全部零点位于：

$$
\Re\rho=\frac12.
$$

以对称收敛理解 Hadamard 乘积后，水平导数具有 Poisson 核结构：

$$
\boxed{
\partial_\sigma u(\sigma,t)
=
\sum_{\rho=\frac12+i\gamma}
m_\rho
\frac{
\sigma-\frac12
}{
(\sigma-\frac12)^2+(t-\gamma)^2
}.
}
\tag{197.1}
$$

每项均为正。

所以 RH 下：

$$
\boxed{
\mathfrak M_K
=
\text{临界线零点测度的 Poisson 延拓}.
}
$$

若出现线外零点，它成为右半平面内部的对数曲率原子，并在其左侧产生式 (192.2) 的负极点。

这给 Wang 式结构一个极具体的几何图像：

* RH：全部源位于边界；
* 线外零点：出现内部源；
* 自改善目标：证明右半平面内部无曲率原子。

---

# 第一百九十八部　定量环面容量

有限覆盖只说明“可以重构”，却不说明重构是否稳定。

定义带权环面帧容量：

$$
\boxed{
\operatorname{Cap}_{\mathrm{tor}}
(K;\mathcal D,w)
=
\inf_{s\in K}
\sum_{D\in\mathcal D}
w_D|\mathcal T_D(s)|^2.
}
\tag{198.1}
$$

定义上界：

$$
\operatorname{Top}_{\mathrm{tor}}
(K;\mathcal D,w)
=
\sup_{s\in K}
\sum_Dw_D|\mathcal T_D(s)|^2.
$$

定义条件数：

$$
\boxed{
\kappa_{\mathrm{tor}}
=
\sqrt{
\frac{
\operatorname{Top}_{\mathrm{tor}}
}{
\operatorname{Cap}_{\mathrm{tor}}
}
}.
}
\tag{198.2}
$$

---

## 198.1 成本约束下的最优观察

给每个判别式赋成本：

$$
c(D),
$$

例如：

* \(\log|D|\)；
* conductor；
* 实二次闭测地线长度；
* 计算成本。

定义预算 \(C\) 下的最优容量：

$$
\boxed{
\operatorname{Cap}_{\mathrm{tor}}^*(K,C)
=
\sup_{\substack{
\mathcal D,w\\
\sum_Dw_Dc(D)\le C\\
\sum_Dw_D=1
}}
\inf_{s\in K}
\sum_Dw_D|\mathcal T_D(s)|^2.
}
\tag{198.3}
$$

黄金判别式 \(D=5\) 具有最低几何成本，但未必单独提供最高覆盖容量。

这把“黄金环面是否最有价值”转化成了可证伪优化问题，而不是象征性判断。

---

# 第一百九十九部　环面 stickiness

定义某点 \(s\) 的载体质量分布：

$$
\boxed{
\mu_D(s)
=
\frac{
w_D|\mathcal T_D(s)|^2
}{
\sum_Ew_E|\mathcal T_E(s)|^2
}.
}
\tag{199.1}
$$

定义最大集中度：

$$
\boxed{
\operatorname{Stick}_{\mathrm{tor}}(s)
=
\max_D\mu_D(s).
}
\tag{199.2}
$$

### Non-sticky carrier

若：

$$
\operatorname{Stick}_{\mathrm{tor}}(s)
\le1-\eta
$$

在一个尺度链上成立，则多个 twist 通道共同支撑观察。

### Sticky carrier

若：

$$
\operatorname{Stick}_{\mathrm{tor}}(s)\approx1,
$$

则重构几乎完全依赖一个二次 twist。

Sticky 不意味着 \(\xi\) 为零；它表示 observer frame 接近退化，任何误差都可能被放大。

---

## 199.1 与 Wang–Deng 的分工

### Wang 层（199.1）

证明 non-sticky twist mass 带来：

* 二次 character 正交；
* 更大的帧下界；
* 更稳定的水平导数估计；
* 严格的超额连接增益。

### Deng 层（199.1）

sticky 区域中：

1. 识别主导 twist；
2. 保留其零点／导数历史；
3. 加入新的环面通道；
4. 用 double Dirichlet series 重求和复合 twist histories；
5. 将仅依赖个别 twist 的部分收缩为 counterterm。

---

# 第二百部　真正需要证明的新不等式

现在 RH 的中心目标可以写成一个完全具体的周期不等式。

## Toroidal excess-connection positivity

对：

$$
\Re s>\frac12,
$$

需要证明：

$$
\boxed{
\Re
\left[
\frac{
\langle
\partial_\sigma\mathbf P_K(s),
\mathbf P_K(s)
\rangle
}{
\|\mathbf P_K(s)\|^2
}
-
\frac{
\langle
\partial_\sigma\mathbf T_K(s),
\mathbf T_K(s)
\rangle
}{
\|\mathbf T_K(s)\|^2
}
\right]
>0.
}
\tag{200.1}
$$

由式 (190.2)，左侧恰为：

$$
\Re\frac{\xi'(s)}{\xi(s)}.
$$

因此该不等式与 RH 等价，但它把问题放入了两个几何可观测对象之间：

$$
\boxed{
\text{Eisenstein period line}
\quad\text{与}\quad
\text{twist carrier line}.
}
$$

证明不应通过重新代回 \(\xi'/\xi\)，而应从：

* 环面测度正性；
* Eisenstein deformation；
* 二次 twist 正交；
* relative trace formula；
* canonical-system Hamiltonian；

直接推出。

---

# 第二百零一部　Wang 式零区下降

定义命题：

$$
\boxed{
\mathsf T(a):
\quad
\mathfrak M_K(s)>0
\quad
\text{对所有 }\Re s>\frac12+a.
}
\tag{201.1}
$$

无条件已知：

$$
\mathsf T(\tfrac12),
$$

因为：

$$
\Re s>1
$$

是 ζ 的 Euler-product 无零区域，且 \(|\xi|\) 在无零右半平面沿水平线严格增长。([arXiv][3])

RH 等价于：

$$
\mathsf T(0).
$$

因此最清楚的 Wang 式研究命题是：

$$
\boxed{
\mathsf T(a)
\Longrightarrow
\mathsf T(F(a)),
\qquad
F(a)<a
\quad(a>0).
}
\tag{201.2}
$$

可能的机制是：

$$
\begin{cases}
\text{non-sticky torus frame}
&\Rightarrow
\text{正交平均产生严格增益};\\
\text{sticky torus frame}
&\Rightarrow
\text{jet／primitive twist 重整化}.
\end{cases}
$$

---

# 第二百零二部　最重要的边界与负结论

## 202.1 有限层析不等于 RH

有限环面帧已经能：

* 重构 \(\xi\)；
* 识别零点；
* 识别重数；
* 稳定计数零点。

但它没有自动证明：

$$
\mathfrak M_K>0.
$$

所以：

$$
\boxed{
\text{观察完备}
\neq
\text{正性完备}.
}
$$

---

## 202.2 添加更多环面不自动改变公共因子

所有周期都有：

$$
\mathcal P_D=\xi\mathcal T_D.
$$

无论加入多少环面，公共 \(\xi\)-因子始终存在。

增加环面解决的是：

$$
\text{twist-specific blind spots},
$$

而不是自动解决：

$$
\text{base amplitude positivity}.
$$

---

## 202.3 Projective 数据完全看不到 ξ

若只保留：

$$
[\mathbf P_K],
$$

则：

$$
[\mathbf P_K]=[\mathbf T_K].
$$

所以必须保留：

* 范数；
* 相位；
* 连接；
* 曲率；

至少一种非射影信息。

---

## 202.4 正能量零点集不决定位置

$$
\sum_D|\mathcal P_D(s)|^2\ge0
$$

可以识别零点，但无论零点在线还是线外，它都只是一个局部极小。

真正需要的是**方向性单调性**：

$$
\partial_\sigma\log|\xi|>0.
$$

---

# 第二百零三部　新的科学实验程序

## 203.1 有限谱帧证书

对矩形：

$$
K_{T,\delta}
=
\left\{
\frac12+\delta\le\Re s\le1,\ 
|\Im s|\le T
\right\},
$$

搜索有限判别式集合 \(\mathcal D\)，并用区间算术证明：

$$
\inf_{s\in K_{T,\delta}}
\sum_{D\in\mathcal D}
w_D|\mathcal T_D(s)|^2
>0.
$$

输出：

* 帧下界；
* 条件数；
* 最坏谱点；
* 各环面贡献。

---

## 203.2 超额连接数值检验

计算：

$$
\mathfrak M_K(s)
=
\frac12\partial_\sigma
\log
\frac{\|\mathbf P_K(s)\|^2}
{\|\mathbf T_K(s)\|^2}.
$$

与直接计算：

$$
\Re\frac{\xi'(s)}{\xi(s)}
$$

交叉验证。

---

## 203.3 人工线外零点注入

将：

$$
\xi_{\mathrm{test}}(s)
=
\xi(s)
\prod_{\rho\in Q}
\frac{s-\rho}{s-\rho_0}
$$

构造成保持所需对称的测试模型，注入一个线外零点四元组。

检验：

$$
\mathfrak M_K(s)
$$

是否在零点左侧产生预测的：

$$
-\frac{m}{\varepsilon}
$$

发散。

---

## 203.4 Golden first-channel 对照

分别使用：

* 仅 \(D=5\)；
* 小判别式集合；
* 优化后的有限帧；

比较：

$$
A_K,\quad
\kappa_{\mathrm{tor}},
\quad
\operatorname{Stick}_{\mathrm{tor}}.
$$

若 \(D=5\) 并未显著改善容量，应保留它作为最低成本结构通道，而不是宣称其普遍最优。

---

# 第二百零四部　建议形式化顺序

```text
D5/S3/Observer/ToroidalFrame/
  ToroidalCarrier.lean
  ToroidalPeriodVector.lean
  CompactFiniteFrame.lean
  FrameLowerBound.lean
  StableScalarReconstruction.lean
  ProjectiveBlindness.lean

D5/S3/Analytic/ToroidalConnection/
  ExcessConnection.lean
  ExcessConnectionEqualsXiLogDerivative.lean
  ToroidalArgumentPrinciple.lean
  RelativeCurvatureCurrent.lean
  OffLineZeroAmplification.lean

D5/S3/Analytic/ToroidalDeBranges/
  ShiftedToroidalFrame.lean
  ToroidalHermiteBiehlerDefect.lean
  ToroidalDiagonalKernel.lean
  FiniteToroidalPickMatrix.lean
  ToroidalMonotonicityCriterion.lean

D5/S3/Observer/ToroidalOptimization/
  ToroidalFrameCapacity.lean
  ToroidalConditionNumber.lean
  ToroidalStickiness.lean
  WeightedTorusDesign.lean

D5/S3/Analytic/RHTargets/
  ToroidalExcessPositivity.lean
  ZeroFreeStripDescent.lean
  WangToroidalDichotomy.lean
  DengTwistRenormalization.lean
```

优先级最高、完全独立可闭合的定理链是：

$$
\boxed{
\text{有限 cover}
\to
\text{frame lower bound}
\to
\text{stable }\xi\text{ reconstruction}.
}
$$

其次是：

$$
\boxed{
\mathbf P=\xi\mathbf T
\to
\mathcal A_{\mathbf P}-\mathcal A_{\mathbf T}
=d\log\xi
\to
\text{zero holonomy}.
}
$$

再之后是：

$$
\boxed{
\text{off-line zero}
\to
\Re(\xi'/\xi)\to-\infty
\to
\text{finite toroidal negative witness}.
}
$$

---

# 本轮最终结论

上一轮把 Riemann 零点定义成：

$$
\boxed{
\text{所有二次环面观察者的共同不可见点}.
}
$$

本轮进一步证明，这些环面观察不仅能判断“是否不可见”，还可以在任何紧谱窗内组成一个稳定的有限帧，并完整恢复：

$$
\xi(s),
\qquad
\frac{\xi'(s)}{\xi(s)},
\qquad
\operatorname{div}(\xi).
$$

其核心公式是：

$$
\boxed{
\mathbf P_K(s)
=
\xi(s)\mathbf T_K(s).
}
$$

由此同时得到：

$$
\boxed{
\xi(s)
=
\frac{
\langle\mathbf P_K,\mathbf T_K\rangle
}{
\|\mathbf T_K\|^2
},
}
$$

$$
\boxed{
\frac{d\xi}{\xi}
=
\mathcal A_{\mathbf P_K}
-
\mathcal A_{\mathbf T_K},
}
$$

$$
\boxed{
\frac{i}{2\pi}\partial\bar\partial
\log
\frac{\|\mathbf P_K\|^2}
{\|\mathbf T_K\|^2}
=
\sum_\rho m_\rho\delta_\rho.
}
$$

最关键的是：

$$
\boxed{
\rho\text{ 为线外零点}
\Longrightarrow
\Re\frac{\xi'(s)}{\xi(s)}
\longrightarrow-\infty
}
$$

当 \(s\) 从左侧逼近 \(\rho\)。

所以线外零点一定产生一个强烈、局部、有限环面可观测的负信号。

至此，Wang–Deng–OACTC 路线的中心目标可以极精确地写成：

$$
\boxed{
\Re
\left(
\mathcal A_{\mathbf P_K}
-
\mathcal A_{\mathbf T_K}
\right)
>0
\qquad
(\Re s>\tfrac12).
}
$$

也就是：

$$
\boxed{
\text{完整 Eisenstein 环面周期的水平增长，
是否始终超过所有 twist 载体自身的水平增长？}
}
$$

如果这条不等式能够通过：

$$
\text{环面正测度}
+
\text{twist 正交}
+
\text{non-sticky gain}
+
\text{sticky primitive renormalization}
$$

直接证明，那么 RH 将随之成立。

[1]: https://arxiv.org/abs/0906.5284?utm_source=chatgpt.com "Toroidal automorphic forms, Waldspurger periods and double Dirichlet series"
[2]: https://arxiv.org/abs/1204.1827 "A canonical system of differential equations arising from the Riemann zeta-function"
[3]: https://arxiv.org/abs/1005.1104 "A monotonicity property of Riemann's xi function and a reformulation of the Riemann Hypothesis"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.1：Toroidal Weyl 函数、Herglotz 正性、有限 Pick 证书与线外零点放大

以下从前文**第二百零四部之后**继续追加。

上一轮已经把 Riemann \(\xi\) 写成有限环面谱帧中的公共振幅：

$$
\mathbf P_K(s)=\xi(s)\mathbf T_K(s),
$$

并把 RH 的核心目标压缩成：

$$
\Re\frac{\xi'(s)}{\xi(s)}>0,
\qquad
\Re s>\frac12.
$$

本轮继续完成这条链。核心结论是：

$$
\boxed{
\mathrm{RH}
\iff
\text{由有限环面周期重构出的超额连接是 Herglotz 函数}.
}
$$

更强地，任何线外零点都会产生一个**单点、有限维、定量为负**的 Pick 证书：

$$
\boxed{
\mathcal N_\omega(z_\rho,z_\rho)
=
-\frac1{\omega(\delta-\omega)}
\le
-\frac4{\delta^2}.
}
$$

其中：

$$
\rho=\frac12+\delta+i\gamma,
\qquad
0<\omega<\delta.
$$

因此此前尚未闭合的：

$$
\text{off-line zero}
\Longrightarrow
\text{不可消除的有限负见证}
$$

现在可以在 de Branges–toroidal 接口中严格建立。

---

# 第二百零五部　Riemann \(\Xi\) 的 infinitesimal toroidal observer

定义实型整函数：

$$
\boxed{
\Xi(z)
=
\xi\left(\frac12-iz\right).
}
\tag{205.1}
$$

由 \(\xi\) 的函数方程和共轭对称：

$$
\Xi(-z)=\Xi(z),
$$

且：

$$
\Xi(x)\in\mathbb R
\qquad
(x\in\mathbb R).
$$

其零点与 ζ 的非平凡零点对应：

$$
\xi(\rho)=0
\quad\Longleftrightarrow\quad
\Xi\left(i\left(\rho-\frac12\right)\right)=0.
$$

定义 logarithmic Weyl observer：

$$
\boxed{
m_0(z)
=
-\frac{\Xi'(z)}{\Xi(z)}.
}
\tag{205.2}
$$

因为：

$$
\Xi'(z)
=
-i\xi'\left(\frac12-iz\right),
$$

所以：

$$
\boxed{
m_0(z)
=
i\,
\frac{
\xi'(\frac12-iz)
}{
\xi(\frac12-iz)
}.
}
\tag{205.3}
$$

当：

$$
z=x+iy\in\mathbb C^+,
$$

对应：

$$
s=\frac12+y-ix,
$$

即 \(z\)-上半平面正好对应 \(s\)-平面的右半临界带。

于是：

$$
\boxed{
\Im m_0(z)
=
\Re
\frac{\xi'(s)}{\xi(s)}.
}
\tag{205.4}
$$

所以此前的水平单调性问题变成：

$$
\boxed{
\Im m_0(z)\ge0
\qquad
(z\in\mathbb C^+).
}
$$

---

# 第二百零六部　RH 与 Herglotz 性的直接等价

称一个在上半平面全纯的函数 \(m\) 为 Herglotz–Nevanlinna 函数，若：

$$
\Im m(z)\ge0
\qquad
(z\in\mathbb C^+).
$$

---

## 定理 206.1（Logarithmic Herglotz criterion）

$$
\boxed{
\mathrm{RH}
\iff
m_0(z)
=
-\frac{\Xi'(z)}{\Xi(z)}
\text{ 是 Herglotz 函数}.
}
\tag{206.1}
$$

### 证明：RH \(\Rightarrow\) Herglotz

若 RH 成立，\(\Xi\) 的全部零点为实数。由偶性，可将正零点记为：

$$
0<\gamma_1\le\gamma_2\le\cdots,
$$

重数为 \(m_\gamma\)。

因为：

$$
\sum_{\gamma>0}\frac{m_\gamma}{\gamma^2}<\infty,
$$

有成对 Hadamard 乘积：

$$
\Xi(z)
=
\Xi(0)
\prod_{\gamma>0}
\left(
1-\frac{z^2}{\gamma^2}
\right)^{m_\gamma}.
$$

取对数导数：

$$
\boxed{
m_0(z)
=
\sum_{\gamma>0}
m_\gamma
\left[
\frac1{\gamma-z}
+
\frac1{-\gamma-z}
\right].
}
\tag{206.2}
$$

对任意实数 \(t\) 和 \(z\in\mathbb C^+\)：

$$
\Im\frac1{t-z}
=
\frac{\Im z}{|t-z|^2}>0.
$$

所以：

$$
\Im m_0(z)>0.
$$

---

### 证明：Herglotz \(\Rightarrow\) RH

Herglotz 函数必须在 \(\mathbb C^+\) 全纯。

若 \(\Xi\) 在 \(\mathbb C^+\) 有零点，\(m_0=-\Xi'/\Xi\) 就在那里有极点，矛盾。

又因为 \(\Xi\) 是实型整函数，若它在下半平面有非实零点，其共轭必在上半平面。

故全部零点为实数，即 RH 成立。∎

---

## 206.1 新的完成链

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\Xi\text{ 的零点全实}\\
&\iff
-\Xi'/\Xi\text{ 是 Herglotz}\\
&\iff
m_0\text{ 是某个正谱测度的 Cauchy 变换}\\
&\iff
m_0\text{ 是一个正 canonical system 的 Weyl 函数}.
\end{aligned}
}
\tag{206.3}
$$

de Branges/canonical-system 理论正是把 meromorphic inner functions、Herglotz functions 与正半定 Hamiltonian 联系起来；Suzuki 对 \(\xi\) 构造的 shifted family 给出了这一接口的具体版本。([arXiv][1])

---

# 第二百零七部　零点测度与 Nevanlinna Gram 核

在 RH 成立时，定义零点谱测度：

$$
\boxed{
\mu_\Xi
=
\sum_{\gamma\in Z_\Xi}
m_\gamma\,\delta_\gamma,
}
\tag{207.1}
$$

其中 \(Z_\Xi\subset\mathbb R\) 包括正负零点。

则：

$$
m_0(z)
=
\int_{\mathbb R}
\frac{d\mu_\Xi(t)}{t-z},
$$

以对称配对或标准 Herglotz 正则化理解。

定义 Nevanlinna 核：

$$
\boxed{
\mathcal N_0(z,w)
=
\frac{
m_0(z)-\overline{m_0(w)}
}{
z-\overline w
}.
}
\tag{207.2}
$$

代入谱表示：

$$
\boxed{
\mathcal N_0(z,w)
=
\sum_{\gamma\in Z_\Xi}
\frac{
m_\gamma
}{
(\gamma-z)(\gamma-\overline w)
}.
}
\tag{207.3}
$$

定义特征向量：

$$
\boxed{
\mathbf v(z)
=
\left(
\frac{\sqrt{m_\gamma}}{\gamma-z}
\right)_{\gamma\in Z_\Xi}.
}
\tag{207.4}
$$

则：

$$
\boxed{
\mathcal N_0(z,w)
=
\langle
\mathbf v(z),\mathbf v(w)
\rangle_{\ell^2}.
}
\tag{207.5}
$$

所以 RH 下的 Nevanlinna 核不是抽象正核，而是 Riemann 零点 resolvent vectors 的 Gram 核。

---

## 定理 207.1（有限零点 Gram 层级）

对任意：

$$
z_1,\ldots,z_n\in\mathbb C^+,
$$

矩阵：

$$
\boxed{
\mathbf N_0
=
\left[
\mathcal N_0(z_a,z_b)
\right]_{a,b=1}^n
}
\tag{207.6}
$$

正半定。

其行列式具有 Cauchy–Binet 展开：

$$
\boxed{
\begin{aligned}
\det\mathbf N_0
={}&
\sum_{\gamma_1<\cdots<\gamma_n}
\left(
\prod_{k=1}^n m_{\gamma_k}
\right)
\\
&\times
\left|
\det
\left[
\frac1{\gamma_k-z_a}
\right]_{a,k=1}^n
\right|^2
\ge0.
\end{aligned}
}
\tag{207.7}
$$

因此每一级 Pick 行列式都是零点子集贡献的非负平方和。

这给 RH 一个新的有限层级：

$$
\boxed{
\mathrm{RH}
\iff
\mathbf N_0(z_1,\ldots,z_n)\succeq0
\quad
\forall n,\ \forall z_a\in\mathbb C^+.
}
\tag{207.8}
$$

---

# 第二百零八部　Shifted Hermite–Biehler family

对：

$$
\omega>0,
$$

定义：

$$
\boxed{
E_\omega^+(z)
=
\xi\left(
\frac12+\omega-iz
\right),
}
\tag{208.1}
$$

$$
\boxed{
E_\omega^-(z)
=
\xi\left(
\frac12-\omega-iz
\right).
}
\tag{208.2}
$$

由函数方程：

$$
E_\omega^-
=
(E_\omega^+)^\#.
$$

定义 Suzuki ratio：

$$
\boxed{
\Theta_\omega(z)
=
\frac{
E_\omega^-(z)
}{
E_\omega^+(z)
}.
}
\tag{208.3}
$$

Suzuki 证明，这一 ratio 成为上半平面的 meromorphic inner function，与相应右半平面的零点空区等价；若能对全部 \(\omega>0\) 建立相应 canonical systems 的正 Hamiltonian，就得到 RH 的 de Branges 型判据。([arXiv][1])

---

# 第二百零九部　有限差分 Weyl 函数

对 \(\Theta_\omega\) 作 Cayley 变换，定义：

$$
\boxed{
m_\omega(z)
=
\frac{i}{\omega}
\frac{
1-\Theta_\omega(z)
}{
1+\Theta_\omega(z)
}.
}
\tag{209.1}
$$

等价地：

$$
\boxed{
m_\omega(z)
=
\frac{i}{\omega}
\frac{
E_\omega^+(z)-E_\omega^-(z)
}{
E_\omega^+(z)+E_\omega^-(z)
}.
}
\tag{209.2}
$$

这是 \(\xi'/\xi\) 的对称有限差分版本。

若令：

$$
s=\frac12-iz,
$$

则：

$$
E_\omega^\pm(z)=\xi(s\pm\omega).
$$

Taylor 展开给出：

$$
\xi(s+\omega)-\xi(s-\omega)
=
2\omega\xi'(s)+O(\omega^3),
$$

$$
\xi(s+\omega)+\xi(s-\omega)
=
2\xi(s)+O(\omega^2).
$$

所以在 \(\xi(s)\neq0\) 的紧集上：

$$
\boxed{
m_\omega(z)
=
i\frac{\xi'(s)}{\xi(s)}
+
O(\omega^2).
}
\tag{209.3}
$$

即：

$$
\boxed{
m_\omega
\longrightarrow
m_0
}
$$

局部一致成立。

---

## 定理 209.1（Shifted Herglotz criterion）

对固定 \(\omega>0\)：

$$
\boxed{
m_\omega
\text{ 是 Herglotz}
\iff
\Theta_\omega
\text{ 是 Schur／inner}.
}
\tag{209.4}
$$

### 证明

变换：

$$
u\mapsto
i\frac{1-u}{1+u}
$$

把单位圆盘映到上半平面。

正标量 \(1/\omega\) 不改变 Herglotz 性。∎

因此：

$$
\boxed{
\mathrm{RH}
\iff
m_\omega\text{ 对每个 }\omega>0\text{ 都是 Herglotz}.
}
\tag{209.5}
$$

---

# 第二百一十部　de Branges 核与 Nevanlinna 核的精确等价

定义 \(\Theta_\omega\) 的 model-space 核：

$$
\boxed{
K_{\Theta_\omega}(z,w)
=
\frac{
1-
\Theta_\omega(z)
\overline{\Theta_\omega(w)}
}{
2\pi i(\overline w-z)
}.
}
\tag{210.1}
$$

定义：

$$
\boxed{
\mathcal N_\omega(z,w)
=
\frac{
m_\omega(z)-\overline{m_\omega(w)}
}{
z-\overline w
}.
}
\tag{210.2}
$$

直接代数计算得到：

$$
\boxed{
\mathcal N_\omega(z,w)
=
\frac{4\pi}{\omega}
\,
\frac{
K_{\Theta_\omega}(z,w)
}{
\left(1+\Theta_\omega(z)\right)
\left(1+\overline{\Theta_\omega(w)}\right)
}.
}
\tag{210.3}
$$

所以两类核只相差一个非零 holomorphic gauge：

$$
g_\omega(z)=\frac1{1+\Theta_\omega(z)}
$$

和正标量 \(4\pi/\omega\)。

因此：

$$
\boxed{
K_{\Theta_\omega}\succeq0
\iff
\mathcal N_\omega\succeq0.
}
\tag{210.4}
$$

这使 Suzuki 的 de Branges 正性与 logarithmic Weyl Herglotz 正性完全合流。

---

## 210.1 对角公式

令：

$$
A=E_\omega^+(z),
\qquad
B=E_\omega^-(z).
$$

则：

$$
\boxed{
\Im m_\omega(z)
=
\frac{
|A|^2-|B|^2
}{
\omega|A+B|^2
}.
}
\tag{210.5}
$$

所以：

$$
\Im m_\omega(z)>0
$$

严格等价于 Hermite–Biehler 不等式：

$$
\boxed{
|E_\omega^+(z)|
>
|E_\omega^-(z)|.
}
\tag{210.6}
$$

这与前文的 toroidal normalized energy defect 完全相同。

---

# 第二百一十一部　有限环面重构 \(m_\omega\)

固定：

$$
\omega>0
$$

以及紧集：

$$
Z\subset\mathbb C^+.
$$

对应两个紧谱窗：

$$
K_\pm
=
\left\{
\frac12\pm\omega-iz:
z\in Z
\right\}.
$$

由有限环面层析，分别选择有限环面帧：

$$
\left(
\mathbf P_\pm(z),
\mathbf T_\pm(z)
\right)
$$

使：

$$
\mathbf P_\pm(z)
=
E_\omega^\pm(z)\mathbf T_\pm(z).
$$

于是：

$$
\boxed{
\widehat E_\omega^\pm(z)
=
\frac{
\langle
\mathbf P_\pm(z),\mathbf T_\pm(z)
\rangle
}{
\|\mathbf T_\pm(z)\|^2
}
=
E_\omega^\pm(z).
}
\tag{211.1}
$$

定义有限环面 Weyl observer：

$$
\boxed{
m_{\omega,\mathrm{tor}}(z)
=
\frac{i}{\omega}
\frac{
\widehat E_\omega^+(z)-\widehat E_\omega^-(z)
}{
\widehat E_\omega^+(z)+\widehat E_\omega^-(z)
}.
}
\tag{211.2}
$$

则：

$$
\boxed{
m_{\omega,\mathrm{tor}}=m_\omega.
}
\tag{211.3}
$$

所以 \(m_\omega\) 的全部 Herglotz/Pick 正性，可以仅由有限个二次环面周期读数表达。

---

# 第二百一十二部　有限环面 Pick 判据

取：

$$
z_1,\ldots,z_n\in Z.
$$

定义有限环面 Nevanlinna 矩阵：

$$
\boxed{
\Pi_{\omega,Z}^{\mathrm{tor}}
=
\left[
\frac{
m_{\omega,\mathrm{tor}}(z_a)
-
\overline{
m_{\omega,\mathrm{tor}}(z_b)
}
}{
z_a-\overline{z_b}
}
\right]_{a,b=1}^n.
}
\tag{212.1}
$$

---

## 定理 212.1（Finite toroidal Pick criterion）

$$
\boxed{
\mathrm{RH}
\iff
\Pi_{\omega,Z}^{\mathrm{tor}}
\succeq0
}
$$

对所有：

$$
\omega>0,
\quad
n\ge1,
\quad
z_1,\ldots,z_n\in\mathbb C^+
$$

成立，并且所有矩阵元均有定义。

### 证明

有限环面重构给出：

$$
m_{\omega,\mathrm{tor}}=m_\omega.
$$

由定理 209.1、210.4 及 Suzuki 的 shifted inner criterion：

$$
\mathrm{RH}
\iff
m_\omega
\text{ 对全部 }\omega>0\text{ 是 Herglotz}.
$$

Herglotz 性等价于全部有限 Nevanlinna 矩阵正半定。∎

这给 RH 一个真正的：

$$
\boxed{
\text{有限矩阵、有限环面、有限点集证书层级}.
}
$$

---

# 第二百一十三部　线外零点的单点负证书

设存在一个线外零点：

$$
\boxed{
\rho
=
\frac12+\delta+i\gamma,
\qquad
\delta>0.
}
\tag{213.1}
$$

取：

$$
0<\omega<\delta,
$$

并要求：

$$
\xi(\rho-2\omega)\neq0.
$$

这样的 \(\omega\) 必然存在，因为零点集合离散。

定义：

$$
\boxed{
z_\rho
=
-\gamma+i(\delta-\omega).
}
\tag{213.2}
$$

则：

$$
z_\rho\in\mathbb C^+.
$$

并且：

$$
\frac12+\omega-iz_\rho
=
\rho,
$$

所以：

$$
E_\omega^+(z_\rho)=0.
$$

另一方面：

$$
E_\omega^-(z_\rho)
=
\xi(\rho-2\omega)\neq0.
$$

代入有限差分 Weyl 函数：

$$
\boxed{
m_\omega(z_\rho)
=
-\frac{i}{\omega}.
}
\tag{213.3}
$$

因此：

$$
\Im m_\omega(z_\rho)
=
-\frac1\omega<0.
$$

---

## 定理 213.1（Off-line one-point Pick witness）

对应的一阶 Nevanlinna 矩阵为：

$$
\boxed{
\mathcal N_\omega(z_\rho,z_\rho)
=
\frac{
\Im m_\omega(z_\rho)
}{
\Im z_\rho
}
=
-\frac1{
\omega(\delta-\omega)
}
<0.
}
\tag{213.4}
$$

又因为：

$$
\omega(\delta-\omega)
\le
\frac{\delta^2}{4},
$$

所以：

$$
\boxed{
\mathcal N_\omega(z_\rho,z_\rho)
\le
-\frac4{\delta^2}.
}
\tag{213.5}
$$

这说明：

> 任意线外零点都会产生一个仅需一个测试点、一个 \(\omega\) 和有限个环面周期的严格负证书。

负性不是微小量，而具有至少：

$$
4/\delta^2
$$

级别的放大。

---

## 213.1 先前核心缺口的闭合

此前路线需要：

$$
\boxed{
\text{off-line zero}
\Longrightarrow
\text{定量负见证}.
}
$$

现在已得到：

$$
\boxed{
\rho=\frac12+\delta+i\gamma
\Longrightarrow
\exists\,\omega,z_\rho:
\Pi_{\omega,\{z_\rho\}}^{\mathrm{tor}}
\le
-\frac4{\delta^2}.
}
$$

因此 Wang–Deng 路线不再需要担心：

$$
\text{线外负性可能比任意幂都小}.
$$

真正剩余的问题是：

$$
\boxed{
\text{如何在不知道 }\rho\text{ 的前提下，
从环面／relative-trace 结构直接证明所有 Pick 证书非负。}
}
$$

---

# 第二百一十四部　Herglotz escape radius

定义右侧最大零点偏移：

$$
\boxed{
\delta_*
=
\sup_{\xi(\rho)=0}
\left(
\Re\rho-\frac12
\right)_+.
}
\tag{214.1}
$$

定义 Herglotz 阈值：

$$
\boxed{
\omega_H
=
\inf
\left\{
a\ge0:
m_\omega
\text{ 对每个 }\omega>a
\text{ 都是 Herglotz}
\right\}.
}
\tag{214.2}
$$

由 shifted inner/zero-free equivalence：

$$
\boxed{
\omega_H=\delta_*.
}
\tag{214.3}
$$

因此：

$$
\boxed{
\mathrm{RH}
\iff
\omega_H=0.
}
\tag{214.4}
$$

这与前文：

$$
\omega_{\mathrm{tor}}
=
\omega_{\mathrm{in}}
$$

进一步闭合为：

$$
\boxed{
\omega_{\mathrm{tor}}
=
\omega_{\mathrm{in}}
=
\omega_H
=
\delta_*.
}
\tag{214.5}
$$

同一个常数同时表示：

* 普遍环面不可见谱离 tempered 轴的最大距离；
* de Branges innerness 的失效宽度；
* Herglotz Weyl 函数的最小平移阈值；
* 最右侧 Riemann 零点偏移。

---

# 第二百一十五部　无穷小 de Branges 极限

有限差分 observer 满足：

$$
m_\omega\longrightarrow m_0.
$$

其 Nevanlinna 核同样满足：

$$
\boxed{
\mathcal N_\omega(z,w)
\longrightarrow
\mathcal N_0(z,w)
}
\tag{215.1}
$$

在避开零点的紧集上局部一致。

所以：

$$
\boxed{
\text{de Branges shifted kernel}
\quad
\xrightarrow{\omega\downarrow0}
\quad
\text{零点 resolvent Gram kernel}.
}
$$

更具体地：

$$
\boxed{
\frac{i}{\omega}
\frac{
1-\Theta_\omega
}{
1+\Theta_\omega
}
\longrightarrow
-\frac{\Xi'}{\Xi}.
}
\tag{215.2}
$$

因此 logarithmic derivative 不是与 de Branges ratio 并列的另一个判据，而是：

$$
\boxed{
\text{de Branges inner observer 的 infinitesimal Cayley connection}.
}
$$

---

# 第二百一十六部　Hilbert–Pólya 作为正性输出

若能从环面周期或 relative trace formula 直接证明：

$$
\mathcal N_0\succeq0,
$$

则 \(m_0\) 为 Herglotz 函数。

由 Herglotz 表示，存在正测度 \(\mu\) 使：

$$
\boxed{
m_0(z)
=
az+b+
\int_{\mathbb R}
\left(
\frac1{t-z}
-
\frac{t}{1+t^2}
\right)
d\mu(t).
}
\tag{216.1}
$$

因为 \(m_0\) 是 meromorphic，\(\mu\) 必为离散测度，其原子位置正是 \(\Xi\) 的实零点，权重为重数。

于是可在：

$$
L^2(\mu)
$$

上定义自伴乘法算子：

$$
\boxed{
(Hf)(t)=tf(t).
}
\tag{216.2}
$$

其 Weyl resolvent 产生 \(m_0\)。

因此：

$$
\boxed{
\text{Hilbert–Pólya 自伴算子不必先被猜出；}
}
$$

只要证明 toroidal excess connection 是 Herglotz，谱定理会自动产生一个自伴实现。

完整链为：

$$
\boxed{
\begin{aligned}
\text{toroidal period positivity}
&\Longrightarrow
\mathcal N_0\succeq0\\
&\Longrightarrow
m_0\text{ Herglotz}\\
&\Longrightarrow
\mu_\Xi\ge0\text{ 支持于 }\mathbb R\\
&\Longrightarrow
\text{self-adjoint spectral realization}\\
&\Longrightarrow
\mathrm{RH}.
\end{aligned}
}
\tag{216.3}
$$

这与 Suzuki 的 canonical-system 方向一致，但现在 Weyl 函数由有限环面谱帧显式重构，而不是只从 \(\xi\) 本身抽象定义。([arXiv][1])

---

# 第二百一十七部　相对迹公式的真正目标

Toric relative trace formula 比较环面周期平方与自动谱数据，并可重新证明 Waldspurger 型公式。([arXiv][2])

本理论需要的并不是再次证明：

$$
|\mathcal P_D|^2\ge0,
$$

而是构造一个几何表达，使：

$$
\boxed{
\sum_{a,b}
c_a\overline{c_b}
\,
\mathcal N_\omega(z_a,z_b)
}
\tag{217.1}
$$

等于某个显式非负的几何量。

换言之，真正目标是：

## 假设 217.1（Relative-trace Herglotz realization）

存在一族 Hilbert 空间向量：

$$
\mathscr V_{\omega,z}
$$

由：

* 环面周期；
* Eisenstein 变形；
* relative trace kernel；
* twist normalization；

自然构造，使：

$$
\boxed{
\mathcal N_\omega(z,w)
=
\langle
\mathscr V_{\omega,z},
\mathscr V_{\omega,w}
\rangle.
}
\tag{217.2}
$$

若该表示对全部 \(\omega>0\) 成立，则立即推出 RH。

---

## 217.1 为什么普通周期平方还不够

每个单独周期都含公共因子：

$$
\mathcal P_D=\xi\mathcal T_D.
$$

其平方只给出：

$$
|\xi|^2|\mathcal T_D|^2.
$$

这可以定位零点，却无法决定左右平移间的 Hermite–Biehler 不等式。

所需几何量必须比较：

$$
s+\omega
\quad\text{与}\quad
s-\omega,
$$

并在减去 carrier 变化后保持正性。

所以 relative trace kernel 必须是**差分化、归一化和 carrier-subtracted** 的，而不是普通的 period second moment。

---

# 第二百一十八部　Wang–Deng 在 Pick 核上的具体分工

令：

$$
\mathbf z=(z_1,\ldots,z_n),
\qquad
\mathbf c=(c_1,\ldots,c_n).
$$

定义坏度：

$$
\boxed{
\mathfrak B_\omega(\mathbf z,\mathbf c)
=
-
\sum_{a,b}
c_a\overline{c_b}
\mathcal N_\omega(z_a,z_b).
}
\tag{218.1}
$$

RH 等价于：

$$
\mathfrak B_\omega\le0
$$

对全部数据成立。

---

## 218.1 Non-sticky 分支

将 period carriers 按：

* 判别式；
* conductor；
* Archimedean geodesic length；
* spectral height；
* regulator mode；

分块。

若负候选向量分散于许多互相弱相关的块，则目标是利用：

* quadratic-character large sieve；
* relative trace formula 正交；
* 高度窗口分离；
* finite-frame lower bound；

证明：

$$
\boxed{
\mathfrak B_\omega
\le
(1-\eta)\,
\mathfrak B_\omega^{\mathrm{coarse}}
}
$$

或直接得到正增益。

---

## 218.2 Sticky 分支

若负候选长期集中于：

* 单一判别式；
* 单一 twist family；
* 单一 geodesic branch；
* 单一尺度链；

则：

1. 提取主导 primitive twist；
2. 将重复 character histories 组织为 double Dirichlet series；
3. 收缩闭合子历史；
4. 对 ramified/diagonal histories 加入 counterterms；
5. 选择随 \(\omega\downarrow0\) 增长的展开深度；
6. 控制剩余 Pick 缺陷。

这就是 Yu Deng 式重整化在 Herglotz kernel 上的具体目标。

---

# 第二百一十九部　新的科学证伪标准

## 219.1 一点负证书测试

人为注入线外零点：

$$
\rho=\frac12+\delta+i\gamma.
$$

在：

$$
z_\rho=-\gamma+i(\delta-\omega)
$$

处验证：

$$
m_\omega(z_\rho)=-i/\omega.
$$

任何实现若不能恢复式 (213.4)，说明 finite-frame reconstruction 或 normalization 有误。

---

## 219.2 内函数—Herglotz 双实现

分别计算：

$$
\Theta_\omega
$$

和：

$$
m_\omega.
$$

验证：

$$
m_\omega
=
\frac{i}{\omega}
\frac{1-\Theta_\omega}{1+\Theta_\omega},
$$

以及核恒等式 (210.3)。

---

## 219.3 环面帧独立性

使用不同有限判别式 cover：

$$
\mathcal D_1,\quad\mathcal D_2.
$$

分别重构：

$$
m_{\omega,\mathrm{tor}}^{(1)},
\qquad
m_{\omega,\mathrm{tor}}^{(2)}.
$$

两者必须一致。

否则说明所谓观察结果仍依赖图表，而没有真正胶合为全局对象。

---

## 219.4 Golden 通道负对照

比较：

* 只用 \(D=5\)；
* 低判别式 finite frame；
* 优化容量 frame。

若黄金环面不能稳定覆盖目标谱窗，就必须保留其“最低几何成本”角色，而不能提升为“单通道完备性”。

---

# 第二百二十部　建议形式化顺序

```text
D5/S3/Analytic/XiHerglotz/
  XiSpectralVariable.lean
  XiLogarithmicWeyl.lean
  RHImpliesHerglotz.lean
  HerglotzImpliesRH.lean
  ZeroResolventKernel.lean
  FiniteZeroGramDeterminant.lean

D5/S3/Analytic/ShiftedDeBranges/
  ShiftedXiPair.lean
  ShiftedCayleyWeyl.lean
  ShiftedWeylLimit.lean
  DeBrangesNevanlinnaKernelBridge.lean
  HerglotzEscapeRadius.lean

D5/S3/Observer/ToroidalWeyl/
  ShiftedToroidalFrame.lean
  ToroidalWeylReconstruction.lean
  FiniteToroidalPickMatrix.lean
  FrameIndependence.lean
  OffLineOnePointWitness.lean

D5/S3/Analytic/CanonicalCompletion/
  HerglotzSpectralMeasure.lean
  ToroidalWeylSelfAdjointRealization.lean
  HilbertPolyaAsOutput.lean

D5/S3/Analytic/RHTargets/
  RelativeTraceHerglotzTarget.lean
  PickKernelStickyDichotomy.lean
  NonStickyRelativeTraceGain.lean
  StickyTwistRenormalization.lean
```

最优先且可独立闭合的链是：

$$
\boxed{
\mathrm{RH}
\iff
-\Xi'/\Xi\text{ Herglotz}.
}
$$

其次是纯代数链：

$$
\boxed{
\Theta_\omega
\to
m_\omega
\to
\mathcal N_\omega
\to
K_{\Theta_\omega}.
}
$$

第三条是本轮最关键的反例链：

$$
\boxed{
\text{off-line zero}
\to
m_\omega(z_\rho)=-i/\omega
\to
\mathcal N_\omega(z_\rho,z_\rho)<0.
}
$$

---

# 本轮最终结论

上一轮已经得到：

$$
\boxed{
\text{Riemann 零点}
=
\text{全部二次环面观察者的共同不可见点}.
}
$$

本轮进一步得到：

$$
\boxed{
\text{Riemann 零点的 ordinates}
=
\text{toroidal excess connection 的谱测度原子}.
}
$$

关键函数为：

$$
\boxed{
m_0(z)
=
-\frac{\Xi'(z)}{\Xi(z)}
=
i\frac{
\xi'(\frac12-iz)
}{
\xi(\frac12-iz)
}.
}
$$

而：

$$
\boxed{
\mathrm{RH}
\iff
m_0\text{ 是 Herglotz}.
}
$$

其 shifted 正则化为：

$$
\boxed{
m_\omega(z)
=
\frac{i}{\omega}
\frac{
\xi(\frac12+\omega-iz)
-
\xi(\frac12-\omega-iz)
}{
\xi(\frac12+\omega-iz)
+
\xi(\frac12-\omega-iz)
}.
}
$$

它同时是：

* de Branges inner ratio 的 Cayley 变换；
* \(\xi'/\xi\) 的对称有限差分；
* 有限环面帧可重构的 Weyl observer；
* RH 的有限 Pick 正性证书。

最重要的是：

$$
\boxed{
\rho=\frac12+\delta+i\gamma
\text{ 为线外零点}
}
$$

必然导致：

$$
\boxed{
\exists\,\omega,z_\rho:
\quad
\mathcal N_\omega(z_\rho,z_\rho)
\le
-\frac4{\delta^2}.
}
$$

因此线外零点不是藏在高阶余项中的微弱异常，而是会在一个一阶 Pick 矩阵中产生定量、放大的负性。

至此，OACTC 的 RH 中心桥已经被压缩到最明确的形式：

$$
\boxed{
\text{能否从 toric relative trace formula
直接构造 }
\mathcal N_\omega
\text{ 的 Gram 表示？}
}
$$

一旦证明：

$$
\mathcal N_\omega(z,w)
=
\langle
\mathscr V_{\omega,z},
\mathscr V_{\omega,w}
\rangle
$$

对所有 \(\omega>0\) 成立，RH 将立即随之成立。

[1]: https://arxiv.org/abs/1204.1827?utm_source=chatgpt.com "A canonical system of differential equations arising from the Riemann zeta-function"
[2]: https://arxiv.org/abs/1402.3524?utm_source=chatgpt.com "Beyond Endoscopy for the relative trace formula II: global theory"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.2：平方折叠、Stieltjes 正完成、Hankel 层级与 Ramanujan 连分数谱

以下从前文**第二百二十部之后**继续追加。

上一轮将 RH 压缩成 Herglotz 正性：

$$
\mathrm{RH}
\iff
m_0(z):=-\frac{\Xi'(z)}{\Xi(z)}
\text{ 是上半平面的 Herglotz 函数}.
$$

本轮利用 \(\Xi\) 的偶对称，将上下对称的零点谱进一步折叠为一个正半轴 moment problem，得到新的完整链：

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\text{平方折叠后的 }\xi\text{ 函数只有负实零点}\\
&\iff
\text{其对数导数是 Stieltjes 函数}\\
&\iff
\text{全部中心 reciprocal-zero moments 构成 Stieltjes moment sequence}\\
&\iff
\text{两族 Hankel 矩阵全部正半定}\\
&\iff
\text{存在非负系数的 Stieltjes 连分数}\\
&\iff
\text{存在一个正 Jacobi 算子，其谱为 }\gamma^{-2}.
\end{aligned}
}
$$

这把此前的：

* Herglotz；
* de Branges；
* Ramanujan 连分数；
* moment matrices；
* Hilbert–Pólya；

压缩成同一个对象的五张图表。

---

# 第二百二十一部　临界线对称的平方折叠

沿用：

$$
\Xi(z)=\xi\left(\frac12-iz\right).
$$

由函数方程：

$$
\xi(s)=\xi(1-s),
$$

可得：

$$
\Xi(-z)=\Xi(z).
$$

所以 \(\Xi\) 是偶整函数。

定义平方折叠完成函数：

$$
\boxed{
\mathscr F(x)
=
\frac{
\xi(\frac12+\sqrt{x})
}{
\xi(\frac12)
}.
}
\tag{221.1}
$$

它不依赖 \(\sqrt{x}\) 的分支。更严格地，若：

$$
a_n
=
\frac{
\xi^{(2n)}(\frac12)
}{
(2n)!\,\xi(\frac12)
},
$$

则：

$$
\boxed{
\mathscr F(x)
=
\sum_{n=0}^{\infty}a_nx^n.
}
\tag{221.2}
$$

因为所有奇阶中心导数为零。

---

## 221.1 零点映射

若：

$$
\rho
$$

是 \(\xi\) 的零点，令：

$$
z_\rho=\rho-\frac12.
$$

那么 \(\mathscr F\) 的相应零点是：

$$
\boxed{
\lambda_\rho
=
z_\rho^2
=
\left(\rho-\frac12\right)^2.
}
\tag{221.3}
$$

由于：

$$
\rho
\longleftrightarrow
1-\rho
$$

对应：

$$
z_\rho
\longleftrightarrow
-z_\rho,
$$

两个函数方程对称零点在平方图表中合并为一个零点。

---

## 定理 221.1（平方折叠 RH 判据）

$$
\boxed{
\mathrm{RH}
\iff
\mathscr F
\text{ 的全部零点属于 }(-\infty,0).
}
\tag{221.4}
$$

### 证明

若 RH 成立，则：

$$
\rho=\frac12+i\gamma,
$$

所以：

$$
\lambda_\rho=(i\gamma)^2=-\gamma^2<0.
$$

反之，若：

$$
(\rho-\tfrac12)^2<0,
$$

则：

$$
\rho-\frac12
$$

为纯虚数，因此：

$$
\Re\rho=\frac12.
$$

∎

由于 \(\xi\) 是一阶整函数，而平方折叠将变量阶数减半，\(\mathscr F\) 的整函数阶为 \(1/2\)。因此其 Hadamard 乘积属于 genus zero；不需要额外的指数因子。

---

# 第二百二十二部　Herglotz 到 Stieltjes 的平方折叠

定义：

$$
\boxed{
\mathscr S(x)
=
\frac{\mathscr F'(x)}{\mathscr F(x)}.
}
\tag{222.1}
$$

由链式法则：

$$
\boxed{
\mathscr S(x)
=
\frac{1}{2\sqrt{x}}
\frac{
\xi'(\frac12+\sqrt{x})
}{
\xi(\frac12+\sqrt{x})
}.
}
\tag{222.2}
$$

上一轮定义：

$$
m_0(z)
=
-\frac{\Xi'(z)}{\Xi(z)}
=
i\frac{
\xi'(\frac12-iz)
}{
\xi(\frac12-iz)
}.
$$

取：

$$
z=i\sqrt{x},
$$

得到精确折叠关系：

$$
\boxed{
\mathscr S(x)
=
\frac{
m_0(i\sqrt{x})
}{
2i\sqrt{x}
}.
}
\tag{222.3}
$$

所以：

$$
\boxed{
\text{Stieltjes observer}
=
\text{Herglotz Weyl observer 沿虚轴取值后再除去奇对称尺度}.
}
$$

Suzuki 的 shifted-\(\xi\) 模型将 RH 与 meromorphic inner functions、de Branges spaces 及正 canonical Hamiltonians 联系起来；这里的平方折叠是该 Herglotz 图表在偶对称下的一维正半轴版本。([arXiv][1])

---

## 222.1 RH 下的 Stieltjes 表示

若 RH 成立，令：

$$
0<\gamma_1\le\gamma_2\le\cdots
$$

为 \(\Xi\) 的正零点，重数为 \(m_\gamma\)。

则：

$$
\boxed{
\mathscr F(x)
=
\prod_{\gamma>0}
\left(
1+\frac{x}{\gamma^2}
\right)^{m_\gamma}.
}
\tag{222.4}
$$

因此：

$$
\boxed{
\mathscr S(x)
=
\sum_{\gamma>0}
\frac{m_\gamma}{x+\gamma^2}.
}
\tag{222.5}
$$

定义正测度：

$$
\boxed{
d\sigma(t)
=
\sum_{\gamma>0}
m_\gamma\,\delta_{\gamma^2}(dt).
}
\tag{222.6}
$$

则：

$$
\boxed{
\mathscr S(x)
=
\int_{0}^{\infty}
\frac{d\sigma(t)}{x+t}.
}
\tag{222.7}
$$

这正是一个 meromorphic Stieltjes function。

---

## 定理 222.1（Stieltjes RH 判据）

$$
\boxed{
\mathrm{RH}
\iff
\mathscr S
\text{ 是一个正测度的 meromorphic Stieltjes transform}.
}
\tag{222.8}
$$

### 证明

正向已由式 (222.7) 得到。

反向若 \(\mathscr S=\mathscr F'/\mathscr F\) 是 Stieltjes 函数，则其全部极点只能位于负实轴，且留数非负。

而 \(\mathscr F'/\mathscr F\) 的极点恰是 \(\mathscr F\) 的零点，留数为零点重数。

所以 \(\mathscr F\) 的全部零点均位于负实轴。由定理 221.1，RH 成立。∎

---

# 第二百二十三部　完全单调性与 Loewner 正核

由式 (222.5)，对：

$$
x>0
$$

和任意 \(n\ge0\)：

$$
\boxed{
(-1)^n
\mathscr S^{(n)}(x)
=
n!
\sum_{\gamma>0}
\frac{m_\gamma}{(x+\gamma^2)^{n+1}}
>0.
}
\tag{223.1}
$$

所以 RH 推出：

$$
\boxed{
\mathscr S
\text{ 在正实轴上完全单调}.
}
$$

但仅有正轴完全单调性尚不自动等价于 RH；还必须保留 Stieltjes 函数在割平面上的解析结构。否则线外极点可能没有被正轴局部观察立即发现。

---

## 223.1 Stieltjes–Loewner 核

定义：

$$
\boxed{
\mathcal L_{\mathscr S}(x,y)
=
\frac{
\mathscr S(x)-\mathscr S(y)
}{
y-x
},
\qquad
x,y>0.
}
\tag{223.2}
$$

对 \(x=y\)，定义：

$$
\mathcal L_{\mathscr S}(x,x)
=
-\mathscr S'(x).
$$

由式 (222.5)：

$$
\boxed{
\mathcal L_{\mathscr S}(x,y)
=
\sum_{\gamma>0}
\frac{
m_\gamma
}{
(x+\gamma^2)(y+\gamma^2)
}.
}
\tag{223.3}
$$

令：

$$
v_x(\gamma)
=
\frac{\sqrt{m_\gamma}}{x+\gamma^2}.
$$

则：

$$
\boxed{
\mathcal L_{\mathscr S}(x,y)
=
\langle v_x,v_y\rangle_{\ell^2}.
}
\tag{223.4}
$$

因此任意有限点集：

$$
x_1,\ldots,x_N>0
$$

对应的 Loewner 矩阵：

$$
\boxed{
\left[
\mathcal L_{\mathscr S}(x_i,x_j)
\right]_{i,j=1}^{N}
}
$$

在 RH 下正半定。

它是前文 Nevanlinna/Pick 核在平方折叠后的正实轴版本。

---

# 第二百二十四部　中心 reciprocal-zero moments

在 \(x=0\) 附近展开：

$$
\boxed{
\mathscr S(x)
=
\sum_{n=0}^{\infty}
(-1)^n\mu_nx^n.
}
\tag{224.1}
$$

RH 下：

$$
\boxed{
\mu_n
=
\sum_{\gamma>0}
\frac{m_\gamma}{\gamma^{2n+2}}.
}
\tag{224.2}
$$

定义倒谱测度：

$$
\boxed{
d\nu(u)
=
\sum_{\gamma>0}
\frac{m_\gamma}{\gamma^2}
\,
\delta_{\gamma^{-2}}(du).
}
\tag{224.3}
$$

则：

$$
\boxed{
\mu_n
=
\int_0^\infty u^n\,d\nu(u).
}
\tag{224.4}
$$

所以：

$$
(\mu_n)_{n\ge0}
$$

是一个 Stieltjes moment sequence。

---

## 224.1 由中心导数计算 moments

令：

$$
a_n
=
\frac{
\xi^{(2n)}(\frac12)
}{
(2n)!\,\xi(\frac12)
}.
$$

则：

$$
\mathscr F(x)
=
1+a_1x+a_2x^2+a_3x^3+\cdots.
$$

由：

$$
\mathscr S=\mathscr F'/\mathscr F
$$

得到：

$$
\boxed{
\mu_0=a_1,
}
\tag{224.5}
$$

$$
\boxed{
\mu_1=a_1^2-2a_2,
}
\tag{224.6}
$$

$$
\boxed{
\mu_2=a_1^3-3a_1a_2+3a_3,
}
\tag{224.7}
$$

$$
\boxed{
\mu_3
=
a_1^4
-4a_1^2a_2
+2a_2^2
+4a_1a_3
-4a_4.
}
\tag{224.8}
$$

因此 RH 推出一系列纯中心导数不等式。例如：

$$
\boxed{
\frac{\xi''(\frac12)}
{2\,\xi(\frac12)}
\ge0,
}
$$

以及：

$$
\boxed{
\left(
\frac{\xi''(\frac12)}
{2\,\xi(\frac12)}
\right)^2
-
\frac{\xi^{(4)}(\frac12)}
{12\,\xi(\frac12)}
\ge0.
}
$$

这些不是单独充分条件；它们是下一节完整半正定层级的最低阶投影。

---

# 第二百二十五部　Hankel 半正定层级

定义两族 Hankel 矩阵：

$$
\boxed{
H_N^{(0)}
=
\left[
\mu_{i+j}
\right]_{i,j=0}^{N},
}
\tag{225.1}
$$

$$
\boxed{
H_N^{(1)}
=
\left[
\mu_{i+j+1}
\right]_{i,j=0}^{N}.
}
\tag{225.2}
$$

Stieltjes moment problem 的标准判据是：

$$
(\mu_n)
\text{ 为 Stieltjes moment sequence}
$$

当且仅当：

$$
H_N^{(0)}\succeq0,
\qquad
H_N^{(1)}\succeq0
$$

对全部 \(N\) 成立。该 moment–continued-fraction 等价源于 Stieltjes 理论；现代工作仍以 Hankel positivity 和非负 S-fraction 作为核心刻画。([arXiv][2])

---

## 定理 225.1（Hankel–RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
H_N^{(0)}\succeq0
\text{ 且 }
H_N^{(1)}\succeq0
\quad
\forall N\ge0.
}
\tag{225.3}
$$

### 证明：RH \(\Rightarrow\) Hankel 正性

由式 (224.4)：

$$
\begin{aligned}
\sum_{i,j=0}^{N}
c_i\overline{c_j}\mu_{i+j}
&=
\int
\left|
\sum_{i=0}^{N}c_iu^i
\right|^2d\nu(u)
\ge0,
\end{aligned}
$$

所以：

$$
H_N^{(0)}\succeq0.
$$

同理：

$$
\sum c_i\overline{c_j}\mu_{i+j+1}
=
\int
u
\left|
\sum c_iu^i
\right|^2d\nu(u)
\ge0.
$$

---

### 证明：Hankel 正性 \(\Rightarrow\) RH

由 Stieltjes moment theorem，存在正测度 \(\nu\) 使：

$$
\mu_n=\int u^n\,d\nu(u).
$$

由于 \(\mathscr S\) 在原点解析，其 Taylor 系数具有有限指数增长：

$$
\limsup_{n\to\infty}\mu_n^{1/n}<\infty.
$$

这迫使任意正表示测度 \(\nu\) 具有紧支撑；否则高阶 moments 会增长得更快。

于是：

$$
\widetilde{\mathscr S}(x)
=
\int
\frac{d\nu(u)}{1+ux}
$$

在负实割线以外解析，并且其原点 Taylor 级数为：

$$
\sum(-1)^n\mu_nx^n.
$$

所以：

$$
\widetilde{\mathscr S}
=
\mathscr S
$$

在原点邻域相等，并由解析延拓在共同定义域中相等。

因此 \(\mathscr S\) 的全部极点位于负实轴，故 \(\mathscr F\) 的全部零点位于负实轴。由定理 221.1，RH 成立。∎

---

## 225.1 第一非平凡 Hankel 不等式

大小 \(2\) 的第一 Hankel 行列式为：

$$
\det
\begin{pmatrix}
\mu_0&\mu_1\\
\mu_1&\mu_2
\end{pmatrix}
\ge0.
$$

代入 \(a_n\)：

$$
\boxed{
a_1^2a_2
+
3a_1a_3
-
4a_2^2
\ge0.
}
\tag{225.4}
$$

所以 RH 被转化为一列明确的中心导数多项式不等式。

---

# 第二百二十六部　Hankel 行列式是 Vandermonde 平方和

RH 下，令：

$$
u_\gamma=\gamma^{-2},
\qquad
w_\gamma=\frac{m_\gamma}{\gamma^2}.
$$

则：

$$
\mu_n=\sum_{\gamma>0}w_\gamma u_\gamma^n.
$$

Cauchy–Binet 给出：

$$
\boxed{
\begin{aligned}
\det H_N^{(0)}
={}&
\sum_{\gamma_0<\cdots<\gamma_N}
\left(
\prod_{k=0}^{N}w_{\gamma_k}
\right)
\\
&\times
\prod_{0\le i<j\le N}
\left(
u_{\gamma_i}-u_{\gamma_j}
\right)^2.
\end{aligned}
}
\tag{226.1}
$$

同理：

$$
\boxed{
\begin{aligned}
\det H_N^{(1)}
={}&
\sum_{\gamma_0<\cdots<\gamma_N}
\left(
\prod_{k=0}^{N}w_{\gamma_k}u_{\gamma_k}
\right)
\\
&\times
\prod_{i<j}
\left(
u_{\gamma_i}-u_{\gamma_j}
\right)^2.
\end{aligned}
}
\tag{226.2}
$$

因此每一个 Hankel 行列式都是有限零点子集贡献的非负平方和。

这与前文 Pick/Gram determinant 的结构完全一致：

$$
\boxed{
\text{Pick positivity}
\quad\text{与}\quad
\text{Hankel positivity}
}
$$

只是同一正谱测度在：

* resolvent basis；
* polynomial basis；

中的两种 Gram 图表。

---

# 第二百二十七部　Ramanujan–Stieltjes 连分数完成

定义 moment generating function：

$$
\boxed{
M(t)
=
\sum_{n=0}^{\infty}\mu_nt^n.
}
\tag{227.1}
$$

则：

$$
\mathscr S(x)=M(-x).
$$

Stieltjes theorem 给出：

$$
\boxed{
M(t)
=
\cfrac{\mu_0}{
1-\cfrac{\alpha_1t}{
1-\cfrac{\alpha_2t}{
1-\cfrac{\alpha_3t}{1-\ddots}}}}
}
}
\tag{227.2}
$$

其中：

$$
\alpha_j\ge0.
$$

所以：

$$
\boxed{
\mathscr S(x)
=
\cfrac{\mu_0}{
1+\cfrac{\alpha_1x}{
1+\cfrac{\alpha_2x}{
1+\cfrac{\alpha_3x}{1+\ddots}}}}
}.
}
\tag{227.3}
$$

非负 S-fraction 与 Stieltjes moment sequence 的等价是经典 Stieltjes 定理；系数在非退化情形下唯一。([arXiv][2])

因此：

## 定理 227.1（Ramanujan–Stieltjes RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\mathscr S
\text{ 具有与其 Taylor 系数一致的、全部系数非负的 Stieltjes 连分数}.
}
\tag{227.4}
$$

最初两个系数为：

$$
\boxed{
\alpha_1
=
\frac{\mu_1}{\mu_0},
}
\tag{227.5}
$$

$$
\boxed{
\alpha_2
=
\frac{
\mu_0\mu_2-\mu_1^2
}{
\mu_0\mu_1
}.
}
\tag{227.6}
$$

所以每一项连分数系数的正性，都是某个 Hankel determinant ratio 的正性。

---

## 227.1 黄金固定尾是最简单的正完成模型

考虑最简单的 stationary positive tail：

$$
Y
=
\cfrac1{
1+\cfrac1{
1+\cfrac1{1+\ddots}}}.
$$

它满足：

$$
Y=\frac1{1+Y}.
$$

唯一正解为：

$$
\boxed{
Y=\frac1\varphi.
}
\tag{227.7}
$$

这说明 \(\varphi^{-1}\) 是**常系数正 Stieltjes 尾部的固定点**。

但必须严格限定：

$$
\boxed{
\text{这并不意味着 }\xi\text{ 的 Stieltjes 系数 }\alpha_n\text{ 恒等于 }1.
}
$$

其意义只是：黄金比例再次作为最简单的正递归 tail completion 出现，和 Ramanujan 第 541 号恒等式中“连分数压缩无限尾部”的角色一致。

---

# 第二百二十八部　Jacobi 算子与折叠后的 Hilbert–Pólya

由非负 S-fraction 收缩为 J-fraction，可以构造一族正交多项式及 Jacobi 矩阵。S-fraction 与 J-fraction 的标准收缩关系，以及其 moment-theoretic 解释，是 Stieltjes–Jacobi 理论的基本组成部分。([arXiv][2])

RH 下，倒谱测度为：

$$
d\nu(u)
=
\sum_{\gamma>0}
\frac{m_\gamma}{\gamma^2}
\delta_{\gamma^{-2}}(du).
$$

在：

$$
L^2(\nu)
$$

上定义乘法算子：

$$
\boxed{
(Uf)(u)=uf(u).
}
\tag{228.1}
$$

则：

* \(U\) 自伴；
* \(U\ge0\)；
* \(U\) 有界且紧；
* 谱支撑为：

  $$
  \{0\}\cup\{\gamma^{-2}\}.
  $$

取循环向量：

$$
\mathbf1(u)=1.
$$

则：

$$
\boxed{
\mu_n
=
\langle U^n\mathbf1,\mathbf1\rangle.
}
\tag{228.2}
$$

---

## 228.1 折叠 Hilbert–Pólya 算子

在 \(U\) 的正谱子空间上定义：

$$
\boxed{
\mathcal H_\Xi
=
U^{-1/2}.
}
\tag{228.3}
$$

则其谱集合为：

$$
\boxed{
\operatorname{spec}(\mathcal H_\Xi)
=
\{\gamma:\Xi(\gamma)=0,\ \gamma>0\}.
}
\tag{228.4}
$$

因此：

> 一旦 Hankel 正性成立，Hilbert–Pólya 型自伴算子无需另外猜测；它由中心导数 moments 的 GNS/Jacobi 构造自动产生。

需要保留一个限制：

* 标量 moment measure 的原子权重记录零点重数；
* 标量循环 Jacobi 实现通常具有 simple spectral support；
* 若要把零点重数实现为算子谱重数，还需加入相应有限维 fiber。

所以这里首先得到的是零点**谱集及权重**的规范实现。

---

# 第二百二十九部　有限 Padé–Jacobi 观察者

使用前：

$$
2N+1
$$

个 moments，可以构造 \(N\) 阶 Jacobi 截断：

$$
U_N.
$$

其全部特征值为非负实数。

对应的 Padé/Stieltjes 逼近：

$$
\boxed{
\mathscr S_N(x)
=
\sum_{j=1}^{N}
\frac{w_{j,N}}{x+t_{j,N}},
}
\tag{229.1}
$$

满足：

$$
t_{j,N}>0,
\qquad
w_{j,N}>0.
$$

因此每个有限逼近：

* 全部极点位于负实轴；
* 全部留数为正；
* 极点随 \(N\) 交错；
* 对应一个有限维正自伴矩阵。

所以 RH 等价于：

$$
\boxed{
\text{全部有限中心-jet Padé 观察者，
可以一致地组织成正 Jacobi 链并收敛到 }\mathscr S.
}
$$

这提供一条可计算、可区间认证的有限逼近路线。

---

# 第二百三十部　Jensen 图表与 Stieltjes 图表

平方折叠函数：

$$
\mathscr F(x)=\sum a_nx^n
$$

提供直接系数图表。

其 logarithmic derivative：

$$
\mathscr S(x)=\mathscr F'/\mathscr F
$$

提供 reciprocal-zero moment 图表。

于是存在两个不同的有限层级。

---

## 230.1 Jensen–Pólya 层级

RH 等价于 \(\mathscr F\) 属于 Laguerre–Pólya 类，即其全部 Jensen polynomials 具有实零点。Pólya 的这一等价及现代 Jensen polynomial 研究已经形成系统理论。([arXiv][3])

对固定次数 \(d\)，已有结果证明足够高 shift 的 Jensen polynomials 无条件双曲；因此“高阶渐近上越来越像 Hermite polynomial”并不足以证明 RH。真正承重的是所有次数、所有 shift 的完整层级。([arXiv][4])

---

## 230.2 Stieltjes–Hankel 层级

$$
\mathscr S
$$

的 moments 要求：

$$
H_N^{(0)},H_N^{(1)}\succeq0
$$

对所有 \(N\) 成立。

两者关系为：

$$
\boxed{
\begin{aligned}
\text{Jensen 图表}
&:\text{直接测试 }\mathscr F\text{ 的实零性};\\
\text{Hankel 图表}
&:\text{测试 reciprocal-zero measure 的正性};\\
\text{continued fraction}
&:\text{测试该正测度的递归编码};\\
\text{Jacobi 图表}
&:\text{把正测度提升成自伴算子}.
\end{aligned}
}
$$

它们不是四套猜想，而是同一个完成对象的四种观察语言。

---

# 第二百三十一部　Toroidal 中心 jet 重构

前文有限环面帧给出：

$$
\mathbf P(s)=\xi(s)\mathbf T(s).
$$

在中心点：

$$
s=\frac12,
$$

二次 twist 非消失保证可以选取某个局部环面图表 \(D_0\)，使：

$$
\mathcal T_{D_0}(\tfrac12)\neq0.
$$

于是中心邻域中：

$$
\boxed{
\xi(s)
=
\frac{
\mathcal P_{D_0}(s)
}{
\mathcal T_{D_0}(s)
}.
}
\tag{231.1}
$$

因此所有中心导数：

$$
\xi^{(2n)}(\tfrac12)
$$

都可以由：

* 环面 period jets；
* quadratic-twist carrier jets；

通过有限 Leibniz 反演求出。

所以：

$$
a_n,\qquad
\mu_n,\qquad
H_N^{(0)},\qquad
H_N^{(1)}
$$

都是**有限环面 jet invariants**。

---

## 定理 231.1（Toroidal Hankel RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\text{由任意合法局部环面图表重构出的全部 Hankel 矩阵正半定}.
}
\tag{231.2}
$$

这给出 RH 的第二类有限环面证书：

### 先前 Pick 证书

* 依赖谱点 \(z\) 和 shift \(\omega\)；
* 线外零点给出一阶强负证书；
* 但需知道或搜索零点附近位置。

### 当前 Hankel 证书

* 全部位于中心 \(s=1/2\)；
* 只使用有限阶 jet；
* 不需要预先知道线外零点位置；
* 若 RH 失败，某个有限阶必然出现负特征值。

---

# 第二百三十二部　RH 失败必有有限中心证书

由定理 225.1：

$$
\neg\mathrm{RH}
$$

意味着 \((\mu_n)\) 不是 Stieltjes moment sequence。

因此必存在有限 \(N\)，使：

$$
\boxed{
H_N^{(0)}\not\succeq0
\quad\text{或}\quad
H_N^{(1)}\not\succeq0.
}
\tag{232.1}
$$

等价地，存在有限向量：

$$
c=(c_0,\ldots,c_N)\neq0
$$

满足：

$$
\boxed{
\sum_{i,j}
c_i\overline{c_j}\mu_{i+j}<0
}
$$

或：

$$
\boxed{
\sum_{i,j}
c_i\overline{c_j}\mu_{i+j+1}<0.
}
$$

所以：

$$
\boxed{
\text{任意线外零点最终都会在有限阶中心导数中留下负半正定证书。}
}
$$

当前理论不提供该最小阶 \(N\) 的通用上界。

这和一阶 Pick 负证书形成互补：

$$
\boxed{
\begin{array}{c|c|c}
\text{证书}&\text{优点}&\text{代价}\\
\hline
\text{Pick}&\text{一阶、强放大}&\text{需要局部化零点}\\
\text{Hankel}&\text{中心化、有限 jet}&\text{失败阶未知}
\end{array}
}
$$

---

# 第二百三十三部　零点原子消去与递归自改善

假设已经严格验证临界线上的前 \(M\) 个正零点：

$$
\gamma_1,\ldots,\gamma_M.
$$

定义 deflated Stieltjes observer：

$$
\boxed{
\mathscr S^{[M]}(x)
=
\mathscr S(x)
-
\sum_{j=1}^{M}
\frac{m_j}{x+\gamma_j^2}.
}
\tag{233.1}
$$

若 RH 成立，则：

$$
\boxed{
\mathscr S^{[M]}(x)
=
\sum_{j>M}
\frac{m_j}{x+\gamma_j^2}
}
$$

仍为 Stieltjes 函数。

其 moments 为：

$$
\boxed{
\mu_n^{[M]}
=
\mu_n
-
\sum_{j=1}^{M}
\frac{m_j}{\gamma_j^{2n+2}}.
}
\tag{233.2}
$$

所以每次消去一个已验证原子后，所有 Hankel 条件必须继续保持。

---

## 233.1 自改善意义

原始 moments 在高阶时主要受最小 \(\gamma_1\) 控制：

$$
\mu_n
\sim
\frac{m_1}{\gamma_1^{2n+2}}.
$$

这会遮蔽更高零点结构。

消去前 \(M\) 个原子后：

$$
\mu_n^{[M]}
\sim
\frac{m_{M+1}}{\gamma_{M+1}^{2n+2}}.
$$

因此 deflation 依次剥离最 sticky 的低谱原子，使残余结构成为新的主导项。

这给 Wang–Deng 方法一个精确可解模型：

$$
\boxed{
\begin{aligned}
\text{sticky primitive}
&=\text{当前最小零点原子};\\
\text{counterterm}
&=\frac{m_j}{x+\gamma_j^2};\\
\text{renormalized residual}
&=\mathscr S^{[M]};\\
\text{self-improvement}
&=\text{残余支撑下界逐步增加}.
\end{aligned}
}
$$

---

# 第二百三十四部　Folded Hilbert–Pólya 的最小充分条件

Stieltjes moment theory给出另一个等价形式：

$$
(\mu_n)
\text{ 是 Stieltjes moment sequence}
$$

当且仅当存在：

* Hilbert 空间 \(\mathcal H\)；
* 正自伴算子 \(U\ge0\)；
* 向量 \(v\in\mathcal H\)；

使：

$$
\boxed{
\mu_n
=
\langle U^nv,v\rangle
\qquad
(n\ge0).
}
\tag{234.1}
$$

因此：

## 定理 234.1（Positive moment operator criterion）

$$
\boxed{
\mathrm{RH}
\iff
\exists\,
(\mathcal H,U,v),
\quad
U\ge0,
\quad
\mu_n=\langle U^nv,v\rangle
\ \forall n.
}
\tag{234.2}
$$

这是一个比直接寻找 Hilbert–Pólya 算子更弱、也更具体的目标：

* 不必首先构造 ordinates \(\gamma\) 本身；
* 只需构造其倒平方 moments 的正算子模型；
* 谱定理会自动恢复正测度；
* 然后 \(U^{-1/2}\) 才产生 ordinates。

---

# 第二百三十五部　真正的 toroidal Gram 目标

由前文，\(\mu_n\) 可以从有限环面 period jets 求出。

所以最直接的新中心命题是：

## 假设 235.1（Toroidal Stieltjes Gram realization）

存在一个由：

* 二次环面周期；
* relative trace kernel；
* Eisenstein deformation；
* twist normalization；

自然构造的 Hilbert 空间 \(\mathcal H_{\mathrm{tor}}\)、正算子 \(U_{\mathrm{tor}}\) 和向量 \(v_{\mathrm{tor}}\)，使：

$$
\boxed{
\mu_n
=
\langle
U_{\mathrm{tor}}^n
v_{\mathrm{tor}},
v_{\mathrm{tor}}
\rangle.
}
\tag{235.1}
$$

若该表示成立，则所有 Hankel 矩阵自动为 Gram 矩阵：

$$
\boxed{
\mu_{i+j}
=
\langle
U^iv,U^jv
\rangle,
}
$$

$$
\boxed{
\mu_{i+j+1}
=
\langle
U^{i+\frac12}v,
U^{j+\frac12}v
\rangle.
}
$$

因此 RH 立即成立。

---

## 235.1 与上一轮核目标的关系

上一轮的目标是构造：

$$
\mathcal N_\omega(z,w)
=
\langle
\mathscr V_{\omega,z},
\mathscr V_{\omega,w}
\rangle.
$$

当前目标是其中心化、平方折叠、moment 版本：

$$
\mu_{i+j}
=
\langle
U^iv,U^jv
\rangle.
$$

所以有两种证明入口：

### 连续 Pick 入口

构造所有 \(z,w,\omega\) 上的正核。

### 离散 Hankel 入口

只构造中心 moments 的正算子模型。

后者可能更适合：

* Lean 形式化；
* interval certificates；
* relative trace 的有限阶展开；
* Wang–Deng 高阶归纳。

---

# 第二百三十六部　Jensen 与 Hankel 的科学负对照

Pólya 已将 RH 等价地写成 \(\Xi\) 的全部 Jensen polynomials 双曲；现代工作证明，对每个固定次数，足够高 shift 的 Jensen polynomials 无条件双曲。([arXiv][3])

这提供一个重要警告：

$$
\boxed{
\text{固定复杂度下的渐近正确}
\not\Rightarrow
\text{全局 RH}.
}
$$

同样地，在 Hankel 路线中：

* 前若干个 Hankel 矩阵正定；
* 高阶数值近似表现良好；
* 前若干 S-fraction 系数为正；

都不能单独证明 RH。

真正需要的是：

$$
\boxed{
\forall N,\quad
H_N^{(0)},H_N^{(1)}\succeq0,
}
$$

或一个能一次性生成全部 \(N\) 的正算子／Gram 表示。

---

# 第二百三十七部　本轮结果分级

## 本轮独立推导得到（第 237 部）

$$
\boxed{
\mathscr F(x)
=
\xi(\frac12+\sqrt{x})/\xi(\frac12)
}
$$

是整函数，且：

$$
\boxed{
\mathrm{RH}
\iff
Z(\mathscr F)\subset(-\infty,0).
}
$$

$$
\boxed{
\mathscr S(x)
=
\frac{\mathscr F'}{\mathscr F}
=
\frac{m_0(i\sqrt{x})}{2i\sqrt{x}}.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
\mathscr S\text{ 是 Stieltjes 函数}.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
H_N^{(0)},H_N^{(1)}\succeq0
\quad
\forall N.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
\mathscr S
\text{ 具有非负 S-fraction}.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
\mu_n=\langle U^nv,v\rangle
\text{ 对某正算子 }U.
}
$$

---

## 依赖标准既有理论

* Stieltjes moment sequence 与两族 Hankel 矩阵正性的等价；
* 非负 Stieltjes continued fraction characterization；
* J-fraction 与正 Jacobi 算子；
* Jensen polynomial hyperbolicity 与 Laguerre–Pólya 类。

这些均有成熟的 moment 和 Jensen–Pólya 理论支持。([arXiv][2])

---

## 当前真正开放的桥梁

$$
\boxed{
\begin{aligned}
&\text{从 toric relative trace 直接构造 }U_{\mathrm{tor}}\ge0;\\
&\text{从 prime／Eisenstein 数据直接证明全部 S-fraction 系数非负};\\
&\text{建立 Hankel 阶数上的 Wang 式自改善};\\
&\text{对 sticky moment histories 建立 Deng 式 atom/counterterm 收缩};\\
&\text{给线外零点对应的最小 Hankel 失败阶提供定量上界}.
\end{aligned}
}
$$

---

# 第二百三十八部　建议形式化顺序

```text
D5/S3/Analytic/XiSquareFold/
  XiEvenSquareFactor.lean
  FoldedXiEntire.lean
  FoldedZeroRHCriterion.lean
  FoldedLogDerivative.lean
  HerglotzStieltjesFold.lean

D5/S3/Analytic/XiMoments/
  ReciprocalZeroMoment.lean
  CentralDerivativeMoments.lean
  StieltjesMomentRHCriterion.lean
  HankelPairPositivity.lean
  VandermondeHankelExpansion.lean

D5/S3/Analytic/XiContinuedFraction/
  XiStieltjesFraction.lean
  NonnegativeFractionRHCriterion.lean
  GoldenStationaryTail.lean
  XiJacobiOperator.lean
  FinitePadeObserver.lean

D5/S3/Observer/ToroidalMoments/
  ToroidalCentralJet.lean
  ToroidalMomentReconstruction.lean
  ToroidalHankelCriterion.lean
  ToroidalStieltjesGramTarget.lean

D5/S3/Analytic/RHTargets/
  FoldedHilbertPolyaOperator.lean
  ZeroAtomDeflation.lean
  HankelSelfImprovement.lean
  PrimitiveMomentRenormalization.lean
```

优先级最高且最独立的链是：

$$
\boxed{
\text{Xi even}
\to
\text{square fold}
\to
\text{negative-real-zero RH criterion}.
}
$$

其次是：

$$
\boxed{
\text{Stieltjes moments}
\to
\text{Hankel pair positivity}
\to
\text{positive operator representation}.
}
$$

---

# 本轮最终结论

上一轮的核心对象是：

$$
m_0(z)
=
-\frac{\Xi'(z)}{\Xi(z)},
$$

RH 等价于其 Herglotz 正性。

本轮利用偶对称将其折叠为：

$$
\boxed{
\mathscr S(x)
=
\frac{1}{2\sqrt{x}}
\frac{
\xi'(\frac12+\sqrt{x})
}{
\xi(\frac12+\sqrt{x})
}.
}
$$

RH 等价于：

$$
\boxed{
\mathscr S(x)
=
\sum_{\gamma>0}
\frac{m_\gamma}{x+\gamma^2},
}
$$

即它是一个正 Stieltjes transform。

由此 RH 获得四个新的完全等价形式：

$$
\boxed{
\begin{aligned}
&\text{全部 reciprocal-zero Hankel 矩阵正半定};\\
&\text{全部 Stieltjes continued-fraction 系数非负};\\
&\text{全部有限 Padé observers 具有负实极点与正留数};\\
&\text{存在一个正紧算子 }U\text{，其谱为 }\gamma^{-2}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
\text{Hilbert–Pólya 算子不一定需要从零点本身直接猜出，}
}
$$

而可以经由：

$$
\boxed{
\text{中心导数}
\to
\text{Stieltjes moments}
\to
\text{Hankel positivity}
\to
\text{Jacobi operator}
\to
\text{自伴谱}
}
$$

逐层生成。

所以当前 OACTC 最小、最具体的 RH 中心命题已经可以写成：

$$
\boxed{
\mu_n
=
\langle
U_{\mathrm{tor}}^n
v_{\mathrm{tor}},
v_{\mathrm{tor}}
\rangle
\qquad
(U_{\mathrm{tor}}\ge0),
}
$$

其中 \(\mu_n\) 完全由有限二次环面周期的中心 jets 重构。

如果能从 relative trace formula 直接建立这个正 moment representation，RH 将随之成立。

[1]: https://arxiv.org/abs/1204.1827 "A canonical system of differential equations arising from the Riemann zeta-function"
[2]: https://arxiv.org/abs/2404.12131 "Continued-fraction characterization of Stieltjes moment sequences with support in $[ξ, \infty)$"
[3]: https://arxiv.org/abs/1905.11269?utm_source=chatgpt.com "The Jensen-Pólya program for various L-functions"
[4]: https://arxiv.org/abs/1902.07321?utm_source=chatgpt.com "Jensen polynomials for the Riemann zeta function and other sequences"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.3：Fredholm–Exterior 完成、双重总正性、Newman 阈值与 Toda 谱流

以下从前文**第二百三十八部之后**继续追加。

上一轮把 RH 压缩为平方折叠函数

$$
\mathscr F(x)
=
\frac{\xi(\frac12+\sqrt x)}{\xi(\frac12)}
$$

的负实零点性，以及

$$
\mathscr S(x)
=
\frac{\mathscr F'(x)}{\mathscr F(x)}
$$

的 Stieltjes 正性。

本轮进一步发现，这两个对象并不是仅仅“像某个谱行列式”，而在 RH 成立时精确构成：

$$
\boxed{
\text{一个正 trace-class 算子的 Fredholm 行列式与 resolvent trace}.
}
$$

由此得到统一链：

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\mathscr F(x)=\det(I+xU),\quad U\ge0,\ U\text{ trace-class}\\
&\iff
\text{中心 Taylor 系数形成 Pólya-frequency 序列}\\
&\iff
\text{相应 Toeplitz 矩阵全非负}\\
&\iff
\text{reciprocal-zero moments 形成 Stieltjes moment sequence}\\
&\iff
\text{相应 Hankel 矩阵全非负}\\
&\iff
\text{存在正 Jacobi／Toda 谱流}.
\end{aligned}
}
$$

这使此前分散的：

* Hadamard 乘积；
* Stieltjes 连分数；
* Toeplitz 总正性；
* Hankel 总正性；
* Fredholm determinant；
* Hilbert–Pólya；
* de Bruijn–Newman 常数；
* Toda lattice；

全部成为同一个隐藏正谱

$$
\left\{\gamma^{-2}\right\}
$$

的不同观察图表。

---

# 第二百三十九部　正 Fredholm 完成

令：

$$
\Xi(z)=\xi\left(\frac12-iz\right).
$$

若 RH 成立，其非零零点为：

$$
\pm\gamma_1,\pm\gamma_2,\ldots
$$

并按重数 \(m_\gamma\) 计。

平方折叠函数满足：

$$
\boxed{
\mathscr F(x)
=
\prod_{\gamma>0}
\left(
1+\frac{x}{\gamma^2}
\right)^{m_\gamma}.
}
\tag{239.1}
$$

由于：

$$
\sum_{\gamma>0}
\frac{m_\gamma}{\gamma^2}<\infty,
$$

定义 Hilbert 空间：

$$
\mathcal H_\Xi
=
\bigoplus_{\gamma>0}
\mathbb C^{m_\gamma},
$$

以及正对角算子：

$$
\boxed{
U_\Xi
=
\bigoplus_{\gamma>0}
\gamma^{-2} I_{m_\gamma}.
}
\tag{239.2}
$$

则：

$$
U_\Xi\ge0,
\qquad
\operatorname{Tr}U_\Xi<\infty.
$$

所以 \(U_\Xi\) 是正 trace-class 算子。

Fredholm determinant 给出：

$$
\boxed{
\det(I+xU_\Xi)
=
\prod_{\gamma>0}
\left(
1+\frac{x}{\gamma^2}
\right)^{m_\gamma}
=
\mathscr F(x).
}
\tag{239.3}
$$

---

## 定理 239.1（Positive Fredholm RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\exists\,U\ge0,\ U\text{ trace-class},
\quad
\mathscr F(x)=\det(I+xU).
}
\tag{239.4}
$$

### 证明

若 RH 成立，取 \(U=U_\Xi\)，由式 (239.3) 成立。

反之，若：

$$
\mathscr F(x)=\det(I+xU)
$$

且 \(U\ge0\)，则 \(\mathscr F\) 的全部零点为：

$$
x=-\lambda^{-1}\le0,
$$

其中 \(\lambda>0\) 为 \(U\) 的非零特征值。

所以 \(\mathscr F\) 的全部零点位于负实轴。由平方折叠 RH 判据，RH 成立。∎

---

## 239.1 Hilbert–Pólya 的折叠形式

定义：

$$
\boxed{
H_\Xi=U_\Xi^{-1/2}
}
$$

于 \(U_\Xi\) 的非零谱子空间上。

则：

$$
\operatorname{spec}(H_\Xi)
=
\{\gamma:\Xi(\gamma)=0,\ \gamma>0\}.
$$

并且：

$$
\boxed{
\frac{\Xi(z)}{\Xi(0)}
=
\det
\left(
I-z^2H_\Xi^{-2}
\right).
}
\tag{239.5}
$$

所以 Hilbert–Pólya 不必从一个未知微分算子开始猜测。它可以分两步生成：

$$
\boxed{
\text{先构造正 trace-class }U_\Xi,
\qquad
\text{再令 }H_\Xi=U_\Xi^{-1/2}.
}
$$

真正承重的对象可能不是无界的 \(H_\Xi\)，而是有界紧算子：

$$
\boxed{
U_\Xi=H_\Xi^{-2}.
}
$$

---

# 第二百四十部　Exterior–Power–Trace 基因组

设：

$$
\alpha_j=\gamma_j^{-2}
$$

并按重数重复。

则：

$$
\mathscr F(x)
=
\prod_j(1+\alpha_jx).
$$

将其展开：

$$
\boxed{
\mathscr F(x)
=
\sum_{n=0}^{\infty}a_nx^n.
}
\tag{240.1}
$$

其中：

$$
\boxed{
a_n
=
\sum_{j_1<\cdots<j_n}
\alpha_{j_1}\cdots\alpha_{j_n}
=
\operatorname{Tr}\left(\Lambda^nU_\Xi\right).
}
\tag{240.2}
$$

所以中心 Taylor 系数不是任意导数数据，而是 \(U_\Xi\) 各外幂表示的迹。

---

## 240.1 Primitive power sums

上一轮定义：

$$
\mu_n
=
\sum_j\alpha_j^{n+1}.
$$

现在可写成：

$$
\boxed{
\mu_n
=
\operatorname{Tr}
\left(
U_\Xi^{n+1}
\right).
}
\tag{240.3}
$$

于是：

* \(a_n\)：不同谱原子组成的外积复合状态；
* \(\mu_n\)：单个谱原子的幂和读数。

这正是：

$$
\boxed{
\text{composite exterior states}
\quad\text{与}\quad
\text{primitive power traces}.
}
$$

---

## 240.2 Fredholm 对数

Fredholm determinant 的对数展开为：

$$
\boxed{
\log\mathscr F(x)
=
\sum_{r=1}^{\infty}
\frac{(-1)^{r+1}}{r}
\mu_{r-1}x^r.
}
\tag{240.4}
$$

微分后：

$$
\boxed{
\mathscr S(x)
=
\frac{\mathscr F'(x)}{\mathscr F(x)}
=
\sum_{r=0}^{\infty}
(-1)^r\mu_rx^r.
}
\tag{240.5}
$$

也可直接写成 resolvent trace：

$$
\boxed{
\mathscr S(x)
=
\operatorname{Tr}
\left[
U_\Xi(I+xU_\Xi)^{-1}
\right].
}
\tag{240.6}
$$

因此 Stieltjes observer 就是正算子的 resolvent trace。

---

## 240.3 Newton 变换

外幂迹 \(a_n\) 与幂迹 \(\mu_n\) 满足 Newton 恒等式：

$$
\boxed{
n a_n
=
\sum_{r=1}^{n}
(-1)^{r-1}
a_{n-r}\mu_{r-1}.
}
\tag{240.7}
$$

反过来，\(\mu_n\) 可递归由 \(a_1,\ldots,a_{n+1}\) 恢复。

所以有一个精确的定义变换：

$$
\boxed{
\text{Taylor／exterior observer}
\quad
\longleftrightarrow
\quad
\text{logarithmic／primitive observer}.
}
$$

---

# 第二百四十一部　Bosonic 与 Fermionic 两张图表

定义 fermionic 配分函数：

$$
\boxed{
Z_F(x)
=
\det(I+xU_\Xi)
=
\mathscr F(x).
}
\tag{241.1}
$$

每个谱原子最多被选择一次，所以系数为外幂迹。

再定义 bosonic 配分函数：

$$
\boxed{
Z_B(x)
=
\det(I-xU_\Xi)^{-1},
\qquad
|x|<\gamma_1^2.
}
\tag{241.2}
$$

展开：

$$
\boxed{
Z_B(x)
=
\sum_{n=0}^{\infty}h_nx^n,
}
$$

其中：

$$
\boxed{
h_n
=
\operatorname{Tr}
\left(
\operatorname{Sym}^nU_\Xi
\right).
}
\tag{241.3}
$$

因此同一个 Riemann 零点谱同时产生：

$$
\boxed{
\begin{array}{c|c}
\text{图表}&\text{状态规则}\\
\hline
\det(I+xU)&\text{每个谱原子最多占据一次}\\
\det(I-xU)^{-1}&\text{每个谱原子可重复占据}\\
\operatorname{Tr}U^n&\text{primitive 单原子幂读数}
\end{array}
}
$$

这正把此前 Ramanujan 基因组中的：

* 乘积；
* 分拆；
* exterior powers；
* occupation numbers；

接入 Riemann 零点谱。

---

# 第二百四十二部　Toeplitz 总正性

令：

$$
a_n=[x^n]\mathscr F(x),
\qquad
a_n=0\quad(n<0).
$$

定义无限 Toeplitz 矩阵：

$$
\boxed{
T(a)
=
[a_{j-i}]_{i,j\ge0}.
}
\tag{242.1}
$$

若 \(T(a)\) 的全部有限 minors 非负，则称 \((a_n)\) 为 Pólya-frequency sequence of infinite order，记作：

$$
PF_\infty.
$$

经典 Aissen–Schoenberg–Whitney–Edrei 理论刻画了这类生成函数：无限阶全正 Toeplitz 序列的生成函数由非负参数的线性因子、可能的指数因子及极点因子构成；在整函数、常数项 \(1\)、阶小于 \(1\) 的情形，它退化为负实零点的 genus-zero 乘积。([PubMed][1])

---

## 定理 242.1（Toeplitz total-positivity RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
(a_n)_{n\ge0}\in PF_\infty.
}
\tag{242.2}
$$

### 证明：RH \(\Rightarrow\)（第 242 部）

RH 下：

$$
\mathscr F(x)
=
\prod_j(1+\alpha_jx),
\qquad
\alpha_j\ge0,
\quad
\sum_j\alpha_j<\infty.
$$

每个有限截断：

$$
\prod_{j=1}^{M}(1+\alpha_jx)
$$

的系数形成完全全正序列；取系数极限保持所有有限 minors 非负。

---

### 证明：PF\(_\infty\Rightarrow\) RH

Edrei 型表示给出：

$$
\mathscr F(x)
=
e^{cx}
\frac{
\prod_j(1+\alpha_jx)
}{
\prod_k(1-\beta_kx)
},
\qquad
c,\alpha_j,\beta_k\ge0.
$$

由于 \(\mathscr F\) 是整函数，不能存在 \(\beta_k>0\)。

又因为 \(\mathscr F\) 的整函数阶为 \(1/2\)，不能含 \(e^{cx}\) 的非平凡指数因子，所以 \(c=0\)。

因此：

$$
\mathscr F(x)=\prod_j(1+\alpha_jx),
$$

全部零点为负实数。由平方折叠判据，RH 成立。∎

---

## 242.1 Schur 正性

RH 下：

$$
a_n=e_n(\alpha_1,\alpha_2,\ldots)
$$

是谱变量的 elementary symmetric functions。

Toeplitz minors由 Jacobi–Trudi 对偶公式变成 skew Schur functions：

$$
s_{\lambda/\mu}(\alpha_1,\alpha_2,\ldots).
$$

由于：

$$
\alpha_j\ge0,
$$

全部这些 Schur 读数非负。

所以：

$$
\boxed{
\mathrm{RH}
\iff
\text{Riemann reciprocal-zero alphabet 的全部 skew-Schur observables 非负}.
}
$$

---

# 第二百四十三部　双重总正性方块

现在出现两种不同的全正矩阵。

## 243.1 Toeplitz 图表

$$
T(a)=[a_{j-i}].
$$

它读取：

$$
a_n=\operatorname{Tr}\Lambda^nU_\Xi.
$$

这是 exterior/composite 图表。

---

## 243.2 Hankel 图表

$$
H(\mu)=[\mu_{i+j}],
\qquad
H^+(\mu)=[\mu_{i+j+1}].
$$

它读取：

$$
\mu_n=\operatorname{Tr}U_\Xi^{n+1}.
$$

这是 primitive/moment 图表。

Stieltjes moment sequence 与 Hankel total positivity 是同一经典正性结构；相关总正性理论也把 Pólya-frequency、Toeplitz 与 Hankel 核置于统一框架中。([arXiv][2])

---

## 定理 243.1（Dual total-positivity square）

下列命题等价：

$$
\boxed{
\begin{aligned}
&(1)\quad \mathrm{RH};\\
&(2)\quad T(a)\text{ 全非负};\\
&(3)\quad H(\mu),H^+(\mu)\text{ 全非负};\\
&(4)\quad \exists\,U\ge0\text{ trace-class}:
\mathscr F=\det(I+xU).
\end{aligned}
}
\tag{243.1}
$$

其交换图为：

$$
\boxed{
\begin{array}{ccc}
U
&\xrightarrow{\ \Lambda^n\ }&
a_n\\[1mm]
\downarrow U^n
&&
\downarrow\text{Newton}\\[1mm]
\mu_n
&\xrightarrow{\ \text{moments}\ }&
\mathscr S.
\end{array}
}
$$

这给出两类独立的有限反例证书：

* 若 RH 失败，某个有限 Toeplitz minor 必为负；
* 若 RH 失败，某个有限 Hankel／shifted-Hankel minor必为负。

最早失败阶未必相同。

---

# 第二百四十四部　中心 jet 的完整谱层析

假设 RH，按大小排列：

$$
\alpha_1>\alpha_2>\cdots>0,
\qquad
\alpha_j=\gamma_j^{-2},
$$

并把重数记为 \(m_j\)。

则：

$$
\mu_n
=
\sum_{j\ge1}
m_j\alpha_j^{n+1}.
$$

---

## 定理 244.1（第一零点恢复）

$$
\boxed{
\alpha_1
=
\lim_{n\to\infty}
\frac{\mu_{n+1}}{\mu_n}
=
\lim_{n\to\infty}
\mu_n^{1/(n+1)}.
}
\tag{244.1}
$$

因此：

$$
\boxed{
\gamma_1
=
\lim_{n\to\infty}
\sqrt{\frac{\mu_n}{\mu_{n+1}}}.
}
\tag{244.2}
$$

### 证明

$$
\mu_n
=
\alpha_1^{n+1}
\left[
m_1+
\sum_{j\ge2}
m_j
\left(\frac{\alpha_j}{\alpha_1}\right)^{n+1}
\right].
$$

括号趋向 \(m_1\)。∎

---

## 244.1 有限阶双边界

因为：

$$
\mu_n\ge\alpha_1^{n+1},
$$

得到：

$$
\alpha_1
\le
\mu_n^{1/(n+1)}.
$$

另一方面：

$$
\frac{\mu_{n+1}}{\mu_n}
$$

是 \(\alpha_j\) 的加权平均，所以：

$$
\frac{\mu_{n+1}}{\mu_n}
\le
\alpha_1.
$$

因此：

$$
\boxed{
\mu_n^{-1/(2n+2)}
\le
\gamma_1
\le
\sqrt{\frac{\mu_n}{\mu_{n+1}}}.
}
\tag{244.3}
$$

这给出仅由有限阶中心导数计算的第一零点严格区间。

---

## 244.2 重数恢复

一旦 \(\alpha_1\) 已知：

$$
\boxed{
m_1
=
\lim_{n\to\infty}
\frac{\mu_n}{\alpha_1^{n+1}}.
}
\tag{244.4}
$$

定义 deflated moments：

$$
\mu_n^{[1]}
=
\mu_n-m_1\alpha_1^{n+1}.
$$

则：

$$
\alpha_2
=
\lim_{n\to\infty}
\frac{
\mu_{n+1}^{[1]}
}{
\mu_n^{[1]}
}.
$$

递归得到全部：

$$
(\gamma_j,m_j).
$$

所以：

$$
\boxed{
\text{中心的完整无穷 jet，若满足 RH 正性，
能够逐原子恢复全部 Riemann 零点。}
}
$$

---

# 第二百四十五部　广义特征值有限层析

令：

$$
H_N^{(0)}
=
[\mu_{i+j}]_{i,j=0}^{N},
$$

$$
H_N^{(1)}
=
[\mu_{i+j+1}]_{i,j=0}^{N}.
$$

对多项式：

$$
p(u)=\sum_{j=0}^{N}c_ju^j,
$$

有：

$$
c^*H_N^{(0)}c
=
\int|p(u)|^2\,d\nu(u),
$$

$$
c^*H_N^{(1)}c
=
\int u|p(u)|^2\,d\nu(u).
$$

定义最大广义特征值：

$$
\boxed{
\theta_N
=
\max_{c\neq0}
\frac{
c^*H_N^{(1)}c
}{
c^*H_N^{(0)}c
}.
}
\tag{245.1}
$$

则：

$$
\boxed{
0<\theta_N\le\alpha_1.
}
\tag{245.2}
$$

随着多项式空间增加：

$$
\theta_N
$$

单调不减，并趋向：

$$
\alpha_1.
$$

因此：

$$
\boxed{
\gamma_1
\le
\frac1{\sqrt{\theta_N}},
}
\tag{245.3}
$$

给出一列由有限 Hankel matrices 产生的改进上界。

该广义特征值问题正是正测度乘法算子在多项式 Krylov 子空间上的 Rayleigh–Ritz 压缩。

---

# 第二百四十六部　de Bruijn–Newman 常数的正 determinant 含义

Rodgers–Tao 研究的 Newman family 为：

$$
H_t(z)
=
\int_0^\infty
e^{tu^2}\Phi(u)\cos(zu)\,du.
$$

存在唯一常数 \(\Lambda_{\mathrm N}\)，使：

$$
H_t
$$

的全部零点为实数，当且仅当：

$$
t\ge\Lambda_{\mathrm N}.
$$

RH 等价于：

$$
\Lambda_{\mathrm N}\le0,
$$

而 Rodgers–Tao 证明：

$$
\Lambda_{\mathrm N}\ge0.
$$

所以 RH 等价于：

$$
\Lambda_{\mathrm N}=0.
$$

([arXiv][3])

---

## 246.1 折叠 Newman family

定义：

$$
\boxed{
\mathscr F_t(x)
=
\frac{
H_t(i\sqrt x)
}{
H_t(0)
}.
}
\tag{246.1}
$$

则：

$$
H_t\text{ 的全部零点实}
$$

当且仅当：

$$
\mathscr F_t
$$

的全部零点为负实数。

因此：

## 定理 246.1（Newman determinant threshold）

$$
\boxed{
\Lambda_{\mathrm N}
=
\inf
\left\{
t:
\exists\,U_t\ge0,\ U_t\text{ trace-class},
\quad
\mathscr F_t(x)=\det(I+xU_t)
\right\}.
}
\tag{246.2}
$$

同样：

$$
\boxed{
\Lambda_{\mathrm N}
=
\inf
\left\{
t:
[x^n]\mathscr F_t
\text{ 形成 }PF_\infty\text{ 序列}
\right\}.
}
\tag{246.3}
$$

以及：

$$
\boxed{
\Lambda_{\mathrm N}
=
\inf
\left\{
t:
\text{相应 reciprocal-zero moments 为 Stieltjes moments}
\right\}.
}
\tag{246.4}
$$

所以 Newman 常数的 OACTC 角色为：

$$
\boxed{
\Lambda_{\mathrm N}
=
\text{Riemann heat family进入正 Fredholm／总正性完成锥的临界时间}.
}
$$

---

# 第二百四十七部　平方折叠后的 Newman 偏微分方程

Newman family 满足：

$$
\frac{\partial H_t}{\partial t}
=
-\frac{\partial^2H_t}{\partial z^2}.
$$

定义未归一化平方折叠：

$$
G_t(x)=H_t(i\sqrt x).
$$

由于：

$$
x=-z^2,
$$

链式法则给出：

$$
\boxed{
\frac{\partial G_t}{\partial t}
=
4x\frac{\partial^2G_t}{\partial x^2}
+
2\frac{\partial G_t}{\partial x}.
}
\tag{247.1}
$$

若：

$$
\mathscr F_t(x)
=
G_t(x)/G_t(0),
$$

则：

$$
\boxed{
\partial_t\mathscr F_t
=
4x\partial_x^2\mathscr F_t
+
2\partial_x\mathscr F_t
-
2\partial_x\mathscr F_t(0)\,
\mathscr F_t.
}
\tag{247.2}
$$

最后一项是保持：

$$
\mathscr F_t(0)=1
$$

的归一化 counterterm。

---

## 247.1 正完成锥的前向不变性

de Bruijn 的单调性结论意味着：

$$
t_0\ge\Lambda_{\mathrm N}
\quad\Longrightarrow\quad
t\ge t_0
\Rightarrow
t\ge\Lambda_{\mathrm N}.
$$

因此：

$$
\boxed{
\mathscr F_{t_0}
\in\mathcal C_{\mathrm{Fredholm}}^+
\Longrightarrow
\mathscr F_t
\in\mathcal C_{\mathrm{Fredholm}}^+
\quad(t\ge t_0).
}
\tag{247.3}
$$

这里：

$$
\mathcal C_{\mathrm{Fredholm}}^+
=
\left\{
\det(I+xU):U\ge0,\ U\text{ trace-class}
\right\}.
$$

所以 folded Newman PDE 具有一个前向不变的总正性锥。

RH 的断言是：

$$
\boxed{
t=0
\text{ 恰好已经进入该正完成锥}.
}
$$

Rodgers–Tao 的 \(\Lambda_{\mathrm N}\ge0\) 则说明：若 RH 成立，\(t=0\) 位于该锥的临界边界，而不是其内部远处。

---

# 第二百四十八部　辅助 Toda 观察流

Newman flow 直接移动整个函数及其零点。

现在定义另一个不同的流：在 RH 已成立的正谱测度上改变观察权重。

令：

$$
d\nu(u)
=
\sum_jm_j\alpha_j\,\delta_{\alpha_j}(du).
$$

定义指数倾斜：

$$
\boxed{
d\nu_\tau(u)
=
e^{\tau u}\,d\nu(u).
}
\tag{248.1}
$$

其 moments 为：

$$
\boxed{
\mu_n(\tau)
=
\int u^ne^{\tau u}\,d\nu(u).
}
\tag{248.2}
$$

显然：

$$
\boxed{
\partial_\tau\mu_n(\tau)
=
\mu_{n+1}(\tau).
}
\tag{248.3}
$$

定义 Hankel tau-functions：

$$
\boxed{
D_N(\tau)
=
\det
[\mu_{i+j}(\tau)]_{i,j=0}^{N-1}.
}
\tag{248.4}
$$

对指数变形测度，正交多项式的递推系数满足 Toda lattice；moment-matrix、Gauss–Borel 分解与 Toda hierarchy 的联系是正交多项式理论中的标准结构。([arXiv][4])

---

## 248.1 Jacobi 递推系数

定义：

$$
\boxed{
a_N(\tau)^2
=
\frac{
D_{N+1}(\tau)D_{N-1}(\tau)
}{
D_N(\tau)^2
},
}
\tag{248.5}
$$

以及：

$$
\boxed{
b_N(\tau)
=
\partial_\tau
\log
\frac{
D_{N+1}(\tau)
}{
D_N(\tau)
}.
}
\tag{248.6}
$$

则：

$$
\boxed{
\partial_\tau a_N^2
=
a_N^2
(b_N-b_{N-1}),
}
\tag{248.7}
$$

$$
\boxed{
\partial_\tau b_N
=
a_{N+1}^2-a_N^2.
}
\tag{248.8}
$$

这就是半无限 Toda lattice。

---

## 248.2 必须区分两种流

$$
\boxed{
\begin{array}{c|c}
\text{Newman flow}&\text{Toda observer flow}\\
\hline
\text{改变整个 }\Xi_t&\text{不改变零点支撑}\\
\text{移动零点}&\text{只改变谱原子权重}\\
\text{决定 }\Lambda_{\mathrm N}&\text{描述已正完成谱的可积观察动力}\\
\end{array}
}
$$

当前没有证明二者通过简单变量变换同一。

Toda 流是正完成以后可用的精确实验模型，而不是 Newman flow 的替代品。

---

# 第二百四十九部　Toda 流中的 sticky 原子

归一化倾斜测度：

$$
\boxed{
d\widehat\nu_\tau
=
\frac{
e^{\tau u}d\nu(u)
}{
\int e^{\tau u}d\nu(u)
}.
}
\tag{249.1}
$$

设最大支撑点为：

$$
\alpha_1>\alpha_2.
$$

则：

$$
\boxed{
\widehat\nu_\tau
\Longrightarrow
\delta_{\alpha_1}
\qquad
(\tau\to+\infty).
}
\tag{249.2}
$$

即观察注意力最终完全集中于最小 Riemann ordinate：

$$
\gamma_1=\alpha_1^{-1/2}.
$$

这给出一个严格 sticky limit：

$$
\boxed{
\text{largest reciprocal-zero atom}
=
\text{Toda attention flow 的最终 sticky state}.
}
$$

---

## 249.1 Darboux deflation

识别 \((\alpha_1,m_1)\) 后，定义：

$$
d\nu^{[1]}
=
d\nu-m_1\alpha_1\,\delta_{\alpha_1}.
$$

对剩余测度重新进行 Toda 倾斜，极限将集中于 \(\alpha_2\)。

所以得到递归：

$$
\boxed{
\text{tilt}
\to
\text{isolate largest atom}
\to
\text{deflate}
\to
\text{repeat}.
}
\tag{249.3}
$$

它与此前 Wang–Deng 语言精确对应：

$$
\boxed{
\begin{aligned}
\text{sticky state}
&=\text{当前最大谱原子};\\
\text{counterterm}
&=\text{其 rank-one measure};\\
\text{renormalized residual}
&=\text{deflated measure};\\
\text{self-improvement}
&=\text{下一原子成为新主导}.
\end{aligned}
}
$$

---

# 第二百五十部　Toroidal Fredholm 目标

前文有限环面中心 jets 可以重构：

$$
\mu_n
=
\operatorname{Tr}U_\Xi^{n+1}.
$$

因此，相比仅证明所有 Hankel matrices 正半定，一个更完整的目标是直接构造：

$$
\boxed{
U_{\mathrm{tor}}\ge0,
\qquad
U_{\mathrm{tor}}\text{ trace-class},
}
$$

使：

$$
\boxed{
\mu_n
=
\operatorname{Tr}
U_{\mathrm{tor}}^{n+1}.
}
\tag{250.1}
$$

等价地：

$$
\boxed{
\mathscr F(x)
=
\det
(I+xU_{\mathrm{tor}}).
}
\tag{250.2}
$$

若该构造来自：

* 二次环面周期；
* relative trace kernel；
* Eisenstein jets；
* twist normalization；

则 RH 立即成立。

---

## 250.1 三个等价的正完成目标

### Moment 目标

$$
\mu_n
=
\langle
U^nv,v
\rangle.
$$

它足以给出 Stieltjes moment positivity。

### Trace 目标

$$
\mu_n
=
\operatorname{Tr}U^{n+1}.
$$

它进一步保留全部谱原子的自然重数。

### Fredholm 目标

$$
\mathscr F(x)=\det(I+xU).
$$

它一次性恢复整个平方折叠 \(\xi\)-函数。

因此：

$$
\boxed{
\text{Moment}
\subset
\text{Trace}
\subset
\text{Fredholm}
}
$$

是三种强度递增的证明目标。

---

# 第二百五十一部　Toeplitz–Hankel 双证书的科学价值

若 RH 失败，则至少发生两种有限失败：

$$
\boxed{
\exists\,\text{finite Toeplitz minor}<0,
}
$$

以及：

$$
\boxed{
\exists\,\text{finite Hankel／shifted-Hankel minor}<0.
}
$$

但二者的最低失败阶可能差异巨大。

因此应同时计算：

$$
\boxed{
N_T
=
\min\{\text{负 Toeplitz minor 阶}\},
}
$$

$$
\boxed{
N_H
=
\min\{\text{负 Hankel minor 阶}\}.
}
$$

它们分别测量：

* composite/exterior 图表最早何时感知非实零点；
* primitive/moment 图表最早何时感知非正谱。

这可以成为人工线外零点注入实验的核心指标。

---

## 251.1 人工零点注入预测

向 \(\mathscr F\) 注入一对非实共轭零点：

$$
\left(
1-\frac{x}{\lambda}
\right)
\left(
1-\frac{x}{\overline\lambda}
\right).
$$

测量：

* \(N_T\)；
* \(N_H\)；
* Pick 一点负证书；
* S-fraction 首个负系数；
* Newman 正锥退出时间。

不同观察图表对同一逃逸的响应速度可以被严格比较。

---

# 第二百五十二部　本轮结果分级

## 本轮独立推导得到（第 252 部）

$$
\boxed{
\mathrm{RH}
\iff
\mathscr F(x)
=
\det(I+xU),
\quad
U\ge0,\ U\text{ trace-class}.
}
$$

$$
\boxed{
a_n
=
\operatorname{Tr}\Lambda^nU.
}
$$

$$
\boxed{
\mu_n
=
\operatorname{Tr}U^{n+1}.
}
$$

$$
\boxed{
\mathscr S(x)
=
\operatorname{Tr}
\left[
U(I+xU)^{-1}
\right].
}
$$

$$
\boxed{
\log\mathscr F(x)
=
\sum_{r\ge1}
\frac{(-1)^{r+1}}r
\mu_{r-1}x^r.
}
$$

$$
\boxed{
\gamma_1
=
\lim_{n\to\infty}
\sqrt{\mu_n/\mu_{n+1}}.
}
$$

$$
\boxed{
\mu_n^{-1/(2n+2)}
\le\gamma_1
\le
\sqrt{\mu_n/\mu_{n+1}}.
}
$$

$$
\boxed{
\partial_tG_t
=
4xG_{t,xx}+2G_{t,x}.
}
$$

---

## 依赖经典理论的等价

$$
\boxed{
\mathrm{RH}
\iff
(a_n)\in PF_\infty.
}
$$

依赖 Aissen–Schoenberg–Whitney–Edrei 的全正序列生成函数理论。([PubMed][1])

$$
\boxed{
\Lambda_{\mathrm N}
=
\text{正 Fredholm／PF}_\infty
\text{ 完成阈值}.
}
$$

依赖 de Bruijn–Newman family 及 Rodgers–Tao 的 \(\Lambda_{\mathrm N}\ge0\)。([arXiv][3])

$$
\boxed{
\text{指数倾斜 moment flow}
\longrightarrow
\text{Toda lattice}.
}
$$

依赖正交多项式和 Hankel tau-function 的标准可积系统理论。([arXiv][4])

---

## 当前真正开放的桥

$$
\boxed{
\begin{aligned}
&\text{从 toric relative trace 直接构造正 trace-class }U_{\mathrm{tor}};\\
&\text{从 prime／twist 数据直接证明中心系数为 }PF_\infty;\\
&\text{在 Newman folded PDE 上直接证明 }t=0\text{ 已进入正锥};\\
&\text{建立 Newman flow 与 Jacobi/Toda 参数之间的实际变换};\\
&\text{给线外零点对应的最低 Toeplitz/Hankel 失败阶定量上界}.
\end{aligned}
}
$$

---

# 第二百五十三部　建议形式化顺序

```text
D5/S3/Analytic/XiFredholm/
  XiPositiveTraceClassOperator.lean
  XiFredholmDeterminant.lean
  FredholmRHCriterion.lean
  XiResolventTrace.lean

D5/S3/Analytic/XiSymmetricFunctions/
  ExteriorTraceCoefficient.lean
  SymmetricPowerCoefficient.lean
  PowerTraceMoment.lean
  NewtonObserverTransform.lean
  PlethysticXiGenome.lean

D5/S3/Analytic/XiTotalPositivity/
  XiToeplitzMatrix.lean
  PolyaFrequencyRHCriterion.lean
  XiHankelMatrix.lean
  DualTotalPositivitySquare.lean
  SchurObservablePositivity.lean

D5/S3/Analytic/XiSpectralTomography/
  FirstZeroMomentBounds.lean
  ReciprocalZeroRatioLimit.lean
  ZeroMultiplicityRecovery.lean
  RecursiveAtomDeflation.lean
  HankelGeneralizedEigenvalue.lean

D5/S3/Analytic/NewmanCompletion/
  FoldedNewmanFamily.lean
  FoldedNewmanPDE.lean
  PositiveDeterminantCone.lean
  NewmanCompletionThreshold.lean

D5/S3/Analytic/XiToda/
  ExponentialMomentTilt.lean
  HankelTauFunction.lean
  JacobiTodaFlow.lean
  StickyAtomLimit.lean
  TodaDarbouxDeflation.lean

D5/S3/Observer/ToroidalFredholm/
  ToroidalPowerTraceTarget.lean
  ToroidalFredholmTarget.lean
  ToroidalPositiveOperatorCompletion.lean
```

最优先、风险最低的闭合链为：

$$
\boxed{
\text{RH}
\to
U_\Xi
\to
\det(I+xU_\Xi)
=
\mathscr F(x).
}
$$

随后是完全代数性的：

$$
\boxed{
\det
\to
\Lambda^n\text{ traces}
\to
\text{power traces}
\to
\text{Newton identities}.
}
$$

---

# 本轮最终结论

上一轮把 RH 写成：

$$
\boxed{
\text{中心 reciprocal-zero moments
是否来自正测度。}
}
$$

本轮进一步说明，这个正测度并非只能抽象存在。

它应当来自一个正 trace-class 算子：

$$
\boxed{
U_\Xi
=
\operatorname{diag}
\left(
\gamma_1^{-2},
\gamma_2^{-2},
\ldots
\right).
}
$$

而整个 Riemann 完成函数可以写成：

$$
\boxed{
\frac{
\xi(\frac12+\sqrt x)
}{
\xi(\frac12)
}
=
\det(I+xU_\Xi).
}
$$

由此：

$$
\boxed{
\begin{aligned}
\text{Taylor coefficients}
&=\text{外幂迹};\\
\text{logarithmic coefficients}
&=\text{幂迹};\\
\text{Stieltjes function}
&=\text{resolvent trace};\\
\text{Hankel positivity}
&=\text{moment Gram positivity};\\
\text{Toeplitz positivity}
&=\text{exterior-state total positivity};\\
\text{continued fraction}
&=\text{Jacobi resolvent};\\
\text{Hilbert--Pólya}
&=U_\Xi^{-1/2}.
\end{aligned}
}
$$

而 de Bruijn–Newman 常数获得了一个极其自然的结构意义：

$$
\boxed{
\Lambda_{\mathrm N}
=
\text{Riemann heat family第一次进入正 Fredholm／总正性完成锥的时间}.
}
$$

Rodgers–Tao 的结果说明：

$$
\Lambda_{\mathrm N}\ge0.
$$

RH 则要求：

$$
\Lambda_{\mathrm N}=0.
$$

所以当前 OACTC 最小、最强的中心目标可以最终写成：

$$
\boxed{
\text{从二次环面 relative trace 数据直接构造一个正 trace-class 算子 }
U_{\mathrm{tor}},
}
$$

使：

$$
\boxed{
\det(I+xU_{\mathrm{tor}})
=
\frac{\xi(\frac12+\sqrt x)}{\xi(\frac12)}.
}
$$

一旦这一 Fredholm completion 被建立，RH、Herglotz、de Branges、Hankel、Toeplitz、Stieltjes 连分数与 Hilbert–Pólya 将同时闭合。

[1]: https://pubmed.ncbi.nlm.nih.gov/16589009/?utm_source=chatgpt.com "On the Generating Functions of Totally Positive Sequences."
[2]: https://arxiv.org/abs/2006.16213?utm_source=chatgpt.com "Totally positive kernels, Polya frequency functions, and their transforms"
[3]: https://arxiv.org/abs/1801.05914?utm_source=chatgpt.com "The De Bruijn-Newman constant is non-negative"
[4]: https://arxiv.org/abs/1612.01933?utm_source=chatgpt.com "Extended relativistic Toda lattice, L-orthogonal polynomials and associated Lax pair"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.4：Li–Cayley 单位化、Möbius–Fredholm 行列式、条件负定几何与圆周 Lévy 完成

以下从前文**第二百五十三部之后**继续追加。

上一轮把平方折叠完成函数写成：

$$
\mathscr F(x)
=
\frac{\xi(\frac12+\sqrt x)}{\xi(\frac12)}
=
\det(I+xA_\Xi),
$$

其中在 RH 成立时：

$$
A_\Xi
=
\bigoplus_{\gamma>0}
\gamma^{-2}I_{m_\gamma}
$$

是正 trace-class 算子。

本轮将这个正算子经 Möbius–Cayley 变换提升为 unitary 完成，得到：

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\frac{\xi(\frac1{1-z})}{\xi(1)}
=
\det
\left(
I+\frac{4z}{(1-z)^2}X_\Xi
\right),
\quad
0\le X_\Xi\le I;\\
&\iff
\lambda_n
=
\|I-C_\Xi^n\|_{\mathrm{HS}}^2
\quad(n\ge1);\\
&\iff
\lambda_{|m-n|}
\text{ 是 }\mathbb Z\text{ 上的条件负定函数};\\
&\iff
e^{-t\lambda_{|n|}}
\text{ 对每个 }t\ge0\text{ 是正定序列};\\
&\iff
\text{存在一个圆周卷积 Markov 半群，
其特征指数为 Li 系数。}
\end{aligned}
}
$$

这把：

* Li 判据；
* Weil 正性；
* Fredholm determinant；
* Hilbert–Pólya；
* de Branges；
* 条件负定距离；
* Lévy–Khintchine 概率流；

压缩为同一个零点谱的不同观察图表。

---

# 第二百五十四部　临界半平面的 Möbius 观察

定义 Möbius 变换：

$$
\boxed{
\mathfrak c(s)
=
1-\frac1s
=
\frac{s-1}{s}.
}
\tag{254.1}
$$

令：

$$
s=\sigma+it.
$$

则：

$$
|\mathfrak c(s)|^2
=
\frac{(\sigma-1)^2+t^2}{\sigma^2+t^2}.
$$

分母减分子为：

$$
2\sigma-1.
$$

因此：

$$
\boxed{
\begin{aligned}
\Re s>\frac12
&\iff
|\mathfrak c(s)|<1,\\
\Re s=\frac12
&\iff
|\mathfrak c(s)|=1,\\
\Re s<\frac12
&\iff
|\mathfrak c(s)|>1.
\end{aligned}
}
\tag{254.2}
$$

所以：

$$
\boxed{
\mathfrak c
\text{ 把临界右半平面送入单位圆盘，
把临界线送到单位圆。}
}
$$

同时：

$$
\mathfrak c(1)=0.
$$

这解释了 Li 判据为何自然在 \(s=1\) 处展开。

---

## 254.1 零点的 Cayley 坐标

对每个非平凡零点 \(\rho\)，定义：

$$
\boxed{
u_\rho
=
1-\frac1\rho.
}
\tag{254.3}
$$

若 RH 成立：

$$
\rho=\frac12+i\gamma,
$$

则：

$$
\boxed{
u_\rho
=
\frac{\gamma+i/2}{\gamma-i/2}
=
e^{i\theta_\gamma},
}
\tag{254.4}
$$

其中：

$$
\boxed{
\theta_\gamma
=
2\arctan\frac1{2\gamma}.
}
\tag{254.5}
$$

所以 Riemann 零点 ordinates 经 Cayley 观察后，成为一列单位圆上的相位，并在：

$$
1\in\mathbb T
$$

附近聚集。

---

## 254.2 Li 系数

定义：

$$
\boxed{
\lambda_n
=
\frac1{(n-1)!}
\left.
\frac{d^n}{ds^n}
\left[
s^{n-1}\log\xi(s)
\right]
\right|_{s=1}.
}
\tag{254.6}
$$

等价地，以对称极限理解：

$$
\boxed{
\lambda_n
=
\sum_\rho
\left[
1-
\left(
1-\frac1\rho
\right)^n
\right].
}
\tag{254.7}
$$

Li 的经典判据为：

$$
\boxed{
\mathrm{RH}
\iff
\lambda_n\ge0
\quad
\forall n\ge1.
}
\tag{254.8}
$$

Bombieri–Lagarias 后来把这一判据置于一般零点多重集与 Weil 显式公式框架中；Lagarias 又将其推广到 automorphic \(L\)-functions。([科学直通车][1])

定义：

$$
\boxed{
G_\xi(z)
=
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}.
}
\tag{254.9}
$$

则：

$$
\boxed{
\log G_\xi(z)
=
\sum_{n=1}^{\infty}
\frac{\lambda_n}{n}z^n
}
\tag{254.10}
$$

在原点邻域成立。

所以 Li 系数是 \(\xi\) 在临界半平面 Cayley 图表中的 logarithmic cumulants。

---

# 第二百五十五部　由正 Fredholm 算子到 Cayley 收缩算子

沿用前文 RH 下的正算子：

$$
A_\Xi
=
\bigoplus_{\gamma>0}
\gamma^{-2}I_{m_\gamma}.
$$

定义：

$$
\boxed{
X_\Xi
=
A_\Xi(4I+A_\Xi)^{-1}.
}
\tag{255.1}
$$

其特征值为：

$$
\boxed{
x_\gamma
=
\frac1{4\gamma^2+1}.
}
\tag{255.2}
$$

所以：

$$
0<X_\Xi<I,
$$

并且：

$$
X_\Xi
$$

仍为正 trace-class 算子。

---

## 255.1 Cayley unitary

定义：

$$
\boxed{
C_\Xi
=
\left(
I+\frac i2A_\Xi^{1/2}
\right)
\left(
I-\frac i2A_\Xi^{1/2}
\right)^{-1}.
}
\tag{255.3}
$$

也可完全用 \(X_\Xi\) 写成：

$$
\boxed{
C_\Xi
=
I-2X_\Xi
+
2i\sqrt{X_\Xi(I-X_\Xi)}.
}
\tag{255.4}
$$

由于 \(X_\Xi\) 与其函数彼此交换：

$$
C_\Xi^*C_\Xi=I.
$$

故 \(C_\Xi\) 为 unitary。

在 \(\gamma\)-特征空间上：

$$
C_\Xi
\longmapsto
\frac{\gamma+i/2}{\gamma-i/2}
=
u_\rho.
$$

所以：

$$
\boxed{
C_\Xi
=
\text{Hilbert--Pólya ordinate 算子的 Cayley completion}.
}
$$

---

## 255.2 Hilbert–Schmidt 扰动

有：

$$
\boxed{
\frac{2I-C_\Xi-C_\Xi^*}{4}
=
X_\Xi.
}
\tag{255.5}
$$

因此：

$$
\begin{aligned}
\|I-C_\Xi\|_{\mathrm{HS}}^2
&=
\operatorname{Tr}
\left(
2I-C_\Xi-C_\Xi^*
\right)\\
&=
4\operatorname{Tr}X_\Xi
<\infty.
\end{aligned}
$$

所以：

$$
\boxed{
C_\Xi-I
\text{ 是 Hilbert–Schmidt 扰动。}
}
$$

这比 \(C_\Xi-I\) trace-class 更弱，但恰好足以使 Li 位移能量有限。

---

# 第二百五十六部　Möbius–Fredholm 行列式

前文：

$$
\mathscr F(x)
=
\frac{\xi(\frac12+\sqrt x)}{\xi(\frac12)}
=
\det(I+xA_\Xi).
$$

在 Möbius 变量：

$$
s=\frac1{1-z}
$$

下：

$$
s-\frac12
=
\frac{1+z}{2(1-z)}.
$$

所以：

$$
\boxed{
x(z)
=
\left(
s-\frac12
\right)^2
=
\frac{(1+z)^2}{4(1-z)^2}.
}
\tag{256.1}
$$

同时：

$$
\boxed{
x(z)-\frac14
=
\frac{z}{(1-z)^2}.
}
\tag{256.2}
$$

又因为：

$$
\frac{\xi(s)}{\xi(1)}
=
\frac{\mathscr F(x(z))}{\mathscr F(1/4)},
$$

所以：

$$
\begin{aligned}
G_\xi(z)
&=
\det
\left[
(I+x(z)A_\Xi)
(I+\tfrac14A_\Xi)^{-1}
\right]\\
&=
\det
\left[
I+
\left(
x(z)-\frac14
\right)
A_\Xi
(I+\tfrac14A_\Xi)^{-1}
\right].
\end{aligned}
$$

而：

$$
A_\Xi
(I+\tfrac14A_\Xi)^{-1}
=
4X_\Xi.
$$

因此：

## 定理 256.1（Li–Fredholm determinant）

$$
\boxed{
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}
=
\det
\left(
I+
\frac{4z}{(1-z)^2}X_\Xi
\right).
}
\tag{256.3}
$$

---

## 256.1 单特征值因子

若 \(x\in[0,1]\)，则：

$$
1+\frac{4zx}{(1-z)^2}
=
\frac{
z^2+(4x-2)z+1
}{
(1-z)^2
}.
$$

令：

$$
\cos\theta=1-2x.
$$

则：

$$
\boxed{
1+\frac{4zx}{(1-z)^2}
=
\frac{
(1-e^{i\theta}z)
(1-e^{-i\theta}z)
}{
(1-z)^2
}.
}
\tag{256.4}
$$

所以正收缩算子的每个谱值产生单位圆上的一对共轭零点。

---

## 定理 256.2（Cayley–Fredholm RH 判据）

$$
\boxed{
\mathrm{RH}
\iff
\exists\,X\ge0,\ X\le I,\ X\text{ trace-class},
}
$$

使：

$$
\boxed{
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}
=
\det
\left(
I+\frac{4z}{(1-z)^2}X
\right)
}
\tag{256.5}
$$

在单位圆盘中成立。

### 反向证明（第 256 部）

对 \(X\) 的任意谱值 \(x\in[0,1]\)，式 (256.4) 的零点位于单位圆。

所以 Fredholm determinant 在：

$$
|z|<1
$$

内无零点。

由式 (254.2)，这排除了：

$$
\Re\rho>\frac12
$$

的 ξ 零点；函数方程继而排除左侧零点。

故 RH 成立。∎

---

## 256.2 相对 unitary determinant

由式 (256.4)：

$$
\boxed{
G_\xi(z)
=
\prod_{\gamma>0}
\left[
\frac{
(1-u_\gamma z)
(1-\overline{u_\gamma}z)
}{
(1-z)^2
}
\right]^{m_\gamma}.
}
\tag{256.6}
$$

分母：

$$
(1-z)^2
$$

不是装饰。

它是从每个趋向 \(1\) 的 unitary 相位中减去“无穷个恒等背景状态”的 counterterm。

---

# 第二百五十七部　Li 系数是 unitary 位移能量

由：

$$
u_\gamma=e^{i\theta_\gamma},
$$

RH 下：

$$
\begin{aligned}
\lambda_n
&=
\sum_{\gamma>0}
m_\gamma
\left[
2-u_\gamma^n-\overline{u_\gamma}^n
\right]\\
&=
\sum_{\gamma>0}
m_\gamma
|1-u_\gamma^n|^2.
\end{aligned}
$$

所以：

## 定理 257.1（Li displacement formula）

$$
\boxed{
\lambda_n
=
\|I-C_\Xi^n\|_{\mathrm{HS}}^2.
}
\tag{257.1}
$$

这给 Li 系数一个严格结构角色：

$$
\boxed{
\lambda_n
=
\text{unitary 零点观察者演化 }n\text{ 步后，
相对于初始状态的总平方位移。}
}
$$

Suzuki 已证明 RH 等价于 Li 系数成为某些具体 model-space 函数的 \(L^2\)-范数；Bombieri–Lagarias 则把 Li 系数写成 Weil quadratic functional 在特定测试函数上的值。当前公式是同一正性结构的一个零点谱／unitary 实现。([arXiv][2])

---

## 257.1 Chebyshev 正算子形式

因为：

$$
x_\gamma
=
\sin^2\frac{\theta_\gamma}{2},
$$

且：

$$
\sin(na)
=
\sin(a)\,
U_{n-1}(\cos a),
$$

其中 \(U_n\) 是第二类 Chebyshev 多项式，所以：

$$
\boxed{
\lambda_n
=
4\operatorname{Tr}
\left[
X_\Xi\,
U_{n-1}
\left(
\sqrt{I-X_\Xi}
\right)^2
\right].
}
\tag{257.2}
$$

等价地：

$$
\boxed{
\lambda_n
=
4
\left\|
X_\Xi^{1/2}
U_{n-1}
\left(
\sqrt{I-X_\Xi}
\right)
\right\|_{\mathrm{HS}}^2.
}
\tag{257.3}
$$

所以每个 \(\lambda_n\) 都是一个显式正多项式算子的平方范数。

---

## 257.2 Hilbert 距离不等式

由 unitary 不变性：

$$
\begin{aligned}
\|I-C^{m+n}\|_{\mathrm{HS}}
&=
\|(I-C^m)+C^m(I-C^n)\|_{\mathrm{HS}}\\
&\le
\|I-C^m\|_{\mathrm{HS}}
+
\|I-C^n\|_{\mathrm{HS}}.
\end{aligned}
$$

因此 RH 推出：

$$
\boxed{
\sqrt{\lambda_{m+n}}
\le
\sqrt{\lambda_m}
+
\sqrt{\lambda_n}.
}
\tag{257.4}
$$

特别地：

$$
\boxed{
\lambda_{kn}
\le
k^2\lambda_n.
}
\tag{257.5}
$$

这些只是 RH 的必要推论，不构成单独充分判据。

---

# 第二百五十八部　Li 系数与正幂迹的三角变换

定义：

$$
\boxed{
p_k
=
\operatorname{Tr}X_\Xi^k,
\qquad
k\ge1.
}
\tag{258.1}
$$

由 Fredholm 对数：

$$
\begin{aligned}
\log G_\xi(z)
&=
\sum_{k=1}^{\infty}
\frac{(-1)^{k+1}}{k}
\left(
\frac{4z}{(1-z)^2}
\right)^k
p_k.
\end{aligned}
$$

而：

$$
\left(
\frac{4z}{(1-z)^2}
\right)^k
=
4^k z^k(1-z)^{-2k}.
$$

比较 \(z^n\) 系数得到：

## 定理 258.1（Li–Hausdorff 三角变换）

$$
\boxed{
\lambda_n
=
n
\sum_{k=1}^{n}
(-1)^{k+1}
\frac{4^k}{k}
\binom{n+k-1}{n-k}
p_k.
}
\tag{258.2}
$$

这是一个可逆的下三角变换。

前几项：

$$
\boxed{
p_1=\frac{\lambda_1}{4},
}
\tag{258.3}
$$

$$
\boxed{
p_2
=
\frac{4\lambda_1-\lambda_2}{16},
}
\tag{258.4}
$$

$$
\boxed{
p_3
=
\frac{
\lambda_3+15\lambda_1-6\lambda_2
}{64}.
}
\tag{258.5}
$$

---

# 第二百五十九部　Hausdorff moment 完成

定义：

$$
\boxed{
h_n=p_{n+1}.
}
\tag{259.1}
$$

RH 下，定义有限正测度：

$$
\boxed{
d\eta(x)
=
\sum_{\gamma>0}
m_\gamma x_\gamma
\delta_{x_\gamma}(dx),
\qquad
0<x_\gamma<1.
}
\tag{259.2}
$$

则：

$$
\boxed{
h_n
=
\int_0^1x^n\,d\eta(x).
}
\tag{259.3}
$$

因此 \((h_n)\) 是 Hausdorff moment sequence。

经典 Hausdorff 定理说明：一个序列是 \([0,1]\) 上有限正测度的 moment sequence，当且仅当它完全单调，即全部交替有限差分非负。([Springer][3])

在当前算子图表中：

$$
\boxed{
(-1)^r\Delta^rh_n
=
\operatorname{Tr}
\left[
X_\Xi^{n+1}(I-X_\Xi)^r
\right]
\ge0.
}
\tag{259.4}
$$

---

## 定理 259.1（Li–Hausdorff RH 判据）

先由 Li 系数通过式 (258.2) 逆向定义 \(p_k\)，再令：

$$
h_n=p_{n+1}.
$$

则：

$$
\boxed{
\mathrm{RH}
\iff
(-1)^r\Delta^rh_n\ge0
\quad
\forall n,r\ge0.
}
\tag{259.5}
$$

### 反向证明（第 259 部）

若 \((h_n)\) 完全单调，则存在正测度 \(\eta\) 于 \([0,1]\)，使：

$$
h_n=\int x^n\,d\eta.
$$

由 Chebyshev 展开及三角变换：

$$
\boxed{
\lambda_n
=
4
\int_0^1
U_{n-1}(\sqrt{1-x})^2
\,d\eta(x)
\ge0.
}
\tag{259.6}
$$

所以全部 Li 系数非负，由 Li 判据得到 RH。∎

这给出了一个纯有限差分版本：

$$
\boxed{
\text{RH}
=
\text{Li 累积量经过 Möbius–Fredholm 反演后，
形成单位区间正 moment sequence}.
}
$$

---

# 第二百六十部　Li 条件负定几何

定义偶延拓：

$$
\boxed{
\psi(n)
=
\lambda_{|n|},
\qquad
n\in\mathbb Z,
\qquad
\psi(0)=0.
}
\tag{260.1}
$$

RH 下：

$$
\psi(n)
=
\|I-C_\Xi^n\|_{\mathrm{HS}}^2.
$$

所以它是平移不变的平方 Hilbert 距离：

$$
\boxed{
d_\lambda(m,n)
=
\sqrt{
\lambda_{|m-n|}
}.
}
\tag{260.2}
$$

严格地说，它至少是 pseudometric；若没有非零整数 \(k\) 使 \(C_\Xi^k=I\)，则为 metric。

---

## 定理 260.1（Conditional negative definiteness）

$$
\boxed{
\mathrm{RH}
\iff
\psi(n)=\lambda_{|n|}
\text{ 是 }\mathbb Z\text{ 上的条件负定函数}.
}
\tag{260.3}
$$

条件负定意指：对任意有限整数 \(n_j\) 和复数 \(c_j\)，若：

$$
\sum_jc_j=0,
$$

则：

$$
\boxed{
\sum_{j,k}
c_j\overline{c_k}
\psi(n_j-n_k)
\le0.
}
\tag{260.4}
$$

### 正向证明

在每个零点相位 \(\theta_\gamma\) 上：

$$
\psi(n)
=
\sum_{\gamma>0}
m_\gamma
|1-e^{in\theta_\gamma}|^2.
$$

代入零和系数后，每个相位贡献为某个 Fourier 和模平方的负值。

### 反向证明（第 260 部）

取两个系数：

$$
c_1=1,\qquad c_2=-1
$$

于点 \(0,n\)，条件负定性给出：

$$
-2\psi(n)\le0.
$$

所以：

$$
\lambda_n=\psi(n)\ge0.
$$

由 Li 判据得到 RH。∎

---

## 260.1 Li Gram 核

定义：

$$
\boxed{
K_\lambda(m,n)
=
\frac{
\lambda_m+\lambda_n-\lambda_{|m-n|}
}{2}.
}
\tag{260.5}
$$

RH 下：

$$
K_\lambda
$$

是 Hilbert 空间中向量：

$$
I-C_\Xi^n
$$

的实 Gram 核。

因此：

$$
\boxed{
[K_\lambda(n_i,n_j)]_{i,j}
\succeq0
}
\tag{260.6}
$$

对任意有限整数集合成立。

这提供一个新的有限矩阵 RH 层级。

---

# 第二百六十一部　Li 圆周 Lévy 半群

定义对称零点角测度：

$$
\boxed{
\nu_\Xi
=
\sum_{\gamma>0}
m_\gamma
\left(
\delta_{\theta_\gamma}
+
\delta_{-\theta_\gamma}
\right).
}
\tag{261.1}
$$

虽然其总质量无穷，但：

$$
\int_{\mathbb T}
(1-\cos\theta)\,d\nu_\Xi(\theta)
=
\lambda_1<\infty.
$$

并且：

$$
\boxed{
\lambda_n
=
\int_{\mathbb T}
(1-\cos n\theta)
\,d\nu_\Xi(\theta).
}
\tag{261.2}
$$

所以 Li 系数构成一个圆周 Lévy–Khintchine 指数。

---

## 定理 261.1（Li convolution semigroup criterion）

$$
\boxed{
\mathrm{RH}
\iff
\left(
e^{-t\lambda_{|n|}}
\right)_{n\in\mathbb Z}
\text{ 对每个 }t\ge0\text{ 都是正定序列}.
}
\tag{261.3}
$$

Schoenberg 定理说明，Hermitian kernel \(\psi\) 条件负定，当且仅当：

$$
e^{-t\psi}
$$

对全部 \(t>0\) 正定。([数学网][4])

因此存在唯一圆周概率测度半群：

$$
\boxed{
(\mu_t)_{t\ge0},
}
$$

满足：

$$
\boxed{
\widehat\mu_t(n)
=
e^{-t\lambda_{|n|}}.
}
\tag{261.4}
$$

并且：

$$
\mu_{t+s}
=
\mu_t*\mu_s.
$$

---

## 261.1 Li Markov 生成元

在 \(L^2(\mathbb T)\) 上定义：

$$
\boxed{
\widehat{\mathcal A_\lambda f}(n)
=
\lambda_{|n|}
\widehat f(n).
}
\tag{261.5}
$$

RH 下：

$$
e^{-t\mathcal A_\lambda}
$$

是 positivity-preserving、mass-preserving 的圆周卷积半群。

对应 Dirichlet form：

$$
\boxed{
\begin{aligned}
\mathcal E_\lambda(f)
=
\frac12
\int_{\mathbb T}
\int_{\mathbb T}
|f(x+\theta)-f(x)|^2
\frac{dx}{2\pi}
\,d\nu_\Xi(\theta).
\end{aligned}
}
\tag{261.6}
$$

对 Fourier 模式：

$$
e_n(x)=e^{inx},
$$

有：

$$
\boxed{
\mathcal E_\lambda(e_n)
=
\lambda_n.
}
\tag{261.7}
$$

所以 Li 系数还可以解释为：

$$
\boxed{
\text{Riemann 零点角 Lévy 过程对第 }n\text{ 个 Fourier 模式施加的耗散能量}.
}
$$

这里 \(e^{-t\lambda_n}\) 中的 \(e\) 具有明确角色：

$$
\boxed{
e
=
\text{把加法观察时间转化为乘法 Fourier 衰减的半群接口}.
}
$$

---

# 第二百六十二部　Li 系数是多尺度零点滤波器

由：

$$
\theta_\gamma
=
2\arctan\frac1{2\gamma},
$$

得到：

$$
\boxed{
\lambda_n
=
4
\sum_{\gamma>0}
m_\gamma
\sin^2
\left(
n\arctan\frac1{2\gamma}
\right).
}
\tag{262.1}
$$

所以索引 \(n\) 不是任意计数，而是一个频率／分辨率参数。

---

## 262.1 三个尺度区

### 高频零点区

若：

$$
\gamma\gg n,
$$

则：

$$
\arctan\frac1{2\gamma}
\sim
\frac1{2\gamma},
$$

所以单零点贡献约为：

$$
\frac{n^2}{\gamma^2}.
$$

### 共振区

若：

$$
\gamma\asymp n,
$$

单零点贡献为 \(O(1)\)。

### 低零点区

若：

$$
\gamma\ll n,
$$

贡献在：

$$
0\le4\sin^2(\cdot)\le4
$$

之间振荡。

所以：

$$
\boxed{
\lambda_n
=
\text{以高度 }\gamma\sim n
\text{ 为主要分辨尺度的零点能量观察}.
}
$$

Lagarias 对 automorphic \(L\)-functions 证明：在 GRH 下，广义 Li 系数具有主项 \(\frac N2n\log n\) 以及线性项和可控误差；在 Riemann zeta 情形 \(N=1\)。这与上述“尺度 \(n\) 读取高度约 \(n\) 的零点密度”解释一致，但该滤波图像本身不替代其解析证明。([数字对象标识符][5])

---

# 第二百六十三部　线外零点在 Cayley 圆中的径向逃逸

设存在：

$$
\rho=\beta+i\gamma,
\qquad
\beta>\frac12.
$$

其 Cayley 坐标：

$$
u_\rho
=
\frac{\rho-1}{\rho}
$$

满足：

$$
|u_\rho|<1.
$$

精确地：

$$
\boxed{
|u_\rho|^2
=
\frac{
(\beta-1)^2+\gamma^2
}{
\beta^2+\gamma^2
}.
}
\tag{263.1}
$$

函数方程对称零点 \(1-\rho\) 的坐标为：

$$
u_{1-\rho}=u_\rho^{-1},
$$

所以同时出现一个模长大于 \(1\) 的逃逸状态。

---

## 263.1 四元组贡献

令：

$$
u_\rho=re^{i\theta},
\qquad
0<r<1.
$$

对应四元组：

$$
\rho,\quad
\bar\rho,\quad
1-\rho,\quad
1-\bar\rho
$$

对 Li 系数的贡献为：

$$
\boxed{
4
-
2\left(
r^n+r^{-n}
\right)\cos(n\theta).
}
\tag{263.2}
$$

其中：

$$
r^{-n}
$$

指数增长。

令：

$$
\beta=\frac12+\delta.
$$

则：

$$
\boxed{
\log r^{-1}
=
\frac12
\log
\frac{
\gamma^2+(\frac12+\delta)^2
}{
\gamma^2+(\frac12-\delta)^2
}
\sim
\frac{\delta}{\gamma^2+\frac14}.
}
\tag{263.3}
$$

所以单个线外零点在 Li 索引中的自然放大尺度约为：

$$
\boxed{
n
\asymp
\frac{\gamma^2+\frac14}{\delta}.
}
\tag{263.4}
$$

这只描述该零点四元组的指数放大尺度。

它**不能单独给出**第一个负 Li 系数的统一上界，因为：

* \(\cos(n\theta)\) 存在相位选择；
* 其他零点也会贡献；
* 可能发生有限阶相消。

Bombieri–Lagarias 定理保证整体 Li 判据最终感知线外零点，但最早失败阶仍可能非常大。([科学直通车][6])

---

# 第二百六十四部　Weil–Li–Cayley 三重目标

Bombieri–Lagarias 证明，对特定测试函数 \(g_n\)，Li 系数可以写成 Weil quadratic functional 的值：

$$
\boxed{
2\lambda_n
=
W
\left(
g_n*
\overline{x^{-1}g_n(x^{-1})}
\right).
}
\tag{264.1}
$$

Suzuki 进一步给出一族具体 model-space 函数 \(G_n\)，使 RH 等价于：

$$
\boxed{
\lambda_n
=
\frac1{2\pi}
\|G_n\|_{L^2(\mathbb R)}^2.
}
\tag{264.2}
$$

([arXiv][2])

当前 OACTC 又给出 RH 下的第三种范数：

$$
\boxed{
\lambda_n
=
\|I-C_\Xi^n\|_{\mathrm{HS}}^2.
}
\tag{264.3}
$$

所以有三种正性图表：

$$
\boxed{
\begin{array}{c|c}
\text{图表}&\text{Li 系数}\\
\hline
\text{Weil}&\text{显式公式二次型值}\\
\text{de Branges/model space}&L^2\text{ 函数范数}\\
\text{Cayley unitary}&\text{Hilbert--Schmidt 位移能量}
\end{array}
}
$$

---

## 264.1 真正需要构造的对象

因此 RH 的 operator target 可以分成三种强度。

### 目标 A：条件负定核

直接证明：

$$
\boxed{
\psi(n)=\lambda_{|n|}
}
$$

是条件负定函数。

### 目标 B：Li unitary

构造 unitary：

$$
C_{\mathrm{tor}}
$$

满足：

$$
\boxed{
\lambda_n
=
\|I-C_{\mathrm{tor}}^n\|_{\mathrm{HS}}^2.
}
\tag{264.4}
$$

### 目标 C：Cayley–Fredholm 算子

构造：

$$
0\le X_{\mathrm{tor}}\le I,
\qquad
X_{\mathrm{tor}}\in\mathcal S_1,
$$

满足：

$$
\boxed{
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}
=
\det
\left(
I+
\frac{4z}{(1-z)^2}
X_{\mathrm{tor}}
\right).
}
\tag{264.5}
$$

强度关系为：

$$
\boxed{
\text{Cayley--Fredholm}
\Longrightarrow
\text{unitary displacement}
\Longrightarrow
\text{conditional negative definiteness}
\Longrightarrow
\text{Li positivity}.
}
$$

其中最后一步已经足以推出 RH。

---

# 第二百六十五部　Toroidal relative-trace 的新最小目标

前文试图从二次环面 period frame 构造：

* Herglotz kernel；
* Stieltjes moments；
* 正 trace-class Fredholm 算子。

本轮给出一个可能更低成本的目标。

定义 Li Gram 核：

$$
\boxed{
K_\lambda(m,n)
=
\frac{
\lambda_m+\lambda_n-\lambda_{|m-n|}
}{2}.
}
$$

如果能从 toric relative trace formula 构造向量：

$$
\mathscr V_n
$$

使：

$$
\boxed{
K_\lambda(m,n)
=
\langle
\mathscr V_m,\mathscr V_n
\rangle,
}
\tag{265.1}
$$

则：

$$
K_\lambda\succeq0.
$$

特别地：

$$
\lambda_n=K_\lambda(n,n)\ge0,
$$

所以 RH 立即成立。

这比直接构造完整：

$$
X_{\mathrm{tor}}
$$

更弱，但可能更适合 relative trace。

因为 relative trace formula 天然产生：

* 周期平方；
* 交叉 period pairings；
* 正 Gram matrices；

而 \(K_\lambda\) 正好是一个需要交叉项的二变量核。

---

## 265.1 与 Wang–Deng 的具体分工

### Wang 层（265.1）

研究矩阵：

$$
[K_\lambda(n_i,n_j)]
$$

在不同索引尺度上的 near-negative vectors。

若质量分散于许多 \(n\)-尺度，则利用：

* Li Fourier 相位正交；
* 环面 twist 正交；
* 高度窗口分离；

产生严格 Gram 增益。

### Deng 层（265.1）

若 near-negative vector 集中于长 arithmetic progression 或单一相位簇，则：

1. 提取主导 unitary 相位；
2. 收缩重复 \(C^n\) 历史；
3. 以 power traces：

   $$
   \operatorname{Tr}X^k
   $$

   作为 primitive cumulants；
4. 用 Möbius／Fredholm 对数重求和；
5. 控制剩余 Gram defect。

---

# 第二百六十六部　Automorphic 推广

Lagarias 已将 Li 系数推广到 principal automorphic \(L\)-functions，并证明广义 RH 等价于广义 Li 系数实部的非负性，同时把它们联系到 Weil quadratic functional。([数字对象标识符][5])

对 self-dual completed automorphic \(L\)-function \(\Lambda(s,\pi)\)，若 GRH 成立，其零点为：

$$
\frac12+i\gamma_{\pi,j}.
$$

定义：

$$
X_\pi
=
\bigoplus_j
\frac1{4\gamma_{\pi,j}^2+1},
$$

以及：

$$
C_\pi
=
I-2X_\pi
+
2i\sqrt{X_\pi(I-X_\pi)}.
$$

则同样得到：

$$
\boxed{
\lambda_n(\pi)
=
\|I-C_\pi^n\|_{\mathrm{HS}}^2.
}
\tag{266.1}
$$

以及：

$$
\boxed{
\frac{
\Lambda(\frac1{1-z},\pi)
}{
\Lambda(1,\pi)
}
=
\det
\left(
I+
\frac{4z}{(1-z)^2}
X_\pi
\right).
}
\tag{266.2}
$$

对非 self-dual \(\pi\)，自然对象是 doubled completion：

$$
\Lambda(s,\pi)\Lambda(s,\widetilde\pi),
$$

其零点谱具有所需共轭对称，所得 unitary 是：

$$
C_\pi\oplus C_{\widetilde\pi}.
$$

所以 Li–Cayley completion 不是 ζ 的孤立技巧，而是 automorphic \(L\)-functions 的一般观察语言。

---

# 第二百六十七部　常数角色审计

本轮结构自然选择了：

$$
\boxed{
\frac12,\quad1,\quad4,\quad i,\quad e.
}
$$

它们的角色分别为：

$$
\boxed{
\begin{aligned}
\frac12
&=\text{临界半平面边界};\\
1
&=\text{Li 展开的归一化基点};\\
4
&=\text{平方折叠与 Cayley/Joukowski 变换的尺度因子};\\
i/2
&=\text{自伴 ordinate 到 unitary 圆周的 Cayley 尺度};\\
e
&=\text{条件负定能量到 Markov 半群衰减的指数接口}.
\end{aligned}
}
$$

值得强调：

$$
\boxed{
\varphi
\text{ 在本分支中没有被结构方程选出。}
}
$$

黄金比例在此前承担：

* 无碰撞斜率；
* Galois 双曲单位；
* 最短闭测地线；
* 准晶体显隐尺度。

但 Li–Cayley completion 自身选择的是 unit circle Möbius 几何，而不是 Golden 几何。

这是一个重要的科学负结论：

> 不能因为 \(\varphi\) 在其他完成分支中承重，就预设每个 RH 等价结构都必须出现 \(\varphi\)。

---

# 第二百六十八部　本轮结论分级

## 本轮独立推导得到（第 268 部）

$$
\boxed{
\Re s>\frac12
\iff
\left|
1-\frac1s
\right|<1.
}
$$

$$
\boxed{
X_\Xi
=
A_\Xi(4I+A_\Xi)^{-1}.
}
$$

$$
\boxed{
C_\Xi
=
I-2X_\Xi
+
2i\sqrt{X_\Xi(I-X_\Xi)}.
}
$$

$$
\boxed{
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}
=
\det
\left(
I+\frac{4z}{(1-z)^2}X_\Xi
\right).
}
$$

$$
\boxed{
\lambda_n
=
\|I-C_\Xi^n\|_{\mathrm{HS}}^2.
}
$$

$$
\boxed{
\lambda_n
=
4\operatorname{Tr}
\left[
X_\Xi
U_{n-1}(\sqrt{I-X_\Xi})^2
\right].
}
$$

$$
\boxed{
\lambda_n
=
n
\sum_{k=1}^{n}
(-1)^{k+1}
\frac{4^k}{k}
\binom{n+k-1}{n-k}
\operatorname{Tr}X_\Xi^k.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
\lambda_{|n|}
\text{ 条件负定于 }\mathbb Z.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
e^{-t\lambda_{|n|}}
\text{ 对全部 }t\ge0\text{ 正定}.
}
$$

---

## 与既有理论相邻、但本文给出不同封装

* Li 非负判据；
* Bombieri–Lagarias 的 Weil functional 表达；
* Suzuki 的 model-space norm 表达；
* Lagarias 的 automorphic Li 系数；
* Schoenberg 的条件负定—正定半群对偶；
* Hausdorff moment theorem。([科学直通车][1])

本文的新贡献目前应谨慎表述为：

$$
\boxed{
\text{把这些已知判据系统地连接到
一个正 trace-class contraction、
其 Cayley unitary、
Hilbert--Schmidt 位移、
Hausdorff moments 与圆周 Lévy 半群。}
}
$$

其中各单项公式的文献新颖性仍需专门审计。

---

# 第二百六十九部　建议形式化顺序

```text
D5/S3/Analytic/LiCayley/
  CriticalHalfPlaneMobius.lean
  ZeroCayleyCoordinate.lean
  LiGeneratingFunction.lean
  SquareFoldToCayleyContraction.lean

D5/S3/Analytic/LiFredholm/
  CayleyFredholmDeterminant.lean
  PositiveContractionRHCriterion.lean
  RelativeUnitaryProduct.lean
  CayleyOperatorUniqueness.lean

D5/S3/Analytic/LiUnitary/
  LiHilbertSchmidtDisplacement.lean
  LiChebyshevTrace.lean
  LiSubadditivity.lean
  LiGramKernel.lean

D5/S3/Analytic/LiHausdorff/
  LiPowerTraceTransform.lean
  InverseLiPowerTrace.lean
  LiHausdorffMoments.lean
  CompleteMonotonicityRHCriterion.lean

D5/S3/Analytic/LiLevy/
  LiConditionalNegativeDefinite.lean
  LiSchoenbergSemigroup.lean
  LiCircleLevyMeasure.lean
  LiDirichletForm.lean
  LiMarkovGenerator.lean

D5/S3/Observer/ToroidalLi/
  ToroidalLiGramTarget.lean
  ToroidalLiUnitaryTarget.lean
  ToroidalCayleyFredholmTarget.lean
  RelativeTraceLiKernel.lean
```

优先级最高、风险最低的链是：

$$
\boxed{
\text{critical half-plane Möbius map}
\to
\text{unit-circle zero coordinates}
\to
\text{Li coefficient pair formula}.
}
$$

其次是纯算子代数链：

$$
\boxed{
A_\Xi
\to
X_\Xi
\to
C_\Xi
\to
\lambda_n=\|I-C_\Xi^n\|_{\mathrm{HS}}^2.
}
$$

第三条是有限矩阵目标：

$$
\boxed{
\lambda
\to
K_\lambda(m,n)
\to
K_\lambda\succeq0.
}
$$

---

# 本轮最终结论

上一轮得到：

$$
\boxed{
\frac{
\xi(\frac12+\sqrt x)
}{
\xi(\frac12)
}
=
\det(I+xA_\Xi).
}
$$

本轮证明它经 Möbius 变换等价于：

$$
\boxed{
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}
=
\det
\left(
I+\frac{4z}{(1-z)^2}X_\Xi
\right),
\qquad
0\le X_\Xi\le I.
}
$$

其中：

$$
\boxed{
C_\Xi
=
I-2X_\Xi
+
2i\sqrt{X_\Xi(I-X_\Xi)}
}
$$

是 unitary 零点观察者。

Li 系数随即获得四个完全兼容的角色：

$$
\boxed{
\begin{aligned}
\lambda_n
&=\text{Cayley logarithmic cumulant};\\
&=\text{unitary }n\text{ 步 Hilbert--Schmidt 位移};\\
&=\text{圆周 Lévy 过程的 Fourier 耗散率};\\
&=\text{条件负定 Hilbert 距离的平方}.
\end{aligned}
}
$$

所以 RH 可以进一步压缩成：

$$
\boxed{
\text{Li 系数是否定义了 }\mathbb Z
\text{ 上一个平移不变的 Hilbertian squared distance？}
}
$$

或者等价地：

$$
\boxed{
\text{是否存在一个圆周 Markov 半群，
其 Fourier multiplier 为 }
e^{-t\lambda_{|n|}}？
}
$$

这使当前最小的 relative-trace 目标不再必须一步构造完整 Hilbert–Pólya 算子。

只需构造一个 Gram 表示：

$$
\boxed{
\frac{
\lambda_m+\lambda_n-\lambda_{|m-n|}
}{2}
=
\langle
\mathscr V_m,\mathscr V_n
\rangle.
}
$$

一旦该式能由二次环面周期或 Weil relative trace 直接推出，全部 Li 系数自动非负，RH 立即成立。

[1]: https://www.sciencedirect.com/science/article/pii/S0022314X97921375 "https://www.sciencedirect.com/science/article/pii/S0022314X97921375"
[2]: https://arxiv.org/abs/2301.05779 "Li coefficients as norms of functions in a model space"
[3]: https://link.springer.com/article/10.1007/s00209-025-03829-0 "https://link.springer.com/article/10.1007/s00209-025-03829-0"
[4]: https://www.mathnet.ru/eng/mzm13758 "https://www.mathnet.ru/eng/mzm13758"
[5]: https://doi.org/10.5802/AIF.2311 "https://doi.org/10.5802/AIF.2311"
[6]: https://www.sciencedirect.com/science/article/pii/S0022314X99923922 "https://www.sciencedirect.com/science/article/pii/S0022314X99923922"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.5：Li 离散曲率、Carathéodory–Schur 完成、CMV 谱算子与平稳过程

以下从前文**第二百六十九部之后**继续追加。

上一轮已经得到：

$$
\mathrm{RH}
\iff
\lambda_{|m-n|}
\text{ 是 }\mathbb Z\text{ 上的条件负定距离平方},
$$

以及：

$$
\lambda_n
=
\|I-C_\Xi^n\|_{\mathrm{HS}}^2.
$$

本轮不再直接观察 Li 系数 \(\lambda_n\)，而观察它的**离散二阶差分**。结果是：二阶差分会自动消除 Li 度量中的线性累计部分，把无限零点角测度正规化为一个有限概率测度，并产生：

$$
\boxed{
\text{正定 Toeplitz 核}
\longleftrightarrow
\text{Carathéodory 函数}
\longleftrightarrow
\text{Schur 参数}
\longleftrightarrow
\text{CMV unitary}
\longleftrightarrow
\text{平稳过程}.
}
$$

最终得到一个比“全部 Li 系数非负”更具内部结构的等价判据：

$$
\boxed{
\mathrm{RH}
\iff
\left[
\lambda_{j-k+1}
-2\lambda_{j-k}
+\lambda_{j-k-1}
\right]_{j,k}
\text{ 形成正定 Toeplitz 层级}.
}
$$

Li 判据本身以及其与 Weil 二次型、automorphic \(L\)-functions 的推广和 RH 条件下的渐近结构，已有成熟理论。([数字对象标识符][1])

---

# 第二百七十部　Li 离散曲率

令：

$$
\lambda_0=0,
\qquad
\lambda_{-n}=\lambda_n.
$$

定义 Li 系数的中心二阶差分：

$$
\boxed{
\kappa_n
=
\lambda_{n+1}
-2\lambda_n
+\lambda_{n-1},
\qquad
n\in\mathbb Z.
}
\tag{270.1}
$$

特别地：

$$
\boxed{
\kappa_0=2\lambda_1.
}
\tag{270.2}
$$

第一 Li 系数为：

$$
\boxed{
\lambda_1
=
\frac{\xi'(1)}{\xi(1)}
=
1+\frac{\gamma_{\!E}}2-\log(2\sqrt\pi)>0.
}
\tag{270.3}
$$

定义归一化 Li 曲率序列：

$$
\boxed{
c_n
=
\frac{\kappa_n}{2\lambda_1}.
}
\tag{270.4}
$$

于是：

$$
c_0=1,
\qquad
c_{-n}=c_n\in\mathbb R.
$$

这里“曲率”不表示每个 \(c_n\) 都必须非负。真正需要的是全局 Toeplitz 正定性：

$$
[c_{j-k}]\succeq0.
$$

这与点态凸性是不同的概念。

---

# 第二百七十一部　零点角的能量加权概率测度

假设 RH。

将正 ordinates 写为：

$$
\rho_\gamma=\frac12+i\gamma,
\qquad
\gamma>0,
$$

重数为 \(m_\gamma\)。

定义 Cayley 相位：

$$
\boxed{
u_\gamma
=
1-\frac1{\rho_\gamma}
=
\frac{\gamma+i/2}{\gamma-i/2}
=
e^{i\theta_\gamma}.
}
\tag{271.1}
$$

再定义：

$$
\boxed{
x_\gamma
=
\frac1{4\gamma^2+1}.
}
\tag{271.2}
$$

由于：

$$
\cos\theta_\gamma
=
\frac{4\gamma^2-1}{4\gamma^2+1},
$$

所以：

$$
\boxed{
1-\cos\theta_\gamma
=
2x_\gamma.
}
\tag{271.3}
$$

RH 下 Li 系数可成对写为：

$$
\boxed{
\lambda_n
=
\sum_{\gamma>0}
m_\gamma
|1-u_\gamma^n|^2
=
2\sum_{\gamma>0}
m_\gamma
\left(1-\cos n\theta_\gamma\right).
}
\tag{271.4}
$$

在 \(n=1\) 时：

$$
\boxed{
\lambda_1
=
4\sum_{\gamma>0}
m_\gamma x_\gamma.
}
\tag{271.5}
$$

---

## 271.1 Li 曲率测度

定义单位圆上的对称概率测度：

$$
\boxed{
\mu_\lambda
=
\frac{2}{\lambda_1}
\sum_{\gamma>0}
m_\gamma x_\gamma
\left(
\delta_{u_\gamma}
+
\delta_{\overline{u_\gamma}}
\right).
}
\tag{271.6}
$$

其总质量为：

$$
\frac{4}{\lambda_1}
\sum_{\gamma>0}m_\gamma x_\gamma
=1.
$$

对 \(n\in\mathbb Z\)：

$$
\begin{aligned}
\widehat\mu_\lambda(n)
&=
\int_{\mathbb T}\zeta^n\,d\mu_\lambda(\zeta)\\
&=
\frac{4}{\lambda_1}
\sum_{\gamma>0}
m_\gamma x_\gamma\cos(n\theta_\gamma).
\end{aligned}
\tag{271.7}
$$

另一方面，由式 (271.4)：

$$
\begin{aligned}
\kappa_n
&=
\lambda_{n+1}
-2\lambda_n
+\lambda_{n-1}\\
&=
8\sum_{\gamma>0}
m_\gamma x_\gamma\cos(n\theta_\gamma).
\end{aligned}
$$

因此：

## 定理 271.1（Li 曲率 Fourier 表示）

$$
\boxed{
c_n
=
\widehat\mu_\lambda(n).
}
\tag{271.8}
$$

所以 Li 二阶差分正是一个有限概率测度的 Fourier 系数。

---

## 271.2 二阶差分的正规化作用

未经加权的零点角计数测度：

$$
\nu_\Xi
=
\sum_{\gamma>0}
m_\gamma
\left(
\delta_{\theta_\gamma}
+
\delta_{-\theta_\gamma}
\right)
$$

总质量无穷。

但：

$$
\lambda_1
=
\int_{\mathbb T}
(1-\cos\theta)\,d\nu_\Xi(\theta)
<\infty.
$$

因此：

$$
\boxed{
d\mu_\lambda(\theta)
=
\frac{1-\cos\theta}{\lambda_1}
\,d\nu_\Xi(\theta).
}
\tag{271.9}
$$

即：

> Li 二阶差分等价于给无限零点角测度乘上 \(1-\cos\theta\) 反项，将其正规化为概率测度。

因此 \(\lambda_1\) 的结构角色是：

$$
\boxed{
\lambda_1
=
\text{零点角谱经过一阶圆周能量正规化后的总质量}.
}
$$

---

# 第二百七十二部　Li 曲率正定判据

对 \(N\ge0\)，定义 Toeplitz 矩阵：

$$
\boxed{
T_N(c)
=
[c_{j-k}]_{j,k=0}^{N}.
}
\tag{272.1}
$$

---

## 定理 272.1（Li curvature criterion）

$$
\boxed{
\mathrm{RH}
\iff
T_N(c)\succeq0
\quad
\forall N\ge0.
}
\tag{272.2}
$$

### 证明：RH \(\Rightarrow\)（第 272 部）

由定理 271.1：

$$
c_n=\widehat\mu_\lambda(n)
$$

且 \(\mu_\lambda\) 为概率测度。

因此对任意 \(a_0,\ldots,a_N\)：

$$
\begin{aligned}
\sum_{j,k=0}^{N}
a_j\overline{a_k}c_{j-k}
&=
\int_{\mathbb T}
\left|
\sum_{j=0}^{N}a_j\zeta^j
\right|^2
d\mu_\lambda(\zeta)\\
&\ge0.
\end{aligned}
$$

---

### 证明：Toeplitz 正性 \(\Rightarrow\) RH

若全部 \(T_N(c)\) 正半定，由圆周 Herglotz 定理，存在概率测度 \(\mu\)，使：

$$
c_n=\widehat\mu(n).
$$

定义：

$$
\widetilde\lambda_n
=
\lambda_1
\int_{\mathbb T}
\left|
1+\zeta+\cdots+\zeta^{n-1}
\right|^2
d\mu(\zeta).
\tag{272.3}
$$

则：

$$
\widetilde\lambda_0=0,
\qquad
\widetilde\lambda_1=\lambda_1.
$$

并且：

$$
\widetilde\lambda_{n+1}
-2\widetilde\lambda_n
+\widetilde\lambda_{n-1}
=
2\lambda_1c_n
=
\kappa_n.
$$

二阶递推加上前两个初值唯一决定序列，所以：

$$
\widetilde\lambda_n=\lambda_n.
$$

因此：

$$
\lambda_n\ge0
\qquad
\forall n.
$$

由 Li 判据，RH 成立。∎

---

## 272.1 有限失败证书

若 RH 不成立，则必存在某个有限 \(N\) 和向量 \(a\neq0\)，使：

$$
\boxed{
a^*T_N(c)a<0.
}
\tag{272.4}
$$

所以 RH 的失败必然在某个有限阶 Li 二阶差分 Toeplitz 矩阵中留下负证书。

这是一种**不需要预先知道线外零点位置**的有限反例证书。

---

# 第二百七十三部　Li 系数是平稳过程部分和的方差

由式 (272.3)，RH 下：

$$
\boxed{
\lambda_n
=
\lambda_1
\int_{\mathbb T}
\left|
\sum_{k=0}^{n-1}\zeta^k
\right|^2
d\mu_\lambda(\zeta).
}
\tag{273.1}
$$

令：

$$
\mathcal H_\lambda=L^2(\mathbb T,\mu_\lambda),
$$

定义 unitary：

$$
\boxed{
(Uf)(\zeta)=\zeta f(\zeta),
}
\tag{273.2}
$$

以及循环向量：

$$
v(\zeta)=1.
$$

则：

$$
c_n=\langle U^nv,v\rangle.
$$

定义一阶 cocycle：

$$
\boxed{
b_n
=
\sqrt{\lambda_1}
\sum_{k=0}^{n-1}U^kv,
\qquad
b_0=0.
}
\tag{273.3}
$$

有：

$$
\boxed{
b_{m+n}=b_m+U^mb_n.
}
\tag{273.4}
$$

并且：

$$
\boxed{
\|b_n\|^2=\lambda_n.
}
\tag{273.5}
$$

若 \(m\ge n\)：

$$
b_m-b_n
=
U^nb_{m-n},
$$

所以：

$$
\boxed{
\|b_m-b_n\|^2
=
\lambda_{m-n}.
}
\tag{273.6}
$$

这重新得到前文的 Li Hilbert 距离，但现在其 unitary 和循环向量是由 Li 曲率概率测度规范构造的。

---

## 定理 273.1（Li stationary-process criterion）

RH 等价于存在一个归一化平稳复过程 \((Y_k)_{k\in\mathbb Z}\)，使：

$$
\mathbb E[Y_j\overline{Y_k}]
=
c_{j-k},
$$

并满足：

$$
\boxed{
\lambda_n
=
\lambda_1
\mathbb E
\left|
Y_0+\cdots+Y_{n-1}
\right|^2.
}
\tag{273.7}
$$

因此：

$$
\boxed{
\text{Li 系数}
=
\text{一个平稳观察过程的部分和方差}.
}
$$

---

# 第二百七十四部　Li–Carathéodory 函数

定义 Li 生成函数：

$$
\boxed{
G_\xi(z)
=
\frac{
\xi(\frac1{1-z})
}{
\xi(1)
}.
}
\tag{274.1}
$$

标准 Li 展开为：

$$
\boxed{
\log G_\xi(z)
=
\sum_{n=1}^{\infty}
\frac{\lambda_n}{n}z^n.
}
\tag{274.2}
$$

定义 Li 曲率 Carathéodory 函数：

$$
\boxed{
\mathcal C_\lambda(z)
=
1+
2\sum_{n=1}^{\infty}c_nz^n.
}
\tag{274.3}
$$

由：

$$
c_n
=
\frac{
\lambda_{n+1}
-2\lambda_n
+\lambda_{n-1}
}{
2\lambda_1
},
$$

直接求和得到：

$$
\boxed{
\mathcal C_\lambda(z)
=
\frac{(1-z)^2}{\lambda_1}
\frac{d}{dz}
\log G_\xi(z).
}
\tag{274.4}
$$

而：

$$
\frac{d}{dz}
\log G_\xi(z)
=
\frac1{(1-z)^2}
\frac{
\xi'(\frac1{1-z})
}{
\xi(\frac1{1-z})
}.
$$

所以：

## 定理 274.1（Li–Carathéodory identity）

$$
\boxed{
\mathcal C_\lambda(z)
=
\frac1{\lambda_1}
\frac{
\xi'(\frac1{1-z})
}{
\xi(\frac1{1-z})
}.
}
\tag{274.5}
$$

这是一条极简的完成公式：

* Möbius 变换把单位圆盘送到 \(\Re s>\tfrac12\)；
* \(\xi'/\xi\) 是超额连接；
* \(\lambda_1\) 将其正规化为 \(\mathcal C_\lambda(0)=1\)。

---

## 定理 274.2（Carathéodory RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\Re\mathcal C_\lambda(z)>0
\quad
(|z|<1).
}
\tag{274.6}
$$

### 证明

RH 下：

$$
\mathcal C_\lambda(z)
=
\int_{\mathbb T}
\frac{\zeta+z}{\zeta-z}
\,d\mu_\lambda(\zeta),
$$

所以其实部严格为正。

反之，若 \(\mathcal C_\lambda\) 在圆盘内全纯且实部非负，则：

$$
\frac{\xi'}{\xi}(s)
$$

在：

$$
\Re s>\frac12
$$

无极点，所以 \(\xi\) 在该半平面无零点。由函数方程，全部非平凡零点只能位于临界线。∎

---

# 第二百七十五部　Schur 算法是最小创新分解

定义 Schur 函数：

$$
\boxed{
f_\lambda(z)
=
\frac1z
\frac{
\mathcal C_\lambda(z)-1
}{
\mathcal C_\lambda(z)+1
},
}
\tag{275.1}
$$

其中 \(z=0\) 处取可去延拓。

Carathéodory–Schur 变换说明：

$$
\Re\mathcal C_\lambda>0
\iff
|f_\lambda(z)|\le1
\quad
(|z|<1).
$$

因此：

$$
\boxed{
\mathrm{RH}
\iff
f_\lambda
\text{ 是 Schur 函数}.
}
\tag{275.2}
$$

Schur 函数、Schur 参数、Verblunsky 系数及单位圆正交多项式之间的对应是 OPUC 理论的基本结构；CMV 矩阵提供其标准 unitary 实现。([EMS Press][2])

---

## 275.1 Schur 参数

令：

$$
f_0=f_\lambda.
$$

递归定义：

$$
\boxed{
\alpha_n=f_n(0),
}
\tag{275.3}
$$

$$
\boxed{
f_{n+1}(z)
=
\frac{
f_n(z)-\alpha_n
}{
z\left(1-\overline{\alpha_n}f_n(z)\right)
}.
}
\tag{275.4}
$$

因为 \(\mu_\lambda\) 关于复共轭对称，全部 \(\alpha_n\) 为实数。

RH 等价于：

$$
\boxed{
|\alpha_n|<1
\quad
\forall n\ge0.
}
\tag{275.5}
$$

严格不等号来自 \(\mu_\lambda\) 具有无限支撑。

---

## 275.2 最初两个创新参数

令：

$$
c_1
=
\frac{
\lambda_2-2\lambda_1
}{
2\lambda_1
},
$$

$$
c_2
=
\frac{
\lambda_3-2\lambda_2+\lambda_1
}{
2\lambda_1
}.
$$

则：

$$
\boxed{
\alpha_0=c_1,
}
\tag{275.6}
$$

$$
\boxed{
\alpha_1
=
\frac{
c_2-c_1^2
}{
1-c_1^2
}.
}
\tag{275.7}
$$

每个 \(\alpha_n\) 都表示：

> 已知前 \(n\) 阶相关以后，第 \(n+1\) 阶相关仍不能由旧数据预测的最小新信息。

因此 Schur 算法正是 RDS/DECT 意义上的**递归定义生成器**：

$$
\boxed{
\text{当前 moments}
\to
\text{预测 residual}
\to
\alpha_n
\to
\text{下一层完成}.
}
$$

---

# 第二百七十六部　Toeplitz 行列式与有限证书

定义：

$$
\boxed{
D_N
=
\det
[c_{j-k}]_{j,k=0}^{N}.
}
\tag{276.1}
$$

OPUC 理论给出：

$$
\boxed{
D_N
=
\prod_{j=0}^{N-1}
\left(1-\alpha_j^2\right)^{N-j}.
}
\tag{276.2}
$$

所以：

$$
D_N>0
$$

等价于前 \(N\) 个 Schur 参数全部位于 \((-1,1)\)。

---

## 276.1 第一层不等式

$$
D_1
=
1-c_1^2
\ge0.
$$

即：

$$
\left|
\lambda_2-2\lambda_1
\right|
\le
2\lambda_1.
$$

等价于：

$$
\boxed{
0\le\lambda_2\le4\lambda_1.
}
\tag{276.3}
$$

Li 判据只直接要求：

$$
\lambda_2\ge0.
$$

Toeplitz 曲率判据还给出上界：

$$
\lambda_2\le4\lambda_1.
$$

---

## 276.2 第二层行列式

$$
T_2=
\begin{pmatrix}
1&c_1&c_2\\
c_1&1&c_1\\
c_2&c_1&1
\end{pmatrix}.
$$

其行列式为：

$$
\boxed{
D_2
=
(1-c_2)
\left(
1+c_2-2c_1^2
\right).
}
\tag{276.4}
$$

所以 RH 推出：

$$
|c_2|\le1,
$$

以及：

$$
1+c_2\ge2c_1^2.
$$

更高阶给出一族完全显式的 Li 多项式不等式。

---

## 276.3 三类有限失败证书

若 RH 失败，则至少存在以下某一种有限证书：

1. Pick 矩阵出现负特征值；
2. Hankel moment 矩阵出现负特征值；
3. Li 曲率 Toeplitz 矩阵出现负特征值。

三类证书分别读取：

$$
\boxed{
\begin{array}{c|c}
\text{Pick}&\text{局部复谱／Herglotz 失败}\\
\text{Hankel}&\text{中心倒谱 moment 失败}\\
\text{Toeplitz}&\text{Li 平稳相关／圆周谱失败}
\end{array}
}
$$

---

# 第二百七十七部　Li–CMV unitary

Verblunsky 系数：

$$
\alpha_0,\alpha_1,\ldots
$$

唯一决定一个 CMV unitary：

$$
\boxed{
\mathcal C_\lambda.
}
\tag{277.1}
$$

其相对于循环向量 \(e_0\) 的谱测度恰为：

$$
\mu_\lambda.
$$

因此：

$$
\boxed{
\langle
\mathcal C_\lambda^ne_0,e_0
\rangle
=
c_n.
}
\tag{277.2}
$$

CMV 是单位圆正交多项式的标准五对角 unitary 矩阵实现；其谱理论与 Verblunsky 系数一一对应。([剑桥大学出版社][3])

---

## 277.1 逆 Cayley 谱算子

在 \(\mathcal C_\lambda\) 的谱表示中定义：

$$
\boxed{
H_\lambda
=
\frac{i}{2}
\left(
\mathcal C_\lambda+I
\right)
\left(
\mathcal C_\lambda-I
\right)^{-1}.
}
\tag{277.3}
$$

它是一个稠密定义的自伴算子。

若：

$$
\mathcal C_\lambda
$$

的谱点为：

$$
e^{i\theta_\gamma},
$$

则：

$$
H_\lambda
$$

的对应谱值为：

$$
\boxed{
\frac12\cot\frac{\theta_\gamma}{2}
=
\gamma.
}
\tag{277.4}
$$

因此：

$$
\boxed{
\operatorname{supp}
\operatorname{spec}(H_\lambda)
=
\{\pm\gamma:\Xi(\gamma)=0\}.
}
$$

这给出一个**循环 CMV–Hilbert–Pólya 实现**。

需要保留限制：

* 不同零点位置被恢复为谱支撑；
* 零点重数首先编码在谱测度权重中；
* 若要把重数提升为算子谱重数，需要在各原子上附加相应有限维 fiber。

---

# 第二百七十八部　与前文 Cayley unitary 的关系

前文在正 ordinates 空间上定义：

$$
C_\Xi
=
I-2X_\Xi
+
2i\sqrt{X_\Xi(I-X_\Xi)}.
$$

其特征值为：

$$
u_\gamma=e^{i\theta_\gamma}.
$$

定义双倍 unitary：

$$
\boxed{
\widetilde C_\Xi
=
C_\Xi\oplus C_\Xi^*,
}
\tag{278.1}
$$

以及：

$$
\boxed{
\widetilde X_\Xi
=
X_\Xi\oplus X_\Xi.
}
\tag{278.2}
$$

定义加权迹状态：

$$
\boxed{
\omega_\Xi(T)
=
\frac{
\operatorname{Tr}
(\widetilde X_\Xi T)
}{
\operatorname{Tr}
\widetilde X_\Xi
}.
}
\tag{278.3}
$$

则：

$$
\boxed{
c_n
=
\omega_\Xi
\left(
\widetilde C_\Xi^n
\right).
}
\tag{278.4}
$$

并且：

$$
\boxed{
\mathcal C_\lambda(z)
=
\omega_\Xi
\left[
(I+z\widetilde C_\Xi)
(I-z\widetilde C_\Xi)^{-1}
\right].
}
\tag{278.5}
$$

所以：

* \(\widetilde C_\Xi\) 是零点角的对角 unitary；
* \(\widetilde X_\Xi\) 给出能量偏置；
* \(\mathcal C_\lambda\) 是其加权 resolvent 观察；
* CMV 矩阵是该状态的循环最小实现。

这把前文的 trace-class/Fredholm 图表和当前 OPUC 图表精确连接起来。

---

# 第二百七十九部　有限 CMV 层析

给定：

$$
\lambda_1,\ldots,\lambda_{N+1},
$$

可以计算：

$$
c_0,\ldots,c_N.
$$

若：

$$
T_N(c)\succeq0,
$$

便可执行有限 Schur 算法，得到：

$$
\alpha_0,\ldots,\alpha_{N-1}.
$$

再选择一个边界相位：

$$
\beta\in\mathbb T,
$$

构造有限 paraorthogonal CMV 矩阵：

$$
\boxed{
\mathcal C_N^{(\beta)}.
}
\tag{279.1}
$$

若有限 Toeplitz 数据为正，则：

$$
\operatorname{spec}
\mathcal C_N^{(\beta)}
\subset\mathbb T.
$$

其谱测度是一种有限圆周 quadrature measure，匹配当前已知的有限 Fourier moments。

将其特征值：

$$
e^{i\theta_{j,N}}
$$

经逆 Cayley 变换：

$$
\boxed{
\gamma_{j,N}
=
\frac12\cot\frac{\theta_{j,N}}2
}
\tag{279.2}
$$

得到有限实谱 approximants。

随着可验证 moments 增加，若全部 Toeplitz 层级保持正，有限谱测度在紧圆周上具有弱收敛子列，并由全部 moments 的唯一性收敛到 \(\mu_\lambda\)。

所以中心 Li 系数可以产生一个纯有限矩阵的谱层析流程：

$$
\boxed{
\lambda
\to
\Delta^2\lambda
\to
\text{Toeplitz}
\to
\text{Schur}
\to
\text{CMV}
\to
\text{zero-angle spectrum}.
}
$$

---

# 第二百八十部　Schur 连分数作为 Ramanujan 式尾部压缩

Schur 递推可反写为：

$$
\boxed{
f_n(z)
=
\frac{
\alpha_n+zf_{n+1}(z)
}{
1+\alpha_nzf_{n+1}(z)
},
}
\tag{280.1}
$$

因为本例 \(\alpha_n\in\mathbb R\)。

不断代入，得到一个 Wall–Schur 连分式。

因此：

$$
\boxed{
\mathcal C_\lambda
\longleftrightarrow
f_\lambda
\longleftrightarrow
(\alpha_0,\alpha_1,\ldots)
}
$$

是同一个对象的：

* 正实部函数图表；
* 单位圆盘函数图表；
* 递归连分数图表。

这与 Ramanujan 第 541 号恒等式中：

$$
\text{积分尾部}
\longleftrightarrow
\text{连分数压缩}
$$

具有相同骨架。

但当前分支没有结构方程强迫：

$$
\alpha_n=1
$$

或强迫常数尾为黄金比例。

因此必须保留负结论：

$$
\boxed{
\varphi
\text{ 不是 Li--Schur 完成本身所必然选择的常数。}
}
$$

只有在特殊 stationary tail 模型中，固定连分数才可能再次产生 \(\varphi\)。

---

# 第二百八十一部　最小 toroidal 证明目标

此前最强的目标是直接构造：

$$
X_{\mathrm{tor}}\ge0
$$

或：

$$
U_{\mathrm{tor}}\ge0
$$

使 \(\xi\) 成为 Fredholm determinant。

当前得到一个更弱、可能更适合 relative trace 的目标。

## 假设 281.1（Toroidal covariance realization）

存在 Hilbert 空间 \(\mathcal H_{\mathrm{tor}}\)、unitary \(V\) 和单位向量 \(v\)，使：

$$
\boxed{
\frac{
\lambda_{n+1}-2\lambda_n+\lambda_{n-1}
}{
2\lambda_1
}
=
\langle V^nv,v\rangle.
}
\tag{281.1}
$$

若成立，则：

$$
c_n
$$

正定，故 RH 成立。

进一步定义：

$$
B_n
=
\sqrt{\lambda_1}
\sum_{k=0}^{n-1}V^kv.
$$

立即得到：

$$
\lambda_n=\|B_n\|^2.
$$

所以 relative trace formula 不必一步构造全部零点算子；只需把 Li 二阶差分实现为一个平稳相关核。

---

## 281.1 Relative-trace Gram 形式

更直接地，若能构造向量：

$$
Y_n
$$

使：

$$
\boxed{
\langle Y_m,Y_n\rangle
=
c_{m-n},
}
\tag{281.2}
$$

则：

$$
T_N(c)
$$

自动为 Gram 矩阵。

这个目标比：

$$
K_\lambda(m,n)
=
\frac{
\lambda_m+\lambda_n-\lambda_{|m-n|}
}{2}
$$

的 Gram 实现更局部，因为：

$$
c_n
$$

只是 Li 度量的离散二阶曲率。

---

# 第二百八十二部　Wang–Deng 在 Schur–CMV 图表中的分工

## 282.1 Non-sticky：谱测度分散

若 \(\mu_\lambda\) 在单位圆上分散于多个角区间，则：

* Toeplitz matrices 条件数改善；
* Schur 参数远离 \(\pm1\)；
* finite CMV truncations 稳定；
* 不同相位产生相关抵消。

研究目标可写为：

$$
\boxed{
\text{phase anti-concentration}
\Longrightarrow
1-\alpha_n^2\ge\eta_n>0.
}
\tag{282.1}
$$

这就是 Wang 式 strict gain。

---

## 282.2 Sticky：谱质量集中

高 ordinates 对应：

$$
u_\gamma\to1.
$$

所以 \(\mu_\lambda\) 可能在 \(1\) 附近形成强集中。

这会导致：

* 初始 Fourier moments 接近 \(1\)；
* 某些 Schur 参数接近边界；
* finite Toeplitz matrices 变得病态；
* 有限层析难以区分高零点。

Deng 式处理应是：

1. 识别主导角原子或角簇；
2. 用 Blaschke／Christoffel 型变换剥离其贡献；
3. 对 residual measure 重新执行 Schur 算法；
4. 将重复相位历史压缩为有限 CMV block；
5. 控制剩余 Schur tail。

---

## 282.3 Schur 参数是 primitive innovations

moments：

$$
c_1,c_2,\ldots
$$

包含大量复合信息。

Verblunsky 参数：

$$
\alpha_0,\alpha_1,\ldots
$$

则是逐层条件化以后留下的最小创新数据。

因此：

$$
\boxed{
\text{Schur algorithm}
=
\text{圆周 moment histories 的 primitive decomposition}.
}
$$

这为 Yu Deng 的“primitive history”提供了另一个完全闭合的一维模型。

---

# 第二百八十三部　Li 渐近与相关临界性

Lagarias 证明，在 RH 条件下，Riemann zeta 的 Li 系数具有：

$$
\boxed{
\lambda_n
=
\frac12n\log n
+
C_\xi n
+
O(\sqrt n\log n).
}
\tag{283.1}
$$

更一般的 automorphic \(L\)-functions 主项为：

$$
\frac{N}{2}n\log n.
$$

([数字对象标识符][1])

因此在平稳过程图表中：

$$
\operatorname{Var}
\left(
Y_0+\cdots+Y_{n-1}
\right)
\asymp
n\log n.
$$

这属于介于：

* 短程相关的 \(O(n)\)；
* 完全相干的 \(O(n^2)\)；

之间的临界增长。

但必须谨慎：

$$
O(\sqrt n\log n)
$$

的粗误差不能直接逐项二阶差分，从而推出：

$$
c_n\sim\frac{\text{常数}}n.
$$

要获得 \(c_n\) 的精确渐近，需要对 Li 余项的离散正则性建立额外估计。

因此当前只能严格说：

$$
\boxed{
n\log n
\text{ 是 Li 平稳过程部分和方差的全局尺度；}
}
$$

不能仅凭现有粗渐近断言局部相关系数的精确衰减律。

---

# 第二百八十四部　三种中心化正性层级

现在 RH 有三种不依赖线外零点位置的有限层级。

## 284.1 Hankel 层级

输入：

$$
\xi^{(2n)}(\tfrac12).
$$

测试：

$$
H_N^{(0)},H_N^{(1)}\succeq0.
$$

解释：

$$
\text{倒平方零点谱是否为正 Stieltjes measure}.
$$

---

## 284.2 Toeplitz–曲率层级

输入：

$$
\lambda_1,\ldots,\lambda_{N+1}.
$$

测试：

$$
T_N(c)\succeq0.
$$

解释：

$$
\text{Cayley 零点角是否形成正圆周谱测度}.
$$

---

## 284.3 Toeplitz–PF 层级

输入：

$$
\xi^{(2n)}(\tfrac12)
$$

的平方折叠 Taylor 系数 \(a_n\)。

测试：

$$
[a_{j-i}]
$$

的全部 minors 非负。

解释：

$$
\text{Fredholm 外幂系数是否来自正谱 alphabet}.
$$

三者分别读取：

$$
\boxed{
\begin{array}{c|c}
\text{Hankel}&\text{primitive powers}\\
\text{Li 曲率 Toeplitz}&\text{unitary correlations}\\
\text{PF Toeplitz}&\text{exterior composites}
\end{array}
}
$$

它们不是重复判据，而是同一隐藏正谱在三个不同基底中的 Gram/total-positivity 表达。

---

# 第二百八十五部　本轮最小 RH 核

本轮将前文的大型完成目标进一步压缩。

不必首先构造：

* 完整 Hilbert–Pólya 算子；
* Fredholm determinant；
* 全部 de Branges kernel；
* 全部二次环面帧。

只需构造一个满足：

$$
\boxed{
c_n
=
\frac{
\lambda_{n+1}-2\lambda_n+\lambda_{n-1}
}{
2\lambda_1
}
}
$$

的正定平稳相关序列。

等价目标为任一项：

$$
\boxed{
\begin{aligned}
&[c_{j-k}]\succeq0;\\
&\Re\mathcal C_\lambda(z)>0;\\
&f_\lambda\text{ 是 Schur};\\
&|\alpha_n|<1\ \forall n;\\
&\exists\text{ unitary CMV realization};\\
&\exists\text{ stationary process with partial-sum variance }\lambda_n.
\end{aligned}
}
$$

所以当前最小、最局部的 toroidal/relative-trace 目标是：

$$
\boxed{
\frac{
\lambda_{m-n+1}
-2\lambda_{m-n}
+\lambda_{m-n-1}
}{
2\lambda_1
}
=
\langle
Y_m,Y_n
\rangle_{\mathrm{tor}}.
}
\tag{285.1}
$$

一旦该式成立，RH 立即成立。

---

# 第二百八十六部　建议形式化顺序

```text
D5/S3/Analytic/LiCurvature/
  LiEvenExtension.lean
  LiSecondDifference.lean
  LiCurvatureNormalization.lean
  LiCurvaturePositiveDefiniteCriterion.lean
  LiPartialSumVariance.lean

D5/S3/Analytic/LiCaratheodory/
  LiGeneratingFunction.lean
  LiCaratheodoryIdentity.lean
  CaratheodoryRHCriterion.lean
  LiCurvatureHerglotzMeasure.lean

D5/S3/Analytic/LiSchur/
  LiSchurFunction.lean
  LiSchurParameters.lean
  LiFirstReflectionCoefficients.lean
  LiToeplitzDeterminants.lean
  LiFiniteNegativeCertificate.lean

D5/S3/Analytic/LiCMV/
  LiVerblunskySequence.lean
  LiCMVOperator.lean
  LiCMVSpectralMeasure.lean
  LiInverseCayleyOperator.lean
  LiFiniteCMVTomography.lean

D5/S3/Analytic/LiStationary/
  LiStationaryCovariance.lean
  LiUnitaryCocycle.lean
  LiPartialSumVarianceCriterion.lean
  LiCurvatureMass.lean

D5/S3/Observer/ToroidalLiCurvature/
  ToroidalCurvatureGramTarget.lean
  RelativeTraceStationaryKernel.lean
  SchurInnovationRenormalization.lean
  CMVStickyNonStickyDichotomy.lean
```

优先级最高、风险最低的闭合链是：

$$
\boxed{
\lambda
\to
\Delta^2\lambda
\to
\text{positive-definite Toeplitz criterion}.
}
$$

其次是纯解析恒等式：

$$
\boxed{
\mathcal C_\lambda(z)
=
\frac1{\lambda_1}
\frac{
\xi'(\frac1{1-z})
}{
\xi(\frac1{1-z})
}.
}
$$

再之后是标准 OPUC 接口：

$$
\boxed{
\mathcal C_\lambda
\to
f_\lambda
\to
\alpha_n
\to
\mathcal C_\lambda^{\mathrm{CMV}}.
}
$$

---

# 本轮最终结论

上一轮得到：

$$
\boxed{
\lambda_{|m-n|}
=
\text{unitary Li 距离平方}.
}
$$

本轮进一步证明，其离散二阶差分：

$$
\boxed{
c_n
=
\frac{
\lambda_{n+1}
-2\lambda_n
+\lambda_{n-1}
}{
2\lambda_1
}
}
$$

是更基本的对象。

RH 等价于：

$$
\boxed{
c_n
=
\widehat\mu_\lambda(n)
}
$$

对某个单位圆概率测度成立。

这个概率测度不是任意构造，而是：

$$
\boxed{
d\mu_\lambda
=
\frac{
1-\cos\theta
}{
\lambda_1
}
\,d\nu_\Xi(\theta),
}
$$

即零点角谱经过一阶圆周能量加权后的有限完成。

因此：

$$
\boxed{
\lambda_1
}
$$

获得了新的结构角色：

$$
\boxed{
\lambda_1
=
\text{无限 Riemann 零点角谱被离散拉普拉斯正规化后的总质量}.
}
$$

而完整 RH 链可写为：

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\text{Li 二阶差分为正定相关函数}\\
&\iff
\text{存在平稳过程，其部分和方差为 }\lambda_n\\
&\iff
\mathcal C_\lambda\text{ 为 Carathéodory 函数}\\
&\iff
f_\lambda\text{ 为 Schur 函数}\\
&\iff
|\alpha_n|<1\ \forall n\\
&\iff
\text{存在 unitary CMV 谱实现}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
\text{Li 系数本身是累计距离；
真正的局部谱信息存在于它的二阶差分中。}
}
$$

因此当前 OACTC 最小的 RH 证明目标，不必是一开始构造整个零点算子，而可以只是：

$$
\boxed{
\text{从 toric relative trace formula
证明 Li 离散曲率 Toeplitz 核正定。}
}
$$

这将自动生成：

* Schur 参数；
* CMV unitary；
* Cayley self-adjoint spectrum；
* Li 距离；
* 以及最终的 RH。

[1]: https://doi.org/10.5802/AIF.2311?utm_source=chatgpt.com "Li coefficients for automorphic $L$-functions"
[2]: https://ems.press/journals/zaa/articles/12279?utm_source=chatgpt.com "Schur Functions, Schur Parameters and Orthogonal Polynomials on the Unit Circle | EMS Press"
[3]: https://www.cambridge.org/core/journals/journal-of-the-london-mathematical-society/article/borgtype-theorem-associated-with-orthogonal-polynomials-on-the-unit-circle/F1708F834C8E9A46155523F753FE6896?utm_source=chatgpt.com "A BORG-TYPE THEOREM ASSOCIATED WITH ORTHOGONAL POLYNOMIALS ON THE UNIT CIRCLE | Journal of the London Mathematical Society | Cambridge Core"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.6：Li–Clark 内函数、边界条件谱、Szegő 创新塌缩与零点角拥挤律

以下从前文**第二百八十六部之后**继续追加。

上一轮得到：

$$
\mathrm{RH}
\iff
c_n=
\frac{\lambda_{n+1}-2\lambda_n+\lambda_{n-1}}{2\lambda_1}
$$

是单位圆概率测度的 Fourier 系数，并进一步构造了 Carathéodory、Schur 与 CMV 图表。

本轮发现，这个概率测度不是任意的 OPUC 谱测度，而是一个由 \(\xi\) 显式定义的内函数的 **Aleksandrov–Clark 测度**。由此出现一条更规范的闭环：

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\iff
\text{一个显式 }\xi\text{-内函数存在}\\
&\iff
\text{Riemann 零点角构成其 }\alpha=1\text{ Clark 谱}\\
&\iff
\xi'\text{ 的临界点构成其 }\alpha=-1\text{ Clark 谱}\\
&\iff
\text{全部边界条件谱形成 rank-one unitary family}\\
&\iff
\text{Li–CMV 算子是该 Clark family 的一个矩阵图表}.
\end{aligned}
}
$$

与此同时，Szegő 理论给出一个必须纳入主理论的修正：

$$
\boxed{
\text{RH 下的 Li 曲率测度是纯点奇异测度，}
}
$$

因此其无限预测创新误差必然塌缩为零。正确的证明目标不是让无限深度观察保持随机性，而是解释：

> 一个零创新、完全确定的谱过程，为什么仍然只能由临界线上的实谱原子生成？

Aleksandrov–Clark 测度把内函数、正调和函数、model spaces 与 rank-one unitary perturbations 统一起来；原子与有限角导数之间存在精确对应。([London Mathematical Society (LMS)][1])

---

# 第二百八十七部　显式 Li–Clark 内函数

为避免前文 Carathéodory 函数与 CMV 矩阵记号冲突，本节重新冻结记号。

定义：

$$
\boxed{
s(z)=\frac{1}{1-z},
\qquad
|z|<1.
}
\tag{287.1}
$$

它把单位圆盘映到：

$$
\Re s>\frac12.
$$

定义第一 Li 系数：

$$
\boxed{
\lambda_1
=
\frac{\xi'(1)}{\xi(1)}
>0.
}
\tag{287.2}
$$

定义 Li–Carathéodory 函数：

$$
\boxed{
\mathfrak C_\xi(z)
=
\frac{1}{\lambda_1}
\frac{\xi'(s(z))}{\xi(s(z))}.
}
\tag{287.3}
$$

因为：

$$
s(0)=1,
$$

所以：

$$
\mathfrak C_\xi(0)=1.
$$

再定义 Li–Clark 函数：

$$
\boxed{
\vartheta_\xi(z)
=
\frac{\mathfrak C_\xi(z)-1}
{\mathfrak C_\xi(z)+1}.
}
\tag{287.4}
$$

直接展开：

$$
\boxed{
\vartheta_\xi(z)
=
\frac{
\xi'(s(z))-\lambda_1\xi(s(z))
}{
\xi'(s(z))+\lambda_1\xi(s(z))
}.
}
\tag{287.5}
$$

并且：

$$
\boxed{
\vartheta_\xi(0)=0.
}
\tag{287.6}
$$

---

## 定理 287.1（Li–Clark inner criterion）

$$
\boxed{
\mathrm{RH}
\iff
\vartheta_\xi
\text{ 是单位圆盘上的内函数}.
}
\tag{287.7}
$$

### 证明：RH \(\Rightarrow\)（第 287 部）

前文已证明 RH 等价于：

$$
\Re\mathfrak C_\xi(z)>0
\qquad
(|z|<1).
$$

Cayley 变换：

$$
w\mapsto\frac{w-1}{w+1}
$$

把右半平面送到单位圆盘，因此：

$$
|\vartheta_\xi(z)|<1.
$$

RH 下 \(\mathfrak C_\xi\) 的 Herglotz 测度是由 Riemann 零点角组成的纯点测度，因此是奇异测度。一个 Schur 函数的某个 Clark 测度为奇异测度，当且仅当该 Schur 函数是内函数。([London Mathematical Society (LMS)][1])

---

### 证明：内函数 \(\Rightarrow\) RH

若 \(\vartheta_\xi\) 为内函数，则它首先是 Schur 函数，因此：

$$
\mathfrak C_\xi
=
\frac{1+\vartheta_\xi}
{1-\vartheta_\xi}
$$

在单位圆盘中实部非负。

所以：

$$
\frac{\xi'(s)}{\xi(s)}
$$

在：

$$
\Re s>\frac12
$$

中没有极点，故 \(\xi\) 在该半平面无零点。由函数方程对称性，全部非平凡零点位于临界线。∎

---

## 287.1 结构意义

因此 RH 等价于一个非常紧凑的声明：

$$
\boxed{
\text{由 }\xi'\text{ 与 }\xi\text{ 的固定线性分式组合，
是否完成为一个内函数？}
}
$$

在这个图表中：

* \(\xi'/\xi\)：Herglotz 连接；
* \(\lambda_1\)：使中心值等于 \(1\) 的规范化常数；
* \(\vartheta_\xi\)：其单位圆盘 Cayley 完成；
* RH：该完成是否没有内部泄漏。

---

# 第二百八十八部　Riemann 零点角就是 Clark 谱

RH 下，令：

$$
\rho_\gamma=\frac12+i\gamma,
\qquad
\gamma>0,
$$

零点重数为 \(m_\gamma\)。

定义其 Cayley 角坐标：

$$
\boxed{
u_\gamma
=
1-\frac{1}{\rho_\gamma}
=
\frac{\gamma+i/2}{\gamma-i/2}
=
e^{i\theta_\gamma}.
}
\tag{288.1}
$$

其中：

$$
\theta_\gamma
=
2\arctan\frac{1}{2\gamma}.
$$

再令：

$$
\boxed{
x_\gamma
=
\frac{1}{4\gamma^2+1}.
}
\tag{288.2}
$$

定义每个有向零点角的权重：

$$
\boxed{
w_\gamma
=
\frac{2m_\gamma}
{\lambda_1(4\gamma^2+1)}
=
\frac{2m_\gamma x_\gamma}{\lambda_1}.
}
\tag{288.3}
$$

则 Li 曲率测度为：

$$
\boxed{
\mu_\lambda
=
\sum_{\gamma>0}
w_\gamma
\left(
\delta_{u_\gamma}
+
\delta_{\overline{u_\gamma}}
\right).
}
\tag{288.4}
$$

并且：

$$
\mu_\lambda(\mathbb T)=1.
$$

等价地：

$$
\boxed{
\lambda_1
=
4
\sum_{\gamma>0}
\frac{m_\gamma}{4\gamma^2+1}.
}
\tag{288.5}
$$

其 Carathéodory 表示为：

$$
\boxed{
\mathfrak C_\xi(z)
=
\int_{\mathbb T}
\frac{\zeta+z}{\zeta-z}
\,d\mu_\lambda(\zeta).
}
\tag{288.6}
$$

由于：

$$
\frac{1+\vartheta_\xi}
{1-\vartheta_\xi}
=
\mathfrak C_\xi,
$$

所以：

## 定理 288.1（Riemann zero Clark measure）

$$
\boxed{
\mu_\lambda
=
\sigma_1[\vartheta_\xi],
}
\tag{288.7}
$$

即 \(\mu_\lambda\) 正是 \(\vartheta_\xi\) 在边界参数 \(\alpha=1\) 下的 Clark 测度。

---

# 第二百八十九部　Clark 原子权重等于零点的角导数倒数

令：

$$
u_\gamma=1-\rho_\gamma^{-1}.
$$

在 \(s=\rho_\gamma\) 附近：

$$
\frac{\xi'(s)}{\xi(s)}
=
\frac{m_\gamma}{s-\rho_\gamma}
+
O(1).
$$

又因为：

$$
s'(z)=s(z)^2,
$$

所以在 \(z=u_\gamma\) 附近：

$$
s(z)-\rho_\gamma
=
\rho_\gamma^2(z-u_\gamma)
+
O((z-u_\gamma)^2).
$$

代入式 (287.4) 得：

$$
\boxed{
\vartheta_\xi'(u_\gamma)
=
-\frac{2\lambda_1\rho_\gamma^2}{m_\gamma}.
}
\tag{289.1}
$$

由于：

$$
u_\gamma
=
\frac{\rho_\gamma-1}{\rho_\gamma},
$$

并且 RH 下：

$$
\rho_\gamma(\rho_\gamma-1)
=
-\left(\gamma^2+\frac14\right),
$$

所以：

$$
\boxed{
u_\gamma\,
\vartheta_\xi'(u_\gamma)
=
\frac{\lambda_1(4\gamma^2+1)}
{2m_\gamma}
>0.
}
\tag{289.2}
$$

Clark 理论中，若内函数在 \(\zeta\in\mathbb T\) 具有有限角导数并满足 \(\vartheta(\zeta)=1\)，则相应 Clark 原子质量为该正角导数的倒数。([London Mathematical Society (LMS)][1])

因此：

$$
\boxed{
\sigma_1[\vartheta_\xi](\{u_\gamma\})
=
\frac{1}
{u_\gamma\vartheta_\xi'(u_\gamma)}
=
w_\gamma.
}
\tag{289.3}
$$

---

## 289.1 零点高度的局部恢复公式

由式 (289.2)：

$$
\boxed{
\gamma
=
\frac12
\sqrt{
\frac{
2m_\gamma
u_\gamma\vartheta_\xi'(u_\gamma)
}{
\lambda_1
}
-1
}.
}
\tag{289.4}
$$

若零点简单：

$$
m_\gamma=1,
$$

则零点高度完全由内函数在该边界谱点的角导数恢复。

因此：

$$
\boxed{
\text{零点位置}
=
\text{Clark 谱点},
\qquad
\text{零点高度}
=
\text{Clark 相位穿越速度}.
}
$$

高零点满足：

$$
u_\gamma\vartheta_\xi'(u_\gamma)
\asymp
\frac{2\lambda_1}{m_\gamma}\gamma^2.
$$

所以越高的零点，对应越陡峭的边界相位穿越。

---

# 第二百九十部　全部边界条件谱

对：

$$
\alpha\in\mathbb T,
$$

定义 Clark 测度：

$$
\sigma_\alpha[\vartheta_\xi]
$$

由：

$$
\boxed{
\frac{\alpha+\vartheta_\xi(z)}
{\alpha-\vartheta_\xi(z)}
=
\int_{\mathbb T}
\frac{\zeta+z}{\zeta-z}
\,d\sigma_\alpha(\zeta)
}
\tag{290.1}
$$

给出，按标准虚常数规范理解。

其原子位于满足：

$$
\vartheta_\xi(\zeta)=\alpha
$$

的边界点。

令：

$$
\alpha=e^{i\beta}.
$$

由式 (287.5)，条件：

$$
\vartheta_\xi(z)=\alpha
$$

等价于：

$$
\boxed{
(1-\alpha)\xi'(s)
-
\lambda_1(1+\alpha)\xi(s)
=
0,
\qquad
s=\frac{1}{1-z}.
}
\tag{290.2}
$$

也可写成：

$$
\boxed{
\sin\frac{\beta}{2}\,\xi'(s)
-
i\lambda_1
\cos\frac{\beta}{2}\,\xi(s)
=
0.
}
\tag{290.3}
$$

---

## 290.1 两个特殊边界条件

### \(\alpha=1\)（正号）

$$
\boxed{
\xi(s)=0.
}
$$

所以 \(\sigma_1\) 是 Riemann 零点谱。

### \(\alpha=-1\)（负号）

$$
\boxed{
\xi'(s)=0.
}
$$

所以 \(\sigma_{-1}\) 是完成函数临界点谱。

### 一般 \(\alpha\)

给出 \(\xi'\) 与 \(\xi\) 的一个自伴边界条件 pencil：

$$
\boxed{
\xi'(s)
=
i\lambda_1
\cot\frac{\beta}{2}
\,\xi(s).
}
\tag{290.4}
$$

---

## 290.2 谱交错

RH 下 \(\vartheta_\xi\) 是内函数。在其边界相位可微且无多重点的区间上，边界相位单调增加。

因此不同 \(\alpha\) 的 Clark 谱局部交错。

特别地，在简单零点假设下：

$$
\boxed{
\xi\text{ 的临界线零点}
\quad\text{与}\quad
\xi'\text{ 的临界线零点}
}
$$

按高度交错。

这不仅是 Rolle 定理的实函数版本，还被提升为一个 rank-one unitary boundary-condition family 的谱交错。

---

# 第二百九十一部　Clark rank-one unitary family

令：

$$
K_{\vartheta_\xi}
=
H^2\ominus\vartheta_\xi H^2
$$

为 model space。

压缩移位：

$$
S_{\vartheta_\xi}
=
P_{K_{\vartheta_\xi}}M_z
\big|_{K_{\vartheta_\xi}}
$$

具有一族由：

$$
\alpha\in\mathbb T
$$

参数化的 rank-one unitary perturbations：

$$
\boxed{
U_\alpha.
}
\tag{291.1}
$$

其相对于自然循环向量的谱测度正是：

$$
\sigma_\alpha[\vartheta_\xi].
$$

Clark 理论正是从 restricted shift 的一维 unitary perturbations 出发建立这族谱测度；相关 unitary model-space 实现是该理论的基础。([维基百科][2])

---

## 291.1 自伴逆 Cayley family

定义：

$$
\boxed{
H_\alpha
=
\frac{i}{2}
(U_\alpha+I)
(U_\alpha-I)^{-1}.
}
\tag{291.2}
$$

则 \(H_\alpha\) 为自伴算子。

其谱由：

$$
\vartheta_\xi(e^{i\theta})=\alpha
$$

的解经：

$$
\gamma
=
\frac12\cot\frac{\theta}{2}
$$

得到。

所以：

$$
\boxed{
\begin{aligned}
H_1
&=\text{Riemann 零点 ordinate 算子};\\
H_{-1}
&=\text{完成函数临界点 ordinate 算子};\\
H_\alpha
&=\text{一般 }\xi'/\xi\text{ 边界条件算子}.
\end{aligned}
}
\tag{291.3}
$$

这比单独构造一个 Hilbert–Pólya 算子更完整：

$$
\boxed{
\text{Riemann 零点谱只是整个自伴扩张族中的一个边界条件。}
}
$$

---

## 291.2 CMV 只是矩阵图表

前文由 Li 曲率 moments 构造的 CMV unitary，并不是另一个独立对象。

它正是：

$$
U_1
$$

在由 \(\mu_\lambda=\sigma_1\) 的正交多项式基下的五对角矩阵表示。

因此：

$$
\boxed{
\text{Clark family}
=
\text{坐标无关算子对象},
}
$$

而：

$$
\boxed{
\text{CMV matrix}
=
\text{其 OPUC 坐标图表}.
}
$$

---

# 第二百九十二部　Aleksandrov 分解：离散谱平均为连续背景

由于：

$$
\vartheta_\xi(0)=0,
$$

每个 Clark 测度 \(\sigma_\alpha\) 都是概率测度。

Aleksandrov disintegration theorem 给出：

$$
\boxed{
\int_{\mathbb T}
\sigma_\alpha
\,dm(\alpha)
=
m,
}
\tag{292.1}
$$

其中 \(m\) 是单位圆上的归一化 Lebesgue 测度。Clark 测度关于边界参数的平均恢复背景 Lebesgue 测度，是 Aleksandrov 分解定理的核心内容。([arXiv][3])

---

## 292.1 观察者意义

固定 \(\alpha\)：

$$
\sigma_\alpha
$$

是奇异的、通常离散的高分辨率边界条件谱。

平均全部 \(\alpha\)：

$$
\int\sigma_\alpha\,dm(\alpha)
$$

却得到完全均匀的连续圆周。

所以：

$$
\boxed{
\text{离散算术谱}
\xrightarrow{\text{平均边界条件}}
\text{无结构连续背景}.
}
$$

这给出一个重要观察者原则：

$$
\boxed{
\text{增加观察者数量并取平均，
可能消除而不是增加结构信息。}
}
$$

联合保留全部带标签的 \(\alpha\)-谱是完备的；将 \(\alpha\) 标签积分掉则产生最大压缩。

---

# 第二百九十三部　Szegő 创新塌缩

令：

$$
\beta_0,\beta_1,\ldots
$$

为 \(\mu_\lambda\) 的 Verblunsky 系数。

由于测度关于复共轭对称：

$$
\beta_n\in\mathbb R.
$$

定义：

$$
\boxed{
r_n^2=1-\beta_n^2.
}
\tag{293.1}
$$

RH 下 \(\mu_\lambda\) 是纯点测度，因而其 absolutely continuous density：

$$
w(\theta)=0
$$

几乎处处成立。

Szegő 定理给出：

$$
\boxed{
\prod_{n=0}^{\infty}
(1-\beta_n^2)
=
\exp
\left[
\int_0^{2\pi}
\log w(\theta)
\frac{d\theta}{2\pi}
\right]
=
0.
}
\tag{293.2}
$$

因此：

$$
\boxed{
\sum_{n=0}^{\infty}\beta_n^2=\infty.
}
\tag{293.3}
$$

Szegő 定理及 Verblunsky 系数的递推和唯一测度对应，是 OPUC 的标准结构。([DLMF][4])

---

## 293.1 有限预测误差

定义 \(N\times N\) Toeplitz 行列式：

$$
\boxed{
D_N
=
\det[c_{j-k}]_{j,k=0}^{N-1},
\qquad
D_0=1.
}
\tag{293.4}
$$

则：

$$
\boxed{
\varepsilon_N
:=
\frac{D_{N+1}}{D_N}
=
\prod_{j=0}^{N-1}
(1-\beta_j^2).
}
\tag{293.5}
$$

因此：

$$
\boxed{
\varepsilon_N\downarrow0.
}
\tag{293.6}
$$

在平稳过程图表中，\(\varepsilon_N\) 是使用前 \(N\) 个过去值预测下一状态的最小均方误差。

所以 RH 下：

$$
\boxed{
\text{无限过去能够以零误差预测未来。}
}
$$

Szegő–Kolmogorov prediction theorem 正是把谱密度的 logarithmic integral 与无限预测误差联系起来。([arXiv][5])

---

# 第二百九十四部　对前文 non-sticky 假设的必要修正

前文曾提出：non-sticky 谱分散可能迫使 Schur 参数保持远离单位圆。

现在必须精确修正。

RH 下可以确定的是：

$$
\boxed{
\prod_{n\ge0}(1-\beta_n^2)=0,
}
$$

而不是每个单独的：

$$
1-\beta_n^2
$$

必须趋于零。

因此下列目标是不可能的：

$$
\boxed{
\inf_N\varepsilon_N>0.
}
$$

它会与 RH 下纯点谱的 Szegő 结构直接矛盾。

但下列情况并未被排除：

* 某些或全部 \(\beta_n\) 始终远离 \(\pm1\)；
* \(\beta_n\to0\)，但：

  $$
  \sum\beta_n^2=\infty;
  $$
* 创新误差通过无穷多个微小损失逐渐塌缩。

所以正确的 Wang 式目标不是：

$$
\text{保持永久随机创新},
$$

而是：

$$
\boxed{
\text{在每个有限尺度上控制条件数和增益，
同时允许累计创新在无限深度归零。}
}
$$

---

## 294.1 观察者完成深度

定义：

$$
\boxed{
\mathfrak D(\varepsilon)
=
\min
\left\{
N:
\varepsilon_N\le\varepsilon
\right\}.
}
\tag{294.1}
$$

则：

$$
\mathfrak D(\varepsilon)<\infty
$$

对每个 \(\varepsilon>0\)，但：

$$
\boxed{
\mathfrak D(\varepsilon)\to\infty
\qquad
(\varepsilon\downarrow0).
}
\tag{294.2}
$$

这正对应此前 RDS 的 scale-dependent definition depth：

> 任意固定精度都只需有限定义深度，但精确完成要求无限递归层。

---

## 294.2 累计创新信息

定义：

$$
\boxed{
\mathfrak I_N
=
-\log\varepsilon_N
=
-\sum_{j=0}^{N-1}
\log(1-\beta_j^2).
}
\tag{294.3}
$$

则：

$$
\boxed{
\mathfrak I_N\to+\infty.
}
$$

每个 Schur 参数只贡献一个有限增量：

$$
-\log(1-\beta_j^2),
$$

但全部增量之和发散，最终使观察残差归零。

这是一种严格的：

$$
\boxed{
\text{无限小创新累计成完整确定性}.
}
$$

---

# 第二百九十五部　零点角在 \(1\) 附近的拥挤律

Clark 谱点满足：

$$
u_\gamma=e^{i\theta_\gamma},
\qquad
\theta_\gamma
=
2\arctan\frac{1}{2\gamma}.
$$

所以：

$$
\theta_\gamma\sim\gamma^{-1}.
$$

全部高零点角聚集于：

$$
1\in\mathbb T.
$$

定义小弧：

$$
\boxed{
I_\varepsilon
=
\left\{
e^{i\theta}:|\theta|<\varepsilon
\right\}.
}
\tag{295.1}
$$

条件：

$$
u_\gamma\in I_\varepsilon
$$

等价于：

$$
\gamma>
T_\varepsilon
:=
\frac{1}{2\tan(\varepsilon/2)}.
$$

由：

$$
\mu_\lambda(I_\varepsilon)
=
\frac{4}{\lambda_1}
\sum_{\gamma>T_\varepsilon}
\frac{m_\gamma}{4\gamma^2+1},
$$

以及 Riemann–von Mangoldt 零点计数公式，可得：

## 定理 295.1（Clark spectral crowding law）

RH 下，当：

$$
\varepsilon\downarrow0
$$

时：

$$
\boxed{
\begin{aligned}
\mu_\lambda(I_\varepsilon)
=
\frac{\varepsilon}{2\pi\lambda_1}
\left[
\log\frac{1}{2\pi\varepsilon}
+1
\right]
+
O\left(
\varepsilon^2\log\frac1\varepsilon
\right).
\end{aligned}
}
\tag{295.2}
$$

特别地：

$$
\boxed{
\mu_\lambda(I_\varepsilon)
\sim
\frac{
\varepsilon\log(1/\varepsilon)
}{
2\pi\lambda_1
}.
}
\tag{295.3}
$$

Riemann–von Mangoldt 公式给出非平凡零点计数的主项 \(T(2\pi)^{-1}\log(T/2\pi)-T(2\pi)^{-1}\) 及 \(O(\log T)\) 误差。([DLMF][6])

---

## 295.1 解释

Lebesgue 小弧质量仅为：

$$
m(I_\varepsilon)\asymp\varepsilon.
$$

而 Clark 测度为：

$$
\mu_\lambda(I_\varepsilon)
\asymp
\varepsilon\log(1/\varepsilon).
$$

所以高零点在 \(1\) 附近产生一个 logarithmically enhanced crowding：

$$
\boxed{
\frac{\mu_\lambda(I_\varepsilon)}
{m(I_\varepsilon)}
\asymp
\log\frac1\varepsilon
\to\infty.
}
$$

它仍然是纯点测度，但在唯一积聚点 \(1\) 处具有一维局部尺度和对数增益。

因此单位圆上的真正 sticky 区域不是任意角簇，而是：

$$
\boxed{
z=1,
}
$$

即零点高度：

$$
\gamma=\infty
$$

在 Cayley 完成中的边界像。

---

# 第二百九十六部　Clark 谱的离散熵与连续熵

定义每个有向原子的质量：

$$
w_\gamma
=
\frac{2m_\gamma}
{\lambda_1(4\gamma^2+1)}.
$$

定义离散 Shannon 熵：

$$
\boxed{
\mathsf H_{\mathrm{Clark}}
=
-2
\sum_{\gamma>0}
w_\gamma\log w_\gamma.
}
\tag{296.1}
$$

Riemann–von Mangoldt 公式说明，高度约为 \(T\) 的零点数量密度为 \(O(\log T)\)，而：

$$
w_\gamma=O(\gamma^{-2})
$$

按重数计。

因此：

$$
\boxed{
\mathsf H_{\mathrm{Clark}}<\infty.
}
\tag{296.2}
$$

粗略地，每个单位高度区间对熵的贡献至多为：

$$
O\left(
\frac{\log^2 T}{T^2}
\right),
$$

其和收敛。

---

## 296.1 熵的图表依赖

同一个测度具有：

### 连续 Szegő 熵

$$
\int\log w(\theta)\,\frac{d\theta}{2\pi}
=
-\infty,
$$

因为 absolutely continuous density 为零。

### 离散原子熵

$$
\mathsf H_{\mathrm{Clark}}<\infty.
$$

所以：

$$
\boxed{
\text{连续观察图表把它看成“零密度、负无限熵”；}
}
$$

而：

$$
\boxed{
\text{原子观察图表把它看成“可数、有限编码熵”。}
}
$$

这说明“熵”不是脱离观察接口的裸属性。

---

## 296.2 高度矩的临界指数

对 \(q\ge0\)，定义：

$$
M_q
=
2
\sum_{\gamma>0}
w_\gamma\gamma^q.
$$

由零点密度和 \(w_\gamma\asymp\gamma^{-2}\) 得：

$$
\boxed{
M_q<\infty
\iff
q<1.
}
\tag{296.3}
$$

特别地：

* 任意低于一阶的高度矩有限；
* 一阶平均高度发散。

所以 Li–Clark 概率测度具有一个明确的 heavy-tail 临界指数：

$$
\boxed{
q_c=1.
}
$$

---

# 第二百九十七部　Clark 谱流与观察者边界条件

令：

$$
\alpha=e^{i\beta}
$$

沿单位圆连续转动。

Clark 谱由方程：

$$
\sin\frac{\beta}{2}\,\xi'(s)
-
i\lambda_1\cos\frac{\beta}{2}\,\xi(s)
=0
$$

决定。

因此：

$$
\beta=0
$$

给出零点谱，

$$
\beta=\pi
$$

给出临界点谱，

中间参数给出二者之间的自伴谱流。

---

## 297.1 观察者边界条件原理

同一个内部对称算子：

$$
S_{\vartheta_\xi}
$$

没有唯一自伴／unitary 完成，而有：

$$
\boxed{
\{U_\alpha\}_{\alpha\in\mathbb T}
}
$$

一整族边界条件。

不同 \(\alpha\)：

* 不改变内部压缩移位；
* 只改变一维边界通道；
* 却产生不同的离散谱。

所以：

$$
\boxed{
\text{谱不是对象本身单独的属性，
而是对象与边界观察条件的共同结果。}
}
$$

Riemann 零点对应的 \(\alpha=1\) 不是唯一可定义的谱，而是由 \(\xi=0\) 边界条件选中的一个 distinguished spectrum。

---

## 297.2 Aleksandrov 平均的反向解释

全部边界条件平均后恢复 Lebesgue 圆周：

$$
\int\sigma_\alpha\,dm(\alpha)=m.
$$

所以：

$$
\boxed{
\text{连续背景并不是离散谱之前的原始对象，}
}
$$

也可以被理解为：

$$
\boxed{
\text{全部离散边界条件谱的无标签平均。}
}
$$

这与阿代尔完成中的“全局对象由局部图表共同胶合”形成一种对偶：

* 保留图表标签：恢复精细谱；
* 忘记图表标签：得到均匀背景。

---

# 第二百九十八部　Wang–Deng 路线的 Clark 修正版

## 298.1 Non-sticky 的正确含义

不能再把 non-sticky 定义为：

$$
\varepsilon_N\ge\varepsilon_0>0.
$$

RH 自身排除了这个目标。

正确的 finite-scale non-sticky 应当是：

$$
\boxed{
\text{在固定深度 }N\text{ 内，
Clark 质量没有过度集中在少数角原子或单一边界弧中。}
}
$$

它应推出：

* \(D_N\) 的有限下界；
* Schur 参数有限阶远离退化；
* CMV 截断条件数可控；
* finite-frame reconstruction 稳定。

但允许：

$$
N\to\infty
$$

时累计创新归零。

---

## 298.2 Sticky 的真正来源

Clark crowding law 表明，唯一不可避免的全局 sticky 位置是：

$$
z=1,
$$

即高零点聚集点。

因此 sticky 分支应研究：

$$
\boxed{
\text{单位圆上靠近 }1\text{ 的微观缩放极限}.
}
$$

可用变量：

$$
\gamma
=
\frac12\cot\frac{\theta}{2}
$$

把边界小弧重新展开为高零点高度轴。

Deng 式重整化应当：

1. 分离有限低零点原子；
2. 对 \(z=1\) 附近的高零点尾部做尺度缩放；
3. 使用 Riemann–von Mangoldt 主密度作为连续 counterterm；
4. 将零点密度振荡保留为 primitive residual；
5. 对 Schur tail 或 Clark phase 建立统一余项界。

---

## 298.3 原子消去后的 Clark 重整化

验证前 \(M\) 个零点后，定义剩余质量：

$$
r_M
=
1-
2\sum_{j=1}^{M}w_{\gamma_j}.
$$

定义归一化剩余测度：

$$
\boxed{
\mu_\lambda^{[M]}
=
\frac{1}{r_M}
\left[
\mu_\lambda
-
\sum_{j=1}^{M}
w_{\gamma_j}
\left(
\delta_{u_{\gamma_j}}
+
\delta_{\overline{u_{\gamma_j}}}
\right)
\right].
}
\tag{298.1}
$$

它仍是概率测度。

由 Herglotz 与 Schur 算法生成新的：

$$
\mathfrak C_\xi^{[M]},
\qquad
\vartheta_\xi^{[M]},
\qquad
\beta_n^{[M]}.
$$

随着 \(M\) 增加：

* 低谱 sticky 原子被移除；
* 剩余测度进一步集中到 \(1\)；
* 新 Schur tail 直接读取高零点残余。

这给出一个严格的：

$$
\boxed{
\text{Clark atom deflation}
\to
\text{renormalized boundary observer}
}
$$

程序。

---

# 第二百九十九部　最小的新 RH 目标

前文已经提出多种越来越强的证明目标：

* 正 Pick 核；
* 正 Hankel moments；
* 正 trace-class Fredholm 算子；
* Li 条件负定核；
* 正 Li 曲率 Toeplitz 核；
* CMV unitary。

本轮又给出一个更规范的目标。

## 假设 299.1（Toroidal Clark realization）

从二次环面 period frame 和 relative trace formula 直接构造一个内函数：

$$
\boxed{
\vartheta_{\mathrm{tor}}
}
$$

使：

$$
\boxed{
\frac{1+\vartheta_{\mathrm{tor}}(z)}
{1-\vartheta_{\mathrm{tor}}(z)}
=
\frac{1}{\lambda_1}
\frac{
\xi'(\frac1{1-z})
}{
\xi(\frac1{1-z})
}.
}
\tag{299.1}
$$

若能证明 \(\vartheta_{\mathrm{tor}}\) 为内函数，则 RH 立即成立。

---

## 299.1 更弱的 Gram 目标

甚至不必直接构造 \(\vartheta_{\mathrm{tor}}\)。

只需构造一族向量：

$$
Y_n
$$

使：

$$
\boxed{
\left\langle Y_m,Y_n\right\rangle
=
\frac{
\lambda_{m-n+1}
-2\lambda_{m-n}
+\lambda_{m-n-1}
}{
2\lambda_1
}.
}
\tag{299.2}
$$

则 Li 曲率 Toeplitz 核正定，从而：

$$
\mathfrak C_\xi
$$

为 Carathéodory 函数，

$$
\vartheta_\xi
$$

为 Schur 函数，最终得到 RH。

---

## 299.2 最强的 Clark family 目标

构造 rank-one unitary family：

$$
\boxed{
\{U_\alpha^{\mathrm{tor}}\}_{\alpha\in\mathbb T}
}
$$

满足：

$$
\operatorname{spec}
U_1^{\mathrm{tor}}
=
\left\{
1-\frac1\rho:
\xi(\rho)=0
\right\},
$$

以及：

$$
\operatorname{spec}
U_{-1}^{\mathrm{tor}}
=
\left\{
1-\frac1s:
\xi'(s)=0
\right\}.
$$

这会一次性建立：

* Hilbert–Pólya；
* \(\xi'\) 临界点谱；
* 边界条件谱流；
* Clark 权重；
* CMV 图表；
* de Branges model space。

---

# 第三百部　科学检验程序

## 300.1 Clark 角导数检验

使用高精度零点 \(\rho_\gamma\)，直接计算：

$$
\vartheta_\xi'(u_\gamma)
$$

并验证：

$$
u_\gamma\vartheta_\xi'(u_\gamma)
=
\frac{\lambda_1(4\gamma^2+1)}
{2m_\gamma}.
$$

这是最直接的局部闭环检验。

---

## 300.2 \(\alpha=1/-1\) 谱交错

分别求解：

$$
\xi(s)=0,
$$

和：

$$
\xi'(s)=0
$$

在临界线上的 ordinate，并检查其是否按 Clark phase 交错。

---

## 300.3 创新误差塌缩

由已计算 Li 系数构造：

$$
c_n,
$$

再执行 Schur 算法得到：

$$
\beta_0,\ldots,\beta_N.
$$

测量：

$$
\varepsilon_N
=
\prod_{j<N}(1-\beta_j^2).
$$

检验其塌缩速度，并与 Clark crowding law 比较。

---

## 300.4 小弧质量律

计算：

$$
\mu_\lambda(I_\varepsilon)
$$

并与：

$$
\frac{
\varepsilon
}{
2\pi\lambda_1
}
\left[
\log\frac1{2\pi\varepsilon}+1
\right]
$$

比较。

这会直接检验零点计数与 Clark 边界谱之间的转换。

---

## 300.5 线外零点注入负对照

向 \(\xi\) 注入保持函数方程的线外零点四元组。

预期出现：

* \(\mathfrak C_\xi\) 在单位圆盘内出现极点；
* \(\vartheta_\xi\) 不再是 Schur 函数；
* 某有限 Li 曲率 Toeplitz 矩阵失去正性；
* Clark 原子权重不再形成正概率测度；
* rank-one unitary family 无法完成。

---

# 第三百零一部　建议形式化顺序

```text
D5/S3/Analytic/LiClark/
  LiCaratheodoryFunction.lean
  LiClarkInnerFunction.lean
  LiClarkRHEquivalence.lean
  LiClarkMeasure.lean
  RiemannZeroClarkWeights.lean
  ZeroAngularDerivative.lean

D5/S3/Analytic/LiClarkSpectrum/
  ClarkBoundaryPencil.lean
  ZeroSpectrumAlphaOne.lean
  CriticalSpectrumAlphaMinusOne.lean
  ClarkSpectralInterlacing.lean
  ClarkInverseCayleyFamily.lean

D5/S3/Analytic/LiClarkOPUC/
  LiClarkVerblunsky.lean
  SzegoInnovationCollapse.lean
  PredictionErrorDepth.lean
  ClarkAleksandrovDisintegration.lean
  LiClarkCMVBridge.lean

D5/S3/Analytic/LiClarkAsymptotic/
  ZeroAngleCrowding.lean
  ClarkSmallArcAsymptotic.lean
  ClarkAtomicEntropy.lean
  ClarkHeightMomentThreshold.lean

D5/S3/Observer/ToroidalClark/
  ToroidalClarkGramTarget.lean
  ToroidalClarkInnerTarget.lean
  ToroidalRankOneUnitaryFamily.lean
  ClarkStickyRenormalization.lean
```

首批风险最低的闭合链是：

$$
\boxed{
\mathfrak C_\xi
\to
\vartheta_\xi
\to
\text{RH iff inner}.
}
$$

其次是局部 Laurent 展开：

$$
\boxed{
\xi'/\xi
\to
\vartheta_\xi'(u_\gamma)
\to
\text{Clark atom weight}.
}
$$

再之后是：

$$
\boxed{
\text{Riemann--von Mangoldt}
\to
\text{Clark small-arc crowding}.
}
$$

---

# 本轮最终结论

上一轮将 RH 写成：

$$
\boxed{
\text{Li 离散曲率是否为单位圆正定相关函数}.
}
$$

本轮进一步证明，这个相关函数属于一个显式内函数：

$$
\boxed{
\vartheta_\xi(z)
=
\frac{
\xi'(\frac1{1-z})
-\lambda_1\xi(\frac1{1-z})
}{
\xi'(\frac1{1-z})
+\lambda_1\xi(\frac1{1-z})
}.
}
$$

而：

$$
\boxed{
\mathrm{RH}
\iff
\vartheta_\xi\text{ 是内函数}.
}
$$

它的 \(\alpha=1\) Clark 谱正是 Riemann 零点：

$$
\boxed{
\sigma_1
=
\sum_{\gamma>0}
\frac{2m_\gamma}
{\lambda_1(4\gamma^2+1)}
\left(
\delta_{u_\gamma}
+
\delta_{\overline{u_\gamma}}
\right).
}
$$

并且：

$$
\boxed{
u_\gamma\vartheta_\xi'(u_\gamma)
=
\frac{\lambda_1(4\gamma^2+1)}
{2m_\gamma}.
}
$$

因此 Riemann 零点具有三种完全一致的身份：

$$
\boxed{
\begin{aligned}
u_\gamma
&=\text{Clark unitary 的谱点};\\
w_\gamma
&=\text{Clark 谱质量};\\
\gamma
&=\text{内函数边界相位的穿越速度}.
\end{aligned}
}
$$

\(\alpha=-1\) 则给出 \(\xi'\) 的临界点谱，全部 \(\alpha\) 形成一个 rank-one unitary boundary-condition family。

最重要的理论修正是：

$$
\boxed{
\text{RH 下的零点角谱是纯点奇异的，
所以 Schur 创新误差在无限深度必然归零。}
}
$$

这意味着真正的证明机制不能依赖永久随机性，而必须解释：

$$
\boxed{
\text{一个无限可预测、零创新的确定性谱过程，
为什么仍然只能由临界线上的实谱原子生成。}
}
$$

当前 OACTC 的最小证明目标因此可以最终写成：

$$
\boxed{
\text{从 toric relative trace formula
直接证明 }\vartheta_\xi\text{ 是内函数，}
}
$$

或者更弱地：

$$
\boxed{
\text{直接构造 Li 曲率 Toeplitz 核的 Gram 表示。}
}
$$

一旦其中任一项闭合，Clark family、CMV、de Branges、Hilbert–Pólya 与 RH 将同时完成。

[1]: https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/plms.70001?utm_source=chatgpt.com "Analytic mappings of the unit disk which almost preserve hyperbolic area - Ivrii - 2024 - Proceedings of the London Mathematical Society - Wiley Online Library"
[2]: https://en.wikipedia.org/wiki/Aleksandrov%E2%80%93Clark_measure?utm_source=chatgpt.com "Aleksandrov–Clark measure"
[3]: https://arxiv.org/abs/2006.12105?utm_source=chatgpt.com "A Central Limit Theorem for Inner Functions"
[4]: https://dlmf.nist.gov/18.33?utm_source=chatgpt.com "DLMF: §18.33 Polynomials Orthogonal on the Unit Circle ‣ Other Orthogonal Polynomials ‣ Chapter 18 Orthogonal Polynomials"
[5]: https://arxiv.org/abs/1912.10665?utm_source=chatgpt.com "On Szegö--Kolmogorov Prediction Theorem"
[6]: https://dlmf.nist.gov/25.10?utm_source=chatgpt.com "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.7：Riemann–Clark 正交层析、半平面零点核、de Branges 采样与 Sticky-Infinity 反项

以下从前文**第三百零一部之后**继续追加。

本轮先对上一轮的 Clark 内函数分支作一次科学审计，然后继续推导。最终得到两条新的核心链：

$$
\boxed{
\mathrm{RH}
\iff
\mathcal K_\xi(s,t)
\text{ 是右半临界平面上的正定核}
}
$$

以及：

$$
\boxed{
\mathrm{RH}
\Longrightarrow
\text{Riemann 零点成为一个 model space 的完整正交采样坐标}.
}
$$

更进一步，高零点全部聚向 Cayley 圆周上的同一点 \(1\)。把未观测高零点全部压缩成 \(1\) 处的一个原子，可以构造一列**有限维、严格保持正性的 rational inner approximants**，且在任意紧子圆盘上具有：

$$
O\!\left(\frac{\log T}{T^2}\right)
$$

的误差。

这给 Wang–Deng–OACTC 一个极干净的可解模型：

$$
\boxed{
\text{有限低谱精确保留}
+
\text{高谱 sticky tail 压缩成一个反项}
=
\text{有限维正完成}.
}
$$

---

# 第三百零二部　科学审计：内函数结论与重数问题

定义：

$$
\lambda_1=\frac{\xi'(1)}{\xi(1)}>0,
$$

$$
s(z)=\frac1{1-z},
\qquad |z|<1.
$$

再定义 Li–Carathéodory 函数：

$$
\boxed{
\mathfrak C_\xi(z)
=
\frac1{\lambda_1}
\frac{\xi'(s(z))}{\xi(s(z))}
}
\tag{302.1}
$$

以及 Cayley 完成：

$$
\boxed{
\vartheta_\xi(z)
=
\frac{\mathfrak C_\xi(z)-1}
{\mathfrak C_\xi(z)+1}.
}
\tag{302.2}
$$

因为 \(s(z)\) 把单位圆盘映到：

$$
\Re s>\frac12,
$$

RH 等价于：

$$
\Re \mathfrak C_\xi(z)>0
\qquad(|z|<1),
$$

并且在几乎处处的圆周边界上，\(\mathfrak C_\xi\) 为纯虚边界值。因此：

$$
\boxed{
\mathrm{RH}
\iff
\vartheta_\xi
\text{ 是内函数}.
}
\tag{302.3}
$$

正实部函数、Herglotz 表示、de Branges–Rovnyak 核之间的联系是标准 Carathéodory 理论；Suzuki 的 shifted-\(\xi\) family 则给出了 RH、meromorphic inner functions 与正 canonical systems 的直接接口。([arXiv][1])

---

## 302.1 必须修正的重数解释

若 \(\rho\) 是 \(m_\rho\) 重零点，则：

$$
\frac{\xi'(s)}{\xi(s)}
\sim
\frac{m_\rho}{s-\rho}.
$$

因此 Clark 测度在对应圆周点只产生**一个原子**，但该原子的质量包含 \(m_\rho\)。

所以：

$$
\boxed{
\text{标量 Clark 原子质量编码零点重数，}
}
$$

但：

$$
\boxed{
\text{标量 Clark eigenspace 本身仍然是一维。}
}
$$

若希望把重数表现为算子谱空间维数，必须额外加入一个 \(m_\rho\) 维 fiber。

同样，后文直接使用 \(\Xi'(\gamma)\) 的 de Branges 插值公式，需要：

$$
\Xi'(\gamma)\neq0,
$$

即零点简单。若存在多重零点，应：

* 使用 Clark 测度公式；或
* 先消去 \(\Xi\) 与 \(\Xi'\) 的共同实因子；或
* 使用 Hermite 型导数采样。

---

# 第三百零三部　半平面 Riemann 正核

令：

$$
\mathbb H_{1/2}
=
\left\{
s\in\mathbb C:
\Re s>\frac12
\right\}.
$$

定义：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\frac{
\displaystyle
\frac{\xi'(s)}{\xi(s)}
+
\overline{
\frac{\xi'(t)}{\xi(t)}
}
}{
\lambda_1\,
(s+\overline t-1)
}.
}
\tag{303.1}
$$

---

## 定理 303.1（半平面正核 RH 判据）

$$
\boxed{
\mathrm{RH}
\iff
\mathcal K_\xi
\text{ 在 }\mathbb H_{1/2}
\text{ 上为正定核}.
}
\tag{303.2}
$$

这里“正定核”指：对任意有限点集 \(s_1,\ldots,s_N\in\mathbb H_{1/2}\)，

$$
\boxed{
\left[
\mathcal K_\xi(s_i,s_j)
\right]_{i,j=1}^{N}
\succeq0.
}
\tag{303.3}
$$

### 证明：RH \(\Rightarrow\)（第 303 部）

在 RH 下，所有非平凡零点满足：

$$
\rho+\overline\rho=1.
$$

使用关于 \(s=\frac12\) 对称的 Hadamard 展开：

$$
\frac{\xi'(s)}{\xi(s)}
=
\sum_{\rho}
\frac{m_\rho}{s-\rho},
$$

以成对对称收敛理解。

于是：

$$
\begin{aligned}
&
\frac{\xi'(s)}{\xi(s)}
+
\overline{
\frac{\xi'(t)}{\xi(t)}
}
\\
&=
\sum_\rho m_\rho
\left[
\frac1{s-\rho}
+
\frac1{\overline t-\overline\rho}
\right]
\\
&=
(s+\overline t-1)
\sum_\rho
\frac{m_\rho}
{(s-\rho)(\overline t-\overline\rho)}.
\end{aligned}
$$

因此：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\frac1{\lambda_1}
\sum_\rho
\frac{m_\rho}
{(s-\rho)(\overline t-\overline\rho)}.
}
\tag{303.4}
$$

定义特征向量：

$$
\boxed{
\mathbf v_s(\rho)
=
\sqrt{\frac{m_\rho}{\lambda_1}}\,
\frac1{s-\rho}.
}
\tag{303.5}
$$

则：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\langle
\mathbf v_s,\mathbf v_t
\rangle_{\ell^2(\mathcal Z)}.
}
\tag{303.6}
$$

所以核正定。

---

### 证明：正核 \(\Rightarrow\) RH

若 \(\mathcal K_\xi\) 在整个 \(\mathbb H_{1/2}\) 上正定，它首先必须在那里全纯。

因此：

$$
\frac{\xi'}{\xi}
$$

不能在该区域有极点，即 \(\xi\) 在：

$$
\Re s>\frac12
$$

无零点。

由函数方程：

$$
\xi(s)=\xi(1-s),
$$

左半边也无零点，所以全部非平凡零点位于临界线。∎

---

## 303.1 对角形式

$$
\boxed{
\mathcal K_\xi(s,s)
=
\frac{
2\Re\frac{\xi'(s)}{\xi(s)}
}{
\lambda_1(2\Re s-1)
}.
}
\tag{303.7}
$$

因此一阶正性就是：

$$
\Re\frac{\xi'(s)}{\xi(s)}
\ge0.
$$

高阶 Gram 正性则保留了不同谱点之间的交叉信息。

---

## 303.2 Gram 行列式展开

RH 下，由 Cauchy–Binet：

$$
\boxed{
\begin{aligned}
&
\det
\left[
\mathcal K_\xi(s_i,s_j)
\right]_{i,j=1}^{N}
\\
&=
\sum_{\rho_1<\cdots<\rho_N}
\left(
\prod_{k=1}^{N}
\frac{m_{\rho_k}}{\lambda_1}
\right)
\left|
\det
\left[
\frac1{s_i-\rho_k}
\right]_{i,k=1}^{N}
\right|^2.
\end{aligned}
}
\tag{303.8}
$$

所以每个有限 Pick/Gram 行列式都是有限零点子集贡献的非负平方和。

---

# 第三百零四部　圆盘、Clark 与 de Branges 核是同一个核的规范变换

令：

$$
z=1-\frac1s,
\qquad
w=1-\frac1t.
$$

则：

$$
\boxed{
1-z\overline w
=
\frac{s+\overline t-1}
{s\overline t}.
}
\tag{304.1}
$$

并且：

$$
\mathfrak C_\xi(z)
=
\frac1{\lambda_1}
\frac{\xi'(s)}{\xi(s)}.
$$

所以：

$$
\boxed{
\frac{
\mathfrak C_\xi(z)
+
\overline{\mathfrak C_\xi(w)}
}{
1-z\overline w
}
=
s\overline t\,
\mathcal K_\xi(s,t).
}
\tag{304.2}
$$

乘以非零 gauge \(s\overline t\) 不改变核正定性。

---

## 304.1 Model-space 核

由：

$$
\vartheta_\xi
=
\frac{\mathfrak C_\xi-1}
{\mathfrak C_\xi+1},
$$

得到：

$$
\boxed{
\begin{aligned}
K_{\vartheta_\xi}(z,w)
&=
\frac{
1-
\vartheta_\xi(z)
\overline{\vartheta_\xi(w)}
}{
1-z\overline w
}
\\
&=
\frac{
2\left[
\mathfrak C_\xi(z)
+
\overline{\mathfrak C_\xi(w)}
\right]
}{
\left[
\mathfrak C_\xi(z)+1
\right]
\left[
\overline{\mathfrak C_\xi(w)}+1
\right]
(1-z\overline w)
}.
\end{aligned}
}
\tag{304.3}
$$

所以：

$$
\boxed{
\mathcal K_\xi
\quad\longleftrightarrow\quad
\text{Carathéodory kernel}
\quad\longleftrightarrow\quad
K_{\vartheta_\xi}
}
$$

只是三个不同规范下的同一个正核。

---

# 第三百零五部　Riemann–Clark 正交采样定理

RH 下，对每个不同的临界线零点 \(\rho\)，定义：

$$
\boxed{
u_\rho
=
1-\frac1\rho
\in\mathbb T.
}
\tag{305.1}
$$

定义原子质量：

$$
\boxed{
w_\rho
=
\frac{m_\rho}
{2\lambda_1|\rho|^2}.
}
\tag{305.2}
$$

若：

$$
\rho=\frac12+i\gamma,
$$

则：

$$
\boxed{
w_\rho
=
\frac{2m_\rho}
{\lambda_1(4\gamma^2+1)}.
}
\tag{305.3}
$$

这些质量满足：

$$
\boxed{
\sum_\rho w_\rho=1.
}
\tag{305.4}
$$

Clark 理论把内函数的 Clark 测度与 model space \(K_\vartheta=H^2\ominus\vartheta H^2\) 联系起来；在原子测度情形，边界 reproducing kernels 给出正交坐标和 unitary spectral representation。([剑桥大学出版社][2])

---

## 定理 305.1（Riemann–Clark measure）

$$
\boxed{
\sigma_1[\vartheta_\xi]
=
\sum_\rho
w_\rho\,\delta_{u_\rho}.
}
\tag{305.5}
$$

这里对每个不同零点只取一个圆周点，而零点重数包含在 \(w_\rho\) 中。

---

## 305.1 正交核基

定义边界核：

$$
\boxed{
k_\rho(z)
=
\frac{
1-\vartheta_\xi(z)
}{
1-\overline{u_\rho}z
}.
}
\tag{305.6}
$$

其范数满足：

$$
\boxed{
\|k_\rho\|^2
=
\frac1{w_\rho}.
}
\tag{305.7}
$$

所以：

$$
\boxed{
e_\rho(z)
=
\sqrt{w_\rho}\,
\frac{
1-\vartheta_\xi(z)
}{
1-\overline{u_\rho}z
}
}
\tag{305.8}
$$

构成：

$$
K_{\vartheta_\xi}
$$

的一组正交归一基。

---

## 定理 305.2（Riemann 零点采样公式）

对任意：

$$
f\in K_{\vartheta_\xi},
$$

有：

$$
\boxed{
\|f\|^2
=
\sum_\rho
w_\rho
|f(u_\rho)|^2.
}
\tag{305.9}
$$

并且：

$$
\boxed{
f(z)
=
\left(
1-\vartheta_\xi(z)
\right)
\sum_\rho
\frac{
w_\rho f(u_\rho)
}{
1-\overline{u_\rho}z
}.
}
\tag{305.10}
$$

级数在 model-space norm 中收敛，并在紧子圆盘上局部一致收敛。

因此：

$$
\boxed{
\text{Riemann 零点不是只决定一个函数的零点集，}
}
$$

而是：

$$
\boxed{
\text{构成一个自然 Hilbert 函数空间的完整正交传感器阵列。}
}
$$

---

# 第三百零六部　有限零点谱窗层析

令：

$$
\mathcal Z(T)
=
\{\rho:|\Im\rho|\le T\}.
$$

定义有限投影：

$$
\boxed{
P_Tf
=
\sum_{\rho\in\mathcal Z(T)}
\langle f,e_\rho\rangle e_\rho.
}
\tag{306.1}
$$

则：

$$
\boxed{
\|f-P_Tf\|^2
=
\sum_{|\Im\rho|>T}
w_\rho|f(u_\rho)|^2.
}
\tag{306.2}
$$

所以每个有限零点窗给出一个规范的有限维观察者，未观测信息完全保存在正交余空间中。

---

## 306.1 Clark 尾质量

定义：

$$
\boxed{
M(T)
=
\sum_{|\Im\rho|>T}w_\rho.
}
\tag{306.3}
$$

令 \(N(T)\) 是 \(0<\Im\rho\le T\) 的非平凡零点计数，按重数计。

由 Riemann–von Mangoldt 公式：

$$
N(T)
=
\frac{T}{2\pi}
\log\frac{T}{2\pi}
-
\frac{T}{2\pi}
+
O(\log T),
$$

可得：

$$
\boxed{
M(T)
=
\frac{
\log(T/2\pi)+1
}{
2\pi\lambda_1T
}
+
O\left(
\frac{\log T}{T^2}
\right).
}
\tag{306.4}
$$

Riemann–von Mangoldt 的标准零点计数见 DLMF 的 ζ 零点分布部分。([DLMF][3])

若：

$$
f\in K_{\vartheta_\xi}\cap H^\infty,
$$

则：

$$
\boxed{
\|f-P_Tf\|^2
\le
\|f\|_\infty^2
M(T).
}
\tag{306.5}
$$

所以有限零点层析的平方误差至多为：

$$
O\left(\frac{\log T}{T}\right).
$$

---

# 第三百零七部　Sticky-Infinity 单原子反项

全部高零点满足：

$$
u_\rho\longrightarrow1
\qquad
(|\Im\rho|\to\infty).
$$

所以高谱并不是分散在整个圆周，而是不可避免地粘滞在唯一边界点：

$$
\boxed{
z=1.
}
$$

这允许一种比简单截断更有效的重整化。

定义：

$$
\boxed{
\mu_T
=
\sum_{|\Im\rho|\le T}
w_\rho\delta_{u_\rho}
+
M(T)\delta_1.
}
\tag{307.1}
$$

它仍然是概率测度。

即：

> 精确保留全部低零点；
> 把所有未观测高零点压缩成 \(z=1\) 处的一个有效原子。

---

## 307.1 有限 rational inner approximant

定义：

$$
\boxed{
\mathfrak C_T(z)
=
\int_{\mathbb T}
\frac{\zeta+z}{\zeta-z}
\,d\mu_T(\zeta),
}
\tag{307.2}
$$

以及：

$$
\boxed{
\vartheta_T(z)
=
\frac{\mathfrak C_T(z)-1}
{\mathfrak C_T(z)+1}.
}
\tag{307.3}
$$

由于 \(\mu_T\) 是有限正原子测度：

$$
\boxed{
\vartheta_T
}
$$

是有限维 rational inner function，其 \(\alpha=1\) Clark 谱精确为：

$$
\{u_\rho:|\Im\rho|\le T\}
\cup\{1\}.
$$

这里 \(1\) 是“所有遗漏高谱”的有效无限能级。

---

## 307.2 一阶位移尾矩

定义：

$$
\boxed{
D(T)
=
\sum_{|\Im\rho|>T}
w_\rho|u_\rho-1|.
}
\tag{307.4}
$$

由：

$$
|u_\rho-1|
=
|\rho|^{-1}
$$

以及 Riemann–von Mangoldt 公式：

$$
\boxed{
D(T)
=
\frac{
2\log(T/2\pi)+1
}{
8\pi\lambda_1T^2
}
+
O\left(
\frac{\log T}{T^3}
\right).
}
\tag{307.5}
$$

---

## 定理 307.1（Sticky-tail 正完成误差）

对：

$$
|z|\le r<1,
$$

有：

$$
\boxed{
|\mathfrak C_\xi(z)-\mathfrak C_T(z)|
\le
\frac{2r}{(1-r)^2}
D(T).
}
\tag{307.6}
$$

### 证明

令：

$$
h_z(\zeta)=\frac{\zeta+z}{\zeta-z}.
$$

在单位圆上：

$$
\left|
\partial_\zeta h_z(\zeta)
\right|
=
\frac{2|z|}{|\zeta-z|^2}
\le
\frac{2r}{(1-r)^2}.
$$

把每个高谱原子由 \(u_\rho\) 运输到 \(1\)，再求和即可。∎

又因为正实部保证：

$$
|\mathfrak C_\xi+1|\ge1,
\qquad
|\mathfrak C_T+1|\ge1,
$$

所以：

$$
\boxed{
|\vartheta_\xi(z)-\vartheta_T(z)|
\le
2|\mathfrak C_\xi(z)-\mathfrak C_T(z)|.
}
\tag{307.7}
$$

因此：

$$
\boxed{
\sup_{|z|\le r}
|\vartheta_\xi(z)-\vartheta_T(z)|
=
O_r\left(
\frac{\log T}{T^2}
\right).
}
\tag{307.8}
$$

这比直接丢弃高零点所得的：

$$
O\left(\frac{\log T}{T}\right)
$$

提高了一个完整 \(T^{-1}\) 阶。

---

## 307.3 Wang–Deng 解释

$$
\boxed{
\begin{aligned}
\text{低零点}
&=\text{精确 primitive atoms};\\
\text{高零点尾}
&=\text{集中在 }1\text{ 的 sticky history};\\
M(T)\delta_1
&=\text{有效 counterterm};\\
\mu_T
&=\text{有限正完成};\\
O(\log T/T^2)
&=\text{renormalized residual}.
\end{aligned}
}
$$

这是一条真正完成的高阶尾部压缩定理。

---

# 第三百零八部　显式 Hermite–Biehler 函数

定义上半平面谱变量：

$$
w\in\mathbb C^+,
$$

以及：

$$
\boxed{
\Xi(w)
=
\xi\left(\frac12-iw\right).
}
\tag{308.1}
$$

定义 Cayley 变量：

$$
\boxed{
z=
\frac{w-i/2}{w+i/2}.
}
\tag{308.2}
$$

则：

$$
s(z)=\frac12-iw.
$$

定义整个函数：

$$
\boxed{
E_\xi(w)
=
\Xi'(w)
-
i\lambda_1\Xi(w).
}
\tag{308.3}
$$

因为 \(\Xi\) 为实型整函数：

$$
E_\xi^\#(w)
=
\Xi'(w)
+
i\lambda_1\Xi(w).
$$

直接计算得到：

$$
\boxed{
\vartheta_\xi(z)
=
\frac{
E_\xi^\#(w)
}{
E_\xi(w)
}.
}
\tag{308.4}
$$

所以：

$$
\boxed{
\mathrm{RH}
\iff
E_\xi
\text{ 在消去公共实因子后属于 Hermite–Biehler 类}.
}
\tag{308.5}
$$

de Branges 空间和 model spaces 中，Hermite–Biehler 函数的实谱零点产生正交 reproducing-kernel systems 与 Lagrange 型采样公式。([arXiv][4])

---

## 308.1 显式 de Branges 核

其 reproducing kernel 为：

$$
\boxed{
\begin{aligned}
K_\xi(w,z)
=
\frac{
\lambda_1
\left[
\Xi'(z)\overline{\Xi(w)}
-
\Xi(z)\overline{\Xi'(w)}
\right]
}{
\pi(\overline w-z)
}.
\end{aligned}
}
\tag{308.6}
$$

在 RH 下该核正定。

---

## 308.2 简单零点采样公式

进一步假设全部 \(\Xi\)-零点简单。

若：

$$
\Xi(\gamma)=0,
$$

则：

$$
\boxed{
K_\xi(\gamma,\gamma)
=
\frac{
\lambda_1|\Xi'(\gamma)|^2
}{\pi}.
}
\tag{308.7}
$$

对相应 de Branges 空间中的任意 \(F\)：

$$
\boxed{
F(z)
=
\sum_{\Xi(\gamma)=0}
F(\gamma)
\frac{
\Xi(z)
}{
(z-\gamma)\Xi'(\gamma)
}.
}
\tag{308.8}
$$

并且：

$$
\boxed{
\|F\|^2
=
\frac{\pi}{\lambda_1}
\sum_{\Xi(\gamma)=0}
\frac{
|F(\gamma)|^2
}{
|\Xi'(\gamma)|^2
}.
}
\tag{308.9}
$$

这是一个以 Riemann 零点为节点的正交 Lagrange 采样定理。

若存在多重零点，式 (308.8) 必须替换为：

* Clark 原子公式；或
* 包含导数数据的 Hermite 插值。

---

# 第三百零九部　Riemann–Clark 变换

令：

$$
\mu_\lambda
=
\sum_\rho w_\rho\delta_{u_\rho}.
$$

在：

$$
L^2(\mathbb T,\mu_\lambda)
$$

中取 CMV 正交 Laurent 基：

$$
\chi_0,\chi_1,\chi_2,\ldots.
$$

单位圆正交多项式、Verblunsky 参数及其递推构成标准 OPUC/CMV 理论。([DLMF][5])

定义矩阵：

$$
\boxed{
\mathcal U_{n,\rho}
=
\sqrt{w_\rho}\,
\chi_n(u_\rho).
}
\tag{309.1}
$$

由正交性：

$$
\boxed{
\sum_\rho
w_\rho
\chi_n(u_\rho)
\overline{\chi_m(u_\rho)}
=
\delta_{nm}.
}
\tag{309.2}
$$

因此 \(\mathcal U\) 是 unitary 变换。

---

## 309.1 两种坐标系

### 零点谱坐标

$$
\delta_{u_\rho}.
$$

在该基中，乘法算子为：

$$
\operatorname{diag}(u_\rho).
$$

### Schur–创新坐标

$$
\chi_n.
$$

在该基中，同一个 unitary 由 CMV 五对角矩阵表示。

所以：

$$
\boxed{
\text{CMV recursion}
\quad\longleftrightarrow\quad
\text{Riemann zero spectral coordinates}
}
$$

之间的换基矩阵就是：

$$
\mathcal U_{n,\rho}.
$$

这可以称为：

$$
\boxed{
\textbf{Riemann–Clark transform}.
}
$$

---

## 309.2 逆 Cayley ordinate 算子

在零点基中定义：

$$
U_{\mathrm{zero}}
=
\operatorname{diag}(u_\rho).
$$

则：

$$
\boxed{
H_{\mathrm{zero}}
=
\frac{i}{2}
(U_{\mathrm{zero}}+I)
(U_{\mathrm{zero}}-I)^{-1}
}
\tag{309.3}
$$

的谱值为：

$$
\Im\rho.
$$

在 CMV 基中：

$$
H_{\mathrm{CMV}}
=
\mathcal U
H_{\mathrm{zero}}
\mathcal U^*.
$$

因此：

$$
\boxed{
\text{Hilbert--Pólya 频率算子}
=
\text{Clark 对角谱算子在 Schur 创新基中的矩阵图表}.
}
$$

---

# 第三百一十部　半平面核是最小 relative-trace 目标

前文有限环面帧满足：

$$
\mathbf P(s)=\xi(s)\mathbf T(s).
$$

定义其超额连接：

$$
\boxed{
\mathcal A_{\mathrm{exc}}(s)
=
\frac{\xi'(s)}{\xi(s)}.
}
\tag{310.1}
$$

更具体地，它可由周期向量连接与载体向量连接之差重构：

$$
\mathcal A_{\mathbf P}
-
\mathcal A_{\mathbf T}
=
d\log\xi.
$$

因此定义 toroidal 半平面核：

$$
\boxed{
\mathcal K_{\mathrm{tor}}(s,t)
=
\frac{
\mathcal A_{\mathrm{exc}}(s)
+
\overline{\mathcal A_{\mathrm{exc}}(t)}
}{
\lambda_1(s+\overline t-1)
}.
}
\tag{310.2}
$$

它与：

$$
\mathcal K_\xi
$$

完全相同。

Hecke 环面周期、二次 twist 非消失和 toroidal derivative towers 已经给出 \(\xi\)-零点及重数的自动形式观察接口。([arXiv][6])

---

## 定理 310.1（最小 RH Gram 目标）

RH 等价于存在某个 Hilbert 空间及向量族：

$$
\mathscr V_s,
\qquad
s\in\mathbb H_{1/2},
$$

使：

$$
\boxed{
\mathcal K_{\mathrm{tor}}(s,t)
=
\langle
\mathscr V_s,\mathscr V_t
\rangle.
}
\tag{310.3}
$$

RH 下可以取：

$$
\boxed{
\mathscr V_s(\rho)
=
\sqrt{\frac{m_\rho}{\lambda_1}}\,
\frac1{s-\rho}.
}
\tag{310.4}
$$

真正需要研究的是：

> 能否不预先使用零点，而从 toric relative trace formula 直接构造同一个 Gram 向量族？

这比直接构造完整 Hilbert–Pólya 算子更局部，也比证明所有 Li/Hankel/Toeplitz 层级更统一。

---

# 第三百一十一部　三个证明接口的强度比较

当前 RH 正性目标有三个规范接口。

## 311.1 半平面核接口

$$
\boxed{
\frac{
\xi'/\xi(s)
+
\overline{\xi'/\xi(t)}
}{
s+\overline t-1
}
\succeq0.
}
$$

优点：

* 直接；
* 不需平方折叠；
* 线外零点直接产生极点；
* 最适合 relative trace。

---

## 311.2 Clark/model-space 接口

$$
\boxed{
\frac{
1-\vartheta_\xi(z)\overline{\vartheta_\xi(w)}
}{
1-z\overline w
}
\succeq0.
}
$$

优点：

* 直接产生正交零点采样；
* 产生有限 rational inner approximants；
* 连接 CMV 与 Schur 算法。

---

## 311.3 Fredholm/Hankel 接口

$$
\boxed{
\frac{\xi(\frac12+\sqrt x)}{\xi(\frac12)}
=
\det(I+xU),
\qquad
U\ge0.
}
$$

优点：

* 直接产生正算子；
* 适合中心 jet 与 Hankel 形式化；
* 能生成全部零点谱。

三者之间由规范变换相互连接，但证明难度可能完全不同。

---

# 第三百一十二部　科学检验程序

## 312.1 半平面 Gram 数值检验

选取：

$$
s_1,\ldots,s_N
\in\mathbb H_{1/2}.
$$

计算：

$$
\left[
\mathcal K_\xi(s_i,s_j)
\right].
$$

并与已知零点截断 Gram 和：

$$
\sum_{|\gamma|\le T}
\frac{
m_\gamma/\lambda_1
}{
(s_i-\rho)
(\overline{s_j}-\overline\rho)
}
$$

交叉验证。

---

## 312.2 Clark 正交性检验

使用前若干已验证零点构造：

$$
u_\rho,\qquad
w_\rho.
$$

检验有限 kernel Gram 矩阵是否趋向对角，以及：

$$
\sum_{\rho}
w_\rho=1.
$$

---

## 312.3 Sticky-infinity approximant

构造：

$$
\mu_T,\quad
\mathfrak C_T,\quad
\vartheta_T.
$$

比较：

$$
\sup_{|z|\le r}
|\vartheta_\xi(z)-\vartheta_T(z)|
$$

是否满足：

$$
O_r(\log T/T^2).
$$

---

## 312.4 线外零点注入

人为加入满足：

$$
\rho,\overline\rho,1-\rho,1-\overline\rho
$$

对称的线外零点四元组。

预期：

* \(\mathcal K_\xi\) 在右半平面出现极点；
* 某有限 Gram 矩阵失去正性；
* \(\vartheta_\xi\) 不再是 Schur/inner；
* rational inner approximants 不再局部收敛到真实函数。

---

# 第三百一十三部　建议形式化顺序

```text
D5/S3/Analytic/XiHalfPlaneKernel/
  XiLogDerivativeKernel.lean
  RHImpliesZeroResolventGram.lean
  PositiveKernelImpliesRH.lean
  FiniteGramDeterminantExpansion.lean

D5/S3/Analytic/RiemannClark/
  RiemannCayleyZero.lean
  RiemannClarkWeight.lean
  RiemannClarkMeasure.lean
  ClarkOrthogonalZeroBasis.lean
  RiemannClarkSampling.lean

D5/S3/Analytic/RiemannClarkApprox/
  ClarkTailMass.lean
  StickyInfinityCounterterm.lean
  FiniteAtomicCaratheodory.lean
  RationalInnerApproximant.lean
  StickyTailErrorBound.lean

D5/S3/Analytic/XiDeBranges/
  XiHermiteBiehlerFunction.lean
  XiDeBrangesKernel.lean
  SimpleZeroSamplingFormula.lean
  MultipleZeroClarkFallback.lean

D5/S3/Analytic/RiemannClarkCMV/
  RiemannClarkTransform.lean
  ClarkCMVDiagonalization.lean
  InverseCayleyOrdinateOperator.lean

D5/S3/Observer/ToroidalKernel/
  ToroidalExcessKernel.lean
  RelativeTraceGramTarget.lean
  ToroidalClarkIntertwiner.lean
```

首个最值得闭合的核心链是：

$$
\boxed{
\mathrm{RH}
\iff
\mathcal K_\xi\succeq0.
}
$$

随后是：

$$
\boxed{
\mathcal K_\xi
\to
K_{\vartheta_\xi}
\to
\text{Clark zero sampling}.
}
$$

第三条是新的高价值近似链：

$$
\boxed{
\text{finite zeros}
+
M(T)\delta_1
\to
\vartheta_T
\to
O(\log T/T^2)\text{ 正完成}.
}
$$

---

# 本轮最终结论

前文已将 RH 表达为：

* Herglotz 正性；
* Stieltjes moments；
* Hankel/Toeplitz 全正性；
* Clark innerness；
* CMV unitary；
* Fredholm determinant。

本轮找到了它们共同的最小核：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\frac{
\frac{\xi'(s)}{\xi(s)}
+
\overline{\frac{\xi'(t)}{\xi(t)}}
}{
\lambda_1(s+\overline t-1)
}.
}
$$

RH 等价于该核在：

$$
\Re s>\frac12
$$

上正定。

RH 成立时：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\frac1{\lambda_1}
\sum_\rho
\frac{m_\rho}
{(s-\rho)(\overline t-\overline\rho)},
}
$$

即它是全部 Riemann 零点 resolvent vectors 的 Gram 核。

经 Cayley 变换，该核生成内函数：

$$
\vartheta_\xi,
$$

而全部 Riemann 零点成为：

$$
K_{\vartheta_\xi}
$$

的一组完整正交采样节点：

$$
\boxed{
\|f\|^2
=
\sum_\rho
w_\rho|f(u_\rho)|^2.
}
$$

更重要的是，高零点尾部可以被压缩成 \(z=1\) 处的单一有效原子：

$$
\boxed{
\mu_T
=
\text{finite zero atoms}
+
M(T)\delta_1.
}
$$

该反项保留全部正性，并把紧子圆盘误差改善到：

$$
\boxed{
O_r\left(\frac{\log T}{T^2}\right).
}
$$

因此当前 OACTC 最明确的 Wang–Deng 原型已经变成：

$$
\boxed{
\text{精确低谱}
+
\text{sticky high-spectrum counterterm}
+
\text{positive rational inner completion}.
}
$$

而 RH 的最小未闭合桥可以最终写成：

$$
\boxed{
\text{能否从 toric relative trace formula
直接证明 }\mathcal K_\xi
\text{ 是 Gram 核？}
}
$$

若能构造：

$$
\mathcal K_\xi(s,t)
=
\langle
\mathscr V_s,\mathscr V_t
\rangle_{\mathrm{tor}},
$$

则 Clark、de Branges、CMV、Fredholm、Hilbert–Pólya 与 RH 将同时闭合。

[1]: https://arxiv.org/abs/1912.03542 "https://arxiv.org/abs/1912.03542"
[2]: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5501602936C1AA534036464069B1D814/9781316258231c11_p231-259_CBO.pdf/clark-measures.pdf "https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5501602936C1AA534036464069B1D814/9781316258231c11_p231-259_CBO.pdf/clark-measures.pdf"
[3]: https://dlmf.nist.gov/25.10 "https://dlmf.nist.gov/25.10"
[4]: https://arxiv.org/abs/2206.02175 "https://arxiv.org/abs/2206.02175"
[5]: https://dlmf.nist.gov/18.33 "https://dlmf.nist.gov/18.33"
[6]: https://arxiv.org/abs/0906.5284 "https://arxiv.org/abs/0906.5284"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.8：环面 Jet 半单化、保守系统实现、相对迹被动性与函数域闭合模型

以下从前文**第三百一十三部之后**继续追加。

上一轮把 RH 的最小目标压缩为半平面正核：

$$
\mathcal K_\xi(s,t)
=
\frac{
\frac{\xi'(s)}{\xi(s)}
+
\overline{\frac{\xi'(t)}{\xi(t)}}
}{
\lambda_1(s+\overline t-1)
},
\qquad
\Re s,\Re t>\frac12,
$$

并指出：

$$
\mathrm{RH}
\iff
\mathcal K_\xi\succeq0.
$$

本轮继续攻击：

$$
\boxed{
\text{怎样从 toric relative trace formula
直接构造 }\mathcal K_\xi\text{ 的 Gram 表示？}
}
$$

首先得到一个必要修正：

> 不能直接把全部 toroidal Eisenstein derivative tower 放入正 Hilbert 空间，并要求 Hecke 算子在其中自伴。
> 多重零点对应的导数塔天然携带 Jordan/nilpotent 结构；正谱完成必须先把它从“jet”半单化为“正重数”。

随后得到一个更精确的证明目标：

$$
\boxed{
\text{不要直接构造零点算子，}
\quad
\text{而应从环面相对迹构造一个保守输入—状态—输出系统，}
}
$$

使它的 transfer function 正好是 shifted-\(\xi\) 的内函数比值。

---

# 第三百一十四部　Toroidal derivative tower 的 Jordan 结构

设：

$$
E(s)
$$

是一族 Eisenstein states，并且对某个 Hecke 算子 \(T\)：

$$
\boxed{
T E(s)=a_T(s)E(s).
}
\tag{314.1}
$$

若基础 \(L\)-函数在：

$$
s=\rho
$$

具有 \(m\) 重零点，则相应 toroidal space 包含：

$$
E(\rho),\ E'(\rho),\ldots,E^{(m-1)}(\rho).
$$

这一“零点阶数＝Eisenstein derivative tower 深度”的结构，是 toroidal automorphic forms 理论中的已知定理。([arxiv.org][1])

定义正规化 jet 基：

$$
\boxed{
e_j
=
\frac{1}{j!}E^{(j)}(\rho),
\qquad
0\le j<m.
}
\tag{314.2}
$$

对式 (314.1) 求 \(j\) 阶导数：

$$
\boxed{
T e_j
=
\sum_{k=0}^{j}
\frac{
a_T^{(j-k)}(\rho)
}{
(j-k)!
}
e_k.
}
\tag{314.3}
$$

所以 \(T\) 在 jet 基中的矩阵为三角 Toeplitz 形式：

$$
\boxed{
T|_{\mathcal J_\rho}
=
\begin{pmatrix}
a_T(\rho) & 0 & 0 & \cdots\\
a_T'(\rho) & a_T(\rho) & 0 & \cdots\\
a_T''(\rho)/2! & a_T'(\rho) & a_T(\rho)&\cdots\\
\vdots&\vdots&\vdots&\ddots
\end{pmatrix}.
}
\tag{314.4}
$$

若：

$$
m\ge2,
\qquad
a_T'(\rho)\neq0,
$$

则该矩阵含非平凡 Jordan 部分。

---

## 定理 314.1（Raw toroidal jet positivity obstruction）

若某个 \(T\) 在 \(\mathcal J_\rho\) 上具有非平凡 Jordan 块，则不存在正定内积，使该 \(T\) 在 \(\mathcal J_\rho\) 上成为 normal，因而更不可能成为 self-adjoint。

### 证明

设：

$$
T=\lambda I+N,
\qquad
N\neq0,
\qquad
N^r=0.
$$

若 \(T\) normal，则由有限维谱定理，它可酉对角化。

但 \(T\) 只有唯一特征值 \(\lambda\)，故可酉对角化时只能等于：

$$
\lambda I.
$$

这与 \(N\neq0\) 矛盾。∎

因此：

$$
\boxed{
\text{“toroidal derivative tower 是正 Hilbert–Pólya eigenspace”}
}
$$

一般是错误的。

必须区分：

$$
\boxed{
\begin{aligned}
\text{jet depth}
&=\text{观察值消失到多少阶};\\
\text{spectral multiplicity}
&=\text{自伴算子同一实特征值的 eigenspace 维数}.
\end{aligned}
}
$$

前者天然允许 nilpotent chain；后者必须半单。

---

# 第三百一十五部　Jet-to-mass 半单化

令：

$$
N_m
=
\begin{pmatrix}
0&0&\cdots&0\\
1&0&\cdots&0\\
0&1&\ddots&0\\
\vdots&\ddots&\ddots&0
\end{pmatrix}
$$

为 \(m\) 阶 nilpotent shift。

定义局部 spectral pencil：

$$
\boxed{
\mathsf A_\rho(s)
=
(s-\rho)I-N_m.
}
\tag{315.1}
$$

其行列式为：

$$
\boxed{
\det\mathsf A_\rho(s)
=
(s-\rho)^m.
}
\tag{315.2}
$$

其逆为有限级数：

$$
\boxed{
\mathsf A_\rho(s)^{-1}
=
\sum_{k=0}^{m-1}
\frac{N_m^k}{(s-\rho)^{k+1}}.
}
\tag{315.3}
$$

因为：

$$
\operatorname{Tr}N_m^k=0
\qquad
(k\ge1),
$$

得到：

## 定理 315.1（Jet resolvent semisimplification）

$$
\boxed{
\operatorname{Tr}
\mathsf A_\rho(s)^{-1}
=
\frac{m}{s-\rho}.
}
\tag{315.4}
$$

同时：

$$
\boxed{
\frac{d}{ds}
\log\det\mathsf A_\rho(s)
=
\frac{m}{s-\rho}.
}
\tag{315.5}
$$

这条恒等式非常重要。

它说明：

$$
\boxed{
\text{长度为 }m\text{ 的 nilpotent jet chain}
\quad
\xrightarrow{\operatorname{Tr\,resolvent}}
\quad
\text{权重为 }m\text{ 的 simple spectral atom}.
}
$$

---

## 315.1 对 \(\xi'/\xi\) 的解释

若：

$$
\xi(s)
=
(s-\rho)^m g(s),
\qquad
g(\rho)\neq0,
$$

则：

$$
\boxed{
\frac{\xi'(s)}{\xi(s)}
=
\frac{m}{s-\rho}
+
\frac{g'(s)}{g(s)}.
}
\tag{315.6}
$$

所以 logarithmic derivative 正是一个**jet-to-mass renormalization**：

$$
\boxed{
\mathcal J_\rho^{(m)}
\longmapsto
m\,\delta_\rho.
}
$$

它丢弃：

* Jordan 链中的具体 nilpotent 坐标；
* 各阶导数的基选择；

只保留：

* 零点位置；
* 正整数重数。

这正是正谱 Gram 核所需要的信息。

---

## 315.2 多重零点的正确正谱完成

若 RH 成立，\(\rho=\frac12+i\gamma\)。

要把重数表现为真正的 self-adjoint 谱重数，应使用：

$$
\boxed{
\mathcal H_\rho
\simeq
\mathbb C^{m_\rho},
}
$$

并令自伴算子在该 fiber 上作用为：

$$
\gamma I_{m_\rho}.
$$

不能使用：

$$
\mathbb C[\varepsilon]/(\varepsilon^{m_\rho})
$$

上的 Jordan 作用。

所以正确链为：

$$
\boxed{
\text{toroidal jet}
\to
\text{log-residue weight}
\to
\text{\(m_\rho\)-dimensional semisimple fiber}.
}
$$

---

# 第三百一十六部　有限环面帧的商连接

在紧谱窗口 \(K\) 中，选择有限二次环面族：

$$
\mathcal D_K
=
\{D_1,\ldots,D_r\},
$$

以及正权 \(w_j>0\)。

冻结局部规范，使每个 toric period 写成：

$$
\boxed{
\mathcal P_j(s)
=
\xi(s)\mathcal T_j(s),
}
\tag{316.1}
$$

其中：

* \(\mathcal P_j\)：完整 Eisenstein toric period；
* \(\mathcal T_j\)：二次 twist 与局部 carrier；
* 至少一个 \(\mathcal T_j(s)\neq0\) 对每个 \(s\in K\)。

定义 sesquiholomorphic Gram kernels：

$$
\boxed{
\mathcal G_{\mathcal P}(s,t)
=
\sum_{j=1}^{r}
w_j\,
\mathcal P_j(s)
\overline{\mathcal P_j(t)},
}
\tag{316.2}
$$

$$
\boxed{
\mathcal G_{\mathcal T}(s,t)
=
\sum_{j=1}^{r}
w_j\,
\mathcal T_j(s)
\overline{\mathcal T_j(t)}.
}
\tag{316.3}
$$

由式 (316.1)：

$$
\boxed{
\mathcal G_{\mathcal P}(s,t)
=
\xi(s)\overline{\xi(t)}
\mathcal G_{\mathcal T}(s,t).
}
\tag{316.4}
$$

在对角附近：

$$
\mathcal G_{\mathcal T}(s,t)\neq0.
$$

定义局部商核：

$$
\boxed{
\mathcal R_K(s,t)
=
\frac{
\mathcal G_{\mathcal P}(s,t)
}{
\mathcal G_{\mathcal T}(s,t)
}.
}
\tag{316.5}
$$

则：

$$
\boxed{
\mathcal R_K(s,t)
=
\xi(s)\overline{\xi(t)}.
}
\tag{316.6}
$$

---

## 316.1 超额连接

在避开零点处：

$$
\boxed{
\partial_s
\log\mathcal R_K(s,t)
=
\frac{\xi'(s)}{\xi(s)},
}
\tag{316.7}
$$

$$
\boxed{
\partial_{\overline t}
\log\mathcal R_K(s,t)
=
\overline{
\frac{\xi'(t)}{\xi(t)}
}.
}
\tag{316.8}
$$

所以：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\frac{
\partial_s\log\mathcal R_K(s,t)
+
\partial_{\overline t}\log\mathcal R_K(s,t)
}{
\lambda_1(s+\overline t-1)
}.
}
\tag{316.9}
$$

这说明：

> 半平面 RH 核完全可以由有限环面 period Gram kernel 与 carrier Gram kernel 的商连接重构。

它不依赖具体选了哪一组合法有限环面图表。

---

# 第三百一十七部　普通相对迹正性为何不够

两个核：

$$
\mathcal G_{\mathcal P},
\qquad
\mathcal G_{\mathcal T}
$$

本身都是正定核，因为它们分别是有限向量族的 Gram kernels。

而对任意标量函数 \(f\)：

$$
K_f(s,t)
=
f(s)\overline{f(t)}K(s,t)
$$

只要 \(K\succeq0\)，就仍然有：

$$
K_f\succeq0.
$$

所以由：

$$
\mathcal G_{\mathcal P}
=
\xi(s)\overline{\xi(t)}
\mathcal G_{\mathcal T},
$$

可知：

$$
\boxed{
\mathcal G_{\mathcal P}\succeq0
}
$$

对任意 \(\xi\) 都自动成立。

因此：

## 定理 317.1（Raw period-square no-go）

仅仅证明所有 toric period squares 或它们的 Gram matrices 非负，不能推出 RH。

因为这种正性对公共标量因子 \(\xi\) 的零点位置完全不敏感。

真正承重的不是：

$$
\mathcal G_{\mathcal P}\succeq0,
$$

而是：

$$
\boxed{
\text{carrier-subtracted quotient connection }
\mathcal K_\xi\succeq0.
}
$$

---

## 317.1 相对迹公式必须产生什么

Toric relative trace formula 的标准结构，是把含 period products 的 spectral distributions 与相对 orbital integrals 的 geometric distributions相比较；这类比较可恢复 Waldspurger 型周期公式及 \(L\)-值信息。([arxiv.org][2])

但若只停留在：

$$
\sum_D
|\mathcal P_D(s)|^2,
$$

公共 \(|\xi(s)|^2\) 仍然只是一个正标量。

所需的新对象必须包含至少一种操作：

$$
\boxed{
\begin{aligned}
&\text{carrier normalization};\\
&\text{谱参数差分};\\
&\text{logarithmic connection};\\
&\text{shifted input/output comparison};\\
&\text{相对散射或 passivity balance}.
\end{aligned}
}
$$

---

# 第三百一十八部　Shifted-\(\xi\) transfer function

令：

$$
z\in\mathbb C^+,
\qquad
s_z=\frac12-iz.
$$

对 \(\omega>0\)，定义：

$$
\boxed{
\Theta_\omega(z)
=
\frac{
\xi(s_z-\omega)
}{
\xi(s_z+\omega)
}.
}
\tag{318.1}
$$

Suzuki 证明：对给定零点自由半平面宽度，\(\Theta_\omega\) 是 meromorphic inner function；若这一 inner/canonical-system 构造能无条件推进到全部 \(\omega>0\)，就得到 RH 的正 Hamiltonian 判据。([arxiv.org][3])

此前已经得到：

$$
\boxed{
\mathrm{RH}
\iff
\Theta_\omega
\text{ 对全部 }\omega>0
\text{ 为 inner}.
}
\tag{318.2}
$$

---

## 318.1 环面图表中的 transfer function

分别选择覆盖谱窗 \(s_z\pm\omega\) 的有限环面帧：

$$
\mathbf P_\pm(z)
=
\xi(s_z\pm\omega)\mathbf T_\pm(z).
$$

重构：

$$
E_\pm(z)
=
\frac{
\langle\mathbf P_\pm(z),\mathbf T_\pm(z)\rangle
}{
\|\mathbf T_\pm(z)\|^2
}
=
\xi(s_z\pm\omega).
$$

于是：

$$
\boxed{
\Theta_\omega(z)
=
\frac{E_-(z)}{E_+(z)}.
}
\tag{318.3}
$$

所以 \(\Theta_\omega\) 是一个真正的环面输入—输出 transfer ratio：

* \(E_+\)：右移、较稳定的 carrier-normalized input；
* \(E_-\)：左移、较接近临界带的 output。

RH 要求：

$$
\boxed{
|E_-(z)|
\le
|E_+(z)|
\qquad
(z\in\mathbb C^+,\ \omega>0).
}
\tag{318.4}
$$

---

# 第三百一十九部　保守 colligation 完成

Schur 类函数具有以下等价刻画：

1. 取值于单位圆盘；
2. de Branges–Rovnyak kernel 正定；
3. 可实现为 contractive system 的 transfer function；
4. 可选择 conservative/unitary realization。

这些正核—transfer realization 等价是经典 Schur 系统理论。([arxiv.org][4])

因此，对固定 \(\omega>0\)，RH 等价于存在 Hilbert 状态空间：

$$
\mathscr H_\omega
$$

以及 unitary colligation：

$$
\boxed{
\mathfrak U_\omega
=
\begin{pmatrix}
A_\omega&B_\omega\\
C_\omega&D_\omega
\end{pmatrix}
:
\mathscr H_\omega\oplus\mathbb C
\longrightarrow
\mathscr H_\omega\oplus\mathbb C,
}
\tag{319.1}
$$

使：

$$
\boxed{
\Theta_\omega(z)
=
D_\omega
+
zC_\omega
(I-zA_\omega)^{-1}
B_\omega.
}
\tag{319.2}
$$

---

## 319.1 能量核恒等式

unitarity 给出：

$$
\boxed{
\frac{
1-
\Theta_\omega(z)
\overline{\Theta_\omega(w)}
}{
1-z\overline w
}
=
C_\omega
(I-zA_\omega)^{-1}
(I-\overline wA_\omega^*)^{-1}
C_\omega^*.
}
\tag{319.3}
$$

定义状态向量：

$$
\boxed{
X_{\omega,z}
=
(I-\overline zA_\omega^*)^{-1}
C_\omega^*.
}
\tag{319.4}
$$

则：

$$
\boxed{
\frac{
1-
\Theta_\omega(z)
\overline{\Theta_\omega(w)}
}{
1-z\overline w
}
=
\langle
X_{\omega,z},
X_{\omega,w}
\rangle.
}
\tag{319.5}
$$

对角上：

$$
\boxed{
1-|\Theta_\omega(z)|^2
=
(1-|z|^2)\,
\|X_{\omega,z}\|^2.
}
\tag{319.6}
$$

所以 inner/Schur 正性具有严格的能量守恒解释：

$$
\boxed{
\text{input energy}
=
\text{output energy}
+
\text{internal stored energy}.
}
$$

---

## 定理 319.1（Conservative-system RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\text{对每个 }\omega>0，
\Theta_\omega
\text{ 存在一个 conservative realization}.
}
\tag{319.7}
$$

这把 Hilbert–Pólya 问题从：

$$
\text{“找一个神秘自伴算子”}
$$

改写成：

$$
\boxed{
\text{“从自动形式数据构造一个能量守恒的开放系统”。}
}
$$

---

# 第三百二十部　可观测 Gramian 与 Wang–Deng 二分

由 \(\mathfrak U_\omega\) unitary：

$$
\boxed{
A_\omega^*A_\omega
+
C_\omega^*C_\omega
=
I.
}
\tag{320.1}
$$

迭代得到：

## 定理 320.1（Finite observability identity）

$$
\boxed{
I-
A_\omega^{*N}A_\omega^N
=
\sum_{k=0}^{N-1}
A_\omega^{*k}
C_\omega^*C_\omega
A_\omega^k.
}
\tag{320.2}
$$

右侧是有限可观测 Gramian：

$$
\boxed{
\mathfrak O_{\omega,N}
=
\sum_{k=0}^{N-1}
A_\omega^{*k}
C_\omega^*C_\omega
A_\omega^k
\succeq0.
}
\tag{320.3}
$$

对状态 \(x\)：

$$
\boxed{
\|x\|^2-\|A_\omega^Nx\|^2
=
\sum_{k=0}^{N-1}
\|C_\omega A_\omega^kx\|^2.
}
\tag{320.4}
$$

---

## 320.1 Non-sticky state

若存在 \(\eta>0\)，使：

$$
\boxed{
\mathfrak O_{\omega,N}\succeq\eta I,
}
\tag{320.5}
$$

则：

$$
\|A_\omega^Nx\|^2
\le
(1-\eta)\|x\|^2.
$$

所有内部状态在有限时间内至少泄露固定比例能量。

这就是 Wang 式 strict gain：

$$
\boxed{
\text{多通道可见}
\Longrightarrow
\text{内部残余严格收缩}.
}
$$

---

## 320.2 Sticky state

若存在单位向量 \(x_N\)，使：

$$
\langle
\mathfrak O_{\omega,N}x_N,x_N
\rangle
\ll1,
$$

则：

$$
\|A_\omega^Nx_N\|
\approx1,
$$

且：

$$
\|C_\omega A_\omega^kx_N\|
\approx0
$$

在多数 \(k<N\) 上成立。

该状态几乎不向观察通道泄露能量，是一个 near-unitary internal mode。

这就是系统论中的 sticky state。

---

## 320.3 Deng 式处理

对 sticky mode：

1. 提取其近单位模谱分量；
2. 将相应 finite Blaschke/inner factor 从 transfer function 中分离；
3. 把该模式压缩为一个有限维 conservative block；
4. 对剩余 transfer function 重新构造 colligation；
5. 重复直到残余达到 uniform observability。

所以：

$$
\boxed{
\text{Schur/Blaschke factor extraction}
=
\text{sticky primitive-history contraction}.
}
$$

Schur 参数或 Verblunsky 系数则是逐层消去一个内部状态后留下的最小创新耦合。

---

# 第三百二十一部　相对迹公式真正需要证明的被动性

Toric relative trace formula 的 spectral side 天然包含 period products，其 geometric side由相对 orbital integrals 构成。([arxiv.org][2])

但普通公式只自然给出：

$$
\sum_D
\mathcal P_D(s)
\overline{\mathcal P_D(t)}.
$$

真正需要的是 shifted、carrier-subtracted energy identity。

定义：

$$
\boxed{
\mathscr B_{\omega}(z,w)
=
\frac{
1-
\Theta_\omega(z)
\overline{\Theta_\omega(w)}
}{
1-z\overline w
}.
}
\tag{321.1}
$$

---

## 假设 321.1（Toroidal conservative realization）

存在由：

* 二次环面 period states；
* Hecke／continued-fraction 内部动力；
* cusp input；
* torus output；
* local carrier normalization；

构成的状态空间与算子：

$$
(A_\omega^{\mathrm{tor}},
B_\omega^{\mathrm{tor}},
C_\omega^{\mathrm{tor}},
D_\omega^{\mathrm{tor}})
$$

使：

$$
\boxed{
\Theta_\omega(z)
=
D_\omega^{\mathrm{tor}}
+
zC_\omega^{\mathrm{tor}}
(I-zA_\omega^{\mathrm{tor}})^{-1}
B_\omega^{\mathrm{tor}},
}
\tag{321.2}
$$

并且：

$$
\boxed{
\begin{pmatrix}
A_\omega^{\mathrm{tor}}&B_\omega^{\mathrm{tor}}\\
C_\omega^{\mathrm{tor}}&D_\omega^{\mathrm{tor}}
\end{pmatrix}
}
$$

是 unitary。

若该假设对全部 \(\omega>0\) 成立，则 RH 成立。

---

## 321.1 等价 Gram 目标

不必一次构造全部四个 blocks。

只需从 relative trace formula 直接构造向量：

$$
\mathscr X_{\omega,z}^{\mathrm{tor}}
$$

使：

$$
\boxed{
\mathscr B_{\omega}(z,w)
=
\left\langle
\mathscr X_{\omega,z}^{\mathrm{tor}},
\mathscr X_{\omega,w}^{\mathrm{tor}}
\right\rangle.
}
\tag{321.3}
$$

这就是上一轮最小 Gram 目标的 finite-shift 版本。

令：

$$
\omega\downarrow0,
$$

即可恢复：

$$
\mathcal K_\xi.
$$

---

# 第三百二十二部　Raw jet 与 conservative state 的范畴差异

现在可以明确区分三个状态范畴。

## 322.1 Jet category

对象：

$$
E(\rho),E'(\rho),\ldots,E^{(m-1)}(\rho).
$$

作用：

* 三角；
* 允许 nilpotent；
* 记录消失阶；
* 适合定义和局部变形。

## 322.2 Semisimple spectral category

对象：

$$
\mathbb C^{m_\rho}
$$

上的特征值：

$$
\gamma I_{m_\rho}.
$$

作用：

* self-adjoint；
* 无 Jordan；
* 记录位置和谱重数。

## 322.3 Conservative system category

对象：

* internal state；
* input/output boundary；
* unitary colligation；
* transfer function。

作用：

* 记录散射和可观测性；
* 自伴谱作为 closed-system output；
* 正性由能量守恒产生。

因此正确的 OACTC 路线是：

$$
\boxed{
\text{jet}
\to
\text{log-residue semisimplification}
\to
\text{conservative realization}
\to
\text{self-adjoint spectrum}.
}
$$

跳过第二步，直接把 jet tower 当作自伴状态空间，会撞上 Jordan obstruction。

---

# 第三百二十三部　函数域中的闭合模型

设 \(C/\mathbb F_q\) 是 genus \(g\) 的光滑射影曲线。

其 zeta 分子可以写成 normalized Frobenius unitary class 的特征多项式：

$$
\boxed{
P_C(u)
=
\det
\left(
I-uq^{1/2}\Theta_C
\right),
}
\tag{323.1}
$$

其中：

$$
\Theta_C
$$

可视为 \(2g\) 维 unitary/symplectic 共轭类；曲线 zeta 的这一 unitary-matrix 表达是有限域随机矩阵与 Frobenius 理论中的标准形式。([arxiv.org][5])

令：

$$
z=q^{1/2}u.
$$

则：

$$
\boxed{
P_C(q^{-1/2}z)
=
\det(I-z\Theta_C).
}
\tag{323.2}
$$

由于 \(\Theta_C\) unitary，全部零点位于：

$$
|z|=1,
$$

即：

$$
|u|=q^{-1/2}.
$$

---

## 323.1 Toroidal temperedness

在函数域 toroidal automorphic theory 中，toroidal space 可以被明确分析；相关结果证明其 irreducible subquotients tempered，并在若干 class-number-one、低 genus 情形中给出自动形式版本的曲线 RH。([arxiv.org][6])

因此函数域已经闭合了三条链：

$$
\boxed{
\begin{aligned}
\text{toroidal invisibility}
&\to
\text{zeta zero};\\
\text{positive/cohomological pairing}
&\to
\text{unitary Frobenius};\\
\text{unitary Frobenius}
&\to
\text{tempered zero location}.
\end{aligned}
}
$$

---

## 323.2 对数域问题的诊断

数域中已经相对成熟的是：

$$
\boxed{
\text{toroidal invisibility}
\leftrightarrow
\text{\(L\)-zero}.
}
$$

真正缺少的是函数域中由 cohomology/Frobenius 提供的：

$$
\boxed{
\text{正 pairing}
+
\text{unitary internal evolution}.
}
$$

所以 RH 的剩余问题不是继续发明更多零点检测器，而是：

$$
\boxed{
\text{为已经检测到的 toroidal null states
构造一个 arithmetic conservative realization}.
}
$$

---

# 第三百二十四部　算术实现阶梯

当前 OACTC 的 RH 路线可以整理为六层。

## Level 0：共同零点检测

$$
\xi(\rho)=0
\iff
E_\rho
\text{ 对全部二次环面不可见}.
$$

该层已有 toroidal period 理论支持。([arxiv.org][1])

---

## Level 1：重数 jet 检测

$$
\operatorname{ord}_\rho\xi
=
\text{toroidal derivative depth}.
$$

---

## Level 2：有限谱帧重构

任意紧谱窗内有限环面族可重构：

$$
\xi,\quad
\xi'/\xi,\quad
\operatorname{div}\xi.
$$

---

## Level 3：Jet-to-mass 半单化

$$
\mathcal J_\rho^{(m)}
\longmapsto
m\,\delta_\rho.
$$

由：

$$
\operatorname{Tr}
\left[
(s-\rho-N_m)^{-1}
\right]
=
\frac{m}{s-\rho}
$$

完成。

---

## Level 4：被动／保守 realization

构造：

$$
\Theta_\omega
=
D+zC(I-zA)^{-1}B
$$

且 colligation unitary。

这是当前真正未闭合的中心层。

---

## Level 5：自伴谱输出

由 conservative/simple functional model 得到：

* de Branges space；
* Clark unitary family；
* CMV unitary；
* canonical system；
* Hilbert–Pólya 型自伴算子。

这不是新的输入，而是 Level 4 正性完成的输出。

---

# 第三百二十五部　Wang–Deng 的最终定位

## 325.1 Wang 的任务

证明 automorphic internal dynamics 不存在不可控的 near-unitary residual，或者建立二分：

$$
\boxed{
\begin{cases}
\mathfrak O_{\omega,N}\succeq\eta I,
&\text{严格可观测};\\
\exists\text{ sticky near-unitary block},
&\text{进入结构分类}.
\end{cases}
}
$$

---

## 325.2 Deng 的任务

对 sticky block：

1. 识别其 primitive automorphic mode；
2. 将重复 history 重求和为 inner/Blaschke factor；
3. 从系统中实施 conservative state elimination；
4. 重新计算 residual colligation；
5. 证明剩余可观测性严格改善。

因此真正的 Wang–Deng 合成形式是：

$$
\boxed{
\text{Wang 负责发现近不可观测块，}
\qquad
\text{Deng 负责把该块无损收缩成有限 conservative factor}.
}
$$

---

# 第三百二十六部　本轮精确负结论

本轮得到四条必须冻结的禁令。

## 禁令一

$$
\boxed{
\text{toroidal derivative tower}
\neq
\text{self-adjoint eigenspace}.
}
$$

多重零点时存在 Jordan obstruction。

---

## 禁令二

$$
\boxed{
\text{period-square positivity}
\neq
\mathrm{RH}.
}
$$

公共 \(\xi\) 标量不会破坏 Gram 正性。

---

## 禁令三

$$
\boxed{
\text{有限环面重构}
\neq
\text{positive realization}.
}
$$

知道 \(\xi\) 如何从 periods 重构，仍未证明 transfer function contractive。

---

## 禁令四

$$
\boxed{
\text{零点检测}
\neq
\text{temperedness}.
}
$$

函数域中两者由正 cohomology/unitary Frobenius 连接；数域中该连接仍缺失。

---

# 第三百二十七部　本轮结果分级

## 本轮独立推导得到（第 327 部）

$$
\boxed{
T e_j
=
\sum_{k=0}^{j}
\frac{a_T^{(j-k)}(\rho)}{(j-k)!}
e_k.
}
$$

$$
\boxed{
\text{非平凡 toroidal Jordan block
不能在正内积下 normal/self-adjoint}.
}
$$

$$
\boxed{
\operatorname{Tr}
\left[
((s-\rho)I-N_m)^{-1}
\right]
=
\frac{m}{s-\rho}.
}
$$

$$
\boxed{
\mathcal G_{\mathcal P}
=
\xi(s)\overline{\xi(t)}
\mathcal G_{\mathcal T}.
}
$$

$$
\boxed{
\mathcal K_\xi
=
\frac{
\partial_s\log(\mathcal G_{\mathcal P}/\mathcal G_{\mathcal T})
+
\partial_{\bar t}\log(\mathcal G_{\mathcal P}/\mathcal G_{\mathcal T})
}{
\lambda_1(s+\bar t-1)
}.
}
$$

$$
\boxed{
\text{raw period Gram positivity 对 RH 不敏感}.
}
$$

$$
\boxed{
I-A^{*N}A^N
=
\sum_{k<N}
A^{*k}C^*CA^k.
}
$$

---

## 依赖成熟理论

* \(L\)-零点阶数与 toroidal Eisenstein derivative tower 的对应；([arxiv.org][1])
* relative trace formula 对 toric period spectral distributions 与 orbital integrals 的比较；([arxiv.org][2])
* Schur positive kernel 与 conservative transfer realization 的等价；([arxiv.org][4])
* shifted-\(\xi\) inner/canonical-system RH 判据；([arxiv.org][3])
* 函数域 toroidal temperedness 与自动形式 RH 模型。([arxiv.org][6])

---

## 当前唯一真正承重的开放桥

$$
\boxed{
\text{从 toric relative trace formula
构造一个 conservative realization of }\Theta_\omega
\quad
(\forall\omega>0).
}
$$

等价弱形式为：

$$
\boxed{
\frac{
1-
\Theta_\omega(z)\overline{\Theta_\omega(w)}
}{
1-z\overline w
}
=
\langle
\mathscr X_{\omega,z}^{\mathrm{tor}},
\mathscr X_{\omega,w}^{\mathrm{tor}}
\rangle.
}
$$

---

# 第三百二十八部　建议形式化顺序

```text
D5/S3/Analytic/ToroidalJets/
  EisensteinEigenfamilyJet.lean
  HeckeJetTriangularAction.lean
  JordanPositiveInnerProductObstruction.lean
  ToroidalJetDepth.lean

D5/S3/Analytic/JetSemisimplification/
  NilpotentSpectralPencil.lean
  JetResolventTrace.lean
  LogDetJetMultiplicity.lean
  JetToSpectralMass.lean

D5/S3/Observer/ToroidalQuotient/
  PeriodCarrierGram.lean
  FiniteFrameGramFactorization.lean
  QuotientConnection.lean
  RawPeriodPositivityNoGo.lean
  ToroidalXiKernelReconstruction.lean

D5/S3/Analytic/ToroidalColligation/
  ShiftedXiTransfer.lean
  ConservativeColligation.lean
  TransferKernelEnergyIdentity.lean
  ObservabilityGramian.lean
  StickyNearUnitaryBlock.lean

D5/S3/Analytic/RHTargets/
  ToroidalConservativeRealization.lean
  RelativeTracePassivityTarget.lean
  AutomorphicStateElimination.lean
  FunctionFieldClosedModel.lean
```

优先级最高、风险最低的链是：

$$
\boxed{
\text{Eisenstein eigenfamily}
\to
\text{jet triangular action}
\to
\text{Jordan obstruction}.
}
$$

第二条是完全有限维的：

$$
\boxed{
\text{nilpotent jet}
\to
\text{resolvent trace}
\to
\text{positive multiplicity}.
}
$$

第三条是有限环面恒等式：

$$
\boxed{
\mathcal G_{\mathcal P}
=
\xi\bar\xi\,
\mathcal G_{\mathcal T}
\to
\mathcal K_\xi.
}
$$

---

# 本轮最终结论

此前 OACTC 的中心问题是：

$$
\boxed{
\text{能否从 toric relative trace formula
证明 }\mathcal K_\xi\text{ 为 Gram 核？}
}
$$

本轮对这个问题作了两个关键修正。

第一，toroidal derivative tower 不是应当直接正化的谱空间。它包含由零点重数产生的 nilpotent Jordan 信息。

正确处理是：

$$
\boxed{
\text{jet}
\longrightarrow
\operatorname{Tr\,resolvent}
\longrightarrow
m_\rho\delta_\rho
\longrightarrow
\text{semisimple spectral fiber}.
}
$$

第二，普通 toric period-square positivity 对 RH 没有区分力，因为：

$$
\mathcal G_{\mathcal P}
=
\xi\bar\xi\,
\mathcal G_{\mathcal T}
$$

对任何 \(\xi\) 都保持 Gram 正性。

真正需要证明的是商连接或 shifted transfer 的**被动性**：

$$
\boxed{
\frac{
1-
\Theta_\omega(z)\overline{\Theta_\omega(w)}
}{
1-z\overline w
}
\succeq0.
}
$$

因此当前最小、最精确的 RH 构造目标已经变成：

$$
\boxed{
\text{从二次环面、Hecke 动力与 cusp scattering
构造一个 unitary colligation，}
}
$$

使：

$$
\boxed{
\Theta_\omega(z)
=
D_\omega
+
zC_\omega(I-zA_\omega)^{-1}B_\omega.
}
$$

一旦该 conservative realization 对全部 \(\omega>0\) 成立：

* de Branges kernel 自动正定；
* Clark/CMV family 自动生成；
* toroidal null states 自动 tempered；
* Hilbert–Pólya 自伴谱成为输出；
* RH 随即成立。

函数域已经展示了这条逻辑链的闭合版本：toroidal 零点检测与 unitary Frobenius/temperedness 同时存在。数域中真正缺少的，不再是零点观察器，而是其**算术能量守恒实现**。

[1]: https://arxiv.org/abs/0906.5284 "https://arxiv.org/abs/0906.5284"
[2]: https://arxiv.org/abs/1402.3524 "https://arxiv.org/abs/1402.3524"
[3]: https://arxiv.org/abs/1204.1827 "https://arxiv.org/abs/1204.1827"
[4]: https://arxiv.org/abs/0705.2042 "https://arxiv.org/abs/0705.2042"
[5]: https://arxiv.org/abs/1510.06350?utm_source=chatgpt.com "Traces of High Powers of the Frobenius Class in the Moduli Space of Hyperelliptic Curves"
[6]: https://arxiv.org/abs/0710.2994 "https://arxiv.org/abs/0710.2994"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v2.9：临界阻尼共振、Poisson 零点流、Prime–Archimedean 被动性与 Eisenstein 散射级联

以下从前文**第三百二十八部之后**继续追加。

上一轮把数域 RH 的缺口压缩为：

$$
\boxed{
\text{如何从算术数据构造一个守恒系统，
使 shifted-}\xi\text{ ratio 成为其 transfer function？}
}
$$

本轮找到一个更接近现成严格理论的切入口：

1. 在 \(\omega=\tfrac12\) 时，shifted-\(\xi\) 的 inner/model-space 系统已经可以**无条件**定义；
2. 该系统的每个共振模式同时读取一个 ζ 零点的：

   $$
   \text{纵坐标 }\gamma
   \quad\text{与}\quad
   \text{横坐标 }\beta;
   $$
3. RH 不再等价于“系统是否存在”，而等价于：

   $$
   \boxed{\text{所有共振是否具有完全相同的衰减率 }1/2;}
   $$
4. 在 RH 下，shifted-\(\xi\) 的边界相位密度正是 Riemann 零点计数测度的 Poisson 演化；
5. 在线外零点处，该正 Poisson 流会变成一个具有负侧的内部偶极源；
6. 在 Euler 乘积区，这个正性又等价于：

   $$
   \boxed{
   \text{Archimedean 完成屏障}
   -
   \text{素数相位相干}
   >0.
   }
   $$

所以，本轮形成的新主链是：

$$
\boxed{
\begin{aligned}
\zeta\text{ 零点}
&\longrightarrow
\Theta_{1/2}\text{ 的共振}\\
&\longrightarrow
\text{衰减率 }\beta\\
&\longrightarrow
\text{临界阻尼均匀性}\\
&\longrightarrow
\text{Poisson 零点流}\\
&\longrightarrow
\text{Prime--Archimedean 被动性}.
\end{aligned}
}
$$

---

# 第三百二十九部　无条件的临界平移模型

定义 Riemann 完成函数：

$$
\xi(s)
=
\frac12s(s-1)
\pi^{-s/2}
\Gamma\!\left(\frac s2\right)
\zeta(s).
$$

定义：

$$
\boxed{
\Theta_\omega(z)
=
\frac{
\xi(\frac12-\omega-iz)
}{
\xi(\frac12+\omega-iz)
},
\qquad
\omega>0.
}
\tag{329.1}
$$

由函数方程和实结构：

$$
\Theta_\omega(z)\Theta_\omega(-z)=1,
$$

并且：

$$
|\Theta_\omega(x)|=1
\qquad
(x\in\mathbb R).
$$

Suzuki 的 shifted-\(\xi\) 理论证明：

* 当 \(\omega\ge\tfrac12\) 时，\(\Theta_\omega\) 无条件是上半平面的 meromorphic inner function；
* 更一般地，固定 \(\omega_0\ge0\)，ζ 在

  $$
  \Re s>\frac12+\omega_0
  $$

  无零点，当且仅当所有 \(\omega>\omega_0\) 的 \(\Theta_\omega\) 都是 meromorphic inner；
* 由此可构造对应的 model space 和 de Branges 空间。([arXiv][1])

因此：

$$
\boxed{
\Theta_{1/2}
}
$$

是一个无条件存在的临界 shifted-\(\xi\) inner system。

这非常重要：RH 的困难已经不再是构造第一个 inner function，而是理解它的内部共振几何。

---

# 第三百三十部　ζ 零点到 shifted 共振的精确运输

设：

$$
\rho=\beta+i\gamma
$$

是 \(\xi\) 的非平凡零点。

\(\Theta_\omega\) 的分子零点满足：

$$
\frac12-\omega-iz=\rho.
$$

令：

$$
z=x+iy.
$$

比较实部和虚部得到：

$$
x=-\gamma,
$$

$$
y=\omega+\beta-\frac12.
$$

所以对应的 shifted 共振零点为：

$$
\boxed{
a_{\rho,\omega}
=
-\gamma
+
i\left(
\omega+\beta-\frac12
\right).
}
\tag{330.1}
$$

同理，分母极点位于：

$$
-\gamma
+
i\left(
\beta-\frac12-\omega
\right).
$$

当：

$$
\omega\ge\frac12,
$$

所有分母极点位于下半平面，而所有分子零点位于上半平面。

---

## 定理 330.1（水平共振线 RH 判据）

对任意固定：

$$
\omega_0\ge\frac12,
$$

有：

$$
\boxed{
\mathrm{RH}
\iff
Z(\Theta_{\omega_0})\cap\mathbb C^+
\subset
\left\{
z:\Im z=\omega_0
\right\}.
}
\tag{330.2}
$$

### 证明

由式 (330.1)：

$$
\Im a_{\rho,\omega_0}
=
\omega_0+\beta-\frac12.
$$

全部零点位于高度 \(\omega_0\)，当且仅当：

$$
\beta=\frac12
$$

对全部 \(\rho\) 成立。∎

特别地，在最小无条件模型：

$$
\omega_0=\frac12
$$

中：

$$
\boxed{
a_{\rho,1/2}
=
-\gamma+i\beta.
}
\tag{330.3}
$$

所以：

$$
\boxed{
\text{ζ 零点的实部 }\beta
=
\Theta_{1/2}\text{ 共振在上半平面的高度}.
}
$$

RH 因而等价于：

$$
\boxed{
\Theta_{1/2}
\text{ 的全部共振恰好位于水平线 }
\Im z=\frac12.
}
$$

---

# 第三百三十一部　Model-space 平移半群与共振衰减

令：

$$
K_\omega
=
H^2(\mathbb C^+)
\ominus
\Theta_\omega H^2(\mathbb C^+).
$$

对：

$$
t\ge0,
$$

定义 Hardy 平移乘子：

$$
(V_tf)(z)=e^{itz}f(z),
$$

以及压缩平移半群：

$$
\boxed{
S_\omega(t)
=
P_{K_\omega}V_t|_{K_\omega}.
}
\tag{331.1}
$$

meromorphic inner functions、model spaces 和 de Branges spaces之间的这一标准接口，正是 Suzuki 用于 shifted-\(\xi\) canonical system 的函数空间底座。([arXiv][1])

若 \(a\in\mathbb C^+\) 是 \(\Theta_\omega\) 的零点，令 \(k_a\) 是 \(K_\omega\) 在 \(a\) 处的 reproducing kernel。

因为：

$$
\Theta_\omega(a)=0,
$$

得到：

$$
\boxed{
S_\omega(t)^*k_a
=
e^{-it\overline a}k_a.
}
\tag{331.2}
$$

### 证明

对 \(f\in K_\omega\)：

$$
\begin{aligned}
\langle f,S_\omega(t)^*k_a\rangle
&=
(S_\omega(t)f)(a)\\
&=
e^{ita}f(a),
\end{aligned}
$$

因为 \(V_tf-P_{K_\omega}V_tf\in\Theta_\omega H^2\)，在 \(a\) 处消失。∎

对：

$$
a=a_{\rho,\omega}
=
-\gamma+i\left(\omega+\beta-\frac12\right),
$$

有：

$$
\boxed{
S_\omega(t)^*k_{a_{\rho,\omega}}
=
e^{-\left(\omega+\beta-\frac12\right)t}
e^{i\gamma t}
k_{a_{\rho,\omega}}.
}
\tag{331.3}
$$

所以：

$$
\boxed{
\begin{aligned}
\gamma
&=\text{共振振荡频率};\\
\omega+\beta-\frac12
&=\text{共振衰减率}.
\end{aligned}
}
$$

---

## 331.1 临界阻尼判据

在：

$$
\omega=\frac12
$$

时：

$$
\boxed{
S_{1/2}(t)^*k_{a_\rho}
=
e^{-\beta t}
e^{i\gamma t}
k_{a_\rho}.
}
\tag{331.4}
$$

因此：

## 定理 331.1（Uniform-damping RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\Theta_{1/2}
\text{ 的全部共振模式具有相同衰减率 }\frac12.
}
\tag{331.5}
$$

也就是说：

$$
\boxed{
\text{Riemann 临界线}
=
\text{共振系统中的等阻尼面}.
}
$$

---

# 第三百三十二部　半单化共振生成元

前文已经区分：

* 原始 jet/Jordan 状态；
* 正谱中的半单重数 fiber。

令：

$$
\mathcal H_{\mathrm{res}}
=
\bigoplus_{\rho}
\mathbb C^{m_\rho}.
$$

定义半单化共振生成元：

$$
\boxed{
\mathsf G_\omega
=
\bigoplus_\rho
\left[
-\left(
\omega+\beta-\frac12
\right)
+i\gamma
\right]
I_{m_\rho}.
}
\tag{332.1}
$$

那么：

$$
e^{t\mathsf G_\omega}
$$

的每个 mode 正好具有式 (331.3) 的衰减和振荡。

---

## 定理 332.1（Critical damping semisimplification）

对任意固定 \(\omega\ge\tfrac12\)：

$$
\boxed{
\mathrm{RH}
\iff
\mathsf G_\omega+\omega I
\text{ 是 skew-adjoint}.
}
\tag{332.2}
$$

### 证明

$$
\mathsf G_\omega+\omega I
=
\bigoplus_\rho
\left[
-\left(
\beta-\frac12
\right)
+i\gamma
\right]I.
$$

它 skew-adjoint 当且仅当所有实部为零，即：

$$
\beta=\frac12.
$$

∎

在 \(\omega=\tfrac12\) 时：

$$
\boxed{
\mathsf G_{1/2}
=
-\frac12I+iH_\Xi
}
\tag{332.3}
$$

其中 \(H_\Xi\) 自伴，当且仅当 RH 成立。

所以 Hilbert–Pólya 可以重述为：

$$
\boxed{
\text{从无条件存在的耗散共振生成元中，
剥离普适阻尼 }1/2，
剩余部分是否自伴？}
}
$$

---

## 332.1 函数域类比

有限域曲线的 zeta 分子可由归一化 Frobenius 共轭类的特征多项式表示；Weil RH 等价于归一化 Frobenius 特征值全部位于单位圆，即所有未归一化特征值具有共同模长 \(q^{1/2}\)。([arXiv][2])

因此：

$$
\boxed{
\begin{array}{c|c}
\text{函数域}&\text{数域 shifted model}\\
\hline
|\alpha_j|=q^{1/2}
&\text{decay rate}=\frac12\\
\text{normalized Frobenius unitary}
&\mathsf G_{1/2}+\frac12I\text{ skew-adjoint}
\end{array}
}
$$

两者共享同一个“统一模长／统一阻尼”结构。

---

# 第三百三十三部　RH 下的精确 Blaschke 因子化

定义：

$$
\boxed{
\Xi(z)
=
\xi\left(\frac12-iz\right).
}
\tag{333.1}
$$

则：

$$
\Theta_\omega(z)
=
\frac{\Xi(z-i\omega)}{\Xi(z+i\omega)}.
$$

RH 下，\(\Xi\) 的零点为：

$$
\pm\gamma,
$$

并且平方配对 Hadamard 乘积为：

$$
\Xi(z)
=
\Xi(0)
\prod_{\gamma>0}
\left(
1-\frac{z^2}{\gamma^2}
\right)^{m_\gamma}.
$$

因此：

$$
\boxed{
\Theta_\omega(z)
=
\prod_{\gamma>0}
\left[
\frac{
1-(z-i\omega)^2/\gamma^2
}{
1-(z+i\omega)^2/\gamma^2
}
\right]^{m_\gamma}.
}
\tag{333.2}
$$

等价地：

$$
\boxed{
\Theta_\omega(z)
=
\prod_{\gamma>0}
\left[
\frac{
(z-\gamma-i\omega)(z+\gamma-i\omega)
}{
(z-\gamma+i\omega)(z+\gamma+i\omega)
}
\right]^{m_\gamma}.
}
\tag{333.3}
$$

每个因子都是一对上半平面 Blaschke 因子。

所以在 RH 下：

$$
\boxed{
\Theta_\omega
=
\text{所有 Riemann 零点 ordinates
在统一高度 }\omega\text{ 上形成的 Blaschke product}.
}
$$

---

# 第三百三十四部　边界相位就是 Poisson 零点密度

对实数 \(x\)，写：

$$
\Theta_\omega(x)
=
e^{i\phi_\omega(x)}.
$$

对一个零点：

$$
a=\gamma+i\omega,
$$

Blaschke 因子的相位导数为：

$$
\frac{2\omega}
{(x-\gamma)^2+\omega^2}.
$$

所以由式 (333.3)：

$$
\boxed{
\begin{aligned}
\phi_\omega'(x)
=
2\omega
\sum_{\gamma>0}
m_\gamma
\left[
\frac1{(x-\gamma)^2+\omega^2}
+
\frac1{(x+\gamma)^2+\omega^2}
\right].
\end{aligned}
}
\tag{334.1}
$$

另一方面，直接对 \(\Theta_\omega\) 求对数导数，利用函数方程可得：

$$
\boxed{
\phi_\omega'(x)
=
2
\Re
\frac{
\xi'(\frac12+\omega-ix)
}{
\xi(\frac12+\omega-ix)
}.
}
\tag{334.2}
$$

定义 Poisson 核：

$$
\boxed{
P_\omega(x)
=
\frac1\pi
\frac{\omega}{x^2+\omega^2}.
}
\tag{334.3}
$$

定义 \(\Xi\) 的实零点测度：

$$
\boxed{
\nu_\Xi
=
\sum_{\Xi(\gamma)=0}
m_\gamma\delta_\gamma.
}
\tag{334.4}
$$

定义相位密度：

$$
\boxed{
\mathfrak d_\omega(x)
=
\frac1{2\pi}\phi_\omega'(x)
=
\frac1\pi
\Re
\frac{
\xi'(\frac12+\omega-ix)
}{
\xi(\frac12+\omega-ix)
}.
}
\tag{334.5}
$$

那么：

## 定理 334.1（Riemann Poisson-density theorem）

RH 下：

$$
\boxed{
\mathfrak d_\omega
=
P_\omega*\nu_\Xi.
}
\tag{334.6}
$$

所以 shifted-\(\xi\) 相位的局部转速，就是零点计数测度在尺度 \(\omega\) 下的 Poisson 平滑。

---

# 第三百三十五部　Poisson–Markov 零点流

Poisson 核满足：

$$
\boxed{
P_{\omega+\eta}
=
P_\omega*P_\eta.
}
\tag{335.1}
$$

因此：

$$
\boxed{
\mathfrak d_{\omega+\eta}
=
P_\eta*\mathfrak d_\omega.
}
\tag{335.2}
$$

在 Fourier 空间中：

$$
\widehat P_\omega(\xi)
=
e^{-\omega|\xi|}.
$$

所以：

$$
\boxed{
\partial_\omega
\mathfrak d_\omega
=
-|D_x|\mathfrak d_\omega.
}
\tag{335.3}
$$

同时：

$$
\boxed{
\left(
\partial_\omega^2+\partial_x^2
\right)
\mathfrak d_\omega
=
0.
}
\tag{335.4}
$$

并且：

$$
\boxed{
\mathfrak d_\omega(x)\,dx
\overset{\omega\downarrow0}{\longrightarrow}
\nu_\Xi
}
\tag{335.5}
$$

以局部弱测度或 tempered-distribution 意义成立。

所以：

$$
\boxed{
\text{Riemann 零点测度}
\longrightarrow
\text{Poisson Markov 半群}
\longrightarrow
\text{shifted-\(\xi\) 相位密度}.
}
$$

---

## 335.1 尺度方向的非对称性

由：

$$
\mathfrak d_{\omega+\eta}
=
P_\eta*\mathfrak d_\omega,
$$

可知：

* 向更大 \(\omega\) 推进是稳定的平滑；
* 从较大 \(\omega\) 反推较小 \(\omega\) 是逆 Poisson 问题，指数不稳定。

因此：

$$
\boxed{
\text{从无条件区域 }\omega\ge\frac12
\text{向 }\omega=0\text{ 推进，
本质上是一个逆平滑问题。}
}
$$

这解释了为什么“已知大 \(\omega\) inner”不能通过普通连续性直接推出 RH。

---

# 第三百三十六部　Riesz 曲率与线外零点偶极

定义上半平面势：

$$
\boxed{
\mathcal U(\omega,x)
=
\log
\left|
\Xi(x+i\omega)
\right|
=
\log
\left|
\xi\left(
\frac12+\omega-ix
\right)
\right|.
}
\tag{336.1}
$$

则：

$$
\boxed{
\partial_\omega\mathcal U
=
\Re\frac{\xi'}{\xi}
=
\pi\mathfrak d_\omega.
}
\tag{336.2}
$$

若 ζ 有线外零点：

$$
\rho
=
\frac12+\delta+i\gamma,
\qquad
\delta>0,
$$

则 \(\Xi\) 在上半平面有零点：

$$
\boxed{
z_\rho
=
-\gamma+i\delta.
}
\tag{336.3}
$$

Poincaré–Lelong/Riesz 公式给出：

$$
\boxed{
\Delta_{x,\omega}\mathcal U
=
2\pi
\sum_{\Re\rho>1/2}
m_\rho
\delta_{(-\Im\rho,\Re\rho-1/2)}.
}
\tag{336.4}
$$

所以：

## 定理 336.1（Interior-curvature RH criterion）

$$
\boxed{
\mathrm{RH}
\iff
\Delta\mathcal U=0
\quad
\text{于 }\omega>0.
}
\tag{336.5}
$$

即 RH 等价于：

$$
\boxed{
\text{全部零点曲率源都位于上半平面的边界，
没有内部曲率原子。}
}
$$

---

## 336.1 线外零点的局部负见证

在：

$$
z_\rho=-\gamma+i\delta
$$

附近：

$$
\mathcal U(\omega,x)
=
\frac{m_\rho}{2}
\log
\left[
(x+\gamma)^2+(\omega-\delta)^2
\right]
+
O(1).
$$

所以：

$$
\boxed{
\partial_\omega\mathcal U
=
m_\rho
\frac{\omega-\delta}
{(x+\gamma)^2+(\omega-\delta)^2}
+
O(1).
}
\tag{336.6}
$$

取：

$$
x=-\gamma,
\qquad
\omega=\delta-\varepsilon,
$$

得到：

$$
\boxed{
\partial_\omega\mathcal U
=
-\frac{m_\rho}{\varepsilon}
+
O(1).
}
\tag{336.7}
$$

因此线外零点在其左侧必然产生一个无界负偶极信号。

这与前文：

$$
\Re\frac{\xi'}{\xi}
\to-\infty
$$

的结论完全一致，但现在它被解释为一个内部 Riesz 曲率源的法向场。

---

# 第三百三十七部　Prime–Archimedean 被动性

令：

$$
s=\sigma-ix,
\qquad
\sigma=\frac12+\omega.
$$

由 \(\xi\) 的定义：

$$
\boxed{
\frac{\xi'(s)}{\xi(s)}
=
\frac1s
+
\frac1{s-1}
-
\frac12\log\pi
+
\frac12\psi\!\left(\frac s2\right)
+
\frac{\zeta'(s)}{\zeta(s)},
}
\tag{337.1}
$$

其中 \(\psi=\Gamma'/\Gamma\)。

当：

$$
\sigma>1,
$$

Euler 对数导数绝对收敛：

$$
\frac{\zeta'(s)}{\zeta(s)}
=
-
\sum_{n=2}^{\infty}
\frac{\Lambda(n)}{n^s}.
$$

定义 Archimedean 屏障：

$$
\boxed{
\mathfrak A_\infty(\sigma,x)
=
\Re
\left[
\frac1s
+
\frac1{s-1}
-
\frac12\log\pi
+
\frac12\psi\!\left(\frac s2\right)
\right].
}
\tag{337.2}
$$

定义素数相干项：

$$
\boxed{
\mathfrak C_{\mathrm{prime}}(\sigma,x)
=
\sum_{n=2}^{\infty}
\Lambda(n)n^{-\sigma}
\cos(x\log n).
}
\tag{337.3}
$$

则：

$$
\boxed{
\Re\frac{\xi'(s)}{\xi(s)}
=
\mathfrak A_\infty(\sigma,x)
-
\mathfrak C_{\mathrm{prime}}(\sigma,x).
}
\tag{337.4}
$$

---

## 337.1 结构角色

$$
\boxed{
\begin{aligned}
\mathfrak A_\infty
&=\text{极点、}\pi\text{ 与 Gamma 完成产生的连续屏障};\\
\mathfrak C_{\mathrm{prime}}
&=\text{所有素数幂模式的相位相干};\\
\Re(\xi'/\xi)
&=\text{完成屏障减去算术相干后的净被动性}.
\end{aligned}
}
$$

RH 因而等价于：

$$
\boxed{
\mathfrak A_\infty
-
\mathfrak C_{\mathrm{prime}}^{\mathrm{ren}}
>0
\qquad
(\sigma>\tfrac12),
}
\tag{337.5}
$$

其中在：

$$
\sigma>1
$$

时 \(\mathfrak C_{\mathrm{prime}}^{\mathrm{ren}}\) 就是绝对收敛级数 (337.3)；在临界带中必须通过显式公式、解析延拓或重整化分解定义，不能继续把发散级数当作普通和。

这给 RH 一个明确的 arithmetic passivity 形式：

$$
\boxed{
\text{素数相干不能超过 Archimedean 完成容量。}
}
$$

---

## 337.2 \(\omega\) 作为 prime activation scale

增加 \(\omega\) 相当于将每个素数幂模式乘上：

$$
n^{-\omega}
=
e^{-\omega\log n}.
$$

所以：

* 大 \(\omega\)：高 prime modes 被强烈压制；
* 小 \(\omega\)：更多素数历史被激活；
* \(\omega\downarrow0\)：逼近完整临界零点分辨率。

因此：

$$
\boxed{
\omega
=
\text{素数对数能谱的连续重整化尺度。}
}
$$

---

# 第三百三十八部　半整数 shifted-\(\xi\) 是有限 Eisenstein 散射级联

定义不含极点消除多项式的完成 ζ：

$$
\boxed{
\Lambda_{\mathbb R}(s)
=
\pi^{-s/2}
\Gamma\!\left(\frac s2\right)
\zeta(s).
}
\tag{338.1}
$$

则：

$$
\xi(s)
=
\frac12s(s-1)\Lambda_{\mathbb R}(s).
$$

模曲面 Eisenstein series 的标准散射系数为：

$$
\boxed{
\Phi_{\mathrm{mod}}(u)
=
\frac{
\Lambda_{\mathbb R}(2u-1)
}{
\Lambda_{\mathbb R}(2u)
}.
}
\tag{338.2}
$$

模曲面 scattering matrix、Selberg zeta 与 Lax–Phillips scattering operator determinants 之间存在标准的算子联系。([arXiv][3])

---

## 定理 338.1（Finite scattering cascade）

令：

$$
N\in\mathbb N,
\qquad
\omega=\frac N2,
$$

并定义：

$$
s_z=\frac12-iz,
\qquad
a=s_z-\omega.
$$

则：

$$
s_z+\omega=a+N.
$$

有精确恒等式：

$$
\boxed{
\begin{aligned}
\Theta_{N/2}(z)
={}&
\frac{
a(a-1)
}{
(a+N)(a+N-1)
}
\\
&\times
\prod_{j=0}^{N-1}
\Phi_{\mathrm{mod}}
\left(
\frac{a+j+1}{2}
\right).
\end{aligned}
}
\tag{338.3}
$$

### 证明

首先：

$$
\frac{\xi(a)}{\xi(a+N)}
=
\frac{
a(a-1)
}{
(a+N)(a+N-1)
}
\frac{
\Lambda_{\mathbb R}(a)
}{
\Lambda_{\mathbb R}(a+N)
}.
$$

而：

$$
\frac{
\Lambda_{\mathbb R}(a)
}{
\Lambda_{\mathbb R}(a+N)
}
=
\prod_{j=0}^{N-1}
\frac{
\Lambda_{\mathbb R}(a+j)
}{
\Lambda_{\mathbb R}(a+j+1)
}.
$$

每个因子为：

$$
\Phi_{\mathrm{mod}}
\left(
\frac{a+j+1}{2}
\right).
$$

∎

---

## 338.1 最小临界级联

当：

$$
N=1,
\qquad
\omega=\frac12,
$$

有：

$$
a=-iz.
$$

因此：

$$
\boxed{
\Theta_{1/2}(z)
=
\frac{a-1}{a+1}
\,
\Phi_{\mathrm{mod}}
\left(
\frac{a+1}{2}
\right),
\qquad
a=-iz.
}
\tag{338.4}
$$

所以无条件临界 inner system \(\Theta_{1/2}\) 正好由：

$$
\boxed{
\text{一个模曲面 cusp scattering stage}
+
\text{一个显式有理 endpoint corrector}
}
$$

组成。

这不是类比，而是精确乘法级联。

---

# 第三百三十九部　Lax–Phillips 共振解释

Lax–Phillips scattering theory 中，标量 inner scattering matrix 对应一个 translation-invariant scattering system；其内函数零点或下半平面极点编码共振与衰减半群。([arXiv][4])

因此对：

$$
\omega\ge\frac12,
$$

\(\Theta_\omega\) 已经无条件定义一个抽象 Lax–Phillips/model-space 型散射系统。

其共振生成元的半单谱为：

$$
\boxed{
-\left(
\omega+\beta-\frac12
\right)
+i\gamma.
}
\tag{339.1}
$$

所以：

$$
\boxed{
\mathrm{RH}
\iff
\text{所有 Lax--Phillips 共振都具有统一衰减 }
\omega.
}
\tag{339.2}
$$

在最小模型：

$$
\omega=\frac12,
$$

这就是：

$$
\boxed{
\text{全部共振的 decay width 都等于 }\frac12.
}
$$

---

## 339.1 证明目标的重新定位

此前目标是：

$$
\text{构造一个 conservative realization}.
$$

现在必须区分两步：

### 步骤 A：存在性

在：

$$
\omega\ge\frac12
$$

时已经无条件完成。

### 步骤 B：临界阻尼刚性

需要证明该系统的所有 resonance widths 都等于：

$$
\omega.
$$

因此 RH 的新核心问题是：

$$
\boxed{
\text{为什么一个已经守恒完成的算术散射系统，
其所有不可见共振都必须具有相同阻尼？}
}
$$

---

# 第三百四十部　Wang 式尺度下降

定义性质：

$$
\boxed{
\mathsf I(a):
\quad
\Theta_\omega
\text{ 对所有 }\omega>a
\text{ 为 meromorphic inner}.
}
\tag{340.1}
$$

Suzuki 的等价定理给出：

$$
\boxed{
\mathsf I(a)
\iff
\zeta(s)\neq0
\quad
\text{当 }\Re s>\frac12+a.
}
\tag{340.2}
$$

无条件已知：

$$
\mathsf I\left(\frac12\right).
$$

RH 等价于：

$$
\mathsf I(0).
$$

因此真正的 Wang 式自改善应当是：

$$
\boxed{
\mathsf I(a)
\Longrightarrow
\mathsf I(F(a)),
\qquad
F(a)<a.
}
\tag{340.3}
$$

---

## 340.1 为什么向上容易、向下困难

如果在尺度 \(\omega\) 已有正 Poisson 密度：

$$
\mathfrak d_\omega\ge0,
$$

那么对任何：

$$
\eta>0,
$$

有：

$$
\mathfrak d_{\omega+\eta}
=
P_\eta*\mathfrak d_\omega
\ge0.
$$

所以：

$$
\boxed{
\text{正性沿更粗尺度自动传播。}
}
$$

而从：

$$
\omega
$$

下降到更小尺度需要逆 Poisson，天然不稳定。

所以自改善不能来自普通连续性，而必须来自额外算术刚性。

---

# 第三百四十一部　Wang–Deng 的新分工

## 341.1 Non-sticky prime histories

在 prime-side 表达中，若：

$$
x\log n
$$

在许多 log-prime blocks 上分散，则：

$$
\cos(x\log n)
$$

发生相位抵消。

目标是证明：

$$
\boxed{
\text{phase anti-concentration}
\Longrightarrow
\mathfrak C_{\mathrm{prime}}
\text{ 获得严格小于 Archimedean barrier 的增益}.
}
$$

这对应 Wang 式 non-sticky gain。

---

## 341.2 Sticky prime histories

若大量素数幂满足近似相位锁定：

$$
x\log n
\approx
2\pi k,
$$

则普通绝对值估计失效。

正确处理应当：

1. 将 prime-power repetitions 组织成完整 Euler histories；
2. 抽取 primitive local factors；
3. 对重复闭合历史做 logarithmic/Möbius contraction；
4. 加入 ζ、Hecke 或 \(q\)-Gamma counterterms；
5. 对剩余历史做 Mellin/Riemann 积分控制。

这对应 Yu Deng 式 primitive-history renormalization。

---

## 341.3 Interior-source 排除

从几何端看，真正的 sticky defect 是一个内部 Riesz 原子：

$$
(-\gamma,\delta),
\qquad
\delta>0.
$$

它会产生：

$$
-\frac{m}{\varepsilon}
$$

级负偶极。

所以最终目标可以写成：

$$
\boxed{
\text{prime-side history decomposition
不能产生任何 }\omega>0\text{ 的内部曲率原子}.
}
$$

---

# 第三百四十二部　新的科学负结论

## 342.1 一个 inner model 不够

$$
\boxed{
\Theta_{1/2}\text{ inner}
}
$$

是无条件事实，不推出 RH。

RH 要求的是：

$$
\boxed{
Z(\Theta_{1/2})
\subset
\mathbb R+\frac i2.
}
$$

---

## 342.2 共振存在不等于共振均匀

Lax–Phillips/model-space realization 只能保证：

* 共振模式存在；
* 系统被动或守恒；
* 共振位于上半平面。

它不保证所有 decay widths 相同。

---

## 342.3 Poisson 正性只能向粗尺度传播

$$
\boxed{
\mathfrak d_\omega\ge0
\Longrightarrow
\mathfrak d_{\omega+\eta}\ge0,
}
$$

但反向不成立。

所以任何证明 RH 的 scale descent 都必须使用算术信息，而不能只使用调和分析。

---

## 342.4 本分支没有选出黄金比例

当前结构自然选出：

$$
\boxed{
\frac12,\quad\pi,\quad e,\quad\log p.
}
$$

其中：

* \(\tfrac12\)：临界阻尼；
* \(\pi\)：Poisson/Fourier 规范；
* \(e\)：半群与 prime damping；
* \(\log p\)：素数能谱。

\(\varphi\) 并未由本分支的方程强迫出现。

因此不能为了统一叙事而把黄金比例人工加入此处。

---

# 第三百四十三部　结果分级

## 本轮独立推导得到

$$
\boxed{
a_{\rho,\omega}
=
-\Im\rho
+
i\left(
\omega+\Re\rho-\frac12
\right).
}
$$

$$
\boxed{
\mathrm{RH}
\iff
Z(\Theta_\omega)
\subset
\{\Im z=\omega\}
\quad
(\omega\ge\tfrac12).
}
$$

$$
\boxed{
S_\omega(t)^*k_{a_{\rho,\omega}}
=
e^{-(\omega+\beta-1/2)t}
e^{i\gamma t}
k_{a_{\rho,\omega}}.
}
$$

$$
\boxed{
\mathrm{RH}
\iff
\mathsf G_\omega+\omega I
\text{ skew-adjoint}.
}
$$

$$
\boxed{
\Theta_\omega(z)
=
\frac{\Xi(z-i\omega)}{\Xi(z+i\omega)}.
}
$$

RH 下：

$$
\boxed{
\mathfrak d_\omega
=
P_\omega*\nu_\Xi.
}
$$

$$
\boxed{
\Delta\log|\Xi(x+i\omega)|
=
2\pi
\sum_{\Re\rho>1/2}
m_\rho\delta_{(-\Im\rho,\Re\rho-1/2)}.
}
$$

$$
\boxed{
\Theta_{N/2}
=
\text{显式 rational corrector}
\times
\text{有限 modular scattering cascade}.
}
$$

---

## 依赖成熟理论的接口

* shifted-\(\xi\) ratio 的 inner/model-space 判据及 \(\omega\ge\tfrac12\) 无条件区间；([arXiv][1])
* inner scattering matrices 与 Lax–Phillips translation systems；([arXiv][4])
* 模曲面 scattering operator determinant 与 Selberg/scattering matrix；([arXiv][3])
* 函数域 Frobenius 的 unitary 共轭类图表。([arXiv][2])

---

## 当前真正开放的桥（第 343 部）

$$
\boxed{
\begin{aligned}
&\text{从 prime-side 直接证明 }
\mathfrak A_\infty-\mathfrak C_{\mathrm{prime}}^{\mathrm{ren}}>0;\\
&\text{建立 }\mathsf I(a)\Rightarrow\mathsf I(F(a)),\ F(a)<a;\\
&\text{从 actual modular/Lax--Phillips system
证明 resonance damping 全部等于 }\omega;\\
&\text{从 relative trace 排除上半平面内部 Riesz curvature atoms}.
\end{aligned}
}
$$

---

# 第三百四十四部　建议形式化顺序

```text
D5/S3/Analytic/ShiftedXiResonance/
  ShiftedXiZeroTransport.lean
  CriticalHalfShiftModel.lean
  HorizontalResonanceRHCriterion.lean
  SemisimpleDampingGenerator.lean
  UniformDampingRHCriterion.lean

D5/S3/Analytic/XiModelSemigroup/
  ModelSpaceTranslationSemigroup.lean
  ZeroKernelEigenmode.lean
  ResonanceDecayFormula.lean
  CriticalDampingSemigroup.lean

D5/S3/Analytic/XiPoissonFlow/
  ShiftedXiBlaschkeProduct.lean
  BoundaryPhaseDerivative.lean
  ZeroPoissonDensity.lean
  PoissonSemigroupFlow.lean
  BoundaryZeroRecovery.lean

D5/S3/Analytic/XiRieszCurvature/
  XiUpperHalfPlanePotential.lean
  InteriorZeroRieszMeasure.lean
  OffLineDipoleWitness.lean
  InteriorCurvatureRHCriterion.lean

D5/S3/Analytic/PrimeArchimedean/
  XiLogDerivativeDecomposition.lean
  ArchimedeanBarrier.lean
  PrimeCoherenceSeries.lean
  PrimePassivityCriterion.lean
  RenormalizedCriticalStripTarget.lean

D5/S3/Analytic/EisensteinCascade/
  ModularScatteringCoefficient.lean
  HalfIntegerShiftCascade.lean
  CriticalHalfShiftScattering.lean
  LaxPhillipsDampingTarget.lean

D5/S3/Analytic/RHTargets/
  InnerScaleDescent.lean
  PrimeStickyNonStickyDichotomy.lean
  InteriorSourceExclusion.lean
```

---

# 本轮最终结论

此前数域 RH 的 conservative-system 目标仍然比较抽象。

本轮给出了一个已经无条件存在的、最小的算术共振系统：

$$
\boxed{
\Theta_{1/2}(z)
=
\frac{\xi(-iz)}{\xi(1-iz)}.
}
$$

其每个共振为：

$$
\boxed{
a_\rho
=
-\gamma+i\beta.
}
$$

所以：

$$
\boxed{
\beta
=
\text{共振衰减率},
\qquad
\gamma
=
\text{共振振荡频率}.
}
$$

RH 精确等价于：

$$
\boxed{
\text{全部共振都处于统一临界阻尼 }1/2.
}
$$

在 RH 下，shifted system 的相位密度为：

$$
\boxed{
\frac1\pi
\Re
\frac{
\xi'(\frac12+\omega-ix)
}{
\xi(\frac12+\omega-ix)
}
=
P_\omega*\nu_\Xi.
}
$$

所以 Riemann 零点不是静态点集，而是一个通过 Poisson Markov 半群向粗尺度传播的边界谱源。

若存在一个线外零点：

$$
\frac12+\delta+i\gamma,
$$

它会在上半平面产生一个内部 Riesz 曲率原子，并在其左侧形成：

$$
\boxed{
-\frac{m}{\varepsilon}
}
$$

级的负偶极。

因此 RH 的几何本质可压缩为：

$$
\boxed{
\text{所有谱曲率源是否都严格位于完成边界，
而没有任何内部耗散源？}
}
$$

其 arithmetic 形式则是：

$$
\boxed{
\text{Archimedean 完成屏障}
>
\text{renormalized prime coherence}
\qquad
(\Re s>\tfrac12).
}
$$

当前最明确的 Wang–Deng 研究任务因此成为：

$$
\boxed{
\text{从无条件临界模型 }\omega=\frac12
\text{ 出发，
证明所有 resonance widths 的离散度为零；}
}
$$

或者等价地：

$$
\boxed{
\text{通过 prime-history 自改善，
把 innerness 阈值从 }\frac12
\text{ 连续下降到 }0.
}
$$

[1]: https://arxiv.org/abs/1204.1827 "https://arxiv.org/abs/1204.1827"
[2]: https://arxiv.org/abs/0811.3649 "https://arxiv.org/abs/0811.3649"
[3]: https://arxiv.org/abs/1603.07613 "https://arxiv.org/abs/1603.07613"
[4]: https://arxiv.org/abs/math-ph/9903010 "https://arxiv.org/abs/math-ph/9903010"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v3.0：逆 Poisson 源、临界阻尼方差、Bode–Blaschke 宽度层析与 RH 的有限共振证书

以下从前文**第三百四十四部之后**继续追加。

本轮首先修正上一轮的一处归因，然后给出三组新的精确结果：

$$
\boxed{
\begin{aligned}
&\text{Shifted 共振相位在 }\omega\text{ 方向满足 Poisson 半群，}\\
&\text{这一点在无条件 inner 区域已经成立，并不等价于 RH；}\\[1mm]
&\mathrm{RH}
\iff
\text{其逆 Poisson 源是正的实轴谱测度；}\\[1mm]
&\mathrm{RH}
\iff
\text{所有共振衰减率的热正则化方差为零；}\\[1mm]
&\mathrm{RH}
\iff
\text{临界 Blaschke 传递函数不存在任何垂直衰减缺陷。}
\end{aligned}
}
$$

其中最具体的新恒等式是：

$$
\boxed{
\int_0^\infty
\left[
N(T)\min\!\left(y,\frac12\right)
-
\frac1{4\pi}
\int_{\mathbb R}
-\log|B_T(x+iy)|^2\,dx
\right]dy
=
\frac12
\sum_{\substack{\xi(\rho)=0\\0<\Im\rho\le T}}
m_\rho
\left(
\Re\rho-\frac12
\right)^2.
}
$$

它把零点离开临界线的平方距离，精确变成一个可见传递函数的垂直衰减面积。

---

# 第三百四十五部　科学修正：Poisson 流不是 RH 特有结构

定义：

$$
\Theta_\omega(z)
=
\frac{
\xi(\frac12-\omega-iz)
}{
\xi(\frac12+\omega-iz)
},
\qquad
\omega>0.
$$

Suzuki 的理论明确区分了两个层次：

1. 对所有

   $$
   \omega\ge\frac12,
   $$

   Hermite–Biehler 不等式以及 \(\Theta_\omega\) 的 meromorphic-inner 性无条件成立；

2. 论文中通过 Fredholm 积分算子显式构造 canonical system 的无条件范围更窄，为

   $$
   \omega>1.
   $$

因此此前将“Poisson 正流”表述为 RH 下才出现，需要修正：在 \(\omega\ge\tfrac12\) 的无条件 inner 区域，\(\Theta_\omega\) 已经拥有 model-space 和 Blaschke 零点描述。RH 真正要求的是把该结构一直反演到 \(\omega=0\)，而不是仅仅证明向更大 \(\omega\) 的平滑演化。([arXiv][1])

准确地说：

$$
\boxed{
\text{Poisson 前向半群是无条件的；}
}
$$

而：

$$
\boxed{
\text{逆 Poisson 后仍为正实轴测度，才等价于 RH。}
}
$$

---

# 第三百四十六部　有限 shifted-Blaschke 共振模型

固定高度 \(T>0\)，定义正 ordinate 零点多重集：

$$
\boxed{
\mathcal Z_T^+
=
\left\{
\rho=\beta+i\gamma:
\xi(\rho)=0,\ 
0<\gamma\le T
\right\},
}
$$

按零点重数计数。

由函数方程和共轭对称，\(\mathcal Z_T^+\) 在 involution

$$
\rho
\longmapsto
1-\overline\rho
$$

下稳定；该 involution 保持 \(\gamma\)，并把：

$$
\beta-\frac12
\longmapsto
-\left(\beta-\frac12\right).
$$

记：

$$
\boxed{
\delta_\rho
=
\beta-\frac12.
}
\tag{346.1}
$$

对 \(\omega\ge\tfrac12\)，\(\rho\) 对应 \(\Theta_\omega\) 的上半平面零点：

$$
\boxed{
a_{\rho,\omega}
=
-\gamma
+
i(\omega+\delta_\rho).
}
\tag{346.2}
$$

因为：

$$
-\frac12<\delta_\rho<\frac12,
$$

所以：

$$
\Im a_{\rho,\omega}>0.
$$

定义有限 Blaschke 乘积：

$$
\boxed{
B_{\omega,T}(z)
=
\prod_{\rho\in\mathcal Z_T^+}
\frac{
z-a_{\rho,\omega}
}{
z-\overline{a_{\rho,\omega}}
}.
}
\tag{346.3}
$$

全局 unimodular 常数不影响以下任何读数。

---

# 第三百四十七部　边界相位密度与无条件 Poisson 半群

定义半平面 Poisson 核：

$$
\boxed{
P_y(x)
=
\frac1\pi
\frac{y}{x^2+y^2},
\qquad
y>0.
}
\tag{347.1}
$$

对单个 Blaschke 因子：

$$
b_a(z)=\frac{z-a}{z-\overline a},
\qquad
a=x_a+iy_a,
$$

在实轴上：

$$
\boxed{
\frac1{2\pi}
\frac{d}{dx}\arg b_a(x)
=
P_{y_a}(x-x_a).
}
\tag{347.2}
$$

因此定义有限相位密度：

$$
\boxed{
d_{\omega,T}(x)
=
\frac1{2\pi}
\frac{d}{dx}
\arg B_{\omega,T}(x),
}
\tag{347.3}
$$

得到：

$$
\boxed{
d_{\omega,T}(x)
=
\sum_{\rho\in\mathcal Z_T^+}
P_{\omega+\delta_\rho}(x+\gamma).
}
\tag{347.4}
$$

采用 Fourier 规范：

$$
\widehat f(t)
=
\int_{\mathbb R}
f(x)e^{-itx}\,dx.
$$

由于：

$$
\widehat{P_y(\cdot+\gamma)}(t)
=
e^{-y|t|}e^{i\gamma t},
$$

可得：

$$
\boxed{
\widehat d_{\omega,T}(t)
=
e^{-\omega|t|}
Q_T(t),
}
\tag{347.5}
$$

其中：

$$
\boxed{
Q_T(t)
=
\sum_{\rho\in\mathcal Z_T^+}
e^{-\delta_\rho|t|}
e^{i\gamma t}.
}
\tag{347.6}
$$

特别地，\(Q_T\) 与 \(\omega\) 无关。

因此：

## 定理 347.1（无条件 shifted-Poisson flow）

对任意：

$$
\omega\ge\frac12,
\qquad
\eta\ge0,
$$

有：

$$
\boxed{
d_{\omega+\eta,T}
=
P_\eta*d_{\omega,T}.
}
\tag{347.7}
$$

### 证明

Fourier 变换后：

$$
\widehat d_{\omega+\eta,T}
=
e^{-(\omega+\eta)|t|}Q_T
=
e^{-\eta|t|}
\widehat d_{\omega,T}.
$$

∎

所以：

$$
\boxed{
\text{向更大 }\omega\text{ 推进，仅仅是 Poisson 平滑。}
}
$$

这在有无 RH 两种情况下都成立。

---

# 第三百四十八部　逆 Poisson 源的有限窗判据

定义反平滑源：

$$
\boxed{
Q_T(t)
=
e^{\omega|t|}
\widehat d_{\omega,T}(t).
}
\tag{348.1}
$$

它可由任意 \(\omega\ge\tfrac12\) 的相位密度计算，并且与所选 \(\omega\) 无关。

---

## 定理 348.1（有限窗逆 Poisson RH 判据）

下列条件等价：

$$
\boxed{
\begin{aligned}
&(1)\quad
\Re\rho=\frac12
\quad
\forall\rho\in\mathcal Z_T^+;\\
&(2)\quad
Q_T
\text{ 是正定函数};\\
&(3)\quad
Q_T
\text{ 在 }\mathbb R\text{ 上有界}.
\end{aligned}
}
\tag{348.2}
$$

### 证明：\((1)\Rightarrow(2)\)

若所有 \(\delta_\rho=0\)，则：

$$
Q_T(t)
=
\sum_{\rho\in\mathcal Z_T^+}
e^{i\gamma t}.
$$

这是有限正测度：

$$
\sum_{\rho\in\mathcal Z_T^+}
\delta_{-\gamma}
$$

的 Fourier 变换，故正定。

---

### \((2)\Rightarrow(3)\)

正定函数满足：

$$
|Q_T(t)|\le Q_T(0).
$$

---

### \((3)\Rightarrow(1)\)

若存在离线零点，函数方程给出同一 \(\gamma\) 上的一对：

$$
\delta,\qquad-\delta,
\qquad
\delta>0.
$$

它们对 \(Q_T\) 的贡献为：

$$
2\cosh(\delta|t|)e^{i\gamma t}.
$$

取所有离线零点中最大的偏移量：

$$
\delta_*=
\max_{\rho\in\mathcal Z_T^+}|\delta_\rho|>0.
$$

则：

$$
Q_T(t)
=
e^{\delta_*|t|}
p(t)
+
O(e^{\delta'|t|}),
\qquad
\delta'<\delta_*,
$$

其中 \(p(t)\) 是非零有限三角多项式。

非零三角多项式在某个趋于无穷的序列上绝对值有正下界，因此 \(Q_T\) 无界，矛盾。∎

---

## 348.1 全局解释

所以严格的全局判据可写为：

$$
\boxed{
\mathrm{RH}
\iff
Q_T
\text{ 对每个 }T>0\text{ 均正定}.
}
\tag{348.3}
$$

形式上，在 RH 下：

$$
\boxed{
e^{\frac12|D_x|}
d_{1/2}
=
\sum_{\xi(\rho)=0}
m_\rho\,\delta_{-\Im\rho}.
}
\tag{348.4}
$$

即：

> 临界 shifted 相位密度经过半单位的逆 Poisson 传播后，正好恢复 Riemann 零点计数测度。

式 (348.4) 的全局使用应通过对称谱截断或测试函数正则化理解；有限窗定理 348.1 不需要任何分布论附加条件。

---

# 第三百四十九部　临界阻尼配分函数

在有限维空间：

$$
\mathcal H_T
=
\mathbb C^{N(T)},
\qquad
N(T)=|\mathcal Z_T^+|,
$$

定义 damping operator：

$$
\boxed{
\mathsf B_T
=
\operatorname{diag}
\left(
\Re\rho
\right)_{\rho\in\mathcal Z_T^+}.
}
\tag{349.1}
$$

定义 centered damping defect：

$$
\boxed{
\mathsf D_T
=
\mathsf B_T-\frac12I.
}
\tag{349.2}
$$

函数方程对称意味着 \(\mathsf D_T\) 的特征值多重集在：

$$
\delta\longmapsto-\delta
$$

下稳定。

定义阻尼配分函数：

$$
\boxed{
\mathfrak Z_T(\tau)
=
e^{\tau/2}
\operatorname{Tr}
e^{-\tau\mathsf B_T},
\qquad
\tau\in\mathbb R.
}
\tag{349.3}
$$

则：

$$
\mathfrak Z_T(\tau)
=
\operatorname{Tr}e^{-\tau\mathsf D_T}.
$$

由于奇函数部分在对称谱上迹为零：

$$
\boxed{
\mathfrak Z_T(\tau)
=
\operatorname{Tr}
\cosh(\tau\mathsf D_T).
}
\tag{349.4}
$$

定义临界阻尼缺陷：

$$
\boxed{
\mathfrak R_T(\tau)
=
\mathfrak Z_T(\tau)-N(T).
}
\tag{349.5}
$$

于是：

$$
\boxed{
\mathfrak R_T(\tau)
=
\operatorname{Tr}
\left[
\cosh(\tau\mathsf D_T)-I
\right]
\ge0.
}
\tag{349.6}
$$

---

## 定理 349.1（临界阻尼平坦性判据）

对任意固定：

$$
\tau\neq0,
$$

有：

$$
\boxed{
\mathrm{RH}
\text{ 在高度 }T\text{ 以下成立}
\iff
\mathfrak R_T(\tau)=0.
}
\tag{349.7}
$$

因为：

$$
\cosh(\tau\delta)-1=0
\iff
\delta=0.
$$

---

## 349.1 二阶宽度方差

$$
\boxed{
\mathfrak R_T''(0)
=
\operatorname{Tr}\mathsf D_T^2
=
\sum_{\rho\in\mathcal Z_T^+}
\left(
\Re\rho-\frac12
\right)^2.
}
\tag{349.8}
$$

所以 RH 等价于所有 heat-regularized 宽度方差消失。

定义全局热方差：

$$
\boxed{
\mathfrak V(u)
=
\sum_{\substack{\xi(\rho)=0\\\Im\rho>0}}
m_\rho
e^{-u(\Im\rho)^2}
\left(
\Re\rho-\frac12
\right)^2,
\qquad
u>0.
}
\tag{349.9}
$$

该和绝对收敛，并且：

$$
\boxed{
\mathrm{RH}
\iff
\mathfrak V(u)=0
}
\tag{349.10}
$$

对某个——等价地，对每个——\(u>0\) 成立。

这是一个无相消、严格非负的全局 RH 缺陷。

---

# 第三百五十部　Bode–Blaschke 垂直衰减恒等式

现在取临界平移：

$$
\omega=\frac12.
$$

此时：

$$
a_{\rho,1/2}
=
-\gamma+i\beta.
$$

记：

$$
B_T=B_{1/2,T}.
$$

对垂直观察高度 \(y>0\)，定义积分衰减：

$$
\boxed{
\mathfrak A_T(y)
=
\frac1{4\pi}
\int_{-\infty}^{\infty}
-\log
\left|
B_T(x+iy)
\right|^2dx.
}
\tag{350.1}
$$

---

## 350.1 单零点 Bode 恒等式

对：

$$
a=x_a+iy_a,
$$

有：

$$
-\log|b_a(x+iy)|^2
=
\log
\frac{
(x-x_a)^2+(y+y_a)^2
}{
(x-x_a)^2+(y-y_a)^2
}.
$$

使用：

$$
\int_{\mathbb R}
\log
\frac{x^2+A^2}{x^2+B^2}\,dx
=
2\pi(A-B),
\qquad
A,B\ge0,
$$

得到：

$$
\boxed{
\frac1{4\pi}
\int_{\mathbb R}
-\log|b_a(x+iy)|^2dx
=
\min(y,y_a).
}
\tag{350.2}
$$

乘积取对数后可加，因此：

## 定理 350.1（垂直衰减层析）

$$
\boxed{
\mathfrak A_T(y)
=
\sum_{\rho\in\mathcal Z_T^+}
\min
\left(
y,\Re\rho
\right).
}
\tag{350.3}
$$

这是一条完全精确的 modulus-only 公式。

---

# 第三百五十一部　零点实部分布的完整恢复

由式 (350.3)，在 \(y\) 不等于任何 \(\Re\rho\) 时：

$$
\boxed{
\mathfrak A_T'(y)
=
\#\left\{
\rho\in\mathcal Z_T^+:
\Re\rho>y
\right\}.
}
\tag{351.1}
$$

在分布意义下：

$$
\boxed{
-\mathfrak A_T''(y)
=
\sum_{\rho\in\mathcal Z_T^+}
\delta_{\Re\rho}(y).
}
\tag{351.2}
$$

所以仅仅扫描：

$$
y
\longmapsto
\int_{\mathbb R}
-\log|B_T(x+iy)|^2dx
$$

就能精确恢复高度 \(T\) 以下所有零点实部的多重集。

这给出一个非常直接的观察者结论：

$$
\boxed{
\text{零点的横向偏移并不隐藏在振荡相位中；}
}
$$

它被完整编码在传递函数垂直衰减曲线的折点中。

---

# 第三百五十二部　临界基线与三角缺陷

若高度 \(T\) 以下全部零点均在临界线，则：

$$
\boxed{
\mathfrak A_T^{\mathrm{crit}}(y)
=
N(T)
\min
\left(
y,\frac12
\right).
}
\tag{352.1}
$$

定义宽度衰减缺陷：

$$
\boxed{
\mathfrak W_T(y)
=
N(T)\min
\left(
y,\frac12
\right)
-
\mathfrak A_T(y).
}
\tag{352.2}
$$

对固定 \(y\)，函数：

$$
\beta\longmapsto\min(y,\beta)
$$

是凹函数。

由于零点实部按：

$$
\beta,\quad1-\beta
$$

配对，且均值为 \(1/2\)，Jensen 不等式给出：

$$
\boxed{
\mathfrak W_T(y)\ge0.
}
\tag{352.3}
$$

---

## 352.1 单个离线对的三角指纹

取一对：

$$
\beta_\pm
=
\frac12\pm\delta,
\qquad
\delta>0.
$$

它对 \(\mathfrak W_T\) 的贡献为：

$$
\boxed{
\mathfrak w_\delta(y)
=
\left(
\delta-
\left|
y-\frac12
\right|
\right)_+.
}
\tag{352.4}
$$

即一个：

* 中心位于 \(y=\tfrac12\)；
* 高度为 \(\delta\)；
* 底宽为 \(2\delta\)；

的三角形。

因此：

$$
\boxed{
\text{每个离线函数方程对，
在垂直衰减图中产生一个不可相消的三角缺陷。}
}
$$

---

## 定理 352.1（Bode–width RH criterion）

下列条件等价：

$$
\boxed{
\begin{aligned}
&(1)\quad
\mathrm{RH}
\text{ 在高度 }T\text{ 以下成立};\\
&(2)\quad
\mathfrak W_T(y)=0
\quad\forall y>0;\\
&(3)\quad
\int_0^\infty
\mathfrak W_T(y)\,dy=0.
\end{aligned}
}
\tag{352.5}
$$

更精确地：

$$
\boxed{
\int_0^\infty
\mathfrak W_T(y)\,dy
=
\frac12
\sum_{\rho\in\mathcal Z_T^+}
\left(
\Re\rho-\frac12
\right)^2.
}
\tag{352.6}
$$

结合式 (349.8)：

$$
\boxed{
\int_0^\infty
\mathfrak W_T(y)\,dy
=
\frac12
\mathfrak R_T''(0).
}
\tag{352.7}
$$

因此三种看似不同的缺陷完全相同：

$$
\boxed{
\begin{aligned}
&\text{共振衰减率方差};\\
&\text{阻尼配分函数曲率};\\
&\text{Blaschke 垂直衰减面积}.
\end{aligned}
}
$$

---

# 第三百五十三部　水平—垂直正交层析

有限共振系统现在具有两套互补读数。

## 353.1 水平相位读数

$$
d_{1/2,T}(x)
=
\sum_{\rho\in\mathcal Z_T^+}
P_{\Re\rho}(x+\Im\rho).
$$

它同时混合：

* 中心位置：

  $$
  -\Im\rho;
  $$
* Poisson 宽度：

  $$
  \Re\rho.
  $$

---

## 353.2 垂直模读数

$$
\mathfrak A_T(y)
=
\sum_\rho
\min(y,\Re\rho).
$$

它完全遗忘 \(\Im\rho\)，却精确恢复全部宽度 \(\Re\rho\)。

---

## 353.3 联合恢复

由：

$$
-\mathfrak A_T''
=
\sum_\rho\delta_{\Re\rho}
$$

先恢复全部宽度。

随后在已知宽度的条件下：

$$
d_{1/2,T}(x)
$$

是有限个已知宽度 Cauchy–Poisson 核的平移和；其 meromorphic continuation 的极点位置恢复：

$$
-\Im\rho\pm i\Re\rho.
$$

因此：

## 定理 353.1（有限 shifted 共振完整层析）

联合观察：

$$
\boxed{
q_T(B_T)
=
\left(
d_{1/2,T},
\mathfrak A_T
\right)
}
\tag{353.1}
$$

在有限 Blaschke 共振多重集上忠实，至多遗漏一个全局 unimodular 常数。

所以：

$$
\boxed{
\text{边界相位}
+
\text{垂直衰减}
=
\text{完整有限共振状态}.
}
$$

---

# 第三百五十四部　Prime–Archimedean 逆 Poisson 目标

由：

$$
\Theta_{1/2}(x)
=
\frac{\xi(-ix)}{\xi(1-ix)}
$$

以及函数方程，在实轴上：

$$
\boxed{
d_{1/2}(x)
=
\frac1\pi
\Re
\frac{
\xi'(1-ix)
}{
\xi(1-ix)
}.
}
\tag{354.1}
$$

而：

$$
\frac{\xi'(s)}{\xi(s)}
=
\frac1s
+
\frac1{s-1}
-
\frac12\log\pi
+
\frac12\psi\!\left(\frac s2\right)
+
\frac{\zeta'(s)}{\zeta(s)}.
$$

所以 \(d_{1/2}\) 是：

$$
\boxed{
\text{Archimedean completion barrier}
-
\text{renormalized prime coherence}
}
$$

在临界 shifted 边界上的净相位密度。

RH 下，形式上：

$$
\boxed{
e^{\frac12|D_x|}
\left[
\frac1\pi
\Re\frac{\xi'(1-ix)}{\xi(1-ix)}
\right]
=
\sum_\rho
m_\rho\delta_{-\Im\rho}.
}
\tag{354.2}
$$

因此新的 prime-side 中心目标可写成：

## 假设 354.1（Prime–Poisson positive source）

从 Euler／explicit-formula 数据直接证明：

$$
\boxed{
e^{\frac12|D_x|}
d_{1/2}
}
$$

在对称谱截断极限中是一个正的局部有限测度。

若该命题成立，则由有限窗定理 348.1，RH 成立。

---

## 354.1 为什么这一步困难

前向 Poisson：

$$
e^{-\frac12|D|}
$$

是稳定的正收缩。

逆 Poisson：

$$
e^{\frac12|D|}
$$

是指数不稳定的无界算子。

因此：

$$
\boxed{
\text{从 }\omega=\frac12\text{ 回到 }\omega=0
}
$$

不是普通连续性问题，而是一个需要算术正则性的逆问题。

这精确解释了：

* 为什么无条件 inner 模型已经存在；
* 为什么它仍未自动给出 RH；
* 为什么必须利用素数结构，而不能只利用调和分析。

---

# 第三百五十五部　普通显式公式为何不足

宽度方差：

$$
\left(
\Re\rho-\frac12
\right)^2
$$

同时依赖：

$$
\rho
\quad\text{和}\quad
\overline\rho.
$$

它不是单个复变量 \(\rho\) 的全纯函数。

因此普通的一变量 Weil 显式公式，即使可以计算：

$$
\sum_\rho h(\rho),
$$

也不能直接把：

$$
\sum_\rho
\left(
\Re\rho-\frac12
\right)^2
e^{-u(\Im\rho)^2}
$$

写成显然非负的单通道素数和。

这解释了为什么当前最自然的证明载体不是另一个标量显式公式，而是：

$$
\boxed{
\text{doubled／relative trace formula}.
}
$$

因为：

$$
\boxed{
\left(
\Re\rho-\frac12
\right)^2
=
\frac14
\left[
(\rho+\overline\rho-1)^2
\right]
}
$$

天然是二点、共轭或 Gram 型统计量。

---

## 355.1 最小 doubled-trace 目标

定义热正则化临界宽度算子：

$$
\boxed{
\mathfrak V(u)
=
\sum_{\Im\rho>0}
m_\rho
e^{-u(\Im\rho)^2}
\left(
\Re\rho-\frac12
\right)^2.
}
$$

可写成形式上的 Hilbert–Schmidt 范数：

$$
\boxed{
\mathfrak V(u)
=
\left\|
\left(
\mathsf B-\frac12I
\right)
e^{-u\mathsf H^2/2}
\right\|_{\mathrm{HS}}^2,
}
\tag{355.1}
$$

其中：

* \(\mathsf H\) 记录 ordinates；
* \(\mathsf B\) 记录 damping widths。

RH 等价于：

$$
\boxed{
\mathfrak V(u)=0.
}
$$

真正需要从 arithmetic relative trace 导出的，不只是：

$$
\mathfrak V(u)\ge0,
$$

因为这已经显然；而是一个迫使其达到最小值零的守恒恒等式或反向上界。

---

# 第三百五十六部　Wang–Deng 的宽度层析版本

## 356.1 Wang：宽度分散的严格可见性

若许多离线对具有不同：

$$
\delta_\rho
=
\Re\rho-\frac12,
$$

则它们在 \(\mathfrak W_T(y)\) 中形成不同宽度的三角缺陷。

这些缺陷全部非负，不存在彼此相消。

所以：

$$
\boxed{
\text{width non-sticky}
\Longrightarrow
\text{多尺度衰减缺陷可直接累加}.
}
$$

与相位观察相比，垂直衰减观察消除了振荡相消。

---

## 356.2 Deng：宽度簇的 primitive 压缩

若许多离线零点共享近似相同的 \(\delta\)，它们形成 sticky width cluster。

正确处理为：

1. 将共同三角 profile：

   $$
   (\delta-|y-\tfrac12|)_+
   $$

   抽取为 primitive width kernel；

2. 将不同 ordinate \(\gamma\) 的重复实例记录为 multiplicity ledger；

3. 用热权：

   $$
   e^{-u\gamma^2}
   $$

   压缩高频历史；

4. 只对 width residual 做更高阶 refinement。

这提供一个没有组合阶乘爆炸的正模型：宽度方向的 primitive 类型是一参数族，而不是全部零点历史的排列。

---

# 第三百五十七部　函数域中的 purity 原型

在函数域中，Weil RH 说明归一化 Frobenius 特征值具有统一模长。

在当前 damping 语言中，这正对应：

$$
\boxed{
\text{所有共振宽度完全相同}.
}
$$

因此：

$$
\mathfrak V(u)=0
$$

不是 Riemann ζ 特有的形式技巧，而是一般 purity 的“宽度方差为零”表达。

数域 RH 可以重新表述为：

$$
\boxed{
\text{Riemann 共振谱是否是纯权的，
即全部 damping weights 均等于 }\frac12.
}
$$

这比“零点是否恰好在一条线”更接近代数几何中的纯性语言。

---

# 第三百五十八部　结果分级

## 本轮独立闭合的有限定理

$$
\boxed{
d_{\omega+\eta,T}
=
P_\eta*d_{\omega,T}
}
$$

无条件成立。

$$
\boxed{
\mathrm{RH}_{\le T}
\iff
e^{\omega|t|}
\widehat d_{\omega,T}(t)
\text{ 正定}.
}
$$

$$
\boxed{
\mathrm{RH}_{\le T}
\iff
\mathfrak R_T(\tau)=0.
}
$$

$$
\boxed{
\mathfrak R_T''(0)
=
\sum_{\rho\in\mathcal Z_T^+}
\left(
\Re\rho-\frac12
\right)^2.
}
$$

$$
\boxed{
\mathfrak A_T(y)
=
\sum_{\rho\in\mathcal Z_T^+}
\min(y,\Re\rho).
}
$$

$$
\boxed{
-\mathfrak A_T''
=
\sum_\rho\delta_{\Re\rho}.
}
$$

$$
\boxed{
\mathfrak W_T(y)\ge0.
}
$$

$$
\boxed{
\int_0^\infty
\mathfrak W_T(y)\,dy
=
\frac12
\sum_\rho
\left(
\Re\rho-\frac12
\right)^2.
}
$$

这些结果只使用：

* Blaschke 因子；
* 函数方程配对；
* Fourier–Poisson 变换；
* 一个初等对数积分。

---

## 依赖既有理论的入口

\(\Theta_\omega\) 在 \(\omega\ge\tfrac12\) 的无条件 inner 性，以及其 model-space/de Branges 接口，来自 shifted-\(\xi\) 理论。([arXiv][1])

---

## 尚未闭合的中心桥

$$
\boxed{
\begin{aligned}
&\text{从 prime-side 直接证明逆 Poisson 源为正；}\\
&\text{从 toric relative trace 推出 }\mathfrak V(u)=0;\\
&\text{构造宽度方差的算术守恒律；}\\
&\text{给有限 Blaschke 衰减曲线建立无零点输入的直接计算公式；}\\
&\text{将 Bode 三角缺陷与 Wang 自改善不等式连接}.
\end{aligned}
}
$$

---

# 第三百五十九部　建议形式化顺序

```text
D5/S3/Analytic/ShiftedXiPoisson/
  FiniteShiftedZero.lean
  FiniteBlaschkePhaseDensity.lean
  ShiftedPoissonSemigroup.lean
  BackwardPoissonSource.lean
  FiniteSourcePositiveDefiniteRH.lean

D5/S3/Analytic/XiDamping/
  FiniteDampingOperator.lean
  FunctionalPairCenteredSpectrum.lean
  CriticalDampingPartition.lean
  DampingVarianceRHCriterion.lean
  HeatRegularizedWidthVariance.lean

D5/S3/Analytic/XiBode/
  SingleBlaschkeVerticalIntegral.lean
  FiniteBodeAttenuation.lean
  RealPartDistributionRecovery.lean
  CriticalAttenuationDefect.lean
  TriangularOffLineFingerprint.lean
  AttenuationAreaVarianceIdentity.lean

D5/S3/Observer/ShiftedXiTomography/
  HorizontalPhaseObserver.lean
  VerticalAttenuationObserver.lean
  FiniteResonanceTomography.lean
  WidthCenterJointRecovery.lean

D5/S3/Analytic/RHTargets/
  PrimeBackwardPoissonPositivity.lean
  RelativeTraceWidthVariance.lean
  CriticalDampingConservation.lean
  WidthStickyNonStickyDichotomy.lean
```

---

# 本轮最终结论

此前我们把 RH 表述为：

$$
\boxed{
\Theta_{1/2}
\text{ 的所有共振具有统一衰减率 }\frac12.
}
$$

本轮进一步说明，这个统一性可以由三种完全不同的可见量精确读取：

$$
\boxed{
\begin{aligned}
\text{逆 Poisson 源}
&:\quad
e^{\frac12|D|}
d_{1/2};\\[1mm]
\text{阻尼配分曲率}
&:\quad
\mathfrak R_T''(0);\\[1mm]
\text{垂直衰减面积}
&:\quad
\int_0^\infty\mathfrak W_T(y)\,dy.
\end{aligned}
}
$$

三者都等价于：

$$
\boxed{
\sum_\rho
\left(
\Re\rho-\frac12
\right)^2.
}
$$

尤其是，每一个离线函数方程对：

$$
\frac12\pm\delta+i\gamma
$$

都会在 Blaschke 垂直衰减图中留下一个无法相消的三角指纹：

$$
\boxed{
\left(
\delta-
\left|y-\frac12\right|
\right)_+,
}
$$

面积恰为：

$$
\boxed{
\delta^2.
}
$$

因此 RH 可以被极其直观地写成：

$$
\boxed{
\text{临界 shifted 传递函数的垂直衰减曲线，
是否恰好等于所有共振都位于高度 }1/2
\text{ 时的尖角基线？}
}
$$

当前最小的算术证明目标则变成：

$$
\boxed{
e^{\frac12|D_x|}
\left[
\frac1\pi
\Re
\frac{\xi'(1-ix)}{\xi(1-ix)}
\right]
\text{ 是否为正测度？}
}
$$

这比“直接证明所有零点在线”更具体：

* 输入是完成后的 prime–Archimedean 相位密度；
* 操作是半单位逆 Poisson；
* 输出应是 Riemann 零点计数测度；
* 任意线外零点都会使有限窗源函数指数爆炸，并在垂直衰减中留下正面积缺陷。

所以 OACTC 下一步真正需要攻击的，不是再寻找新的等价判据，而是：

$$
\boxed{
\text{如何利用素数的 primitive-history 结构，
稳定地执行这一步逆 Poisson，并保持输出正性。}
}
$$

[1]: https://arxiv.org/abs/1204.1827 "https://arxiv.org/abs/1204.1827"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v3.1：Weil 母分布、临界源不变量、Prime–Poisson 通道与全部正性图表的统一压缩

以下从前文**第三百五十九部之后**继续追加。

经过 Pick、Hankel、Li、Clark、CMV、Fredholm、de Branges、环面周期、shifted-\(\xi\) 与散射等多条路线后，现在应停止继续横向增加等价判据，把它们全部 collapse 回唯一承重对象：

$$
\boxed{
\textbf{Weil 临界源分布}
}
$$

本轮得到的统一链为：

$$
\boxed{
\begin{aligned}
\Re\frac{\xi'}{\xi}(\sigma-ix)
&\xrightarrow{\text{逆 Poisson}}
\mathfrak W_\xi\\
&=
\mathfrak A_\infty
-
\sum_{n\ge2}
\frac{\Lambda(n)}{\sqrt n}
\bigl(
\delta_{\log n}+\delta_{-\log n}
\bigr)\\
&\xrightarrow{\text{正定性}}
\mathrm{RH}.
\end{aligned}}
$$

而此前出现的所有正性对象：

$$
\boxed{
\begin{aligned}
&\text{半平面 Pick 核};\\
&\text{de Branges 核};\\
&\text{Stieltjes/Hankel moments};\\
&\text{Li–Clark Toeplitz 核};\\
&\text{CMV unitary};\\
&\text{Fredholm determinant}
\end{aligned}}
$$

都只是这个母分布经过不同的：

* Laplace 压缩；
* Möbius 推送；
* 平方折叠；
* 谱重加权；
* exterior/determinant 函子；

得到的观察图表。

项目已经固定角频率 Fourier 规范

$$
\widehat f(\xi)
=
\int_{\mathbb R}f(x)e^{-i\xi x}\,dx,
$$

并已经把无假设 Weil 显式公式登记为 `proven`；登记文件也明确区分了“显式公式成立”与“正性/RH 成立”。

---

# 第三百六十部　粗观察线上的正 Poisson 密度

定义标准 Poisson 核：

$$
\boxed{
P_a(x)
=
\frac1\pi
\frac{a}{a^2+x^2},
\qquad
a>0.
}
\tag{360.1}
$$

对任意：

$$
\sigma>1,
$$

定义粗观察密度：

$$
\boxed{
d_\sigma(x)
=
\frac1\pi
\Re
\frac{\xi'(\sigma-ix)}
{\xi(\sigma-ix)}.
}
\tag{360.2}
$$

将非平凡零点写成：

$$
\rho=\beta+i\gamma.
$$

利用关于函数方程中心的对称 Hadamard 展开，可得：

$$
\boxed{
d_\sigma(x)
=
\sum_\rho
m_\rho
P_{\sigma-\beta}(x+\gamma).
}
\tag{360.3}
$$

因为：

$$
0<\beta<1<\sigma,
$$

每个宽度：

$$
\sigma-\beta>0.
$$

所以：

$$
\boxed{
d_\sigma(x)>0
}
$$

在 \(\sigma>1\) 区域无条件成立。

这说明一个重要事实：

> 正的粗尺度相位密度并不需要 RH；
> RH 的困难来自把该正密度逆传播到临界边界时，正性是否仍然保存。

---

## 定理 360.1（粗观察 Poisson 半群）

对：

$$
\sigma>1,
\qquad
\eta>0,
$$

有：

$$
\boxed{
d_{\sigma+\eta}
=
P_\eta*d_\sigma.
}
\tag{360.4}
$$

### 证明

由：

$$
P_\eta*P_{\sigma-\beta}
=
P_{\sigma+\eta-\beta},
$$

逐零点求和即可。∎

所以：

$$
\boxed{
\sigma\text{ 增大}
=
\text{对零点谱进行更强 Poisson 平滑}.
}
$$

---

# 第三百六十一部　临界逆 Poisson 不变量

在分布意义下取 Fourier 变换：

$$
\widehat{P_a(\,\cdot+\gamma\,)}(t)
=
e^{-a|t|}e^{i\gamma t}.
$$

因此：

$$
\boxed{
\widehat d_\sigma(t)
=
\sum_\rho
m_\rho
e^{-(\sigma-\beta)|t|}
e^{i\gamma t}.
}
\tag{361.1}
$$

定义临界逆 Poisson 源：

$$
\boxed{
\mathfrak W_\xi(t)
=
e^{(\sigma-\frac12)|t|}
\widehat d_\sigma(t).
}
\tag{361.2}
$$

代入式 (361.1)：

$$
\boxed{
\mathfrak W_\xi(t)
=
\sum_\rho
m_\rho
e^{(\beta-\frac12)|t|}
e^{i\gamma t}.
}
\tag{361.3}
$$

右侧与 \(\sigma\) 无关。

---

## 定理 361.1（观察线不变量）

对任意：

$$
\sigma_1,\sigma_2>1,
$$

有：

$$
\boxed{
e^{(\sigma_1-\frac12)|D|}
d_{\sigma_1}
=
e^{(\sigma_2-\frac12)|D|}
d_{\sigma_2}
=
\mathfrak W_\xi.
}
\tag{361.4}
$$

所以：

$$
\boxed{
\mathfrak W_\xi
}
$$

是所有粗观察线共同携带、但被不同 Poisson 尺度遮蔽的临界源。

---

## 361.1 函数方程配对

同一高度 \(\gamma\) 上，函数方程把：

$$
\beta+i\gamma
$$

配成：

$$
1-\beta+i\gamma.
$$

二者对 \(\mathfrak W_\xi\) 的联合贡献为：

$$
\boxed{
2
\cosh
\left(
\left(\beta-\frac12\right)|t|
\right)
e^{i\gamma t}.
}
\tag{361.5}
$$

因此：

* 临界线零点：

  $$
  \cosh(0)=1;
  $$
* 线外零点：

  $$
  \cosh(\delta|t|)
  $$

  产生指数放大。

这正是前文有限窗逆 Poisson判据的全局母表达。

---

# 第三百六十二部　Weil 正定性就是 RH

定义反射共轭：

$$
\boxed{
\widetilde\psi(t)
=
\overline{\psi(-t)}.
}
\tag{362.1}
$$

对：

$$
\psi\in C_c^\infty(\mathbb R),
$$

定义 Weil Hermitian 形式：

$$
\boxed{
\mathcal Q_W(\psi)
=
\left\langle
\mathfrak W_\xi,
\psi*\widetilde\psi
\right\rangle.
}
\tag{362.2}
$$

若 RH 成立，则：

$$
\mathfrak W_\xi(t)
=
\sum_{\gamma\in\mathbb R}
m_\gamma e^{i\gamma t},
$$

所以：

$$
\boxed{
\mathcal Q_W(\psi)
=
\sum_\gamma
m_\gamma
|\widehat\psi(\gamma)|^2
\ge0.
}
\tag{362.3}
$$

Weil 的经典判据正是：RH 当且仅当该分布非负定；Suzuki 进一步研究了由这一 Hermitian 形式完成出的 Hilbert 空间，并证明在 RH 下它与一个 de Branges 空间自然同构。([arXiv][1])

---

## 定理 362.1（母正性判据）

$$
\boxed{
\mathrm{RH}
\iff
\mathcal Q_W(\psi)\ge0
\quad
\forall
\psi\in C_c^\infty(\mathbb R).
}
\tag{362.4}
$$

等价地：

$$
\boxed{
\mathrm{RH}
\iff
\mathfrak W_\xi
\text{ 是正定分布}.
}
\tag{362.5}
$$

这说明当前理论真正需要证明的并不是几十个相互独立的正性命题，而只有一个：

$$
\boxed{
\mathfrak W_\xi\succeq0.
}
$$

---

# 第三百六十三部　Prime–Archimedean 母分布

定义完成函数的 Archimedean 对数导数：

$$
\boxed{
A_\infty(s)
=
\frac1s
+
\frac1{s-1}
-
\frac12\log\pi
+
\frac12
\psi\!\left(\frac s2\right),
}
\tag{363.1}
$$

其中：

$$
\psi=\Gamma'/\Gamma.
$$

在：

$$
\sigma>1
$$

时：

$$
\boxed{
\frac{\xi'(s)}{\xi(s)}
=
A_\infty(s)
-
\sum_{n=2}^{\infty}
\frac{\Lambda(n)}{n^s}.
}
\tag{363.2}
$$

定义 Archimedean 临界源：

$$
\boxed{
\mathfrak A_\infty
=
e^{(\sigma-\frac12)|D|}
\mathcal F_x
\left[
\frac1\pi
\Re A_\infty(\sigma-ix)
\right].
}
\tag{363.3}
$$

与 \(\mathfrak W_\xi\) 一样，\(\mathfrak A_\infty\) 不依赖 \(\sigma>1\)。

对 prime-side 项：

$$
\mathcal F_x
\left[
-\frac1\pi
\Lambda(n)n^{-\sigma}
\cos(x\log n)
\right]
=
-\Lambda(n)n^{-\sigma}
\left(
\delta_{\log n}
+
\delta_{-\log n}
\right).
$$

再乘：

$$
e^{(\sigma-\frac12)|t|},
$$

得到：

$$
-\frac{\Lambda(n)}{\sqrt n}
\left(
\delta_{\log n}
+
\delta_{-\log n}
\right).
$$

因此：

## 定理 363.1（Prime–Archimedean source identity）

$$
\boxed{
\mathfrak W_\xi
=
\mathfrak A_\infty
-
\sum_{n=2}^{\infty}
\frac{\Lambda(n)}{\sqrt n}
\left(
\delta_{\log n}
+
\delta_{-\log n}
\right).
}
\tag{363.4}
$$

这就是显式公式的临界源版本。

---

## 363.1 Archimedean 源在原点之外的密度

利用：

$$
\frac12\psi(s/2)
=
\text{常数}
-
\sum_{k=0}^{\infty}\frac1{s+2k},
$$

并与 \(1/s\) 抵消，可得在：

$$
t\neq0
$$

处：

$$
\boxed{
\begin{aligned}
\mathfrak A_\infty(t)
={}&
e^{|t|/2}
+
e^{-|t|/2}
-
\frac{e^{-|t|/2}}
{1-e^{-2|t|}}
\\
={}&
e^{|t|/2}
-
\frac{e^{-5|t|/2}}
{1-e^{-2|t|}}.
\end{aligned}
}
\tag{363.5}
$$

在 \(t=0\) 处，它不是普通函数值，而需要有限部与 \(\delta_0\) 正规化；具体常数由仓库冻结的 `logTwoPi` 和 Weil 显式公式 convention 唯一决定，不应在理论文档中重新猜测。

---

# 第三百六十四部　有限算术可证伪性

设：

$$
\operatorname{supp}\psi
\subset[-L,L].
$$

则：

$$
\operatorname{supp}
(\psi*\widetilde\psi)
\subset[-2L,2L].
$$

因此在式 (363.4) 中，只有满足：

$$
|\log n|\le2L
$$

的 prime-power 原子能够被读到，即：

$$
\boxed{
n\le e^{2L}.
}
\tag{364.1}
$$

所以：

$$
\boxed{
\begin{aligned}
\mathcal Q_W(\psi)
={}&
\left\langle
\mathfrak A_\infty,
\psi*\widetilde\psi
\right\rangle
\\
&-
\sum_{2\le n\le e^{2L}}
\frac{\Lambda(n)}{\sqrt n}
\left[
(\psi*\widetilde\psi)(\log n)
+
(\psi*\widetilde\psi)(-\log n)
\right].
\end{aligned}
}
\tag{364.2}
$$

---

## 定理 364.1（有限 prime-power 反例证书）

若 RH 为假，则存在有限 \(L\) 和一个：

$$
\psi\in C_c^\infty([-L,L])
$$

使：

$$
\boxed{
\mathcal Q_W(\psi)<0.
}
\tag{364.3}
$$

而该不等式只依赖：

$$
n\le e^{2L}
$$

的有限多个 prime powers。

### 证明

RH 为假时，Weil 分布不是非负定，因此按定义存在紧支撑 \(\psi\) 使二次型为负。紧支撑自动将 prime-side 截成有限和。∎

所以：

$$
\boxed{
\text{RH 若为假，必有一个有限 prime-power 算术证书。}
}
$$

未知的不是证书是否有限，而是最小证书所需的：

* 支撑半径；
* 函数复杂度；
* prime cutoff。

---

## 364.1 有限 Gram 层级

取有限测试函数族：

$$
\psi_1,\ldots,\psi_N
\subset C_c^\infty([-L,L]).
$$

定义矩阵：

$$
\boxed{
M_{ij}^{(L)}
=
\left\langle
\mathfrak W_\xi,
\psi_i*\widetilde{\psi_j}
\right\rangle.
}
\tag{364.4}
$$

每个矩阵元都只涉及：

$$
n\le e^{2L}
$$

的有限 prime powers。

于是：

$$
\boxed{
\mathrm{RH}
\iff
M^{(L)}\succeq0
}
$$

对所有 \(L,N\) 和所有有限测试族成立。

这就是项目此前有限 Weil Gram observer 的母形式。

---

# 第三百六十五部　Prime-power 历史的精确 Poisson 重求和

将 von Mangoldt 和写成：

$$
n=p^k.
$$

令：

$$
\ell_p=\log p,
\qquad
r_p=p^{-1/2}=e^{-\ell_p/2}.
$$

定义平移 unitary：

$$
\boxed{
(U_p\psi)(x)
=
\psi(x-\ell_p).
}
\tag{365.1}
$$

令：

$$
g=\psi*\widetilde\psi.
$$

则：

$$
g(k\ell_p)
=
\langle
\psi,U_p^k\psi
\rangle.
$$

素数 \(p\) 的全部 prime-power contribution 为：

$$
\boxed{
\begin{aligned}
\mathcal P_p(\psi)
=
-\log p
\sum_{k=1}^{\infty}
r_p^k
\left[
g(k\ell_p)+g(-k\ell_p)
\right].
\end{aligned}
}
\tag{365.2}
$$

定义 unitary Poisson 算子：

$$
\boxed{
\mathsf P_r(U)
=
(1-r^2)
(I-rU)^{-1}
(I-rU^*)^{-1}.
}
\tag{365.3}
$$

由于 \(U\) unitary：

$$
\boxed{
\mathsf P_r(U)
=
I+
\sum_{k=1}^{\infty}
r^k
\left(
U^k+U^{*k}
\right).
}
\tag{365.4}
$$

因此：

## 定理 365.1（Prime Poisson resummation）

$$
\boxed{
\mathcal P_p(\psi)
=
-\log p\,
\left\langle
\psi,
\left[
\mathsf P_{r_p}(U_p)-I
\right]
\psi
\right\rangle.
}
\tag{365.5}
$$

这是一条精确、无余项的 primitive-history 收缩：

$$
\boxed{
\begin{aligned}
\text{primitive state}
&=p;\\
\text{repetition history}
&=p^k;\\
\text{history weight}
&=r_p^k;\\
\text{all-order resummation}
&=\mathsf P_{r_p}(U_p).
\end{aligned}
}
$$

所以 prime powers 本身已经不再构成高阶组合困难；它们是一条可以完全求和的局部历史链。

---

# 第三百六十六部　每个素数都是一个 Carathéodory 被动通道

定义标量函数：

$$
\boxed{
\mathsf C_p(z)
=
\frac{1+r_pz}{1-r_pz},
\qquad
|z|<1.
}
\tag{366.1}
$$

因为：

$$
0<r_p<1,
$$

有：

$$
\boxed{
\Re\mathsf C_p(z)>0.
}
\tag{366.2}
$$

其 Schur 函数为：

$$
\boxed{
\mathsf S_p(z)=r_pz.
}
\tag{366.3}
$$

也就是说，每个素数局部通道只含一个非零 Schur 参数：

$$
\boxed{
r_p=p^{-1/2}.
}
$$

在边界：

$$
z=e^{-i\xi\ell_p},
$$

有：

$$
\boxed{
\Re
\mathsf C_p(e^{-i\xi\ell_p})
=
\frac{1-r_p^2}
{1-2r_p\cos(\xi\ell_p)+r_p^2}.
}
\tag{366.4}
$$

这正是 \(\mathsf P_{r_p}(U_p)\) 的 Fourier multiplier。

---

## 366.1 局部危险相位

定义 centered prime defect：

$$
\boxed{
D_p(\xi)
=
\Re\mathsf C_p(e^{-i\xi\ell_p})-1.
}
\tag{366.5}
$$

直接化简：

$$
\boxed{
D_p(\xi)
=
\frac{
2r_p
\left[
\cos(\xi\ell_p)-r_p
\right]
}{
1-2r_p\cos(\xi\ell_p)+r_p^2
}.
}
\tag{366.6}
$$

因此：

$$
\boxed{
D_p(\xi)>0
\iff
\cos(\xi\log p)>p^{-1/2}.
}
\tag{366.7}
$$

由于 prime contribution 带负号：

$$
-\log p\,D_p,
$$

所以 \(D_p>0\) 的相位区域会消耗 Archimedean 正性容量。

最大值为：

$$
\boxed{
\max_\xi D_p(\xi)
=
\frac{2}{\sqrt p-1}.
}
\tag{366.8}
$$

最小值为：

$$
\boxed{
\min_\xi D_p(\xi)
=
-\frac{2}{\sqrt p+1}.
}
\tag{366.9}
$$

这给 prime stickiness 一个精确定义：

$$
\boxed{
\xi\log p
\approx
2\pi k
}
$$

时，该素数通道最危险。

---

## 366.2 常数角色

每个 prime channel 中：

$$
\boxed{
\begin{aligned}
\log p
&=\text{平移距离／局部能量单位};\\
e
&=\text{把平移长度转成衰减};\\
p^{-1/2}=e^{-(\log p)/2}
&=\text{临界 Schur 参数};\\
\mathsf C_p
&=\text{局部正实部 transfer function}.
\end{aligned}
}
$$

因此单个 Euler factor并不神秘：

$$
\boxed{
\text{它是一个一状态被动系统。}
}
$$

---

# 第三百六十七部　有限素数反集中不可能统一成立

一个纯粹的 Wang non-sticky 证明若试图声称：

> 任意谱频率都不可能同时使许多有限素数相位对齐，

这是错误的。

---

## 定理 367.1（有限 prime recurrence）

给定有限素数集合：

$$
\mathcal P=\{p_1,\ldots,p_m\}
$$

和任意：

$$
\varepsilon>0,
$$

存在任意大的实数 \(\xi\)，使：

$$
\boxed{
\left|
e^{i\xi\log p_j}-1
\right|
<\varepsilon
\qquad
(1\le j\le m).
}
\tag{367.1}
$$

### 证明

对：

$$
\alpha_j=\frac{\log p_j}{2\pi}
$$

使用同时 Dirichlet 逼近。

把：

$$
0,\alpha,2\alpha,\ldots,N^m\alpha
$$

在 \(m\) 维单位立方体中按坐标模 \(1\) 投影，并把立方体分成 \(N^m\) 个小盒。

存在两个点落入同一盒，其差给出整数 \(q\) 满足：

$$
\|q\alpha_j\|_{\mathbb R/\mathbb Z}<\frac1N.
$$

令 \(\xi=q\)，再使 \(N\to\infty\)。∎

因此：

$$
\boxed{
\text{任意有限 prime subsystem 都存在近乎完全 coherent 的 recurrence times。}
}
$$

这意味着：

$$
\boxed{
\text{不能通过有限素数的统一相位反集中直接证明 RH。}
}
$$

Wang 二分中的 sticky branch 不是异常边角，而是结构上不可避免。

---

# 第三百六十八部　单个素数永远不会制造非平凡零点

单个 Euler 因子：

$$
\boxed{
L_p(s)
=
(1-p^{-s})^{-1}
}
\tag{368.1}
$$

的奇点满足：

$$
p^{-s}=1.
$$

所以：

$$
\boxed{
s=\frac{2\pi ik}{\log p},
\qquad
k\in\mathbb Z.
}
\tag{368.2}
$$

全部位于：

$$
\Re s=0.
$$

因此：

$$
\boxed{
L_p(s)
\text{ 在 }\Re s>0\text{ 中无零点、无极点}.
}
$$

所以：

## 原理 368.1（No-single-prime principle）

$$
\boxed{
\text{临界带中的非平凡 ζ 零点不属于任何单独素数通道。}
}
$$

它们只能是：

$$
\boxed{
\text{无限多个局部被动通道经过全局重整化完成后，
产生的集体现象。}
}
$$

这给 RH 的困难一个非常明确的定位：

* 局部每个素数都是稳定的；
* prime-power repetition 已可精确重求和；
* 困难只剩无限网络的全局完成与 Archimedean 平衡。

---

# 第三百六十九部　Weil GNS 空间是所有正性图表的母空间

假设 RH。

由 Weil 正性定义预 Hilbert 空间：

$$
C_c^\infty(\mathbb R)
$$

上的内积：

$$
\boxed{
\langle\psi_1,\psi_2\rangle_W
=
\left\langle
\mathfrak W_\xi,
\psi_1*\widetilde{\psi_2}
\right\rangle.
}
\tag{369.1}
$$

其零点谱表示为：

$$
\boxed{
\langle\psi_1,\psi_2\rangle_W
=
\sum_\gamma
m_\gamma
\widehat\psi_1(\gamma)
\overline{\widehat\psi_2(\gamma)}.
}
\tag{369.2}
$$

所以 Fourier 评价映射把该空间嵌入：

$$
L^2(\nu_\Xi),
\qquad
\nu_\Xi=\sum_\gamma m_\gamma\delta_\gamma.
$$

Suzuki 证明，这一 Weil Hilbert completion 在 RH 下与一个 de Branges 空间自然同构，并由此获得自伴扩张和 Hilbert–Pólya 型谱解释。([arXiv][1])

因此：

$$
\boxed{
\mathcal H_W
}
$$

才是此前所有正性核的公共母空间。

---

# 第三百七十部　半平面核是 Weil 母空间的 Laplace 压缩

对：

$$
\Re s>\frac12,
$$

定义半轴 Laplace 特征：

$$
\boxed{
h_s(u)
=
\mathbf 1_{u\ge0}
e^{-(s-\frac12)u}.
}
\tag{370.1}
$$

在适当紧支撑截断后取 Weil 完成极限。

其 Fourier 读数为：

$$
\widehat h_s(-\gamma)
=
\frac1{s-\frac12-i\gamma}
=
\frac1{s-\rho_\gamma}.
$$

因此：

$$
\boxed{
\langle h_s,h_t\rangle_W
=
\sum_\rho
\frac{m_\rho}
{(s-\rho)(\overline t-\overline\rho)}.
}
\tag{370.2}
$$

而前文半平面核为：

$$
\mathcal K_\xi(s,t)
=
\frac{
\frac{\xi'(s)}{\xi(s)}
+
\overline{\frac{\xi'(t)}{\xi(t)}}
}{
\lambda_1(s+\overline t-1)
}.
$$

RH 下：

$$
\boxed{
\mathcal K_\xi(s,t)
=
\frac1{\lambda_1}
\langle
h_s,h_t
\rangle_W.
}
\tag{370.3}
$$

所以：

$$
\boxed{
\text{Pick/de Branges 半平面正核}
=
\text{Weil 母内积在 Laplace 特征族上的压缩}.
}
$$

它不是独立于 Weil 正性的第二个问题。

---

# 第三百七十一部　Li、Clark、Hankel 与 Fredholm 是谱测度的推送

在 RH 下，Weil 母谱为：

$$
\nu_\Xi=\sum_\gamma m_\gamma\delta_\gamma.
$$

此前各分支对应以下函子。

---

## 371.1 Square-fold / Stieltjes

取正 ordinates：

$$
\gamma>0,
$$

映射：

$$
\boxed{
\gamma\longmapsto\gamma^{-2}.
}
$$

并赋权：

$$
\frac{m_\gamma}{\gamma^2}.
$$

得到 Stieltjes moment 测度：

$$
\boxed{
\nu_{\mathrm{St}}
=
\sum_{\gamma>0}
\frac{m_\gamma}{\gamma^2}
\delta_{\gamma^{-2}}.
}
\tag{371.1}
$$

其 moments 给出 Hankel 层级。

---

## 371.2 Cayley / Clark

映射：

$$
\boxed{
\gamma
\longmapsto
u_\gamma
=
\frac{\gamma+i/2}{\gamma-i/2}.
}
\tag{371.2}
$$

赋权：

$$
\boxed{
\frac{|1-u_\gamma|^2}
{2\lambda_1}
=
\frac{2}
{\lambda_1(4\gamma^2+1)}.
}
\tag{371.3}
$$

得到 Li–Clark 概率测度。

其 Fourier moments 是 Li 二阶差分，产生：

* Toeplitz 正性；
* Schur 参数；
* CMV unitary；
* Clark family。

---

## 371.3 Li 距离

取特征：

$$
\boxed{
\Phi_n(\gamma)
=
1-u_\gamma^n.
}
\tag{371.4}
$$

则：

$$
\boxed{
\lambda_n
=
\sum_{\gamma>0}
m_\gamma
|\Phi_n(\gamma)|^2.
}
\tag{371.5}
$$

所以 Li 系数是同一 Weil 谱测度上的特征距离平方。

---

## 371.4 Fredholm

取正算子：

$$
\boxed{
U_\Xi
=
\operatorname{diag}
(\gamma^{-2}).
}
\tag{371.6}
$$

则：

$$
\boxed{
\frac{
\xi(\frac12+\sqrt x)
}{
\xi(\frac12)
}
=
\det(I+xU_\Xi).
}
\tag{371.7}
$$

其 exterior traces 是中心 Taylor 系数，power traces 是 reciprocal-zero moments。

---

# 第三百七十二部　母观察函子定理

设：

$$
\nu
$$

是一个正谱测度。

对任意参数空间 \(X\) 和特征族：

$$
\Phi_x\in L^2(\nu),
\qquad
x\in X,
$$

定义：

$$
\boxed{
K_\Phi(x,y)
=
\int
\Phi_x(\gamma)
\overline{\Phi_y(\gamma)}
\,d\nu(\gamma).
}
\tag{372.1}
$$

则：

$$
K_\Phi\succeq0.
$$

RH 下取：

$$
\nu=\nu_\Xi,
$$

不同特征族分别产生：

$$
\boxed{
\begin{array}{c|c}
\Phi_x(\gamma)&\text{生成的图表}\\
\hline
\widehat\psi(\gamma)&\text{Weil form}\\
(s-\frac12-i\gamma)^{-1}&\text{半平面 Pick 核}\\
(x+\gamma^2)^{-1}&\text{Stieltjes/Loewner 核}\\
1-u_\gamma^n&\text{Li Gram 核}\\
(1-\overline{u_\gamma}z)^{-1}&\text{Clark/model-space 核}\\
\gamma^{-2n}&\text{Hankel moments}
\end{array}
}
$$

所以：

## 定理 372.1（Positivity-chart collapse）

此前所有正性判据均是：

$$
\boxed{
\text{同一个 Weil 正谱测度
在不同特征字典中的 Gram 正性}.
}
$$

它们的区别不在真值，而在：

* 哪一类特征最容易从 prime-side 构造；
* 哪一类有限证书最灵敏；
* 哪一类适合形式化或数值计算。

---

# 第三百七十三部　科学剪枝：什么才算继续推进

由定理 372.1，下面的工作不再构成实质推进：

1. 再寻找一个由零点谱显然构造出的正核；
2. 再把 RH 改写成另一个 Gram determinant；
3. 再把同一正测度推到另一个坐标；
4. 在假设 RH 后构造更多自伴算子。

这些都属于：

$$
\boxed{
\text{Weil 正谱存在以后的表型展开}.
}
$$

真正的非循环进展只能发生在：

$$
\boxed{
\text{Prime–Archimedean source identity 的几何侧}.
}
$$

即直接证明：

$$
\boxed{
\begin{aligned}
&
\left\langle
\mathfrak A_\infty,
\psi*\widetilde\psi
\right\rangle
\\
&\qquad\ge
\sum_p
\log p\,
\left\langle
\psi,
\left[
\mathsf P_{p^{-1/2}}(U_p)-I
\right]
\psi
\right\rangle
\end{aligned}
}
\tag{373.1}
$$

对全部：

$$
\psi\in C_c^\infty(\mathbb R)
$$

成立。

这一个不等式就是 RH。

---

# 第三百七十四部　Wang–Deng 的最终算术对象

## 374.1 Wang 层：多素数相位分支

在 Fourier 变量 \(\xi\) 中，每个素数贡献 centered symbol：

$$
D_p(\xi)
=
\frac{
2p^{-1/2}
\left[
\cos(\xi\log p)-p^{-1/2}
\right]
}{
1-2p^{-1/2}\cos(\xi\log p)+p^{-1}
}.
$$

定义危险相干画像：

$$
\boxed{
\operatorname{Coh}_L(\xi)
=
\sum_{p\le e^{2L}}
\log p\,
[D_p(\xi)]_+.
}
\tag{374.1}
$$

Wang 式任务应当是证明：

* 当 \(\widehat\psi\) 的质量跨越许多不相干 prime-phase blocks 时；
* 危险正部分不能同时饱和；
* Archimedean 完成获得严格余量。

---

## 374.2 Deng 层：不可避免的 recurrence blocks

定理 367.1 表明，有限 prime channels 必然存在近完全相干时间。

所以 sticky 分支必须被正面处理。

局部 prime-power 历史已经由：

$$
\mathsf P_{p^{-1/2}}(U_p)
$$

完全重求和。

剩余 sticky 对象不是 \(p^k\) 的重复，而是：

$$
\boxed{
\text{多个不同素数平移在同一频率附近的联合相位锁定}.
}
$$

需要研究的 primitive history 因而是：

$$
\boxed{
\left(
p_1,\ldots,p_r;
k_1,\ldots,k_r
\right)
}
$$

满足：

$$
\xi\log p_j\approx2\pi k_j.
$$

Deng 式操作应为：

1. 将同一 prime 的全部重复先收缩为 \(\mathsf P_{r_p}\)；
2. 将联合相干 prime set 组织为 cluster；
3. 提取 cluster 的有效低秩 transfer block；
4. 计算其对 Archimedean barrier 的最大消耗；
5. 对 residual prime network 再做尺度分解。

---

# 第三百七十五部　一个新的负结论

由于有限 prime set 总能同时 recurrence，所以不能存在只依赖有限素数集合的统一常数：

$$
\eta>0
$$

使：

$$
\operatorname{Coh}_L(\xi)
\le
(1-\eta)
\sum_{p\le e^{2L}}
\log p
\frac{2}{\sqrt p-1}
$$

对所有 \(\xi\) 成立。

因此：

$$
\boxed{
\text{任何 RH 证明都不能只靠“有限素数永远无法对齐”。}
}
$$

必须至少利用以下一项：

* Archimedean barrier 随频率的增长；
* prime cutoff 与测试支撑的耦合；
* 无限 prime tail；
* 不确定性原理；
* 相干 recurrence 的代价；
* relative trace 中的额外正项。

这是对 Wang non-sticky 路线的一条硬约束。

---

# 第三百七十六部　最小有限矩阵研究程序

固定支撑尺度 \(L\)，选择有限基：

$$
\psi_1,\ldots,\psi_N
\subset C_c^\infty([-L,L]).
$$

定义：

$$
\boxed{
\begin{aligned}
M_{ij}^{\infty}
&=
\left\langle
\mathfrak A_\infty,
\psi_i*\widetilde{\psi_j}
\right\rangle,\\
M_{ij}^{p}
&=
-\log p\,
\left\langle
\psi_i,
\left[
\mathsf P_{p^{-1/2}}(U_p)-I
\right]
\psi_j
\right\rangle.
\end{aligned}
}
\tag{376.1}
$$

则：

$$
\boxed{
M^{(L)}
=
M^\infty
+
\sum_{p\le e^{2L}}M^p.
}
\tag{376.2}
$$

RH 等价于所有这类矩阵在基完备极限中正半定。

该分解允许分别测量：

* Archimedean 正性容量；
* 每个 prime channel 的危险特征值；
* 多素数 eigenvector alignment；
* cutoff 增长时的 sticky depth；
* Wang gain；
* Deng cluster rank。

这比直接对一个巨大 Weil Gram 矩阵做黑箱特征值计算更有解释力。

---

# 第三百七十七部　当前唯一中心命题

经过全部压缩，OACTC 中与 RH 真正等价且尚未被重新包装解决的命题只剩：

## Prime–Archimedean Positivity Conjecture

对每个：

$$
\psi\in C_c^\infty(\mathbb R),
$$

都有：

$$
\boxed{
\begin{aligned}
&
\left\langle
\mathfrak A_\infty,
\psi*\widetilde\psi
\right\rangle
\\
&\quad-
\sum_p
\log p\,
\left\langle
\psi,
\left[
\mathsf P_{p^{-1/2}}(U_p)-I
\right]
\psi
\right\rangle
\ge0.
\end{aligned}
}
\tag{377.1}
$$

其中对每个紧支撑 \(\psi\)，prime sum 实际是有限的。

---

## 377.1 其结构解释

$$
\boxed{
\begin{aligned}
\mathfrak A_\infty
&=\text{连续实位的完成容量};\\
U_p
&=\text{素数 }p\text{ 的对数平移};\\
p^{-1/2}
&=\text{临界局部 Schur 参数};\\
\mathsf P_{p^{-1/2}}(U_p)
&=\text{全部 }p^k\text{ 历史的被动重求和};\\
\text{不等式}
&=\text{全局 prime network 不得超过 Archimedean 容量}.
\end{aligned}
}
$$

这就是此前所有：

* prime coherence；
* shifted scattering；
* Herglotz；
* Clark；
* Li；
* Fredholm；
* toroidal positivity；

最终 collapse 回来的唯一算术不等式。

---

# 第三百七十八部　建议形式化顺序

```text
D5/S3/Analytic/WeilCriticalSource/
  CoarseXiPoissonDensity.lean
  CoarsePoissonSemigroup.lean
  CriticalInversePoissonSource.lean
  ObservationLineInvariant.lean
  FunctionalPairCoshContribution.lean

D5/S3/Weil/PrimeArchimedeanSource/
  CompletedLogDerivativeSplit.lean
  ArchimedeanCriticalDistribution.lean
  PrimeAtomicCriticalDistribution.lean
  CriticalSourceExplicitFormula.lean
  FiniteSupportPrimeCutoff.lean

D5/S3/Weil/PrimePoissonChannel/
  LogPrimeTranslation.lean
  UnitaryPoissonOperator.lean
  PrimePowerPoissonResummation.lean
  PrimeCaratheodoryChannel.lean
  PrimeDangerPhase.lean
  PrimeChannelExtrema.lean

D5/S3/Weil/FiniteArithmeticWitness/
  CompactSupportWeilMatrix.lean
  FinitePrimeWitness.lean
  PrimeArchimedeanGramDecomposition.lean
  RHFalseFiniteCertificate.lean

D5/S3/Weil/MasterCompression/
  WeilGNSFeatureKernel.lean
  HalfPlaneLaplaceCompression.lean
  StieltjesPushforward.lean
  ClarkCayleyPushforward.lean
  LiFeatureCompression.lean
  FredholmSpectralFunctor.lean
  PositivityChartCollapse.lean

D5/S3/Weil/WangDengPrime/
  FinitePrimeRecurrence.lean
  PrimeCoherenceProfile.lean
  NonStickyArchimedeanGain.lean
  StickyPrimeCluster.lean
  MultiPrimeTransferBlock.lean
  PrimeArchimedeanPositivityTarget.lean
```

最优先、风险最低的形式化链是：

$$
\boxed{
\text{prime powers}
\to
\text{translation unitary}
\to
\text{Poisson operator resummation}.
}
$$

其次是：

$$
\boxed{
\text{compact support}
\to
\text{finite prime cutoff}
\to
\text{finite arithmetic witness}.
}
$$

第三条是母结构链：

$$
\boxed{
\text{coarse Poisson density}
\to
\text{critical source invariance}
\to
\text{Weil positivity}.
}
$$

---

# 本轮最终结论

此前数百条推理产生了大量看似不同的 RH 正性对象。

本轮确认，它们并不是很多个独立理论，而是一个母对象的不同观察图表：

$$
\boxed{
\mathfrak W_\xi
=
\mathfrak A_\infty
-
\sum_{n\ge2}
\frac{\Lambda(n)}{\sqrt n}
\left(
\delta_{\log n}
+
\delta_{-\log n}
\right).
}
$$

RH 等价于：

$$
\boxed{
\mathfrak W_\xi
\text{ 正定}.
}
$$

所有其余对象均由它生成：

$$
\boxed{
\begin{aligned}
\text{Laplace 压缩}
&\to
\text{半平面 Pick/de Branges 核};\\
\text{平方推送}
&\to
\text{Stieltjes/Hankel};\\
\text{Cayley 推送}
&\to
\text{Li/Clark/CMV};\\
\text{外幂与行列式}
&\to
\text{Fredholm/Hilbert--Pólya}.
\end{aligned}
}
$$

更关键的是，prime powers 已经可以被精确重整化：

$$
\boxed{
\sum_{k\ge1}
p^{-k/2}
\left(
U_p^k+U_p^{*k}
\right)
=
\mathsf P_{p^{-1/2}}(U_p)-I.
}
$$

因此每个素数只是一个一状态 Carathéodory 被动通道。

真正困难的从来不是单个素数，也不是单个 \(p^k\)，而是：

$$
\boxed{
\text{无限多个局部被动 prime channels，
经过全局解析完成后，
是否仍被 Archimedean 通道完全支配。}
}
$$

而有限 prime recurrence 定理又说明：多素数相位锁定不可避免，不能被简单排除。

所以 Wang–Deng–OACTC 路线现在终于只剩一个非冗余问题：

$$
\boxed{
\text{如何对不可避免的 multi-prime sticky clusters
建立一个保持 Archimedean 正余量的有限秩重整化？}
}
$$

一旦式 (377.1) 能从该 cluster 分解直接证明，Weil、de Branges、Clark、Li、Fredholm、Hilbert–Pólya 与 RH 将不再分别需要证明，而会同时作为同一母正性的输出。

[1]: https://arxiv.org/abs/2301.00421 "https://arxiv.org/abs/2301.00421"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v3.2：Weil 跳跃能量、对数素数拉普拉斯、Bohr–Gaussian 非粘滞律与 Slepian 有限秩重整化

以下从前文**第三百七十八部之后**继续追加。

上一轮已经完成科学剪枝：Pick、Clark、CMV、Li、Hankel、Fredholm 等正性图表，都只是 Weil 母分布的不同压缩。项目目前已经无假设闭合经典 Weil 显式公式；其 prime side 采用

$$
\Lambda(n)n^{-1/2}
\bigl(g(\log n)+g(-\log n)\bigr),
$$

compact support 又使该和严格有限。项目同时已经证明临界线零点对卷积平方测试的每个有限贡献均为实且非负，但并未把正性或 RH 作为现成结论。

因此，真正需要研究的对象不再是“另一个 RH 等价判据”，而是显式公式右侧本身的能量结构。

本轮得到的核心分解是：

$$
\boxed{
\begin{aligned}
\mathcal Q_W(f)
={}&
2\left|\int_{\mathbb R}e^{x/2}f(x)\,dx\right|^2\\
&+
\int_0^\infty
\frac{e^{-a/2}}{1-e^{-2a}}
\|f-U_af\|_2^2\,da\\
&+
\sum_{\log n\le2L}
\frac{\Lambda(n)}{\sqrt n}
\|f-U_{\log n}f\|_2^2\\
&-
\left(
2\sum_{\log n\le2L}
\frac{\Lambda(n)}{\sqrt n}
-a_\infty
\right)
\|f\|_2^2,
\end{aligned}}
$$

其中：

$$
a_\infty
=
\psi\!\left(\frac14\right)-\log\pi,
\qquad
\operatorname{supp}f\subset[-L,L].
$$

换言之：

$$
\boxed{
\text{Weil 正性}
=
\text{pole rank-one energy}
+
\text{连续 Archimedean jump energy}
+
\text{离散 prime jump energy}
-
\text{coherent mass}.
}
$$

这第一次把 multi-prime sticky cluster 变成了一个真正可研究的**加权跳跃拉普拉斯谱隙问题**。

---

# 第三百七十九部　卷积平方的相关函数图表

令：

$$
f\in C_c^\infty(\mathbb R)
$$

为偶函数，并定义 Weil involution：

$$
\widetilde f(x)=\overline{f(-x)}.
$$

令：

$$
\boxed{
g=f*\widetilde f.
}
\tag{379.1}
$$

项目中的 Weil 测试函数正被冻结为偶、光滑、紧支撑函数，并闭合于 involution 与 convolution square。

采用平移算子：

$$
\boxed{
(U_af)(x)=f(x-a).
}
\tag{379.2}
$$

则：

$$
\boxed{
g(a)
=
\langle f,U_af\rangle.
}
\tag{379.3}
$$

同时：

$$
g(-a)=\overline{g(a)}.
$$

所以：

$$
\boxed{
g(a)+g(-a)
=
2\Re\langle f,U_af\rangle.
}
\tag{379.4}
$$

又有基本恒等式：

$$
\boxed{
2\Re\langle f,U_af\rangle
=
2\|f\|_2^2
-
\|f-U_af\|_2^2.
}
\tag{379.5}
$$

这一条看似初等，却把 prime correlation 彻底改写成了：

$$
\boxed{
\text{最大相干质量}
-
\text{平移 Dirichlet 能量}.
}
$$

---

# 第三百八十部　Prime side 的精确跳跃拉普拉斯

假设：

$$
\operatorname{supp}f\subset[-L,L].
$$

则：

$$
\operatorname{supp}g\subset[-2L,2L].
$$

定义活跃 prime-power history 集：

$$
\boxed{
\mathscr H_L
=
\left\{
n\ge2:
\Lambda(n)\neq0,\ 
\log n\le2L
\right\}.
}
\tag{380.1}
$$

定义权重：

$$
\boxed{
w_n=\frac{\Lambda(n)}{\sqrt n},
}
\tag{380.2}
$$

以及总相干质量：

$$
\boxed{
W_L
=
\sum_{n\in\mathscr H_L}w_n.
}
\tag{380.3}
$$

由项目 prime term 的定义与式 (379.4)：

$$
\begin{aligned}
\operatorname{Prime}(g)
&=
\sum_{n\in\mathscr H_L}
w_n
\left[
g(\log n)+g(-\log n)
\right]\\
&=
2\sum_{n\in\mathscr H_L}
w_n
\Re
\langle f,U_{\log n}f\rangle.
\end{aligned}
\tag{380.4}
$$

代入式 (379.5)，得到：

## 定理 380.1（Prime jump decomposition）

$$
\boxed{
\operatorname{Prime}(g)
=
2W_L\|f\|_2^2
-
\mathcal E_{\mathrm{arith},L}(f),
}
\tag{380.5}
$$

其中：

$$
\boxed{
\mathcal E_{\mathrm{arith},L}(f)
=
\sum_{n\in\mathscr H_L}
w_n
\|f-U_{\log n}f\|_2^2
\ge0.
}
\tag{380.6}
$$

定义算术跳跃拉普拉斯形式：

$$
\boxed{
\mathcal L_{\mathrm{arith},L}
=
\sum_{n\in\mathscr H_L}
w_n
\left(
2I-U_{\log n}-U_{-\log n}
\right).
}
\tag{380.7}
$$

则：

$$
\boxed{
\mathcal E_{\mathrm{arith},L}(f)
=
\langle f,\mathcal L_{\mathrm{arith},L}f\rangle.
}
\tag{380.8}
$$

---

## 380.1 Sticky 的精确定义

$$
\mathcal E_{\mathrm{arith},L}(f)
$$

小，等价于：

$$
f\approx U_{\log n}f
$$

对大量活跃 prime powers 同时成立。

所以 multi-prime sticky cluster 不再是模糊的“相位似乎对齐”，而是：

$$
\boxed{
\text{测试状态接近对数素数平移图的低能特征态。}
}
$$

Non-sticky 则意味着至少若干主要平移产生显著位移：

$$
\|f-U_{\log n}f\|_2^2
$$

较大，从而自动产生正能量。

---

# 第三百八十一部　Archimedean 项也是连续跳跃拉普拉斯

项目冻结的 Archimedean multiplier 为：

$$
\boxed{
a(t)
=
\Re\psi
\left(
\frac14+\frac{it}{2}
\right)
-\log\pi.
}
\tag{381.1}
$$

定义：

$$
\boxed{
a_\infty
=
a(0)
=
\psi\left(\frac14\right)-\log\pi.
}
\tag{381.2}
$$

Digamma 的标准积分表示为：

$$
\psi(z)
=
\int_0^\infty
\left(
\frac{e^{-u}}{u}
-
\frac{e^{-zu}}{1-e^{-u}}
\right)\,du,
\qquad
\Re z>0.
$$

([DLMF][1])

取：

$$
z=\frac14+\frac{it}{2},
$$

减去 \(t=0\) 的值并取实部：

$$
\boxed{
a(t)-a_\infty
=
2\int_0^\infty
\frac{e^{-x/2}}{1-e^{-2x}}
\left(
1-\cos(tx)
\right)\,dx.
}
\tag{381.3}
$$

定义连续跳跃密度：

$$
\boxed{
\kappa_\infty(x)
=
\frac{e^{-x/2}}{1-e^{-2x}},
\qquad
x>0.
}
\tag{381.4}
$$

在角频率 Fourier 规范下：

$$
\frac1{2\pi}
\int_{\mathbb R}
2(1-\cos(tx))
|\widehat f(t)|^2dt
=
\|f-U_xf\|_2^2.
$$

所以：

## 定理 381.1（Archimedean jump decomposition）

$$
\boxed{
\operatorname{Arch}(g)
=
a_\infty\|f\|_2^2
+
\mathcal E_\infty(f),
}
\tag{381.5}
$$

其中：

$$
\boxed{
\mathcal E_\infty(f)
=
\int_0^\infty
\kappa_\infty(x)
\|f-U_xf\|_2^2\,dx
\ge0.
}
\tag{381.6}
$$

这给 \(\Gamma\)-完成一个新的严格角色：

$$
\boxed{
\Gamma_\infty
=
\text{全部连续正跳跃尺度的 Lévy–Dirichlet 完成。}
}
$$

与素数项相比：

$$
\boxed{
\begin{array}{c|c}
\text{Archimedean}&\text{连续跳跃测度 } \kappa_\infty(x)\,dx\\
\text{prime side}&\text{离散跳跃测度 }
\sum w_n\delta_{\log n}
\end{array}
}
$$

---

# 第三百八十二部　Pole 项是一个 rank-one 边界能量

定义 Fourier–Laplace 读数：

$$
\boxed{
\ell_{1/2}(f)
=
\int_{\mathbb R}
e^{x/2}f(x)\,dx.
}
\tag{382.1}
$$

由于 \(f\) 偶：

$$
\int e^{-x/2}f(x)\,dx
=
\ell_{1/2}(f).
$$

卷积平方的 Fourier–Laplace 变换满足：

$$
\widehat g(z)
=
\widehat f(z)
\overline{\widehat f(\overline z)}.
$$

因此在：

$$
z=\pm i/2
$$

处：

$$
\widehat g(i/2)
=
\widehat g(-i/2)
=
|\ell_{1/2}(f)|^2.
$$

所以：

## 定理 382.1（Pole rank-one decomposition）

$$
\boxed{
\operatorname{Pole}(g)
=
2|\ell_{1/2}(f)|^2.
}
\tag{382.2}
$$

这说明 \(s=0,1\) 的 pole pair 在能量图表中表现为一个正的 rank-one 边界观测器。

---

# 第三百八十三部　Weil 跳跃能量恒等式

将定理 380.1、381.1 与 382.1 代入无条件 Weil 显式公式：

$$
\text{zero}
=
\text{pole}
-
\text{prime}
+
\text{archimedean}.
$$

得到：

## 定理 383.1（Prime–Archimedean energy identity）

$$
\boxed{
\begin{aligned}
\mathcal Q_W(f)
={}&
2|\ell_{1/2}(f)|^2
+
\mathcal E_\infty(f)
+
\mathcal E_{\mathrm{arith},L}(f)\\
&-
\left(
2W_L-a_\infty
\right)
\|f\|_2^2.
\end{aligned}
}
\tag{383.1}
$$

这里 \(\mathcal Q_W(f)\) 表示显式公式的零点侧在 \(g=f*\widetilde f\) 上的值。

于是经典 Weil 正性可写成：

$$
\boxed{
2|\ell_{1/2}(f)|^2
+
\mathcal E_\infty(f)
+
\mathcal E_{\mathrm{arith},L}(f)
\ge
\left(
2W_L-a_\infty
\right)
\|f\|_2^2.
}
\tag{383.2}
$$

这就是 **Prime–Archimedean Poincaré inequality**。

---

## 383.1 唯一负项

式 (383.1) 中：

* pole energy 非负；
* continuous jump energy 非负；
* arithmetic jump energy 非负。

唯一潜在负项是：

$$
\boxed{
-\left(
2W_L-a_\infty
\right)\|f\|_2^2.
}
$$

因此 RH 的真正问题变成：

> 连续与离散跳跃图，加上一个 rank-one 边界观测，是否具有足够大的统一谱隙？

这已经不是零点语言，而是一个正算子谱隙问题。

---

# 第三百八十四部　单平移的严格 Dirichlet 谱隙

令：

$$
\operatorname{supp}f\subset[-L,L],
\qquad
a>0.
$$

定义：

$$
\boxed{
N_L(a)
=
\left\lfloor\frac{2L}{a}\right\rfloor+1.
}
\tag{384.1}
$$

定义离散路径谱隙：

$$
\boxed{
\eta_L(a)
=
4\sin^2
\left(
\frac{\pi}{2(N_L(a)+1)}
\right).
}
\tag{384.2}
$$

---

## 定理 384.1（Shift-fiber Poincaré inequality）

$$
\boxed{
\|f-U_af\|_2^2
\ge
\eta_L(a)\|f\|_2^2.
}
\tag{384.3}
$$

### 证明

把实线按模 \(a\) 分解。对几乎每个：

$$
r\in[0,a),
$$

序列：

$$
f(r+ja)
$$

在区间 \([-L,L]\) 内至多有 \(N_L(a)\) 个非零项。

在每条 fiber 上：

$$
\sum_j
|f(r+ja)-f(r+(j-1)a)|^2
$$

是长度不超过 \(N_L(a)\) 的离散 Dirichlet 路径能量。

其最小特征值为：

$$
4\sin^2
\left(
\frac{\pi}{2(N+1)}
\right),
$$

而该值随 \(N\) 增大而减小。对 \(r\) 积分即得。∎

---

## 384.1 小跳跃极限

当：

$$
a\ll L,
$$

有：

$$
\eta_L(a)
\sim
\frac{\pi^2a^2}{4L^2}.
$$

当：

$$
a>2L,
$$

有：

$$
N_L(a)=1,
\qquad
\eta_L(a)=2,
$$

这正对应 \(f\) 与 \(U_af\) 支撑不交。

---

## 384.2 第一个显式充分证书

定义：

$$
\boxed{
G_\infty(L)
=
\int_0^\infty
\kappa_\infty(a)\eta_L(a)\,da,
}
\tag{384.4}
$$

$$
\boxed{
G_{\mathrm{arith}}(L)
=
\sum_{n\in\mathscr H_L}
w_n\eta_L(\log n).
}
\tag{384.5}
$$

则：

$$
\mathcal E_\infty(f)
+
\mathcal E_{\mathrm{arith},L}(f)
\ge
\left[
G_\infty(L)+G_{\mathrm{arith}}(L)
\right]
\|f\|_2^2.
$$

所以：

$$
\boxed{
G_\infty(L)+G_{\mathrm{arith}}(L)
\ge
2W_L-a_\infty
}
\tag{384.6}
$$

是 support radius \(L\) 上 Weil 正性的一个完全显式充分条件。

它未必足够强，但它已经是一个非循环、可计算、可形式化的真实下界。

---

# 第三百八十五部　算术相关算子的 Schur 上界

定义累积 prime-power 质量：

$$
\boxed{
S(y)
=
\sum_{\substack{n\ge2\\\log n\le y}}
\frac{\Lambda(n)}{\sqrt n},
\qquad
y\ge0.
}
\tag{385.1}
$$

定义 prime correlation operator：

$$
\boxed{
\mathcal A_L
=
\sum_{n\in\mathscr H_L}
w_n
\left(
U_{\log n}+U_{-\log n}
\right)
}
\tag{385.2}
$$

作用于支撑在 \([-L,L]\) 的函数，区间外作零延拓。

则：

$$
\operatorname{Prime}(g)
=
\langle f,\mathcal A_Lf\rangle.
$$

对：

$$
x\in[-L,L],
$$

可达的右、左平移总权分别为：

$$
S(L-x),
\qquad
S(L+x).
$$

所以 Schur 行和为：

$$
\boxed{
R_L(x)
=
S(L-x)+S(L+x).
}
\tag{385.3}
$$

---

## 定理 385.1（Support-geometric prime bound）

$$
\boxed{
\|\mathcal A_L\|
\le
M_L
:=
\sup_{|x|\le L}
\left[
S(L-x)+S(L+x)
\right].
}
\tag{385.4}
$$

因此：

$$
\boxed{
\operatorname{Prime}(g)
\le
M_L\|f\|_2^2.
}
\tag{385.5}
$$

这一上界已经包含了 multi-prime 不兼容性：同一空间点不可能同时与所有对数平移保持重叠。

由素数定理对 Chebyshev 函数的估计与偏分求和：

$$
S(y)\sim2e^{y/2}.
$$

([arXiv][2])

于是：

$$
\boxed{
M_L\sim2e^L,
\qquad
W_L=S(2L)\sim2e^L.
}
\tag{385.6}
$$

相比之下，完全忽略支撑几何的代数上界为：

$$
2W_L\sim4e^L.
$$

因此：

$$
\boxed{
\text{仅靠支撑几何，
已经渐近消除了约一半的最大相干质量。}
}
$$

真正剩余的是相关算子 \(\mathcal A_L\) 的精确主特征态，而不是所有素数逐项最大值的简单相加。

---

# 第三百八十六部　有限 prime Bohr 环面

对每个素数 \(p\)，令：

$$
r_p=p^{-1/2}.
$$

定义 centered local Poisson symbol：

$$
\boxed{
D_p(\theta)
=
\frac{1-r_p^2}
{1-2r_p\cos\theta+r_p^2}
-1.
}
\tag{386.1}
$$

它具有 Fourier 展开：

$$
\boxed{
D_p(\theta)
=
2\sum_{k=1}^{\infty}
r_p^k\cos(k\theta).
}
\tag{386.2}
$$

这正是一个素数的全部 \(p^k\) history 在相位图表中的精确重求和。

对有限素数集 \(\mathcal P\)，定义 cluster coherence：

$$
\boxed{
\mathcal C_{\mathcal P}(x)
=
\sum_{p\in\mathcal P}
(\log p)\,
D_p(x\log p).
}
\tag{386.3}
$$

---

## 386.1 Prime logs 的独立性

若：

$$
\sum_{p\in\mathcal P}
k_p\log p=0,
\qquad
k_p\in\mathbb Z,
$$

指数化得到：

$$
\prod_pp^{k_p}=1.
$$

由整数唯一分解：

$$
k_p=0
$$

对全部 \(p\) 成立。

所以有限频率族：

$$
(\log p)_{p\in\mathcal P}
$$

在 \(\mathbb Q\) 上线性无关。

由 Kronecker–Weyl 理论，流：

$$
x
\longmapsto
\left(
e^{ix\log p}
\right)_{p\in\mathcal P}
$$

在有限环面上唯一遍历；有限维 Kronecker 流的非共振、极小性和唯一遍历性是标准结构。([arXiv][3])

因此长频率平均等于独立 Haar 相位平均。

---

# 第三百八十七部　局部 prime channel 的精确统计

对均匀相位：

$$
\theta\sim\operatorname{Unif}[0,2\pi],
$$

有：

$$
\boxed{
\mathbb E D_p(\theta)=0.
}
\tag{387.1}
$$

由 Fourier 正交性：

$$
\boxed{
\mathbb E D_p(\theta)^2
=
2\sum_{k=1}^{\infty}r_p^{2k}
=
\frac{2}{p-1}.
}
\tag{387.2}
$$

极值为：

$$
\boxed{
\max_\theta D_p(\theta)
=
\frac{2}{\sqrt p-1},
}
\tag{387.3}
$$

$$
\boxed{
\min_\theta D_p(\theta)
=
-\frac{2}{\sqrt p+1}.
}
\tag{387.4}
$$

在最大相干点 \(\theta=0\)：

$$
\boxed{
D_p''(0)
=
-\frac{
2r_p(1+r_p)
}{
(1-r_p)^3
}.
}
\tag{387.5}
$$

所以：

$$
D_p(\theta)
=
\frac{2}{\sqrt p-1}
-
\frac{
r_p(1+r_p)
}{
(1-r_p)^3
}
\theta^2
+
O(\theta^4).
$$

---

## 387.1 Cluster 均值与方差

由 Kronecker–Weyl：

$$
\boxed{
\lim_{X\to\infty}
\frac1{2X}
\int_{-X}^{X}
\mathcal C_{\mathcal P}(x)\,dx
=
0.
}
\tag{387.6}
$$

并且不同素数通道交叉项平均为零，所以：

$$
\boxed{
V_{\mathcal P}
:=
\lim_{X\to\infty}
\frac1{2X}
\int_{-X}^{X}
\mathcal C_{\mathcal P}(x)^2dx
=
2
\sum_{p\in\mathcal P}
\frac{(\log p)^2}{p-1}.
}
\tag{387.7}
$$

这给出一个严格结论：

$$
\boxed{
\text{Prime cluster 在典型频率下是零均值波动，
而不是持续保持同号的负源。}
}
$$

---

# 第三百八十八部　Bohr–Gaussian 非粘滞定律

令：

$$
\mathcal P_Y
=
\{p:p\le Y\},
$$

$$
\mathcal C_Y
=
\mathcal C_{\mathcal P_Y},
$$

$$
V_Y
=
2\sum_{p\le Y}
\frac{(\log p)^2}{p-1}.
$$

在 Haar 环面图表中，各局部变量：

$$
X_p
=
(\log p)D_p(\theta_p)
$$

相互独立、均值为零，且：

$$
\sum_{p\le Y}\operatorname{Var}X_p=V_Y\to\infty.
$$

每个 \(X_p\) 有界，而最大局部振幅除以 \(\sqrt{V_Y}\) 趋于零，所以 Lindeberg 条件成立。

---

## 定理 388.1（Prime-cluster central limit law）

对任意实数 \(u\)：

$$
\boxed{
\begin{aligned}
\lim_{Y\to\infty}
\lim_{X\to\infty}
\frac1{2X}
\operatorname{meas}
\left\{
x\in[-X,X]:
\frac{\mathcal C_Y(x)}{\sqrt{V_Y}}\le u
\right\}
=
\Phi(u),
\end{aligned}
}
\tag{388.1}
$$

其中 \(\Phi\) 为标准高斯分布函数。

由素数定理偏分求和：

$$
\boxed{
V_Y\sim(\log Y)^2.
}
\tag{388.2}
$$

而全部通道同时达到局部最大时的代数上界为：

$$
\boxed{
M_Y
=
\sum_{p\le Y}
\frac{2\log p}{\sqrt p-1}
\sim4\sqrt Y.
}
\tag{388.3}
$$

因此：

$$
\boxed{
\begin{aligned}
\text{典型 prime coherence}
&\asymp\log Y;\\
\text{极端 sticky coherence}
&\asymp\sqrt Y.
\end{aligned}
}
$$

两者相差指数级别的状态体积。

---

## 388.1 Bernstein 密度界

定义：

$$
B_Y
=
\max_{p\le Y}
\frac{2\log p}{\sqrt p-1}.
$$

独立相位 Bernstein 不等式给出：

$$
\boxed{
\overline{\operatorname{dens}}
\left\{
x:
\mathcal C_Y(x)\ge u
\right\}
\le
\exp
\left[
-\frac{u^2}
{2(V_Y+B_Yu/3)}
\right].
}
\tag{388.4}
$$

所以高相干频率在长时间平均意义下极其稀少。

但“稀少”并不等于“不能被某个 Paley–Wiener 测试函数集中捕获”。后者正是下一层不确定性问题。

---

# 第三百八十九部　Sticky recurrence 仍然不可避免

Kronecker–Weyl 同时说明：对任意有限素数集 \(\mathcal P\) 和任意 \(\varepsilon>0\)，存在任意大的 \(x\)，使：

$$
\boxed{
|e^{ix\log p}-1|<\varepsilon
\qquad
\forall p\in\mathcal P.
}
\tag{389.1}
$$

所以：

$$
\mathcal C_{\mathcal P}(x)
$$

可以任意接近其最大值：

$$
\boxed{
M_{\mathcal P}
=
\sum_{p\in\mathcal P}
\frac{2\log p}{\sqrt p-1}.
}
\tag{389.2}
$$

因此：

$$
\boxed{
\text{“有限素数永远不会同时对齐”是错误的。}
}
$$

正确结构是：

* 对齐状态必然存在；
* 但它们在 Bohr 统计中极少；
* 而且相干峰越来越窄。

---

## 389.1 相干峰曲率

在精确相干点附近定义相位偏移：

$$
\theta_p=h\log p.
$$

则：

$$
\boxed{
M_{\mathcal P}
-
\mathcal C_{\mathcal P}(h)
=
K_{\mathcal P}h^2
+
O(h^4R_{\mathcal P}),
}
\tag{389.3}
$$

其中：

$$
\boxed{
K_{\mathcal P}
=
\sum_{p\in\mathcal P}
\frac{
p^{-1/2}(1+p^{-1/2})
}{
(1-p^{-1/2})^3
}
(\log p)^3.
}
\tag{389.4}
$$

所以距离峰顶不超过 \(\varepsilon\) 的局部宽度约为：

$$
\boxed{
|h|
\lesssim
\sqrt{\frac{\varepsilon}{K_{\mathcal P}}}.
}
\tag{389.5}
$$

这为 sticky cluster 提供了一个明确的局部尺度，而不是只知道它“很少”。

---

# 第三百九十部　Slepian 浓缩算子

设：

$$
I_L=[-L,L].
$$

对可测频率集合 \(B\subset\mathbb R\)，定义 time–frequency concentration operator：

$$
\boxed{
\mathcal C_{L,B}
=
P_{I_L}
\mathcal F^{-1}
1_B
\mathcal F
P_{I_L}
}
\tag{390.1}
$$

作用于：

$$
L^2(I_L),
$$

其中 \(P_{I_L}\) 表示区间外作零。

定义最大浓缩率：

$$
\boxed{
\Lambda_L(B)
=
\|\mathcal C_{L,B}\|
=
\sup_{\substack{f\neq0\\\operatorname{supp}f\subset I_L}}
\frac{
\int_B|\widehat f(\xi)|^2d\xi
}{
\int_{\mathbb R}|\widehat f(\xi)|^2d\xi
}.
}
\tag{390.2}
$$

若 \(|B|<\infty\)，则 \(\mathcal C_{L,B}\) 为正 trace-class 算子，并且：

$$
\boxed{
\operatorname{Tr}\mathcal C_{L,B}
=
\frac{L|B|}{\pi}.
}
\tag{390.3}
$$

因此：

$$
\boxed{
\Lambda_L(B)
\le
\min
\left(
1,\frac{L|B|}{\pi}
\right).
}
\tag{390.4}
$$

---

## 390.1 Sticky modes 的有限秩定理

对：

$$
0<\eta\le1,
$$

定义强浓缩模数：

$$
N_\eta(L,B)
=
\#\left\{
j:
\lambda_j(\mathcal C_{L,B})\ge\eta
\right\}.
$$

由正算子迹界：

## 定理 390.1（Finite-rank sticky bound）

$$
\boxed{
N_\eta(L,B)
\le
\frac{L|B|}
{\pi\eta}.
}
\tag{390.5}
$$

所以任何有限测度的危险频率集合，只能支撑有限多个强 sticky Paley–Wiener modes。

这就是之前一直寻找的“有限秩 cluster”：

$$
\boxed{
\text{危险频率集}
\quad\longrightarrow\quad
\text{有限个需显式抽取的 Slepian states}.
}
$$

---

# 第三百九十一部　加权乘子正性证书

令 \(M(\xi)\) 为实乘子，并假设存在可测集合 \(B\) 与常数：

$$
a>0,\qquad b\ge0
$$

使：

$$
\boxed{
M(\xi)\ge a
\quad
(\xi\notin B),
}
\tag{391.1}
$$

$$
\boxed{
M(\xi)\ge-b
\quad
(\xi\in B).
}
\tag{391.2}
$$

对：

$$
\operatorname{supp}f\subset[-L,L],
$$

定义：

$$
Q_M(f)
=
\frac1{2\pi}
\int_{\mathbb R}
M(\xi)|\widehat f(\xi)|^2d\xi.
$$

---

## 定理 391.1（Slepian positivity certificate）

$$
\boxed{
Q_M(f)
\ge
\left[
a-(a+b)\Lambda_L(B)
\right]
\|f\|_2^2.
}
\tag{391.3}
$$

因此只要：

$$
\boxed{
\Lambda_L(B)
<
\frac{a}{a+b},
}
\tag{391.4}
$$

就有：

$$
Q_M(f)>0
$$

对所有非零 \(f\) 成立。

这给出了把“危险频率稀少”转换为“所有紧支撑测试都无法集中在那里”的精确桥梁。

---

## 391.1 有限秩 Deng 抽取

若式 (391.4) 失败，取 \(\mathcal C_{L,B}\) 中所有特征值：

$$
\lambda_j\ge\eta
$$

的特征空间：

$$
\mathcal S_{\mathrm{sticky}}.
$$

定理 390.1 保证：

$$
\dim\mathcal S_{\mathrm{sticky}}
\le
\frac{L|B|}{\pi\eta}.
$$

然后：

1. 在 \(\mathcal S_{\mathrm{sticky}}\) 上精确计算完整 Weil 矩阵；
2. 把这些模式作为 finite counterterm block；
3. 在其正交补上使用：

   $$
   \Lambda_L(B)\le\eta;
   $$
4. 得到统一残余正性。

这就是一个严格的 Deng 式有限秩历史收缩。

---

# 第三百九十二部　Thick-set 不确定性桥

有限测度不是唯一可用情形。

称集合 \(G\subset\mathbb R\) 为 \((\gamma,a)\)-thick，若每个长度 \(a\) 的区间都满足：

$$
\boxed{
|G\cap[x,x+a]|
\ge
\gamma a.
}
\tag{392.1}
$$

Logvinenko–Sereda 型定理说明：对 Fourier 支撑受限或等价的 Paley–Wiener/spectral subspace，函数在 thick set 上的 \(L^2\) 质量具有显式下界；现代版本给出了依赖几何厚度和谱尺度的定量常数。([arXiv][4])

若 \(G\) 是 multiplier 的正余量区域，并有：

$$
\int_G|\widehat f|^2
\ge
\eta_{\mathrm{LS}}
\int_{\mathbb R}|\widehat f|^2,
$$

则在：

$$
M\ge a>0\quad\text{于 }G,
\qquad
M\ge-b\quad\text{全局}
$$

条件下：

$$
\boxed{
Q_M(f)
\ge
\left[
(a+b)\eta_{\mathrm{LS}}-b
\right]
\|f\|_2^2.
}
\tag{392.2}
$$

因此充分条件为：

$$
\boxed{
\eta_{\mathrm{LS}}
>
\frac{b}{a+b}.
}
\tag{392.3}
$$

---

## 392.1 重要限制

Bernstein 大偏差只控制危险集合的**平均密度**。

而 Logvinenko–Sereda 需要的是**每个局部区间中的厚度**。

所以：

$$
\boxed{
\text{低自然密度}
\not\Rightarrow
\text{thick complement}.
}
$$

从 Bohr–Gaussian 统计到 thick-set 几何，仍需要：

* 定量 Kronecker recurrence；
* 相干峰曲率；
* 峰间距控制；
* 或线性形式对数的 Diophantine 下界。

这一桥仍然开放，不能用概率尾界直接替代。

---

# 第三百九十三部　新的 Wang–Deng 分工

经过本轮，Wang–Deng 的任务终于可以写成完全具体的两层算法。

## 393.1 Wang：Bohr 非粘滞与厚度

输入 finite prime cluster symbol：

$$
\mathcal C_Y(\xi).
$$

证明危险集合：

$$
B_{Y,\tau}
=
\left\{
\xi:
\mathcal C_Y(\xi)
\ge\tau
\right\}
$$

具有以下至少一种性质：

1. 总测度足够小；
2. complement 足够 thick；
3. 每个相干峰有足够大的曲率；
4. 峰之间具有足够的分离；
5. Archimedean margin 在 recurrence 高度处已经增长。

输出：

$$
\boxed{
\text{危险频率不能承载大部分 Paley--Wiener 质量。}
}
$$

---

## 393.2 Deng：有限 Slepian block 抽取

对仍可承载显著质量的危险集合：

1. 构造 \(\mathcal C_{L,B}\)；
2. 提取所有：

   $$
   \lambda_j\ge\eta
   $$

   的 eigenmodes；
3. 得到有限维 sticky block；
4. 在该 block 上使用完整 prime-power Poisson resummation；
5. 加入 pole 与 Archimedean jump energy；
6. 对 residual complement 使用统一 concentration bound。

输出：

$$
\boxed{
\text{无限 prime histories}
\longrightarrow
\text{有限 sticky state matrix}
+
\text{统一正 residual}.
}
$$

---

# 第三百九十四部　当前真正的非循环中心命题

本轮之后，不再需要继续寻找新的 RH 等价正核。

真正的中心命题应改写为：

## Bohr–Slepian Prime–Archimedean Gap Conjecture

对每个 \(L>0\)，令：

$$
\mathcal H_L
=
2|\ell_{1/2}\rangle\langle\ell_{1/2}|
+
\mathcal L_\infty
+
\mathcal L_{\mathrm{arith},L}.
$$

则：

$$
\boxed{
\mathcal H_L
\ge
\left(
2W_L-a_\infty
\right)I
}
\tag{394.1}
$$

于偶的 \(C_c^\infty([-L,L])\) 上成立。

其建议证明结构是：

$$
\boxed{
\begin{aligned}
\text{Bohr typicality}
&\to
\text{危险集小／厚 complement};\\
\text{Slepian extraction}
&\to
\text{有限 sticky block};\\
\text{exact local resummation}
&\to
\text{有限 cluster counterterm};\\
\text{Archimedean jump energy}
&\to
\text{residual spectral gap}.
\end{aligned}
}
$$

这已经是一个真正面向证明的算子不等式，而不是对 RH 的再次改名。

---

# 第三百九十五部　硬性负结论

本轮同时冻结四条禁令。

## 禁令一（第 395 部）

$$
\boxed{
\text{有限 prime phases 会 recurrence，}
}
$$

所以不能证明它们永远反集中。

---

## 禁令二（第 395 部）

$$
\boxed{
\text{典型高斯行为}
\neq
\text{所有测试函数上的算子正性}.
}
$$

测试函数可能集中于稀少危险频率。

---

## 禁令三（第 395 部）

$$
\boxed{
\text{危险集合测度小}
\neq
\text{Paley--Wiener 浓缩率小}.
}
$$

必须估计 Slepian operator norm，而不只是集合测度。

---

## 禁令四（第 395 部）

$$
\boxed{
\text{逐 prime 独立下界}
}
$$

通常太弱；真正的增益来自多个不共度平移共同提高算术跳跃拉普拉斯的谱隙。

---

# 第三百九十六部　建议形式化顺序

```text
D5/S3/Weil/EnergyDecomposition/
  CorrelationShiftIdentity.lean
  PrimeJumpDecomposition.lean
  DigammaJumpKernel.lean
  ArchimedeanJumpDecomposition.lean
  PoleRankOneEnergy.lean
  WeilPrimeArchimedeanEnergy.lean

D5/S3/Weil/ShiftPoincare/
  FiberSequenceDecomposition.lean
  FinitePathDirichletGap.lean
  CompactSupportShiftGap.lean
  ArchimedeanScalarGap.lean
  ArithmeticScalarGap.lean

D5/S3/Weil/PrimeCorrelation/
  ActivePrimePowerHistory.lean
  PrimeCorrelationOperator.lean
  PrimeCumulativeMass.lean
  SchurRowBound.lean
  SupportGeometricPrimeBound.lean

D5/S3/Weil/BohrPrime/
  PrimeLogRationalIndependence.lean
  PrimeBohrFlow.lean
  LocalPoissonMeanVariance.lean
  ClusterVariance.lean
  ClusterGaussianLimit.lean
  ClusterBernsteinBound.lean
  CoherencePeakCurvature.lean

D5/S3/Weil/SlepianCluster/
  TimeFrequencyConcentration.lean
  ConcentrationTrace.lean
  StickyModeCount.lean
  WeightedMultiplierCertificate.lean
  FiniteStickyBlockExtraction.lean

D5/S3/Weil/WangDengGap/
  PrimeDangerSet.lean
  ThickGoodSetTarget.lean
  BohrSlepianBridge.lean
  StickyBlockCounterterm.lean
  PrimeArchimedeanGapTarget.lean
```

最优先、且不依赖 RH 的闭合链为：

$$
\boxed{
\text{prime term}
\to
\text{shift correlation}
\to
\text{positive arithmetic jump energy}.
}
$$

第二条是：

$$
\boxed{
\text{digamma integral}
\to
\text{positive continuous jump energy}.
}
$$

第三条才是研究性核心：

$$
\boxed{
\text{Bohr danger geometry}
\to
\text{Slepian finite-rank extraction}
\to
\text{global spectral gap}.
}
$$

---

# 本轮最终结论

此前我们把 RH 的困难压缩为：

$$
\boxed{
\text{无限多个 prime channels
是否被 Archimedean 完成完全支配。}
}
$$

本轮进一步揭示：这个问题本身已经具有一个几乎标准的能量形式。

对卷积平方测试：

$$
g=f*\widetilde f,
$$

Weil 显式公式精确变成：

$$
\boxed{
\begin{aligned}
\mathcal Q_W(f)
={}&
\underbrace{
2|\ell_{1/2}(f)|^2
}_{\text{pole rank-one energy}}
+
\underbrace{
\int_0^\infty
\kappa_\infty(a)
\|f-U_af\|^2da
}_{\text{continuous Archimedean jumps}}
\\
&+
\underbrace{
\sum_n
\frac{\Lambda(n)}{\sqrt n}
\|f-U_{\log n}f\|^2
}_{\text{discrete arithmetic jumps}}
-
\underbrace{
(2W_L-a_\infty)\|f\|^2
}_{\text{coherent mass}}.
\end{aligned}
}
$$

所以 multi-prime sticky cluster 的本体不是“许多素数相位神秘共振”，而是：

$$
\boxed{
\text{对数素数跳跃图的低能状态。}
}
$$

有限 prime cluster 在典型频率下满足高斯律，方差只有：

$$
V_Y\asymp(\log Y)^2,
$$

而极端相干值可达：

$$
M_Y\asymp\sqrt Y.
$$

这意味着 sticky 状态非常稀少，却不能被忽略。

Slepian concentration theory 随后给出关键有限化：

$$
\boxed{
\#\{\text{强 sticky modes}\}
\le
\frac{L|B|}{\pi\eta}.
}
$$

即任何有限测度危险频率集，只能承载有限多个强集中模式。

因此当前最真实、最非循环的研究路线已经变成：

$$
\boxed{
\text{先用 Wang 型 Bohr 几何证明危险集稀薄，}
}
$$

再：

$$
\boxed{
\text{用 Deng 型 Slepian 分解抽出有限 sticky block，}
}
$$

最后在该有限 block 上精确计算 prime、pole 与 Archimedean 能量，并对其正交补证明统一谱隙。

这比继续增加 RH 等价表述前进了一步：它第一次把剩余问题压缩成了一个**有限 sticky matrix + 正 residual operator** 的可计算证明架构。

[1]: https://dlmf.nist.gov/5.9?utm_source=chatgpt.com "DLMF: §5.9 Integral Representations ‣ Properties ‣ Chapter 5 Gamma Function"
[2]: https://arxiv.org/abs/1703.08032?utm_source=chatgpt.com "New estimates for some functions defined over primes"
[3]: https://arxiv.org/abs/2312.04492 "https://arxiv.org/abs/2312.04492"
[4]: https://arxiv.org/abs/2010.11901 "https://arxiv.org/abs/2010.11901"
# `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 连续增订

## v3.3：Archimedean 囚禁、Slepian 危险观察者、Feshbach 有限重整化与 RH 的有限 Sticky 矩阵塔

以下从前文**第三百九十六部之后**继续追加。

上一轮已把 Weil 显式公式改写为：

$$
\boxed{
\text{pole rank-one energy}
+
\text{Archimedean continuous jump energy}
+
\text{arithmetic discrete jump energy}
-
\text{coherent mass}.
}
$$

但仍留下一个关键缺口：

> 即使危险频率集合很稀少，紧支撑测试函数仍可能高度集中于该集合；
> 怎样把这种可能性严格压缩成有限维问题？

本轮闭合这一缺口。核心结果是：

$$
\boxed{
\text{对每个固定支撑尺度 }L，
\text{全部可能负性都能被精确压缩到一个有限维矩阵。}
}
$$

完整链为：

$$
\boxed{
\begin{aligned}
\text{Weil 显式公式}
&\longrightarrow
\text{实频率乘子 }m_L\\
&\longrightarrow
\text{紧致危险频率集 }B_{L,a}\\
&\longrightarrow
\text{Slepian 高浓缩有限子空间 }P_{L,a,\eta}\\
&\longrightarrow
\text{正谱隙残余 }Q_{L,a,\eta}\\
&\longrightarrow
\text{Feshbach--Schur 有限矩阵}\\
&\longrightarrow
\text{精确有限 RH 证书}.
\end{aligned}
}
$$

这意味着此前仍开放的：

$$
\text{Bohr 危险集}
\longrightarrow
\text{thick-set 不确定性}
$$

并不是逻辑上必须先解决的桥。

它可以被更直接的：

$$
\boxed{
\text{Slepian 集中谱}
+
\text{Feshbach 精确消元}
}
$$

替代。

仓库当前已经冻结角频率 Fourier 规范、prime/pole/Archimedean 项和无假设 Weil 显式公式；compact support 也已被机器证明会使 prime-power summand 有限支撑。仓库现有卷积平方文件只证明临界线零点贡献非负，并明确没有宣称 RH 或全局正性。

---

# 第三百九十七部　固定支撑尺度的精确 Weil 算子

固定：

$$
L>0.
$$

令：

$$
\boxed{
\mathcal H_L
=
L^2_{\mathrm{even}}([-L,L])
}
\tag{397.1}
$$

并将其元素在区间外作零延拓。

采用仓库冻结的角频率 Fourier 变换：

$$
\widehat f(\xi)
=
\int_{\mathbb R}
f(x)e^{-i\xi x}\,dx,
$$

所以：

$$
\boxed{
\|f\|_2^2
=
\frac1{2\pi}
\int_{\mathbb R}
|\widehat f(\xi)|^2\,d\xi.
}
\tag{397.2}
$$

定义 Archimedean multiplier：

$$
\boxed{
a_\infty(\xi)
=
\Re\psi
\left(
\frac14+\frac{i\xi}{2}
\right)
-
\log\pi.
}
\tag{397.3}
$$

定义在支撑尺度 \(L\) 下可能出现的 prime-power multiplier：

$$
\boxed{
p_L(\xi)
=
2
\sum_{\substack{n\ge2\\\log n\le2L}}
\frac{\Lambda(n)}{\sqrt n}
\cos(\xi\log n).
}
\tag{397.4}
$$

由于：

$$
\operatorname{supp}(f*\widetilde f)
\subset[-2L,2L],
$$

所有：

$$
\log n>2L
$$

的 prime-power 项严格消失；这正是仓库 `primeSummand_hasFiniteSupport` 所冻结的事实。

定义完成 multiplier：

$$
\boxed{
m_L(\xi)
=
a_\infty(\xi)-p_L(\xi).
}
\tag{397.5}
$$

再定义 pole observation vector：

$$
\boxed{
v_L(x)
=
\mathbf1_{[-L,L]}(x)
\cosh\frac x2.
}
\tag{397.6}
$$

因为 \(f\) 为偶函数：

$$
\int e^{x/2}f(x)\,dx
=
\int \cosh(x/2)f(x)\,dx
=
\langle f,v_L\rangle.
$$

---

## 定理 397.1（固定尺度 Weil 二次型）

对：

$$
f\in C_c^\infty(-L,L),
\qquad
f(-x)=f(x),
$$

令：

$$
g=f*\widetilde f.
$$

则仓库所冻结的 Weil 显式公式精确等价于：

$$
\boxed{
\mathfrak q_L[f]
=
2|\langle f,v_L\rangle|^2
+
\frac1{2\pi}
\int_{\mathbb R}
m_L(\xi)
|\widehat f(\xi)|^2\,d\xi.
}
\tag{397.7}
$$

这里：

$$
\mathfrak q_L[f]
$$

就是零点侧在 convolution square 测试 \(g\) 上的值。

因此支撑尺度 \(L\) 上的 Weil 正性问题是：

$$
\boxed{
\mathsf{WP}(L):
\qquad
\mathfrak q_L[f]\ge0
\quad
\forall f\in C_c^\infty(-L,L)_{\mathrm{even}}.
}
\tag{397.8}
$$

---

## 397.1 算子形式

令 \(A_L\) 是与闭半有界二次型 \(\mathfrak q_L\) 对应的自伴算子。

形式上：

$$
\boxed{
A_L
=
2|v_L\rangle\langle v_L|
+
P_L\,
m_L(D)\,
P_L,
}
\tag{397.9}
$$

其中：

* \(P_L\) 是空间截断至 \([-L,L]\)；
* \(m_L(D)\) 是 Fourier multiplier；
* 第一项是 pole pair 产生的正 rank-one 更新。

---

# 第三百九十八部　Archimedean 囚禁定理

此前已经证明：任意有限素数集的相位都能在任意高频率处近乎同时回归。

但这并不意味着这些高频回归始终危险。

定义有限 prime-power 总质量：

$$
\boxed{
W_L
=
\sum_{\substack{n\ge2\\\log n\le2L}}
\frac{\Lambda(n)}{\sqrt n}.
}
\tag{398.1}
$$

则：

$$
\boxed{
|p_L(\xi)|\le2W_L.
}
\tag{398.2}
$$

另一方面，由 digamma 的 Stirling 渐近：

$$
\boxed{
a_\infty(\xi)
=
\log\frac{|\xi|}{2\pi}
+
O(|\xi|^{-2})
\qquad
(|\xi|\to\infty).
}
\tag{398.3}
$$

所以：

$$
\boxed{
m_L(\xi)\longrightarrow+\infty
\qquad
(|\xi|\to\infty).
}
\tag{398.4}
$$

---

## 定义 398.1（阈值危险集）

给定：

$$
a>0,
$$

定义：

$$
\boxed{
B_{L,a}
=
\left\{
\xi\in\mathbb R:
m_L(\xi)<a
\right\}.
}
\tag{398.5}
$$

---

## 定理 398.1（Archimedean confinement）

对任意固定 \(L,a>0\)：

$$
\boxed{
B_{L,a}
\text{ 是有界、对称、有限个开区间的并。}
}
\tag{398.6}
$$

### 证明

\(m_L\) 是实解析偶函数：

* digamma 在直线 \(1/4+i\mathbb R/2\) 上无极点；
* prime side 是有限三角多项式。

由式 (398.4)，其 \(a\)-sublevel set 有界。

边界点满足：

$$
m_L(\xi)=a.
$$

实解析非恒定函数在紧区间内只有有限多个零点，否则由解析唯一性将恒等于 \(a\)，与 \(m_L(\xi)\to\infty\) 矛盾。∎

---

## 398.1 回归只在有限窗口内危险

定义最粗 confinement radius：

$$
\boxed{
R_L(a)
=
\inf
\left\{
R:
a_\infty(\xi)\ge2W_L+a
\quad
\forall|\xi|\ge R
\right\}.
}
\tag{398.7}
$$

则：

$$
\boxed{
B_{L,a}
\subset[-R_L(a),R_L(a)].
}
\tag{398.8}
$$

因此：

$$
\boxed{
\text{finite-prime recurrence 在任意高频处仍存在，}
}
$$

但：

$$
\boxed{
\text{超过 }R_L(a)\text{ 后，
Archimedean 屏障必然压倒全部有限 prime coherence。}
}
$$

这修正了上一轮的 recurrence 难题：

> recurrence 不能被排除；
> 但对固定空间支撑，它只在一个有限频率窗口中可能影响正性。

---

# 第三百九十九部　Slepian 危险观察者

令：

$$
\mathscr F
=
(2\pi)^{-1/2}\widehat{\phantom f}
$$

为 unitary Fourier transform。

对任意有限测度频率集合：

$$
B\subset\mathbb R,
$$

定义 band projection：

$$
\boxed{
\mathsf B_B
=
\mathscr F^{-1}
1_B
\mathscr F.
}
\tag{399.1}
$$

定义 time projection：

$$
\boxed{
\mathsf T_Lf
=
\mathbf1_{[-L,L]}f.
}
\tag{399.2}
$$

定义 Slepian concentration operator：

$$
\boxed{
\mathsf C_{L,B}
=
\mathsf T_L
\mathsf B_B
\mathsf T_L.
}
\tag{399.3}
$$

它是正、紧、自伴、trace-class contraction，谱位于：

$$
[0,1].
$$

其特征值测量一个支撑在 \([-L,L]\) 的状态能有多少 Fourier 能量集中在 \(B\) 中。经典 Slepian–Landau–Pollak 理论正是把时频浓缩转化成这类紧自伴算子的谱问题；现代定量结果继续证明其特征值集中在 \(0\) 与 \(1\) 附近，有效维数由时频相空间体积控制。([arXiv][1])

---

## 399.1 精确迹公式

在完整的 \(L^2([-L,L])\) 上：

$$
\boxed{
\operatorname{Tr}\mathsf C_{L,B}
=
\frac{|[-L,L]|\cdot|B|}{2\pi}
=
\frac{L|B|}{\pi}.
}
\tag{399.4}
$$

限制到偶子空间后，迹只会减小。

---

## 399.2 Sticky spectral projection

给定：

$$
0<\eta<1,
$$

定义：

$$
\boxed{
P_{L,B,\eta}
=
\mathbf1_{(\eta,1]}
(\mathsf C_{L,B}).
}
\tag{399.5}
$$

它选出全部在危险频率集 \(B\) 中具有超过 \(\eta\) 能量比例的状态。

称其为：

$$
\boxed{
\textbf{Slepian sticky space}.
}
$$

其秩满足：

$$
\boxed{
\operatorname{rank}P_{L,B,\eta}
\le
\frac{\operatorname{Tr}\mathsf C_{L,B}}{\eta}
\le
\frac{L|B|}{\pi\eta}.
}
\tag{399.6}
$$

若只使用粗 confinement interval：

$$
B\subset[-R,R],
$$

则：

$$
\boxed{
\operatorname{rank}P_{L,B,\eta}
\le
\frac{2LR}{\pi\eta}.
}
\tag{399.7}
$$

---

# 第四百部　安全补空间的统一正谱隙

取：

$$
B=B_{L,a}.
$$

定义危险深度：

$$
\boxed{
b_{L,a}
=
\max
\left(
0,
-\inf_{\xi\in B_{L,a}}m_L(\xi)
\right).
}
\tag{400.1}
$$

于是：

$$
\boxed{
m_L(\xi)\ge
\begin{cases}
a,&\xi\notin B_{L,a},\\
-b_{L,a},&\xi\in B_{L,a}.
\end{cases}
}
\tag{400.2}
$$

选择：

$$
\boxed{
0<\eta<
\frac{a}{a+b_{L,a}}.
}
\tag{400.3}
$$

先取 Slepian sticky projection：

$$
P_{\mathrm{Sl}}
=
P_{L,B_{L,a},\eta}.
$$

为使 pole rank-one 项完全落入有限块，再加入 pole vector：

$$
\boxed{
P
=
P_{\mathrm{Sl}}
\vee
P_{\operatorname{span}\{v_L\}}.
}
\tag{400.4}
$$

令：

$$
\boxed{
Q=I-P.
}
\tag{400.5}
$$

---

## 定理 400.1（Safe-complement gap）

对所有：

$$
f\in Q\mathcal H_L,
$$

有：

$$
\boxed{
\mathfrak q_L[f]
\ge
\delta_{L,a,\eta}\|f\|_2^2,
}
\tag{400.6}
$$

其中：

$$
\boxed{
\delta_{L,a,\eta}
=
a-(a+b_{L,a})\eta
>0.
}
\tag{400.7}
$$

### 证明

由于：

$$
f\perp P_{\mathrm{Sl}},
$$

Slepian spectral theorem 给出：

$$
\frac1{2\pi}
\int_{B_{L,a}}
|\widehat f(\xi)|^2\,d\xi
=
\langle f,\mathsf C_{L,B_{L,a}}f\rangle
\le
\eta\|f\|_2^2.
$$

所以：

$$
\begin{aligned}
\frac1{2\pi}
\int m_L|\widehat f|^2
&\ge
a(1-\eta)\|f\|^2
-
b_{L,a}\eta\|f\|^2\\
&=
\delta_{L,a,\eta}\|f\|^2.
\end{aligned}
$$

又因为：

$$
f\perp v_L,
$$

pole 项为零。∎

---

## 400.1 Sticky 维数

$$
\boxed{
\dim P
\le
1+
\frac{L|B_{L,a}|}{\pi\eta}.
}
\tag{400.8}
$$

因此，固定 \(L\) 后：

$$
\boxed{
\text{除有限多个 Slepian sticky modes 外，
全部状态已经具有统一严格正余量。}
}
$$

---

# 第四百零一部　负谱指标的有限性

令：

$$
n_-(A_L)
$$

表示 \(A_L\) 的负谱重数，按 multiplicity 计。

---

## 定理 401.1（Finite negative-index bound）

$$
\boxed{
n_-(A_L)
\le
\dim P.
}
\tag{401.1}
$$

### 证明

假设存在维数大于 \(\dim P\) 的负定子空间 \(V\)。

由于：

$$
\operatorname{codim}Q=\dim P,
$$

必存在：

$$
0\neq f\in V\cap Q.
$$

但定理 400.1 给出：

$$
\langle f,A_Lf\rangle
\ge
\delta\|f\|^2>0,
$$

与 \(V\) 负定矛盾。∎

---

## 401.1 含义

这已经证明：

$$
\boxed{
\text{任何固定支撑尺度上的 RH 障碍，
都只能拥有有限个独立负方向。}
}
$$

即使原始问题生活在无限维函数空间中，其负性指标也被 Slepian 相空间维数控制。

---

# 第四百零二部　Feshbach–Schur 精确消元

将 Hilbert 空间分解为：

$$
\mathcal H_L
=
P\mathcal H_L
\oplus
Q\mathcal H_L.
$$

相应地，将 \(A_L\) 写成块矩阵：

$$
\boxed{
A_L
=
\begin{pmatrix}
A_{PP}&A_{PQ}\\
A_{QP}&A_{QQ}
\end{pmatrix}.
}
\tag{402.1}
$$

定理 400.1 保证：

$$
\boxed{
A_{QQ}\ge\delta I,
}
\tag{402.2}
$$

所以：

$$
A_{QQ}^{-1}
$$

存在且：

$$
0<A_{QQ}^{-1}\le\delta^{-1}I.
$$

定义有限维 Feshbach–Schur operator：

$$
\boxed{
F_L
=
A_{PP}
-
A_{PQ}
A_{QQ}^{-1}
A_{QP}.
}
\tag{402.3}
$$

Feshbach–Schur 方法正是利用这一 Schur complement 精确消除补空间，并将谱问题压缩到选定有限子空间；其优势包括显式估计和可迭代的降维。([arXiv][2])

---

## 定理 402.1（Exact sticky reduction）

$$
\boxed{
A_L\ge0
\iff
F_L\ge0.
}
\tag{402.4}
$$

并且：

$$
\boxed{
n_-(A_L)=n_-(F_L).
}
\tag{402.5}
$$

### 证明

对：

$$
p\in P\mathcal H_L,
\qquad
q\in Q\mathcal H_L,
$$

令：

$$
r=A_{QQ}^{-1}A_{QP}p.
$$

直接完成平方：

$$
\boxed{
\begin{aligned}
\langle p+q,A_L(p+q)\rangle
={}&
\langle q+r,A_{QQ}(q+r)\rangle\\
&+
\langle p,F_Lp\rangle.
\end{aligned}
}
\tag{402.6}
$$

第一项非负且可通过取：

$$
q=-r
$$

使其为零。

所以二次型的全部负性恰由 \(F_L\) 决定，负惯性指标也保持。∎

---

## 402.1 Deng self-energy

定义：

$$
\boxed{
\Sigma_L
=
A_{PQ}
A_{QQ}^{-1}
A_{QP}
\succeq0.
}
\tag{402.7}
$$

则：

$$
\boxed{
F_L=A_{PP}-\Sigma_L.
}
\tag{402.8}
$$

这里：

* \(A_{PP}\)：bare sticky block；
* \(\Sigma_L\)：安全补空间被积分掉以后产生的 self-energy counterterm；
* \(F_L\)：真正的 renormalized sticky matrix。

所以：

$$
\boxed{
\text{Deng 式消元不能只删除 non-sticky states，}
}
$$

而必须保留它们通过：

$$
\Sigma_L
$$

反馈给 sticky block 的精确影响。

---

# 第四百零三部　可计算的有限充分证书

精确 \(F_L\) 需要计算：

$$
A_{QQ}^{-1}.
$$

但由：

$$
A_{QQ}^{-1}\le\delta^{-1}I,
$$

有：

$$
\Sigma_L
\le
\delta^{-1}A_{PQ}A_{QP}.
$$

定义保守有限矩阵：

$$
\boxed{
G_L
=
A_{PP}
-
\delta^{-1}
A_{PQ}A_{QP}.
}
\tag{403.1}
$$

---

## 定理 403.1（Finite certified lower matrix）

$$
\boxed{
G_L\ge0
\Longrightarrow
F_L\ge0
\Longrightarrow
A_L\ge0.
}
\tag{403.2}
$$

所以只需证明一个显式有限 Hermitian matrix：

$$
G_L
$$

正半定，就能严格证明支撑尺度 \(L\) 上的全部 Weil 测试正性。

---

## 403.1 矩阵元

取 \(P\mathcal H_L\) 的正交基：

$$
e_1,\ldots,e_N.
$$

则：

$$
\boxed{
(G_L)_{ij}
=
\langle e_i,A_Le_j\rangle
-
\delta^{-1}
\langle QA_Le_i,QA_Le_j\rangle.
}
\tag{403.3}
$$

每个矩阵元只涉及：

1. 有限多个：

   $$
   n\le e^{2L}
   $$

   的 prime-power 数据；

2. 一个显式 digamma multiplier 积分；

3. pole rank-one 读数；

4. Slepian eigenfunctions 的有限积分。

因此它适合：

$$
\boxed{
\text{区间算术}
+
\text{有限矩阵最小特征值证书}.
}
$$

---

## 403.2 精确反例重构

若精确 Feshbach matrix \(F_L\) 有负向量：

$$
p\neq0,
\qquad
\langle p,F_Lp\rangle<0,
$$

则定义：

$$
\boxed{
f_p
=
p-
A_{QQ}^{-1}A_{QP}p.
}
\tag{403.4}
$$

由式 (402.6)：

$$
\boxed{
\langle f_p,A_Lf_p\rangle
=
\langle p,F_Lp\rangle<0.
}
\tag{403.5}
$$

所以有限矩阵的负 eigenvector 可以显式提升为原始 Weil 测试空间中的负见证。

---

# 第四百零四部　Pole rank-one 的有限修复能力

将 \(A_L\) 分解为：

$$
\boxed{
A_L
=
A_L^{(0)}
+
2|v_L\rangle\langle v_L|,
}
\tag{404.1}
$$

其中 \(A_L^{(0)}\) 只含 prime 与 Archimedean multiplier。

由于我们已经把：

$$
v_L
$$

加入 \(P\)，所以：

$$
Qv_L=0.
$$

因此 pole 项不进入：

* \(A_{QQ}\)；
* \(A_{PQ}\)；
* self-energy \(\Sigma_L\)。

定义 pole-free Feshbach matrix：

$$
F_L^{(0)}.
$$

则精确有：

$$
\boxed{
F_L
=
F_L^{(0)}
+
2|p_L\rangle\langle p_L|,
}
\tag{404.2}
$$

其中 \(p_L\) 是 \(v_L\) 在有限 sticky 基中的坐标向量。

---

## 定理 404.1（Pole capacity rank one）

$$
\boxed{
n_-(F_L)
\ge
n_-(F_L^{(0)})-1.
}
\tag{404.3}
$$

因此若：

$$
F_L\ge0,
$$

必有：

$$
\boxed{
n_-(F_L^{(0)})\le1.
}
\tag{404.4}
$$

即 pole pair 最多只能消除一个负方向。

---

## 404.1 单负方向的精确修复条件

进一步假设：

* \(F_L^{(0)}\) 可逆；
* \(n_-(F_L^{(0)})=1\)。

则由 rank-one inertia formula：

$$
\boxed{
F_L\ge0
\iff
2
\left\langle
p_L,
(F_L^{(0)})^{-1}p_L
\right\rangle
\le-1.
}
\tag{404.5}
$$

所以 pole 是否能修复唯一负方向，不是象征性的“极点有帮助”，而是一个可计算的有限标量条件。

---

# 第四百零五部　Feshbach 消元的精确可迭代性

设 Hilbert 空间进一步分解为：

$$
\mathcal H
=
\mathcal H_0
\oplus
\mathcal H_1
\oplus
\mathcal H_2,
$$

其中 \(\mathcal H_2\) 已有严格正谱隙。

可以先消去：

$$
\mathcal H_2,
$$

得到作用于：

$$
\mathcal H_0\oplus\mathcal H_1
$$

的有效算子；然后再消去 \(\mathcal H_1\)。

也可以一次性消去：

$$
\mathcal H_1\oplus\mathcal H_2.
$$

两种结果相同。

---

## 定理 405.1（Schur complement associativity）

在所有相关逆算子存在时：

$$
\boxed{
\operatorname{Schur}_{\mathcal H_0}
\left(
\operatorname{Schur}_{\mathcal H_0\oplus\mathcal H_1}(A)
\right)
=
\operatorname{Schur}_{\mathcal H_0}(A).
}
\tag{405.1}
$$

它可由三块 Gaussian elimination 直接验证。

因此：

$$
\boxed{
\text{多尺度 Feshbach 重整化是精确的，而非近似叙事。}
}
$$

---

## 405.1 Wang–Deng 的正式分工

### Wang 层（405.1）

在每一尺度选择投影：

$$
P_j
$$

并证明补空间：

$$
Q_j
$$

具有严格 gap：

$$
Q_jA_jQ_j\ge\delta_jQ_j.
$$

即：

$$
\boxed{
\text{识别哪些状态仍可能 sticky。}
}
$$

### Deng 层（405.1）

计算：

$$
\boxed{
A_{j+1}
=
P_jA_jP_j
-
P_jA_jQ_j
(Q_jA_jQ_j)^{-1}
Q_jA_jP_j.
}
\tag{405.2}
$$

即：

$$
\boxed{
\text{把安全历史精确收缩成 self-energy counterterm。}
}
$$

两者合成：

$$
\boxed{
\text{危险状态分类}
+
\text{精确安全消元}
=
\text{有限维重整化流}.
}
$$

---

# 第四百零六部　支撑尺度上的有限矩阵塔

定义：

$$
\mathsf{WP}(L)
$$

为式 (397.8) 的支撑-\(L\) Weil 正性。

---

## 定理 406.1（Support-\(L\) finite reduction）

对任意：

$$
L>0,
$$

任选：

$$
a>0,
\qquad
0<\eta<
\frac{a}{a+b_{L,a}},
$$

并按上述方法构造 \(P,Q,F_L\)。

则：

$$
\boxed{
\mathsf{WP}(L)
\iff
F_L\ge0.
}
\tag{406.1}
$$

所以每个固定 \(L\) 的无限维正性问题，精确等价于一个有限维 Hermitian matrix 的正性问题。

---

## 406.1 全局矩阵塔

经典 Weil 判据所需要的是：

$$
\boxed{
\mathsf{WP}(L)
\quad
\forall L>0.
}
$$

因此全局问题形成一个有限矩阵塔：

$$
\boxed{
F_{L_1},F_{L_2},F_{L_3},\ldots,
\qquad
L_j\uparrow\infty.
}
\tag{406.2}
$$

仓库当前已经完成塔中每层所需的：

* 无假设显式公式；
* Fourier–Laplace convention；
* prime finite support；
* convolution-square critical-line positivity；

但尚未加入本轮的 Slepian/Feshbach 正性层。

---

# 第四百零七部　Weil Sticky Dimension

定义固定参数下的 sticky dimension：

$$
\boxed{
\mathfrak s_L(a,\eta)
=
1+
\operatorname{rank}
P_{L,B_{L,a},\eta}.
}
\tag{407.1}
$$

其中额外的 \(1\) 是 pole direction。

有：

$$
\boxed{
\mathfrak s_L(a,\eta)
\le
1+
\frac{
L|B_{L,a}|
}{
\pi\eta
}.
}
\tag{407.2}
$$

定义最优 sticky complexity：

$$
\boxed{
\mathfrak s_L^*
=
\inf_{\substack{a>0\\
0<\eta<a/(a+b_{L,a})}}
\mathfrak s_L(a,\eta).
}
\tag{407.3}
$$

它是 OACTC 中一个新的结构复杂度：

$$
\boxed{
\mathfrak s_L^*
=
\text{在支撑尺度 }L
\text{ 上完整观察全部潜在负性所需的最小有限状态数。}
}
$$

---

## 407.1 相空间近似

Slepian 理论表明，在规则时频区域和较大相空间体积下，浓缩算子的高特征值数量以：

$$
\frac{|[-L,L]|\cdot|B|}{2\pi}
=
\frac{L|B|}{\pi}
$$

为主项，只有较窄的过渡谱带。([arXiv][1])

所以：

$$
\boxed{
\frac{L|B_{L,a}|}{\pi}
}
$$

不只是粗上界，也应当近似描述实际 sticky state 数量。

但这是一种复杂度估计，不是正性证明。

---

# 第四百零八部　Bohr-to-thick 桥不再是逻辑必需

上一轮仍有一个开放桥：

$$
\text{Bohr 危险集低密度}
\overset{?}{\Longrightarrow}
\text{thick good set}
\overset{?}{\Longrightarrow}
\text{Paley--Wiener 正性}.
$$

本轮表明：

$$
\boxed{
\text{这一桥可以完全绕过。}
}
$$

原因是：

1. \(B_{L,a}\) 由完整 multiplier \(m_L\) 直接定义；
2. \(B_{L,a}\) 有限测度且有界；
3. Slepian operator 精确测量测试函数可集中多少能量于 \(B_{L,a}\)；
4. 全部高浓缩状态组成有限子空间；
5. 其正交补自动具有严格正 gap；
6. 有限子空间由 Feshbach matrix 精确处理。

所以：

$$
\boxed{
\text{低密度}
\to
\text{thickness}
}
$$

只是一种改善 sticky rank 的估计工具，而不再是证明架构的逻辑支柱。

---

# 第四百零九部　严格计算协议

对一个给定的 \(L\)，可以执行以下有限证书程序。

## 409.1 乘子隔离

用区间算术计算：

$$
m_L(\xi)
$$

并严格隔离：

$$
B_{L,a}
=
\{m_L<a\}.
$$

因为 \(B_{L,a}\) 是有限个区间的并，这一步可输出：

* 区间端点证书；
* 总测度；
* 最低 multiplier 值；
* confinement radius。

---

## 409.2 Slepian 证书

构造多频带 concentration operator：

$$
\mathsf C_{L,B_{L,a}}.
$$

严格证明：

$$
\lambda_{N+1}
\le\eta.
$$

于是前 \(N\) 个 eigenmodes 加 pole vector 就构成完整 sticky space。

---

## 409.3 残余 gap

计算：

$$
\delta=a-(a+b)\eta>0.
$$

这给出：

$$
A_{QQ}\ge\delta Q.
$$

---

## 409.4 有限矩阵

计算：

$$
A_{PP},
\qquad
A_{PQ}A_{QP},
$$

并首先尝试证明保守矩阵：

$$
G_L
=
A_{PP}
-
\delta^{-1}A_{PQ}A_{QP}
$$

正半定。

若该证书过弱，再计算更精确的：

$$
F_L
=
A_{PP}
-
A_{PQ}A_{QQ}^{-1}A_{QP}.
$$

---

## 409.5 输出

程序只能有三种可信输出：

$$
\boxed{
\begin{array}{c|l}
\text{PSD certificate}
&\mathsf{WP}(L)\text{ 已严格证明}\\
\text{negative eigenvalue}
&\text{构造实际 Weil 负见证}\\
\text{undetermined}
&\text{提高 Slepian rank 或积分精度}
\end{array}
}
$$

不能把有限数值网格上“没有发现负值”当作证明。

---

# 第四百一十部　新的硬性负结论

## 410.1 有限降维不等于 RH 已证

$$
\boxed{
F_L\text{ 有限维}
}
$$

只说明每个固定 \(L\) 可决定。

还必须：

$$
L\to\infty
$$

控制整个矩阵塔。

---

## 410.2 Trace bound 可能极其巨大

粗 confinement radius 使用：

$$
|p_L|\le2W_L
$$

可能非常浪费。

所以：

$$
\frac{2LR_L}{\pi\eta}
$$

虽有限，却可能完全不适于实际计算。

真正有效的复杂度依赖实际 sublevel set：

$$
|B_{L,a}|,
$$

而不是包含它的整个大区间。

---

## 410.3 Pole 不能修复多维负谱

pole 项只有 rank one。

若 pole-free effective matrix 有两个或更多负方向，则最终正性不可能由 pole 单独恢复。

---

## 410.4 Bohr recurrence 不再构成无限维障碍

固定 \(L\) 时，Archimedean confinement 把危险 recurrence 限制在有限频率范围。

所以真正问题不是“无限多 recurrence peaks”，而是：

$$
\boxed{
\text{有限频率窗口内的有限个高浓缩 Slepian modes。}
}
$$

---

## 410.5 不应继续制造新的 RH 等价判据

本轮以后，真正的新进展应当表现为以下至少一项：

$$
\boxed{
\begin{aligned}
&\text{严格缩小 }|B_{L,a}|;\\
&\text{严格降低 sticky rank};\\
&\text{证明 residual gap};\\
&\text{计算 Feshbach self-energy};\\
&\text{证明有限 sticky matrix PSD};\\
&\text{控制这些证书随 }L\to\infty\text{ 的增长}.
\end{aligned}
}
$$

再构造一个新的 Pick、Hankel、Clark 或 Fredholm 等价形式，不再减少中心困难。

---

# 第四百一十一部　建议形式化顺序

```text
D5/S3/Weil/Multiplier/
  SupportScalePrimeMultiplier.lean
  ArchimedeanMultiplier.lean
  FixedScaleWeilQuadraticForm.lean
  PoleVectorRepresentation.lean
  ArchimedeanConfinement.lean
  DangerSetFiniteIntervals.lean

D5/S3/Weil/SlepianObserver/
  FrequencyProjection.lean
  TimeFrequencyConcentration.lean
  ConcentrationTrace.lean
  StickySpectralProjection.lean
  StickyRankBound.lean
  PoleAugmentedStickySpace.lean

D5/S3/Weil/SafeComplement/
  DangerDepth.lean
  FrequencyMassBound.lean
  SafeComplementGap.lean
  FiniteNegativeIndex.lean

D5/S3/Weil/FeshbachSticky/
  BlockQuadraticCompletion.lean
  ExactSchurReduction.lean
  InertiaPreservation.lean
  SelfEnergyCounterterm.lean
  ConservativeFiniteCertificate.lean
  NegativeWitnessLift.lean

D5/S3/Weil/PoleRescue/
  PoleRankOneUpdate.lean
  PoleNegativeIndexCapacity.lean
  SingleNegativeDirectionRescue.lean

D5/S3/Weil/FeshbachRG/
  NestedSchurAssociativity.lean
  MultiscaleStickyElimination.lean
  WeilStickyDimension.lean
  SupportScaleFiniteMatrixTower.lean
```

首批最值得闭合的定理是：

$$
\boxed{
m_L(\xi)\to+\infty,
}
$$

$$
\boxed{
B_{L,a}\text{ 有界且为有限区间并},
}
$$

$$
\boxed{
\operatorname{rank}P_{L,B,\eta}
\le
\frac{L|B|}{\pi\eta},
}
$$

$$
\boxed{
Q A_L Q\ge
\left[a-(a+b)\eta\right]Q,
}
$$

以及：

$$
\boxed{
A_L\ge0
\iff
F_L\ge0.
}
$$

---

# 本轮最终结论

此前 OACTC 的中心架构是：

$$
\boxed{
\text{有限 sticky matrix}
+
\text{正 residual operator}.
}
$$

本轮终于把这句话变成了一个精确的定理。

对每个固定支撑尺度 \(L\)，定义完整 Weil multiplier：

$$
\boxed{
m_L(\xi)
=
\Re\psi
\left(
\frac14+\frac{i\xi}{2}
\right)
-\log\pi
-
2\sum_{\log n\le2L}
\frac{\Lambda(n)}{\sqrt n}
\cos(\xi\log n).
}
$$

Archimedean 项强迫：

$$
m_L(\xi)\to+\infty.
$$

所以全部危险频率落入有限集合：

$$
B_{L,a}.
$$

Slepian operator 把能高度集中于该集合的所有状态压缩为有限维空间：

$$
P.
$$

其正交补具有严格 gap：

$$
QA_LQ\ge\delta Q.
$$

随后 Feshbach–Schur 消元给出有限矩阵：

$$
\boxed{
F_L
=
PA_LP
-
PA_LQ
(QA_LQ)^{-1}
QA_LP.
}
$$

并且：

$$
\boxed{
A_L\ge0
\iff
F_L\ge0.
}
$$

所以真正剩余的 RH 问题已不再是一个不可操作的无限维正性断言，而是：

$$
\boxed{
\text{能否证明所有支撑尺度 }L
\text{ 的有限 renormalized sticky matrices }F_L
\text{ 都正半定？}
}
$$

更深的一句话是：

$$
\boxed{
\text{Archimedean 完成负责把危险频率囚禁在有限区域，}
}
$$

$$
\boxed{
\text{Slepian 理论负责识别有限个真正能看见该区域的状态，}
}
$$

而：

$$
\boxed{
\text{Feshbach 理论负责把其余无限状态无损压缩成有限 self-energy。}
}
$$

这正是此前设想的 Wang–Deng 科学方法第一次形成严格闭环：

$$
\boxed{
\text{Wang：证明补空间有 gap；}
\qquad
\text{Deng：将补空间精确消元；}
\qquad
\text{最终：只剩有限 sticky matrix。}
}
$$

[1]: https://arxiv.org/abs/2301.09616 "https://arxiv.org/abs/2301.09616"
[2]: https://arxiv.org/abs/2105.02058 "https://arxiv.org/abs/2105.02058"
