<!-- editorial-note:preface:start -->
# Robin 分层损失、全素数连续包络与联合补层（编者拟题）

**编者说明。** 题名为描述性编者拟题。下文保留来稿的顺序与原文；“本轮”“上一轮”“我核对了”“已核验”等表述均沿用作者叙述，归属于作者，不作为编者的核验声明。以“编者注”标识的文字补足符号、适用域与局部证明细节，原有正文保留。
<!-- editorial-note:preface:end -->

可以继续推进。这一轮可以得到三项更实质的结果：

1. **把上一轮的整体 Jensen 下界，升级为逐层保留联合信息的精确分解。**
2. **完全求出允许全部素数、允许连续指数时的最优配置，并精确计算整数配置偏离它的损失。**
3. **证明一个更强的 Robin 充分条件：许多小素数方向的微小缺口可以联合起来，产生严格余量。**

其中第三项直接扩大了我们已经能够证明的整数范围；第二项则明确指出，完成 RH 需要多大量级的整数修正。

本轮以项目提交 [`98d92f3c…`](https://github.com/the-omega-institute/trureturing/tree/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa) 为源码基准，重点衔接三指数连续图与完整价格损失分解。相关文档仍明确保留全域有符号估计这一义务。下面给出普通数学证明，没有把源码阅读当作 Lean 构建验证。[三指数坐标图，§13](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)；[连续包络与整数损失，§§457–458](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_FULL_STOCK.md)

---

<a id="section-1"></a>

## 一、固定目标：需要控制的是同一个整数的完整对数余量

<!-- editorial-note:domains:start -->
**编者注（符号与适用域）。** 全文 $\log$ 为自然对数，$n$ 为正整数，$\sigma(n)=\sum_{d\mid n,\ d>0}d$，$\gamma$ 为 Euler–Mascheroni 常数，$v_p(n)$ 为素数 $p$ 在 $n$ 中的非负整数指数；当 $p\mid n$ 时，$a_p=v_p(n)\ge1$。$Z(n)>0$。有限指数损失、素数分组和整数连续包络比较以 $n\ge2$ 为域，此时 $r=\omega(n)\ge1$。涉及正的 $R(n)$、实数 $\log R(n)$ 或 $G(K)$ 的式子另需 $\log\log n>0$，即整数情形 $n\ge3$；Robin 目标始终为 $n>5040$。特别地，$n=2$ 可用于损失及包络恒等式，不能代入实数 $\log R(n)$。
<!-- editorial-note:domains:end -->

定义

$$
Z(n)=\frac{\sigma(n)}n,
\qquad
R(n)=\frac{Z(n)}{e^\gamma\log\log n}.
$$

Robin 目标是

$$
\boxed{R(n)<1\qquad(n>5040).}
$$

设

$$
n=\prod_{p\mid n}p^{a_p}.
$$

则

$$
Z(n)
=
\prod_{p\mid n}
\frac{1-p^{-(a_p+1)}}{1-p^{-1}}.
$$

令

$$
t_p=(a_p+1)\log p,
\qquad
\psi(t)=-\log(1-e^{-t}),\quad t>0.
$$

于是有限指数造成的损失恰为

<a id="eq-1"></a>

$$
\boxed{
D_{\rm cap}(n)=\sum_{p\mid n}\psi(t_p).
}
\tag{1}
$$

而且

<a id="eq-2"></a>

$$
\log Z(n)
=
\sum_{p\mid n}\log\frac p{p-1}
-
D_{\rm cap}(n).
\tag{2}
$$

因此，若能对 $D_{\rm cap}$ 给出足够强的下界，就能对 $Z(n)$ 给出足够强的上界。

这里与三轴对数表示的连接是：

- 素因子及指数给出实际来源；
- $t_p$ 保存乘法的对数尺度；
- $\psi(t_p)$ 保存有限几何和留下的非线性修正；
- 递归组合必须保留这些修正及其权重。

---

<a id="section-2"></a>

## 二、先检验上一轮的下界：单个整体平均确实会损失主要信息

上一轮由凸性得到

<a id="eq-3"></a>

$$
D_{\rm cap}(n)
\ge
r\psi\left(\frac1r\sum_{p\mid n}t_p\right),
\qquad r=\omega(n).
\tag{3}
$$

这个不等式正确，但可能过弱。

### 定理 1：在素数连乘族上，整体 Jensen 下界趋于零，实际损失却保持正量级

令

$$
n_r=\prod_{i=1}^r p_i,
$$

其中 $p_i$ 是第 $i$ 个素数。则

<a id="eq-4"></a>

$$
D_{\rm cap}(n_r)
=
-\sum_{i=1}^r\log(1-p_i^{-2})
\ge
\log\frac43>0.
\tag{4}
$$

但式 $(3)$ 的下界

$$
J_r
=
-r\log\left(1-n_r^{-2/r}\right)
$$

满足

<a id="eq-5"></a>

$$
\boxed{J_r\longrightarrow0.}
\tag{5}
$$

### 证明

因为 $p_i\ge i$，

$$
\log n_r
\ge
\log(r!)
\ge
\int_1^r\log t\,dt
=
r\log r-r+1.
$$

因此

$$
K_r:=n_r^{2/r}\ge\frac{r^2}{e^2}.
$$

利用

$$
-\log(1-x)\le\frac{x}{1-x},
\qquad0<x<1,
$$

<!-- editorial-note:jensen-domain:start -->
**编者注（分母为正的范围）。** 下列链式估计的最后一步使用 $r>e$，使 $r^2-e^2>0$；它是趋于无穷时的估计，不断言对所有正整数 $r$ 成立。此前 $D_{\rm cap}(n_r)\ge\log(4/3)$ 与 $0<J_r$ 对 $r\ge1$ 均有效。
<!-- editorial-note:jensen-domain:end -->

得到

$$
0<J_r
\le
\frac r{K_r-1}
\le
\frac{e^2r}{r^2-e^2}
\longrightarrow0.
$$

而实际损失至少包含素数 $2$ 的贡献：

$$
D_{\rm cap}(n_r)
\ge
-\log(1-2^{-2})
=
\log\frac43.
$$

证毕。

**这个检验说明：把所有素数方向压成一个平均值，会稀释小素数的主要贡献。** 所以接下来应保留分组差异，而不能只依靠“Jensen 不等式严格成立”。

---

<a id="section-3"></a>

## 三、定义三分树：把局部三轴组合提升为完整损失分解

我们现在定义一个新的算术读出层：叶子是实际素数方向，每个内部节点汇总两个或三个非空子块。每个节点都保留来源标签和权重。

这是明确的分组结构；原生 AURIC 五模式的合法性仍按项目定义使用。

<!-- editorial-note:tree:start -->
**编者注（分组对象）。** 此处使用有限有根树：叶子与同一个实际整数的不同素因子一一对应，每个内部节点有两个或三个非空子块，子块彼此不交且其并为父块，$r_v$ 为叶子数。此算术分组不自动取得原生 AURIC 五模式的操作合法性。
<!-- editorial-note:tree:end -->

### 定义 1：节点的尺度与损失

对节点 $v$，令

$$
r_v=\text{节点中包含的素数个数},
$$

$$
\mu_v=\frac1{r_v}\sum_{p\in v}t_p.
$$

如果 $v$ 的子节点为 $c$，定义局部修正

<a id="eq-6"></a>

$$
\boxed{
\mathcal J_v
=
\sum_c r_c\psi(\mu_c)
-r_v\psi(\mu_v).
}
\tag{6}
$$

由于

$$
\mu_v=\sum_c\frac{r_c}{r_v}\mu_c,
$$

这正是该局部合成中的加权凸性差额。

### 定理 2：全部损失等于根读出加上逐层非负修正

有

$$
\boxed{\mathcal J_v\ge0,}
$$

并且

<a id="eq-7"></a>

$$
\boxed{
D_{\rm cap}(n)
=
r_{\rm root}\psi(\mu_{\rm root})
+
\sum_{v\text{ 为内部节点}}\mathcal J_v.
}
\tag{7}
$$

### 证明

直接计算

$$
\psi''(t)=\frac{e^t}{(e^t-1)^2}>0.
$$

所以 $\psi$ 严格凸，式 $(6)$ 非负。

再将所有内部节点的式 $(6)$ 求和，中间节点贡献成对抵消，只留下根项和单点叶项。每个叶子贡献 $\psi(t_p)$，其总和就是 $D_{\rm cap}(n)$。证毕。

这带来一个很有用的结构：

$$
\boxed{
\text{粗读出}
+\text{第一层修正}
+\text{第二层修正}
+\cdots
=
\text{完整算术损失}.
}
$$

截断这棵树给出下界；逐层展开，所得下界单调增加；展开到单点时，恢复精确值。

### 定理 3：每个局部修正都有方差下界

令

$$
M_v=\max_c\mu_c.
$$

则

<a id="eq-8"></a>

$$
\boxed{
\mathcal J_v
\ge
\frac{e^{M_v}}{2(e^{M_v}-1)^2}
\sum_c r_c(\mu_c-\mu_v)^2.
}
\tag{8}
$$

等价地，

<a id="eq-9"></a>

$$
\boxed{
\mathcal J_v
\ge
\frac{e^{M_v}}{2r_v(e^{M_v}-1)^2}
\sum_{c<d}r_cr_d(\mu_c-\mu_d)^2.
}
\tag{9}
$$

### 证明

函数 $\psi''(t)$ 随 $t>0$ 递减。因此，在所有子均值与父均值之间，

$$
\psi''(t)\ge\frac{e^{M_v}}{(e^{M_v}-1)^2}.
$$

对每个子均值作二阶 Taylor 下界，再求加权和。一阶项由于

$$
\sum_c r_c(\mu_c-\mu_v)=0
$$

消失，得到式 $(8)$。式 $(9)$ 来自加权方差恒等式。证毕。

### 整数来源还保证非平凡节点严格为正

若两个不相交的非空素数块 $A,B$ 满足 $\mu_A=\mu_B$，则

$$
\left(\prod_{p\in A}p^{a_p+1}\right)^{|B|}
=
\left(\prod_{p\in B}p^{a_p+1}\right)^{|A|}.
$$

两边的素数支撑不相交，与唯一分解矛盾。

所以每个真正发生分组的内部节点都有

<a id="eq-10"></a>

$$
\boxed{\mathcal J_v>0.}
\tag{10}
$$

这一步已经把“三轴之间有差异”转成了一个严格的算术修正。要用于 Robin，还需要估计这些修正的总量。

---

<a id="section-4"></a>

## 四、把三个指数方向推广到全部素数：连续最优配置可以完全求出

项目 §13 的局部函数是

$$
h_p(u)
=
\log\frac{1-e^{-u}/p}{1-1/p},
\qquad u\ge0.
$$

当 $u=a\log p$ 时，

$$
h_p(a\log p)
=
\log\left(1+\frac1p+\cdots+\frac1{p^a}\right).
$$

其导数为

$$
h_p'(u)=\frac1{pe^u-1},
$$

<a id="eq-11"></a>

$$
h_p''(u)
=
-\frac{pe^u}{(pe^u-1)^2}<0.
\tag{11}
$$

现在允许全部素数方向，并固定总对数尺度

$$
\sum_pu_p=T.
$$

考虑最大化

$$
H(u)=\sum_ph_p(u_p),
$$

其中 $u_p\ge0$，且只有有限个非零坐标。

### 定理 4：全素数连续最优点唯一，并具有共同阈值

定义

<a id="eq-12"></a>

$$
T(K)=\sum_{p<K}\log\frac Kp,
\qquad K>2.
\tag{12}
$$

对于每个 $T>0$，存在唯一的 $K>2$ 满足 $T(K)=T$。最优配置为

<a id="eq-13"></a>

$$
\boxed{
u_p^*=\max\left\{0,\log\frac Kp\right\}.
}
\tag{13}
$$

最优值为

<a id="eq-14"></a>

$$
\boxed{
B(T)
=
\sum_{p<K}
\left[
\log\frac p{p-1}
+
\log\left(1-\frac1K\right)
\right].
}
\tag{14}
$$

### 证明

$T(K)$ 连续且严格递增。每当 $K$ 穿过一个素数，新项从零开始，所以没有跳跃；又 $T(K)\to\infty$。因此 $K$ 唯一存在。

令

$$
\alpha=\frac1{K-1}.
$$

对于 $p<K$，

$$
h_p'(u_p^*)=\alpha.
$$

凹性给出

$$
h_p(u_p)
\le
h_p(u_p^*)+\alpha(u_p-u_p^*).
$$

对于 $p\ge K$，

$$
h_p'(0)=\frac1{p-1}\le\alpha,
$$

所以

$$
h_p(u_p)\le\alpha u_p.
$$

逐素数求和，线性项由于相同的总尺度 $T$ 而消失，于是

$$
H(u)\le H(u^*).
$$

严格凹性保证唯一性。代入最优点即得式 $(14)$。证毕。

<!-- editorial-note:all-prime-boundary:start -->
**编者注（全素数与边界）。** 任一可行向量的支撑与 $u^*$ 的支撑之并仍有限，因此证明中的求和覆盖任意有限支撑，而非预先固定的素数集合。若 $K$ 本身是素数，$p=K$ 属于不活跃边界，$u_p^*=0$ 且 $h_p'(0)=\alpha$；严格凹性仍使该坐标取正值时切线不等式严格，从而不损害唯一性。
<!-- editorial-note:all-prime-boundary:end -->

对实际整数 $n$，取

$$
T=\log n,\qquad u_p=v_p(n)\log p,
$$

因此

<a id="eq-15"></a>

$$
\boxed{\log Z(n)\le B(\log n).}
\tag{15}
$$

这一步已经处理了可增长的素数支撑。

---

<a id="section-5"></a>

## 五、一个关键检验：最佳连续上界最终仍然太高

如果仅凭式 $(15)$ 证明 Robin，就需要

$$
B(T)<\gamma+\log\log T.
$$

但可以证明，充分大时恰好相反。

### 定理 5：连续包络与 Robin 边界之间有明确的正超额

<!-- editorial-note:g-domain:start -->
**编者注（连续余量的实数域）。** 本节 $G(K)$ 只在 $T(K)>1$ 时作为实数定义，因为 $\log\log T(K)$ 要求 $\log T(K)>0$。以下渐近式均指 $K\to\infty$，不对整个 $K>2$ 区间断言其定义或正性。
<!-- editorial-note:g-domain:end -->

定义

$$
G(K)
=
B(T(K))-\gamma-\log\log T(K).
$$

则

<a id="eq-16"></a>

$$
\boxed{
G(K)
=
\frac{\log\log K-1}{\log K}
+
O\left(
\frac{(\log\log K)^2}{(\log K)^2}
\right).
}
\tag{16}
$$

所以

<a id="eq-17"></a>

$$
\boxed{G(K)>0\quad\text{对所有充分大的 }K.}
\tag{17}
$$

这一结论不假设 RH。

### 证明

使用经典无条件素数定理，以及 Mertens 乘积估计

$$
\log\prod_{p\le K}\frac p{p-1}
=
\gamma+\log\log K+O((\log K)^{-2}).
$$

所需乘积估计可直接由 Rosser–Schoenfeld 定理 8 得到；我核对了原论文第 70 页的双边界及第 66 页的素数定理误差项。[Rosser–Schoenfeld，1962，原论文](http://denise.vella.chemla.free.fr/Rosser-Schoenfeld-1962.pdf)

<!-- editorial-note:classical-premises:start -->
**编者注（经典输入的精确范围）。** Rosser–Schoenfeld 原论文印刷页 66 的式 (2.21)–(2.22) 给出：存在正常数 $c,C,x_0$，使 $x\ge x_0$ 时

$$
|\pi(x)-\operatorname{li}(x)|<Cx\exp(-c\sqrt{\log x}).
$$

这里 $\pi(x)$ 是不超过 $x$ 的素数个数。印刷页 70 的定理 8、式 (3.28)–(3.29) 给出

$$
e^\gamma\log x\left(1-\frac{1}{2(\log x)^2}\right)
<\prod_{p\le x}\frac p{p-1}
<e^\gamma\log x\left(1+\frac{1}{2(\log x)^2}\right)
\qquad(x\ge286),
$$

其中左界本身适用于 $x>1$。对充分大的 $x$ 取对数即得正文的 $O((\log x)^{-2})$ 乘积估计；PNT 误差比任意固定次对数倒数更小，因而支持下面所用的展开精度。这些均为已归属文献的无条件前提。
<!-- editorial-note:classical-premises:end -->

令 $L=\log K$。由

$$
T(K)=\int_2^K\frac{\pi(t)}t\,dt
$$

得到

$$
T(K)
=
\frac K L+\frac{2K}{L^2}
+O\left(\frac K{L^3}\right).
$$

于是

<a id="eq-18"></a>

$$
\log\log T(K)
=
\log L-\frac{\log L}{L}
+
O\left(\frac{(\log L)^2}{L^2}\right).
\tag{18}
$$

另一方面，

$$
B(T(K))
=
\log\prod_{p\le K}\frac p{p-1}
+
\pi(K)\log\left(1-\frac1K\right),
$$

<!-- editorial-note:endpoint:start -->
**编者注（素数端点的抵消）。** 上一式把 $p<K$ 改写为 $p\le K$ 时，若 $K$ 恰为素数，新增贡献为 $\log(K/(K-1))+\log(1-1/K)=0$。故该式在端点也精确成立；它没有把边界素数当成正的连续指数。
<!-- editorial-note:endpoint:end -->

所以

<a id="eq-19"></a>

$$
B(T(K))
=
\gamma+\log L-\frac1L+O(L^{-2}).
\tag{19}
$$

式 $(19)$ 减式 $(18)$，即得式 $(16)$。主项最终为正，且误差相对主项趋零。证毕。

**这个结果排除了一个具体的证明捷径：把素数指数全部连续化，再只利用凹性，无法完成全域 Robin。**

原因也很清楚：连续模型允许把微小指数分配给大量素数；实际整数每增加一个素数方向，至少要支付完整一层的成本 $\log p$。

因此，需要把这种不可分割的整数成本精确计入。

---

<a id="section-6"></a>

## 六、整数损失可以写成逐素数非负项，并具有相对熵形式

### 定义 2：相对于共同阈值的局部损失

对 $K>2,\ q>1$，定义

<a id="eq-20"></a>

$$
\boxed{
d_K(q)
=
\log\frac{1-1/K}{1-1/q}
+
\frac{\log(q/K)}{K-1}.
}
\tag{20}
$$

### 定理 6：局部损失非负，且只在连续最优点取零

有

$$
d_K(q)\ge0,
$$

等号当且仅当 $q=K$。

**证明。** 令 $v=\log(q/K)$。则

$$
\frac d{dv}d_K(Ke^v)
=
\frac1{K-1}-\frac1{Ke^v-1},
$$

$$
\frac{d^2}{dv^2}d_K(Ke^v)
=
\frac{Ke^v}{(Ke^v-1)^2}>0.
$$

它在 $v=0$ 处取得唯一最小值零。证毕。

进一步，定义二元相对熵函数

$$
\operatorname{kl}(r\Vert s)
=
r\log\frac rs+(1-r)\log\frac{1-r}{1-s}.
$$

直接展开得到

<a id="eq-21"></a>

$$
\boxed{
d_K(q)
=
\frac K{K-1}
\operatorname{kl}\left(\frac1K\;\middle\Vert\;\frac1q\right).
}
\tag{21}
$$

这里将相对熵作为一个明确的数学函数使用，并不要求赋予参数额外的物理概率解释。

### 定理 7：Robin 余量具有一个精确的“连续超额减整数损失”分解

给定实际整数 $n\ge2$，令 $K$ 由

<a id="eq-22"></a>

$$
\boxed{\log n=T(K)}
\tag{22}
$$

唯一确定，并置

$$
q_p=p^{v_p(n)+1}.
$$

定义

<a id="eq-23"></a>

$$
\boxed{
\Delta_K(n)
=
\sum_{p<K}d_K(q_p)
+
\sum_{p\ge K}
\bigl[d_K(q_p)-d_K(p)\bigr].
}
\tag{23}
$$

第二个和只有 $p\mid n$ 的项非零，因此全部都是有限和。

则

$$
\Delta_K(n)\ge0,
$$

并且

<a id="eq-24"></a>

$$
\boxed{
\log Z(n)=B(\log n)-\Delta_K(n).
}
\tag{24}
$$

<!-- editorial-note:integer-log-domain:start -->
**编者注（定理 7 的域分开使用）。** $n\ge2$ 足以定义式 (22)–(24) 并得到 $\Delta_K(n)\ge0$；下列实数对数式 (25) 还需 $n\ge3$，等价地 $T(K)=\log n>1$。式 (26) 的 $n>5040$ 已满足此条件。对 $p\ge K$，非负性来自 $h_p'(0)\le1/(K-1)$ 的边界切线；按式 (22) 配置同一总尺度后，活跃与不活跃坐标的线性项才一并抵消。
<!-- editorial-note:integer-log-domain:end -->

所以

<a id="eq-25"></a>

$$
\boxed{
\log R(n)=G(K)-\Delta_K(n).
}
\tag{25}
$$

### 证明

对 $p<K$，令 $u_p=v_p(n)\log p$。逐项计算：

$$
d_K(q_p)
=
h_p(u_p^*)
+\frac{u_p-u_p^*}{K-1}
-h_p(u_p).
$$

对 $p\ge K$，

$$
d_K(q_p)-d_K(p)
=
\frac{u_p}{K-1}-h_p(u_p)\ge0.
$$

求和后，

$$
\sum_p(u_p-u_p^*)=0,
$$

线性项全部消失，剩下的正是

$$
B(\log n)-\log Z(n).
$$

再减去 Robin 的对数边界，即得式 $(25)$。证毕。

这一分解同时保留了：

- 连续最优配置中出现、实际整数却缺失的素数；
- 实际素因子的整数指数偏差；
- 实际整数中可能存在的更大素数方向。

因此，全局目标精确变成

<a id="eq-26"></a>

$$
\boxed{
\Delta_K(n)>G(K)
\qquad
\text{对所有 }n>5040,\quad T(K)=\log n.
}
\tag{26}
$$

### 可以证明严格整数修正，但必须检查量级

只使用素数 $2,3$，已经可以证明

<a id="eq-27"></a>

$$
\boxed{
\Delta_K(n)
\ge
\frac1{12K(3K-1)^2}>0
\qquad(K>3).
}
\tag{27}
$$

证明要点如下。每个素数方向的整数最小损失，只可能在连续指数两侧的相邻整数取得。对 $p=2,3$，对应的两个最优素数幂分别落在

$$
K/2\le q_2\le2K,
\qquad
K/3\le q_3\le3K.
$$

它们是不同整数，所以

$$
|\log q_2-\log q_3|\ge\frac1{3K}.
$$

而相关区间上的对数曲率至少为

$$
\frac{3K}{(3K-1)^2}.
$$

用二阶 Taylor 下界和

$$
x^2+y^2\ge\frac12(x-y)^2
$$

即可得到式 $(27)$。

<!-- editorial-note:bound-27:start -->
**编者注（式 (27) 对任意实际指数成立）。** 固定 $K>3$。对 $p=2,3$ 分别在所有 $j\ge1$ 中最小化 $d_K(p^j)$，记一个最小点为 $\widehat q_p$。因 $d_K(q)$ 在 $1<q<K$ 上递减、在 $q>K$ 上递增，最小点可从夹住 $K$ 的相邻两幂中选取；$K$ 恰为素数幂时可直接选该幂。于是 $K/p\le\widehat q_p\le pK$。原文此处的 $q_2,q_3$ 可读作这两个最小点，而非对任意实际指数的大小限制。实际 $q_p=p^{v_p(n)+1}$ 总满足 $d_K(q_p)\ge d_K(\widehat q_p)$，包括 $v_p(n)=0$ 的情形。

$\widehat q_2,\widehat q_3$ 是不同的正整数，且均不超过 $3K$，故其对数间距至少 $1/(3K)$。令 $x=\log(\widehat q_2/K)$、$y=\log(\widehat q_3/K)$；从零到这两点的对数线段均对应 $1<q\le3K$。由于 $q/(q-1)^2$ 递减，沿线段二阶导数至少为 $3K/(3K-1)^2$，而零点函数值和一阶导数均为零。因此

$$
\begin{aligned}
\Delta_K(n)
&\ge d_K(\widehat q_2)+d_K(\widehat q_3)\\
&\ge\frac{3K}{2(3K-1)^2}(x^2+y^2)\\
&\ge\frac{3K}{4(3K-1)^2}(x-y)^2\\
&\ge\frac{1}{12K(3K-1)^2}.
\end{aligned}
$$

第一步使用 $2,3<K$ 的活跃项及其余损失非负，故上述推导覆盖任意实际整数指数，不要求实际素数幂本身邻近 $K$。
<!-- editorial-note:bound-27:end -->

这个已证明的下界约为 $K^{-3}$，而连续超额的主量级是

$$
\frac{\log\log K}{\log K}.
$$

因此，式 $(27)$ 证明了严格分离，却尚不足以证明式 $(26)$。真正需要的是许多素数方向的联合损失。

---

<a id="section-7"></a>

## 七、进一步证明：许多微小缺口可以共同推出 Robin

下面给出本轮一个直接的无条件充分条件。

它使用已核验的 Axler 定理 1.3：

$$
Z(m)
<
e^\gamma
\left(
\log\log m+
\frac{A_0}{(\log\log m)^2}
\right),
\qquad m>5040,
$$

其中

$$
A_0=0.0094243.
$$

该输入本身不假设 RH。[Axler，*On Robin’s inequality*，v3，定理 1.3](https://arxiv.org/pdf/2110.13478v3)

<!-- editorial-note:axler:start -->
**编者注（Axler 输入的范围）。** v3 原文第 2 页定理 1.3 对有限例外集 $\mathcal A$ 之外的所有正整数给出严格上界；该集合最大元为 $5040$。因而正文只取 $m>5040$ 时无须逐项处理例外。原文写成 $e^\gamma\log\log m\left(1+0.0094243/(\log\log m)^3\right)$，与此处展开后的输入相同。
<!-- editorial-note:axler:end -->

### 定义 3：小素数方向的总截断损失

令

$$
\Lambda=\log\log n,
\qquad Y=\Lambda^4.
$$

定义

<a id="eq-28"></a>

$$
\boxed{
D_Y(n)
=
-\sum_{p\le Y}
\log\left(1-p^{-v_p(n)-1}\right).
}
\tag{28}
$$

这里包含 $p\nmid n$ 的情况：此时 $v_p(n)=0$，相应项记录这个素数方向完全缺失。

### 定理 8：联合补层不等式

若

$$
\Lambda\ge100,
$$

则

<a id="eq-29"></a>

$$
\boxed{
\log R(n)
<
\frac{A_0}{\Lambda^3}
+\frac2{\Lambda^4}
-D_Y(n).
}
\tag{29}
$$

因此，

<a id="eq-30"></a>

$$
\boxed{
D_Y(n)\ge
\frac{A_0}{\Lambda^3}
+\frac2{\Lambda^4}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{30}
$$

### 证明

取

$$
k=
\left\lceil\frac{8\log\Lambda}{\log2}\right\rceil,
\qquad
M=\prod_{p\le Y}p^k.
$$

这是给所有相关小素数方向同时补上 $k$ 层。

**第一步：补层收益是精确的。**

由 Euler 因子逐项相除，

<a id="eq-31"></a>

$$
\boxed{
\log Z(nM)-\log Z(n)
=
D_Y(n)-D_Y(nM).
}
\tag{31}
$$

**第二步：补层后的剩余截断可以统一控制。**

利用 $-\log(1-x)\le x/(1-x)$，有

<a id="eq-32"></a>

$$
D_Y(nM)
<
\frac{\pi(Y)}{2^{k+1}-1}
\le
\frac{Y}{2^k}
\le
\Lambda^{-4}.
\tag{32}
$$

**第三步：补层引起的尺度增加很小。**

因为 $\Lambda\ge100$，

$$
k\le17\log\Lambda.
$$

所以

$$
\log M
\le kY\log Y
\le68\Lambda^4(\log\Lambda)^2.
$$

令

$$
\delta=\log\log(nM)-\Lambda.
$$

则

<a id="eq-33"></a>

$$
\frac{\delta}{\Lambda}
\le
68\Lambda^3(\log\Lambda)^2e^{-\Lambda}
\le
\Lambda^{-4}.
\tag{33}
$$

最后一个显式界可以直接验证：函数

$$
68\Lambda^7(\log\Lambda)^2e^{-\Lambda}
$$

在 $\Lambda\ge100$ 上递减，且在 $100$ 处小于 $1$。

<!-- editorial-note:scale-bound:start -->
**编者注（式 (33) 的纸笔界）。** $\log2>1/2$ 且 $\log\Lambda>1$，故向上取整至多增加 $1$，给出 $k\le17\log\Lambda$。又 $\delta=\log(1+(\log M)e^{-\Lambda})\le(\log M)e^{-\Lambda}$。对 $F(\Lambda)=68\Lambda^7(\log\Lambda)^2e^{-\Lambda}$，有 $F'/F=7/\Lambda+2/(\Lambda\log\Lambda)-1<0$（$\Lambda\ge100$）。在端点，$\log100<5$ 及 $e>2$ 给出 $F(100)<68\cdot100^7\cdot25/2^{100}<1$；最后可用 $2^{10}>10^3$ 验证。因此式 (33) 在整段 $\Lambda\ge100$ 上有效。
<!-- editorial-note:scale-bound:end -->

**第四步：对同一个补层整数 $nM$ 使用 Axler 上界。**

有

$$
\begin{aligned}
\frac{Z(nM)}{e^\gamma\Lambda}
&<
\frac{\Lambda+\delta+A_0/(\Lambda+\delta)^2}{\Lambda}\\
&\le
1+\frac{\delta}{\Lambda}+\frac{A_0}{\Lambda^3}.
\end{aligned}
$$

取对数并使用 $\log(1+x)<x$：

$$
\log\frac{Z(nM)}{e^\gamma\Lambda}
<
\frac{\delta}{\Lambda}+\frac{A_0}{\Lambda^3}.
$$

结合式 $(31)$—$(33)$，得到

$$
\log R(n)
<
\frac{A_0}{\Lambda^3}
+\frac2{\Lambda^4}
-D_Y(n).
$$

证毕。

### 一个更容易使用的充分条件

<!-- editorial-note:condition-34:start -->
**编者注（式 (34) 继承的前提）。** 本小节仍取定理 8 的 $\Lambda=\log\log n\ge100$ 与 $Y=\Lambda^4$；式 (34) 不是对所有较小整数无条件适用的独立判据。
<!-- editorial-note:condition-34:end -->

因为

$$
-\log(1-x)>x,
$$

所以

<a id="eq-34"></a>

$$
\boxed{
\sum_{p\le\Lambda^4}p^{-v_p(n)-1}
\ge
\frac{A_0}{\Lambda^3}+\frac2{\Lambda^4}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{34}
$$

这比只寻找一个缺失素数更灵活：**每个方向的缺口都可以很小，只要总和达到所需规模，就能证明 Robin。**

---

<a id="section-8"></a>

## 八、潜在反例的必要结构进一步收紧

对定理 8 取逆否命题。

若

$$
\Lambda\ge100,\qquad R(n)\ge1,
$$

则

$$
D_Y(n)
<
\frac{A_0}{\Lambda^3}+\frac2{\Lambda^4}.
$$

每个单独项都不能超过总和，因此，对所有 $p\le Y$，

$$
p^{v_p(n)+1}
>
\frac{\Lambda^3}{A_0+2/\Lambda}.
$$

记

<a id="eq-35"></a>

$$
\boxed{
y=
\frac{\Lambda^3}{A_0+2/\Lambda}.
}
\tag{35}
$$

由于 $y<\Lambda^4$，这涵盖所有 $p\le y$，所以

<a id="eq-36"></a>

$$
\boxed{
R(n)\ge1,\ \log\log n\ge100
\quad\Longrightarrow\quad
\operatorname{lcm}(1,\ldots,\lfloor y\rfloor)\mid n.
}
\tag{36}
$$

<!-- editorial-note:lcm:start -->
**编者注（严格性与整除桥梁）。** 若记阈值为 $c=A_0/\Lambda^3+2/\Lambda^4=1/y$，则对每个 $p\le Y$，$1/q_p< -\log(1-1/q_p)\le D_Y(n)<c$，故 $q_p>y$。又 $\Lambda A_0+2>1$ 给出 $y<Y$。对任一 $p^j\le\lfloor y\rfloor$，必有 $j\le v_p(n)$，否则 $p^j\ge q_p>y$；这恰是式 (36) 的最小公倍数整除条件。
<!-- editorial-note:lcm:end -->

并且

$$
A_0+\frac2\Lambda<\frac3{100},
$$

故

<a id="eq-37"></a>

$$
\boxed{
y>\frac{100}{3}(\log\log n)^3.
}
\tag{37}
$$

相比上一轮的

$$
\operatorname{lcm}
\left(1,\ldots,\lfloor(\log\log n)^3\rfloor\right)\mid n,
$$

这次得到了更大的必要整除范围，而且还保留了更强的联合条件 $(29)$，没有只取逐素数推论。

但仍未形成矛盾，因为

$$
\log\operatorname{lcm}(1,\ldots,\lfloor y\rfloor)
\le y\log y
$$

在这里至多是 $\Lambda$ 的多项式乘对数规模，而

$$
\log n=e^\Lambda
$$

大得多。这样的必要因子仍然可以包含在 $n$ 中。

---

<a id="section-9"></a>

## 本轮实际推进到了哪里？

现在形成了两条互相补充、但不能重复计算同一损失的证明路线：

| 路线 | 已经证明的内容 | 继续需要证明的内容 |
|---|---|---|
| 分层读出 | 截断损失等于根均值加逐层非负修正；每层有方差下界 | 在危险整数上，哪些分组能提供足够大的统一下界 |
| 连续与整数比较 | 全素数连续最优点显式可求；实际整数损失是精确非负和 | 对所有实际整数证明 $\Delta_K(n)>G(K)$ |
| 联合补层 | 小素数总缺口达到明确阈值，即严格满足 Robin | 处理这些小素数方向都已高度饱和的整数 |

**最核心的未完成命题已经可以精确写成：**

$$
\boxed{
\forall n>5040,\quad
\Delta_{K(n)}(n)>G(K(n)),
\qquad
\sum_{p<K(n)}\log\frac{K(n)}p=\log n.
}
$$

本轮没有证明这个全称命题，因此还没有完成 RH。但已经从“三轴能够表示加法与乘法”推进到了三个可核查的数学层次：**保留联合信息的递归分解、带明确量级的整数修正目标，以及直接排除一大类潜在反例的联合补层定理。**
