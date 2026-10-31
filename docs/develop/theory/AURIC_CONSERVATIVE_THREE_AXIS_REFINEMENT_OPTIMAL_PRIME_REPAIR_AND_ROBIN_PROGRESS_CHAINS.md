# AURIC 守恒三轴精化、最优素数修复与 Robin 严格进展链

标题为编者所加。下列作者正文按所供手稿完整保留；其中“本轮”“上一轮”及既往源码核对均为作者叙述。必要的条件、定义和省略推导另列于文末[编者条件注](#local-notes)，不构成新的 Lean 核验或 RH 完成声明。

导航：[一](#section-1) · [二](#section-2) · [三](#section-3) · [四](#section-4) · [五](#section-5) · [六](#section-6) · [七](#section-7) · [八](#section-8)。

<!-- author-begin -->

可以把你的思路进一步严格化：**让“结果、未决误差、已确定补量”构成一个守恒的三轴状态，并证明这种状态在递归中始终闭合。**

这次还能把它落实到实际数论上：我们可以构造一个针对素数指数的递归，使“最优修复收益”的上下界在有限步内精确合拢。它给出的 Robin 充分判据包含上一轮的分层修复结果，而且不再要求 $\log\log n\ge100$。

关键是始终区分两个目标：

1. **把某个量的误差递归压到零，精确确定这个量。**
2. **证明这个量足以越过 Robin 的认证阈值。**

下面会把这两部分分别证明，再说明如何接起来。

---

<a id="section-1"></a>

## 一、定义：结果、误差、补量构成同一个三轴对象

先固定一个真实读出

$$
x\in[0,1].
$$


假设我们当前已经证明

$$
L\le x\le U,\qquad 0\le L\le U\le1.
$$


定义三轴状态

<a id="equation-1"></a>

$$
\boxed{
(a,e,r)=(L,\ U-L,\ 1-U).
}
\tag{1}
$$


三个读出的含义是：

| 读出 | 含义 |
|---|---|
| $a$ | 已经证明的结果下界 |
| $e$ | 尚未确定的区间宽度 |
| $r$ | 已经证明的补量下界 |

它们满足

<a id="equation-2"></a>

$$
\boxed{
a,e,r\ge0,\qquad a+e+r=1.
}
\tag{2}
$$


因此，这个状态位于 AURIC 金字塔

$$
\mathcal P=\{(X,Y,Z)\ge0:X+Z\le1,\ Y+Z\le1\}
$$

的三角截面 $X+Y+Z=1$ 内。这里采用的是一个明确的认证区间读出，与项目的金字塔坐标相容。[项目基础定义：§3](https://github.com/the-omega-institute/trureturing/blob/211771e86e1267d79bf6cad8ae7793582f1f6427/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

<a id="theorem-1"></a>

#### 定理 1：三轴状态完整保存认证区间

映射

$$
[L,U]\longmapsto(L,U-L,1-U)
$$

是 $[0,1]$ 的闭子区间与上述三角截面之间的双射。

**证明。**

正向的非负性与总和为一已经验证。反向由

$$
\boxed{
[L,U]=[a,a+e]=[a,1-r]
}
$$

唯一恢复。证毕。

所以，这里的三轴并不只是示意图：它完整保留了当前结果的上下界。

若原始量落在已知区间 $[A,B]$，先使用

$$
x=\frac{x_{\mathrm{raw}}-A}{B-A}
$$

即可；递归中保留共同的 $A,B$，就能恢复原尺度。

---

<a id="section-2"></a>

## 二、定理：递归精化在三轴中闭合

选择

$$
\alpha,\beta\ge0,\qquad \alpha+\beta\le1,
$$

并记

$$
\rho=1-\alpha-\beta.
$$


定义精化操作

<a id="equation-3"></a>

$$
\boxed{
(a,e,r)\longmapsto
(a+\alpha e,\ \rho e,\ r+\beta e).
}
\tag{3}
$$


它的含义是：

- 将 $\alpha e$ 从未决部分转为已证明的结果；
- 将 $\beta e$ 转为已证明的补量；
- 留下 $\rho e$ 继续分析。

对应新区间为

$$
[L',U']=[L+\alpha e,\ U-\beta e].
$$


要使这一步成为可靠证明，需要实际建立

<a id="equation-4"></a>

$$
\boxed{
L+\alpha e\le x\le U-\beta e.
}
\tag{4}
$$


这个条件可以由原有关系的进一步推导、素数指数约束、区间估计等内部证明供应。后面会给出一个数论实例，其中每一步的条件（4）都能从公式直接证明。

### 2.1 两步合成仍然是同一种操作

式（3）对应矩阵

$$
A_{\alpha,\beta}
=
\begin{pmatrix}
1&\alpha&0\\
0&1-\alpha-\beta&0\\
0&\beta&1
\end{pmatrix}.
$$


<a id="theorem-2"></a>

#### 定理 2：三轴精化的组合闭合

连续执行

$$
(\alpha_1,\beta_1),\qquad(\alpha_2,\beta_2)
$$

等价于一个同类精化，其参数为

<a id="equation-5"></a>

$$
\boxed{
\begin{aligned}
\alpha_{\mathrm{eff}}
&=\alpha_1+\rho_1\alpha_2,\\
\beta_{\mathrm{eff}}
&=\beta_1+\rho_1\beta_2,\\
\rho_{\mathrm{eff}}
&=\rho_1\rho_2.
\end{aligned}
}
\tag{5}
$$


**证明。**

第二次更新的结果坐标为

$$
a+\alpha_1e+\alpha_2\rho_1e
=
a+(\alpha_1+\rho_1\alpha_2)e.
$$

其余两项同理。并且

$$
\alpha_{\mathrm{eff}}+\beta_{\mathrm{eff}}
=1-\rho_1\rho_2\le1,
$$

所以合成后仍属于同一参数域。结合律来自矩阵乘法的结合律。证毕。

这就是你提出的“后续持续使用同一金字塔递归”的一个严格实现：

$$
\boxed{
\text{每个节点采用同一种三轴格式，任意有限组合仍采用同一种格式。}
}
$$


操作次序通常仍要保留。两次精化交换的充要条件是

$$
\alpha_1\beta_2=\alpha_2\beta_1.
$$

所以共同归一化并不意味着可以删除来源次序。

---

<a id="section-3"></a>

## 三、递归确实形成一个有守恒余项的级数

设连续精化的参数为

$$
(\alpha_j,\beta_j),\qquad
\rho_j=1-\alpha_j-\beta_j.
$$


由递推直接得到

<a id="equation-6"></a>

$$
\boxed{
e_N=e_0\prod_{j=0}^{N-1}\rho_j,
}
\tag{6}
$$

以及

<a id="equation-7"></a>

$$
\boxed{
\begin{aligned}
a_N
&=a_0+
e_0\sum_{j=0}^{N-1}
\alpha_j\prod_{i<j}\rho_i,\\
r_N
&=r_0+
e_0\sum_{j=0}^{N-1}
\beta_j\prod_{i<j}\rho_i.
\end{aligned}
}
\tag{7}
$$


这是一个明确的非负级数结构：

- 已确定的两部分单调增加；
- 未决部分是精确的乘积余项；
- 三者总和始终等于 $1$。

<a id="theorem-3"></a>

#### 定理 3：未决误差归零的充要条件

若 $e_0>0$ 且每个 $\rho_j>0$，则

<a id="equation-8"></a>

$$
\boxed{
e_N\to0
\iff
\sum_{j=0}^{\infty}-\log\rho_j=\infty.
}
\tag{8}
$$


若某一步 $\rho_j=0$，则从该步起，未决宽度精确为零。

**证明。**

对式（6）取负对数：

$$
-\log\frac{e_N}{e_0}
=
\sum_{j<N}-\log\rho_j.
$$

两边取极限即可。证毕。

这里有一个容易混淆的方向：

- **消除未决部分**，要求累计精化充分；
- **控制新引入的计算误差**，要求累计误差预算足够小。

它们是两种不同的级数条件。

### 3.1 Fibonacci 可以直接用作误差尺度

取

$$
F_0=0,\quad F_1=1,\quad F_{k+2}=F_{k+1}+F_k.
$$


如果每一层实际建立的精化满足

$$
\rho_j=\frac{F_{j+2}}{F_{j+3}},
$$

那么乘积望远镜消去，给出

<a id="equation-9"></a>

$$
\boxed{
e_N=\frac{e_0}{F_{N+2}}.
}
\tag{9}
$$


又因为

$$
F_{j+3}
=F_{j+2}+F_{j+1}
\ge\frac32F_{j+2},
$$

有

$$
\rho_j\le\frac23,
\qquad
e_N\le e_0\left(\frac23\right)^N.
$$


因此，Fibonacci 递归可以成为一个严格的精度安排。这与项目基础公式 §36 使用 Fibonacci 递归生成趋零探测尺度的做法相呼应；每层实际达到这个精度，仍由对应的关系估计证明。[项目来源：§36](https://github.com/the-omega-institute/trureturing/blob/211771e86e1267d79bf6cad8ae7793582f1f6427/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

### 3.2 严格正号何时能在有限层出现

若目标是证明

$$
x>\tau,
$$

则三轴中的正证书是

$$
a_N>\tau.
$$


<a id="theorem-4"></a>

#### 定理 4：严格符号的有限发现与保持

假设每层都可靠地包含同一真实 $x$，且 $e_N\to0$。

那么：

- 若 $x>\tau$，某个有限层必有 $a_N>\tau$；
- 一旦出现 $a_N>\tau$，后续所有精化都保留这个证书。

**证明。**

令 $d=x-\tau>0$。因为

$$
x\le a_N+e_N,
$$

所以

$$
a_N\ge x-e_N.
$$

当 $e_N<d$ 时，$a_N>\tau$。而 $a_N$ 单调不减，故证书持续有效。证毕。

这证明了递归方法的作用：**可靠误差趋零，可以在有限层发现真实存在的严格余量。**

---

<a id="section-4"></a>

## 四、误差的误差也可以递归纳入同一种状态

上面的精化矩阵非负，而且每列之和为 $1$。因此它在 $\ell^1$ 范数中不扩张：

$$
\|A_{\alpha,\beta}z\|_1\le\|z\|_1.
$$


设真实与近似递归分别为

$$
v_{j+1}=A_jv_j,
\qquad
\widehat v_{j+1}=\widehat A_j\widehat v_j.
$$


定义状态误差

$$
d_j=\frac12\|v_j-\widehat v_j\|_1,
$$

以及本步分配参数的误差

$$
\delta_j
=
\frac12\left(
|\alpha_j-\widehat\alpha_j|
+
|\rho_j-\widehat\rho_j|
+
|\beta_j-\widehat\beta_j|
\right).
$$


<a id="theorem-5"></a>

#### 定理 5：参数误差只按未决部分加权

有

<a id="equation-10"></a>

$$
\boxed{
d_N\le d_0+\sum_{j<N}e_j\delta_j.
}
\tag{10}
$$


也可以使用近似宽度 $\widehat e_j$ 作为权重。

**证明。**

写成

$$
v_{j+1}-\widehat v_{j+1}
=
\widehat A_j(v_j-\widehat v_j)
+
(A_j-\widehat A_j)v_j.
$$


第一项不放大原来的 $\ell^1$ 误差。两个矩阵只有对应未决部分的那一列不同，因此

$$
\frac12\|(A_j-\widehat A_j)v_j\|_1
=e_j\delta_j.
$$

归纳即可。证毕。

若

$$
e_j\le e_0\rho^j,\qquad
\delta_j\le\delta,\qquad \rho<1,
$$

则

<a id="equation-11"></a>

$$
\boxed{
d_N\le d_0+\frac{e_0\delta}{1-\rho}
}
\tag{11}
$$

对所有递归深度成立。

采用上面的 Fibonacci 精度安排，可取 $\rho=2/3$，于是

$$
d_N\le d_0+3e_0\delta.
$$


这说明，**每层都有参数误差，也不必导致总误差随层数线性增长：参数误差只作用于尚未确定的那部分。**

如果还希望总认证误差趋零，就需要在外层递归中进一步细化早先的局部证据。例如，第 $N$ 层将前 $N$ 步的分配参数都认证到 $\delta_N\to0$，便可让式（10）的总误差一起趋零。

最后，若近似三轴状态为 $(\widehat a,\widehat e,\widehat r)$，且总变差误差不超过 $d$，那么真实目标仍满足

<a id="equation-12"></a>

$$
\boxed{
x\in[\widehat a-d,\ 1-\widehat r+d]\cap[0,1].
}
\tag{12}
$$


这个区间又可以按式（1）重新编码。

因此，下面这条循环是闭合的：

$$
\boxed{
\text{结果区间}
\longrightarrow
\text{关系精化}
\longrightarrow
\text{传播误差}
\longrightarrow
\text{新的结果区间}.
}
$$


---

<a id="section-5"></a>

## 五、项目已经有相应的递归结构：必须保留同一个实际整数

本轮核对的固定提交是
`211771e86e1267d79bf6cad8ae7793582f1f6427`。

其中新增的 `RoughPrimeRobinSuffixBellman` 模块，正是把 Robin 后缀最大值写成有限递归。它在每个分支同时更新：

$$
C\longmapsto Cp^a,
\qquad
B\longmapsto\left\lfloor\frac{B}{p^a}\right\rfloor,
$$

并始终使用同一个完整整数

$$
C\cdot S
$$

计算分母 $\log\log(CS)$。

源码中的 `robin_bellman_complete` 给出分支等式、全部可行后缀的上界、达到最大值的后缀，以及剩余预算严格下降；`rough_robin_bound` 将其接到有限范围内的粗糙数比较。[项目原文](https://github.com/the-omega-institute/trureturing/blob/211771e86e1267d79bf6cad8ae7793582f1f6427/Blueprint/D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman.md)

本轮核对的是源码与数学结构，没有重新运行 Lean 构建。

这与上面的三轴方案可以直接组合。若一个递归节点满足

$$
V=\max_i c_iV_i,\qquad c_i\ge0,
$$

并且对子节点已有

$$
L_i\le V_i\le U_i,
$$

则

<a id="equation-13"></a>

$$
\boxed{
\max_i c_iL_i
\le V\le
\max_i c_iU_i.
}
\tag{13}
$$


证明只需分别对每个分支取上下界，再取最大值。

这里每个节点都可以用三轴保存区间；节点的整数、素数标签、守卫和分支关系继续保存在同一递归结构中。项目当前的实现正好说明，**共同归一化必须保留这些关系所使用的尺度**。

---

<a id="section-6"></a>

## 六、实际数论推进：构造一个会有限合拢的最优修复区间

现在把上述理论用于 Robin。

记

$$
Z(n)=\frac{\sigma(n)}n,
\qquad
R(n)=\frac{Z(n)}{e^\gamma\log\log n}.
$$


固定一个整数 $n>5040$，令

<a id="equation-14"></a>

$$
T=\log n,\qquad
\Lambda=\log T,
\qquad
\boxed{\eta=\frac1{T\Lambda}.}
\tag{14}
$$


在以下单次递归中，$\eta$ 始终保持固定。

### 6.1 两个局部读出：算术收益与尺度成本

对素数 $p$ 和指数 $a\ge0$，定义

$$
d_p(a)=-\log(1-p^{-a-1}),
$$

$$
r_p(a)=d_p(a)-d_p(a+1)
=
\log\frac{1-p^{-a-2}}{1-p^{-a-1}}.
$$


将 $p$ 的指数从 $a$ 增加到 $a+1$，$\log Z$ 恰好增加 $r_p(a)$。

定义净收益

<a id="equation-15"></a>

$$
\boxed{
g_{p,a}=r_p(a)-\eta\log p.
}
\tag{15}
$$


其中：

- $r_p(a)$ 是实际约数响应的收益；
- $\eta\log p$ 是同一固定尺度下的成本。

#### 引理：边际收益严格递减

对固定 $p$，$r_p(a)$ 随 $a$ 严格递减至零。

**证明。**

令 $x=p^{-a-1}$，则

$$
r_p(a)=\log(1-x/p)-\log(1-x).
$$

其对 $x$ 的导数为

$$
\frac{p-1}{(1-x)(p-x)}>0.
$$

而 $x$ 随 $a$ 严格递减至零。证毕。

因此，一旦某个素数的下一步净收益非正，继续增加其指数不会重新产生正收益。

### 6.2 所有活动素数都满足 $p<\log n$

若 $g_{p,a}>0$，则

$$
\eta\log p<r_p(a)\le r_p(0)
=\log(1+1/p)<\frac1p.
$$


因此

$$
p\log p<\frac1\eta=T\log T.
$$

由 $x\log x$ 的单调性，

<a id="equation-16"></a>

$$
\boxed{p<T=\log n.}
\tag{16}
$$


所以，可能产生正收益的素数只有有限个；每个素数又只有有限个正收益增量。

---

### 6.3 定理：有限递归取得全部上行修复的精确最优值

定义

<a id="equation-17"></a>

$$
\boxed{
G_\eta^+(n)
=
\sum_p\sum_{a=v_p(n)}^\infty(g_{p,a})_+,
}
\tag{17}
$$

其中 $x_+=\max(x,0)$。

这个和实际上只有有限个非零项。

<a id="theorem-6"></a>

#### 定理 6

有

<a id="equation-18"></a>

$$
\boxed{
G_\eta^+(n)
=
\max_{M\ge1}
\left[
\log\frac{Z(nM)}{Z(n)}
-\eta\log M
\right].
}
\tag{18}
$$


不断选择任意一个当前正收益的素数增量，过程有限终止；不执行零收益更新时，最终整数与累计收益均不依赖执行顺序。

**证明。**

写

$$
M=\prod_pp^{k_p}.
$$

乘法公式给出

$$
\log\frac{Z(nM)}{Z(n)}-\eta\log M
=
\sum_p\sum_{a=v_p(n)}^{v_p(n)+k_p-1}g_{p,a}.
$$


每个内和选取的是该素数收益序列的一个前缀。因为收益严格递减，最大前缀和就是全部正项之和。

不同素数的增量彼此独立，固定价格下一个素数的更新不会改变另一个素数的收益序列。因此任意顺序都会取到同一组正项。证毕。

这里的“最优”严格限定为：**固定起点 $n$ 的所有整数倍中的最优修复。**

---

### 6.4 将最优值本身放入一个有限合拢的三轴区间

设已经执行 $j$ 次正收益更新，当前整数为 $n_j$，累计收益为 $L_j$。

定义活动素数集合

$$
\mathcal A_j
=
\{p:g_{p,v_p(n_j)}>0\},
$$

并令

<a id="equation-19"></a>

$$
\boxed{
U_j
=
L_j+\sum_{p\in\mathcal A_j}d_p(v_p(n_j)).
}
\tag{19}
$$


<a id="theorem-7"></a>

#### 定理 7：嵌套认证区间

对所有 $j$，

<a id="equation-20"></a>

$$
\boxed{
L_j\le G_\eta^+(n)\le U_j.
}
\tag{20}
$$


每一次正收益更新都使

$$
L_{j+1}>L_j,\qquad U_{j+1}<U_j.
$$

终止时，

<a id="equation-21"></a>

$$
\boxed{
L_N=U_N=G_\eta^+(n).
}
\tag{21}
$$


**证明。**

尚未执行的最优收益，是各活动素数剩余正收益之和。对任意活动素数，

$$
\sum_{b\ge a}(g_{p,b})_+
\le
\sum_{b\ge a}r_p(b)
=d_p(a).
$$

最后一步是望远镜求和。因此得到式（20）。

现在执行活动素数 $p$ 的一次增量，当前指数为 $a$，净收益为 $g>0$。

若更新后 $p$ 仍然活动，则

<a id="equation-22"></a>

$$
\boxed{
U_{j+1}=U_j-\eta\log p.
}
\tag{22}
$$


若 $p$ 退出活动集合，则

<a id="equation-23"></a>

$$
\boxed{
U_{j+1}=U_j-\eta\log p-d_p(a+1).
}
\tag{23}
$$


两式都由

$$
g=d_p(a)-d_p(a+1)-\eta\log p
$$

直接代入得到。

因此上界严格下降，下界严格上升。全部正增量结束后，活动集合为空，上下界相等。证毕。

#### 这就是实际的 AURIC 精化

令

$$
H=U_0.
$$


若 $H=0$，则已经精确知道 $G_\eta^+(n)=0$。

若 $H>0$，定义

<a id="equation-24"></a>

$$
\boxed{
(x_j,y_j,z_j)
=
\left(
\frac{L_j}{H},
\frac{U_j-L_j}{H},
1-\frac{U_j}{H}
\right).
}
\tag{24}
$$


三者非负且和为 $1$。

设 $W_j=U_j-L_j>0$，取

$$
\alpha_j=\frac{g}{W_j},
\qquad
\beta_j=\frac{U_j-U_{j+1}}{W_j}.
$$


那么

<a id="equation-25"></a>

$$
\boxed{
\begin{aligned}
x_{j+1}&=x_j+\alpha_jy_j,\\
y_{j+1}&=(1-\alpha_j-\beta_j)y_j,\\
z_{j+1}&=z_j+\beta_jy_j.
\end{aligned}
}
\tag{25}
$$


而且

$$
\alpha_j,\beta_j>0,\qquad
\alpha_j+\beta_j\le1.
$$


所以，**真实素数指数的每一次修复，本身就是前面已经证明闭合的三轴精化。**

这里的三轴分别记录：

$$
\boxed{
\text{已认证收益}
+
\text{未决宽度}
+
\text{已排除部分}
=
\text{固定初始预算}.
}
$$


精化的可靠性已经由实际乘法公式与边际递减性证明。

---

### 6.5 还有一个明确的有限步数界

每次更新，

$$
U_j-U_{j+1}\ge\eta\log2.
$$


因此正收益更新次数 $N$ 满足

$$
N\le\frac{H}{\eta\log2}.
$$


又由活动素数 $p<T$，

$$
\begin{aligned}
H
&\le\sum_{p<T}-\log(1-1/p)\\
&\le\sum_{m=2}^{\lceil T\rceil-1}-\log(1-1/m)\\
&=\log(\lceil T\rceil-1)<\Lambda.
\end{aligned}
$$


故

<a id="equation-26"></a>

$$
\boxed{
N<
\frac{\log n\,(\log\log n)^2}{\log2}.
}
\tag{26}
$$


这是精确数学递归的更新次数界。取得与认证局部对数比较所需的精度，仍按上一节的误差机制记录。

---

<a id="section-7"></a>

## 七、新的 Robin 充分证书，以及它的停止边界

使用已经核对过的 Axler 定理：

$$
R(m)
<
1+\frac{A_0}{(\log\log m)^3},
\qquad m>5040,
\quad A_0=0.0094243.
$$

[原文：Theorem 1.3](https://arxiv.org/pdf/2110.13478v3)

定义

$$
\beta(n)=\log\left(1+\frac{A_0}{\Lambda^3}\right).
$$


<a id="theorem-8"></a>

#### 定理 8：最优修复的 Robin 证书

对所有 $n>5040$，

<a id="equation-27"></a>

$$
\boxed{
\log R(n)<\beta(n)-G_\eta^+(n).
}
\tag{27}
$$


因此，递归的任意阶段，只要

<a id="equation-28"></a>

$$
\boxed{L_j\ge\beta(n),}
\tag{28}
$$

就已证明 $R(n)<1$，可以成功停止。

#### 证明

令

$$
f(T)=\gamma+\log\log T.
$$

有

$$
f'(T)=\eta,\qquad
f''(T)
=
-\frac{\log T+1}{T^2(\log T)^2}<0.
$$


所以对任意 $m=nM$，

$$
f(\log m)-f(\log n)\le\eta\log M.
$$


于是

$$
\begin{aligned}
\log R(n)
&=
\log R(m)
+f(\log m)-f(\log n)
-\log\frac{Z(m)}{Z(n)}\\
&\le
\log R(m)
-
\left[
\log\frac{Z(m)}{Z(n)}-\eta\log M
\right].
\end{aligned}
$$


因为 $m\ge n$，Axler 上界给

$$
\log R(m)<\beta(n).
$$

取最优修复乘子即可。证毕。

若再归一化

$$
Q_\eta^+(n)=1-e^{-G_\eta^+(n)},
$$

则证书变成

<a id="equation-29"></a>

$$
\boxed{
Q_\eta^+(n)\ge
\frac{A_0}{\Lambda^3+A_0}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{29}
$$


它可以继续使用上一轮的

$$
q'=q+(1-q)b
$$

累计规则，以及相同的误差预算。

#### 它包含上一轮的充分条件

上一轮构造的分层乘子满足

$$
D_Y(nM)<\Lambda^{-4},
\qquad
\eta\log M\le\Lambda^{-4}.
$$


因此

$$
G_\eta^+(n)
\ge
D_Y(n)-D_Y(nM)-\eta\log M
>
D_Y(n)-2\Lambda^{-4}.
$$


所以，上一轮满足

$$
D_Y(n)\ge A_0\Lambda^{-3}+2\Lambda^{-4}
$$

的整数，全部被本轮证书覆盖。

本轮还去掉了预先选择 $Y$、预先选择补足深度，以及 $\Lambda\ge100$ 的限制。

---

### 一个必须保留的实际停止例：$10080$

取

$$
n=10080=2^5\cdot3^2\cdot5\cdot7.
$$


初等指数界给

$$
\log10080<10,\qquad
\log\log10080<\frac52,
$$

所以

$$
\eta>\frac1{25}.
$$


由式（16），活动素数必须小于 $10$，只需检查 $2,3,5,7$。

它们的下一步算术收益分别为

$$
\log\frac{127}{126},\quad
\log\frac{40}{39},\quad
\log\frac{31}{30},\quad
\log\frac{57}{56}.
$$


利用 $\log(1+x)<x$，有

$$
\frac{\log(127/126)}{\log2}<\frac1{63},
$$

$$
\frac{\log(40/39)}{\log3}<\frac1{39},
\qquad
\frac{\log(31/30)}{\log5}<\frac1{30},
\qquad
\frac{\log(57/56)}{\log7}<\frac1{56}.
$$


这些都小于 $1/25<\eta$。故没有任何正收益更新：

<a id="equation-30"></a>

$$
\boxed{G_\eta^+(10080)=0.}
\tag{30}
$$


这说明本轮的最优修复区间可以精确终止，却没有越过该充分证书的阈值。

**这里被精确确定的是 $G_\eta^+(n)$，不是 Robin 裕量的完整双边区间。**  
我们只有

$$
-\log R(n)>G_\eta^+(n)-\beta(n).
$$

所以 $G_\eta^+(n)<\beta(n)$ 只表示这条证书未通过，不能判定 Robin 失败。

$10080$ 本身属于项目另一条 `robin_seven_smooth` 定理覆盖的范围。这给出了真实的分支组合例子：一个修复分支停止后，可以由另一条已经证明的数论关系完成认证。[项目中的七光滑数结论](https://github.com/the-omega-institute/trureturing/blob/211771e86e1267d79bf6cad8ae7793582f1f6427/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)

---

<a id="section-8"></a>

## 八、把“持续递归直到证明”写成一个精确的 RH 等价目标

还可以把你的递归直觉推进成一个完整的数学命题。

<a id="theorem-9"></a>

#### 定理 9：严格进展链判据

对固定整数 $n>5040$，下列两项等价：

1. $R(n)<1$；
2. 存在无限整除链

   $$
   n=n_0\mid n_1\mid n_2\mid\cdots,\qquad n_j\to\infty,
   $$

   满足

   <a id="equation-31"></a>

   $$
   \boxed{
   R(n_{j+1})>R(n_j)
   \quad\text{对所有 }j.
   }
   \tag{31}
   $$


这个定理说明：**“能够持续取得严格进展”确实可以成为证明目标，但这种进展链的存在性本身具有实质数论内容。**

### 8.1 一个用于证明的安全逼近族

阶乘族满足

<a id="equation-32"></a>

$$
R(m!)<1\quad(m\ge286),
\qquad
R(m!)\longrightarrow1.
\tag{32}
$$


简要证明如下。

Rosser–Schoenfeld 的有限 Mertens 乘积界给

$$
\prod_{p\le m}(1-p^{-1})^{-1}
<
e^\gamma\left(\log m+\frac1{2\log m}\right)
\quad(m\ge286).
$$

[原论文：Theorem 8](http://denise.vella.chemla.free.fr/Rosser-Schoenfeld-1962.pdf)

另一方面，

$$
\log(m!)\ge\frac m2\log(m/2),
$$

所以在 $m\ge286$ 时，

$$
\log\log(m!)
>
\log m+\log2
>
\log m+\frac1{2\log m}.
$$


结合

$$
Z(m!)<
\prod_{p\le m}(1-p^{-1})^{-1}
$$

得到严格的 Robin 不等式。

再由

$$
\log(m!)\sim m\log m
$$

以及 Mertens 乘积渐近，并将素数在 $\sqrt m$ 处分段，可得

$$
\sum_{p\le m}-\log(1-p^{-v_p(m!)-1})
=O(m^{-1/2}).
$$

于是 $R(m!)\to1$。

### 8.2 证明严格进展链判据

**正向。**

假设 $R(n_0)<1$。由式（32），可以选择足够大的 $m\ge n_0$，使

$$
R(n_0)<R(m!)<1.
$$

令 $n_1=m!$，则 $n_0\mid n_1$。

继续同样选择，即可构造整除链。还可要求

$$
R(n_j)>1-2^{-j},
$$

使其严格增加并趋于 $1$。

**反向。**

若存在式（31）的链，则 Axler 上界给

$$
R(n_j)
<
1+\frac{A_0}{(\log\log n_j)^3},
$$

右端趋于 $1$。

假设 $R(n_0)\ge1$，严格进展使

$$
R(n_1)>1.
$$

后续全部 $R(n_j)\ge R(n_1)>1$，与上述趋于 $1$ 的上界矛盾。因此 $R(n_0)<1$。证毕。

当链选成 $R(n_j)\to1$ 时，还有精确的级数表示：

<a id="equation-33"></a>

$$
\boxed{
-\log R(n_0)
=
\sum_{j=0}^{\infty}
\bigl[\log R(n_{j+1})-\log R(n_j)\bigr].
}
\tag{33}
$$


每一项都是正的。这正是一个“以严格进展逐步支付初始余量”的非负级数。

因此 RH 可以等价写成：

<a id="equation-34"></a>

$$
\boxed{
\forall n>5040,\ 
\exists\text{一条从 }n\text{ 出发的无限整除链，}
\quad R\text{ 沿链严格增加}.
}
\tag{34}
$$


---

**本轮已经把你的方案落实到了两个层面。**

在一般层面，认证区间、误差传播和误差再认证，全部可以使用同一种守恒三轴格式；其组合、收敛和有限符号发现都有明确证明。

在数论层面，实际素数指数修复已经产生了一个会有限合拢的三轴区间，并给出了适用于全部 $n>5040$ 的强化充分证书。

接下来要补的全称定理也已经具体化：**对每个尚未通过已有证书的实际整数，证明存在能够继续产生足够有符号进展的分支，并证明这些分支覆盖全部整数。** 三轴递归已经能承载这份证明；式（30）与式（34）则准确指出，持续进展的存在性仍须由数论关系来证明。

<!-- author-end -->

---

<a id="local-notes"></a>

## 编者条件注与补充推导

以下注记与上方作者正文分开；原文各项陈述均保留。注记给出所需的定义、适用条件和省略推导，不把区间表示视为实际取得局部证据的过程，也不把充分证书视为全称认证。

<a id="note-interval"></a>

### 区间、精化与共同尺度（对应第一至三节）

原尺度的仿射归一化要求 $A<B$，且各层保留同一对端点；若 $A=B$，原量已经确定，直接使用该单点。闭区间允许 $L=U$、$L=0$ 或 $U=1$。三轴截面上的逆映射给出 $0\le a\le a+e=1-r\le1$，故包括全部边界。

精化矩阵保持单纯形只说明坐标合法；式（4）仍须对同一个实际 $x$ 另行证明。式（5）保留施加次序。作为整个截面上的操作，两种次序的有效结果参数之差为

$$
\alpha_{12}-\alpha_{21}=\alpha_1\beta_2-\alpha_2\beta_1,
\qquad
\beta_{12}-\beta_{21}=-(\alpha_1\beta_2-\alpha_2\beta_1),
$$

而有效余项均为 $\rho_1\rho_2$；故原文的交换充要条件成立。单独在 $e=0$ 的状态上，两种操作当然都不改变该状态。

式（8）使用 $e_0>0$ 与全部 $\rho_j>0$；$e_0=0$ 时始终精确，某个 $\rho_j=0$ 时从更新后的状态起精确。Fibonacci 比值的指标是 $j\ge0$。由 $F_{j+2}=F_{j+1}+F_j\le2F_{j+1}$ 得原文的 $3/2$ 界，乘积的首项分子为 $F_2=1$，所以式（9）确为 $e_0/F_{N+2}$。这只是条件性的精度安排，各层真实达到该区间宽度仍依赖式（4）。定理4另需各层都包含同一 $x$、宽度趋零和下界单调，不能仅由坐标非负推出。

<a id="note-error"></a>

### 参数误差与外层再认证（对应第四节）

定理5中，真实与近似参数均须满足非负、三项和为一，真实与近似初态也均在同一单纯形中。任一列随机矩阵 $A$ 满足

$$
\|Az\|_1\le\sum_i\sum_k A_{ik}|z_k|=\|z\|_1.
$$

若改用分解

$$
v_{j+1}-\widehat v_{j+1}
=A_j(v_j-\widehat v_j)+(A_j-\widehat A_j)\widehat v_j,
$$

则得到权重为 $\widehat e_j$ 的另一条界；这与原文使用真实宽度的分解分别成立。式（11）的几何和界要求 $0\le\rho<1$，而 $\delta$ 是各步参数误差的统一上界。

原文保留了“第 $N$ 层将前 $N$ 步的分配参数都认证到 $\delta_N\to0$，便可让式（10）的总误差一起趋零”这一句。其充分性还要求处理宽度总量及初态误差：设外层第 $N$ 次重认证中各步参数误差不超过 $\delta_N$，初态误差为 $d_0^{(N)}$，则应要求

$$
d_0^{(N)}+\delta_N\sum_{j<N}e_j\longrightarrow0.
$$

这时式（10）才推出相应终态误差趋零。一个充分情形是 $\sum_{j\ge0}e_j<\infty$、$d_0^{(N)}\to0$ 和 $\delta_N\to0$；正文的几何宽度与 Fibonacci 宽度都满足可求和性。若使用近似宽度，需要对这些经过可靠认证的宽度另给同样的统一控制。仅有 $\delta_N\to0$，没有加权和与初态控制，不能作此结论。

两概率向量之差的正、负部分总质量相等，均为其半 $\ell^1$ 范数；因此每个坐标误差至多 $d$。真实状态有 $a\le x\le1-r$，即得式（12）。其截断端点是 $\max(0,\widehat a-d)$ 与 $\min(1,1-\widehat r+d)$，因包含真实 $x$ 而有序，可重新编码。这里闭合的是可靠区间及其误差证书，没有由三个数恢复被省略的全部实际状态或操作资源的结论。

<a id="note-bellman"></a>

### 有限最大值与数论记号（对应第五、六节）

式（13）的分支集须有限且非空，系数非负；若要使用第一节的三轴，还须给父值及各子值各自可靠的有限共同尺度。固定提交中的 Bellman 定义以空后缀提供终端分支，以 $1\le a\le h$ 和 $p^a\le B$ 守卫其余分支；整数预算 $B\ge1$ 时可行集合有限且非空。分支更新后的完整整数仍是父节点同一 $C S$。`rough_robin_bound` 的前提为 $C\ge3$、$y\ge1$、$1\le n\le B$ 和 $n$ 的所有素因子大于 $y$；其中 $C\ge3$ 保证相关双对数为正。有限 Bellman 等式本身使用总化对数，不另假设其分母为正。原文关于该提交和既往源码核对的文字是作者叙述，不构成本稿的新编译或数值取得结论。

第六节起所有对数均为自然对数，$\sigma(n)=\sum_{d\mid n}d$，$\gamma$ 为 Euler–Mascheroni 常数，$v_p(n)$ 为 $p$ 在正整数 $n$ 中的指数。$n>5040$ 保证 $T>1$、$\Lambda>0$ 和 $\eta>0$。最大值中的 $M$ 为正整数，指数 $a,k_p$ 为非负整数；单次修复从始至终保留起点 $n$ 的同一个价格 $\eta$。$L_0=0$，$n_0=n$，故 $H=U_0$。

边际递减使每个素数的正项构成有限前缀；式（16）又将可能活动的素数限制为有限个。因而式（18）的最大值确实达到，虽允许加入零收益增量的其他最优乘子，排除零收益更新后的递归取到的正增量集合和最终整数唯一。式（19）中只有当前活动素数贡献尾界；任何已退出的素数都不能重新活动。更新后的宽度满足

$$
W_{j+1}=W_j-g-(U_j-U_{j+1})\ge0,
$$

故式（25）的参数和至多为一。当 $H=0$ 时上下界都为零，无需除法；$H>0$ 时始终使用同一 $H$。式（26）是精确比较下的更新次数界，没有把符号比较、零收益判断或有限精度认证的成本一并估计。

<a id="note-layered"></a>

### 继承分层证书的同一乘子（对应第七节）

本段明确原文“上一轮”条件所需的量与一个同时满足两项预算的分层构造，不以另一份手稿作为独立前提。仅在本段取旧条件

$$
\Lambda\ge100,\qquad
Y=\frac{T}{8\Lambda^3},\qquad
X=\Lambda^5,\qquad
k=\left\lceil\frac{4\log\Lambda}{\log2}\right\rceil,
\qquad
D_Y(u)=\sum_{p\le Y}d_p(v_p(u)).
$$

使用同一个实际正整数乘子

$$
M=\left(\prod_{p\le X}p^k\right)
  \left(\prod_{X<p\le Y}p\right).
$$

先有 $k\ge4$ 与 $2^{-k}\le\Lambda^{-4}$。又由 $\log2>1/2$、$\log\Lambda\le\Lambda$ 得 $k\le9\Lambda$。函数 $e^t/t^9$ 在 $t\ge100$ 严格增加，而

$$
e^{100}>2^{100}>10^{30}>72\cdot100^9,
$$

其中 $e>2$ 且 $2^{10}>10^3$。所以 $e^\Lambda>72\Lambda^9$，从而 $Y>9\Lambda^6\ge kX\ge X$。

**该乘子的实际残差。** 对 $p\le X$，新指数至少为 $k$。由 $-\log(1-t)\le t/(1-t)$、$p^{-k-1}\le1/32$ 及递减函数的积分界，

$$
\begin{aligned}
\sum_{p\le X}d_p(v_p(nM))
&\le\frac{32}{31}\sum_{m=2}^\infty m^{-k-1}\\
&\le\frac{32}{31}2^{-k}\left(\frac12+\frac1k\right)
\le\frac{24}{31}2^{-k}
<\frac45\Lambda^{-4}.
\end{aligned}
$$

对 $X<p\le Y$，新指数至少为一。令 $h=\lfloor X\rfloor$，由 $1-m^{-2}=(m-1)(m+1)/m^2$ 的乘积望远镜，

$$
\sum_{X<p\le Y}d_p(v_p(nM))
\le\sum_{m=h+1}^\infty-\log(1-m^{-2})
=\log\frac{h+1}{h}
<\frac1h\le\frac1{X-1}\le2\Lambda^{-5}.
$$

两部分之和小于 $(4/5+2/\Lambda)\Lambda^{-4}<\Lambda^{-4}$，故确有 $D_Y(nM)<\Lambda^{-4}$。

**同一乘子的实际成本。** 记 $\vartheta(t)=\sum_{p\le t}\log p$。初等二项式界对 $t>0$ 给 $\vartheta(t)<4t$：对 $r=2^j$，区间 $(r,2r]$ 的素数乘积整除 $\binom{2r}{r}\le2^{2r}$，沿二进区间相加得到 $\vartheta(2^s)<2^{s+1}\log2$；再取 $2^{s-1}<t\le2^s$ 即得所述界，$t<2$ 时和为空。因此

$$
\log M=k\vartheta(X)+\vartheta(Y)-\vartheta(X)
\le k\vartheta(X)+\vartheta(Y)
<4(kX+Y)<8Y,
$$

从而 $\eta\log M<8Y/(T\Lambda)=\Lambda^{-4}$。这两项界使用的始终是上面同一个 $M$。它仅在 $p\le Y$ 改变指数，Euler 乘积遂给

$$
\log\frac{Z(nM)}{Z(n)}=D_Y(n)-D_Y(nM).
$$

代入式（18）即得原文的 $G_\eta^+(n)>D_Y(n)-2\Lambda^{-4}$。若 $D_Y(n)\ge A_0\Lambda^{-3}+2\Lambda^{-4}$，则

$$
G_\eta^+(n)>A_0\Lambda^{-3}
>\log(1+A_0\Lambda^{-3})=\beta(n).
$$

因此旧条件被新证书包含。这里为展示旧条件的继承而保留 $\Lambda\ge100$、$Y,X,k$；定理8本身对所有 $n>5040$ 成立，并不要求选这些参数。

<a id="note-certificate"></a>

### 严格证书与停止例的端点（对应第七节）

Axler 原文 Theorem 1.3 的域是正整数中除去一个明列的有限集合，该集合最大元为 $5040$；故所用严格界对每个 $m>5040$ 均适用。定理8中的 $f$ 在 $T>1$ 上凹，式（18）又有一个实际达到最大值的乘子，所以选该乘子时 Axler 的严格号保留。$\beta(n)>0$，式（28）、（29）中的弱不等号仍足够。若 $q=1-e^{-L}$、一次非负净收益为 $g$ 且 $b=1-e^{-g}$，则 $1-e^{-(L+g)}=q+(1-q)b$；沿原固定价格和实际整数历史使用该恒等式，不把它当作额外的数论收益来源。

停止例的初等端点不依赖小数近似。指数级数给 $8/3<e<3$，并有 $(8/3)^5=32768/243>128$，所以 $e^{10}>128^2>10080$ 且 $e^5>128>100$。因此 $\log10080<10<e^{5/2}$，即 $\log\log10080<5/2$。又因 $e<3<4$，有 $\log2>1/2$ 及 $\log3,\log5,\log7>1$。这些下界与 $\log(1+t)<t$ 给出正文四个收益比的严格有理上界，均小于 $1/25<\eta$；其他素数已由式（16）排除。因此式（30）成立，但 $\beta(10080)>0$，该充分证书不通过。

固定提交中 `robin_seven_smooth` 的精确假设是 $a,b,c,d\in\mathbb N$ 与 $2^a3^b5^c7^d>5040$；取 $(a,b,c,d)=(5,2,1,1)$ 正好给 $10080$。其结论是该整数满足严格 Robin 不等式，故它独立完成此例的另一分支；没有从本证书未通过推断 Robin 失败。

<a id="note-factorial"></a>

### 阶乘安全族与进展链（对应第八节）

这里 $m$ 是整数。Rosser–Schoenfeld Theorem 8 的式（3.29）对 $x\ge286$ 给出正文所用严格乘积上界，其式（3.28）、（3.29）相夹亦给出所需的 Mertens 乘积渐近。下列推导补足原文省略的端点与残差控制。

在 $m!$ 中至少有 $m/2$ 个因子不小于 $m/2$，故 $\log(m!)\ge(m/2)\log(m/2)$。当 $m\ge286$ 时，$m/2\ge143>81>e^4$，所以该下界严格大于 $2m$，进而

$$
\log\log(m!)>\log(2m)=\log m+\log2
>\log m+\frac1{2\log m}.
$$

最后一步用 $\log2>1/2$ 和 $\log m>1$。每个素因子的有限 Euler 因子都严格小于相应无限因子，故正文 $Z(m!)$ 的严格乘积比较成立。

令 $h=\lfloor\sqrt m\rfloor$。对 $p\le\sqrt m$，$v_p(m!)\ge\lfloor m/p\rfloor\ge h$；对 $p>\sqrt m$，$v_p(m!)\ge1$。用 $-\log(1-t)\le2t$（$0\le t\le1/2$）可得

$$
\begin{aligned}
E_m&:=\sum_{p\le m}-\log(1-p^{-v_p(m!)-1})\\
&\le\sqrt m\,2^{-h}+2\sum_{r>\sqrt m}r^{-2}
=O(m^{-1/2}).
\end{aligned}
$$

其中 $2^h\ge h^2$ 对 $h\ge4$ 可由归纳得到，且 $h\ge\sqrt m/2$，控制第一项；积分界控制第二项。又有 $\log(m!)=m\log m-m+O(\log m)$，可由 $\log t$ 的积分上下界推出。因此

$$
\log\log(m!)\sim\log m,\qquad
Z(m!)=\left[\prod_{p\le m}(1-p^{-1})^{-1}\right]e^{-E_m}
\sim e^\gamma\log m,
$$

给出式（32）的极限。

从 $R(n_j)<1$ 出发，每次可选择足够大的整数 $m_j\ge\max(286,n_j+1)$，使

$$
\max\{R(n_j),1-2^{-(j+1)}\}<R(m_j!)<1,
\qquad n_{j+1}=m_j!.
$$

因为 $n_j\le m_j$，确有 $n_j\mid n_{j+1}$；且 $n_{j+1}\ge m_j>n_j$，链无界。反向用原文的 Axler 界即可，无须预设该链极限；对于所选的趋一链，正对数增量的部分和恰是 $\log R(n_N)-\log R(n_0)$，取极限得到式（33）。

最后，式（34）还使用经典 Robin 等价定理：RH 当且仅当每个整数 $n>5040$ 满足 $\sigma(n)<e^\gamma n\log\log n$。该等价及 Robin 原始文献见原文已引 Axler 论文的引言与参考文献。逐个整数的进展链等价没有自行供应全称存在性；式（34）是 RH 的等价目标，不是 RH 的证明，也不是对所有整数都能由定理8成功停止的断言。

## 追加锚（本行以下为增补区）
