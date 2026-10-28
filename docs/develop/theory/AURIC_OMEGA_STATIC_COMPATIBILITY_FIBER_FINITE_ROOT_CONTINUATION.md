# AURIC Ω 静态相融纤维理论续卷：全人口消去与有限根前沿

## 61. 指定人口、共同实部与原联合域的参数

**定义 81.1（同一输入存在问题）。** 固定
[《AURIC Ω 静态相融纤维理论》定义 68.1、73.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
的物理顺序
$(000,100,010,001,101)$ 和被动实帧
$D_3=\operatorname{diag}(1,i,i,i,1)$。
任取这个顺序中的 $z=(z_i)_{i=1}^5$，满足 $z_i\geq0$、$\sum_i z_i=1$；
令 $\zeta_1\geq\cdots\geq\zeta_5$ 是其降序排列，并置

$$
P=\zeta_1,\qquad Q=\zeta_1+\zeta_2,\qquad
V=\zeta_4+\zeta_5,\qquad d=\min\{V,(1-Q)/2\}.
\tag{XII.1}
$$

沿用原卷的 $\mathcal E(z)$、$\mathcal S_z$、$H_z(s)$：
输入为同一个指定实帧中的两个实际 $5\times5$ 半正定迹一矩阵
$\rho,\sigma$，两者对角均为 $z$，逐项实部相同，且

$$
\operatorname{spec}(\rho-\sigma)=(a,b,0,-b,-a),\qquad
a\geq b\geq0,\qquad s=a+b.
\tag{XII.2}
$$

共同实部是每对见证的存在变量，不是在不同态对之间预先固定的矩阵。
$H_z(s)$ 只在实际非空的固定 $s$ 切片上定义。
原卷的 $a_1,a_2,D$ 在这里分别为 $a,b,s$；
原卷 (X.3) 的 $U$ 为这里的 $V$。
下文的 $A=a^2/4$、$B=b^2/4$ 是非负标量，
不沿用原卷实反对称矩阵 $A$ 的记号。
$d$ 是人口上限的合并量，不是 Hilbert 空间维数或第二差权重。
大写 $Z$ 及小写 $\xi$ 是实部谱坐标，不是人口向量 $z$。

原卷定理 76.1 给出的共同四谱接口写为

$$
\begin{gathered}
r=(x,y,\xi,w),\quad x\geq y\geq\xi\geq w\geq0,\quad
x+y+\xi+w=1,\\
x\geq P,\quad x+y\geq Q,\quad w\leq V,\\
xy\geq A,\quad xw\geq B,\quad y\xi\geq B,\quad
xy\xi w\geq AB.
\end{gathered}
\tag{XII.3}
$$

存在这样一个共同 $r$，当且仅当 $(a,b)\in\mathcal S_z$。
这是包括零人口、相同人口和奇异实部的实际密度接口；
四个乘积不等式必须由同一个 $r$ 满足。
其证明使用原卷命题 73.2 的奇异值乘积与第四外幂必要界、
命题 75.1 的同谱充分性，以及实 Schur–Horn 对角接口。
这些标准谱工具在原卷相应证明内使用，不作为本续卷新增的独立结论。
人口排序还给出

$$
Q\leq2P,\qquad 1-V\leq3P.
\tag{XII.4}
$$

## 62. 任意五人口的确定四谱与充要判据

**定义 82.1（不含谱优化的候选）。** 对 $0<b\leq a$、$a+b\leq1$、
$d>0$，定义

$$
\begin{aligned}
A&=a^2/4,& B&=b^2/4,\\
h(a)&=
\begin{cases}
(1+\sqrt{1-3a^2})/6,&0\leq a\leq1/2,\\
a/2,&1/2\leq a\leq1,
\end{cases}\\
X&=\max\{P,h(a),B/d\},& T&=1-X,\\
u&=A/X,& q&=Q-X,& v&=(T-u)/2,\\
W&=\min\{d,u,v\},&
Y&=\max\{u,q,(T-W)/2\},&
Z&=T-Y-W.
\end{aligned}
\tag{XII.5}
$$

在 $a=1/2$ 两个 $h$ 表达式均为 $1/4$。
总有 $h(a)\geq\max\{1/4,a/2\}$，所以所有除以 $X$ 的表达式均有定义。
即使候选不合格，也先按这些实数表达式计算，再使用下述两个不等式筛选。

**定理 82.2（全人口固定差谱的显式充要条件）。**
对定义 81.1 中的任意 $z$，正第二权重的成员资格恰为

$$
\boxed{
(a,b)\in\mathcal S_z
\ \Longleftrightarrow\
\begin{cases}
0<b\leq a,\quad a+b\leq1,\quad d>0,\\
X(1-X)\geq A+2B,\\
XYZW\geq AB,
\end{cases}}
\qquad(b>0),
\tag{XII.6}
$$

其中右侧使用 (XII.5) 的同一个确定四元组。
合格时 $(X,Y,Z,W)$ 本身满足 (XII.3)，因而是实际密度见证的共同实部谱。
没有 $P\geq1/2$ 的前提。
零轴单独为

$$
(a,0)\in\mathcal S_z
\ \Longleftrightarrow\
0\leq a\leq2\sqrt{m(1-m)},\qquad m=\max\{P,1/2\}.
\tag{XII.7}
$$

$d=0$ 时没有正 $b$；$P=1$ 时整个域只有 $(0,0)$。

**证明。** 从 (XII.3) 出发，$b>0$ 强制四个谱坐标严格正。
$w\leq V$ 及 $x+y\geq Q$ 因而给 $V>0$、$Q<1$，即 $d>0$。
$a+b\leq1$ 是两个密度矩阵的迹距离上界。

先作一个只替换存在见证的约化。若 $xw>A$，置

$$
x'=\frac{x+w+\sqrt{(x+w)^2-4A}}2,\qquad w'=A/x'.
\tag{XII.8}
$$

因 $x\geq w>0$、$A<xw$，有 $x'>x$、$0<w'<w$、
$x'+w'=x+w$、$x'w'=A$。保留 $y,\xi$ 后仍降序且迹一；
$P,Q,V$ 约束改善，$x'y\geq xy\geq A$、$x'w'=A\geq B$，
而新四乘积为 $Ay\xi\geq AB$。
所以只须考虑另一个满足 $xw\leq A$ 的共同谱。

对这个谱，$x\geq1/4$、$x\geq\sqrt A=a/2$。
由 $y,\xi\leq x$ 和 $w\leq A/x$ 得

$$
1\leq3x+A/x,\qquad 3x^2-x+A\geq0.
\tag{XII.9}
$$

二次式在 $x\geq1/4$ 上严格递增。
若 $a\leq1/2$，其大根为 $h(a)$，小根至多 $1/6$；
故 (XII.9) 与 $x\geq1/4,a/2$ 恰要求 $x\geq h(a)$。
若 $a\geq1/2$，在 $x=a/2$ 处二次式为 $a(a-1/2)\geq0$，
故 $x\geq a/2$ 已足够；这也包括判别式为负的情形。
又由 (XII.3) 得

$$
x\geq P,\qquad xV\geq B,\qquad
x(1-Q)\geq x(\xi+w)\geq2xw\geq2B.
\tag{XII.10}
$$

因为 $B/d=\max\{B/V,2B/(1-Q)\}$，这些下界正是 $x\geq X$。
同时

$$
x(1-x)=xy+x\xi+xw\geq A+2B=:C.
\tag{XII.11}
$$

这里 $x\xi\geq y\xi\geq B$。
在正 $b$ 的权重范围内 $a<1$，且
$b^2\leq a(1-a)$，所以
$a^2+2b^2\leq2a-a^2<1$，从而 $C<1/4$。
记

$$
x_\pm=\frac{1\pm\sqrt{1-4C}}2.
\tag{XII.12}
$$

还有
$(a/2)(1-a/2)-C=(a-a^2-b^2)/2\geq0$，故
$x_-\leq a/2\leq h(a)$。
于是每个约化见证的第一坐标都在 $[X,x_+]$ 内。

下面固定 $x\in[X,x_+]$，用 $T_x=1-x$、
$u_x=A/x$、$q_x=Q-x$、$k_x=\max\{u_x,q_x\}$，并定义

$$
\begin{aligned}
W_x^0&=\min\{V,u_x,T_x/3,(T_x-k_x)/2\},\\
Y_x&=\max\{k_x,(T_x-W_x^0)/2\},\qquad
Z_x=T_x-Y_x-W_x^0.
\end{aligned}
\tag{XII.13}
$$

首先 $k_x\leq x$：$u_x\leq x$ 来自 $x\geq\sqrt A$，
$q_x\leq x$ 来自 $Q\leq2P\leq2x$。
(XII.11) 在整个区间成立。四个 $W_x^0$ 上限分别都至少为 $B/x$：
前两项使用 $xV\geq B$、$A\geq B$；
第三项使用 $xT_x\geq A+2B\geq3B$；
最后一项在 $k_x=u_x$ 时使用 $xT_x-A\geq2B$，
在 $k_x=q_x$ 时使用 $x(1-Q)\geq2B$。

这四个上限还都至少为 $1-3x$。
对 $V$ 使用 $x\geq P\geq(1-V)/3$；
对 $u_x$ 使用 (XII.9)；
对 $T_x/3$ 使用 $x\geq1/4$；
对 $(T_x-k_x)/2$ 使用
$k_x\leq x\leq5x-1$。因此

$$
W_x^0\geq\max\{B/x,1-3x\}>0,\qquad k_x\leq x.
\tag{XII.14}
$$

给定 $w$ 后，在 $y+\xi=T_x-w$、$y\geq\xi\geq w$、
$y\geq k_x$ 中，$y\xi$ 的最大值由
$y=\max\{k_x,(T_x-w)/2\}$ 取得。
存在这样的 $y\leq x$ 恰额外要求 $k_x\leq x$、$w\geq1-3x$；
$w$ 的上限恰为 $W_x^0$。
在两种最大乘积表达式上，

$$
\begin{array}{c|c}
y\xi w&\dfrac{d}{dw}(y\xi w)\\ \hline
w(T_x-w)^2/4&(T_x-w)(T_x-3w)/4\\
k_xw(T_x-k_x-w)&k_x(T_x-k_x-2w)
\end{array}
\tag{XII.15}
$$

导数在 $w\leq W_x^0$ 的相应分支上非负，换支处函数连续。
这里仅为上界暂时放松 $y\xi\geq B$；
其余约束由 (XII.14) 保证在 $w=W_x^0$ 同时可行。
故保留约束下最大的四乘积为

$$
F(x)=xY_xZ_xW_x^0.
\tag{XII.16}
$$

现在合并选择器。因为

$$
\frac{T_x-k_x}{2}
=\min\{(T_x-u_x)/2,(1-Q)/2\},
$$

且对任意实 $u_x,T_x$，
$\min\{u_x,(T_x-u_x)/2\}\leq T_x/3$，所以

$$
W_x^0=\min\{d,u_x,v_x\},\qquad v_x=(T_x-u_x)/2.
\tag{XII.17}
$$

在 (XII.14) 的可行区间内，$F$ 的全部非恒等开分支归入下表。
导数固定 $A,B,P,Q,V$，从而也固定 $d$。

| $W_x^0$ | $Y_x$ | $F(x)$ | $F'(x)$ |
| --- | --- | --- | --- |
| $d$ | $(T_x-d)/2$ | $dx(T_x-d)^2/4$ | $d(T_x-d)(1-d-3x)/4$ |
| $d$ | $u_x$ | $Ad(T_x-A/x-d)$ | $Ad(-1+A/x^2)$ |
| $d$ | $q_x$ | $dx(Q-x)(1-Q-d)$ | $d(1-Q-d)(Q-2x)$ |
| $u_x$ | $(T_x-u_x)/2$ | $A(T_x-A/x)^2/4$ | $A(T_x-A/x)(-1+A/x^2)/2$ |
| $v_x$ | $u_x$ | $A(T_x-A/x)^2/4$ | $A(T_x-A/x)(-1+A/x^2)/2$ |
| $u_x$ | $q_x$ | $A(Q-x)(1-Q-A/x)$ | $A[-(1-Q)+AQ/x^2]$ |

必须保留两种只有等号的选择情形。
其一，$W_x^0=v_x,Y_x=q_x$ 时，
$v_x\leq d\leq(1-Q)/2=(T_x-q_x)/2$ 给 $u_x\geq q_x$，
而 $Y_x=q_x$ 给反向不等式，故 $u_x=q_x$。
它是表中 $W_x^0=v_x,Y_x=u_x$ 的等值情形。
其二，当 $d=(1-Q)/2$ 且
$W_x^0=d,Y_x=(T_x-d)/2$ 时，
$d\leq v_x$ 给 $u_x\leq q_x$，
$d\leq u_x$ 给 $d\leq u_x$，而
$(T_x-d)/2=(q_x+d)/2\geq q_x$ 给 $d\geq q_x$。
因此

$$
u_x=q_x=d,\qquad x=(3Q-1)/2.
\tag{XII.18}
$$

这是单点等号情形，不能作为一条新的开分支删除或外推。
此外，$W_x^0=u_x,Y_x=u_x$ 强制 $u_x=T_x/3$；
$W_x^0=v_x,Y_x=(T_x-v_x)/2$ 也强制
$u_x=v_x=T_x/3$。两者都与表中的连续值一致。
这穷尽三个 $W$ 项及三个 $Y$ 项的全部组合，包括多重并列。

所有开分支的导数非正。
第一行若 $d=V$，用 $x\geq P\geq(1-V)/3$；
若 $d=(1-Q)/2<V$，它只能是 (XII.18) 的单点，故没有这条开分支。
第二、第四、第五行用 $x^2\geq A$ 及非负尾因子。
第三行用 $d\leq(1-Q)/2$、$Q\leq2P\leq2x$。
最后一行的 $W_x^0=u_x$ 给
$A/x\leq d\leq(1-Q)/2$，所以

$$
AQ/x^2\leq (1-Q)Q/(2x)\leq1-Q.
\tag{XII.19}
$$

所有选择项是 $x>0$ 上的有理函数；
非恒等的比较只在有限个多项式根处换号。
恒等并列在同一段给相同函数值，单点并列由连续性连接。
因此上述导数证明 $F$ 在整个闭区间 $[X,x_+]$ 上不增，
而不需要 $x\geq1/2$。

必要性现在成立：约化见证给
$AB\leq xy\xi w\leq F(x)\leq F(X)$，并有 $X\leq x_+$。
又 $X\geq h(a)\geq x_-$，故
$X(1-X)\geq A+2B$。
(XII.17) 在 $x=X$ 就是 (XII.5)，所以第二个测试也成立。

反向，两个测试使 $X\in[x_-,x_+]$，从而 (XII.13)–(XII.14)
在 $x=X$ 适用。它们给
$X\geq Y\geq Z\geq W>0$、迹一、$X\geq P$、
$X+Y\geq Q$、$W\leq V$、$XY\geq A$、$XW\geq B$。
这里 $Y\leq X$ 使用 $W\geq1-3X$，
$Z\geq W$ 使用 $W\leq T/3,(T-\max\{u,q\})/2$。
最后 $XW\leq A$，所以

$$
YZ=\frac{XYZW}{XW}\geq\frac{AB}{XW}\geq B.
\tag{XII.20}
$$

同一个确定四元组满足全部 (XII.3)，由原卷定理 76.1 得到实际态对；
第 63 节还给出不需求解连续插值方程的具体矩阵。
零轴及其实际达到复用原卷定理 77.3 的秩二谱
$(m,1-m,0,0)$ 和单个虚反对称块。
$d=0$ 排除正 $b$ 已在开头证明；$P=1$ 代入 (XII.7) 即得原点。$\square$

**推论 82.3（重人口公式与边界保持）。**
若 $P\geq1/2$，(XII.5) 的第一坐标化为

$$
X=\max\{P,B/d\}
=\max\{P,B/V,2B/(1-Q)\}.
\tag{XII.21}
$$

若 $P<1/2$，仍使用完整的 $h(a)$ 项。
人口为零或并列时，(XII.6) 不引入严格人口排序条件。

**证明。** $a+b\leq1$ 给 $a/2\leq1/2$；
在 $a\leq1/2$ 上 $h(a)\leq1/3$，
在另一段上 $h(a)=a/2\leq1/2$。
故重人口时 $P$ 支配 $h$。
证明 82.2 只用 (XII.4) 的非严格不等式，
零分母只在已独立排除的 $d=0$ 情形出现。$\square$

## 63. 同一四谱的三分支实际半正密度

**定理 83.1（确定谱的显式实二维构造）。**
设 $b>0$，且 $r=(x,y,\xi,w)$ 满足 (XII.3)，
特别可以取定理 82.2 的 $(X,Y,Z,W)$。
以下三个互斥分支给出实 $2\times2$ 矩阵 $M$，
其奇异值恰为 $\alpha=\sqrt A=a/2$、$\beta=\sqrt B=b/2$，
且

$$
\left\|
\operatorname{diag}(\sqrt x,\sqrt\xi)^{-1}
M\operatorname{diag}(\sqrt y,\sqrt w)^{-1}
\right\|_{\mathrm{op}}\leq1.
\tag{XII.22}
$$

一次共同实正交共轭便把该 $M$ 变成指定人口的两实际密度矩阵。

**证明。** 正 $b$ 使四个谱坐标均严格正。
记四个容量和共同乘积为

$$
p=xw,\quad q_0=y\xi,\quad r_0=xy,\quad c_0=\xi w,\quad
K=xy\xi w=pq_0=r_0c_0,\quad
L=\max\{p,q_0\},\quad \ell=\min\{p,q_0\}.
\tag{XII.23}
$$

这里 $q_0,r_0$ 只在本证明表示容量，不表示原端口块维数或四谱。
已知 $A\leq r_0$、$B\leq\ell$、$AB\leq K$，
且 $r_0\geq L\geq\ell\geq c_0>0$。

第一分支为 $A\leq L$。若 $p\geq q_0$，取

$$
M=\begin{pmatrix}0&\alpha\\ \beta&0\end{pmatrix};
\qquad
\text{若 }p<q_0,\quad
M=\begin{pmatrix}0&\beta\\ \alpha&0\end{pmatrix}.
\tag{XII.24}
$$

大奇异值必须放在较大反对角容量的位置。
归一化后的两个非零元素分别被 $A\leq L$、$B\leq\ell$ 控制，
故 (XII.22) 成立，奇异值也正是 $\alpha,\beta$。

第二分支为 $A>L$ 且 $B\leq c_0$。取

$$
M=\operatorname{diag}(\alpha,\beta).
\tag{XII.25}
$$

$A\leq xy$、$B\leq\xi w$ 直接给 (XII.22)。
第一、第二分支都允许其所含的等号。

第三分支为 $A>L$ 且 $B>c_0$。定义

$$
\begin{aligned}
\tau&=(AB/K)^{1/4},\\
\delta&=(xy+\xi w)-(xw+y\xi)=(x-\xi)(y-w),\\
\theta&=\frac{(A+B)/\tau^2-(xw+y\xi)}{\delta},\\
U_\theta&=
\begin{pmatrix}
\sqrt\theta&-\sqrt{1-\theta}\\
\sqrt{1-\theta}&\sqrt\theta
\end{pmatrix},\\
M&=\tau\operatorname{diag}(\sqrt x,\sqrt\xi)\,
U_\theta\,\operatorname{diag}(\sqrt y,\sqrt w).
\end{aligned}
\tag{XII.26}
$$

这些根式均有定义。事实上 $0<\tau\leq1$。
若 $x=\xi$，排序给 $x=y=\xi$，便有
$A\leq xy=y\xi\leq L$，矛盾；
若 $y=w$，则 $A\leq xy=xw\leq L$，同样矛盾。
故 $\delta>0$，没有在容量并列的零分母上取商。

由 $A>L$、$B\leq\ell$、$A\leq r_0$、$B>c_0$ 得

$$
L/\ell\leq A/B\leq r_0/c_0.
\tag{XII.27}
$$

函数 $t\mapsto\sqrt K(\sqrt t+1/\sqrt t)$ 在 $t\geq1$ 上不减。
在 (XII.27) 的两端，其值分别为 $p+q_0$ 和 $r_0+c_0$；
在 $t=A/B$，其值为 $(A+B)/\tau^2$。
所以 $0\leq\theta\leq1$，包括旋转的两个端点。
归一化矩阵恰为 $\tau U_\theta$，给出 (XII.22)。
又有

$$
\begin{aligned}
\operatorname{tr}(MM^T)
 &=\tau^2[\theta(xy+\xi w)+(1-\theta)(xw+y\xi)]
 =A+B,\\
\det(MM^T)&=\tau^4xy\xi w=AB.
\end{aligned}
\tag{XII.28}
$$

因此 $MM^T$ 的两个特征值为 $A,B$；
$A=B$ 时这仍成立，不需要选择不同的特征根。
三个分支穷尽全部可能。

在分组坐标 $(1,3\mid2,4\mid5)$ 中，置

$$
\begin{aligned}
R_*&=\operatorname{diag}(x,\xi,y,w,0),\\
C_*&=\begin{pmatrix}0&M\\-M^T&0\end{pmatrix}\oplus0,\qquad
T_*=\operatorname{diag}(\sqrt x,\sqrt\xi)^{-1}
M\operatorname{diag}(\sqrt y,\sqrt w)^{-1}.
\end{aligned}
\tag{XII.29}
$$

在前四轴上的合同分解为

$$
R_*\pm iC_*=
\operatorname{diag}(\sqrt x,\sqrt\xi,\sqrt y,\sqrt w)
\begin{pmatrix}I&\pm iT_*\\ \mp iT_*^T&I\end{pmatrix}
\operatorname{diag}(\sqrt x,\sqrt\xi,\sqrt y,\sqrt w),
\tag{XII.30}
$$

第五轴补零。中间块的特征值为 $1\pm s_j(T_*)$，
故两边半正，迹均为一；差 $2iC_*$ 的谱为 (XII.2)。

由 $x\geq P$、$x+y\geq Q$、$w\leq V$ 和迹一，
$(x,y,\xi,w,0)$ 主序支配 $\zeta$；
第三前缀恰为 $1-w\geq1-V$，第四前缀自动成立。
使用原卷定理 76.1 证明内的实 Schur–Horn 接口，
选同一个实正交矩阵 $O$ 使
$\operatorname{diag}(OR_*O^T)=z$，并置

$$
\rho=O(R_*+iC_*)O^T,\qquad
\sigma=O(R_*-iC_*)O^T.
\tag{XII.31}
$$

这给两个半正迹一矩阵，人口恰为原顺序中的 $z$，
共同实部为 $OR_*O^T$，差谱和迹距离均准确保持。
若先对排序后的 $\zeta$ 选 $O$，则把同一个逆排序置换同时吸收到 $O$。
实 Schur–Horn 的经典来源为
Carlen–Lieb，*Short proofs of theorems of Mirsky and Horn on diagonals and eigenvalues of matrices*，
[arXiv:0904.0734v3](https://arxiv.org/pdf/0904.0734v3) 的开篇 Horn 陈述及其 Horn 归纳证明；
不是其中属于 Mirsky 的 Theorem 1.2。
这里复用该实对角接口，不另立标准 Schur–Horn 定理。
最后 $D_3\rho D_3^\dagger,D_3\sigma D_3^\dagger$
给原物理坐标的态对；$D_3$ 为对角被动变换，保留人口。

$b=0$ 不使用 (XII.22) 的逆矩阵。
此时使用原卷定理 77.3 的
$R_*=\operatorname{diag}(m,1-m,0,0,0)$、
$C_{12}=a/2$、$C_{21}=-a/2$，其余元素为零。
唯一非零块的行列式为 $m(1-m)-a^2/4\geq0$。
同一实 Schur–Horn 共轭给 (XII.7) 的全部实际见证；
$P=1$ 时只有 $a=0$，可直接取 $\rho=\sigma=\operatorname{diag}z$。
因此奇异第五轴、其他零轴、重复人口、容量并列和 $a=b$ 均在相应分支内。$\square$

## 64. 十九个二元多项式与七十六个单变量消去式

**定义 84.1（固定距离的有限根表）。**
令 $m=\max\{P,1/2\}$、$s_{\max}=2\sqrt{m(1-m)}$。
先考虑 $0<s\leq s_{\max}$ 且 $d>0$。
以 $t$ 表示第二权重，并令

$$
0\leq t\leq s/2,\quad a=s-t,\quad
A=(s-t)^2/4,\quad B=t^2/4,\quad T=1-x.
\tag{XII.32}
$$

以下十九个 $f_j(x,t)$ 的系数只依赖固定的 $P,Q,d,s$：

$$
\begin{aligned}
f_1&=x-P,&
f_2&=x^2-A,&
f_3&=dx-B,\\
f_4&=3x^2-x+A,&
f_5&=a-\tfrac12,\\
f_6&=dx-A,&
f_7&=xT-A-2dx,&
f_8&=xT-3A,\\
f_9&=A-x(Q-x),\\
f_{10}&=2A-xT+dx,&
f_{11}&=2Q-x-1+d,\\
f_{12}&=x(2Q-x-1)+A,&
f_{13}&=x(4Q-1-3x)-A,\\
f_{14}&=xT-A-2B,\\
f_{15}&=dx(T-d)^2-4AB,\\
f_{16}&=d[x(T-d)-A]-Bx,\\
f_{17}&=dx(Q-x)(1-Q-d)-AB,\\
f_{18}&=(xT-A)^2-4Bx^2,\\
f_{19}&=(Q-x)[x(1-Q)-A]-Bx.
\end{aligned}
\tag{XII.33}
$$

对每个 $f=f_j$ 作四种单变量消去。前三种为

$$
E_P[f](t)=f(P,t),\qquad
E_a[f](t)=f((s-t)/2,t),\qquad
E_B[f](t)=d^{n_f}f(B/d,t),
\tag{XII.34}
$$

其中 $n_f$ 为 (XII.33) 显示表达式对 $x$ 的次数；
即使某组参数使首项消失，也可保留该显示次数。
因 $d>0$，乘上 $d^{n_f}$ 不引入或删除根。
第四种先按

$$
q_g(x,t)=3x^2-x+A
$$

作关于 $x$ 的多项式除法，写唯一余式
$U_f(t)x+V_f(t)$，然后定义

$$
E_g[f](t)=A\,U_f(t)^2+U_f(t)V_f(t)+3V_f(t)^2.
\tag{XII.35}
$$

从这 $19\times4=76$ 个实系数单变量多项式中，
丢弃恒零式及非零常数；重复多项式可以保留。
令 $\mathcal C_z(s)$ 为 $0,s/2$ 与其余多项式在 $(0,s/2)$
中的全部实根组成的集合。重根作为一个实数保留。
对 $t>0$，定义过滤谓词 $\Phi_z(s,t)$：
在 (XII.5) 中代入 $a=s-t,b=t$，并同时要求

$$
X(1-X)\geq A+2B,\qquad XYZW\geq AB.
\tag{XII.36}
$$

过滤时直接使用 $h$ 的实分支和原来的 $\max,\min$；
不以平方后方程或消去式的根代替分支合法性。
$t=0$ 按 (XII.7) 单独保留，不作正因子消约。

**定理 84.2（全人口的有限精确根前沿）。**
对每个定义 81.1 的人口向量，固定距离的域恰为
$0\leq s\leq s_{\max}$；域外切片为空。
域内若 $s=0$ 或 $d=0$，则 $H_z(s)=0$。
其余情形，

$$
\boxed{
H_z(s)=
\max\bigl(\{0\}\cup
\{t\in\mathcal C_z(s):t>0,\ \Phi_z(s,t)\}\bigr).
}
\tag{XII.37}
$$

每个消去式的次数至多八，故根候选总数至多 $76\cdot8+2=610$；
这只是允许重复计数的上界。
该公式没有连续谱优化或待选辅助谱。
其每个保留的正候选都由 (XII.5)、(XII.24)–(XII.31)
给出实际同人口、同实部态对；零候选由零轴构造达到。
整个固定距离切片仍恰为

$$
\{(s-b,b):0\leq b\leq H_z(s)\}.
\tag{XII.38}
$$

特别地，当 $P\leq1/2$，

$$
H_z(1)=\min\{1/2,1-2P,2V\};
\tag{XII.39}
$$

当 $P\geq1/2$，最远距离端点只有 $(s_{\max},0)$。

**证明。** 实际距离域、全部切片为填满的闭区间、
最大值达到以及 (XII.39)，均复用原卷定理 77.3；
它们来自同一个共同四谱域，不来自权重域的凸化。
这里只须证明 (XII.37) 的根表不会漏掉该已存在的最大值。
正 $b$ 的可行性则由定理 82.2 完全给出。

第一坐标的可能分支是

$$
x=P,\qquad x=a/2,\qquad x=B/d,\qquad
x=x_g=\frac{1+\sqrt{1-3a^2}}6.
\tag{XII.40}
$$

$a/2$ 仅在 $a\geq1/2$ 作为 $h$ 项可用，
$x_g$ 仅在 $a\leq1/2$ 可用；
在 $a=1/2$ 两者相同。
选中的值必须等于 $\max\{P,h(a),B/d\}$，并列均保留。
$f_1,f_2,f_3,f_4$ 分别记录与 $P,a/2,B/d,x_g$ 相遇的等式：
在正候选邻域内 $x>0,a>0$，所以 $x^2=A$ 的非负根正是 $a/2$。
几何分支只取大根；小根至多 $1/6$，实际 $X\geq1/4$。
$f_5$ 记录两个 $h$ 表达式的可用性边界。
因此任一真正的 $X$ 换支都产生相应消去式的根，除非该比较恒等。

在一个 $X$ 分支上，写 $u=A/x$、$q=Q-x$、
$v=(T-u)/2$。
$W=\min\{d,u,v\}$ 的三个两两相等式，清去正分母后为
$f_6,f_7,f_8$。
$Y=\max\{u,q,(T-W)/2\}$ 的比较依次为：

| 所选 $W$ | $u=q$ | $u=(T-W)/2$ | $q=(T-W)/2$ |
| --- | --- | --- | --- |
| $d$ | $f_9=0$ | $f_{10}=0$ | $f_{11}=0$ |
| $u$ | $f_9=0$ | $f_8=0$ | $f_{12}=0$ |
| $v$ | $f_9=0$ | $f_8=0$ | $f_{13}=0$ |

表中只标相等式，不用乘过分母的符号方向替代原始比较。
$f_{14}$ 正是容量测试的边界。
在 $t>0$ 上 $x,A>0$，五种乘积边界如下：

| 所选 $W,Y$ | $xYZW-AB$ 的正因子消约后等式 |
| --- | --- |
| $d,(T-d)/2$ | $f_{15}=0$ |
| $d,u$ | $f_{16}=0$ |
| $d,q$ | $f_{17}=0$ |
| $u,(T-u)/2$ 或 $v,u$ | $f_{18}=0$ |
| $u,q$ | $f_{19}=0$ |

定理 82.2 证明中保留的 $W=v,Y=q$ 只能在 $q=u$ 上发生，
所以其乘积式已由 $f_{18}$ 覆盖；
$W=d,Y=(T-d)/2$ 在 $d=(1-Q)/2$ 时只能是 (XII.18)，
仍由 $f_{15}$ 及选择器等式覆盖。
$W=u,Y=u$ 及 $W=v,Y=(T-v)/2$ 强制 $u=v=T/3$，
也给同一个 $f_{18}$ 等式。
因此没有遗漏一个需要额外乘积多项式的等号分支。

四种消去都包含对应真实相等式的根。
前三种是直接代入并乘以正常数。
对第四种，若 $\gamma_1,\gamma_2$ 为 $q_g$ 的两个根，则
$\gamma_1+\gamma_2=1/3$、$\gamma_1\gamma_2=A/3$，从而

$$
3(U_f\gamma_1+V_f)(U_f\gamma_2+V_f)
=A U_f^2+U_fV_f+3V_f^2.
\tag{XII.41}
$$

只要 $f(x_g,t)=0$，右侧便为零。
反向不作要求；小根、不可用分支或其他代数消去产生的候选，
统一交给 (XII.36) 的原始实分支过滤。
可能的重根不改变此蕴含。

次数界也可直接由表验证，不需要数值采样。
每个 $f_j$ 的 $x,t$ 总次数至多四；
因此代入常数 $P$ 或一次式 $a/2$ 后次数至多四。
赋 $x$ 权二、$t$ 权一时，每项的权次数至多八，
故代入 $B/d$ 后次数至多八。
对几何分支，逐次使用

$$
x^2\equiv(x-A)/3,\qquad
x^3\equiv((1-3A)x-A)/9,\qquad
x^4\equiv((1-6A)x-A+3A^2)/27
\pmod {q_g}.
\tag{XII.42}
$$

在 (XII.33) 的十九个式子中，这给
$\deg_t U_f\leq2$、$\deg_t V_f\leq4$，
故 (XII.35) 的次数至多
$\max\{2+2\cdot2,2+4,2\cdot4\}=8$。
所有非恒零式因而只有有限个实根。

还须核对丢弃恒零消去式不会隐藏边界。
直接代入分支的恒零式就是该分支上的函数恒等。
对几何分支，$q_g$ 在 $\mathbb R(t)[x]$ 上不可约：
其判别式 $1-3(s-t)^2$ 有两个不同的简单实零点，
不能是有理函数的平方。
若 (XII.35) 恒零且 $U_f\ne0$，
则 $-V_f/U_f$ 为 $q_g$ 的有理函数根，矛盾；
若 $U_f=0$，则 $3V_f^2=0$。
因此恒零 $E_g[f]$ 必有 $U_f=V_f=0$，
即 $f$ 在整个几何分支恒等为零。
这些恒等式只是并列关系，不是未列出的换号点。

设实际正端点 $H$ 不等于 $s/2$，也不是任何保留多项式的根。
在 $H$ 的一个小邻域内，所有非恒等选择器比较具有固定符号；
$f_5$ 同样固定可用的 $h$ 表达式。
于是可在该邻域选定连续解析的 $X,W,Y$ 分支，
恒等并列给相同值。
容量测试及该乘积测试若在 $H$ 为零，
其非恒等消去式便以 $H$ 为根，矛盾；
若对应消去式恒零，上段证明说明测试在该分支恒等为零。
所以两测试或严格成立，或在整段上为等号，
可行性必延伸到 $H$ 右侧，与最大性矛盾。
根表之外的端点 $0,s/2$ 已另列，
故真实最大值属于 $\mathcal C_z(s)$。

每个保留候选由 (XII.6) 真正可行，故不超过真实最大值；
真实最大值又已在候选中，证明 (XII.37)。
若最大值为零，用零轴，不用上述正 $A,x$ 消约。
由原卷的连续填充结论，(XII.38) 的全部中间点也有实际共同谱见证；
对其中任意正 $b$，还可以直接对该 $a=s-b,b$
使用 (XII.5) 和定理 83.1，而无需拼接两个不同态对。
全域及两个距离端点均按原有量词保持。$\square$

## 65. 精确根指定与原固定菜单的条件接口

**约定 85.1（系数域和有效求根的区别）。**
(XII.37) 是给定实系数上的有限根指定。
当 $z,s$ 为有理数或实代数数时，人口排序、$d$ 的选择、
恒零判断、实根隔离、代数数比较及 (XII.36) 的符号过滤，
均属于有限的精确实代数运算。
当人口和 $s$ 是任意实数时，(XII.37) 仍定义准确的数学端点；
要把它执行为有认证输出的过程，
还须供应精确有序实数运算与比较能力，
包括系数域及所需实代数扩张上的零判断、根隔离和分支符号判断。
仅给有限精度近似或不可判等的实数黑箱，不供应这些能力。
公式不把这项额外能力当作免费资源，也不声称多项式数或次数为最小。

**命题 85.2（同一菜单消费者的有限根参数化）。**
在原卷定理 79.1 的全部控制、输入和末端读口前提下，
保留原 $n=3$ 五维安装、被动帧 $D_3$、
唯一正向收费相位
$S_{13}=\operatorname{diag}(1,1,1,1,i)$，
以及固定二值 PVM
$\{n_1,I-n_1\}$、
$n_1=\operatorname{diag}(0,1,0,0,1)$。
令 $B_k$ 仍只表示该原合同中已知候选对的最优二值概率差。
对每个实际可行 $s$，(XII.37) 给出原前沿的有限根参数：

$$
\{(B_1,B_2)\}
=\{(s-b,s):0\leq b\leq H_z(s)\}.
\tag{XII.43}
$$

正端点输入可选 (XII.5)、(XII.24)–(XII.31) 的同一个态对。

**证明。** 原卷定理 79.1 已在该完整合同下证明
$B_0=0,B_1=a,B_k=a+b=s$（$k\geq2$）及相应有限字达到。
这里不重证原生字实现，也不从被动矩阵构造推断门权限。
定理 84.2 把该原定理的 $H_z(s)$ 换成 (XII.37)，
并为每个 $b$ 提供同一总距离的实际输入对，
所以 (XII.43) 的等号及达到直接保持。
该推论仅在原菜单假设全部成立时使用；
两个预算的最优值可以使用不同设置，
每个设置必须共同作用于两个未知标签，不能依赖实际未知标签。$\square$

**约定 85.3（输入存在、来源与数学归属的范围）。**
本续卷的承重内容是 (XII.6) 的全人口确定谱消去、
(XII.24)–(XII.31) 的三分支矩阵插值，
以及 (XII.33)–(XII.37) 的有限根前沿。
它们是原卷共同谱接口之上的仓内综合推导（repo-derived），
不作全球原创或优先权断言。
实 Schur–Horn、奇异值乘积、外幂与有限维半正谱分解
分别按原卷命题 73.2、75.1、定理 76.1 的出处和条件复用；
这些经典工具不是新增的独立承重定理。

存在域的量词始终是：给定指定帧人口和目标差谱，
存在一对真实半正迹一矩阵及其共同实部。
它不要求每个矩阵满秩，不把人口解释成控制中的逐时守恒量，
也不把普通 $(a,b)$ 坐标下的域假定为凸。
排序、第五谱质量吸收、(XII.8) 的替换和 Schur–Horn 共轭
均用于存在性证明，不是来源制备、共同 CPTP 预处理、
历史相融运输或额外可用控制。
对任何原先给定的来源／历史纤维，仍须另外证明见证属于该纤维；
对原支持三维来源、准备程序、原生实现、完整仪器或经验物理主张，
本存在定理不供应缺失的实现桥梁。
命题 85.2 只复用原固定菜单消费者，不扩大其输入资源、动作或读口，
不增加量子参考、辅助端口、相位、后选择或未知输入副本。
有限根数和次数界不等于纯翻转脉冲数、执行时长、
制备精度、概率估计或重复样本成本界。

## 追加锚（本行以下为增补区）
