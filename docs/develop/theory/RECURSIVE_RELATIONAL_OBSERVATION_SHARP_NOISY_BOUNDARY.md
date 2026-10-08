# 递归关系观察：全未来噪声边界的尖锐二次项

> **本卷的机器契约。** 本卷采用 `generic-v1` 理论卷形状，地址由正文的字节确定。合入后的正文只增不减；修订、勘误和增补写在文末追加锚之后的新章中。数学陈述的依据是相应证明及明确引用的前提，消化状态不承担数学真值。

## 1. 定位、证明范围与主要结论

本卷是参考输入，给出普通数学定义、构造和证明，未经 Lean kernel 验证。证明采用原来源的结构恒等式和本卷的 Euclidean 几何推导；没有使用有限数值实验，也不以既有源文件可读、提案结论或检查状态代替证明。下文以 **PCR** 指 [《参数化叉积恢复》](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md)，精确版本和复用编号列于第 10 章。

对原来的三次带噪向量读取，在两个完整平台参数域内，分别有

$$
R_\delta=\frac12+\frac{\delta^2}{4}+O(\delta^3),
\qquad \delta\downarrow0,\quad\delta>0.
$$

同一结论还单独成立于更宽的实际单位读数类：只要求三个真实读数的范数不超过 1，允许全部实制备，包括零和依赖制备。这里的 $R_\delta$ 对所有集合函数取下确界，计入任意相关、像外报告的完整误差球，对全部未来 $j\ge3$ 取上确界。它是信息论风险，不是有限字、有效取得、有限算术或自主记忆的结论。

本卷给出小噪声区间 $0<\delta\le1/4096$ 上的显式上界、全部 $0<\delta<1$ 上由实际源实现的下界，以及二次系数 $1/4$ 的证明。原十制度、实际达到的 $`H_*`$、$R_0=0$ 和平台粗噪声端点保持原范围。完整中间曲线、最优次主项及有限资源实现仍未解决。

## 2. 原来源、报告纤维与三个不同的源类

**定义 2.1（字面树和固定制备）。** $\mathcal T$ 是由叶 $\alpha,\beta$ 和有序二元节点 $\langle u,v\rangle$ 自由生成的非空有限树集；不作结合、交换或其它语法识别，不限制树大小。固定定向 Euclidean 空间 $\mathbb R^3$。一个实际源 $\mathsf s=(t,p)$ 给定一棵树和一个制备 $p=(a,b)$。解释为

$$
E_p(\alpha)=a,\qquad E_p(\beta)=b,\qquad
E_p(\langle u,v\rangle)=E_p(u)\times E_p(v).
$$

所有同标签叶使用同一个向量。原替换为

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

置 $x_j(\mathsf s)=E_p(\rho^jt)$、$q_j=|x_j|$。每次执行始终使用这个 $p$，取得菜单恰为

$$
\operatorname{Read}(x_0),\ \rho,\ \operatorname{Read}(x_1),\
\rho,\ \operatorname{Read}(x_2),\ \operatorname{Stop}.
$$

比较世界可有不同的合法制备，但每个世界的三读和未来必须由它自己的一棵树、一个固定制备共同实现。证明中旋转、缩放或选树是在构造比较世界，不是观察者的动作。

**定义 2.2（主域与单位读数域）。** 固定 $L,H>0$、$0<d_0<L^4$，记

$$
\begin{aligned}
\Delta(p)&=|a|^2|b|^2-(a\cdot b)^2,\\
\mathcal D_{L,H,d_0}
&=\{(t,p): |a|,|b|\le L,\ \Delta(p)\ge d_0,
\ q_0,q_1,q_2\le H\},\\
\mathcal U&=\{(t,p):q_0,q_1,q_2\le1\}.
\end{aligned}
$$

$L$ 限制叶向量范数，不限制叶数。$\mathcal U$ 没有叶界或正行列式下界，允许全部制备。令 $\varphi=(1+\sqrt5)/2$、$D_{\rm crit}=L^{2/\varphi^2}$。两个原平台恰为

| 平台 | 完整主参数范围 |
| --- | --- |
| 第一平台 $\mathcal P_1$ | $L=1,H\ge1,0<d_0<1$ |
| 第二平台 $\mathcal P_2$ | $L>1,H=1,0<d_0<D_{\rm crit}$ |

两者均为 $\mathcal U$ 的子类。第一平台中，叉积范数不等式和树归纳给任意非空树的范数至多 1，包括每个替换后树；第二平台中该包含关系直接来自三个读界。第二平台的 $d_0<1$、$d_0=1$ 和 $1<d_0<D_{\rm crit}$ 全部保留。

**定义 2.3（完整误差球风险）。** 对任意声明的实际源类 $\mathcal S$ 和 $\delta\ge0$，报告 $y=(y_0,y_1,y_2)$ 遍历全部 $(\mathbb R^3)^3$。定义

$$
\begin{aligned}
\mathcal A_\delta(y)&=\{\mathsf s\in\mathcal S:
\max_{0\le i\le2}|y_i-x_i(\mathsf s)|\le\delta\},\\
R_\delta(\mathcal S)&=\inf_D\ \sup_{\mathsf s\in\mathcal S}
\ \sup_{y:\mathsf s\in\mathcal A_\delta(y)}
\ \sup_{j\ge3}|D(y,j)-x_j(\mathsf s)|.
\end{aligned}
$$

$D:(\mathbb R^3)^3\times\{3,4,\ldots\}\to\mathbb R^3$ 遍历所有集合函数，输出不必是一条实际轨道。$j$ 是外供的数学查询。没有概率、误差独立性或报告属于实际像的条件；三个误差可以任意相关。空纤维上的输出任意定义，不改变风险。

**定理 2.4（尖锐小噪声边界）。** 分别取 $\mathcal S=\mathcal P_1,\mathcal P_2,\mathcal U$。对于 $0<\delta<1$，令

$$
g(\delta)=
\begin{cases}
\dfrac1{2\sqrt{1-\delta^2}},&0<\delta\le1/\sqrt2,\\
\delta,&1/\sqrt2\le\delta<1.
\end{cases}
$$

两式在分界相等。在上述三个类的每一个上，

$$
g(\delta)\le R_\delta(\mathcal S)\le1\quad(0<\delta<1),
\qquad R_0(\mathcal S)=0,\qquad
R_\delta(\mathcal S)=1\quad(\delta\ge1).
$$

若 $0<\delta\le1/4096$，再置

$$
f_\delta=\frac1{2\sqrt{1-\delta^2}},\qquad
B_\delta=\left\lfloor\frac1{64\delta}\right\rfloor,\qquad
U_\delta=\sqrt{f_\delta^2+\frac{3\delta^2}{B_\delta-1}}+2^{-B_\delta}.
$$

则 $B_\delta\ge64$，并有

$$
f_\delta\le R_\delta(\mathcal S)\le U_\delta
\le f_\delta+385\delta^3
\le\frac12+\frac{\delta^2}{4}+386\delta^3.
$$

因此

$$
R_\delta(\mathcal S)=\frac12+\frac{\delta^2}{4}+O(\delta^3),
\qquad
\lim_{\delta\downarrow0,\ \delta>0}
\frac{R_\delta(\mathcal S)-1/2}{\delta^2}=\frac14.
$$

上界在整个 $\mathcal U$ 上统一，故在它的每个实际子类上也有效；任意子类不自动继承下界。下界将在两个原平台内分别构造。证明见第 3–6 章。

## 3. 从原树到投影幂约束的完整桥梁

本章的运输、五符号归约、符号核和投影恒等式复用 PCR 定理 3.1、引理 4.2、定理 4.3、5.1、引理 16.2、推论 16.3 和第 50 节。为使后面的几何有完整的来源对应，给出普通推导；这些恒等式不重复计作新增数学。

**引理 3.1（全树符号归约及零分支）。** 置

$$
A=|a|^2,\quad B=|b|^2,\quad C=a\cdot b,\quad
K=b\times a,\quad U=K\times a=Ca-Ab,\quad V=K\times b=Ba-Cb.
$$

完整上三角叉积表为

| 左符号 $\times$ | $b$ | $K$ | $U$ | $V$ |
| --- | --- | --- | --- | --- |
| $a$ | $-K$ | $-U$ | $AK$ | $CK$ |
| $b$ | — | $-V$ | $CK$ | $BK$ |
| $K$ | — | — | $-\Delta a$ | $-\Delta b$ |
| $U$ | — | — | — | $-\Delta K$ |

同符号乘积为零，反序取负。每棵树可选择一个对所有制备同时有效的描述子：零，或

$$
\varepsilon A^iB^hC^v\Delta^kZ,
\qquad \varepsilon\in\{\pm1\},\quad i,h,v,k\in\mathbb N,
\quad Z\in\{a,b,K,U,V\}.
$$

证明。前两列由定义和反序得到。代入 $U,V$ 给其余 $a,b$ 行。$K\perp a,b$ 和向量三重积给 $K\times U=-\Delta a$、$K\times V=-\Delta b$；双线性展开给

$$
(Ca-Ab)\times(Ba-Cb)=-\Delta K.
$$

叶有描述子 $a,b$；节点处乘子描述子的单项式，查表后仍有此形状。结构归纳不作除法，覆盖 $C=0$ 和 $\Delta=0$。

令 $f_1=e_1,f_2=e_2,f_3=e_2\times e_1=-e_3$，单位标签为 $\chi(t)=E_{(e_1,e_2)}(t)$。表在参考处有 $A=B=\Delta=1,C=0,U=-f_2,V=f_1$，故 $\chi(t)\in\{0,\pm f_1,\pm f_2,\pm f_3\}$；非零恰是所选描述子非零且无正 $C$ 次数。若 $\chi(t)=\sigma f_\nu\ne0$，$\nu\in\{1,2,3\}$，初值可写成 $\sigma A^iB^h\Delta^kZ$，选取正向符号 $Z\in\{a,b,K,-U,V\}$。标签 $f_1,f_2,f_3$ 分别对应 $Z\in\{a,V\},\{b,-U\},\{K\}$。

**引理 3.2（同源运输、幅度与相位）。** 定义解释换参 $F(a,b)=(b,K)$，则对每棵原树及每个 $j\ge0$，

$$
E_p(\rho^jt)=E_{F^j(p)}(t).
$$

若 $\Delta>0$、$\chi(t)=\sigma f_\nu\ne0$，置 $r=|b|$、$s=\sqrt\Delta$ 及

$$
g_1=b/r,\qquad g_2=K/s,\qquad g_3=V/(rs).
$$

这是左手正交单位标架，循环满足 $g_{i+1}\times g_i=g_{i+2}$。设树的实际两叶数为 $(m,n)$，则

$$
x_1=\sigma r^ms^ng_\nu,\qquad
x_2=\sigma r^ns^{m+n}g_{\nu+1},\qquad
q_{j+2}=q_jq_{j+1},\qquad
x_{j+2}=\sigma(x_{j+1}\times x_j)\quad(j\ge1).
$$

若 $\chi(t)=0$，全部 $x_j,j\ge1$ 为零；若 $\Delta=0$，全部 $x_j,j\ge2$ 为零。

证明。运输在两个叶处直接成立，节点处保持同一有序叉积，树归纳再对 $j$ 归纳。它是解释恒等式，没有执行换制备。$K\perp b$、$|K|=s$、$|V|=rs$ 给标架和乘法表，三循环保持叉积。按真实叶数齐次性，在正交叶 $(rg_1,sg_2)$ 处树值为 $r^ms^n$ 乘对应单位标签。这正是 $F(p)$；下一次换参的叶为 $(sg_2,rsg_3)$，给第二式。计数更新为 $(m,n)\mapsto(n,m+n)$；矩阵满足 $M^2=M+I$，给幅度递推和方向三循环。零标签在正交 $F(p)$ 处仍零；依赖制备满足 $F^2(p)=(0,0)$，给最后两分支。

**引理 3.3（实际初读的正投影）。** 在非零尾分支，令 $w=x_2\times x_1$、$u=x_3/|x_3|$。则

$$
P=x_0\cdot u
=\left(\frac{AB}{\Delta}\right)^i\frac{q_2}{q_1}
\ge\frac{q_2}{q_1}>0.
$$

在全部源上，包括零和依赖分支，有

$$
x_3=\operatorname{sgn}(x_0\cdot w)w,\qquad
|x_0\cdot w|\ge q_2^2,\qquad q_2\le q_0q_1,
\qquad \operatorname{sgn}(0)=0.
$$

证明。暂在非零分支给 $A,B,C,\Delta$ 双次数 $(2,0),(0,2),(1,1),(2,2)$，给 $a,b,K,U,V$ 双次数 $(1,0),(0,1),(1,1),(2,1),(1,2)$。表逐项保持孩子次数之和。若初值描述子为 $\sigma A^iB^h\Delta^kZ$，则

$$
m=2i+2k+m_Z,\qquad n=2h+2k+n_Z.
$$

对应正向 $g_{\nu+2}$ 的五个符号投影为

$$
\begin{array}{c|ccccc}
Z&a&b&K&-U&V\\\hline
Z\cdot g_{\nu+2}&s/r&r&s&s^2/r&rs.
\end{array}
$$

其中两个非平凡项来自 $a\cdot V=\Delta$、$(-U)\cdot b=\Delta$，其余为正范数。各项恰是 $(s/r)^{m_Z}r^{n_Z}$。用 $B=r^2,\Delta=s^2,A=(s^2/r^2)(AB/\Delta)$，相乘后给

$$
\sigma x_0\cdot g_{\nu+2}
=\left(\frac{AB}{\Delta}\right)^i(s/r)^mr^n
=\left(\frac{AB}{\Delta}\right)^i\frac{q_2}{q_1}.
$$

$w=q_1q_2g_{\nu+2}$，实际递推给 $x_3=\sigma w$，上述正投影使报告无噪时的三重积符号为 $\sigma$，且 $u=\sigma g_{\nu+2}$。因为 $AB\ge\Delta$，得到 $P\ge q_2/q_1$。乘 $q_1q_2$ 给三重积界；$P\le q_0$ 给幅度界。在零分支 $w=x_3=0,q_2=0$，所有不含除法的式子照样成立。将符号式应用于每个实际替换后的树，三次准确读恢复每个有限未来时刻；在实际像外任意定义，证明全部主域及 $\mathcal U$ 的 $R_0=0$。

**推论 3.4（无负指数的全未来与投影幂）。** 令 $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$。对 $j\ge3$，置 $a_j=F_{j-2},b_j=F_{j-1}$，约定 $0^0=1$。有

$$
x_j=
\begin{cases}
q_1^{a_j-1}q_2^{b_j}x_1,&j\equiv1\pmod3,\\
q_1^{a_j}q_2^{b_j-1}x_2,&j\equiv2\pmod3,\\
q_1^{a_j-1}q_2^{b_j-1}x_3,&j\equiv0\pmod3.
\end{cases}
$$

在 $\mathcal U$ 中，所有未来范数至多 $Q=q_1q_2\le1$；相位 1、2 的未来分别位于 $[0,x_1]$、$[0,x_2]$。任意非零相位 0 目标写成 $x_j=q u$ 后，有

$$
0<P=x_0\cdot u\le1,\qquad 0<q=q_1^{a_j}q_2^{b_j}\le P^{b_j}.
$$

证明。幅度乘法递推给 $q_j=q_1^{a_j}q_2^{b_j}$，与方向三循环合并给三条公式。指数非负，零尾中相位 0 锚为零，另外两相位的正 $q_2$ 次数使输出为零，故无需除法。单位读界使 $q_1,q_2\le1$，给全未来幅度和两线段界。相位 0 的方向恰为引理 3.3 的 $u$，故

$$
q=q_1^{a_j+b_j}\left(\frac{q_2}{q_1}\right)^{b_j}
\le P^{b_j}.
$$

这个新使用方式保留同一实际树的投影和幅度关系；不声称独立选择的幅度、方向或标量过程都可由原树实现。

**命题 3.5（中性成员的精确边界）。** $\mathcal U$ 的非零中性尾满足 $q_1=q_2=1$、$r=s=1$、$\Delta=1$，且 $x_0=x_3$。第一平台有中性成员；第二平台有中性成员恰当且仅当 $d_0\le1$，包括等号。其 $d_0>1$ 部分的非零尾全部严格收缩。

证明。非零尾的对数递推特征根为 $\varphi,-1/\varphi$，主系数符号为

$$
\log q_1+\varphi\log q_2
=(m+\varphi n)(\log r+\varphi\log s).
$$

中性令该式为零；单位读界给两对数非正，所以二者均零。两个幅度方程在 $\log r,\log s$ 中的系数矩阵为 $\left(\begin{smallmatrix}m&n\\n&m+n\end{smallmatrix}\right)$，行列式 $m^2+mn-n^2\ne0$：单叶情形直接成立，其余若零会令有理数 $n/m$ 等于黄金无理根。因此 $r=s=1$。又 $P\ge1,q_0\le1$，Cauchy–Schwarz 的等号给 $x_0=u=x_3$。正交单位叶的 $\alpha$ 是合法中性源，在两个平台内恰需 $d_0\le1$。没有中性时，上式非正且不能为零，故严格收缩。这个结论没有要求每个底层中性制备都为正交单位叶。

## 4. 一个中心的线段与投影幂几何

**引理 4.1（统一中心及线段包围）。** 固定 $0<\delta\le1/8$。对全部 $y\in\mathbb R^3$，置

$$
k(y)=1+|y|^2-\delta^2>0,\qquad C_\delta(y)=\frac{y}{k(y)}.
$$

则 $|C_\delta(y)|\le f_\delta$。若 $|x|\le1,|y-x|\le\delta$，则全部 $t\in[0,1]$ 有 $|tx-C_\delta(y)|\le f_\delta$。

证明。写 $r=|y|$，平方 $(r-\sqrt{1-\delta^2})^2\ge0$ 给 $k(y)\ge2r\sqrt{1-\delta^2}$，包括 $r=0$。若 $r\ge\delta$，则 $k\ge1$，兼容性给 $2y\cdot x\ge|x|^2+r^2-\delta^2$，从而

$$
|x-C_\delta(y)|^2-|C_\delta(y)|^2
\le\frac{k-1}{k}(|x|^2-1)\le0.
$$

平方距离在 $t\in[0,1]$ 上凸，两个端点已受界，故全线段受界。若 $r<\delta$，则 $|x|<2\delta$、$|C_\delta(y)|\le\delta/(1-\delta^2)\le2\delta$，全线段距离至多 $4\delta\le1/2\le f_\delta$。证明没有使用方向、符号或像成员判断。

**引理 4.2（投影幂包围）。** 保持 $0<\delta\le1/8$，设 $|x|\le1,|y-x|\le\delta,|u|=1$，$p=x\cdot u\in[0,1]$，整数 $b\ge2$，以及 $0\le q\le p^b$。则

$$
|qu-C_\delta(y)|
\le\sqrt{f_\delta^2+\frac{3\delta^2}{b-1}}+2^{-b}.
$$

证明。若 $p<1/2$，则 $q\le2^{-b}$，三角不等式和引理 4.1 的中心范数界立即给结论。以下取 $p\ge1/2$，令 $h=p-q\ge0$。$q\le p^b\le p^2$ 给

$$
1-q\le3h,\qquad (b-1)q(1-p)\le h.
$$

第一式来自 $3p-1-2q\ge3p-1-2p^2=(2p-1)(1-p)\ge0$。第二式先在 $q=p^b$ 使用

$$
p-p^b=p(1-p)\sum_{i=0}^{b-2}p^i
\ge(b-1)p^b(1-p),
$$

再减小 $q$：左边 $(b-1)q(1-p)$ 减少，右边 $p-q$ 增加。两式包括 $p=1,h=0$。

写 $e=y-x$。$|e|^2\le\delta^2$ 使 $k\le1+|x|^2+2x\cdot e$，所以

$$
kq-2y\cdot u\le-2h+2\delta|qx-u|.
$$

这里 $q(1+|x|^2)-2p\le2q-2p=-2h$，余项用 Cauchy–Schwarz。并且

$$
|qx-u|^2\le(1-q)^2+2q(1-p)
\le9h^2+\frac{2h}{b-1}.
$$

故 $|qx-u|\le3h+\sqrt{2h/(b-1)}$。由 $\delta\le1/8$，有

$$
\begin{aligned}
kq-2y\cdot u
&\le-h+2\delta\sqrt{\frac{2h}{b-1}}\\
&\le\frac{2\delta^2}{b-1}.
\end{aligned}
$$

末步在 $\sqrt h$ 中配方。最后 $q\le1,k\ge63/64$，给

$$
\begin{aligned}
|qu-C_\delta(y)|^2
&=|C_\delta(y)|^2+\frac qk(kq-2y\cdot u)\\
&\le f_\delta^2+\frac{3\delta^2}{b-1},
\end{aligned}
$$

因为 $2q/k\le128/63<3$。加上非负的 $2^{-b}$ 即可统一两个 $p$ 分支。这是对全部 $p,q,b$ 的估计，没有将固定参数的 Taylor 余项用于移动的极大点，也没有假设 $q$ 远离零。

**推论 4.3（全部中间噪声的直接相位包围）。** 对 $0<\delta<1$，定义

$$
H_\delta(y)=
\begin{cases}
y,&|y|\le\delta,\\
y/(1-\delta^2+|y|^2),&|y|>\delta.
\end{cases}
$$

若 $|x|\le1,|y-x|\le\delta$，整个 $[0,x]$ 被以 $H_\delta(y)$ 为中心、半径 $g(\delta)$ 的球包围。因此 $\mathcal U$ 的相位 1、2 单独可达误差 $g(\delta)$；本结论没有同时解决相位 0。

证明。第一分支两个端点到 $y$ 的距离均不超过 $\delta\le g(\delta)$。第二分支令 $\lambda=(1-\delta^2+r^2)^{-1}\in(0,1)$，则

$$
|x-\lambda y|^2
=(1-\lambda)|x|^2+\lambda|x-y|^2
-\lambda(1-\lambda)|y|^2
\le\lambda^2r^2.
$$

零端点距离也是 $\lambda r$。当 $\delta\le1/\sqrt2$，引理 4.1 的平方关系给 $\lambda r\le f_\delta$，不需它的小噪声限制。当 $\delta\ge1/\sqrt2,r>\delta$，

$$
\delta r^2-r+\delta(1-\delta^2)
=(r-\delta)(\delta r+\delta^2-1)\ge0,
$$

故 $\lambda r\le\delta$。再用线段凸性。

## 5. 对全部未来有效的单一上界构造

**引理 5.1（零、错号和极小锚的稳健误差）。** 若 $\mathsf s\in\mathcal U$、$|y_i-x_i|\le\delta$、$0<\delta\le1$，置

$$
\widehat w=y_2\times y_1,\qquad
Z(y)=\operatorname{sgn}(y_0\cdot\widehat w)\widehat w.
$$

则 $|Z(y)-x_3|\le9\sqrt\delta$。

证明。双线性给 $|\widehat w-w|\le(2+\delta)\delta\le3\delta$。若 $w=0$ 或真实非零符号与报告符号相同，误差至多此量。若非零尾的报告符号错误或为零，则两个三重积异号或报告为零，由引理 3.3，

$$
\begin{aligned}
q_2^2&\le|x_0\cdot w|
\le|x_0\cdot w-y_0\cdot\widehat w|\\
&\le\delta|w|+(q_0+\delta)|\widehat w-w|
\le(3+3\delta+\delta^2)\delta\le7\delta.
\end{aligned}
$$

故 $|w|=q_1q_2\le\sqrt{7\delta}$，即

$$
|Z-x_3|\le3\delta+2\sqrt{7\delta}\le9\sqrt\delta.
$$

以上未要求报告正交或误差独立；真实三重积可以任意小。此为 PCR 第 51 节稳健锚界的单位实例。

**定理 5.2（单位读数类的显式上界）。** 对 $0<\delta\le1/4096$，定义全部实报告上的集合函数

$$
D_\delta(y,j)=
\begin{cases}
C_\delta(y_1),&j\equiv1\pmod3,\\
C_\delta(y_2),&j\equiv2\pmod3,\\
C_\delta(y_0),&j\equiv0\pmod3,\ b_j\ge B_\delta,\\
|y_1|^{a_j-1}|y_2|^{b_j-1}Z(y),
&j\equiv0\pmod3,\ b_j<B_\delta.
\end{cases}
$$

使用 $\operatorname{sgn}(0)=0,0^0=1$。则对每个 $\mathsf s\in\mathcal U$、每个兼容的完整报告和每个 $j\ge3$，

$$
|D_\delta(y,j)-x_j(\mathsf s)|\le U_\delta.
$$

证明。分母在全部报告上严格正，幂指数非负，所以定义在空纤维也有意义，不需要来源搜索或优化器。相位 1、2 的目标属于对应实际线段，引理 4.1 给误差 $f_\delta$。相位 0 且 $b_j\ge B_\delta$ 时，零目标由中心范数界处理；非零目标用推论 3.4 的 $q\le P^{b_j}$，在引理 4.2 中取 $x=x_0,y=y_0,p=P$，得到误差不超过 $U_\delta$。

只剩相位 0 且 $b_j<B_\delta$。真标量系数和报告标量系数分别记 $c_x,c_y$，次数 $n=a_j+b_j-2<2B_\delta$。每个真范数因子在 $[0,1]$，报告范数因子在 $[0,1+\delta]$，相应因子之差至多 $\delta$。逐因子替换给

$$
|c_y-c_x|\le n(1+\delta)^{n-1}\delta,\qquad
c_y\le(1+\delta)^n,
$$

次数零的差按零处理。$|x_3|\le1$ 和引理 5.1 给

$$
|c_yZ-c_xx_3|
\le(1+\delta)^n(9\sqrt\delta+n\delta).
$$

现在 $n\delta\le2B_\delta\delta\le1/32$，且

$$
(1+\delta)^n\le e^{1/32}<2,
\qquad
|c_yZ-c_xx_3|
\le18\sqrt\delta+4B_\delta\delta
\le\frac{18}{64}+\frac1{16}=\frac{11}{32}<\frac12.
$$

$e^{1/32}<2$ 也可由级数 $e^v\le1/(1-v)$、$0\le v<1$ 得到。故该分支的误差小于 $f_\delta$。所有分支使用同一个 $D_\delta$，覆盖每个未来指数和全部源大小。阈值只改变求值规则，没有截断所要求的未来。对源、报告和 $j$ 取上确界，再对集合函数取下确界，得到 $R_\delta(\mathcal U)\le U_\delta$。证明没有使用 $L,d_0$ 或收缩裕量。

**推论 5.3（统一三次余项）。** 在 $0<\delta\le1/4096$ 上，

$$
0\le U_\delta-f_\delta\le385\delta^3,
\qquad
f_\delta=\frac12+\frac{\delta^2}{4}+O(\delta^4).
$$

证明。令 $t=1/(64\delta)\ge64$、$B=\lfloor t\rfloor$。有 $B-1\ge t-2\ge t/2$，有理化平方根，利用 $2f_\delta\ge1$，得到

$$
U_\delta-f_\delta
\le\frac{3\delta^2}{B-1}+2^{-B}
\le384\delta^3+2^{-B}.
$$

对全部整数 $B\ge64$，有 $2^B>64^3(B+1)^3$。起点成立，因为 $65<128$ 使右边小于 $2^{39}<2^{64}$；从 $B$ 到 $B+1$，左边乘 2，右边乘 $((B+2)/(B+1))^3\le(66/65)^3<(5/4)^3<2$，故归纳成立。又 $\delta>1/[64(B+1)]$，所以 $2^{-B}<\delta^3$，证明显式常数。

令 $v=\delta^2$。函数 $(1-v)^{-1/2}$ 在 $0\le v\le1/16$ 的二阶导数为 $(3/4)(1-v)^{-5/2}<1$，因为 $(3/4)(16/15)^3<1$。Taylor 定理因此给

$$
\frac12+\frac{\delta^2}{4}\le f_\delta
\le\frac12+\frac{\delta^2}{4}+\delta^4.
$$

加上 $385\delta^3$ 并用 $\delta^4\le\delta^3$ 即得定理 2.4 的最后一个上界。这些是普遍整数不等式和普通分析证明，不依赖有限枚举。

## 6. 两个平台内的实际共同报告下界

**引理 6.1（分别合法的近单位严格收缩族）。** 在两个完整平台的每一个内，都有一族实际源，三读趋向 $\mathsf U=(e_1,e_2,-e_3)$；每个固定相对时刻的向量趋向相应单位三循环 $\mathsf U_j$，但每个固定成员的未来趋零。第二平台的族在 $d_0>1$ 时也成立。

证明。第一平台取树 $\alpha$ 和 $p_\lambda=(\lambda e_1,\lambda e_2)$，$\lambda<1$ 趋于 1，并要求 $\lambda^4\ge d_0$。叶界、行列式界及 $q_0,q_1,q_2\le1\le H$ 同时成立。规范递推给 $q_j=\lambda^{F_{j+1}}$，以及方向 $e_1,e_2,-e_3$ 的三循环。固定时刻幅度趋 1，每个固定成员的全尾趋零。

第二平台选

$$
\max(1,\sqrt{d_0})<s_*<L^{1/\varphi^2},\qquad
a_*=s_*^{\varphi^2},\quad r_*=s_*^{-\varphi},\quad
p_*=(a_*e_1,r_*e_2),\quad C_* =\log a_*>0.
$$

区间非空恰由本平台参数保证。两叶长严格小于 $L$，叶积 $`a_*r_*=s_*`$，$`\Delta_*=s_*^2>d_0`$。规范字面树 $T_k=\rho^k\alpha$ 有 $T_0=\alpha,T_1=\beta,T_{k+2}=\langle T_{k+1},T_k\rangle$，故叶数为 $F_{k+1}$。两个初始对数 $`C_*,-C_*/\varphi`$ 和同一递推给

$$
\log|E_{p_*}(T_k)|=C_*\psi^k,\qquad \psi=-1/\varphi.
$$

只取正的 12 倍数 $k$，令

$$
\tau_k=\frac{2(1+C_*)\varphi^{-k}}{F_{k+1}},\qquad
\mathsf s_k=(T_k,e^{-\tau_k}p_*).
$$

此执行的制备固定。因双线性按真实叶数齐次，每个相对时刻 $h\ge0$ 有准确式

$$
\log q_h(\mathsf s_k)
=C_*\psi^{k+h}-\tau_kF_{k+h+1}.
$$

$h=0,1,2$ 时正项不超过 $`C_*\varphi^{-k}`$，减项至少 $`2(1+C_*)\varphi^{-k}`$，所以三读均严格小于 1。缩小叶不破坏叶界；$\tau_k\to0$ 使全部足够晚成员仍有 $`s_*^2e^{-4\tau_k}\ge d_0`$。固定 $h$ 时，$F_{k+h+1}/F_{k+1}$ 有界且趋于 $\varphi^h$，两个对数项都趋零。$k\equiv0\pmod3$ 保持同一相位。反之固定 $k$ 后随 $h\to\infty$，负 Fibonacci 项趋于负无穷而第一项趋零，所以该成员严格收缩。每个成员是一棵有限原树与一个合法固定制备，全部三读与整个未来共同实现。此复用的是 PCR 定理 27.2 和第 55 节的一族，不将其单位极限插入源类。

**引理 6.2（三实际世界的半径下界）。** 对每个 $0<\delta<1$，在两个平台的每一个内都有 $R_\delta\ge g(\delta)$。

证明。先选 $0<\theta<\pi/2$、$\sin\theta<\delta$。令 $Q_\pm$ 为绕 $e_3$ 的正向 $\pm\theta$ 旋转，共同报告取

$$
y_\theta=(\cos\theta\,e_1,\ \cos\theta\,e_2,\ -e_3).
$$

正向旋转满足 $Q(v\times w)=(Qv)\times(Qw)$；由定向体积恒等式或正交基叉积表直接证明，再作树归纳即给所有时刻同时旋转。将引理 6.1 每个成员的两个叶同时旋转，保留字面树，所有叶、Gram、行列式和读界均保留。两个旋转单位记录到上述报告的三块距离为 $\sin\theta,\sin\theta,0$；未旋转的单位记录距离为 $1-\cos\theta,1-\cos\theta,0$，而 $1-\cos\theta\le\sin\theta<\delta$。因此所有足够晚的旋转实际成员，以及一个固定足够晚的未旋转收缩成员 $\mathsf s_0$，都在同一个 $\mathcal A_\delta(y_\theta)$ 中。

给定任意 $\eta>0$，先保持 $\mathsf s_0$ 固定，选一个有限 $j\ge3,j\equiv0\pmod3$，使 $|x_j(\mathsf s_0)|<\eta$。再保持这个 $j$ 固定，选两族足够晚的实际旋转成员，使它们的未来分别到

$$
u_+=(\cos\theta,\sin\theta,0),\qquad
u_-=(\cos\theta,-\sin\theta,0)
$$

小于 $\eta$，三读仍兼容同一报告。于此单个有限查询，任意 $D(y_\theta,j)$ 对这三个实际源的最大误差，至少为 $\{0,u_+,u_-\}$ 的最小包围球半径减 $\eta$。这是在取上确界之前已选出的三个真实有限世界，不是边缘读数拼接，也不是把极限源当作合法成员。

计算该半径。将中心正交投影到 $e_1,e_2$ 平面，再与关于 $e_1$ 轴的反射取平均，凸性不增最大距离；负的第一坐标也不能改善距离。因此中心可取 $te_1,t\ge0$，目标为

$$
\max\{t,\sqrt{1+t^2-2t\cos\theta}\}.
$$

若 $\theta\le\pi/4$，两项在 $t=1/(2\cos\theta)\le\cos\theta$ 相等。低于此点，第二项不小于该值；高于此点，第一项不小于该值。所以半径为 $1/(2\cos\theta)$，且该中心达到。若 $\theta\ge\pi/4$，两单位端点的半距离给下界 $\sin\theta$；其中点 $\cos\theta\,e_1$ 到零的距离也不超过 $\sin\theta$，故达到这个下界。两式在 $\pi/4$ 相等。

让 $\eta\downarrow0$，再让 $\theta\uparrow\arcsin\delta$，连续性给 $g(\delta)$，包括 $\delta=1/\sqrt2$。所有兼容性先用严格裕量在真实成员上成立，之后才取角极限。未来查询和族索引的选择顺序不能交换。本报告通常不在实际记录像内：其 $q_2=1,q_0q_1=\cos^2\theta<1$ 违反引理 3.3，但它的实际带噪纤维非空；像外报告本来就在风险范围内。

**定理 6.3（端点、正噪声不连续与尖锐系数）。** 定理 2.4 在 $\mathcal P_1,\mathcal P_2,\mathcal U$ 上全部成立。

证明。前两类的下界由引理 6.2 分别证明，$\mathcal U$ 包含第一平台的实际族，故也继承该下界。上界由第 5 章统一给出；零输出在三个类上对任意噪声都有风险至多 1。若 $\delta\ge1$，共同零报告与所有单位有界三读兼容。于一个固定相位 0 查询，把引理 6.1 的足够晚成员与一个使该相位方向取反的正向旋转成员比较，两个真实未来距离趋于 2。共同输出的最大误差至少是其距离一半，因此风险至少 1，包括 $\delta=1$。

$R_0=0$ 已由引理 3.3 的准确式给出。小正噪声时 $g=f_\delta$；合并下界与推论 5.3，证明二次项和三次充分余项。特别地每个 $\delta>0$ 的风险严格大于 $1/2$，右极限为 $1/2$，而准确报告处的值为零。平方根的下一向量误差机制可以存在，但第 5 章使其有限头部误差低于 $1/2$；全未来风险超出平台的主项由近单位方向不确定性与同纤维内延迟衰减共同实现。

## 7. 原十制度、真实组成与达到阈值

本章是 PCR 定理 18.2–18.4、命题 19.1、定理 19.2、命题 19.3、第 24–28 节和第 53 节的精确复用与风险转换。除两平台的新噪声估计外，其余制度不作为新增结果。

**定理 7.1（完整分类）。** 保持 $L,H>0,0<d_0<L^4,D_{\rm crit}=L^{2/\varphi^2}$。全部行均有 $R_0=0$；正噪声制度为

| 行 | 完整主参数条件 | 同一全未来任务的风险 |
| --- | --- | --- |
| 1 | $L<1$，任意 $H>0$ | $R_\delta=\Theta(\delta)$，$\delta\downarrow0$ |
| 2 | $L=1,H<1$ | $R_\delta=\Theta(\delta)$，$\delta\downarrow0$ |
| 3 | $L=1,H\ge1$ | 第一平台，定理 2.4 |
| 4 | $L>1,d_0<D_{\rm crit},H<1$ | $R_\delta=\Theta(\delta)$，$\delta\downarrow0$ |
| 5 | $L>1,d_0<D_{\rm crit},H=1$ | 第二平台，定理 2.4 |
| 6 | $L>1,d_0<D_{\rm crit},H>1$ | 每个 $\delta>0$ 有 $R_\delta=+\infty$ |
| 7 | $L>1,d_0=D_{\rm crit},H\le1$ | 每个 $\delta\ge0$ 有 $R_\delta=0$ |
| 8 | $L>1,d_0=D_{\rm crit},H>1$ | 每个 $\delta>0$ 有 $R_\delta=+\infty$ |
| 9 | $`L>1,d_0>D_{\rm crit},H<H_*`$ | 每个 $\delta\ge0$ 有 $R_\delta=0$ |
| 10 | $`L>1,d_0>D_{\rm crit},H\ge H_*`$ | 每个 $\delta>0$ 有 $R_\delta=+\infty$，包括达到的 $`H=H_*`$ |

$\Theta$ 的常数允许依固定主参数而变，线性行恰是 1、2、4。以下三条证明给出原分类如何进入本风险定义，不将实际对模量与风险混同。

**命题 7.2（实际支撑和同一个 $`H_*`$）。** 置 $s_0=\sqrt{d_0},z=\log s_0,\ell=\log L,G=\varphi^2z-\ell$。允许的非零标签组成恰为

$$
\mathcal S_{\rm comp}=\{(1,0),(0,1)\}
\cup\{(m,n):m,n\ge1,\text{不同时为偶数}\}.
$$

令 $I=[z-\ell,\ell]$，并定义

$$
f_0(v)=mz+(n-m)v,\quad f_1(v)=nz+mv,\quad
f_2(v)=(m+n)z+nv=f_0(v)+f_1(v).
$$

当 $G>0$ 时，原非零尾阈值可写成有限达到的最小值

$$
\log H_*=
\min_{\substack{(m,n)\in\mathcal S_{\rm comp}\\
m+\varphi n\le\varphi^2z/G}}
\ \min_{v\in I}\max\{f_0(v),f_1(v),f_2(v)\},
\qquad 1<H_*\le\sqrt{d_0}.
$$

有真实树和合法制备在 $`H=H_*`$ 达到非零尾。$G=0$ 的非零三读高度下确界是 1 而不达到；$G<0$ 时是 0 而不达到。

证明。将单位轴 $f_1,f_2,f_3$ 分别赋 $\mathbb F_2^2$ 的非零度 $(1,0),(0,1),(1,1)$。非零叉积的度相加，故非零标签的总度不能为 $(0,0)$，排除双偶组成。单标签多叶树含同叶 cherry，值零。反向从 $\langle\beta,\alpha\rangle$ 的奇／奇组成开始，两次左接同一个叶使相应叶数增加 2，两个叉积均非零；它们生成全部奇／奇组成。再左接一个 $\alpha$ 或 $\beta$，分别给偶／奇或奇／偶。两个单叶原树补齐其余支撑。构造全为实际有限有序树。

任意非零源可将 $a$ 去掉沿 $b$ 的分量，保持 $b,K$ 和全部尾，降低叶范数；其初值范数变为 $q_2/q_1\le q_0$，由引理 3.3 或正交齐次性给出。再同时正比例缩小两叶，使 $\Delta=d_0$，每个读数按自己的正叶数缩小，仍合法。于是非零三读可行性等价于某个支撑组成和一个正交制备

$$
p=((s_0/r)e_1,re_2),\qquad v=\log r\in I
$$

同时满足三条 $f_i(v)\le\log H$。其反向用上述组成的实际树直接实现三条幅度，因此不是独立三幅度的松弛。

叶 $\alpha$ 在两等长叶 $\sqrt{s_0}<L$ 处的三读高度是 $s_0$，给竞争上界 $z$。且

$$
f_1+\varphi f_2=(m+\varphi n)(v+\varphi z)
\ge(m+\varphi n)G.
$$

若候选能持平或改善叶上界，三个 $f_i\le z$，故 $(m+\varphi n)G\le\varphi^2z$。这给完整的有限截止；对闭区间上连续三线最大值取最小，再取有限最小均达到，实际树与正交制备实现之。$G>0$ 使每个候选的最大值严格正，故 $`1<H_*\le s_0`$。PCR 的较宽截止在保留完整三线测试后给同一个阈值。

允许的 $(r,s)$ 恰满足 $s\ge s_0,s\le Lr,r\le L$，由 $s\le|a||b|$ 得必要性，由正交叶 $((s/r)e_1,re_2)$ 得充分性。因此 $\Gamma=\log r+\varphi\log s$ 的最小值为 $G$。当 $G<0$，选达到该负值的正交制备，规范树 $T_k$ 的三读随着 $k$ 趋零，给非零高度下确界 0，正幅度使零不达到。当 $G=0$，临界端点规范树的三读趋 1；若高度不超过 1，$\Gamma\ge0$ 和两尾对数非正迫使 $q_1=q_2=1$，再由组成矩阵可逆得 $s=1$，与 $s_0=L^{1/\varphi^2}>1$ 矛盾。因此下确界 1 不达到。

**命题 7.3（线性行的风险转换）。** 在行 1、2、4，令

$$
M=\min(L,H)<1,\quad c=\sqrt{d_0}/L^2,\quad
K(M)=2M+\frac{2M(2M+1)}c,\quad
C_\Omega=\max(1,K(M))+\frac{M}{(1-M)^2}.
$$

则 $R_\delta\le\min\{M^2,2C_\Omega\delta\}$。固定一个合法非零源后，存在 $b>0,\delta_0>0$ 使 $R_\delta\ge b\delta$，$0<\delta\le\delta_0$。

证明。写 $\Omega(\epsilon)$ 为实际源对的全未来距离模量，三读距离为最大块范数。共同中点报告及三角不等式给

$$
\frac{\Omega(2\delta)}2\le R_\delta\le\Omega(2\delta).
$$

右界对每个非空纤维任取一兼容实际源并输出它的未来，任意两兼容源的三读距离至多 $2\delta$；这是集合函数选择，不供应取得算法。

三读范数均不超过 $M$：$L\le1$ 时树归纳给 $q_i\le L$，其余情况 $H<1$ 直接给出。由引理 3.3 的五投影比值，在主域有 $|x_0\cdot w|\ge cq_0|w|$。实际对的 $|w-w'|\le2M\epsilon$。同号或零尾直接受此界。异号时两个归一化三重积的绝对值至少 $c$、符号相反，其差至少 $2c$。归一化差界 $|x/|x|-y/|y||\le2|x-y|/|x|$ 及逐因子相减给

$$
2c\le2\epsilon(q_0^{-1}+q_1^{-1}+q_2^{-1})
\le\frac{2(2M+1)\epsilon}{q_2}.
$$

末步用 $q_2\le q_0q_1$。于是 $q_2\le(2M+1)\epsilon/c$，第三锚差至多 $2M\epsilon+2Mq_2\le K(M)\epsilon$。在 $[0,M]^2$ 上，总次数 $n$ 的单项式差至多 $nM^{n-1}\epsilon$，大小至多 $M^n$。由推论 3.4，每个未来差至多

$$
(\max(1,K(M))M^n+nM^n)\epsilon
\le C_\Omega\epsilon,
$$

利用 $\sum_{n\ge1}nM^n=M/(1-M)^2$ 同时控制全部次数和全部未来。未来范数还均不超过 $M^2$，零输出给风险上界 $M^2$。

这些行均有 $G<0$：$L<1$ 时 $z<2\ell<0$ 给 $G<(2\varphi^2-1)\ell<0$；$L=1$ 时 $z<0$；行 4 则由 $d_0<D_{\rm crit}$ 直接给出。命题 7.2 的规范源给一个合法非零源。固定之，令 $M_0=\max(q_0,q_1,q_2)>0$。绕垂直于 $x_3$ 的轴正向旋转两叶，取 $2\sin(\theta/2)=2\delta/M_0$，$0<\delta\le M_0$。读距至多 $2\delta$，第三未来距离恰 $2(q_3/M_0)\delta$。同一中点报告强迫风险至少 $(q_3/M_0)\delta$，全部源条件包括等号由旋转保留。这完成三行的线性阶证明。

**命题 7.4（零行和增长行，包括阈值等号）。** 行 7、9 的全部未来为零；行 6、8、10 每个正噪声的风险无穷。

证明。行 7 由命题 7.2 的临界高度不达到排除全部非零尾；行 9 由达到阈值的必要性排除它们。其余零标签尾未来零，所以零输出对全部报告准确；这不要求 $x_0=0$ 或源类为空。

行 6 的 $G<0$ 选 $\max(1,s_0)<s<L^{1/\varphi^2}$；行 8 取 $s=s_0=L^{1/\varphi^2}$。临界正交制备 $(s^{\varphi^2}e_1,s^{-\varphi}e_2)$ 的规范三读趋 1，所以某个固定有限 $T_k$ 的三读严格低于 $H>1$。将第二叶长乘 $e^v$、第一叶长乘 $e^{-v}$，$v>0$ 足够小；叶积和行列式不变，第一叶不增加，第二叶有严格叶界余量，有限三个多项式值的严格读界由连续性保持。$\Gamma$ 变为 $v>0$，所以得到一条合法增长源。行 10 直接用真实 $`H_*`$ 达到者，其 $\Gamma\ge G>0$，包括 $`H=H_*`$。

固定上述任意增长源，绕 $x_1$ 轴小幅正向旋转两叶，保留字面树和全部源限制。角度足够小令三读距离不超过 $2\delta$；相位 2 垂直于该轴，未来两源距离为 $2\sin(\theta/2)q_j$，沿该相位趋于无穷。共同中点报告与三角不等式强迫任一估计器风险无穷。准确数据仍由符号式给 $R_0=0$，无需未来有界。

**命题 7.5（保留实际对模量的准确平台）。** 在两个固定参数平台上，$\Omega(0)=0$、$\Omega(\epsilon)\le2$；对于 $0<\epsilon\le(2+6/c)^{-1}$，$\Omega(\epsilon)=1$；对于 $\epsilon\ge2$，$\Omega(\epsilon)=2$。这里 $c=\sqrt{d_0}/L^2$，$\Omega$ 是源对模量，不能将其等式改写成风险 $R_\delta=1/2$。

证明。命题 7.3 中的对应锚误差论证在三读单位有界时仍给第三锚差至多 $K(1)\epsilon=(2+6/c)\epsilon$，另外两锚差至多 $\epsilon$。对 $|v|,|v'|\le1$ 及 $t,t'\in[0,1]$，矩形上的凸性给 $|tv-t'v'|\le\max(0,|v|,|v'|,|v-v'|)$。同相位应用推论 3.4，即得规定小区间的上界 1，全局幅度界给 2。给定 $\epsilon,\eta>0$，引理 6.1 先固定一成员，使三读到单位记录的距离小于 $\epsilon/2$，再取一个相位 0 有限查询使其未来范数小于 $\eta$，最后选另一晚成员，三读仍到单位记录小于 $\epsilon/2$，该固定查询的幅度大于 $1-\eta$。同相位距离至少 $1-2\eta$，得每个正 $\epsilon$ 的下界 1。反向旋转近单位成员给读距至多 2、某固定相位未来距离趋 2，故 $\epsilon\ge2$ 时下界 2。准确三读给 $\Omega(0)=0$。这是 PCR 定理 27.1–27.4 的原端点，不新增模量中间曲线。

## 8. 保留不同噪声范围的可用上界

**命题 8.1（已发表半锚界的范围）。** 在 $\mathcal U$ 上，$0<\delta\le1$ 有

$$
R_\delta\le\min\{1,\tfrac12+\tfrac92\sqrt\delta\}.
$$

在每个固定参数平台上，令 $c=\sqrt{d_0}/L^2$，还可取

$$
R_\delta\le\min\{1,\tfrac12+8\delta/c\}.
$$

证明。PCR 第 54 节的普通半锚为 $(x_1/2,x_2/2,x_3/2)$；推论 3.4 使对应线段的误差至多 $1/2$。报告半锚 $(y_1/2,y_2/2,Z/2)$ 的前两中心误差至多 $\delta/2$，第三由引理 5.1 至多 $(9/2)\sqrt\delta$。

固定主域的第三锚可用 PCR 定理 51.2 的 $16\delta/c$ 界，其单位实例也如下直接得到。错号分支若 $q_0<2\delta$，由 $|w|\le q_0$，总误差至多 $4\delta+(2+\delta)\delta$。若 $q_0\ge2\delta>0$，投影界给

$$
cq_0|w|\le\delta|w|+(q_0+\delta)(2+\delta)\delta
\le q_0\delta+\tfrac32q_0(2+\delta)\delta.
$$

故 $2|w|+(2+\delta)\delta\le4(\delta+(2+\delta)\delta)/c\le16\delta/c$。正确符号和零尾的叉积界更小，$\delta=0$ 由准确式承担。半锚得 $8\delta/c$，零输出给上界 1。这些界对 $\mathcal U$ 和固定主域使用不同前提，不能混用。

**命题 8.2（更宽小噪声区间的二次包络）。** 在全部 $\mathcal U$ 上，$0<\delta\le1/32$ 有

$$
R_\delta\le P_\delta:=\frac1{2\sqrt{1-2\delta^2}}.
$$

证明。置 $\kappa=\sqrt{1-2\delta^2}$、$v_i=\min(1,|y_i|+\delta)$，$i=1,2$。若 $v_1v_2\le1/2$，所有相位输出零；真实 $q_i\le v_i$，所以未来范数至多 $1/2$。否则在全部分母和三重积非零时置

$$
n_1=y_1/|y_1|,\quad n_2=y_2/|y_2|,\quad
n_0=\operatorname{sgn}(y_0\cdot(y_2\times y_1))
\frac{y_2\times y_1}{|y_2\times y_1|},
$$

按查询相位输出 $P_\delta n_r$；其余报告定义为零，使规则总定义。

对兼容源的高分支，$q_i>1/2-2\delta\ge7/16$。三重积扰动至多 $(3+3\delta+\delta^2)\delta\le3169/32768$，严格小于真实绝对值下界 $q_2^2>49/256$。故报告符号正确且非零。叉积扰动至多 $(2+\delta)\delta\le65/1024<q_1q_2$，所以报告叉积非零且与真实叉积正内积；高分支的回退情形不发生于非空兼容纤维。

令 $u_1,u_2,u_0$ 为真实正交相位方向，$Q=q_1q_2$。报告法向 $n_0$ 垂直于两个报告，故 $|n_0\cdot u_i|\le\delta/q_i$，$i=1,2$，且 $n_0\cdot u_0>0$。因此

$$
n_0\cdot u_0\ge\sqrt{1-\delta^2(q_1^{-2}+q_2^{-2})}.
$$

报告 $y_i$ 到真实 $x_i$ 的垂直投影误差至多 $\delta$，正内积由 $q_i>\delta$ 得到，所以另外两相位的方向余弦至少 $\sqrt{1-\delta^2/q_i^2}$，也不小于上述共同下界。无需报告正交。

用 $q_1^2+q_2^2\le1+Q^2$，有

$$
\begin{aligned}
\delta^2(q_1^{-2}+q_2^{-2}-2Q^2)
&\le(1-Q^2)\delta^2(Q^{-2}+2)\\
&\le1-Q^2.
\end{aligned}
$$

末步由 $Q>(7/16)^2$ 及 $\delta^2\le1/1024$ 给 $\delta^2(Q^{-2}+2)\le((16/7)^4+2)/1024<1$。故每个相位的报告方向余弦至少 $Q\kappa$。真实未来为 $tu_r,0\le t\le Q$，平方误差

$$
|P_\delta n_r-tu_r|^2
=P_\delta^2+t^2-2P_\delta t(n_r\cdot u_r)
$$

在 $t$ 中凸；在两个端点 $0,Q$ 都至多 $P_\delta^2$，因为 $2P_\delta\kappa=1$。这同时覆盖全部未来，证明包络。此较大有效区间没有解决二次系数：单独与下界合用，仅给 $1/4$ 至 $1/2$ 的系数夹界。

**推论 8.3（其它充分包络及其限定）。** 以下上界均在 $\mathcal U$、从而两个完整平台上有效，可以只在各自区间取最小值。

| 包络 | 有效噪声区间 | 能承担的结论 |
| --- | --- | --- |
| $G_\delta=1/(2\sqrt{1-\eta_\delta^2})$，$\eta_\delta=(\sqrt2\delta+\delta^2)/(1-2\delta)$ | $0<\delta\le1/64$ | 二次阶，单独的系数上界 $1/2$ |
| $\frac12+\frac{\delta^2}{4}+4\delta^{5/2}+\delta^3$ | $0<\delta\le10^{-6}$ | 系数 $1/4$，充分 $O(\delta^{5/2})$ 余项 |
| $\max\{f_\delta+\delta^3,\sqrt{f_\delta^2+2e_\delta\delta^2/(1-2e_\delta)}\}$，$e_\delta=32\delta\log(1/\delta)$ | $0<\delta\le2^{-20}$ | 系数 $1/4$，充分 $O(\delta^3\log(1/\delta))$ 余项 |

证明。第一行 $\eta_\delta\ge\sqrt2\delta$，且在所述区间 $\eta_\delta<1$，所以 $G_\delta\ge P_\delta$，由命题 8.2 得到。第二行由定理 2.4 的 $386\delta^3$ 余项推出，因为 $385\sqrt\delta\le385/1000<4$。

第三行在该区间有 $e_\delta\le640/2^{20}<1/64$：$\delta\log(1/\delta)$ 在 $\delta\le2^{-20}$ 上随 $\delta$ 增加，且 $\log2<1$。$\sqrt{f_\delta^2+2e_\delta\delta^2/(1-2e_\delta)}$ 和 $f_\delta$ 都小于 1，故有理化后的增量至少 $e_\delta\delta^2=32\log(1/\delta)\delta^3$。不等式 $\log2\ge2/3$ 可由 $\log x\ge2(x-1)/(x+1)$、$x\ge1$ 的导数检验给出，因此 $32\log(1/\delta)\ge1280/3>385$。第三行便覆盖 $f_\delta+385\delta^3$。这保留各包络的实际区间，不证明其余项必要。定理 2.4 还蕴含较弱的 $o(\delta^2)$ 余项结论；它本身不能把一个只对固定辅助参数成立的余项改成对移动参数统一成立。

因此新三次余项与较大区间的二次包络是不同坐标的改进，没有统一 Pareto 支配的声明。对于未覆盖的噪声区间，保留 $g(\delta)\le R_\delta\le1$ 和命题 8.1；不能从这些包络或风险单调性推断完整曲线。

## 9. 量化、取得、有限记录与自主记忆的边界

**约定 9.1（本风险的资源接口）。** 原取得仅有三次宽度三的向量回复、两次破坏性 $\rho$ 和 Stop。没有后续源调用、精度细化名字、归档、复位、校准、嫁接、重制备、树码、叶数、行列式／收缩／中性证书或源相关建议。第 5、8 章的范数、符号、除法、幂、比较和阈值是集合函数的数学定义，未授予准确实数算术或相等／符号 oracle。噪声参数的数学给定也不是任意实参数的有限有效表示。

若要求有限实现，需要另给并证明报告表示、传感精度与舍入合同、公共常数和安装数据的表示、每个源相关程序／元数据／选择信息的完整收费、解析和算术的终止、比较精度、中间整数及工作空间、输出精度和缓冲区，以及查询 $j$ 的全部字符、相位、计数器与时间开销。九个实坐标不等于九个有限字。外供 $j$ 不是内部时钟或自主的下一输出服务。此处没有给这些费用或最优保留记忆律。

**命题 9.2（特定最近真格点仪器的既有结论）。** 复用 PCR 定理 56.2。若仪器对真实准确坐标作最近步长 $h=2^{-b}$ 的格点舍入，$b\ge0$ 是整数；记录只含九个舍入坐标、公共 $b$ 与同一取得菜单／Stop 元数据，没有源相关附带信息，则两个平台上任何全未来误差 $E=1/2+\tau$ 的保证都必须有

$$
\tau\ge h^2/384.
$$

证明。取 $\theta=h/8\le1/8$。单位记录 $\mathsf U$ 在格点上，两个旋转单位记录各坐标距它至多 $h/8$。引理 6.1 取足够晚实际成员，使附加坐标偏差严格小于 $h/8$；再固定同样足够晚的未旋转收缩成员。所有九个坐标都在 $\mathsf U$ 的同一个格点单元内部，距其中心小于 $h/4<h/2$，任何平局规则均无关。相同有限报告按第 6 章的固定成员、固定查询、再选晚成员顺序强迫半径 $1/(2\cos\theta)$。交错 Taylor 界在此范围给 $\cos\theta\le1-\theta^2/3$，于是

$$
\frac1{2\cos\theta}-\frac12
=\frac{1-\cos\theta}{2\cos\theta}
\ge\theta^2/6=h^2/384.
$$

这是仪器及记录合同限定的普通证明。第 6 章的缩短实报告不是自动的共同量化单元，因此尖锐实误差球下界不产生新的最优位数系数；先有限近似再舍入也需要另行校核。

**既有表示结论的准确范围。** PCR 定理 55.1 证明：两个平台上，即使源感知编码器知道整个来源，有统一有限位上限的完整字也不能统一达到 $E\le1/2$；源相关程序和建议属于完整字。其有限字母表证明先在每个方向的无限近单位族中选重复字，再对不同方向作鸽巢与半径等号分析，包含端点 $E=1/2$。它不排除可数无限字母表、每源有限但没有统一字长上限的编码。PCR 第 54 节的有限报告构造在分别付费的精度及输出合同下给每个 $E>1/2$ 的充分解；这不是从本卷的集合函数自动得到的有限实现。

PCR 定理 57.1 和 65.2 的全实增长行有限字障碍使用不可数个两两全未来距离无穷的实际旋转源，含 $`H=H_*`$。其准确有限有理回复例外、持续名字服务以及逐查询工作费用各有自己的合同，不能改称原三读免费扩展。本卷不使用任何待定 Memory76、Memory77 或 Memory78 结论。

**反例 9.3（不同任务的平方根机制）。** PCR 定理 21.3、第 52 节的实际下一向量平方根对允许叶范数发散且 $\Delta\to0$。它们证明无正行列式下界的下一向量任务可有 $\Theta(\sqrt\delta)$ 风险，但不能提供固定 $L,d_0$ 平台的全未来下界。环境三元组 $(\pm\epsilon e_3,e_1,e_2)$ 在 $\epsilon<1$ 时违反 $q_2\le q_0q_1$，根本不是本原来源的合法读数。两种反例均不能代替第 6 章的同源共同报告构造。

## 10. 精确复用、文献关系与未解问题

**来源边界 10.1。** 下表中的仓内理论使用版本 `531252e1cabf27b1045e16993d12ffae880c1e46`；PCR 的完整文本 SHA256 为 `34965bcd940caa8e5f73cabae09061c8cbb8727661cd69a42ada3fdc08e5e2f0`。源库声明的比较版本为 `cda923132d98ab62379ad5bd2434c747e44c6a74`，只核对其陈述、定义和适用范围，没有当前编译或精确形式实例化的主张。

| 来源与精确编号 | 复用内容与边界 |
| --- | --- |
| [PCR](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) 定义 1.1–1.2、定理 3.1、引理 4.2、定理 4.3、5.1 | 原语法、单次制备、运输、五符号表、带符号尾及准确三读；本卷第 2–3 章完整写出所需关系 |
| PCR 引理 16.2、推论 16.3、第 50–51 节 | 实际投影、幅度限制、三锚和稳健符号界；投影幂包围的新几何由本卷第 4–5 章承担 |
| PCR 定理 18.2–18.4、命题 19.1、定理 19.2、命题 19.3、第 24–28 节、第 53 节 | 真实组成、完整三线可行性、有限达到的 $`H_*`$、十制度及全未来模量；第 7 章给风险转换 |
| PCR 第 54–56 节、定理 65.2、结论范围 74.3 | 半锚、两个实际收缩族、正噪声三点纤维、最近真格点单元、有限字与表示边界；本卷缩短共同报告并证明尖锐系数，不导入待定记忆结果 |
| [《原子关系生成》](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 第 2–3 节 | 自由有序原树、字面规范递推和真实叶数 |
| [《递归全息边界几何》](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) 定理 7.2 | 单位轴、七标签和正向三循环；不迁移其其它维数或容量结论 |
| [《过程几何》](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 定理 44.2 | 非零组成实际见证；嫁接只构造比较源，不供应观察动作 |
| [《恢复几何》](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 定理 3.2 | 兼容纤维最小包围半径的视角；其估计器输出域须随任务指定，本卷中心在 $\mathbb R^3$ 中且不必实际可达，不直接迁移受限输出域的常数。该一般视角本身不计新结果，也不提供优化服务 |

源库 `RankOneInfiniteHorizonRisk` 的声明 `rank_one_infinite_horizon_risk` 是标量 $a^n$、$0<a<1$、有限窗口、正有界标量噪声下的全未来风险 $1/2$；其极限次序是相关类比，但方向与原树共同约束不同，本卷不直接实例化它。`FinitePowerExtrapolationRisk` 的 `finite_power_extrapolation_risk` 只处理指定有限视界；`ZeroSumBoxRecovery` 的 `zero_sum_box_recovery_sharp` 使用零和实平面、坐标最大范数以及必须输出合法平面的估计器。它们均不承担本卷的三向量乘积误差球和全未来 Euclidean 尖锐常数。

**文献表态 10.2。** 文献支持一般最优恢复背景，原来源的尖锐几何属于 `repo-derived`，不作全球原创性声明。

| 文献／结果 | 精确使用范围 |
| --- | --- |
| Foucart–Liao, *Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize, but what of the Parameter?*, [arXiv:2111.02601v1](https://arxiv.org/html/2111.02601v1)，第 1.1–1.3 节 | `literature-attested`：兼容集、局部／全局最坏风险与 Chebyshev 中心背景。其线性信息、Hilbert 近似管和合计二范数噪声没有被验证为原非线性树图及三个块误差球，不导入其优化器或精确公式 |
| Babenko–Parfinovych–Skorokhodov, *Optimal recovery of operator sequences*, [arXiv:2110.08543v1](https://arxiv.org/html/2110.08543v1)，第 2 节引理 1 | `literature-attested`：同一信息的三角不等式下界。对应对象是本卷实际源、兼容报告和全未来目标；普通共同报告论证已经直接给出。独立序列系数及对角算子类不替代原来源 |
| Foucart–Liao, *S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers*, [arXiv:2310.09677v1](https://arxiv.org/html/2310.09677v1)，第 1–2 节及定理 2.1 | `literature-attested`：特定 Hilbert 模型的精确性及实／复边界。正交投影、$`\Lambda\Lambda^*=I`$、共同核条件和合计 Euclidean 不确定性均未获本源桥梁；不导入 S-procedure 或 SDP 结论 |
| 本卷推论 3.4、引理 4.1–4.2、定理 5.2、引理 6.2 和定理 6.3 | `repo-derived`：实际投影幂的使用、统一中心几何、全未来显式三次余项、改进实际下曲线及系数 $1/4$；普通证明自足 |

恒等式、十制度、端点、一般风险／模量比较、原收缩族、半锚和有限字障碍是精确复用，不重复称为新增数学。实际新内容是把同源初读投影约束用于全部相位 0 未来，并与非共线三实际世界半径匹配，证明此前未定的二次系数及显式充分三次余项。读取形式源或文献只建立上述陈述对应，不构成当前 Lean 核验。

**开放问题 10.3（中间曲线与次主项）。** 对 $0<\delta<1$，完整 $R_\delta$、最优实际纤维中心及可能的其它转折点仍为 open。$g(\delta)$ 是下界，不是已证等式。$385\delta^3$ 是充分余项，未证明最优阶、非零三次系数或排除更强展开。第 8 章的包络只在自己的有效区间使用，不能插值成曲线。

**开放问题 10.4（有效实现与长期目标）。** 三个线性行的最优常数和有限噪声曲线、达到本卷渐近式的有限表示与舍入算法、实际共同量化单元的新精度律、取得与保留字长的最优关系、自主在线记忆、以及物理空间／时间／边界记忆互恢复均未由本卷解决。须分别补齐真实表示、供应、运算和资源桥梁；不以集合函数存在替代它们。所有本卷的普遍数学结论由普通结构归纳、直接不等式、合法有限源构造及指定顺序的极限承担，没有有限样本代替全称证明，也没有新增 Lean、构建或消化核验的声明。

## 追加锚（本行以下为增补区）
