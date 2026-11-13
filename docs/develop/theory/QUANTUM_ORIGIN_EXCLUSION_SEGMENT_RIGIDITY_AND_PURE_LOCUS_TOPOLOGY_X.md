# QUANTUM ORIGIN: EXCLUSION SEGMENT RIGIDITY AND PURE LOCUS TOPOLOGY X

本卷中的 X121、X122、X123 是本卷的局部章号。
引用校准卷的 123—130、排除几何卷 IX 的 118—120，或 THREE_COPY VII 的 121—122 时，均带卷名。
式号的 X 前缀只标识本卷，不改变被引用结论的归属。
各章的假设在其入口分别给出；后章引用前章的式子时，保留该式的全部前件。

## 121. 严格种子偏差的整球传播、反向亏量与联合轴截面

### 121.0 完整原域与正法向的固定含义

**定义 121.1（同一原锥及全部原读数）。**
设 $V\ne0$ 为有限维实空间，$C\subset V$ 为闭、尖、生成凸锥，
$u\in V^*$ 在 $C\setminus\{0\}$ 上严格正。
始终取整个原归一基、所有原纯点和整个原效应区间

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\\
C^*=\{h\in V^*:h\ge0\text{ 于全部 }C\},\qquad
\mathcal E=[0,u]_{C^*}.
\end{gathered}
\tag{X121.1}
$$

对每个 $p\in P$ 定义

$$
\begin{gathered}
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
\mathcal T_p(z)=\min_{f\in\mathcal F_p}f(z),\\
D_p=\{z\in K:\mathcal T_p(z)=0\},\\
\mathcal A_p=\{a\in\mathcal E:a(p)=1,\ a|_{D_p}=0\},\qquad
P_0=\{p\in P:\mathcal A_p\text{ 为单点}\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad S_p=\operatorname{span}N_p.
\end{gathered}
\tag{X121.2}
$$

若 $p\in P_0$，记 $\mathcal A_p=\{e_p\}$，$g_p=u-e_p$。
$\mathcal F_p$ 是全部确认效应；$\mathcal A_p$ 是其中在整个排除面上为零的效应。
定义 $D_p$ 时不能把 $\mathcal F_p$ 换成 $\mathcal A_p$。
原效应区间及确认切片紧，所以这里的最小值确实达到；
$z\in D_p$ 等价于存在某个原 $f\in\mathcal F_p$ 使 $f(z)=0$。
这个等价包括所有混合 $z\in K$。

记 $\mathrm{EB3}$ 为每个完整 $D_p$ 都有一个单射仿射闭单位三球图，
$\mathrm{Inj}$ 为 $p\mapsto D_p$ 在全部 $P$ 上单射。
原关系

$$
p\perp q
\quad\Longleftrightarrow\quad
\exists f\in\mathcal E:\ f(p)=1,\ f(q)=0
\tag{X121.3}
$$

由原补效应 $u-f$ 对称。
它是同一原数学对象上的关系；有限边路并不指定共同仪器或实际门字。

使用 [FINITE_PURE VII103.1—103.2、104.1](QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md)
及 [EXCLUSION IX120.1—120.2](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
的完整面接口：每个 $D_p$ 是完整暴露面，非空真面为纯单点或某个完整排除球；
不同完整球相交至多于一个原纯点。
在 Inj 下，任何 $a\in\mathcal A_p$ 的整个零面是 $D_p$，整个一值面是 $\{p\}$。
球图的整个球面恰是 $P\cap D_p$。
这些接口的证明归于上述来源；本卷只在下列推导中应用它们。

这里的 $N_p$ 是原双锥中的齐次正法向面。
它不是只在某颗球上非负的仿射函数锥，也不是全部满足 $h(p)=0$ 的有符号泛函。
所有非负、最大值和效应上界，除非明确写了限制集，均指整个原 $C$ 或整个原 $K$。

### 121.1 弱种子入口与相反方向

**定义 121.2（实际种子及严格偏差方向）。**
本章另设 EB3、Inj、$\dim V=9$，并给定实际原正交三角 $(p,q,r)$，至少一个顶点属于 $P_0$。
实际边传播使三个顶点都属于 $P_0$。
选择完整图

$$
D_p=c+B\overline{\mathbb B}^{,3},\qquad
q=c+Bv_0,\quad r=c-Bv_0,\quad \|v_0\|=1.
\tag{X121.4}
$$

令 $g=u-e_p$，取原线性读数 $H:V\to\mathbb R^3$，使

$$
H(c+Bw)=w,\qquad H(p)=0,\qquad H_i\in S_p.
\tag{X121.5}
$$

[EXCLUSION IX120.8、120.10—120.13](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
给出 $S_p\simeq\operatorname{Aff}(D_p)$、$\dim S_p=4$、$g\in\operatorname{ri}N_p$，以及原方向函数

$$
\rho_p(\ell)=\sup_{z\in K\setminus\{p\}}
\frac{-\ell\cdot H(z)}{g(z)}.
\tag{X121.6}
$$

$g$ 在 $K\setminus\{p\}$ 严格正，$\rho_p$ 有限且正齐次。
对 $h=\alpha g+\ell\cdot H\in S_p$，原全局正性恰为
$\alpha\ge\rho_p(\ell)$；只有先满足这个条件，才可用原最大值公式
$\max_Kh=\alpha+\|\ell\|$ 检查上效应界。

固定一个原纯邻点及其原对径

$$
s=c+Bv\in P\cap D_p,\quad \|v\|=1,\qquad
b=c-Bv.
\tag{X121.7}
$$

这里的 $b$ 是态标签，与 X122 中的达到宽度的效应 $b$ 无关。
令

$$
\begin{gathered}
R_+=\rho_p(v),\quad R_-=\rho_p(-v),\quad \tau=v\cdot v_0,\\
d_+=\delta_p(s)=\frac{R_+-1}{R_++1}>0,\qquad
d_-=\frac{R_--1}{R_-+1},\qquad
c_0=\frac{1+R_-}{1+R_+},\\
k_+=u-e_p-e_s=\frac{g-v\cdot H}{1+R_+},\qquad
k_-=u-e_p-e_b=\frac{g+v\cdot H}{1+R_-}.
\end{gathered}
\tag{X121.8}
$$

原相邻确认公式为整个 $V$ 上的恒等式

$$
e_s=\frac{R_+g+v\cdot H}{1+R_+},\qquad
e_b=\frac{R_-g-v\cdot H}{1+R_-}.
\tag{X121.9}
$$

[校准卷 123.8 的定理 123.11](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
拥有相邻有符号法向交线、原正性／接触／边完成等价及相反方向接触等价。
因 $d_+>0$，该等价给 $R_+,R_->1$，从而 $0<d_+,d_-<1$。
种子两方向已有 $\rho_p(v_0)=\rho_p(-v_0)=1$，所以
$v\ne\pm v_0$，$-1<\tau<1$。
$k_+,k_-$ 是有符号候选，未被称为原效应。

[校准卷 125.4、125.7](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
给出整个 $V$ 上的种子恒等式与完整球支撑式

$$
\begin{gathered}
e_p+e_q+e_r=u,\qquad
e_q=\frac{g+v_0\cdot H}{2},\quad
e_r=\frac{g-v_0\cdot H}{2},\\
h|_{D_q}=h(p)e_p+h(r)e_r\quad(h\in S_q),\\
h|_{D_r}=h(p)e_p+h(q)e_q\quad(h\in S_r),\\
e_s|_{D_q}=e_s(r)e_r,\qquad
e_s|_{D_r}=e_s(q)e_q.
\end{gathered}
\tag{X121.10}
$$

这些不是只在三个取样点成立的式子。
有实际 $P_0$ 种子且 $\dim V=9$ 时，
[校准卷 125.3—125.5](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
已给 $U_\triangle=V$、$\mathcal S_\triangle=V^*$ 和联合分离 $\mathsf J_\triangle$。
$\mathsf J_\triangle$ 在本章不是额外未付桥。
同卷 125.6 将三个规范读回的全锥正性与全部种子方向校准另行联系；
线性同构及九维数不支付那项正性。

本章不假设 $P_{\rm reg}$、移动球或效应族连续性、数值互易、
$\mathrm{Pair}_\perp$、正规范读回、$\mathsf E_0$、共同正延拓或原生操作。
以下五步保留这个九维入口，推导本身不使用环境维数九。

### 121.2 实际远端与四颗完整来源球上的符号

**命题 121.3（实际对径过载见证及严格参数）。**
令 $x$ 为 $p$ 在完整 $D_b$ 中的实际对径。
则 $b,x\in P_0$，置 $t=e_p(x)$、$a=e_x(p)$，有

$$
0<a,t<1,\qquad
e_x=a e_p+\gamma(g+v\cdot H)\quad\text{于全部 }V,
\tag{X121.11}
$$

其中

$$
\gamma=\frac{1-at}{(1-t)(1+R_-)},\qquad
\lambda=\frac{a}{\gamma(1+R_-)}
=\frac{a(1-t)}{1-at},\qquad
0<\lambda<1,
\tag{X121.12}
$$

且有严格界

$$
\frac1{1+R_-}<\gamma<\frac12.
\tag{X121.13}
$$

对完整 $D_b$ 的每个 $z$，

$$
k_+(z)=-\frac{R_--1}{1+R_+}g(z)\le0,
\quad k_+(z)=0\Longleftrightarrow z=p.
\tag{X121.14}
$$

在另外三颗完整球上则有

$$
\begin{aligned}
k_+(c+Bw)&=\frac{1-v\cdot w}{1+R_+}\ge0
&& (\|w\|\le1),\\
k_+|_{D_q}&=(1-e_s(r))e_r\ge0,\\
k_+|_{D_r}&=(1-e_s(q))e_q\ge0.
\end{aligned}
\tag{X121.15}
$$

特别地，$x$ 在三颗种子球之外，且
$e_p(x),e_q(x),e_r(x)>0$。

证明。
$p\perp b$ 是实际边，P0 边传播给 $b\in P_0$。
完整球 $D_b$ 的实际对径 $x$ 在其球面，故是原纯点；
$b\perp x$ 再给 $x\in P_0$。
于是 $p-b-x$ 是实际原边路，不是由稠密性挑出的近似路。

若 $t=0$，原确认 $e_p$ 使 $p\perp x$；
若 $a=0$，$e_x$ 使 $x\perp p$，补效应对称仍给同一关系。
任一情形都使 $p,b,x$ 成实际三角，完成实际边 $(p,b)$。
由相反方向完成等价，这要求 $R_-=1$，与严格偏差矛盾。
因此 $a,t>0$。
$x\ne p$，而 $e_p,e_x$ 的整个一值面分别为 $\{p\},\{x\}$，
所以 $a,t<1$。

[校准卷定理 123.3](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
在方向 $-v$ 的全域远端确认式正是 (X121.11)—(X121.12)。
其消元使用同一完整邻球中 $p,x$ 的两个原确认式，故所得等式在全部 $V$ 上成立。
$1-at>0$，且

$$
1-at-a(1-t)=1-a>0,
$$

给 $0<\lambda<1$。
另有

$$
\gamma-\frac1{1+R_-}
=\frac{t(1-a)}{(1-t)(1+R_-)}>0.
\tag{X121.16}
$$

在 $s$ 处，$e_p(s)=0$、$g(s)=1$、$v\cdot H(s)=1$，
故 $e_x(s)=2\gamma$。
而 $e_b(s)=d_->0=e_b(x)$，所以 $x\ne s$。
$e_x$ 的原一值面仅为 $\{x\}$，从而 $2\gamma<1$，得到严格上界。

在整个 $D_b$，$e_b=0$；由 (X121.9) 可得
$v\cdot H=R_-g$，代入 $k_+$ 即得 (X121.14)。
$g$ 的全 $K$ 零点仅是 $p$，所以除 $p$ 外符号严格负。
在完整 $D_p$ 上，$g=1$、$H(c+Bw)=w$，得到 (X121.15) 第一式。
在完整 $D_q$ 上，$e_p+e_r=1$ 及跨球支撑式给
$k_+=1-e_p-e_s=(1-e_s(r))e_r$。
在完整 $D_r$ 上同理。
系数非负来自原 $e_s\in\mathcal E$，没有局部效应替换。

$x\ne p$ 使 $k_+(x)<0$，所以它不属于这三颗非负球中的任何一颗。
各个原 $e_i$ 的整个零面是 $D_i$；$e_i(x)\ge0$ 而不为零，
故三个种子坐标都严格正。
这一步使用整面零集，不能只检查球的几个端点。证毕。

### 121.3 见证自己的完整球上的定位与符号传播

**命题 121.4（完整 $D_x$ 的混合态定位）。**
有

$$
D_x\cap D_p=\{b\},\qquad
D_x\cap D_q=D_x\cap D_r=\varnothing.
\tag{X121.17}
$$

在整个 $D_x$ 上，

$$
\begin{gathered}
k_-=-\lambda e_p,\qquad
e_b=1-(1-\lambda)e_p,\\
e_s=d_+-(d_++c_0\lambda)e_p,\\
k_+=\frac{2g+(1+R_-)\lambda e_p}{1+R_+}>0.
\end{gathered}
\tag{X121.18}
$$

$e_q,e_r$ 在整个 $D_x$ 上严格正；$e_p$ 在其中仅于 $b$ 为零。
因此每个原纯或混合 $z\in D_x\setminus\{b\}$ 都有三个严格正种子坐标，
并满足 $k_-(z)<0$。
在 $b$ 处，$e_p=k_-=0$，$e_q,e_r>0$，$k_+(b)=2/(1+R_+)>0$。

证明。
在完整 $D_p$，(X121.11) 化为

$$
e_x(c+Bw)=\gamma(1+v\cdot w).
\tag{X121.19}
$$

其整个闭球零集恰为 $w=-v$，即 $b$。
在完整 $D_q$，由 (X121.10) 中 $e_r=(g-v_0\cdot H)/2$，
$v\cdot H=-\tau e_r$、$g=e_r$，得到

$$
e_x|_{D_q}=a e_p+\gamma(1-\tau)e_r.
\tag{X121.20}
$$

两个系数都严格正，且 $e_p+e_r=1$；因此对整个混合球都严格正。
同理

$$
e_x|_{D_r}=a e_p+\gamma(1+\tau)e_q>0.
\tag{X121.21}
$$

$e_x$ 的整个原零面是 $D_x$，这就给出全部交集 (X121.17)。

在 $D_x$ 的每个 $z$，(X121.11) 的左边为零，
$g+v\cdot H=(1+R_-)k_-$，所以 $k_-=-\lambda e_p$。
于是 $e_b=g-k_-=1-(1-\lambda)e_p$。
由两个方向公式相加，先有整个 $V$ 上的恒等式

$$
(1+R_+)k_++(1+R_-)k_-=2g.
\tag{X121.22}
$$

限制到 $D_x$ 给出 (X121.18) 最后一式。
$e_x(p)=a>0$ 使 $p\notin D_x$；$g$ 的唯一原零点为 $p$，
故 $g>0$ 于整个 $D_x$，从而该式严格正。
从 $e_s=g-k_+$ 减去并整理，得到

$$
e_s=\frac{R_+-1}{1+R_+}
-\frac{R_+-1+(1+R_-)\lambda}{1+R_+}e_p,
$$

即所列 $d_+,c_0$ 形式。

精确原零面及 (X121.17) 给 $e_q,e_r>0$ 于整个 $D_x$，
$e_p$ 的唯一零点为 $b$。
再用 $\lambda>0$ 得到除 $b$ 外的严格负 $k_-$。
在 $b=c-Bv$，$e_q(b)=(1-\tau)/2>0$、
$e_r(b)=(1+\tau)/2>0$，(X121.22) 给指定的 $k_+(b)$。
所有等式均包括球内部的混合态。证毕。

### 121.4 反向亏量及穷尽的接触分支

**命题 121.5（同一实际反向亏量的界与等号）。**
令 $y$ 为 $b$ 在完整 $D_x$ 中的实际对径，记

$$
M_A=e_p(y)=\max_{D_x}e_p,\qquad
D=e_b(y)=\min_{D_x}e_b.
\tag{X121.23}
$$

则 $y\in P_0$，三个种子坐标均严格正，且

$$
\begin{gathered}
0<M_A<1,\qquad
D=1-(1-\lambda)M_A=\delta_x(b),\\
M_A\le\frac{d_+}{d_++c_0\lambda}
=\frac{R_+-1}{R_+-1+(1+R_-)\lambda}.
\end{gathered}
\tag{X121.24}
$$

置

$$
B_0=\frac{\lambda(R_++R_-)}{R_+-1+(1+R_-)\lambda}.
\tag{X121.25}
$$

有

$$
\lambda<B_0\le D<1.
\tag{X121.26}
$$

恰有如下两个互斥且穷尽的分支：

$$
\begin{aligned}
D=B_0
&\Longleftrightarrow e_s(y)=0
\Longleftrightarrow D_s\cap D_x=\{y\},\\
D>B_0
&\Longleftrightarrow \min_{D_x}e_s>0
\Longleftrightarrow D_s\cap D_x=\varnothing.
\end{aligned}
\tag{X121.27}
$$

证明。
$e_p$ 在完整 $D_x$ 非负、非恒定且唯一零点为球面点 $b$。
闭欧氏球上非恒定仿射函数的最小值和最大值在同一直径的唯一两端达到，
所以最大端正是实际 $y$，且 $M_A>0$。
如果 $M_A=1$，原一值面 $\{p\}$ 迫使 $y=p$；
但 $p\notin D_x$，矛盾。因此 $M_A<1$。
实际边 $x\perp y$ 由 P0 传播给 $y\in P_0$。
$y\ne b$，命题 121.4 给其三个种子坐标严格正。

(X121.18) 中 $e_b$ 是 $e_p$ 的严格递减仿射函数，
故在同一 $y$ 达唯一最小值 $D=1-(1-\lambda)M_A$。
[EXCLUSION IX120.13](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
把这个值识别为原边 $(x,b)$ 的反向亏量 $\delta_x(b)$，不要求这条边已完成。

原 $e_s\in\mathcal E$ 在全部 $C$ 非负。
在 (X121.18) 的唯一最小点 $y$ 评价给

$$
0\le e_s(y)=d_+-(d_++c_0\lambda)M_A.
\tag{X121.28}
$$

$d_++c_0\lambda>0$，可合法相除，得到 (X121.24)。
代入 $D$，有

$$
D\ge1-(1-\lambda)
\frac{R_+-1}{R_+-1+(1+R_-)\lambda}=B_0.
$$

写 $Q=R_+-1+(1+R_-)\lambda>0$，两个端点计算分别为

$$
\begin{aligned}
B_0-\lambda&=\frac{\lambda(1+R_-)(1-\lambda)}{Q}>0,\\
1-B_0&=\frac{(R_+-1)(1-\lambda)}{Q}>0.
\end{aligned}
\tag{X121.29}
$$

另由 $M_A>0$ 和 $1-\lambda>0$ 给 $D<1$。
从以上逐步等价可见，$D=B_0$ 恰是 (X121.28) 取等。
$e_s|_{D_x}$ 严格随 $e_p$ 递减，唯一最小点为 $y$；
其全 $K$ 零面是完整 $D_s$。
因此最小值为零时整个交集恰为 $\{y\}$，最小值严格正时整个交集为空。
混合点不产生第三种交集情形。证毕。

这里 $B_0<1$ 是明确的标量结论。
它既不实现所有球的联合配置，也不把任一接触分支排除。
等号尚未被证明迫使种子校准。

### 121.5 同一原正锥的轴截面及其有符号横线

**命题 121.6（联合三维空间中的实际正轴截面）。**
令

$$
L_{\rm ax}=\operatorname{span}\{u,e_p,e_b\}
=\operatorname{span}\{u,e_p,e_s\},\qquad g_x=u-e_x.
\tag{X121.30}
$$

则

$$
\begin{gathered}
\dim L_{\rm ax}=3,\quad e_x,g_x\in L_{\rm ax},\\
S_x\cap L_{\rm ax}=\operatorname{span}\{g_x,e_b\},\\
N_x\cap L_{\rm ax}=\operatorname{cone}\{e_b,e_y\},\\
L_{\rm ax}=(S_x\cap L_{\rm ax})\oplus\mathbb R k_+,\qquad
L_{\rm ax}\subset S_p+S_s,\\
\dim\bigl(S_x/(S_x\cap L_{\rm ax})\bigr)=2.
\end{gathered}
\tag{X121.31}
$$

在实际 $D_x=c_x+B_x\overline{\mathbb B}^{,3}$ 中令
$b=c_x+B_xn_x$、$y=c_x-B_xn_x$、$\|n_x\|=1$，并取原读数 $H_x$。
置 $R_b=\rho_x(n_x)$、$R_y=\rho_x(-n_x)$，则整个 $V$ 上有

$$
e_b=\frac{R_bg_x+n_x\cdot H_x}{1+R_b},\qquad
e_y=\frac{R_yg_x-n_x\cdot H_x}{1+R_y}.
\tag{X121.32}
$$

轴上 $\alpha g_x+\beta n_x\cdot H_x$ 的原全局正性恰为

$$
\begin{cases}
\alpha\ge\beta R_b,&\beta\ge0,\\
\alpha\ge(-\beta)R_y,&\beta\le0.
\end{cases}
\tag{X121.33}
$$

证明。
从 (X121.9) 可解出 $v\cdot H$，因而两个生成空间相同。
$u,e_p$ 独立，因为在 $p$ 读数同为一而在 $D_p$ 分别为一、零。
$e_b|_{D_p}$ 非恒定，所以 $e_b$ 不在 $\operatorname{span}\{u,e_p\}$；
这证明维数三。
(X121.11) 及 (X121.9) 把 $e_x,g_x$ 放在同一空间。

$g_x\in N_x$，实际边 $x\perp b$ 给 $e_b\in N_x$。
在 $D_x$ 上，它们分别是恒定一和非恒定的 $e_b$，所以独立。
评价 $\operatorname{ev}_x$ 在 $L_{\rm ax}$ 非零，因为 $u(x)=1$。
而每个 $S_x$ 元素在 $x$ 为零。
因此 $S_x\cap L_{\rm ax}$ 至多二维，以上两个独立元恰好张满它。

(X121.32) 是旧的原邻点确认公式在锚 $x$ 的直接应用。
旧的全局方向锥条件 (EXCLUSION IX120.11) 及 $\rho_x$ 的正齐次性，
对 $\beta\ge0$ 给 $\rho_x(\beta n_x)=\beta R_b$，
对 $\beta\le0$ 给 $\rho_x(\beta n_x)=(-\beta)R_y$。
这正是 (X121.33)，其两个边界射线为原 $e_b,e_y$。
当 $\beta=0$，条件是 $\alpha\ge0$，也在这两射线生成的锥内。
更明确地，$R_b+R_y>0$ 且

$$
\alpha g_x+\beta n_x\cdot H_x
=\frac{(1+R_b)(\alpha+\beta R_y)}{R_b+R_y}e_b
+\frac{(1+R_y)(\alpha-\beta R_b)}{R_b+R_y}e_y.
\tag{X121.34}
$$

(X121.33) 恰使两个系数非负；反向也由原效应正性成立。
所以正截面确在原 $C^*$ 中，而非仅在完整 $D_x$ 上非负。
事实上 $\min_{D_x}e_b=D>0$；
若把全部局部球正函数当作原正法向，会丢失这条真实边界。

$k_+=u-e_p-e_s\in L_{\rm ax}$，命题 121.3 给 $k_+(x)<0$。
$S_x$ 在 $x$ 为零，所以它与 $\mathbb R k_+$ 只有零交，得到直和。
$g,e_s\in S_p$，而 $e_p\in S_s$，且 $u=g+e_p$，
故 $L_{\rm ax}\subset S_p+S_s$。
最后 $x\in P_0$ 给 $\dim S_x=4$，扣除二维轴截面便得商维数二。证毕。

二维轴锥的计算应用已有方向锥；这里保留的是它在同一 $S_p+S_s$、
$S_x$ 及严格有符号横线中的联合位置。
它没有识别整个 $N_x$ 为 Lorentz 锥，也没有构造全正限制逆。

### 121.6 指定实际点上的准确反馈

**命题 121.7（两个指定有符号过载的乘积）。**
置 $k_{xb}=u-e_x-e_b$。则在已经存在的原纯点 $s$，

$$
\begin{aligned}
k_{xb}(s)
&=1-2\gamma-d_-\\
&=-\frac{t(1-a)(1-d_-)}{1-t}<0,
\end{aligned}
\tag{X121.35}
$$

而在已经存在的 $x$，

$$
-k_+(x)=\frac{(R_--1)(1-t)}{1+R_+}>0.
\tag{X121.36}
$$

两个指定幅度满足

$$
[-k_+(x)][-k_{xb}(s)]
=d_-(1-d_+)t(1-a)>0.
\tag{X121.37}
$$

证明。
命题 121.3 已给 $e_x(s)=2\gamma$；原反向确认给 $e_b(s)=d_-$。
因此 $k_{xb}(s)=1-2\gamma-d_-$。
用 $1-d_-=2/(1+R_-)$ 和 (X121.12)，有

$$
1-2\gamma-d_-
=\frac{2}{1+R_-}
\left(1-\frac{1-at}{1-t}\right)
=-\frac{2t(1-a)}{(1-t)(1+R_-)}.
$$

$0<a,t,d_-<1$ 保证所有分母与严格符号。
在 $x$ 使用 (X121.14) 及 $g(x)=1-t$ 得 (X121.36)。
相乘，再用

$$
\frac{R_--1}{1+R_-}=d_-,\qquad
\frac2{1+R_+}=1-d_+,
$$

便得 (X121.37)。证毕。

数学边路是 $p-b-x-y$：每条边已由实际完整球中的纯端点支付。
没有由此加入 $b-y$ 边、闭合循环、原生制备或门字证书。
两个负读数都属于指定有符号候选；原效应仍在整个 $C$ 上非负，
不存在这里推出的负物理概率。

### 121.7 同时配置的条件范围与原目标

**约定 121.8（保留的未证关系）。**
命题 121.3—121.7 的组合为 repo-derived：
远端恒等式归于校准卷 123.3，邻接有符号交线与相反接触等价归于该卷 123.11，
法向限制、方向锥及实际行走归于 EXCLUSION IX120.8、120.11—120.18，
种子全域单位与跨球式归于校准卷 125.4、125.7。
新组合是完整 $D_b,D_x$ 符号传播、反向亏量／关联界、联合轴截面位置和指定反馈乘积。
这些来源归属不构成文献优先性或独立性断言。

尚未排除在同一九维原实现中同时存在：这整个 $D_b,D_x$ 配置、
两个严格过载、原正轴截面及剩余两个独立法向方向、种子横向块与相邻有符号法向几何。
$D=B_0$ 与 $D>B_0$ 都未被排除；等号没有推出校准。
反馈乘积与标量区间没有推出 $d_+=0$，也没有构造全签名实现或反模型。
继续原对径行走仍保留旧的长奇周期或塌缩备选。

指定路径属于种子边分支且全部标签在 $P_0$，不推出整个纯点图覆盖或原生可达。
校准卷 124 的正则性／连续性入口、127—129 的正读回入口和 E0 条件仍分别保留。
实际 $P_0$ 种子加九维已支付 $\mathsf J_\triangle$；规范读回正性仍未支付。
裸 EB3 也没有在这里提供全局 Inj 或所给实际种子。

本卷始终保留同一原 $\Omega$、全部合法门序列、每个中间切口、
整个预测及未来读出域，以及所有原混合、符号和条件读数前件。
以上静态条件推导不供给实际物理来源、原操作或共同仪器、任意有限复合及纠缠输入、
全旁观者正性／CP、事件和记录实现、时钟、动力学、Hamiltonian、能量或数值 $\hbar$。
完整量子起源目标在这些原合同上仍未完成。

## 追加锚（本行以下为增补区）

## 122. 同一最大宽接触对的全确认转移与共同法向斜率

### 122.0 独立的最大宽入口

**定义 122.1（同一最大球、效应与接触对）。**
本章只沿用定义 121.1 的完整原 $V,C,u,K,P,\mathcal E,D_t,\mathcal A_t,N_t,S_t$，
并假设 EB3 和全局 Inj。
环境维数为任意有限维；不继承 X121 的九维、实际种子、$P_0$ 或 E0 前件。
对每个完整原球定义整个原效应区间上的宽度

$$
W(D_t)=\max_{f\in\mathcal E}\operatorname{osc}_{D_t}f,
\qquad
\operatorname{osc}_Af=\max_Af-\min_Af.
\tag{X122.1}
$$

[EXCLUSION IX118.14—118.15](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
及 [ExclusionWidthCompactness](../../../Blueprint/D5/S3/Quantum/Foundation/ExclusionWidthCompactness.md)
给出正的、实际达到的全局最大值，及达到每颗球宽度的原效应。
固定这份实际数据，并研究其条件分支

$$
F=D_p=c+B\overline{\mathbb B}^{,3}_F,\qquad
M=W(F)=\max_{t\in P}W(D_t),\qquad 0<M<1.
\tag{X122.2}
$$

选定达到 $M$ 的同一原效应 $b\in\mathcal E$，其全局振幅为一。
使用 [EXCLUSION IX 定理 120.21](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
及 [OriginalWidthContact](../../../Blueprint/D5/S3/Quantum/Foundation/OriginalWidthContact.md)
给出的同一唯一共同接触对。
它的至少一个接触面是纯单点：若零面是单点，它是纯点；
否则原真面分类使零面为某完整排除球，Inj 的一值面刚性使另一接触面为纯单点。
必要时把同一 $b$ 换成 $u-b$，同时交换其两端和两接触，并反转球方向。
此为同一对的定向，不是另选极值者。
由此记

$$
\begin{gathered}
q=c+Bn,\quad r=c-Bn,\quad \|n\|_F=1,\\
b(s)=1,\quad b(y)=0,\quad s\in P,\qquad
q-r=M(s-y).
\end{gathered}
\tag{X122.3}
$$

令

$$
G=D_s=c_s+A\overline{\mathbb B}^{,3}_G,\qquad
y=c_s+A\eta,\quad \|\eta\|_G\le1,\qquad m_s=W(G).
\tag{X122.4}
$$

$y\in G$ 由原 $b$ 这个零见证给出；不假设 $b$ 在全部 $G$ 为零。
$0<m_s\le M$。第二接触 $y$ 不被假设为纯点。
F 图与 G 图的三维坐标、内积和范数各自独立。
下文的 $n^\perp$ 属于 F 图，不存在默认的跨球等距识别。
只有在实际使用 $D_r$ 时才记 $m_r=W(D_r)$。

### 122.1 整个完整确认纤维向同一接触对的转移

**命题 122.2（A：对每个完整确认的同一接触转移）。**
对整个 $\mathcal A_s$ 的每个 $a$，均有

$$
a(q)-a(r)=M,\qquad
\operatorname{osc}_Fa=M,\qquad
\operatorname{slope}_F(a)=\frac M2n.
\tag{X122.5}
$$

其整个原一值面为 $\{s\}$，整个原零面为 $G$，
且它在同一 $q-r$ 上的共同接触对仍是 $(s,y)$。
唯一球上最大、最小点仍为 $q,r$。

证明。
因 $a\in\mathcal A_s$，有 $a(s)=1$ 且它在整个 $D_s$ 为零。
已由原 $b$ 支付的同一 $y\in D_s$ 因此满足 $a(y)=0$。
在固定原向量等式 (X122.3) 评价，得 $a(q)-a(r)=M$。
每个原效应在完整 $F$ 的振幅至多 $M$，所以这个指定端点差达到全部振幅。

写 $a(c+Bw)=a(c)+w_a\cdot w$，则完整球振幅为 $2\|w_a\|_F$，
指定直径差为 $2n\cdot w_a$。
于是

$$
2\|w_a\|_F=M=2n\cdot w_a.
$$

$M>0$，Cauchy–Schwarz 取等给 $w_a=(M/2)n$。
非恒定仿射球函数的两个极值点唯一，故确为同一 $q,r$。

定义已给 $G\subseteq\{z\in K:a(z)=0\}$；
反向任一额外零点会以这个原 $a$ 成为 $s$ 的原排除见证，故也属于完整 $D_s$。
这证明整个零面恰为 $G$，包括所有混合点。
Inj 的旧一值面接口给整个顶面 $\{s\}$。
同一 $s,y$ 仍满足原全幅效应的顶／底接触和指定弦等式；
旧共同对唯一性把它们识别为当前 $a$ 的同一接触对。证毕。

本命题转移的是已经存在的接触，不重新证明接触存在、唯一或第二端纯性。
它量化整个 $\mathcal A_s$，没有挑选一个便利确认子菜单。

### 122.2 一般接触标签的核包含及唯一共同斜率因子

**命题 122.3（B：一般冗余法向的同接触因子）。**
记 $H_s=S_s=\operatorname{span}N_s$。
用完整 G 图定义线性限制及 F 斜率

$$
\begin{aligned}
R_s:H_s&\longrightarrow\mathbb R\times\mathbb R_G^3,
&h(c_s+Az)&=\alpha+v\cdot z,\quad R_sh=(\alpha,v),\\
S_F:H_s&\longrightarrow\mathbb R_F^3,
&h(c+Bw)&=h(c)+(S_Fh)\cdot w.
\end{aligned}
\tag{X122.6}
$$

则

$$
\ker R_s\subseteq\ker S_F.
\tag{X122.7}
$$

有唯一线性映射 $T_s:\mathbb R\times\mathbb R_G^3\to\mathbb R_F^3$ 满足
$S_F=T_sR_s$，以及唯一线性 $L:\mathbb R_G^3\to n^\perp$，使

$$
T_s(\alpha,v)=-\frac M2(\alpha+\eta\cdot v)n+Lv,
\qquad T_s(1,0)=-\frac M2n.
\tag{X122.8}
$$

核的原载体表达为

$$
\begin{gathered}
\ker R_s=H_s\cap\operatorname{ann}(\operatorname{span}G),\\
\ker S_F=H_s\cap\operatorname{ann}(\operatorname{lin}(F-F)),\\
\operatorname{lin}(F-F)\subseteq\operatorname{span}G+H_s^\perp,
\end{gathered}
\tag{X122.9}
$$

其中 $H_s^\perp=\{x\in V:h(x)=0\text{ 对全部 }h\in H_s\}$。

证明。
[EXCLUSION IX120.7 及定理 IX119.10](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
已给 $R_s$ 满射和某个 $g_0\in\operatorname{ri}N_s$，其 $R_sg_0=(1,0)$。
这里的相对内部取于实际 $H_s=\operatorname{span}N_s$。
同一接口见 [OriginalNormalRestriction](../../../Blueprint/D5/S3/Quantum/Foundation/OriginalNormalRestriction.md)：
常数一的原正切片等于整个完整确认纤维的补，并与实际法向张成空间中的内部相交。
这些输入不需要 $s\in P_0$；本命题不重立六轴满射或内部切片定理。

对任一实际 $g\in N_s$ 且 $R_sg=(1,0)$，
旧原正法向最大值公式给

$$
\max_Kg=\max_Gg=1.
\tag{X122.10}
$$

它已在整个 $C$ 非负。
对非零 $x\in C$ 按原 $u(x)>0$ 归一到 $K$，得 $0\le g(x)\le u(x)$；
零向量也满足，故 $g$ 是原全锥效应。
$u-g$ 在 $s$ 为一，在全部 $G$ 为零，因此属于整个 $\mathcal A_s$。
命题 122.2 遂给

$$
S_Fg=-\frac M2n.
\tag{X122.11}
$$

现在取任意 $k\in\ker R_s$。
$g_0$ 在 $H_s$ 中相对内，所以存在可依赖于 $k$ 的 $\epsilon>0$，使

$$
g_0+\epsilon k\in N_s,\qquad g_0-\epsilon k\in N_s.
\tag{X122.12}
$$

二者仍有同一常数一的完整 G 限制。
(X122.11) 给它们同一 F 斜率；相减得到 $2\epsilon S_Fk=0$。
因此 $S_Fk=0$，证明核包含。
满射 $R_s$ 及该包含使 $T_s(\alpha,v)=S_Fh$ 对任一 $R_sh=(\alpha,v)$ 定义良好，
且线性、唯一。

对每个有符号 $h\in H_s$ 都有 $h(s)=0$。
把它作用于固定弦，得

$$
2n\cdot S_Fh=-Mh(y)=-M(\alpha+\eta\cdot v).
\tag{X122.13}
$$

(X122.11) 又固定 $T_s(1,0)$。
因此取 $T_s(0,v)$ 在 $n^\perp$ 上的正交投影为 $Lv$，
便给 (X122.8)，且没有常数坐标的横向项。
唯一性也由投影及满射给出。

限制为零恰是消去 $\operatorname{span}G$，斜率为零恰是消去 $\operatorname{lin}(F-F)$，
给 (X122.9) 前两式。
核包含表明每个 F 方向消去 $H_s\cap\operatorname{ann}(\operatorname{span}G)$。
有限维双重消去律

$$
\bigl(H_s\cap\operatorname{ann}(\operatorname{span}G)\bigr)^\perp
=H_s^\perp+\operatorname{span}G
$$

给最后的载体包含。证毕。

若另外给 $s\in P_0$，旧 EXCLUSION IX120.8／定理 IX119.10
已经使 $R_s$ 为同构；此时对任何斜率映射都自动存在 $S_FR_s^{-1}$。
所以这个特例没有新增限制单射、四维或法向同构结论。
一般 $s$ 下新组合是接触导致的核包含和一个共同因子的固定接触公式。
它没有证明一般 $R_s$ 单射，没有使 $T_s$ 为正，
也没有为任意有符号坐标给出原正提升。
(X122.9) 只涉及方向空间，不识别中心值或跨球度量。

### 122.3 仅在实际全局正法向像上的宽度约束

**命题 122.4（C：同一原正法向的两个完整球约束）。**
对每个非零实际 $h\in N_s$，写 $R_sh=(\alpha,v)$。
则

$$
\alpha\ge\|v\|_G,\qquad
\lambda_N=\alpha+\|v\|_G=\max_Kh>0,\qquad
f_h=\frac h{\lambda_N}\in\mathcal E.
\tag{X122.14}
$$

其完整球振幅准确为

$$
\operatorname{osc}_G f_h=\frac{2\|v\|_G}{\lambda_N},\qquad
\operatorname{osc}_F f_h=\frac{2\|T_s(\alpha,v)\|_F}{\lambda_N}.
\tag{X122.15}
$$

因而

$$
\begin{gathered}
\alpha\ge\left(\frac2{m_s}-1\right)\|v\|_G
\ge\left(\frac2M-1\right)\|v\|_G,\\
4\|Lv\|_F^2\le
M^2\left[(\alpha+\|v\|_G)^2-(\alpha+\eta\cdot v)^2\right].
\end{gathered}
\tag{X122.16}
$$

定义整个实际原法向像切片

$$
\mathcal B_s=\{v\in\mathbb R_G^3:\exists h\in N_s,\ R_sh=(1,v)\}.
\tag{X122.17}
$$

对它的每个 $v$，有

$$
\begin{gathered}
\|v\|_G\le\frac{m_s}{2-m_s}\le\frac M{2-M},\\
(1+\eta\cdot v)^2+\frac4{M^2}\|Lv\|_F^2
\le(1+\|v\|_G)^2.
\end{gathered}
\tag{X122.18}
$$

证明。
原正性在整个 G 给仿射球函数 $\alpha+v\cdot z\ge0$，
所以 $\alpha\ge\|v\|_G$。
旧原正法向最大值公式给 $\max_Kh=\alpha+\|v\|_G$。
若这最大值为零，$h$ 在全 $K$ 为零；$K$ 张成 $V$，所以 $h=0$，矛盾。
故 $\lambda_N>0$，并且按整个 K 的最大值归一真给全 $C$ 上的原效应。
这里没有把 $R_s$ 的有符号满射当成原正坐标满射。

完整仿射球的振幅是斜率范数的两倍，得到 (X122.15)。
第一振幅至多 $m_s$，因此

$$
2\|v\|_G\le m_s(\alpha+\|v\|_G),
$$

得第一行 (X122.16)。$m_s\le M$ 给第二个不等号。
第二振幅至多 $M$，所以

$$
4\|T_s(\alpha,v)\|_F^2
\le M^2(\alpha+\|v\|_G)^2.
$$

把 (X122.8) 代入，并用 $Lv\perp n$，其左边为
$M^2(\alpha+\eta\cdot v)^2+4\|Lv\|_F^2$，得到所列二次约束。
两个范数各在自己的图中，没有共享度量的假设。

对每个 $v\in\mathcal B_s$，定义提供同一实际正 $h$ 且 $\alpha=1$。
将其代入 (X122.16)，由 $0<m_s\le M<1$，
$M,2-m_s,2-M$ 都严格正，合法整理便得 (X122.18)。
$v=0$、$Lv=0$ 及其他斜率退化全部留在不等式内。
只在归一步骤排除 $h=0$。证毕。

径向界是旧全域最大值公式与宽度定义的准确改写。
二次界是旧 F 宽度上界在命题 122.3 的同一共同因子坐标中的表达，
不是第二个独立数值原理，也没有构造超出可行域的原正法向。

### 122.4 同一第二接触纯时的核方向

**命题 122.5（D：同一纯接触方向被共同横向因子消去）。**
在本章入口之外，另设同一 $y$ 是原纯点。
则 $\|\eta\|_G=1$ 且

$$
L\eta=0.
\tag{X122.19}
$$

证明。
[OriginalFacePolarity 的 chart_boundary](../../../Blueprint/D5/S3/Quantum/Foundation/OriginalFacePolarity.md)
把原纯 $y\in G$ 识别为这个完整图的球面点，故 $\|\eta\|_G=1$。
全局 Inj 给锚 $s$ 的 singleton exclusion-label 条件，即 SingleLabel。
[SingleLabelNormalBody 的 positive_ray](../../../Blueprint/D5/S3/Quantum/Foundation/SingleLabelNormalBody.md)
在这个前件下提供实际 $t_{\rm ray}>0$，使 $t_{\rm ray}\eta\in\mathcal B_s$。
其成员身份带有原 $N_s$ 中的正见证；没有从球上的局部正性制造它。
在 (X122.18) 取 $v=t_{\rm ray}\eta$，则

$$
1+\eta\cdot v=1+t_{\rm ray}=1+\|v\|_G.
$$

二次界只剩 $4\|L(t_{\rm ray}\eta)\|_F^2/M^2\le0$，
故 $L(t_{\rm ray}\eta)=0$，线性及 $t_{\rm ray}>0$ 给结论。证毕。

若同一 $y$ 混合，它在 $\operatorname{ri}G$，所以 $\|\eta\|_G<1$。
上述两个平方项的抵消不成立。
这里没有提供第二接触纯性，也没有把另一个纯点换成同一 $y$。
positive_ray 的 SingleLabel 不等于 $\mathcal A_s$ 单点，未偷加 $s\in P_0$。

### 122.5 同一两球相交时的严格宽度耦合

**命题 122.6（E：完整相交球的严格双宽度界）。**
在本章入口之外，另设同一 $F$ 与同一 $G$ 相交。
则

$$
F\cap G=\{r\},\qquad r\in P,\qquad p,s\in D_r.
\tag{X122.20}
$$

记 $m_r=W(D_r)$，有 $0<m_r\le M$。
对整个 $\mathcal A_p$ 的每个 $e$，置 $t_e=e(s)=e(y)$，则

$$
0<t_e<1,\qquad
1-m_r<t_e\le m_s,\qquad
m_s+m_r>1,\qquad M>\frac12.
\tag{X122.21}
$$

若同一 $y$ 是混合态，上界也严格：$t_e<m_s$。
若 $y$ 纯，上界允许取等。
准确的逆否命题为：$M\le1/2$ 迫使这同一最大球 F 与定向纯接触球 G 不相交。

证明。
任选 $a\in\mathcal A_s$；旧面接口保证其存在。
命题 122.2 给它在 F 的唯一最小点为 $r$，其原零面为 G。
如果 F 与 G 相交，最小值为零，因而整个交集恰为 $\{r\}$。
$r$ 是完整 F 的球面端点，故原纯。
从 $r\in D_p\cap D_s$ 及原零关系对称，得 $p,s\in D_r$。
这一步不能用于不相交分支。

旧定理 IX120.21 对每个当前 $e\in\mathcal A_p$ 给
$0<t_e=e(s)=e(y)<1$。
它是每个效应的两个相同接触读数；不同 $e$ 的 $t_e$ 不被当成同一常数。
又 $r\in D_p$ 给 $e(r)=0$。
因 $r,y\in G$，

$$
t_e=e(y)-e(r)\le\operatorname{osc}_G e\le m_s.
\tag{X122.22}
$$

严格下界应用的是 [EXCLUSION IX 的定理 119.8](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)，
不是同卷的第 119.8 节。
准确代换为：该定理的完整球取 $D_r$，球的 owner 标签取 $r$，
相邻纯点取 $p\in P\cap D_r$，相邻完整确认取当前 $e\in\mathcal A_p$。
再取一个完整确认 $a_r\in\mathcal A_r$。
$a_r(r)=1$ 且 $r\in D_p$；全局 $M<1$ 给

$$
\min_{D_p}a_r\ge1-W(D_p)\ge1-M>0.
\tag{X122.23}
$$

这正支付旧定理的一侧变分所需严格正下界。
旧定理于是给原效应在 $D_r$ 上的严格改进，故

$$
\operatorname{osc}_{D_r}e<m_r.
$$

由于同一 $p,s\in D_r$，有

$$
1-t_e=e(p)-e(s)
\le\operatorname{osc}_{D_r}e<m_r.
\tag{X122.24}
$$

联合 (X122.22) 得 $1-m_r<t_e\le m_s$，于是 $m_s+m_r>1$。
$m_s,m_r\le M$ 给 $2M>1$。

若同一 $y$ 混合，它在 G 的相对内部。
$e|_G$ 非恒定，因为 $e(r)=0<e(y)$。
非恒定仿射函数不能在球内部达到最大值，所以
$e(y)<\max_Ge$。
原非负及 $e(r)=0$ 给 $\min_Ge=0$，故
$t_e<\operatorname{osc}_Ge\le m_s$。
纯 $y$ 没有这个内部严格性。证毕。

这项新组合耦合两颗实际完整球的宽度；严格变分本身仍归旧定理 IX119.8。
它不提供 F/G 相交，不排除 $1/2<M<1$，也不把所有接触效应的读数统一成一个 $t$。

### 122.6 完整 EB1 五边形的准确方法控制

**命题 122.7（维数一控制中的同一宽度与接触）。**
取正五边形的整个原签名

$$
\begin{gathered}
V_5=\mathbb R\times\mathbb R^2,\qquad u_5(t,z)=t,\\
v_j=(\cos(2\pi j/5),\sin(2\pi j/5)),\qquad p_j=(1,v_j),\\
K_5=\operatorname{conv}\{p_j:j\in\mathbb Z/5\mathbb Z\},\quad
C_5=\operatorname{cone}K_5,\quad
\mathcal E_5=[0,u_5]_{C_5^*}.
\end{gathered}
\tag{X122.25}
$$

其原闭尖生成锥、严格单位、全部纯点、全效应及完整混合排除边的证明，
使用已有 [Janotta–Gogolin–Barrett–Brunner 多边形 note 第 1—2 节](../../../Library/FiniteGeometry/janottagogolinbarrettbrunner2011polygon.md)
与 [Takakura 多边形 note 的完整效应及整个对边范围](../../../Library/FiniteGeometry/takakura2020polygonentropy.md)。
前者与这里的质量坐标顺序仅差一个置换。
具体输入是：全部纯点恰为五个 $p_j$，效应为全 K 上所有 $[0,1]$ 仿射函数的齐次化，且

$$
D_{p_j}=[p_{j+2},p_{j+3}]
\tag{X122.26}
$$

包含整条混合边。
这同时给 EB1 和 Inj，绝非 EB3。
这些一般 carrier／效应／完整排除证明仍由既有 notes 承担；
以下保留这同一签名的短准确最大宽／接触计算。

置

$$
\sigma_5=\sin(2\pi/5),\quad
\tau_5=\sin(\pi/5),\quad c_5=\cos(\pi/5),\quad
\phi=\frac{1+\sqrt5}{2}=2c_5.
\tag{X122.27}
$$

则全部完整排除宽度为

$$
W(D_{p_j})=M_5=\frac1\phi<1.
\tag{X122.28}
$$

在 $F_5=D_{p_0}=[p_2,p_3]$，原效应

$$
b_5(t,z)=\frac{z_2+\sigma_5t}{2\sigma_5}
\tag{X122.29}
$$

达到该宽度，其唯一全局顶／底接触为同一 $s=p_1,y=p_4$，满足

$$
p_2-p_3=M_5(p_1-p_4).
\tag{X122.30}
$$

完整确认纤维 $\mathcal A_{p_0}$ 单点，其成员为

$$
e_0(t,z)=\frac{z_1+c_5t}{1+c_5},\qquad
e_0(p_1)=e_0(p_4)=\frac1\phi.
\tag{X122.31}
$$

且 $G_5=D_{p_1}=[p_3,p_4]$，$F_5\cap G_5=\{p_3\}$。
两颗相关完整球的宽度都为 $M_5$，$1-M_5<M_5$。
一维图中的法向限制已为线性同构，横向目标 $n^\perp=\{0\}$，所以 $L=0$。

证明。
全效应及完整排除事实如上述既有 notes。
它们给出的两个排除包含方向分别保留所有确认效应可能的混合零点，
以及在整条对边上为零的实际原效应；没有把完整确认菜单换成唯一完整确认。

两个差向量的质量坐标为零，水平坐标也相消，竖直坐标分别为 $2\tau_5,2\sigma_5$。
$\sigma_5=2\tau_5c_5$，故

$$
p_2-p_3=\frac{\tau_5}{\sigma_5}(p_1-p_4)
=\frac1\phi(p_1-p_4).
\tag{X122.32}
$$

对整个 $\mathcal E_5$ 的任意 $f$，$f(p_1),f(p_4)\in[0,1]$，于是

$$
|f(p_2)-f(p_3)|\le\frac1\phi.
$$

仿射函数在整条边的振幅恰是端点差的绝对值，
所以这给全效应宽度上界，不是有限菜单的上界。

竖直坐标在整个 $K_5$ 上的唯一最大、最小点为 $p_1,p_4$，值分别为 $\sigma_5,-\sigma_5$。
故 $b_5$ 在全 $K_5$ 取值于 $[0,1]$，齐次后在全部 $C_5$ 是原效应。
它在 F 上的端点差为 $\tau_5/\sigma_5=1/\phi$，
达到上界，且全局顶／底面确为指定单点。
(X122.32) 就是这同一对的弦等式。
整五边形的旋转保留全 carrier 和整个效应区间，因而给每条完整排除边同一宽度。

完整确认 $a\in\mathcal A_{p_0}$ 必须满足
$a(p_0)=1$、$a(p_2)=a(p_3)=0$。
三个不共线状态条件决定唯一仿射函数，解得 (X122.31)。
其全域 proper 性及整条边为零也由原多边形接口保证。
直接评价

$$
e_0(p_1)=e_0(p_4)
=\frac{\cos(2\pi/5)+c_5}{1+c_5}
=\frac1\phi.
$$

此唯一性是 $\mathcal A_{p_0}$ 的唯一性，
不宣称 $\mathcal F_{p_0}$ 只有该效应，更不改变原排除定义。
由 (X122.26) 立即有 $G_5=[p_3,p_4]$ 和指定单点交集。
$M_5>1/2$ 给 $1-M_5<M_5$，此处纯 $y$ 上界取等。

在 $s=p_1$ 的齐次法向 span 维数二，限制到其不共线对边的仿射函数空间也是二维同构。
所以 B 的零核在本例自动成立；一维 F 的 $n^\perp$ 为零，故 $L=0$。
两个原归一化及 C 的不等式由上述完整宽度直接满足；
D 的方向消去在零横向目标中成立；E 的严格下界和纯 y 上等号如上。
这给 A—E 的一维方法控制。证毕。

原多边形 carrier 和排除结论是 literature-attested 的中间输入：
Janotta、Gogolin、Barrett、Brunner，arXiv:1012.1215v3，第 3.1 节式 (5)、(6)、(8)，
及 Takakura，arXiv:1803.07388v2，第 2.2 节，版本和 DOI 见两份既有 notes。
准确的最大宽／同接触计算是这里保留的初等组合，不错误归于只证明 carrier 的 note。
FINITE_PURE VII97.6 的定理是有理七边形；其中五边形提及不代替上述准确计算。
已有 note 的另一个正延拓预算也不被当成这里的宽度。

此控制只限制对所有正球维数都有效的方法：
仅有接触纯性、完整法向最大值及单点接触面，仍允许一维的 $M<1$。
每个排除面在这里仿射维数一，所以它不是原 EB3 问题的反模型，
也不提供 EB3 饱和失败或逻辑独立性。

### 122.7 剩余的全局正性、宽度与原操作桥

**约定 122.8（共同因子的用途及仍缺见证）。**
本章的 repo-derived 组合为：整个 $\mathcal A_s$ 的同接触转移，
一般接触冗余下的核包含及唯一共同斜率公式，
同一纯 y 条件下的核方向，以及同一 F/G 相交时的严格双宽度耦合。
满射／内部切片、P0 同构、原全局最大值归一、径向宽度改写及严格变分均保留原归属。
既有 [CommonPositiveExtension](../../../Blueprint/D5/S3/Quantum/Foundation/CommonPositiveExtension.md)
的正限制双射／全正延拓另需 weakPair；
FINITE_PURE VII105.4 的对应结论也有其 W／Pair 前件。
全局标签 Inj 不支付这些前件。

没有推出 $M=1$，没有构造完整原 EB3+Inj 反模型。
同一 y 纯、F/G 相交和 $s\in P_0$ 都是各自明列的附加前件。
E 的耦合不能建立相交，也不能排除 $1/2<M<1$。

一个足够的实际上升证书是：有 $v\in\mathcal B_s$ 且
$\|v\|_G>M/(2-M)$，并带有定义中的原 $h\in N_s$、$R_sh=(1,v)$。
该同一 $h$ 给原全锥效应 $h/(1+\|v\|_G)$，在 G 的振幅为

$$
\frac{2\|v\|_G}{1+\|v\|_G}>M.
\tag{X122.33}
$$

同理，一个实际原正法向若违反共同图二次界，会给 F 上超过 M 的原效应。
本章未提供任一这种见证。
旧正内半径只给小的合法斜率，不给超过宽度阈值的斜率。
有符号满射或局部球正性不能补出全局正见证。

即使以后得到 $M=1$，首先也只支付至少一颗最大排除球的饱和；
传播至全部原球是另一条关系。
$T_s$ 只控制斜率，不控制中心值；它不是保持原单位的正态回缩、滤波、
逆映射、仪器、门字或实际控制。
[UnitPreservingLiftImage](../../../Blueprint/D5/S3/Quantum/Foundation/UnitPreservingLiftImage.md)
保留原单位的闭像／最小成本结果也没有提供正线性 section、成本一接触或这里的上升证书。
全原 $\Omega$、合法字、未来读出及 X121.7 的全部原生、复合、过程和时间合同仍保留。

## 追加锚（本行以下为增补区）
