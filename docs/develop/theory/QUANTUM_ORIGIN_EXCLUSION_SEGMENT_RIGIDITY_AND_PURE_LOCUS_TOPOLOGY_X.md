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
