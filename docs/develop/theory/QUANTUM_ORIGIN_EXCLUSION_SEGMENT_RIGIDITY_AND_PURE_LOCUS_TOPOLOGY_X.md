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
D_p=c+B\overline{\mathbb B}^{3},\qquad
q=c+Bv_0,\quad r=c-Bv_0,\quad \|v_0\|=1.
\tag{X121.4}
$$

这里 $\overline{\mathbb B}^{3}=\{w\in\mathbb R^3:\|w\|\le1\}$ 是整个闭单位三球。

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

[校准卷 125.3、125.4、125.7](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
给出整个 $V$ 上的种子恒等式与完整球支撑式

$$
\begin{gathered}
e_p+e_q+e_r=u,\qquad
e_q=\frac{g+v_0\cdot H}{2},\quad
e_r=\frac{g-v_0\cdot H}{2},\\
h|_{D_q}=h(p)e_p+h(r)e_r\quad(h\in\mathbb R e_p+S_p),\\
h|_{D_r}=h(p)e_p+h(q)e_q\quad(h\in\mathbb R e_p+S_p),\\
e_s|_{D_q}=e_s(r)e_r,\qquad
e_s|_{D_r}=e_s(q)e_q.
\end{gathered}
\tag{X121.10}
$$

这些不是只在三个取样点成立的式子。
其中跨球支撑先由校准卷 125.3 的唯一球支撑式对 $N_p$ 成立，
取 span 延至 $S_p$，再加入 $e_p$ 方向，给所列 $\mathbb R e_p+S_p$ 范围。
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

在实际 $D_x=c_x+B_x\overline{\mathbb B}^{3}$ 中令
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
F=D_p=c+B\overline{\mathbb B}^{3}_F,\qquad
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
G=D_s=c_s+A\overline{\mathbb B}^{3}_G,\qquad
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

## 123. 实际过载法向的规范横向平面与六整球测试边界

### 123.0 同一过载配置、实际轴标签与测试锥

**定义 123.1（完整原域上的横向数据）。**
本章沿用 X121 的同一原实现和全部前件：EB3、全局 Inj、实际含 $P_0$ 顶点的种子三角、
$\dim V=9$，以及原纯单位方向邻点 $s=c+Bv$、$\|v\|=1$、$d_+>0$。
使用同一实际 $p,q,r,s,b,x,y$ 和它们的整个排除球；
不是分别实现各颗球后拼接边缘数据。
保留 X121 的全部参数

$$
\begin{gathered}
R_+,R_->1,\quad 0<d_+,d_-,a,t,\lambda<1,\quad
\frac1{1+R_-}<\gamma<\frac12,\\
0<M_A<1,\quad \lambda<B_0\le D<1,\qquad
g_x=u-e_x,\quad G_0=1-2\gamma>0.
\end{gathered}
\tag{X123.1}
$$

$G_0$ 是标量，与 X122 的完整球 $G=D_s$ 无关。
在 X121 的实际 $D_x$ 图中，$b$ 位于 $n_x$，$y$ 位于 $-n_x$，
保留 $R_b=\rho_x(n_x)$、$R_y=\rho_x(-n_x)$。
从 (X121.32) 有

$$
D=e_b(y)=\frac{R_b-1}{R_b+1}>0.
\tag{X123.2}
$$

故 $R_b>1$；旧相反接触等价再给 $R_y>1$。
置

$$
\Delta=e_y(b)=\frac{R_y-1}{R_y+1},\qquad 0<\Delta<1.
\tag{X123.3}
$$

两个已有原确认式消去同一轴读数，给整个 $V$ 上的系数库存

$$
\begin{gathered}
e_y=A_0g_x-B_1e_b,\qquad
A_0=\frac{R_b+R_y}{1+R_y}>0,\qquad
B_1=\frac{1+R_b}{1+R_y}>0,\\
e_y(p)=A_0(1-a)>0.
\end{gathered}
\tag{X123.4}
$$

这只是 (X121.32) 的同一轴恒等式，不另立法向定理。
记 $\sigma_y=e_y(s)$。
原纯零关系对称及 (X121.27) 给

$$
\begin{aligned}
\sigma_y>0&\Longleftrightarrow D>B_0,\\
\sigma_y=0&\Longleftrightarrow D=B_0
\Longleftrightarrow s\in D_y.
\end{aligned}
\tag{X123.5}
$$

定义完整原球的线性张成与消去空间

$$
\begin{gathered}
M_p=\operatorname{span}D_p,\qquad M_y=\operatorname{span}D_y,\\
\operatorname{ann}(M)=\{h\in V^*:h|_M=0\},\\
T_y=\{h\in S_x:h|_{D_y}=0\},\qquad
Z_y=\{h\in T_y:h(y)=0\},\\
A_{\rm ax}=\operatorname{span}\{g_x,e_y\}
=S_x\cap L_{\rm ax}.
\end{gathered}
\tag{X123.6}
$$

最后一个等号由 X121 的二维原轴截面及 (X123.4) 给出。
设

$$
\begin{gathered}
U_4=D_p\cup D_q\cup D_r\cup D_x,\qquad
U_6=U_4\cup D_b\cup D_y,\\
Q_j=\{h\in S_x:h(z)\ge0\text{ 对每个 }z\in U_j\},\quad j=4,6,\\
\|h\|_K=\max_{\xi\in K}|h(\xi)|,\qquad
h_z=e_y+z\quad(z\in Z_y).
\end{gathered}
\tag{X123.7}
$$

$K$ 张成 $V$，故 $\|\cdot\|_K$ 是线性泛函空间上的范数。
$Q_4,Q_6$ 是辅助测试锥；原全局正性仍为

$$
N_x=C^*\cap S_x\subseteq Q_6\subseteq Q_4.
\tag{X123.8}
$$

每个 $D$ 都是整个原闭球，包括所有混合点。
在完整 $D_p=c+B\overline{\mathbb B}^{3}$ 上，把 $z\in Z_y$ 的有符号限制写成
$z(c+Bw)=\alpha_z+\beta_z\cdot w$，定义

$$
\Theta:Z_y\longrightarrow v^\perp,\qquad
\Theta(z)=\operatorname{proj}_{v^\perp}\beta_z.
\tag{X123.9}
$$

目标是 Dp 图中的二维欧氏平面；这只是有符号限制映射。
定义原评价映射

$$
\pi_x:V\longrightarrow S_x^*,\qquad
\pi_x(\xi)(h)=h(\xi).
\tag{X123.10}
$$

本章使用 $\dim S_x=4$ 和 X121 的实际轴截面。
环境九维与已支付的 $\mathsf J_\triangle$ 不被用于推定 $\operatorname{rank}\Theta=2$，
也没有正种子读回、E0、PC1、Pair、正则锚、球族连续性或原生仪器前件。

### 123.1 规范横向代表与原正切片的唯一点

**命题 123.2（A：由整个 $D_y$ 定义的规范二维补）。**
有

$$
\dim T_y=3,\qquad \dim Z_y=2,\qquad
S_x=A_{\rm ax}\oplus Z_y.
\tag{X123.11}
$$

所以 $Z_y$ 自然映到商 $S_x/(S_x\cap L_{\rm ax})$ 为线性同构。
原正锥满足

$$
C^*\cap\operatorname{ann}(M_y)=\mathbb R_{\ge0}e_y,
\qquad
N_x\cap(e_y+Z_y)=\{e_y\}.
\tag{X123.12}
$$

证明。
实际边 $x\perp y$ 使 $x$ 位于完整 $D_y$ 的球面。
每个实际 $k\in N_x$ 在该整个球非负且在 $x$ 为零。
若在某个单位三球图中该限制为 $\alpha+\ell\cdot w$，
非负性给 $\alpha\ge\|\ell\|$；
在球面点 $w_x$ 取零，给 $\ell\cdot w_x=-\alpha$，
所以 $\alpha=\|\ell\|$ 且 $\ell=-\alpha w_x$。
包括 $\alpha=0$ 在内，这些限制都在同一支撑仿射射线上。
取线性张成后，整个 $S_x$ 的限制像维数至多一。

$g_x$ 在 $D_y$ 非零：它在 $x$ 为零，且原一值面 $\{x\}$
使 $g_x$ 在该球其余每点严格正。
完整球正维，故确有其余点；限制像秩准确为一。
因此 $\dim T_y=4-1=3$。
$e_y\in T_y$ 且 $e_y(y)=1$，所以 $\operatorname{ev}_y|_{T_y}$ 非零，
其核 $Z_y$ 为二维。
在 $A_{\rm ax}=\operatorname{span}\{g_x,e_y\}$ 中，
限制到 Dy 先除去非零的 $g_x$ 方向，只剩 $\mathbb R e_y$；
再在 y 评价除去最后这条线。
故 $A_{\rm ax}\cap Z_y=0$，维数相加为四，得到规范直和。

为使用原面与唯一确认接口，取非零 $k\in C^*\cap\operatorname{ann}(M_y)$。
原生成性使 $m=\max_Kk>0$。
在紧的原最大面取一个原纯最大点 $w$。
则 $k/m\in\mathcal E$，在 $w$ 为一，在整个 $D_y$ 为零，故
$D_y\subseteq D_w$。
完整排除球的真面最大性给 $D_y=D_w$，Inj 给 $w=y$。
因此 $m=k(y)$，且 $k/m\in\mathcal A_y=\{e_y\}$，
从而 $k=k(y)e_y$。
$k=0$ 另给该射线的零端点；反向 $e_y\ge0$ 且消去 $M_y$，所以第一式成立。

每个 $e_y+z$，$z\in Z_y$，都在全部 Dy 为零且在 y 为一。
若它在原整个 C 非负，刚用的原正射线强迫它等于 $e_y$。
$e_y\in N_x$，所以第二式成立。证毕。

正消去射线是已有完整面归一及唯一确认的应用，
不是新增正提升或极端性原理。
本组合识别的是由整个 Dy 定义的规范商代表，未给任何正逆。

### 123.2 严格关联分支中的整二维六球测试缺口

**命题 123.3（B：穿孔二维邻域通过全部六颗完整球）。**
另设同一配置满足 $D>B_0$，即 $\sigma_y>0$。
存在 $\epsilon>0$，使每个 $z\in Z_y$、$\|z\|_K<\epsilon$ 都满足

$$
\begin{gathered}
h_z>0\text{ 于全部 }U_4,\qquad h_z|_{D_y}=0,\\
h_z\ge0\text{ 于全部 }D_b,\qquad
\{\xi\in D_b:h_z(\xi)=0\}=\{x\}.
\end{gathered}
\tag{X123.13}
$$

其中 $z=0$ 给原正 $e_y$；每个非零这种 $z$ 则有

$$
h_z\in Q_6\setminus N_x.
\tag{X123.14}
$$

这是整个二维横向平面中一个穿孔邻域，不是只沿一条轴线。

证明。
在完整 Dx，原反向确认式给 $\min_{D_x}e_y=\Delta>0$。
$e_y\in L_{\rm ax}$，而 (X123.4)、(X121.11) 和 (X121.9)
说明它在 Dp 的限制只依赖 $v\cdot w$。
在直径两端 b、s 的值分别是 $\Delta,\sigma_y$，所以

$$
e_y(c+Bw)=\frac{\Delta+\sigma_y}{2}
+\frac{\sigma_y-\Delta}{2}v\cdot w.
\tag{X123.15}
$$

严格分支使它在整个 Dp 的最小值 $\min\{\Delta,\sigma_y\}>0$。
在两颗其余种子球上，原全球支撑式给

$$
\begin{aligned}
e_y|_{D_q}&=e_y(p)e_p+e_y(r)e_r,\qquad e_p+e_r=1,\\
e_y|_{D_r}&=e_y(p)e_p+e_y(q)e_q,\qquad e_p+e_q=1.
\end{aligned}
\tag{X123.16}
$$

这些式子可把 $e_y$ 在 $L_{\rm ax}=\operatorname{span}\{u,e_p,e_b\}$ 中逐项限制而得，
其中 $e_b$ 的跨球支撑由校准卷 125.7 给出；不是仅从端点插值猜测全高维球。
$e_y(p)>0$ 已由 (X123.4) 支付。
由 $v\ne\pm v_0$，$q,r$ 均不同于 Dp 的可能零端点 s，
所以 (X123.15) 给 $e_y(q),e_y(r)>0$；严格分支下整个 Dp 本已严格正。
因此 (X123.16) 在整个 Dq、Dr 各有正下界。

置

$$
\mu=\min\{\Delta,\sigma_y,e_y(p),e_y(q),e_y(r)\}>0.
\tag{X123.17}
$$

以上整球式给 $e_y\ge\mu$ 于有限紧并 $U_4$。
取 $0<\epsilon<\mu/2$；则 $\|z\|_K<\epsilon$ 使
$h_z=e_y+z>\mu/2$ 于全部 U4，也使 $h_z(p)>0$。
根据 $Z_y$ 定义，$h_z$ 在整个 Dy 恒零。

还需整颗 Db，不能只检查它的端点。
同一实际球 Db 含球面点 x 及另一点 p，且 $g_x(p)=1-a>0$。
对每个正法向 $k\in N_x$，唯一球支撑论证使其在 Db 的限制与 $g_x$ 成比例。
取 span 后对每个有符号 $k\in S_x$ 仍有

$$
k|_{D_b}=\frac{k(p)}{g_x(p)}g_x|_{D_b}.
\tag{X123.18}
$$

对当前 $h_z$，系数正，且 $g_x$ 在 Db 仅于 x 为零。
因此 (X123.13) 的最后两项对整个混合球成立。
若 $z\ne0$，命题 123.2 的原全局正切片唯一性给 $h_z\notin C^*$；
它属于 $S_x$，从而正好是 (X123.14)。
当 $z=0$ 则 $h_0=e_y\in N_x$，不在负见证分支。证毕。

本结论条件于严格分支，没有证明该分支有一个全签名实现，也没有排除它。
它准确说明这六颗整球上的必要非负测试不足以支付原全局正性。

### 123.3 接触分支中的切向核与完整局部判据

**命题 123.4（C：同一接触下六球测试准确留下切向核）。**
另设同一配置满足 $D=B_0$，即 $s\in D_y$、$\sigma_y=0$。
存在 $\epsilon>0$，使对每个 $z\in Z_y$、$\|z\|_K<\epsilon$，

$$
h_z\in Q_4
\quad\Longleftrightarrow\quad \Theta(z)=0
\quad\Longleftrightarrow\quad h_z\in Q_6.
\tag{X123.19}
$$

这是一张局部仿射切片上的充要条件。
核具有不依赖补空间选择的描述

$$
\ker\Theta\simeq S_x\cap\operatorname{ann}(M_p+M_y),
\qquad
\dim\ker\Theta=2-\operatorname{rank}\Theta.
\tag{X123.20}
$$

秩 $0,1,2$ 分别留下二维、一维、零维局部候选空间。
若核非零，每个充分小的非零核向量都给 $Q_6\setminus N_x$ 中的 $h_z$。
若核为零，该邻域中唯一通过测试的 $h_z$ 是 $e_y$。

证明。
由 (X123.15) 及接触前件，整个 Dp 上有

$$
e_y(c+Bw)=\frac{\Delta}{2}(1-v\cdot w).
\tag{X123.21}
$$

而 $s\in D_y$ 使每个 $z\in Z_y$ 都满足 $z(s)=0$。
写 $z(c+Bw)=\alpha_z+\beta_z\cdot w$，则
$\alpha_z+\beta_z\cdot v=0$。
因此 $h_z$ 在 Dp 的中心值为 $\Delta/2+\alpha_z$，
其沿 v 的斜率为该数的相反数，切向斜率为 $\Theta(z)$。
完整球上的准确最小值是

$$
\min_{D_p}h_z
=\frac{\Delta}{2}+\alpha_z
-\sqrt{\left(\frac{\Delta}{2}+\alpha_z\right)^2
       +\|\Theta(z)\|^2}.
\tag{X123.22}
$$

只要 $\Theta(z)\ne0$，根号严格大于中心值的绝对值，
所以该最小值严格负。
这检验的是整颗球，不只是接触点 s 与反端点 b。
等价的球支撑表述是：一个在整球非负且在球面 s 为零的仿射函数，
其切向斜率必须为零。

若 $\Theta(z)=0$，$\beta_z$ 平行 v，且 $z(s)=0$，
故整球限制准确为

$$
z|_{D_p}=\frac{z(b)}{\Delta}e_y|_{D_p},
\qquad
h_z|_{D_p}=\left(1+\frac{z(b)}{\Delta}\right)e_y|_{D_p}.
\tag{X123.23}
$$

取 $\epsilon<\Delta/2$，即可使右侧系数严格正。
在 Dq、Dr，(X123.16) 仍成立。
尽管 $e_y(s)=0$，$q,r\ne s$，(X123.21) 仍给
$e_y(q),e_y(r)>0$；再加 $e_y(p)>0$，两颗整球都有正余量。
Dx 的余量仍是 $\Delta>0$。
将 $\epsilon$ 再缩至小于这些正余量的一半，
使当前 $h_z$ 在整个 Dq、Dr、Dx 严格正。
Dy 上恒零由定义给出；Db 上沿用 (X123.18)，
并用 $h_z(p)>0$，得到其仅在 x 为零、其余严格正。
因此一个共同邻域内，$\Theta(z)=0$ 充分保证 $h_z\in Q_6$。
反向 $Q_6\subseteq Q_4$，而 (X123.22) 给 $Q_4$ 的必要性，
故 (X123.19) 的两个方向均成立。

为证明 (X123.20)，对 $z\in\ker\Theta$ 定义

$$
\Phi(z)=z-\frac{z(b)}{\Delta}e_y.
\tag{X123.24}
$$

(X123.23) 使它消去整个 Dp；$z,e_y$ 都消去整个 Dy，
故 $\Phi(z)\in S_x\cap\operatorname{ann}(M_p+M_y)$。
反向对该空间中任一 $k$，定义

$$
\Psi(k)=k-k(y)e_y.
\tag{X123.25}
$$

它消去 Dy 且在 y 为零，所以属于 $Z_y$。
在 Dp，$k=0$，而 $e_y$ 没有切向斜率，因此 $\Theta(\Psi(k))=0$。
这两式互逆可在同一原点逐项核对：
对 $k=\Phi(z)$，$z(y)=0$、$e_y(y)=1$ 给
$k(y)=-z(b)/\Delta$，所以 $\Psi(\Phi(z))=z$。
对 $z=\Psi(k)$，$k(b)=0$、$e_y(b)=\Delta$ 给
$z(b)=-k(y)\Delta$，所以 $\Phi(\Psi(k))=k$。
两映射均线性，故为所称同构。
秩—零化度公式结合 $\dim Z_y=2$ 给维数式。

最后，任何通过局部测试的非零 $z$ 仍受 (X123.12) 约束：
$h_z$ 不可能原全局正，故属于 $Q_6\setminus N_x$。
零核情形没有这种非零局部候选，$z=0$ 给原正 $e_y$。证毕。

没有从 $\dim V=9$、$\mathsf J_\triangle$ 或二维轴正锥推定 $\Theta$ 的秩。
(X123.20) 只把未付的切向核改写成原完整球张成的共同消去空间。
零核时的局部切片唯一性也不等于 $Q_6=N_x$。

### 123.4 实际正法向的横向界与秩二圆盘

**命题 123.5（D：对同一个实际法向成立的必要界）。**
对每个非零实际 $h\in N_x$，不论两种关联分支，均有

$$
h(y)>0,\qquad h(b)>0.
\tag{X123.26}
$$

将该同一 $h$ 正归一化为 $h(y)=1$ 后，存在唯一 $r\in\mathbb R$、
$z\in Z_y$，使

$$
h=e_y+r(g_x-e_y)+z,\qquad r\ge0.
\tag{X123.27}
$$

以下进一步条件于接触 $D=B_0$。
置 $w_\Theta=\Theta(z)$，则

$$
\begin{gathered}
h(s)=rG_0,\qquad
h(b)=\Delta+(1-\Delta)r+z(b)>0,\\
\|w_\Theta\|^2
\le rG_0\bigl[\Delta+(1-\Delta)r+z(b)\bigr].
\end{gathered}
\tag{X123.28}
$$

若再明确加入 $\operatorname{rank}\Theta=2$，则存在唯一
$c_\Theta\in v^\perp$ 使 $z(b)=c_\Theta\cdot\Theta(z)$，
而同一必要界等价于平面圆盘条件

$$
\left\|w_\Theta-\frac{rG_0}{2}c_\Theta\right\|^2
\le rG_0\Delta
+r^2\left[G_0(1-\Delta)
+\frac{G_0^2}{4}\|c_\Theta\|^2\right].
\tag{X123.29}
$$

对于满足前述实际正法向前件的 h，(X123.28) 等号当且仅当
其在整个 Dp 有且仅有一个球面零点；此时每个内部点严格正。
严格不等号当且仅当该整球最小值严格正。
$r=0$ 的实际正分支只给 $h=e_y$、$z=0$；
零法向 $h=0$ 不进入归一化，另行保留。

证明。
先证严格读数。
若非零 $h\in N_x$ 还满足 $h(y)=0$，
取原纯最大点 $w$ 及 $m=\max_Kh>0$，则 $h/m\in\mathcal E$ 在 w 为一，
在 x、y 都为零。
所以 $x,y\in D_w$；原纯零关系对称给 $w\in D_x\cap D_y$。
但 $\min_{D_x}e_y=\Delta>0$，而 $e_y|_{D_y}=0$，两颗完整球不交。
这矛盾证明 $h(y)>0$。
同理，若 $h(b)=0$，纯最大点会属于 $D_x\cap D_b$。
然而 $\min_{D_x}e_b=D>0$，而 $e_b|_{D_b}=0$，仍矛盾。
这证明 (X123.26)，且没有把 signed 候选当作实际正法向。

由规范直和 (X123.11)，每个 $h\in S_x$ 唯一写为
$\alpha g_x+\beta e_y+z$，$z\in Z_y$。
在 y 处 $g_x(y)=e_y(y)=1$、$z(y)=0$，
故归一化使 $\alpha+\beta=1$。
令 $r=\alpha$，得到 (X123.27) 的唯一性。
其在完整 Dy 的限制是 $r g_x$，因为 $e_y,z$ 在那里恒零。
$g_x$ 在 Dy 的非 x 点严格正，实际 $h\ge0$ 强迫 $r\ge0$。

现在使用接触前件。
已有 $g_x(s)=1-e_x(s)=1-2\gamma=G_0>0$，
$e_y(s)=z(s)=0$，从而 $h(s)=rG_0$。
另一端 b 上，$g_x(b)=1$、$e_y(b)=\Delta$，给 (X123.28) 的第二式。
$g_x$ 和 $e_y$ 在 Dp 都没有切向斜率，因此 h 的切向斜率准确为 $w_\Theta$。
以直径两端 s、b 分解完整球图，得到准确最小值

$$
\min_{D_p}h
=\frac{h(s)+h(b)}2
-\sqrt{\left(\frac{h(s)-h(b)}2\right)^2+\|w_\Theta\|^2}.
\tag{X123.30}
$$

$h(s)\ge0$、$h(b)>0$ 已由实际正前件支付，中心值严格正。
因此最小值非负等价于平方后的判据

$$
\|w_\Theta\|^2\le h(s)h(b),
\tag{X123.31}
$$

代入两端读数就是 (X123.28)。
它是同一实际 h 在整个 Dp 的必要正性条件，
没有将一组分别可达的边缘界拼为共同实现，
也没有声称它充分刻画整个 $N_x$。

若 $r=0$，实际归一化 h 属于 $e_y+Z_y$，
(X123.12) 使它只能为 $e_y$，所以 $z=0$。
仅要求 Dp 上非负时，(X123.31) 只给 $\Theta(z)=0$，
不消去命题 123.4 的可能非零核。

若 $\operatorname{rank}\Theta=2$，二维定义域与二维目标使 $\Theta$ 为同构。
$z\mapsto z(b)$ 因而成为目标平面上的线性泛函，
欧氏表示唯一给 $c_\Theta$。
代入 $z(b)=c_\Theta\cdot w_\Theta$ 后，(X123.28) 为

$$
\|w_\Theta\|^2-rG_0c_\Theta\cdot w_\Theta
\le rG_0\Delta+r^2G_0(1-\Delta).
\tag{X123.32}
$$

两边加 $r^2G_0^2\|c_\Theta\|^2/4$ 即得 (X123.29)。
对于 $r>0$，右侧严格正；$r=0$ 时圆盘退化为原点。
圆盘描述每个固定 r 的必要横向范围，不是原全局正锥的一张已付参数化。
秩零或一时没有使用不存在的平面逆，也不套用 (X123.29)。

最后，实际 h 在 Dp 的中心值严格正。
若 (X123.31) 为等号，(X123.30) 的中心值等于斜率范数且非零，
球上非负仿射函数的零点唯一，是斜率反向的球面点；内部严格正。
若严格不等，中心值严格大于斜率范数，整个闭球最小值严格正。
反向分别由最小值公式成立。
零法向在整个 C 上非负，但 $h(y)=0$，故不能除以其读数，
它作为 $N_x$ 的零元保留。证毕。

所有严格常数都来自同一非退化源配置：
$\Delta,G_0,a,t>0$，$a,t,\lambda,M_A<1$，$\lambda,M_A>0$，
$R_+>1$、$d_+>0$。
没有把 $\Delta=0$、$G_0=0$、$a=0$、$t=0$、
$\lambda\in\{0,1\}$、$M_A\in\{0,1\}$ 或 $R_+=1$ 的端点补入这些证明。
接触等号、零法向和秩退化的处理不授权取消这些源严格前件。

### 123.5 原完整域中的实际纯负见证

**命题 123.6（E：每个通过六球测试的非零小候选有原纯外部见证）。**
取命题 123.3 严格分支的任一充分小非零 $z$，
或命题 123.4 接触分支的任一充分小非零 $z\in\ker\Theta$。
对同一个 $h_z=e_y+z$，存在原纯点 $a_{n_\ell}$，使

$$
\begin{gathered}
h_z(a_{n_\ell})<0,\qquad
a_{n_\ell}\notin U_6,\\
\pi_x(a_{n_\ell})\notin
\overline{\operatorname{cone}(\pi_x(U_6))}.
\end{gathered}
\tag{X123.33}
$$

该见证由同一个 signed h 的原方向和实际两边路径
$x-q_{n_\ell}-a_{n_\ell}$ 给出，
并具有准确读数式 (X123.37)。
接触零核时不存在本命题的非零局部候选；$z=0$ 为原正 $e_y$，
没有负见证结论。

证明。
两种分支都已逐颗证明 $h_z\ge0$ 于全部六颗完整球，
并由 (X123.12) 给 $h_z\notin C^*$。
x 是实际 P0 锚，故已有原法向限制同构允许唯一写成

$$
h_z=\alpha g_x+\ell\cdot H_x.
\tag{X123.34}
$$

这里 $H_x$ 是完整 Dx 的原三维法向坐标；
它与 Dp 图中的 $\Theta$ 目标不混同。
若 $\ell=0$，在 y 处 $h_z(y)=1$、$g_x(y)=1$ 使 $\alpha=1$，
所以 $h_z=g_x\in C^*$，矛盾。
故 $\ell\ne0$。
已有准确原全局方向判据随原 P0 限制同构给

$$
\alpha<\rho_x(\ell),\qquad
n_\ell=\frac{\ell}{\|\ell\|},\qquad
\rho_x(\ell)=\|\ell\|\rho_x(n_\ell).
\tag{X123.35}
$$

这里 $\rho_x$ 是原全局法向体的方向阈值，
不是只在六球测试域求出的阈值。
调用位置是
[校准卷 123.9、定理 123.12](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
与
[THREE_COPY VII122.2–122.3、定理 122.4](QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md)。
这些已有接口把正性阈值与实际完整原排除球的读数联系，
并非本章新设的正延拓假设。

令 $q_{n_\ell}$ 为 Dx 球面上方向 $n_\ell$ 的实际原纯邻点。
在完整原 $D_{q_{n_\ell}}$ 内，取 x 的实际反端点 $a_{n_\ell}$。
该点原纯，且两条实际边的 P0 传播使所需锚都保持 P0。
实际远端取得不依赖正则锚或球族连续性，见
[EXCLUSION IX120.11–120.13 的实际远端接口](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)。
完整球的原邻点确认式为

$$
e_{q_{n_\ell}}
=\frac{\rho_x(n_\ell)g_x+n_\ell\cdot H_x}
       {1+\rho_x(n_\ell)}.
\tag{X123.36}
$$

该确认式在整个 $D_{q_{n_\ell}}$ 为零，
所以那里有 $n_\ell\cdot H_x=-\rho_x(n_\ell)g_x$。
实际反端点不同于 x，原一值面 $\{x\}$ 使 $g_x(a_{n_\ell})>0$。
代入同一 $h_z$，得到

$$
\begin{aligned}
h_z(a_{n_\ell})
&=g_x(a_{n_\ell})
  \left[\alpha-\|\ell\|\rho_x(n_\ell)\right]\\
&=g_x(a_{n_\ell})[\alpha-\rho_x(\ell)]<0.
\end{aligned}
\tag{X123.37}
$$

这直接给实际原纯负见证，
而不是只用分离定理给出一个未标记的抽象点。
同一个 $h_z$ 在整个 $U_6$ 非负，故该原纯点不属于其中任何一颗完整球。

最后，在有限维 $S_x^*$ 上，评价于固定 $h_z$ 是连续线性泛函。
它在每个 $\pi_x(\xi)$、$\xi\in U_6$ 非负，
所以在这些评价像的锥包及其闭包非负。
而在 $\pi_x(a_{n_\ell})$ 上，它等于 (X123.37) 的严格负数，
故后者不在该闭锥包，证明 (X123.33)。证毕。

这里没有假设或推出 $\pi_x(C)$ 闭，
没有据此判任何锥为 nice 或 non-nice，
也没有把另一个锥和的闭性偷换为当前评价像的闭性。
原路径中的每个点和完整排除球都在同一 K 内；
存在该有限关系路径没有提供一条实现它的原合法门词。
$h_z$ 是 signed 线性候选，非负测试失败不等于物理负概率，
本章从未将其宣称为效果或可实施读回。

### 123.6 横向结论的适用范围与现有来源边界

**约定 123.7（原域、所有权与仍缺的桥梁）。**
X123 的新组合是：用同一实际 Dy 定义规范横向代表，
把严格关联与接触两分支中的六整球测试逐一算清，
再对同一实际正法向推导必要横向界，
并将每个已通过局部测试但不全局正的非零候选回接到原纯远端。
每条结论都保留 X121 的原 EB3、全标签 Inj、实际 P0 种子、
给定九维、实际纯 s 与 $d_+>0$；没有把它们换成更小域或更弱对象。

严格分支的穿孔二维缺口不证明严格分支有全签名实现，
也不证明该分支不可能。
接触分支保留全部 $\operatorname{rank}\Theta=0,1,2$ 情形；
共同消去空间是否为零、实际正锥横向非线性边界怎样闭合，均未支付。
秩二圆盘条件只在该附加秩前件下约束每个同一 h，
不供给全局正性、有限六球充分性、正校准读回或 $d_+=0$。
三步旧种子框架的 $\mathsf J_\triangle$ 已由实际 P0 种子与九维支付，
但个别规范种子读回的原全局正性仍按校准卷 125.6 单列。

现有来源的数学所有权保持如下区分。

1. [校准卷 123–125](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
   与 [EXCLUSION IX119–120](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
   拥有完整确认菜单、实际全局法向体、P0 限制同构、原球面纯点、
   实际边传播、反端点取得与种子维数接口。
   本卷仅在这些接口上形成 X121–X123 的已列组合，
   不复制旧接口的证明或把它们重命名为新原理。
2. [校准卷 128](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
   的弱分支给 $\nu_p\le1$，无需本卷实际种子；
   其 E0 下的迹与球内界保留额外 E0 前件。
   两种作用域既不相互替换，也不为本卷供给 E0。
3. [校准卷 129](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
   拥有 E0 下固定状态体的内球与 IC0 对校准间隙的条件描述。
   固定状态体、局部法向限制与本卷整球测试缺口是不同对象，
   不能把其内球当作本卷的共同正延拓或 PC1。
4. [校准卷 130](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
   区分几何覆盖与原反端点/正交实现，
   其中 Pair 型接口保留自身 $\mathrm{Pair}_{\perp}$ 前件。
   本卷不借几何覆盖插入 Pair、IC0、全原域同时实现或额外物理源。
5. [OriginalNormalRestriction](../../../Blueprint/D5/S3/Quantum/Foundation/OriginalNormalRestriction.md)
   拥有原法向限制的满射、实际常一读数的相对内部点及 P0 下的限制同构。
   满射不是任意原标签的单射；本卷 X122 的一般核消去不改这一边界。
6. [ExclusionIncidence](../../../Blueprint/D5/S3/Quantum/Foundation/ExclusionIncidence.md)
   拥有其精确前件下关联 O、开性及 Hausdorff 球空间之间的条件等价。
   条件等价不提供 O；X121、X123 的具体两分支均未被该接口自动排除。
7. [FixedZeroObstruction](../../../Blueprint/D5/S3/Quantum/Foundation/FixedZeroObstruction.md)
   拥有原全局最大、准确面与稳定零集推出 O 或坍缩的条件接口。
   稳定零集存在和适用前件仍须实际供给，不能从名称或条件结论倒推。
8. [UnitPreservingLiftImage](../../../Blueprint/D5/S3/Quantum/Foundation/UnitPreservingLiftImage.md)
   拥有原单位图像闭性与最小成本接口。
   该闭图像不供给当前带共同接触的正截面、仪器或球族实现。
9. [ActualExclusionBoundary](../../../Blueprint/D5/S3/Quantum/Foundation/ActualExclusionBoundary.md)
   的原单例标签存在、沿实际边传播及连续统多不同整球，
   仍只说标签纤维为单例。
   它既不替代全标签 Inj，也不等于单例确认 P0，
   更不推出纯点传递性或正种子读回。

上述来源均为已有结果；没有在本卷另立它们的证明或新增准入记录。
凸几何术语中的闭投影背景只按
[校准卷 123.14 的 Pataki 边界](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
使用。
当前 $C+S_x^\perp$ 的闭性、正截面或相关 niceness 条件未支付，
未调用任何要求这些前件的分类结论。
同样，若与射影面分类、滤子或自对偶文献比较，
其原复合、滤子、转置与对称性前件必须分别保留，
本卷没有补成这些前件。

所有推导仍位于同一原 Omega、全部原合法门序列及完整未来读出域。
既未删去混合点、符号、条件未来或中间切口，
也未把辅助 $Q_4,Q_6$ 的测试域换为新的物理状态体。
本卷没有提供原物理源、实际共同操作、原生事件或仪器、任意复合与旁观者兼容，
没有提供时钟、动力学、Hamiltonian、能量或 $\hbar$。
EB1 五边形仅为方法控制，未冒充 EB3 全签名反例；
全部条件几何结果也不构成独立性、最小性或量子起源完备性证明。
完整量子起源目标保持 active/incomplete。

## 追加锚（本行以下为增补区）

## 124. 极端对偶零面的整球塌缩障碍与互易非塌缩重构

本章在同一个原有限维有序空间上，证明一条对偶障碍：若极端正法向只在一个原纯点取零，那么实际完整排除球必能整体收缩到这个点。结合已有孤立重复球二分，这条障碍使纯端点互易加统一非塌缩足以推出标签单射；随后才调用既有同锥、同单位静态重构。在固定 EB3+PR 域内，统一有限预算已足以得到全部单位预算，不另输入预算数值一；任一球预算大于一则迫使全局预算无界及实际整球塌缩。以下均为普通数学定义、定理及纸面证明，未作 Lean 形式化或 kernel 核验。

### 124.1 完整原域、纯点暴露与非塌缩

**定义 124.1（全部原量词及本章条件）。** 设 $V\ne0$ 为有限维实空间，$C\subset V$ 为闭、尖、生成凸锥，$u\in V^{\ast}$ 在 $C\setminus\{0\}$ 上严格正。始终保留

$$
\begin{gathered}
C^{\ast}=\{f\in V^{\ast}:f(c)\ge0\quad(c\in C)\},\qquad
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\\
\mathcal E=[0,u]_{C^{\ast}},\qquad
F_p=\{f\in\mathcal E:f(p)=1\},\\
T_p(x)=\min_{f\in F_p}f(x)\quad(p\in P,\ x\in K),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{X124.1}
$$

这里的 $K$ 是整个原归一基，$P$ 是全部原纯点，最小化遍历整个原确认族，第二变量包括全部混态。由 [IX114.1][Q124IX]，$K,\mathcal E,F_p$ 紧，且这些最小值达到。$K$ 线性张成 $V$，$\operatorname{aff}K=\{u=1\}$。

对 $0\ne f\in C^{\ast}$ 及 $x\in C\setminus\{0\}$，记

$$
Z(f)=K\cap\ker f,\qquad N_x=\{g\in C^{\ast}:g(x)=0\}.
\tag{X124.2}
$$

在 $V$ 上固定一个辅助欧氏范数，只用于拓扑、直径及 Hausdorff 距离；这不是共同物理内积。使用以下条件：

$$
\begin{aligned}
\mathrm{EB}_{\ge1}:&\quad
\forall p\in P\ \exists d_p\in\mathbb N,\ d_p\ge1:
D_p\simeq_{\mathrm{aff}}\overline B^{d_p},\\
\mathrm{PE}:&\quad
\forall p\in P\ \exists h_p\in C^{\ast}\setminus\{0\}:
Z(h_p)=\{p\},\\
\mathrm{NC}:&\quad
\inf_{p\in P}\operatorname{diam}D_p>0,\\
\mathrm{Inj}:&\quad
\forall p,s\in P:\ D_p=D_s\Longrightarrow p=s,\\
\mathrm{PR}:&\quad
\forall p,q\in P:\ T_p(q)=T_q(p).
\end{aligned}
\tag{X124.3}
$$

$\mathrm{EB}_m$ 是所有 $d_p=m\ge1$ 的特例，EB3 是 $m=3$。PE 指每个原纯点是正泛函的单点零面；在这里可将 $h_p$ 除以 $\max_Kh_p>0$，等价地选在原效应区间内。PR 由 [IX114.3][Q124IX] 供应 PE，主应用不另输入 PE。PR 只交换两个纯端点的数值比较，不要求顺序测量交换。

非塌缩 NC 要求同一个正下界适用于全部原球；每颗球各自非退化不等于 NC。UF 保留 IX115.8 的统一有限预算原义，只在下面固定 EB3+PR 的预算域内使用，不用作通用非塌缩的名称。有限维范数等价使 NC 的真假及整球趋单点的性质与辅助范数的选择无关。下文直到静态重构之前，不输入 Inj、Pair、least 确认效应、Jordan 结构或全局球族连续性。

直接复用 [IX114.2及IX116.1][Q124IX] 的完整原面接口：在 $\mathrm{EB}_{\ge1}$ 下，每个 $D_p$ 是非单点紧暴露极大真面；每个非空真面恰为纯单点或某个完整 $D_s$。存在原 $e_p\in F_p$，其整个零面为 $D_p$。每个完整球 $F$ 的相对球面恰为 $S(F):=P\cap F$，且 $F=\operatorname{conv}S(F)$；不同完整球至多交于一个原纯点。变维版本使用 IX116.1 指明的 [VII103.2][Q124VII] 接口，不把固定维数版本扩大使用。

### 124.2 暴露对偶点对应的实际原混态

**引理 124.2（每个纯点有两条不同正法向）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{PE}$ 下，每个 $p\in P$ 的 $N_p$ 都含两条不成比例的非零正泛函。其中一条的零面为 $\{p\}$，另一条的零面为包含 $p$ 的实际完整球。

证明。先只用整个原效应区间的补：若 $f(p)=1,f(q)=0$，则 $u-f$ 在 $q,p$ 取一、零。因此

$$
T_p(q)=0\quad\Longleftrightarrow\quad T_q(p)=0
\qquad(p,q\in P).
\tag{X124.4}
$$

这一步不使用数值 PR。固定 $p$，在正维完整球 $D_p$ 的球面取 $q\in P\cap D_p$。零对称给 $p\in D_q$。原共同零确认 $e_q\in F_q$ 满足 $Z(e_q)=D_q$，所以 $e_q\in N_p\setminus\{0\}$。PE 另给 $h_p\in N_p\setminus\{0\}$，其零面为单点。若二者成比例，因都正且非零，只能成正比例，零面应相同；但 $D_q$ 正维，矛盾。证毕。

**引理 124.3（实际紧对偶基）。** 取任意 $x_0\in\operatorname{int}C$，定义

$$
B^{\ast}=\{f\in C^{\ast}:f(x_0)=1\}.
\tag{X124.5}
$$

在 $\mathrm{EB}_{\ge1}$ 下，$B^{\ast}$ 是至少含两个点的紧凸集，其仿射包为 $\{f:f(x_0)=1\}$；每条非零对偶射线与它恰交一次。

证明。$C$ 生成 $V$，故内部非空。取 $r>0$ 使 $x_0+r\overline B_V\subset C$。对任意 $f\in C^{\ast}$，在这颗球上取最小值得

$$
f(x_0)\ge r\|f\|_{\ast}.
\tag{X124.6}
$$

故非零正泛函在 $x_0$ 严格正，$B^{\ast}$ 闭且有界，归一交点唯一。它非空，因为含 $u/u(x_0)$。严格正的 $u$ 在紧 $K$ 上恒为一；充分小的对偶范数扰动仍在 $K$ 严格正，经齐次化仍属 $C^{\ast}$，所以 $C^{\ast}$ 满维。于是 $B^{\ast}$ 在所列超平面内有相对内部并张成该超平面。EB 正维排除 $K$ 为单点，因此 $\dim V>1$，这张基不可能只有一个点。证毕。

**命题 124.4（对偶暴露点的非零混态桥梁）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{PE}$ 下，若 $n\in B^{\ast}$ 是暴露点，则存在实际 $x\in C\setminus\{0\}$，使

$$
N_x=\mathbb R_+n,\qquad
\widehat x:=\frac{x}{u(x)}\in K\setminus P.
\tag{X124.7}
$$

其零面必为一张实际完整排除球：存在 $p\in P$，满足 $Z(n)=D_p$，且 $\widehat x\in\operatorname{ri}D_p$。

证明。暴露点定义给出在 $B^{\ast}$ 上以 $n$ 为唯一最小点的线性泛函。有限维自然对偶对应使它可写为 $f\mapsto f(v)$，其中 $v\in V$。置

$$
\alpha=\min_{f\in B^{\ast}}f(v),\qquad x=v-\alpha x_0.
\tag{X124.8}
$$

任取非零 $g\in C^{\ast}$，引理124.3允许归一，且

$$
g(x)=g(x_0)
\left[\left(\frac{g}{g(x_0)}\right)(v)-\alpha\right]\ge0.
\tag{X124.9}
$$

零泛函也满足此不等式。因此由闭凸锥的有限维分离定理，$x\in C$：若不在 $C$，会有某个 $g\in C^{\ast}$ 使 $g(x)<0$。

$x$ 不能为零；否则 $v=\alpha x_0$，所用暴露泛函在整个 $B^{\ast}$ 恒为 $\alpha$，与至少两点的基上唯一取最小矛盾。严格正单位于是给 $u(x)>0$，$\widehat x$ 确为原 $K$ 中的实际态。

对非零正 $g$，(X124.9) 等号当且仅当其归一元是唯一最小点 $n$，从而 $N_x=\mathbb R_+n$。正比例归一不改法向面，故 $N_{\widehat x}=N_x$。若 $\widehat x$ 纯，引理124.2使这个法向面至少含两条不同射线，矛盾。因此 $\widehat x$ 是混态。

现在 $n(\widehat x)=0$，故 $Z(n)$ 非空。$n\ne0$，而 $K$ 张成 $V$，所以它不可能在整个 $K$ 为零；$Z(n)$ 是非空真面。它包含混态，完整原面分类排除纯单点，只能给 $Z(n)=D_p$。该球的相对边界全部是原纯点，混态 $\widehat x$ 因而在相对内部。证毕。

这条桥梁构造的是非零原锥向量及其归一混态，不是一个原纯暴露点。识别为完整球的理由是这个实际混态加原面分类；没有把任意抽象对偶面称为原排除球，也没有把它当成 facet。

### 124.3 极端对偶单点零面迫使实际整球塌缩

**定理 124.5（极端对偶零面的塌缩障碍）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{PE}$ 下，若原 $C^{\ast}$ 的某条极端射线有单点零面 $\{q\}$，则 $q\in P$，且存在原标签 $p_i\in P$ 及暴露对偶基点 $n_i\in B^{\ast}$，满足

$$
Z(n_i)=D_{p_i},\qquad
d_H(D_{p_i},\{q\})\longrightarrow0,\qquad
\operatorname{diam}D_{p_i}\longrightarrow0.
\tag{X124.10}
$$

每个 $D_{p_i}$ 都是原完整正维球，且含命题124.4构造的实际混态。这里不要求球维数固定，不预设 $P$ 闭、球族连续或 Inj。

证明。单点零面是单点凸面，其唯一点必为原极点，所以 $q\in P$。将给定极端射线归一为 $n\in B^{\ast}$。射线极端性等价于 $n$ 是该基的极点：基中非平凡凸分解直接给射线的正分解；反向对 $n=g+h$ 的非零正项分别除以它们在 $x_0$ 的值，就得到基中的凸分解，且两个正权之和为 $n(x_0)=1$。

对有限维紧凸集 $B^{\ast}$ 应用成熟的 Straszewicz 定理：暴露点集在极点集中稠密。这里所用恰是 [Bru—de Siqueira Pedra §4.3，PDF第31页第二段][Q124BP] 明述的有限维结论。故可选暴露点列 $n_i\to n$。命题124.4逐项给实际混态和实际标签，使 $Z(n_i)=D_{p_i}$。

须证明整个零面都接近 $q$。若不成立，存在 $\varepsilon>0$、子列及 $y_i\in Z(n_i)$，使 $\|y_i-q\|\ge\varepsilon$。紧 $K$ 允许再取 $y_i\to y\in K$。有限维配对联合连续给

$$
n(y)=\lim_i n_i(y_i)=0.
\tag{X124.11}
$$

于是 $y=q$，与距离下界矛盾。因此

$$
\eta_i:=\max_{y\in Z(n_i)}\|y-q\|\longrightarrow0.
\tag{X124.12}
$$

各零面非空，故 $d_H(Z(n_i),\{q\})=\eta_i$，并且其直径至多 $2\eta_i$，得到全部结论。证毕。

**引理 124.6（极端正法向的零面穷尽）。** 在本章原域及 $\mathrm{EB}_{\ge1}$ 下，每条非零极端对偶射线的零面非空且为真面，因而恰为原纯单点或实际完整球。在另有 PE 和 NC 时，全部这类零面都是完整球。

证明。令 $n\in\operatorname{ext}B^{\ast}$。若 $n\in\operatorname{int}C^{\ast}$，可选非零 $k\in V^{\ast}$ 满足 $k(x_0)=0$，并取足够小的 $t>0$，使 $n\pm tk\in C^{\ast}$。二者仍在 $B^{\ast}$，且以 $n$ 为中点，违背极端性；故 $n$ 在对偶锥边界。

若 $Z(n)$ 为空，紧 $K$ 给 $\min_K n>0$；对偶范数足够小的扰动仍在整个 $K$ 非负，从而仍在 $C^{\ast}$，这却使 $n$ 在内部。故零面非空。$K$ 张成 $V$ 且 $n\ne0$，又使它为真面。完整原面分类给所列二择。若另有 PE，单点分支由定理124.5产生实际直径趋零球列，与 NC 矛盾，故只剩完整球。证毕。

定理124.5只证明“极端单点零面推出塌缩”。它没有把所有可能的塌缩反向归结为极端单点零面，也没有从面分类本身推出 NC。

### 124.4 孤立重复球对必产生这种对偶障碍

**定理 124.7（重复标签迫使实际塌缩）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{PE}$ 下，若存在不同原纯标签 $p,s$ 满足 $D_p=D_s$，则存在 [IX116.2][Q124IX] 的孤立重复球对 $F,G$。对每个

$$
q\in S(F)\cup S(G)
\tag{X124.13}
$$

都存在原极端对偶射线，其零面恰为 $\{q\}$；从而实际完整球可按(X124.10)整体收缩到 $q$。这一逆否方向不使用 NC。

证明。复用 IX116.2 的准确二分：有唯一配对球 $G$，使

$$
I(F)=S(G),\quad I(G)=S(F),\quad F\cap G=\varnothing,
\qquad I(A):=\{t\in P:D_t=A\},
\tag{X124.14}
$$

而 $F,G$ 均不与第三张不同完整球相交。因此每个 $q\in S(F)$ 只属于完整球 $F$；另一侧相同。

固定 $q\in S(F)$。PE 给非零 $h\in C^{\ast}$，使 $Z(h)=\{q\}$。将 $h$ 归一到紧对偶基。有限维 Minkowski 定理及 Carathéodory 定理给极点的有限凸分解；恢复正比例后可写为

$$
h=\sum_{j=1}^{r}\lambda_j n_j,\qquad
\lambda_j>0,\quad n_j\in\operatorname{ext}B^{\ast}.
\tag{X124.15}
$$

因为 $h(q)=0$，而各项在 $q$ 非负，所以每个 $n_j(q)=0$。引理124.6的零面二择因而在每项上准确成为 $Z(n_j)=\{q\}$ 或一张经过 $q$ 的完整球。假如全部为球，孤立性迫使全部等于 $F$。此时(X124.15)会使 $h$ 在整个 $F$ 为零，与 $Z(h)=\{q\}$ 及 $F$ 非单点矛盾。因此至少一个 $n_j$ 的零面恰为 $\{q\}$。其射线极端，定理124.5给实际塌缩。对 $q\in S(G)$ 交换两球即得。证毕。

**推论 124.8（非塌缩自动支付标签单射）。** 在允许变维的 $\mathrm{EB}_{\ge1}$ 原域中，

$$
\mathrm{PE}+\mathrm{NC}\quad\Longrightarrow\quad\mathrm{Inj}.
\tag{X124.16}
$$

特别地，$\mathrm{EB3}+\mathrm{PR}+\mathrm{NC}$ 推出 Inj，主前件中不需要另列标签唯一性。

证明。若 Inj 失败，定理124.7给直径趋零的实际原球列，直接违反 NC。主特例的 PE 由 IX114.3 的原纯端点严格暴露供应。证毕。

**推论 124.9（与既有整球极限接口的精确衔接）。** 在 EB3+PR 下，若定理124.5产生 $D_{p_i}\to\{q\}$，则可取子列使原标签 $p_i\to p\in P$，并有 $q\in P\cap D_p$，特别地 $p\ne q$。这是 [IX115.4—115.5][Q124IX] 保留的单点极限分支。若 $q$ 属于重复球对中的 $S(F)$，则可进一步确定 $D_p=F$、$p\in S(G)$。

证明。这里只在 PR 特例中复用 IX114.4 的 $P$ 紧性，取得纯极限标签 $p$。从每个非空 $D_{p_i}$ 任取 $y_i$，整球趋单点给 $y_i\to q$；IX115.4 的原零关系闭图于是给 $q\in D_p$。又 $T_p(p)=1$，故 $p\ne q$。IX115.5在这个纯极限标签处允许的两分支是完整 $D_p$ 与原纯单点；这里属于后者，没有违反上半连续性。最后，重复球隔离使经过 $q\in S(F)$ 的完整球只能为 $F$，再用 $I(F)=S(G)$ 即得末项。证毕。

这不把“存在塌缩的备选分支”误作一般反模型；定理124.7是在假定实际重复球对存在时，强制产生这种分支。也没有声称塌缩球的标签趋向塌缩点本身。

### 124.5 互易加非塌缩的同原静态复三能级应用

**定理 124.10（固定EB3+PR域内的条件类）。** 在定义124.1的完整原域中，假设 EB3 和 PR。记 $H(p,q)$ 为原 $K$ 中包含 $p,q$ 的最小面，记

$$
\mathrm{Pair}_{\perp}:\quad
\forall p,q\in P:\ T_p(q)=0\Longrightarrow H(p,q)\ne K.
\tag{X124.17}
$$

对每个完整球 $F=D_p$，$\beta_F$ 保留 [IX114.5—114.6][Q124IX] 的原全锥正延拓预算定义：在任意仿射球图 $b_F:\overline B^3\to F$ 中，令 $h_v(b_F(z))=(1+v\cdot z)/2$，$v\in S^2$；则

$$
\beta_F=
\min_{\substack{g\in C^{\ast}\\g|_F=h_v}}\max_Kg
=\frac1{2a_F}\ge1,
\tag{X124.18}
$$

其中 $a_F$ 为该来源的球内共同系数。这里仅复用其有限性、方向无关性及准确预算，不重新推导校准公式。

在这个固定域内，令 $\mathscr B=\{D_p:p\in P\}$，即不同实际完整球的集合，并准确沿用 [IX115.1、IX115.8][Q124IX] 的参数与名称：

$$
\begin{gathered}
d(p)=\operatorname{diam}D_p,\qquad a(p)=a_{D_p},\qquad
\beta(p)=\beta_{D_p}=\frac1{2a(p)},\\
\mathrm{UF}:\quad\sup_{F\in\mathscr B}\beta_F
=\sup_{p\in P}\beta(p)<\infty.
\end{gathered}
\tag{X124.18a}
$$

即使尚未有 Inj，两种上确界也相同，因为预算属于球本身，不依赖同球标签的选择。

在固定的 EB3+PR 域内，下列六项等价：

1. NC，即全部原完整球的直径有统一正下界；
2. Inj 与 NC 同时成立；
3. 原 $\mathrm{Pair}_{\perp}$；
4. 对全部 $p\in P$，$\beta_{D_p}=1$；
5. 存在同原锥、同原单位的实线性双射

$$
\Phi:H_3(\mathbb C)\overset{\sim}{\longrightarrow}V,
\qquad
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,
\qquad u(\Phi X)=\operatorname{Tr}X.
\tag{X124.19}
$$

6. IX115.8 的 UF，即所有原完整球的预算有同一个有限上界。

因此候选包 $\mathrm{EB3}+\mathrm{PR}+\mathrm{NC}$ 及 $\mathrm{EB3}+\mathrm{PR}+\mathrm{UF}$ 都与(X124.19)等价，并给 $\dim_{\mathbb R}V=9$。全 Pair 指任意两个不同原纯点均生成真最小面；它也与这些条件等价。其中自动去掉单列 Inj 的推导是推论124.8；复三能级分类本身完全复用既有结果。

证明。先在取得 Inj 之前核对 $1\Longleftrightarrow6$。取与定义124.1相同的辅助范数，令 $L=\max_{f\in\mathcal E}\|f\|_{\ast}>0$。IX115.3、IX115.6 的普遍估计为 $2a(p)\le Ld(p)$。若 UF 给出 $\beta(p)\le M<\infty$，则

$$
d(p)\ge\frac{2a(p)}L=\frac1{L\beta(p)}\ge\frac1{LM}>0,
\tag{X124.18b}
$$

故有 NC。反之，若 $d(p)\ge d_0>0$ 对全部 $p$ 成立，取 $j$ 使 $1/j\le d_0$，则 IX115.1 的 $S_j=P$，故 $\mathcal R=P$。IX115.6 给整球映射在全部 $P$ 上 Hausdorff 连续；IX115.8 因而给 UF。这里使用 IX114.4 的紧 $P$：等价地，IX115.6 已给 $\beta$ 在 $\mathcal R=P$ 连续，故其在 $P$ 上有有限上界；直径也随整球连续且处处为正。此段只消费原预算、正则区及紧性，不用量子重构、Inj 或 Pair。

$1\Rightarrow2$ 是推论124.8，$2\Rightarrow1$ 直接成立。第2项与第5项的等价恰为 [IX118.8][Q124IX] 的第2、4项：其前件是同一完整 EB3 域、Inj 及这个正直径下界，三项现均已支付；不在取得 Inj 前调用该重构。它不要求 PR，而本定理保留 PR 的较窄原域也满足其适用条件。第3、4项的等价直接使用 IX114.8；第4、5项的等价直接使用 IX114.9。IX118.8还给第5项下的全Pair，反向全Pair当然蕴含第3项，所以全Pair同属这个条件类。此处不重证成熟静态分类、拓扑环计算或 Jordan 桥。

反向的完整量词不能缩为有限菜单。IX118.8 的反向及 IX114.9 的字典给出：在(X124.19)坐标中，全部原态、纯点、效应和原最小确认分别为

$$
\begin{gathered}
K=\{\Phi\rho:\rho\succeq0,\ \operatorname{Tr}\rho=1\},\qquad
P=\{\Phi(vv^{\ast}):v\in\mathbb C^3,\ v^{\ast}v=1\},\\
\mathcal E=\{f_E:0\preceq E\preceq I_3\},\qquad
f_E(\Phi X)=\operatorname{Tr}(EX),\\
T_{\Phi(vv^{\ast})}(\Phi\rho)=\operatorname{Tr}(vv^{\ast}\rho),\qquad
T_{\Phi(vv^{\ast})}(\Phi(ww^{\ast}))=|v^{\ast}w|^2,\\
D_{\Phi(vv^{\ast})}
=\{\Phi\rho:\rho\succeq0,\ \operatorname{Tr}\rho=1,\ \rho v=0\}.
\end{gathered}
\tag{X124.20}
$$

所以 PR 对全部纯对成立，每个完整排除集都是 $v^{\perp}\cong\mathbb C^2$ 上的整个密度态三球；不是从其中选择三球子面。其支撑确定 $v^{\perp}$，故已有反向也给 Inj。

为明确 NC 的原环境含义，可取 $a>0$ 使 $\|\Phi X\|\ge a\|X\|_{\mathrm{HS}}$ 对全部 Hermitian $X$ 成立。每个上述二维复支撑中的一对正交秩一投影相距 $\sqrt2$，故每张原完整球直径至少 $a\sqrt2>0$。这只是固定线性同构下的长度运输，不要求 $\Phi$ 对辅助尺等距。于是同一个整个量子模型确实满足 EB3、PR、NC 的全部原量词，证明反向候选包成立。证毕。

这里没有得到 Inj 单独推出 NC，也没有证明非塌缩比原 $\mathrm{Pair}_{\perp}$ 或单位预算严格更弱。在固定 EB3+PR 域中，它们正是同一条件类的不同表述。少列一个 Inj 前件指上述特定桥梁中的逻辑蕴含，不是独立公理数量、最小性或总体量子起源任务已经完成的结论。

**推论 124.11（有限统一预算即单位饱和；偏离迫使实际塌缩）。** 在同一完整 EB3+PR 域中，

$$
\sup_{F\in\mathscr B}\beta_F<\infty
\quad\Longleftrightarrow\quad
\forall F\in\mathscr B:\ \beta_F=1.
\tag{X124.20a}
$$

若存在实际完整球 $F$ 使 $\beta_F>1$，则

$$
\sup_{F\in\mathscr B}\beta_F=+\infty,\qquad
\inf_{p\in P}\operatorname{diam}D_p=0,
\tag{X124.20b}
$$

并存在实际原标签列及纯点 $p,q\in P$，使

$$
\begin{gathered}
p_i\longrightarrow p,\qquad q\in D_p,\qquad p\ne q,\\
d_H(D_{p_i},\{q\})\longrightarrow0,\qquad
a(p_i)\longrightarrow0,\qquad\beta(p_i)\longrightarrow+\infty.
\end{gathered}
\tag{X124.20c}
$$

证明。若 $\sup_F\beta_F=M<\infty$，(X124.18b)先给 NC；推论124.8再给 Inj；此时 IX118.8 才给同原锥、同原单位静态复三能级，IX114.9 的反向结论给全部 $\beta_F=1$。反向的统一有限上界直接取一。因此无需另输入预算的数值一。

若某个 $\beta_F>1$，(X124.20a)排除有限上确界；定理124.10已在重构前证明的 NC 与 UF 等价于是给 $\inf_p d(p)=0$。对每个 $i$ 选实际 $p_i\in P$ 使 $d(p_i)<1/i$，并选 $q_i\in P\cap D_{p_i}$。IX114.4 的 $P$ 紧性给子列使 $p_i\to p\in P$、$q_i\to q\in P$。由于

$$
\max_{x\in D_{p_i}}\|x-q\|\le d(p_i)+\|q_i-q\|\longrightarrow0,
$$

这些实际完整球整体趋于 $\{q\}$。IX115.4 的原零闭图给 $q\in D_p$，而 $T_p(p)=1$ 给 $p\ne q$；这正是 IX115.5—115.6 保留的单点分支。最后 $0<2a(p_i)\le Ld(p_i)\to0$ 及 $\beta(p_i)=1/(2a(p_i))$ 给其余极限。极限标签本身仍有 $a(p)>0$、$\beta(p)<\infty$；没有把单个球的预算说成无穷。证毕。

此推论在出现偏离时强制产生实际整球塌缩，不断言存在具有 $\beta_F>1$ 的原 EB3+PR 模型。逐球各自有限也不等于统一有限；自动 NC 或自动 UF 仍须另证。

### 124.6 中文候选、三维几何与静态量子公理对应

**定义及应用 124.12（互易且不整体缩点的完整排除候选）。** 候选可用白话完整表述为：在同一个有限维实有序空间中，原态是严格正单位截出的整个紧基，纯态是它的全部极点，允许的数学二元测试是整个 $[0,u]$。用“在确认第一个纯态为一的所有原测试中，第二个态的最小读数”定义比较。要求每个纯态的全部零比较对象，包括混态，恰组成一个完整仿射闭三球；任意两个纯态的比较值交换端点后相同；并存在同一个正数，使所有这些实际完整三球在固定辅助尺下的直径都不小于它。

最后一条也可等价地改用预算白话表达：每张完整球上的全部取值在零到一之间的仿射面测试，都能正延拓到同一个原锥，且存在一个共同有限常数，控制所有这些延拓在整个原态域上的最优最大读数。只要求这个共同上界有限，不预先把它定为一；124.11使最优预算随后全部等于一。

这段候选没有先指定两个标签不能给出同一球，也没有先要求原正交对有第三个共同正交点。前者由124.8取得，后者及同锥同单位复三能级静态结构由124.10消费既有重构取得。仅说“每对都能比较、交换端点结果不变”不包含完整三球或 NC，因而不等于这段候选。

在所得静态表示中，排除一个秩一纯点后的整个支撑是二维复空间。在该支撑任取一组 Pauli 坐标，成熟的密度矩阵字典写成

$$
\rho(r)=\frac12(I_2+r\cdot\sigma),\qquad
r\in\mathbb R^3,\quad\|r\|_2\le1.
\tag{X124.21}
$$

所以这里的“三”准确指每个排除面的实仿射维数三；球面 $\|r\|_2=1$ 是该面的原纯点，球内是混态。这不是把环境维数设为三：全部原 $V$ 的实维数由重构给九，单体复 Hilbert 空间的维数为三。球图各自存在不先指定跨球的共同物理内积。

完整静态对应沿 [IX114.9、IX118.8及其112.8来源][Q124IX] 使用：

| 原对象或条件 | 同锥同单位表示中的对应 | 结论范围 |
| --- | --- | --- |
| 全部 $K$ 与凸混合 | 全部三阶迹一半正定矩阵及其凸混合 | 保留全部原混态 |
| 全部 $P$ | 全部复三维秩一投影，等价于复射线 | 单体静态纯态 |
| 整个 $\mathcal E$ 及 $u-f$ | 全部 $0\preceq E\preceq I_3$ 及 $I_3-E$ | 保留整个效应区间 |
| 原评价 $f(x)$ | $\operatorname{Tr}(E\rho)$ | Born 概率字典 |
| 全部原纯—纯比较 | $|v^{\ast}w|^2$ | PR 是端点互易 |
| 任意有限组 $f_j\in\mathcal E$、$\sum_j f_j=u$ | 全部有限 POVM：$E_j\succeq0$、$\sum_jE_j=I_3$ | 数学测量的完整对应 |
| 原正交三纯框架 | 三个互相正交的秩一投影及共同三结果效应 | 静态共同测量表达 |
| NC，等价地 UF 的共同有限预算 | 全部球预算为一及完整面测试的单位预算正延拓 | 在 EB3+PR 内的推论，不另输入数值一 |

此表的复数、Born 规则与有限数学测量来自同一个原 $C,u$ 的表示，没有换一个只拟合所选读数的新状态体。PR 也不使所有矩阵效应相互对易；它不陈述两个实际仪器先后执行的可交换性。

### 124.7 自动非塌缩仍缺的关系及物理边界

**约定 124.13（原目标的精确未决项）。** 上述结果给出

$$
\begin{gathered}
\mathrm{EB3}+\mathrm{PR}
+\text{实际重复标签}
\ \Longrightarrow\ \text{极端对偶单点零面}
\ \Longrightarrow\ \text{实际完整三球塌缩},\\
\mathrm{EB3}+\mathrm{PR}+\mathrm{NC}
\ \Longrightarrow\ \mathrm{Inj}
\ \Longrightarrow\ \text{可在NC仍保留时应用IX118.8}.
\end{gathered}
\tag{X124.22}
$$

这里第一行不以 NC 为前提；第二行的最后一步始终保留 NC，不能删成 Inj 单独重构。一般的极端单点零面障碍也没有消除全部可能的塌缩来源。

原 $\mathrm{EB3}+\mathrm{PR}\Rightarrow\mathrm{NC}$，等价地自动 UF，尚未证明。在这个固定原域内，124.10—124.11说明只要支付统一有限预算，无需指定上界一，就会支付原 $\mathrm{Pair}_{\perp}$、全部 $\beta=1$ 和静态复三能级；因此不能把 NC 或 UF 当作已从逐球三维或互易性自动取得的小条件。若原 $\mathrm{Pair}_{\perp}$ 失败，IX114.8 与 $\beta_F\ge1$ 给某球 $\beta_F>1$，124.11便给全局预算无界及带纯极限标签、实际纯塌缩点的整球列；这不提供一个实现其失败的原模型，也不构成原无条件 EB3+PR 任务的严格削弱。

IX114.4 已给 PR 下纯点紧性，IX115.4 已给闭图与上半连续，IX115.5 已给整球或单点的极限二择，IX115.6—115.8 已给正则区及全域有限预算的连续性判据；这些既有结果仍允许单点分支。上半连续只把极限点留在极限标签的完整球内，不把缩成一点的球放大回来。要从 EB3+PR 自动推出 NC 或 UF，仍须排除这种实际整球塌缩，或者另行证明同域等价条件；本章没有提供这一步。极端对偶单点零面存在、重复球存在及塌缩存在也均未被断言为已实现的原 EB3+PR 反模型。

所以原任务“EB3+PR 自动给原 $\mathrm{Pair}_{\perp}$，或构造保留同一有限维 $V,C,u$、全部 $K/P$、全效应及完整混合排除集的同域反模型”仍未完成，全 Pair 也未自动取得。没有逻辑独立性、最小性、全球原创或完整物理重构声明。

静态表示也没有提供在原物理来源上制备这些态、实现全部效应或 POVM、执行正投影／滤波或原生合法门词的方法。任意有限复合系统的联合态锥、纠缠输入、局部层析、全旁观者正性／CP、共同仪器、事件与记录，以及物理时钟、动力学、Hamiltonian、能量和数值 $\hbar$ 都各有未付桥梁。若原合同还要求同一个 $\Omega$、所有原合法门序列、每个中间切口及全部条件未来读出，这些全称量词不由单体静态字典消去。

### 124.8 来源与适用范围

本章数学归属为 `repo-derived` 的条件应用：将有限维对偶暴露点的显式混态构造、Straszewicz 逼近与孤立重复球的有限正分解连接起来，再把既有有限预算与非塌缩接口接到单位饱和。已有完整面分类、纯点暴露及复三能级分类各保留原归属；本章不将它们重证或计作新增分类。

| 已有来源 | 在本章中的准确作用 |
| --- | --- |
| IX114.1—114.2；IX116.1及VII103.2 | 完整原域、正维完整球、所有非空真面的穷尽及共同零确认；变维结论只用其变维接口 |
| IX114.3 | 原纯端点数值 PR 供应 PE；不要求 EB 的额外暴露公理 |
| IX114.4；IX115.4—115.5 | 仅在PR特例中使用纯点紧性、原闭图及准确的整球／单点极限二择 |
| IX114.5—114.6；IX115.1、115.3、115.6、115.8 | 相同球系数、尖锐预算、普遍直径估计及正则区；在重构前建立 NC 与原 UF 等价，再接有限预算即单位饱和及偏离时的实际塌缩 |
| IX116.2 | 重复标签的孤立双球块，尤其球面纯点只属于本侧一张完整球 |
| Straszewicz 有限维定理；Bru—de Siqueira Pedra §4.3 | 紧对偶基的每个极点可用暴露点逼近；不用无限维推广 |
| 有限维分离、Minkowski及Carathéodory定理 | 实际原锥成员身份、紧对偶基极点的有限正分解 |
| IX118.8第2、4项 | 在 Inj 与正直径下界均已支付后，取得同一原锥、同一原单位的静态表示 |
| IX114.8—114.9及其112.8来源 | 原Pair、全部单位预算与静态表示的等价；完整反向量子模型及数学POVM字典 |

[Bru—de Siqueira Pedra][Q124BP]，*Weak$^{\ast}$ Hypertopologies with Application to Genericity of Convex Sets*，arXiv:2103.08446v1，§4.3，PDF第31页第二段，直接明述这里所用的有限维 Straszewicz 稠密性。其参考文献[20]追溯 Straszewicz 原论文；本章不声称已核对原论文页码。所核对版本的 PDF SHA256 为 `3788b1f70dd7a73a76908c0efa741dece05b628e9544a22de866810e9845fddd`。

X121—X123 的实际种子、最大宽共同接触、共同法向斜率与六整球测试边界均有各自前件；本章不继承它们的九维、种子或 Inj 输入，也不重述其共同切向材料。[132章][Q124LP] 处理移动标签的共同正提升与有限源测试障碍，不承担本章对偶暴露点到原混态的构造。上述区分只是适用对象及来源边界，不给任何未付前件补证。

[Q124IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "114.1—114.9、115.1—115.8、116.1—116.2及118.8：完整原域与本章实际消费的条件结论。"
[Q124VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "103.2：允许正维变维排除球的原真面分类；经IX116.1复用。"
[Q124LP]: QUANTUM_ORIGIN_LOCAL_PURE_LIMIT_AND_COMMON_POSITIVE_LIFTS_CONTINUATION.md "132：有限共同源测试的正提升障碍及返回球维数。"
[Q124BP]: https://arxiv.org/pdf/2103.08446v1 "J.-B. Bru and W. de Siqueira Pedra；§4.3，PDF31：有限维Straszewicz定理的明确陈述。"

## 追加锚（本行以下为增补区）

## 125. 旧完整球的共同近零确认与固定球心的真零稳定性

**定义 125.1（完整原域、共同读数与球心）。** 保留 [IX114.1][Q125IX] 的同一个非零有限维实空间 $V$、闭尖生成凸锥 $C$ 及在 $C\setminus\{0\}$ 上严格正的 $u\in V^{\ast}$。始终取全部

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^{\ast}},\\
F_a=\{e\in\mathcal E:e(a)=1\},\qquad
T_a(x)=\min_{e\in F_a}e(x)\quad(a\in P,\ x\in K),\\
D_a=\{x\in K:T_a(x)=0\}.
\end{gathered}
\tag{X125.1}
$$

这里的第二变量包括所有混态，确认族使用整个原效应区间。假设 EB3 与 PR：每个完整 $D_a$ 仿射同构于整个闭三球，且 $T_a(b)=T_b(a)$ 对全部原纯点 $a,b$ 成立。PR 只交换纯端点，不是顺序测量交换。固定辅助欧氏范数，令

$$
M=\max_{e\in\mathcal E}\|e\|_{\ast}<\infty,
\qquad c_p=\text{完整球 }D_p\text{ 的唯一对称中心}.
\tag{X125.2}
$$

此范数只承担距离与拓扑，不是共同物理内积。按 IX114.1、114.4，$K,P,\mathcal E$ 均紧，$F_a$ 非空紧；按 IX114.4，固定第一参数的 $T_a$ 在整个 $K$ 上有共同 Lipschitz 常数 $M$。

对非空、紧、凸、中心对称的 $G\subset K$，中心记为 $c$，定义同一效应的整集最优上读数

$$
\kappa_G(a)=\min_{e\in F_a}\max_{x\in G}e(x).
\tag{X125.3}
$$

紧性与配对连续性保证最小值、最大值均达到。另记 $Z(e)=\{x\in K:e(x)=0\}$。只复用 IX114.2 的准确原面接口：每个完整 $D_a$ 是非单点紧暴露极大真面；其球面恰为 $P\cap D_a$；存在 $h_a\in F_a$ 使 $Z(h_a)=D_a$；所有非空真面均为原纯单点或一张完整排除球。不输入该分类最后一项的全 Pair 前件，也不输入 Inj、least 确认效应或全局球族连续性。

**定理 125.2（同一原确认效应在整块旧混态球上趋零）。** 在定义125.1的完整 EB3+PR 域中，任取 $p\in P$ 及原纯列 $a_i\to p$，置 $G=D_p$。则

$$
T_a(c)\le\kappa_G(a)\le2T_a(c)
\quad(a\in P)
\tag{X125.4}
$$

对定义125.1中的任意中心对称 $G$ 成立；对上述固定完整 $G=D_p$，有

$$
\kappa_{D_p}(a_i)\longrightarrow0,
\qquad T_{a_i}(c_p)\longrightarrow0,
\qquad \sup_{x\in D_p}T_{a_i}(x)\longrightarrow0.
\tag{X125.5}
$$

具体地，若实际完整球 $G_i=D_{a_i}$ 趋于 $G$，则

$$
\kappa_G(a_i)\le M d_H(G_i,G).
\tag{X125.6}
$$

若实际完整球塌缩为 $G_i\to\{q\}$，则 $q\in P\cap G$。记 $\delta_i=d_H(G_i,\{q\})$，对充分大的 $i$，存在同一张 $e_i\in F_{a_i}$，使

$$
\begin{gathered}
\max_{x\in G}e_i(x)
\le M\bigl(\|a_i-p\|+\delta_i\bigr),\\
e_i(c_p)\le\frac M2\bigl(\|a_i-p\|+\delta_i\bigr).
\end{gathered}
\tag{X125.7}
$$

这些结论不以 NC、UF、Inj 或全域 least 为前提；尤其不要求对旧球的不同输入更换效应。

证明。先记录推导中使用的两个初等仿射步骤，它们不作为独立的新分类结果。对任何原纯 $a$、原混态 $x$，若 $t=T_a(x)<1$，则每个达到此最小值的 $e\in F_a$ 都满足 $\min_K e=0$。否则令 $m=\min_K e>0$。有 $m\le t<1$，且

$$
\widetilde e=\frac{e-mu}{1-m}\in\mathcal E,
\qquad\widetilde e(a)=1,
\qquad\widetilde e(x)=\frac{t-m}{1-m}<t,
\tag{X125.8}
$$

矛盾。效应资格在整个原 $K$ 上由 $0\le e-m\le1-m$ 给出，再经同一 $u$ 齐次化到整个 $C$；没有调用面效应延拓。

其次，若 $G$ 关于 $c$ 对称，则 $x\in G$ 时 $2c-x\in G$。每张原效应非负且仿射，因而

$$
0\le e(x)\le e(x)+e(2c-x)=2e(c).
\tag{X125.9}
$$

因为 $c\in G$，先对每张 $e$ 使用 $e(c)\le\max_Ge$ 再取最小值得 (X125.4) 的左侧；取达到 $T_a(c)$ 的效应并用 (X125.9)，得右侧。此处没有交换极小与极大，也没有使用 minimax 等式。

若 $G_i\to G$，从 IX114.2 取原 $h_i\in F_{a_i}$，使 $h_i|_{G_i}=0$。对每个 $x\in G$，取 $y\in G_i$ 达到到 $G_i$ 的距离。全效应的统一范数界给

$$
0\le h_i(x)=h_i(x)-h_i(y)
\le M\|x-y\|\le M d_H(G_i,G).
$$

同一 $h_i$ 对整个 $G$ 有效，得到 (X125.6)。

现在设实际 $G_i\to\{q\}$。由 [IX115.4—115.5][Q125IX]，$q\in P\cap G$。在旧完整球取对径纯点 $r=2c_p-q\in P\cap G$。PR 只用于这个纯点 $r$ 与 $a_i,p$，并结合固定 $T_r$ 在整个 $K$ 上的 Lipschitz 界，给

$$
0\le T_{a_i}(r)=T_r(a_i)
\le M\|a_i-p\|,
\qquad T_r(p)=T_p(r)=0.
\tag{X125.10}
$$

右端趋零，所以充分大时 $T_{a_i}(r)<1$。取 $e_i\in F_{a_i}$ 达到该最小值。由 (X125.8) 的论证，存在 $z_i\in K$ 使 $e_i(z_i)=0$；因为它确认 $a_i$，有 $z_i\in G_i$。于是

$$
\|z_i-q\|\le\delta_i,
\qquad0\le e_i(q)\le M\delta_i,
\qquad e_i(r)=T_{a_i}(r)\le M\|a_i-p\|.
\tag{X125.11}
$$

用 $q+r=2c_p$ 及 (X125.9)，得到

$$
\max_Ge_i\le2e_i(c_p)=e_i(q)+e_i(r)
\le M\bigl(\delta_i+\|a_i-p\|\bigr),
$$

即 (X125.7)。这里只知道 $Z(e_i)$ 是原 $K$ 的一个非空真面，且包含于 $G_i$；它可以是原纯单点。如它含两个点，原面分类与完整球极大性才使它等于 $G_i$，不能事先作此替换。

最后处理任意 $a_i\to p$。非空紧子集的 Hausdorff 紧性使任一子列的 $G_i\subset K$ 可再取收敛子列。IX115.5 准确给该极限只有 $G$ 或 $\{q\}$ 两种。前者由 (X125.6)，后者由 (X125.7)，都使 $\kappa_G(a_i)\to0$。若原序列的 $\kappa_G$ 不趋零，取有统一正下界的子列就与这两种情况矛盾。因此第一个极限成立。再用

$$
0\le T_{a_i}(c_p)\le\kappa_G(a_i),
\qquad0\le\sup_{x\in G}T_{a_i}(x)\le\kappa_G(a_i)
$$

得到其余极限。第二个不等式来自同一张达到 $\kappa_G$ 的原效应，而不是将 PR 外推成混态互易或把 $T_a$ 当作仿射函数。证毕。

**推论 125.3（确认纤维极限必遇旧球完整零确认面）。** 在同一完整 EB3+PR 域中，沿用 IX120.1 的完整零确认族

$$
\mathcal A_p=\{e\in F_p:e|_{D_p}=0\}.
\tag{X125.12}
$$

它是 $F_p$ 的非空紧暴露真面，并且

$$
\mathcal A_p=\{e\in F_p:e(c_p)=0\},
\qquad \forall e\in\mathcal A_p:\quad Z(e)=D_p.
\tag{X125.13}
$$

若 $a_i\to p$ 且非空紧集 $F_{a_i}$ 在 $\mathcal E$ 中 Hausdorff 收敛于 $A$，则

$$
A\subseteq F_p,
\qquad A\cap\mathcal A_p\ne\varnothing.
\tag{X125.14}
$$

即使没有预先选定这样的极限，也有

$$
\min_{e\in F_{a_i}}\operatorname{dist}_{\ast}(e,\mathcal A_p)
\longrightarrow0.
\tag{X125.15}
$$

证明。IX114.2 给 $\mathcal A_p$ 非空；紧性由闭条件给出。原效应在 $D_p$ 上非负，(X125.9) 给 $e(c_p)=0$ 当且仅当在整个 $D_p$ 上为零。评价 $e\mapsto e(c_p)$ 在凸集 $F_p$ 上的最小值为零，最小面便是 $\mathcal A_p$；$u\in F_p$ 而 $u(c_p)=1$，所以它是暴露真面。对 $e\in\mathcal A_p$，$e(p)=1$ 保证 $e\ne0$，$Z(e)$ 是包含 $D_p$ 的原真面。IX114.2 的极大真面性质因而给 $Z(e)=D_p$。这里非零性、全域正性与完整球极大性均不可省略。

对任意 $f\in A$，Hausdorff 收敛提供 $f_i\in F_{a_i}$ 使 $f_i\to f$。由 $f_i(a_i)=1$ 得 $f(p)=1$，故 $A\subseteq F_p$。再取 $e_i\in F_{a_i}$ 达到 $\kappa_{D_p}(a_i)$。紧 $\mathcal E$ 中任一收敛子列 $e_i\to e$，均由定理125.2 得

$$
e(p)=1,\qquad e|_{D_p}=0.
$$

所以 $e\in\mathcal A_p$；若存在指定的 Hausdorff 极限 $A$，同一子列还给 $e\in A$，证明交非空。所有这样的聚点都在紧集 $\mathcal A_p$，故这些 $e_i$ 到它的距离趋零，得到 (X125.15)。这不声称 $A=F_p$、$A\subseteq\mathcal A_p$，也不提供趋于预先指定效应的选择或连续选择。证毕。

**定义 125.4（旧球心的实际零集稳定性）。** 条件 CS 为

$$
\forall p\in P\ \forall(a_i)\subset P:\quad
 a_i\to p\ \Longrightarrow
 \operatorname{dist}(c_p,D_{a_i})\longrightarrow0.
\tag{X125.16}
$$

球心始终取固定旧球 $D_p$ 的 $c_p$。此处距离的对象是同标签完整 $D_{a_i}$，不是某张效应的零集。NC 保留124.1的原义 $\inf_p\operatorname{diam}D_p>0$；UF 保留 IX115.8 的原义 $\sup_p\beta_{D_p}<\infty$，其中 $\beta_{D_p}=1/(2a_{D_p})$ 是 IX114.5—114.6 的原全锥正延拓预算。

**定理 125.5（CS 恰是既有 UF 的单点几何测试）。** 在同一完整 EB3+PR 域中，对每个固定 $p$，(X125.16) 中以该 $p$ 为极限的条件成立，当且仅当 $a\mapsto D_a$ 在 $p$ 处 Hausdorff 连续。因而

$$
\mathrm{CS}\quad\Longleftrightarrow\quad\mathrm{UF}
\quad\Longleftrightarrow\quad\mathrm{NC}.
\tag{X125.17}
$$

并且 CS 可代入124.10，得到同原锥、同原单位的完整复三能级静态表示及该定理的全部等价条件。

证明。若整球映射在 $p$ 连续，由 $c_p\in D_p$ 有

$$
\operatorname{dist}(c_p,D_{a_i})\le d_H(D_p,D_{a_i})\to0.
$$

反过来，若在 $p$ 不连续，可选 $a_i\to p$，使 $d_H(D_{a_i},D_p)$ 有统一正下界；Hausdorff 紧性给收敛子列。IX115.5 排除其他极限，且上述正下界排除极限为 $D_p$，所以只能有 $D_{a_i}\to\{q\}$，$q\in P\cap D_p$。旧球正维，中心 $c_p$ 是两个不同对径纯点的中点，因而不是原纯点；特别地 $q\ne c_p$。距离对 Hausdorff 收敛连续，故

$$
\operatorname{dist}(c_p,D_{a_i})\longrightarrow\|c_p-q\|>0,
$$

与固定 $p$ 的 CS 矛盾。全域连续与 UF 的等价直接消费 IX115.8；UF 与 NC 的等价及静态表示直接消费124.10，不重证其标签单射桥、IX116.2 的重复球二分或 IX118.8 的静态分类。证毕。

定理125.2无条件供应的是 $T_{a_i}(c_p)\to0$；CS 要求的是到实际完整零集的几何距离趋零。两种量不能混同。自动 $\mathrm{EB3}+\mathrm{PR}\Rightarrow\mathrm{CS}$，等价地自动 UF，仍未证明；满足全部同域前件而使 CS 失败的模型亦未构造。CS 只把既有整球稳定要求化为每个固定旧球心的一点测试，没有取得独立假设数减少的结论，也不证明独立性、最小性或严格更弱的公理包。

**命题 125.6（原复三能级中任意效应零面误差界的失败）。** 在完整复三能级模型中，取两两正交的秩一投影 $p,r,q$，故 $p+r+q=I_3$。对 $0<\varepsilon<1$，令

$$
A_{\varepsilon}=p+\varepsilon r,
\qquad c=\frac{r+q}{2}.
\tag{X125.18}
$$

以 $A_{\varepsilon}$ 同时表示原效应 $\rho\mapsto\operatorname{Tr}(A_{\varepsilon}\rho)$。则

$$
\begin{gathered}
A_{\varepsilon}\in F_p,\qquad
Z(A_{\varepsilon})=\{q\},\qquad
A_{\varepsilon}(c)=\varepsilon/2,\\
\operatorname{dist}_1(c,Z(A_{\varepsilon}))=1,\qquad
c=c_p\in D_p,\qquad
\max_{x\in D_p}A_{\varepsilon}(x)=\varepsilon.
\end{gathered}
\tag{X125.19}
$$

这里 $\|X\|_1=\operatorname{Tr}|X|$ 为未除以二的迹范数。于是不存在趋零模 $\omega(t)\to0$（$t\downarrow0$），能对原模型的所有确认效应及所有原态保证

$$
\operatorname{dist}_1(x,Z(A))
\le\omega\bigl(\operatorname{Tr}(Ax)\bigr),
\tag{X125.20}
$$

即使只要求 $A\in F_p$、$\min_KA=0$、$\max_KA=1$ 且固定 $x=c_p$。

证明。$A_{\varepsilon}$ 的特征值为 $1,\varepsilon,0$，所以 $0\preceq A_{\varepsilon}\preceq I_3$，并确认 $p$。若正半定迹一矩阵 $\rho$ 满足 $\operatorname{Tr}(A_{\varepsilon}\rho)=0$，在 $p,r,q$ 的正交基中，$\rho_{pp}+\varepsilon\rho_{rr}=0$ 迫使两个非负对角元均为零。正半定性给 $|\rho_{jk}|^2\le\rho_{jj}\rho_{kk}$，故对应行列也全为零，余下迹一条件给 $\rho=q$。反向 $A_{\varepsilon}(q)=0$，因此零面恰为单点。

旧完整 $D_p$ 是支撑在 $p^{\perp}$ 上的全部密度矩阵三球，中心为 $(r+q)/2$；这是124.10与 IX118.8 的完整反向字典。直接计算给 $A_{\varepsilon}(c)=\varepsilon/2$。矩阵 $c-q=(r-q)/2$ 的特征值为 $1/2,-1/2,0$，所以其迹范数为一。在整个 $D_p$ 上，效应值为 $\varepsilon\operatorname{Tr}(r\rho)$，最大值为 $\varepsilon$。代入 (X125.20) 便要求 $1\le\omega(\varepsilon/2)\to0$，矛盾。证毕。

该例的标签始终为同一个 $p$，完整 $D_p$ 固定，且这个量子模型满足 CS、UF 与 NC。它反驳的是对任意单张效应零面所要求的统一模，不能作为 EB3+PR 的反模型，也不能反驳只涉及同标签完整 $D_a$ 的 CS。零面取零与完整排除集不可互换；把 (X125.20) 添加为目标理论的必要条件会排除目标量子模型本身。

**约定 125.7（完整候选、几何与静态公理字典）。** 保留的条件候选可完整说成：在同一个有限维原态锥和原单位上，使用全部原纯态、全部混态与全部零一效应；确认一个纯态时能够完全排除的全部态恰成一颗实心三球；交换两个纯端点，最优确认读数不变；再要求纯标签靠近时，新完整排除球到固定旧球心的距离趋零。最后一项是 CS，按定理125.5仍是一项未由前两项推出的稳定要求。这与124.10的 EB3+PR+UF 候选有相同条件强度，没有每轮都减少假设的结论。

几何上，塌缩分支的旧球有一对对径纯点 $q,r$。在 $r$ 处最优的确认效应必须在新完整球某点取零；新球若缩到 $q$，这张同一效应在 $q$ 与 $r$ 都近零。仿射性与非负性经球心控制整颗旧球，包括全部混态。然而该效应仍可只在新球的一个点取零，所以这幅图没有把球心放回新完整球。

只有额外支付 CS，才通过定理125.5和124.10消费既有静态重构，取得实线性双射 $\Phi:H_3(\mathbb C)\to V$，满足 $\Phi(\operatorname{Herm}_+(\mathbb C^3))=C$、$u(\Phi X)=\operatorname{Tr}X$。其完整对应为：

| 原对象或关系 | 同原锥、同原单位的矩阵表示 |
| --- | --- |
| 全部 $K$ 与全部 $P$ | 全部三阶密度矩阵 $\rho$；全部秩一投影 $p=vv^{\ast}$，$v^{\ast}v=1$ |
| 全效应 $\mathcal E$ 与确认族 $F_{\Phi p}$ | 全部 $0\preceq E\preceq I_3$；其中 $Ep=p$ 的全部效应 |
| 原全混态最优读数 $T_{\Phi p}(\Phi\rho)$ | $\operatorname{Tr}(p\rho)$；纯对为 $|v^{\ast}w|^2$，对端点交换对称 |
| 完整 $D_{\Phi p}$ 与其球心 | 全部满足 $\rho p=0$ 的密度态三球；球心为 $\Phi((I_3-p)/2)$ |
| CS，等价地 UF 或 NC | 既有全部球单位预算、Pair 及同原静态复三能级条件类 |
| 数学共同三结果与数学 POVM | 正效应之和等于同一个 $I_3$；不自动取得实际调用这些仪器的能力 |

整个环境的实维数九及单体复 Hilbert 维数三是条件重构的结果；辅助范数没有预付共同物理尺。原物理来源、实际原操作、仪器、事件和记录、任意有限复合及纠缠输入、全旁观者兼容与 CP、动力学、物理钟、能量和 $\hbar$ 仍各有未付桥梁，按124.7保留其原完整量词。

**约定 125.8（数学归属与来源范围）。** 本章承重组合为 `repo-derived`：把非平凡最优确认的全域取零、旧球对径控制与 IX115.5 的准确极限二择连接，得到整块固定旧混态球的同一近零效应、确认纤维极限约束，并将剩余稳定要求准确定位为 CS。紧性、极值达到、仿射归一与中心反射只是成熟有限维工具，不作为新的独立发现。IX114.2—114.4、IX115.4—115.8、IX116.2、IX118.8 与124.10—124.11保留原假设与归属；共同完整零确认、整球连续的既有等价条件和静态分类均按原结果复用。命题125.6仅界定从效应小读数到实际零集距离的工具边界。[132章][Q125LP]研究的移动正零泛函提升与有限共同源误差障碍，保留其单标签、混极限及源半范数条件，不提供本章未付的 CS。

[Landsman，§1.3][Q125L]的完整仿射效应最小确认及其对称性，提供相应成熟概念；将其 $p(\rho,\sigma)$ 对应为这里的 $T_{\sigma}(\rho)$。其第2节重构另有 uniform Poisson、two-sphere 等公理，未作为本章 EB3+PR 的后果使用。[Janotta—Gogolin—Barrett—Brunner，§2.1及§3.1][Q125J]提供完整仿射效应区间及其多边形实例；其复合与非局域结论未进入本章证明，一维排除边也不替代 EB3。本章不主张全球原创、历史优先权、独立性、最小性或完整物理重构；自动 UF 与同域坏模型仍为上述明确的未解问题。

[Q125IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.4：完整域、完整面、严格暴露与纯点紧性；IX115.4—115.8：闭图、准确极限二择及UF；IX116.2与IX118.8：重复块及条件静态重构。"
[Q125LP]: QUANTUM_ORIGIN_LOCAL_PURE_LIMIT_AND_COMMON_POSITIVE_LIFTS_CONTINUATION.md "132：移动正零泛函的单位控制与有限共同源提升障碍；其局部前件不替代CS。"
[Q125L]: https://arxiv.org/src/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability, §1.3与第2节；Rev. Math. Phys. 9 (1997), 29–58，DOI 10.1142/S0129055X97000038；所引原文为arXiv v2作者源码。"
[Q125J]: https://arxiv.org/html/1012.1215v3 "P. Janotta, C. Gogolin, J. Barrett and N. Brunner, Limits on non-local correlations from the structure of the local state space, §2.1及§3.1；New J. Phys. 13 (2011), 063024，DOI 10.1088/1367-2630/13/6/063024。"

## 追加锚（本行以下为增补区）

## 126. 实际整球塌缩的固定边整行约束与唯一确认分支的单位饱和

**定义 126.1（完整原域、实际塌缩及固定边面）。** 设 $V\ne0$ 为有限维实空间，$C\subset V$ 为闭、尖、生成凸锥，$u\in V^{\ast}$ 在 $C\setminus\{0\}$ 上严格正。保留同一个原载体上的全部对象

$$
\begin{gathered}
C^{\ast}=\{h\in V^{\ast}:h|_C\ge0\},\qquad
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^{\ast}},\\
F_p=\{e\in\mathcal E:e(p)=1\},\qquad
T_p(x)=\min_{e\in F_p}e(x)\quad(p\in P,\ x\in K),\\
D_p=\{x\in K:T_p(x)=0\},\qquad
\mathcal A_p=\{e\in F_p:e|_{D_p}=0\}.
\end{gathered}
\tag{X126.1}
$$

第二变量遍历所有原混态；效应和确认族均不缩减。始终假设

$$
\mathrm{EB3}:\quad D_p\simeq_{\rm aff}\overline B^3\quad(p\in P),
\qquad
\mathrm{PR}:\quad T_p(s)=T_s(p)\quad(p,s\in P).
\tag{X126.2}
$$

PR 仅交换两个纯比较端点。固定一个辅助欧氏范数，记其 Hausdorff 距离为 $d_H$，并置 $M=\max_{e\in\mathcal E}\|e\|_{\ast}$。该范数只用于拓扑与估计，不指定共同物理内积。称

$$
p_i\in P,\qquad p_i\longrightarrow p\in P,\qquad
D_{p_i}\longrightarrow\{q\}
\tag{X126.3}
$$

为一次实际整球塌缩。按 [IX115.4—115.5][Q126IX]，必有 $q\in P\cap D_p$、$q\ne p$。对这条固定原正交边定义

$$
J(p,q)=\{e\in\mathcal E:e(p)=1,\ e(q)=0\}.
\tag{X126.4}
$$

它是原效应区间的非空紧凸面。非空性来自 $q\in D_p$ 及原最小值达到。

以下只复用既有接口。[IX114.1—114.4][Q126IX] 给 $K,P,\mathcal E$ 紧、最小值达到，以及每个原纯点 $s$ 都有仅在 $s$ 取一的原确认效应；后者不要求 Inj。固定 $T_s$ 在整个 $K$ 上为 $M$-Lipschitz。完整面接口给每个 $D_s$ 为暴露极大真面，$\mathcal A_s\ne\varnothing$，且任一完整球 $H$ 的球面恰为 $P\cap H$；不同完整球至多交于一个原纯点。其全效应原合同见 [ExclusionBallFaces.exclusion_ball_faces][Q126Faces]，这里只使用共同暴露与全部真面分类两项，不使用另带全 Pair 前件的末项。

[IX114.5—114.6][Q126IX] 给每个实际完整球 $H$ 唯一的共同系数和原正延拓预算：对任意完整球图 $b_H:\overline B^3\to H$，

$$
\begin{gathered}
0<a_H\le\tfrac12,\qquad \beta_H=\frac1{2a_H},\\
T_{b_H(w)}(b_H(z))=1-a_H+a_Hw\cdot z
\quad(w\in S^2,\ z\in\overline B^3).
\end{gathered}
\tag{X126.5}
$$

此式包括整个球内部的混态，但不宣称 $T_{b_H(w)}$ 在全 $K$ 仿射。

**定理 126.2（实际塌缩迫使全部纯输入的固定边达到）。** 在定义126.1的完整 EB3+PR 域中，若发生 (X126.3)，则对每个原纯点 $s\in P$，

$$
T_p(s)=\min_{e\in J(p,q)}e(s).
\tag{X126.6}
$$

即 $\forall s\in P\ \exists e_s\in J(p,q)$ 达到该读数；不要求一个效应同时达到所有纯输入。

证明。因 $J(p,q)\subseteq F_p$，右侧不小于左侧。先固定 $s\ne p$。严格暴露给 $T_p(s)<1$。PR 和固定 $T_s$ 的连续性给

$$
T_{p_i}(s)=T_s(p_i)\longrightarrow T_s(p)=T_p(s)<1.
\tag{X126.7}
$$

故充分大的 $i$ 有 $t_i:=T_{p_i}(s)<1$。取达到此最小值的原 $e_i\in F_{p_i}$。

使用 [125.2证明中的全域归一化步骤][Q126X]：若 $m_i:=\min_K e_i>0$，则 $m_i\le t_i<1$，且

$$
\widetilde e_i=\frac{e_i-m_i u}{1-m_i}\in F_{p_i},\qquad
\widetilde e_i(s)=\frac{t_i-m_i}{1-m_i}<t_i,
\tag{X126.8}
$$

矛盾。因此 $m_i=0$，存在真实 $z_i\in K$ 使 $e_i(z_i)=0$。因 $e_i$ 确认 $p_i$，这个同一零点属于实际完整 $D_{p_i}$。整球塌缩因而给 $z_i\to q$，不是只给某个局部球片上的近零点。

紧 $\mathcal E$ 中取子列 $e_i\to e_s$。由 $e_i(p_i)=1$、$e_i(z_i)=0$ 及 (X126.7)，得到

$$
e_s(p)=1,\qquad e_s(q)=0,\qquad e_s(s)=T_p(s).
$$

故 $e_s\in J(p,q)$ 并给出反向不等式。

当 $s=p$，直接用 $J(p,q)\ne\varnothing$：其中每张效应在 $p$ 的读数都是 $1=T_p(p)$。这里无需把趋于一的值误当作严格小于一。对 $s\ne p$，收敛 $p_i\to p$ 本身保证尾部 $p_i\ne s$；即使初始有限多个指标满足 $p_i=s$，也不进入上述严格小于一的尾部。整个序列恒等于某个 $s\ne p$ 与标签收敛不相容。证明没有加入标签互异条件或 Inj。证毕。

(X126.6) 是全部纯输入的行约束。一般混态上的两个下包络是否相同，不由逐纯点各自的达到自动推出；不同纯点的最优效应可以不同。

**定理 126.3（每张包含极限标签的完整球上的同效应达到与反向三点刻度）。** 在定理126.2的前件下，任一实际完整球 $H$ 若包含 $p$，则存在一张原效应 $e_H\in J(p,q)$，使

$$
e_H(x)=T_p(x)\quad(x\in H).
\tag{X126.9}
$$

特别地，$p\in D_q$。在完整球图 $b_H$ 中取 $H=D_q$、$p=b_H(w)$、$r=b_H(-w)$，$\|w\|=1$。可取 $h=u-e_H$，满足

$$
\begin{gathered}
h\in J(q,p),\qquad
h(b_H(z))=a_H(1-w\cdot z)\quad(z\in\overline B^3),\\
(h(q),h(p),h(r))=(1,0,2a_H),\qquad
(e_H(p),e_H(q),e_H(r))=(1,0,1-2a_H),\\
Z_K(h):=K\cap\ker h=\{p\},\qquad
\max_{k\in J(q,p)}k(r)=2a_{D_q}.
\end{gathered}
\tag{X126.10}
$$

此处 $a_H=a_{D_q}$，不能以 $a_{D_p}$ 替换。

证明。因 $p$ 是原纯点并属于面 $H$，它在该完整球的球面。写 $p=b_H(w)$，令 $r_H=b_H(-w)$ 为同一球的实际对径原纯点。由定理126.2，在 $r_H$ 选 $e_H\in J(p,q)$ 达到 $T_p(r_H)$。在整个 $H$，$e_H\ge T_p$；由 (X126.5)，后者在这张球上仿射。因此

$$
d(z)=e_H(b_H(z))-(1-a_H+a_Hw\cdot z)
$$

是闭单位球上的非负仿射函数，且在 $w,-w$ 均为零。它在中点 $0$ 为零。写 $d(z)=c+t\cdot z$，则 $c=0$，在 $z,-z$ 均非负迫使 $t=0$。故 $d\equiv0$，得到包括所有混态的 (X126.9)。每张 $H$ 可使用自己的 $e_H$，没有全局共用效应的断言。

由 $q\in D_p$，原补效应的零一对称性给 $p\in D_q$。取 $H=D_q$ 并按前段选 $e_H$。因 $e_H(p)=1$、$e_H(q)=0$，其补 $h$ 确认 $q$ 并零于 $p$。(X126.9) 与 (X126.5) 立即给球上的仿射式及两组三点读数。$h\in F_q$ 使它在全 $K$ 的零集包含于完整 $D_q=H$，而所列球上仿射式只在 $z=w$ 为零，因为 $a_H>0$。所以 $Z_K(h)=\{p\}$；这里不需 Inj，也没有把球上零集未经检验地外推到全 $K$。

任一 $k\in J(q,p)$ 的补效应属于 $J(p,q)\subseteq F_p$，故

$$
1-k(r)\ge T_p(r)=1-2a_H.
$$

于是 $k(r)\le2a_H$，而上述 $h$ 达到等号。紧性保证这里确为最大值。证毕。

**定理 126.4（整个移动确认面的统一旧球斜率约束）。** 在定义126.1及实际塌缩 (X126.3) 下，固定旧完整球

$$
G=D_p=b(\overline B^3),\qquad q=b(v),\quad \|v\|=1,\qquad
\delta_i=d_H(D_{p_i},\{q\}).
$$

对每个 $i$、每张原 $f\in F_{p_i}$，令 $m=\min_K f$，并唯一写

$$
(f-mu)(b(z))=\alpha+t\cdot z.
\tag{X126.11}
$$

则统一有

$$
\begin{gathered}
0\le\|t\|\le\alpha\le1,\qquad
\alpha+\|t\|\le1-m,\\
0\le\alpha+t\cdot v\le M\delta_i,\qquad
\|t+\alpha v\|^2\le2M\delta_i.
\end{gathered}
\tag{X126.12}
$$

因此对整个移动确认面同时有

$$
\sup_{f\in F_{p_i}}\ \sup_{\|z\|\le1}
\left|f(b(z))-[m+\alpha(1-v\cdot z)]\right|
\le\sqrt{2M\delta_i},
\tag{X126.13}
$$

其中 $m,\alpha$ 随该同一 $f$ 取值；$M$ 不随 $i,f$ 变化。不需要 Inj 或 $p\in P_0$。

证明。若 $f$ 在 $K$ 恒定，因 $f(p_i)=1$ 及 $K$ 张成 $V$，有 $f=u$。此时 $m=1$、$\alpha=t=0$，全部式子成立。

若 $f$ 非恒定，则 $0\le m<1$，因为其全 $K$ 最大值在 $p_i$ 达到一。原效应

$$
\widehat f=\frac{f-mu}{1-m}\in F_{p_i}
$$

在某个真实 $z_i\in K$ 取零，所以 $z_i\in D_{p_i}$，且 $f(z_i)=m$。因此

$$
0\le f(q)-m=f(q)-f(z_i)
\le\|f\|_{\ast}\|q-z_i\|\le M\delta_i.
\tag{X126.14}
$$

在整颗旧球上，$0\le f-m\le1-m$。仿射式 (X126.11) 的球上最小、最大值分别为 $\alpha-\|t\|$、$\alpha+\|t\|$，给第一行约束；在 $q=b(v)$ 评价给第二行首式。最后

$$
\begin{aligned}
\|t+\alpha v\|^2
&=\|t\|^2+2\alpha\,t\cdot v+\alpha^2\\
&\le2\alpha(\alpha+t\cdot v)\le2M\delta_i,
\end{aligned}
\tag{X126.15}
$$

使用 $\alpha\ge0$ 及 $\alpha\le1$。仿射式与 $m+\alpha(1-v\cdot z)$ 的差正是 $(t+\alpha v)\cdot z$，Cauchy–Schwarz 给 (X126.13)。估计对每张 $f$ 成立且右端相同，故可取整个确认面的上确界。证毕。

这约束同一个移动标签的所有实际确认效应在同一旧球上的限制。若从逐面延拓取得两个确认效应列，其旧球斜率分别收敛到 $t_1,t_2$，则 (X126.12) 迫使两者都属于 $\mathbb R_{\le0}v$；两个非零极限斜率若不在同一射线上，就排除这次塌缩。只有当那些原延拓确实还满足 $f(p_i)=1$ 时才能应用此检验，正延拓本身不供应这项资格。

**定义 126.5（唯一完整零确认分支及原法向坐标）。** 以下另加

$$
\mathrm{Inj}:\quad D_s=D_t\Longrightarrow s=t,
\qquad
p\in P_0:=\{s\in P:\mathcal A_s\text{ 为单点}\}.
\tag{X126.16}
$$

写 $\mathcal A_p=\{e_p\}$、$g=u-e_p$，并选完整旧球图 $G=D_p=b(\overline B^3)$。这不是 $F_p=\{e_p\}$：整个 $F_p$ 始终保留，且包含 $u$。

按 [IX120.2、120.8、120.10—120.13][Q126IX]，令 $N_p=\{n\in C^{\ast}:n(p)=0\}$，则限制 $\operatorname{span}N_p\to\operatorname{Aff}(G)$ 是同构，$g\in\operatorname{ri}N_p$，$g>0$ 于 $K\setminus\{p\}$。存在唯一原线性 $H:V\to\mathbb R^3$，其各分量属于 $\operatorname{span}N_p$，且

$$
H(p)=0,\qquad H(b(z))=z,\qquad g(b(z))=1.
\tag{X126.17}
$$

对每个已经属于原正锥的 $n=\alpha g+t\cdot H\in N_p$，准确最大值为

$$
\max_K n=\alpha+\|t\|.
\tag{X126.18}
$$

正性必须先支付，不能仅凭右端不大于一就把一个有符号泛函称为效应。对 $v\in S^2$，置

$$
\rho_p(v)=\sup_{x\in K\setminus\{p\}}\frac{-v\cdot H(x)}{g(x)}\ge1.
\tag{X126.19}
$$

该函数有限。若 $q=b(v)$，则 $q\in P_0$，记 $\mathcal A_q=\{e_q\}$；既有全空间公式及完整原边区间为

$$
\begin{gathered}
e_q=(1-\lambda)g+\lambda v\cdot H,\qquad
\lambda=\frac1{1+\rho_p(v)}\in(0,\tfrac12],\\
\{n\in\mathcal E:n(p)=0,\ n(q)=1\}=[g,e_q],\qquad
J(p,q)=[e_p,u-e_q].
\end{gathered}
\tag{X126.20}
$$

区间在整个 $V^{\ast}$ 中，不只是旧球上的限制。其末式由前式取补得到。相对内部、全域正性、边传播及区间公式均按上述来源使用，不另列为新的分类结果。

**定理 126.6（唯一完整确认标签处的塌缩迫使两球单位饱和及全混态 least）。** 在定义126.1、126.5的完整原域中，若发生实际塌缩 (X126.3)，则

$$
\begin{gathered}
a_{D_p}=a_{D_q}=\tfrac12,\qquad
\beta_{D_p}=\beta_{D_q}=1,\\
T_p(x)=e_p(x)\quad(x\in K),\qquad
e_p\le_{C^{\ast}} f\quad(f\in F_p).
\end{gathered}
\tag{X126.21}
$$

证明。定理126.2与完整边区间 (X126.20) 给全部纯输入

$$
T_p(s)=\min\{e_p(s),1-e_q(s)\}\quad(s\in P).
\tag{X126.22}
$$

令 $\mathcal B_p=\{n\in\mathcal E:n(p)=0\}$。取补将整个 $F_p$ 双射到 $\mathcal B_p$，故同一纯域公式等价于

$$
\max_{n\in\mathcal B_p}n(s)=\max\{g(s),e_q(s)\}
\quad(s\in P).
\tag{X126.23}
$$

先只排除反方向越界。固定 $s\in P\setminus\{p\}$，令 $Y=H(s)/g(s)$。若 $\|Y\|>1$，取 $t=Y/\|Y\|$。因为 $g\in\operatorname{ri}N_p$ 且 $t\cdot H\in\operatorname{span}N_p$，可取充分小的 $\varepsilon>0$ 使 $g+\varepsilon t\cdot H\in N_p$。在这项全域正性已经成立之后，(X126.18) 给其原全域最大值 $1+\varepsilon$。于是

$$
n_{\varepsilon}=\frac{g+\varepsilon t\cdot H}{1+\varepsilon}
\in\mathcal B_p,\qquad
n_{\varepsilon}(s)=g(s)\frac{1+\varepsilon\|Y\|}{1+\varepsilon}>g(s).
\tag{X126.24}
$$

由 (X126.23)，必有 $e_q(s)>g(s)$。再用 $\lambda>0$ 及 (X126.20)，得到

$$
\|Y\|>1\quad\Longrightarrow\quad v\cdot Y>1.
\tag{X126.25}
$$

此时不能声称所有 $\|Y\|>1$ 都已被排除。但如果 $v\cdot Y<-1$，则 $\|Y\|>1$，(X126.25) 又迫 $v\cdot Y>1$，矛盾。所以每个上述原纯点满足 $g(s)+v\cdot H(s)\ge0$；在 $s=p$ 两项都为零。因为 $K=\operatorname{conv}P$，线性读数的非负性延到全部 $K$，再按 $C=\mathbb R_{\ge0}K$ 延到整个原锥。因此

$$
k=\frac{g+v\cdot H}{2}\in N_p.
$$

原最大值公式给 $\max_Kk=1$，故 $k\in\mathcal E$。在同一旧球上取真实对径 $r=b(-v)$，则 $k(q)=1$、$k(r)=0$，于是 $q\perp r$。旧球公式 (X126.5) 给

$$
0=T_q(r)=1-2a_{D_p},
$$

从而 $a_{D_p}=1/2$。

原边对称性及 $q,r\in D_p$ 给 $p\in D_q$ 和 $p\perp r$；新取得的 $q\perp r$ 又给 $r\in D_q$。因此两个不同的原纯点 $p,r$ 同属完整 $D_q$ 且正交。在该球图中写 $p=b_{D_q}(w)$、$r=b_{D_q}(z)$，其中 $\|w\|=\|z\|=1$。准确球公式给

$$
0=T_p(r)=1-a_{D_q}+a_{D_q}w\cdot z
\ge1-2a_{D_q}\ge0.
\tag{X126.26}
$$

所以 $a_{D_q}=1/2$ 且 $w\cdot z=-1$，即 $z=-w$。这同时证明此处同球正交点确为该球对径，未预设任意三纯点都能组成共同仪器。

已有 $a_{D_p}=1/2$，故 (X126.5) 使 $D_p$ 的每条直径两端都原正交。[IX120.13][Q126IX] 遂给 $\rho_p(t)=1$ 对全部单位方向成立。对 $x\ne p$，以 $-t$ 代入 (X126.19)，有 $t\cdot H(x)\le g(x)$ 对全部单位 $t$ 成立；取上确界并处理 $x=p$，得到

$$
\|H(x)\|\le g(x)\quad(x\in K).
\tag{X126.27}
$$

现在才排除了全部方向越界。由 (X126.20) 得 $e_q\le g$ 于全 $K$，因而 (X126.22) 化为 $T_p(s)=e_p(s)$ 对全部原纯点成立。

任一原 $f\in F_p$ 都满足 $f(s)\ge e_p(s)$ 于全部 $s\in P$。每张固定 $f-e_p$ 是线性的，$K=\operatorname{conv}P$ 因而给 $f\ge e_p$ 于所有混态；齐次化给整个 $C$ 上的序支配。又 $e_p\in F_p$，所以在每个 $x\in K$，下包络恰为 $e_p(x)$。这一步没有使用混态 PR，也没有把不同纯输入各自的最优选择直接拼成仿射函数。预算结论由 $\beta_H=1/(2a_H)$ 给出。证毕。

**推论 126.7（非单位预算的唯一确认标签必为连续点及剩余塌缩集合）。** 在完整 EB3+PR+Inj 域中，若 $p\in P_0$ 且 $\beta_{D_p}>1$，则 $s\mapsto D_s$ 在 $p$ 处 Hausdorff 连续。存在 $p$ 在整个 $P$ 中的相对开邻域 $U$ 及有限 $B$，使

$$
\beta_{D_s}\le B\quad(s\in U).
\tag{X126.28}
$$

令 $\Sigma$ 为 [IX115.1、115.6][Q126IX] 的整球映射不连续点集，则

$$
\Sigma\subseteq
(P\setminus P_0)\ \cup\
\{p\in P_0:\beta_{D_p}=1,\ T_p=e_p\text{ 于全部 }K\}.
\tag{X126.29}
$$

对右侧第二分支中的实际塌缩 $D_{p_i}\to\{q\}$，还必有 $\beta_{D_q}=1$。

证明。IX115.6 对每个 $p\in\Sigma$ 都供应实际纯列 $p_i\to p$ 及 $q\in P\cap D_p$，使 $D_{p_i}\to\{q\}$。若该 $p$ 又在 $P_0$，定理126.6给 $\beta_{D_p}=1$、$T_p=e_p$ 及 $\beta_{D_q}=1$，得到 (X126.29)。所以 $p\in P_0$、$\beta_{D_p}>1$ 排除 $p\in\Sigma$，即整球映射在 $p$ 连续；IX115.6 的局部预算等价恰给 (X126.28)，其邻域不局限于 $P_0$。证毕。

IX120.9 的 $P_0$ 稠密性并不删除 (X126.29) 的任一分支：稠密集的补集可非空，属于该稠密集的单位预算标签也未被排除。此推论未证明实际塌缩存在，也未证明其不存在。若实际出现 $p\in P_0$ 且 $\beta_{D_p}>1$，本推论使该 $p$ 成为连续点，而 [124.11][Q126X] 所迫使的全局预算无界与塌缩发生在其他极限标签。这个条件结论不构成此类模型的存在性断言。

**定义及应用 126.8（完整直观候选、静态字典与未付接口）。** 完整条件候选仍为：在同一个有限维实锥和严格正单位上，保留全部纯态、全部混态以及整个零一效应区间；确认一个纯态时可完全排除的全部态恰是一整颗实心仿射三球；任意两个纯态的最优确认读数交换端点不变；再要求纯标签趋近时，新完整排除球到固定旧球心的距离趋零。最后这一条是 [125.4—125.5][Q126X] 的 CS：

$$
\forall p\in P\ \forall(p_i)\subset P:\quad
p_i\to p\Longrightarrow\operatorname{dist}(c_p,D_{p_i})\to0,
\qquad c_p=\text{完整 }D_p\text{ 的中心}.
\tag{X126.30}
$$

它在完整 EB3+PR 域中仍与 UF、NC 等价，未由定理126.2—126.7自动取得。上述塌缩结论是实际塌缩必须满足的必要关系，不是足以重构的新公理。CS 仍是既有等价重构接口，没有独立公理数减少或最小性结论。

几何上，若一颗移动实心球真缩到旧球的球面点 $q$，在任何固定纯输入处最优的非平凡确认都必须带着自己的真实零点一起走向 $q$。因此整行纯读数都可在同一条固定零一边 $p\mapsto1,q\mapsto0$ 的效应面上达到。在任何另一颗包含 $p$ 的完整球上，只须在 $p$ 的对径处达到，非负仿射差就使同一效应达到整颗混态球。与此同时，移动标签的全部确认效应在旧球上的非恒定斜率，只能共同靠向与旧球中心指向 $q$ 的方向相反的射线。若原球标签另满足 Inj，且极限标签属于唯一完整零确认分支，旧球的四个原法向坐标把这条跨纯点约束转成真正的对径零一边，再由同球刻度强迫两颗相关球满刻度。没有这项唯一性，四维限制同构及原边线段不能直接输入；即使有它，单位预算极限标签处的塌缩仍未排除。

只有另支付 CS，才经125.5与 [124.10][Q126X] 消费已有同原锥、同原单位静态分类，取得实线性双射

$$
\Phi:H_3(\mathbb C)\longrightarrow V,\qquad
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad
u(\Phi X)=\operatorname{Tr}X.
\tag{X126.31}
$$

其完整对应按原定理保留：

| 原对象与关系 | 同原静态复三能级表示 |
| --- | --- |
| 全部 $K$、全部 $P$ | 全部三阶密度矩阵；全部秩一投影 $p=vv^{\ast}$，$v^{\ast}v=1$ |
| 整个 $\mathcal E$、单位及补 | 全部 $0\preceq E\preceq I_3$、$I_3$ 及 $I_3-E$ |
| 原评价与全混态最优确认 | $f_E(\Phi\rho)=\operatorname{Tr}(E\rho)$；$T_{\Phi p}(\Phi\rho)=\operatorname{Tr}(p\rho)$ |
| 全部纯对比较与交换端点 | $|v^{\ast}w|^2=|w^{\ast}v|^2$；不要求矩阵效应或顺序仪器交换 |
| 完整 $D_{\Phi p}$ 与球心 | $p^{\perp}$ 上全部密度矩阵三球；球心 $\Phi((I_3-p)/2)$ |
| 共同球刻度与预算 | 全部 $a_H=1/2$、$\beta_H=1$；全部原完整球的单位预算正延拓 |
| 有限数学测量 | 全部 $E_j\succeq0$、$\sum_jE_j=I_3$ 的 POVM，包括正交三结果 |

环境实维数九和单体复 Hilbert 维数三是该条件静态表示的结论。每张排除球的实仿射维数三，并不是预先给整个状态空间一个三维物理尺。

同一个原 $\Omega$、全部原合法门序列、每个中间切口与全部记录后条件未来，仍须由实际操作合同供应；数学效应存在不供应其制备、调用或共同仪器。对每个有限复合数仍需整个联合态锥、产品与纠缠输入、共同单位及相容接线；全旁观者正性需量化所有旁观系统，不能从单体正性直接取得 CP。事件分支、TP/TNI 共同预算、零质量分支、实际记录、粗粒化及更新律继续需要各自接口。动力学、连续时间群、物理钟、Hamiltonian、能量单位和数值 $\hbar$ 均未由这些静态结论决定。

本章的承重内容属于 `repo-derived` 的跨合同综合：实际整球塌缩与全部纯输入的固定边达到；每颗包含极限标签的完整球上的同效应达到及反向精确刻度；整个移动确认面的统一旧球斜率；以及在 Inj、唯一完整零确认分支由原正法向扰动取得的单位饱和与全混态 least。共同零确认、严格暴露、球内刻度、原边区间、极限二择、局部预算和静态分类均保留上述原结果的假设与归属。紧性、极值达到、有限纯点凸分解、仿射归一化和球上非负仿射函数只是推导的成熟中间工具，不另立为新增分类。这里不主张全球原创、历史优先权或逻辑独立性。

[Landsman §1.3][Q126L] 的完整仿射效应最小确认构造以 $p(\rho,\sigma)=T_{\sigma}(\rho)$ 对应 (X126.1) 的纯域部分，纯端点对称性对应 PR。其第2节的 uniform Poisson、two-sphere 等重构公理没有从本章前件取得。[Niestegge §3][Q126N] 的 $e_{\omega}(\zeta)$ 定义则对所有非负仿射 $a$、$a(\omega)=1$ 取下确界，未在该定义中加 $a\le1$；其性质 $(\ast\ast)$ 另要求该函数本身仿射、连续且仅在 $\omega$ 取一。本章不能把单个塌缩极限标签处的 (X126.21) 直接当作其全部标签、该更大最小化族上的性质。该文 Theorem 3 仍显式要求 Axioms 1、2、proper 效应序性质 $(\ast)$、有限信息容量和对称跃迁概率；这些前件没有由裸 EB3+PR 或局部 $P_0$ 唯一性整体支付，故不在这里调用其自对偶结论。自动 UF、剩余实际塌缩集合的排除，以及保留全部原量词的同域坏模型，仍是未解决的数学边界。

[Q126IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.6完整原域、严格暴露与球刻度；IX115.4—115.6极限与连续性；IX120.2、120.8、120.10—120.13原法向、唯一完整确认及全空间原边区间。"
[Q126X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "124.10—124.11条件静态类及偏离迫使实际塌缩；125.2全域取零归一化；125.4—125.5固定旧球心CS及其与UF、NC的等价。"
[Q126Faces]: ../../../D5/S3/Quantum/Foundation/ExclusionBallFaces.lean "exclusion_ball_faces：完整排除球的共同暴露和全部真面分类；末项的全Pair前件不在本章输入。"
[Q126L]: https://arxiv.org/src/quant-ph/9603005v2 "N. P. Landsman, Poisson Spaces with a Transition Probability, §1.3及第2节；Rev. Math. Phys. 9 (1997), 29–58，DOI 10.1142/S0129055X97000038；arXiv v2作者源码。"
[Q126N]: https://arxiv.org/html/2312.13213v2 "Gerd Niestegge, Quantum transition probability in convex sets and self-dual cones, §2—§3及Theorem 3；Proc. R. Soc. A 480 (2024), 20230941，DOI 10.1098/rspa.2023.0941；arXiv v2。"

## 追加锚（本行以下为增补区）

## 127. 裸排除球域中的重复球对比度与实际整球塌缩

### 127.1 全局对偶暴露射线的实际完整球

**定义 127.1（原域、球缘及整球零法向面）。** 保留定义124.1的同一个有限维实空间 $V\ne0$、闭尖生成凸锥 $C$ 和在 $C\setminus\{0\}$ 上严格正的原单位 $u$，始终使用整个

$$
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^{\ast}},\qquad
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
D_p=\{x\in K:\min_{f\in F_p}f(x)=0\}.
\tag{X127.1}
$$

唯一全局几何前件是 $\mathrm{EB}_{\ge1}$：对每个原纯 $p$，完整 $D_p$ 仿射同构于某个正维闭欧氏球；球维数允许随标签改变。所有混态均留在 $K$，最小化遍历全部原确认效应。固定辅助欧氏范数及 $x_0\in\operatorname{int}C$，沿用引理124.3的紧对偶基

$$
B^{\ast}=\{h\in C^{\ast}:h(x_0)=1\}.
\tag{X127.2}
$$

对完整球 $F$，记

$$
\begin{gathered}
S(F)=P\cap F=\partial_{\mathrm{rel}}F,\qquad
I(F)=\{a\in P:D_a=F\},\qquad c_F=\text{$F$ 的中心},\\
Z(h)=K\cap\ker h,\qquad
N_t=\{h\in C^{\ast}:h(t)=0\},\qquad
\mathcal N_F=\{h\in C^{\ast}:h|_F=0\},\\
\mathcal A_a=\{e\in F_a:e|_{D_a}=0\}.
\end{gathered}
\tag{X127.3}
$$

本章引用 [IX116.1—116.2][QX127IX] 的完整原面分类、完整零确认、零对称及孤立重复球二分；这些接口适用于允许变维的上述域。特别地，$\mathcal A_a\ne\varnothing$，其中每张效应的整个原零面都是 $D_a$。不输入 PE、PR、Inj、$P$ 闭、共同正延拓、谱性、框架数上界或 NC。以下“暴露点”对 $B^{\ast}$ 指在整个 $B^{\ast}$ 上暴露，不是只在某个 $N_t$ 的切片内暴露。

**命题 127.2（裸 EB 的全局暴露射线有完整球零面）。** 若 $n\in B^{\ast}$ 是暴露点，则存在实际原纯标签 $a\in P$，使

$$
Z(n)=D_a=:F,\qquad
c_F\in K\setminus P,\qquad
N_{c_F}=\mathcal N_F=\mathbb R_+n.
\tag{X127.4}
$$

并且，置 $M_n=\max_Kn>0$，对每个 $b\in I(F)$，都有

$$
n(b)=M_n,\qquad \mathcal A_b=\{n/M_n\}.
\tag{X127.5}
$$

这里唯一的是在整个 $D_b$ 上为零的完整确认；不将 $F_b$ 的全部效应称为唯一，也不将 $n/M_n$ 断言为最小确认或正限制映射的逆。

证明。复用命题124.4中不涉及 PE 的构造 (X124.8)—(X124.9)：若 $f\mapsto f(v)$ 在整个 $B^{\ast}$ 上唯一最小于 $n$，置

$$
\alpha=\min_{f\in B^{\ast}}f(v),\qquad
x=v-\alpha x_0.
\tag{X127.6}
$$

对任意非零 $g\in C^{\ast}$，其原基归一给

$$
g(x)=g(x_0)\left[\left(\frac{g}{g(x_0)}\right)(v)-\alpha\right]\ge0,
\qquad g(x)=0\ \Longleftrightarrow\ g\in\mathbb R_+n.
\tag{X127.7}
$$

有限维闭锥双对偶性给 $x\in C$；该成熟分离步骤与124.4相同。$B^{\ast}$ 至少有两个点，故 $x=0$ 会使暴露泛函恒定而矛盾。因此 $x\ne0$，$\widehat x=x/u(x)\in K$，且 $N_{\widehat x}=\mathbb R_+n$。这一构造尚未判定 $\widehat x$ 的纯混。

若 $\widehat x$ 非纯，则非空真面 $Z(n)$ 含混态，原面分类直接给 $Z(n)=D_a$。

若 $\widehat x=t\in P$，在实际正维球 $D_t$ 的球面取 $s\in P\cap D_t$。原补效应给零对称，所以 $t\in D_s$。取完整原零确认 $e_s\in\mathcal A_s$，有

$$
e_s\ne0,\qquad e_s(t)=0,\qquad Z(e_s)=D_s.
\tag{X127.8}
$$

于是 $e_s\in N_t\setminus\{0\}=\mathbb R_{>0}n$，从而 $Z(n)=D_s$；取 $a=s$。这一步使用的是整个原锥正的完整效应及实际原零邻点，没有假定纯暴露态不存在。

两种情形都得到完整正维球 $F=Z(n)$，且 $\widehat x\in F$。球心 $c_F$ 是两个不同原纯对径点的中点，故不纯。若 $g\in C^{\ast}$ 且 $g(c_F)=0$，对每个 $z\in F$ 使用 $2c_F-z\in F$，由两项非负及

$$
g(z)+g(2c_F-z)=2g(c_F)=0
$$

得 $g|_F=0$。所以 $N_{c_F}=\mathcal N_F\subseteq N_{\widehat x}$；而 $n$ 零于整个 $F$，反向射线包含也成立，得到 (X127.4)。由此获得的混态见证是 $c_F$，不必是最初的 $\widehat x$。

最后固定 $b\in I(F)$。任取 $e\in\mathcal A_b$，有 $e\in\mathcal N_F\setminus\{0\}$，故 $e=\lambda n$，$\lambda>0$。$e(b)=1$ 与原全域上界 $e\le u$ 分别给 $\lambda n(b)=1$ 及 $\lambda M_n\le1$。又 $n(b)\le M_n$，所以 $n(b)=M_n$、$\lambda=1/M_n$。存在性由 $\mathcal A_b\ne\varnothing$ 给出，且 $M_n>0$ 来自 $n\ne0$ 及 $K$ 张成 $V$。证毕。

### 127.2 单点极端零面的裸域塌缩与实际重复标签消费者

**定理 127.3（无 PE 的极端单点零面塌缩）。** 在定义127.1的原域中，若 $C^{\ast}$ 有一条非零极端射线 $\mathbb R_+h$，且 $Z(h)=\{q\}$，则 $q\in P$，并存在实际原纯标签 $a_i\in P$ 和在整个 $B^{\ast}$ 上暴露的点 $n_i$，使

$$
\begin{gathered}
n_i\longrightarrow h/h(x_0),\qquad
Z(n_i)=D_{a_i},\qquad
N_{c_{D_{a_i}}}=\mathbb R_+n_i,\\
d_H(D_{a_i},\{q\})\longrightarrow0,\qquad
\operatorname{diam}D_{a_i}\longrightarrow0.
\end{gathered}
\tag{X127.9}
$$

每张 $D_{a_i}$ 均是完整原正维球，中心是实际原混态。没有断言 $a_i\to q$，也没有预设原标签列有纯极限。

证明。单点真面使 $q$ 为原极点。沿用124.5的射线与紧基极点对应，$n=h/h(x_0)\in\operatorname{ext}B^{\ast}$。有限维 Straszewicz 定理给整个基上的暴露点列 $n_i\to n$；所用的准确有限维陈述见 [Bru—de Siqueira Pedra §4.3，PDF第31页][Q124BP]，这里不使用其无限维推广。对每项应用命题127.2，取得完整原 $D_{a_i}=Z(n_i)$ 及实际混态球心。

复用定理124.5的整零面紧性步骤，明确其量词如下。若

$$
\eta_i:=\max_{z\in Z(n_i)}\|z-q\|
\not\longrightarrow0,
$$

则可取 $\varepsilon>0$、子列及 $z_i\in Z(n_i)$，使 $\|z_i-q\|\ge\varepsilon$。紧 $K$ 给再一子列 $z_i\to z\in K$，而 $n_i\to n$ 与有限维配对连续性给 $n(z)=0$。这迫使 $z=q$，矛盾。因此 $\eta_i\to0$。每个零面非空，故到单点的 Hausdorff 距离正是 $\eta_i$，直径至多 $2\eta_i$，证明 (X127.9)。此论证未使用 $P$ 闭或球维数固定。证毕。

**定理 127.4（实际重复球缘的原确认对比度迫使整球塌缩）。** 设实际不同原纯标签共用一张完整球，取 IX116.2 给出的孤立重复球对 $F,G$，即

$$
I(F)=S(G),\qquad I(G)=S(F),\qquad F\cap G=\varnothing,
\tag{X127.10}
$$

且两球均不与第三张不同完整球相交。若存在

$$
q\in S(F),\qquad f\in F_q,\qquad f|_F\text{ 非恒定},
\tag{X127.11}
$$

则 $C^{\ast}$ 有一条全局极端射线，其整个原零面是 $\{q\}$；因而存在 (X127.9) 的实际完整原球列整体收缩到 $q$。交换 $F,G$ 后同样成立。$F$ 是包含球缘点 $q$ 的这一侧球，而 $q$ 自己的完整排除球是 $D_q=G$；非恒定性测试的是整个 $F$ 上的一张原确认，不是 $f|_{D_q}$。

证明。令 $h=u-f$。这是整个原 $C$ 上的正泛函，且 $h(q)=0$。因 $f(q)=1$ 而 $f|_F$ 非恒定，存在 $z\in F$ 使

$$
h(z)>0.
\tag{X127.12}
$$

特别地 $h\ne0$。使用124.7中紧对偶基的成熟有限极点分解步骤，将同一个 $h$ 写为

$$
h=\sum_{j=1}^{r}\lambda_j n_j,
\qquad \lambda_j>0,\qquad n_j\in\operatorname{ext}B^{\ast}.
\tag{X127.13}
$$

这是整个 $B^{\ast}$ 的有限维 Minkowski 分解；可用 Carathéodory 定理缩减项数，但证明不需要任何统一框架数或全局预算。每个 $n_j$ 都在整个原锥上非负。由 $h(q)=0$，逐项得 $n_j(q)=0$；由 (X127.12)，至少有一项 $n_j(z)>0$。固定该项。

其整个零面 $Z(n_j)$ 非空且为真面，包含 $q$，却不包含 $z$。原面分类使它或者是 $\{q\}$，或者是经过 $q$ 的完整排除球。孤立重复球二分使后一张球只能为 $F$，这与 $n_j(z)>0$ 矛盾。因此 $Z(n_j)=\{q\}$。$n_j$ 是整个基的极点，故其射线在整个 $C^{\ast}$ 极端；不是仅在 $N_q$ 中极端或暴露的局部证书。定理127.3遂产生实际整球塌缩。证毕。

### 127.3 精确平坦分支与非塌缩的剩余范围

**推论 127.5（重复球缘的平坦法向替代与条件性非塌缩限制）。** 保留定理127.4的实际重复球对。对每个固定 $q\in S(F)$，下列两种情况恰有一种：

1. 存在 $f\in F_q$ 在整个 $F$ 上非恒定，并且有实际完整排除球列整体收缩到 $q$。
2. 全部原确认在整个 $F$ 上精确恒为一，且

$$
\forall f\in F_q:\ f|_F=1,
\qquad N_q=\mathcal N_F.
\tag{X127.14}
$$

第二种情况下，$q$ 不是 $K$ 的暴露点；等价地，没有 $h\in C^{\ast}\setminus\{0\}$ 以 $\{q\}$ 为整个零面。这个分支不声称排除由其他机制产生的塌缩。另一侧 $S(G)$ 有相同结论。

若额外输入 NC，即 $\inf_{a\in P}\operatorname{diam}D_a>0$，则第一种情况在全部重复球缘上被排除，(X127.14) 对全部 $q\in S(F)$ 成立，另一侧亦然。特别地，在此条件分支有

$$
\begin{aligned}
q,r\in S(F)&\ \Longrightarrow\ N_q=N_r=\mathcal N_F,
\quad F_q=F_r,\\
s,t\in S(G)&\ \Longrightarrow\ N_s=N_t=\mathcal N_G,
\quad F_s=F_t.
\end{aligned}
\tag{X127.15}
$$

此外，裸 $\mathrm{EB}_{\ge1}+\mathrm{NC}$ 下每条非零全局极端对偶射线的整个零面都是完整排除球；此结论不需 PE。

证明。若有非恒定确认，定理127.4给第一种情况。否则每个 $f\in F_q$ 在 $F$ 恒定，而 $q\in F$ 及 $f(q)=1$ 使该常数必为一。显然 $\mathcal N_F\subseteq N_q$。反向取 $0\ne h\in N_q$，令 $M=\max_Kh>0$。整个 $K$ 上 $0\le h/M\le1$，经原单位齐次化到整个 $C$，得到

$$
f=u-h/M\in\mathcal E,\qquad f(q)=1.
\tag{X127.16}
$$

平坦性使 $h|_F=0$。零泛函也在 $\mathcal N_F$ 中，故 $N_q=\mathcal N_F$。反过来，这个法向面等式也使每个 $u-f\in N_q$ 零于 $F$，所以全部确认恒为一。两种情况按非恒定确认的存在与否互斥且穷尽。

若有正泛函以 $\{q\}$ 为零面，法向面等式会迫使它零于非单点 $F$，矛盾。通常的仿射暴露定义与这里的正零面定义相同：在 $\{u=1\}$ 上的仿射暴露函数先减去其最小值，再齐次化即是整个 $C$ 上的非负线性泛函。

NC 与直径趋零矛盾，故两侧所有球缘点都进入第二种情况。固定 $q,r\in S(F)$，若 $f\in F_q$，则 $f|_F=1$ 给 $f(r)=1$，所以 $F_q\subseteq F_r$；交换两点得相等。法向等式及另一侧同理，得到 (X127.15)。最后，复用引理124.6不含 PE 的零面穷尽步骤：每条非零极端对偶射线的零面是原纯单点或完整球。定理127.3和 NC 排除单点分支，得到末项。证毕。

**约定 127.6（原问题及来源的适用边界）。** 本章的 `repo-derived` 增量是命题127.2的实际纯暴露态分支及其在定理127.4中的原重复球消费者：非恒定的原确认限制供应一个全局极端单点零面，继而强制实际完整球塌缩。124.3的紧对偶基、124.4的闭锥分离构造、124.5的 Straszewicz 与整零面紧性步骤、124.7的有限极点分解，以及 IX116.1—116.2 的完整面与孤立性均按原数学归属复用，不作为独立的新定理。

有限维 Straszewicz 陈述采用 [Bru—de Siqueira Pedra，§4.3][Q124BP]；这里只需要紧凸集极点可被暴露点逼近。有限维闭锥双对偶性及紧凸集的有限极点分解是成熟凸分析步骤，分别用于 (X127.7) 的实际锥成员身份与 (X127.13) 的全局正分解。所有正性、效应上界、暴露和极端性均对应同一个完整原锥；没有把球内正函数或局部法向切片的证书提升为全局证书。

[X125的共同近零确认][QX127X125]保留 EB3+PR 前件，只供应旧球上的小读数，不将任意单张效应零面换成完整 $D_a$；本章通过命题127.2确实取得完整 $D_{a_i}$。原五边形的完整排除边与正限制像计算见 [OriginalWidthContact 的原五边形应用][QX127Pent]，该计算属于 EB1+Inj，未提供重复球对或 EB3 坏模型；本章不以其有符号限制同构供应正延拓。

没有从裸 EB 推出 NC，也没有证明实际重复球缘一定存在非恒定确认。若另给 PE，则每个重复球缘都不能进入 (X127.14)，因而恢复124.7的全部球缘塌缩；没有 PE 时，精确平坦且非暴露的法向分支必须保留，不能从 NC 单独推出 Inj。这里的塌缩点在重复球缘，未对 [131.1的指定坏对径内点][QX127LP]证明局部纯极限 $\mathsf{LP}_{p,y}$，也未证明该命题的否定。共同正提升、稳健框架分离以及满足整个裸 EB 原域的完整反模型仍未由本章构造；这些目标不由条件性塌缩或完整确认唯一性代付。

[QX127IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.2：允许变维的完整面分类、完整零确认、零对称及孤立重复球对。"
[QX127X125]: #125-旧完整球的共同近零确认与固定球心的真零稳定性 "X125.2—125.6：EB3+PR中的近零确认、CS及任意效应零面误差界的边界。"
[QX127Pent]: ../../../Blueprint/D5/S3/Quantum/Foundation/OriginalWidthContact.md "Application: the original regular pentagon and all five complete exclusions；一维完整排除边及更窄的正限制像。"
[QX127LP]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "131.1—131.3：指定坏对径内点的原局部纯极限问题；132—133见其共同正提升续卷。"

## 追加锚（本行以下为增补区）

## 128. 完整球中心关系的有限代数障碍与有界闭包恢复

**定义 128.1（全部原纯点的形式关系空间）。** 沿用126.1的完整原域及 EB3+PR，保留同一个 $V,C,u$、全部 $K,P$ 和整个 $\mathcal E=[0,u]$，记 $k(p,s)=T_p(s)=T_s(p)$。PR 仅交换两个纯端点。令

$$
\mathcal F_0=\mathbb R^{(P)},\qquad
J_0:\mathcal F_0\longrightarrow V,\qquad
J_0\left(\sum_p\alpha_p[p]\right)=\sum_p\alpha_pp.
\tag{X128.1}
$$

这里 $[p]$ 是形式基元，系数只有有限支撑；$\ker J_0$ 是全部真实原线性关系。对每张实际完整排除球 $F=D_r$，取任一仿射同构 $b_F:\overline B^3\to F$，定义

$$
\begin{aligned}
c_{F,v,w}&=[b_F(v)]+[b_F(-v)]-[b_F(w)]-[b_F(-w)],\\
R_{\mathrm{cent}}&=\operatorname{span}_{\mathbb R}
\{c_{F,v,w}:F=D_r,\ r\in P,\ v,w\in S^2\}.
\end{aligned}
\tag{X128.2}
$$

球面点都是原纯点。每条直径的中点都是同一实际球心，故 $R_{\mathrm{cent}}\subseteq\ker J_0$。定义遍历全部原排除球及全部直径，不依赖球图的选择。任意函数 $h:P\to\mathbb R$ 都在形式空间上定义实线性泛函 $L_h(\sum\alpha_p[p])=\sum\alpha_ph(p)$；消灭 $R_{\mathrm{cent}}$ 恰指保持全部球中心关系。

全关系到原全域 least 确认及 fullMixture 的下降，直接复用 [CircuitBalancedConfirmation 的两个既有结论][Q128C]：在126.1的闭生成原锥与严格正单位上，每个核行消灭全部 $\ker J_0$，即满足其全部原 circuit 的 balance 前件，从而取得同原锥上的 reciprocalLeast 与 fullMixture。此处只检验中心关系能否供应这个前件，不另立或重证该下降定理。

**定理 128.2（标准复三能级中，代数生成严格不足而 $\ell^1$ 闭包完整）。** 专取实际模型

$$
V=H_3(\mathbb C),\qquad C=H_3(\mathbb C)_+,\qquad
u=\operatorname{Tr},\qquad
P=\{zz^{\ast}:z\in\mathbb C^3,\ z^{\ast}z=1\}.
\tag{X128.3}
$$

沿用定义128.1，$\mathcal F_0$ 自然嵌入实 Banach 空间 $\ell^1(P)$。将 $J_0$ 连续延拓为 $J_1:\ell^1(P)\to H_3(\mathbb C)$。则

$$
R_{\mathrm{cent}}\subsetneq\ker J_0,
\qquad
\overline{R_{\mathrm{cent}}}^{\,\ell^1(P)}=\ker J_1.
\tag{X128.4}
$$

对应的连续消灭子精确为

$$
R_{\mathrm{cent}}^{\perp}
=\{P\longmapsto\operatorname{Tr}(HP):H\in H_3(\mathbb C)\}
=(\ker J_1)^{\perp}\quad\text{于 }\ell^{\infty}(P).
\tag{X128.5}
$$

特别地，每个有界且保持全部中心关系的实函数有唯一的 Hermitian 迹表示；这一步使用 [Gleason 定理3.5][Q128G]，不是新的框架函数表示定理。

证明。首先核对这是原完整域中的真实检验模型。124.10的完整反向字典给出全部密度态、全部秩一投影、整个矩阵效应区间 $0\preceq E\preceq I_3$，以及

$$
T_R(\rho)=\operatorname{Tr}(R\rho),\qquad
D_R=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \operatorname{supp}\rho\subseteq R^{\perp}\}.
\tag{X128.6}
$$

因此模型满足完整 EB3 和纯端点 PR。每个复二维平面 $W\subset\mathbb C^3$ 都恰由 $R=\Pi_{W^{\perp}}$ 给出一张完整球 $F_W=D_R$，其中心为 $\Pi_W/2$。在 $W$ 上的 Bloch 坐标为 $\rho=(I_W+x\cdot\sigma)/2$、$\|x\|\le1$。所以任意一组对径纯点满足 $P+Q=\Pi_W$；反之 $Q=\Pi_W-P$ 是 $W$ 中与 $P$ 正交的秩一投影，故每组正交基给出一条直径。这覆盖所有实际完整排除球，不只一张坐标球。

先证严格包含。取无理数 $t\in(0,1)$。$1,t$ 在 $\mathbb Q$ 上线性无关；由包含它们的 Hamel 基，指定并延拓得到

$$
A:\mathbb R\longrightarrow\mathbb R\quad\text{为 }\mathbb Q\text{-线性},
\qquad A(1)=0,\quad A(t)=1.
\tag{X128.7}
$$

在全部 $P$ 上置 $f(P)=A(P_{11})$。对每个 $W$ 及其中任意两组对径纯点，

$$
f(P)+f(Q)=A((\Pi_W)_{11})=f(P')+f(Q').
\tag{X128.8}
$$

这里只有系数 $1,-1$，$A$ 的加性足够。因此形式基上的实线性 $L_f$ 消灭全部 $R_{\mathrm{cent}}$。这不声称 $A\circ J_0$ 是实线性的。

令 $P_j=e_je_j^{\ast}$，并取实际单位向量及投影

$$
v_{\pm}=\sqrt t\,e_1\pm\sqrt{1-t}\,e_2,\qquad
P_{\pm}=v_{\pm}v_{\pm}^{\ast}.
$$

两个非对角项相消，故

$$
\begin{gathered}
P_++P_-=2tP_1+2(1-t)P_2,\\
z=[P_+]+[P_-]-2t[P_1]-2(1-t)[P_2]\in\ker J_0,\\
L_f(z)=1+1-2t\,A(1)-2(1-t)A(0)=2.
\end{gathered}
\tag{X128.9}
$$

所以 $z\notin R_{\mathrm{cent}}$，尽管 $L_f$ 消灭所有球的中心关系。除以二后，首式也是两个不同纯分解表达同一个真实密度态的关系。

函数 $f$ 无界。否则因 $P_{11}$ 遍历整个 $[0,1]$，$A$ 在该区间有绝对界 $B$。加性使它在 $[-1,1]$ 同样有界；当 $|x|\le1/n$ 时，$|A(x)|=|A(nx)|/n\le B/n$，所以 $A$ 在零连续，进而由有理逼近有 $A(x)=xA(1)=0$，与 $A(t)=1$ 矛盾。故 $f$ 不是原效应，也不是值域在 $[0,1]$ 的原核行；它只分离两个代数子空间，不构成 EB3+PR 的坏物理模型。以不连续加法函数复合产生无界框架函数的机制，已由 Gleason 原文第886页明确指出。

再确定有界消灭子。设 $h\in\ell^{\infty}(P)$ 消灭 $R_{\mathrm{cent}}$。同一复二维平面中替换一组酉正交基，$h$ 的两个值之和不变。任意两个三维酉正交基都可由有限次这样的二坐标变换及相位变换连接：对非零列对 $(a,b)$，酉块

$$
\frac1{\sqrt{|a|^2+|b|^2}}
\begin{pmatrix}\overline a&\overline b\\-b&a\end{pmatrix}
\begin{pmatrix}a\\b\end{pmatrix}
=\begin{pmatrix}\sqrt{|a|^2+|b|^2}\\0\end{pmatrix}
$$

其中块矩阵的两行范数为一且彼此正交，故确为酉矩阵；所列乘积消去一个分量，零列对跳过。对酉矩阵依次消去对角线下的分量，得到上三角酉矩阵，而列正交性使后者为对角相位矩阵。逆转这些有限步就把原矩阵写成嵌入 $U(2)$ 的块及相位矩阵的乘积。按此乘积分解对当前基右乘，每步只替换当前两个基向量，其余向量不变；所涉二维平面各自都是上段列出的实际 $W$。相位不改变秩一投影。因此

$$
h(z_1z_1^{\ast})+h(z_2z_2^{\ast})+h(z_3z_3^{\ast})=w
\tag{X128.10}
$$

对 $\mathbb C^3$ 的所有酉正交基有同一个实常数 $w$；这一步不以路径连续性代替有限连接。

在全部单位向量上定义 $g(z)=h(zz^{\ast})+B$，其中 $B=\|h\|_{\infty}$。这是非负实函数，对每个完整正交基的和都是 $w+3B$，并且相位不变。其域为完整 $\mathbb C^3$ 的单位球面，复维数为三且有限维空间可分，恰满足 Gleason 第886页的 frame function 定义及第892页定理3.5的前件；不要求预先连续或可测。按该定理及其 regular 定义，存在自伴 $T$ 使 $g(z)=z^{\ast}Tz$。减去常数得 $H=T-BI_3$，于是

$$
h(P)=\operatorname{Tr}(HP)\quad(P\in P).
\tag{X128.11}
$$

若两个 Hermitian 矩阵给出相同值，其差在每个单位向量上的二次型为零；在差矩阵的单位特征向量上评价便使全部特征值为零，故 $H$ 唯一。反向迹函数有界，且由 $P+Q=\Pi_W$ 保持每个中心关系。这证明 (X128.5) 中关于 $R_{\mathrm{cent}}^{\perp}$ 的描述。

最后处理闭包及不可数纯集。这里

$$
\ell^1(P)=\{\alpha:P\to\mathbb R:\sum_P|\alpha_P|<\infty\},
\qquad J_1\alpha=\sum_P\alpha_PP.
$$

非负和按有限子集和的上确界定义。每个集合 $\{P:|\alpha_P|\ge1/n\}$ 有限，故每个 $\alpha$ 的支撑至多可数；有限支撑向量稠密。用矩阵迹范数 $\|P\|_1=1$ 得绝对收敛和 $\|J_1\alpha\|_1\le\|\alpha\|_{\ell^1}$，所以延拓存在且 $\ker J_1$ 闭。这里不把不可数 $P$ 换成一个选定的可数菜单。

标准实对偶 $\ell^1(P)^{\ast}=\ell^{\infty}(P)$ 的配对为 $L_h(\alpha)=\sum_P\alpha_Ph(P)$：连续泛函在单位基元上的值一致有界，且由有限支撑稠密性确定其全部值；反向由绝对收敛直接给连续泛函。每个迹函数还满足

$$
L_h(\alpha)=\operatorname{Tr}(H J_1\alpha),
$$

因此消灭 $\ker J_1$。又 $R_{\mathrm{cent}}\subseteq\ker J_1$，得到 (X128.5) 的另一等号。

令 $M=\overline{R_{\mathrm{cent}}}^{\ell^1}\subseteq\ker J_1$。若存在 $\alpha\in\ker J_1\setminus M$，实 Hahn–Banach 分离给连续 $L$，使 $L|_M=0$ 而 $L(\alpha)\ne0$。它对应一个有界中心函数，故由 (X128.11) 为迹函数，于是 $L(\alpha)=\operatorname{Tr}(H J_1\alpha)=0$，矛盾。得到 (X128.4) 的闭包等式。证毕。

所以即使是有限支撑的真实关系，也可能只能由中心关系的有限线性组合在 $\ell^1$ 范数下逼近，不能用某一次有限组合精确拼出。这个结论不提供逼近速率、系数预算或实际操作程序。无界 $L_f$ 不连续，故不妨碍闭包等式。

**定义及应用 128.3（原域的有界行、未付接口与完整候选）。** 回到126.1的任意完整 EB3+PR 域，不预先把 $P$ 识别为 $\mathbb {CP}^2$。由原紧效应区间及既有固定标签估计，置 $L=\max_{e\in\mathcal E}\|e\|_{\ast}<\infty$，则

$$
0\le k(p,s)\le1,\qquad
|k(p,s)-k(p',s')|\le L\bigl(\|p-p'\|+\|s-s'\|\bigr).
\tag{X128.12}
$$

这使用 PR 将变化标签转为固定 $T_s$ 的输入，再用126.1所引的共同 Lipschitz 界；不是新增连续性公理。尚未支付的第一项是对所有外部纯测试也保持同球中心：

$$
\forall s,r\in P\ \forall v,w\in S^2:\quad
k(b_{D_r}(v),s)+k(b_{D_r}(-v),s)
=k(b_{D_r}(w),s)+k(b_{D_r}(-w),s).
\tag{X128.13}
$$

即使取得此式，还须在同一个原球关联几何上证明这些有界核行消灭全部 $\ker J_0$。一个足够的分析桥是原 $\ell^1(P)$ 中相应的闭包等式；原 $P\subset K$ 有界，故原 $J_0$ 同样具有连续延拓。若该桥及 (X128.13) 均成立，有界行的连续性就使其消灭全关系，随后直接接入定义128.1引用的成熟下降结论。定理128.2只在已经明确指定的标准量子模型中支付这个分析桥；它既未证明一般原域的 (X128.13)，也未证明其在该域中足以推出全关系或 UF。不能先输入 Hilbert 识别、全 Pair 或 Jordan 结构，再把该识别算作从裸 EB3+PR 得出的结果。

白话上，同一个球心可以由任意一对对径纯态各半表达。要求球外比较也不随这对端点的选择改变，仍不同于交换两个纯比较端点。标准量子模型表明：全部球心等式还不能靠有限代数拼接给出所有混合等式；但对始终有界的读数，球与球之间的全部 Hilbert 关联使这些等式在分析意义下已经足够。一般原域的读数有界性已具备，仍缺上述中心兼容及其跨球推广；病态辅助函数不是缺少物理连续性的证据。

完整条件候选仍是：在同一有限维原锥及严格正单位上保留全部纯态、全部混态和全部零一效应；每个纯态可完全排除的全部态恰成一整颗实心仿射三球（EB3）；交换两个纯比较端点，最优确认读数不变（PR）；另要求纯标签趋近时，新完整排除球到固定旧球心的距离趋零，即

$$
\mathrm{CS}:\quad
p_i\to p\text{ 于 }P\Longrightarrow
\operatorname{dist}(c_p,D_{p_i})\to0
\quad\text{对每个 }p\text{ 及每条原纯列成立}.
\tag{X128.14}
$$

按125.5，CS 与 UF 在本域中等价；只有另付此条件，才由124.10取得同原 $C/u$ 的静态复三能级表示。全部原对象及原混态最优确认的对应直接沿用124.10、125.7及126.8，不缩为纯态菜单。本章没有去掉 CS，也没有独立公理数减少或同域坏模型的结论。排除球的实仿射维数三不是物理空间维数；条件静态模型的归一化态空间实维数为八。

同一个原 $\Omega$、全部实际合法门序列、中间切口及记录后的条件未来仍由原操作合同供应；数学效应存在不供应制备、调用或共同仪器。事件分支、更新、TP/TNI 预算与零质量分支，任意有限复合的整个联合态锥、产品及纠缠输入、共同单位和接线，全旁观者兼容与 CP，以及动力学、物理钟、Hamiltonian、能量单位和 $\hbar$，均保留126.8的独立接口边界。

本章承重增量为 `repo-derived` 的具体关系空间应用：针对全部实际完整排除球建立代数严格包含的分离关系，并在同一完整标准模型中用有界消灭子确定精确闭包。Hamel 基与无界加法函数、有限酉消元、Gleason 表示、$\ell^1$ 对偶及 Hahn–Banach 分离都是成熟中间工具，不单列为新发现。原尺度的 Hamel 障碍亦已用于 [V49命题13.5][Q128H49]、[V79第9.2节][Q128H79]及 [C140第4.2节][Q128H140]；它们不替代本章对全部实际排除球的关系检验。Gleason原文第886页给无界机制与 regular 定义，第892页定理3.5给非负框架函数表示；仓内有限复投影表示 [GleasonComplexRepresentation][Q128GR] 亦为既有结果。本章不认领新的 Gleason 定理、全球原创、历史优先权或裸 EB3+PR 的自动 UF。

[Q128C]: ../../../D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.lean "circuit_balance_least_confirmation 与 full_mixture_iff_circuit_balance：同原闭生成锥、严格正单位、全纯域和全效应区间上的既有下降；此处不重证。"
[Q128G]: https://www.iumj.indiana.edu/IUMJ/FTDLOAD/1957/6/56050/pdf "A. M. Gleason, Measures on the Closed Subspaces of a Hilbert Space；第886页的定义与无界例，第892页Theorem 3.5；DOI 10.1512/iumj.1957.6.56050。"
[Q128GR]: ../../../D5/S3/Quantum/GleasonComplexRepresentation.lean "Gleason.ProjectionPackage.gleason_representation：有限复维数至少三，所有投影上的非负、归一与正交可加；不直接供应原中心关系到全部框架的映射。"
[Q128H49]: AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md "13.5：Hamel 权重通过有限标定而非平方，及未归一全域有界性的边界。"
[Q128H79]: AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md "9.2：非连续加法平方与共同范数上界的不同作用。"
[Q128H140]: AURIC_C140_COMMON_SOURCE_THREE_PATH_BALANCE_AND_QUANTUM_GEOMETRY.md "4.2：有理配比与原实配比的 Hamel 障碍。"

## 追加锚（本行以下为增补区）

## 129. 交错法向无限多边形的完整 EB1 与平坦重复球

### 129.1 同一个原锥、全部纯点与完整支撑面

**定义 129.1（有理半平面载体）。** 对 $r>0$ 定义单位向量

$$
N(r)=\left(\frac{1-r^2}{1+r^2},\frac{2r}{1+r^2}\right),
\qquad r_n=2^n,\quad \nu_n=N(r_n),\quad
\mu_n=N(3r_n/2)\quad(n\in\mathbb Z).
\tag{X129.1}
$$

在同一个平面中取全部半平面的交

$$
L=\left\{z=(x,y):
\begin{array}{l}
-1\le x\le1,\\
\nu_n\cdot z\le1+(\nu_n)_2\quad\text{对所有 }n\in\mathbb Z,\\
-\mu_n\cdot z\le1+(\mu_n)_2\quad\text{对所有 }n\in\mathbb Z
\end{array}\right\}.
\tag{X129.2}
$$

取 $V=\mathbb R\times\mathbb R^2$，质量坐标在前，定义

$$
\begin{gathered}
\iota(z)=(1,z),\qquad
C=\{\lambda\iota(z):\lambda\ge0,\ z\in L\},\\
u(t,x,y)=t,\qquad X(t,x,y)=x,\qquad Y(t,x,y)=y,\\
K=C\cap\{u=1\},\quad P=\operatorname{ext}K,\quad
\mathcal E=[0,u]_{C^\ast},\\
\mathcal F_p=\{e\in\mathcal E:e(p)=1\},\qquad
D_p=\{z\in K:\exists e\in\mathcal F_p,\ e(z)=0\}.
\end{gathered}
\tag{X129.3}
$$

效应区间始终是在整个 $C$ 上的全部实线性零一效应。以下平面集合用于 $D,I,N$ 等原对象时均经 $\iota$ 提升；不另选纯态或混态子集。辅助距离取 $V$ 的通常欧氏距离，其在质量一平面上的限制就是平面距离。

定义两条双向无限顶点链及其相邻闭边：

$$
\begin{aligned}
v_n&=\left(\frac{1-2r_n^2}{1+2r_n^2},
                 1+\frac{3r_n}{1+2r_n^2}\right),\\
w_n&=\left(\frac{9r_n^2-2}{9r_n^2+2},
                -1-\frac{9r_n}{9r_n^2+2}\right),\\
A_n&=[v_{n-1},v_n],\qquad B_n=[w_{n-1},w_n],\\
R_\pm&=(1,\pm1),\qquad L_\pm=(-1,\pm1),\\
F&=[R_-,R_+],\qquad G=[L_-,L_+].
\end{aligned}
\tag{X129.4}
$$

对 $\alpha\in[0,2\pi)$，令 $d_\alpha=(\cos\alpha,\sin\alpha)$，$H(\alpha)=\operatorname{argmax}_{z\in L}d_\alpha\cdot z$。记

$$
\theta_n=2\arctan r_n,\qquad
\phi_n=2\arctan(3r_n/2).
\tag{X129.5}
$$

**定理 129.2（完整基、全部支撑面及四个非暴露极限纯点）。** $L$ 是有内部的紧凸集，$C$ 是闭尖生成凸锥，$u$ 在 $C\setminus\{0\}$ 上严格正，且整个归一化基恰为 $K=\iota(L)$。其完整支撑面表为

| 支撑方向角 | 整个 $H(\alpha)$ |
| --- | --- |
| $0$ | $F$ |
| $\pi$ | $G$ |
| $\theta_n$ | $A_n$ |
| $\theta_n<\alpha<\theta_{n+1}$ | $\{v_n\}$ |
| $\pi+\phi_n$ | $B_n$ |
| $\pi+\phi_n<\alpha<\pi+\phi_{n+1}$ | $\{w_n\}$ |

这里 $n$ 遍历全部 $\mathbb Z$，各行合起来穷尽整个方向圆。全部原纯点为

$$
P=\iota\bigl(\{v_n,w_n:n\in\mathbb Z\}
                  \cup\{R_+,R_-,L_+,L_-\}\bigr).
\tag{X129.6}
$$

$P$ 紧。所有 $v_n,w_n$ 都在整个 $L$ 中暴露，四个 $R_\pm,L_\pm$ 都极端但非暴露。

证明。令 $S=\overline B^2+[-1,1](0,1)$ 为竖直线段与闭单位圆盘的 Minkowski 和。单位方向 $d$ 在 $S$ 上的支撑值为 $\|d\|+|d_2|$。因此 $S\subset L$，特别地 $L$ 有内部，四个所列角点均在 $L$。$L$ 是闭凸集；$\nu_0=(0,1)$ 给 $y\le2$，而 $\mu_0=(-5/13,12/13)$ 的下侧约束给

$$
5x-12y\le25,\qquad y\ge(5x-25)/12\ge-5/2.
\tag{X129.7}
$$

结合 $|x|\le1$，得到 $L$ 紧。

凸性使 $C$ 对加法及非负数乘封闭。若 $\lambda_j\iota(z_j)$ 收敛，则其质量 $\lambda_j$ 收敛到 $\lambda\ge0$。$\lambda>0$ 时，空间坐标除以质量收敛到 $L$ 中一点；$\lambda=0$ 时，$L$ 有界使空间坐标也趋零。因此 $C$ 闭，且质量为零的锥向量只有 $0$。这同时给严格正性与尖性。$L$ 含单位圆盘，故 $\iota(0),\iota(1/2,0),\iota(0,1/2)$ 线性无关，$C-C=V$。由质量坐标直接得到 $K=\iota(L)$，包括整个原混态域。

下面计算边界，不以有限截断代替 (X129.2)。对任意 $0<s<t$，两条直线 $N(s)\cdot z=N(t)\cdot z=1$ 的唯一交点是

$$
T(s,t)=\left(\frac{1-st}{1+st},\frac{s+t}{1+st}\right),
\qquad
N(\rho)\cdot T(s,t)-1
=-\frac{2(\rho-s)(\rho-t)}{(1+\rho^2)(1+st)}.
\tag{X129.8}
$$

第二式对每个 $\rho>0$ 成立。若 $\rho\notin(s,t)$，其右侧非正，且只在 $\rho=s,t$ 取零。取 $s=r_n,t=2r_n$，就有 $v_n=(0,1)+T(s,t)$。双向几何数列在这两个相邻参数之间没有别项，所以 $v_n$ 满足全部上侧约束，并且只在指标 $n,n+1$ 取等。它满足 $|x|<1,y>1$；因每个 $(\mu_j)_2>0$，

$$
-\mu_j\cdot v_n
<|(\mu_j)_1|-(\mu_j)_2
\le1-(\mu_j)_2<1+(\mu_j)_2.
\tag{X129.9}
$$

故全部下侧约束也满足。取 $s=3r_n/2,t=3r_n$ 并作 $z\mapsto-z+(0,-1)$，同理得到 $w_n$ 满足全部约束，只在下侧指标 $n,n+1$ 取等，且 $|x|<1,y<-1$。

在上侧第 $n$ 条支撑直线上，相邻约束 $n-1,n+1$ 分别切出端点 $v_{n-1},v_n$。相邻法向的夹角严格介于 $0,\pi$，故它们在该直线上的可行半线相反，交恰为这两点间的线段。两端点已被证明满足所有约束，其间线段也可行。因此该直线与整个 $L$ 的交恰为 $A_n$。下侧同理恰为 $B_n$。这些端点互异：$v_n$ 的第一坐标随 $r_n$ 严格下降，$w_n$ 的第一坐标严格上升。

竖直边也没有额外端点。记 $s=3r_j/2$；在 $x=1$ 与 $x=-1$ 上，约束分别化出

$$
\begin{array}{c|cc}
&\text{全部上侧约束}&\text{全部下侧约束}\\ \hline
x=1&y\le1+r_j&y\ge-1-1/s\\
x=-1&y\le1+1/r_j&y\ge-1-s .
\end{array}
\tag{X129.10}
$$

令相应参数趋于 $0$ 或 $\infty$，得到两处都必须 $-1\le y\le1$；反向由 $S\subset L$ 得到整个 $F,G$ 可行。

还须排除未列出的边界弧。固定 $z=(x,y)\in L$ 且 $|x|<1$，两族约束的余量为

$$
a_j(z)=1+(\nu_j)_2-\nu_j\cdot z,\qquad
b_j(z)=1+(\mu_j)_2+\mu_j\cdot z.
\tag{X129.11}
$$

当 $j\to-\infty$ 时，它们分别趋 $1-x,1+x$；当 $j\to+\infty$ 时，分别趋 $1+x,1-x$。四个极限都严格正。因此两端尾部的余量有共同正下界。若其余有限多个余量也全严格正，则它们与 $1-|x|$ 的最小值严格正；法向长度为一，使足够小的整个邻域仍满足全部约束，$z$ 就是内点。故任何 $|x|<1$ 的边界点都属于某个 $A_j$ 或 $B_j$。结合 (X129.10)，边界恰为所列全部闭边及其端点。

由 $r_n<3r_n/2<2r_n$，

$$
0<\theta_n<\phi_n<\theta_{n+1}<\pi,\qquad
\lim_{n\to-\infty}\theta_n=\lim_{n\to-\infty}\phi_n=0,\qquad
\lim_{n\to+\infty}\theta_n=\lim_{n\to+\infty}\phi_n=\pi.
\tag{X129.12}
$$

每个严格位于相邻上侧法向之间的单位方向，都是这两个法向的严格正线性组合。具体地，对 $\gamma<\alpha<\beta$、$\beta-\gamma<\pi$，其系数为 $\sin(\beta-\alpha)/\sin(\beta-\gamma)$ 与 $\sin(\alpha-\gamma)/\sin(\beta-\gamma)$。支撑取等就迫使两个相邻约束同时取等，因而唯一最大点为 $v_n$。下侧给 $w_n$。边法向与水平法向的支撑面已求出；(X129.12) 保证表中没有遗漏方向。这是成熟支撑面交运算在当前全部半平面上的应用。

单点暴露使所有链顶点极端。$F,G$ 是整个 $L$ 的暴露面，其各端点也在 $L$ 中极端；边的相对内点与 $L$ 的内点都不极端，故纯点恰为 (X129.6)。对 $q=(\sigma,\varepsilon)$，其中 $\sigma,\varepsilon\in\{-1,1\}$，若非零方向 $d=(a,b)$ 在 $L$ 上最大于 $q$，则在子集 $S$ 上也最大于 $q$，于是

$$
\sigma a+\varepsilon b=\sqrt{a^2+b^2}+|b|.
\tag{X129.13}
$$

由 $\sigma a\le\sqrt{a^2+b^2}$、$\varepsilon b\le|b|$，取等迫使 $b=0,\ \sigma a>0$。这样的整个支撑面是 $F$ 或 $G$，不是单点。四个角点因此均非暴露。

最后，有理坐标直接给出全部尾极限：

$$
\begin{array}{c|cc}
&n\to-\infty&n\to+\infty\\ \hline
v_n&R_+&L_+\\
w_n&L_-&R_-
\end{array}
\tag{X129.14}
$$

任一整数指标序列若无界，就有趋于其中一个尾部的子列；有界指标只有有限个值。因此这些是两条链唯一可能的新聚点，它们全已列入 $P$，所以 $P$ 闭且紧。特别地，全局暴露点 $\{\iota(v_n),\iota(w_n)\}$ 在 $P$ 中稠密，仍有这四个非暴露原纯点。证毕。

### 129.2 全部原效应的完整排除表与精确纤维

**定理 129.3（全部标签、全部效应及全部混态的 EB1）。** 对每个 $n\in\mathbb Z$，完整原排除集合恰为

$$
\begin{aligned}
D_{\iota(v_n)}&=\iota(B_n),&
D_{\iota(w_n)}&=\iota(A_{n+1}),\\
D_{\iota(R_+)}=D_{\iota(R_-)}&=\iota(G),&
D_{\iota(L_+)}=D_{\iota(L_-)}&=\iota(F).
\end{aligned}
\tag{X129.15}
$$

每张集合都是整个非退化仿射闭一球，故 (X129.3) 满足全局 EB1，尤其属于原 $\mathrm{EB}_{\ge1}$ 域。

证明。先将成熟的完整仿射效应归一化用于本实例，保留任意原效应而非选定测试。对 $d\in\mathbb R^2$ 记

$$
m(d)=\min_{z\in L}d\cdot z,\qquad
M(d)=\max_{z\in L}d\cdot z,\qquad W(d)=M(d)-m(d).
\tag{X129.16}
$$

任一实线性泛函唯一写为 $e(t,z)=a t+d\cdot z$。整个效应区间的精确条件是

$$
e\in\mathcal E\quad\Longleftrightarrow\quad
-m(d)\le a\le1-M(d).
\tag{X129.17}
$$

确实，在 $\lambda\iota(z)$ 上的读数为 $\lambda(a+d\cdot z)$，所以全 $L$ 上的零一界等价于全 $C$ 上的 $0\le e\le u$；$\lambda=0$ 时两边读数都为零。$d=0$ 恰给 $e=a u,\ 0\le a\le1$。$L$ 含单位圆盘，还使 (X129.17) 给 $0\le a\le1$、$2\|d\|\le1$，所以 $\mathcal E$ 闭且有界，原确认纤维紧，定义中的存在零值也等价于原最小值为零。

对任意 $e\in\mathcal E$，若 $a+m(d)>0$，则整个原零面为空；若 $d\ne0$ 且 $a+m(d)=0$，则整个零面恰为 $\iota(\operatorname{argmin}_L d\cdot z)$，由定理129.2的表穷尽。常数效应中，$e=0$ 的零面为整个 $K$，$e=a u,\ a>0$ 的零面为空。零效应不能确认任何原纯点，所以其全 $K$ 零面不会加入某个 $D_p$。

若 $d\ne0$，则 $W(d)>0$。这样的 $e$ 确认 $\iota(p)$ 时，必有 $p\in\operatorname{argmax}_L d\cdot z$ 且 $a=1-M(d)$。它的全 $K$ 最小值为 $1-W(d)\ge0$；零面非空当且仅当 $W(d)=1$，此时整个零面恰为 $\iota(\operatorname{argmin}_L d\cdot z)$。最小值严格正的确认不添加任何排除点，常数确认 $u$ 也不添加。

反向，对任何非零支撑方向 $d$，不论原始宽度是多少，

$$
e_d(t,z)=\frac{d\cdot z-m(d)t}{W(d)}
\tag{X129.18}
$$

都是同一原效应区间中的实际效应。它确认该方向的每个最大点，并零于整个最小面，包括面内的全部混态。故精确地

$$
D_{\iota(p)}
=\bigcup_{\substack{d\ne0\\p\in\operatorname{argmax}_L d\cdot z}}
  \iota(\operatorname{argmin}_L d\cdot z).
\tag{X129.19}
$$

这一步只是完整效应域的归一化与支撑面演算，不是另加的操作或正提升假设。

由定理129.2，$v_n$ 的非零支撑方向角恰为 $[\theta_n,\theta_{n+1}]$。利用更精确的交错

$$
\phi_{n-1}<\theta_n<\phi_n<\theta_{n+1}<\phi_{n+1},
\tag{X129.20}
$$

这些方向的反向支撑面依次是 $\{w_{n-1}\},B_n,\{w_n\}$：恰在反向角 $\pi+\phi_n$ 处取得整条 $B_n$，两旁各为一个端点。因此它们的并恰为整条 $B_n$。特别地，$d=\mu_n$ 的 (X129.18) 就给同时零于全部 $B_n$ 的同一原确认。

$w_n$ 的支撑方向角恰为 $[\pi+\phi_n,\pi+\phi_{n+1}]$；反向落在 $[\phi_n,\phi_{n+1}]$，其中恰有一个上侧边法向 $\theta_{n+1}$。其最小面依次为 $\{v_n\},A_{n+1},\{v_{n+1}\}$，并恰为 $A_{n+1}$；可取 $d=-\nu_{n+1}$ 取得整条零边。四个角点只有定理129.2求出的水平支撑方向，遂分别给 $G,F$，实际确认可取 $(u+X)/2,(u-X)/2$。这证明 (X129.15) 对所有原效应与所有原混态精确成立。

每条 $A_n,B_n$ 的两端点不同，$F,G$ 的两端点也不同。任一这样的边 $[a,b]$ 有单射仿射图

$$
s\longmapsto\iota\left(\frac{a+b}{2}
                         +s\frac{a-b}{2}\right),\qquad s\in\mathbb R,
\tag{X129.21}
$$

将整个闭单位一球 $[-1,1]$ 映到整条边。故没有退化球，也没有删去边内混态。证毕。

**定理 129.4（实际孤立重复球及完整正法向纤维）。** 对完整球 $H$ 记 $I(H)=\{p\in P:D_p=H\}$、$S(H)=P\cap H$。在提升记号下，全部标签纤维为

$$
\begin{aligned}
I(A_n)&=\{w_{n-1}\},& I(B_n)&=\{v_n\},\\
I(F)&=\{L_+,L_-\}=S(G),&
I(G)&=\{R_+,R_-\}=S(F).
\end{aligned}
\tag{X129.22}
$$

$F,G$ 不相交，且各自都不与任何第三张不同完整排除球相交。令

$$
\begin{aligned}
h_n^+&=(1+(\nu_n)_2)u-(\nu_n)_1X-(\nu_n)_2Y,\\
h_n^-&=(1+(\mu_n)_2)u+(\mu_n)_1X+(\mu_n)_2Y.
\end{aligned}
\tag{X129.23}
$$

对 $z\in L$ 记 $N_z=\{h\in C^\ast:h(\iota(z))=0\}$，并记 $\mathcal N_H=\{h\in C^\ast:h|_{\iota(H)}=0\}$。它们的完整值为

$$
\begin{aligned}
N_{v_n}&=\operatorname{cone}\{h_n^+,h_{n+1}^+\},&
N_{w_n}&=\operatorname{cone}\{h_n^-,h_{n+1}^-\},\\
N_z&=\mathbb R_+h_n^+&& (z\in\operatorname{ri}A_n),\\
N_z&=\mathbb R_+h_n^-&& (z\in\operatorname{ri}B_n),\\
N_z&=\mathcal N_F=\mathbb R_+(u-X)&& (z\in F),\\
N_z&=\mathcal N_G=\mathbb R_+(u+X)&& (z\in G),\\
N_z&=\{0\}&& (z\in\operatorname{int}L).
\end{aligned}
\tag{X129.24}
$$

特别地，在 $R_+,R_-$ 的每一个原确认都恒为一于整个 $F$；在 $L_+,L_-$ 的每一个原确认都恒为一于整个 $G$。精确确认纤维为

$$
\begin{aligned}
\mathcal F_{\iota(R_\pm)}
 &=\{(1-b)u+bX:0\le b\le1/2\},\\
\mathcal F_{\iota(L_\pm)}
 &=\{(1-b)u-bX:0\le b\le1/2\}.
\end{aligned}
\tag{X129.25}
$$

因此，即使额外要求 $P$ 闭，裸 EB1 也不推出 Inj 或 PE，且不能排除 X127.5 的精确平坦分支。

证明。全部上侧边的点满足 $|x|<1,y>1$，全部下侧边的点满足 $|x|<1,y<-1$，所以没有一条碰到 $F$ 或 $G$。同侧不同边的支撑法向不同，不可能是同一条边；异侧边与竖直边也不同。于是 (X129.22) 由完整表 (X129.15) 逐项读出，给出 [IX116.2][Q129IX] 的实际孤立重复球对。“孤立”在这里指完整球的交叠关系；它不声称其他球的 Hausdorff 极限避开 $F,G$。

任一非零正泛函 $h=a u+d\cdot(X,Y)$ 若零于 $\iota(z)$，则 $d\ne0$、$a=-d\cdot z=-m(d)$，所以 $-d$ 是 $L$ 在 $z$ 的全局支撑方向。支撑面表使链顶点的这些方向恰为两个相邻边法向的非负锥；因它们在该顶点取等，常数项也按同一非负系数组合，得到 (X129.24) 的首行。边的相对内点只允许自己的边法向。四个角点只允许水平法向，$F,G$ 的内点也如此；内点没有非零零法向。这证明全部所列正法向都是在整个原锥上的法向，而非球内限制的局部法向。零质量向量的法向集合另为 $\{h\in C^\ast:h(0_V)=0\}=C^\ast$，而质量一基点 $\iota(0,0)$ 的正零法向为 $\{0\}$。

对任一右端点，$e\in\mathcal F_{\iota(R_\pm)}$ 当且仅当 $u-e\in N_{R_\pm}$ 且 $e\ge0$。由 (X129.24)，$u-e=b(u-X)$、$b\ge0$；在全 $L$ 上其最小值为 $1-2b$，所以精确地 $0\le b\le1/2$。左端点相同。这证明 (X129.25) 及整边恒一性。非零 $N_{R_\pm}$ 中每个泛函的整个零面都是 $F$，左侧都是 $G$，所以四点无单点正零面，PE 失败；两对不同标签共用完整球，Inj 失败。定理129.2又给 $P$ 紧及暴露点在 $P$ 中稠密。这些额外性质与精确平坦分支同时存在。证毕。

### 129.3 全部坏对径的 LP 与四个联合塌缩尾部

**定理 129.5（真实坏见证存在，而本模型处处满足原 LP）。** 本模型每张完整排除一球的两个端点都不可由一个原效应读成一、零；故每个纯标签都确有 [131.1][Q129LP] 的坏对径见证。对每个这样的见证 $(p,q,\bar q)$，原指定点 $y=(3q+\bar q)/4$ 都满足

$$
\operatorname{dist}(y,P)>0,\qquad \mathsf{LP}_{p,y}.
\tag{X129.26}
$$

特别地，可以实际取

$$
p=(1,-1,1),\qquad q=(1,1,1),\qquad
\bar q=(1,1,-1),\qquad y=(1,1,1/2),
\tag{X129.27}
$$

此时 $D_p=\iota(F)$，且

$$
\operatorname{dist}(y,P)=1/2.
\tag{X129.28}
$$

证明。闭一球的对径端点就是其两个线段端点，换用单射仿射球图也不改变它们。$A_n$ 的两端点同在上侧链，而任一上侧链纯点的完整排除集在下侧；所以一端不属于另一端的完整排除集，不能被确认为一而使另一端为零。$B_n$ 同理。$F$ 的两端点的排除集均为不相交的 $G$，$G$ 的两端点亦然。因此所列全部对径都是坏对径，且 (X129.27) 是实际原见证，不是形式上的球内点对。

任意这样的 $y$ 是一条所列边的严格内点，而全部纯点在这条边上的交恰为两端点。故 $y\notin P$。由定理129.2的紧性，$\operatorname{dist}(y,P)$ 达到且严格正，因而不存在原纯点列收敛到 $y$，得到 (X129.26)。对 (X129.27)，全部上侧纯点的平面第二坐标至少为 $1$，全部下侧纯点的第二坐标至多为 $-1$；所以它们与 $(1,1/2)$ 的距离均至少 $1/2$。$R_+$ 达到 $1/2$，证明精确距离。

依 [131.2—131.3][Q129LP] 的既有等价，每个固定坏见证也各有某个正误差阈值下的稳健原框架距离；这不限制框架大小。这里没有全见证统一的正距离：例如取 $A_n$ 的有序端点，指定点到其中一个端点的距离为 $\|v_n-v_{n-1}\|/4$，当 $n\to-\infty$ 时趋零。逐见证 LP 与统一下界必须区分。证毕。

**定理 129.6（同锥、同标签、同确认的四个整球塌缩极限）。** 全部四个尾部都有实际完整排除球塌缩。其联合极限为

| 整球 | 实际原标签 | 指标尾部 | 整球的 Hausdorff 极限 | 标签极限 | 极限标签的完整排除球 |
| --- | --- | --- | --- | --- | --- |
| $A_n$ | $w_{n-1}$ | $n\to-\infty$ | $\{R_+\}$ | $L_-$ | $F$ |
| $A_n$ | $w_{n-1}$ | $n\to+\infty$ | $\{L_+\}$ | $R_-$ | $G$ |
| $B_n$ | $v_n$ | $n\to-\infty$ | $\{L_-\}$ | $R_+$ | $G$ |
| $B_n$ | $v_n$ | $n\to+\infty$ | $\{R_-\}$ | $L_+$ | $F$ |

表内全部点、球与标签按 $\iota$ 提升。所有单项球仍非退化，但 $\inf_{p\in P}\operatorname{diam}D_p=0$，所以 NC 失败。极限确认的整个零面始终是表中最后一列的非退化球，不是塌缩单点。

证明。由 (X129.15)，$A_n=D_{w_{n-1}}$、$B_n=D_{v_n}$ 是实际标签的完整排除集。由 (X129.14)，每个线段的两端点在相应尾部都趋于表中同一点，故整个线段的 Hausdorff 距离趋零；标签也由同一显式公式收敛到表中实际原纯点。这同时处理了全部正、负整数尾部。

还可以将这些几何极限与同一原效应区间内的完整确认保持联合。取 (X129.23) 的正泛函，定义

$$
\begin{aligned}
M_n^+&=\max_Kh_n^+=h_n^+(\iota(w_{n-1})),&
f_n^+&=h_n^+/M_n^+,\\
M_n^-&=\max_Kh_n^-=h_n^-(\iota(v_n)),&
f_n^-&=h_n^-/M_n^-.
\end{aligned}
\tag{X129.29}
$$

最大点等式由完整支撑表直接得到：$\phi_{n-1}<\theta_n<\phi_n$ 使 $-\nu_n$ 的唯一最大点为 $w_{n-1}$；$\theta_n<\phi_n<\theta_{n+1}$ 使 $\mu_n$ 的唯一最大点为 $v_n$。$M_n^\pm>0$，各值均是 (X129.1)、(X129.4) 的有限有理表达式。于是

$$
\begin{gathered}
f_n^\pm\in\mathcal E,\qquad
f_n^+(\iota(w_{n-1}))=f_n^-(\iota(v_n))=1,\\
Z_K(f_n^+)=\iota(A_n),\qquad
Z_K(f_n^-)=\iota(B_n).
\end{gathered}
\tag{X129.30}
$$

这些等式指整个原零面，包括全部边内混态；它们不是任意局部函数的正延拓。

由于 $\nu_n,\mu_n$ 在两个尾部分别趋于 $(1,0),(-1,0)$，并且实际最大标签也按表收敛，(X129.29) 给两端均有 $M_n^\pm\to2$，且在整个 $V^\ast$ 中

$$
\begin{array}{c|cc}
&n\to-\infty&n\to+\infty\\ \hline
f_n^+&(u-X)/2&(u+X)/2\\
f_n^-&(u+X)/2&(u-X)/2 .
\end{array}
\tag{X129.31}
$$

$(u-X)/2$ 的整个原零面为 $\iota(F)$，$(u+X)/2$ 的整个原零面为 $\iota(G)$。因此实际零边可以整体塌缩，而极限正泛函的零面扩大为一整条竖直边。尤其第一行的负尾部同时满足 $w_{n-1}\to L_-$、$D_{w_{n-1}}\to\{R_+\}$、$f_n^+\to(u-X)/2$，但 $D_{L_-}=Z_K((u-X)/2)=F$。四个极限球缘点的全部非零正零法向均已由 (X129.24) 求出，不存在以它们为单点零面的极限法向。

直径随端点差趋零，所以 NC 失败。这种塌缩与 X127.5 的平坦分支相容：该分支排除的是在旧球上非恒定的原确认，未排除由其他机制产生的塌缩。表中塌缩点全是原纯球缘，不能换作定理129.5的指定混态内点。证毕。

**约定 129.7（数学归属、文献重叠与剩余原问题）。** 本章承重增量为 repo-derived 的完整原域实例：有理半平面交给出同一个闭尖生成锥及严格正单位，完整支撑表给出全部原纯标签，全部原效应的归一化给出 (X129.15) 的整混态排除表，并实现四个非暴露纯标签的孤立平坦重复块。有限维支撑面演算、紧基齐次化、仿射零一归一化与闭集距离都是成熟中间工具，不另列为新增一般定理。

[Janotta—Hinrichsen][Q129JH] 的式(16)—(18)给出全效应区间 $V_+^\ast\cap(u-V_+^\ast)$ 及其 no-restriction 含义，§3.5介绍有限正多边形状态空间；这里复用这套凸状态—全效应语言，不借用其复合或物理实现结论。[原五边形的完整排除应用][Q129Pent]已计算有限 EB1+Inj，全部顶点均暴露；它不供应这里的双向无限链及四个非暴露极限标签。全局暴露点在极点中稠密是成熟有限维 Straszewicz 结论，明确陈述见 [Bru—de Siqueira Pedra §4.3][Q129BP]；定理129.2直接计算本实例的全部聚点，稠密性不被重计为新增定理，也不能把稠密性升级为 PE。这里只限定这两份文献的所引范围及上述仓内重叠，不主张全球原创或历史优先权。

本实例支付了 [X127.5][Q129Flat] 所保留平坦分支的完整原域存在性，否定从裸 EB、甚至从裸 EB 加 $P$ 闭与原暴露点稠密性消灭全部这类分支的路线。定理129.5同时证明本实例的全部坏见证满足 LP，故它不是普适原 LP 的反模型。一般原域仍须处理纯点能否积累到指定坏对径的混态内点，以及该积累与同一原锥全部 EB 条件的相容性；共同正提升也未由这份实例供应。

本实例所有排除球维数恰为一，且不满足 NC，因此不提供 EB3、EB3+PR 或加入 NC 的原域反例。X128.2的标准复三能级中心关系闭包及 X128.3的 EB3+PR 未付接口保留其原适用范围，不承担本实例的供应，也不由本实例解决。这里仅构造有序实空间及其全效应区间，没有定义动力学、仪器、复合或物理实现。

[Q129IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "116.1—116.2：变维完整面与孤立重复球二分；本章直接实现其中的平坦重复块。"
[Q129LP]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "131.1—131.3：实际坏对径、指定四分点、原LP及稳健框架距离等价；本章仅结算所构造模型中的全部见证。"
[Q129Flat]: #127-裸排除球域中的重复球对比度与实际整球塌缩 "127.5：全部原确认恒一、整球零法向相等的非暴露平坦分支；该分支不禁止其他机制的塌缩。"
[Q129Pent]: ../../../Blueprint/D5/S3/Quantum/Foundation/OriginalWidthContact.md "Application: the original regular pentagon and all five complete exclusions；有限EB1+Inj及完整仿射效应归一化。"
[Q129JH]: https://arxiv.org/abs/1402.6562 "J. Janotta and H. Hinrichsen, Generalized probability theories: what determines the structure of quantum theory? 式(16)—(18)与§3.5；全文：https://ar5iv.labs.arxiv.org/html/1402.6562。"
[Q129BP]: https://arxiv.org/abs/2103.08446 "J.-B. Bru and W. de Siqueira Pedra, Weak* Hypertopologies with Application to Genericity of Convex Sets，§4.3开头的有限维Straszewicz陈述；全文：https://ar5iv.labs.arxiv.org/html/2103.08446。"

## 追加锚（本行以下为增补区）

## 130. 原零图的两步覆盖、连通边界与完整静态复三能级

**定义 130.1（完整原域与两步条件）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，及在 $C\setminus\{0\}$ 上严格正的 $u\in V^*$。始终保留

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{X130.1}
$$

$K$ 是整个原紧基，$P$ 是全部原纯点，$\mathcal E$ 是全部原效应；不取截面、所选纯点或测试子菜单代替它们。对 $p,q\in P$ 定义

$$
p\perp q\quad\Longleftrightarrow\quad
\exists f\in\mathcal E:\ f(p)=1,\ f(q)=0.
\tag{X130.2}
$$

补效应给对称性，且 $p\not\perp p$。沿用[VII103.1—103.2][Q130VII]的 $\mathrm{EB}_{\ge2}$：对每个原 $p$，整个 $D_p$ 仿射同构于某个完整闭球 $B^{d_p}$，$d_p\ge2$，允许维数随标签改变；$\mathrm{EB3}$ 表示全部 $d_p=3$。在此域记

$$
\begin{aligned}
\mathsf D_2(p):&\quad
\forall q\in P:\ p\perp q\ \lor
\exists r\in P:\ p\perp r\ \land\ q\perp r,\\
\mathsf D_2:&\quad\forall p\in P\ \mathsf D_2(p).
\end{aligned}
\tag{X130.3}
$$

每个存在量词中的 $r$ 是同一原纯点，两条边均由原全域效应见证。$D_p$ 有纯球缘，故 $q=p$ 时的共同邻点自动存在。因此 $\mathsf D_2$ 正是原简单零图直径至多二，也等价于每对不同且不相邻的原纯点有共同邻点。它不要求一条已经指定的边有共同邻点。

**定理 130.2（固定纯点的两步覆盖迫真实三角）。** 在定义130.1的完整 $\mathrm{EB}_{\ge2}$ 域内，固定 $p\in P$。若 $\mathsf D_2(p)$ 成立，则存在 $q,r\in P$，使

$$
p\perp q,\qquad p\perp r,\qquad q\perp r.
\tag{X130.4}
$$

等价地，若 $p$ 不属于任何真实零三角，则存在原 $s\in P\setminus\{p\}$，满足

$$
p\not\perp s,\qquad
\nexists r\in P:\ p\perp r\ \land\ s\perp r.
\tag{X130.5}
$$

特别地，$\mathsf D_2$ 使每个原纯点属于一个真实三角。

证明。只复用[VII103.2及IX116.1][Q130VII][Q130IX]的裸EB面接口：每个 $D_a$ 是非点紧暴露极大真面；全部非空真面只有原纯单点和完整 $D_a$；且

$$
S_a:=P\cap D_a=\partial_{\rm rel}D_a,\qquad
D_a=\operatorname{conv}S_a.
\tag{X130.6}
$$

这里的原面不预先要求闭。$S_a\cong S^{d_a-1}$ 是紧连通集；用到的紧性只属于各个固定球缘，不属于整个 $P$。假设 $p$ 没有三角，置

$$
A=D_p,\qquad B=\bigcup_{r\in S_p}D_r,\qquad
S=\partial_{\rm rel}K.
\tag{X130.7}
$$

$A$ 紧。$B$ 也紧：它是紧集

$$
\{(r,x,f)\in S_p\times K\times\mathcal E:
f(r)=1,\ f(x)=0\}
\tag{X130.8}
$$

在 $K$ 上的投影。这里直接使用[SAME_READBACK126.1][Q130SR]的原零关联紧投影构造；该构造只要求 $K,\mathcal E$ 紧及评价连续，不依赖该章随后针对EB3的纤维结论。两集均在 $S$ 内，$A\ne\varnothing$，且任取 $r\in S_p$，零对称给 $p\in D_r\subset B$，所以 $B\ne\varnothing$。

先证 $A\cap B=\varnothing$。否则存在 $r\in S_p$ 使 $A\cap D_r\ne\varnothing$。这个交是非空紧原面，故有一个原纯点 $t$。于是 $r,t\in S_p$ 且 $t\in D_r$，得到 $p,r,t$ 的真实三角，矛盾。交中的原纯点来自原面的极点，不是把任意混态交点当作纯点；这里复用[IX116.1式(IX116.3)][Q130IX]在可变球维数域中的取交点步骤。[SAME_READBACK126.2][Q130SR]在EB3域给出相应的关系平方表述，不将其额外纤维结论用于本条的可变维数域。

$\mathsf D_2(p)$ 给 $P\subset A\cup B$：与 $p$ 相邻的纯点在 $A$ 中；其余纯点由同一个共同邻点 $r\in S_p$ 落入 $D_r\subset B$。现检查每一张完整原球 $D_s$。若 $s\in A$，纯性给 $s\in S_p$，所以 $D_s\subset B$。若 $s\notin A$，则 $s\in B$；可取 $r\in S_p$ 使 $s\in D_r$，零对称给

$$
r\in S_s\cap A.
\tag{X130.9}
$$

连通集 $S_s$ 被其两个不交相对闭子集 $S_s\cap A$ 与 $S_s\cap B$ 覆盖，且前者非空，故 $S_s\subset A$。取凸包得 $D_s\subset A$；极大真面性使 $D_s=A$。这一步逐张使用所有原球的连通纯边界；没有从 $S_s\subset B$ 擅自推出非凸并集 $B$ 包含其凸包，也没有输入标签单射。

由此，每张完整球都包含于 $A$ 或 $B$；原纯单点亦已被覆盖。任意 $x\in S$ 都有一个相对支撑超平面，其接触集是含 $x$ 的非空原真面。完整面穷尽遂给

$$
S=A\sqcup B.
\tag{X130.10}
$$

另一方面，$D_p$ 是维数至少二的真暴露面，故 $n=\dim\operatorname{aff}K\ge3$。有限维凸体从一个相对内点作径向投影，其整个相对边界同胚于 $S^{n-1}$，因而连通。这与(X130.10)的两个非空不交闭集覆盖矛盾，证明(X130.4)。否定 $\mathsf D_2(p)$ 就是(X130.5)；$s=p$ 已由非空 $S_p$ 排除。

维数下界的控制直接复用[正五边形的完整原模型，OP2—OP3][Q130Pent]及[X122.7][Q130PentX]：$D_{p_i}=[p_{i+2},p_{i+3}]$，指标模五，且满足EB1与PR。其纯零图的边差是 $\pm2$，故为五圈，直径二且无三角。此时每条原排除边的纯边界为不连通的 $S^0$，恰好不能作上述连通推断；无须重算多边形的原锥、全效应或比较函数。

本条的原域两步覆盖到整边界分离矛盾是 `repo-derived` 推导；紧投影、原面接口、零对称及凸体边界的球面拓扑均是复用的中间事实，不是新的紧性或分类定理。该归属不主张文献穷尽或历史优先权。证毕。

**定理 130.3（两步候选的同原完整静态字典及反向）。** 在(X130.1)的整个原域，下列条件等价：

$$
\begin{gathered}
\mathrm{EB3}+\mathsf D_2,\\
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V
\text{ 实线性双射},\qquad
\Phi(\mathrm{PSD}_3)=C,\quad u\Phi=\operatorname{Tr}.
\end{gathered}
\tag{X130.11}
$$

其正向新增桥是定理130.2；静态分类及全字典直接消费[IX120.4—120.5、IX116.17—116.18][Q130IX]。原域的全部对应为

$$
\begin{gathered}
K=\{\Phi\rho:\rho\succeq0,\ \operatorname{Tr}\rho=1\},\qquad
P=\{\Phi(vv^*):v^*v=1\}\cong\mathbb{CP}^2,\\
\mathcal E=\{f_E:f_E(\Phi X)=\operatorname{Tr}(EX),\ 0\preceq E\preceq I_3\},\\
T_{\Phi(vv^*)}(\Phi\rho)=\operatorname{Tr}(vv^*\rho),\qquad
T_{\Phi(vv^*)}(\Phi(ww^*))=|v^*w|^2,\\
D_{\Phi(vv^*)}
=\{\Phi\rho:\rho\succeq0,\ \operatorname{Tr}\rho=1,\ \rho v=0\},
\qquad v^*v=w^*w=1.
\end{gathered}
\tag{X130.12}
$$

所有原凸混合被保持；全部有限数学测量 $f_j\ge0,\sum_jf_j=u$ 恰对应全部有限POVM $E_j\succeq0,\sum_jE_j=I_3$。谱分解、原joint、迹尺、中心及Jordan乘法分别取既有同一表示中的矩阵谱、正交投影组、$\operatorname{Tr}(XY)$、$\Phi(I_3/3)$ 及运输的 $(XY+YX)/2$。PR、Inj、$P$ 紧、全Pair和每条指定原零边的唯一第三点均为此后结论。局部排除球的实维数是三，整个 $K$ 的实仿射维数是八。

证明。130.2给全部原纯点属于三角，故[IX120.4][Q130IX]给每个完整 $D_p$ 的宽度为一。此时才由IX120.5调用IX116.17取得(X130.11)的同锥同单位表示，并复用其整个原静态字典。三条各自真实的零一边在130.2中没有被当作一台共同仪器；全域三结果共同效应及指定边完成由上述既有分类链供应。

反向在整个标准模型中核对。对任意单位 $v$，IX116.17的完整确认计算给全部 $vv^*\oplus B$，$0\preceq B\preceq I_{v^\perp}$，因此(X130.12)对所有原混态成立。全部支撑于 $v^\perp\cong\mathbb C^2$ 的密度矩阵由Pauli坐标组成完整闭三球，所以EB3成立。对任意两个原纯点 $`vv^*,ww^*`$，包括相同端点，因 $\dim_{\mathbb C}\operatorname{span}\{v,w\}\le2$，可取单位

$$
z\in\operatorname{span}\{v,w\}^{\perp},\qquad r=zz^*.
\tag{X130.13}
$$

原全域效应 $`f_{vv^*},f_{ww^*}`$ 分别见证 $vv^*\perp r$ 与 $ww^*\perp r$，得到全部 $\mathsf D_2$ 量词。同一个 $\Phi$ 运输整个锥、单位、效应及全部 $D_p$，并非只运输选定基。证毕。

**定义 130.4（候选及原问题的保留范围）。** 完整静态候选定义为(X130.1)的同一有限维全域、全部原EB3及 $\mathsf D_2$。白话是：每个纯态的所有原零比较对象，包括混态，合成一整颗实心三球；任意两张不相邻的原纯标签，都能找到同一个原纯标签，与它们各有真实零一边。130.2把两步可达接到每点真实三角，130.3再接到全部复三能级静态态与效应。候选不输入PR、Inj、纯点紧性、CS、球族连续、滤子或Jordan结构。

原PR仍指 $T_p(q)=T_q(p)$ 对全部原纯对成立；UF仍指[IX115.8及X124.9—124.13][Q130UF]的原全锥正延拓预算 $\sup_p\beta_{D_p}<\infty$。保留未决问题

$$
\mathrm{EB3}+\mathrm{PR}\ \stackrel{?}{\Longrightarrow}\ \mathsf D_2,
\qquad
\mathrm{EB3}+\mathrm{PR}\ \stackrel{?}{\Longrightarrow}\ \mathrm{UF}.
\tag{X130.14}
$$

[X125.5][Q130CS]的CS与UF等价仍限于其完整EB3+PR域。BILATERAL VIII121.5的局部两步四维纯点片另有Inj前件，且不提供任意原纯对的两步覆盖[Q130BV]。130.2的直接结论是每点有三角，不是给每条指定边补第三点；后者在EB3中由130.3的既有分类取得。五边形与X129的无限一球模型都不是EB3+PR反模型。这里没有断言 $\mathsf D_2$ 独立、候选逻辑上严格更弱或物理公理数最少。

单体静态字典的适用范围按[IX116.23及VIII113.11][Q130IX][Q130VIII]保留：实际来源、制备与操作、全部有限 $N$ 的共同复合及纠缠准备、全旁观正性与CP/Kraus、逐输入预算、同族事件仪器与记录、Lüders校准、原物理钟、连续动力学来源、Hamiltonian及数值 $\hbar$ 各有独立前件。数学POVM不等于可调用的实际仪器，单体几何不供应这些联合或时间合同。

[Q130VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.1—103.2：完整原域、可变球维数、共同暴露及全部原真面穷尽。"
[Q130IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1及式(IX116.3)：完整面与纯交点；IX120.4—120.5：三角、宽度及条件静态应用；IX116.17—116.18：成熟分类及同原完整静态字典；IX116.23：原过程边界。"
[Q130SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "126.1：原零关联的紧闭投影；126.2：关系平方与同处原真面。"
[Q130Pent]: ../../../Library/FiniteGeometry/janottagogolinbarrettbrunner2011polygon.md "OP2—OP3：整个原奇多边形排除边及PR；文献载体与全效应取Janotta—Gogolin—Barrett—Brunner §3.1式(5)、(6)、(8)及补效应。"
[Q130PentX]: #1226-完整-eb1-五边形的准确方法控制 "X122.7：完整原五边形的一维控制。"
[Q130UF]: #124-极端对偶零面的整球塌缩障碍与互易非塌缩重构 "X124.9—124.13：原UF预算、条件静态表示及自动UF未决项；预算原义见IX115.8。"
[Q130CS]: #125-旧完整球的共同近零确认与固定球心的真零稳定性 "X125.5：仅在完整EB3+PR域的CS与UF等价。"
[Q130BV]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md "121.5：EB3+Inj的局部两步四维片；121.7：没有任意标签到种子的两步覆盖。"
[Q130VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII113.11及所引112.9：全部原操作、全有限复合、CP、仪器、记录与时间合同。"

## 追加锚（本行以下为增补区）
