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
