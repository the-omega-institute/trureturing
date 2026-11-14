# QUANTUM ORIGIN: EXCLUSION SEGMENT RIGIDITY AND PURE LOCUS TOPOLOGY XI

## 134. 根邻完整球、曲边确认域与球加纯弧的全零集

**定义 134.1（同一载体、全部效应与完整比较）。** 对整数 $d\ge2$、$m\ge1$，在欧氏空间
$W=\mathbb R\oplus\mathbb R^d\oplus\mathbb R^m$ 中取

$$
K=K_{d,m}=\{(t,a,b):0\le t\le1,\ \|a\|\le1-t,\ \|b\|^2\le t(1-t)\}.
\tag{XI134.1}
$$

令 $V=\mathbb R\oplus W$，并定义齐次化及原单位

$$
C=\{\rho(1,z):\rho\ge0,\ z\in K\},\qquad
u(\rho,\xi)=\rho,\qquad P=\operatorname{ext}K.
\tag{XI134.2}
$$

将 $z\in K$ 与归一向量 $(1,z)\in C$ 识别。始终使用同一个全部效应区间及其限制：

$$
\begin{gathered}
C^\ast=\{g\in V^\ast:g(C)\subseteq\mathbb R_+\},\qquad
\mathcal E=[0,u]_{C^\ast},\qquad f(z)=f(1,z),\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\\
D_p=\{z\in K:T_p(z)=0\},\qquad S_p=P\cap D_p\quad(p\in P).
\end{gathered}
\tag{XI134.3}
$$

最小值的存在性包含在命题134.2的证明中。这里 $\mathcal E$ 等同于所有仿射映射
$K\to[0,1]$，不以预选效应或只在某个面上非负的仿射函数替代；全效应区间的含义参见
[Janotta–Lal，III.A，Theorem 1，式(15)—(16)](https://arxiv.org/pdf/1302.2632)。
对纯点定义 $p\perp r\Longleftrightarrow r\in D_p$；补效应 $u-f$ 使该零关系对称。
全域 EB3 指每个 $p\in P$ 的整个 $D_p$ 都仿射等价于完整闭三球；纯 PR 指
$T_p(r)=T_r(p)$ 对所有 $p,r\in P$ 成立。零关系对称和正值纯 PR 是不同条件，
比较约定参见 [Landsman，§1.3，式(1.4)—(1.9)](https://arxiv.org/pdf/quant-ph/9603005v2)。

固定单位向量 $v\in\mathbb R^d$、$e\in\mathbb R^m$，记

$$
o=(1,0,0),\qquad p_s=(0,s,0)\quad(\|s\|=1),\qquad
q=\left(\frac12,\frac v2,-\frac e2\right).
\tag{XI134.4}
$$

以下球面均指相应仿射球的相对边界，$\overline{\mathbb B}^{k}$ 表示欧氏闭单位 $k$ 球。

**命题 134.2（根覆盖与完整确认读数的联合控制）。** 对定义134.1的所有 $d,m,v,e$，
$K$ 是满维紧凸体，$C$ 是闭尖生成凸锥，$u$ 在 $C\setminus\{0\}$ 上严格正。
全部原纯点恰为

$$
P=\{(t,a,b)\in K:\|a\|=1-t,\ \|b\|^2=t(1-t)\}.
\tag{XI134.5}
$$

根及每个根邻点的完整读数和整个排除集为

$$
\begin{aligned}
T_o(t,a,b)&=t,& D_o&=\{(0,a,0):\|a\|\le1\},\\
T_{p_s}(t,a,b)&=\frac{1-t+s\cdot a}{2},&
D_{p_s}&=\{(t,-(1-t)s,b):\|b\|^2\le t(1-t)\}.
\end{aligned}
\tag{XI134.6}
$$

它们分别是完整 $d$ 球及完整 $(m+1)$ 球，且

$$
S_o=\{p_s:\|s\|=1\},\qquad
P=\bigcup_{\|s\|=1}(P\cap D_{p_s}).
\tag{XI134.7}
$$

特别地，$d=3,m=2$ 时根与全部根邻点的完整排除集同时为三球，并满足同一固定根的两步覆盖。
对 $z=(t,a,b)\in P\setminus\{o\}$，其唯一根邻关联为

$$
\pi_o(z)=p_{-a/(1-t)}\in S_o,\qquad z\in D_{\pi_o(z)}.
\tag{XI134.8}
$$

标签 $q$ 的完整确认域则为曲边域

$$
\begin{gathered}
\Omega=\{(\lambda,\mu):\lambda,\mu\ge0,
\lambda+\mu+\sqrt{\lambda^2+\mu^2}\le1\},\\
\mathcal F_q=\{f_{\lambda,\mu}:(\lambda,\mu)\in\Omega\},\\
f_{\lambda,\mu}(t,a,b)
=1-\lambda-\mu+\lambda t+\lambda v\cdot a-2\mu e\cdot b.
\end{gathered}
\tag{XI134.9}
$$

对每个 $z=(t,a,b)\in K$，置 $A=1-t-v\cdot a\ge0$、$B=1+2e\cdot b\ge0$，则

$$
\begin{gathered}
T_q(z)=1-\Lambda(A,B),\\
\Lambda(A,B)=
\begin{cases}
A/2,& A\ge2B,\\
B/2,& B\ge2A,\\
A+B-\sqrt{2AB},& A<2B\ \text{且}\ B<2A.
\end{cases}
\end{gathered}
\tag{XI134.10}
$$

在 $A=2B$ 或 $B=2A$ 时相邻表达式一致；在 $A=B=0$ 时两个轴分支均给 $\Lambda=0$。
整个零集，包括全部混态，恰为

$$
\begin{gathered}
D_q=F\cup\Gamma,\qquad
F=\left\{\left(\frac12,a,\frac e2\right):\|a\|\le\frac12\right\},\\
\Gamma=\left\{\gamma(t)=\bigl(t,-(1-t)v,\sqrt{t(1-t)}e\bigr):0\le t\le\frac12\right\}.
\end{gathered}
\tag{XI134.11}
$$

其中 $F$ 是完整 $d$ 球，$\Gamma\subset P$，两者仅交于 $(1/2,-v/2,e/2)$，并有

$$
\begin{gathered}
F\cap D_o=\varnothing,\qquad
S_q=\partial_{\rm rel}F\cup\Gamma,\\
\pi_o\left(\frac12,\frac w2,\frac e2\right)=p_{-w}\quad(\|w\|=1),
\qquad \pi_o(\gamma(t))=p_v\quad(0\le t\le1/2).
\end{gathered}
\tag{XI134.12}
$$

故横截球面 $\partial_{\rm rel}F$ 的关联满射到整个根球面，完整 $S_q$ 却还包含关联恒定的纯弧。
若 $s\in\mathbb R^d$ 为任意满足 $\|s\|=1$、$s\cdot v=0$ 的向量，则

$$
T_{p_s}(q)=\frac14,\qquad T_q(p_s)=\sqrt2-1,\qquad
T_q(p_s)-T_{p_s}(q)=\sqrt2-\frac54>0.
\tag{XI134.13}
$$

因而此控制在所有所述维数上同时失败全域 EB3 与纯 PR。
这些结论只比较同一 $K,P,\mathcal E$ 上的完整标量菜单及其零集。

证明。先建立整个菜单的存在性，再计算两类标签的全部确认效应，最后比较几何与纯读数。

由

$$
\|b\|^2\le t(1-t)
\quad\Longleftrightarrow\quad
\left(t-\frac12\right)^2+\|b\|^2\le\frac14
\tag{XI134.14}
$$

可知 $(t,b)$ 的约束是完整欧氏球；$\|a\|\le1-t$ 是凸的范数约束。
两者的交集闭、有界且凸，$(1/2,0,0)$ 满足两个严格不等式，所以 $K$ 满维紧凸。
$K$ 的凸性使其齐次化 $C$ 为凸锥。
若 $\rho_n(1,z_n)\in C$ 收敛，则首坐标 $\rho_n\to\rho\ge0$。
当 $\rho>0$ 时，$z_n$ 收敛到 $K$ 中一点；当 $\rho=0$ 时，$K$ 有界使其余坐标也趋于零。
故 $C$ 闭；首坐标非负且零截面只有零点，故 $C$ 尖，且 $u$ 在非零锥元上严格正。
$K$ 满仿射维使 $(1,K)$ 张成 $V$，所以 $C$ 生成 $V$。

每个 $V$ 上线性泛函在 $(1,K)$ 的限制唯一写成

$$
f(t,a,b)=\alpha+\beta t+c\cdot a+h\cdot b.
\tag{XI134.15}
$$

它属于 $[0,u]_{C^\ast}$ 当且仅当在全部 $K$ 上取值于 $[0,1]$。
从满维 $K$ 取 $\dim W+1$ 个仿射无关点；在这些点的评价给仿射函数空间到
$\mathbb R^{\dim W+1}$ 的线性同构。所有效应的这些评价均在 $[0,1]$，故效应系数有界。
对每个 $z\in K$ 的 $0\le f(z)\le1$ 是闭条件，因此 $\mathcal E$ 在有限维空间中紧。
$\mathcal F_p$ 是其闭子集，且包含常数效应 $1$，所以非空紧；每个 $T_p(z)$ 的最小值都达到。
特别地，$z\in D_p$ 当且仅当存在同一原菜单中的真实效应在 $p,z$ 分别取一、零。

若 $\|a\|<1-t$，可只在 $a$ 方向作非零对称小微扰；若 $\|b\|^2<t(1-t)$，
可只在 $b$ 方向作这种微扰。每种情形均把该点写为两个不同 $K$ 中点的中点，故极点必须同时饱和。
反之，若两约束均饱和，任意非平凡凸分解投影到 $(t,b)$ 后给欧氏球边界点的凸分解。
球的严格凸性迫两端的 $(t,b)$ 相同；当 $t<1$ 时，半径 $1-t$ 的 $a$ 球再次以严格凸性迫两端相同。
当 $t=1$ 时，约束直接迫 $a=b=0$。这证明(XI134.5)，也证明 $o,p_s,q$ 均为原纯点。

接着在本模型中直接求一般仿射函数的极值。令 $r=\|c\|$、$H=\|h\|$。
固定 $t$ 后，$a,b$ 两个球上的线性极值相互独立，所以

$$
\begin{aligned}
\min_K f&=\alpha+\frac{\beta-r}{2}
 -\frac12\sqrt{(\beta+r)^2+H^2},\\
\max_K f&=\alpha+\frac{\beta+r}{2}
 +\frac12\sqrt{(\beta-r)^2+H^2}.
\end{aligned}
\tag{XI134.16}
$$

具体地，固定 $t$ 的两个极值是
$\alpha+\beta t\mp r(1-t)\mp H\sqrt{t(1-t)}$。
置 $\sigma=2t-1$、$\eta=2\sqrt{t(1-t)}$，则 $(\sigma,\eta)$ 遍历 $\eta\ge0$ 的单位半圆。
对任意实数 $L$ 及 $H\ge0$，Cauchy–Schwarz 给
$\max(L\sigma+H\eta)=\sqrt{L^2+H^2}$ 和
$\min(L\sigma-H\eta)=-\sqrt{L^2+H^2}$。
若 $(L,H)\ne(0,0)$，分别取对应的单位方向达到；若 $H=0$，所需方向为半圆端点；
若 $L=H=0$，所有半圆点都达到。代入 $L=\beta-r$ 或 $L=\beta+r$ 即得(XI134.16)。
这是各维欧氏球的直接计算，未从某个特定 $d,m$ 外推。
支持函数与支撑法向的成熟凸分析背景参见
[Boyd–Vandenberghe，Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)；
这里的一般极值式只作为完整确认域计算的中间步骤。

先求根侧菜单。若 $f(o)=1$，则 $\alpha=1-\beta$。
若 $H>0$，取 $t=1-\varepsilon$、$a=0$、
$b=\sqrt{\varepsilon(1-\varepsilon)}h/H$，所得值相对 $f(o)$ 增加
$-\beta\varepsilon+H\sqrt{\varepsilon(1-\varepsilon)}$，对充分小的正 $\varepsilon$ 为正，矛盾。
所以 $h=0$。在 $t=0$ 的完整 $a$ 球上，上下界分别给
$r\le\beta$、$\beta+r\le1$；这两个条件反向也使两个端面及它们之间的全部读数落在 $[0,1]$。
因而对任意 $z\in K$，

$$
f(z)-t=(1-\beta)(1-t)+c\cdot a
\ge(1-\beta-r)(1-t)\ge0.
\tag{XI134.17}
$$

效应 $f(z)=t$ 属于同一菜单并确认 $o$，故 $T_o(z)=t$，给出完整 $D_o$ 及 $S_o$。

对任意单位 $s$，若 $f(p_s)=1$，在 $t=0$ 的完整 $a$ 球上达到最大迫
$c=rs$、$r\ge0$ 及 $\alpha=1-r$。
若 $H>0$，沿 $a=(1-t)s$、$b=\sqrt{t(1-t)}h/H$，读数相对 $f(p_s)$ 增加
$ (\beta-r)t+H\sqrt{t(1-t)}$，对充分小的正 $t$ 为正，矛盾。因此 $h=0$。
再由 $a=(1-t)s$ 上的上界，以及 $t=0,a=-s$ 和 $o$ 上的下界，分别得到
$\beta\le r$、$r\le1/2$、$\beta\ge r-1$。
反之，这些条件使固定 $t$ 时的最大值不超过一、最小值不小于零，因为它们都是端点值的线性插值。
所以完整菜单恰为

$$
\mathcal F_{p_s}
=\{1-r+\beta t+rs\cdot a:0\le r\le1/2,\ r-1\le\beta\le r\}.
\tag{XI134.18}
$$

对任意 $z\in K$，先以 $t\ge0$ 取 $\beta=r-1$，再以
$1-t-s\cdot a\ge0$ 取 $r=1/2$，即得

$$
\min_{\mathcal F_{p_s}}f(z)
=\min_{0\le r\le1/2}\{1-t-r(1-t-s\cdot a)\}
=\frac{1-t+s\cdot a}{2}.
\tag{XI134.19}
$$

效应 $(1-t+s\cdot a)/2$ 在全部 $K$ 合法并达到该值。
零值迫 $s\cdot a=-(1-t)$，结合范数约束等价于 $a=-(1-t)s$，包括 $t=1$。
完整球的仿射参数为

$$
(\sigma,\eta)\longmapsto
\left(\frac{1+\sigma}{2},-\frac{1-\sigma}{2}s,\frac\eta2\right),
\qquad \sigma^2+\|\eta\|^2\le1.
\tag{XI134.20}
$$

此映射单射，像恰为整个 $D_{p_s}$，故其维数为 $m+1$。
同时 $D_o$ 的 $a$ 坐标给完整 $d$ 球。两者同时是三球恰要求 $d=3,m=2$，
并非确认域计算对 $m$ 的限制。
对任何 $z\in P\setminus\{o\}$，有 $t<1$、$a=(1-t)w$、$\|w\|=1$；
它属于 $D_{p_s}$ 当且仅当 $s=-w$。而 $o$ 属于所有 $D_{p_s}$。
这证明覆盖和唯一关联式(XI134.7)—(XI134.8)。每个 $p_s\in S_o$，
故覆盖的同一个标签 $p_s$ 同时见证 $o\perp p_s$ 与 $z\perp p_s$，包括目标 $z=o$。

现在求 $q$ 的完整菜单，必要性中不删去零法向。
任取(XI134.15)中的 $f\in\mathcal F_q$。在 $t=1/2$ 的两个独立完整球上，
$q$ 达到全域最大值一，迫
$c=\lambda v$、$h=-2\mu e$，其中 $\lambda,\mu\ge0$。
沿整个可行曲线

$$
\tau\longmapsto\bigl(\tau,(1-\tau)v,-\sqrt{\tau(1-\tau)}e\bigr)
\tag{XI134.21}
$$

的读数为 $\alpha+\lambda+(\beta-\lambda)\tau+2\mu\sqrt{\tau(1-\tau)}$。
$\tau=1/2$ 为内部极大点，导数给 $\beta=\lambda$，即使 $\mu=0$ 也成立。
再由 $f(q)=1$ 得 $\alpha=1-\lambda-\mu$。代入(XI134.16)，

$$
\max_K f_{\lambda,\mu}=1,\qquad
\min_K f_{\lambda,\mu}=1-\lambda-\mu-\sqrt{\lambda^2+\mu^2}.
\tag{XI134.22}
$$

所以全域非负性必要地给 $(\lambda,\mu)\in\Omega$。
反向，对每个 $\Omega$ 中的参数，(XI134.22)证明该仿射函数在全部 $K$ 上处于 $[0,1]$，
直接代入又给 $f_{\lambda,\mu}(q)=1$，故它确是原全域确认效应。
这证明(XI134.9)的双向完整性；$\lambda=0$ 时 $0\le\mu\le1/2$，
$\mu=0$ 时 $0\le\lambda\le1/2$，原点给常数效应一，均未删除。

对任意 $z\in K$，$v\cdot a\le1-t$ 给 $A\ge0$，
$e\cdot b\ge-\sqrt{t(1-t)}\ge-1/2$ 给 $B\ge0$，并且

$$
f_{\lambda,\mu}(z)=1-A\lambda-B\mu,\qquad
\Lambda(A,B)=\max_{(\lambda,\mu)\in\Omega}(A\lambda+B\mu).
\tag{XI134.23}
$$

$\Omega$ 闭且有界，因此这个最大值也达到。
若 $A\ge2B$，则对每个 $\Omega$ 中参数，

$$
A\lambda+B\mu
\le A(\lambda+\mu/2)
\le\frac A2\bigl(\lambda+\mu+\sqrt{\lambda^2+\mu^2}\bigr)
\le\frac A2.
\tag{XI134.24}
$$

真实效应参数 $(\lambda,\mu)=(1/2,0)$ 达到该值。
若 $B\ge2A$，交换两坐标得 $B/2$，由 $(0,1/2)$ 达到。
当 $A=B=0$ 时，目标恒零，所有参数均达到，特别可取 $(0,0)$，此时 $T_q(z)=1$。

余下 $A<2B$、$B<2A$，于是 $A,B>0$。令 $L=A+B-\sqrt{2AB}$，
则 $0<L<\min(A,B)$，且

$$
(A-L)^2+(B-L)^2=L^2.
\tag{XI134.25}
$$

因而

$$
\begin{aligned}
A\lambda+B\mu
&=L(\lambda+\mu)+(A-L)\lambda+(B-L)\mu\\
&\le L\bigl(\lambda+\mu+\sqrt{\lambda^2+\mu^2}\bigr)\le L.
\end{aligned}
\tag{XI134.26}
$$

取真正属于原菜单的参数

$$
\lambda=\frac{A-L}{A+B-L},\qquad
\mu=\frac{B-L}{A+B-L},\qquad
\sqrt{\lambda^2+\mu^2}=\frac L{A+B-L}.
\tag{XI134.27}
$$

两参数严格正，三项之和为一，且(XI134.26)中的两处不等式均取等号，故达到 $L$。
在 $A=2B$ 时 $A+B-\sqrt{2AB}=A/2$，在 $B=2A$ 时等于 $B/2$；
这些等式也包括原点。由此得到覆盖全部非负 $A,B$ 的(XI134.10)，
不是仅比较两个候选效应的读数。

为穷尽整个 $D_q$，逐一分类所有参数对应的零面。记 $R=\sqrt{\lambda^2+\mu^2}$。
若 $\lambda+\mu+R<1$，(XI134.22)给严格正的全域最小值，没有零点。
边界 $\lambda+\mu+R=1$ 上，若 $\mu=0$，则 $\lambda=1/2$，且

$$
f_{1/2,0}(t,a,b)=\frac{1+t+v\cdot a}{2}\ge t.
\tag{XI134.28}
$$

零值必须 $t=0,a=-v,b=0$，反向该点确为零，故整个零面只有 $p_{-v}$。
若 $\lambda=0$，则 $\mu=1/2$，效应为 $1/2-e\cdot b$。
零值迫

$$
\frac12=e\cdot b\le\|b\|\le\sqrt{t(1-t)}\le\frac12,
\tag{XI134.29}
$$

所以 $t=1/2,b=e/2$；$a$ 的唯一限制为 $\|a\|\le1/2$。
反向这些点全为零，故该效应的整个零面恰为 $F$。

若边界上 $\lambda,\mu>0$，任何零点必须在(XI134.22)的全域最小值处取等。
固定 $t$ 的线性极值和半圆上的严格取等条件，分别迫

$$
a=-(1-t)v,\qquad
2t-1=-\frac\lambda R,\qquad
2\sqrt{t(1-t)}=\frac\mu R,\qquad
b=\frac\mu{2R}e.
\tag{XI134.30}
$$

于是 $t=(1-\lambda/R)/2\in(0,1/2)$，整个零面只有 $\gamma(t)$ 这一个原纯点。
这穷尽 $\Omega$ 内部、两条轴及正参数边界的所有零点，证明 $D_q\subseteq F\cup\Gamma$。

反向不仅需要零点候选，还需同一全效应菜单中的见证。
整个 $F$ 已由 $f_{0,1/2}$ 见证。任给 $0\le t\le1/2$，令

$$
U=1-2t,\qquad W=2\sqrt{t(1-t)},\qquad
\lambda=\frac U{1+U+W},\qquad \mu=\frac W{1+U+W}.
\tag{XI134.31}
$$

因 $U,W\ge0$、$U^2+W^2=1$，有 $\lambda+\mu+R=1$，故该效应属于 $\mathcal F_q$。
在 $\gamma(t)$ 处，$A=1+U$、$B=1+W$，从而

$$
A\lambda+B\mu
=\frac{U+W+U^2+W^2}{1+U+W}=1.
\tag{XI134.32}
$$

所以 $f_{\lambda,\mu}(\gamma(t))=0$。
两个端点分别给 $(1/2,0)$ 与 $(0,1/2)$，也由真实原效应实现。
因所有效应非负且最小值达到，这就证明 $F\cup\Gamma\subseteq D_q$ 及(XI134.11)的完整集合等式。

由(XI134.5)，$\Gamma$ 的全部点都纯，而 $P\cap F$ 恰为 $\partial_{\rm rel}F$。
由 $t$ 坐标知 $F\cap\Gamma$ 只有 $t=1/2$ 的端点，且 $F\cap D_o=\varnothing$。
将 $F$ 的纯点和 $\Gamma$ 分别代入同一模型的(XI134.8)，即得(XI134.12)。
球面关联的逆映射为 $p_s\mapsto(1/2,-s/2,e/2)$，故横截球面确实映满根球面；
但完整 $S_q$ 还含整条 $\Gamma$，关联在这条弧上恒为 $p_v$。

因 $d\ge2$，可取单位 $s\perp v$；因 $m\ge1$，单位 $e$ 也存在，无须 $m\ge2$。
完整反向菜单(XI134.18)—(XI134.19)在 $q$ 处给 $T_{p_s}(q)=1/4$。
另一方面，$p_s$ 在(XI134.23)中的 $A=B=1$，故完整三分支式给 $T_q(p_s)=\sqrt2-1$。
其达到参数为 $\lambda=\mu=1/(2+\sqrt2)$，不是未经最小化的候选读数。
两点的纯性已由(XI134.5)支付；$2>25/16$ 给(XI134.13)的严格正差，故纯 PR 失败。

最后，取 $p_{-v}=\gamma(0)\in\Gamma$ 和 $z_0=(1/2,0,e/2)\in F$。
它们的中点

$$
z_*=(1/4,-v/2,e/4),\qquad
\|{-v/2}\|=\frac12<\frac34,\qquad
\|e/4\|^2=\frac1{16}<\frac3{16}
\tag{XI134.33}
$$

在 $K$ 内部，既不在 $F$ 也不在 $\Gamma$，所以不在 $D_q$。
因此 $D_q$ 非凸，不可能仿射等价于完整三球。这与
[IX114.11，式(IX114.36)—(IX114.42)](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)
中全菜单零集非凸的现象相容；那里是参数三角形及两个完整三球之并，
这里的曲边确认域、三个最优分支和正参数边界扫出的纯弧由(XI134.9)—(XI134.32)联合刻画。
非凸中点只说明相应全域球形前件失败。

与完整球域的条件结论比较时，量词不能缩减。
[SAME132.1](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)
以每个原标签的完整 $\mathrm{EB}_{\ge1}$ 为前件，给整个 $K$ 的纯点—排除球覆盖及径向三纯项；
它不输入 Inj，也不把三纯项自动变成两两正交谱分解或共同三结果。
本模型的根邻覆盖不能替换该全标签前件。
[THREE_COPY VIII130.7—130.9](QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md)
的 $\mathsf{FA}_4$ 及纯极限紧性桥保留完整 EB3+$\mathsf{Conn}$ 域和其指定零菜单；
本模型中显式集合的计算不支付该域的一般纯紧性或 $\mathsf{FA}_4$ 自动性。

[X133.1、133.5—133.6](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md)
传播的是全部标签完整 EB3 加一个固定根的覆盖；其中满射的源是完整 $S_q$，不是任取横截球的球面。
在 $d=3,m=2$ 的此控制中，根覆盖、根与根邻三球、横截球面的关联满射同时成立，
但完整 $D_q$ 非凸且完整 $S_q$ 含恒关联纯弧，所以不满足该传播定理的全域 EB3 前件。
它也失败纯 PR，因而不是 EB3+PR 的反模型，不判定(X133.32)的固定根自动性，
不提供同原全局分类、实际标签返回、共同三结果、物理仪器或物理实现。证毕。

## 追加锚（本行以下为增补区）


## 135. 原混合等价关系的球心下降与同锥量子重构

**定义 135.1（完整原域及球心替换）。** 沿用 [THREE_COPY VIII131.1][XI135TC] 的原对象：非零有限维实空间 $V$、闭尖生成凸锥 $C$、严格正泛函 $u$，整个紧基 $K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$、整个原效应区间 $\mathcal E=[0,u]_{C^\ast}$，以及

$$
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\tag{XI135.1}
$$

本章完整 EB3 指每个原 $p\in P$ 的整个 $D_p$ 仿射等价于非退化实心闭三球，记其唯一仿射中心为 $c_p$。不改 $C,u,K,P,\mathcal E$，不预设 Inj、PR、纯域闭性、共同中心、正回缩、Pair 或谱性。$u$ 是原质量泛函，不与后面派生的 $U\in V$ 混同。

直接复用 [FINITE_PURE VII103.2][XI135FP] 及 [EXCLUSION IX116.1、118.4][XI135IX]：每个 $D_p$ 是非点紧暴露极大真面；全部非空真面只有纯单点和完整排除球；不同球至多交一个纯点；$P\cap D_p=\partial_{\rm rel}D_p$；纯零关系 $p\perp q\Longleftrightarrow q\in D_p$ 对称。球心 $c_p$ 属于 $D_p$ 的相对内部，因而不是原纯点。原全效应在有限维中紧，故上述 minimum 达到。

定义球心混合相容条件 $\mathsf{MC}$：对任意正整数 $m,n$、全部原纯点 $p_i,q_j$ 及非负实权重 $\lambda_i,\mu_j$，

$$
\begin{gathered}
\sum_{i=1}^m\lambda_i=\sum_{j=1}^n\mu_j=1,\qquad
\sum_{i=1}^m\lambda_i p_i=\sum_{j=1}^n\mu_j q_j\\
\Longrightarrow\qquad
\sum_{i=1}^m\lambda_i c_{p_i}=\sum_{j=1}^n\mu_j c_{q_j}.
\end{gathered}
\tag{XI135.2}
$$

量词包括零权、重复标签以及同一原态的所有有限纯分解。这是球心替换保持两份混合表达的原态相等关系，不只是排列同一份表达的项；也不是顺序测量交换。

**定理 135.2（全刻度原比较的严格球心反序）。** 在完整 EB3 域，任取 $p,q\in P$ 及同一 $f\in\mathcal E$，若 $f(p)=1,f(q)=0$，则

$$
f(c_p)\le\frac12\le f(c_q),\qquad f(c_p)<f(c_q).
\tag{XI135.3}
$$

证明。$f$ 给 $q\in D_p$，补效应 $u-f$ 给 $p\in D_q$。中心反射分别给

$$
r=2c_p-q\in D_p,\qquad s=2c_q-p\in D_q.
\tag{XI135.4}
$$

全域 $0\le f\le1$ 使 $f(r)=2f(c_p)\le1$、$f(s)=2f(c_q)-1\ge0$，得到两个弱界。若两中心读数相同，它们只能都等于 $1/2$，于是 $f(r)=1$。$r$ 是 $D_p$ 的球面点，故原纯；同一 $f$ 在 $r,q$ 取一、零，补效应给 $r\in D_q$。此时 $p,r\in D_q$ 都使 $f$ 达到一。$f|_{D_q}$ 因 $f(c_q)=1/2,f(p)=1$ 非恒定，而非恒定仿射泛函在仿射欧氏球上只有一个最大点。因此 $r=p$，与 $r\in D_p$、$T_p(p)=1$ 矛盾。故严格界成立。这里两颗球均须是原完整排除集；没有把局部球上任意仿射尺当成全原效应。证毕。

**推论 135.3（完整球心族不损失仿射维数）。** 在同一原域，

$$
\operatorname{aff}\{c_p:p\in P\}=\operatorname{aff}K,
\qquad
\operatorname{span}_{\mathbb R}\{c_p:p\in P\}=V.
\tag{XI135.5}
$$

证明。若球心仿射包是真子空间，存在在 $\operatorname{aff}K$ 上非恒定、却在全部 $c_p$ 上恒定的实仿射泛函 $h$。令 $a=\min_Kh<b=\max_Kh$，将 $(h-a)/(b-a)$ 唯一齐次延拓为 $V$ 上的线性泛函 $f$。其在整个 $K$ 上取值于 $[0,1]$；由 $C=\mathbb R_+K$，延拓属于原 $\mathcal E$，包括零元上的界。

紧凸的最小面、最大面各有原纯点 $q,p$，满足 $f(q)=0,f(p)=1$。定理135.2遂给 $f(c_p)<f(c_q)$，违反球心恒值。故仿射包等于整个 $\operatorname{aff}K$。$K$ 张成 $V$，且所有球心均满足 $u(c_p)=1$，便得线性张成结论。证毕。

**定理 135.4（混合相容给可逆正球心图及统一非塌缩）。** 若完整 EB3 另满足 $\mathsf{MC}$，则存在唯一实线性映射 $R:V\to V$，满足

$$
R(p)=c_p\quad(p\in P),\qquad R(C)\subseteq C,\qquad uR=u.
\tag{XI135.6}
$$

此 $R$ 是实线性双射，但此处不声称 $R^{-1}$ 正。球标签忠实，$P$ 在原 $K$ 中闭而紧；对任意辅助欧氏范数，

$$
\delta=\operatorname{dist}(P,R(P))>0,\qquad
\inf_{p\in P}\operatorname{diam}D_p\ge2\delta>0.
\tag{XI135.7}
$$

证明。有限维紧凸基满足 $K=\operatorname{conv}P$，因而 $P$ 线性张成 $V$。任意有限实线性关系 $\sum_i\alpha_i p_i=0$ 经 $u$ 给 $\sum_i\alpha_i=0$。若非全部系数为零，将正负系数分组，两边总质量同为某个 $t>0$；除以 $t$ 得两份同一原态的有限纯混合。$\mathsf{MC}$ 给 $\sum_i\alpha_i c_{p_i}=0$。因此纯生成元的赋值 $p\mapsto c_p$ 唯一线性下降为 $R$。球心属于 $K$、$K=\operatorname{conv}P$ 及锥齐次性给 $R(C)\subseteq C$，并给 $uR=u$。这段生成元下降是成熟线性代数，不计为新增刚性。

推论135.3使 $R(V)$ 包含一个张成 $V$ 的集合，故 $R$ 满射；有限维使之双射。若 $D_p=D_q$，唯一球心给 $R(p)=R(q)$，可逆性给 $p=q$，取得 Inj。

现在证明 $P$ 闭，而不先用它选紧纯子列。设 $p_n\in P,p_n\to x\in K$；反设 $x$ 混。紧 $K$ 的非空紧子集空间允许取子列使 $D_{p_n}\to G\ne\varnothing$。已有 Inj，故准确应用 IX118.4：若 $G$ 非点则极限标签纯；在本分支只能 $G=\{r\}$，且 $r\in P$。每个 $c_{p_n}\in D_{p_n}$，于是

$$
R(x)=\lim_nR(p_n)=\lim_nc_{p_n}=r.
\tag{XI135.8}
$$

但非纯 $x$ 可写成 $x=t y+(1-t)z$，其中 $y,z\in K$、$y\ne z$、$0<t<1$。正且保质量的 $R$ 将它送成 $K$ 中两个不同点 $R(y),R(z)$ 的严格凸组合，因为 $R$ 单射。这与 $R(x)=r$ 原纯矛盾。所以 $P$ 闭而紧。

$R(P)$ 亦紧；每个 $R(p)=c_p$ 都非纯，故它与紧 $P$ 不交，给 $\delta>0$。对每颗原球任选一个原纯球面点 $q\in P\cap D_p$；其中心反射 $q'=2c_p-q$ 仍在同一球面，故

$$
\operatorname{diam}D_p\ge\|q-q'\|
=2\|q-c_p\|\ge2\delta.
\tag{XI135.9}
$$

这里仅用辅助环境尺，未假设各球在该尺下为圆球。非塌缩来自两不交紧集的正距离；既未把单射自动当作逆映射正性，也未在证明闭性前预用紧 $P$。证毕。

**定理 135.5（球心混合相容的完整同原静态分类）。** 在定义135.1的全部原域，以下两项等价：

1. 完整 EB3 加 $\mathsf{MC}$；
2. 存在实线性双射 $\Phi:\operatorname{Herm}_3(\mathbb C)\to V$，使

$$
\Phi(\operatorname{PSD}_3(\mathbb C))=C,\qquad
u\Phi=\operatorname{Tr}.
\tag{XI135.10}
$$

在这些等价条件下，同一个 $\Phi$ 给

$$
U=\Phi(I_3),\qquad
c_p=\frac{U-p}{2},\qquad
R(x)=\frac{u(x)U-x}{2}\quad(x\in V).
\tag{XI135.11}
$$

证明。$1\Rightarrow2$ 的新增桥是定理135.2—135.4。其终点恰为完整 EB3、Inj 及原整球统一正直径下界，逐项满足 IX118.8第二项。此时直接消费 IX118.6—118.8 的既有分类，不重证其真实球丛、ENR 同调流形、Gysin、支持对偶、全 Pair 或 Jordan 桥，也不预先把它们作为本章输入。

$2\Rightarrow1$ 及中心公式复用同原矩阵字典：对秩一纯投影 $P_v=vv^\ast$，完整 $D_{\Phi(P_v)}$ 是 $v^\perp$ 上所有归一正矩阵的三球，唯一球心为 $\Phi((I_3-P_v)/2)$。故同一纯混合 $x=\sum_i\lambda_i p_i$ 的球心替换恒为 $(U-x)/2$，与分解无关；全部零权及重复标签均包含。线性生成再给全 $V$ 上的135.11。共同中心公式是这一分类的后果，没有反向用于135.2—135.4。证毕。

**条件应用 135.6（现有静态量子公理的同对象对应）。** 在定理135.5的等价条件下，已有 IX118.8、VIII113.7—113.9 和 THREE_COPY VIII131.7 的静态字典通过同一个 $\Phi$ 逐项适用：

| 原对象 | 同原对应及结论 |
| --- | --- |
| 全载体、质量与全态 | $\dim_{\mathbb R}V=9$；整个 $C$ 是全部 PSD 矩阵像，包括零及任意非负质量；$K$ 是全部迹一密度矩阵，仿射维数八。 |
| 全部原纯态 | $p_v=\Phi(vv^\ast)$，$\|v\|=1$；非零复向量只按非零复倍数取商，完整纯域为 $\mathbb{CP}^2$，实维四。 |
| 原效应与概率 | 全部且仅有 $f_M(\Phi X)=\operatorname{Tr}(MX)$、$0\preceq M\preceq I_3$；对每个原混态是 Born 评价。 |
| 全确认菜单与最低比较 | $M=P_v+B$、$B=(I-P_v)B(I-P_v)$、$0\preceq B\preceq I-P_v$；least 为 $P_v$，$T_{p_v}(\Phi\rho)=v^\ast\rho v$，纯比较为 $|v^\ast w|^2$，交换两端不变。 |
| 完整排除及三元提升 | $D_{p_v}$ 为 $\rho v=0$ 的整个密度三球，纯球缘为 $\mathbb{CP}^1\cong S^2$；每条纯零边有唯一第三点，三者的 least 效应和为 $u$。 |
| 谱与数学测量 | 全态有允许零权、重谱的三项正交谱分解；全部有限正效应单位分解恰为全部有限 POVM。 |
| 派生几何 | 共同内积为迹配对，原锥自对偶；Jordan 积为 $(XY+YX)/2$ 的运输。总体中心为 $U/3$；球心替换是以该点为中心、比例 $-1/2$ 的仿射映射。 |

证明。定理135.5取得的锥及单位同构精确满足所引既有字典；各行只是同一原对象的运输，不另计新的 Hilbert、Born、谱或测量重构定理。特别地，球心图虽正且保质量，却不是由本条件供应的实际事件：在复矩阵字典中它是 $X\mapsto(\operatorname{Tr}(X)I_3-X)/2$，静态正性并不代付全旁观完全正性。证毕。

**约定 135.7（完整候选、适用边界与关系图景）。** 本章的完整静态候选为 $\boxed{\mathrm{EB3}+\mathsf{MC}}$：保留同一原全态与全效应，确认每个纯标签时能完全排除的全部态是一颗完整实心三球；同一个混态无论如何写成有限纯混合，将每个纯分量换成它所排除的完整球的球心并保留权重后，仍得到同一个原态。对两份混合表达所定义的“原态相同”这一二元关系，球心替换是相容的。这比单纯重排同一份混合多出实际约束，而不要求先后测量可交换。

直观地，每个纯标签都带着一颗自己排除的完整三球。把原标签换成那颗球的中心，这个动作必须只认原来的态，不认描述它的配方。先证明这些中心没有丢掉任何仿射方向，再证明这个统一球心图不能把不同原态压成同一点。若纯标签趋向混态，整颗排除球会被旧极限定理迫成一个纯点；球心图的可逆性却不允许混态变纯，于是这种塌缩被排除。纯点与球心因而成为两团互不接触的紧集，每颗球都有统一的非零大小。既有分类遂把全部球接成同一个复三能级状态体；最后才发现，所有球心替换恰好都是朝同一个总体中心反向缩小一半。

$\mathsf{MC}$ 是否由裸 EB3、或由 EB3 加纯比较互易 PR 自动推出，本章均未证明，也未给相应完整原域反模型。该候选与已有完整同原量子分类等价，不主张严格减少独立公理数量、最弱性或逻辑独立性。它把待付条件集中为同一混态不同配方之间的一条相容关系；球心尊重混合不是从定义自动取得的事实。

全部来源、非负质量、所有实际有限复合与纠缠、三份资源、全旁观 CP、逐输入预算、事件仪器、记录、所有合法未来、原物理钟、连续动态来源、Hamiltonian、能量识别和数值 $\hbar$，均完整继承 THREE_COPY VIII131.8 及其传递引用的全部前件与量词。此处没有改变这些原消费者合同；单体静态分类没有供应这些实际实现。三球的仿射维数也不是物理空间维数。

**约定 135.8（数学来源与新增桥）。** 本章采用 `repo-derived` 综合归属。原面、极限标签和非塌缩分类分别复用 FINITE_PURE VII103.2、EXCLUSION IX116.1与118.4、118.6—118.8；静态字典与全部外延合同复用 THREE_COPY VIII131.7—131.8。有限凸生成、仿射关系的正负分组、有限维满射即双射、非恒定仿射尺在欧氏球上的唯一最大点、紧集间正距离及紧子集空间的 Hausdorff 子列均为成熟中间工具。

新增承重步骤为：135.2中同一全刻度原效应对两个内生球心的严格反序；由此强迫全部球心张成原域；将混合相容给出的线性图接为可逆图，再用原混标签塌缩判据排除非纯极限，最后取得分类实际需要的统一直径下界。生成元延拓本身、中心公式的矩阵计算及已有分类均不计为新增内容。一般状态空间与全部效应的背景沿用134.1所引 Janotta—Lal；交换纯比较端点与动力学的区分沿用134.1所引 Landsman。这里不以这些文献的名称替代本章新增桥，也不作全球优先权断言。

[XI135TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII131.1完整原域，131.7同原静态字典，131.8所有物理消费者合同。"
[XI135FP]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2完整排除面的暴露、极大性及全部原真面穷尽。"
[XI135IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1球面原纯及点交；118.4精确极限标签判据；118.6—118.8统一正直径到同原复三能级分类。"

## 追加锚（本行以下为增补区）

## 136. 一张全效应的纯态判别与排除球全轴间隙

**定义 136.1（原球心图及完全分离关系）。** 保留135.1的同一有限维原 $V,C,u,K,P,\mathcal E,\mathcal F_p,T_p,D_p$。本章先允许每个完整 $D_p$ 是任意正维实心仿射欧氏闭球，维数可以随 $p$ 变化，仍记其中心为 $c_p$。另外假定实际存在连续仿射映射 $R:K\to K$，满足 $R(p)=c_p$，并满足原球标签单射

$$
D_p=D_q\ \Longrightarrow\ p=q\qquad(p,q\in P).
\tag{XI136.1}
$$

这里仿射性遍历全部原态和实权重，不是只在某个球内的仿射性。完整 EB3 加135.1的 $\mathsf{MC}$ 已由135.2—135.4中纯点闭性论证之前的部分供应这两个条件；本章不使用135.4的纯点紧性结论或135.5的矩阵分类。

定义同一原效应的完全分离关系及其最大间隙：

$$
\begin{aligned}
\Gamma_R&=\{(x,f)\in K\times\mathcal E:f(x)=1,\ f(Rx)=0\},\\
d_R(x)&=\max_{f\in\mathcal E}\bigl(f(x)-f(Rx)\bigr).
\end{aligned}
\tag{XI136.2}
$$

全效应区间在有限维中紧，故最大值达到。$R$ 在此是原几何上的静态仿射图，不预设为可执行操作。

**定理 136.2（纯态是闭的全效应分离关系）。** 在定义136.1的原域，

$$
\boxed{
P=\operatorname{pr}_K\Gamma_R=d_R^{-1}(\{1\}).
}
\tag{XI136.3}
$$

因此原全部纯态集合 $P$ 紧。并且 $d_R:K\to[0,1]$ 连续；对每个 $\eta>0$，存在 $\varepsilon>0$，使全部原态满足

$$
d_R(x)>1-\varepsilon
\quad\Longrightarrow\quad
\operatorname{dist}(x,P)<\eta.
\tag{XI136.4}
$$

距离使用任意固定辅助欧氏范数；不声称存在与原模型无关的数值模量。

证明。先记录将要实际使用的原共同零面接口。任取 $p\in P$，若 $f\in\mathcal F_p$ 且 $f(c_p)=0$，则对 $y\in D_p$，中心反射给 $y'=2c_p-y\in D_p$。原效应非负，故

$$
0=f(c_p)=\frac{f(y)+f(y')}{2}
\quad\Longrightarrow\quad f(y)=0.
$$

反向，$y\in K$ 且 $f(y)=0$ 时，同一 $f\in\mathcal F_p$ 见证 $T_p(y)=0$。因此

$$
D_p=K\cap\ker f.
\tag{XI136.5}
$$

$c_p\in D_p$ 以及原 minimum 达到，总能供应这样的 $f$。这是 [FINITE_PURE VII103.2][XI135FP] 已有的共同零确认步骤；此处只重述被消费的等式，不使用全部真面分类。它同时保证 $D_p$ 是原面。因为球正维，$c_p$ 不是原纯点。

若 $x=p\in P$，取上述共同零确认效应就有 $f(x)=1,f(Rx)=f(c_p)=0$，所以 $P\subseteq\operatorname{pr}_K\Gamma_R$。

反之，设 $(x,f)\in\Gamma_R$。有限维紧凸集的有限极点分解定理给出

$$
x=\sum_{i=1}^m\lambda_i p_i,\qquad
p_i\in P,\quad\lambda_i>0,\quad\sum_i\lambda_i=1.
$$

仿射性、全域效应界及两端饱和给

$$
1=\sum_i\lambda_i f(p_i),\qquad
0=\sum_i\lambda_i f(c_{p_i}),\qquad
f(p_i)\le1,\quad f(c_{p_i})\ge0.
$$

因所有权重正，逐项必有 $f(p_i)=1$ 及 $f(c_{p_i})=0$。于是(XI136.5)使全部 $D_{p_i}$ 都等于同一个 $K\cap\ker f$；标签单射再使全部 $p_i$ 相同。因此 $x$ 纯，得到第一个等式。这里既未从“不同标签”直接推“不同效应”，也未在混合分解前假定 $P$ 闭。

$\Gamma_R$ 是紧 $K\times\mathcal E$ 的闭子集，其投影紧；故 $P$ 紧。这个步骤没有选取任何排除球的 Hausdorff 极限，也未调用 IX118.4 的极限标签定理。

由于 $0\le f(x),f(Rx)\le1$，间隙不超过一；零效应使最大间隙非负。最大值达到时，$f(x)-f(Rx)=1$ 恰好等价于 $f(x)=1,f(Rx)=0$，得到第二个等式。

在 $\operatorname{aff}K$ 的平移空间上，令 $A$ 为 $x\mapsto x-Rx$ 的线性部分，并令 $M=\max_{f\in\mathcal E}\|f\|$。对 $x,y\in K$，

$$
|d_R(x)-d_R(y)|\le M\|A\|\,\|x-y\|.
\tag{XI136.6}
$$

这由每张原效应的相同界取最大直接得到，故 $d_R$ 连续。对给定 $\eta>0$，集合 $H_\eta=\{x\in K:\operatorname{dist}(x,P)\ge\eta\}$ 紧且不交 $P$。若它非空，取 $\varepsilon=1-\max_{H_\eta}d_R>0$；若为空，任取 $\varepsilon>0$。由(XI136.3)即得(XI136.4)。证毕。

**定理 136.3（每颗完整球的全部半轴统一非退化）。** 在定义136.1的原域，固定任意辅助欧氏范数，令 $L_p=\operatorname{lin}(D_p-c_p)$。则

$$
\delta=\operatorname{dist}(P,R(P))>0,\qquad
c_p+\delta\,\overline B_{L_p}\subseteq D_p
\quad(p\in P).
\tag{XI136.7}
$$

特别地，每颗完整排除椭球在该辅助尺下的全部半轴都至少为 $\delta$，并有 $\operatorname{diam}D_p\ge2\delta$。

证明。定理136.2给紧 $P$，连续性给紧 $R(P)$。每个 $R(p)=c_p$ 都是正维原面 $D_p$ 的中心，因而非纯，所以两紧集不交，得到严格正距离。仿射球的每个相对边界点 $q$ 都是该球的极点；$D_p$ 是原面，故 $q\in P$。因此

$$
\|q-c_p\|\ge\delta
\qquad(q\in\partial_{\rm rel}D_p).
$$

对 $L_p$ 的每条单位方向 $v$，沿射线 $c_p+t v$ 首次遇到的边界点距离至少为 $\delta$；由凸性，$0\le t\le\delta$ 的整段都在 $D_p$。遍历所有方向便得内球包含式。中心反射再给直径界。本证明允许不同球在辅助环境尺下为不同椭球，未输入共同物理内积。证毕。

**条件应用 136.4（完整候选的短桥及量词边界）。** 在135.1的完整 EB3 加 $\mathsf{MC}$ 下，先消费135.2—135.4中线性下降、满秩及标签单射的部分，再应用136.2—136.3，即得到 IX118.8第二项需要的原球统一正直径下界。这样，纯点紧性及非塌缩入口的证明不再选取极限球；135.5的同原锥、同原单位复三能级表示与135.6的全部静态字典仍消费 IX118.8，包括该分类已有的极限球依赖。

证明。$\mathsf{MC}$ 使纯生成元的球心替换在全部原混合上良定义；135.3的中心张成使其线性延拓满秩，从而取得定义136.1的实际仿射 $R$ 和原标签单射。136.2—136.3正好供应剩余的非塌缩前件，之后直接应用既有 IX118.8，不重证其拓扑或 Jordan 分类。反向与矩阵字典直接复用135.5—135.6，不作为本章新增分类。证毕。

**约定 136.5（新增连接及关系图景）。** 本章采用 `repo-derived` 归属；新增承重连接是(XI136.3)在分类前以同一全效应关系识别全部原纯点，并由此直接推出紧性及(XI136.7)的全轴间隙。紧投影、有限极点分解、最大值连续性与紧集间正距离是成熟中间工具。量子端的 $X\mapsto(\operatorname{Tr}(X)I-X)/2$ 属于既有 universal state inversion／reduction map；参见 [Rungta等，Universal state inversion and concurrence in arbitrary dimensions](https://doi.org/10.1103/PhysRevA.64.042315) 及 [Horodecki—Horodecki，Reduction criterion of separability and limits for a class of distillation protocols](https://doi.org/10.1103/PhysRevA.59.4206)。这些文献不被当作本章抽象纯域判别的证明，亦不据有限检索声称全球原创。

完整静态候选仍是 $\mathrm{EB3}+\mathsf{MC}$，本章缩短其推导，不声称删去了独立假设。其关系图景是：同一个态可有不同纯混合配方，取每个纯分量的排除球心后仍须得到同一态；若一张原尺能把替换前后完全分开，所有配方分量就必须指向同一颗排除球，标签单射迫使它们本来就是同一纯点。纯态因而由这项闭的二元分离关系完整刻画，球心与纯点之间出现统一正间隙，任何排除球的细轴也不能趋于零。只检验两项混合是否足以替代全部有限混合、裸 EB3 或 EB3加纯比较互易是否推出 $\mathsf{MC}$，仍不由本章解决。实际操作、复合系统、测量更新与时间演化继续保留135.7的原合同；交换比较端点不等于交换连续测量的次序。

## 追加锚（本行以下为增补区）

## 137. 单根纯芽的法向椭球、局部二步饱和与纯极限紧性

### 137.1 完整原域与唯一一个根芽

**定义 137.1（全部原对象）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，及在 $C\setminus\{0\}$ 上严格正的原单位 $u\in V^\ast$。始终取

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
C^\ast=\{h\in V^\ast:h(C)\subseteq\mathbb R_+\},\qquad
\mathcal E=[0,u]_{C^\ast},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p,\\
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\qquad
N_p=\{h\in C^\ast:h(p)=0\},\qquad L_p=\operatorname{span}N_p.
\end{gathered}
\tag{XI137.1}
$$

$K$ 是整个原紧基并张成 $V$，$P$ 是全部原纯点，$\mathcal E$ 是完整原效应区间。$\mathcal F_p$ 非空紧，minimum 达到；第二变量 $x$ 遍历全部原混态。故 $x\in D_p$ 准确等价于存在同一原 $f\in\mathcal E$，满足 $f(p)=1,f(x)=0$。完整暴露族 $\mathcal A_p$ 不替代完整确认菜单 $\mathcal F_p$。

只对纯端点定义 $p\perp q\Longleftrightarrow q\in S_p$。补效应给此关系对称且反自反，不给正比较值互易。EB3 要求每个原 $p\in P$ 的整个 $D_p$ 仿射等价于完整闭三球。本章另取原零图连通条件

$$
\mathsf{Conn}:\quad
\forall p,q\in P\ \exists n\ge0\ \exists p_0,\ldots,p_n\in P:
\quad p_0=p,\ p_n=q,\ p_{j-1}\perp p_j\ (1\le j\le n).
\tag{XI137.2}
$$

步数可依赖端点；它不是纯域的拓扑连通性或统一半径。

在全部目标之前固定同一个原纯点 $o$。对任意原 $p$ 定义含全部混态端点的二步带及其纯交

$$
B_2(p)=\bigcup_{s\in S_p}D_s,\qquad
Q(p)=P\cap B_2(p)=\bigcup_{s\in S_p}S_s.
\tag{XI137.3}
$$

这里恰走两条原零边，允许回走，故 $p\in Q(p)$。唯一额外的局部前件为

$$
\mathsf G(o):\quad
\exists\ U\subset V\text{ 开},\qquad o\in U,\qquad U\cap P\subseteq Q(o).
\tag{XI137.4}
$$

这是在一个固定根处的相对纯邻域条件：每个目标各有一个同时承担两条原零边的中间原纯标签，标签可依目标改变，并非所有目标共用一个见证。它不要求整个关联投影开放、所有根满足同一条件、共同半径、固定效应的延续或同一见证的连续选择。以下证明不输入 PR、紧 $P$、种子三角、正压缩、谱性、Jordan 结构、锥自对偶或齐次性。

### 137.2 复用的完整面与法向接口

**原域接口 137.2。** [FINITE_PURE VII103.2、VII104.1][Q137VII]及[EXCLUSION IX116.1—116.2][Q137IX]给出：每个 $D_p$ 是非点紧暴露极大真面；全部非空原真面只有纯单点或这些完整球；

$$
S_p=\partial_{\rm rel}D_p\cong S^2,\qquad
D_p=\operatorname{conv}S_p,
\qquad
D_a\ne D_b\ \Longrightarrow\ D_a\cap D_b
\text{ 为空或一个原纯单点}.
\tag{XI137.5}
$$

这些面接口不消费全 Pair。球面拓扑均从原 $V$ 继承，不将整个 $P$ 当作流形。

完整 EB3+$\mathsf{Conn}$ 下，直接复用 [THREE_COPY VIII复用组合130.2][Q137TC] 的 Conn$\Rightarrow$Inj、$P=P_0$。其前件和论证均保留：IX116.2 的重复球会组成孤立完全二部原零图块；Conn 会使全部纯点只剩这对不交球的球缘，进而把原凸体的连通相对边界分成两个不交紧球，故排除重复标签。随后 IX119.10 的沿每条原边冗余不变、至少一个零冗余标签及有限路径传播，给全部 $P=P_0$。结合 IX120.2、定理120.8，准确得到对每个原 $p$

$$
\begin{gathered}
D_p=D_q\Longrightarrow p=q,\qquad
\mathcal A_p=\{e_p\},\qquad g_p=u-e_p,\qquad \dim L_p=4,\\
N_{D_p}:=\{h\in C^\ast:h|_{D_p}=0\}=\mathbb R_+e_p,\\
\{x\in K:e_p(x)=0\}=D_p,\qquad
\{x\in K:e_p(x)=1\}=\{p\},\\
R_p:L_p\longrightarrow\operatorname{Aff}(D_p),\quad h\longmapsto h|_{D_p}
\text{ 是线性同构},\qquad g_p\in\operatorname{int}_{L_p}N_p.
\end{gathered}
\tag{XI137.6}
$$

这里的 $P_0$ 只表示完整暴露族 $\mathcal A_p$ 为单点。没有把 $\mathcal F_p$ 说成单点或证明 $e_p$ 为其 least，也没有把 $R_p^{-1}$ 说成正映射。这些接口及 Conn 的消费均为复用。

### 137.3 同一个根的实际法向截面

记 $A=D_o$、$S=S_o$、$N=N_o$、$L=L_o$、$g=g_o$、$B=B_2(o)$、$Q=Q(o)$。定义

$$
\begin{gathered}
J:V\longrightarrow L^*,\qquad J(x)(h)=h(x),\\
N^\vee=\{\lambda\in L^*: \lambda(h)\ge0\ \forall h\in N\},\qquad
H=\{\lambda\in L^*: \lambda(g)=1\},\qquad \Omega=N^\vee\cap H,\\
j(x)=\frac{J(x)}{g(x)}\quad(x\in K\setminus\{o\}),\qquad
\iota:A\longrightarrow H,\quad \iota(x)=J(x).
\end{gathered}
\tag{XI137.7}
$$

$N^\vee$ 是四维空间 $L^*$ 中的对偶锥，不是整个原 $C$。由(XI137.6)，$g(x)>0$ 对所有 $x\in K\setminus\{o\}$ 成立，所以 $j$ 在上述全部混态端点上有定义，且 $j(x)\in\Omega$。

$N$ 在 $L$ 中闭、尖、满维。尖性来自 $C^\ast$ 的尖性，满维来自 $L=\operatorname{span}N$；$g\in\operatorname{int}_L N$。因此每个非零 $\lambda\in N^\vee$ 都有 $\lambda(g)>0$：否则在 $g$ 的双侧小邻域上非负会迫 $\lambda=0$。在单位球与 $N^\vee$ 的紧交上，此值有严格正下界，故 $\Omega$ 紧。对偶锥有内点，归一后给 $\Omega$ 在 $H$ 中的内点；所以 $\Omega$ 是三维紧凸体。由内点径向投影，其相对边界 $\partial_H\Omega$ 同胚于 $S^2$。

又 $g|_A=1$，$R_o$ 的同构使 $L$ 在 $A$ 上给出全部仿射读数，故 $\iota$ 是仿射嵌入，$\iota(A)\subseteq\Omega$。内层 $\iota(A)$ 本来就是三维椭球；此时尚未知道外层 $\Omega$ 的形状，更没有认定两者相等。

**定理 137.3（单根纯芽的支持结论）。** 在定义137.1的完整 EB3+$\mathsf{Conn}$ 域，若同一个 $o$ 满足 $\mathsf G(o)$，则：

1. $\Omega$ 仿射等价于完整闭三球，因而 $N_o$ 线性同构于四维 Lorentz 锥。
2. 存在同胚 $b:S_o\to\partial_H\Omega$，使

$$
j(x)=b(s)\quad(s\in S_o,\ x\in D_s\setminus\{o\}),\qquad
B_2(o)\setminus\{o\}
=\{x\in K\setminus\{o\}:j(x)\in\partial_H\Omega\}.
\tag{XI137.8}
$$

3. 存在同一个环境开集 $U_0\ni o$，使

$$
\forall q\in U_0\cap P,\qquad Q(q)=Q(o).
\tag{XI137.9}
$$

4. $Q(o)$ 在原 $V$ 中紧，其全部点仍为原纯点。

另有准确的根三角定位：记 $\mathsf{Tri}(o)$ 为 $o$ 属于一个真实原零三角，则

$$
\mathsf{Tri}(o)\quad\Longleftrightarrow\quad
\iota(D_o)\cap\partial_H\Omega\ne\varnothing.
\tag{XI137.10}
$$

本定理的证明依次如下。紧 $B_2$ 与实际定义域上的部分关联连续性为既有方法的复用；实质连接是固定球面片的椭球拼接、局部完整二步集合相等及三点排除混态极限。

### 137.4 只在实际纯定义域上使用共同邻点

先复用 X130式(X130.8)、X133.3及 THREE_COPY VIII131.3 的完整紧投影。紧集

$$
\{(s,x,f)\in S\times K\times\mathcal E:f(s)=1,\ f(x)=0\}
\tag{XI137.11}
$$

在 $K$ 上的投影恰为 $B$，包括全部混态，故 $B$ 紧。这不使 $B\cap P$ 自动紧。

若 $s,t\in S$ 不同，则 Inj 及(XI137.5)给

$$
D_s\cap D_t=\{o\}.
\tag{XI137.12}
$$

因此只在 $Q\setminus\{o\}$ 上定义唯一共同邻点

$$
\pi:Q\setminus\{o\}\longrightarrow S,\qquad x\in D_{\pi(x)}.
\tag{XI137.13}
$$

其定义域不扩大为全部 $P\setminus\{o\}$。若 $x_n\to x\in Q\setminus\{o\}$，对任一子列，可用紧 $S$ 与完整紧 $\mathcal E$ 再取 $\pi(x_n)\to s$ 和真实见证 $f_n\to f$，使 $f(s)=1,f(x)=0$。故 $x\in D_s$，唯一性给 $s=\pi(x)$。所有聚点相同，证明 $\pi$ 连续。这是 [X133.5及 THREE_COPY VIII131.6][Q137X][Q137TC] 的实际域闭图方法，不要求 $Q$ 先紧。

### 137.5 从根芽到整个法向边界

固定 $s\in S$。每个 $h\in N$ 在完整球 $D_s$ 上非负且在球面点 $o$ 为零。球在该点只有一条非负支持仿射函数射线；$g|_{D_s}$ 非零且属于该射线。所以

$$
h|_{D_s}=b_s(h)g|_{D_s}\quad(h\in N),\qquad b_s(h)\ge0.
\tag{XI137.14}
$$

因 $N$ 张成 $L$，这给唯一线性 $b_s\in L^*$，且同式延至所有 $h\in L$。例如固定 $y\in D_s\setminus\{o\}$，系数就是 $h(y)/g(y)$，故延拓确为线性且与 $y$ 无关。于是

$$
b_s(g)=1,\qquad b_s\in\Omega,\qquad
J(x)=g(x)b_s\quad(x\in D_s).
\tag{XI137.15}
$$

原效应 $e_s\in N$ 非零，且 $b_s(e_s)=0$，故 $b_s\in\partial_H\Omega$。若 $t\ne s$，在 $D_t\setminus\{o\}$ 取一点 $y$；(XI137.12)和 $e_s$ 的准确零面给 $e_s(y)>0$，因此

$$
b_t(e_s)>0=b_s(e_s).
\tag{XI137.16}
$$

所以 $s\mapsto b_s$ 单射；这一步尚未假定它连续。

取根芽供应的 $U$，令 $U_0=U\setminus A$。因 $A$ 紧且 $o\notin A$，这是含 $o$ 的环境开集，仍有 $U_0\cap P\subseteq Q$。对每个指定 $s\in S$，在固定球面 $S_s$ 上取

$$
q\in S_s\cap U_0\setminus\{o\},\qquad a\in S_q\setminus\{s\}.
\tag{XI137.17}
$$

前者存在，因为 $S_s$ 在 $o$ 没有孤立点；后者存在，因为 $S_q$ 是完整二维球面。$\pi(q)=s$；若 $a\in S$，则 $a$ 也是 $o,q$ 的共同邻点，违反唯一性。因此 $a\notin S$，零对称给 $o\notin D_a$。在固定球面 $S_a$ 取含 $q$ 的开片 $W\subseteq S_a\cap U_0$。

$W\subseteq Q\setminus\{o\}$，故 $\pi|_W$ 连续。若两个点同映到 $t\in S$，它们同属 $D_a\cap D_t$；$a\notin S$ 保证 $a\ne t$，Inj 及点交规则使两点相等。因此 $\pi|_W$ 是二维流形开片到 $S\cong S^2$ 的连续单射。区域不变性给 $\pi(W)$ 在 $S$ 中开，且限制为同胚。对这个含 $s$ 的开邻域，

$$
b_t=j\bigl((\pi|_W)^{-1}(t)\bigr)\qquad(t\in\pi(W)).
\tag{XI137.18}
$$

右侧连续；分母 $g$ 在整个紧 $D_a$ 上严格正。每个 $s$ 都有上述邻域，故 $b:s\mapsto b_s$ 连续。$S$ 和 $\partial_H\Omega$ 是紧二维球面；连续单射的像由区域不变性开，由紧性闭，目标连通，所以

$$
b:S\overset{\sim}{\longrightarrow}\partial_H\Omega.
\tag{XI137.19}
$$

这里使用 [Hatcher，Theorem 2B.3、Corollary 2B.4][Q137H]：$\mathbb R^n$ 的开集到 $\mathbb R^n$ 的连续单射有开像；紧 $n$ 流形嵌入连通 $n$ 流形必满射。流形均为无边界 Hausdorff 流形。上文每次用坐标图降至 $n=2$；没有对整个 $P$ 应用该定理。

还须证明 $\Omega$ 严格凸。任一真支持面可写为 $\{\lambda\in\Omega:\lambda(h)=0\}$，其中 $0\ne h\in N$。确实，$H$ 上的非负支持仿射函数可线性延至 $L^*$，再沿 $N^\vee$ 的正归一化齐次延拓；双极性给其代表属于 $N$。该面含某个 $b_s$，则(XI137.15)使 $h$ 零于整个 $D_s$。由(XI137.6)，$h$ 为 $e_s$ 的正倍数；(XI137.16)使此面只有 $b_s$。所有支持面均为单点，故边界没有非退化线段，$\Omega$ 严格凸。

现在已可证明(XI137.8)的全态集合等式。正向由(XI137.15)。反向，若 $x\in K\setminus\{o\}$ 且 $j(x)\in\partial_H\Omega$，则由(XI137.19)写成 $b_s$；于是 $e_s(x)=g(x)b_s(e_s)=0$，准确零面给 $x\in D_s$。没有把混端点改成纯端点。

### 137.6 完整球的射影像与椭球拼接

保留上一节的 $a,W$，记 $M_a=\operatorname{span}D_a$，其维数为四。先证明

$$
J_a:=J|_{M_a}:M_a\longrightarrow L^*\quad\text{是线性同构}.
\tag{XI137.20}
$$

若其秩至多三，则 $j(D_a)$ 落在仿射维数至多二的平面 $\operatorname{ran}J_a\cap H$ 中。但 $j|_W=b\circ\pi|_W$ 连续单射，且 $j(W)=b(\pi(W))$ 是 $\partial_H\Omega$ 的非空开片。把上述平面嵌入 $\mathbb R^2$，对 $W$ 的一个坐标开片应用区域不变性：维数小于二时开像不可能包含于该平面；维数为二时像含一个平面开圆盘，故 $\partial_H\Omega$ 含非退化线段，违反严格凸性。因此秩为四，得到(XI137.20)。

令 $E_a=j(D_a)$。这是完整三球在严格正分母下的非退化射影像，且 $E_a\subseteq\Omega$。为明确其形状，在 $M_a$ 取齐次球坐标 $(t,z)\in\mathbb R\oplus\mathbb R^3$，使

$$
\operatorname{cone}(D_a)=\{(t,z):t\ge\|z\|\},\qquad
D_a=\{(1,z):\|z\|\le1\}.
\tag{XI137.21}
$$

写 $g(t,z)=\alpha t+\beta\cdot z$。$g$ 在 $D_a$ 上严格正，准确给 $\alpha>\|\beta\|$。$J_a$ 将该锥的 $g=1$ 截面线性送到 $E_a$；消去 $t$ 后，截面为

$$
z^{\mathsf T}(\alpha^2I-\beta\beta^{\mathsf T})z+2\beta\cdot z\le1.
\tag{XI137.22}
$$

二次项正定，配方给非退化椭球。这个椭球含 $z=0$ 的内点，且其上 $1-\beta\cdot z$ 不会为零，否则原不等式迫 $z=0$ 而又有 $1=0$；连通性使它始终为正，故没有混入 $t<0$ 的另一支。这证明整个截面、因而整个 $E_a$ 确为三维闭椭球。$j|_{D_a}$ 是射影同胚，逆由 $J_a^{-1}$ 后按原 $u$ 归一给出，故把 $S_a$ 送到 $\partial_HE_a$，并有

$$
O_a:=j(W)\subseteq\partial_HE_a\cap\partial_H\Omega,
\tag{XI137.23}
$$

且 $O_a$ 在两个边界中都开。

上述论证适用于每个满足 $a\notin S$、$S_a\cap U_0\ne\varnothing$ 的原标签：取非空 $W\subseteq S_a\cap U_0$ 即可。上一节又为每个 $s\in S$ 构造了这样的开片，使 $b_s\in O_a$。所以这些片覆盖整个 $\partial_H\Omega$。

这里需要的二次曲面唯一性是初等工具。若两个非退化三维椭球的边界共享一个非空二维开片，把第一个化成单位球，将第二个的二次方程记为 $F$。固定开片内一点 $y$；每个经过 $y$ 的大圆在开片中含一段开弧。$F$ 在该圆上的限制是次数至多二的三角多项式，在开弧为零便在整圆为零。所有经过 $y$ 的大圆覆盖单位球面，故 $F$ 在整个球面为零。写 $F(z)=c+\ell\cdot z+z^{\mathsf T}Az$，$A$ 对称；比较正反点给 $\ell=0$，代入坐标轴端点和 $(e_i+e_j)/\sqrt2$，给 $A=-cI$。所以两边界方程成非零比例，椭球相同。

若 $O_a,O_{a'}$ 相交，其交在 $\partial_HE_a$ 中是非空开片：它先在 $\partial_H\Omega$ 中开，再限制于 $O_a$。于是上段工具给 $E_a=E_{a'}$。按相同椭球归组的开片并，构成 $\partial_H\Omega$ 的不交开覆盖；边界连通迫使只有一组。记共同椭球为 $E$。全部 $O_a$ 又在 $\partial_HE$ 中开，故其并 $\partial_H\Omega$ 在 $\partial_HE$ 中开；它紧而闭，$\partial_HE$ 连通，遂得两边界相等。取边界凸包即得

$$
\Omega=E,\qquad
a\notin S,\ S_a\cap U_0\ne\varnothing
\ \Longrightarrow\
J_a\text{ 为同构},\quad j(D_a)=\Omega,\quad S_a\subseteq Q.
\tag{XI137.24}
$$

最后一个包含使用已证全态式(XI137.8)：$j(S_a)=\partial_H\Omega$ 且 $o\notin D_a$。因此它是由完整原球的二次刚性取得的整球延拓，没有延续移动效应见证。

$N^\vee=\operatorname{cone}\Omega$；一个椭球基的齐次化线性同构于四维 Lorentz 锥。Lorentz 锥对通常配对自对偶：Cauchy–Schwarz 给一向包含，若 $t<\|z\|$，用 $(1,-z/\|z\|)$ 即分离，负时间轴另用 $(1,0)$。对偶化线性同构便给 $N$ 同样为 Lorentz 锥。此结论只属于 $N_o\subset L_o$，不把整个原 $C$ 认作自对偶锥。

### 137.7 近根纯点的完整二步集合相等

固定 $q\in U_0\cap P$。$q=o$ 时结论自明；余设 $q\ne o$，记 $s=\pi(q)$。对任意 $a\in S_q$，若 $a\in S$，唯一共同邻点给 $a=s$，于是 $S_a=S_s\subseteq Q$。若 $a\ne s$，则 $a\notin S$ 且 $q\in S_a\cap U_0$，(XI137.24)仍给 $S_a\subseteq Q$。取并得到

$$
Q(q)\subseteq Q(o).
\tag{XI137.25}
$$

反向固定任意 $t\in S$。$t=s$ 时，由 $s\in S_q$ 直接有 $S_s\subseteq Q(q)$。设 $t\ne s$。对每个 $a\in S_q$，交集 $D_a\cap D_t$ 恰为一个原纯点。$a=s$ 时交点是 $o$。$a\ne s$ 时，(XI137.24)给射影同胚 $j|_{D_a}:D_a\to\Omega$，所以存在唯一 $x\in S_a$ 满足 $j(x)=b_t$；(XI137.8)的准确零面证明给 $x\in D_t$。两球不同，因为 $a\notin S$ 而 $t\in S$；点交规则保证交点唯一。于是定义全域映射

$$
h_t:S_q\longrightarrow S_t,\qquad \{h_t(a)\}=D_a\cap D_t.
\tag{XI137.26}
$$

连续性无需 $a\mapsto e_a$ 连续。紧集

$$
\{(a,x,f)\in S_q\times S_t\times\mathcal E:f(a)=1,\ f(x)=0\}
\tag{XI137.27}
$$

的前两坐标投影恰为 $h_t$ 的图；图到紧源 $S_q$ 为连续双射，目标 Hausdorff，故其逆连续，再投影得 $h_t$ 连续。

若 $h_t(a)=h_t(a')=x$，则零对称给 $a,a'\in D_q\cap D_x$。若 $a\ne a'$，点交规则迫两球相同，Inj 给 $x=q$。但 $q\in S_t$ 将使 $t$ 成为 $o,q$ 的共同邻点，违反 $t\ne s$。故 $h_t$ 单射。其源是整个紧二维球面 $S_q$，目标是整个连通二维球面 $S_t$；Hatcher 的同维满射结论适用，故 $h_t$ 满射。

每个 $x\in S_t$ 遂有实际 $a\in S_q$ 满足 $x\in S_a$，从而 $S_t\subseteq Q(q)$。遍历全部 $t\in S$ 并结合(XI137.25)，得到(XI137.9)。这里获得的其他根仅为 $U_0\cap P$ 中的原纯点，没有把局部量词扩大为全 $P$。

### 137.8 三个不共球的近根纯点排除混态极限

取不同 $s_1,s_2\in S$，在两张各自固定的球面上选

$$
q_i\in S_{s_i}\cap U_0\setminus\{o\}\quad(i=1,2).
\tag{XI137.28}
$$

则 $\pi(q_i)=s_i$，上一节给 $Q(q_1)=Q(q_2)=Q(o)$。三个原纯点 $o,q_1,q_2$ 不可能同处一张完整排除球：若 $o,q_i\in D_t$，零对称使 $t\in S$ 且为 $o,q_i$ 的共同邻点，故 $t=s_i$，两式不相容。

现令 $x_n\in Q(o)$ 且 $x_n\to x\in K$。三个全态二步带都紧闭，所以

$$
x\in B_2(o)\cap B_2(q_1)\cap B_2(q_2).
\tag{XI137.29}
$$

若 $x$ 混，从三个并集定义分别选标签 $t_0\in S_o$、$t_i\in S_{q_i}$，使 $x\in D_{t_0}\cap D_{t_1}\cap D_{t_2}$。不同完整球只能交于原纯点，故三球必须相同；Inj 迫 $t_0=t_1=t_2=t$。零对称遂给 $o,q_1,q_2\in D_t$，与刚证不共球矛盾。因此 $x$ 纯，且由 $x\in B_2(o)$ 得 $x\in Q(o)$。这证明 $Q(o)$ 在紧 $K$ 中闭而紧。

紧性来自对混极限的上述排除，不来自与未知闭性的 $P$ 取交。也没有由此证明整个 $P$ 紧或全部有限纯图球紧。定理137.3的四项支持结论至此证毕。

### 137.9 根三角恰是实际内外椭球接触，覆盖仍另有量词

因 $o\notin A$、$g|_A=1$，全态式(XI137.8)直接给

$$
\iota(A)\cap\partial_H\Omega\ne\varnothing
\quad\Longleftrightarrow\quad A\cap B_2(o)\ne\varnothing.
\tag{XI137.30}
$$

若 $x\in A\cap D_s$、$s\in S$，则 $s\ne o$，Inj 使 $D_s\ne A$，所以该交点必为原纯点。于是 $o\perp s$、$o\perp x$、$s\perp x$，给根三角。反向，根三角的另两点立即给这样的交点。这证明(XI137.10)，也复用 X130.2、THREE_COPY VIII131.6 的原面接触含义。

因此根若无三角，准确剩余形状是

$$
\iota(D_o)\Subset\operatorname{int}_H\Omega.
\tag{XI137.31}
$$

符号表示紧包含，等价于在任一辅助环境尺下到外边界有严格正距离；两边均为实际三维椭球。定理证明了外层的椭球性，没有证明原全域凸体与全效应约束禁止这种严格嵌套。只画两颗嵌套椭球也不是合法反模型：还必须同时实现原全部纯标签、全部完整 $D_p$、整个原效应区间、Conn 和同一根芽。

原固定根条件仍严格取 [X133.1][Q137X]：

$$
\begin{aligned}
\mathsf D_2(o):&\quad
\forall q\in P:\ o\perp q\ \lor\ \exists r\in P\ (o\perp r\land q\perp r),\\
\mathsf R_1:&\quad\exists o\in P\ \mathsf D_2(o).
\end{aligned}
\tag{XI137.32}
$$

$\mathsf D_2(o)$ 准确要求 $P\subseteq S_o\cup Q(o)$；X133.3在支付此条件后才进一步证明 $Q(o)=P$。本章没有由 $\mathsf G(o)$ 取得根三角、$\mathsf D_2(o)$ 或某个根的 $\mathsf R_1$。即使另取得一次(XI137.30)接触，也只先得到这个根的三角；仍须完整全域传播，不能把一个三角改称 $\mathsf R_1$。

另须与 X132定义132.3 的条件区分：

$$
\mathsf L:\quad
\forall p\in P\ \exists\varepsilon_p\in(0,1)\ \forall q\in P:\quad
0<T_p(q)<\varepsilon_p
\ \Longrightarrow\ \exists r\in P:\ T_p(r)=T_q(r)=0.
\tag{XI137.33}
$$

它量化每个 $p$，并用原最低读数的小正比较带选择目标；$\mathsf G(o)$ 只在一个根的环境纯邻域选择目标。未证明二者前件相同，也没有把该条件的静态重构结论改计为本章结论。根芽在本章是支持定理的明示前件，不是已完成的量子替代公理。

### 137.10 两条既有完整静态候选与同原字典、反向

**既有条件应用 137.4。** 在(XI137.1)的全部原域上，完整 EB3 与(XI137.32)的 $\mathsf R_1$ 是一条既有完整静态候选。直接复用 [X133定理133.6及命题133.7][Q137X]，它等价于存在同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V,
\qquad C=\Phi(\mathrm{PSD}_3),\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI137.34}
$$

另一条既有完整静态候选是 [本卷定义135.1、定理135.2—135.5及条件应用135.6][Q137XI135] 的完整 EB3+$\mathsf{MC}$。记每个完整原 $D_p$ 的唯一仿射球心为 $c_p$；$\mathsf{MC}$ 准确要求：任意正整数 $m,n$、全部原纯点 $p_i,q_j\in P$ 和非负实权重 $\lambda_i,\mu_j$，均满足

$$
\begin{gathered}
\sum_{i=1}^m\lambda_i=\sum_{j=1}^n\mu_j=1,\qquad
\sum_{i=1}^m\lambda_i p_i=\sum_{j=1}^n\mu_j q_j\\
\Longrightarrow\qquad
\sum_{i=1}^m\lambda_i c_{p_i}=\sum_{j=1}^n\mu_j c_{q_j}.
\end{gathered}
\tag{XI137.34a}
$$

零权、重复标签和同一原态的所有有限纯分解均在量词内。这是球心替换保持原混态相等关系，不只是重排同一份表达，也不是顺序测量交换。

该来源的承重链直接引用而不重证：在完整 EB3 下，同一原 $f\in\mathcal E$ 满足 $f(p)=1,f(q)=0$ 时有 $f(c_p)\le1/2\le f(c_q)$ 且 $f(c_p)<f(c_q)$，由此迫使 $\operatorname{aff}\{c_p:p\in P\}=\operatorname{aff}K$、$\operatorname{span}\{c_p:p\in P\}=V$。另付 $\mathsf{MC}$ 才使生成元赋值唯一下降为实线性 $R:V\to V$，满足 $R(p)=c_p$、$R(C)\subseteq C$、$uR=u$；全张成使 $R$ 满射而可逆，进而给 Inj，不声称 $R^{-1}$ 正。若原纯标签趋向混态，先由紧 $K$ 取整球 Hausdorff 收敛子列，IX引理118.4使该极限只能塌成一个原纯点，连续球心图于是把该混态送到纯点；正、保质量且单射的 $R$ 排除这一分支。因此全部原 $P$ 闭而紧，且对任意辅助欧氏范数，$\delta=\operatorname{dist}(P,R(P))>0$、$\inf_{p\in P}\operatorname{diam}D_p\ge2\delta>0$。此时才复用 IX118.6—118.8 的分类，取得同一个(XI137.34)；没有在纯紧性前预用紧 $P$。球心图 $R:V\to V$ 与限制图 $R_o:L_o\to\operatorname{Aff}(D_o)$ 不同型。

同一完整 EB3+$\mathsf{MC}$ 分支也可直接消费[本卷定义136.1、定理136.2—136.3及条件应用136.4][Q137XI136]的短桥：只使用135.2—135.4在纯点闭性论证之前已取得的实际仿射 $R|_K:K\to K$、$R(p)=c_p$ 与原球标签 Inj，不使用135.4的纯点紧性或135.5的矩阵分类。相应关系及判别结论为

$$
\begin{gathered}
\Gamma_R=\{(x,f)\in K\times\mathcal E:f(x)=1,\ f(Rx)=0\},\qquad
d_R(x)=\max_{f\in\mathcal E}\bigl(f(x)-f(Rx)\bigr),\\
P=\operatorname{pr}_K\Gamma_R=d_R^{-1}(\{1\}).
\end{gathered}
\tag{XI137.34b}
$$

所消费证明的关键是同一张原全效应的两端饱和。任取 $p\in P$、$f\in\mathcal F_p$，若 $f(c_p)=0$，中心反射及全域非负性便给 $f|_{D_p}=0$，反向由最低定义给 $D_p=K\cap\ker f$。$c_p\in D_p$ 和达到的原 minimum 总供应这样的效应，故 $P\subseteq\operatorname{pr}_K\Gamma_R$。若 $(x,f)\in\Gamma_R$，取有限纯分解 $x=\sum_i\lambda_i p_i$，$\lambda_i>0$、$\sum_i\lambda_i=1$；实际仿射性和全效应界使 $1=\sum_i\lambda_i f(p_i)$、$0=\sum_i\lambda_i f(c_{p_i})$ 逐项饱和。因此所有 $D_{p_i}$ 都等于同一零面 $K\cap\ker f$，Inj 迫使所有 $p_i$ 相同，故 $x$ 纯。紧 $K\times\mathcal E$ 中的 $\Gamma_R$ 闭，投影遂紧；最大值达到使间隙一恰等于两端饱和，给(XI137.34b)。这不预用紧 $P$，也不选择任何极限球。原效应紧性和 $R$ 的连续性还给连续 $d_R:K\to[0,1]$；对每个 $\eta>0$，紧的 $\{x\in K:\operatorname{dist}(x,P)\ge\eta\}$ 上最大间隙严格小于一，故存在 $\varepsilon>0$，使全部原 $x\in K$ 满足 $d_R(x)>1-\varepsilon\Rightarrow\operatorname{dist}(x,P)<\eta$；该紧集为空时结论直接成立。

由此，$P$ 与连续像 $R(P)$ 是不交紧集：球心均为正维原面的非纯相对内点。对任意固定辅助欧氏范数，令 $Z_p=\operatorname{lin}(D_p-c_p)$，便有

$$
\delta=\operatorname{dist}(P,R(P))>0,\qquad
c_p+\delta\,\overline B_{Z_p}\subseteq D_p\quad(p\in P),\qquad
\operatorname{diam}D_p\ge2\delta.
\tag{XI137.34c}
$$

确实，每个完整球的所有相对边界点都原纯，到其球心的距离至少为 $\delta$；从中心沿 $Z_p$ 的每条单位射线取首次边界点，凸性给整个半径 $\delta$ 的内球，中心反射再给直径界。因此不仅直径，辅助尺下全部半轴都统一非塌缩。这里的 $Z_p$ 不与本章法向张成 $L_p$ 混型。此短桥只省去纯点紧性及非塌缩入口处的极限球选择；随后仍消费 IX118.8，包括其既有分类的极限球依赖，不重证拓扑或 Jordan 分类。136.1本身允许正维可变维球并把实际仿射 $R$、Inj 列为前件；本章只在完整 EB3+$\mathsf{MC}$ 已支付它们的接口复用，不从局部 $\mathsf G(o)$ 取得 $R$ 或 $\mathsf{MC}$。

EB3+$\mathsf R_1$ 路线仍由 IX120.4—120.5消费 IX116定理116.17及定义应用116.18；EB3+$\mathsf{MC}$ 路线可经本卷136.4的短桥复用135.5。两条完整候选均与同原锥、同原单位的(XI137.34)等价；本章不新增分类。其球心公式仅在分类后为 $U=\Phi(I_3)$、$c_p=(U-p)/2$、$R(x)=(u(x)U-x)/2$（$x\in V$）；这些公式不逆用为支持定理的前件。该静态正球心图也不因此成为实际事件，仍须137.11的全旁观及事件合同。

定理137.3的前件仅为完整 EB3+$\mathsf{Conn}$+$\mathsf G(o)$，不假设 $\mathsf{MC}$，也不以先取得完整矩阵表示来证明四项支持结论。$\mathsf G(o)$ 只约束一个固定根附近的纯零关联，$\mathsf{MC}$ 则约束全部原纯混合表达；EB3+$\mathsf{Conn}$+$\mathsf G(o)\Rightarrow\mathsf{MC}$ 以及从同一前件取得全域 $\mathsf R_1$ 均未证明。仅引用这些完整候选，不能从未付 $\mathsf{MC}$ 或 $\mathsf R_1$ 的根芽前件取得内外接触或全域覆盖。

只在上述任一路线取得同一个 $\Phi$ 时，令 $P_v=vv^\ast$、$v^\ast v=1$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$，有完整对应：

| 通常静态量子对象 | 同一原表示中的准确对应 |
| --- | --- |
| 全锥、质量、单位 | $\dim_{\mathbb R}V=9$，全部 $X\succeq0$ 连同零与任意非负质量由 $\Phi$ 运输；$u(\Phi X)=\operatorname{Tr}X$。原泛函 $u$ 与派生 Jordan 单位 $U=\Phi(I_3)\in V$ 不混型。 |
| 全态、凸混合、纯射线 | $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，保持全部凸混合；$P=\{p_v\}\cong\mathbb{CP}^2$。任意 $z\ne0$ 对应 $\Phi(zz^\ast/(z^\ast z))$，非零复倍数给同一纯标签。 |
| 全效应与全部混态 Born 评价 | $f_M(\Phi X)=\operatorname{Tr}(MX)$，恰遍历 $0\preceq M\preceq I_3$；零、单位、补、序均保持。全部实线性读数由任意 Hermitian $M$ 表示。 |
| 完整确认、least、minimum | $\mathcal F_{p_v}$ 恰为 $f_{P_v+B}$，$B=Q_vBQ_v$、$0\preceq B\preceq Q_v$；least 是 $f_{P_v}$。每个原混态满足 $T_{p_v}(\Phi\rho)=\operatorname{Tr}(P_v\rho)=v^\ast\rho v$，并非确认菜单单点。 |
| 纯比较与完整排除三球 | $T_{p_v}(p_w)=|v^\ast w|^2$；未归一向量须除以两范数平方之积。$D_{p_v}=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1,\rho v=0\}$，含全部混态；其纯球缘为 $\mathbb{CP}^1\cong S^2$，球心为 $\Phi(Q_v/2)$。 |
| 维数、中心、完整正交框架 | $\dim_{\rm aff}K=8$，纯域实维四，完整排除球实维三；中心为 $U/3$。原零三角对应三个和为 $I_3$ 的正交秩一投影，least 效应和为 $u$；每条原零边有唯一第三纯点，数学完美区别容量为三。 |
| 全部有限数学测量 | 任意有限结果族 $f_j\in C^\ast,\sum_j f_j=u$ 恰对应全部 $M_j\succeq0,\sum_jM_j=I_3$ 的 POVM；对全部原输入概率为 $\operatorname{Tr}(M_j\rho)$，允许零效应。 |
| 谱、Jordan、自对偶 | 每态有三项正交谱分解，允许零权及重谱；全部 Hermitian 可观测量有实谱及谱效应。$\langle\Phi X,\Phi Y\rangle_\Phi=\operatorname{Tr}(XY)$ 下 $C$ 自对偶，$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$，单位为 $U$。 |

完整确认公式需要保留其原最低定义：若 $0\preceq M\preceq I_3$ 且 $v^\ast Mv=1$，正半定性使 $(I_3-M)v=0$，Hermitian 性消去交叉块，准确给 $M=P_v+B$ 及表中全部 $B$。对每个 $\rho\succeq0$，$\operatorname{Tr}(B\rho)\ge0$，且 $B=0$ 属于同一菜单并达到下界，才给 least 和所有混态上的 minimum。正半定性又使 $v^\ast\rho v=0\Longleftrightarrow\rho v=0$；在 $v^\perp\cong\mathbb C^2$ 的 Pauli 坐标给整个闭三球。

反向取满足(XI137.34)的整个标准模型。上段计算给每个完整 $D_{p_v}$ 的 EB3。对任意预先指定的根 $p_v$ 和任意目标 $p_w$，包括相同标签，因 $\dim_{\mathbb C}\operatorname{span}\{v,w\}\le2$，可取单位 $z\in\operatorname{span}\{v,w\}^\perp$；同一个原纯点 $p_z$ 与二者均有原零边，分别由原投影效应 $f_{P_v},f_{P_w}$ 见证。故每根都有 $Q(p_v)=P$，满足 $\mathsf D_2$、Conn 及 $\mathsf G(p_v)$。同一标准模型还给 $c_{p_v}=\Phi((I_3-P_v)/2)=(U-p_v)/2$；任意原纯混合 $x=\sum_i\lambda_i p_i$ 的球心替换都等于 $\sum_i\lambda_i c_{p_i}=(U-x)/2$，所以同一态的所有有限纯分解给相同替换，含零权和重复标签，完整 $\mathsf{MC}$ 成立。这是上述两条完整候选的既有反向，不是 $\mathsf G\Rightarrow\mathsf R_1$ 或 $\mathsf G\Rightarrow\mathsf{MC}$ 的证明。

定理137.3的 $N_o$、$\Omega$ 和 $j$ 本身不供应表中 least、全态 Born、正压缩或整个 $C$ 的自对偶与 Jordan 结构。尤其 $R_o$ 为线性同构而外层为椭球，并不证明 $R_o^{-1}$ 把原 $D_o$ 上每个非负函数送回 $C^\ast$；两颗椭球严格嵌套的可能性仍保留这一原正性费用。

### 137.11 来源、全部有限联合、事件仪器、未来和时间的完整继承

本节逐项完整继承 [SAME_READBACK SECTION127.10][Q137SR]（节号，不是定理号）和 [EXCLUSION X133.10][Q137X]。其全部传递引用仍为 SAME_READBACK125.11、124.9、123.13，EXCLUSION VIII命题113.11及112.9、EXCLUSION IX120.11，THREE_COPY VII121.12与122.14，以及所指 INTRINSIC_POLAR VI定义89.7、全部两尺度式(89.13)、89.8—89.10、V88.6与87章、原生续卷VII和III的来源、过程、全未来和动态合同；BILATERAL VIII128.H 的继承同样保留。每项均按原文的完整前件、原对象、作用域与全部量词使用。操作／来源的 INTRINSIC_POLAR VI 与整球 BILATERAL VI 不混同。

同一个原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性，零／单位／补／有界倍增、重复标签和每种同中点实现、全部非负质量及零／次归一／不等质量、过程和参考各自完整的相关联合输入域继续保留。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)的全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集，均保持原定义。此处操作映射 $p$ 与纯标签不同型，$G=1_E$ 与根芽条件不同型。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、旧 support、全部合法未来和每个中间切口均保留。原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption及资源合同继续由原消费者承担。数学射线、零图关联及三结果效应不产生实际来源、接线、权限或未来。

对每个有限 $N\ge1$，仍须供应实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 和完整原效应区间。对每个实际二分割 $a+b=N$，保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{XI137.35}
$$

同一产品配对、严格张量单位、全部原因子置换及其逆的正性、规范重括号和指定运输下不连续位置分块均保持。完整实际二份比较 $S_2$ 仍量化每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族、全部 $t_\ell\ge0$、$\sum_\ell t_\ell=1$，包括零权和重复标签，并要求

$$
\begin{gathered}
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\\
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]_{C_2^\ast}\\f(p)=1}}f(x).
\end{gathered}
\tag{XI137.36}
$$

单体最低定义的线性化不支付这项全纠缠合同。原低二份 $q=1,2$ 的 least／谱性／正面投影及保纯到 Jordan 桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制与秩和实维乘法的复型选择，以及同一实际两因子的产品正规形，仍是既有全有限层级定理分别需要的三项具名供应。

非经典支路 $\mathsf F_{\max}$ 仍要求同一最大复块 $n_r=L\ge2$、同一含相位正交基上的实际三份正性资源

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{XI137.37}
$$

其余三份扇区为零，归一原源为 $\Delta_r/L$；不预付三份纯性或实际制备，全经典 $L=1$ 支路按原规则免除此资源。单体复三能级支路为 $L=3$，二、三份秩分别为九、二十七；高阶整个排除集不继续被规定为单体 EB3。形式矩阵不保证实际 $C_3$ 成员资格。只有全部联合前件及三项供应齐备后，才调用既有全有限层级结论。

对输入、输出份数 $m,n$ 及同一原类型的实线性映射 $F:W_m\to W_n$，数学全旁观正性仍量化每个旁观份数 $b\ge0$ 和任意含纠缠的同一共同输入，要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{XI137.38}
$$

只有实际完整有限层级及共同表示已供应，才沿原 Choi 桥识别通常 CP、矩形跨扇区 Kraus 和逐输入 TP／TNI 原预算。原预算对每个原非负输入 $x\in C_m$ 分别要求 TP 的 $u_n(Fx)=u_m(x)$ 或 TNI 的 $u_n(Fx)\le u_m(x)$；同族分支预算由同一个输入上的分支总和承担。同一实际事件的 CP 另需原完整提升、实际探针和相容核；全部数学 CP-TNI 分支实际可用另需原事件饱和选择。同族仪器保留共同输入预算、接线、记录、粗粒化和校准；只对严格正质量分支条件归一，零质量分支不强定归一条件态。Lüders 更新另需同一分支的锐效应、接受态中性与输出校准。全部数学 POVM、三张原效应和为单位及可执行同族仪器，各保留原合同。

原物理钟、实际动态来源、连续齐次可逆时间群与单位继续分别供应。若另给同载体上的全实时间连续线性群 $A_t$，满足

$$
A_0=I,\qquad A_{s+t}=A_sA_t,\qquad A_t(C)=C,\qquad uA_t=u,
\tag{XI137.39}
$$

才有该额外时间供应的有限维生成元。在重构复块上又给保迹酉时间族之后，才使用

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad
\rho_t=U_t\rho U_t^\ast,\qquad
\mathcal L(\rho)=-\mathrm i[H,\rho]/\hbar,\qquad H=H^\ast.
\tag{XI137.40}
$$

量词覆盖全部原输入及全部实际时间。$H$ 的标量平移不改变态作用，时间重标改变生成元尺度而不改变静态几何；恒等时间族与非平凡 Hamiltonian 族可共享全部静态对象。实际 Hamiltonian、能量识别及标定、数值 $\hbar$、时空和物理空间维数仍有各自费用。原零图的一步和两步是关联步数，不是物理时间。

### 137.12 复用边界与完整白话图景

完整面、孤立重复块、Conn 后的 Inj 与 $P=P_0$、四维法向、限制同构、相对内部、固定球面效应连续性及原零关联紧投影，均复用137.2、137.4所列来源。IX120.11—120.12的原正性阈值没有被限制线性同构删去。THREE_COPY VIII130.8—130.9的纯紧性桥及VIII131.3—131.6的第三全态带、R3奇返回和部分关联域边界，仍保留各自前件。

[Hatcher，印刷页172，Theorem 2B.3、Corollary 2B.4][Q137H]供应区域不变性与紧源满射工具；每次应用均已建立等维无边界流形、连续、单射及完整源域。[Boyd—Vandenberghe，§2.2.2、§2.2.3 Example 2.3、§2.3.3][Q137B]供应椭球、Lorentz 锥及正分母射影映射背景；所需截面形状和二次曲面重叠唯一性已在(XI137.21)—(XI137.24)直接证明。

本章的连接是固定根芽到整个法向边界的球面片覆盖、椭球拼接、近根完整 $Q$ 集合相等，以及三点排除混态极限；全态边界等式保持全部原混输入。137.10中的135.2—135.6球心桥、完整 MC 分类与反向，136.1—136.4全效应纯态判别与全轴间隙，均为复用。条件量子字典是已有同原表示的运输，不另计新 Born 或全域重构定理。

**完整白话。** 全部纯态、混态和全部允许读数仍在同一原凸状态体中。每个纯标签背后有一整颗实心排除三球，球面恰为其全部原纯零邻居。额外条件先固定一个根，只要求它的某个环境邻域内，每个原纯目标各有一个中间原纯点，同时与根和该目标有两条真实零边；中间点可随目标改变，并未要求远处目标也如此。Conn 只给逐目标有限路径，未给统一半径。

把根的四维法向读数按根外严格正的原尺归一，会得到一个三维凸截面；根的原排除球嵌在其中。每颗经过根的完整球，其根外部分被归一到外边界的一个点。根芽供应固定原球面上的开片，覆盖整个外边界；完整球的非退化射影像是椭球，重叠开片迫这些椭球相同，于是外截面也是椭球，根法向锥为四维 Lorentz 锥。这没有把内层原球与外层截面认成同一个集合。

把根移到同一邻域中的任一原纯点，完整球面间的共同邻点关联给连续单射；两端都是完整二维球面，因而满射，附近根的完整二步纯集合遂相等。再选三个近根且不共处一颗原排除球的纯点。若共同集合中一列纯点趋向混态，三个紧的全态二步带会把该混态留在三颗球中；不同球只交纯点，故只能是同一颗球，反过来迫三个所选纯点共球，矛盾。所以该二步集合在环境空间中紧，全部极限仍纯；这未证明全 $P$ 紧。

尚缺两件事：内层原球为何必须碰到外层法向椭球的边界，以及全部原纯目标为何都落在某个固定根的一步或二步内。一次接触仅给该根一个真实零三角；紧的局部二步集与有限图路径尚未支付全域传播。两颗严格嵌套椭球也未成为合法反模型，因为还须同时实现全部原标签、完整排除球、全效应、Conn 和根芽。正限制逆、least 与整个原锥的 Jordan 结构也未由局部法向结论取得。

两条完整静态路线仍分别保留 EB3+$\mathsf R_1$ 与 EB3+$\mathsf{MC}$。前者要求事先固定的一个根覆盖全部纯目标；后者要求同一混态的所有有限纯配方逐项换成排除球心后仍相同。后一路先由 MC 取得统一球心图，再由球心全张成使它在原实空间上可逆，取得标签单射，再使用第136章的饱和关系：一张原尺若把某态及其替换像完全分开，该态每个正权纯分量的排除球就必须是同一个零面，单射迫全部分量相同。闭关系遂识别全纯域，给纯紧性；纯点与非纯球心的紧像有正间隙，连最细半轴也不能趋零。第135章的极限球论证同样保留；短桥只在紧性及非塌缩入口免选极限球，后续分类仍保留其依赖。第136章没有从根芽供应实际仿射图、MC 或全域覆盖。

在任一完整路线付清后，同一个原锥、原单位表示才同时给全部密度态、复射线、全效应、非单点确认菜单、least、每个混态上的 Born minimum、全部有限数学 POVM、谱及 Jordan 字典，反向也取整个标准模型。本章根芽定理没有支付任一路线的完整前件。137.11的实际来源、读回及全部质量、全有限复合与纠缠、三份相位资源、全旁观 CP 和逐输入预算、事件仪器、记录、全部合法未来与切口、物理钟、Hamiltonian、能量及数值 $\hbar$ 合同继续逐项保留。静态球心图不是实际事件，原零图步数不是物理时间，三球维数不是物理空间维数。

[Q137VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2、104.1：完整原面、纯球缘与点交；无全 Pair 前件。"
[Q137IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.2；118.4、118.6—118.8；119.10（119.7节）；120.2、120.4—120.5、120.8、120.11—120.12；116.17—116.18。"
[Q137TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.1—130.2、130.5—130.9：Conn、四维法向与纯紧性边界；131.1—131.8：全态带、部分关联域、候选及完整合同。"
[Q137X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X130.2；132.3；133.1—133.7固定覆盖根、传播、同原字典与反向；133.10完整物理合同。"
[Q137XI135]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md#135-原混合等价关系的球心下降与同锥量子重构 "135.1完整 MC；135.2—135.4球心桥；135.5—135.7分类、反向、字典及物理合同。"
[Q137XI136]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md#136-一张全效应的纯态判别与排除球全轴间隙 "136.1实际仿射 R 与 Inj 前件；136.2纯态闭分离判别；136.3全轴间隙；136.4已付 EB3+MC 短桥及 IX118.8 依赖。"
[Q137SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "126.1紧见证投影；SECTION127.10完整来源、质量、联合、事件、未来和时间合同。"
[Q137H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology，印刷页172，Theorem 2B.3、Corollary 2B.4及证明。"
[Q137B]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf "Stephen Boyd and Lieven Vandenberghe, Convex Optimization，§2.2.2、§2.2.3 Example 2.3、§2.3.3。"

## 追加锚（本行以下为增补区）

## 138. 二元混合相容的内部截面、反射纯球与跨块障碍

**定义 138.1（同原二元相容与球内图）。** 保留135.1的完整原 $V,C,u,K,P,\mathcal E,T_p,D_p$ 及 EB3。记完整球族、球缘和标签纤维为

$$
\mathscr B=\{D_p:p\in P\},\qquad
S(F)=P\cap F=\partial_{\rm rel}F,\qquad I(F)=\{p:D_p=F\}.
$$

$c_F$ 是完整球 $F$ 的唯一仿射中心，$c_p=c_{D_p}$。只在本章另加二元混合相容

$$
\begin{aligned}
\mathsf{BC}:\quad&
tp+(1-t)q=vr+(1-v)s\\
&\Longrightarrow\quad
tc_p+(1-t)c_q=vc_r+(1-v)c_s
\end{aligned}
\quad
\left(\begin{gathered}p,q,r,s\in P,\\t,v\in[0,1]\end{gathered}\right).
\tag{XI138.1}
$$

全部端点与权重都来自同一个原模型，允许重复端点及零权。$\mathsf{MC}$ 蕴含 $\mathsf{BC}$；本章不把反向蕴含作为前件。单纯重排同一份混合不改变任何仿射和，(XI138.1)还比较端点不同但实际原态相同的两条弦。

复用 IX116.1—116.6 的原面接口：每个非点真面都是完整球；不同完整球至多交于一个原纯点；每个 $F$ 或单标签，或与唯一不交的 $H$ 构成重复对，满足 $I(F)=S(H),I(H)=S(F)$，且两球均不交第三球；至少有一张单标签球，单标签球的全部球缘标签在全域均无重复。所有内部、边界及支撑均相对于 $\operatorname{aff}K$，球内相对内部另记 $\operatorname{ri}F$。

**定理 138.2（局部球心图的零秩或满秩二分）。** 每个 $F\in\mathscr B$ 存在唯一仿射图 $G_F:F\to K$，满足 $G_F(q)=c_q$ 对全部 $q\in S(F)$ 成立。准确地，

$$
\begin{cases}
G_F\text{ 为常值图},& I(F)\text{ 非单点},\\
G_F\text{ 单射且秩为三},& I(F)\text{ 为单点}.
\end{cases}
\tag{XI138.2}
$$

证明。先用成熟的弦延拓论证构造图。每个 $x\in F$ 都可写成一条球缘弦的凸组合，定义 $G_F(x)$ 为相同权重的端点球心组合。$\mathsf{BC}$ 使不同弦给出相同值，且值在 $K$。若 $x,y\in F$ 不同，通过它们的直线与球相交为一条以球缘为端点的闭弦，$x,y$ 及其全部凸组合均在这条共同弦上，故 $G_F$ 保全部实凸组合。因此它仿射，球缘凸生成给唯一性；有限维仿射图连续。

若 $G_F$ 非单射，其线性部分有非零核方向。沿该方向取球的两个对径 $r,s\in S(F)$，得 $c_r=c_s$。这个共同球心非纯，故 $D_r,D_s$ 的交含非纯点，原面接口迫使 $D_r=D_s=:H$。$r\ne s$ 使 $H$ 重复；IX116.2给其唯一配对球 $J$，且 $r,s\in I(H)=S(J)$。$J$ 与 $F$ 共享两个不同点，故 $J=F$。于是 $F$ 重复，而且每个 $q\in S(F)$ 都满足 $D_q=H$，所以整个 $G_F$ 恒为 $c_H$。

反之，$F$ 重复时 IX116.2直接给 $G_F$ 在球缘恒值，故在整个球恒值。单标签情形因而单射，且 $F$ 为完整三球，线性秩恰为三。证毕。

**定理 138.3（球心像的精确内部截面及横截）。** 设 $F$ 单标签，置

$$
E_F=G_F(F),\qquad o_F=G_F(c_F),\qquad
L_E=\operatorname{lin}(E_F-o_F).
$$

则 $E_F$ 是嵌入的仿射三球，且

$$
\begin{gathered}
G_F(\operatorname{ri}F)\subseteq\operatorname{ri}K,\qquad
\partial_{\rm rel}E_F=\{c_q:q\in S(F)\}\subseteq\partial K,\\
E_F=K\cap\operatorname{aff}E_F,\qquad
L_E\cap\operatorname{lin}(D_q-c_q)=\{0\}\quad(q\in S(F)).
\end{gathered}
\tag{XI138.3}
$$

特别地，$\dim\operatorname{aff}K\ge6$，至少存在一张这样的内部截面。

证明。138.2给嵌入三球及其边界公式。每个 $c_q$ 是真面 $D_q$ 的非纯球心，因此位于 $\partial K$。设某个 $x\in\operatorname{ri}F$ 的像在 $\partial K$。取 $K$ 上非负、非恒定且在 $G_F(x)$ 为零的支撑仿射泛函 $h$。$h\circ G_F$ 非负仿射且在球内点为零，所以在整个 $F$ 恒零。于是支撑真面 $Z=K\cap\{h=0\}$ 含所有 $c_q$。

对任意 $y\in D_q$，中心反射 $2c_q-y\in D_q$ 与非负性给 $h(y)+h(2c_q-y)=2h(c_q)=0$，从而 $D_q\subseteq Z$。极大真面性给 $D_q=Z$ 对全部 $q\in S(F)$ 成立。这迫使 $G_F$ 恒值，与单射矛盾。因此球内全部像均为 $K$ 内点，特别是 $o_F\in\operatorname{ri}K$。

若存在 $y\in K\cap\operatorname{aff}E_F$ 不在 $E_F$，从 $o_F$ 向 $y$ 的射线首次离开 $E_F$ 的点 $z$ 位于 $\partial_{\rm rel}E_F$ 且位于开线段 $(o_F,y)$。凸体内点与任意凸体点之间的开线段仍在内部，所以 $z\in\operatorname{ri}K$，与上述边界包含矛盾，取得精确截面。

若非零 $w$ 同时属于 $L_E$ 及 $\operatorname{lin}(D_q-c_q)$，因 $c_q\in\operatorname{ri}D_q$，充分小的 $\varepsilon>0$ 使 $c_q\pm\varepsilon w\in D_q\subset K$。它们又属于 $\operatorname{aff}E_F$，故都在 $E_F$，违反 $c_q$ 是三球 $E_F$ 的极点。两方向空间均为三维，零交给维数下界；IX116.6给至少一张单标签球。证毕。

**定理 138.4（反射纯球的面或内部截面二分）。** 设 $I(F)=\{a\}$。定义

$$
\sigma_F(q)=2c_q-a\quad(q\in S(F)),\qquad
A_F=2G_F(F)-a,\qquad b_F=2o_F-a.
\tag{XI138.4}
$$

则 $A_F\subset K$ 为非退化仿射三球，$b_F$ 是其中心，整个相对球面满足

$$
\partial_{\rm rel}A_F=\sigma_F(S(F))\subset P.
\tag{XI138.5}
$$

恰有以下两种情形：若 $b_F\in\partial K$，则 $A_F$ 本身是一张完整原排除球；若 $b_F\in\operatorname{ri}K$，则

$$
A_F=K\cap\operatorname{aff}A_F,
\tag{XI138.6}
$$

且 $A_F$ 不是真面。此外，

$$
A_F=F
\quad\Longleftrightarrow\quad
c_q=\frac{a+2c_F-q}{2}\quad(q\in S(F)).
\tag{XI138.7}
$$

证明。对每个 $q\in S(F)$，$q\in D_a$，零对称给 $a\in D_q$。$a$ 是 $D_q$ 的球缘点，故其中心反射 $2c_q-a$ 也是该球的球缘点，因而属于原 $P$。138.2使 $2G_F-a$ 单射，故它将 $F$ 映为非退化三球，球面恰为上述纯点；球缘凸生成和 $K$ 凸给 $A_F\subset K$。

若 $b_F\in\partial K$，取非负非恒定支撑 $h$ 在 $b_F$ 为零。$A_F$ 关于 $b_F$ 中心对称，故 $h$ 在整个 $A_F$ 为零，$A_F$ 包含于支撑真面 $H$。该面非点，原面分类使它为三球。两球同维，故仿射包相等，且 $b_F\in\operatorname{ri}H$。若 $H$ 中某点在 $A_F$ 外，从 $b_F$ 向该点的开线段跨过 $A_F$ 的球面；交点属于 $\operatorname{ri}H$，却由(XI138.5)为原纯点，矛盾。故 $A_F=H\in\mathscr B$。

若 $b_F\in\operatorname{ri}K$，(XI138.5)使球面在 $\partial K$，138.3的射线论证原样给(XI138.6)。包含 $K$ 内点的非空面只能为整个 $K$；138.3给 $\dim\operatorname{aff}K\ge6$，而 $A_F$ 仅三维，所以它不是真面。

最后假设 $A_F=F$。对 $q\in S(F)$，上述反射点 $\sigma_F(q)$ 与 $q$ 均在 $F$，又满足 $q\perp\sigma_F(q)$。取实现这一原零一读数的同一原效应，其在球 $F$ 的限制非恒定，最大、最小点只能是一对唯一球内对径。因此 $\sigma_F(q)=2c_F-q$，重排即得(XI138.7)右侧。反之，该公式使 $\sigma_F$ 将球缘映为同一球缘的对径，取凸包即得 $A_F=F$。证毕。

**定理 138.5（固定原球缘上的非塌缩）。** 任取 $D_p=F$，不要求 $F$ 单标签。固定辅助欧氏范数，令

$$
\delta_F=2\min_{q\in S(F)}\|p-G_F(q)\|.
$$

则 $\delta_F>0$ 且

$$
\operatorname{diam}D_q\ge\delta_F\quad(q\in S(F)).
\tag{XI138.8}
$$

因此若 $\operatorname{diam}D_{p_n}\to0$，该序列最终避开每一张预先固定的 $S(F)$。

证明。固定球的球缘紧，$G_F$ 连续，且每个 $G_F(q)=c_q$ 非纯，与纯点 $p$ 不同，故连续正距离取得严格正的最小值。零对称给 $p\in D_q$，中心反射给 $2c_q-p\in D_q$；两点距离为 $2\|p-c_q\|$，取得(XI138.8)。每张固定球缘的正下界直接给序列断言。不同 $F$ 的下界尚未统一，本结论不供应 IX118.8 的全域正下界，也不供应136.3的全轴内球。证毕。

**定理 138.6（重复块的内部相容及单外端点禁交）。** 设 $F,H$ 是 IX116.2的重复球对，令 $B=S(F)\cup S(H)$。则球心替换在全部端点属于 $B$ 的任意有限纯混合等式上相容。另一方面，在 $\mathsf{BC}$ 下不可能有

$$
tr+(1-t)a=vb+(1-v)d,
\qquad
0<t,v<1,\quad a,b,d\in B,\quad r\in P\setminus B.
\tag{XI138.9}
$$

证明。IX116.3给同一原效应 $e$，满足 $K\cap\{e=0\}=F$ 及 $K\cap\{e=1\}=H$。仿射图

$$
J(x)=(1-e(x))c_H+e(x)c_F
$$

在 $S(F)$ 恒为 $c_H=c_q$，在 $S(H)$ 恒为 $c_F=c_q$。故任意有限 $B$ 混合的球心替换都等于对原混合施加同一仿射 $J$，取得内部相容。

若(XI138.9)成立，分别应用 $\mathsf{BC}$ 及 $J$，相减得 $t(c_r-J(r))=0$，故 $c_r=J(r)$。$r$ 在两球缘之外且为原纯点，因此 $0<e(r)<1$，使 $J(r)\in(c_F,c_H)$。这个整个开球心段在 $\operatorname{ri}K$：否则某非负非恒定支撑同时在两球心为零，中心反射迫其零面同时包含 $F,H$，极大性迫 $F=H$，矛盾。于是 $c_r\in\operatorname{ri}K$，违反 $c_r\in D_r\subset\partial K$。证毕。

**定义 138.7（简化候选及尚缺的整体约束）。** 待证候选为 $\mathrm{EB3}+\mathsf{BC}$。138.2—138.6没有证明它推出 $\mathsf{MC}$、全标签单射或全域非塌缩，也没有给出其反模型。反射构造尚缺 $A_F=F$；138.4的“完整原球”分支仍允许另一张完整球，“内部截面”分支也未被排除。即使逐球得到(XI138.7)，将各球的 $a+2c_F$ 拼成全域同一个向量，仍须另证整体连接条件。

重复块内部的全部混合关系已经相容，故不能只在块内寻找矛盾。138.6仅排除一外三内的活跃二元等式；两个外端点与两个块内端点的弦相交仍可能在内部发生，未被该论证排除。局部下界亦仅逐球成立，不能以逐点正值代替统一正值。

已取得完整静态分类的候选仍为135.1的 $\mathrm{EB3}+\mathsf{MC}$。它的同原表示与 Born、谱分解、全效应和有限数学测量字典直接复用135.5—135.6；本章只压缩二元候选所缺桥梁的几何形状，不新增 Hilbert 或物理实现断言。其白话关系图景是：同一混态若能由两对纯态调出来，换成各自排除球的球心后也应相同。这使每颗单标签球的球心族拉成一张穿过总态空间内部的完整三维切片；再隔着球心反射纯点，会得到另一整张纯球面。要把“两两相容”升级为量子结构，还须说明这张反射球为何回到原球，并把各球的关系接成全域同一关系。

**约定 138.8（数学来源及迁移条件）。** 本章新增承重连接采用 `repo-derived` 归属：原全效应产生的排除面与二元球心图共同给出局部秩二分、精确内部截面及横截、反射纯球二分、逐球非塌缩及重复块禁交。弦上的仿射延拓、支撑面、凸体内点射线、有限维维数公式及紧集最小距离是成熟中间工具；IX116的面与重复纤维分类、XI135—136的全域分类桥均按原前件复用，不另计新结果。

[Schillewaert—Van Maldeghem，On the varieties of the second row of the split Freudenthal–Tits Magic Square，§2.1](https://arxiv.org/abs/1308.0745) 的 Mazzocca–Melone 公理 MM1要求每对点位于一张指定二次空间，MM2约束射影张成空间的交，另有分裂二次曲面及切空间条件；本章的凸面交叠不供应这些前件，尤其不能用其分类倒付未证的全 Pair。[Barnum—Müller—Ududec，Higher-order interference and single-system postulates characterizing quantum theory，Theorem 16](https://arxiv.org/abs/1403.4147) 则显式要求 projectivity、对称跃迁概率及保纯滤子；二元混合相容未供应这些结构。两项文献只界定可迁移的条件，不替代上述原域证明，也不据有限检索宣称全球原创。

## 追加锚（本行以下为增补区）

## 139. 紧纯二步集的秩二丛、原球交数与完整载体标签紧性

### 139.1 完整原域与所消费的单根结论

**定义 139.1（原对象、单根与完整载体标签）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的原单位 $u\in V^*$。始终使用整个原域

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
C^*=\{h\in V^*:h(C)\subseteq\mathbb R_+\},\qquad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p.
\end{gathered}
\tag{XI139.1}
$$

第二变量 $x$ 遍历全部原态，包括每个混态。$K$ 紧且张成 $V$；原全效应区间紧，$\mathcal F_p$ 非空紧，故 minimum 达到。对纯端点记 $p\perp q\Longleftrightarrow q\in S_p$；补效应使它对称，且 $p\not\perp p$。完整 EB3 要求每个原 $p\in P$ 的整个 $D_p$ 都仿射等价于非退化实心闭三球。

另取原零图的 $\mathsf{Conn}$：任意两个原纯点之间有一条有限原零边路，长度可依端点改变。在全部目标之前固定同一个 $o\in P$，置

$$
B_2(r)=\bigcup_{s\in S_r}D_s,\qquad
Q(r)=P\cap B_2(r)=\bigcup_{s\in S_r}S_s,\qquad S=S_o,\quad Q=Q(o).
\tag{XI139.2}
$$

唯一额外根条件仍是137.1的原意义：

$$
\mathsf G(o):\quad \exists U\subset V\text{ 开},\quad
o\in U,\quad U\cap P\subseteq Q(o).
\tag{XI139.3}
$$

以下直接消费[原域接口137.2、定理137.3及137.4、137.7—137.8][Q139XI]：

$$
\begin{gathered}
D_p\text{ 为非点紧暴露极大真面},\quad
S_p=\partial_{\rm rel}D_p\cong S^2,\quad D_p=\operatorname{conv}S_p,\\
\text{全部非空原真面只有纯单点和这些完整球},\\
D_p=D_q\Longrightarrow p=q,\qquad
p\ne q\Longrightarrow D_p\cap D_q\text{ 为空或一个原纯单点},\\
Q\subseteq P\text{ 在原 }V\text{ 中紧},\qquad
\exists U_0\subset V\text{ 开}:\quad o\in U_0,\quad
U_0\cap D_o=\varnothing,\quad
\forall q\in U_0\cap P, Q(q)=Q.
\end{gathered}
\tag{XI139.4}
$$

其中完整面接口的原来源为 FINITE_PURE VII103.2、EXCLUSION IX116.1；Conn 后的标签单射由 IX116.2 与 THREE_COPY VIII130.2取得。$U_0$ 可以按137.5缩小为避开整个 $D_o$ 的环境开集。紧性和近根集合相等在这里是137.3的结论；以下不把它们扩张到全 $P$，也不把 $\mathsf G$ 重新施于别的根。

定义辅助标签集及实际共同邻点存在域

$$
\Lambda=\{a\in P:S_a\subseteq Q\},\qquad
\mathcal J=\{(a,b)\in P^2:\exists r\in P, a\perp r, b\perp r\}.
\tag{XI139.5}
$$

$\Lambda$ 由每张完整原球的整个纯球缘定义，仍是原 $P$ 中的标签集合；$K,P,\mathcal E,\mathcal F_p,T_p,D_p$ 一概保留原定义。$\mathsf{Tri}(o)$ 表示存在三个不同原纯点 $o,s,t$，满足三条原零边。$d_\perp$ 表示原零图最短有限路径长度。

**定理 139.2（紧纯二步集到完整载体交点的桥梁）。** 在上述完整 EB3+$\mathsf{Conn}$+$\mathsf G(o)$ 原域中：

1. $Q$ 是紧、连通、可定向、无边界的四维拓扑流形。存在 $S_o\cong S^2$ 上的实秩二向量丛 $\xi_o$，使 $Q\setminus\{o\}\cong\operatorname{Tot}(\xi_o)$、$Q\cong T(\xi_o)$，且 $|\langle e(\xi_o),[S_o]\rangle|=1$。整数交形式为 $[\pm1]$；成熟的秩二丛分类进一步给底层拓扑同胚 $Q\cong\mathbb{CP}^2$。
2. $\Lambda$ 在原 $V$ 中紧，$a\mapsto D_a$ 在整个 $\Lambda$ 上按 Hausdorff 距离连续，并有 $S_o\subseteq\Lambda$ 及 $S_q\subseteq\Lambda$ 对每个 $q\in U_0\cap P$ 成立。
3. 任意两个不同原标签 $a,b\in\Lambda$ 都有唯一实际原纯共同邻点 $r\in Q$，准确满足 $D_a\cap D_b=\{r\}$。包括相同标签时仍有 $\Lambda^2\subseteq\mathcal J$。
4. 若 $\neg\mathsf{Tri}(o)$，则存在 $x\in Q$ 及 $a\in P\setminus(Q\cup\Lambda)$，使

$$
x\perp a,\qquad d_\perp(o,a)=3,\qquad
S_a\cap Q\ne\varnothing,\quad S_a\not\subseteq Q,\quad S_a\cap U_0=\varnothing.
\tag{XI139.6}
$$

以下逐项支付原球族的连续性、丛拓扑、根处流形性与交数适用条件；没有另加全局关联存在或正则嵌入前件。

### 139.2 实际定义域上的关联与两张完整横截球面

**引理 139.3（完整横截球面）。** 对任意原根 $r$，只在 $Q(r)\setminus\{r\}$ 上定义

$$
\pi_r:Q(r)\setminus\{r\}\longrightarrow S_r,\qquad
x\in S_{\pi_r(x)}.
\tag{XI139.7}
$$

该映射单值且连续。若 $S_a\subseteq Q(r)$ 且 $r\notin S_a$，则 $\pi_r|_{S_a}$ 是到整个 $S_r$ 的同胚。存在 $q\in U_0\cap P$、$q\ne o$，以及原标签 $a_0,b_0$，使 $S_{a_0}$ 是根 $o$ 的这种横截球面，$S_{b_0}$ 是根 $q$ 的这种横截球面，且 $Q(q)=Q$。

证明。不同 $s,t\in S_r$ 的完整球都含 $r$，所以点交接口给 $D_s\cap D_t=\{r\}$。这支付(XI139.7)的唯一性。若 $x_n\to x\ne r$，紧 $S_r$ 与紧 $\mathcal E$ 使任意子列可再取

$$
\pi_r(x_n)\to s\in S_r,\qquad
f_n\to f\in\mathcal E,\qquad
f_n(\pi_r(x_n))=1,\quad f_n(x_n)=0.
$$

极限满足 $f(s)=1,f(x)=0$，故 $s=\pi_r(x)$。所有聚点相同，给连续性；不需预用紧 $P$。这也是137.4已用的原紧见证方法。

若 $S_a\subseteq Q(r)$ 且 $r\notin S_a$，零对称给 $a\notin S_r$。若 $x,y\in S_a$ 同映到 $s\in S_r$，二者都在 $D_a\cap D_s$；$a\ne s$，故 $x=y$。因此 $\pi_r|_{S_a}$ 是整个紧二维球面到整个连通二维球面的连续单射。两者均为从原 $V$ 继承拓扑的无边界 Hausdorff 流形，[Hatcher，Theorem 2B.3、Corollary 2B.4][Q139AT]给满射及同胚。

固定 $t\in S_o$，在完整球面 $S_t$ 上取 $q\in U_0\setminus\{o\}$；存在性来自 $o\in S_t$ 且球面无孤立点。于是 $q\notin D_o$、$Q(q)=Q$，而 $S_q\cap S_o=\{t\}$。取

$$
a_0\in S_q\setminus S_o,\qquad b_0\in S_o\setminus S_q.
\tag{XI139.8}
$$

按二步集合的定义，$S_{a_0}\subseteq Q(q)=Q$、$S_{b_0}\subseteq Q(o)=Q$；零对称给 $o\notin S_{a_0}$、$q\notin S_{b_0}$。上一段分别适用于根 $o,q$。这没有从 $S_{a_0}\subseteq Q$ 推断标签 $a_0\in Q$。证毕。

### 139.3 紧纯球缘排除退化并给真实连续椭球族

**引理 139.4（指定根球族的非塌缩与连续性）。** 分别对引理139.3中的 $r=o,q$，映射 $s\mapsto D_s$ 在整个 $S_r$ 上 Hausdorff 连续。对任意固定辅助欧氏内积，其球心、形状算子和三维方向空间均连续。

证明。两种情形均有 $Q(r)=Q$；固定相应横截球面 $T$，令

$$
z_s=(\pi_r|_T)^{-1}(s)\in S_s\cap T.
\tag{XI139.9}
$$

$z_s$ 连续且从不等于 $r$。任取 $s_n\to s$，在辅助欧氏空间 $H_0=\ker u$ 内写

$$
D_{s_n}=c_n+B_n\overline{\mathbb B}^3,
\qquad B_n:\mathbb R^3\longrightarrow H_0\text{ 单射}.
\tag{XI139.10}
$$

可以逐球选择正交半轴为 $B_n$ 的列；这里只作有界选择，尚不假定这些选择连续。所有中心在紧 $K$ 中，半轴长不超过 $\operatorname{diam}K/2$。任意子列遂可再取 $c_n\to c,B_n\to B$，于是整个球 Hausdorff 收敛到

$$
F=c+B\overline{\mathbb B}^3.
\tag{XI139.11}
$$

选原共同零确认效应 $e_n\in\mathcal F_{s_n}$、$e_n|_{D_{s_n}}=0$；它们由完整面接口供应。紧 $\mathcal E$ 给进一步子列极限 $e$，且 $e(s)=1,e|_F=0$，故 $F\subseteq D_s$。同时 $r,z_{s_n}\in D_{s_n}$，所以 $r,z_s\in F$，两点不同。

对每个 $v\in S^2$，点 $c_n+B_nv$ 都在 $S_{s_n}\subseteq Q$；紧纯集 $Q$ 给

$$
c+BS^2\subseteq Q\subseteq P.
\tag{XI139.12}
$$

若 $\operatorname{rank}B<3$，沿非零核方向把任意单位闭球中的向量补到单位球面，得到 $B S^2=B\overline{\mathbb B}^3$。于是整个凸集 $F$ 都由原极点组成，只能是单点，与 $r\ne z_s$ 矛盾。因此 $\operatorname{rank}B=3$。

此时 $\partial_{\rm rel}F=c+B S^2\subseteq P\cap D_s=S_s$。$F,D_s$ 都是三维椭球且 $F\subseteq D_s$，所以仿射包相同。若包含严格，取 $y\in\operatorname{ri}F$ 及 $w\in\operatorname{ri}D_s\setminus F$，线段从 $y$ 首次离开 $F$ 的点既在 $\partial_{\rm rel}F$ 又在 $\operatorname{ri}D_s$，不可能同时原纯与非纯。故 $F=D_s$。任意子列的再极限均如此，整球连续性得证。

每颗完整椭球唯一写为

$$
D_s=c_s+A_s^{1/2}\overline B_{H_0},\qquad A_s\ge0,\quad\operatorname{rank}A_s=3,
\qquad Z_s=\operatorname{im}A_s.
\tag{XI139.13}
$$

若 $h_s(v)=\max_{x\in D_s}\langle v,x\rangle$，则

$$
h_s(v)-h_s(-v)=2\langle v,c_s\rangle,\qquad
\left(\frac{h_s(v)+h_s(-v)}2\right)^2=\langle A_sv,v\rangle.
\tag{XI139.14}
$$

Hausdorff 连续使支持函数连续；有限个坐标与极化给 $c_s,A_s$ 连续。秩恒三，正特征值在每点附近与零谱有间隙，故像投影、伪逆及其平方根连续。投影固定环境向量并作连续 Gram–Schmidt，给 $Z_s$ 的局部标架。这是 IX116.11中已陈述的成熟参数工具；本引理新增的是在指定原球族上由紧纯 $Q$ 和完整横截球面支付它的非退化入口，没有输入全 $P$ 紧性或全局球族连续。证毕。

### 139.4 显式秩二丛与根处的四维流形邻域

**引理 139.5（根外球极投影及根处补图）。** 对 $r=o,q$，存在 $S_r$ 上的实秩二向量丛 $\xi_r$，使 $Q\setminus\{r\}$ 与其总空间同胚。因此 $Q$ 是连通、可定向、无边界四维拓扑流形，且 $Q\cong T(\xi_o)$。

证明。保留(XI139.13)，令 $A_s^{\dagger/2}$ 表示伪逆的非负平方根，并置

$$
w_s=A_s^{\dagger/2}(r-c_s)\in Z_s,\qquad \|w_s\|=1,\qquad
(\xi_r)_s=Z_s\cap w_s^\perp.
\tag{XI139.15}
$$

连续性由引理139.4给出。若 $\Pi_s$ 是 $Z_s$ 的正交投影，则 $\Pi_s-w_s\otimes w_s$ 是连续的秩二正交投影。将两个固定环境向量投影到这些平面，在独立性保持的邻域内作 Gram–Schmidt，就给局部线性平凡化。因此这是实际构造的向量丛，尚未涉及任何嵌入的法丛。

逐纤维定义

$$
\begin{aligned}
Y_s(v)&=\frac{2v+(\|v\|^2-1)w_s}{1+\|v\|^2},\\
\Psi_r(s,v)&=c_s+A_s^{1/2}Y_s(v),\qquad v\in(\xi_r)_s.
\end{aligned}
\tag{XI139.16}
$$

$Y_s$ 是从二维平面到 $Z_s$ 的单位球面去掉 $w_s$ 的球极投影逆；$c_s+A_s^{1/2}w_s=r$，故其像恰为 $S_s\setminus\{r\}$。不同纤维的像不交，且这些像覆盖 $Q\setminus\{r\}$。$\Psi_r$ 连续；其逆的第一坐标是已付的 $\pi_r$，第二坐标由

$$
y=A_{\pi_r(x)}^{\dagger/2}(x-c_{\pi_r(x)}),\qquad
v=\frac{y-\langle y,w_{\pi_r(x)}\rangle w_{\pi_r(x)}}{1-\langle y,w_{\pi_r(x)}\rangle}
\tag{XI139.17}
$$

给出。因 $x\ne r$，分母严格正；各项连续，故逆也连续。这里的同胚使用原子空间拓扑，且完整覆盖每张原 $S_s\setminus\{r\}$。

秩二丛的基 $S_r$ 是二维流形，所以总空间是无边界四维流形。$Q\setminus\{o\}$ 给全部非根点的坐标；由同一个 $Q(q)=Q$，$Q\setminus\{q\}$ 又给 $o$ 的坐标。两者在 $Q$ 中都是开集并覆盖 $Q$。作为有限维 $V$ 的子空间，$Q$ Hausdorff、第二可数；加上(XI139.4)的紧性，流形前件全部成立。

每张连通 $S_s$ 都含 $o$，故 $Q=\bigcup_{s\in S_o}S_s$ 连通。$S_o\cong S^2$ 单连通，$\xi_o$ 可定向；结合基的定向使其总空间可定向。在 $o$ 取一个四维坐标球，删去 $o$ 后仍连通，其定向与总空间定向相差一个固定符号，调整后便延拓过 $o$。所以 $Q$ 可定向。

最后，紧 Hausdorff 空间 $Q$ 是其非紧开子空间 $Q\setminus\{o\}$ 的一点紧化：删去任何含 $o$ 的开邻域得到紧集，反之该开子空间中的紧集在 $Q$ 中闭且避开 $o$。紧基上的向量丛总空间的一点紧化是其 Thom 空间 $D(\xi_o)/S(\xi_o)$，其中盘丛及球丛用任一连续丛度量定义；见[Hatcher，Vector Bundles and K-Theory，Thom Spaces，印刷页112][Q139VB]。因此 $Q\cong T(\xi_o)$。这一步不预设无穷远点是流形点；它已经由第二根的原坐标支付。证毕。

### 139.5 Euler 数、整数交形式与拓扑识别

**引理 139.6（Euler 数的绝对值为一）。** 选定 $S_o$ 与 $\xi_o$ 的定向，令 $\alpha$ 生成 $H^2(S_o;\mathbb Z)$，$e(\xi_o)=n\alpha$。则 $n=\pm1$，$H_2(Q;\mathbb Z)\cong\mathbb Z$，交形式为 $[\pm1]$，并有底层拓扑同胚 $Q\cong\mathbb{CP}^2$。

证明。引理139.5给的是基为紧二维球面的可定向实秩二向量丛，其盘／球丛是实际局部平凡丛对。[Hatcher，Theorem 4D.10、Corollary 4D.9][Q139AT]因此供应整数 Thom 类 $\tau$ 及同构

$$
\Phi_\xi:H^i(S_o;\mathbb Z)\overset\sim\longrightarrow
\widetilde H^{i+2}(Q;\mathbb Z),\qquad
\Phi_\xi(1)=\tau.
\tag{XI139.18}
$$

于是 $H^2(Q)=\mathbb Z\tau$、$H^4(Q)=\mathbb Z\Phi_\xi(\alpha)$，其他正次上同调为零。Euler 类是 Thom 类在零截面的限制；原 Thom 平方公式准确给

$$
\tau\smile\tau=\Phi_\xi(e(\xi_o))=n\Phi_\xi(\alpha).
\tag{XI139.19}
$$

公式及相对乘法的类型见[Hatcher，§4.D末段及 Vector Bundles and K-Theory §3.2，印刷页88、91—92][Q139AT][Q139VB]。

此时 $Q$ 已是闭、连通、整数可定向四维拓扑流形，才可用[Hatcher，Theorem 3.30、Corollary 3.39][Q139AT]。后者对无限循环直和项的生成元 $\tau$ 要求存在 $m\tau\in H^2(Q;\mathbb Z)$，使 $\tau\smile m\tau$ 生成 $H^4(Q;\mathbb Z)$。由(XI139.19)，$mn=\pm1$，所以 $n=\pm1$。整数对偶给 $H_2(Q;\mathbb Z)\cong\mathbb Z$，秩一交形式遂为 $[\pm1]$；符号依定向。

拓扑识别只消费成熟丛分类。[Hatcher，Proposition 1.14及印刷页26—27的秩二球面基分类][Q139VB]以 $S^1\to SO(2)\cong S^1$ 的粘合次数分类 $S^2$ 上的可定向实秩二丛；其次数的绝对值等于 Euler 数绝对值，这也是 Proposition 3.22的首个截面障碍识别。因此忘掉定向后，$|n|=1$ 的丛是 Hopf 复线丛的底层实丛。该丛的 Thom 空间为 $\mathbb{CP}^2$，见同书§3.2印刷页93的 Hopf 丛 Thom 空间说明。故 $Q\cong\mathbb{CP}^2$。这里没有以同调环相同替代拓扑分类，也不调用原凸体的 Jordan 分类。证毕。

### 139.6 不借入局部平坦性的原球交数

**引理 139.7（每张完整内载球缘都代表生成元）。** 对每个 $a\in\Lambda$，嵌入 $S_a\hookrightarrow Q$ 的整数基本类生成 $H_2(Q;\mathbb Z)$。任意两个这样的球缘必相交；不同原标签的整个球恰交于一个实际原纯点。

证明。若 $a\in S_o$，$S_a$ 正是 $\xi_o$ 的一根纤维加公共无穷远点 $o$。Thom 类在这个纤维紧化 $S^2$ 上限制为生成元，故

$$
|\langle\tau,[S_a]\rangle|=1.
\tag{XI139.20}
$$

若 $a\notin S_o$，则 $o\notin S_a$；引理139.3使 $\pi_o|_{S_a}$ 为到整个 $S_o$ 的同胚。经 $\Psi_o^{-1}$ 后，$S_a$ 是 $\xi_o$ 的一个连续截面的像。沿纤维标量乘法将截面同伦到零截面，Thom 类在零截面限制为 $e(\xi_o)$，所以

$$
\langle\tau,[S_a]\rangle=\pm\langle e(\xi_o),[S_o]\rangle=\pm1.
\tag{XI139.21}
$$

由整数对偶及 $H^3(Q)=0$ 有 $H_1(Q)=0$，再由整系数通用系数定理，$H^2(Q)\to\operatorname{Hom}(H_2(Q),\mathbb Z)$ 为同构。因此(XI139.20)—(XI139.21)确实说明每个 $[S_a]$ 是 $H_2(Q)\cong\mathbb Z$ 的生成元，而非只证明它非零。它们两两的同调交数遂为 $\pm1$。

这里须特别支付“同调交数非零迫实际相交”，不能偷用光滑横截交点计数。反设两个球缘 $S_a,S_b$ 不交。它们是 $Q$ 的不交紧子集，故有不交开邻域 $O_a,O_b\subset Q$。作为可定向四维拓扑流形的开子集，二者也都是可定向四维流形；不要求它们是球面的管状邻域。球面基本类分别给

$$
z_a\in H_2(O_a;\mathbb Z),\qquad z_b\in H_2(O_b;\mathbb Z).
$$

[Hatcher，Theorem 3.35及其前后紧支撑构造][Q139AT]给 $\beta_a\in H_c^2(O_a;\mathbb Z)$、$\beta_b\in H_c^2(O_b;\mathbb Z)$，分别对偶于 $z_a,z_b$。取其紧支撑代表所在的紧集 $K_a\subset O_a$、$K_b\subset O_b$。切除给开嵌入的延拓映射

$$
H_c^2(O_a)\longrightarrow H^2(Q),\qquad H_c^2(O_b)\longrightarrow H^2(Q).
$$

这些映射将 $\beta_a,\beta_b$ 分别送成 $[S_a],[S_b]$ 的 Poincaré 对偶：在各紧支撑集上限制 $Q$ 的基本定向类，切除识别为相应开集的局部基本类，cap 自然性便给此等式。这是该书印刷页240—241、244—248的同一构造，并非假定嵌入具有法丛。

两个延拓类分别来自 $H^2(Q,Q\setminus K_a)$ 与 $H^2(Q,Q\setminus K_b)$。补集都是开集，故[Hatcher，印刷页209—210的相对 cup 乘积][Q139AT]适用。因 $K_a\cap K_b=\varnothing$，乘积落在

$$
H^4\bigl(Q,(Q\setminus K_a)\cup(Q\setminus K_b)\bigr)
=H^4(Q,Q)=0.
\tag{XI139.22}
$$

于是同调交数为零，与 $\pm1$ 矛盾。整个论证只用连续球面映射的基本类、开流形对偶及相对乘积；未给 $S_a\hookrightarrow Q$ 添加光滑、局部平坦或管状邻域假设。

故 $S_a\cap S_b\ne\varnothing$。当 $a\ne b$ 时，原标签单射使 $D_a\ne D_b$，原点交接口给唯一 $r\in P$，满足

$$
D_a\cap D_b=S_a\cap S_b=\{r\},\qquad r\in Q,\quad a\perp r,\quad b\perp r.
\tag{XI139.23}
$$

当 $a=b$，任选非空 $S_a\subseteq Q$ 中一点仍给实际共同邻点，所以包括对角线有 $\Lambda^2\subseteq\mathcal J$。这建立的是原标签端点之间的存在性；并未单凭 $S_a\subseteq Q$ 就对标签 $a$ 写 $\pi_o(a)$。证毕。

### 139.7 完整载体标签集的紧性及整个球族连续性

**引理 139.8（以三个固定球缘排除标签极限塌缩）。** $\Lambda$ 在原 $K$ 中闭而紧，且 $a\mapsto D_a$ 在整个 $\Lambda$ 上 Hausdorff 连续。

证明。先由定义得 $S_o\subseteq\Lambda$。更一般地，$q\in U_0\cap P$ 及 $a\in S_q$ 时，$S_a\subseteq Q(q)=Q$，故

$$
S_o\ \cup\!\bigcup_{q\in U_0\cap P}S_q\ \subseteq\Lambda.
\tag{XI139.24}
$$

取不同 $s,t\in S_o$，以及引理139.3的 $a_0$。这三个标签在 $\Lambda$ 中，而且

$$
S_s\cap S_t=\{o\},\qquad o\notin S_{a_0},\qquad
S_s\cap S_t\cap S_{a_0}=\varnothing.
\tag{XI139.25}
$$

引理139.7保证每个 $a\in\Lambda$ 的 $S_a$ 都与这三张固定球缘分别相交；若标签恰相同，就用该球缘自身。这些是已经证明的实际交点，不是新关联前件。

现令 $a_n\in\Lambda$、$a_n\to z\in K$，尚不假定 $z$ 纯。如(XI139.10)—(XI139.12)，任意子列可再选中心及半轴参数，使

$$
D_{a_n}=c_n+B_n\overline{\mathbb B}^3\longrightarrow
F=c+B\overline{\mathbb B}^3,\qquad c+B S^2\subseteq Q\subseteq P.
\tag{XI139.26}
$$

若 $\operatorname{rank}B<3$，整个 $F$ 由纯点组成，故 $F=\{v\}$。在 $S_{a_n}$ 与三张固定球缘的交点各取一点；它们距 $F$ 都趋零，三张固定球缘紧闭，因此 $v$ 同时属于它们，违反(XI139.25)。故 $\operatorname{rank}B=3$，$\partial_{\rm rel}F\subseteq Q$。

从原完整面接口选 $e_n\in\mathcal F_{a_n}$、$e_n|_{D_{a_n}}=0$，紧性给共同子列极限 $e\in\mathcal E$，满足

$$
e(z)=1,\qquad e|_F=0.
\tag{XI139.27}
$$

取不同 $x,y\in\partial_{\rm rel}F\subseteq Q\subseteq P$。同一原补效应 $u-e$ 确认 $x,y$ 且在 $z$ 读零，所以 $z\in D_x\cap D_y$。Inj 使两球不同，原点交接口迫 $z$ 纯。此为 IX118.4非点极限判据在这里的直接两端见证证明，不预用紧 $P$。

现在(XI139.27)给 $F\subseteq D_z$；两者都是三维椭球，且 $\partial F\subseteq P\cap D_z$，引理139.4的同维包含论证给 $F=D_z$。于是 $S_z=\partial F\subseteq Q$、$z\in\Lambda$。任意原 $K$ 中的序列极限均收下，$\Lambda$ 在紧度量空间 $K$ 中闭而紧。

若 $a_n\to a\in\Lambda$，同一论证使每个整球参数子列的再极限均为 $D_a$，故 $D_{a_n}\to D_a$。支持函数式(XI139.14)也给整个 $\Lambda$ 上的球心、形状及球缘连续。结论只涉及这个由完整原球缘定义的标签集；它不声称全 $P$ 的球族连续。证毕。

### 139.8 无根三角必有真正的距离三越出载体

**引理 139.9（两团紧球族不能封闭无三角分支）。** 有

$$
\mathsf{Tri}(o)\quad\Longleftrightarrow\quad Q\cap\Lambda\ne\varnothing.
\tag{XI139.28}
$$

若无根三角，则(XI139.6)成立。

证明。根三角中的另一个顶点 $s$ 属于 $S_o\cap Q$；$S_o\subseteq\Lambda$ 给正向。反之，设 $a\in Q\cap\Lambda$。若 $a\ne o$，取 $s=\pi_o(a)\in S_o$；零对称给 $s\in S_a\subseteq Q$，故 $s\in S_o\cap Q$。若 $a=o$，$o\in\Lambda$ 直接给 $S_o\subseteq Q$，也可取 $s\in S_o\cap Q$。按 $Q$ 的定义，某个 $t\in S_o$ 满足 $s\in S_t$；反自反性使 $o,s,t$ 两两不同，得到真实根三角。这证明(XI139.28)。

现假设无根三角，则 $Q,\Lambda$ 是不交非空紧集。反设 $P=Q\cup\Lambda$。每个 $a\in\Lambda$ 已有 $S_a\subseteq Q$；若 $x\in Q$，存在 $s\in S_o\subseteq\Lambda$ 满足 $x\in S_s$，故 $s\in S_x$。连通球面 $S_x$ 在不交闭开分割 $P=Q\sqcup\Lambda$ 中只能留在一侧，因而

$$
S_a\subseteq Q\quad(a\in\Lambda),\qquad
S_x\subseteq\Lambda\quad(x\in Q).
\tag{XI139.29}
$$

考虑保留全部混态的两个集合

$$
H_\Lambda=\bigcup_{a\in\Lambda}D_a,\qquad H_Q=\bigcup_{x\in Q}D_x.
\tag{XI139.30}
$$

对紧纯标签集 $A$，紧集

$$
\{(a,y,f)\in A\times K\times\mathcal E:f(a)=1,f(y)=0\}
\tag{XI139.31}
$$

在 $K$ 上的投影恰为 $\bigcup_{a\in A}D_a$。所以(XI139.30)两侧非空且紧，不需假设 $P$ 紧。若有共同点，它在不同标签的两球交中，故原纯；(XI139.29)又使它同时在 $Q,\Lambda$，矛盾。全部非空真面的原分类及反设 $P=Q\cup\Lambda$ 给

$$
\partial_{\rm rel}K=H_\Lambda\sqcup H_Q.
\tag{XI139.32}
$$

这里纯单点也被覆盖：$x\in Q$ 有上述 $s\in\Lambda$ 使 $x\in D_s$；$a\in\Lambda$ 任取 $x\in S_a\subseteq Q$，零对称给 $a\in D_x$。$K$ 有三维真面，故仿射维数至少四，其相对边界由内点径向投影同胚于相应球面，因而连通。(XI139.32)将它分成两个不交非空紧集，不可能。因此 $P\setminus(Q\cup\Lambda)\ne\varnothing$。

用 Conn 从 $o\in Q$ 沿一条有限原零边路到这个外部集合，取首次离开 $Q\cup\Lambda$ 的顶点 $a$ 及其前驱 $x$。前驱不可能在 $\Lambda$，因为 $\Lambda$ 中标签的全部原邻点都在 $Q$；故 $x\in Q$，且 $x\perp a$。$x\in Q$ 给从 $o$ 到 $x$ 的两步路，所以 $d_\perp(o,a)\le3$。另一方面，$a\ne o$、$a\notin S_o$（因 $S_o\subseteq\Lambda$）、$a\notin Q$，依次排除距离零、一、二，故距离恰为三。

$x\in S_a\cap Q$，而 $a\notin\Lambda$ 给 $S_a\not\subseteq Q$。若 $y\in S_a\cap U_0$，则 $y\in P$、$Q(y)=Q$ 且 $a\in S_y$；按二步集合定义便有 $S_a\subseteq Q(y)=Q$，矛盾。因此 $S_a\cap U_0=\varnothing$，得到(XI139.6)。定理139.2全部结论证毕。

### 139.9 已得几何与未付全域覆盖的准确分界

新建立的存在性是 $\Lambda^2\subseteq\mathcal J$：两个端点都是原纯标签，交点是真实原纯共同邻点；标签集的紧性及其整个球族连续性也已推出。虽然 $S_o\subseteq\Lambda$，但 $o\in\Lambda$ 自身要求整个 $S_o\subseteq Q$，尚未得到。因此这个交点定理不能未经新论证用于任意 $(o,a)$，更不能把原部分映射 $\pi_o$ 的定义域改成全部 $P\setminus\{o\}$。

对照[X133.1、133.3][Q139X]，固定根的准确全域条件仍是

$$
\begin{aligned}
\mathsf D_2(o):&\quad\forall a\in P:\quad o\perp a\ \lor\ \exists r\in P\ (o\perp r\land a\perp r),\\
\mathsf R_1:&\quad\exists o\in P\ \mathsf D_2(o).
\end{aligned}
\tag{XI139.33}
$$

它先要求 $P\subseteq S_o\cup Q(o)$；X133.3在该前件下才进一步给 $Q(o)=P$。本章尚未证明存在任何满足(XI139.33)的根，也未证明 $\mathsf{MC}$。$Q\cong\mathbb{CP}^2$ 只识别这个紧纯二步集的拓扑，不产生整个 $K$ 的仿射表示、全效应 least、全态 Born 读数、正限制逆或原锥 Jordan 结构。

无根三角时，137.9中原法向截面的严格嵌套含义继续保持：令 $N_o=\{h\in C^*:h(o)=0\}$、$L_o=\operatorname{span}N_o$，取137.2的唯一完整暴露尺 $e_o$、$g_o=u-e_o$，令 $J(x)(h)=h(x)$、$H=\{\lambda\in L_o^*: \lambda(g_o)=1\}$、$\Omega=N_o^\vee\cap H$，并令 $\iota=J|_{D_o}$。该原接口给

$$
\neg\mathsf{Tri}(o)\quad\Longleftrightarrow\quad
\iota(D_o)\Subset\operatorname{int}_H\Omega.
\tag{XI139.34}
$$

本章未排除这种严格嵌套；它证明该分支必须带着(XI139.6)的实际完整距离三载体，不能由 $Q,\Lambda$ 两团紧球族封闭整个原域。尚缺的是排除这种遇到 $Q$、避开 $U_0$ 而球缘伸出 $Q$ 的真实原载体，或另行支付全域覆盖的充分桥。即使另有一个根三角，也不能仅以(XI139.28)的接触替代全目标量词。这里没有构造满足全部原前件而失败覆盖的反例，也不宣称该边界逻辑独立。

### 139.10 两条完整静态候选的同原字典与反向

**既有条件应用 139.10。** 完整 EB3 加(XI139.33)的 $\mathsf R_1$，仍按[X133.6—133.7][Q139X]等价于存在同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\mathrm{PSD}_3(\mathbb C))=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI139.35}
$$

另一条完整候选仍是[定义135.1、定理135.5与条件应用136.4][Q139XI]的完整 EB3+$\mathsf{MC}$。记原完整 $D_p$ 的唯一仿射球心为 $c_p$，其条件准确为：任意正整数 $m,n$，全部原纯点 $p_i,q_j\in P$，全部非负实权重 $\lambda_i,\mu_j$，若

$$
\sum_{i=1}^m\lambda_i=\sum_{j=1}^n\mu_j=1,\qquad
\sum_{i=1}^m\lambda_i p_i=\sum_{j=1}^n\mu_j q_j,
\quad\text{则}\quad
\sum_{i=1}^m\lambda_i c_{p_i}=\sum_{j=1}^n\mu_j c_{q_j}.
\tag{XI139.36}
$$

零权、重复标签及同一原态的全部有限纯分解都在量词内。135.2—135.4的球心严格反序、全张成及线性下降先取得实际可逆正保质量球心图；136.2—136.3也可供应其纯域紧性和全轴间隙。随后135.5仍消费 IX118.8的既有分类，包括其既有依赖。$\mathsf R_1$ 路线由 X133.6消费 IX120.4—120.5及 IX116.17—116.18。这里直接引用这两条同原等价及其反向，不重证分类，不把139.2的拓扑同胚替代(XI139.35)的锥／单位同构。

只在另行支付任一完整候选后，取其同一个 $\Phi$，令 $P_v=vv^*$、$v^*v=1$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$、$U=\Phi(I_3)$，已有完整字典为：

| 静态对象 | 同一个原锥和原单位中的准确对应 |
| --- | --- |
| 全载体、质量、单位 | $\dim_{\mathbb R}V=9$；全部 $X\succeq0$，包括零与任意非负质量，由 $\Phi$ 运输到整个 $C$，且 $u(\Phi X)=\operatorname{Tr}X$。$u\in V^*$ 与 Jordan 单位 $U\in V$ 不混型。 |
| 全态、凸混合、复射线 | $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，保持全部凸混合；全部原 $P=\{p_v\}\cong\mathbb{CP}^2$。任意非零 $z\in\mathbb C^3$ 对应 $\Phi(zz^*/(z^*z))$，非零复倍数给同一原纯标签。 |
| 全效应、全混态 Born 评价 | $f_M(\Phi X)=\operatorname{Tr}(MX)$ 恰遍历全部 $0\preceq M\preceq I_3$；零、单位、补及序均保持。任意实线性读数对应任意 Hermitian $M$。 |
| 完整确认菜单、least、minimum | $\mathcal F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\}$。least 为 $f_{P_v}$；对每个原混态 $T_{p_v}(\Phi\rho)=\operatorname{Tr}(P_v\rho)=v^*\rho v$。确认菜单不是单点。 |
| 全纯比较及整个排除球 | $T_{p_v}(p_w)=|v^*w|^2$；未归一时除以 $(v^*v)(w^*w)$。$D_{p_v}=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1,\rho v=0\}$，含全部混态；纯球缘为 $\mathbb{CP}^1\cong S^2$。 |
| 维数、中心、完整框架 | $\dim_{\rm aff}K=8$，全纯域实维四，完整排除球实维三；$c_{p_v}=\Phi(Q_v/2)=(U-p_v)/2$，总体中心为 $U/3$。原零三角对应三个和为 $I_3$ 的正交秩一投影，三个 least 效应之和为 $u$；每条原零边有唯一第三原纯点，数学完美区别容量为三。 |
| 全部有限数学测量 | 对任意有限结果数，$f_j\in C^*$、$\sum_jf_j=u$ 恰对应全部 $M_j\succeq0$、$\sum_jM_j=I_3$ 的 POVM；每个原输入概率为 $\operatorname{Tr}(M_j\rho)$，允许零效应。 |
| 谱与实可观测量 | 每个原态有三项正交谱分解，允许零权和重谱；全部 Hermitian 可观测量有实谱及谱效应，重谱不指定唯一的逐本征射线。 |
| Jordan、自对偶、球心图 | $\langle\Phi X,\Phi Y\rangle_\Phi=\operatorname{Tr}(XY)$ 下 $C$ 自对偶，$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$，单位为 $U$；$R(x)=(u(x)U-x)/2$ 在全部 $V$ 上为球心图。 |

确认菜单和全部混输入上的 minimum 必须一起保留。$0\preceq M\preceq I_3$ 且 $v^*Mv=1$ 时，正半定性给 $(I_3-M)v=0$；Hermitian 性消去交叉块，恰给上表的全部 $B$。对每个 $\rho\succeq0$，$\operatorname{Tr}(B\rho)\ge0$，而 $B=0$ 是同一原菜单中的允许选择并达到下界，故取得 least 及所有混态上的 minimum。正半定性还给 $v^*\rho v=0\Longleftrightarrow\rho v=0$，在整个 $v^\perp\cong\mathbb C^2$ 上用 Pauli 坐标才得到完整闭三球。

反向取满足(XI139.35)的整个标准对象。上述完整确认计算为每个原纯标签供应 EB3。对任意预先指定根 $p_v$ 和任意目标 $p_w$，包括相同标签，$\dim_{\mathbb C}\operatorname{span}\{v,w\}\le2$，故有单位 $z$ 垂直于这个张成空间；同一原纯点 $p_z$ 同时与二者有真实原零边，分别由原投影效应见证。因此每个根都满足 $Q(p_v)=P$、$\mathsf D_2(p_v)$、Conn 和 $\mathsf G(p_v)$。同一个 $\Phi$ 又给 $c_p=(U-p)/2$，使任何纯混合 $x=\sum_i\lambda_i p_i$ 的球心替换都等于 $(U-x)/2$；含零权与重复标签的全部分解都相容，故完整 $\mathsf{MC}$ 成立。这些是既有全域反向，不是从单根芽推出 $\mathsf R_1$ 或 $\mathsf{MC}$ 的新蕴含。

### 139.11 原来源、全部有限复合、事件与物理时间合同

逐项完整继承[SAME_READBACK SECTION127.10][Q139SR]（节号）和[EXCLUSION X133.10][Q139X]，并保留137.11的全部传递接口：SAME_READBACK125.11、124.9、123.13，EXCLUSION VIII命题113.11与112.9、EXCLUSION IX120.11，THREE_COPY VII121.12、122.14，以及所指 INTRINSIC_POLAR VI定义89.7、全部两尺度式(89.13)、89.8—89.10、V88.6与87章、原生续卷VII和III的来源、全未来与动态合同；BILATERAL VIII128.H的继承同样保留。每项均按原文的完整前件、原对象、作用域及全部量词使用。操作／来源的 INTRINSIC_POLAR VI 与整球 BILATERAL VI 不混同。

同一个原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性，零／单位／补／有界倍增、重复标签和每种同中点实现，全部非负质量及零／次归一／不等质量，过程与参考各自完整的相关联合输入域继续保留。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)的全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集，均保持原定义。操作映射 $p$ 与纯标签不同型，$G=1_E$ 与根芽条件不同型。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、旧 support、全部合法未来和每个中间切口均保留。原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption及资源合同继续由原消费者承担。数学射线、原关联交点和数学三结果效应不产生实际来源、接线、权限或未来。

对每个有限 $N\ge1$，仍须供应实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 及完整原效应区间。对每个实际二分割 $a+b=N$，保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{XI139.37}
$$

同一产品配对、严格张量单位、全部原因子置换及其逆的正性、规范重括号与指定运输下不连续位置分块均保持。完整实际二份比较 $S_2$ 仍量化每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族、全部 $t_\ell\ge0$、$\sum_\ell t_\ell=1$，包括零权和重复标签，并要求

$$
\begin{gathered}
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\\
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]_{C_2^*}\\f(p)=1}}f(x).
\end{gathered}
\tag{XI139.38}
$$

单体 minimum 的线性化不支付这项全纠缠合同。原低二份 $q=1,2$ 的 least／谱性／正面投影及保纯到 Jordan 桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制与秩和实维乘法的复型选择，以及同一实际两因子的产品正规形，仍是既有全有限层级定理分别需要的三项具名供应。

非经典支路 $\mathsf F_{\max}$ 仍要求同一最大复块 $n_r=L\ge2$、同一含相位正交基上的实际三份正性资源

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{XI139.39}
$$

其余三份扇区为零，归一原源为 $\Delta_r/L$；不预付三份纯性或实际制备，全经典 $L=1$ 支路按原规则免除此资源。单体复三能级支路为 $L=3$，二、三份秩分别为九、二十七；高阶整个排除集不继续被规定为单体 EB3。形式矩阵不保证实际 $C_3$ 成员资格。全部联合前件及三项供应齐备后，才调用既有全有限层级结论。

对输入、输出份数 $m,n$ 及同一原类型的实线性映射 $F:W_m\to W_n$，数学全旁观正性仍量化每个旁观份数 $b\ge0$ 和任意含纠缠的同一共同输入，要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{XI139.40}
$$

只有实际完整有限层级及共同表示已经供应，才沿原 Choi 桥识别通常 CP、矩形跨扇区 Kraus 和逐输入 TP／TNI 原预算。对每个原非负输入 $x\in C_m$，分别要求 TP 的 $u_n(Fx)=u_m(x)$ 或 TNI 的 $u_n(Fx)\le u_m(x)$；同族分支预算由同一个输入上的分支总和承担。同一实际事件的 CP 另需原完整提升、实际探针和相容核；全部数学 CP-TNI 分支实际可用另需原事件饱和选择。同族仪器保留共同输入预算、接线、记录、粗粒化和校准；只对严格正质量分支条件归一，零质量分支不强定归一条件态。Lüders 更新另需同一分支的锐效应、接受态中性与输出校准。全部数学 POVM、三张原效应和为单位及可执行同族仪器，各保留原合同。静态球心图的正性不支付其全旁观 CP 或实际事件资格。

原物理钟、实际动态来源、连续齐次可逆时间群与单位继续分别供应。若另给同载体上的全实时间连续线性群 $A_t$，满足

$$
A_0=I,\qquad A_{s+t}=A_sA_t,\qquad A_t(C)=C,\qquad uA_t=u,
\tag{XI139.41}
$$

才有该额外时间供应的有限维生成元。在重构复块上又给保迹酉时间族之后，才使用

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\mathrm i[H,\rho]/\hbar,\qquad H=H^*.
\tag{XI139.42}
$$

量词覆盖全部原输入及全部实际时间。$H$ 的标量平移不改变态作用，时间重标改变生成元尺度而不改变静态几何；恒等时间族与非平凡 Hamiltonian 族可共享全部静态对象。实际 Hamiltonian、能量识别与标定、数值 $\hbar$、时空和物理空间维数仍有各自费用。原图距离三只数静态关联步数，不是经过三单位物理时间；四维 $Q$ 和三维排除球也不指定物理空间维数。

### 139.12 数学归属、适用条件与完整白话

本章采用 `repo-derived` 综合归属。原完整面、点交、Conn 后的 Inj 复用 FINITE_PURE VII103.2、EXCLUSION IX116.1—116.2及 THREE_COPY VIII130.2；实际存在域上的关联连续性复用137.4的紧见证方法。近根完整 $Q$ 集合相等与环境紧纯 $Q$ 则准确消费137.3、137.7—137.8，不以先有矩阵表示证明这些前件。

新增承重连接为：以两个原完整横截球面和紧纯球缘排除指定根球族退化；从原连续椭球族构造秩二丛，用第二根补齐公共根处的四维坐标；经整数对偶取得非零交形式，再把完整载于 $Q$ 的所有原球缘识别为生成元，支付全部 $\Lambda$ 标签对的实际交点；用三个固定球缘排除标签塌缩，取得紧 $\Lambda$ 与全 $\Lambda$ 球族连续；最后在无根三角支用原凸边界和 Conn 取得真正的距离三越出载体。此链中 $\Lambda$ 紧性、球族连续性及关联存在性均为结论。

外部成熟工具及其实际前件如下：Hatcher《Algebraic Topology》Theorem 2B.3、Corollary 2B.4只用于已经支付连续单射的完整二维球面；Theorem 4D.10、Corollary 4D.9及§4.D末段只用于已构造的可定向秩二丛盘／球对；Theorem 3.30、Corollary 3.39只在 $Q$ 的闭连通可定向四维流形性成立后使用。Theorem 3.35用于该流形的开邻域，印刷页209—210的相对乘积用于两个开补集。由此非零交数确实迫实际相交，不要求球面嵌入光滑或局部平坦。原椭球在 $V$ 内的存在不被当作其在 $Q$ 内的法丛。

Hatcher《Vector Bundles and K-Theory》Proposition 1.14及印刷页26—27供应 $S^2$ 上定向实二平面丛的粘合分类；§3.2及 Proposition 3.22供应 Euler 类与截面障碍的对应，印刷页93供应 Hopf 丛 Thom 空间的射影平面识别。这些成熟分类只是139.6的消费者。139.10的同原静态等价、字典与反向全部复用135.5、136.4、X133.6—133.7及其明确的 IX 分类来源；它们不是139.2拓扑结论的另一种表述。没有调用要求整个面格 modular、全域关联开放或正限制逆的其他重构入口。

**完整白话。** 原来的状态体、全部纯态、全部混态和全部允许读数始终是同一套对象。每个纯标签带着一整颗实心排除三球，球面就是它的全部原纯零邻居。固定根的二步集合 $Q$，由所有经过根的这些完整球面组成。已有单根结论告诉我们，$Q$ 紧而且极限仍纯，附近另一个原纯点拥有完全相同的 $Q$。

本章首先找到一张不经过根、却横过每张根球面的完整原球面。它为每张根球面连续地标出另一个点。假如移动中的实心球压扁，球面极限会填满低维实心片；因这些极限全在纯 $Q$ 中，实心片上的混合点也会被迫成为原极点，不可能。整球也不能缩成一点，因为根与横截点始终是不同的两个点。因此这族完整球确实连续而不退化。

把每张球面上的根删掉，球极投影将它变成一个二维平面。这些平面连续拼成二维向量丛，底面是根自己的完整邻点球面。另一根的同一描述保证公共汇合点也有普通四维坐标，所以 $Q$ 是闭四维空间，根不是未经解释的尖点。闭流形的整数对偶迫使这个丛的 Euler 数只能为正负一；成熟丛分类随后把这个紧空间识别为复射影平面。

接着收集所有“整张球缘都留在 $Q$ 内”的原标签，得到 $\Lambda$。这样的每张球缘，不论是经过根的纤维紧化，还是避开根的完整截面，都代表同一个二维同调生成元，交数不能消掉。如果两张球缘完全错开，就能用不交开邻域把它们的对偶类支撑分开，交数必须为零，产生矛盾。因此两个不同 $\Lambda$ 标签确实有唯一原纯共同邻点。再固定三张没有公共点的球缘，它们阻止任何 $\Lambda$ 标签序列的整球缩成一点；非退化极限又迫极限标签仍纯且仍属于 $\Lambda$，所以标签集本身紧。

但这还不能把全部原纯态塞进 $Q$。尤其“根的邻点标签属于 $\Lambda$”不等于“根标签属于 $\Lambda$”；后者还要求根自己的整张排除球缘也在 $Q$ 中。若根没有三角，$Q$ 与 $\Lambda$ 是两团不交紧集，却不可能轮流承载全部原球，否则整个原凸体边界会被分成两半。因此完整原域必须有一张真正从外面伸进来的球：它的标签到根恰为三步，球缘碰到 $Q$，避开原近根邻域，并有原纯点伸到 $Q$ 外。排除这种真实载体以及证明一个根覆盖全部原目标，仍是未付的全域桥；仅有一次接触也还没有支付它。

最后，$Q$ 的复射影平面拓扑并没有确定全部混态如何凸混合，也没有确定全部原效应的数值。只有另行取得固定根全覆盖或全部混合配方的球心相容，同一个锥及单位表示才运输完整密度态、全部射线、非单点确认菜单、least、每个混态上的 Born minimum、全部有限数学 POVM、谱和 Jordan 字典。实际来源、读回与全部质量、全有限联合和纠缠、三份相位资源、全旁观 CP、逐输入预算、事件仪器、记录、全部合法未来与切口、物理钟、Hamiltonian、能量和数值 $\hbar$ 仍逐项保留139.11的原合同。静态关系步数不是时间，数学效应和拓扑交点也不产生实际装置。

[Q139XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "135.1—135.6：完整 MC、同原分类与字典；136.1—136.4：实际球心图前件、纯判别与全轴间隙；137.1—137.4、137.7—137.9：完整原域、原面、实际关联、近根集合相等、紧纯 Q 与根三角接触；137.10—137.11：条件字典与完整物理合同。"
[Q139VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.1—103.2：完整原菜单、minimum、共同零暴露与全部真面穷尽。"
[Q139IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.2：完整球缘与点交、重复标签孤立块；116.11：椭球参数与真实丛工具；118.4：非点极限的纯标签判据；118.8：既有分类；119.10、120.2、120.8：Conn 分支法向接口；120.4—120.5、116.17—116.18：既有静态分类。"
[Q139TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.2：Conn 到 Inj、P=P0 及四维法向的原组合；131.2—131.3：原混标签极限与实心带紧投影。"
[Q139X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.1—133.7：固定根完整覆盖、原关联传播、同锥同单位分类与全部反向字典；133.10：完整物理合同。"
[Q139SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "SECTION127.10：共同来源、全部质量、全有限联合、事件仪器、未来切口及时间合同，连同其全部传递引用。"
[Q139AT]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology：印刷页172 Theorem 2B.3、Corollary 2B.4；209—210相对 cup 乘积；240—241 cap 自然性；241 Theorem 3.30；244—248紧支撑、开嵌入延拓与 Theorem 3.35；250 Proposition 3.38、Corollary 3.39；441—444 Corollary 4D.9、Theorem 4D.10及 Euler 平方公式。"
[Q139VB]: https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf "Allen Hatcher, Vector Bundles and K-Theory：§1.2 Proposition 1.14、印刷页26—27的实二平面丛分类；§3.2页88、91—93的 Thom／Euler 类、Proposition 3.13及 Hopf 丛 Thom 空间；页105 Proposition 3.22；页112 Thom Spaces。"

## 追加锚（本行以下为增补区）

## 140. 一把零尺的中点相容与单个正交三角的传播

**定义 140.1（完整原域与单尺中点相容）。** 保留135.1的同一非零有限维实空间 $V$、闭尖生成凸锥 $C$、严格正原单位 $u$，整个 $K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$ 和整个 $\mathcal E=[0,u]_{C^*}$。仍以全部原确认效应定义 $T_p$ 和完整 $D_p$，并假定 EB3。记

$$
\begin{gathered}
\mathcal A_a=\{e\in\mathcal E:e(a)=1,\ e|_{D_a}=0\},\qquad
S(D_a)=P\cap D_a,\qquad \bar x^{\,a}=2c_a-x\quad(x\in S(D_a)),\\
p\perp q\quad\Longleftrightarrow\quad T_p(q)=0.
\end{gathered}
\tag{XI140.1}
$$

原面接口 [VII103.2、IX120.1][XI140IX] 给 $\mathcal A_a\ne\varnothing$，每个 $e\in\mathcal A_a$ 的整个零面恰为 $D_a$；球缘恰为原纯点，故 $\bar x^{\,a}$ 也是原纯点。补效应使 $\perp$ 对称。只以三条这样的真实原边定义正交三角，不预付共同三结果仪器。

本章考察如下单尺中点相容条件：

$$
\mathsf{ZC}:\quad
\forall a\in P\ \exists e_a\in\mathcal A_a\ \exists\kappa_a\in\mathbb R\ \forall x\in S(D_a):\quad
e_a(c_x)+e_a(c_{\bar x^{\,a}})=\kappa_a.
\tag{XI140.2}
$$

同一个球心 $c_a=(x+\bar x^{\,a})/2$ 有全部对径分解。将两个纯端点各换成它自己的完整排除球球心后，(XI140.2)只要求一把在原球上恒零的确认尺读到的平均值与直径方向无关。该尺在整原 $K$ 上合法，量词只要求存在一把；不要求其唯一，也不要求球心替换为实际操作。

138.1的 $\mathsf{BC}$ 蕴含更强的向量关系

$$
c_x+c_{\bar x^{\,a}}=c_y+c_{\bar y^{\,a}}
\quad(x,y\in S(D_a)),
\tag{XI140.3}
$$

因为两份对径混合的原态都等于 $c_a$。再施加任意 $e_a\in\mathcal A_a$ 就得到 $\mathsf{ZC}$。这里没有反向宣称 $\mathsf{ZC}$ 单独给出 $\mathsf{BC}$；(XI140.3)是 X128中心关系空间被向量球心赋值消灭，(XI140.2)只取该球自身的一条原效应读数，亦不同于 X128.13对全部外部纯比较行的要求。[X128][XI140X]

令 $\mathcal T$ 为全部真实正交三角顶点。$\mathsf{Seed}$ 指 $\mathcal T\ne\varnothing$；$\mathsf{Conn}$ 指原图 $(P,\perp)$ 的任意两点可由有限条原边连接，允许起终点相同时的零长路。它不是 $P$ 的拓扑连通性。

**定理 140.2（单尺中点相容的局部饱和桥）。** 在完整 EB3 域，固定 $a\in P$、$e_a\in\mathcal A_a$。不加 $\mathsf{ZC}$，135.2已有

$$
e_a(c_x)\ge\frac12\qquad(x\in S(D_a)).
\tag{XI140.4}
$$

若该尺满足(XI140.2)，则 $\kappa_a\ge1$，并且

$$
a\in\mathcal T\quad\Longleftrightarrow\quad\kappa_a=1.
\tag{XI140.5}
$$

在这些等价条件下，对整颗原球的每个球缘点 $x$ 都有

$$
2c_x=a+\bar x^{\,a},\qquad
x\perp\bar x^{\,a},\qquad
a,x,\bar x^{\,a}\text{ 构成原正交三角},\qquad
x+2c_x=a+2c_a.
\tag{XI140.6}
$$

证明。任取 $x\in S(D_a)$。原零关系对称给 $a\in D_x$；因 $a$ 原纯，它在该完整球的球缘。于是对径反射

$$
y=2c_x-a
\tag{XI140.7}
$$

也是 $D_x$ 的原纯球缘点，特别是同一个 $K$ 中的态。原效应非负性给 $0\le e_a(y)=2e_a(c_x)-1$，证明(XI140.4)。对 $\bar x^{\,a}$ 同样成立，故 $\kappa_a\ge1$。

设 $a,q,r$ 为一个真实正交三角。在完整球 $D_a$ 内，原全效应对 $q,r$ 读到一、零。非恒定仿射函数在欧氏闭球上取完整振幅一的两个端点必互为对径，故 $q+r=2c_a$。在 $D_q,D_r$ 内应用同一原几何，得到

$$
2c_q=a+r,\qquad 2c_r=a+q,\qquad c_q+c_r=a+c_a.
\tag{XI140.8}
$$

这只使用三条分别真实的边；同球一零端点必对径的论证正是 IX120.4及既有原正交球心恒等式的中间步骤。对(XI140.8)施加 $e_a$，并用 $q,r$ 是 $D_a$ 的对径，得到 $\kappa_a=e_a(a+c_a)=1$。

反之设 $\kappa_a=1$。对任意对径 $x,\bar x^{\,a}$，两个(XI140.4)之和恰为一，故各项都等于 $1/2$。(XI140.7)于是满足 $e_a(y)=0$，而该尺的整个零面恰为 $D_a$，所以 $y\in D_a$。又 $y\in D_x$，故 $x\perp y$。在同一个完整球 $D_a$ 中，这对原一零端点只能是对径，故 $y=\bar x^{\,a}$。代回(XI140.7)即得(XI140.6)的中心公式；三条原边和末个向量等式随之成立。因球缘非空，$a\in\mathcal T$。证毕。

该桥既不需要 $q\mapsto c_q$ 的球内仿射延拓，也不需要138.2的秩二分、原标签单射、纯集紧、数值比较互易 PR 或预先的矩阵表示。低界(XI140.4)来自原全效应对真实反射态的非负性，不能仅凭“读数与交换顺序无关”替代。

**定理 140.3（一个三角覆盖其整图分支并固定中心和）。** 在完整 EB3+$\mathsf{ZC}$ 域，$\mathcal T$ 是原零图若干完整图分支之并。对任一含三角的分支 $Q$，存在一个向量 $U_Q$，使

$$
p+2c_p=U_Q\quad(p\in Q),\qquad
c_p=\frac{U_Q-p}{2}.
\tag{XI140.9}
$$

证明。若 $a\in\mathcal T$ 且 $a\perp x$，则 $x\in S(D_a)$。在 $a$ 处选取 $\mathsf{ZC}$ 保证的原尺，140.2给 $a,x,\bar x^{\,a}$ 是真实三角，且 $x+2c_x=a+2c_a$。因此任一三角顶点的每个邻点仍是三角顶点，且该边两端的向量和相等。沿任意有限边路归纳，就得到整个分支及同一 $U_Q$。这里不以极限替代有限可达性，也没有给不含三角的分支指定共同向量。证毕。

**定理 140.4（单尺候选的完整同原静态结论）。** 在定义140.1的全部原量词下，以下两项等价：

$$
\boxed{\mathrm{EB3}+\mathsf{ZC}+\mathsf{Conn}+\mathsf{Seed}};
\qquad
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V\text{ 实线性},\quad
\Phi(\operatorname{PSD}_3)=C,\quad u\Phi=\operatorname{Tr}.
\tag{XI140.10}
$$

在左项下，$U=p+2c_p$ 与全部原纯标签无关，球心替换保持全部有限原纯混合等式，即 $\mathsf{MC}$。特别地，$\mathrm{EB3}+\mathsf{BC}+\mathsf{Conn}+\mathsf{Seed}$ 也给同一结论。

证明。由 $\mathsf{Seed}$ 选一个三角顶点，再由 $\mathsf{Conn}$ 及140.3把(XI140.9)推广到整个 $P$，得到共同 $U$。对任意有限纯混合 $x=\sum_i\lambda_i p_i$，允许零权和重复端点，

$$
\sum_i\lambda_i c_{p_i}=\frac{U-x}{2},\qquad
\lambda_i\ge0,\quad\sum_i\lambda_i=1.
\tag{XI140.11}
$$

因此该值只由同一原态 $x$ 决定，正是135.1的 $\mathsf{MC}$。此时直接消费既有135.5，取得同原锥同原单位的 $\Phi$；140.2—140.3是新增局部到整体的桥，分类本身不重新证明。$\mathsf{BC}$ 的条件结论由140.1的蕴含即得。

反向在整个标准复三能级域计算，再通过同一 $\Phi$ 运输。任意原纯点为 $p=vv^*$，$\|v\|=1$，其整个 $D_p$ 是 $v^\perp$ 上全部迹一正矩阵，故为完整三球且 $c_p=(I_3-p)/2$。取原效应 $e_a(\rho)=\operatorname{Tr}(a\rho)$；它满足 $e_a(a)=1$、整个零面为 $D_a$。对任意 $x\in S(D_a)$，$\operatorname{Tr}(ax)=0$，所以 $e_a(c_x)=1/2$，$\mathsf{ZC}$ 成立且 $\kappa_a=1$。正交标准基的三个秩一投影给 $\mathsf{Seed}$。任意两个不同纯射线若不正交，在复三维中其二维张成空间的正交补含一条纯射线，给连接二者的两条真实零边；正交时已有一条边，相同时取零长路。这覆盖全部 $P$，给 $\mathsf{Conn}$。证毕。

**条件应用 140.5（几何、静态公理与剩余接口）。** 在140.4的等价条件下，完整静态字典直接复用135.6：$\dim_{\mathbb R}V=9$，整个归一态体仿射维数八；全部纯态为 $\mathbb{CP}^2$，每张完整排除球的球缘为 $\mathbb{CP}^1\cong S^2$。同一个 $\Phi$ 给全部效应 $f_M(\Phi\rho)=\operatorname{Tr}(M\rho)$、$0\preceq M\preceq I_3$，并给所有原混态上的最低确认 $T_{p_v}(\Phi\rho)=v^*\rho v$，故纯读数为 $|v^*w|^2$。三元正交完成、正交谱分解及全部有限数学 POVM 都在135.6的原量词下随同运输。

证明。140.4精确取得135.5的同锥同单位前件，故135.6逐项适用。其球心几何为 $U=\Phi(I_3)$、总体中心 $U/3$，球心替换在整个 $K$ 上为 $x\mapsto(U-x)/2$；把它相对于 $U/3$ 写出，恰是反向缩小一半。这些都是同一已取得表示的后果，不倒用为140.2的局部前件。证毕。

条件(XI140.2)的检验范围少于138.1的全部二元混合等式，但本章另明确支付有限边路连接和一个真实三角；它不证明独立假设数量减少、最弱性或严格逻辑弱化。尚未证明 EB3+$\mathsf{ZC}$ 或 EB3+$\mathsf{BC}$ 自动供应 $\mathsf{Conn}$、$\mathsf{Seed}$ 或全域 $\mathsf{MC}$，也未给这些自动性的同原反模型。140.2准确说明：若单尺相容成立而一个标签尚不在三角中，该处相容常数必严格大于一；非负性只给下界，不能强迫达到一。

单体静态字典不供应实际球心替换、可调用制备或仪器。全部实际事件与条件更新、零质量分支、任意有限复合的整个联合态锥及纠缠、全旁观 CP、共同预算与接线、连续动力学、原物理钟、Hamiltonian、能量标定和数值 $\hbar$，仍保留135.7及其所引原操作合同的全部独立前件。

**约定 140.6（推导归属与关系图景）。** 本章新增承重关系是：用原球自己的一个全域零尺，把所有邻球反射态的非负性与一个三角的等号相拼，迫使整球的每条直径饱和；再沿原有限零边路传播共同 $p+2c_p$，取得原全混合相容。原面接口、同球一零端点必对径、全 $\mathsf{MC}$ 静态分类及量子字典均复用既有来源，不计为新的分类结果。X128的中心关系在标准 Hilbert 域上的 Gleason闭包结论不被反向用于本章未知原域；140.2也不从标量读数等式直接推断向量相等，而是先把真实反射态放回整原零面，再以同球对径唯一性取得向量式。

与现成分类的对应须保留其额外前件：Barnum—Müller—Ududec的 Theorem 16要求 projectivity、对称跃迁概率及保纯滤子，不能在本章局部阶段提前使用；本章只在取得全 $\mathsf{MC}$ 后接135.5的既有分类链。[BMU][XI140BMU] 本章采用仓内综合推导归属，不声明全球新颖性或历史优先权。

白话上，把每个纯态背后的完整排除面看成一颗实心三球。每颗球只拿一把在整球上读零、在自己标签上读一的原尺：无论选哪条直径，将两端各换成它自己排除球的球心后，这把尺读到的平均值都相同。若已有三个两两完全排除的纯态，它们先把这个平均值锁到边界；原读数不能为负，就迫使相邻整球上的每条直径都闭成同样的三角。若原零图有限边路连通，一个三角便传到全部纯态，所有球心最终都朝同一总体中心反向缩小一半，既有分类随之给同一完整复三能级量子态体。这里仍明确需要连接和那个真实三角；两两比较的端点交换本身没有供应它们。

[XI140IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX120.1全部原量词与原面接口；120.4同球三角与宽度；120.5同原静态分类。VII103.2的原暴露面接口由该处明确引用。"
[XI140X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X128.1—128.3全部原球中心关系空间、标准模型有界闭包及一般原域仍缺的接口。"
[XI140BMU]: https://arxiv.org/html/1403.4147v4#Thmtheorem16 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory, Theorem 16；不是裸EB3或单尺中点相容的分类定理。"

## 追加锚（本行以下为增补区）

## 141. 完整载体不塌缩、原对偶开放边界与整个实空间九维

### 141.1 完整原域与准确的条件接口

**定义 141.1（原对象、根与维数约定）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，及在 $C\setminus\{0\}$ 上严格正的原单位 $u\in V^*$。始终使用

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\qquad C^*=\{h\in V^*:h(C)\subseteq\mathbb R_+\},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\\
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p,\\
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p.
\end{gathered}
\tag{XI141.1}
$$

这里 $x$ 遍历每个原混态。$K$ 紧且张成 $V$；完整 $\mathcal E$ 紧，$\mathcal F_p$ 是含 $u$ 的非空紧集，故每个 minimum 达到。纯关系 $p\perp q\Longleftrightarrow q\in S_p$ 对称且反自反，见[VII103.1—103.2][Q141VII]。完整 EB3 要求每个原 $p\in P$ 的整个 $D_p$ 都是非退化仿射闭三球。另保留原 $\mathsf{Conn}$：任意两个原纯点间有有限原零边路，长度可依端点改变。

在全部目标之前固定同一个原纯点 $o$，记

$$
Q(r)=\bigcup_{s\in S_r}S_s,\qquad Q=Q(o),\qquad
\mathsf G(o):\ \exists U\subset V\text{ 开},\ o\in U,\ U\cap P\subseteq Q.
\tag{XI141.2}
$$

本章在这个完整 EB3+$\mathsf{Conn}$+$\mathsf G(o)$ 域上，条件性地消费[XI137.2—137.3、XI139.1—139.2][Q141XI]的以下准确接口；这些支持结论不在本章重证。

* 每个非空原真面是纯单点或某个完整 $D_a$，且 $S_a=\partial_{\rm rel}D_a$、$D_a=\operatorname{conv}S_a$。
* $\mathcal A_p:=\{e\in\mathcal F_p:e|_{D_p}=0\}$ 为单点 $\{e_p\}$，$g_p=u-e_p$，$\dim_{\mathbb R}L_p=4$，且 $\{x\in K:g_p(x)=0\}=\{p\}$。
* 有一个环境开集 $U_0\ni o$，满足 $U_0\cap D_o=\varnothing$，并且 $Q(q)=Q$ 对每个 $q\in U_0\cap P$ 成立。
* $Q\subset P$ 在原 $V$ 中紧，且以原子空间拓扑为无边界四维拓扑流形。
* 对原标签集 $\Lambda=\{a\in P:S_a\subseteq Q\}$，$\Lambda$ 在原 $V$ 中紧，整个球映射 $a\mapsto D_a$ 在整个 $\Lambda$ 上按环境 Hausdorff 距离连续；每个 $q\in U_0\cap P$ 都满足整个 $S_q\subseteq\Lambda$。

第一项的原来源是 VII103.2 与 IX116.1。第二项不是从一个根的法向向别的根外推：[IX116.2][Q141IX]的孤立重复块结合 Conn 排除重复标签；IX119.10 在 EB3+Inj 下给 $\dim L_p=\dim_{\rm aff}\mathcal A_p+4$、沿每条原边的冗余不变及至少一个零冗余标签；沿原有限路径传播才取得全部 $P=P_0$。再用 IX120.2、120.8，得到上述法向及唯一零点性质。这正是[THREE_COPY VIII130.2][Q141TC]与 XI137.2 的复用组合。它既未把 $\mathcal F_p$ 缩为单点，也未取得 least 或正限制逆。

本证明实际需要四维法向的根集合可进一步精确为：上界只用所得唯一零点像上的 $\dim L_p\le4$，下界只用 $p\in Q$ 上的 $\dim L_p\ge4$，另用根 $o$ 的 $g_o$。下文的像包含于 $Q$，所以只在 $Q$ 上消费四维法向；没有在 $\Lambda\setminus Q$ 上使用它，也没有对另一个根重新假设 $\mathsf G$。最后两项准确取自139.2第1、2项及139.8、式(XI139.24)；仅需其中的四维流形性、紧性、整球连续性与近根捕获，不消费 Euler 数、定向、交形式或 $\Lambda$ 上的两标签共同邻点。

置 $n=\dim_{\mathbb R}V$、$d=n-1$、$A=\{u=1\}=\operatorname{aff}K$、$L=\ker u$。只为距离和拓扑选辅助欧氏内积。$\dim$ 表示覆盖维数，$\dim_H$ 表示这个原子空间度量的 Hausdorff 维数；凸集的仿射维数与锥的张成维数另行注明。选任意原 $z\in\operatorname{ri}K$，定义整个原对偶基及零面

$$
H_z=\{h\in V^*:h(z)=1\},\qquad K^*=C^*\cap H_z,\qquad
Z(h)=\{x\in K:h(x)=0\},\qquad F_p^*=N_p\cap K^*.
\tag{XI141.3}
$$

$K^*$ 的边界和开集均相对于整个 $H_z$，不相对于某个 $L_p$ 或选出的法向片。

### 141.2 单一定理及证明

**定理 141.2（由实际原对偶开区域确定整个 $V$ 的维数）。** 在定义141.1的完整原域及所列条件接口下，存在

$$
h_o=\frac{g_o}{g_o(z)}\in\partial_{H_z}K^*,\qquad
h_o\in O\subseteq\partial_{H_z}K^*\text{ 相对开},
\tag{XI141.4}
$$

使每个 $h\in O$ 的整个原零面恰为一个 $p\in U_0\cap P\subseteq Q$。唯一零点映射 $\pi:O\to Q$ 连续，且每条纤维包含于一个三维仿射平面。在 $O$ 中有维数 $n-2$ 的紧坐标闭球，其到自身像的限制为闭映射。由 Hurewicz 的紧闭映射维数定理及凸函数高阶奇异集的原始图覆盖定理，得到

$$
\boxed{\dim_{\mathbb R}V=9.}
\tag{XI141.5}
$$

证明分成以下六步，始终不更换原 $V,C,u,K,P,\mathcal E$。

**一、完整载体不能缩入小根邻域。** 对 $q\in U_0\cap P$，任选 $s\in S_q$；EB3 保证非空。零对称给 $q\in S_s$，故 $q\in Q(q)=Q$，从而 $U_0\cap P\subseteq Q$。又 $S_o\subseteq\Lambda$，因为 $a\in S_o$ 时 $S_a\subseteq Q(o)$，所以 $\Lambda$ 非空。

对任意非空紧集 $F,G$，三角不等式给

$$
|\operatorname{diam}F-\operatorname{diam}G|\le2d_H(F,G).
$$

整球连续性和紧 $\Lambda$ 因而给出实际正数

$$
\delta:=\min_{a\in\Lambda}\operatorname{diam}D_a>0.
\tag{XI141.6}
$$

严格正性使用每个完整球均非退化；这里没有声称控制 $\Lambda$ 外的球。取以 $o$ 为心的环境开球 $W$，使 $\overline W\subset U_0$ 且 $\operatorname{diam}W<\delta$。若某个原完整球 $D_a\subset W$，在其完整球缘取 $q\in S_a$。则 $q\in U_0\cap P$，而原零对称给

$$
q\in S_a\quad\Longrightarrow\quad a\in S_q\subseteq\Lambda.
\tag{XI141.7}
$$

于是 $\delta\le\operatorname{diam}D_a\le\operatorname{diam}W<\delta$，矛盾。因此没有任何原完整球包含于 $W$。捕获的是球标签 $a$；没有使用 $S_a\subseteq Q\Rightarrow a\in Q$ 这种未有接口。

**二、在整个原对偶边界建立开区域。** $C$ 生成 $V$ 使 $K$ 在 $A$ 中满仿射维，且 $z\in\operatorname{ri}K$ 蕴含 $z\in\operatorname{int}C$：近 $z$ 的向量仍有正质量，其除以质量后的归一向量仍在 $K$ 的相对内邻域中。故某个 $\varepsilon>0$ 满足 $z\pm\varepsilon v\in C$ 对所有单位 $v\in V$ 成立。对 $h\in K^*$，

$$
0\le h(z\pm\varepsilon v)=1\pm\varepsilon h(v),
$$

给出对偶范数有界；$K^*$ 闭，故紧。原严格正 $u$ 属于 $\operatorname{int}C^*$，且 $u(z)=1$，所以 $K^*$ 是 $H_z$ 中有非空相对内部的 $n-1$ 维凸体。这里 $u\in\operatorname{int}C^*$ 也可直接由 $u$ 在 $C$ 与单位球的紧交上的正最小值取得。

每个非零 $h\in C^*$ 在 $z$ 严格正。归一截面与正径向变量给 $C^*\setminus\{0\}$ 的乘积参数，故 $\partial_{H_z}K^*=H_z\cap\partial C^*$。对 $h\in K^*$，还有准确等价

$$
h\in\partial_{H_z}K^*\quad\Longleftrightarrow\quad
\min_{x\in K}h(x)=0.
\tag{XI141.8}
$$

若最小值正，全 $K$ 的有界性保证小对偶扰动仍在 $C^*$；若有零点，该原非零锥元给一个支持超平面，排除 $C^*$ 内部性。$h(z)=1$ 又排除零面等于 $K$。所以每个实际边界点都有非空真原零面。

原 $g_o$ 仅在 $o$ 为零，且 $g_o(z)>0$；故(XI141.4)中的 $h_o$ 确属边界。因 $D_o\cap U_0=\varnothing$，$K\setminus W$ 非空。其紧性和 $h_o$ 的唯一零点给

$$
m:=\min_{x\in K\setminus W}h_o(x)>0,\qquad
O:=\{h\in\partial_{H_z}K^*:\|h-h_o\|_K<m/2\},\qquad
\|b\|_K=\max_{x\in K}|b(x)|.
\tag{XI141.9}
$$

$K$ 张成 $V$，故 $\|\cdot\|_K$ 是有限维对偶空间上的范数；$O$ 是包含 $h_o$ 的实际相对开集。对每个 $h\in O$，在整个 $K\setminus W$ 上 $h>m/2$，因此 $\varnothing\ne Z(h)\subset W$。该零面是真原面；面分类只允许纯单点或完整球。第一步已排除完整球，遂有

$$
Z(h)=\{\pi(h)\},\qquad \pi(h)\in W\cap P\subseteq Q.
\tag{XI141.10}
$$

这是在整个原对偶基边界上的开放结论，并非先选一个较小的法向集合再赋予它相对开性。

**三、唯一零点映射与纤维。** 若 $h_j\to h\in O$，在紧 $K$ 中取 $p_j=\pi(h_j)$ 的任意收敛子列 $p_{j_\ell}\to p$。评价连续使 $h(p)=\lim_\ell h_{j_\ell}(p_{j_\ell})=0$，故 $p=\pi(h)$。每个子列都有这个唯一聚点，所以 $p_j\to\pi(h)$。$\pi:O\to Q$ 连续，所用拓扑正是原子空间拓扑。

对 $p\in\pi(O)$ 有完整集合等式

$$
\pi^{-1}(p)=O\cap F_p^*\subseteq\{h\in L_p:h(z)=1\}.
\tag{XI141.11}
$$

评价 $z$ 在 $L_p$ 上非零，因为这条纤维中已有 $h(z)=1$ 的元素。$\dim_{\mathbb R}L_p=4$，所以右端是三维仿射平面。不需要 $p\mapsto L_p$ 或 $p\mapsto N_p$ 连续。

**四、紧闭映射给上界。** 从 $K^*$ 的相对内点径向投影，其整个边界同胚于 $S^{n-2}$，故非空开集 $O$ 是 $n-2$ 维拓扑流形。三维真面保证 $d\ge4$。在 $O$ 的一个坐标图内取一个有正半径的紧坐标闭球 $A_0$，于是

$$
\dim A_0=n-2,\qquad Y=\pi(A_0)\subseteq Q.
$$

$Y$ 为紧度量空间；$f=\pi|_{A_0}:A_0\to Y$ 连续、满射，并且是闭映射，因为紧集的像在 Hausdorff 空间中闭。覆盖维数的紧子集单调性及四维流形性给 $\dim Y\le4$。每条 $f^{-1}(p)$ 是(XI141.11)的三维仿射平面中的紧子集，故 $\dim f^{-1}(p)\le3$。

现在才用 [Hurewicz，Theorem III，印刷页163—164][Q141H]：紧度量空间的连续满射满足

$$
\dim A_0\le\dim Y+\sup_{p\in Y}\dim f^{-1}(p).
$$

原文页164也直接以这个不等式组织证明；页163脚注12说明紧源保证所需闭性。若像维数已不小于源，所用不等式本来即平凡。全部应用条件均已在这个紧限制上支付，故

$$
n-2\le4+3=7,\qquad n\le9.
\tag{XI141.12}
$$

这没有对原非紧开区域直接套闭映射定理，也没有假设 $\pi$ 开放、局部平凡或具有局部乘积。

**五、将原法向送入同一原状态体的凸次微分。** 在原仿射空间 $A\cong\mathbb R^d$ 中定义外法锥

$$
\widehat N_K(p)=\{v\in L:\langle v,x-p\rangle\le0\ (x\in K)\}.
\tag{XI141.13}
$$

借助 $L$ 上的欧氏 Riesz 识别，$h\mapsto-h|_L$ 将 $N_p$ 送入该外法锥。它在 $L_p$ 上单射：若 $h|_L=0$，则 $h=t u$；而 $L_p$ 中全部泛函都在 $p$ 为零，故 $t=0$。因此对每个 $p\in Q$，$\widehat N_K(p)$ 的线性张成维数至少四。

令 $a(x)=\operatorname{dist}(x,K)$，定义于整个 $A$。它有限值且 $1$-Lipschitz；凸性由两个最近点的凸组合与三角不等式直接得到。对 $p\in K$，

$$
\partial a(p)=\widehat N_K(p)\cap\overline{\mathbb B}_L.
\tag{XI141.14}
$$

确实，次梯度在全部 $K$ 上的零值给法向不等式，$1$-Lipschitz 性给其范数不超过一。反向，若 $v$ 在右端，对任意 $y\in A$ 取 $k\in K$ 为最近点，则

$$
\langle v,y-p\rangle
=\langle v,y-k\rangle+\langle v,k-p\rangle
\le\|y-k\|=a(y).
$$

这正是全域次梯度不等式。右端包含零，且锥中每个方向均能缩入单位球，故其仿射张成维数等于原外法锥的张成维数。于是

$$
Q\subseteq\Sigma_4(a),\qquad
\Sigma_k(a)=\{x\in A:\dim_{\rm aff}\partial a(x)\ge k\}.
\tag{XI141.15}
$$

这里的次微分定义在整个原 $A$ 上；没有把函数只定义在 $Q$ 或某个面上。

**六、原始奇异集图覆盖给独立下界。** 首先 $d\ge4$ 已由原法向单射得到。若 $d=4$，$Q$ 的任一四维坐标开片包含映入 $A\cong\mathbb R^4$ 的连续单射；[Brouwer 区域不变性，Hatcher Theorem 2B.3，印刷页172][Q141AT]使其像在 $A$ 中开。但 $Q\subset P\subset\partial_AK$，凸体边界在 $A$ 中无内部，矛盾。所以 $d>4$，以下 $k=4$ 满足原奇异集定理的 $0<k<d$。

[Alberti，Theorem 1、Definition 1.1][Q141A]给有限值凸函数的 $\Sigma_k$ 的可数可求长性与 $\dim_H\Sigma_k\le d-k$。这里还使用其 Lemma 2.7、Theorem 2.10 及 Theorem 1 证明中更直接的**覆盖整个奇异集**的图结论；不把“除零测集外”误读为全覆盖。现将准确应用写出，以避开任何度量维数比较费用。

给 $A$ 选原点后令 $b(x)=a(x)+\|x\|^2$。这是整个 $\mathbb R^d$ 上的有限值凸函数，且 $b\ge\|x\|^2$；次梯度不等式给 $\partial b(x)\supseteq\partial a(x)+2x$，故 $Q\subseteq\Sigma_4(b)$。对每个四维坐标子空间 $E$，记 $\operatorname{pr}_E$ 为正交投影。维数至少四的凸集必在至少一个这样的 $E$ 上具有四维投影：取四个独立差向量，选一个非零四阶坐标子式即可。非空内部的投影又包含一个中心为有理坐标、半径为 $2/m$ 的开球，其中 $m\ge1$。因此整个 $Q$ 被以下可数集合覆盖：

$$
\left\{x:\operatorname{pr}_E(\partial b(x))
\supset B_E(\eta,2/m)\right\},\qquad
E\text{ 为四维坐标子空间},\quad\eta\in\mathbb Q^4,\quad m\in\mathbb N_{>0}.
\tag{XI141.16}
$$

在分解 $A=E^\perp\oplus E$ 中，$b(t,y)\ge\|y\|^2$。故 Alberti Lemma 2.7 逐个适用：每个(XI141.16)集合包含于某个局部 Lipschitz 函数 $E^\perp\to E$ 的整个图 $\Gamma_j$。这里函数定义于全部 $E^\perp$，正是该源引理的定义域；其连续性使 $\Gamma_j$ 在 $A$ 中闭。由此得到

$$
Q\subseteq\bigcup_{j\ge1}\Gamma_j,\qquad
\Gamma_j\text{ 是 }\mathbb R^{d-4}\to\mathbb R^4\text{ 的连续函数图，经正交坐标运输}.
\tag{XI141.17}
$$

闭集 $Q\cap\Gamma_j$ 覆盖紧度量空间 $Q$，故某个交包含非空相对开集 $U\subset Q$。所用的紧 Baire 事实可直接说明：若每个交都无内部，从 $B_0=Q$ 开始，递归选非空相对闭球 $B_j$，半径不超过 $2^{-j}$，使 $B_j\subset\operatorname{int}_Q B_{j-1}$ 并避开第 $j$ 个闭集；闭集无内部保证每一步可选，紧性给公共点，违反覆盖。取四维坐标开片 $U'\subset U$。图到 $E^\perp$ 的投影在 $U'$ 上连续且单射，因而给从 $\mathbb R^4$ 非空开集到 $\mathbb R^{d-4}$ 的连续单射。若 $d-4<4$，再将后者线性嵌入 $\mathbb R^4$ 的真子空间，区域不变性会使该真子空间包含一个非空四维开集，矛盾。所以

$$
4\le d-4=n-5,\qquad n\ge9.
\tag{XI141.18}
$$

这里 Q 的四维性仅按原子空间拓扑使用；没有宣称它在辅助度量下有恰好四维的 Hausdorff 维数，也没有将拓扑维数当作 Hausdorff 维数的上界。下界来自原始完整图覆盖、紧性和区域不变性，与第四步的对偶闭映射上界独立。结合(XI141.12)与(XI141.18)，得到(XI141.5)。证毕。

### 141.3 归属与所得范围

本章的实质连接是(XI141.6)—(XI141.10)：以近根零关系捕获完整球的原标签，在紧 $\Lambda$ 上取得统一正直径，从而把原 $g_o$ 的唯一零点稳定成**整个原对偶边界上的开区域**。连续唯一零点、实际仿射纤维界和紧闭映射限制随后把这个原域事实送入成熟维数定理。原面分类、Conn 的四维法向接口以及139.2的指定支持结论均为条件性复用；凸体边界的球面拓扑、覆盖维数基本性质、Hurewicz 定理、Baire 定理、Alberti 奇异集图覆盖与 Brouwer 区域不变性均属成熟数学，不另计新定理。

特别地，Hurewicz 原文只在紧坐标闭球上使用。Alberti 的函数必须有限值并定义于整个欧氏空间；本证明的 $a,b$ 均满足，Lemma 2.7 所需的二次下界也已显式供应。其 Theorem 1 的 Hausdorff 结论可另外给 $\dim_HQ\le n-5$，但本证明用全图覆盖与 Baire 直接取得下界。没有引入光滑性、半代数性、可定义性、局部平坦、连续移动法锥或法丛。

所得九维是整个原 $V$ 的维数：实际原对偶基的边界为七维，原基 $K$ 为八维。若原 $V$ 超过九维，$O$ 的紧坐标球将超过七维，而到四维紧像的闭映射纤维仍至多三维，与 Hurewicz 矛盾。完整球不能靠向根处缩小来逃避这一矛盾，因为其标签必进入已控制的 $\Lambda$。

本章仍未取得 $\operatorname{conv}Q=K$、$P=Q$、$\bigcup_{a\in\Lambda}D_a=\partial_AK$、全局 $\mathsf R_1$、$\mathsf{MC}$、全 $P$ 紧性、原锥的同质性、自对偶、共同内积、正仿射中心图、正限制逆、least、全局谱性或 Jordan 分类。也未决定无根三角支的完整相容性。维数相同不迫使两套凸混合结构相同；四维纯子集的拓扑也没有支付完整原锥表示。以下两条静态候选继续保留其完整前件和既有分类依赖。

### 141.4 两条完整静态候选、同原字典与反向

本节只复用[X133.1、133.6—133.7][Q141X]及[XI135.1—135.6、136.4][Q141XI]。$\mathsf R_1$ 的量词准确为

$$
\exists r\in P\ \forall q\in P:\quad
r\perp q\ \lor\ \exists s\in P:\ r\perp s\ \land\ q\perp s.
\tag{XI141.19}
$$

根先于全部目标选定，包括 $q=r$；这项全目标覆盖未由定理141.2取得。$\mathsf{MC}$ 则要求任意正整数 $m,n$、全部原纯标签及非负权重满足

$$
\begin{gathered}
\sum_{i=1}^m\lambda_i=\sum_{j=1}^n\mu_j=1,\qquad
\sum_i\lambda_i p_i=\sum_j\mu_j q_j\\
\Longrightarrow\qquad
\sum_i\lambda_i c_{p_i}=\sum_j\mu_j c_{q_j},
\end{gathered}
\tag{XI141.20}
$$

其中 $c_p$ 是整个原 $D_p$ 的唯一仿射球心；零权、重复标签和同一原态的全部有限纯配方都在量词内。

既有两条等价分别为完整 EB3+$\mathsf R_1$ 与完整 EB3+$\mathsf{MC}$ 各自等价于存在同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI141.21}
$$

R1 路线仍经 X133.6 消费 IX120.4—120.5、IX116.17—116.18；MC 路线先取得实际正保质量可逆球心图，再由135.5消费 IX118.8，包括其既有分类依赖。136.4只缩短纯紧性与非塌缩入口。定理141.2没有替代这些费用。仅在另行满足任一完整候选后，令 $P_v=vv^*$、$v^*v=1$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$、$U=\Phi(I_3)$，同一个 $\Phi$ 才运输以下完整字典。

| 原对象 | 同一锥和同一单位的对应 |
| --- | --- |
| 全载体、质量与混合 | 全部 $X\succeq0$，包括零和任意非负质量，对应整个 $C$；$u(\Phi X)=\operatorname{Tr}X$。整个 $K$ 对应全部迹一密度矩阵，保持全部凸混合。原 $u\in V^*$ 与 Jordan 单位 $U\in V$ 不混型。 |
| 全纯域与复射线 | 全部原 $P=\{p_v\}\cong\mathbb{CP}^2$；任意非零复向量 $w$ 对应 $\Phi(ww^*/(w^*w))$，非零复倍数给同一标签。 |
| 全效应与全部混输入 | $f_M(\Phi X)=\operatorname{Tr}(MX)$ 恰遍历全部 $0\preceq M\preceq I_3$，保持零、单位、补与序。任意实线性读数由任意 Hermitian $M$ 表示。 |
| 完整确认、least、minimum | $\mathcal F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\}$；least 为 $f_{P_v}$。对每个原混态 $\Phi\rho$，已达 $T_{p_v}(\Phi\rho)=\operatorname{Tr}(P_v\rho)=v^*\rho v$。 |
| 纯比较与完整排除 | $T_{p_v}(p_w)=|v^*w|^2$；未归一时除以 $(v^*v)(w^*w)$。整个 $D_{p_v}$ 是 $\rho\succeq0,\operatorname{Tr}\rho=1,\rho v=0$ 的原像，含全部混态，是完整 qubit 三球，纯球缘为 $\mathbb{CP}^1\cong S^2$。 |
| 中心与完整框架 | $c_{p_v}=\Phi(Q_v/2)=(U-p_v)/2$，总体中心为 $U/3$。原零三角是三个和为 $I_3$ 的正交秩一投影；三个 least 效应和为 $u$，每条原零边有唯一第三点，数学完美区别容量为三。 |
| 全部有限数学测量 | 任意有限结果数的 $f_j\in C^*,\sum_jf_j=u$ 恰对应全部 $M_j\succeq0,\sum_jM_j=I_3$ 的 POVM；概率在每个原输入上为 $\operatorname{Tr}(M_j\rho)$，允许零效应。 |
| 谱与实可观测量 | 每个原态有三项正交谱分解，允许零权和重谱；全部 Hermitian 可观测量有实谱及谱效应。重谱不指定唯一逐本征射线。 |
| Jordan、自对偶与球心图 | $\langle\Phi X,\Phi Y\rangle_\Phi=\operatorname{Tr}(XY)$ 使 $C$ 自对偶；$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$，单位为 $U$；$R(x)=(u(x)U-x)/2$ 定义于全部 $V$。 |

完整确认菜单一般不是单点。若 $0\preceq M\preceq I_3$ 且 $v^*Mv=1$，正半定性给 $(I_3-M)v=0$，Hermitian 性消去交叉块，恰得到表中的全部 $B$。对每个 $\rho\succeq0$，$\operatorname{Tr}(B\rho)\ge0$；同一菜单中的 $B=0$ 达到下界，既给 least，也给每个混输入上的原 minimum。正性又给 $v^*\rho v=0\Longleftrightarrow\rho v=0$，才取得整个 $v^\perp$ 上的归一正矩阵三球。

反向取满足(XI141.21)的整个标准对象。上述完整菜单计算逐标签给 EB3。对任意事先指定根 $p_v$ 和任意目标 $p_w$，包括相同标签，取单位 $z\perp\operatorname{span}_{\mathbb C}\{v,w\}$；同一个原纯点 $p_z$ 用原投影效应分别见证两条零边。因此每根都有 $Q(p_v)=P$、R1、Conn 和 $\mathsf G(p_v)$。同一 $\Phi$ 又使任意纯配方 $x=\sum_i\lambda_i p_i$ 的球心替换恒为 $(U-x)/2$，含零权与重复项，故完整 MC 成立。全谱、POVM、Jordan 与 Born 字典均沿同一个表示运输；这些反向是两条完整静态候选的既有内容。

### 141.5 原来源、所有有限复合、事件与物理时间的保留合同

完整继承[SAME_READBACK SECTION127.10][Q141SR]、[EXCLUSION X133.10][Q141X]及[THREE_COPY VIII131.8][Q141TC]的每一前件、原对象、作用域和全部量词。其传递引用 SAME_READBACK125.11、124.9、123.13，EXCLUSION VIII112.9、113.11及IX120.11，THREE_COPY VII121.12、122.14，INTRINSIC_POLAR VI定义89.7、89.8—89.10与全部两尺度式(89.13)、V88.6与87章、原生续卷VII和III的来源／全未来／动态合同，以及139.11保留的 BILATERAL VIII128.H，均保持原义。操作来源的 INTRINSIC_POLAR VI 与整球 BILATERAL VI 不混同。

同一个原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表与闭性、零／单位／补／有界倍增、重复标签和每种同中点实现，全部非负质量（含零、次归一与不等质量），过程与参考各自完整相关联合输入域，均继续承担。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集均保持原定义。操作映射 $p$、纯标签与根条件按类型区分。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、旧 support、所有合法未来与每个中间切口，以及原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption与资源合同继续保留。数学纯射线、对偶开集或静态效应不产生实际来源、接线和权限。

每个有限 $N\ge1$ 仍须另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 和完整效应区间。对每个实际二分割 $a+b=N$，保留 $C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b$、同一产品配对、严格张量单位、全部原因子置换与逆的正性、规范重括号及指定运输下不连续位置分块。

实际二份 $S_2$ 仍量化每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族和全部 $t_\ell\ge0,\sum_\ell t_\ell=1$，含零权与重复标签，要求

$$
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\qquad
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]_{C_2^*}\\f(p)=1}}f(x).
\tag{XI141.22}
$$

低二份 $q=1,2$ 的 least／谱性／正面投影及保纯到 Jordan 桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩与实维乘法的复型选择，以及同一实际两因子的产品正规形，仍是三项分别供应。非经典 $\mathsf F_{\max}$ 还需同一最大复块 $n_r=L\ge2$、同一含相位正交基上的实际三份资源

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{XI141.23}
$$

其余三份扇区为零，归一原源为 $\Delta_r/L$；不预付三份纯性或实际制备，全经典 $L=1$ 支路按原规则免此资源。单体复三能级支路 $L=3$，二、三份秩分别九、二十七；高阶整个排除集不被规定为单体 EB3。形式矩阵不支付实际锥成员资格。

对所有输入输出份数及同一原类型的实线性 $F:W_m\to W_n$，全旁观正性仍量化每个 $b\ge0$ 和任意含纠缠的同一共同输入，要求 $(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$。实际完整有限层级及共同表示已供应后，才沿原 Choi 桥识别 CP、矩形跨扇区 Kraus。TP／TNI 仍逐个量化所有 $x\in C_m$，要求 $u_n(Fx)=u_m(x)$／$u_n(Fx)\le u_m(x)$；同族分支总预算也由同一个输入承担。

同一实际事件的 CP 另需完整提升、实际探针及相容核；全部数学 CP-TNI 分支成为实际事件另需事件饱和选择。同族仪器保留共同输入预算、接线、记录、粗粒化和校准。只对严格正质量分支作条件归一，零质量分支不强定归一条件态。Lüders 更新另需同一分支的锐效应、接受态中性及输出校准。全数学 POVM、效应和为单位与实际可执行仪器各有原合同；静态正球心图也未取得全旁观 CP 或事件资格。

物理钟、实际动态来源、连续齐次可逆时间群与单位仍分别供应。另给全实时间连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，才有这项额外供应的有限维生成元；再给复块上保迹酉时间族，才使用

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\mathrm i[H,\rho]/\hbar,\qquad H=H^*.
\tag{XI141.24}
$$

量词覆盖全部原输入及全部实际时间。$H$ 的标量平移和时间重标保留原意义；恒等时间族与非平凡 Hamiltonian 族可共享全部静态对象。实际 Hamiltonian、能量识别及标定、数值 $\hbar$、时空和物理空间维数仍各自未付。九维实载体、四维 $Q$、三维排除球和零图关联步数都不指定物理空间或物理时间。

### 141.6 完整中文图景

把整个原状态集合看成一块完整凸体，每个纯标签背后都有一颗完整实心排除三球。原来的根检测量 $g_o$ 只在根纯点 $o$ 为零。由于整个状态体紧，离根一段距离的全部原态，在这张检测量上都有共同的正读数余量。因此稍微改变检测量，新零面只能落到根附近。

这里必须排除一个真实危险：新零面可能是一整颗越来越小的球，不能仅凭它靠近纯点就说它是单点。本章用的是原关联的具体捕获。假如一颗完整球进入很小的根邻域，任选它的纯球缘点 $q$，原零关系的对称性就把这颗球的标签 $a$ 放入 $S_q$；支持接口又把整个 $S_q$ 放入紧标签集 $\Lambda$。在 $\Lambda$ 上，整颗球连续变化，而且每颗球都非退化，所以它们有统一的正直径。它们不可能缩进比这个直径更小的根邻域。于是新零面只能是一个原纯点。

这真的给出了全部原检测量组成的对偶基边界上的一整块开放区域。把每张检测量送到它唯一的零点，是连续映射：检测量和零点一起取极限，零读数保留，而极限检测量仍只有一个零点。同一个零点允许的检测量，都在四维原法向张成空间中；按同一个原内态归一后，只剩三维仿射平面。另一方面，这些零点都落在紧四维流形 $Q$ 中。在开放边界里取一个紧坐标球，连续映射就成为到其紧像的闭映射。Hurewicz 定理因此把这块原对偶边界的维数压到至多七维，使整个原实空间至多九维。

反过来，$Q$ 中每个点的原四维法向，都能送到同一个完整状态体的距离函数次微分中。成熟的凸函数奇异集定理把这些点覆盖在可数张图上，每张图只需环境维数减四个坐标。紧空间的 Baire 性保证，$Q$ 的某个真正四维开片整块落在其中一张图上。若这张图的底面不到四维，投影就会把一个四维开片连续单射到更低维空间，与区域不变性矛盾。所以原基至少八维，整个原实空间至少九维。上下两边相合，得到整个 $V$ 恰为九维。

这个结论精确依赖所列支持接口，却没有把 $Q$ 以外的纯点自动消掉。它也没有确定所有混态如何凸混合，或把整个锥自动认成三能级量子锥。只有再取得一个根对全部目标的完整覆盖，或取得同一混态所有有限纯配方的球心相容，既有分类才给同一锥及单位上的全部密度态、完整非单点确认菜单、least、每个混态上的 Born minimum、全部 POVM、谱和 Jordan 字典。实际来源、读回、全部质量、所有有限复合和纠缠、三份相位资源、全旁观 CP、逐输入预算、事件仪器、记录、全部未来与切口，以及物理钟、Hamiltonian、能量与数值 $\hbar$，仍各按原合同承担。

[Q141VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.1—103.2：完整原菜单、所有混输入 minimum、共同暴露及原真面穷尽。"
[Q141IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.2：原面与孤立重复块；119.10：法向维数与沿边冗余传播；120.2、120.7—120.8：原最大值、唯一零点及限制同构；118.8、120.4—120.5、116.17—116.18：保留的既有分类依赖。"
[Q141TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.2：完整 EB3+Conn 的 Inj、P=P0、全部原四维法向；131.7—131.8：条件静态字典与全部物理合同。"
[Q141XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "135.1—135.6、136.4：完整 MC 候选与同原分类；137.1—137.3：完整原域、单根 G、原法向、近根 Q 集合相等；139.1—139.2第1、2项、139.8与式(XI139.24)：原拓扑四维 Q、紧 Lambda、整个球的 Hausdorff 连续及近根完整捕获；139.11：保留的物理合同。"
[Q141X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.1、133.6—133.7：先固定根的完整 R1、同锥同单位分类、全部静态字典与反向；133.10：完整物理合同。"
[Q141SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "SECTION127.10：同一原来源、全部质量、全有限联合、事件仪器、所有未来与切口及物理时间，连同其全部传递引用。"
[Q141H]: https://dwc.knaw.nl/DL/publications/PU00015429.pdf "W. Hurewicz, Ueber stetige Bilder von Punktmengen (Zweite Mitteilung), Proceedings of the Royal Academy of Amsterdam 30, 159—165：Theorem III，印刷页163—164；紧源与闭性的脚注12，及页164的维数不等式。"
[Q141A]: https://people.dm.unipi.it/alberti/ricerca/1989-91/convex.pdf "G. Alberti, On the structure of singular sets of convex functions, Calculus of Variations and Partial Differential Equations 2, 17—27：Theorem 1、Definitions 1.1、1.2、1.5；Lemma 2.7、Theorem 2.10及Theorem 1的证明。作者原文PDF页1、3—4、7—9；Lemma 2.7给定义于整个底面的局部Lipschitz图，证明中的可数步骤覆盖全部高阶奇异集。"
[Q141AT]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology：印刷页172 Theorem 2B.3，Brouwer区域不变性；连续单射的源与目标同为欧氏四维时适用。"

## 追加锚（本行以下为增补区）

## 142. 单根纯芽的整球延续、紧纯分离子排除与同原复三能级

### 142.1 完整原域、源接口及主定理

**定义 142.1（原对象及定型的两类标签）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的原质量泛函 $u\in V^*$。始终取整个原域

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
C^*=\{h\in V^*:h(C)\subseteq\mathbb R_+\},\qquad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\qquad
D_p=\{z\in K:T_p(z)=0\},\qquad S_p=P\cap D_p,\\
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\qquad
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p.
\end{gathered}
\tag{XI142.1}
$$

$K$ 是紧基且张成 $V$；完整效应区间在有限维中紧，$\mathcal F_p$ 非空紧，所以 minimum 对每个原混输入 $z\in K$ 都达到。纯关系 $p\perp q\Longleftrightarrow q\in S_p$ 由补效应对称，且反自反。完整 EB3 的含义是：对每个原 $p\in P$，整个 $D_p$ 都仿射等价于非退化闭三球。它本身不声称 $T_p$ 仿射、$e_p$ 为 least 或 $\mathcal F_p$ 为单点。

保留原零图条件 $\mathsf{Conn}$：任意两个原纯点由有限条原零边连接，长度可依端点改变。在全部目标之前固定同一个 $o\in P$，置

$$
\begin{gathered}
Q(r)=\bigcup_{s\in S_r}S_s,\qquad Q=Q(o),\qquad
\Lambda=\{a\in P:S_a\subseteq Q\},\\
\mathsf G(o):\quad \exists W\subset V\text{ 开},\quad o\in W,\quad W\cap P\subseteq Q.
\end{gathered}
\tag{XI142.2}
$$

在尚未取得相等之前，$Q$ 与 $\Lambda$ 始终分别定型。$x\in Q$ 是原纯点，故其原球 $D_x$ 有定义；这不表示 $x\in\Lambda$。$a\in\Lambda$ 表示整个 $S_a$ 留在 $Q$，不表示标签 $a\in Q$。

以下仓内来源统一取固定提交 `088113172f8caa47dd61617f69e908a7f370fab1` 的正文。所用源接口及其量词如下。

* [VII103.2][Q142VII]及[IX116.1—116.2][Q142IX]给每个 $D_p$ 为非点紧暴露极大真面，$S_p=\partial_{\rm rel}D_p\cong S^2$，$D_p=\operatorname{conv}S_p$；全部非空原真面只有纯单点和完整排除球。不同完整球至多交于一个原纯点。这些结论不输入全 Pair。
* [THREE_COPY VIII130.2][Q142TC]、[IX119.10、120.2、120.7—120.8][Q142IX]及[XI137.2][Q142XI]在完整 EB3+$\mathsf{Conn}$ 下给全部原标签的 Inj、$\mathcal A_p=\{e_p\}$、$\dim L_p=4$。特别地，这里的 $p$ 遍历整个 $P$，不是只遍历 $Q$。$g_p=u-e_p$ 只在 $p$ 为零，限制 $L_p\to\operatorname{Aff}(D_p)$ 为线性同构；此时不预付其逆的正性。
* [XI137.3、137.7—137.8及139.2第1、2项、139.5、139.8][Q142XI]给紧纯集 $Q\subset P$，其原子空间拓扑为无边界四维拓扑流形；存在同一个环境开集 $U_0\ni o$，使 $Q(p)=Q$ 对每个 $p\in U_0\cap P$ 成立。$\Lambda$ 紧，$a\mapsto D_a$ 在整个 $\Lambda$ 上 Hausdorff 连续，且 $S_p\subseteq\Lambda$ 对这些近根 $p$ 成立。
* [XI141.2][Q142XI]在这些相同原前件和源接口下给 $\dim_{\mathbb R}V=9$。其上界使用原对偶边界中的实际开集与 Hurewicz 紧闭映射定理，下界使用 Alberti 整个奇异集的图覆盖。这里复用该完整维数结论，不重新将九维设作前件。

取辅助欧氏结构，记 $A=\operatorname{aff}K=\{u=1\}\cong\mathbb R^8$，$H_0=\ker u$，$M=\partial_AK$。凸体内点的径向投影给 $M\cong S^7$。辅助尺只用于距离、连续性及图覆盖。

**定理 142.2（单根纯芽的原域全局化）。** 在定义142.1的完整 EB3+$\mathsf{Conn}$ 域，若一个事先固定的原根满足 $\mathsf G(o)$，则

$$
\boxed{P=Q(o)=\Lambda,\qquad
\bigcup_{x\in Q(o)}D_x=M,\qquad \operatorname{conv}Q(o)=K.}
\tag{XI142.3}
$$

更具体地，整个 $Q\ni x\mapsto D_x$ Hausdorff 连续并局部组成真正的闭三球丛；对每个紧集 $T\subset P$ 都有 $\dim_{\rm cov}T\le4$。对全部 $x,y\in P$，包括相同端点，存在同一个原纯标签 $a$ 满足 $x\perp a\perp y$。特别地，原固定根满足 $\mathsf R_1$。随后复用 [X133.6—133.7][Q142X]，取得同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI142.4}
$$

反向，整个标准复三能级锥及迹单位，经任意这样的同锥同单位表示运输，都满足完整 EB3、Conn，以及每个事先指定原根的 $\mathsf G$。因而在这一完整原域内，“EB3、Conn及存在一个固定根芽”与(XI142.4)等价。量子分类与维数工具为既有结论；本定理新增的是从单根局部信息到整个原域覆盖的桥。

### 142.2 七个承重步骤的完整证明

**一、复用全点紧投影覆盖，限制每个紧纯子集的维数。** 全部原标签的 Inj 和四维法向已由上述 THREE_COPY VIII130.2、IX119.10及137.2支付，直接记为

$$
D_p=D_q\Longrightarrow p=q,\qquad \dim L_p=4\quad(p\in P).
\tag{XI142.5}
$$

这里不重证沿有限原零边的冗余传播，也不将完整确认菜单缩为完整暴露族。原法向与 $A$ 中外法向的准确对应直接复用 [BILATERAL VIII121.6证明中的式(121.17)][Q142BVIII]，亦见 [SAME_READBACK128.3][Q142SR]：

$$
N_p\overset\sim\longrightarrow\widehat N_K(p),\qquad h\longmapsto-h|_{H_0},\qquad
\dim\operatorname{span}\widehat N_K(p)=4\quad(p\in P).
\tag{XI142.6}
$$

同一个原 $K$ 是八维仿射空间 $A$ 中有非空内部的紧凸体。对这个 $K$ 直接应用 [SAME_READBACK引理128.2及其证明的紧投影结论][Q142SR]，取该引理的环境维数 $n=8$、锥张成维数索引 $k=4$。得到

$$
P\subseteq\Sigma_4(K)\subseteq\bigcup_{j\ge1}X_j,\qquad
\Sigma_4(K)=\{z\in M:\dim\operatorname{span}\widehat N_K(z)\ge4\},\qquad X_j\subset M\text{ 紧}.
\tag{XI142.7}
$$

该源证明给每个 $X_j$ 一个到四维线性空间 $F_j$ 的正交投影 $\pi_j$，满足

$$
\dim F_j=8-4=4,\qquad
\|z-w\|\le\frac2{\sqrt3}\|\pi_jz-\pi_jw\|\quad(z,w\in X_j).
\tag{XI142.8}
$$

故投影在 $X_j$ 上单射。这一全点、紧层及同一投影的接口也被 BILATERAL VIII121.6明确复用；它由原凸法向单调性与有理有限见证取得，不是几乎处处的可求长覆盖。其一般凸体证明不要求 $P$ 紧、关联开放或额外种子。本章不重新构造该覆盖。

给任意紧 $T\subset P$，置

$$
T_j=T\cap X_j,\qquad T=\bigcup_{j\ge1}T_j.
\tag{XI142.9}
$$

各 $T_j$ 是 $T$ 中的紧闭子集。投影将它同胚到 $F_j\cong\mathbb R^4$ 的一个紧子集，所以

$$
\dim_{\rm cov}T_j=\dim_{\rm cov}\pi_j(T_j)\le4.
\tag{XI142.10}
$$

这里使用覆盖维数对闭子集的单调性及 $\dim\mathbb R^4=4$，准确见 [Engelking，Theorems 3.1.4、1.8.2][Q142En]。同书 **Theorem 3.1.8，印刷页212** 的闭子空间可数和定理要求：正规空间为一列闭子空间的并，且各闭子空间的覆盖维数至多同一个整数 $n$；结论为全空间覆盖维数至多 $n$。其 Lemma 3.1.6—Proposition 3.1.7 的证明在页210—212。此处 $T$ 紧度量，因而正规；$T_j$ 闭、可数且覆盖 $T$。因此

$$
\boxed{\text{每个紧 }T\subset P\text{ 都满足 }\dim_{\rm cov}T\le4.}
\tag{XI142.11}
$$

未假设整个 $P$ 紧或闭，也未把四维 $Q$ 当作 $P$ 的维数界。

**二、只在已付域上构造 join，并在每颗 $S_x$ 上取得开放圆片。** 取 $U=U_0\cap Q$。它是 $Q$ 中含 $o$ 的开集；对每个 $p\in U$，已有 $Q(p)=Q$ 及整个 $S_p\subseteq\Lambda$。对 $x\in Q$、$p\in U$、$x\ne p$，二步集合相等给至少一个

$$
j(x,p)\in S_p\subseteq\Lambda,\qquad x,p\in S_{j(x,p)}.
\tag{XI142.12}
$$

若两个不同标签都满足此式，其不同完整球便含两个不同原纯点，与点交规则矛盾；故 $j$ 唯一。它在 $\{(x,p)\in Q\times U:x\ne p\}$ 上连续：若 $(x_i,p_i)\to(x,p)$，紧 $\Lambda$ 使任意标签子列可再收敛到某个 $a\in\Lambda$；$\Lambda$ 上的整球连续性给 $x,p\in D_a$。两者原纯，故在 $S_a$，唯一性给 $a=j(x,p)$。所有聚点相同，遂有整列连续性。未定义未付的远端点对 join。

固定 $x\in Q$。$U$ 为四维流形非空开集，可选 $p\in U\setminus\{x\}$。记 $a=j(x,p)$，在完整球面 $S_p\subseteq\Lambda$ 中选 $b\ne a$。对称性给 $p\in S_b$，而 $x\notin S_b$，否则 $b$ 也是 $x,p$ 的 join。$b\in\Lambda$ 给 $S_b\subseteq Q$，所以可在 $S_b\cap U$ 中取含 $p$ 的二维开圆片 $A_b$。映射

$$
f_x:A_b\longrightarrow S_x,\qquad t\longmapsto j(x,t)
\tag{XI142.13}
$$

处处有定义、连续，像落在 $\Lambda\cap S_x$。它单射：若不同 $t_1,t_2$ 同映到 $c$，则 $D_b,D_c$ 含这两个点，故两球相同、$b=c$；但 $x\in S_c$ 与 $x\notin S_b$ 矛盾。源、目标均为二维无边界流形，故 [Hatcher，Theorem 2B.3，印刷页172][Q142Ha]的区域不变性给

$$
\varnothing\ne\Omega_x:=f_x(A_b)\subseteq\Lambda\cap S_x,
\qquad\Omega_x\text{ 在整个原 }S_x\text{ 中开}.
\tag{XI142.14}
$$

这时只得到开放圆片，尚未得到 $S_x\subseteq\Lambda$。

**三、九个真实标签连续确定整个原椭球。** 固定 $x_0\in Q$，在上一步的 $\Omega_{x_0}$ 中取点。$A_0=\operatorname{aff}D_{x_0}$ 是三维仿射空间，其次数至多二的实多项式空间维数为十。在 $\Omega_{x_0}$ 上恒零的这些多项式恰是一维空间，由 $S_{x_0}$ 的椭球方程生成。

为直接说明这个初等事实，将原椭球仿射化为单位球。二次多项式在非空球面开片为零；选开片内一点，每条经过该点的大圆上都有零开弧。其限制是次数至多二的三角多项式，因而整圆为零；这些大圆覆盖整个球面。写多项式为 $c+\ell\cdot z+z^{\mathsf T}Bz$，$B$ 对称，比较正反点给 $\ell=0$，代入坐标轴及两轴等分方向给 $B=-cI$。故它是 $\|z\|^2-1$ 的倍数。完整球面的九点评价秩已见 [BILATERAL VIII121.2][Q142BVIII]；这里补上从任意非空开放圆片中选取九点的依据，二次曲面唯一性亦与137.6一致。

所以所有点评价泛函在对偶空间中张成九维子空间，可以选九个实际点 $a_1,\ldots,a_9\in\Omega_{x_0}$，使评价矩阵秩为九。它们必含四个仿射无关点；否则某个非零仿射一次多项式也在这一维核中，不可能与非退化椭球方程成比例。重排使前四点仿射无关。由(XI142.13)，各 $a_i$ 都有固定的 $p_i\in A_b\subset U$ 满足 $a_i=j(x_0,p_i)$。

将 $x$ 限制在 $x_0$ 的充分小 $Q$-邻域内，避开有限个 $p_i$，定义

$$
a_i(x)=j(x,p_i)\in S_x\quad(1\le i\le9),\qquad
F_x(z)=a_1(x)+\sum_{r=1}^3z_r\bigl(a_{r+1}(x)-a_1(x)\bigr).
\tag{XI142.15}
$$

各 $a_i(x)$ 连续；前四点的仿射无关性保持，故 $F_x$ 为 $\mathbb R^3$ 到 $\operatorname{aff}D_x$ 的仿射同构。其余五点在此坐标中的值连续，可由满秩三列的连续左逆给出。九点评价矩阵继续秩九，其一维核有连续非零局部生成元：固定一个非零九阶子式，将一个核坐标归一后解其余坐标即可。

每个原 $S_x$ 的二次方程都在这个核中，因而与所选生成元成比例。选择在 $x_0$ 处二次部分正定的符号，缩小邻域后可连续写为

$$
q_x(z)=z^{\mathsf T}H_xz+2\ell_x^{\mathsf T}z+k_x,
\qquad H_x>0,\qquad
r_x^2=\ell_x^{\mathsf T}H_x^{-1}\ell_x-k_x>0.
\tag{XI142.16}
$$

后二者均为开条件，在 $x_0$ 由实际非退化椭球成立。核唯一性和原球的凸性说明整个原实心球，而非仅九点或圆片，恰为

$$
D_x=F_x\bigl(-H_x^{-1}\ell_x+r_xH_x^{-1/2}\overline{\mathbb B}^3\bigr)
=c(x)+L(x)\overline{\mathbb B}^3,
\qquad \operatorname{rank}L(x)=3.
\tag{XI142.17}
$$

$c(x),L(x)$ 连续；正定平方根连续是有限维线性代数。$x_0$ 任意，故整个 $Q$ 上的原球族 Hausdorff 连续。这里的椭球延续只靠已存在的 join 与有限点确定性，没有给 $Q$ 添加光滑结构，也没有先把 $S_x$ 全放入 $\Lambda$。

**四、真正的七维开球丛在原边界中有开像。** 定义

$$
\begin{gathered}
\mathscr E=\{(x,z)\in Q\times K:z\in D_x\},\qquad
\mathscr E^\circ=\{(x,z)\in\mathscr E:z\in\operatorname{ri}D_x\},\\
\mathcal B=\bigcup_{x\in Q}D_x,\qquad
\mathcal O=\bigcup_{x\in Q}\operatorname{ri}D_x.
\end{gathered}
\tag{XI142.18}
$$

(XI142.17)给真实局部平凡化 $(x,v)\mapsto(x,c(x)+L(x)v)$。其逆为连续左逆作用于 $z-c(x)$，故 $\mathscr E$ 为闭三球丛，$\mathscr E^\circ$ 为开三球丛。$Q$ 是四维无边界 Hausdorff、第二可数拓扑流形，因而 $\mathscr E^\circ$ 是七维无边界拓扑流形。整球连续性还使 $\mathscr E$ 在紧 $Q\times K$ 中闭，所以它紧。

每个 $D_x$ 为原真面，故在 $M$ 中。评价映射

$$
\operatorname{ev}:\mathscr E^\circ\longrightarrow M,
\qquad (x,z)\longmapsto z
\tag{XI142.19}
$$

连续且单射。若两个不同标签的球含同一个相对内点，该点非纯，违反不同完整球的点交规则；球相同又由 Inj 迫标签相同。源、目标均为七维无边界流形，区域不变性逐坐标适用，故 $\mathcal O$ 是 $M$ 的实际非空开子集。另一方面，$\mathscr E$ 的连续像 $\mathcal B$ 紧，故在 $M$ 中闭。此处开放性来自真实球丛的评价映射，不是假设全局点对关联开放。

**五、未覆盖会迫出不可能的紧纯分离子。** 反设 $\mathcal B\ne M$，令

$$
T=\partial_M\mathcal B.
\tag{XI142.20}
$$

$\mathcal B$ 闭且含非空开集 $\mathcal O$，$M\setminus\mathcal B$ 也非空开。于是
$M\setminus T=\operatorname{int}_M\mathcal B\ \sqcup\ (M\setminus\mathcal B)$
为两个非空不交开集的并；连通的 $M$ 还保证 $T\ne\varnothing$。$T$ 为 $M$ 的紧真子集。

因 $T\subseteq\mathcal B$，任取 $z\in T$ 可选 $x\in Q$ 使 $z\in D_x$。若 $z$ 非纯，$S_x=\partial_{\rm rel}D_x$ 的全部点原纯，故 $z\in\operatorname{ri}D_x\subseteq\mathcal O\subseteq\operatorname{int}_M\mathcal B$，与边界定义矛盾。因此

$$
T\subseteq P.
\tag{XI142.21}
$$

现在使用适用于**任意紧集**的 Čech–Alexander 对偶。准确来源是 [Hatcher，Corollary 3.45及紧集扩张说明，印刷页255—257][Q142Ha]。Corollary 3.45的奇异上同调版本需要局部可缩；页256—257明确以 Čech 上同调替代，扩张至没有局部可缩性的紧集。这里 $M\cong S^7$，$T$ 非空、紧、真，没有对 $T$ 加局部可缩或流形前件。所得准确次数是

$$
\check H^6(T;\mathbb Z)
\cong\widetilde H_0(M\setminus T;\mathbb Z)\ne0.
\tag{XI142.22}
$$

非零性也可直接看成：补集的上述两个开闭部分不可能被一条路径连通，故约化零阶奇异同调非零。

若紧度量空间 $T$ 的覆盖维数至多五，则每个有限开覆盖都有重数至多六的有限开细化，其神经的维数至多五，六阶整数上同调为零。按页256—257的覆盖神经直接极限定义，所有六阶 Čech 类在这种细化中消失，所以 $\check H^6(T;\mathbb Z)=0$。故(XI142.22)迫 $\dim_{\rm cov}T\ge6$。但紧 $T\subset P$ 已由第一步得到 $\dim_{\rm cov}T\le4$，矛盾。由此

$$
\mathcal B=M.
\tag{XI142.23}
$$

这一矛盾实际使用的是全部原 $P$ 的紧投影覆盖界；只知道 $\dim Q=4$ 或 $\check H^6(Q)=0$，不足以处理可能落在 $P\setminus Q$ 的分离子。

**六、以非纯面内点返回全部原标签。** 给任意原 $a\in P$，取 $z\in\operatorname{ri}D_a$。它非纯且在 $M=\mathcal B$ 中，故属于某个 $D_x$，$x\in Q$。不同完整球只能交于纯点，迫 $D_a=D_x$；原标签单射给 $a=x\in Q$。这证明整个 $P=Q$，而非仅证明球并覆盖。

于是每个原 $a$ 的整个 $S_a$ 均落在 $P=Q$，定义直接给 $\Lambda=P$。有限维紧凸基由全部极点凸生成，故 $\operatorname{conv}Q=K$。现将先前部分 join 合法推广为全域结论：对不同 $x,y\in P$，将二者视为已知相等的 $\Lambda$ 中标签，139.2第3项给唯一 $a\in Q=P$，使 $a\in S_x\cap S_y$；零对称给 $x,y\in S_a$。相同端点 $x=y$ 时，任选非空原 $S_x$ 中的 $a$，亦有同一标签承担两条边。因此

$$
\forall x,y\in P\ \exists a\in P:\quad x\perp a\ \land\ y\perp a.
\tag{XI142.24}
$$

不同端点时见证唯一，由 Inj 与点交规则也可直接推出。两端同属原真面 $D_a$，所以全部不同纯对的原最小面为真，即原全 Pair。尤其固定的原 $o$ 对每个目标都有共同邻点，满足

$$
\forall y\in P:\quad o\perp y\ \lor\
\exists a\in P:\ o\perp a\ \land\ y\perp a,
\tag{XI142.25}
$$

这正是 $\mathsf R_1$ 的同一固定根；相同目标 $y=o$ 没有遗漏。也可只由 $Q(o)=P$ 立即取得这一点。

**七、消费既有同原分类，并检查整个反向。** 至此才用 X133.6 的 EB3+$\mathsf R_1$ 分类，得到(XI142.4)。其既有依赖为 IX120.4—120.5、IX116.17—116.18；真实三角、满宽、全 Pair 到成熟秩三 Jordan／复型选择均按这些源定理的原费用消费，不算作这里的新分类。下一节直接计算完整确认菜单与每个混态上的 minimum，保证这个消费没有缩小原态域或效应域。

反向取整个标准 $\operatorname{Herm}_3(\mathbb C)$、$\mathrm{PSD}_3$、$\operatorname{Tr}$。完整效应恰为 $f_M(X)=\operatorname{Tr}(MX)$、$0\preceq M\preceq I_3$。对任意单位 $v$，全部确认菜单计算给
$D_{P_v}=\{\rho\succeq0:\operatorname{Tr}\rho=1,\rho v=0\}$，即 $v^\perp$ 上全部二阶密度矩阵的完整三球，所以每个原标签满足 EB3。对任意单位 $v,w$，包括相同射线，$\dim_{\mathbb C}\operatorname{span}\{v,w\}\le2$，可取单位 $z\perp\operatorname{span}\{v,w\}$。同一个原纯点 $P_z$ 给 $P_v\perp P_z\perp P_w$，每条边由原投影效应见证。因此 Conn 成立，而且每个事先指定根都有 $Q(o)=P$，当然满足其局部 $\mathsf G(o)$。整个原域通过同一 $\Phi$ 运输，结论保持。主定理证毕。

### 142.3 同一个表示下的完整静态字典

令 $P_v=vv^*$、$v^*v=1$，$Q_v=I_3-P_v$，$p_v=\Phi(P_v)$，$U=\Phi(I_3)$。以下都是(XI142.4)所得**同一个** $\Phi$ 的全域运输，复用 X133.7、XI135.5—135.6及141.4的字典。

| 原对象 | 同原锥、同原单位的完整对应 |
| --- | --- |
| 载体、质量及全部锥元 | 全部 $X\succeq0$ 对应整个 $C$，含零、次归一及任意非负质量；$u(\Phi X)=\operatorname{Tr}X$。原 $u\in V^*$ 与 Jordan 单位 $U\in V$ 不混型。 |
| 所有密度与混合 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，保持全部有限凸组合和非负组合；$\dim_{\rm aff}K=8$。 |
| 全部纯射线与叠加的静态含义 | $P=\{p_v\}\cong\mathbb{CP}^2$，实维四。任意非零 $w\in\mathbb C^3$ 对应 $\Phi(ww^*/(w^*w))$；任意非零复倍数表示同一原纯标签，任意非零线性叠加也有其射线标签。 |
| 全效应与全部混输入读数 | $f_M(\Phi X)=\operatorname{Tr}(MX)$ 恰遍历全部 $0\preceq M\preceq I_3$，保持零、单位、补与序；全部实线性读数对应任意 Hermitian $M$。 |
| 完整非单点确认菜单、least与已达minimum | $\mathcal F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\}$；least 为 $f_{P_v}$。对每个原混态，$T_{p_v}(\Phi\rho)=\operatorname{Tr}(P_v\rho)=v^*\rho v$，同一个 $B=0$ 达到。 |
| 纯比较与所有端点 | $T_{p_v}(p_w)=\lvert v^*w\rvert^2$，未归一向量时除以 $(v^*v)(w^*w)$。相同射线给一，正交射线给零，纯比较互易 PR 成立。 |
| 完整排除球与球缘 | $D_{p_v}=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1,\rho v=0\}$，包含全部混态，是完整 qubit 三球；球缘为 $\mathbb{CP}^1\cong S^2$。球心 $c_{p_v}=\Phi(Q_v/2)=(U-p_v)/2$，总体中心态 $U/3$。 |
| 原框架与数学共同效应 | 零三角对应三个正交秩一投影，和为 $I_3$；其三个 least 效应和为 $u$。每条原零边有唯一第三点；数学完美区别容量为三。 |
| 全部有限数学测量 | 对每个有限结果数，全部 $f_j\in C^*$、$\sum_jf_j=u$ 恰对应全部 POVM $M_j\succeq0$、$\sum_jM_j=I_3$；在每个原输入上概率为 $\operatorname{Tr}(M_j\rho)$，允许零效应及重复项。 |
| 谱与全部实可观测量 | 每个原态有三项正交纯谱分解，允许零权和重谱；全部 Hermitian 可观测量有实谱及谱效应。重谱不指定唯一的逐本征射线。 |
| 共同尺、Jordan及齐次性 | $\langle\Phi X,\Phi Y\rangle_\Phi=\operatorname{Tr}(XY)$ 使原 $C$ 自对偶；$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$，单位为 $U$。正定矩阵的可逆合同变换给锥内部的齐次性。 |
| 全域球心图与原混合关系 | $R(x)=(u(x)U-x)/2$ 定义于全部 $V$，正、保质量且可逆，$R(p)=c_p$。每份有限纯配方的球心替换只依赖其原混态。 |

完整最低定义需要单独核实。若 $0\preceq M\preceq I_3$ 且 $v^*Mv=1$，则正半定性给 $(I_3-M)v=0$，所以 $Mv=v$；Hermitian 性消去 $\mathbb Cv$ 与 $v^\perp$ 间的交叉块。故全部且仅有 $M=P_v+B$、$B=Q_vBQ_v$、$0\preceq B\preceq Q_v$，其中 $B$ 可从零变化到 $Q_v$，菜单确实非单点。对每个正矩阵 $X$，

$$
f_{P_v+B}(\Phi X)-f_{P_v}(\Phi X)
=\operatorname{Tr}(BX)\ge0.
\tag{XI142.26}
$$

同一菜单的 $B=0$ 给全锥序的 least，并同时在每个混输入达到原 minimum。正半定性还给 $v^*\rho v=0\Longleftrightarrow\rho v=0$；在 $v^\perp$ 取正交坐标后，全部这样的 $\rho$ 恰为 $(I_2+r\cdot\sigma)/2$、$\|r\|\le1$，而非仅有纯零关系表。这证明字典中的完整球与完整 Born 读数。

特别地，全部原 $P$ 现已紧、整个球族连续，且 $P=Q=\Lambda$、$\operatorname{conv}Q=K$、原边界的球覆盖、每根完整二步覆盖、所有真实三角、全 Pair、PR、least、全部混态谱性、共同中心、自对偶与同原 Jordan 结构均已得到。它们在本定理的前件下不再是额外未付条件。全域球心公式还给完整 MC：任意同一原态的两份有限纯配方，都被送到 $(U-x)/2$，含零权与重复标签。因此138.1的 BC 也成立；140.1的 ZC 可取 $e_a=f_{P_v}$，对 $x\in S_a$ 有 $e_a(c_x)=1/2$，故 $\kappa_a=1$；每个原纯点属于正交三角，Seed 成立。这里没有使用140.2的独立传播路线。

原限制 $L_p\to\operatorname{Aff}(D_p)$ 的正逆现在也可由同一矩阵模型核实：$N_{p_v}$ 恰为支持在 $v^\perp$ 的正矩阵读数锥，正好对应 $D_{p_v}$ 上全部非负仿射函数。这个正逆与球心图的逆不同；后者为 $R^{-1}(y)=u(y)U-2y$，对纯点 $p_v$ 给 $U-2p_v\notin C$，故不能宣称球心图有正逆。

本章仍未判定裸 EB3 或 EB3+Conn 是否自动具有某个 $\mathsf G(o)$。本章的单根芽不是从 Conn 定义中自动产生，局部芽条件与整个物理实现的费用也各有作用域。

### 142.4 来源、全部实际复合、事件与时间的保留合同

完整继承[XI141.5、139.11][Q142XI]、[THREE_COPY VIII131.8][Q142TC]及[SAME_READBACK SECTION127.10][Q142SR]的每一前件、原对象、作用域和全部量词。其传递引用 SAME_READBACK125.11、124.9、123.13，EXCLUSION VIII112.9、113.11与IX120.11，THREE_COPY VII121.12、122.14，INTRINSIC_POLAR VI定义89.7、89.8—89.10及全部两尺度式(89.13)、V88.6与87章、原生续卷VII和III的来源／全未来／动态合同，以及 BILATERAL VIII128.H，均按原文保留。操作来源的 INTRINSIC_POLAR VI 与整球 BILATERAL VI 不混同。

同一个原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签及每种同中点实现，全部非负质量（零、次归一与不等质量），过程和参考各自完整的相关联合输入域，仍分别供应。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)的全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集，均保持原定义。操作映射 $p$、纯标签及根芽条件按类型区分。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、旧 support、全部合法未来及每个中间切口，原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption与资源合同，继续由原消费者承担。静态纯射线与数学叠加不供应实际相干制备、相位参考、可调用门、接线或权限。

对每个有限 $N\ge1$，仍须另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 及完整原效应区间。每个实际二分割 $a+b=N$ 要求

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{XI142.27}
$$

同一产品配对、严格张量单位、全部原因子置换及逆的正性、规范重括号、指定运输下不连续位置分块均保留。实际二份比较 $S_2$ 继续量化每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族和全部 $t_\ell\ge0$、$\sum_\ell t_\ell=1$，含零权与重复标签：

$$
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)
=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\qquad
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]_{C_2^*}\\f(p)=1}}f(x).
\tag{XI142.28}
$$

单体 minimum 的线性化不支付全部纠缠输入。原低二份 $q=1,2$ 的 least／谱性／正面投影及保纯到 Jordan 桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制与秩、实维乘法的复型选择，以及同一实际两因子的产品正规形，仍是全有限层级的三项分别供应。

非经典 $\mathsf F_{\max}$ 仍需同一最大复块 $n_r=L\ge2$、同一含相位正交基上的实际三份资源

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{XI142.29}
$$

其余三份扇区为零，归一原源为 $\Delta_r/L$；不预付三份纯性或实际制备，全经典 $L=1$ 支路按原规则免此资源。单体复三能级支路 $L=3$，二、三份秩为九、二十七；高阶整个排除集不继续被规定为单体 EB3。形式矩阵不保证实际 $C_3$ 成员资格。

全部输入输出份数的原实线性 $F:W_m\to W_n$，全旁观正性仍量化每个 $b\ge0$ 和每个含纠缠的同一共同输入，要求 $(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$。实际完整有限层级及共同表示齐备后，才沿原 Choi 桥识别 CP、矩形跨扇区 Kraus。TP／TNI 逐个量化全部原 $x\in C_m$，分别要求 $u_n(Fx)=u_m(x)$／$u_n(Fx)\le u_m(x)$；同族分支总预算对同一个输入逐点承担。

同一实际事件的 CP 另需完整提升、实际探针和相容核；全部数学 CP-TNI 分支成为实际事件另需事件饱和选择。同族仪器保留共同输入预算、接线、记录、粗粒化和校准。只对严格正质量分支作条件归一，零质量分支不强定归一条件态。Lüders 更新另需同一分支的锐效应、接受态中性与输出校准。全部数学 POVM 与实际可执行仪器各保留合同；正保质量球心图也不因此取得全旁观 CP 或实际事件资格。

原物理钟、实际动态来源、连续齐次可逆时间群及单位仍分别供应。另给全实时间连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，才有该额外供应的有限维生成元；再给复块上保迹酉时间族，才使用

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\mathrm i[H,\rho]/\hbar,\qquad H=H^*.
\tag{XI142.30}
$$

量词覆盖全部原输入与全部实际时间。$H$ 的标量平移、时间重标分别保持原意义；恒等时间族和非平凡 Hamiltonian 族可共享全部静态对象。实际 Hamiltonian、能量识别与标定、数值 $\hbar$、时空与物理空间维数仍各自需要供应。九维实载体、四维纯域、三维排除球及零图关联步数均不指定物理空间或物理时间。

### 142.5 数学归属与完整中文图景

本章新增的全局化连接是：在每个 $x\in Q$ 的原球缘上，用近根的实际 join 描出开放圆片；从圆片中选九个有限见证，连续确定整个原椭球；据此建立真实三球丛并以其相对内部评价取得原七维边界中的开放区域；任何未覆盖处的边界都必须是紧纯分离子，而全原 $P$ 的法向紧投影覆盖使每个这样的紧集至多四维，排除对偶所要求的六维。最后以非纯面内点和原标签单射将球覆盖送回 $P=Q=\Lambda$。

完整面论、Conn 后全部原四维法向、近根二步集合相等、紧四维 $Q$、紧 $\Lambda$ 及其整球连续性、原九维结论和 R1 后的同锥同单位分类，均为明确所引源定理的复用。原凸法向层的全点紧投影覆盖、覆盖维数闭集可数和、区域不变性、任意紧集的 Čech–Alexander 对偶，以及有限维正定二次型和谱字典，均属成熟工具。这里没有以拓扑同胚 $Q\cong\mathbb{CP}^2$ 直接替代原凸混合结构，没有引入全局关联开放、光滑 $Q$、模面格、正限制逆或量子矩阵作为全局化前件。

把全部原状态想成同一块八维凸体，每个纯标签背后都有一颗完整实心排除三球。已知根附近每个点都能和 $Q$ 中任一点找到实际共同线路，但两个远处点能否共享线路，起初还不知道。固定一个远点，用根附近的一小片点去探测，就能在它的原球面上描出一块开放圆片。椭球受到二次方程约束，九个适当的真实点便能确定它；这些探针连续变化，整颗球也随之连续变化。这里没有先把整颗球上的标签宣布为已登记。

让 $Q$ 中全部点的完整三球随之移动，四维的标签加三维的球内坐标，确实组成七维的球丛。不同球的混态内部不能相撞，所以这些内部在原凸体的七维边界上铺出一块真正开放的区域。若整球并未铺满，已铺区域和缺口之间的边缘只能由原纯点组成；它还必须能把整个七维球面分开。任意紧集的 Alexander 对偶说，这种边缘至少要有六维的覆盖复杂度。

决定性的另一面来自全部原纯点，而非只来自已经掌握的 $Q$。原连通零图把每个纯点的法向维数都固定为四；已有的原凸法向层引理把全部这些点盖进可数个紧层，每层都能单射投影到四维空间。紧边缘与每个紧层相交仍是闭集，闭集可数和定理便把整个边缘压到至多四维。它不可能同时承担六维的分离任务，所以缺口不存在。

整球铺满后，任取原来可能在 $Q$ 外的纯标签，进入它那颗球的混态内部；此点必已由某颗 $Q$ 球承载，两颗球便只能相同，标签单射将该标签也送回 $Q$。于是全部原纯点、$Q$ 和 $\Lambda$ 真正相等，固定根的覆盖得到，既有分类才把整个原锥和原单位识别为同一个复三能级量子模型。全部密度、纯射线、完整非单点确认菜单、least、每个混输入的 Born minimum、全部有限 POVM、谱与 Jordan 字典因此一起成立。裸 EB3 或 EB3+Conn 是否能自行产生这个根芽仍是另一问题；实际来源、读回、质量、全有限复合与纠缠、三份资源、全旁观 CP、逐输入预算、事件仪器、记录、全部未来与切口，以及物理钟、Hamiltonian、能量和数值 $\hbar$ 仍按各自完整合同承担。

[Q142VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.1—103.2：完整原态与全效应、每混输入的已达minimum、排除面暴露及原真面穷尽。"
[Q142IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.2：点交及孤立重复块；119.10：全部原法向冗余公式、零冗余存在与沿边传播；120.2、120.7—120.8：原最大值、唯一零点、限制同构；120.4—120.5、116.17—116.18：保留的既有同原分类依赖。"
[Q142TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.2：Conn到Inj、P=P0及全部原四维法向的完整组合；131.7—131.8：静态字典及全部物理合同。"
[Q142XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI137.2—137.8：完整源接口、近根二步集合相等、紧纯Q；139.2、139.5、139.7—139.8：四维流形Q、Lambda标签对交点、紧Lambda及整球连续；141.2：上下界合成原V九维，及第五、六步整个奇异集的闭图构造；135.5—135.6、138.1、140.1、141.4—141.5：球心字典、BC/ZC定义及保留合同。"
[Q142X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.1、133.6—133.7：原R1量词、固定根全局分类、同原字典和完整反向；133.10：全部物理合同。"
[Q142SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "128.2及证明式(Q128.6)—(Q128.8)：全部法向层的可数紧覆盖和单射投影；128.3：原法向的准确对应；SECTION127.10及其传递引用：共同原来源、读回、质量、全部实际有限联合、事件仪器、所有未来与切口及物理时间。"
[Q142BVIII]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md "VIII121.2：完整三球九点评价的唯一二次关系；121.6及式(121.15)、(121.17)：明确复用SAME_READBACK128.2的全点紧投影覆盖及原法向对应。这里不使用其E0种子或接触条件。"
[Q142En]: https://www.maths.ed.ac.uk/~v1ranick/papers/engelking.pdf "R. Engelking, Dimension Theory, North-Holland/PWN：Theorem 3.1.8，印刷页212，正规空间的闭子空间可数和覆盖维数定理；证明入口Lemma 3.1.6—Proposition 3.1.7，页210—212；Theorem 3.1.4，页209，闭子集单调性；Theorem 1.8.2，页73，欧氏空间覆盖维数。这里直接使用原著覆盖维数dim版本，无需在ind与Ind间换型。"
[Q142Ha]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology：Theorem 2B.3，印刷页172，连续单射的区域不变性；Corollary 3.45，页255，Alexander对偶；页256—257以Čech上同调替代奇异上同调，将对偶扩张到任意紧集，并给出覆盖神经直接极限定义。"

## 追加锚（本行以下为增补区）

## 143. 原二元反射的增益约束与不塌缩量子候选

**定义 143.1（完整原域、原连通与二元读数界）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C$ 和在 $C\setminus\{0\}$ 上严格正的原单位 $u$，始终使用整个 $K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$ 和整个 $\mathcal E=[0,u]_{C^*}$。全部原确认效应定义 $T_p$ 及完整 $D_p$，完整 EB3 要求每个 $D_p$ 是非退化仿射实心三球，中心记为 $c_p$。原边 $p\perp q$ 指一张原全域效应在两端读一、零；补效应使它对称。$\mathsf{Conn}$ 仍指任意两个原纯点之间有有限原零边路，不是拓扑连通。

以下在 EB3+$\mathsf{Conn}$ 下工作。直接复用[THREE_COPY VIII130.2][Q143TC]：原标签 Inj，全部 $P=P_0$，且

$$
\begin{gathered}
\mathcal A_p=\{e\in\mathcal E:e(p)=1,\ e|_{D_p}=0\}=\{e_p\},\qquad g_p=u-e_p,\\
\{e_p=0\}\cap K=D_p,\qquad \{e_p=1\}\cap K=\{p\}.
\end{gathered}
\tag{XI143.1}
$$

这不把全部确认菜单 $\mathcal F_p$ 缩成单点，也不预付 least。对每条有向原边定义实际反射态及其原读数

$$
s_{pq}=2c_q-p\in P\cap D_q,\qquad
d_{pq}=e_p(s_{pq})=2e_p(c_q)-1.
\tag{XI143.2}
$$

因为 $p$ 是完整球 $D_q$ 的纯球缘点，$s_{pq}$ 是同一原球中的对径纯点。原正性和(XI143.1)给 $0\le d_{pq}<1$；在整个 $D_q$ 上，$e_p$ 的唯一最大点是 $p$，最小点是 $s_{pq}$，故

$$
d_{pq}=1-\operatorname{osc}_{D_q}e_p.
\tag{XI143.3}
$$

先定义用于局部正性估计的二元条件

$$
\mathsf H:\qquad
\forall p,q\in P,\quad p\perp q\ \Longrightarrow\ d_{pq}\le\frac12,
\quad\text{等价于}\quad e_p(c_q)\le\frac34.
\tag{XI143.4}
$$

量词包括两个方向，但不要求两个有向数值相等。143.3使用这个固定半刻度界；143.4的主候选只需下述更弱的统一可读差额：

$$
\mathsf{U}:\qquad\exists\varepsilon>0\ \forall q\in P\ \exists p\in P\cap D_q:\quad
1-d_{pq}\ge\varepsilon.
\tag{XI143.4a}
$$

这里每颗完整球只需一条实际有向反射边，$\varepsilon$ 在全部球之前选定；$\mathsf H$ 给 $\mathsf U$ 的特例 $\varepsilon=1/2$。逐边的 $d_{pq}<1$ 已由原域保证，却不等于这个统一差额。两项都不输入140.1的 $\mathsf{ZC}$、三角种子、所有直径的平均读数恒定或数值比较互易 PR。

**定理 143.2（同一原边的预算乘积及完整正分解）。** 在定义143.1的 EB3+$\mathsf{Conn}$ 域，固定每个原 $p$ 的任意完整球坐标

$$
D_p=c_p+B_p\overline{\mathbb B}^3,\qquad
H_p(c_p+B_pw)=w,\qquad H_p(p)=0.
\tag{XI143.5}
$$

这里 $B_p$ 单射，$H_p:V\to\mathbb R^3$ 的各分量属于 $L_p=\operatorname{span}\{h\in C^*:h(p)=0\}$，由[IX120.8、120.10][Q143IX]的实际限制同构唯一给出。沿用[IX119.4][Q143IX]的有限增益阈值，另记为

$$
\gamma_p=
\sup_{\substack{z\in K\\e_p(z)>0}}
\frac{\|H_p(z)\|-g_p(z)}{e_p(z)}\in[0,\infty).
\tag{XI143.6}
$$

它是指定投影 $P_{p,t}z=(g_p(z)+t e_p(z))c_p+B_pH_p(z)$ 在整个原锥上为正的准确阈值，不是140.1的相容常数。

对原边 $p\perp q$，置 $a=d_{pq}$、$b=d_{qp}$、$s=s_{pq}$、$c=d_{sq}=e_s(p)$，并写 $q=c_p+B_pv$、$\|v\|=1$。则 $a=0$ 当且仅当 $b=0$。当 $a,b>0$ 时，

$$
\gamma_p\ge\frac{2b(1-a)}{a(1-b)},\qquad
\gamma_q\ge\frac{2a(1-b)}{b(1-a)},\qquad
\gamma_p\gamma_q\ge4.
\tag{XI143.7}
$$

对任意实数 $t$，另有整个原 $V$ 上的恒等式

$$
\begin{aligned}
g_p+t e_p-v\cdot H_p
&=\bigl(t-\ell_p(q)\bigr)e_p+
\frac{2(1-a)}{(1-b)(1-ac)}e_s,\\
\ell_p(q)&=\frac{2c(1-a)}{(1-b)(1-ac)}.
\end{aligned}
\tag{XI143.8}
$$

因此若 $t\ge\sup_{q\in P\cap D_p}\ell_p(q)$，右侧由两张原非负效应构成，$P_{p,t}$ 在整个原锥上为正，且 $\gamma_p\le t$。

证明。若 $a=0$，实际 $s$ 被 $e_p$ 读零，所以 $s\in D_p$；它也在 $D_q$ 中，故 $p,q,s$ 是真实三角。在同一个完整球 $D_p$ 上，原效应 $e_q$ 在 $q,s$ 读一、零，因此两点对径，$s=2c_p-q$，给 $b=e_q(s)=0$。交换两端得到反向。这里只复用[IX120.4][Q143IX]的同球满刻度几何，没有合成共同仪器。

[IX120.12—120.13][Q143IX]的原邻点公式，在本章指标下准确为

$$
e_q=\frac{\rho g_p+v\cdot H_p}{1+\rho},\qquad
\rho=\frac{1+b}{1-b}.
\tag{XI143.9}
$$

注意 $b=d_{qp}$，不是 $a$。在真实 $s\in D_q$ 上，$e_q(s)=0$、$g_p(s)=1-a$，故 $v\cdot H_p(s)=-\rho(1-a)$，$\|H_p(s)\|\ge\rho(1-a)$。若 $a>0$，将同一个 $s$ 代入(XI143.6)，得到(XI143.7)第一式。交换两端得到第二式，两式右端之积恰为四。

再复用原双球消去身份：

$$
(1-c)e_p+(1-a)e_s=(1-ac)g_q.
\tag{XI143.10}
$$

它是原三角行走中的球上峰值公式经 $L_q\to\operatorname{Aff}(D_q)$ 的限制单射提升到全部 $V$ 的等式；参数对应于既有 `OriginalRegularHeight.two_ball_identity` 中的 $aa=s$。该恒等式的代数证明不使用该模块后续正规锚点的连续性前件。[Q143RH] 由(XI143.9)，

$$
g_p+t e_p-v\cdot H_p
=(1+\rho)(g_q-e_p)+t e_p.
$$

将(XI143.10)代入并用 $1+\rho=2/(1-b)$，即得(XI143.8)。全部分母严格正，因为 $a,b,c<1$。若右侧对每个单位 $v$ 均非负，则对每个原 $z\in C$，

$$
\|H_p(z)\|\le g_p(z)+t e_p(z).
$$

这是指定球锥投影的整个原域正性判据；等价地在 $e_p(z)>0$ 的归一态上给(XI143.6)的上界。没有把只在一个原球上合法的泛函当作原效应。证毕。

**定理 143.3（闭的二分之一读数界给逐标签严格小于二的预算）。** 在 EB3+$\mathsf{Conn}$+$\mathsf H$ 下，每个原纯标签分别满足

$$
L_p^*:=\sup_{q\in P\cap D_p}\ell_p(q)<2,
\qquad 0\le\gamma_p\le L_p^*<2.
\tag{XI143.11}
$$

不要求 $p\mapsto c_p$ 全局连续、$P$ 紧或跨全部 $p$ 的统一严格上隙。

证明。对固定 $p$ 的任意单位方向，(XI143.4)同时适用于原边 $(p,q)$、$(q,p)$、$(s,q)$，故 $0\le a,b,c\le1/2$。先增加 $b,c$ 至 $1/2$；对 $c$ 的单调性来自 $c/(1-ac)$ 严格递增，得到

$$
0\le\ell_p(q)\le\frac{2(1-a)}{1-a/2}\le2.
\tag{XI143.12}
$$

关键是排除上确界等于二，不能用每个方向严格小于二替代它。反设有 $q_n\in P\cap D_p$，使 $\ell_p(q_n)\to2$。标量盒 $[0,1/2]^3$ 紧；(XI143.12)及(XI143.8)的连续有理式迫使

$$
a_n\to0,\qquad b_n\to\frac12,\qquad c_n\to\frac12.
\tag{XI143.13}
$$

固定原球的完整纯球缘紧，所以取共同子列

$$
q_n\to q\in P\cap D_p,\qquad
s_n=2c_{q_n}-p\to s\in K,\qquad e_{q_n}\to f\in\mathcal E.
\tag{XI143.14}
$$

这里 $s$ 尚不预设纯；使用的是整个 $K$ 和整个 $\mathcal E$ 的紧性。原读数保留为

$$
e_p(p)=1,\qquad e_p(s)=0,\qquad
f(q)=1,\qquad f(p)=f(s)=0.
\tag{XI143.15}
$$

因此 $p,s\in D_q$，而 $e_p$ 在同一个完整球 $D_q$ 上取一、零，迫使 $s$ 是与 $p$ 对径的原纯球缘点。另一方面，$e_p(s)=0$ 的准确零面是 $D_p$，故 $s\in D_p$。在固定完整 $D_p$ 上，$f(q)=1,f(s)=0$ 又迫使

$$
s=2c_p-q.
\tag{XI143.16}
$$

于是对同一条收敛子列，

$$
b_n=e_{q_n}(2c_p-q_n)\longrightarrow f(2c_p-q)=f(s)=0,
$$

与(XI143.13)矛盾。这是原状态、原效应及两张完整球共同实现的约束；抽象赋值 $a_n\to0,b_n\to1/2$ 不满足它。故 $L_p^*<2$。将 $t=L_p^*$ 代入143.2的全方向正分解，即得 $\gamma_p\le L_p^*$。证毕。

**条件应用 143.4（二元不塌缩候选与同原完整静态量子模型）。** 在定义143.1的全部原量词下，下列两项等价：

$$
\boxed{\mathrm{EB3}+\mathsf{Conn}+\mathsf U};
\qquad
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V\text{ 实线性},\quad
\Phi(\operatorname{PSD}_3)=C,\quad u\Phi=\operatorname{Tr}.
\tag{XI143.17}
$$

在左项下，每条有向原边实际上有 $d_{pq}=0$，每条完整排除球的每条直径均有原满刻度效应，全部 $e_p$ 才取得 least 及 $T_p=e_p$ 的整个原混态结论。此处是既有不塌缩分类的原效应表述，不另计为新增分类定理。

证明。在 $V$ 固定任意环境范数，整个原效应区间紧，故

$$
0<M:=\max_{e\in\mathcal E}\|e\|_*<\infty.
\tag{XI143.18}
$$

对每个 $q$ 选 $\mathsf U$ 的同一个真实边见证 $p$。原 $p,s_{pq}$ 都在整个 $D_q$ 中，因而

$$
\varepsilon\le1-d_{pq}=e_p(p)-e_p(s_{pq})
\le M\|p-s_{pq}\|\le M\operatorname{diam}D_q.
\tag{XI143.19}
$$

于是全部原球直径统一不小于 $\varepsilon/M>0$。Conn按VIII130.2支付Inj，现在直接复用[IX118.8第二项到第四项][Q143IX]，得到同一个原锥、原单位的 $\Phi$。纯点紧性、整球连续、拓扑与Jordan分类由该已付路线承担，本章不重新证明。这里没有从逐球非退化跳到统一不塌缩；统一性恰由 $\mathsf U$ 的量词供应。

反向在整个标准复三能级域计算，再沿同一个 $\Phi$ 运输。任意纯态为 $p=vv^*$、$\|v\|=1$，整个 $D_p$ 是 $v^\perp$ 上全部迹一正矩阵的完整三球，$c_p=(I_3-p)/2$，唯一整球零尺为 $e_p(\rho)=\operatorname{Tr}(p\rho)$。若 $p\perp q$，则 $s_{pq}=I_3-q-p$ 是第三个正交秩一投影，$d_{pq}=0$。每颗完整球有原纯球缘点，故 $\mathsf U$ 可取 $\varepsilon=1$，且更强的 $\mathsf H$ 也成立。任意两条不同复射线在复三维中有共同正交射线，给至多两条真实零边的连接；相同射线取零长路。因此完整 $\mathsf{Conn}$ 成立。证毕。

特别地，半刻度候选 EB3+$\mathsf{Conn}$+$\mathsf H$ 也与该静态表示等价。143.2—143.3另外给不预装分类的原正性证明：正缺陷边要求两端增益之积至少四，而每端分别严格小于二，矛盾。分类本身不需要经过这条较长预算路线，也不需要把数值 $1/2$ 选为主前件。

**条件应用 143.5（几何、现有静态公理与剩余原合同）。** 在143.4的等价条件下，同一个 $\Phi$ 直接复用135.6的整个静态字典：$\dim_{\mathbb R}V=9$，全部归一态是八维仿射密度态体，全部纯态为 $\mathbb{CP}^2$，每张完整排除球的纯球缘为 $\mathbb{CP}^1\cong S^2$。全部效应为 $f_M(\Phi\rho)=\operatorname{Tr}(M\rho)$、$0\preceq M\preceq I_3$，每个原混态的最低确认是 $T_{p_v}(\Phi\rho)=v^*\rho v$，纯比较为 $|v^*w|^2$。全部有限数学 POVM、三元正交完成、谱分解、自对偶与 Jordan 结构也沿同一表示取得。

证明。143.4准确取得135.5的同锥同单位结论，因此135.6的全部参数对应逐项适用。特别地，$U=\Phi(I_3)$、$c_p=(U-p)/2$，球心替换相对于 $U/3$ 为反向缩小一半；故全 $\mathsf{MC}$ 及140.1的 $\mathsf{ZC}$ 都是后果。上述推导只在全原满宽已经证明后消费该字典。证毕。

该主候选用(XI143.4a)的统一二元可读差额接上既有不塌缩分类，不再输入140.4的 $\mathsf{ZC}$ 和 $\mathsf{Seed}$；它没有证明 EB3+$\mathsf{Conn}$ 自动给这个统一差额，也不证明独立假设数量最少或相对已等价于量子表示的完整候选严格更弱。三球是排除面的仿射维数，不指定物理空间维数；同一静态态体也不指定物理时间。

全部实际事件与条件更新、零质量分支、实际球心替换、可调用制备和仪器、任意有限复合的整个联合态锥及纠缠、全旁观 CP、同族逐输入预算与接线、记录、来源和合法未来、连续动力学、原物理钟、Hamiltonian、能量标定及数值 $\hbar$，仍保留135.7及其传递引用的全部独立前件。单体静态表示没有供应这些合同。

**约定 143.6（推导归属与白话关系）。** 本章采用仓内综合推导归属，不声明全球新颖性或历史优先权。原面、法向限制同构、峰值公式、双球恒等式及有限投影增益均复用上述原来源；同原不塌缩分类、全满宽分类与量子字典也不重新计为成果。143.4是已有分类的简短应用，不把二元重表述计为新的数学分类。143.2—143.3的仓内综合桥是：若同一条原边的反射缺陷为正，零值互易性使两端缺陷同时为正，真实反射态再将两端的增益乘积锁到至少四；全域二分之一读数界给各端至多二；若逼近等号，原紧球缘和同一极限效应又把反向读数迫到零，排除该等号。由此每端分别严格小于二，迫使每条边的缺陷全零。这不是把有限增益误当单位增益，也没有从两个不同模型的最优值拼出同一预算。

现成分类的迁移仍保留其额外前件：[Barnum—Müller—Ududec，Theorem 16][Q143BMU]要求 projectivity、对称跃迁概率与保纯滤子；本章不在143.2—143.3的原域估计中提前借用该分类，也不把 PR、正投影或谱性放回前件。通用紧性与球上仿射极值只是中间工具；新结论是它们在同一原双球、原单位和有向读数中的联合约束。

白话说：每个纯态背后都是一整颗实心排除三球。球里任取一对对径纯态，用其中一点自己的原零尺去比较另一点，读数之差就是这条直径还剩多少可读区别。主候选只要求每颗球至少有一条这样的真实直径，并且存在一个适用于全部球的正差额；再加上原零边能用有限步连接全部纯态。因为所有合法尺都在同一个有限维完整效应集里，这个统一差额阻止球缩成一点，既有分类便给同一完整复三能级量子态体及 Born 读数，并使全部直径最终都满刻度。无需先指定半刻度、三角种子或直径平均值相等；仍需完整三球、有限边路连通和统一可读差额，不能把逐球有差别冒充统一差额。实际仪器、复合与时间继续另有原合同。

[Q143IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX118.8：完整EB3+Inj+球直径统一不塌缩与同原复三能级分类等价；119.2、119.4：同一原坐标的有限正投影与准确增益；120.8、120.10—120.13：全原法向限制、方向函数与邻点公式；120.4—120.5、116.17—116.18：原满宽分类及静态字典。"
[Q143TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.2：完整 EB3+有限原零图 Conn 支付 Inj、全部唯一整球零尺、原四维法向和限制同构，不供应 least 或正限制逆。"
[Q143RH]: ../../../D5/S3/Quantum/Foundation/OriginalRegularHeight.lean "OriginalRegularHeight.two_ball_identity：实际相邻球中的对径 p、aa 与三个原整球零尺，通过 Coordinates.restriction 单射得到的全 V 恒等式；本章 aa=s。"
[Q143BMU]: https://arxiv.org/html/1403.4147v4#Thmtheorem16 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory, Theorem 16；不作为裸 EB3+Conn 的免费分类。"

## 追加锚（本行以下为增补区）

## 144. 单尺中点相容的球族连续性与上端不塌缩

### 144.1 完整原域与全域同值候选

**定义 144.1（原菜单、单尺和中点预算）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$、在 $C\setminus\{0\}$ 上严格正的原单位 $u\in V^*$。全程保留整个原域

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\qquad
D_p=\{z\in K:T_p(z)=0\},\qquad S_p=P\cap D_p.
\end{gathered}
\tag{XI144.1}
$$

$z$ 遍历每个原混态；完整效应区间和确认菜单紧，minimum 达到。EB3 要求每个完整 $D_p$ 是非退化仿射实心三球，中心为 $c_p$。$p\perp q$ 指 $q\in S_p$，补效应使它对称。$\mathsf{Conn}$ 要求任意两个原纯点之间有有限原零边路，长度可随端点改变。

以下保留 EB3+$\mathsf{Conn}$。直接复用[THREE_COPY VIII130.2][Q144TC]和[IX120.2、120.8、120.12][Q144IX]：全部标签单射，全部非空原真面只有纯单点或完整球，不同球至多交于一个原纯点，且

$$
\begin{gathered}
\mathcal A_p:=\{e\in\mathcal F_p:e|_{D_p}=0\}=\{e_p\},\qquad g_p=u-e_p,\\
\{e_p=0\}\cap K=D_p,\qquad \{e_p=1\}\cap K=\{p\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p,\\
\dim L_p=4,\qquad R_p:L_p\longrightarrow\operatorname{Aff}(D_p)
\text{ 是限制线性同构}.
\end{gathered}
\tag{XI144.2}
$$

每张固定 $S_a$ 上 $x\mapsto e_x$ 连续。这里的 $e_p$ 是唯一整球零确认，并非预先把整个 $\mathcal F_p$ 缩成单点；不预设 least、$T_p=e_p$、$R_p^{-1}$ 正、全纯域紧或跨球连续。

保留140.1的单尺中点相容 $\mathsf{ZC}$：对每个 $a\in P$ 有一个实数 $\kappa_a$，使

$$
e_a(c_x)+e_a(c_{\bar x^{\,a}})=\kappa_a
\quad(x\in S_a),\qquad \bar x^{\,a}=2c_a-x.
\tag{XI144.3}
$$

本章的完整同值候选则把这些局部常数接成同一个数：

$$
\mathsf{UC}:\quad
\exists\kappa\in\mathbb R\ \forall a\in P\ \forall x\in S_a:\quad
 e_a(c_x)+e_a(c_{\bar x^{\,a}})=\kappa.
\tag{XI144.4}
$$

它是由原定义生成的态、球心和效应之间的约束，不额外输入 Hilbert 空间、数值阈值或真实零三角。它加强了 $\mathsf{ZC}$ 的跨标签量词；不宣称该加强已由纯比较互易、Conn 或 EB3 导出。

### 144.2 不输入根芽的固定球连续性

**定理 144.2（单尺中点相容给固定球缘的向量连续性）。** 在定义144.1的完整 EB3+$\mathsf{Conn}$+$\mathsf{ZC}$ 域，对每个固定原根 $a$，

$$
1\le\kappa_a<2,\qquad
x\longmapsto e_a(c_x),\quad x\longmapsto c_x
\quad\text{在整个 }S_a\text{ 上连续}.
\tag{XI144.5}
$$

证明。对 $x\in S_a$，实际反射态 $y_x=2c_x-a\in S_x$。原非负性给 $e_a(c_x)\ge1/2$；$c_x$ 混而 $e_a$ 仅在 $a$ 取一，故 $e_a(c_x)<1$。对径两项相加给预算界；严格上界先是逐标签结论。

置 $h(x)=e_a(c_x)$。设 $x_n\to x$ 于固定紧球面 $S_a$，选择实现下极限的子列，再由紧 $K$ 令 $y_{x_n}\to y$。原效应紧性和已达到的零一见证给纯标签处的上关联 $y\in D_x$，正是 IX118.3 的式(IX118.4)。在完整球 $D_x$ 上，$e_a$ 的唯一最大点是 $a$，故其唯一最小点是 $2c_x-a$。于是

$$
2\liminf_n h(x_n)-1=e_a(y)\ge2h(x)-1.
\tag{XI144.6}
$$

$h$ 下半连续。固定球的对径映射连续，且 $h(x)+h(\bar x^{\,a})=\kappa_a$，故 $h$ 同时上半连续，从而连续。任何 $y_{x_n}$ 聚点现在都在 $D_x$ 上达到 $e_a$ 的唯一最小值，因此必为 $2c_x-a$。所有聚点相同，给 $c_{x_n}\to c_x$。这里只用固定球面紧性，没有使用全 $P$ 紧性。证毕。

**定理 144.3（固定根的完整二步纯载体紧及邻球族非退化连续）。** 在144.2的同一原域，令

$$
Q(a)=\bigcup_{x\in S_a}S_x,\qquad B_2(a)=\bigcup_{x\in S_a}D_x.
\tag{XI144.7}
$$

则 $Q(a)$ 是原 $K$ 中的紧纯集，$x\mapsto D_x$ 在整个固定 $S_a$ 上 Hausdorff 连续；任一固定辅助欧氏尺下，这个固定族的最小半轴有严格正的统一下界。

证明。由固定球缘的 $e_x$ 连续性、紧性及混点 $c_a$ 不在 $e_x$ 的一值面中，

$$
\delta_a:=\min_{x\in S_a}(1-e_x(c_a))>0.
\tag{XI144.8}
$$

对 $x\in S_a$，原点 $a$ 在 $S_x$ 上，将包含它的直径代入 $x$ 处的 ZC，得到

$$
\kappa_x=e_x(c_a)+e_x(c_{2c_x-a})\le1+e_x(c_a)\le2-\delta_a.
\tag{XI144.9}
$$

设 $x_n\in S_a$、$x_n\to x$、$p_n\in S_{x_n}$、$p_n\to z$。原上关联给 $z\in D_x$。反设 $z$ 混，144.2使反射 $p_n'=2c_{x_n}-p_n$ 趋于 $z'=2c_x-z$；两极限均在 $\operatorname{ri}D_x$。分别对这两个纯标签序列应用 IX118.4：其球的每个 Hausdorff 聚点只能是单点，标签单射及混极限所在球的唯一性迫该单点为 $x$。因此

$$
D_{p_n},D_{p_n'}\longrightarrow\{x\}.
\tag{XI144.10}
$$

结合 $e_{x_n}\to e_x$，在 $x_n$ 处的 ZC 给

$$
\kappa_{x_n}=e_{x_n}(c_{p_n})+e_{x_n}(c_{p_n'})\longrightarrow2,
\tag{XI144.11}
$$

违反(XI144.9)。所以 $z$ 必纯，进而 $z\in S_x$；任意 $Q(a)$ 序列都可如此再取子列，故 $Q(a)$ 紧而纯。

现取 $x_n\to x$ 于 $S_a$，在固定欧氏环境写 $D_{x_n}=b_n+A_n\overline B^3$，其中 $A_n$ 的列为正交半轴向量。参数有界；对任意子列再取参数极限 $b_n\to b$、$A_n\to A$，令 $G=b+A\overline B^3\subseteq D_x$。全部球缘的极限属于刚取得的紧纯集 $Q(a)$。若 $1\le\operatorname{rank}A\le2$，沿非零核补足单位长度可知 $A S^2=A\overline B^3$，使整个非点凸集 $G$ 都纯，矛盾。若 $\operatorname{rank}A=0$，中心连续给 $G=\{c_x\}$；每个 $D_{x_n}$ 都含 $a$，所以 $c_x=a$，也矛盾。故秩三。此时 $\partial_{\rm rel}G\subseteq P\cap D_x=S_x$，与 $G\subseteq D_x$ 一起迫 $G=D_x$：否则从 $G$ 内点向 $D_x$ 外部点走，得到落在 $\operatorname{ri}D_x$ 内的 $G$ 球缘点，同时纯与混。所有参数子列都给同一整球极限，故 Hausdorff 连续。

中心、形状算子及其正特征值连续，见139.4的支持函数式(XI139.14)。固定紧 $S_a$ 和恒秩三遂给最小半轴正下界。这里没有把各根的下界统一于全部 $P$。证毕。

### 144.3 上端预算的全域不塌缩桥

**定理 144.4（同一上端余量排除全部原球塌缩）。** 在定义144.1的完整 EB3+$\mathsf{Conn}$+$\mathsf{ZC}$ 域，若

$$
\exists\varepsilon>0\ \forall a\in P:\quad \kappa_a\le2-\varepsilon,
\tag{XI144.12}
$$

则 $\inf_{a\in P}\operatorname{diam}D_a>0$，因而由既有 IX118.8 的第二项到第四项，存在同原锥、同原单位的复三能级表示。$\varepsilon$ 在全部标签之前选定，不能替换为144.3的逐根 $\delta_a$。

证明。先排除纯标签的混极限。设 $a_n\to z\notin P$。IX118.4使所有整球聚点均为同一个 $\{q\}$，其中 $q\in P$、$z\in\operatorname{ri}D_q$；唯一性由不同原球不能交于混点及标签单射给出。若 $e_{a_n}\to h$ 于某子列，则 $h(z)=1,h(q)=0$。非负效应 $u-h$ 在 $D_q$ 的相对内点为零，故在整个 $D_q$ 为零，并在 $q$ 为一；(XI144.2)于是给

$$
e_{a_n}\longrightarrow g_q.
\tag{XI144.13}
$$

任选 $D_{a_n}$ 的一对对径 $x_n,x_n'$；两者都趋于 $q$。纯标签处上关联使 $c_{x_n},c_{x_n'}$ 的每个聚点都在 $D_q$，而 $g_q$ 在整个该球上为一。故 $\kappa_{a_n}\to2$，违反(XI144.12)。所以 $P$ 在紧 $K$ 中闭而紧。

反设尚有 $\operatorname{diam}D_{a_n}\to0$。取共同子列使

$$
a_n\to a\in P,\qquad D_{a_n}\longrightarrow\{q\},\qquad q\in P\cap D_a.
\tag{XI144.14}
$$

$q$ 的纯性来自球缘点极限和刚得的 $P$ 紧性。对任意选择 $x_n\in S_{a_n}$ 都有 $x_n\to q$、$a_n\in D_{x_n}$。其整球任意极限 $G$ 满足 $a\in G\subseteq D_q$。与144.3同样的有界椭球参数及纯球缘极限论证排除秩一、二；秩三迫 $G=D_q$，秩零迫 $G=\{a\}$。因此所有邻球极限只有

$$
G=\{a\}\quad\text{或}\quad G=D_q,
\qquad c_G=a\quad\text{或}\quad c_G=c_q.
\tag{XI144.15}
$$

每张 $S_{a_n}$ 上的中心映射由144.2连续，故其像连通。任选一对对径，从(XI144.12)至少选出一端 $x_n^0$ 使 $e_{a_n}(c_{x_n^0})\le1-\varepsilon/2$。因 $e_{a_n}(a)\to1$，这些中心不可能有趋于 $a$ 的子列；(XI144.15)遂使它们趋于 $c_q$。若还有其他中心趋于 $a$，连通像和距离到 $a$ 的中值定理将给第三种中心极限，例如到 $a$ 距离为 $\|c_q-a\|/2$，违反(XI144.15)。因此

$$
\sup_{x\in S_{a_n}}\|c_x-c_q\|\longrightarrow0,
\qquad D_{x_n}\longrightarrow D_q
\quad\text{对任意 }x_n\in S_{a_n}.
\tag{XI144.16}
$$

对后一列完整球选 $e_{x_n}$ 的任意聚点，整球收敛、$x_n\to q$ 和(XI144.2)迫该聚点为 $e_q$，故 $e_{x_n}\to e_q$。

选 $S_{a_n}$ 的任意一对对径 $x_n,z_n$。在该球坐标里令这对端点的坐标为 $s=\pm1$，写

$$
e_{x_n}|_{D_{a_n}}=1-\beta_n+\beta_n s,\qquad
e_{z_n}|_{D_{a_n}}=1-\gamma_n-\gamma_n s,
\qquad \beta_n,\gamma_n>0.
\tag{XI144.17}
$$

唯一一值面保证非恒定及正斜率。两效应及 $g_{a_n}$ 都在 $L_{a_n}$；消去球上斜率，使用 $R_{a_n}$ 单射，得到整个 $V^*$ 上的既有双球恒等式 IX120.24：

$$
\gamma_ne_{x_n}+\beta_ne_{z_n}
=(\beta_n+\gamma_n-2\beta_n\gamma_n)g_{a_n}.
\tag{XI144.18}
$$

参数对应为 $\beta_n=(1+\rho_+)^{-1}$、$\gamma_n=(1+\rho_-)^{-1}$；不使用正限制逆。固定辅助范数并令 $M=\max_{f\in\mathcal E}\|f\|_*<\infty$。整球振幅给

$$
2\beta_n,\ 2\gamma_n\le M\operatorname{diam}D_{a_n}\longrightarrow0.
\tag{XI144.19}
$$

将(XI144.18)除以 $\beta_n+\gamma_n$。左端是两个均趋于 $e_q$ 的原效应的凸组合，右端是 $(1-t_n)g_{a_n}$，其中

$$
t_n=\frac{2\beta_n\gamma_n}{\beta_n+\gamma_n}
\le\frac{\beta_n+\gamma_n}{2}\longrightarrow0.
\tag{XI144.20}
$$

无需控制两个正系数的比值，就有 $g_{a_n}\to e_q$、$e_{a_n}\to g_q$。结合(XI144.16)，ZC 再给 $\kappa_{a_n}\to2g_q(c_q)=2$，矛盾。全部塌缩被排除。此后才消费 IX118.8；分类本身不是本章的新定理。证毕。

### 144.4 完整静态候选、几何及未证连接

**条件应用 144.5（不指定数值的全域同值候选）。** 在(XI144.1)的全部原量词下，EB3+$\mathsf{Conn}$+$\mathsf{UC}$ 等价于存在实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V,
\qquad\Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{XI144.21}
$$

此时同值候选中的共同数必为 $\kappa=1$。

证明。UC 给 ZC。任取一个原纯点，144.2给共同数 $\kappa<2$；所以同一个 $\varepsilon=2-\kappa>0$ 已在全部标签之前选定。144.4直接取得(XI144.21)。反向在整个标准 qutrit 域，原效应为全部 $0\preceq M\preceq I_3$，$e_p(\rho)=\operatorname{Tr}(p\rho)$，$c_p=(I_3-p)/2$。若 $x\in S_a$，则 $\operatorname{Tr}(ax)=0$，故 $e_a(c_x)=1/2$，UC 取 $\kappa=1$；完整 EB3 和 Conn 的全域反向复用142.2。通过同一 $\Phi$ 运输即得全部原对象的结论。证毕。

同一个表示直接消费142.3的完整静态字典：原 $\dim_{\mathbb R}V=9$，全部态是整个迹一正三阶矩阵，全部纯域为 $\mathbb{CP}^2$，完整排除球的球缘为 $\mathbb{CP}^1\cong S^2$；原全部效应和数学有限 POVM、原完整非单点确认菜单、least 及每个混态的 Born minimum $T_{p_v}(\Phi\rho)=v^*\rho v$、谱分解、自对偶与 Jordan 结构全部沿同一个 $\Phi$ 取得。球心图为 $R(x)=(u(x)U-x)/2$，$U=\Phi(I_3)$。相对于总体中心态 $U/3$，它是反向缩小一半。

实际来源与读回、全部质量、全有限复合及纠缠、实际事件和仪器、全旁观 CP、逐输入预算、记录、所有未来与切口，以及物理钟、Hamiltonian、能量标定和数值 $\hbar$，逐项保留142.4及其传递来源的完整原合同。静态表示不供应这些物理实现。比较端点互易指原最低确认的 $T_p(q)=T_q(p)$；UC 约束球心替换后的同一原尺读数，两者均不表示任意连续测量的先后次序可交换。

**命题 144.6（未取得统一余量时的准确退化条件）。** 仅在 EB3+$\mathsf{Conn}$+$\mathsf{ZC}$ 下，若(XI144.21)不成立，则

$$
\sup_{a\in P}\kappa_a=2.
\tag{XI144.22}
$$

并且对所有原 $a$，

$$
B_2(a)\subseteq\{z\in K:e_a(z)\ge\max(0,2\kappa_a-3)\}.
\tag{XI144.23}
$$

证明。若上确界小于二，144.4即给表示，故反设推出(XI144.22)。对 $x\in S_a$，ZC 和另一项小于一给 $e_a(c_x)\ge\kappa_a-1$。$e_a$ 在 $D_x$ 上唯一最大点为 $a$，最小值为 $2e_a(c_x)-1$，所以每个 $z\in D_x$ 都有 $e_a(z)\ge2\kappa_a-3$；再用原非负性，取全部球的并即得(XI144.23)。证毕。

这只限制任何反模型的必要行为，不构造反模型，也不证明该行为不可能。尤其沿 $\kappa_{a_n}\to2$，同一把原尺在完整一步球 $D_{a_n}$ 上恒零，却在整个二步混态载体 $B_2(a_n)$ 上一致趋于一。144.3的紧 $Q(a)$ 和逐根正余量并未排除这条序列；它们也未证明任何 $Q(a)$ 含根在整个 $P$ 中的邻域。因此142.2的 $\mathsf G(o)$、ZC 到 Seed、以及裸 EB3 或纯比较互易到 UC 的连接仍未在此得到。

**约定 144.7（归属与白话关系）。** 本章采用仓内综合推导归属，不主张全球新颖性。新增承重桥是：ZC 将固定球面上球心读数的下半连续性变成向量连续性；逐根反向余量排除二步纯载体的混极限；全域统一上端余量先取得纯点紧性，再以整张球面的连通中心像同步邻球退化，最后用已存在的双球恒等式排除塌缩。原面论、法向限制、效应消去、同原不塌缩分类及全静态字典按所引来源复用。UC 到量子表示是这一新桥的条件应用，不另算新分类，也未证明相对143.4的独立假设更少或逻辑严格更弱。

成熟文献的适用条件仍须保留：[Barnum—Müller—Ududec，Theorem 16][Q144BMU]要求 projectivity、对称跃迁概率及保纯滤子，本章不在局部阶段预付它们。有限维紧性、椭球参数极限、仿射球上的唯一极值及连通集的中值性质只是中间工具。一般紧性没有把逐点严格上界自动升级为全域统一上界；本章144.4专门支付后者到不塌缩的推导。

白话上，每个纯态背后有一整颗排除三球。取球上一条直径，把两端各换成它自己那颗球的球心，再用原标签那把“自己读一、整颗排除球读零”的尺去读。本候选要求两端读数的平均不随直径，也不随原标签改变，却不先指定平均是多少。每一项都小于一，共同平均便与一保持同一个正距离。若有排除球不断缩成一点，它旁边整片连续的球心就只能一起落到两种位置；原全效应的双球关系迫使这把尺在二步载体上接近读一，违反那一点共同余量。因此球不能塌缩，既有分类给同一个完整复三能级量子态体，平均也随之锁到二分之一。若只要求每颗球各自不随直径改变，跨球的共同余量仍未证明；这正是局部一致与整体一致之间尚缺的关系。

[Q144TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.2：完整EB3+Conn到Inj、P=P0、全部原四维法向及限制同构的复用组合。"
[Q144IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX118.3式(IX118.4)纯标签上关联；118.4混标签极限判据；118.8第二项到第四项同原不塌缩分类；120.2、120.8、120.12全部原零面、一值面、线性限制及固定球缘效应连续性；120.15式(IX120.24)整个原双球效应恒等式。"
[Q144BMU]: https://arxiv.org/html/1403.4147v4#Thmtheorem16 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory, Theorem 16；前件包含projectivity、对称跃迁概率和保纯滤子。"

## 追加锚（本行以下为增补区）

## 145. 有限法向转移、九维同根纯芽与完整原域复三能级

### 145.1 原对象、维数输入与结论

**定义 145.1（完整原域）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，及在 $C\setminus\{0\}$ 上严格正的 $u\in V^*$。始终使用

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
C^*=\{h\in V^*:h(C)\subseteq\mathbb R_+\},\qquad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p,\\
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\qquad
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p,\qquad
\mathcal B(p)=\mathcal E\cap N_p,\qquad
P_0=\{p\in P:\mathcal A_p\text{ 为单点}\}.
\end{gathered}
\tag{XI145.1}
$$

$K$ 是整个紧基且张成 $V$，$P$ 是全部原纯标签。完整效应区间紧，$\mathcal F_p$ 非空紧，故 minimum 对**每个**原混输入 $x\in K$ 都达到。$\mathcal A_p$ 是整球暴露确认族，$\mathcal B(p)$ 是完整零效应菜单；两者都不替代 $\mathcal F_p$。不预设 $T_p$ 仿射、least 或确认菜单单点。

EB3 指每个原 $p\in P$ 的**整个** $D_p$ 都仿射等价于非退化闭三球。纯关系 $p\perp q\Longleftrightarrow q\in S_p$ 由原补效应对称，且反自反。$\mathsf{Inj}$ 指 $D_p=D_q\Rightarrow p=q$。$\mathsf{Conn}$ 准确指任意两个原纯点之间存在有限条原零边组成的路径，允许相同端点的零长路，长度可依端点改变。

对原根 $r\in P$ 定义

$$
Q(r)=\bigcup_{s\in S_r}S_s,\qquad
\mathsf G(r):\quad \exists W\subset V\text{ 开},\quad r\in W,\quad W\cap P\subseteq Q(r).
\tag{XI145.2}
$$

二步见证同时承担 $r\perp s\perp x$，允许回走。$\mathsf G(r)$ 要求邻域以这个**同一根**为中心。

**定理 145.2（九维原域的根芽与静态表示）。** 在定义145.1的完整原域中，以下三项等价：

1. $\mathrm{EB3}+\mathsf{Conn}+\dim_{\mathbb R}V=9$；
2. $\mathrm{EB3}+\mathsf{Inj}+\dim_{\mathbb R}V=9$；
3. 存在同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\operatorname{PSD}_3(\mathbb C))=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI145.3}
$$

在第1或第2项下，先于分类就存在一个实际原 $o\in P$ 满足 $\mathsf G(o)$。对这个同一根，随后有整个

$$
P=Q(o)=\Lambda_o,\qquad
\Lambda_o=\{a\in P:S_a\subseteq Q(o)\},\qquad
\bigcup_{x\in Q(o)}D_x=\partial_{\operatorname{aff}K}K,
\qquad \operatorname{conv}Q(o)=K.
\tag{XI145.4}
$$

全部不同纯对有唯一共同原纯零邻点；相同端点也有实际共同邻点。取得表示后每个原根都满足 $Q(r)=P$。第1项到表示直接消费142.2；第2项使用145.8证明的充分接口版，不把一个写有 Conn 的定理无条件扩大适用域。

这里 $\dim_{\mathbb R}V=9$ 是对**整个原空间**另给的输入，故 $\dim_{\rm aff}K=8$。它不来自先要求 $\mathsf G$ 的137、139或141。EB3+Inj 的独立下界 $\dim_{\mathbb R}V\ge9$ 已由 [THREE_COPY VII121.9][Q145TVII]取得，此处直接消费该结论而不重证；本章新增内容不包括该下界，也不包括无维数前件的自动九维上界。

### 145.2 精确复用的面、法向与完整法向基

**接口 145.3（全部原标签）。** 第1项由 [THREE_COPY VIII130.2][Q145TVIII]得到 Inj、$P=P_0$；第2项则由 [BILATERAL VIII121.6][Q145B]在 EB3+Inj+九维域得到 $P=P_0$。两条入口均对**所有** $p\in P$ 支付以下同一接口：

$$
\begin{gathered}
\mathcal A_p=\{e_p\},\qquad g_p=u-e_p,\qquad \dim L_p=4,\\
N_{D_p}:=\{h\in C^*:h|_{D_p}=0\}=\mathbb R_+e_p,\qquad
K\cap\{e_p=0\}=D_p,\qquad K\cap\{e_p=1\}=\{p\},\\
R_p:L_p\overset\sim\longrightarrow\operatorname{Aff}(D_p),\quad h\longmapsto h|_{D_p},
\qquad g_p\in\operatorname{ri}N_p,\qquad K\cap\{g_p=0\}=\{p\}.
\end{gathered}
\tag{XI145.5}
$$

限制同构与相对内部事实准确取自 [IX120.7—120.8][Q145IX]；维数、暴露射线公式取自 IX119.10。没有在此给 $R_p^{-1}$ 正性。完整面接口取 [XI137.2及其 VII103.2、IX116.1—116.2 来源][Q145XI]：每个 $D_p$ 为非点紧暴露极大真面；全部非空真面只有纯单点和完整排除球；$S_p=\partial_{\rm rel}D_p\cong S^2$、$D_p=\operatorname{conv}S_p$；不同球至多交一个原纯点。特别地，混边界点有唯一最小面 $D_a$，并在其相对内部；在该点为零的全部原正法向恰为 $N_{D_a}=\mathbb R_+e_a$。这些事实不输入全 Pair。

以下三个供应直接引用，不重新推导其源证明。

* [IX120.2][Q145IX]在完整原域给

$$
\max_Kh=\max_{D_p}h\qquad(h\in N_p).
\tag{XI145.6}
$$

* [IX120.11—120.12][Q145IX]给固定**整张**原球面上的 Lipschitz 效应及准确原边区间。具体地，写 $D_p=c_p+B_p\overline{\mathbb B}^3$、$s(t)=c_p+B_pt$，其中 $B_p$ 单射；取 $H_i\in L_p$ 满足 $H(c_p+B_pw)=w$。则有限 Lipschitz 方向函数及原泛函公式为

$$
\begin{gathered}
\rho_p(v)=\sup_{x\in K\setminus\{p\}}\frac{-v\cdot H(x)}{g_p(x)},\qquad
\rho_p(v)\ge\|v\|,\\
e_{s(t)}=\frac{\rho_p(t)g_p+t\cdot H}{1+\rho_p(t)},\qquad
\{b\in\mathcal E:b(p)=0,b(s(t))=1\}=[g_p,e_{s(t)}]\quad(t\in S^2).
\end{gathered}
\tag{XI145.7}
$$

这是整个原 $V$ 上的效应公式与完整区间；只支付固定 $S_p$ 上的连续性，不宣称此时全 $P$ 上连续。

* [THREE_COPY VII122.2—122.5][Q145TVII]的前件是 EB3+Inj、一个 $p\in P_0$。由(XI145.5)，它对每个原 $p$ 适用：$N_p$ 在四维 $L_p$ 中闭、尖、满维、严格凸，其每条非零边界射线恰为某个 $\mathbb R_+e_s$、$s\in S_p$，且是暴露极射线。

固定一次 $z\in\operatorname{ri}K$。它也是 $C$ 的内点，故每个非零 $h\in C^*$ 都有 $h(z)>0$。取辅助欧氏单位球，在 $z$ 周围有 $z+\delta\overline B_V\subset C$，于是 $h(z)\ge\delta\|h\|$ 对所有 $h\in C^*$ 成立。记

$$
\widehat h=h/h(z),\qquad B_p^*=\{h\in N_p:h(z)=1\}.
\tag{XI145.8}
$$

$B_p^*$ 是非空紧凸基。其极点恰对应 $N_p$ 的极射线；上述**全部**边界射线描述给出全部极点 $\widehat e_s$。有限维紧凸集的极点生成定理因而准确给

$$
\boxed{B_p^*=\operatorname{conv}\{\widehat e_s:s\in S_p\}.}
\tag{XI145.9}
$$

这里 conv 是有限凸组合，不需另取闭包：基的仿射维数为三，Carathéodory 定理使每项至多需四个极点；固定球面的效应连续性又使生成集合紧。此为既有完整射线描述的接口应用，不是新的球面效应连续性证明。尤其 $\widehat g_p\in B_p^*$ 也在这同一完整基中。

### 145.3 有限正法向转移到整个原球

**引理 145.4（有限见证的整球转移）。** 设接口145.3成立，$p_i,p\in P$、$p_i\to p$。若存在同一有限指标集 $1\le\ell\le m$，使

$$
h_i^\ell\in N_{p_i},\qquad h_i^\ell\longrightarrow h^\ell,
\qquad \operatorname{span}\{h^1,\ldots,h^m\}=L_p,
\tag{XI145.10}
$$

则 $D_{p_i}\to D_p$ 于 Hausdorff 距离，且 $e_{p_i}\to e_p$ 于原效应空间。这里正法向允许零元；去掉零极限项不影响张成条件。

证明。取任意子列。在 $H_0=\ker u$ 中逐球作有界半轴选择，写

$$
D_{p_i}=c_i+B_i\overline{\mathbb B}^3,
\qquad c_i\in K,\qquad B_i:\mathbb R^3\to H_0\text{ 单射},\qquad
\|B_i\|\le\tfrac12\operatorname{diam}K.
\tag{XI145.11}
$$

界来自 $c_i\pm B_it\in K$ 对所有单位 $t$ 成立，不假设这些选择连续。中心、矩阵和原效应都在有限维有界紧集内，故可共同再取子列使 $c_i\to c$、$B_i\to B$、$e_{p_i}\to e\in\mathcal E$。统一参数球上的一致收敛给实际椭球极限

$$
E=c+B\overline{\mathbb B}^3,\qquad D_{p_i}\to E,\qquad
e(p)=1,\quad e|_E=0,\quad E\subseteq D_p.
\tag{XI145.12}
$$

最后一个包含只用同一 $e\in\mathcal F_p$ 的原零见证，不先断言 $e=e_p$。$B$ 的秩暂时可以小于三。

正锥和评价的闭性给 $h^\ell\in N_p$。任给固定 $a_\ell\ge0$，置 $h_i=\sum_\ell a_\ell h_i^\ell$、$h=\sum_\ell a_\ell h^\ell$。由(XI145.6)，

$$
\max_{D_{p_i}}h_i=\max_Kh_i
\quad\Longrightarrow\quad
\max_Eh=\max_Kh=\max_{D_p}h.
\tag{XI145.13}
$$

此极限同时使用 $h_i\to h$ 在紧 $K$ 上一致，以及实际整球的 Hausdorff 收敛。同一有限见证和同一参数子列已使该式对所有固定非负系数成立，不逐个法向更换极限球或子列。

锥 $\mathcal H=\operatorname{cone}\{h^\ell\}$ 在四维 $L_p$ 中有非空内部：从张成族中选四个线性无关元，其严格正组合已给四维开集。通过已付线性同构 $R_p$，再取仿射函数的三维线性部分，是满射线性映射，所以该内部的线性部分像含一个三维非空开集。可在其中取避开零的开球；其单位方向含 $S^2$ 的非空开片。

把 $D_p$ 化为 $c_p+B_p\overline{\mathbb B}^3$。非零线性部分 $v$ 的唯一最大点是 $c_p+B_pv/\|v\|$。由 $E\subseteq D_p$ 和(XI145.13)，这个**同一**最大点必在 $E$ 中。因此 $E$ 含 $S_p$ 的一块非空球面开片。秩至多二的 $B$ 不可能包含这种片：一个真仿射平面若包含球面开片，其非零仿射方程在该片消失，经球面一次多项式唯一性便在整个球面消失，矛盾。故 $\operatorname{rank}B=3$。

此时 $E,D_p$ 有同一仿射三平面。上述最大点也在 $\partial_{\rm rel}E$，因为相同非零线性部分在 $E$ 上支持。两椭球边界共享非空球面开片，[XI137.6的二次曲面唯一性][Q145XI]遂给 $E=D_p$。该初等工具只用二次方程在球面开片的消失，不消费137的根芽前件。于是 $e\in\mathcal A_p=\{e_p\}$。

对任意起始子列，全部有界参数都能再取上述子列，且再极限只能是 $D_p,e_p$。若任一整列结论失败，就能选距所称极限有固定正下界的子列，与此矛盾。引理得证。没有假设任意原面族的集合值连续性。

### 145.4 原紧法向层中的实际四维纯开片

**引理 145.5（先有全纯域开图，再固定最终根）。** 在接口145.3及 $\dim V=9$ 下，存在非空 $P$-开集 $A$，以原子空间拓扑同胚于 $\mathbb R^4$ 的开集；$p\mapsto e_p$ 在一个包含 $A$ 的 $P$-开集 $O$ 上连续。可固定 $o\in A$ 及一个紧四维坐标闭球 $T\subset A$，使 $o\in\operatorname{int}_P T$，并有环境开集 $W_0\ni o$ 满足

$$
W_0\cap P\subseteq T\subset P,\qquad \overline{W_0\cap P}^{\,V}\subseteq T.
\tag{XI145.14}
$$

证明。原仿射空间 $A_K=\{u=1\}$ 的方向空间 $H_0$ 为八维。按 [SAME_READBACK128.3][Q145SR]的准确识别，

$$
N_p\overset\sim\longrightarrow\widehat N_K(p),\quad h\longmapsto-h|_{H_0},\qquad
h_{x,v}(y)=-\langle v,y-u(y)x\rangle
\tag{XI145.15}
$$

分别是原正法向到外法向的锥同构和反向补常数公式。故每个原纯点的外法向张成恰四维。

对同一原八维凸体应用 [SAME_READBACK128.2，证明式(Q128.6)—(Q128.8)][Q145SR]，取 $k=4$。复用其可数紧层 $X_j\subset\partial_{A_K}K$，覆盖全部 $P$；每层有到四维空间的连续正交投影 $\pi_j$，在整个 $X_j$ 上单射。保留源构造中的同一有限配置：有固定 $b_0,b_1,\ldots,b_4$、正 $\varepsilon$ 和 $E_j=\operatorname{span}\{b_1,\ldots,b_4\}$，使每个 $x\in X_j$ 有八个共同有界见证

$$
v_x^{\ell\pm}\in\widehat N_K(x)\cap
\overline B(b_0\pm b_\ell,\varepsilon),\quad 1\le\ell\le4,
\qquad \frac{2\varepsilon}{\sigma}<\frac12.
\tag{XI145.16}
$$

这里 $\sigma$ 正是源构造中 $E_j\to\mathbb R^4$、$v\mapsto(\langle b_\ell,v\rangle)_\ell$ 的最小奇异值；因此也有 $\|\sum_\ell t_\ell b_\ell\|\ge\sigma\|t\|$。它们是互为伴随的满秩矩阵的相同非零奇异值。

现令 $p_i\to p$ 于 $P\cap X_j$。把八个见证一起放进八个固定紧球，任意子列可共同再取 $v_i^{\ell\pm}\to v^{\ell\pm}\in\widehat N_K(p)$。令 $d_\ell=(v^{\ell+}-v^{\ell-})/2$。则 $\|d_\ell-b_\ell\|\le\varepsilon$，且

$$
\left\|\sum_\ell t_\ell d_\ell\right\|
\ge(\sigma-2\varepsilon)\|t\|>0\quad(t\ne0).
\tag{XI145.17}
$$

四个差仍独立，故八个极限法向张满四维 $\operatorname{span}\widehat N_K(p)$。用(XI145.15)对同一 $p_i$ 补回原法向，得到八个 $h_i^{\ell\pm}\in N_{p_i}$ 及收敛极限；同构使其极限张满 $L_p$。引理145.4正好适用。再以任意子列的再子列论证，得

$$
p\longmapsto(D_p,e_p)\quad\text{在每个 }P\cap X_j\text{ 上连续}.
\tag{XI145.18}
$$

这里不宣称整层都纯，也没有把几乎处处覆盖代替八个实际见证。

[THREE_COPY VII121.5][Q145TVII]给原纯域的准确 $G_\delta$ 描述：

$$
K\setminus P=\bigcup_{m\ge1}M_m,\qquad
M_m=\{(x+y)/2:x,y\in K,\ \|x-y\|\ge1/m\},
\tag{XI145.19}
$$

每个 $M_m$ 是紧中点像。因此 $P$ 是紧度量 $K$ 的 $G_\delta$ 子空间，为 Polish 空间并具有 Baire 性；这不等于 $P$ 闭。$P\cap X_j$ 是可数个相对闭覆盖，故某个

$$
O=\operatorname{int}_P(P\cap X_j)\ne\varnothing.
\tag{XI145.20}
$$

由(XI145.18)，整球及效应在 $O$ 上连续。

取 $a\in O$。按 [BILATERAL VIII121.2—121.5][Q145B]，在同一实际 $S_a$ 中有一张闭二盘 $B_0$，其内部非空，$q\mapsto D_q$ 在该盘上连续。其源证明只需 EB3+Inj，九点秩、第二层见证和 Baire 的作用域均是这张实际球面盘。取 $q_0\in\operatorname{int}B_0$；源121.5给其附近连续局部参数

$$
D_q=b(q)+L(q)\overline{\mathbb B}^3,\qquad
S_q=b(q)+L(q)S^2,\qquad \operatorname{rank}L(q)=3.
\tag{XI145.21}
$$

所有这些 $S_q$ 都含**同一** $a$。以下将已有四维块精化到 $O$：写 $O=P\cap W_O$，其中 $W_O$ 环境开且含 $a$。在 $S_{q_0}\setminus\{a\}$ 取任意充分靠近 $a$ 的 $r_0\in W_O$；在其参数附近取小紧二帽，使整个 $q_0$ 像在 $W_O$ 且避开 $a$。联合连续性和帽的紧性允许同时缩小同一底盘到 $B_1\ni q_0$，使整张乘积像都在 $W_O$ 且避开 $a$。底盘与帽各取闭方盘，便有

$$
\Psi:[0,1]^4\longrightarrow O,\qquad
\Psi(q,t)=b(q)+L(q)t,\qquad a\perp q\perp\Psi(q,t).
\tag{XI145.22}
$$

固定 $q$ 时单射来自 $L(q)$；不同底标签的完整球都含 $a$，Inj及点交规则使其交恰为 $\{a\}$，而全部帽避开它，故跨标签也单射。紧源使 $\Psi$ 为到像的同胚。

现在才使用八维环境减四维法向所得的**四维**投影。$\pi_j\Psi$ 在 $(0,1)^4$ 上是到 $\mathbb R^4$ 的连续单射；[Hatcher Theorem 2B.3][Q145Ha]的区域不变性使

$$
\Omega=\pi_j\Psi((0,1)^4)\text{ 在 }\mathbb R^4\text{ 中开},\qquad
A:=\Psi((0,1)^4)=O\cap\pi_j^{-1}(\Omega).
\tag{XI145.23}
$$

第二个等式用**同一** $X_j$ 上投影的单射性。因此 $A$ 相对于**全部原 $P$** 开，是真实四维流形图，非仅嵌入原空间的四维块。

固定最终根 $o=\Psi(1/2,1/2,1/2,1/2)$。选包含它于坐标内部的紧四维闭球 $T\subset A$。因 $\operatorname{int}_P T$ 含 $o$，可取环境开 $W_0\ni o$ 使 $W_0\cap P\subset T$。$T$ 紧而在 $V$ 中闭，遂得(XI145.14)。尤其落在 $W_0$ 内的纯点极限仍纯。由于 $O$ 是 $P$-开集，(XI145.18)同时给：任何原纯点趋向这个 $o$ 时，其 $e_p$ 趋向 $e_o$。

最初立方体的像在 $Q(a)$ 中；本证明没有据此声称 $\mathsf G(a)$，也没有据 $o\in\operatorname{int}_P Q(a)$ 声称 $\mathsf G(o)$。对最终根的整族论证如下。证毕。

### 145.5 整个同根球族的二分与塌缩排除

**引理 145.6（全部 $S_o$ 上的整球连续）。** 固定引理145.5选出的同一个 $o$。则 $s\mapsto D_s$ 在整个紧球面 $S_o$ 上 Hausdorff 连续，球心、秩三形状算子及方向空间随之连续。

证明。设 $s_i\to s$ 于 $S_o$。每个 $D_{s_i}$ 都含同一个 $o$。按(XI145.11)作有界参数选择；任意子列可再取

$$
D_{s_i}=c_i+B_i\overline{\mathbb B}^3\longrightarrow
E=c+B\overline{\mathbb B}^3,\qquad o\in E\subseteq D_s.
\tag{XI145.24}
$$

包含由原紧效应见证给出；这里也可直接用(XI145.7)在固定 $S_o$ 上的 $e_{s_i}\to e_s$。没有在未知连续域上使用引理145.4。

先证极限只有两种：

$$
E=D_s\quad\text{或}\quad E=\{o\}.
\tag{XI145.25}
$$

若 $\operatorname{rank}B<3$，非零核使 $B S^2=B\overline{\mathbb B}^3$：将任一参数先正交投影到核的正交补，再沿核方向补到单位长度，不改其像。故每个 $x\in E$ 都能写成 $c+Bt$、$\|t\|=1$，是实际原纯点 $c_i+B_it\in S_{s_i}$ 的极限。对 $x\in E\cap W_0$，这些点最终在 $W_0$，由(XI145.14)得 $x\in P$。若 $E$ 另含 $y\ne o$，则充分靠近 $o$ 的开线段点 $(1-t)o+ty$ 在 $E\cap W_0$，却是两个不同 $K$ 点的严格混合，不能原纯，矛盾。因此此分支只能 $E=\{o\}$。

若 $\operatorname{rank}B=3$，$E,D_s$ 有同一仿射三平面。$o$ 原纯且在 $E\subset K$，故 $o\in\partial_{\rm rel}E$。其边界在 $W_0$ 中有非空相对开片；片上每点仍是 $c_i+B_it$、$\|t\|=1$ 的极限，由局部纯闭性属于 $P\cap D_s=S_s$。两椭球边界因而共享 $\partial E$ 的开片，二次唯一性给 $E=D_s$。此处只需根附近的纯闭性，不需全 $P$ 闭。

余下排除 $E=\{o\}$。反设沿该共同子列 $D_{s_i}\to\{o\}$。全部边界同时进入 $o$ 的原纯邻域；由引理145.5在 $o$ 的全纯域效应连续性以及 $e_o(z)>0$，归一映射在 $e_o$ 附近连续，故

$$
\sup_{r\in S_{s_i}}\|\widehat e_r-\widehat e_o\|\longrightarrow0.
\tag{XI145.26}
$$

准确的全边界量词可由反证看出：若上确界不趋零，选相应 $r_i\in S_{s_i}$；整球塌缩给 $r_i\to o$，从而 $e_{r_i}\to e_o$，且分母 $e_{r_i}(z)$ 最终至少 $e_o(z)/2$，矛盾。

(XI145.9)是**整个**原法向基的生成，故(XI145.26)给

$$
\sup_{b\in B_{s_i}^*}\|b-\widehat e_o\|\longrightarrow0.
\tag{XI145.27}
$$

所有凸组合都满足同一误差界，且各基非空；这不是只让有限预选效应趋同。同时 $\widehat g_{s_i}\in B_{s_i}^*$。固定 $S_o$ 上的效应连续性给 $g_{s_i}\to g_s$；原 $z$ 为内点且 $g_s\ne0$，故 $g_s(z)>0$，归一后仍收敛。于是

$$
\widehat g_s=\widehat e_o.
\tag{XI145.28}
$$

在同一个 $o$ 评价：$s\in S_o$ 给 $o\in D_s$，所以 $g_s(o)=1$，而 $e_o(o)=1$。比例常数只能为一，故 $g_s=e_o$。但 $g_s$ 在非退化整个 $D_s$ 上为一，$e_o$ 的整个一值面却只有 $\{o\}$，矛盾。塌缩分支排除。

任意子列的再极限均为 $D_s$，所以整列收敛。由 [BILATERAL VIII121.5式(121.12)—(121.13)][Q145B]的支持函数参数工具，连续整球确定连续中心和连续秩三形状算子；常秩下像空间、局部标架、伪逆及其平方根连续。它们是有限维椭球参数的既有工具，入口的全 $S_o$ 非塌缩在这里已经支付。证毕。

### 145.6 同一个根的真实球束与邻域饱和

**定理 145.7（实际同根芽）。** 接口145.3及九维输入推出引理145.5所选同一个 $o$ 的 $\mathsf G(o)$。

证明。以同一辅助内积在 $H_0$ 中写引理145.6的连续椭球族为

$$
D_s=c_s+A_s^{1/2}\overline B_{H_0},\qquad
A_s\ge0,\quad \operatorname{rank}A_s=3,\quad Z_s=\operatorname{im}A_s,
\qquad w_s=A_s^{\dagger/2}(o-c_s)\in Z_s,\quad\|w_s\|=1.
\tag{XI145.29}
$$

$A_s^{\dagger/2}$ 为伪逆的非负平方根；$o$ 在每个 $S_s$，故最后一个范数为一。连续秩三像投影给 $Z_s$ 的局部正交标架，$w_s$ 为连续单位截面。于是实际关联空间

$$
\mathscr S_o=\{(s,r):s\in S_o,\ r\in S_s\},\qquad
\mathscr S_o^\times=\mathscr S_o\setminus\{(s,o):s\in S_o\}
\tag{XI145.30}
$$

为真实 $S^2$ 丛及删去公共根截面后的丛。具体地，$Z_s\cap w_s^\perp$ 是连续秩二平面丛；对其 $v$ 定义

$$
Y_s(v)=\frac{2v+(\|v\|^2-1)w_s}{1+\|v\|^2},\qquad
(s,v)\longmapsto(s,c_s+A_s^{1/2}Y_s(v)).
\tag{XI145.31}
$$

这逐纤维是整个 $\mathbb R^2$ 到 $S_s\setminus\{o\}$ 的球极投影逆。其逆由 $y=A_s^{\dagger/2}(r-c_s)$ 和
$v=(y-\langle y,w_s\rangle w_s)/(1-\langle y,w_s\rangle)$ 给出；$r\ne o$ 保证分母正，全部项连续。此为 [XI139.5][Q145XI]中同一参数工具的应用，这里已由引理145.6独立支付其连续整球入口。因此 $\mathscr S_o^\times$ 以原关联子空间拓扑是无边界四维流形：底是 $S_o\cong S^2$，纤维是 $\mathbb R^2$。各空间 Hausdorff、第二可数。

$\mathscr S_o$ 紧。事实上它在紧 $S_o\times K$ 中闭：若 $s_i\to s$、$r_i\in S_{s_i}$、$r_i\to r$，写 $r_i=c_{s_i}+A_{s_i}^{1/2}y_i$，其中 $y_i\in Z_{s_i}$、$\|y_i\|=1$；取单位向量子列极限，用像投影连续得 $y\in Z_s$、$\|y\|=1$，所以 $r\in S_s$。此处不以未知闭性的 $P$ 取交来证明紧性。故其连续像 $Q(o)$ 在 $V$ 中紧而闭。

评价映射

$$
\operatorname{ev}:\mathscr S_o^\times\longrightarrow P\setminus\{o\},\qquad(s,r)\longmapsto r
\tag{XI145.32}
$$

连续且单射：不同 $s,t\in S_o$ 的完整球都含 $o$，Inj和点交规则使 $D_s\cap D_t=\{o\}$。限制到 $\operatorname{ev}^{-1}(A\setminus\{o\})$，其源是四维流形的开子空间，目标是引理145.5已付的**全部纯域中的实际开图** $A\setminus\{o\}$。在两端坐标中用 Hatcher Theorem 2B.3，得到

$$
Q(o)\cap(A\setminus\{o\})\quad\text{在 }A\setminus\{o\}\text{ 中开}.
\tag{XI145.33}
$$

在这个同一 $A$ 中取以同一 $o$ 为坐标中心的小四维开球 $U$。$U\setminus\{o\}$ 连通；$Q(o)\cap(U\setminus\{o\})$ 由(XI145.33)开，由紧 $Q(o)$ 闭。它非空：任取 $s\in S_o$，完整球面 $S_s$ 在 $o$ 有其他原纯点趋近 $o$，最终进入 $P$-开集 $U$。开闭性遂给 $U\setminus\{o\}\subset Q(o)$。又 $o\in Q(o)$，故 $U\subset Q(o)$。

$U$ 相对于全部 $P$ 开，存在环境开 $W\ni o$ 使 $W\cap P=U$。这正是(XI145.2)的 $\mathsf G(o)$，整个论证没有再换根。相同目标 $x=o$ 由任意 $s\in S_o$ 的回走见证，亦已包括。证毕。

对定理145.2第1项，130.2已供应接口145.3，145.4—145.7已取得实际根芽；现在直接应用**原前件完整满足的**142.2，得到(XI145.4)与(XI145.3)。以下给第2项所需的精确接口迁移。

### 145.7 Conn 的付清替换与整个标准反向

**命题 145.8（142的充分接口版）。** 在定义145.1的完整原域中，若 EB3、Inj、$P=P_0$、$\dim V=9$ 及一个固定原根的 $\mathsf G(o)$ 成立，则142.2的全部几何结论和同锥同单位表示成立。

证明。先用 EB3+Inj 的原面分类，以及 IX119.10、120.2、120.7—120.8，由 $P=P_0$ 取得(XI145.5)的每项。这里给出所消费源证明的充分接口对应；只迁移列明的结论，不迁移另需 Conn 的距离三分支。

| 被消费的源段落 | 在本命题中的实际前件与推导对应 |
| --- | --- |
| 137.2 | Conn 原先只供应 Inj 与全部 $P=P_0$；本命题已逐项给出，并经上述 IX 接口得到全部四维法向、唯一零点、限制同构及相对内部。 |
| 137.4—137.6 | 同一紧 $S_o,K,\mathcal E$ 给 $B_2$ 紧投影及实际域上唯一关联的连续性；Inj和点交给单射。$\mathsf G(o)$ 给所需完整原球面开片，二维区域不变性给法向边界覆盖；正分母射影椭球及二次唯一性给137.3第1、2项。没有一步需要有限路径。 |
| 137.7—137.8 | 上一行的整球射影像给两张完整球面间的全域关联，紧图及点交给连续单射，二维满射给近根的完整 $Q(q)=Q(o)$。三个不共球的近根纯点及三个紧全态二步带排除混极限，给紧纯 $Q$。因此137.3第3、4项亦成立。 |
| 139.3—139.5 | 只用刚取得的紧纯 $Q$、近根集合相等、Inj及点交，构造两张完整横截球面，排除指定根球族退化；其连续参数和第二根补图给无边界四维 $Q$。 |
| 139.6—139.8 | 已付可定向秩二丛及闭四维流形供应 Thom、Euler、整数对偶；所有内载球缘代表生成元，不交开邻域的相对乘积排除不相交，给 $\Lambda$ 标签对的实际交点。三个固定球缘阻止标签塌缩，故 $\Lambda$ 紧、其整球连续，且每个近根 $q$ 满足 $S_q\subseteq\Lambda$。这些证明均只使用上述接口；引理139.9（第139.8节）末段用 Conn 选首次越出路径的结论不在此列。 |
| 142.1中的维数入口 | 原来引用141.2只在此供应整个 $V$ 的九维。本命题独立给这个维数，故原仿射八维、边界七维及投影四维都准确保持。141.1所列面、法向、紧 $Q$、紧 $\Lambda$ 与近根捕获接口也已逐项付清；这里不从其依赖 G 的维数结论倒推新根。 |

据此，142.2证明第一步在全部原 $P$ 上有四维法向，SAME_READBACK128.2给紧投影层，覆盖维数闭集可数和定理给每个紧纯子集至多四维。第二步用近根 $Q(q)=Q$、紧 $\Lambda$ 及其整球连续性构造实际 join，在每颗 $S_x$ 上得到 $\Lambda$ 内的开圆片。第三步从这些圆片的九个真实见证连续确定整个 $Q$ 球族。第四步由其真实三球丛、Inj及点交，取得原七维边界中的开评价像与紧球并。第五步若未覆盖，边界为紧纯分离子；原任意紧集 Čech–Alexander 对偶要求至少六维，第一步却给至多四维，故排除缺口。第六步用每个原 $D_a$ 的非纯相对内点返回球标签，Inj给 $P=Q=\Lambda$ 和原固定根覆盖。第七步消费只要求 EB3+该 R1 的 X133.6—133.7，得到同原 $\Phi$。这七步所需前件已分别在表中或本命题假设中列尽，均无需额外有限路径；成熟维数、对偶和分类工具仍按142的原适用条件消费。由此得到本命题。证毕。

现在证明定理145.2第2项的全部结论。BILATERAL VIII121.6在**这个** EB3+Inj+九维原域给全部 $P=P_0$，所以145.3—145.7先给同根 $\mathsf G(o)$；命题145.8随后适用，取得(XI145.3)—(XI145.4)。这不是把 Conn 简单改名为 Inj：完整唯一暴露接口由另有九维前件的源121.6实际供应，且上表将其全部后续消费者逐项对接。

反向取整个 $\operatorname{Herm}_3(\mathbb C)$、PSD 锥及迹单位，并通过同一个 $\Phi$ 运输。PSD锥闭、尖且生成整个Hermitian实空间，迹在其非零元上严格正；整个迹一基的极点恰为全部秩一投影，均由有限维谱定理给出。全效应与完整菜单的计算见145.9，给每个纯 $P_v=vv^*$ 的整个

$$
D_{P_v}=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho v=0\}.
\tag{XI145.34}
$$

这是整个 $v^\perp\cong\mathbb C^2$ 上的密度三球，故 EB3 成立；球的整个支持子空间是 $v^\perp$，相同球必给相同纯射线，故 Inj。原实空间维数为九。对任意单位 $v,w$，包括相同射线，可取单位 $z\perp\operatorname{span}_{\mathbb C}\{v,w\}$；同一个 $P_z$ 与二者都有由原投影效应见证的真实零边。因此 Conn成立，每个事先指定根都有 $Q(r)=P$、$\mathsf G(r)$。第3项遂给第1、2项。第1项到第2项已由130.2支付，等价链及整个标准反向完成，定理145.2证毕。

### 145.8 同一表示的完整静态公理字典

**条件应用 145.9（全原对象运输）。** 在定理145.2任一等价条件下，采用其**同一个** $\Phi$。记 $P_v=vv^*$、$v^*v=1$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$、$U=\Phi(I_3)$。直接消费142.3及 X133.7 的字典：

| 原对象／静态量子公理 | 同原锥和同原单位中的完整对应 |
| --- | --- |
| 全载体、全锥与质量 | $V=\Phi(\operatorname{Herm}_3)$；整个 $C=\Phi(\operatorname{PSD}_3)$，包括零、次归一和任意非负质量；$u(\Phi X)=\operatorname{Tr}X$。$u\in V^*$ 与 Jordan 单位 $U\in V$ 不混型。 |
| 全态与全部混合 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，仿射维数八；全部有限凸组合和非负组合保持。 |
| 全纯域与复叠加的静态含义 | 全部 $P=\{p_v\}\cong\mathbb{CP}^2$，实维四。任意非零 $w\in\mathbb C^3$ 对应 $\Phi(ww^*/(w^*w))$；非零复倍数给同一标签，每个非零复线性叠加有其原射线标签。零向量没有归一纯标签。 |
| 全效应与 Born 评价 | $f_M(\Phi X)=\operatorname{Tr}(MX)$ 恰遍历全部 $0\preceq M\preceq I_3$，保持零、单位、补及序；任意实线性读数对应任意 Hermitian $M$。评价覆盖所有原混态和全部非负锥元。 |
| 完整非单点确认、least及已达minimum | $\mathcal F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\}$；least为 $f_{P_v}$。对每个原混态 $T_{p_v}(\Phi\rho)=\operatorname{Tr}(P_v\rho)=v^*\rho v$，由同一菜单的 $B=0$ 达到。 |
| 全纯比较与所有端点 | $T_{p_v}(p_w)=\lvert v^*w\rvert^2$；未归一时除以 $(v^*v)(w^*w)$。相等射线给一，正交射线给零，PR成立。 |
| 整个排除球、球缘及中心 | $D_{p_v}$ 为(XI145.34)的全部原像，含全部混态；Pauli坐标为 $(I_2+r\cdot\sigma)/2$、$\|r\|\le1$，纯球缘 $\mathbb{CP}^1\cong S^2$。$c_{p_v}=\Phi(Q_v/2)=(U-p_v)/2$；总体中心态为 $U/3$。 |
| 原零框架与数学共同效应 | 原零三角对应三个和为 $I_3$ 的正交秩一投影，其三个 least 效应和为 $u$；每条原零边有唯一第三点，数学完美区别容量为三。全部不同纯对的原最小面是真面，全 Pair 成立。 |
| 全部有限数学测量 | 对任意有限结果数，全部 $f_j\in C^*$、$\sum_jf_j=u$ 恰对应全部 POVM $M_j\succeq0$、$\sum_jM_j=I_3$；在每个原归一输入上概率为 $\operatorname{Tr}(M_j\rho)$。零效应、重复项和任意有限粗粒化均允许。 |
| 谱与全部实可观测量 | 每态有三项正交纯谱分解，$\lambda_i\ge0,\sum_i\lambda_i=1$，允许零权与重谱；一般非负质量的谱权重和等于该质量，零元全为零。全部 Hermitian 可观测量有实谱及谱投影，含零本征值；重谱不指定唯一逐本征射线。 |
| 共同尺、Jordan与齐次性 | $\langle\Phi X,\Phi Y\rangle_\Phi=\operatorname{Tr}(XY)$ 使 $C$ 自对偶；$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$，单位为 $U$。正定矩阵的可逆合同变换给原锥内部齐次性。 |
| 全域球心图与相容性 | $R(x)=(u(x)U-x)/2$ 在全部 $V$ 上正、保质量、可逆，且 $R(p)=c_p$；同一原混态的全部有限纯配方替换球心后仍为同一态。 |

证明。全锥、全态、极点和全效应由同锥同单位双射及迹对偶运输。为保留最低定义，完整检查确认菜单：若 $0\preceq M\preceq I_3$ 且 $v^*Mv=1$，则 $I_3-M\succeq0$ 及零二次型给 $(I_3-M)v=0$；Hermitian 性消去交叉块，故全部且仅有 $M=P_v+B$，其中 $B=Q_vBQ_v$、$0\preceq B\preceq Q_v$。$B=0$ 与 $B=Q_v$ 都在菜单中，故菜单非单点。对每个 $X\succeq0$，

$$
\operatorname{Tr}((P_v+B)X)-\operatorname{Tr}(P_vX)
=\operatorname{Tr}(BX)\ge0.
\tag{XI145.35}
$$

因此 $B=0$ 同时给全锥序的 least 和每个混输入上的已达 minimum。$X=0$ 时所有读数为零；$u(x)>0$ 时归一读数为 $f_M(x)/u(x)$，零质量锥元只有零，不强定义其归一态。对正矩阵，$v^*\rho v=0\Longleftrightarrow\rho v=0$，所以最低值的零集是整个二阶密度球，绝非仅纯零表。余项是同一表示的谱定理、迹配对与 Jordan 乘法运输；其全部静态计算亦适用于145.8的整个标准反向。证毕。

这些等价前件下，MC、BC、ZC、Seed、所有根完整覆盖、纯域紧性、整个球族连续、PR、least、谱与 Jordan 结构都是后果。准确地，任意两份同一原态 $x$ 的有限纯配方，含零权和重复标签，球心替换都为 $(U-x)/2$，给135.1的完整 MC及138.1的 BC；取 $e_a=f_{P_v}$ 时，对每个 $x\in S_a$ 有 $e_a(c_x)=1/2$，给140.1的 ZC与 $\kappa_a=1$。每个纯标签均能完成原零三角，Seed成立。它们不再作为本定理额外前件。

与已发表第143章对接时，在完整 EB3+$\mathsf{Conn}$ 原域内，本章九维条件、存在一个实际同根 $\mathsf G(o)$、143.1中式(XI143.4a)的统一可读差额 $\mathsf U$，以及同锥同单位的复三能级表示，四项等价。九维到根芽由145.4—145.7支付，根芽到表示用142.2，表示与 $\mathsf U$ 的双向对应直接复用143.4，表示到九维取整个 Hermitian 实空间的维数。因此无需将根芽或统一差额再作独立输入；在 EB3+Inj 的已知维数下界中取等，已经给出这里的完整静态候选。这是候选之间的已付对应，不是无前提推导、最少公理数或逻辑上严格更弱的断言。

原法向限制的正逆现在也已支付：$N_{p_v}$ 恰为支持在 $v^\perp$ 的正矩阵读数；其线性张成恰对应全部 Hermitian 二阶读数，正好覆盖 $D_{p_v}$ 上所有非负仿射函数。因此 $R_{p_v}^{-1}$ 对该球的非负函数为正。它与球心图的逆不同型：

$$
R^{-1}(y)=u(y)U-2y,\qquad R^{-1}(p_v)=U-2p_v\notin C.
\tag{XI145.36}
$$

球心图的逆并不正，亦不因此产生实际可执行事件。

### 145.9 原物理合同的完整继承

完整继承 [XI142.4][Q145XI]的每一前件、原对象、作用域和全部量词，包括其所引 XI141.5、139.11、THREE_COPY VIII131.8、SAME_READBACK **SECTION127.10**及全部传递引用。具体仍包括 SAME_READBACK125.11、124.9、123.13，EXCLUSION VIII112.9、113.11与 IX120.11，THREE_COPY VII121.12、122.14，INTRINSIC_POLAR VI定义89.7、89.8—89.10和全部两尺度式(89.13)、V88.6与87章、原生续卷VII和III的来源／全未来／动态合同，以及 BILATERAL VIII128.H。操作来源的 INTRINSIC_POLAR VI 与整球 BILATERAL VI 按原类型区分。以下重述其实际范围，不以静态表示供应实际操作。

同一个原装饰元组 $\mathcal O$、共同来源域、**全部**中点实现、原概率像紧性、全测试表及闭性，零／单位／补／有界倍增、重复标签及每种同中点实现，全部非负质量（零、次归一、不等质量），过程和参考各自完整相关联合输入域，仍分别供应。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)的全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集，均保持原定义。操作映射 $p$、纯标签及根条件不同型。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、旧 support、**全部合法未来及每个中间切口**，原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption与资源合同，均由原消费者承担。原复射线和数学叠加不产生实际相干制备、相位参考、可调用门、接线或权限。

对**每个有限** $N\ge1$，仍另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 及完整原效应区间。对每个实际二分割 $a+b=N$，保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{XI145.37}
$$

同一产品配对、严格张量单位、全部原因子置换及逆的正性、规范重括号和指定运输下不连续位置分块仍要求实际供应。实际二份 $S_2$ 量化每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族和全部 $t_\ell\ge0,\sum_\ell t_\ell=1$，含零权和重复标签，要求

$$
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\qquad
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]_{C_2^*}\\f(p)=1}}f(x).
\tag{XI145.38}
$$

低二份 $q=1,2$ 的 least／谱性／正面投影与保纯到 Jordan 桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制及秩、实维乘法的复型选择，同一实际两因子的产品正规形，仍是全有限层级的三项分别供应。单体 Born minimum 不支付这些全纠缠输入合同。

非经典 $\mathsf F_{\max}$ 仍要求同一最大复块 $n_r=L\ge2$、同一含相位正交基上的实际三份资源

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{XI145.39}
$$

其余三份扇区为零，归一原源为 $\Delta_r/L$；不预付三份纯性或实际制备，全经典 $L=1$ 按原规则免此资源。本单体复三能级支路 $L=3$，二、三份秩分别九、二十七；高阶整个排除集不继续被规定为单体 EB3。形式矩阵不支付实际 $C_3$ 成员资格。

对全部输入输出份数及原实线性 $F:W_m\to W_n$，全旁观正性仍量化**每个** $b\ge0$ 和每个含纠缠的同一共同输入，要求 $(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$。实际完整有限层级和共同表示齐备后，才沿原 Choi 桥识别 CP及矩形跨扇区 Kraus。TP／TNI 对**每个**原 $x\in C_m$ 分别要求 $u_n(Fx)=u_m(x)$／$u_n(Fx)\le u_m(x)$；同族分支总预算对同一个输入逐点承担。

同一实际事件的 CP仍需完整提升、实际探针和相容核；全部数学 CP-TNI 分支成为实际事件仍需事件饱和选择。同族仪器保留共同输入预算、接线、记录、粗粒化和校准。只对严格正质量分支条件归一；零质量分支不强定归一条件态。Lüders 更新仍需同一分支的锐效应、接受态中性和输出校准。全数学 POVM与实际可执行同族仪器各保原合同；静态正保质量球心图亦未取得全旁观 CP或事件资格。

原物理钟、实际动态来源、连续齐次可逆时间群与单位仍分别供应。另给全实时间连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，才有这项额外供应的有限维生成元；再给复块上保迹酉时间族，才使用

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad \rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\mathrm i[H,\rho]/\hbar,\qquad H=H^*.
\tag{XI145.40}
$$

量词覆盖全部原输入和全部实际时间。$H$ 的标量平移及时间重标各保原意义；恒等时间族与非平凡 Hamiltonian 族可共享全部静态对象。实际 Hamiltonian、能量识别与标定、数值 $\hbar$、时空和物理空间维数仍各自需要供应。九维实载体、四维纯域、三维排除球与原零图边数均不指定物理空间或物理时间。

### 145.10 归属、开放范围与完整中文图景

本章采用 `repo-derived` 综合归属。原面及全部法向接口、最大值公式、固定球面 Lipschitz 效应与准确原边区间、法锥全部边界射线、紧法向层、实际球面二盘及四维块、纯域 $G_\delta$ 与独立维数下界，均精确复用145.3—145.5所引来源。有限维紧凸极点生成、Carathéodory、奇异值扰动、Polish空间的 Baire 定理、连续正定平方根、球极投影和二次曲面唯一性是成熟中间工具。Hatcher《Algebraic Topology》印刷页172 Theorem 2B.3要求欧氏同维开源上的连续单射；本章分别先支付四维层投影的开源、以及实际球束和实际纯开图的四维流形条件，才应用它。Corollary 2B.4的紧源满射背景与源证明保持一致。

新增承重连接是：有限正法向见证通过原最大值公式迫极限椭球含开放球面片，取得同层整球及效应连续；将已有四维块在同一个原纯开层内缩到任意靠近其构造锚点，并借四维投影得到全部原纯域中的实际开图；固定图内同一个最终根，用局部纯闭性把整球极限压成原整球或根单点，再以**完整法向基**和互补效应排除单点；最后由真实去根球束的开放评价及紧二步集的闭性覆盖这个同一根的穿孔邻域。145.8将已付接口精确送入137、139和142的实际消费者；142的全域覆盖和既有分类、全静态字典及标准反向均按来源归属，不计为新的分类理论。

这里没有调用预设全局关联开放、每对点已有连接、模面格、正限制逆或量子矩阵的外部分类来产生根芽，也不作全球新颖性或最弱公理断言。裸 EB3、去掉 Inj 的 EB3+九维，以及 EB3+Conn 的自动九维上界仍未由本章解决。对于 $\dim V>9$，同一法向层的投影靶维数为 $\dim V-5>4$，四维块不再由区域不变性给出全纯域开图；所以不能由本证明删掉维数输入。九维下 Conn 可换为 Inj 的精确加强，也不意味着二者在裸 EB3 的全部维数上等价。

**完整中文图景。** 原来的纯态、混态、全部允许读数始终在同一块完整凸状态体里。每个纯标签带着一颗完整实心排除三球，球皮是它的全部纯零邻居。九维是原实载体的外加尺寸，不是物理空间的维数。第一步先找一批有同一组八个有界法向见证的纯点。这八个见证的四个差在取极限后仍独立，因此不会悄悄丢掉一个法向方向。

让这批纯标签趋近另一个纯标签，整颗排除球可以先取一个真实椭球极限。原全效应的最大值公式说，这些法向的正组合都在整球上达到全域最大值；极限仍必须保留这些最大点。四维见证张满后，其三维斜率扫出一片球面方向，极限球便被迫含一片原球皮。椭球的二次刚性不允许它只留下这片而改掉整颗球，所以整球和暴露效应都连续。

Baire性使这样一张受控层含一个真正的原纯开片。再在一颗实际球面上取连续底盘，每颗底球都经过同一锚点；把另一片小球帽选得任意靠近锚点但避开它，就能将整个四维乘积块放进这个纯开片。九维恰好使该层能单射投影到四维空间，区域不变性将立方体内部升级为**全部原纯态中的**开图。现在才在图内固定最终根 $o$；最初构造块的锚点不被冒充为最终根。

围绕这个同一 $o$，让它所有零邻标签所带的整球移动。图内紧坐标闭球保证根附近纯点的极限仍纯。若移动球压扁，低维实心极限会在根附近全变成纯点，线段中点却是混态，因此只能整球缩成根一个点；若没有压扁，根附近的纯球皮又迫它等于正确的原整球。于是只剩真正整球和单点两种候选。

单点也不行。若整球缩到 $o$，它全部边界标签的暴露效应会一起趋向 $e_o$。完整射线定理说，这批边界效应生成的是**整个**原法向基，因此整个基也会被压成一点。但同一基里始终保留着互补效应 $g_s$；固定根球面的连续性保留了它的另一项要求，迫使 $g_s=e_o$。前者在一整颗非退化三球上读一，后者却只在 $o$ 读一，矛盾。整个同根球族因而连续。

将每颗球皮的公共根删掉，纤维成为一个二维平面；底也是二维球面，所以得到实际四维球束。不同纤维在根外不能相撞。它在已经建立的原纯四维开图中有开放评价像，完整二步集又因紧性而闭。小四维球删去中心仍连通，且球皮上确有其他点趋近中心，所以这个开闭像不能只占一部分：整个穿孔邻域都被同一根的两步线路覆盖，再补回根本身。这才取得实际 $\mathsf G(o)$。

此后142的整球延续和紧纯分离子排除将局部根芽送到全部原标签，既有分类才给同一个原锥和原单位的复三能级表示。所有原密度态、复射线、完整且非单点的确认菜单、least、每个混输入的已达 Born minimum、全部有限数学 POVM、谱和 Jordan结构同时兑现；旧 MC、BC、ZC、Seed及覆盖条件在这些新前件下成为后果。换成更短的几何说法，就是完整三球之间的原关系放在它已允许的最小实载体里，球标签不能重复，整套复三能级静态几何便由上述桥梁推出；不再另定根芽或统一可读差额。实际来源、装饰与读回、全部质量、每个有限联合及纠缠、三份资源、全旁观 CP、逐输入和同族预算、实际事件仪器、记录权限、全部未来和切口，以及物理钟、Hamiltonian、能量、数值 $\hbar$ 和时空，仍完整保留145.9的各自合同。静态量子态体的识别没有替代这些实际供应。

[Q145XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI137.2、137.4—137.8：完整接口、二次唯一性、近根集合相等及紧纯Q；139.3—139.8：连续整球、秩二丛、交数、紧Lambda；141.1—141.2：明确的维数接口；142.1—142.4：单根全局化、完整静态字典、标准反向与全部物理合同。"
[Q145IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.2原面与点交；119.10全部法向维数和暴露射线公式；120.2原最大值；120.7—120.8限制同构和法向相对内部；120.11—120.12固定球面Lipschitz效应、准确原边区间；120.4—120.5及116.17—116.18既有分类依赖。"
[Q145TVII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "VII121.5原紧中点像与纯域Gdelta、Baire；121.9 EB3+Inj的既有独立下界；122.2—122.5 EB3+Inj且p在P0的全部非零法向边界射线及严格凸法锥。"
[Q145TVIII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII130.2：EB3+Conn的全部Inj、P=P0、四维法向及准确原接口；131.7—131.8全部静态字典和实际物理合同。"
[Q145B]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md "VIII121.2—121.5：EB3+Inj的实际球面闭二盘、整球连续、局部标架和真实四维块；121.6：EB3+Inj+九维给全部P=P0；式(121.15)、(121.17)原全点紧投影层及准确法向对应。"
[Q145SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "128.2：同一2k个固定有界法向见证、严格误差界、可数紧层及单射投影；128.3：原法向的准确补常数公式；SECTION127.10及传递引用的完整实际合同。"
[Q145X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.6—133.7：EB3加固定根R1的同锥同单位分类、全部静态字典及整个标准反向；133.10完整实际合同。"
[Q145Ha]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology，印刷页172 Theorem 2B.3与Corollary 2B.4；区域不变性要求同维欧氏开源与连续单射，流形版本逐坐标应用。"

## 追加锚（本行以下为增补区）

## 146. 原零邻域的有限层推进与最小载体候选的边界

### 146.1 原域、邻域与逐层量词

**定义 146.1（完整原域中的零邻域）。** 保留144.1的全部原域：$V$ 为非零有限维实空间，$C\subset V$ 为闭尖生成凸锥，$u$ 在 $C\setminus\{0\}$ 上严格正，且

$$
\begin{gathered}
K=C\cap\{u=1\},\quad P=\operatorname{ext}K,\quad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\quad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\quad
D_p=\{z\in K:T_p(z)=0\},\quad S_p=P\cap D_p.
\end{gathered}
\tag{XI146.1}
$$

$T_p$ 在全部原混态上取整个紧确认菜单的已达到最小值。EB3 要求每个完整 $D_p$ 是非退化仿射实心三球，中心为 $c_p$；$\mathsf{Conn}$ 要求任意原纯对有有限原零边路。以下保留 EB3+$\mathsf{Conn}$+$\mathsf{ZC}$，其中

$$
\forall a\in P\ \exists\kappa_a\ \forall x\in S_a:\quad
e_a(c_x)+e_a(c_{2c_a-x})=\kappa_a.
\tag{XI146.2}
$$

这里 $e_p$ 是144.1式(XI144.2)所引既有结果供应的唯一整球零确认：$e_p(p)=1$、$e_p|_{D_p}=0$。其完整零面为 $D_p$，唯一一值点为 $p$；不把整个 $\mathcal F_p$ 缩成单点，不预设 least、$T_p=e_p$ 或正限制逆。全部非空真面只有纯单点或完整排除球，球标签单射，不同完整球至多交于一个原纯点。这些接口均沿用144.1的准确来源。

定义实际原邻域、有限层及二步载体为

$$
\mathcal N(A)=\bigcup_{x\in A}S_x,\qquad
H_0(a)=\{a\},\quad H_{m+1}(a)=H_m(a)\cup\mathcal N(H_m(a)),\qquad
Q(a)=\mathcal N(S_a).
\tag{XI146.3}
$$

固定辅助欧氏尺。由144.2，$1\le\kappa_a<2$，每张固定 $S_a$ 上中心连续；由144.3，$Q(a)$ 环境紧且全纯，整球在每张固定 $S_a$ 上连续。下文新增的是从一整层到下一整层的连续性推进，不将逐层常数预先统一于全部 $P$。

### 146.2 移动邻球的极限二分

**定理 146.2（连续母球上的移动邻球只有整球或母标签点极限）。** 若

$$
x_j\to x\in P,\quad D_{x_j}\to D_x,\quad
y_j\in S_{x_j},\quad y_j\to y\in S_x,\quad
D_{y_j}\to F
\tag{XI146.4}
$$

均在同一原域发生，球收敛取 Hausdorff 意义，则

$$
F=D_y\quad\text{或}\quad F=\{x\}.
\tag{XI146.5}
$$

证明。先给所需的椭球内点事实。设非点、允许降秩的椭球 $G=b+B\overline B^3$ 包含于非退化三球 $D$，且 $G\ne D$。存在 $v\in S^2$ 使 $b\pm Bv$ 均在 $\operatorname{ri}D$。确实，严格凸性使非退化中心弦的中点 $b$ 在 $\operatorname{ri}D$。若 $\operatorname{rank}B<3$，取单位核向量即可，两极限点允许相同。若满秩，将 $D$ 仿射化为单位球；若没有所求方向，闭接触集

$$
Z=\{v\in S^2:\|b+Bv\|=1\}
\tag{XI146.6}
$$

及 $-Z$ 覆盖 $S^2$。Baire 定理使 $Z$ 含球面开片。沿用142.2证明第三步的球面二次唯一性，$\|b+Bv\|^2-1$ 在整个 $S^2$ 为零。比较 $v,-v$ 得 $B^{\mathsf T}b=0$，满秩给 $b=0$；再得 $B^{\mathsf T}B=I$，所以 $G=D$，矛盾。

回到(XI146.4)。零对称给 $x_j\in D_{y_j}$，故 $x\in F$；纯标签处的原上关联给 $F\subseteq D_y$。点极限只能是 $\{x\}$。

设 $F$ 非点。任选原效应子列极限 $e_{y_j}\to f\in\mathcal E$，有 $f(y)=1$、$f|_F=0$。$f$ 的整个零面是非点真面，因而是某个完整极大球；又因 $f\in\mathcal F_y$，这个零面包含于 $D_y$，极大性迫其等于 $D_y$。此时才可由唯一整球零确认识别 $f=e_y$。全部聚点如此，故 $e_{y_j}\to e_y$。把 $x_j\in S_{y_j}$ 代入 ZC，有

$$
\kappa_{y_j}\le1+e_{y_j}(c_{x_j}),\qquad
\limsup_j\kappa_{y_j}\le1+e_y(c_x)<2.
\tag{XI146.7}
$$

中心 $c_{x_j}\to c_x$ 来自母球连续；严格性来自 $c_x$ 混、$e_y$ 仅在纯点 $y$ 取一。

反设 $F\subsetneq D_y$。对原球取有界正交半轴参数，再取共同子列

$$
D_{y_j}=b_j+B_j\overline B^3,\quad b_j\to b,\quad B_j\to B,\quad F=b+B\overline B^3.
\tag{XI146.8}
$$

用刚证内点事实选 $v$，实际对径纯点 $r_j=b_j+B_jv$、$r'_j=b_j-B_jv$ 的极限都在 $\operatorname{ri}D_y$。对其反向球的每个聚点应用[IX118.4][Q146IX]：聚点只能为纯单点 $\{q\}$，而相应混极限属于 $\operatorname{ri}D_q$。不同完整球不能共享混点，标签单射遂迫 $q=y$。因此

$$
D_{r_j},D_{r'_j}\to\{y\},\qquad
\kappa_{y_j}=e_{y_j}(c_{r_j})+e_{y_j}(c_{r'_j})\to2,
\tag{XI146.9}
$$

违反(XI146.7)。非点极限只能是 $D_y$。本证明没有在点极限分支中识别效应，也没有预付 $P$ 闭性。证毕。

### 146.3 紧连续层的原邻域推进

**定理 146.3（原邻域保持紧纯、连续与严格预算余量）。** 设非空 $A\subseteq P$ 环境紧，$x\mapsto D_x$ 在 $A$ 上连续，并且存在事先对整个 $A$ 选定的 $\varepsilon>0$，使 $\kappa_x\le2-\varepsilon$ 对全部 $x\in A$ 成立。则 $\mathcal N(A)$ 环境紧且全纯，$D,c,e$ 在其上连续，而且存在 $\varepsilon',\delta'>0$，使

$$
\kappa_y\le2-\varepsilon',\qquad
\text{$D_y$ 的全部三根半轴均不小于 }\delta'
\quad(y\in\mathcal N(A)).
\tag{XI146.10}
$$

证明。连续非退化三球的相对球缘连续，使用[IX118.2][Q146IX]。故实际关联集

$$
I_A=\{(x,y):x\in A,\ y\in S_x\}
\tag{XI146.11}
$$

在紧 $A\times K$ 中闭而紧，第二坐标投影恰为 $\mathcal N(A)$。投影中的点按定义全部原纯；没有把未知闭性的 $P$ 与紧集取交后宣称紧。

取 $y_j\to y$ 于该邻域，选择母标签 $x_j\in A$ 使 $y_j\in S_{x_j}$，再取 $x_j\to x\in A$。母球连续给 $y\in S_x$。146.2将任何球聚点限制为 $D_y$ 或 $\{x\}$。反设有子列 $D_{y_j}\to\{x\}$。

每个 $z\in S_x$ 满足 $x\in S_z$，故 $c_z\ne x$。144.2供应固定 $S_x$ 上中心连续，所以

$$
m_x:=\min_{z\in S_x}\|c_z-x\|>0.
\tag{XI146.12}
$$

令 $M_E=\max_{f\in\mathcal E}\|f\|_*>0$。母层的统一余量和 ZC 使每张 $S_{x_j}$ 都至少有一点 $z_j$ 满足

$$
e_{x_j}(c_{z_j})\le1-\varepsilon/2,\qquad
\|c_{z_j}-x_j\|\ge\frac{\varepsilon}{2M_E}.
\tag{XI146.13}
$$

充分大 $j$ 时，其中心到 $x$ 的距离至少为 $\varepsilon/(4M_E)$；但 $c_{y_j}\to x$。取

$$
0<r<\min\left(m_x,\frac{\varepsilon}{4M_E}\right).
\tag{XI146.14}
$$

每张固定 $S_{x_j}$ 连通，且144.2使该张球面上的中心像连续。因此可取 $w_j\in S_{x_j}$，使 $\|c_{w_j}-x\|=r$。紧 $I_A$ 允许再取 $w_j\to w\in S_x$。146.2使 $D_{w_j}$ 的任一聚点只能为 $D_w$ 或 $\{x\}$，中心极限到 $x$ 的距离遂分别至少为 $m_x$ 或等于零，都不可能为 $r$。点塌缩被排除。

于是所有球聚点均为 $D_y$，子列判据给邻域上的整球连续。中心、形状算子及恒秩三的像投影连续，复用139.4的支持函数式(XI139.14)。效应任一聚点在极限标签读一、在整个极限球读零，唯一性给邻域上的 $e_y$ 连续。

现在才在紧 $I_A$ 上取

$$
\mu_A=\max_{(x,y)\in I_A}e_y(c_x)<1.
\tag{XI146.15}
$$

函数连续，且混点 $c_x$ 处读数严格小于一，故最大值仍严格小于一。ZC 给 $\kappa_y\le1+e_y(c_x)\le1+\mu_A$，可取 $\varepsilon'=1-\mu_A$。紧基上连续的秩三形状算子的最小正特征值有正下界，给 $\delta'$。没有假定 $\kappa$ 连续，也没有把母层常数直接延用到下一层。证毕。

**定理 146.4（全部有限层正规性及退化的图距离逃逸）。** 对任意固定原根 $a$ 及每个整数 $m\ge0$，$H_m(a)$ 环境紧且全纯，$D,c,e$ 在其上连续，且

$$
\forall m\ \exists\varepsilon_m,\delta_m>0\ \forall p\in H_m(a):\quad
\kappa_p\le2-\varepsilon_m,\quad
\text{$D_p$ 的全部三根半轴均不小于 }\delta_m.
\tag{XI146.16}
$$

整个 $Q(a)$ 上 $D,c,e$ 也连续。它的根外部分同胚于 $S_a$ 上一个实际实秩二向量丛 $\xi_a$ 的总空间，而 $Q(a)$ 同胚于其 Thom 一点紧化；不预设根处为流形点或指定 Euler 数。若纯标签列 $p_j$ 满足下列任一完整趋向条件：$\operatorname{diam}D_{p_j}\to0$、$\kappa_{p_j}\to2$、或 $p_j$ 趋于混态，则其原零图距离 $d_\perp(a,p_j)\to\infty$。若 $p_j\to p\in P$ 并已选定 $d_H(D_{p_j},D_p)\ge\eta>0$ 的坏子列，则该选定子列亦逃出全部有限层。

证明。单点层满足146.3的前件，因为 $\kappa_a<2$。逐层推进，再在 $H_m$ 与 $\mathcal N(H_m)$ 两个紧闭子集上粘合连续映射，两层余量和半轴下界分别取较小者，即得(XI146.16)。$Q(a)$ 的紧纯性直接取144.3；连续性由 $Q(a)\subseteq H_2(a)$ 限制得到，未以该包含本身证明紧性。根外丛直接复用139.5的单根构造：在 $S_a$ 上写连续秩三形状 $A_s$，令 $w_s=A_s^{\dagger/2}(a-c_s)$、$(\xi_a)_s=\operatorname{im}A_s\cap w_s^\perp$，逐纤维采用该证明式(XI139.16)—(XI139.17)的球极投影。逆的母标签坐标连续，因为紧 $S_a$ 的任何标签聚点都由原上关联及根外唯一共同邻点确定；未使用第二根补图。紧 $Q(a)$ 是该非紧总空间的一点紧化，紧基的 Thom 空间识别见[Hatcher，印刷页112][Q146VB]。若前三类退化列有无限多项落在一个固定 $H_m$，该层的紧纯性或统一下界立即矛盾。对坏子列，紧闭层使极限 $p$ 也在层内，该层连续性与固定 $\eta$ 矛盾。仅说整列存在一条不收敛子列，不足以让整列逃逸，因为可以交错插入固定 $p$。这里的量词是 $\forall m\exists\varepsilon_m,\delta_m$，没有取得 $\exists\varepsilon,\delta\forall m$。证毕。

### 146.4 复用最小载体候选与完整静态字典

**定义 146.5（最小载体候选及其静态字典）。** 对式(XI146.1)的完整锥模型，另取只含 EB3、$\mathsf{Conn}$ 和整个原空间 $\dim_{\mathbb R}V\le9$ 的候选，不将 ZC 列为该候选的独立前提。Conn 给 Inj 后，[THREE_COPY VII121.9][Q146TVII]的既有下界使维数恰为九；此时直接消费145.2，得到同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,\qquad
\Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI146.17}
$$

145.2的整个标准反向给该候选的反向。该分类及下界均为既有结果的应用，不计为本章新增定理。ZC 在这一最小载体候选中为分类后的后果，且 $\kappa_p=1$；对未限制原维数的 EB3+$\mathsf{Conn}$ 域，本章146.2—146.4的有限层推进仍明确保留 ZC 前件。未证明自动的九维上界，也不将逐层余量统一到全部原纯域。

在同一个 $\Phi$ 下，全部原态、效应、确认菜单、已达到的 minimum、POVM及谱字典直接复用145.8及142.3。特别地，对单位 $v$、$p_v=\Phi(vv^*)$，

$$
\begin{gathered}
f_M(\Phi\rho)=\operatorname{Tr}(M\rho),\quad 0\preceq M\preceq I,\\
\mathcal F_{p_v}=\{f_{vv^*+B}:B=P_{v^\perp}BP_{v^\perp},\ 0\preceq B\preceq P_{v^\perp}\},\\
T_{p_v}(\Phi\rho)=v^*\rho v,\qquad
D_{p_v}\text{ 是 }v^\perp\cong\mathbb C^2\text{ 上的整个态球}.
\end{gathered}
\tag{XI146.18}
$$

矩阵偏序下 $vv^*$ 是菜单的 least 为分类后的后果。全部纯域为 $\mathbb{CP}^2$、每个排除纯球缘为 $\mathbb{CP}^1\cong S^2$。纯比较数值互易不定义连续测量次序交换；实际仪器、更新、复合、物理时间及能量标定仍分别取145.9及142.3所列独立条件。

### 146.5 稠密正规域与尚未排除的逃逸

**定理 146.6（根无关稠密正规域及零边传播的剩余条件）。** 在完整 EB3+$\mathsf{Conn}$+$\mathsf{ZC}$ 域，定义

$$
U=\bigcup_{m\ge0}\operatorname{int}_P H_m(a).
\tag{XI146.19}
$$

则 $U$ 是根无关的非空稠密开集；$P$ 在 $U$ 上局部紧，$D,c,e$ 局部连续，并有局部统一的半轴下界和 $\kappa<2$ 余量。若另能证明 $U$ 沿每条原零边不变，则得到同原 qutrit。若同原表示不存在，则必有 $\dim V\ge10$、$\sup_P\kappa=2$，且从任意固定根出发的原图距离无界。

证明。非极点集正好是下列紧集的可数并：

$$
K\setminus P=
\bigcup_{j\ge1}
\left\{\frac{x+y}{2}:x,y\in K,\ \|x-y\|\ge1/j\right\}.
\tag{XI146.20}
$$

任一非极点可取一条以它为中点的非退化子弦，反向显然。故 $P$ 是紧度量 $K$ 中的 $G_\delta$，完全可度量且为 Baire 空间。Conn 给 $P=\bigcup_mH_m(a)$，各层在 $P$ 中闭。任意非空 $P$ 开集自身为 Baire，其闭层覆盖中至少一层有非空相对内部，所以 $U$ 稠密。两根间原图距离有限，只让各层包含关系偏移一个固定整数，故 $U$ 根无关。其余局部结论直接来自146.4；若点位于一紧层的 $P$ 内部，该层就是其紧邻域。

若 $U$ 沿零边不变，非空性与 Conn 使 $U=P$，从而整个 $P$ 上整球连续。[IX118.3、118.5、118.8][Q146IX]即给同原表示，不须先另假定 $P$ 闭。不存在该表示时，145.2及已引九维下界排除 $\dim V\le9$，144.4迫 $\sup_P\kappa=2$。若某根到全部原纯点的距离有有限上界，则 $P=H_m(a)$ 对某 $m$ 成立，146.4又给全域不塌缩而重构，矛盾。

更具体地，设 $p\in U$、$q\perp p$，且 $q_j\to q$ 是逃出全部有限层的纯标签列。它不可能满足 $D_{q_j}\to D_q$：否则球缘连续给实际 $p_j\in S_{q_j}$、$p_j\to p$；$p$ 的某个 $P$ 邻域包含于固定 $H_m(a)$，零对称遂把所有充分大的 $q_j$ 捕获到 $H_{m+1}(a)$。因此这种失败的球聚点只能是 $D_q$ 的真子椭球或点。尚未由现有条件排除这些极限，也未证明 $U$ 沿边不变或自动的九维上界。146.2的移动邻球二分要求连续母球及实际邻点列，不能应用到这里只给定的任意 $q_j\to q$ 来省去这个缺口。证毕。

[Q146IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "118.2：非退化相对球缘极限；118.3—118.5：原上关联、混极限和开放边不塌缩；118.8：同原量子锥分类。"
[Q146TVII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "VII121.9：EB3+Inj的既有独立九维下界。"
[Q146VB]: https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf "Allen Hatcher, Vector Bundles and K-Theory，Thom Spaces，印刷页112：紧基向量丛总空间的一点紧化。"

## 追加锚（本行以下为增补区）

## 147. 原正尺的核支撑提升与低阶谱截面排除

### 147.1 完整原域与两种矩阵研究类

**定义 147.1（原比较及忠实矩阵载体）。** 全程保持145.1及146.1的非零有限维实空间 $V$、闭尖生成锥 $C$、严格正原单位 $u$，以及整个

$$
K=C\cap\{u=1\},\quad P=\operatorname{ext}K,\quad
\mathcal E=[0,u]_{C^*},\quad
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\quad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\quad D_p=\{z\in K:T_p(z)=0\}.
\tag{XI147.1}
$$

第二变量包含所有混态，最小化遍历整个原菜单并达到；不删原态、效应或确认者。EB3及有限原零边连通 $\mathsf{Conn}$ 取146.1的完整量词。直接复用145.3：Inj、唯一整球零确认 $e_p$、$\{e_p=1\}\cap K=\{p\}$、四维 $L_p=\operatorname{span}N_p$、$N_p=\{h\in C^*:h(p)=0\}$，以及全部非空真面仅为纯单点或完整 $D_a$。不把 $e_p$ 当作整个 $\mathcal F_p$，不预设least或 $T_p=e_p$。

取 $\mathbb F=\mathbb R$ 或 $\mathbb C$，$\operatorname{Herm}_m(\mathbb R)=\operatorname{Sym}_m(\mathbb R)$。忠实 PSD 截面指实线性单射 $A:V\to\operatorname{Herm}_m(\mathbb F)$ 满足

$$
C=\{x\in V:A_x\succeq0\},\qquad A_x:=A(x),\qquad r(x)=\operatorname{rank}_{\mathbb F}A_x.
\tag{XI147.2}
$$

所有阶数均在删去 $A(C)$ 的共同零空间后计量；这称有效阶数。原 $u$ 不预设为迹。另一个较宽研究类仅要求某个实线性单射 $B:V\to\operatorname{Herm}_N(\mathbb C)$ 满足 $B(C)\subseteq\operatorname{PSD}_N$ 且每个原纯像秩一，不要求 $B(C)=B(V)\cap\operatorname{PSD}_N$。矩阵表示是各研究类的明示前件，没有从 EB3、Conn 或纯比较数值互易推得一般原锥具有这些表示。

### 147.2 正代表及实际原邻点的构造

**定理 147.2（同秩趋近的原正尺提升）。** 在 EB3+$\mathsf{Conn}$ 及忠实截面(XI147.2)下，若 $p\perp q$、$q_j\in P$、$q_j\to q\in P$ 且最终 $r(q_j)=r(q)$，则存在实际原纯点 $p_j\in S_{q_j}$，使 $p_j\to p$。同一标签序列上还有 $D_{q_j}\to D_q$ 的 Hausdorff 连续性。本定理不要求 ZC。

证明。先支付同一截面的正代表。取 $x_0\in\operatorname{int}C$。令 $W$ 为全部 $A(C)$ 像空间的共同线性张成。因 $V=\operatorname{span}C$，所有 $A(V)$ 都支撑于 $W$，压缩不损单射性。若 $v\in\ker A_{x_0}$，对任意 $c\in C$ 取充分小 $t>0$ 使 $x_0-tc\in C$；正性给 $0\le v^*(A_{x_0}-tA_c)v=-t v^*A_cv$，所以 $A_cv=0$。故压缩后 $A_{x_0}\succ0$。置 $\lambda_0=\lambda_{\min}(A_{x_0})>0$。对 $G\succeq0$，用实迹配对定义 $A^*(G)(x)=\operatorname{Tr}(GA_x)$，并有

$$
\lambda_0\operatorname{Tr}G\le A^*(G)(x_0).
\tag{XI147.3}
$$

若 $A^*(G_i)$ 收敛，则正矩阵 $G_i$ 的迹及范数有界，存在收敛子列。因此 $A^*(\operatorname{PSD}_m)$ 闭。它的对偶锥恰为 $\{x:A_x\succeq0\}=C$，有限维双极定理遂给

$$
C^*=A^*(\operatorname{PSD}_m),\qquad
N_q=A^*\{G\succeq0:\operatorname{ran}G\subseteq\ker A_q\}.
\tag{XI147.4}
$$

第二式使用正矩阵的 $\operatorname{Tr}(GA_q)=0\Longleftrightarrow\operatorname{ran}G\subseteq\ker A_q$。这同时说明正代表确实在原全锥上非负；没有把任意 PSD 线性像自动当成闭锥。

原 $e_p(q)=0$ 允许选 $G\succeq0$，使 $A^*(G)=e_p$ 且 $\operatorname{ran}G\subseteq\ker A_q$。令 $\Pi_j,\Pi$ 为相应矩阵核的正交投影。同秩矩阵收敛给 $\Pi_j\to\Pi$：极限矩阵的正谱有正间隙，谱投影在该间隙处连续，而相同核维数排除另有趋零的非零谱分支。定义

$$
G_j=\Pi_jG\Pi_j,\qquad h_j=A^*(G_j),\qquad
\alpha_j=\max_Kh_j.
\tag{XI147.5}
$$

于是 $h_j\in N_{q_j}$、$h_j\to e_p$，后者在紧 $K$ 上一致，故 $\alpha_j\to1$。以下最大面选择复用[IX118.11][Q147IX]，核投影在这里支付其所需的原零尺修复条件。充分大 $j$ 时 $f_j=h_j/\alpha_j$ 属于整个原 $\mathcal E$。在 $h_j$ 的非空紧最大面选一个极点 $p_j$；面的极点也是整个 $K$ 的极点，故

$$
f_j(p_j)=1,\qquad f_j(q_j)=0,\qquad p_j\in P\cap D_{q_j}=S_{q_j}.
\tag{XI147.6}
$$

最后一个包含用同一原补效应或零对称。任一聚点 $p'\in K$ 满足 $e_p(p')=1$，唯一一值点迫 $p'=p$，故整列趋向 $p$。有限个前项可任取其实际球缘点。

对每个固定 $p\in S_q$ 均得到上述实际逼近。任意 $z\in D_q$ 是球内一条直径两端的凸组合，分别提升这两个端点并保持系数，即得到 $D_{q_j}$ 中趋向 $z$ 的点。距离函数的统一一阶 Lipschitz 界和紧 $D_q$ 的有限网把逐点逼近变成统一下包含。上包含直接由紧原菜单给出：若 $z_j\in D_{q_j}$、$z_j\to z$，取共同零确认的效应聚点 $f$，则 $f(q)=1,f(z)=0$，所以 $z\in D_q$。紧性遂给整个球的 Hausdorff 收敛。这里真正构造了所需的原邻标签，没有用移动仿射包中的固定射线。证毕。

### 147.3 降秩序列的准确正证书条件

**定理 147.3（指定零边的核支撑判据）。** 在147.2的截面域另取 ZC，令 $U$ 为146.6的根无关稠密正规域。设 $p\in U$、$p\perp q$、$q_j\to q$ 均纯，并已取子列使

$$
\Pi_{\ker A_{q_j}}\to\Pi_H,\qquad
M_H=A^*\{G\succeq0:\operatorname{ran}G\subseteq H\}.
\tag{XI147.7}
$$

则 $H\subseteq\ker A_q$，并且

$$
\left(\exists p_j\in S_{q_j},\ p_j\to p\right)
\quad\Longleftrightarrow\quad e_p\in M_H.
\tag{XI147.8}
$$

若同一 $q_j$ 逃出每个固定有限层 $H_m(a)$，则对该序列每个核投影聚点 $H$ 都必有 $e_p\notin M_H$。

证明。把 $A_{q_j}\Pi_{\ker A_{q_j}}=0$ 取极限即得 $H\subseteq\ker A_q$。若 $e_p=A^*(G)$ 且正 $G$ 支撑于 $H$，式(XI147.5)及最大面构造不再需要同秩，直接给所需 $p_j$。反向若已有这些邻点，146.6在 $p$ 的原纯邻域给 $e_{p_j}\to e_p$。式(XI147.4)允许选正代表 $G_j$，满足

$$
A^*(G_j)=e_{p_j},\qquad \operatorname{ran}G_j\subseteq\ker A_{q_j},\qquad
\lambda_0\operatorname{Tr}G_j\le e_{p_j}(x_0)\le u(x_0).
\tag{XI147.9}
$$

取收敛子列 $G_j\to G$。投影收敛使 $G$ 支撑于 $H$，并有 $A^*(G)=e_p$，证明必要性。这里没有把不受界的正代表直接取极限。

最后 $p\in U$ 使某个原纯开邻域 $O\ni p$ 包含于固定 $H_m(a)$。若 $e_p\in M_H$，相应子列的实际 $p_j$ 最终在 $O$；$q_j\perp p_j$ 遂将这条子列捕获到 $H_{m+1}(a)$，与逃逸矛盾。这个判据只针对给定截面的实际核与给定零边，不是给全域整球连续性另起名称。证毕。

**定理 147.4（同秩层之外才有球退化）。** 在147.2的截面域，不另需 ZC。若 $q_j\to q\in P$ 且某条坏子列满足 $d_H(D_{q_j},D_q)\ge\eta>0$，则可再取子列使 $r(q_j)=r_*>r(q)$。若有 $p\in U$、$p\perp q$，且 $r$ 在 $q$ 的某个原纯邻域常值，则 $q\in U$；后一项在 EB3+$\mathsf{Conn}$+ZC 域使用 $U$。

证明。有限多个矩阵秩允许选常秩子列；矩阵秩的下半连续性给 $r_*\ge r(q)$，147.2排除等号。对第二项，取 $p$ 的纯开邻域 $O\subset H_m(a)$。任意 $q_j\to q$ 最终同秩，147.2构造的 $p_j\to p$ 使 $q_j$ 最终落在 $H_{m+1}(a)$。若 $q$ 不是这同一层的相对内点，可从该层外取趋向 $q$ 的纯列，矛盾。故 $q\in\operatorname{int}_P H_{m+1}(a)$。没有声称极大秩点仅因整球局部连续便已属于 $U$。证毕。

### 147.4 共同核、真实三角与小阶数截面

**定理 147.5（有效阶数的排除范围）。** 在完整 EB3+$\mathsf{Conn}$+ZC 原域，若有忠实 PSD 截面表示，且有效阶数满足

$$
m\le4\quad(\mathbb F=\mathbb C),\qquad
m\le6\quad(\mathbb F=\mathbb R),
\tag{XI147.10}
$$

则同一原锥和原单位具有复三能级表示

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,\qquad
\Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI147.11}
$$

任意有效阶数上，只要有一个实际纯标签的矩阵秩在复域等于一，或在实域不大于二，也得到同一结论。

证明。记 $k(p)=\dim_{\mathbb F}\ker A_p$。由四维 $L_p$ 及(XI147.4)，

$$
4\le\begin{cases}k(p)^2,&\mathbb F=\mathbb C,\\k(p)(k(p)+1)/2,&\mathbb F=\mathbb R,\end{cases}
\qquad k(p)\ge k_0:=\begin{cases}2,&\mathbb F=\mathbb C,\\3,&\mathbb F=\mathbb R,\end{cases}
\qquad r(p)\le m-k_0.
\tag{XI147.12}
$$

若原零边 $p\perp q$ 有非零共同核向量 $v$，原正泛函 $h_v(x)=v^*A_xv$ 在 $p,q$ 均为零；$A_{x_0}\succ0$ 保证 $h_v\ne0$。因此 $K\cap\ker h_v$ 是含不同纯点 $p,q$ 的真面，原面分类迫其等于某个完整 $D_a$。于是 $a,p,q$ 是三个不同原纯标签，且三条实际零边全成立。此时才使用140.4的 EB3+$\mathsf{Conn}$+ZC+Seed 分类。特别地，$r(p)+r(q)<m$ 足以产生这个非零共同核。

若 $m<2k_0$，任取实际零边，(XI147.12)给 $r(p)+r(q)\le2(m-k_0)<m$，遂得三角。若 $m=2k_0$ 且有 $r(p)<k_0$，其任一零邻点 $q$ 同样满足秩和严格小于 $m$。余下只有 $r(p)=k_0$ 对全部原纯点成立，147.2遂给整个 $P$ 上的整球连续，此时直接使用[IX118.3、118.5、118.8][Q147IX]的既有分类。以上穷尽(XI147.10)。任意阶数的低秩标签断言也由 $r(p)<k_0$ 及其邻点的 $r(q)\le m-k_0$ 得到。未输入整个原 $\dim V\le9$；九维是(XI147.11)的后果。证毕。

### 147.5 正秩一嵌入的内生维数上界

**定理 147.6（不用截面相等的秩一嵌入刚性）。** 在完整 EB3+$\mathsf{Conn}$ 原域，若有任意有限阶的正实线性单射 $B:V\to\operatorname{Herm}_N(\mathbb C)$，使每个原纯像秩一，则整个原 $\dim_{\mathbb R}V=9$，并有(XI147.11)。本项不要求 ZC，也不要求 $B(C)=B(V)\cap\operatorname{PSD}_N$。

证明。令 $W$ 为所有 $\operatorname{ran}B(p)$、$p\in P$ 的复线性张成。$K$ 是有限纯凸组合的凸包，$C$ 生成 $V$，故全部 $B(V)$ 支撑于 $W$。若 $\dim_{\mathbb C}W\ge4$，选四个原纯点使 $B(p_i)=v_iv_i^*$ 且 $v_1,v_2,v_3,v_4$ 复线性无关。对 $W_j=\operatorname{span}_{\mathbb C}(v_1,\ldots,v_j)$ 定义实际锥面

$$
F_j=\{x\in C:\operatorname{ran}B(x)\subseteq W_j\}
=C\cap\ker\bigl(x\mapsto\operatorname{Tr}(P_{W_j^\perp}B(x))\bigr).
\tag{XI147.13}
$$

正性保证等式，并保证这些是暴露面。$p_1,p_2\in F_2$，$p_3\in F_3\setminus F_2$，$p_4\notin F_3$，所以 $F_2\subsetneq F_3\subsetneq C$ 是两个非射线真面严格嵌套，违反原完整面分类。因此 $\dim_{\mathbb C}W\le3$，单射性给整个原 $\dim_{\mathbb R}V\le9$。$\mathsf{Conn}$ 给 Inj，[THREE_COPY VII121.9][Q146TVII]的既有下界使维数恰为九；此时直接消费145.2，不重证四维根芽或整个矩阵填充。新增桥是由这一个正嵌入构造实际禁止面链，自动支付原空间上界；九维后的分类是145.2的应用。证毕。

若取任意非空 $X\subseteq\mathbb{CP}^{N-1}$，以全部单位秩一投影的紧闭子集 $\overline{\{vv^*/\|v\|^2:[v]\in X\}}$ 的凸包为基，则其所有极点仍属该紧秩一家族；这是有限维紧凸包的极点性质。故在它所张成的原空间上，若全部原效应和整个原排除集满足 EB3+$\mathsf{Conn}$，该锥已属于本定理范围。这里没有断言原嵌入 $B$ 本身必为满矩阵代数的合同变换，也没有把一般半正定像、部分纯标签秩一或非单射表示纳入结论。

### 147.6 完整候选、静态字典及未付的普遍步骤

**定义 147.7（研究类内的完整静态候选）。** 候选一是147.1的完整原域、EB3、$\mathsf{Conn}$，以及147.6的正单射与全部纯像秩一条件；候选二是同一完整原域、EB3、$\mathsf{Conn}$、ZC，以及147.5的小有效阶数截面条件。它们分别由147.6及147.5推出(XI147.11)，反向复三能级原模型以恒等复三阶截面满足这些条件。二者均不另输入原九维上界；候选一还不输入 ZC，但矩阵研究类条件仍明确承重，不据此宣称一般量子起源公理的独立性、最弱性或数量已减少。

同一个 $\Phi$ 运输全部原态、整个效应区间、所有确认菜单和每个混态上的原 minimum，字典直接取145.8及146.5。特别地，$p_v=\Phi(vv^*)$、$\|v\|=1$ 时，

$$
f_M(\Phi\rho)=\operatorname{Tr}(M\rho),\quad 0\preceq M\preceq I,\qquad
T_{p_v}(\Phi\rho)=v^*\rho v,\qquad
P\cong\mathbb{CP}^2,\quad S_{p_v}\cong\mathbb{CP}^1\cong S^2.
\tag{XI147.14}
$$

全部谱、least、纯端点数值互易及 $\kappa_p=1$ 都是同一表示后的既有后果。原实际来源、仪器与更新、所有有限复合和全旁观 CP、记录及合法未来、物理时钟、Hamiltonian及能量标定仍逐项继承145.9和142.4。纯端点互易仅交换比较双方，不表示任意先后测量交换。

**定理 147.8（谱截面中剩余反例的必要规格）。** 若完整 EB3+$\mathsf{Conn}$+ZC 模型有忠实 PSD 截面而没有(XI147.11)，则其每条原零边满足

$$
\ker A_p\cap\ker A_q=\{0\},\qquad A_p+A_q\succ0,
\tag{XI147.15}
$$

而全部原纯秩满足复域 $2\le r(p)\le m-2$、实域 $3\le r(p)\le m-3$。有效阶数至少分别为五、七。若恰为最小阶数，则两种允许纯秩均出现；低秩点的每个零邻点都是高秩点，所有整球坏子列在进一步取子列后只能高秩趋向低秩。

证明。共同核分支及低秩标签分支都已由147.5排除，(XI147.12)给上界；正矩阵和的核是两核之交，遂得(XI147.15)。小阶数亦由147.5排除。最小未排除复阶数五只容许秩二、三，实阶数七只容许秩三、四；若只出现一秩，147.2使整个球族连续，原分类又给(XI147.11)。两个低秩点若相邻，其秩和分别不超过四、六，均小于有效阶数，再生共同核三角，故低秩点的邻点全高秩。坏子列的唯一剩余秩方向由147.4给出。最高秩点有原纯邻域常秩，故球族在该邻域连续，但不单凭此断言它属于 $U$。

本章没有从 EB3+$\mathsf{Conn}$+ZC 排除这些更高阶截面，也没有构造满足全部前件的反模型。对一般原锥，$U$ 的沿边不变性、整个原空间的自动九维上界及内生矩阵表示仍是未付步骤。147.3解决的是指定截面中的具体正核证书，147.6解决的是全部纯像秩一的正嵌入，二者没有把这些表示当成一般域已有事实。$\mathsf{Conn}$ 也没有在本章被替换为三步全覆盖；[THREE_COPY VIII131.5][Q147TVIII]的奇返回论证仍需其 $\mathsf R_3(o)$ 原前件。

归属采用 `repo-derived` 综合推导：新增连接是核支撑运输支付 IX118.11 所需的原零尺修复条件，并结合 IX118.3 得到同秩整球连续性；其余新增消费者为降秩核证书、由实际共同核产生第三原标签的小阶数排除，以及正单射下的禁止面链上界。PSD 核面与秩一极射线的成熟背景见[Hildebrand，§3.2及§9][Q147H]；该文的 ROG 定义要求真正 PSD 截面，147.6没有借用其表示唯一性。原全截面的正提升已有[SectionROGFrame 的 whole-section positive lift applications][Q147ROG]，这里用(XI147.3)补齐任意严格可行同构截面的正代表闭性及统一迹界。谱投影、紧最大面的极点、有限维双极定理和紧凸包极点性质只作中间工具；同原九维分类及整球连续后的分类保持145.2和IX118.8的原来源，不重计为新结论。证毕。

[Q147IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "118.3：原整球连续和实际零边提升；118.5、118.8：全域连续后的同原分类；118.11：由原零尺修复到真实邻标签的最大面选择。"
[Q147TVIII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "131.5：附加R3(o)下的有限奇返回，不是裸Conn的后果。"
[Q147H]: https://arxiv.org/html/1409.4781v2#S3.SS2 "Roland Hildebrand, Spectrahedral cones generated by rank 1 matrices，§3.2 Lemmas 3.9—3.13及§9；J. Global Optimization 64 (2016), 349—397。"
[Q147ROG]: ../../../Blueprint/D5/S3/Quantum/Foundation/SectionROGFrame.md "Whole-section positive lift applications：整个原unital截面的PSD正代表；原前件与数学归属保持。"

## 追加锚（本行以下为增补区）

## 148. 最高纯秩的塌球排除与跨秩零边连续性

### 148.1 同一原域与最高纯秩

**定义 148.1（忠实截面中的纯秩与整球支撑）。** 保留147.1的整个原 $V,C,u,K,P,\mathcal E,\mathcal F_p,T_p,D_p$，以及 EB3、$\mathsf{Conn}$ 的全部量词。仍不预设 least、$T_p=e_p$、全 Pair 或全纯域闭性。取147.1的忠实有限阶实或复 PSD 截面，删去共同零空间后有

$$
A:V\hookrightarrow\operatorname{Herm}_m(\mathbb F),\qquad
C=A^{-1}(\operatorname{PSD}_m(\mathbb F)),\qquad A(z)\succ0
\quad(z\in\operatorname{ri}K),\qquad \mathbb F\in\{\mathbb R,\mathbb C\}.
\tag{XI148.1}
$$

原单位仍是 $u$，不要求 $u=\operatorname{Tr}\circ A$。定义

$$
r(p)=\operatorname{rank}_{\mathbb F}A(p),\quad
R=\max_{p\in P}r(p),\quad P_{\max}=\{p\in P:r(p)=R\},\quad
J_p=\ker A(p),\quad W_p=\operatorname{ran}A(c_p),\quad d_p=\dim_{\mathbb F}W_p.
\tag{XI148.2}
$$

$R$ 的存在只使用非空 $P$ 上有限个整数秩，不使用 $P$ 紧性。以下定理148.2—148.4不要求 ZC。准确复用145.3的 $\dim L_p=4$、$g_p=u-e_p\in\operatorname{ri}N_p$、全部非零相对边界射线 $\mathbb R_{>0}e_s$（$s\in S_p$），以及整个法向基

$$
B_p^*=\{h\in N_p:h(z)=1\}
=\operatorname{conv}\{\widehat e_s:s\in S_p\},\qquad
\widehat h=h/h(z).
\tag{XI148.3}
$$

复用147.2的同秩整球连续及正代表公式

$$
C^*=A^*(\operatorname{PSD}_m),\qquad
N_p=A^*(\operatorname{PSD}(J_p)).
\tag{XI148.4}
$$

### 148.2 同秩法向边界排除最高秩塌球

**定理 148.2（最高纯秩点不能是整球的单点极限）。** 在定义148.1的完整 EB3+$\mathsf{Conn}$ 和忠实截面下，不存在 $a_j\in P$、$s\in P_{\max}$ 使 $D_{a_j}\to\{s\}$ 于 Hausdorff 距离；不要求 $a_j$ 有纯极限。

证明。先建立该证明所需的同秩法向边界稳定性。设 $p_j\to p\in P$ 且 $r(p_j)=r(p)$，并有 $h_j\in\partial_{L_{p_j}}N_{p_j}$、$h_j\to h$。核投影收敛允许选等距同构 $U_j:J_p\to J_{p_j}$ 趋于 $J_p$ 的包含映射。在固定实空间 $\operatorname{Herm}(J_p)$ 上置

$$
\Psi_j(B)=A^*(U_jBU_j^*),\qquad \Psi(B)=A^*B.
\tag{XI148.5}
$$

由(XI148.4)，$\Psi_j(\operatorname{PSD}(J_p))=N_{p_j}$、$\operatorname{im}\Psi_j=L_{p_j}$，且像维数始终为四。评价闭性给 $h\in N_p$。若 $h\in\operatorname{ri}N_p$，取足够小 $\varepsilon>0$，使 $h-\varepsilon\Psi(I_{J_p})\in N_p$；选该差的正代表 $B_0$，得到

$$
G=B_0+\varepsilon I_{J_p}\succ0,\qquad \Psi(G)=h.
\tag{XI148.6}
$$

选 $B_1,\ldots,B_4\in\operatorname{Herm}(J_p)$，使 $\Psi(B_\ell)$ 是 $L_p$ 的基。充分大 $j$ 时，$\Psi_j(B_\ell)$ 仍是 $L_{p_j}$ 的基；四个极限基向量独立给相应坐标逆统一有界。因此存在 $b_{\ell j}\to0$ 使

$$
h_j-\Psi_j(G)=\sum_{\ell=1}^4 b_{\ell j}\Psi_j(B_\ell),\qquad
G_j=G+\sum_{\ell=1}^4 b_{\ell j}B_\ell\succ0,\qquad \Psi_j(G_j)=h_j.
\tag{XI148.7}
$$

满射线性图把正定矩阵的开邻域送到像空间的开邻域，迫 $h_j\in\operatorname{ri}N_{p_j}$，矛盾。所以

$$
p_j\to p,\ r(p_j)=r(p),\ h_j\in\partial_{L_{p_j}}N_{p_j},\ h_j\to h
\quad\Longrightarrow\quad h\in\partial_{L_p}N_p.
\tag{XI148.8}
$$

对 $s\in P_{\max}$，一个非零 $R$ 阶子式在其附近仍非零，而全部原纯秩不超过 $R$，故所有充分靠近 $s$ 的原纯点均秩 $R$。147.2给该处对任意原纯趋近的整球连续；任何效应聚点在 $s$ 读一、在整个 $D_s$ 读零，由唯一整球零确认即为 $e_s$。故 $e$ 也在 $s$ 对全部原纯趋近连续。

反设 $D_{a_j}\to\{s\}$。整个 $S_{a_j}$ 的点趋于 $s$，刚得的连续性给

$$
\sup_{t\in S_{a_j}}\|\widehat e_t-\widehat e_s\|\to0.
\tag{XI148.9}
$$

若一致性失败，选违反它的 $t_j\in S_{a_j}$ 就与 $t_j\to s$ 的效应连续矛盾。归一化合法：$z\in\operatorname{int}C$ 给所有正 $h$ 的 $h(z)\ge\delta\|h\|$，且 $e_t(t)=1$ 使这些效应的范数统一远离零。完整法向基(XI148.3)于是使 $\widehat g_{a_j}\to\widehat e_s$。

任选 $t_j\in S_{a_j}$。$g_{a_j}(t_j)=1$、$t_j\to s$，且 $g_{a_j}\in\mathcal E$。任取聚点 $g$，则 $g(s)=1$；归一化极限使 $g$ 与 $e_s$ 正比例，两者在 $s$ 都读一，故 $g=e_s$。因此

$$
g_{a_j}\to e_s,\qquad e_{a_j}\to g_s.
\tag{XI148.10}
$$

原零对称给 $a_j\in S_{t_j}$，全部边界射线公式给 $e_{a_j}\in\partial_{L_{t_j}}N_{t_j}$。由于 $t_j\to s$ 最终同为最高秩，(XI148.8)迫 $g_s\in\partial_{L_s}N_s$，违反 $g_s\in\operatorname{ri}N_s$。证毕。

### 148.3 整球内部的秩屏障与真正跨秩连续

**定理 148.3（最高秩邻球的支撑屏障）。** 在同一完整原域与忠实截面下，若 $S_p\cap P_{\max}\ne\varnothing$，则 $d_p>R$，每个 $x\in\operatorname{ri}D_p$ 均有 $\operatorname{rank}A(x)=d_p$，并且 $\overline P^{\,K}\cap D_p=S_p$。若更有 $S_p\subseteq P_{\max}$，则对任意原纯序列 $p_j\to p$ 均有 $D_{p_j}\to D_p$、$e_{p_j}\to e_p$。

证明。对每个 $x\in D_p$，对径点 $2c_p-x\in D_p$ 给 $A(c_p)=(A(x)+A(2c_p-x))/2$，所以 $\operatorname{ran}A(x)\subseteq W_p$。取 $s\in S_p\cap P_{\max}$，有 $d_p\ge R$。若等号成立，$A(s)$ 在 $W_p$ 上正定。对任意 $x\in D_p\setminus\{s\}$ 取充分小 $0<\varepsilon<1$，则 $A(s)-\varepsilon A(x)\succeq0$。忠实截面等式给

$$
y=\frac{s-\varepsilon x}{1-\varepsilon}\in K,\qquad
s=\varepsilon x+(1-\varepsilon)y,
\tag{XI148.11}
$$

这违反原 $s$ 的纯性，故 $d_p>R$。$x,c_p$ 同在 $D_p$ 的相对内部时，各能减去对方的一个小正倍数而仍在 $C$；正矩阵的互相正支配使两者的核相同，故内点秩恒为 $d_p$。原纯像均秩不超过 $R$，而矩阵秩不超过 $R$ 是闭条件。因此任何原纯极限都不能在 $\operatorname{ri}D_p$，得到所述闭包交式。

再设 $S_p\subseteq P_{\max}$。对任意 $p_j\to p$ 及其任意子列，取有界正交半轴及效应的共同再收敛子列，写

$$
D_{p_j}=c_j+B_j\overline{\mathbb B}^3\to E=c+B\overline{\mathbb B}^3,\qquad
e_{p_j}\to f\in\mathcal E.
\tag{XI148.12}
$$

$f(p)=1$、$f|_E=0$ 按原 minimum 定义给 $E\subseteq D_p$。对每个单位 $v$，原纯球缘 $c_j+B_jv$ 的极限在 $\overline P^{\,K}\cap D_p=S_p$，故 $c+BS^2\subseteq S_p$。若 $\operatorname{rank}B<3$，单位核方向补长度给 $BS^2=B\overline{\mathbb B}^3$；于是凸 $E$ 全包含于严格凸球面 $S_p$，只能是 $\{s\}$、$s\in S_p\subseteq P_{\max}$。148.2排除此分支。

若 $\operatorname{rank}B=3$，$E,D_p$ 的仿射包相同，且 $\partial_{\rm rel}E\subseteq\partial_{\rm rel}D_p$。若 $E\ne D_p$，可取 $\operatorname{ri}E$ 内一点及 $\operatorname{ri}D_p\setminus E$ 内一点；连线第一次离开 $E$ 的点属于 $\partial E\cap\operatorname{ri}D_p$，矛盾。因此所有再子列均给 $E=D_p$，整列球连续。效应聚点在 $p$ 读一并在整个 $D_p$ 读零，唯一性给 $f=e_p$。这里没有把固定母球连续或同秩连续当作跨秩连续。证毕。

### 148.4 零边的最高秩覆盖与有限阶排除

**定理 148.4（每条零边触及最高纯秩足以重构）。** 在定义148.1的完整 EB3+$\mathsf{Conn}$ 及忠实有限 PSD 截面下，若

$$
\forall p,q\in P:\quad p\perp q\ \Longrightarrow\ p\in P_{\max}\ \text{或}\ q\in P_{\max},
\tag{XI148.13}
$$

则同一原锥、同一原单位有复三能级表示；不另要求 ZC、全域连续性或原维数上界。

证明。最高秩点处的任意原纯趋近最终同秩，由147.2给整球连续。若 $p\notin P_{\max}$，(XI148.13)给 $S_p\subseteq P_{\max}$，由148.3取得该处的任意跨秩连续。故整个 $P$ 上 $D$ 连续。Conn 已给 Inj，准确调用[IX118.3、118.5、118.8][Q148IX]的同原分类，得到

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,\qquad
\Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XI148.14}
$$

整球连续是以上推导的中间结论。证毕。

**定理 148.5（复五阶、实七阶迫出真实三角）。** 在完整 EB3+$\mathsf{Conn}$ 及忠实有效 PSD 截面下，若 $\mathbb F=\mathbb C,m\le5$ 或 $\mathbb F=\mathbb R,m\le7$，则原零图存在三个不同、两两零比较的原纯标签。再加146.1的原义 ZC，即有(XI148.14)。

证明。令 $k_p=\dim_{\mathbb F}J_p$。由 $\dim L_p=4$ 及(XI148.4)，复情形 $4\le k_p^2$，实情形 $4\le k_p(k_p+1)/2$，故

$$
R\le m-2\quad(\mathbb F=\mathbb C),\qquad
R\le m-3\quad(\mathbb F=\mathbb R).
\tag{XI148.15}
$$

反设没有实际三角 Seed。复用147.5的共同核机制：对实际零边 $p\perp q$，非零共同核向量 $v$ 会给非零原正 $h_v(x)=v^*A(x)v$ 在两端同零；其整个非点真面按原面分类为某个 $D_a$，从而产生实际第三纯标签 $a$。因此无 Seed 时每条零边满足

$$
J_p\cap J_q=\{0\},\qquad r(p)+r(q)\ge m.
\tag{XI148.16}
$$

若该边两端均非最高秩，则 $r(p)+r(q)\le2(R-1)$。复 $m\le5$ 时由(XI148.15)有 $2(R-1)\le2m-6<m$；实 $m\le7$ 时有 $2(R-1)\le2m-8<m$。均矛盾。所以每条零边至少一端最高秩，148.4给同原 qutrit。标准 qutrit 的三个正交秩一投影运输回整个原域又给 Seed，违反反设。因此这些阶数必有实际 Seed。

最后才在原义 ZC 下调用140.4的 Seed 传播，得到(XI148.14)。阶数迫出 Seed 不使用 ZC；一般已有 Seed 之后的全域传播仍保留该额外前件。证毕。

### 148.5 剩余谱规格与完整静态后果

**定理 148.6（非量子有限截面的中间秩零边）。** 在完整 EB3+$\mathsf{Conn}$+原义 ZC及忠实有限截面下，若不存在(XI148.14)，则存在实际零边 $p\perp q$，满足

$$
r(p)<R,\qquad r(q)<R,\qquad
m\le r(p)+r(q)\le2(R-1),\qquad
R\ge\left\lceil\frac m2\right\rceil+1.
\tag{XI148.17}
$$

其有效阶数至少复六、实八。在复 $m=6$ 时必有 $R=4$ 及一条 $3$—$3$ 零边，两端复三维核互补；在实 $m=8$ 时必有 $R=5$ 及一条 $4$—$4$ 零边，两端实四维核互补。复六阶若 $p_j\to p\in P$ 而 $D_{p_j}\not\to D_p$，可选坏子列始终有 $r(p_j)=4,r(p)=3$；实八阶相应仅可为 $5\to4$。

证明。148.4的逆否给两端均非最高秩的零边；若有 Seed，140.4在当前完整前件下已给(XI148.14)，故这里无 Seed，(XI148.16)遂给(XI148.17)。148.5给最低阶数。在复六阶，(XI148.15)、(XI148.17)合给 $R=4$，所选边两端秩至多三且和至少六，故均三；共同核为零及维数和为六给互补。任取纯点，其零邻点非空且秩至多四，(XI148.16)又给其秩至少二。因此纯秩仅为二、三、四；秩二点的全部零邻点均秩四，148.3给其连续，秩四点本已连续。坏纯极限仅能在秩三点；147.4的恒定秩严格下降子列遂只能 $4\to3$。实八阶同理：$R=5$、纯秩为三至五、秩三点的全部邻点秩五，所选非最高零边为四—四，坏子列仅 $5\to4$。证毕。

**定理 148.7（同一菜单的全部混态读数及归属边界）。** 在148.4或148.5已得到(XI148.14)的各自完整前件下，145.9的整个静态字典通过同一个 $\Phi$ 适用。具体地，对全部 $\rho\succeq0,\operatorname{Tr}\rho=1$ 和全部单位 $v\in\mathbb C^3$，置 $p_v=\Phi(vv^*)$、$Q_v=I-vv^*$，则整个原确认菜单及原最低值为

$$
\mathcal F_{p_v}=\{f_{vv^*+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\},\qquad
T_{p_v}(\Phi\rho)=v^*\rho v,
\tag{XI148.18}
$$

其中 $f_H(\Phi X)=\operatorname{Tr}(HX)$，最低值由原菜单中的 $B=0$ 达到；$D_{p_v}$ 是 $v^\perp$ 上全部迹一正矩阵的完整三球。原实维数为九。实际仪器、任意有限联合及纠缠、全旁观 CP、记录与未来、物理钟、Hamiltonian和能量仍取145.9的各自原合同。

证明。完整字典直接复用145.9及其来源，不将确认菜单缩成唯一 $e_{p_v}$。上述 minimum 在所有原混输入和全部确认者上量化，不只在纯标签或部分效应上核对。148.6给必要谱约束，没有构造所述更高阶非量子模型。一般原锥的自动有限 PSD 表示、一般自动九维上界，以及复六／实八及更高阶的中间秩边排除均仍未证明；纯端点互易也未被解释成实际测量次序可交换。

归属采用 `repo-derived` 综合推导。正代表及同秩邻点运输准确复用147.2；完整法向基、全部边界射线与相对内部准确复用145.3及所引来源。新增承重连接是同秩法向边界稳定与完整法向基共同排除最高纯秩单点塌缩，再以整球支撑的严格秩增长处理所有邻点最高秩的真正跨秩极限。由此得到148.4的全域重构入口及148.5—148.6的下一阶排除与中间秩规格。相对内部的正代表、固定有限基的小扰动、正矩阵共同支撑及闭秩条件只作这些连接的中间工具。核面描述的经典背景是[Ramana—Goldman，Theorem 1、Corollary 1][Q148RG]及[Netzer—Plaumann—Schweighofer，Theorem 2.3][Q148NPS]；这些文献不被用作一般原锥具有矩阵表示、全域纯点紧性或原面格模性的证明。证毕。

[Q148IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "118.3、118.5、118.8：整球连续到同原锥、同原单位分类。"
[Q148RG]: https://doi.org/10.1007/BF01100204 "M. V. Ramana and A. J. Goldman, Some geometric results in semidefinite programming, Journal of Global Optimization 7 (1995), 33—50，Theorem 1及Corollary 1。"
[Q148NPS]: https://arxiv.org/abs/0902.3345 "Tim Netzer, Daniel Plaumann and Markus Schweighofer, Exposed Faces of Semidefinitely Representable Sets, SIAM Journal on Optimization 20 (2010), 1944—1955，Theorem 2.3。"

## 追加锚（本行以下为增补区）

## 149. 零边球心互易、全方向高度刚性与同原量子几何

### 149.1 只在真实二元关系上的球心互易

**定义 149.1（完整原域与球心互易）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C$ 及在 $C\setminus\{0\}$ 上严格正的原单位 $u$，保留

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\\
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p .
\end{gathered}
\tag{XI149.1}
$$

minimum 对每个原混态和整个原确认菜单取得。完整 EB3 指每个 $D_p$ 是非退化仿射实心三球，其中心为 $c_p$。$p\perp q$ 指 $q\in S_p$；补效应使它对称。$\mathsf{Conn}$ 指全部原纯标签之间均有有限原零边路。

以下先保留 EB3+$\mathsf{Conn}$。复用144.1、145.3及其原来源：全部 $P=P_0$，存在唯一整球零确认 $e_p$，且

$$
\begin{gathered}
\{f\in\mathcal F_p:f|_{D_p}=0\}=\{e_p\},\qquad
e_p^{-1}(0)\cap K=D_p,\qquad e_p^{-1}(1)\cap K=\{p\},\\
g_p=u-e_p,\qquad
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}N_p,\\
\dim L_p=4,\qquad L_p\longrightarrow\operatorname{Aff}(D_p)
\text{ 的限制是线性同构}.
\end{gathered}
\tag{XI149.2}
$$

球心互易候选只约束真实零边：

$$
\boxed{\qquad
\mathsf{CR}_c:\quad
\forall p,q\in P,\quad p\perp q\ \Longrightarrow\
e_p(c_q)=e_q(c_p).
\qquad}
\tag{XI149.3}
$$

这里的球心及整球零尺均由同一原域定义，没有附加数值、矩阵表示或维数上界。$\mathsf{CR}_c$ 是这些内生对象间新增的模型约束，不是仅凭定义已经成立的恒等式；也没有把 $\mathcal F_p$ 缩成 $\{e_p\}$，或把最低确认互易 $T_p(q)=T_q(p)$ 作为其同义词。

### 149.2 单根互易先支付闭影像与一阶正则性

**定理 149.2（单根球心互易给全方向正高度与闭影像）。** 固定任意原根 $p$，只对这个根假设

$$
e_p(c_q)=e_q(c_p)\qquad(q\in S_p).
\tag{XI149.4}
$$

在其任一完整球图中写

$$
\begin{gathered}
D_p=c_p+B\overline B^3,\quad q_v=c_p+Bv,\quad v\in S^2,\quad
g=g_p,\quad H(c_p+Bw)=w,\quad H_i\in L_p,\\
\rho(v)=\sup_{x\in K\setminus\{p\}}
\frac{-v\cdot H(x)}{g(x)},\quad
a_v=2c_{q_v}-p,\quad m(v)=g(a_v),\\
Z=\{H(x)/g(x):x\in K\setminus\{p\}\},\qquad
z_v=H(a_v)/m(v).
\end{gathered}
\tag{XI149.5}
$$

则 $\rho$ 有限且 Lipschitz，并有

$$
\boxed{\quad
m(v)=\frac{2}{1+\rho(v)},\qquad
0<\sigma_p:=\frac{2}{1+\max_{S^2}\rho}\le m(v)\le1,\qquad
Z=\overline Z .
\quad}
\tag{XI149.6}
$$

此外每个非零方向的完整支撑面只有一个点，

$$
\rho\in C^1(\mathbb R^3\setminus\{0\}),\qquad
\nabla\rho(v)=-z_v\quad(v\in S^2).
\tag{XI149.7}
$$

这些结论不需要 ZC、全纯域紧性或跨球连续性。

证明。[THREE_COPY VII122.2—122.4][Q149TC]及[SAME_READBACK123.2][Q149SR]所需的 $p\in P_0$、邻标签仍在 $P_0$、Inj及限制同构，均由(XI149.2)支付。它们给 $\rho(v)\ge\|v\|$、有界凸影像 $Z$，以及整个原 $V$ 上的

$$
e_{q_v}=\frac{\rho(v)g+v\cdot H}{1+\rho(v)},\qquad
h_{\overline Z}(-v)=\rho(v),\qquad
Z\cap\operatorname*{argmax}_{z\in\overline Z}(-v)\cdot z=\{z_v\}.
\tag{XI149.8}
$$

真实邻球 $D_{q_v}$ 包含球缘点 $p$，其对径点正是 $a_v$。$g$ 在这颗完整球上唯一零于 $p$，故在 $a_v$ 达到唯一最大值 $m(v)\in(0,1]$。在 $c_p$ 评价第一式，再用单根互易及 $2c_{q_v}=p+a_v$，得到

$$
1-\frac{m(v)}2=e_p(c_{q_v})
=e_{q_v}(c_p)=\frac{\rho(v)}{1+\rho(v)}.
\tag{XI149.9}
$$

这直接给出(XI149.6)的高度式及统一正下界，尚未用任何球心连续性。

令

$$
A_{\sigma_p}=\{H(x)/g(x):x\in K,\ g(x)\ge\sigma_p\}.
\tag{XI149.10}
$$

它是紧集，也是凸集。具体地，若 $z_i=H(x_i)/g(x_i)$、$g(x_i)\ge\sigma_p$，则任给 $0\le t\le1$，实际原混态

$$
x=
\frac{t x_1/g(x_1)+(1-t)x_2/g(x_2)}
{t/g(x_1)+(1-t)/g(x_2)}
\tag{XI149.11}
$$

满足 $H(x)/g(x)=tz_1+(1-t)z_2$ 及
$g(x)=(t/g(x_1)+(1-t)/g(x_2))^{-1}\ge\sigma_p$。
每个真实接触值 $z_v$ 已由 $a_v$ 在此紧凸集中实现。因此
$A_{\sigma_p}\subseteq Z\subseteq\overline Z$，且三者在每个方向的支撑值相同；有限维分离给
$A_{\sigma_p}=Z=\overline Z$。现在才可由(XI149.8)把完整支撑面也判成单点，而不是把“唯一实际接触”提前等同于“闭包只有一个接触”。

最后使用紧凸体支撑函数的一阶性质，作为本推导的中间步骤。若 $z(n)$ 是非零方向 $n$ 的唯一支撑点，紧性与唯一性先给 $z(n)$ 连续，支撑不等式给

$$
0\le h_Z(n+k)-h_Z(n)-k\cdot z(n)
\le k\cdot\bigl(z(n+k)-z(n)\bigr)=o(\|k\|).
\tag{XI149.12}
$$

故 $h_Z$ 在非零方向 $C^1$；用 $\rho(v)=h_Z(-v)$ 得(XI149.7)。这里也复用了123.5的同一支撑微分论证，但其正高度入口由(XI149.9)另行支付，不假设 $p\in P_{\rm reg}$。证毕。

### 149.3 原效应上界消除单根方向差异

**定理 149.3（单根互易的全方向常值刚性）。** 在149.2的同一完整前件下，存在 $R_p\ge1$，使

$$
\boxed{\qquad
\rho(v)=R_p,\qquad
m(v)=\frac{2}{1+R_p},\qquad
e_p(c_q)=\frac{R_p}{1+R_p}
\quad(v\in S^2,\ q\in S_p).
\qquad}
\tag{XI149.13}
$$

证明。置 $d(v)=e_{a_v}(p)$。由于 $a_v\ne p$，(XI149.2)给 $0\le d(v)<1$。SAME_READBACK123.3是两个实际球图经限制同构在整个原空间消元的恒等式；其前件是 $P_0$ 接口，不要求 $P_{\rm reg}$。按本章参数对应，

$$
\begin{gathered}
R_v=u-e_p-e_{q_v}=\frac{g-v\cdot H}{1+\rho(v)},\\
e_{a_v}=d(v)e_p+
\left(d(v)+\frac{1-d(v)}{m(v)}\right)R_v .
\end{gathered}
\tag{XI149.14}
$$

这里 $R_v$ 未被假设为正效应。定义同一支撑函数的余差

$$
\mathfrak B(v,w)=\rho(v)-\rho(w)-\nabla\rho(w)\cdot(v-w)\ge0.
\tag{XI149.15}
$$

已有 $H(a_w)=m(w)z_w$、$\nabla\rho(w)=-z_w$ 及 $w\cdot z_w=-\rho(w)$，故

$$
R_v(a_w)=m(w)\left(1-\frac{\mathfrak B(v,w)}{1+\rho(v)}\right).
\tag{XI149.16}
$$

使用合法原效应在实际原态上的上界 $e_{a_v}(a_w)\le1$，与 SAME_READBACK124.3同样的代入给

$$
\begin{aligned}
(1-d(v))(m(w)-m(v))
&\le\bigl(d(v)m(v)+1-d(v)\bigr)m(w)
\frac{\mathfrak B(v,w)}{1+\rho(v)}\\
&\le\frac{\mathfrak B(v,w)}{1+\rho(v)} .
\end{aligned}
\tag{XI149.17}
$$

完整消元式和原上界都在同一个实现中，且 $m(v),m(w)\le1$；没有将不同原态上的分别最优值拼接成共同实现。

由149.2，$\rho$ 在非零方向 $C^1$，而 $m=2/(1+\rho)$ 在球面上也已 $C^1$。固定 $v$，沿任一光滑双向球面弧 $w(t)$、$w(0)=v$，有
$\mathfrak B(v,w(t))=o(|t|)$。这可由(XI149.12)或沿短线段积分连续梯度得到。将(XI149.17)除以严格正的 $(1-d(v))(1+\rho(v))$：对 $t>0$、$t<0$ 分别除以 $t$ 并取极限，得到

$$
\left.\frac{d}{dt}m(w(t))\right|_{t=0}\le0,\qquad
\left.\frac{d}{dt}m(w(t))\right|_{t=0}\ge0 .
\tag{XI149.18}
$$

所以所有切向导数均为零；$S^2$ 连通，$m$ 在整个球面常值，(XI149.6)使 $\rho$ 常值，(XI149.9)再给全部邻球心的同值式。这里不需要 $d$ 连续、统一的反向缺口或旧124.4中另列的正规锚点前件。证毕。

### 149.4 从真实零边互易到同原三能级表示

**定理 149.4（球心互易的完整静态重构）。** 在(XI149.1)全部原量词及完整 EB3+$\mathsf{Conn}$ 下，以下三项等价：球心互易 $\mathsf{CR}_c$；144.1的全域同值 $\mathsf{UC}$；存在实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V,\qquad
\Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{XI149.19}
$$

成立时每条真实零边必有 $e_p(c_q)=1/2$；每个原球图的 $\rho_p(v)=\|v\|$。不另外输入 ZC、Seed、有限矩阵表示、九维上界或任一全域连续性。

证明。假设 $\mathsf{CR}_c$，对每个原根用149.2—149.3，记
$h_p=R_p/(1+R_p)\in[1/2,1)$。对任一真实零边 $p\perp q$，

$$
h_p=e_p(c_q)=e_q(c_p)=h_q .
\tag{XI149.20}
$$

$\mathsf{Conn}$ 使全部 $h_p$ 等于同一 $h<1$，即先固定一个根并沿每条有限零路传递其数值。因而对任意 $a\in P$、任意 $x\in S_a$，完整球内对径 $\bar x=2c_a-x$ 仍在 $S_a$，有

$$
e_a(c_x)+e_a(c_{\bar x})=2h=:\kappa<2 .
\tag{XI149.21}
$$

这正是原义 UC，其全标签量词及同一严格余量 $2-\kappa>0$ 已付清。直接消费144.5给(XI149.19)，不再证明已有分类链。

反向在整个标准三能级域，$e_p(\rho)=\operatorname{Tr}(p\rho)$、
$c_q=(I_3-q)/2$；若 $p\perp q$，则
$e_p(c_q)=(1-\operatorname{Tr}(pq))/2=1/2=e_q(c_p)$。
完整 EB3及全部原纯域的 Conn由142.2的标准反向给出。144.5同时给 UC与(XI149.19)的双向对应。于是 $\kappa=1$、$h=1/2$、$R_p=1$；由正齐次性得全部非零方向的 $\rho_p(v)=\|v\|$，零方向也成立。证毕。

这把先逐根连续、再给全域预算的旧入口替换为真实零边上的一个对称读数条件；所得静态模型与 UC相同，不声称逻辑上严格更弱或公理个数最少。若在 EB3+$\mathsf{Conn}$ 下没有(XI149.19)，本定理的逆否给出至少一条实际零边上的可读不对称 $e_p(c_q)\ne e_q(c_p)$。

### 149.5 完整菜单、简洁几何与交换两端的边界

**定理 149.5（同一原模型的全混态字典与次序边界）。** 在149.4的等价前件下，145.9的整个静态字典通过同一个 $\Phi$ 适用。具体地，置 $p_v=\Phi(vv^*)$、$Q_v=I_3-vv^*$、$f_M(\Phi X)=\operatorname{Tr}(MX)$，其中 $\|v\|=1$，则

$$
\begin{gathered}
K=\{\Phi\rho:\rho\succeq0,\ \operatorname{Tr}\rho=1\},\qquad
P=\{\Phi(vv^*):\|v\|=1\}\cong\mathbb{CP}^2,\\
\mathcal E=\{f_M:0\preceq M\preceq I_3\},\\
\mathcal F_{p_v}=\{f_{vv^*+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\},\\
T_{p_v}(\Phi\rho)=v^*\rho v,\qquad
D_{p_v}=\{\Phi\rho:\rho\succeq0,\ \operatorname{Tr}\rho=1,\ \rho v=0\}.
\end{gathered}
\tag{XI149.22}
$$

原确认菜单完整且非单点，$B=0$ 在全部原混输入上达到 minimum并给 least。每颗完整 $D_{p_v}$ 是 $v^\perp$ 上的整个二阶密度球，球缘为 $\mathbb{CP}^1\cong S^2$；整个原实维数为九。令 $U=\Phi(I_3)$，则原球心图延拓为

$$
R(x)=\frac{u(x)U-x}{2},\qquad
c_p=R(p),\qquad
R(x)-U/3=-\frac12(x-U/3)\quad(x\in K).
\tag{XI149.23}
$$

因此其简洁几何是同一复射影平面中的完整复射影线及其凸球，全部球心围绕同一总体中心反向缩小一半。全部数学有限 POVM、谱、自对偶和 Jordan结构由145.9原字典供给。全纯端点最低确认互易也成立，但它不等于连续测量次序可交换。

证明。表示与字典的参数对应均直接复用145.9，不以选择一部分原态、效应或测量替代(XI149.1)。特别是 $B\succeq0$ 使 $\operatorname{Tr}(B\rho)\ge0$，故上述 $B=0$ 对每个原混输入实现 minimum；正性给 $v^*\rho v=0$ 当且仅当 $\rho v=0$，保留整个零球。其余几何式由 $c_{p_v}=\Phi((I_3-vv^*)/2)$ 得到。端点互易为
$T_{p_v}(p_w)=|v^*w|^2=T_{p_w}(p_v)$。

次序边界可在同一个已得模型内明确检验。取
$P_0=|0\rangle\langle0|$、
$Q_+=|+\rangle\langle+|$、
$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 和原输入 $\rho=P_0$。数学 Lüders 分支 $X\mapsto P_0XP_0$、
$X\mapsto Q_+XQ_+$ 给两个先后双成功概率

$$
\operatorname{Tr}(Q_+P_0\rho P_0)=\frac12,\qquad
\operatorname{Tr}(P_0Q_+\rho Q_+)=\frac14 .
\tag{XI149.24}
$$

此模型满足 $\mathsf{CR}_c$ 及全端点互易，却有不同的先后概率，因此两端交换不能推出这些数学顺序仪器交换。这一例子不供应实际可调用的仪器。实际来源与读回、任意有限复合及纠缠、全旁观 CP、逐输入预算、记录、全部未来与切口、物理钟、Hamiltonian、能量与数值 $\hbar$，仍分别保留145.9及其传递来源的完整原合同。

新增承重内容采用 repo-derived 综合推导归属：原整球零尺和完整法向接口生成真实零边的球心互易式；该式直接支付每根的全方向正高度，再以闭影像和原效应上界取得方向常值，最终沿有限零路支付原 UC的全标签预算。原法向图、实际接触纤维、双球消元及高度差估计分别准确复用 THREE_COPY VII122、SAME_READBACK123—124；UC分类与全部静态字典准确复用144.5和145.9。支撑函数的一阶论证只作中间工具，不作为独立新结果。成熟 Jordan分类的背景仍为 [Barnum—Müller—Ududec Theorem 16][Q149BMU]，其 projectivity、对称跃迁概率及保纯滤子的前件不由局部互易直接冒领，而只经既有完整分类链消费。这里不声明文献优先权，也未从裸 EB3+$\mathsf{Conn}$ 或纯端点 minimum互易导出 $\mathsf{CR}_c$。证毕。

[Q149TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "122.2—122.4：P0锚点的完整法向图、有界凸实际影像与唯一实际接触纤维；闭包支撑面不预设单点。"
[Q149SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "123.2—123.3：P0接口下的双球全原空间消元；123.5的闭影像与支撑微分；124.3的原效应上界和Bregman高度差；旧P_reg入口由149.2另付。"
[Q149BMU]: https://arxiv.org/html/1403.4147v4#Thmtheorem16 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory，Theorem 16的全部前件。"

## 追加锚（本行以下为增补区）
