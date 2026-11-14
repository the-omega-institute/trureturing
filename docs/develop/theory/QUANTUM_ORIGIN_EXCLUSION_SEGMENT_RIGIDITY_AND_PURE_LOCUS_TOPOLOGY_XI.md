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
