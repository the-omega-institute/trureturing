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

## 136. 完整零球的真实标签返回与固定根严格高段

### 136.1 全部原对象与显式根合同

**定义 136.1（完整原域、真实零确认与固定根）。** 取非零有限维实空间 $V$、闭尖生成凸锥
$C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的 $u\in V^\ast$。始终使用

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
C^\ast=\{f\in V^\ast:f(C)\subseteq\mathbb R_+\},\qquad
\mathcal E=[0,u]_{C^\ast},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\qquad
D_p=\{z\in K:T_p(z)=0\},\qquad S_p=P\cap D_p.
\end{gathered}
\tag{XI136.1}
$$

标签 $p$ 遍历全部 $P$，第二端点 $z$ 遍历整个 $K$。$K,\mathcal E,\mathcal F_p$ 的紧性与 minimum 达到沿用
[IX114.1—114.2][Q136IX]、[X133.1][Q136X]；确认族不缩成某个预选效应族。
以下 EB3 总指对每个原 $p\in P$，整个 $D_p$ 都仿射等价于完整闭三球。
纯零关系 $p\perp r\Longleftrightarrow T_p(r)=0$ 由补效应对称，且反自反。
纯 PR 则另指全部纯对的 $T_p(r)=T_r(p)$，不交换混态上的正读数。

复用 IX114.2、IX120.1、X133.1 的原面接口：每个 $D_p$ 是非点紧暴露极大真面，
$S_p=\partial_{\rm rel}D_p\cong S^2$，$D_p=\operatorname{conv}S_p$；
不同完整球的交为空或一个原纯单点，全部非空真面只有这些球与原纯单点。
记 $c_p$ 为 $D_p$ 的唯一中心，$I(F)=\{p\in P:D_p=F\}$，并记

$$
\mathcal A_p=\{e\in\mathcal F_p:K\cap\ker e=D_p\}.
\tag{XI136.2}
$$

此族非空。具体地，在 $c_p$ 取一张达到 $T_p(c_p)=0$ 的原效应 $e$；对任意
$z\in D_p$，其球心反射 $z'=2c_p-z$ 仍在 $D_p$，非负性与
$0=e(c_p)=(e(z)+e(z'))/2$ 使 $e$ 零于整个球。反向由 $0\le T_p\le e$ 得到准确零集。
这只是上述真实暴露接口的复用，不把 $e$ 说成全部确认效应的 least。
同样复用球上极值事实：若一张原效应在同一完整球的两点取一、零，这两点必是球的对径纯点。

在所有目标之前固定原 $o\in P$，置

$$
A=D_o,\qquad S=S_o,\qquad B=\bigcup_{s\in S}D_s,\qquad
w=o+2c_o.
\tag{XI136.3}
$$

这里 $w\in V$ 且 $u(w)=3$，不是归一状态；$B$ 收齐每个末球的全部混态。

**定义 136.2（根合同、局部带与关联的合法域）。** 显式根合同 $R_o$ 包含以下条件：
对每个 $s\in S$ 有原纯点 $a_s$，使 $(o,s,a_s)$ 是真实零三角；
$I(A)=\{o\}$ 且 $I(D_s)=\{s\}$ 对每个 $s\in S$ 成立；
$B$ 紧，$o\in B$ 且 $S\subseteq B$。三角的每条边均由同一完整原菜单内的效应见证。
这些是根与根邻点的条件，不包含 $P\subseteq B$、全 Pair 或全局 Inj。

在 $R_o$ 下，真实共同邻点只在已知覆盖的域上定义：

$$
\begin{gathered}
\pi_o:(P\cap B)\setminus\{o\}\longrightarrow S,\\
\{\pi_o(x)\}=A\cap D_x
=\{s\in S:o\perp s,\ x\perp s\}.
\end{gathered}
\tag{XI136.4}
$$

确实，$x\in B$ 给共同邻点存在；$x\ne o$ 与 $I(A)=\{o\}$ 给 $D_x\ne A$，
故点交接口给唯一性及纯性。根三角还迫 $a_s=2c_o-s$。
这个定义没有给尚未知属于 $B$ 的目标预取 $\pi_o(q)$。

局部条件 $L_\varepsilon(o)$ 是 X132.3 在这个固定根、同一个阈值上的原条件：

$$
\begin{gathered}
0<\varepsilon<1,\qquad
\forall z\in P:\quad 0<T_o(z)<\varepsilon\ \Longrightarrow\\
\exists s\in P:\ T_o(s)=T_z(s)=0.
\end{gathered}
\tag{XI136.5}
$$

它经零对称恰给该小正带的纯目标进入 $B$，不预付其余目标。
$L_\varepsilon(o)$ 单列供根合同的来源与高段消费者使用；下面的返回计算只用 $R_o$。

### 136.2 两球效应计算、原对径回送与分离裕量消去

**定理 136.3（保留邻边完成的单对真实标签返回）。** 在完整 EB3 与 $R_o$ 下，取

$$
q\in P\setminus(A\cup\{o\}),\qquad S_q\subseteq B.
\tag{XI136.6}
$$

此时 $h_q=\pi_o|_{S_q}:S_q\to S$ 是同胚；记 $x_s=h_q^{-1}(s)$。
另要求目标的全部真实邻边完成条件

$$
C_q:\quad \forall s\in S\ \exists y_s\in P:
\quad (s,x_s,y_s)\text{ 是真实零三角}.
\tag{XI136.7}
$$

若有一对满足反向纯比较

$$
\exists s_\ast\in S:\quad T_q(s_\ast)\le T_{s_\ast}(q),
\tag{XI136.8}
$$

则对任意真实 $e_o\in\mathcal A_o$、$e_q\in\mathcal A_q$，都有

$$
e_q(w)=1,\qquad q+2c_q=w,\qquad e_q(o)=e_o(q),\qquad
\min_{z\in A}e_q(z)=0,\qquad D_q\cap A\ne\varnothing,\qquad q\in B.
\tag{XI136.9}
$$

仅有根边 $(o,s)$ 的完成不能删除 $C_q$；后者完成的是另一条实际边 $(s,x_s)$。

证明。先说明复用 X133.5 的关联步骤在当前域内合法。
由 $q\notin A$ 及零对称，$o\notin S_q$；(XI136.6) 因而让整个 $S_q$ 落在
(XI136.4) 的定义域内。紧集

$$
\{(x,s,f)\in S_q\times S\times\mathcal E:f(s)=1,\ f(x)=0\}
\tag{XI136.10}
$$

在 $S_q\times S$ 上的投影正是 $h_q$ 的单值图。该图到 $S_q$ 是紧到 Hausdorff 的连续双射，
故 $h_q$ 连续。若两点同映到 $s$，它们都在 $D_q\cap D_s$；
$I(D_s)=\{s\}$ 与 $q\notin A$ 排除 $D_q=D_s$，点交接口遂给单射。
两端都是完整、紧、无边界的二维球面。区域不变性使连续单射的像开，紧性使像闭，
目标连通使其满射，所以为同胚。这是 [Hatcher，印刷页172，Theorem 2B.3、Corollary 2B.4][Q136H]
及 X133.5 的同一应用。它只支付完整极值范围，不直接支付两球相交。

固定上述真实 $e_o,e_q$，记

$$
\alpha=e_q(w),\qquad r=e_q(o),\qquad d=e_o(q),\qquad
t_s=e_q(s),\qquad b_s=e_o(x_s).
\tag{XI136.11}
$$

$q\notin A$ 给 $d>0$；若 $r=0$，则 $o\in D_q$，零对称会给 $q\in A$，故 $r>0$。
根三角中 $s,a_s$ 在 $A$ 内对径，$o,a_s$ 在 $D_s$ 内对径；因此
$s+a_s=2c_o$、$o+a_s=2c_s$。再用 $C_q$ 中的三角，得到

$$
s+2c_s=w,\qquad x_s+y_s=2c_s,\qquad s+y_s=2c_{x_s},\qquad
x_s+2c_{x_s}=w.
\tag{XI136.12}
$$

最后一个等式尚未涉及 $q$ 的球心，不能以 $q+2c_q=w$ 代替它。

在第一张完整球 $D_s$ 上取单位球坐标，令 $o$ 的坐标为 $v_s$、$x_s$ 的坐标为 $z_s$。
它们均为单位向量。真实 $e_o$ 在 $o,a_s$ 取一、零，所以其整个球上限制为
$(1+v_s\cdot z)/2$。真实 $x_s\in D_q$ 使 $e_q(x_s)=0$，而 $e_q(o)=r>0$；
非负仿射函数在球面零点的方向唯一，结合 $e_q(2c_s)=\alpha-t_s$ 得

$$
e_q(c_s+L_s z)=\frac{\alpha-t_s}{2}(1-z_s\cdot z),\qquad
b_s=\frac{1+v_s\cdot z_s}{2},\qquad
r=(\alpha-t_s)(1-b_s).
\tag{XI136.13}
$$

这里 $L_s$ 是该球图的线性部分；$\alpha-t_s>0$ 且 $1-b_s>0$，由 $r>0$ 保证。
这一步用整个 $D_s$ 上的原效应界，未以任意横截球替代 $D_q$。

真实零关系 $x_s\in D_q$ 经零对称使 $q\in D_{x_s}$，从而进入第二张完整球
$G_s=D_{x_s}$。$s$ 也在该球内。其中心满足 (XI136.12)，故 $e_q$ 的中心值为
$\alpha/2$；$q$ 是其取值一的球面点，因而整个球的最小值是 $\alpha-1$。
效应界给 $1\le\alpha\le2$。令 $\widehat q,\widehat s$ 为在这张球内的单位坐标，便有

$$
\begin{aligned}
e_q(c_{x_s}+L_{x_s}z)
 &=\frac\alpha2+\frac{2-\alpha}{2}\widehat q\cdot z,\\
e_o(c_{x_s}+L_{x_s}z)
 &=\frac{1-b_s}{2}(1-\widehat s\cdot z),\\
(2-\alpha)d&=(1-t_s)(1-b_s).
\end{aligned}
\tag{XI136.14}
$$

第二式使用 $e_o(s)=0$、$e_o(w)=1$ 及 $b_s<1$；第三式在同一球内分别于 $s,q$ 评价得到。
若 $\alpha=2$，第一式使每张 $G_s$ 上 $e_q\equiv1$，于是 $t_s=1$ 对全部 $s\in S$ 成立。
$A=\operatorname{conv}S$ 遂给 $e_q(c_o)=1$，但
$r=\alpha-2e_q(c_o)=0$，矛盾。因此

$$
1\le\alpha<2,\qquad
r(1-t_s)=(2-\alpha)d(\alpha-t_s)\quad(s\in S).
\tag{XI136.15}
$$

在使用反向比较之前，可准确看出正分离障碍：若 $t_s$ 取两个不同值，比较最后一个一次等式的系数与
常数项，得到 $r=(2-\alpha)d=\alpha(2-\alpha)d$，故 $\alpha=1$。
若 $\alpha>1$，只能有 $e_q|_A\equiv m$。第一式 (XI136.13) 及 $h_q$ 满射还给
$e_o|_{D_q}\equiv m/(\alpha-m)$，并有

$$
r=\alpha-2m>0,\qquad \alpha-1<m<\frac\alpha2,\qquad D_q\cap A=\varnothing.
\tag{XI136.16}
$$

其中 $m\ge\alpha-1$ 来自 $s\in G_s$ 与 (XI136.14) 的最小值。
若等号成立，$s$ 是 $q$ 在 $G_s$ 内的对径；$C_q$ 又使 $y_s$ 是 $s$ 在同一球的对径，
所以 $q=y_s\perp s$，与 $e_q(s)=m=\alpha-1>0$ 矛盾。
这些是正数分支的必要关系，不是满足整个原域的反模型。

现在由 (XI136.8) 排除该障碍。对任一完整球 $G$ 与其中的原纯点 $z$，
IX114.5 的证明中不使用 PR 的 (IX114.15)—(IX114.16) 给出

$$
T_z(c_G+L_G v)=1-\kappa_G(z)(1-\widehat z\cdot v),\qquad
0\le\kappa_G(z)\le\frac12.
\tag{XI136.17}
$$

原因是每张确认 $z$ 的原效应在整个球上必形如
$1-\lambda+\lambda\widehat z\cdot v$，$0\le\lambda\le1/2$；紧确认族中的最大 $\lambda$ 达到，
并同时实现球内所有 $v$ 的 minimum。这里并未使用 PR 才能得到的“各方向系数相同”。

在 $G_{s_\ast}$ 中，$C_q$ 给 $s_\ast,y_{s_\ast}$ 的真实正交对径，
所以 $\kappa_{G_{s_\ast}}(s_\ast)=1/2$。又 $q\ne s_\ast$，于是

$$
T_q(s_\ast)-T_{s_\ast}(q)
=\left(\frac12-\kappa_{G_{s_\ast}}(q)\right)
(1-\widehat q\cdot\widehat{s_\ast})\ge0.
\tag{XI136.18}
$$

反向不等式使其为零，后一因子严格正，故 $\kappa_{G_{s_\ast}}(q)=1/2$。
$q$ 的这张球内对径因而有原最低值零，属于真实 $D_q$；
在它上面，(XI136.14) 的真实 $e_q$ 取值 $\alpha-1$，准确零集迫 $\alpha=1$。
(XI136.13)—(XI136.14) 随即给 $d=r$，因为 $1-t_s>0$：若 $t_s=1$，第一式将给 $r=0$。

对任意 $s\in S$，此时才取

$$
q_s^-=2c_{x_s}-q=w-x_s-q.
\tag{XI136.19}
$$

它是 $G_s$ 的原纯对径点，且 $e_q(q_s^-)=\alpha-1=0$。
先由准确零集得 $q_s^-\in D_q$，再注意 $x_s\in D_q$ 且 $q_s^-\in D_{x_s}$。
二者原正交，在同一完整球 $D_q$ 内互为对径，因此

$$
2c_q=x_s+q_s^-=w-q.
\tag{XI136.20}
$$

这是真实标签的回送：球心关系是零值与原正交推出的结论，不是输入。

还须消去 $A$ 与 $D_q$ 之间的可能正间隔。写完整根球
$A=c_o+L_A\overline{\mathbb B}^{\,3}$，置

$$
m=e_q(c_o),\qquad v=\|e_q\circ L_A\|_2,\qquad
0\le v\le m<\frac12,\qquad r=1-2m.
\tag{XI136.21}
$$

非负性给 $v\le m$，$r>0$ 给严格上界。由 (XI136.20)、$e_o(w)=1$ 及 $d=r$，
$e_o(c_q)=(1-d)/2=m$。$s$ 遍历完整 $S$ 时，$t_s$ 遍历整个区间
$[m-v,m+v]$；第一球恒等式给

$$
b_s=1-\frac r{1-t_s}.
\tag{XI136.22}
$$

此函数随 $t_s$ 严格递减。$m+v\le2m<1$ 保证全部分母严格正；
$s\mapsto x_s$ 遍历完整 $S_q$，所以 $e_o$ 在整个 $D_q$ 上的两个极值恰为

$$
\min_{D_q}e_o=\frac{m-v}{1-m-v},\qquad
\max_{D_q}e_o=\frac{m+v}{1-m+v}.
\tag{XI136.23}
$$

这里满射只用于保证真实球面的两个极值都被取遍。
仿射函数在完整球上的极值和等于中心值的两倍，故

$$
\frac{m-v}{1-m-v}+\frac{m+v}{1-m+v}=2m,
\qquad 2(1-m)(m^2-v^2)=0.
\tag{XI136.24}
$$

第二式是第一式乘以正数 $(1-m)^2-v^2$ 后的结果。
$m\ge v\ge0$、$m<1/2$ 迫 $m=v$，于是 $\min_Ae_q=m-v=0$。
最小值在紧 $A$ 达到，真实零集给 $D_q\cap A\ne\varnothing$。
$I(A)=\{o\}$ 与 $q\ne o$ 排除 $D_q=A$，故交恰为原纯点 $s\in S$。
零对称将 $s\in D_q$ 送回 $q\in D_s\subseteq B$，完成 (XI136.9)。证毕。

### 136.3 完整纯 PR 的逐项供应与同阈值高段

**推论 136.4（固定根小正条件下的条件返回及严格高段）。** 在定义136.1的整个原域中，假设
完整 EB3、完整纯 PR，以及对事先固定的同一个 $o$ 成立的 $L_\varepsilon(o)$。
则 $R_o$ 成立；对每个满足 (XI136.6) 的目标，$C_q$ 与 (XI136.8) 均成立，
因而具有定理136.3的全部真实标签返回结论。特别地，

$$
\{q\in P:0<T_o(q)<\varepsilon\}\ \cup\ S\ \cup
\{q\in P:T_o(q)>1-\varepsilon\}\ \subseteq B.
\tag{XI136.25}
$$

这里高段使用的正是 $L_\varepsilon(o)$ 的阈值，不另选更有利的阈值。

证明。先支付根合同，不调用 X133.6 的全覆盖结论。
固定 $S\cong S^2$，由 X130.2、X133.3 的同一紧见证投影，

$$
B=\operatorname{pr}_K
\{(s,z,f)\in S\times K\times\mathcal E:f(s)=1,\ f(z)=0\}
\tag{XI136.26}
$$

紧闭。零对称给 $o\in D_s$ 对任意 $s\in S$ 成立，故 $o\in B$。
$L_\varepsilon(o)$ 已经把全部原小正带目标送入这个固定 $B$。

逐点复用 X132.4 在 $p=o$ 的证明：若 $o$ 无真实三角，则 $A\cap B=\varnothing$。
否则从某个非空紧原面 $A\cap D_s$ 的极点取原纯点，就给 $o,s$ 的第三点。
紧效应区间使固定 $T_o$ 为一致 Lipschitz 效应族的 minimum，所以在紧 $B$ 上有
$\mu=\min_BT_o>0$。X132.2 供应原纯 $z$，满足
$0<T_o(z)<\min\{\mu,\varepsilon\}$；但 $L_\varepsilon(o)$ 又给 $z\in B$，矛盾。
因此根有一个真实三角，X133.2 的标签论证给 $I(A)=\{o\}$。
这一固定根反证只消费 $L_\varepsilon(o)$，没有把它提升成每根条件 $\mathsf L$。

该根三角在 $A$ 上给一条原效应读满一、零的直径。
现在使用 IX114.5 的完整纯 PR 共同刻度：$A$ 中某一纯方向的系数为 $1/2$，
故所有纯方向的共同系数都是 $1/2$。对每个 $s\in S$，原球内对径
$a_s=2c_o-s$ 遂满足 $T_s(a_s)=0$，从而 $(o,s,a_s)$ 是实际根三角。
X133.2 给每个 $I(D_s)=\{s\}$；同时 $s\in D_{a_s}\subseteq B$，故 $S\subseteq B$。
连同 (XI136.26) 与 $o\in B$，这逐项支付了 $R_o$。
关联的合法域与目标上完整球面的同胚性，已在 (XI136.4)、(XI136.10) 按这些根条件证明。
整个论证不需要给未覆盖目标定义 $\pi_o(q)$。

接着支付 $C_q$。对每个 $s\in S$，刚取得的根三角在 $D_s$ 上给 $o,a_s$ 的满刻度直径。
再次应用 IX114.5，$D_s$ 的共同系数为 $1/2$。
于是对每个 $x\in S_s$，其同一完整球内对径 $y=2c_s-x$ 满足 $T_x(y)=0$。
三点 $(s,x,y)$ 因而是原纯零三角。对实际的 $x=x_s$ 使用它，就给全部 $C_q$；
这一步并非把根三角本身改称邻边三角。
完整纯 PR 还对任一 $q,s$ 给 $T_q(s)=T_s(q)$，故任取一个 $s$ 即满足 (XI136.8)。
定理136.3现在给所有满足 $S_q\subseteq B$ 的上述目标返回。

最后只对严格高段支付该前件。若 $q=o$，已由 $o\in B$ 处理。
其余取 $q\in P$ 且 $T_o(q)>1-\varepsilon$，因 $\varepsilon<1$，有 $q\notin A$。
对任意 $x\in S_q$，取真实 $f\in\mathcal F_q$ 使 $f(x)=0$；
$u-f\in\mathcal F_x$。在同一个原纯根 $o$ 上评价，并且只对纯对使用 PR，得到

$$
T_o(q)+T_o(x)=T_q(o)+T_x(o)
\le f(o)+(u-f)(o)=1.
\tag{XI136.27}
$$

于是 $0\le T_o(x)<\varepsilon$。若为零，则 $x\in S\subseteq B$；若严格正，则
$L_\varepsilon(o)$ 给 $x\in B$。这对整个真实 $S_q$ 的每一点成立，所以 $S_q\subseteq B$，
定理136.3使 $q\in B$。小正带与 $S$ 的包含已逐项证明，得到 (XI136.25)。证毕。

### 136.4 适用边界与数学来源

**约定 136.5（未付区域、原菜单与复用范围）。** (XI136.25) 只包含所写的开比较带。
在 $T_o(q)=1-\varepsilon$ 时，(XI136.27) 只给 $T_o(x)\le\varepsilon$，
不能调用要求严格小于 $\varepsilon$ 的局部条件；等号点只有另行落在已付区域时才被覆盖。
未由 (XI136.25) 支付的中间读数只在 $0<\varepsilon\le1/2$ 时出现，其范围为
$[\varepsilon,1-\varepsilon]$；$\varepsilon>1/2$ 时两条开带重叠，中间范围为空。
在非空中间区，本章没有逐点支付整个 $S_q\subseteq B$，但另有该前件的目标仍可用定理136.3。
这些包含关系始终以同一固定根的 $L_\varepsilon(o)$ 为条件；没有证明 PR 自动供应
$L_\varepsilon(o)$、全 $\mathsf L$、一个全覆盖根、全 Pair 或原静态重构目标。
单对版本的 (XI136.8) 也不单独供应 $C_q$；(XI136.16) 不被宣称为完整原域反例。

XI134 的控制模型具有根与根邻完整球、横截球面满射，却在真实标签处出现球加纯弧的完整零集，
并失败全域 EB3 与 PR。因此它不在本章前件内；不能将其横截球面用作 $S_q$，
也不能用其控制结论取代这里真实标签 $q\in D_{x_s}$ 的步骤。
[THREE_COPY VIII131.3、131.5—131.6][Q136TC] 已有裸 EB3 的第三实心带紧性、
R3 条件下的三／五步奇返回，以及紧部分域 $E_q=S_q\cap B_2$ 上的真实连续单射。
这些结论不供应 $E_q=S_q$；本章的 (XI136.6) 仍明确要求整个原球面已落入 $B$。
[SAME_READBACK132.1][Q136SR] 的无 Inj 凸／径向全态覆盖，也不供应该前件或全 Pair。

第135章的 $\mathsf{MC}$ 要求同一原态的所有有限纯混合表达在球心替换后仍相等，
定理135.5以完整 EB3 加该全域混合相容条件取得同原静态分类。
这里既未假设 $\mathsf{MC}$，也未由局部返回推出它；该条件分类不替代定理136.3的局部推导。
裸 EB3、EB3 加纯 PR、以及 X133.9 的完整 $\mathsf E_0$ 自动产生全覆盖根的问题，
仍按 (X133.32) 保留各自的全部原对象、前件与量词；$L_\varepsilon(o)$ 不被当作这些域的已知后果。

本章的承重推导是 (XI136.13)—(XI136.24)：真实原标签进入第二球，单对反向比较迫出原零对径，
先回送球心，再以完整极值范围消去正分离裕量；(XI136.27) 是其严格高段消费者。
采用 `repo-derived` 的纸面归属，不主张全球原创或文献穷尽。
原面分类、真实零确认、IX114.5 的球内刻度与其满刻度传播、X132.2及132.4的固定根证明、
X133.2的标签排重、X133.5的关联拓扑均为明确复用，不另计为新定理。
IX114.4 已在不要求 EB3 的完整 PR 域给 $P$ 紧；这里的固定紧球面论证不重新证明它。
IX120.12—120.13 的 $P_0$ 分支另有 Inj，不被借来替代根合同或 $C_q$。

成熟外部工具限于球上线性函数的极值与 [Hatcher][Q136H] 的区域不变性／同维紧流形嵌入满射。
后者的全部前件只在 (XI136.10) 的两张完整二维球面上使用。
原确认构造与完整效应区间的文献背景沿用 IX114.1 的
[Landsman §1.3，式(1.4)—(1.9)](https://arxiv.org/pdf/quant-ph/9603005v2)；
这里没有从对称跃迁概率另取 least、混态互易、自对偶或额外分类公理。
所得结论仅属于上述有限维原态—效应几何；来源、实际事件仪器、全部有限复合、纠缠、
全旁观正性、记录与全部未来、物理钟、Hamiltonian 及数值 $\hbar$，
继续保留 X133.10 的每个原对象、前件与完整量词，不由这条返回补出。

[Q136IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.2：原全域、真实零确认与原面；114.4：PR下纯紧性；114.5及(IX114.15)—(IX114.16)：整球刻度；IX120.1、120.4—120.5：原面、三角与既有分类；120.12—120.13：另有Inj的P0分支。"
[Q136X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X132.2—132.4：原小正无隙、局部带与逐点三角反证；X133.1—133.5：完整原面、三角标签、紧投影、已付域上的唯一共同邻点与整球面拓扑；X133.6、133.9：全覆盖根及未付自动性；133.10：完整物理合同。"
[Q136TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII131全文，特别是131.3的裸EB3第三实心带紧性、131.5的R3奇返回及131.6的部分关联域与未付全载体。"
[Q136SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "132.1：完整EB域的无Inj纯点—排除球凸覆盖、径向三纯项及未付最后一对正交。"
[Q136H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology，印刷页172，Theorem 2B.3、Corollary 2B.4：区域不变性及紧n流形嵌入连通n流形的满射性；这里只用n=2。"

## 追加锚（本行以下为增补区）
