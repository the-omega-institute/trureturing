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

## 137. 二元混合相容的内部截面、反射纯球与跨块障碍

**定义 137.1（同原二元相容与球内图）。** 保留135.1的完整原 $V,C,u,K,P,\mathcal E,T_p,D_p$ 及 EB3。记完整球族、球缘和标签纤维为

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
\tag{XI137.1}
$$

全部端点与权重都来自同一个原模型，允许重复端点及零权。$\mathsf{MC}$ 蕴含 $\mathsf{BC}$；本章不把反向蕴含作为前件。单纯重排同一份混合不改变任何仿射和，(XI137.1)还比较端点不同但实际原态相同的两条弦。

复用 IX116.1—116.6 的原面接口：每个非点真面都是完整球；不同完整球至多交于一个原纯点；每个 $F$ 或单标签，或与唯一不交的 $H$ 构成重复对，满足 $I(F)=S(H),I(H)=S(F)$，且两球均不交第三球；至少有一张单标签球，单标签球的全部球缘标签在全域均无重复。所有内部、边界及支撑均相对于 $\operatorname{aff}K$，球内相对内部另记 $\operatorname{ri}F$。

**定理 137.2（局部球心图的零秩或满秩二分）。** 每个 $F\in\mathscr B$ 存在唯一仿射图 $G_F:F\to K$，满足 $G_F(q)=c_q$ 对全部 $q\in S(F)$ 成立。准确地，

$$
\begin{cases}
G_F\text{ 为常值图},& I(F)\text{ 非单点},\\
G_F\text{ 单射且秩为三},& I(F)\text{ 为单点}.
\end{cases}
\tag{XI137.2}
$$

证明。先用成熟的弦延拓论证构造图。每个 $x\in F$ 都可写成一条球缘弦的凸组合，定义 $G_F(x)$ 为相同权重的端点球心组合。$\mathsf{BC}$ 使不同弦给出相同值，且值在 $K$。若 $x,y\in F$ 不同，通过它们的直线与球相交为一条以球缘为端点的闭弦，$x,y$ 及其全部凸组合均在这条共同弦上，故 $G_F$ 保全部实凸组合。因此它仿射，球缘凸生成给唯一性；有限维仿射图连续。

若 $G_F$ 非单射，其线性部分有非零核方向。沿该方向取球的两个对径 $r,s\in S(F)$，得 $c_r=c_s$。这个共同球心非纯，故 $D_r,D_s$ 的交含非纯点，原面接口迫使 $D_r=D_s=:H$。$r\ne s$ 使 $H$ 重复；IX116.2给其唯一配对球 $J$，且 $r,s\in I(H)=S(J)$。$J$ 与 $F$ 共享两个不同点，故 $J=F$。于是 $F$ 重复，而且每个 $q\in S(F)$ 都满足 $D_q=H$，所以整个 $G_F$ 恒为 $c_H$。

反之，$F$ 重复时 IX116.2直接给 $G_F$ 在球缘恒值，故在整个球恒值。单标签情形因而单射，且 $F$ 为完整三球，线性秩恰为三。证毕。

**定理 137.3（球心像的精确内部截面及横截）。** 设 $F$ 单标签，置

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
\tag{XI137.3}
$$

特别地，$\dim\operatorname{aff}K\ge6$，至少存在一张这样的内部截面。

证明。137.2给嵌入三球及其边界公式。每个 $c_q$ 是真面 $D_q$ 的非纯球心，因此位于 $\partial K$。设某个 $x\in\operatorname{ri}F$ 的像在 $\partial K$。取 $K$ 上非负、非恒定且在 $G_F(x)$ 为零的支撑仿射泛函 $h$。$h\circ G_F$ 非负仿射且在球内点为零，所以在整个 $F$ 恒零。于是支撑真面 $Z=K\cap\{h=0\}$ 含所有 $c_q$。

对任意 $y\in D_q$，中心反射 $2c_q-y\in D_q$ 与非负性给 $h(y)+h(2c_q-y)=2h(c_q)=0$，从而 $D_q\subseteq Z$。极大真面性给 $D_q=Z$ 对全部 $q\in S(F)$ 成立。这迫使 $G_F$ 恒值，与单射矛盾。因此球内全部像均为 $K$ 内点，特别是 $o_F\in\operatorname{ri}K$。

若存在 $y\in K\cap\operatorname{aff}E_F$ 不在 $E_F$，从 $o_F$ 向 $y$ 的射线首次离开 $E_F$ 的点 $z$ 位于 $\partial_{\rm rel}E_F$ 且位于开线段 $(o_F,y)$。凸体内点与任意凸体点之间的开线段仍在内部，所以 $z\in\operatorname{ri}K$，与上述边界包含矛盾，取得精确截面。

若非零 $w$ 同时属于 $L_E$ 及 $\operatorname{lin}(D_q-c_q)$，因 $c_q\in\operatorname{ri}D_q$，充分小的 $\varepsilon>0$ 使 $c_q\pm\varepsilon w\in D_q\subset K$。它们又属于 $\operatorname{aff}E_F$，故都在 $E_F$，违反 $c_q$ 是三球 $E_F$ 的极点。两方向空间均为三维，零交给维数下界；IX116.6给至少一张单标签球。证毕。

**定理 137.4（反射纯球的面或内部截面二分）。** 设 $I(F)=\{a\}$。定义

$$
\sigma_F(q)=2c_q-a\quad(q\in S(F)),\qquad
A_F=2G_F(F)-a,\qquad b_F=2o_F-a.
\tag{XI137.4}
$$

则 $A_F\subset K$ 为非退化仿射三球，$b_F$ 是其中心，整个相对球面满足

$$
\partial_{\rm rel}A_F=\sigma_F(S(F))\subset P.
\tag{XI137.5}
$$

恰有以下两种情形：若 $b_F\in\partial K$，则 $A_F$ 本身是一张完整原排除球；若 $b_F\in\operatorname{ri}K$，则

$$
A_F=K\cap\operatorname{aff}A_F,
\tag{XI137.6}
$$

且 $A_F$ 不是真面。此外，

$$
A_F=F
\quad\Longleftrightarrow\quad
c_q=\frac{a+2c_F-q}{2}\quad(q\in S(F)).
\tag{XI137.7}
$$

证明。对每个 $q\in S(F)$，$q\in D_a$，零对称给 $a\in D_q$。$a$ 是 $D_q$ 的球缘点，故其中心反射 $2c_q-a$ 也是该球的球缘点，因而属于原 $P$。137.2使 $2G_F-a$ 单射，故它将 $F$ 映为非退化三球，球面恰为上述纯点；球缘凸生成和 $K$ 凸给 $A_F\subset K$。

若 $b_F\in\partial K$，取非负非恒定支撑 $h$ 在 $b_F$ 为零。$A_F$ 关于 $b_F$ 中心对称，故 $h$ 在整个 $A_F$ 为零，$A_F$ 包含于支撑真面 $H$。该面非点，原面分类使它为三球。两球同维，故仿射包相等，且 $b_F\in\operatorname{ri}H$。若 $H$ 中某点在 $A_F$ 外，从 $b_F$ 向该点的开线段跨过 $A_F$ 的球面；交点属于 $\operatorname{ri}H$，却由(XI137.5)为原纯点，矛盾。故 $A_F=H\in\mathscr B$。

若 $b_F\in\operatorname{ri}K$，(XI137.5)使球面在 $\partial K$，137.3的射线论证原样给(XI137.6)。包含 $K$ 内点的非空面只能为整个 $K$；137.3给 $\dim\operatorname{aff}K\ge6$，而 $A_F$ 仅三维，所以它不是真面。

最后假设 $A_F=F$。对 $q\in S(F)$，上述反射点 $\sigma_F(q)$ 与 $q$ 均在 $F$，又满足 $q\perp\sigma_F(q)$。取实现这一原零一读数的同一原效应，其在球 $F$ 的限制非恒定，最大、最小点只能是一对唯一球内对径。因此 $\sigma_F(q)=2c_F-q$，重排即得(XI137.7)右侧。反之，该公式使 $\sigma_F$ 将球缘映为同一球缘的对径，取凸包即得 $A_F=F$。证毕。

**定理 137.5（固定原球缘上的非塌缩）。** 任取 $D_p=F$，不要求 $F$ 单标签。固定辅助欧氏范数，令

$$
\delta_F=2\min_{q\in S(F)}\|p-G_F(q)\|.
$$

则 $\delta_F>0$ 且

$$
\operatorname{diam}D_q\ge\delta_F\quad(q\in S(F)).
\tag{XI137.8}
$$

因此若 $\operatorname{diam}D_{p_n}\to0$，该序列最终避开每一张预先固定的 $S(F)$。

证明。固定球的球缘紧，$G_F$ 连续，且每个 $G_F(q)=c_q$ 非纯，与纯点 $p$ 不同，故连续正距离取得严格正的最小值。零对称给 $p\in D_q$，中心反射给 $2c_q-p\in D_q$；两点距离为 $2\|p-c_q\|$，取得(XI137.8)。每张固定球缘的正下界直接给序列断言。不同 $F$ 的下界尚未统一，本结论不供应 IX118.8 的全域正下界，也不供应136.3的全轴内球。证毕。

**定理 137.6（重复块的内部相容及单外端点禁交）。** 设 $F,H$ 是 IX116.2的重复球对，令 $B=S(F)\cup S(H)$。则球心替换在全部端点属于 $B$ 的任意有限纯混合等式上相容。另一方面，在 $\mathsf{BC}$ 下不可能有

$$
tr+(1-t)a=vb+(1-v)d,
\qquad
0<t,v<1,\quad a,b,d\in B,\quad r\in P\setminus B.
\tag{XI137.9}
$$

证明。IX116.3给同一原效应 $e$，满足 $K\cap\{e=0\}=F$ 及 $K\cap\{e=1\}=H$。仿射图

$$
J(x)=(1-e(x))c_H+e(x)c_F
$$

在 $S(F)$ 恒为 $c_H=c_q$，在 $S(H)$ 恒为 $c_F=c_q$。故任意有限 $B$ 混合的球心替换都等于对原混合施加同一仿射 $J$，取得内部相容。

若(XI137.9)成立，分别应用 $\mathsf{BC}$ 及 $J$，相减得 $t(c_r-J(r))=0$，故 $c_r=J(r)$。$r$ 在两球缘之外且为原纯点，因此 $0<e(r)<1$，使 $J(r)\in(c_F,c_H)$。这个整个开球心段在 $\operatorname{ri}K$：否则某非负非恒定支撑同时在两球心为零，中心反射迫其零面同时包含 $F,H$，极大性迫 $F=H$，矛盾。于是 $c_r\in\operatorname{ri}K$，违反 $c_r\in D_r\subset\partial K$。证毕。

**定义 137.7（简化候选及尚缺的整体约束）。** 待证候选为 $\mathrm{EB3}+\mathsf{BC}$。137.2—137.6没有证明它推出 $\mathsf{MC}$、全标签单射或全域非塌缩，也没有给出其反模型。反射构造尚缺 $A_F=F$；137.4的“完整原球”分支仍允许另一张完整球，“内部截面”分支也未被排除。即使逐球得到(XI137.7)，将各球的 $a+2c_F$ 拼成全域同一个向量，仍须另证整体连接条件。

重复块内部的全部混合关系已经相容，故不能只在块内寻找矛盾。137.6仅排除一外三内的活跃二元等式；两个外端点与两个块内端点的弦相交仍可能在内部发生，未被该论证排除。局部下界亦仅逐球成立，不能以逐点正值代替统一正值。

已取得完整静态分类的候选仍为135.1的 $\mathrm{EB3}+\mathsf{MC}$。它的同原表示与 Born、谱分解、全效应和有限数学测量字典直接复用135.5—135.6；本章只压缩二元候选所缺桥梁的几何形状，不新增 Hilbert 或物理实现断言。其白话关系图景是：同一混态若能由两对纯态调出来，换成各自排除球的球心后也应相同。这使每颗单标签球的球心族拉成一张穿过总态空间内部的完整三维切片；再隔着球心反射纯点，会得到另一整张纯球面。要把“两两相容”升级为量子结构，还须说明这张反射球为何回到原球，并把各球的关系接成全域同一关系。

**约定 137.8（数学来源及迁移条件）。** 本章新增承重连接采用 `repo-derived` 归属：原全效应产生的排除面与二元球心图共同给出局部秩二分、精确内部截面及横截、反射纯球二分、逐球非塌缩及重复块禁交。弦上的仿射延拓、支撑面、凸体内点射线、有限维维数公式及紧集最小距离是成熟中间工具；IX116的面与重复纤维分类、XI135—136的全域分类桥均按原前件复用，不另计新结果。

[Schillewaert—Van Maldeghem，On the varieties of the second row of the split Freudenthal–Tits Magic Square，§2.1](https://arxiv.org/abs/1308.0745) 的 Mazzocca–Melone 公理 MM1要求每对点位于一张指定二次空间，MM2约束射影张成空间的交，另有分裂二次曲面及切空间条件；本章的凸面交叠不供应这些前件，尤其不能用其分类倒付未证的全 Pair。[Barnum—Müller—Ududec，Higher-order interference and single-system postulates characterizing quantum theory，Theorem 16](https://arxiv.org/abs/1403.4147) 则显式要求 projectivity、对称跃迁概率及保纯滤子；二元混合相容未供应这些结构。两项文献只界定可迁移的条件，不替代上述原域证明，也不据有限检索宣称全球原创。

## 追加锚（本行以下为增补区）
