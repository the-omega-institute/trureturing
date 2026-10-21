# AURIC FIB：零保真缺陷下的严格正经典恢复间隙

## 1. 任务、源接口与三个正定量子比特态

本文给出尚未形式化的普通符号数学：在一个明确的三态经典恢复任务中，共同测量的根保真缺陷为零，最小恢复误差却严格为正，并可精确指定；另给出可复用的传输线性下界。本文中的来源归属均相对于前卷《AURIC FIB common-measurement compatibility, defect and recovery separation》（下称源卷），不构成对原文献、链接、文献完备性或原创优先权的认证。量子系统连同记录的恢复仍按源卷的原接口理解。

**定义 1.1（共同测量与纯经典恢复任务）。** 所有空间均为有限维复 Hilbert 空间。密度矩阵半正定且迹为一，严格正指正定；信道为复线性、完全正、保迹映射（CPTP）。记 $[A,B]=AB-BA$，$\|A\|_F^2=\operatorname{Tr}(A^\dagger A)$，另用迹范数 $\|\cdot\|_1$ 与算子范数 $\|\cdot\|_{\mathrm{op}}$。对 $d\ge2,r\ge3$，固定 $\mathbb C^d$ 上的态族 $\rho_0,\ldots,\rho_{r-1}$。根保真度及共同测量缺陷为

$$
\begin{aligned}
F(\rho,\sigma)&=\|\sqrt\rho\sqrt\sigma\|_1,\qquad q=\binom r2,\\
p_i(x)&=\operatorname{Tr}(E_x\rho_i),\qquad
C_{ij}(E)=\sum_x\sqrt{p_i(x)p_j(x)},\\
F_U(\boldsymbol\rho)&=\frac1q\sum_{i<j}F(\rho_i,\rho_j),\\
F_M(\boldsymbol\rho)&=\inf_{\substack{m\ge1\text{ 有限},\ E_x\succeq0\\\sum_{x=1}^mE_x=I_d}}
\frac1q\sum_{i<j}C_{ij}(E),\\
\delta_{ij}(E)&=C_{ij}(E)-F(\rho_i,\rho_j),\qquad
\Delta=F_M-F_U.
\end{aligned}
$$

每一个候选都只有一组共同 POVM，不能为不同态对分别选择测量。采用源卷 §1、§6 的标准根保真接口：对任意两态（包括奇异态），$F$ 是全部有限 POVM 的经典根保真度之下确界，并在 CPTP 映射下不减。因此 $\delta_{ij}(E)\ge0$，$\Delta\ge0$。这些根保真定义及测量表示的文献归属见源卷的 NMLW 引用，成对最佳测量接口见其 Fuchs–Caves 引用。

本卷考察一组任意有限 POVM $E=(E_x)_{x=1}^m$ 和一个固定 CPTP 制备 $\mathcal P$：

$$
\mathcal M(A)=\sum_{x=1}^m\operatorname{Tr}(E_xA)|x\rangle\langle x|,
\qquad
\Lambda(A)=\mathcal P\mathcal M(A)=\sum_{x=1}^m\operatorname{Tr}(E_xA)\omega_x,
$$

其中每个 $\omega_x$ 是输入所在的 $\mathbb C^d$ 上的任意密度矩阵。反之，任意这样的制备态族均定义一个 CPTP 制备，可先在经典基上测量再制备 $\omega_x$。中间仅有经典变量，没有随行量子系统。零效应、混合制备和任意有限 $m$ 都包含在量词内。对指定输入族定义

$$
\varepsilon(\Lambda)=\max_i\frac12\|\Lambda(\rho_i)-\rho_i\|_1,
\qquad Q(\boldsymbol\rho)=\inf_{\mathcal M,\mathcal P}\varepsilon(\mathcal P\mathcal M).
$$

这是这些指定态上的最大半迹误差，不是任意输入及任意未触参考上的误差上确界。

**引理 1.2（正传输与精确残差）。** 对正定态 $\rho_0,\rho_i$，唯一的正定解 $T_i\rho_0T_i=\rho_i$ 是

$$
T_i=\rho_0^{-1/2}(\rho_0^{1/2}\rho_i\rho_0^{1/2})^{1/2}\rho_0^{-1/2},
\qquad \operatorname{Tr}(\rho_0T_i)=F(\rho_0,\rho_i).
$$

删去零效应后，令 $t_{ix}=\sqrt{p_i(x)/p_0(x)}>0$，则

$$
\delta_{0i}(E)=\sum_x
\frac{\|\sqrt{E_x}(T_i-t_{ix}I_d)\sqrt{\rho_0}\|_F^2}{2t_{ix}}.
\tag{1.1}
$$

证明。将传输方程以 $\sqrt{\rho_0}$ 作合同变换，得到 $\rho_0^{1/2}T_i\rho_0^{1/2}$ 必为 $\rho_0^{1/2}\rho_i\rho_0^{1/2}$ 的正平方根，故存在且唯一。根保真度的平方根迹表达给出迹恒等式。正定性保证每个非零效应上的两个概率均为正。设 $A_x=\sqrt{E_x}\sqrt{\rho_0}$，$B_{ix}=\sqrt{E_x}T_i\sqrt{\rho_0}$；其 Frobenius 范数平方分别为 $p_0(x),p_i(x)$。展开平方得

$$
\frac{\|B_{ix}-t_{ix}A_x\|_F^2}{2t_{ix}}
=\sqrt{p_0(x)p_i(x)}-\operatorname{Re}\operatorname{Tr}(A_x^\dagger B_{ix}).
$$

最后一项求和为 $\operatorname{Tr}(\rho_0\sum_xE_xT_i)=\operatorname{Tr}(\rho_0T_i)$，即得 (1.1)。所有分母为正，故等号缺陷为零当且仅当各残差均为零；消去可逆的 $\sqrt{\rho_0}$ 并取伴随，得到 $\sqrt{E_x}T_i=t_{ix}\sqrt{E_x}$ 及其伴随关系。这是源卷定理 2.1 的残差接口。$\square$

**命题 1.3（实际三态与零缺陷）。** 取 Pauli 矩阵

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
$$

以及源卷定理 6.1 的三个态

$$
\begin{aligned}
\sigma_0&=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix}
          =\frac{I_2+uX}{2},\\
\sigma_+&=\begin{pmatrix}3/4&\sqrt3/8\\\sqrt3/8&1/4\end{pmatrix}
          =\frac{I_2+vX+wZ}{2},\\
\sigma_-&=\begin{pmatrix}1/4&\sqrt3/8\\\sqrt3/8&3/4\end{pmatrix}
          =\frac{I_2+vX-wZ}{2},\\
u&=w=\frac12,\qquad v=\frac{\sqrt3}{4},\qquad
h=u-v=\frac{2-\sqrt3}{4}>0.
\end{aligned}
\tag{1.2}
$$

三者均正定，Bloch 向量依次是 $(u,0,0),(v,0,w),(v,0,-w)$。锚定正传输为

$$
D_+=\operatorname{diag}(\sqrt{3/2},1/\sqrt2),\qquad
D_-=\operatorname{diag}(1/\sqrt2,\sqrt{3/2}),\qquad T_0=I_2.
$$

它们两两对易，且 $\Delta(\sigma_0,\sigma_+,\sigma_-)=0$，虽然

$$
[\sigma_0,\sigma_+]=\begin{pmatrix}0&-1/8\\1/8&0\end{pmatrix}\ne0.
$$

证明。三态迹均为一，首对角元为正，行列式分别为 $3/16,9/64,9/64$，因而正定。直接的符号矩阵乘法给出 $D_\pm\sigma_0D_\pm=\sigma_\pm$，由引理 1.2 得唯一性。对易性给出任意态对的正传输 $S_{ij}=T_jT_i^{-1}$，因为 $S_{ij}\rho_iS_{ij}=\rho_j$。共同的 $Z$ 投影测量在各坐标块上使这些传输均为标量，于是引理 1.2 应用于各态对时每个残差均为零。同一个有限测量达到所有成对保真度，故 $F_M=F_U$。所示密度矩阵交换子非零，所以不能把传输对易偷换为态对易。$\square$

源卷的条件界 $\varepsilon\ge\Delta^2/8$ 在本三态上只给出零。以下严格正界针对相同三态上的经典恢复本身。

## 2. 三态经典恢复的精确极小极大值

**定理 2.1（全有限测量的精确最小值）。** 存在唯一的

$$
t_\star\in\left(\frac{\sqrt3}{4},\frac12\right)
$$

满足正根方程

$$
u-t_\star=
\sqrt{(t_\star-v)^2+w^2\left(1-\sqrt{1-t_\star^2}\right)^2}.
\tag{2.1}
$$

对于 (1.2) 的三态，有

$$
Q=\frac{1/2-t_\star}{2},\qquad
0<\frac{4-\sqrt{13}}{16}<Q<\frac{2-\sqrt3}{8}.
\tag{2.2}
$$

此下确界是最小值。令 $c_\star=\sqrt{1-t_\star^2}$，一个达到它的实际方案为

$$
E_\pm=\frac{I_2\pm Z}{2},\qquad
\omega_\pm=\frac{I_2+t_\star X\pm c_\star Z}{2}.
\tag{2.3}
$$

三个半迹误差全部等于 $Q$。这里结论中的两结果测量由全局下界与达到方案共同建立，不是预设的搜索限制。

证明。量子比特两态的差为 $(r-s)\cdot(X,Y,Z)/2$，其特征值为 $\pm|r-s|/2$。故半迹距离等于 Bloch 欧氏距离的一半。以下以 $R=2\varepsilon$ 表示双倍误差。

先作有限对称平均。对任意有限测量制备信道 $\Lambda$，定义

$$
\Lambda^X(A)=X\Lambda(XAX)X,\qquad
\Lambda^K(A)=\bigl(\Lambda(A^{\mathsf T})\bigr)^{\mathsf T}.
$$

第一种变换把效应与制备同时替为 $XE_xX,X\omega_xX$；第二种替为 $E_x^{\mathsf T},\omega_x^{\mathsf T}$，因为 $\operatorname{Tr}(E_xA^{\mathsf T})=\operatorname{Tr}(E_x^{\mathsf T}A)$。它们都是有限测量制备信道，这里未把单独的转置宣称为完全正。$X$ 共轭固定 $\sigma_0$ 并交换 $\sigma_\pm$，转置固定三个输入，迹范数对这两种操作不变，故最大误差不变。两种信道变换因 $X$ 为实矩阵而对易。

将四个群变换后的信道各赋权 $1/4$：把四组有限效应的每个元素缩放为原来的 $1/4$，并将群标记并入结果，便得到一个有限 POVM 和一个制备。迹范数凸性保证平均后的最大误差不增。两种 Bloch 符号作用分别是 $\operatorname{diag}(1,-1,-1)$ 与 $\operatorname{diag}(1,-1,1)$，三个坐标的联合符号不同。平均后的仿射线性部分必须同时与两者对易，平移也必须同时固定，因而作用必为

$$
(x,y,z)\longmapsto(t+ax,by,cz),\qquad a,b,c,t\in\mathbb R.
\tag{2.4}
$$

接着证明不依赖结果数的必要约束。事实上，任意有限测量制备信道的 $x$ 平移 $t$、$xx$ 系数 $a$ 及 $zz$ 系数 $c$，即使未经平均，也满足

$$
|a|+\sqrt{t^2+c^2}\le1.
\tag{2.5}
$$

删去零效应，写

$$
E_x=q_x(I_2+m_x\cdot(X,Y,Z)),\quad q_x>0,\quad |m_x|\le1,
\quad\sum_xq_x=1,\quad\sum_xq_xm_x=0,
$$

并写 $\omega_x=(I_2+s_x\cdot(X,Y,Z))/2$，$|s_x|\le1$。于是

$$
t=\sum_xq_xs_{x,x},\qquad
a=\sum_xq_xs_{x,x}m_{x,x},\qquad
c=\sum_xq_xs_{x,z}m_{x,z}.
$$

任取 $\chi\in\{1,-1\}$ 及实数 $U,V$，$U^2+V^2=1$。对每个制备态的 $x,z$ 分量用 Cauchy–Schwarz 得

$$
\chi a+Ut+Vc\le\sum_xq_x
\sqrt{(\chi m_{x,x}+U)^2+V^2m_{x,z}^2}.
$$

右侧各根号不超过 $1+\chi Um_{x,x}$：此上界非负，包括取零的边界，而其平方与根号内量之差恰为

$$
(1+\chi Um_{x,x})^2-
\left((\chi m_{x,x}+U)^2+V^2m_{x,z}^2\right)
=V^2(1-m_{x,x}^2-m_{x,z}^2)\ge0.
$$

因此 $\chi a+Ut+Vc\le\sum_xq_x(1+\chi Um_{x,x})=1$。对 $\chi$ 与单位向量 $(U,V)$ 取最大，即得 (2.5)。这一步保留了任意的 $y$ 分量，允许混合效应与混合制备，未使用两结果假设或 PPT 刻画。

对于 (2.4)，三态给出的双倍最大误差为

$$
R(a,t,c)=\max\left\{
|t+ua-u|,\sqrt{(t+va-v)^2+w^2(c-1)^2}\right\}.
\tag{2.6}
$$

$\sigma_+$ 与 $\sigma_-$ 的误差相等；所有输入的 $y=0$，故 $b$ 不出现。只需在必要集合 (2.5) 上建立全局下界，再用真实信道达到它。

先确定 (2.1) 的根。在 $[v,u]$ 上，$L(t)=u-t$ 严格递减，

$$
H(t)=\sqrt{(t-v)^2+w^2(1-\sqrt{1-t^2})^2}
$$

严格递增：两个平方项不减，其中 $1-\sqrt{1-t^2}$ 为正且严格递增。此区间 $0<t<1$，所有根号取非负根。端点满足

$$
L(v)=\frac{2-\sqrt3}{4}>\frac{4-\sqrt{13}}8=H(v),
\qquad L(u)=0<H(u).
$$

第一个严格不等式等价于 $\sqrt{13}>2\sqrt3$，因两边为正且 $13>12$ 而成立。连续性与严格单调性给出唯一交点 $t_\star\in(v,u)$。记

$$
e=u-t_\star>0,\qquad d_\star=t_\star-v>0,\qquad
c_\star=\sqrt{1-t_\star^2}>0.
$$

于是

$$
e+d_\star=h,\qquad t_\star^2+c_\star^2=1,\qquad
e^2=d_\star^2+w^2(1-c_\star)^2.
\tag{2.7}
$$

也可纯代数地指定该根：展开 (2.7) 等价于

$$
\sqrt{1-t^2}=\frac78+(2-\sqrt3)t-\frac{t^2}{2},
$$

故 $t_\star$ 是区间 $(v,u)$ 中下列四次方程的唯一根：

$$
\left[\frac78+(2-\sqrt3)t-\frac{t^2}{2}\right]^2+t^2-1=0.
\tag{2.8}
$$

在该区间右侧方括号严格大于 $3/4$，因为 $t^2<1/4$ 且 $(2-\sqrt3)t>0$。所以平方没有引入负号根；反向恢复距离等式时 $u-t>0$ 且 $H(t)>0$，也没有符号伪根。此规格不涉及任何数值求根。

为得到全局支撑下界，定义

$$
\beta=\frac{w^2(1-c_\star)}{c_\star},\quad
\ell=h+\beta t_\star,\quad
\alpha=\frac{d_\star+\beta t_\star}{\ell},\quad
\kappa=\frac\beta\ell,\quad
\eta=ut_\star+\frac{h d_\star}{\beta}.
\tag{2.9}
$$

由 $0<c_\star<1$ 得 $\beta>0$，从而 $\ell,\kappa>0$。并且 $1-\alpha=e/\ell>0$、$\alpha>0$，所以 $0<\alpha<1$，各分母均为正。还需严格控制 $\eta$，不能仅依赖驻点关系。利用 $1-c_\star=t_\star^2/(1+c_\star)$，有

$$
\beta=\frac{t_\star^2}{4c_\star(1+c_\star)}
\ge\frac{t_\star^2}{8}\ge\frac{v^2}{8}=\frac3{128}.
$$

$\sqrt3>3/2$ 给出 $h<1/8$，而 $d_\star<h$、$ut_\star<1/4$。因此

$$
0<\eta<\frac14+\frac{1/64}{3/128}=\frac{11}{12}<1.
\tag{2.10}
$$

对任何满足 (2.5) 的实 $(a,t,c)$，(2.6) 的第一项给出 $R\ge L_0=u-ua-t$。由 (2.7)，向量 $(d_\star/e,-w(1-c_\star)/e)$ 为单位向量，故第二项给出

$$
R\ge L_1=
\frac{d_\star(t+va-v)+w^2(1-c_\star)(1-c)}e.
$$

取正凸组合即得 $R\ge\alpha L_0+(1-\alpha)L_1$。其精确仿射恒等式是

$$
\alpha L_0+(1-\alpha)L_1
=e+\kappa\left(1-\eta a-t_\star t-c_\star c\right).
\tag{2.11}
$$

为核对整个恒等式，其 $a$ 系数为

$$
\frac{-u(d_\star+\beta t_\star)+vd_\star}{\ell}
=-\frac{h d_\star+u\beta t_\star}{\ell}=-\kappa\eta;
$$

$t,c$ 的系数分别为 $-\beta t_\star/\ell=-\kappa t_\star$ 与 $-w^2(1-c_\star)/\ell=-\kappa c_\star$。在 $(a,t,c)=(0,t_\star,c_\star)$ 处，$L_0=L_1=e$，而 $t_\star^2+c_\star^2=1$，所以常数项也一致。这核对的是全局仿射式，而非局部驻点。

对任意符号的 $a,t,c$，由 (2.10)、Cauchy–Schwarz 与 (2.5)，

$$
\eta a+t_\star t+c_\star c
\le |a|+\sqrt{t^2+c^2}\le1.
$$

故 (2.11) 给出整个必要可行集合上的 $R\ge e$。任何原信道的误差不小于其对称平均的误差，因此所有有限测量制备信道均满足 $\varepsilon\ge e/2$。

最后验证达到性。(2.3) 的效应正且和为 $I_2$，制备 Bloch 向量 $(t_\star,0,\pm c_\star)$ 的长度为一，故制备态均为纯态。实际信道作用为 $(x,y,z)\mapsto(t_\star,0,c_\star z)$，在 $\sigma_0$ 上的双倍误差为 $u-t_\star=e$，在每个 $\sigma_\pm$ 上则为 $\sqrt{d_\star^2+w^2(1-c_\star)^2}=e$。因此达到全局下界，$Q=e/2$。

$t_\star>v$ 给出 $c_\star<\sqrt{1-v^2}=\sqrt{13}/4$，结合 $d_\star>0$，有

$$
e=\sqrt{d_\star^2+w^2(1-c_\star)^2}
>w(1-c_\star)>\frac{4-\sqrt{13}}8>0.
$$

最后一个严格正性来自 $13<16$；另一方面 $e=u-t_\star<u-v=h$。除以二即得 (2.2)。严格下端点不被宣称可达到，本证明也不分类所有最优信道。$\square$

## 3. 可复用的对易正传输线性证书

**定理 3.1（共同实现上的响应与误差下界）。** 设 $d\ge2,r\ge3$，$\rho_0,\ldots,\rho_{r-1}$ 是 $\mathbb C^d$ 上的正定密度矩阵。令 $T_0=I_d$，其锚定正传输 $T_i\rho_0T_i=\rho_i$ 两两对易。选择

$$
\rho_0\succeq\mu I_d,\quad\mu>0,\qquad
L_i\ge\|\rho_i\|_{\mathrm{op}},\qquad
M_i=\sqrt{L_i/\mu}\quad(1\le i<r).
\tag{3.1}
$$

令 $P_\alpha$ 是按不同联合特征值元组标记的非零联合谱投影：

$$
\sum_\alpha P_\alpha=I_d,\qquad
T_iP_\alpha=\lambda_{i\alpha}P_\alpha,\qquad
\lambda_{i\alpha}>0,\quad\lambda_{0\alpha}=1.
$$

允许联合块简并。假设存在实系数 $c_0,\ldots,c_{r-1}$，使

$$
C=\sum_{i=0}^{r-1}c_i\rho_i\ne0,\qquad
\sum_{i=0}^{r-1}c_i p_i(\alpha)=0\quad\text{对每个 }\alpha,
\qquad p_i(\alpha)=\operatorname{Tr}(P_\alpha\rho_i).
\tag{3.2}
$$

记 $s=\sum_i|c_i|$，$H=\|C\|_1$。则全部对角联合块都满足 $P_\alpha CP_\alpha=0$。至少有两个联合块，并且联合间隙

$$
s_{\alpha\beta}=\sum_{i=1}^{r-1}(\lambda_{i\alpha}-\lambda_{i\beta})^2,
\qquad
\gamma=\min_{\alpha\ne\beta}\sqrt{s_{\alpha\beta}}>0
\tag{3.3}
$$

良定义。定义斜 Hermitian 矩阵 $A_i$，其对角联合块为零，非对角块为

$$
P_\alpha A_iP_\beta=
\frac{\lambda_{i\alpha}-\lambda_{i\beta}}{s_{\alpha\beta}}
P_\alpha CP_\beta\quad(\alpha\ne\beta).
\tag{3.4}
$$

它们满足

$$
C=\sum_{i=1}^{r-1}[T_i,A_i],\qquad
\sum_{i=1}^{r-1}\|A_i\|_F^2\le\frac{\|C\|_F^2}{\gamma^2}.
\tag{3.5}
$$

对任意一个实际有限测量 $\mathcal M$ 和一个实际 CPTP 制备 $\mathcal P$，令

$$
\tau_i=\mathcal P\mathcal M(\rho_i),\qquad
\varepsilon=\max_i\frac12\|\tau_i-\rho_i\|_1,\qquad
B=4\sqrt{d/\mu}\sum_{i=1}^{r-1}\sqrt{M_i}\|A_i\|_F.
\tag{3.6}
$$

则

$$
\begin{aligned}
\|\mathcal M(C)\|_{\ell^1}&\le B(2\varepsilon)^{1/4},\\
H&\le2s\varepsilon+B(2\varepsilon)^{1/4},\\
\varepsilon&\ge\varepsilon_{\mathrm{cert}}
:=\min\left\{\frac{H}{4s},\frac{H^4}{32B^4}\right\}>0.
\end{aligned}
\tag{3.7}
$$

这里 $\|\mathcal M(C)\|_{\ell^1}=\sum_x|\operatorname{Tr}(E_xC)|$。同一个不严格的证书下界也适用于全部有限方案的误差下确界。可将 $B$ 换为较大的显式间隙常数

$$
B_{\mathrm{gap}}=
4\sqrt{d/\mu}\sqrt{\sum_{i=1}^{r-1}M_i}\,\frac{\|C\|_F}{\gamma}.
\tag{3.8}
$$

所有界均独立于有限结果数。输出 $\tau_i$ 可以奇异，不要求输出正定。各态对的概率、残差、制备和误差必须来自这里同一个实际 $\mathcal M,\mathcal P$。

证明。首先，$T_i$ 在联合块上是标量，即使 $\rho_0$ 不与 $T_i$ 对易，也有

$$
P_\alpha\rho_iP_\alpha
=\lambda_{i\alpha}^2P_\alpha\rho_0P_\alpha,\qquad
p_i(\alpha)=\lambda_{i\alpha}^2p_0(\alpha).
$$

因为 $P_\alpha\ne0$ 且 $\rho_0\succeq\mu I_d$，
$p_0(\alpha)\ge\mu\operatorname{Tr}P_\alpha>0$。把 (3.2) 除以此正数，得到 $\sum_i c_i\lambda_{i\alpha}^2=0$，乘回完整算子 $P_\alpha\rho_0P_\alpha$，便证明 $P_\alpha CP_\alpha=0$。这消去的是整个对角块，不仅是其迹，故覆盖所有简并情形。实系数还保证 $C=C^\dagger$，且

$$
\operatorname{Tr}C=\sum_\alpha\operatorname{Tr}(P_\alpha CP_\alpha)=0
=\sum_i c_i.
$$

若只有一个联合块，则 $C=0$，与假设矛盾。因此至少两块。不同元组意味着每个 $s_{\alpha\beta}>0$，有限个块又使 $\gamma>0$。不能用某个单独传输的最小特征值差代替这个联合条件；单独传输可以简并。

交换 $\alpha,\beta$ 时，(3.4) 的实系数变号，而 $C_{\beta\alpha}=C_{\alpha\beta}^\dagger$，故 $A_i^\dagger=-A_i$。对非对角块，$[T_i,A_i]$ 的系数为 $(\lambda_{i\alpha}-\lambda_{i\beta})^2/s_{\alpha\beta}$，求和恰为一；对角块两边都为零，故得 (3.5) 的恒等式。不同有序块在 Frobenius 内积下正交，从而

$$
\sum_i\|A_i\|_F^2
=\sum_{\alpha\ne\beta}\frac{\|P_\alpha CP_\beta\|_F^2}{s_{\alpha\beta}}
\le\frac{\|C\|_F^2}{\gamma^2}.
$$

有序块在等式两侧一致计数，不需再加倍。

现在固定被估计的同一个实际方案。删去零效应；剩余各 $p_i(x)>0$，因此 $t_{ix}=\sqrt{p_i(x)/p_0(x)}>0$。由

$$
p_i(x)\le L_i\operatorname{Tr}E_x,\qquad
p_0(x)\ge\mu\operatorname{Tr}E_x
$$

得到 $t_{ix}\le M_i$。这些是迹比较，不是把不对易矩阵的因子当作标量交换。$L_i\ge\|\rho_i\|_{\mathrm{op}}\ge1/d>0$，故 $M_i$ 为有限正数。置

$$
R_{ix}=\sqrt{E_x}(T_i-t_{ix}I_d),\qquad
S_i=\sum_x\|R_{ix}\|_F^2.
$$

引理 1.2 以及 $\|R\sqrt{\rho_0}\|_F^2\ge\mu\|R\|_F^2$ 给出

$$
\delta_{0i}(\mathcal M)
=\sum_x\frac{\|R_{ix}\sqrt{\rho_0}\|_F^2}{2t_{ix}}
\ge\frac{\mu}{2M_i}S_i.
\tag{3.9}
$$

为明确近似恢复能推出的方向，沿同一个实际链 $\rho_i\to\mathcal M(\rho_i)\to\tau_i$ 用根保真数据处理，得到

$$
F(\rho_0,\rho_i)\le C_{0i}(\mathcal M)\le F(\tau_0,\tau_i),
\quad
0\le\delta_{0i}(\mathcal M)\le F(\tau_0,\tau_i)-F(\rho_0,\rho_i).
\tag{3.10}
$$

所需连续性不要求输出可逆。对任意固定有限 POVM，由态 $\rho,\rho',\sigma$ 产生分布 $p,p',q$，则

$$
\begin{aligned}
\left|\sum_x\sqrt{p(x)q(x)}-\sum_x\sqrt{p'(x)q(x)}\right|
&\le\|\sqrt p-\sqrt{p'}\|_2\|\sqrt q\|_2\\
&\le\sqrt{\|p-p'\|_1}
\le\sqrt{\|\rho-\rho'\|_1}.
\end{aligned}
$$

第二步用了 $(\sqrt a-\sqrt b)^2\le|a-b|$，第一步的 $\|\sqrt q\|_2=1$，最后一步是测量的迹范数收缩。此界对全部 POVM 一致，故相应两个成对下确界的差也受相同界控制。再改变第二个态，利用定义 1.1 的测量表示，得到包括奇异态在内的

$$
|F(\rho,\sigma)-F(\rho',\sigma')|
\le\sqrt{\|\rho-\rho'\|_1}+\sqrt{\|\sigma-\sigma'\|_1}.
\tag{3.11}
$$

因此 (3.10) 给出 $\delta_{0i}(\mathcal M)\le2\sqrt{2\varepsilon}$，(3.9) 则给出

$$
S_i\le\frac{4M_i}{\mu}\sqrt{2\varepsilon}.
\tag{3.12}
$$

这里用近似恢复控制缺陷，没有把近似恢复当作精确的成对最优测量。

接着证明经典响应估计。残差的精确伴随恒等式与迹循环性为

$$
[E_x,T_i]=\sqrt{E_x}R_{ix}-R_{ix}^\dagger\sqrt{E_x},\qquad
\operatorname{Tr}(E_x[T_i,A_i])=\operatorname{Tr}([E_x,T_i]A_i).
$$

对复矩阵使用合法的 Frobenius 迹界

$$
|\operatorname{Tr}(UV)|
=|\langle U^\dagger,V\rangle_F|\le\|U\|_F\|V\|_F.
$$

将第一项循环为 $\operatorname{Tr}(R_{ix}A_i\sqrt{E_x})$，第二项为 $\operatorname{Tr}(R_{ix}^\dagger\sqrt{E_x}A_i)$，再用

$$
\|A_i\sqrt{E_x}\|_F,\ \|\sqrt{E_x}A_i\|_F
\le\|A_i\|_{\mathrm{op}}\sqrt{\operatorname{Tr}E_x}
\le\|A_i\|_F\sqrt{\operatorname{Tr}E_x},
$$

便得

$$
|\operatorname{Tr}(E_x[T_i,A_i])|
\le2\sqrt{\operatorname{Tr}E_x}\,\|R_{ix}\|_F\|A_i\|_F.
\tag{3.13}
$$

没有要求这些矩阵为实矩阵、两两对易或共用本征向量。由 (3.5)、三角不等式及对 $x$ 的 Cauchy–Schwarz，

$$
\begin{aligned}
\|\mathcal M(C)\|_{\ell^1}
&\le2\sum_i\|A_i\|_F\sum_x\sqrt{\operatorname{Tr}E_x}\,\|R_{ix}\|_F\\
&\le2\sqrt d\sum_i\|A_i\|_F\sqrt{S_i}\\
&\le4\sqrt{d/\mu}\sum_i\sqrt{M_i}\|A_i\|_F\,(2\varepsilon)^{1/4}.
\end{aligned}
\tag{3.14}
$$

吸收结果求和的是恒等式 $\sum_x\operatorname{Tr}E_x=d$，不是结果数。再对 $i$ 用 Cauchy–Schwarz 与 (3.5)，得到 $B\le B_{\mathrm{gap}}$。响应证明只需一个精确分解 $C=\sum_i[T_i,A_i]$；若另有更适合的斜 Hermitian 分解，也可在 (3.6)、(3.14) 中使用它，(3.4) 则始终提供一种选择。

最后，线性与同一实际重建误差给出

$$
\|C-\mathcal P\mathcal M(C)\|_1
=\left\|\sum_i c_i(\rho_i-\tau_i)\right\|_1\le2s\varepsilon.
$$

制备把各经典基态送到密度矩阵 $\omega_x$，所以

$$
\|\mathcal P\mathcal M(C)\|_1
=\left\|\sum_x\operatorname{Tr}(E_xC)\omega_x\right\|_1
\le\sum_x|\operatorname{Tr}(E_xC)|=\|\mathcal M(C)\|_{\ell^1}.
$$

这也是 Hermitian 经典输入上的迹范数收缩。三角不等式结合 (3.14) 得到 $H\le2s\varepsilon+B(2\varepsilon)^{1/4}$。量子线性组合 $C$ 非零，要求经典表示保留足够响应；同一方案的近似保真最优性却迫使此响应变小。这里组合的是一个实际线性信道中的关系，没有合并独立边缘或分别优化的信道。

$C\ne0$ 保证 $H>0,s>0$，且 (3.5) 至少有一个非零 $A_i$。每个 $M_i>0$，因此 $B>0$；所有常数与分母均有限且严格为正。如果 $\varepsilon<\varepsilon_{\mathrm{cert}}$，则同时有

$$
2s\varepsilon<\frac H2,\qquad
B(2\varepsilon)^{1/4}<\frac H2,
$$

与 (3.7) 矛盾。故每个实际方案及其下确界满足不严格的 $\varepsilon\ge\varepsilon_{\mathrm{cert}}>0$，不需要假设最优方案存在。换用较大 $B_{\mathrm{gap}}$ 只会弱化证书，仍有效。$\square$

这一定理要求显式给出非零的块概率消失关系；未满足该假设时，它不给出正障碍。四次根来自连续性的一次平方根和残差到响应的另一次平方根，不宣称是一般最优指数，也不宣称证书常数尖锐。

## 4. 实际三态的独立较弱证书

**推论 4.1（单传输的显式正下界）。** 对 (1.2) 的三态，全部有限经典测量制备方案均满足

$$
\varepsilon\ge
\min\left\{\frac{2-\sqrt3}{32},\frac{(\sqrt3-1)^4}{2^{21}}\right\}>0.
\tag{4.1}
$$

证明。选系数 $(1,-1/2,-1/2)$，则

$$
C=\sigma_0-\frac{\sigma_++\sigma_-}{2}=\frac h2X,
\qquad H=h,\qquad s=2.
$$

两个坐标对角块都为零，故满足定理 3.1 的联合块概率关系。只用 $T=D_+$，其严格正间隙为

$$
g=\sqrt{3/2}-1/\sqrt2=\frac{\sqrt3-1}{\sqrt2}>0.
$$

令

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
A=\frac{h}{2g}J.
$$

则 $A^\dagger=-A$，$[T,J]=gX$，因而 $[T,A]=C$，且 $\|A\|_F=h/(\sqrt2g)$。这是定理 3.1 响应证明允许的另一个分解，令对应 $D_-$ 的 $A_i=0$ 即可；不需加入未使用的传输残差，但重建误差仍约束原来的全部三态。

锚 $\sigma_0$ 的特征值为 $3/4,1/4$，所以可取 $\mu=1/4$。每个密度矩阵均不超过 $I_2$，故 $L=1,M=2$ 合法。对所有非零效应，$0<t_x\le2$，由 (3.9)–(3.12)，

$$
S\le16\delta_{0+}\le32\sqrt{2\varepsilon}.
$$

把 $d=2,\mu=1/4,M=2,\|A\|_F=h/(\sqrt2g)$ 代入响应证明，得到

$$
\|\mathcal M(C)\|_{\ell^1}
\le\frac{8\sqrt2h}{g}(2\varepsilon)^{1/4},\qquad
h\le4\varepsilon+\frac{8\sqrt2h}{g}(2\varepsilon)^{1/4}.
$$

两个证书阈值分别为

$$
\frac{H}{4s}=\frac h8=\frac{2-\sqrt3}{32},\qquad
\frac{H^4}{32B^4}=\frac{g^4}{2^{19}}
=\frac{(\sqrt3-1)^4}{2^{21}},
$$

其中 $(8\sqrt2)^4=2^{14}$，$g^4=(\sqrt3-1)^4/4$。两个阈值均正，严格低于其最小值会导致上面的线性响应不等式矛盾，故结论为不严格的 (4.1)。$\square$

(4.1) 是对相同实际三态的独立较弱证书。定理 2.1 给出的精确最小值及严格下界更强；一般四次根估计不被当作本三态的尖锐优化，也不把 (4.1) 的端点宣称为可达到。

## 5. 保留量子系统的记录恢复与尚缺的普适桥梁

源卷 §§7–10 的终端解码器同时接收实际量子系统和完整保留记录，因而具有不同于定义 1.1 的输入类型。为明确这一点，保留其接口：$H=\mathbb C^5$，$B:\mathbb C^3\to H$ 为等距嵌入，$P_R=BB^\dagger$，$\iota(A)=BAB^\dagger$。源卷的固定仪器在码空间上的每一步算子为 $BQ_j/\sqrt2$，$Q_j$ 为酉矩阵。在已知时长 $n$，按时间顺序 $h=(h_1,\ldots,h_n)$，令 $Q_h=Q_{h_n}\cdots Q_{h_1}$，$Q_\varnothing=I_3$。实际细标签联合信道为

$$
\mathcal J_n(A)=2^{-n}\sum_{h\in\{0,1\}^n}
|h\rangle\langle h|\otimes BQ_hAQ_h^\dagger B^\dagger.
\tag{5.1}
$$

源卷的权限为：每步使用新环境、固定交互和固定环境测量基，只由实际取得的标签更新经典记录，无中间量子反馈、自适应仪器、参考读取、保留量子环境、额外量子摘要、依赖输入的量子旁信息或成功后选择。每个历史在全部码内输入及任意未触有限参考上概率均为 $2^{-n}$；这不表示任意未知 $H$ 输入上也公平。恢复目标是所有 qutrit 输入经 $\iota$ 嵌入，并包含所有未触有限参考，不是任意未知的五维输入。

源卷定理 8.1 的精确恢复可直接看出。对任意全联合输出算子 $Y$，令 $Y_{hh}=(\langle h|\otimes I_5)Y(|h\rangle\otimes I_5)$，设

$$
D_h=BQ_h^\dagger B^\dagger+(I_5-P_R),\qquad
\Gamma(Y)=\sum_hD_hY_{hh}D_h^\dagger.
$$

每个 $D_h$ 在码空间作用为逆酉，在正交补作用为恒等，故是全 $H$ 上的酉；Kraus 算子 $D_h(\langle h|\otimes I_5)$ 的伴随乘积和为全联合恒等，故 $\Gamma$ 在整个输出代数上 CPTP。由 $D_hBQ_h=B$ 得 $\Gamma\mathcal J_n=\iota$。若需回到字面上的 qutrit 代数，任选 qutrit 密度矩阵 $\omega$，使用

$$
\mathcal R_B(Y)=B^\dagger YB+\operatorname{Tr}[(I_5-P_R)Y]\omega.
$$

第一项的 Kraus 乘积为 $P_R$，第二项是补空间上的正泛函制备，Kraus 乘积和为 $I_5-P_R$，故此映射 CPTP，且 $\mathcal R_B\iota=\operatorname{id}_{M_3}$。于是 $\mathcal R_B\Gamma$ 是 $\mathcal J_n$ 的字面左逆。补空间迹项不可省略。这些是复算子代数上的等式，张量任意参考恒等后仍成立。此精确恢复及其来源归属属于源卷，并非本卷的三态经典优化结论。

标签单独的边缘为 $2^{-n}I_{2^n}\operatorname{Tr}A$，但标签连同量子系统的联合输出有上述左逆，二者不能互换。根保真度和共同测量保真度沿 $\mathcal J_n$ 及其左逆双向数据处理，故联合输出保留输入的 $F_U,F_M,\Delta$，即使联合态奇异也成立。源卷的 $\theta=0$ 与 $\theta=\pi/6$ 两种实际仪器还具有相同的平均全信道，却在原有全部权限下有不同的精确保留记录需求：$n\ge3$ 时分别为 $6$ 和 $2^n$ 个值。这些记录计数、前缀实现与种子扩展仍是源卷所引 REC 的成果，本文不把它们重新命名为本卷结果。它们解释了为何仅凭标签边缘、细标签联合缺陷或固定平均信道上的保真标量，不能读出实际记录需求。

**命题 5.1（经典因子化不能由终端记录权限推出）。** 允许解码器读取实际量子系统的恢复接口不蕴含定义 1.1 的纯经典因子化，因而定理 2.1、3.1 不构成该接口上全部协议的误差下界。

证明。细标签方案 (5.1) 配合 $\Gamma$ 已精确恢复所有码输入及其参考。若输入 qutrit 只能经过有限经典测量再制备，则对最大纠缠态 $|\Omega_3\rangle=3^{-1/2}\sum_{k=1}^3|k\rangle\otimes|k\rangle$ 的一半作用后，输出必为

$$
\sum_x\omega_x\otimes
\operatorname{Tr}_{\mathbb C^3}\!\left[(E_x\otimes I_3)|\Omega_3\rangle\langle\Omega_3|\right]
=\frac13\sum_x\omega_x\otimes E_x^{\mathsf T},
$$

是正乘积算子之和，因而可分。目标 $(B\otimes I_3)|\Omega_3\rangle$ 是 Schmidt 秩为三的纯纠缠态，故不能由这种因子化实现。实际接口通过保留量子系统传输纠缠，并不满足本卷经典下界的前提。$\square$

**定义 5.2（OPEN：需要建立的普适协议敏感桥梁）。** 令 $s_0$ 为显式免费的独立共享种子，服从标准 Borel 概率律 $\nu$。设实际输入无关压缩核为 $r_{s_0}(y\mid h)\ge0$、$\sum_y r_{s_0}(y\mid h)=1$，$y$ 为完整被计数的有限视图，解码器 $\mathcal D_{s_0,y}:M_5\to M_5$ 为可测 CPTP 映射。实际协议是

$$
\mathcal C(A)=\int 2^{-n}\sum_{h,y}r_{s_0}(y\mid h)
\mathcal D_{s_0,y}\!\left(BQ_hAQ_h^\dagger B^\dagger\right)\,d\nu(s_0).
\tag{5.2}
$$

解码器仍接收量子 $H$。无种子时取单点空间。视图须包含所有依赖历史且解码器可见的程序、控制选择、时钟变化、相关种子、存档和缓冲；私有且被丢弃的随机性在核内平均。相关可见种子必须一并计数，不能当作独立免费种子。非原子的不可数视图也不能因各点概率为零就被当成有限字母表。

若要把缺陷下界转成这个模型的近似记录下界，先固定例如下列全部输入和参考上的误差：

$$
\operatorname{err}(\mathcal C)=
\sup_{\substack{Z_{\rm ref}\text{ 有限}\\
\rho\text{ 为 }\mathbb C^3\otimes Z_{\rm ref}\text{ 上密度矩阵}}}
\frac12\left\|\bigl((\mathcal C-\iota)\otimes\operatorname{id}_{Z_{\rm ref}}\bigr)(\rho)\right\|_1.
\tag{5.3}
$$

然后必须对每个符合原权限、在时长 $n$ 保留视图规模 $W$ 且误差至多 $\varepsilon$ 的实际协议，构造一个合法有限共同 POVM $E_{\mathcal C}$ 和一个明确的实际态族 $\boldsymbol\eta_{\mathcal C}$，证明

$$
0\le\Delta(\boldsymbol\eta_{\mathcal C})
\le G_{\boldsymbol\eta_{\mathcal C}}(E_{\mathcal C})
\le g(W,n,\varepsilon),\qquad
G_{\boldsymbol\eta}(E)=\frac1q\sum_{i<j}\delta_{ij}^{\boldsymbol\eta}(E).
\tag{5.4}
$$

构造须给出共同实现映射、全部常数和足以沿所需方向结合正缺陷下界的资源依赖。分别最优的成对测量或独立边缘不是 (5.4)。必须保持固定公平仪器、实际时间顺序、解码器收到的量子 $H$、全部未触参考、完整视图计数、种子独立性与积分。积分信道的近似误差界不自动给出几乎处处相同的种子条件误差界；源卷的精确平均成功结论不能如此换成近似结论。

(5.4) 是源卷定义 10.3 的未决义务，本文不提供该构造。若改用定理 3.1 的线性响应路线，也必须先在实际协议中建立同一测量与同一制备实现相应态族的桥梁，不能删除保留量子系统来假定它成立。三个指定标量替代不足、经典因子化不可偷换，均不等于所有未来协议敏感桥梁普遍不可能。

## 6. 数学范围、资源与方法归属

精确优化只处理 (1.2) 的三个输入和半迹误差；它没有任意输入或参考量词，不能当作 diamond 恢复任务。一般证书要求正定输入、对易锚定正传输、一个在联合块上消失且算子值非零的实线性关系，以及同一实际有限经典测量制备链。它容许简并联合块、不对易密度矩阵和奇异输出，但不提供奇异输入的完整传输分类。一般态族的恢复最优值、所有最优信道分类、一般证书的最佳常数和最佳指数、一般或 Pauli 态族的 $F_M$ 精确值，均不由本文决定。

定理 3.1 明列维数、锚正性、概率比上界、联合间隙、系数范数和态范数的依赖，且无结果数因子。定理 2.1 的达到方案只给出两个经典结果与两个数学制备态；不推出运行时间、精度、物理取得、环境准备、测量通信、校准、控制合成、历史存储或总成本。源卷的保留寄存器值数也不等于这些资源之和；已知确定性时钟和固定表可以依赖时长，但不能暗藏额外的运行相关历史。

来源与方法按源卷中的身份区分：根保真与共同测量保真定义及性质归属于 Nuradha、Mishra、Leditzky、Wilde 的《Multivariate Fidelities》（源卷 NMLW）；成对最佳测量及效应本征空间条件归属于 Fuchs–Caves（源卷 FC）；细标签纠正接口与复交叉误差条件分别归属于 Gregoratti–Werner、Knill–Laflamme（源卷 GW、KL）；精确环境记录结论归属于源卷 REC。以上均为源相对引用，原始链接及其文献内容未获本文认证。本文复用源卷定义 1.3、定理 2.1、3.1、6.1–6.2 和 §§7–10 的明确接口；标准 Bloch 表示、凸性与有限对称平均、Cauchy–Schwarz、全局支撑泛函、谱块交换子求逆和迹范数收缩是证明工具，不被宣称为本卷发明。精确三态最小值与定量传输线性证书是相对于该源接口给出的综合推导，不附带世界优先权或文献查全声明。

## 7. 对机器学习的条件性研究解释

若一个学习或压缩模型能忠实对应这里的对象、任务关系和实际解码器类别，那么本例提示：某个选定信息缺陷为零，仍可与特定线性响应的丢失并存。因此可以把研究问题设为检验表示保留了哪些任务关系，并按实际解码器能力评估恢复，而不只比较单个信息标量。这是有条件的研究解释，不是关于所有神经网络的定理，也不包含经验改进、物理取得能力或总成本结论。

## 追加锚（本行以下为增补区）
