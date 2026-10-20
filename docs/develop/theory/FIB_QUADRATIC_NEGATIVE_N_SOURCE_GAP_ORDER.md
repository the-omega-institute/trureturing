# FIB 二次负 n 的严格源间隙与同子片反向间隙序

本卷独立为第 64 节，研究实际五动作 $JMJMJ$ 后的严格 $\beta=7$、$n<0$ 六读父及其实际取得 J 子片。两个实质结论是：每个 $\kappa\le8m$ 子片的实际普通端点都有严格源间隙 $\xi>\xi_*$；同一父、同一该子片中的任意不同普通世界，按 $q<r$ 排序后满足 $0<S-s<2(r-q)$。因此 $s$ 增加而 $s-2q$ 严格减少，且原源坐标 $r_0$ 严格增加、$b$ 严格减少。本文给出全部新证明及其所需的原行桥梁。

这是 `repo-derived` 符号综合，复用插值、因子定理、Vieta、有限割线与介值定理。结论为 fallible UNEXECUTED 符号数学，不是 Lean/kernel、数值、文献穷尽、外部原创性或优先权认证。反向间隙序是实际对的必要限制，不承担实际对存在、全部普通对排空、末函数单射或一般 ENTIRE 选择器。

## 64. 实际原世界上的源间隙几何

### 64.1. 整个世界、实际时钟与取得记录

一个完整目标自始固定为

$$
W=(P,g,d),\qquad
P=\begin{pmatrix}r_0&b\\c_{\rm src}&1-r_0\end{pmatrix},\qquad
0<r_0<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r_0(1-r_0),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
\tag{64.1}
$$

四元正、迹一、行列式零；非零迹排除秩零，故秩恰一。原域允许次数至多二的全部低次、两种尺度符号、合法系数零、样本零、观察零、采样或非采样根及重根。每个候选有自己的一个固定 d，跨它的全部行不变。相等和去重只按整个 $P,g,d$。

实际动作与时钟为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{64.2}
$$

已服务的 $JMJMJ$ 给原时钟零至五，即六次 TOTAL；时钟六只选 J 取得 z，即七次 TOTAL；时钟七至多再选一个动作，得到八次 TOTAL。没有重置、复制、跳读、时钟平移、隐藏源/根/次数标签、额外端口、逐行 refit 或未选响应输入。

对任意左乘积 $A_0$，相加两个对角元即有

$$
\operatorname{tr}(A_0P)=(A_0)_{22}+[(A_0)_{11}-(A_0)_{22}]r_0
 +(A_0)_{21}b+(A_0)_{12}c_{\rm src}.
$$

左 J 交换旧两行；左 M 取旧第二行与旧两行之和。这些行恒等式给下列全部相关原响应，记 $j=b+c_{\rm src}$：

| 原时钟和动作 | 同一个完整世界的响应 |
| --- | --- |
| $0$ | $d+g(0)$ |
| $1,J$ | $d+jg(1)$ |
| $2,M$ | $d+(1+b)g(2)$ |
| $3,J$ | $d+(j+r_0)g(3)$ |
| $4,M$ | $d+(1+2b)g(4)$ |
| $5,J$ | $d+(j+2r_0)g(5)$ |
| $6,J$ | $z=d+(1+2b)g(6)$ |
| $7,J$ 接 J | $f_{JJ}=d+(j+2r_0)g(7)$ |
| $7,M$ 接 J | $f_{JM}=d+(1+j+r_0+2b)g(7)$ |
| $6,M$ | $h_M=d+(1+3b)g(6)$ |
| $7,J$ 接 M | $f_{MJ}=d+(j+3r_0)g(7)$ |
| $7,M$ 接 M | $f_{MM}=d+(1+2r_0+4b+c_{\rm src})g(7)$ |

重复乘积使用新时钟的 gain 样本。表内未选响应只是完整候选的预测。

置 $a_0=y_0$、$x_i=y_i-a_0$，原插值多项式为

$$
E(t)=Lt+At^2,\qquad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
\tag{64.3}
$$

这些式恢复偶节点零、二、四及奇节点一、三、五。次数至多二的差有三个不同根即恒零，故唯一。以下 C 始终是这个 untouched 原奇插值常数；$\xi$ 专指源间隙，不指插值数据。

### 64.2. 达到父的精确区域与全部父系数

令

$$
a=\frac{\sqrt{17}-1}{4},\qquad a^2+a/2=1,\qquad \frac34<a<\frac45.
$$

固定一个满足下列谓词的实际取得父：

$$
B+5D=a(L+5A),\qquad \tau=\frac{D-aA}{3a}\ne0,
$$

$$
U_0=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5),\quad
\Lambda=\frac{C-15a\tau}{a-1},
$$

$$
K=\Lambda+E+\tau U_0=\tau(t+p)(t+v)(t-7),\qquad
p\ne v,\quad p,v>2a.
\tag{64.4}
$$

置

$$
Z=p+v=m+1,\qquad V=pv=n+2m+15,\qquad n<0.
$$

$K/\tau$ 的完整升幂系数是 $(-7V,V-7Z,Z-7,1)$；与左边逐系数比较，再用父条件，得到

$$
\begin{aligned}
\Lambda&=-7\tau V,&A&=\tau m,&L&=\tau(n-5m),\\
D&=a\tau(m+3),&B&=a\tau(n-5m-15),&C&=\tau\bar C,\\
\bar C&=7(1-a)V+15a.
\end{aligned}
\tag{64.5}
$$

因 $U_0-V_o=3t^2-15t+15$，全部系数还给

$$
R=aE+a\tau(U_0-V_o)+(a-1)\Lambda,
\qquad C=(a-1)\Lambda+15a\tau.
\tag{64.6}
$$

**父区域的双向引理。** 除 $n<0$ 外，(64.4) 的精确参数域是

$$
m>4a-1,\qquad
(2a-2)m+4a-19<n<\frac{m^2-6m-59}{4}.
\tag{64.7}
$$

证明。$p-2a,v-2a$ 的和、积均正，不同根给严格判别式，故恰有

$$
Z>4a,\qquad 2aZ-4a^2<V<Z^2/4.
\tag{64.8}
$$

反向 (64.8) 给移位二次式的正和、正积和正判别式 $Z^2-4V$；两个不同实移位根都正。加 $2a$ 即得不同 $p,v>2a$。代入 $Z=m+1,V=n+2m+15$ 并用 $4a^2=4-2a$ 恰得 (64.7)。下文例外世界的完整 converse 实际达到每组这些参数，任意 $a_0$ 和任意 $\tau\ne0$ 均可。因此这里确有 $m>0,V>4a^2>0$，不以未达到的形式父代替。交换根只换名字。∎

所有同子片比较固定 SAME $a_0,\tau,m,n$，以及 SAME 实际取得值

$$
\kappa=\frac{z-a_0-E(4)}{2\tau}.
\tag{64.9}
$$

$\tau$ 的符号不固定。

### 64.3. 严格源双射、BOTH 整个恒等式与原常数

严格源域与下面的整个开域双射：

$$
q=\frac{r_0}{b}>0,\qquad s=\frac2b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},
\qquad j=q+\frac{2(1-q^2)}s.
\tag{64.10}
$$

正向 $s-2q=2(1-r_0)/b>0$，秩一式强制 $c_{\rm src}$ 的逆式。反向四元正、迹一且 $bc_{\rm src}=r_0(1-r_0)$，并返回 q,s。没有删去任一对角侧、对称源、$s=4$ 或 $s=4q$。

记

$$
D_0=2-q-2q^2,\qquad H=D_0+3q=2+2q-2q^2,\qquad
 e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,\quad T=\nu/s.
$$

**完整原行桥梁。** 六原行当且仅当严格源、整个 $g\ne0$、$d=a_0-\lambda$ 及 BOTH 整个恒等式

$$
-\lambda+eg=E+TU_0,\qquad -\lambda+og=R+qTV_o.
\tag{64.11}
$$

证明。e,o 在各自三个原节点等于实际迹。必要方向中，每个节点差次数至多三，三次系数分别为 T、qT；减去相应三次节点积后，余式次数至多二且仍有三个不同根，故恒零。充分方向在原节点取值即恢复全部六行。零样本、取消系数和低次均覆盖，没有除 gain 样本。

偶式完整升幂系数为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T).
$$

依次可逆解出

$$
\nu=sT,\quad\mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad
\lambda=sF_{\rm orig},\quad d=a_0-sF_{\rm orig}.
\tag{64.12}
$$

奇式左完整升幂系数为

$$
\left((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\right),
$$

右边为 $(C-15qT,B+23qT,D-9qT,qT)$。三次自动相同；其余比较恰为

$$
\begin{aligned}
Q&=D-qA-HT=0,\\
L_{\rm res}&=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&=C-15qT-B_{\rm src}F_{\rm orig}=0,\qquad B_{\rm src}=(q-1)s+D_0.
\end{aligned}
\tag{64.13}
$$

其中二次比较是 $D-9qT=q(A-6T)+D_0T$，一次比较是 $B+23qT=q(L+8T)+D_0[A-T(s+6)]$。逆向这些比较逐系数恢复整个奇式，故原行 converse 完整。C 及原 $15qT$ 从未改变；必要符号不能替代 Q 或 $R_C$。∎

### 64.4. 普通支的派生正性、完整图谱与 converse

先声明普通即 $q\ne a$，此后才允许取消 $\delta=q-a\ne0$。令

$$
u=2q+2a+1>0,\quad\theta=T/\tau,\quad\eta=n/u<0,\quad
h=s+5-u=s-2q+4-2a>0.
$$

由 a 的方程，$D_0=-\delta u,H=3q-\delta u$。逐项整理原式给

$$
\frac Q\tau=3a-\delta m-H\theta,
$$

$$
\frac{L_{\rm res}}\tau
=\delta\{u[m-(s+1)\theta]-n\}-5\frac Q\tau.
\tag{64.14}
$$

所以 $Q=L_{\rm res}=0$ iff $Q=0$ 且

$$
m=(s+1)\theta+\eta.
\tag{64.15}
$$

只取消已非零的 δ、τ，没有除 H。令

$$
\Gamma=n-(4a+1)m-6a<0.
$$

由 $u-(4a+1)=2\delta$、(64.14)–(64.15)，

$$
\Gamma=-K_{\rm pos}\theta,\qquad
K_{\rm pos}=u(s+1)+2H=u(s-2q+2a+1)+6q>0.
\tag{64.16}
$$

因此 $\theta>0$ 是派生结论，包括 H=0。全部偶系数再给

$$
F:=F_{\rm orig}/\tau
=n-(s+5)m+(s+2)(s+4)\theta=3\theta-h\eta>0,
$$

$$
g(t)=s\tau[\theta t^2+(\eta-5\theta)t+F],\qquad
\lambda=s\tau F,\quad\mu=s\tau(\eta-5\theta),\quad\nu=s\tau\theta,
\quad d=a_0-s\tau F.
\tag{64.17}
$$

代入 $n=u\eta,m=(s+1)\theta+\eta$ 时，F 的 θ 系数是三、η 系数是 −h。故真正二次及各符号均为原式后果，不是先验次数承诺。

时钟四与所取六 J 的实际迹同为 $1+4/s$。同一个 gain 有 $g(6)-g(4)=2s\tau(5\theta+\eta)$，所以 SAME 第七原行 iff

$$
\kappa=(s+4)(5\theta+\eta)=(s+4)[m-(s-4)\theta]
=5m+15\theta+(s-1)\eta.
\tag{64.18}
$$

尤其

$$
\kappa-8m=(s-4)(\eta-3\theta),\qquad\eta-3\theta<0.
\tag{64.19}
$$

故 $\kappa<8m\iff s>4$，等号 iff s=4，$\kappa>8m\iff s<4$；不除 s−4。

对固定父和任意实 κ，每个辅助 $q>0$ 给 $\eta=n/u$，置

$$
b_\kappa=\kappa-5m+2\eta,\qquad
\Delta_\kappa=b_\kappa^2-60\eta(m-\eta)>b_\kappa^2,
$$

$$
\theta=\frac{b_\kappa+\sqrt{\Delta_\kappa}}{30}>0,\qquad
s=\frac{m-\eta}{\theta}-1.
\tag{64.20}
$$

这是 $15\theta^2-b_\kappa\theta+\eta(m-\eta)=0$ 的唯一正根：常数严格负，判别式严格正，另一根严格负。初始只知辅助 s>−1；尚未成为世界。

定义 $\mathcal S_\kappa$ 为满足 ALL 过滤的辅助 q：

$$
q>0,\quad q\ne a,\quad s>2q,
$$

$$
3a-(q-a)m-H\theta=0,\qquad
\bar C-15q\theta-[(q-1)s+D_0](3\theta-h\eta)=0.
\tag{64.21}
$$

**完整普通七原行 iff。** 每个保留 q 以 (64.10)、(64.17) 重建一个严格 P、一个整个非零 gain、一个固定 d。s 的定义恢复 ordinary 及每个偶系数；(64.14) 恢复原奇一次；Q 恢复二次；untouched 原常数恢复 $R_C$；三次自动成立。因此 BOTH 恒等式恢复全部 SAME 六行。仅除已证正 θ，正根方程恢复 (64.18) 及 SAME 第七行。反向每个实际普通世界由 (64.16) 有 θ>0，故必取唯一正根，s 和全部 gain、d 也由原式强制，必在 (64.21)。这证明必要性及完整原世界充分性。

同 q 固定整个世界；不同 q 给不同源。H=0、s=4 都由原方程保留，不用极限替代。以下任何新不等式都不替代 (64.21) 的两个原残式。

### 64.5. 全部例外、实际匹配、ENTIRE 等号与末函数

在 q=a 有 $D_0=0,H=3a$。原 Q 强制 T=τ，原常数强制 $(a-1)\lambda=C-15a\tau$，所以 λ=Λ，偶式成为 eg=K。整个多项式 gain 要求 K(−s)=0；严格 s>2a 恰接受 s=p 或 v，第三根七要求 s=−7，不能成为源。因此全部例外恰为

$$
W_p=\bigl(P(a,p),\ p\tau(t+v)(t-7),\ d_*\bigr),\qquad
W_v:\ p,v\text{ 交换},\qquad d_*=a_0+7\tau V.
\tag{64.22}
$$

完整 converse 如下。p,v>2a 给严格源，首项 pτ 或 vτ 非零，λ=Λ、d=d* 自始固定。它们有 eg=K、og=aK，(64.6) 恢复 BOTH (64.11)，故恢复每个奇偶系数、原 C/15qT 及 SAME 六原行。这也实际达到 (64.7) 中每个父，不假设普通世界存在。

两个实际取得测试为

$$
\kappa_p=(p+4)(v+3),\qquad\kappa_v=(v+4)(p+3),\qquad
\kappa_p-\kappa_v=v-p\ne0.
\tag{64.23}
$$

其原响应为 $z_p=d_*-\tau(p+4)(6+v)$ 及交换式，相差 $2\tau(v-p)\ne0$。只附加与 SAME 实际取得 κ 匹配的例外，至多一个。

源双射被 q=a 与 q≠a 穷尽，各有完整必要性和 converse，故 ENTIRE 原七行子片恰为

$$
\mathcal K_\kappa=\{W_\kappa(q):q\in\mathcal S_\kappa\}
\ \cup\ \{W_p:\kappa=\kappa_p\}\ \cup\ \{W_v:\kappa=\kappa_v\}.
\tag{64.24}
$$

两个包含方向均成立。去重只按整个三元组。可达恰指这个 ENTIRE 并集非空；空类不是停止成功。

普通世界令

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta
=32\theta+n+\eta+5m-\kappa.
\tag{64.25}
$$

原奇整个式在七给 $o(7)g(7)=\lambda+R(7)+48qT$。实际 JJ 迹为 $o(7)-2q/s$，JM 比它多 $(s+4-2q)/s$，故

$$
f_{JJ}=a_0+R(7)+\tau x,\qquad f_{JM}=a_0+R(7)+\tau y,
$$

$$
x=48q\theta-2q\omega,\qquad
y=48q\theta+(s+4-4q)\omega,\qquad
y-x=(s+4-2q)\omega.
\tag{64.26}
$$

共同偏置是已取得的 $a_0+R(7)$，不是每个候选另拟合的 d。例外 g(7)=0、x=y=48a。SAME τ≠0 保持相等与分离，τ<0 则反转实际大小序。

### 64.6. 所需 N6–N8 桥梁及实际 H 零族

这里给出这些复用桥梁的精确假设与支撑证明，不从其状态或投票推出数学。

**N6 的有界末 gain 正性。** 对 (64.4)、n<0 的任意实际普通世界，任意取得 κ 下，$q\le3a-1$ 推出 ω>0。证明令 $\rho_e=-\eta/\theta>0$；由 m>0 得 $\rho_e<s+1$。h≥7 时 (64.25) 直接正。h<7 时

$$
\frac\omega\theta=17-(u+2-s)\rho_e
>17-(u+2-s)(s+1),
$$

$$
(u+2-s)(s+1)=\frac{(u+3)^2}{4}-\left[s-\frac{u+1}{2}\right]^2\le17.
$$

最后一步用 $0<u+3\le2(4a+1)$ 与 $(4a+1)^2=17$。前面的严格号处理等号情形，故 ω>0，且 $3a-1>5/4$。没有除 H。∎

原常数在七的方向也须保留。在偶重建、$Q=L_{\rm res}=0$ 下，奇整个差只剩常数 $-R_C$。与偶式在七比较，用 K(7)=0 及 (64.6)，有

$$
E(7)=-\Lambda-105\tau,\quad R(7)=-\Lambda-48a\tau,
$$

$$
\frac{R_C}\tau=C_7-(105-48q)\theta-B_7\omega,
\quad C_7=105-48a>0,
$$

$$
B_7=(q-1)(s+7)+D_0=(q-1)(h+2a)-1=-D_7,
\quad D_7=(1-q)(s-2q)+5-4q.
\tag{64.27}
$$

该方向来自 untouched C，包括原 15qT。

**N7 的精确限制。** 任意实际普通端点无 $a<q\le1$；若 $1<q\le5/4$，则 $B_7>0$ 且 $h>1/(q-1)-2a$。证明由 Q 得

$$
H(\theta-1)=-(q-a)R_7,\quad R_7=m+2-2(q+a),
$$

$$
H[(105-48q)\theta-C_7]=-(q-a)M_7,
$$

$$
M_7=(105-48q)m+306-210a-(210-96a)q.
$$

在 0<q≤1，先有 H≥2、D7≥1；M7 的 q 系数负，故 $M_7\ge57m+96-114a>114a+39>0$。原常数于是给 $\omega=-(q-a)M_7/(HD_7)$，与 N6 一起排除 a<q≤1。q=a 另在例外支。在 1<q≤5/4，$H(q)-H(5/4)=2(5/4-q)(q+1/4)\ge0$，故 H≥11/8；$R_7>2a-3/2>0$，因此 0<θ<1。于是 $(105-48q)\theta-C_7<-48(q-a)<0$。N6 及原 $D_7\omega$ 方程迫 D7<0，才除正 q−1 得所述必要界。没有全域 D7 或 H 除法，也没有存在断言。∎

**N8 的全部实际 H=0 族及 converse。** 置

$$
\phi=\frac{1+\sqrt5}{2},\quad\chi=\phi-1,\quad
H(q)=2(\phi-q)(q+\chi),\quad
m_H=\frac{3a}{\phi-a}=2(a+\chi),\quad Z_H=m_H+1,
$$

$$
I_H=(2aZ_H-4a^2,Z_H^2/4).
\tag{64.28}
$$

H 唯一正零为 φ，原 Q 强制 m=mH；等式由 $H(a)=3a=2(\phi-a)(a+\chi)$ 得来。$3/2<\phi<5/3,3/4<a<4/5$ 给 $5/2<m_H<3,7/2<Z_H<4,Z_H>4a$。IH 宽为 $(Z_H-4a)^2/4>0$，每个 V∈IH 经父 converse 得严格达到父，而且

$$
\frac94<V<4,\quad-\frac{75}{4}<n=V-2m_H-15<-16,
\quad\frac{72}{5}<\bar C<19,
$$

$$
\frac{11}{2}<u_H=2\phi+2a+1<6,\qquad -4<\eta=n/u_H<-\frac83.
$$

对 s≥2φ 定义

$$
\theta(s)=\frac{m_H-\eta}{s+1}>0,\quad h=s+5-u_H,\quad
B_H(s)=\chi s-3\phi,
$$

$$
R_H(s)=15\phi\theta+B_H(s)(3\theta-h\eta)-\bar C=-R_C/\tau.
\tag{64.29}
$$

Q 直接成立，ordinary 由定义成立；不除 H。边界 2φ 的预测常数是

$$
\alpha_Hm_H+\eta[(3\phi-2)(4-2a)-\alpha_H],\qquad
\alpha_H=\frac{6(\phi+1)}{2\phi+1}<4.
$$

括号正，因为前一个乘积大于六；预测值小于十二而 Cbar>72/5，故 RH(2φ)<0。这个边界不是世界。在 s=4，θ4<7/5、h4>3、BH(4)=φ−4，故

$$
R_H(4)=(18\phi-12)\theta_4+(4-\phi)h_4\eta-\bar C
<\frac{126}{5}-\frac{56}{3}-\frac{72}{5}<0.
$$

连续表达式恰为

$$
R_H(s)=3(m_H-\eta)\chi+\frac{A_H}{s+1}
-\eta(\chi s-3\phi)(s+5-u_H)-\bar C,
\quad A_H=3(m_H-\eta)(\phi+1)>0.
$$

写成 $c_Hs^2+b_Hs+d_H+A_H/(s+1)$，其中

$$
c_H=-\eta\chi>0,\quad b_H=-\eta[\chi(5-u_H)-3\phi],
\quad d_H=3(m_H-\eta)\chi+3\eta\phi(5-u_H)-\bar C.
$$

取有限 $S>4,1,2|b_H|/c_H,\sqrt{2(|d_H|+1)/c_H}$，则 RH(S)>0。介值定理在有限 [4,S] 给根 sH>4。对 $2\phi\le x<y<z$，两连续割线斜率之差为

$$
(z-x)\left\{\frac{A_H}{(x+1)(y+1)(z+1)}-\eta\chi\right\}>0.
$$

依据是倒数项割线 $-A_H/[(x+1)(y+1)]$、二次项的割线差及仿射项消去。若两严格根 y<z 存在，从边界 x=2φ 到 y 的斜率正，y 到 z 的斜率零，矛盾。故整个严格源射线上根唯一。

在此根用 P(φ,sH)、(64.17) 的整个 gain 和固定 d 重建。源严格，首项非零；ordinary 恢复全部偶系数和原一次式，Q 不经除法成立，RH=0 恢复 untouched $C-15\phi T=B_{\rm src}F_{\rm orig}$。BOTH 恒等式恢复 SAME 六行。定义 $\kappa_H=(s_H+4)(5\theta+\eta)$，未除的 J iff 恢复该 SAME 世界的实际第七行，且 κH<8mH。

反向每个实际 H=0 世界由 Q、父区域、ordinary、原 C 必有这些参数、θ(s) 和 RH(s)=0，故等于此唯一世界。两例外满足

$$
\kappa_p-8m_H=(p-4)(v-5)>0,\qquad
\kappa_v-8m_H=(v-4)(p-5)>0,
$$

因为 p,v<ZH<4。因此这些父的任何 κ≤8mH 子片均无匹配例外。这个实际高 q 族没有被排除；它是端点族，不是 SAME-κ 普通对、碰撞或单点子片定理。

### 64.7. N9：全部 q 的实际普通对充要关系

固定 SAME (64.4)、(64.7) 的 $a_0,\tau,m,n$（其中 $n<0$）与 SAME $\kappa\le8m$。取

$$
0<q<r,\quad q,r\ne a,\quad\ell=r-q>0,\quad s\ge4,\quad\rho>0,\quad t>0.
$$

此处 t 是第二端 θ，不是原时钟；r 是第二端 q，不是 r0。定义

$$
\begin{aligned}
u&=2q+2a+1,&U&=2r+2a+1=u+2\ell,\\
K_p&=15+(s+1)\rho,&L_p&=s-1+\rho,\\
D_p&=uK_p,&R_p&=2\rho/D_p,&V_p&=s^2-16,\\
S&=s+\ell R_pV_p,&\alpha&=R_pL_p,&\beta&=R_pK_p=2\rho/u,\\
M_p&=S+1-\rho.
\end{aligned}
\tag{64.30}
$$

u,U,Kp,Lp,Dp,Rp 均正，Vp≥0。端点是

$$
(q_1,s_1,\theta_1,\eta_1)=(q,s,t(1+\ell\alpha),-\rho tU/u),
\qquad(q_2,s_2,\theta_2,\eta_2)=(r,S,t,-\rho t).
\tag{64.31}
$$

必须保留 ALL 过滤：

$$
s>2q,\qquad S>2r,
$$

$$
tM_p=m,\qquad-U\rho t=n,\qquad(S+4)(5-\rho)t=\kappa,
$$

$$
t[(r-a)M_p+H(r)]=3a,\qquad
M_p=H(q)\alpha+2(q+r-1),
$$

$$
\bar C-15q_i\theta_i-[(q_i-1)s_i+D_0(q_i)](3\theta_i-h_i\eta_i)=0
\quad(i=1,2),\qquad h_i=s_i+5-(2q_i+2a+1).
\tag{64.32}
$$

SAME 父的全部严格区域、a0、τ 也不变。两 Q 与两 untouched C 独立保留。

证明必要性。不同实际世界有不同 q，由固定 q 的完整图谱可知。排序后令 t=θ2、ρ=−η2/t；同 n 给 η1=−ρtU/u、β=2ρ/u。初始只定义 $\alpha=(\theta_1-\theta_2)/(\ell t)$、$k=(s_2-s_1)/\ell$，不假设它们的符号。同 m 和同 κ 精确相减给

$$
k=(s+1)\alpha-\beta,\qquad
k(5-\rho)=(s+4)(5\alpha-\beta).
$$

不除 5−ρ 消去 k，得 αKp=βLp；右边和 Kp 正，故 α=RpLp>0。再得

$$
k=R_p[(s+1)L_p-K_p]=R_pV_p.
\tag{64.33}
$$

端二给 m,n,κ 及第一个 Q；两 Q 相减用 $H(q)-H(r)=2\ell(q+r-1)$，只除正 ℓt，得第二个 Q。每端原 C 各自必要，故 ALL 过滤成立。

证明完整 converse。通过 ALL 过滤的元组有 $u\eta_1=U\eta_2=n$。恒等式 $(s+1)\alpha-\beta=R_pV_p$ 恢复两端同 m。又

$$
5\alpha-\beta=R_p(s-4)(5-\rho),\qquad
S-s=\ell R_p(s-4)(s+4),
$$

恢复两端 SAME κ，包括 s=4、ρ=5 而不除它们。端二 Q 与反向相减恢复 BOTH Q；BOTH 原 C 各自施加。每端以 (64.10)、(64.17) 重建严格 P、整个非零 gain、各自固定 d；同 m,n 恢复每个偶系数及 Lres，Q 与 untouched C 恢复每个奇系数，包括原 C/15qT。BOTH 整个恒等式恢复 SAME 六行，(64.18) 恢复 SAME 第七行。不同 q,r 给不同源。因此这是原世界对的双向充要关系，不只是投影或存在主张。H=0 从未除去。

为保留精确末碰撞问题，令

$$
B_p=8L_p-K_p=8s-23+(7-s)\rho,\quad
C_p=32L_p-K_p=32s-47+(31-s)\rho,\quad A_p=s+4-4q,
$$

$$
W_p^{\rm pol}=D_p[17+(s-U-2)\rho]+2\ell\rho^2V_p,
$$

$$
P_J=D_p[7+(U+2-s)\rho]-2\ell\rho^2V_p+2q\rho B_p,
$$

$$
P_M=48D_p^2-(96q\rho L_p+2A_p\rho C_p)D_p
 +(2\rho V_p-4D_p)W_p^{\rm pol}.
\tag{64.34}
$$

由整个 gain，$\omega_2/t=W_p^{\rm pol}/D_p$；同子片 (64.25) 给 $\omega_1/t=\omega_2/t+\ell(32\alpha-\beta)$。有限相减 x,y 得

$$
\frac{x_2-x_1}{2\ell t}=24-\omega_2/t+q(8\alpha-\beta)=P_J/D_p,
$$

$$
\frac{y_2-y_1}{\ell t}=48-48q\alpha+(R_pV_p-4)\omega_2/t
 -A_p(32\alpha-\beta)=P_M/D_p^2.
$$

这里 $8\alpha-\beta=2\rho B_p/D_p$、$32\alpha-\beta=2\rho C_p/D_p$，解释了全部系数；第二式还用末源因子的差为 ℓ(RpVp−4)。分母和前因子先正。WITH ALL (64.32)，PJ=0、PM=0 分别 iff 此实际普通对的 J、M 碰撞。未过滤零点不是世界；本文不推出任何全称 PJ/PM 符号。

### 64.8. N10–N13：原 C 的正不变量、六障碍与精确完成带

**N10。** 每个严格达到父都有

$$
I=\frac{C-3D}{\tau}>0.
$$

证明令 ε=1−a、$W=V-2aZ+4a^2>0$。$f(x)=x^2+x/2-1=(x-a)(x+a+1/2)$ 与 $f(11/14)=1/98>0$ 给 a<11/14，故 11−14a>0、37−42a>4。原父系数给

$$
I=7\epsilon V-3aZ+9a
=7\epsilon W+a(11-14a)Z+a(37-42a)>0.
\tag{64.35}
$$

此父正性不需 n<0。对实际普通负 n 世界，原 C 和原 Q 分别给

$$
C/\tau=15q\theta+B_{\rm src}(3\theta-h\eta),\qquad
D/\tau=qm+H\theta.
$$

减去三倍后一式，用 ordinary，θ 系数为 $15q+3B_{\rm src}-3q(s+1)-3H=3(q-s)$，η 系数为 $-hB_{\rm src}-3q$。所以

$$
I=3(q-s)\theta-G_C\eta,\qquad G_C=hB_{\rm src}+3q.
\tag{64.36}
$$

若 GC≤0，s>2q、θ>0、η<0 使右边严格负，矛盾。因此先证明 GC>0，再可除 θ 得 $(-\eta/\theta)G_C>3(s-q)>0$。原 C/15qT 对该式不可缺。∎

**N11。** 每个 κ≤8m 子片的实际普通端点都有 q>1、s>6。先由 (64.19) 有 s≥4。若 0<q≤1，则

$$
B_{\rm src}\le4(q-1)+D_0=-2(q-3/4)^2-7/8\le-7/8,
\quad h\ge6-2a>22/5,
$$

所以 $G_C<-77/20+3=-17/20<0$，矛盾；q=a 仍只在例外支。

若 4≤s≤6，严格源给 1<q<3。固定 q 的多项式

$$
G_q(z)=(z-2q+4-2a)[(q-1)z+D_0]+3q
$$

二次系数 q−1>0，对 L<R 有完整有限弦式

$$
G_q(z)=\frac{(R-z)G_q(L)+(z-L)G_q(R)}{R-L}
 -(q-1)(z-L)(R-z).
\tag{64.37}
$$

在 1≤q≤2 令 x=q−1∈[0,1]。完整展开为

$$
G_q(4)=2a-3+(2a-1)x+(4a-10)x^2+4x^3
\le2a-3+(2a-1)x+(4a-6)x^2\le4a-4<0,
$$

$$
G_q(6)=2a-5+(13-2a)x+(4a-18)x^2+4x^3\le-Q_x,
$$

$$
Q_x=(14-4a)x^2-(13-2a)x+5-2a,
$$

$$
4(14-4a)Q_x=[2(14-4a)x-(13-2a)]^2+139-154a>0.
$$

用 x³≤x²、2a−1>0、4a−6<0，以及 a<4/5；最后余项大于 79/5。在 2≤q≤3 令 y=q−2∈[0,1]，则

$$
G_q(6)=4a-6+(6a-11)y+(4a-6)y^2+4y^3
\le4a-6+(6a-11)y+(4a-2)y^2
\le4a-6+(10a-13)y<0.
$$

先用 y³≤y²，再用正 4a−2 与 y²≤y。对 1<q≤2 在 [4,6] 用弦式；对 2<q<3 在 [2q,6] 用它，该段长度正且

$$
G_q(2q)=8-4a+(6a-9)q\le8a-10<0.
$$

两种情况都使实际 GC<0，与 N10 矛盾。弦端只是多项式参数，不假设实际；因此完整排除 4≤s≤6，得 s>6。∎

**N12 的精确范围。** 在这个实际普通域，

$$
7\kappa-50m=-15(s-6)\theta+(7s-22)\eta<0,
\qquad\kappa<50m/7.
\tag{64.38}
$$

两个项各严格负。故每个 SAME 实际可达、$50m/7\le\kappa\le8m$ 的 ENTIRE 子片无普通成员，至多一个例外匹配，而可达给至少一个成员，所以恰是一个匹配例外，七 TOTAL 即恢复整个世界。完整逆只用取得六行识别父、恢复 a0,τ,m,n 及无序 p,v，再从实际 J 行形成 κ、比较 (64.23)。若 κp 匹配，返回

$$
P(a,p),\quad\lambda=-7\tau V,\quad\mu=p\tau(v-7),
\quad\nu=p\tau,\quad d=a_0+7\tau V;
$$

另一匹配则交换 p,v。例外 converse 恢复每个原系数、BOTH 恒等式、SAME 六行，实际匹配恢复 SAME 第七行。反向每个兼容世界只能是该例外，故存在唯一。无匹配表示本类未达到，不是空集停止成功。此定理包含带的两个端点，条件是实际可达；不宣称每个父达到此带、每个带值可达、普通或非单点存在、尖锐性或第八读必要性。

**N13 的全响应普通末 gain 正性。** 任意实际取得 κ 下，普通世界均有 ω>0。q≤5/4 由 N6。q≥5/4 时严格源给

$$
B_7=(q-1)(s-2q)+4q-5>0.
$$

若 θ≥1，原偶式在七给

$$
(s+7)\omega=sF+7V+105(\theta-1)>0.
$$

若 0<θ<1，用 untouched 原常数 (64.27)。写 AC=105−48q；若 AC≥0，则 $C_7-A_C\theta\ge C_7-A_C=48(q-a)>0$，包括 AC=0；若 AC<0，右边大于 C7>0。因 B7 已正，ω>0。这些情形穷尽全部实际普通世界，包括 H=0 和两种 τ 符号。因此 g(7) 的符号是 τ 的符号，不给观察或 d 的符号；例外仍合法末零。逐点 y>x 不等于 ENTIRE 单函数单射。∎

N8 实际族由这些通用定理进一步有 sH>6、κH<50mH/7；这加强其界而不删除实际 H=0 世界。κ>8m 上 (64.38) 没有被证明，也没有从正 n 移用符号。

### 64.9. N14：严格源间隙障碍与完整有限弦证明

以下只对 (64.4)、n<0、实际取得 κ≤8m 的实际普通端点。定义

$$
\xi=s-2q>0,\qquad d_g=4-2a,\qquad \frac{12}{5}<d_g<\frac52,
$$

$$
h(x)=x+d_g,\qquad
\mathcal A(x)=h(x)(x-3)+3=x^2+(1-2a)x+6a-9.
\tag{64.39}
$$

这里 dg 不指漂移 d，$\mathcal A$ 不指父插值 A。在 s=2q+ξ，原式的全部系数给

$$
B_{\rm src}=(q-1)\xi+2-3q=(q-1)(\xi-3)-1,
$$

$$
G_C=(q-1)\mathcal A(\xi)+3-h(\xi).
\tag{64.40}
$$

$x$ 的一次系数 dg−3=1−2a，常数 3−3dg=6a−9，故展开完整。

**定理 N14。** 每个上述实际普通端点都满足

$$
\xi>\xi_*:=\frac{2a-1+\sqrt{41-30a}}2,
\qquad 2<\xi_*<3.
\tag{64.41}
$$

证明先完整排除 0<ξ≤2。N11 给 q>1、s>6，假设该小间隙则 $q=(s-\xi)/2>2$。固定该 q，令

$$
G(q,x)=(x+d_g)[(q-1)x+2-3q]+3q.
$$

二次系数 q−1>0，其两个辅助端值为

$$
G(q,0)=2d_g+3q(1-d_g)<2d_g+6(1-d_g)=8a-10<0,
$$

$$
G(q,2)=q(1-d_g)<0.
$$

第一严格号用 q>2、1−dg<0。对整段 0≤x≤2，精确有限弦是

$$
G(q,x)=\frac{2-x}{2}G(q,0)+\frac x2G(q,2)-(q-1)x(2-x).
\tag{64.42}
$$

两权非负、和一、两端严格负、最后被减项非负，故 G(q,ξ)<0，与原 C 导出的 GC>0 矛盾。辅助零点不是补入的边界源，二也不假定实际。因此 ξ>2。

现在 h(ξ)>2+dg>4，故 h(ξ)−3>0。由 (64.40)、GC>0 得

$$
(q-1)\mathcal A(\xi)>h(\xi)-3>0.
$$

先有 q−1>0，才得 $\mathcal A(\xi)>0$。

$\mathcal A$ 的常数 6a−9<0、首项一，判别式用 a²+a/2=1 化为

$$
(1-2a)^2-4(6a-9)=41-30a>0.
$$

两实根异号，唯一正根恰为 ξ*。又 $\mathcal A(2)=2a-3<0$、$\mathcal A(3)=3>0$，故 2<ξ*<3。按两根因式，在 ξ>0 上 $\mathcal A(\xi)>0\iff\xi>\xi_*$，得到 (64.41)。∎

这只给必要界，不宣称 ξ* 是达到下确界、尖锐常数或存在端点。特别 N8 的实际端点满足 $s_H>2\phi+\xi_*$；H=0 未被丢弃。两个原残式和全部原行始终保留。

### 64.10. N15：SAME 原 C 不变量的精确有限差分

取 ANY 两个不同实际普通世界，必须在 ONE SAME $a_0,\tau,m,n$（其中 $n<0$）达到父和 ONE SAME 实际取得 κ≤8m 子片。按 q<r 排序，使用 (64.30)–(64.32) 的 ALL 过滤；尤其 BOTH Q、BOTH untouched C、BOTH 严格源都保留。置

$$
\ell=r-q>0,\quad k=\frac{S-s}{\ell}=\frac{2\rho(s^2-16)}{uK_p},
\quad X=s-2q,\quad Y=S-2r,
$$

$$
c_a=2a+1,\quad u=2q+c_a,\quad U=2r+c_a=u+2\ell,
\quad t=\theta_2>0,\quad\rho=-\eta_2/t>0.
\tag{64.43}
$$

N11 与 N9 先给 s>6、k>0、S>s；N14 分别给 X,Y>ξ*>2、$\mathcal A(X),\mathcal A(Y)>0$。两端的 SAME $I=(C-3D)/\tau$ 必须固定，不能仅用它各自为正。

令 w=−n>0，并定义

$$
\mathcal R(q,x)=\frac{(q-1)\mathcal A(x)-h(x)}{2q+c_a},
$$

$$
L_g=(c_a+2)\mathcal A(X)+2h(X),\qquad
E_g=(r-1)(X+Y+d_g-3)-1.
\tag{64.44}
$$

**精确不变量恒等式。** 每个实际端点由 (64.36)、ordinary 给

$$
I+3m=3(q+1)\theta+(3-G_C)\eta
=3(q+1)\theta+w\mathcal R(q,\xi).
\tag{64.45}
$$

其中 −η=w/(2q+ca)、GC−3=(q−1)$\mathcal A(\xi)$−h(ξ)。这是 SAME 原 C,D,τ 的等式；只保留一个常数过滤或换父，不能得到两个端点同 I。必要差式本身也不替代两原常数。

下面逐项给全部有限差分系数。在固定 X，交叉相乘得

$$
\mathcal R(r,X)-\mathcal R(q,X)=\frac{\ell L_g}{uU}.
\tag{64.46}
$$

$\mathcal A(X)$ 的分子系数是 $(r-1)u-(q-1)U=\ell(c_a+2)$，h 的贡献是 h(X)(U−u)=2ℓh(X)，故 Lg 的每个符号均确定。在固定 r，

$$
\mathcal A(Y)-\mathcal A(X)=(Y-X)(X+Y+d_g-3),\quad
h(Y)-h(X)=Y-X,
$$

所以

$$
\mathcal R(r,Y)-\mathcal R(r,X)=\frac{(Y-X)E_g}{U}.
\tag{64.47}
$$

没有除 Y−X，也未假设其符号；交叉点 (r,X) 仅是有理式比较点，不是实际中间世界。因为 Y−X=ℓ(k−2)，合并两式得

$$
\mathcal R(r,Y)-\mathcal R(q,X)
=\ell\left[\frac{L_g}{uU}+\frac{(k-2)E_g}{U}\right].
$$

又 $\theta_1=t(1+\ell\alpha)$，故

$$
(r+1)\theta_2-(q+1)\theta_1=\ell t[1-(q+1)\alpha],\quad w=U\rho t.
$$

从两个 SAME (64.45) 相减，只除正 ℓt，得到完整兼容式

$$
0=N_g+\rho(k-2)E_g,\qquad
N_g=3[1-(q+1)\alpha]+\rho L_g/u,
$$

$$
\alpha=\frac{2\rho(s-1+\rho)}{u[15+(s+1)\rho]}.
\tag{64.48}
$$

以下正性证明先于任何 $\rho E_g$ 除法。

### 64.11. N15 的 L、E、N 正性及严格定量亏量

首先 ca+2>0、$\mathcal A(X)>0$、h(X)>4 给

$$
L_g>2h(X)>3.
$$

因 X>2>2a=ca−1，有 $u=2q+c_a<s+1=2q+X+1$；两分母正，所以

$$
\frac{L_g}{u}>\frac3{s+1}.
\tag{64.49}
$$

其次证明 Eg>0，不预设 X,Y 所需次序。令 z=min(X,Y)>2，选择具有间隙 z 的那个实际端点，记其 q 坐标为 qj∈{q,r}。于是 r≥qj>1，且该端原 C 给

$$
(q_j-1)\mathcal A(z)>h(z)-3,
\qquad(r-1)\mathcal A(z)>h(z)-3.
$$

后一式用 $\mathcal A(z)>0$。置 Dg=2z+dg−3>0，完整正多项式恒等式为

$$
\begin{aligned}
[h(z)-3]D_g-\mathcal A(z)
&=h(z)^2-3h(z)-3z+6\\
&=(d_g+2)(d_g-1)+(z-2)(z+2d_g-4)>0.
\end{aligned}
\tag{64.50}
$$

两边完整展开同为 $z^2+(2d_g-6)z+d_g^2-3d_g+6$。最后各因子均正，因为 z>2、dg>2。先将实际端点不等式乘正 Dg，再用此恒等式，得

$$
(r-1)\mathcal A(z)D_g>\mathcal A(z)>0.
$$

现在 $\mathcal A(z)>0$ 已证明，才取消它，得 (r−1)Dg−1>0。又 X+Y+dg−3≥Dg、r−1>0，所以 Eg>0。这里两个端点障碍确保取到的最小间隙仍来自实际端点，没有假设任何中间点实际。

最后由 15>0、ρ>0 及各正因子，

$$
\alpha<\frac{2(s-1+\rho)}{u(s+1)},\qquad
u=2(q+1)+(2a-1)>2(q+1),
$$

所以

$$
(q+1)\alpha<\frac{s-1+\rho}{s+1}.
$$

将它代入 Ng，使用 (64.49)，逐个严格号得

$$
\begin{aligned}
N_g&>\frac{3(2-\rho)}{s+1}+\rho\frac{L_g}{u}\\
&=\frac6{s+1}+\rho\left[\frac{L_g}{u}-\frac3{s+1}\right]
>\frac6{s+1}>0.
\end{aligned}
\tag{64.51}
$$

这对 EVERY ρ>0 成立，不限制 κ 的符号，不限制 ρ 小于五，不除 5−ρ 或任何 gain 样本。

**定理 N15。** 每个 (64.43) 的实际普通对满足

$$
0<k<2,\qquad
2-k=\frac{N_g}{\rho E_g}>\frac6{\rho E_g(s+1)}>0,
$$

$$
0<S-s<2(r-q),\qquad Y=S-2r<X=s-2q.
\tag{64.52}
$$

证明此时 ρ、Eg 已正，才能从 (64.48) 除它们，得到严格定量界；另由 N9、s>6 已先有 k>0。二者合并给 (64.52)。没有断言任何实际对存在。∎

回到同一个严格原源，

$$
b_2=2/S<2/s=b_1,
$$

$$
(r_0)_2-(r_0)_1=\frac{2\ell(s-qk)}{sS}
>\frac{2\ell(s-2q)}{sS}>0.
\tag{64.53}
$$

这里 q>0、k<2、s>2q，分母先正。不给 $c_{\rm src}$ 差、各自固定漂移差或实际末响应差的符号；也不将这两个端点序外推到连续或无限实际族。

### 64.12. 必要限制之后的 ENTIRE 选择器边界

每个完整 N9 实际对在目标区域内有

$$
1<q<r,\quad s>6,\quad S>s,\quad\kappa<50m/7,
\quad X,Y>\xi_*,\quad Y<X,
$$

并满足 (64.52) 的严格定量界。N13 还给 $W_p^{\rm pol}>0$、$W_p^{\rm pol}+2\ell\rho C_p>0$，分别对应两个正 ω。BOTH Q、BOTH untouched C、BOTH 严格源、SAME 父与 SAME κ、每条 SAME 原行都仍为必要过滤。没有从这些正性推出 PJ、PM、Bp 或 Cp 的符号。

全部非递减间隙实际普通对被排除；递减间隙对仍未排除。N14–N15 不证明普通对存在，不证明其不存在，不证明每个子片至多一个普通世界，不给实际碰撞，也不给一般 ENTIRE 末函数选择器。

如果另有真正证明的取得记录守卫排除每个剩余普通对，则 (64.24) 的可达子片至多一个普通 O 加一个实际匹配例外 E。单点七 TOTAL 停；两点时若 x(O)≠48a 选 J，否则由 N13 和严格源，y(O)−48a=(s+4−2q)ω>0，选 M。仅取得所选时钟七响应 f，规范化为 $(f-a_0-R(7))/\tau$，保留完整候选中所选 x 或 y 等于它者。真实世界给存在，ENTIRE 所选分离给唯一；普通或例外的完整 converse 恢复 SAME 七行，所选等式恢复第八行。这是有额外守卫前提的集合论充要逆，不是本卷已经取得的全称守卫、有效求解器或未知类并集逆。

N12 实际完成带仍是 EVERY 可达 $50m/7\le\kappa\le8m$ 子片，七 TOTAL 恢复，无须末读。κ<50m/7 的剩余普通区域和 κ>8m 的区域仍缺一般完成。低 q 与 s=4 的既有局部接口保留原假设；本域 κ≤8m 下原 C 已证明没有普通 q≤1 或 s=4，不是删除原源坐标。例外保留一切合法 s=4 和末零。实际 H=0 族阻止把低 q 守卫变成全域覆盖。

### 64.13. SAME 父坏 M 的 FULL 桥梁与条件支持

由偶整个式在原时钟六，实际 M 响应为

$$
h_M=a_0+E(6)+48T,\qquad
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
$$

要得到 FULL 子片等号，必须排除 ALL 普通 T=τ，不能只排除普通末零。反设 θ=1，原 Q 给 $u=m+3=Z+2$、$q=(Z+1)/2-a$、δ=q−a>1/2。令 ho=s−Z+7>8−2a>6，ordinary 与全部偶系数给

$$
V=(7-h_o)Z+23-2h_o,\qquad
 g=s\tau(t^2-h_ot+\chi_o),\qquad
\chi_o=h_o^2-9h_o+23=(h_o-9/2)^2+11/4>0.
$$

untouched 原常数是 $(a-1)(-7V)-15\delta=B_{\rm src}\chi_o$。减去 (a−1)sχo 并用 D0=−δ(Z+2)，因

$$
(h_o-9)\chi_o+15=(h_o-4)(h_o-6)(h_o-8),
$$

得到

$$
-7V=s\chi_o-\frac{\delta(h_o-4)(h_o-6)(h_o-8)}{1-a}.
\tag{64.54}
$$

原 15δ 保留。负左边、正 sχo、δ>0、ho>6 强制 ho>8。由 V>4a²、Z>4a 及线性 V 式，有

$$
V<23+28a-(4a+2)h_o,\qquad
h_o<\frac{19+30a}{4a+2}<17/2.
$$

最后比较用 4a−2>0。在此严格区间，正三因子积<45/8，χo>15 因 χo−15=(ho−8)(ho−1)>0，且 1−a>1/5。故该积除以 (1−a)χo 小于 15/8；又 0<δ<q<s/2，(64.54) 反迫 $-7V>s\chi_o/16>0$，矛盾。

所以 FULL 原 M 子片恰为 {Wp,Wv}。两个整个 gain 在七都零、固定漂移都 d*，因此 EACH 实际 MJ、MM 的 FULL 响应 d* 末片也恰为同一对。父、该 M 子片、两末片和所有已服务共同祖先均保留不同完整目标及非单点停止守卫。其取得 J 响应不同，故不是 SAME-J 子片碰撞，也不服务早期未取得另一臂。

对同历史 K⊆K′，每个实际 E、同响应 z 的 K 子片包含于对应 FULL K′ 子片。令 L0 要求两个不同完整目标；L(h+1) 要求父非单点、EACH 动作有一个实际 FULL 响应子片满足 Lh。基步不同性随包含保持；归纳保留各动作原响应见证，使用子片包含与归纳假设，并保留父守卫。故任意基数的有限深失败向上保持。

ONLY IF 一个 SAME 取得 J 子片实际具有 x 碰撞对及 y 碰撞对，可取其至多四完整端点，加 SAME 父坏 M 对至多二端。按完整世界去重后至多六端的条件支持保留 BOTH 动作、实际 FULL 片、已服务祖先和所有停止守卫。这是已实现局部失败的条件支持界，与既有 n≠0 的 ENTIRE 子片至多六基数界是不同陈述；都不供给实现、最小支持、尖锐性、单函数单射或根失败树。

### 64.14. 保留接口、严格边界与证据范围

n≠0、κ=8m 的既有完成只在其确切条件内保留；本卷 N12 给本负 n 类可达该响应的例外单点逆。Γ>0 的已知逆、Γ=0 的唯一仿射普通世界加两例外、N=0 的精确两例外及七 TOTAL 逆分别保持各自假设。Γ=0 的普通仿射域有 n>0，不被本域派生真正二次删除；N=0 保留 $(p-2)(v-2)=17,p,v>2,p\ne v$，它不同于 Γ=0。另行给定的 B0 接口仅在自身假设内保留，本卷不提供未载于此的完整 B0 证明。正 n 的符号、源区间、间隙序、独立已知类逆均不移用到本域或未知并集；其他域的历史状态不作为本卷的当前全项目结论。

原源 q>0、s>2q，父 p,v>2a、p≠v、τ≠0。q=0、s=2q、r0=0 或一、b=0、csrc=0、p=2a、p=v、τ=0、极限或无限源均不补作世界。辅助弦端、交叉点、最小间隙的多项式值、有限 IVT 比较点和正根图点，只有 ALL 原过滤成立才是世界。没有假设中间可行、简单根、一般次数、有限枚举或残式非退化。

两种 τ 符号、任意 a0、各自固定漂移、合法 H=0、s=4、s=4q、b=1/2、r0=1/2、个别系数/样本/观察零、采样或非采样及重复 gain 根、消去次数、重复或恒零次级残式，均受原式处理。只有整个零 gain 在原域先验排除；普通真正二次、θ>0、F>0、末 gain 非零都是相应域内的派生结论。N11 与 N14 按原 C 证明排除特定普通端点，例外仍可合法末零。固定漂移可抵消非零 gain 贡献成为零观察。

除法顺序是：源逆先 b,s>0；父归一化只用 τ≠0 不定其符号；普通先 q≠a；u>0 先于 η；Kpos>0 与 Γ<0 先于 θ>0 和正根逆。H 不作全域分母；N7 仅在已证正的受限区间除 H、D7。N8 先有 φ−a、uH、s+1、cH、弦分母正。N9 只除正 ℓ,t,u,U,Kp,Lp,Dp，不除 s−4 或 5−ρ。N10 先证 I、GC 正；N11 先证有限弦长度及 14−4a 正。N14 先排除整段小间隙，再证 $\mathcal A$ 正与判别式正。N15 先证 u,U,ℓt,s+1、Lg、Eg、Ng、ρ 正，最后才除 ρEg；最小间隙论证取消 $\mathcal A(z)$ 前已证其正。没有取消未知 gain 样本、观察、源/漂移差、λ、μ、s−4q、残式首项、根重数或未证判别式。

这里没有执行数学求值、代入程序、数值、导数、递推、枚举、CAS、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe 或 Lean/proof-kernel；没有 D5、Blueprint、Reg、摄入或消化。本卷不提供经验 ML/NN、物理、噪声、稳定性、连续逆、有限精度、可计算性、有效判定、效率、复杂度、资源、最小支持、达到障碍尖锐性、一般 gain 空间逆、gain 跨度下界、文献穷尽、外部原创性或优先权认证。

### 64.15. INERT 的完整全局共同实现合同

此合同为 INERT、UNEXECUTED、UNFULFILLED。保留 ALL 256 终叶槽

$$
\sigma=(w,\varepsilon),\qquad w\in\{J,M\}^7,\quad\varepsilon\in\{0,1\},
$$

ALL 254 非空实际前缀 v，原长度 i=1 至七，其实际即时左乘积 Av 和 EVERY 后代。令

$$
t_v(P)=\operatorname{tr}(A_vP),\quad
\ell_v(P)=(t_v(P)-1,\ it_v(P),\ i^2t_v(P),\ i^3t_v(P)).
$$

对 EACH 前缀及 EACH 规定的非代表后代 σ，针对 SAME 前缀代表 ρ 保留 WHOLE 行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0
$$

于 ONE SAME 完整 $1538\times1024$ 关系。继承层规格 254、252、248、240、224、192、128 全保留。尺寸与层数是给定的惰性规格，不是执行枚举或认证。

ONE 共同堆叠向量包含 ALL 256 整个四系数 gain 块；每个 WHOLE 块非零，每个适用 SAME-source 终叶 WHOLE 四分量差 $x_{(w,0)}-x_{(w,1)}$ 非零。ALL 严格源、ALL 祖先关系、BOTH 动作义务和 ALL 停止守卫须在 SAME 向量、SAME 世界同时满足。每槽自始固定

$$
g_\sigma(t)=\sum_{h=0}^3x_{\sigma h}t^h,\qquad d_\sigma=a_0-x_{\sigma0}
$$

跨全部原行使用。只合并整个 P,g,d 相等的槽；二次限制 $x_{\sigma3}=0$ 同时作用于全部块。局部间隙定理、普通对 iff、末碰撞对、条件六端支持、较小关系、选定支持、分路径/分臂解、遗漏后代、另取守卫向量或逐行 refit 都不满足这个共同合同。原生成族不在本卷内容之内；没有实例生成、求解或履行断言。

### 64.16. 精确完成义务与两个原 FULL 根

**正 ENTIRE 完成 OPEN。** 对 EVERY (64.4)、n<0 的实际达到父和 EVERY 可达 SAME κ，证明子片为单点可停，或至少一个末函数 x、y 在 ENTIRE (64.24) 上单射。动作只由已取得记录与完整预测选择，所得唯一逆只用该动作的一个实际时钟七响应。N12 只完成其精确可达闭带；κ<50m/7 与 κ>8m 仍缺一般完成。普通至多一个是充分路线而非原选择器的必要条件。逐点 ω>0、y>x、原源坐标序、固定 q 唯一、两坐标对点分离或有限基数均不证明 ENTIRE 单动作单射。

**负 ENTIRE 完成 OPEN。** 在 ONE SAME 达到父和 ONE SAME 实际取得 κ 的子片实际实现

$$
U_1\ne V_1,\qquad U_2\ne V_2,\qquad
x(U_1)=x(V_1),\qquad y(U_2)=y(V_2),\qquad U_i,V_i\in\mathcal K_\kappa.
$$

两对可不同、重叠或含实际匹配例外。每端必须有严格源、一个整个非零 gain、一个各自固定 d、BOTH 原过滤、ALL SAME 七原行。共同偏置与 SAME τ≠0 使此条件恰为两实际末函数各非单射；反向非单射各给一对。若要接为该父局部失败，还保留 SAME 父坏 M FULL 对、BOTH 末 FULL 片、BOTH 动作、全部已服务祖先与所有停止守卫。单一碰撞、仅六行多重性、不同父或 κ、未过滤零点和分别可达的极值都不能代替。本文没有实现这样的任一碰撞对或两动作失败。

**原 FULL 二次根 OPEN。** ALL 严格源、ALL 整个非零次数至多二实 gain、任意固定漂移的确定性自适应八 TOTAL 完整恢复 versus 原根 L7，仍未在本卷结算。没有强迫任意根策略进入 JMJMJ、完成早期未服务臂、不受限 SAME 父 L3、根失败树、minimax、第八读必要性、尖锐性或九读上界。

**原 FULL 三次根 OPEN。** ALL 整个非零次数至多三 gain 的八 TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$ 仍未结算。三次 gain 乘线性迹可为四次；四个偶节点相等可留下非零倍 $t(t-2)(t-4)(t-6)$。二次逆不检测隐藏三次次数、根、方向或平面承诺；分别已知类的逆没有跨类证明不能成为未知并集逆。

## 追加锚（本行以下为增补区）
