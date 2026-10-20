# FIB 二次负 n 的 mH 层全响应 ENTIRE 选择器

本卷独立为第 65 节。对实际已服务 $JMJMJ$ 的六次 TOTAL 记录，考虑下文完整声明的严格 $\beta=7$ 父。本文证明：在其整个 $n<0,m=m_H$ 层，每个可达实第七 J 响应的 ENTIRE 原世界集合至多两点；取得记录即可决定七 TOTAL 停止，或选择一个原时钟七末动作，仅凭该动作实际响应在八 TOTAL 恢复整个 $P,g,d$。结论覆盖每个允许的父参数、任意 $a_0$ 和两种非零 $\tau$ 符号。

主要结果为 N16 的有条件双末差分证书、N17 的全响应两点界与 N18 的完整逆。所需原世界双向桥梁及证明均列于本卷。本文是 `repo-derived` 符号综合；插值、因子定理、次数根数、Vieta 和有限区间介值定理是复用工具，不作外部原创性或优先权主张。证据为 fallible UNEXECUTED 符号数学，不是 Lean/kernel 或数值认证。其余父的全响应选择器和两个原 FULL 根问题仍为 OPEN。

## 65. 严格负 n 的 mH 层、全部响应与完整世界逆

### 65.1. 原完整世界与实际时钟

一个完整目标自始固定为

$$
W=(P,g,d),\qquad P=\begin{pmatrix}r_0&b\\c_{\rm src}&1-r_0\end{pmatrix},
\quad 0<r_0<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r_0(1-r_0),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
$$

非零迹一与零行列式给秩恰一。原域允许所有低次、两种尺度符号、系数零、样本零、观察零、采样或非采样根及重根；每个世界的 $d$ 跨全部行固定。相等与去重均按整个三元组。

实际动作与读数为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\quad Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
$$

已服务 $JMJMJ$ 给原时钟零至五，共六 TOTAL；时钟六选 J 取得 $z$，共七 TOTAL；至多再选一个时钟七动作，共八 TOTAL。没有重置、复制、跳读、平移时钟、额外端口、隐藏源/根/次数标签、逐行 refit 或未选实际响应输入。

令 $j=b+c_{\rm src}$。纸面恒等式

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r_0+A_{21}b+A_{12}c_{\rm src}
$$

以及左 J 交换两行、左 M 取旧第二行与旧两行和，给出全部相关实际迹：

| 原时钟及动作 | 实际响应 |
| --- | --- |
| $0$ | $d+g(0)$ |
| $1,J$ | $d+jg(1)$ |
| $2,M$ | $d+(1+b)g(2)$ |
| $3,J$ | $d+(j+r_0)g(3)$ |
| $4,M$ | $d+(1+2b)g(4)$ |
| $5,J$ | $d+(j+2r_0)g(5)$ |
| $6,J$ | $d+(1+2b)g(6)$ |
| $7,JJ$ | $d+(j+2r_0)g(7)$ |
| $7,JM$ | $d+(1+j+r_0+2b)g(7)$ |
| $6,M$ | $d+(1+3b)g(6)$ |
| $7,MJ$ | $d+(j+3r_0)g(7)$ |
| $7,MM$ | $d+(1+2r_0+4b+c_{\rm src})g(7)$ |

重复左乘积使用新原时钟的同一整个增益样本。令 $\mathcal S(\mathcal H_5)$ 为满足已取得六行的 ALL 原世界，令

$$
\mathcal K_{6,E,z}=\{W\in\mathcal S(\mathcal H_5):h_E(W)=z\}.
$$

这是 FULL 定义。可达恰指非空；空类不构成停止成功。

### 65.2. 完整父谓词与精确达到区域

由已取得记录置 $a_0=y_0,\ v_i=y_i-a_0$，唯一插值为

$$
E(t)=Lt+At^2,\quad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{v_4-2v_2}{8},\quad L=\frac{4v_2-v_4}{4},\quad
D=\frac{v_5-2v_3+v_1}{8},\quad B=\frac{v_3-v_1-8D}{2},\quad C=v_1-B-D.
$$

这些式恢复各三个原偶、奇节点；两个次数至多二候选之差有三个不同根即恒零，故唯一。$C$ 始终为这个原奇常数。

置

$$
a=\frac{\sqrt{17}-1}{4},\qquad a^2+a/2=1,\qquad \frac34<a<\frac45,
$$

$$
\Sigma:\ B+5D=a(L+5A),\quad \tau=\frac{D-aA}{3a}\ne0,
\quad \Lambda=\frac{C-15a\tau}{a-1},
$$

$$
U_0=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5),\quad
K=\Lambda+E+\tau U_0=\tau(t+p)(t+v)(t-7),\quad p,v>2a,\quad p\ne v.
$$

这就是本卷声明的严格父谓词。正数 $x$ 的
$\,x^2+x/2-1=(x-a)(x+a+1/2)\,$ 给所用 $a$ 界。定义

$$
Z=p+v=m+1,\quad V=pv=n+2m+15,\qquad n<0.
$$

$K/\tau$ 的全部升幂系数为 $(-7V,V-7Z,Z-7,1)$。与 $\Lambda/\tau+E/\tau+U_0$ 对比，并用 $\Sigma$，得到

$$
\Lambda=-7\tau V,\quad A=\tau m,\quad L=\tau(n-5m),\quad
D=a\tau(m+3),\quad B=a\tau(n-5m-15),
$$

$$
C=\tau\bar C,\qquad \bar C=7(1-a)V+15a,
\qquad R=aE+a\tau(U_0-V_o)+(a-1)\Lambda.
$$

最后的整个恒等式包括常数，因为 $U_0-V_o=3t^2-15t+15$。固定父就同时固定 $a_0,\tau,m,n$ 及上述全部系数。

**引理 65.1（父区域双向性）。** 除 $n<0$ 外，精确区域是

$$
Z>4a,\quad 2aZ-4a^2<V<Z^2/4,
$$

等价地

$$
m>4a-1,\qquad (2a-2)m+4a-19<n<\frac{m^2-6m-59}{4}.
$$

证明。$p-2a,v-2a$ 的和为 $Z-4a$、积为 $V-2aZ+4a^2$，且 $(p-v)^2=Z^2-4V>0$，给必要性。反向这些严格不等式给移位二次式正判别式、正和与正积；两不同实根只能都正，移回即得不同 $p,v>2a$。用 $Z=m+1,V=n+2m+15,4a^2=4-2a$ 得展开区域。65.4 的两个例外实际达到每个这样父，对任意 $a_0$ 和两种 $\tau$ 符号均成立。因此 $m>0,V>4a^2>0$ 是实际父事实。∎

### 65.3. 源双射、BOTH 整个恒等式与原系数

整个严格源域与下列开域双射：

$$
q=r_0/b>0,\qquad s=2/b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},
\quad j=q+\frac{2(1-q^2)}s.
$$

正向 $s-2q=2(1-r_0)/b>0$，秩一给 $c_{\rm src}$ 的逆式。反向四元正、迹一、$bc_{\rm src}=r_0(1-r_0)$，且返回相同 $q,s$。这没有删去任一对角侧、$s=4$ 或 $s=4q$。

定义

$$
D_0=2-q-2q^2,\quad H=D_0+3q=2+2q-2q^2,\quad
e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,\quad T=\nu/s.
$$

**引理 65.2（六原行完整 iff）。** 六原行当且仅当严格源、整个 $g\ne0$、$d=a_0-\lambda$ 和 BOTH 整个多项式恒等式

$$
-\lambda+eg=E+TU_0,\qquad -\lambda+og=R+qTV_o.
$$

证明。$e,o$ 在各原偶、奇节点恰是实际迹。各节点差的次数至多三，三次系数分别为 $T,qT$；减去对应 $TU_0,qTV_o$ 后次数至多二且有三个不同根，故恒零。反向在这些原节点取值。没有除任何增益样本。

偶式的全部升幂系数为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T).
$$

可逆重建为

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad
\lambda=sF_{\rm orig},\quad d=a_0-sF_{\rm orig}.
$$

奇式左侧全部升幂系数为

$$
\big((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\big),
$$

右侧为 $(C-15qT,B+23qT,D-9qT,qT)$。三次自动相同，其余恰为

$$
\begin{aligned}
Q&=D-qA-HT=0,\\
L_{\rm res}&=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&=C-15qT-[(q-1)s+D_0]F_{\rm orig}=0.
\end{aligned}
$$

逐系数反向恢复整个奇式，所以这些是充要原式；$C$ 和原 $15qT$ 均未改动。∎

仅在声明普通 $q\ne a$ 后，置

$$
\delta=q-a,\quad c_a=2a+1,\quad u=2q+c_a>0,\quad
\theta=T/\tau,\quad \eta=n/u<0,\quad h=s+5-u=s-2q+4-2a>0.
$$

$a$ 的方程给 $D_0=-\delta u,H=3q-\delta u$；完整原残式给精确可逆恒等式

$$
Q/\tau=3a-\delta m-H\theta,\qquad
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}-5Q/\tau.
$$

故仅取消已非零的 $\delta,\tau$ 后，$Q=L_{\rm res}=0$ 等价于

$$
3a-\delta m-H\theta=0,\qquad m=(s+1)\theta+\eta.
$$

定义 $\Gamma=n-(4a+1)m-6a<0$，则

$$
\Gamma=-K_{\rm pos}\theta,\qquad
K_{\rm pos}=u(s+1)+2H=u(s-2q+2a+1)+6q>0.
$$

因此 $\theta>0$ 是原式的结论，包括 $H=0$；普通真正二次也为结论。全部偶系数化为

$$
F:=F_{\rm orig}/\tau=n-(s+5)m+(s+2)(s+4)\theta=3\theta-h\eta>0,
$$

$$
\lambda=s\tau F,\quad \mu=s\tau(\eta-5\theta),\quad
\nu=s\tau\theta,\quad d=a_0-s\tau F.
$$

$F$ 的等号由 $n=u\eta,m=(s+1)\theta+\eta$ 归并：$\theta$ 系数为三，$\eta$ 系数为 $-h$。没有全局除 $H$。

### 65.4. 第七 J、完整正根图谱与全部实际匹配例外

原时钟四与六 J 的迹相同，均为 $1+4/s$。同一整个增益给
$g(6)-g(4)=2s\tau(5\theta+\eta)$。定义已取得量

$$
\kappa=\frac{z-a_0-E(4)}{2\tau}.
$$

第七原行恰等价于

$$
\kappa=(s+4)(5\theta+\eta)=5m+15\theta+(s-1)\eta,
\qquad \kappa-8m=(s-4)(\eta-3\theta).
$$

$\eta-3\theta<0$，所以完整双向关系为

$$
\kappa<8m\iff s>4,\quad \kappa=8m\iff s=4,\quad \kappa>8m\iff s<4.
$$

对每个辅助 $q>0$ 和每个实 $\kappa$，置

$$
b_\kappa=\kappa-5m+2\eta,\quad
\Delta=b_\kappa^2-60\eta(m-\eta)>b_\kappa^2,
$$

$$
\theta=\frac{b_\kappa+\sqrt\Delta}{30}>0,\qquad s=\frac{m-\eta}{\theta}-1.
$$

其来源为 $15\theta^2-b_\kappa\theta+\eta(m-\eta)=0$；常数负，故恰一正根、另一根负。辅助图谱点成为世界必须同时保留

$$
q\ne a,\quad s>2q,\quad
\bar Q:=3a-(q-a)m-H\theta=0,
$$

$$
\bar R_C:=\bar C-15q\theta-[(q-1)s+D_0](3\theta-h\eta)=0.
$$

记全部这样的 $q$ 为 $S_\kappa$。

**引理 65.3（普通七原行双向逆）。** 每个保留点给唯一整个普通世界，其源为 $P(q,s)$，全部系数为 65.3 的 $\lambda,\mu,\nu,d$；全部普通原世界也都这样出现。

证明。严格源和非零首项 $s\tau\theta$ 已成立。$s$ 定义恢复 ordinary 与全部偶系数；精确 $L_{\rm res}$ 恒等式恢复奇一次；$\bar Q$ 恢复奇二次；untouched $\bar R_C$ 恢复原常数 $C-15qT$；奇三次自动相同。因此 BOTH 整个恒等式恢复 SAME 六原行。将正根方程仅除已正的 $\theta$，恢复 SAME 已取得 $\kappa$ 方程与第七原行。反向每个普通原世界先有导出的 $\theta>0$，必取这个唯一正根，随后 $s$ 及全部偶系数强制相同 $P,g,d$。等 $q$ 固定整个世界，不同 $q$ 固定不同源。必要符号不能替代两个原残式。∎

在 $q=a$ 不使用普通取消。$D_0=0,H=3a$，原 $Q$ 迫 $T=\tau$，原 $R_C$ 迫 $(a-1)\lambda=C-15a\tau$，即 $\lambda=\Lambda$。偶整个式成为 $eg=K$，整个多项式增益要求 $K(-s)=0$；严格 $s>2a$ 恰接受 $s=p$ 或 $v$，正根七要求 $s=-7$ 而不合法。因此全部例外恰为

$$
W_p=(P(a,p),\ p\tau(t+v)(t-7),\ d_*),\qquad
W_v:\ p,v\text{ 交换},\qquad d_*=a_0+7\tau V.
$$

反向两源严格、首项非零、$\lambda=\Lambda$、漂移固定。$eg=K,og=aK$ 与整个父恒等式恢复 BOTH 整个恒等式、每个原系数和 SAME 六原行，包括原 $C/15qT$。这也证明每个严格区域父实际达到。

它们的实际第七测试为

$$
\kappa_p=(p+4)(v+3),\quad \kappa_v=(v+4)(p+3),\quad \kappa_p-\kappa_v=v-p\ne0.
$$

实际响应为 $z_p=d_*-\tau(p+4)(6+v)$ 及交换式，差为 $2\tau(v-p)\ne0$。仅附加 SAME 已取得测试实际匹配者，至多一个，记为 $\mathcal A_\kappa$。

源双射将每个世界分为 $q=a$ 或 $q\ne a$；两支必要性与充分性共同给 ENTIRE 等号

$$
\mathcal K_\kappa:=\mathcal K_{6,J,z}
=\{W_\kappa(q):q\in S_\kappa\}\cup\mathcal A_\kappa.
$$

此处及以后只按整个 $P,g,d$ 去重。可达性针对这个整个并集。

### 65.5. 实际末函数、原常数方向与 N6–N7 桥梁

普通世界定义

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta
=32\theta+n+\eta+5m-\kappa.
$$

原奇整个式在七给 $o(7)g(7)=\lambda+R(7)+48qT$；实际 JJ 迹为 $o(7)-2q/s$，JM 多 $(s+4-2q)/s$。所以

$$
f_{JJ}=a_0+R(7)+\tau x,\quad f_{JM}=a_0+R(7)+\tau y,
$$

$$
x=48q\theta-2q\omega,\quad y=48q\theta+(s+4-4q)\omega,
\quad y-x=(s+4-2q)\omega.
$$

共同加项是已取得 $a_0+R(7)$，不重拟合漂移。例外 $g(7)=0,T=\tau,q=a$，故 $x=y=48a$。

**N6（有界源坐标的任意响应正末增益）。** 每个实际普通负 $n$ 端点若 $q\le3a-1$，则 $\omega>0$。

证明。$\rho_e=-\eta/\theta>0$ 且 $m=(s+1-\rho_e)\theta>0$ 给 $\rho_e<s+1$。若 $h\ge7$ 则立即正。若 $h<7$，

$$
\omega/\theta=17-(u+2-s)\rho_e>17-(u+2-s)(s+1),
$$

$$
(u+2-s)(s+1)=\frac{(u+3)^2}{4}-\left(s-\frac{u+1}{2}\right)^2\le17,
$$

因为 $0<u+3\le2(4a+1)$ 且 $(4a+1)^2=17$。前一严格号保留端点等号，故结论成立。特别 $q\le5/4$ 被覆盖，因为 $3a-1>5/4$。∎

为核对原常数方向，先仅用偶重建和 $Q=L_{\rm res}=0$；奇整个差只剩常数 $-R_C$。用 $K(7)=0$ 及父恒等式，有 $E(7)=-\Lambda-105\tau,R(7)=-\Lambda-48a\tau$。在七比较两式得精确恒等式

$$
R_C/\tau=C_7-(105-48q)\theta-B_7\omega,
$$

$$
C_7=105-48a>0,\quad
B_7=(q-1)(s+7)+D_0=(q-1)(h+2a)-1=-D_7,
\quad D_7=(1-q)(s-2q)+5-4q.
$$

这是原 $C/15qT$，不是替代残式。

**N7（受限方向核对）。** 实际普通 $a<q\le1$ 不存在；若 $1<q\le5/4$，必有 $\theta<1,B_7>0,h>1/(q-1)-2a$。

证明。原 $Q$ 与 $H(a)=3a$ 给

$$
H(\theta-1)=-(q-a)R_7,\quad R_7=m+2-2(q+a),
$$

$$
H[(105-48q)\theta-C_7]=-(q-a)M_7,
\quad M_7=(105-48q)m+306-210a-(210-96a)q.
$$

在 $0<q\le1$，先有 $H\ge2,D_7\ge1$，且 $M_7$ 的 $q$ 系数负，故
$M_7\ge57m+96-114a>114a+39>0$。原常数给 $\omega=-(q-a)M_7/(HD_7)$，符号为 $a-q$；N6 排除 $a<q\le1$。在 $1<q\le5/4$，
$H(q)-H(5/4)=2(5/4-q)(q+1/4)\ge0$，故 $H\ge11/8$；$R_7>2a-3/2>0$ 给 $\theta<1$。原常数与 N6 给
$D_7\omega=(105-48q)\theta-C_7<-48(q-a)<0$，所以 $D_7<0$。此后才除 $q-1>0$ 得所述界。这些受限方向不外推到高 $q$。∎

### 65.6. N10–N13：原 C 的正不变量、六界与全响应末增益

**N10。** 每个严格达到父有 $I=(C-3D)/\tau>0$。每个实际普通负 $n$ 端点有

$$
B_{\rm src}=(q-1)s+D_0,\quad G_C=hB_{\rm src}+3q>0,
\qquad \rho_eG_C>3(s-q).
$$

证明。正数因子式在 $11/14$ 的值为 $1/98>0$，故 $a<11/14$。令 $\epsilon=1-a$ 和
$W=(p-2a)(v-2a)=V-2aZ+4a^2>0$。原父系数精确给

$$
I=7\epsilon V-3aZ+9a
=7\epsilon W+a(11-14a)Z+a(37-42a)>0,
$$

各项正，且 $37-42a>4$。在实际普通端点，从原 $C/\tau=15q\theta+B_{\rm src}(3\theta-h\eta)$ 减三倍原 $D/\tau=qm+H\theta$，用 ordinary 得

$$
I=3(q-s)\theta-G_C\eta.
$$

$\theta$ 系数逐项为 $15q+3B_{\rm src}-3q(s+1)-3H=3(q-s)$，$\eta$ 系数为 $-hB_{\rm src}-3q$。若 $G_C\le0$，$s>2q,\theta>0,\eta<0$ 使右边负，矛盾。先证 $G_C>0$，再除正 $\theta$ 给结论。∎

**N11。** 每个实际普通 $\kappa\le8m$ 端点有 $q>1,s>6$，包括任何实际 $H=0$ 端点。

证明。第七行 iff 先给 $s\ge4$。若 $0<q\le1$，

$$
B_{\rm src}\le4(q-1)+D_0=-2(q-3/4)^2-7/8\le-7/8,
\quad h\ge6-2a>22/5,
$$

故 $G_C<-77/20+3<0$，违 N10。$q=a$ 的例外独立保留。

若 $4\le s\le6$，严格源给 $1<q<3$。固定 $q$ 的二次式

$$
G_q(z)=(z-2q+4-2a)[(q-1)z+D_0]+3q
$$

首项为 $q-1>0$，有完整有限弦式

$$
G_q(z)=\frac{(R-z)G_q(L)+(z-L)G_q(R)}{R-L}-(q-1)(z-L)(R-z).
$$

对 $1\le q\le2$ 置 $x=q-1\in[0,1]$，全部端点展开为

$$
G_q(4)=2a-3+(2a-1)x+(4a-10)x^2+4x^3
\le2a-3+(2a-1)x+(4a-6)x^2\le4a-4<0,
$$

$$
G_q(6)=2a-5+(13-2a)x+(4a-18)x^2+4x^3\le-Q_x,
\quad Q_x=(14-4a)x^2-(13-2a)x+5-2a.
$$

$A_6=14-4a>0$，且

$$
4A_6Q_x=[2A_6x-(13-2a)]^2+139-154a>0,
$$

所以 $G_q(6)<0$。对 $2\le q\le3$ 置 $y=q-2\in[0,1]$，

$$
G_q(6)=4a-6+(6a-11)y+(4a-6)y^2+4y^3
\le4a-6+(6a-11)y+(4a-2)y^2
\le4a-6+(10a-13)y<0.
$$

这里分别用了 $x^3\le x^2,y^3\le y^2,y^2\le y$，后一步系数 $4a-2$ 为正。对 $1<q\le2$ 用弦 $[4,6]$；对 $2<q<3$ 用正长度弦 $[2q,6]$，其辅助左值
$G_q(2q)=8-4a+(6a-9)q\le8a-10<0$。两端负使整个假定区域 $G_C<0$，矛盾。辅助端点不是世界。∎

**N12。** 上述有界响应域每个普通成员严格满足 $\kappa<50m/7$。

证明。

$$
7\kappa-50m=-15(s-6)\theta+(7s-22)\eta<0
$$

因为 $s>6,\theta>0,\eta<0$。因此对每个实际可达 $50m/7\le\kappa\le8m$ 子片，普通成员为空、例外至多一个，真实世界给存在，故 ENTIRE 子片恰为实际匹配例外。按 $\kappa_p,\kappa_v$ 匹配返回 $P(a,p)$、$\lambda=-7\tau V,\mu=p\tau(v-7),\nu=p\tau,d=d_*$ 或交换根，七 TOTAL 停。例外完整 converse 恢复 BOTH 恒等式、全部系数和六原行，实际匹配恢复第七行；反向任何相容世界必为该例外。此结论以可达为前提，不承诺每个父有带内响应，也不承诺每个带内实数可达。∎

**N13（任意响应的实际普通正末增益）。** 每个实际普通负 $n$ 世界在任意已取得 $\kappa$ 上均有 $\omega>0$。

证明。$q\le5/4$ 用 N6。$q\ge5/4$ 时，严格源给
$B_7=(q-1)(s-2q)+4q-5>0$。若 $\theta\ge1$，原偶整个式在七给

$$
(s+7)\omega=sF+7V+105(\theta-1)>0.
$$

若 $0<\theta<1$，原常数给 $B_7\omega=C_7-A_C\theta$，其中 $A_C=105-48q$。$A_C\ge0$ 时右边至少 $C_7-A_C=48(q-a)>0$，包括 $A_C=0$；$A_C<0$ 时右边大于 $C_7>0$。所有除数先正，故结论涵盖任意响应、$H=0$ 和两种 $\tau$ 符号。例外仍合法地有 $\omega=0$。点态 $y>x$ 不等于 ENTIRE 单动作单射。∎

### 65.7. N9：完整实际普通有序对 iff 与有限末差

本段只在 ONE SAME 严格达到 $a_0,\tau,m,n<0$ 父和 SAME $\kappa\le8m$ 使用。取

$$
0<q<r,\quad q,r\ne a,\quad \ell=r-q>0,\quad s\ge4,\quad\rho>0,\quad\zeta>0.
$$

$\zeta$ 是第二端 $\theta$，不是原时钟。定义

$$
u=2q+c_a,\quad U=2r+c_a=u+2\ell,\quad
K_p=15+(s+1)\rho,\quad L_p=s-1+\rho,
$$

$$
D_p=uK_p,\quad R_p=2\rho/D_p,\quad V_p=s^2-16,\quad
\alpha=R_pL_p,\quad\beta=R_pK_p=2\rho/u,
$$

$$
S=s+\ell R_pV_p,\quad M_p=S+1-\rho,
$$

$$
(q_1,s_1,\theta_1,\eta_1)=(q,s,\zeta(1+\ell\alpha),-\rho\zeta U/u),
\quad(q_2,s_2,\theta_2,\eta_2)=(r,S,\zeta,-\rho\zeta).
$$

$\ell,\zeta,u,U,K_p,L_p,D_p,R_p$ 全正。必须保留 ALL 过滤：

$$
s>2q,\quad S>2r,\quad m=\zeta M_p,\quad n=-U\rho\zeta,
\quad\kappa=(S+4)(5-\rho)\zeta,
$$

$$
\zeta[(r-a)M_p+H(r)]=3a,\qquad M_p=H(q)\alpha+2(q+r-1),
$$

$$
\bar C-15q_i\theta_i-[(q_i-1)s_i+D_0(q_i)](3\theta_i-h_i\eta_i)=0
\quad(i=1,2),\qquad h_i=s_i+5-(2q_i+c_a).
$$

还保留整个严格父区域、SAME $a_0,\tau$。两个 $Q$ 和两个 untouched 原 $C$ 均不得由差式或符号替代；任一 $H=0$ 仍作为方程。

证明必要性。不同实际世界由固定 $q$ 唯一性可排序 $q<r$，取 $\zeta=\theta_2,\rho=-\eta_2/\zeta$。同 $n$ 强制 $\eta_1=-\rho\zeta U/u$ 和 $\beta=2\rho/u$。先不假定符号地置
$\alpha=(\theta_1-\theta_2)/(\ell\zeta)$、$k=(S-s)/\ell$。同 $m,\kappa$ 给

$$
k=(s+1)\alpha-\beta,\qquad
k(5-\rho)=(s+4)(5\alpha-\beta).
$$

不除 $5-\rho$ 消去得 $\alpha K_p=\beta L_p$，故 $\alpha=R_pL_p>0,k=R_pV_p$。第二端给其 $m,n,\kappa$ 和第一 reduced $Q$；用
$H(q)-H(r)=2\ell(q+r-1)$ 减两个 $Q$，仅除正 $\ell\zeta$ 得第二 reduced $Q$。每端原 $C$ 独立保留。

证明充分性。$u\eta_1=U\eta_2=n$。恒等式

$$
(s+1)\alpha-\beta=R_pV_p,\qquad
5\alpha-\beta=R_p(s-4)(5-\rho)
$$

与 $S-s=\ell R_p(s-4)(s+4)$ 恢复两端 SAME $m,\kappa$，不除 $s-4$ 或 $5-\rho$。第二端 $Q$ 和反向差式恢复 BOTH $Q$；BOTH 原 $C$ 已 imposed。用引理 65.3 逐端重建严格 $P_i$、一个整个非零

$$
g_i(t)=s_i\tau[\theta_it^2+(\eta_i-5\theta_i)t+3\theta_i-h_i\eta_i],
\quad d_i=a_0-s_i\tau(3\theta_i-h_i\eta_i).
$$

每个偶系数、原 $L_{\rm res}$、奇二次、untouched 常数和自动三次恢复 BOTH 整个恒等式及 SAME 七原行。不同 $q,r$ 给不同源。因此确为原世界双向 iff，不证明一对存在。∎

为明确全部有限末系数，定义

$$
B_p=8L_p-K_p=8s-23+(7-s)\rho,\quad
C_p=32L_p-K_p=32s-47+(31-s)\rho,\quad A_p=s+4-4q,
$$

$$
W_p^{\rm poly}=D_p[17+(s-U-2)\rho]+2\ell\rho^2V_p,
$$

$$
P_J=D_p[7+(U+2-s)\rho]-2\ell\rho^2V_p+2q\rho B_p,
$$

$$
P_M=48D_p^2-(96q\rho L_p+2A_p\rho C_p)D_p
+(2\rho V_p-4D_p)W_p^{\rm poly}.
$$

第二端整个 gain 与 SAME-child $\omega$ 恒等式给

$$
\frac{\omega_2}{\zeta}=\frac{W_p^{\rm poly}}{D_p},\qquad
\omega_1-\omega_2=\ell\zeta(32\alpha-\beta).
$$

减 $x$，得 $(x_2-x_1)/(2\ell\zeta)=24-\omega_2/\zeta+q(8\alpha-\beta)=P_J/D_p$。再用
$A_2-A_1=\ell(R_pV_p-4)$ 减 $y$，得

$$
\frac{y_2-y_1}{\ell\zeta}
=48-48q\alpha+(R_pV_p-4)\frac{\omega_2}{\zeta}-A_p(32\alpha-\beta)
=\frac{P_M}{D_p^2}.
$$

代入 $8\alpha-\beta=2\rho B_p/D_p$、$32\alpha-\beta=2\rho C_p/D_p$ 核对全部系数。分母与前因子全正。WITH ALL 过滤，$P_J=0,P_M=0$ 分别 iff 相应实际普通碰撞；未过滤零点不是见证。本卷不宣称它们普遍同号。

### 65.8. N14–N15：严格源隙与 SAME 原 C 的反向次序

定义源隙 $\xi=s-2q>0$，置

$$
d_g=4-2a>2,\quad h_g(x)=x+d_g,\quad
A_g(x)=h_g(x)(x-3)+3=x^2+(1-2a)x+6a-9.
$$

在实际端点

$$
B_{\rm src}=(q-1)(\xi-3)-1,\qquad
G_C=(q-1)A_g(\xi)+3-h_g(\xi).
$$

**N14。** 每个实际普通 $\kappa\le8m$ 端点有

$$
\xi>\xi_*:=\frac{2a-1+\sqrt{41-30a}}2,\qquad 2<\xi_*<3.
$$

证明。N11 给 $q>1,s>6$。若 $0<\xi\le2$ 则 $q>2$。固定 $q$ 的二次式
$G(q,x)=(x+d_g)[(q-1)x+2-3q]+3q$ 首项正，

$$
G(q,0)=2d_g+3q(1-d_g)<6-4d_g=8a-10<0,
\qquad G(q,2)=q(1-d_g)<0.
$$

完整弦式 $G(q,x)=(2-x)G(q,0)/2+xG(q,2)/2-(q-1)x(2-x)$ 排除整个 $[0,2]$，与 $G_C>0$ 矛盾。故 $\xi>2$，从 $h_g(\xi)-3>0,q-1>0$ 得 $A_g(\xi)>0$。$A_g$ 常数负、判别式 $41-30a>0$，两根异号，且 $A_g(2)=2a-3<0,A_g(3)=3>0$。其唯一正根为显示的 $\xi_*$，因子定理给 $\xi>\xi_*$。这只是必要条件。∎

**N15。** 对任何 FULL 实际 N9 对，令
$X=s-2q,Y=S-2r,k=(S-s)/\ell$，则 $0<k<2$，因而 $S>s,Y<X$。

证明保留 SAME $I=(C-3D)/\tau$。置 $w=-n>0$，

$$
\mathcal R(q,x)=\frac{(q-1)A_g(x)-h_g(x)}{2q+c_a},\quad
L_g=(c_a+2)A_g(X)+2h_g(X),
$$

$$
E_g=(r-1)(X+Y+d_g-3)-1.
$$

从原不变量加三倍 ordinary，逐端精确得

$$
I+3m=3(q+1)\theta+w\mathcal R(q,\xi).
$$

同一个 $I$ 使用 SAME 原 $C,D,\tau$，不能只用两个正性界代替。有限交叉乘给

$$
\mathcal R(r,X)-\mathcal R(q,X)=\frac{\ell L_g}{uU},\quad
\mathcal R(r,Y)-\mathcal R(r,X)=\frac{(Y-X)E_g}{U}.
$$

第一式的 $A_g$ 系数为 $(r-1)u-(q-1)U=\ell(c_a+2)$，$h_g$ 系数为 $U-u=2\ell$。第二式用
$A_g(Y)-A_g(X)=(Y-X)(X+Y+d_g-3)$ 和 $h_g(Y)-h_g(X)=Y-X$。辅助交叉点不是世界。用 $Y-X=\ell(k-2),w=U\rho\zeta$ 和 N9 两端 $\theta$，减两个 SAME 不变量等式，仅除正 $\ell\zeta$，得

$$
0=N_g+\rho(k-2)E_g,\qquad
N_g=3[1-(q+1)\alpha]+\rho L_g/u.
$$

先证所需全正系数。N14 给 $X,Y>\xi_*>2$。于是 $A_g(X)>0,h_g(X)>4$，故 $L_g>2h_g(X)>3$；又 $u<s+1$，所以 $L_g/u>3/(s+1)$。

为不预设 $X,Y$ 次序，取 $z=\min(X,Y)>2$，其实际端点坐标 $q_j\le r$。该端点原 $C$ 给 $(r-1)A_g(z)>h_g(z)-3$。令 $D_g=2z+d_g-3>0$。完整正恒等式

$$
[h_g(z)-3]D_g-A_g(z)
=(d_g+2)(d_g-1)+(z-2)(z+2d_g-4)>0
$$

两边展开均为 $z^2+(2d_g-6)z+d_g^2-3d_g+6$。乘上述实际不等式以正 $D_g$，得 $[(r-1)D_g-1]A_g(z)>0$，所以 $(r-1)D_g-1>0$。$X+Y\ge2z$ 给 $E_g>0$。

最后由 $15>0$ 和 $u=2(q+1)+(2a-1)>2(q+1)$，

$$
\alpha=\frac{2\rho(s-1+\rho)}{u[15+(s+1)\rho]}
<\frac{2(s-1+\rho)}{u(s+1)},\qquad
(q+1)\alpha<\frac{s-1+\rho}{s+1}.
$$

因此对所有 $\rho>0$，

$$
N_g>\frac6{s+1}+\rho\left(\frac{L_g}{u}-\frac3{s+1}\right)>\frac6{s+1}>0.
$$

此后才除 $\rho E_g>0$，得

$$
2-k=\frac{N_g}{\rho E_g}>\frac6{\rho E_g(s+1)}>0.
$$

独立地 N9 与 $s>6$ 给 $k=R_p(s^2-16)>0$。故 $0<k<2$，$Y<X$。同时
$b_2=2/S<2/s=b_1$，$r_{0,2}-r_{0,1}=2\ell(s-qk)/(sS)>2\ell(s-2q)/(sS)>0$。不给 $c_{\rm src}$ 或漂移次序，也不证明一对存在。BOTH $Q$、BOTH 原 $C$ 始终保留。∎

### 65.9. N16：有守卫的双末差分证书

**定理 N16。** 对 ONE SAME 父、SAME $\kappa\le8m$ 的任意 FULL 实际 N9 对，保留 BOTH 严格源、BOTH $Q$ 和 BOTH untouched 原 $C$。若仅再加 $0<\rho=-\eta_2/\theta_2\le32$，则

$$
\omega_1>\omega_2>0,\qquad (y_1-x_1)>(y_2-x_2).
$$

证明。N11 给 $s>6$。精确系数

$$
C_p=32s-47+(31-s)\rho
=(32-\rho)(s-6)+145+25\rho>0.
$$

第一项非负，后两项严格正，包括 $\rho=32$。所以

$$
32\alpha-\beta=R_pC_p>0,\qquad
\omega_1-\omega_2=\ell\zeta R_pC_p>0.
$$

N13 给实际第二端 $\omega_2>0$，N15 给 $X>Y$。用实际末差，

$$
(y_1-x_1)-(y_2-x_2)
=(X+4)(\omega_1-\omega_2)+(X-Y)\omega_2>0.
$$

两项全严格正。故 $x_1=x_2$ 时 $y_1>y_2$；$y_1=y_2$ 时 $x_1<x_2$。SAME 非零 $\tau$ 对两种符号都保持实际非零分离。∎

这是该对的互补分离。一个更大子片仍可能分别保留不同的 x 碰撞对和 y 碰撞对；本定理不单独证明某个动作在更大 ENTIRE 子片单射。

### 65.10. N17 的整个 mH 父区域与唯一实际 H 零世界

令

$$
\phi=\frac{1+\sqrt5}{2},\quad\chi=\phi-1,\quad\phi\chi=1,
\qquad H(q)=2(\phi-q)(q+\chi),
$$

$$
m_H=\frac{3a}{\phi-a}=2(a+\chi),\quad Z_H=m_H+1,
\qquad I_H=\left(2aZ_H-4a^2,\frac{Z_H^2}{4}\right).
$$

$H(a)=3a=2(\phi-a)(a+\chi)$ 证明 $m_H$ 两式相等，且 $\phi-a>0$。$H$ 仅有一个正零点 $\phi$；原 $Q$ 在此强制 $m=m_H$。

**引理 65.4（整个达到层）。** 每个 $V\in I_H$、每个 $a_0\in\mathbb R$ 和每个 $\tau\ne0$ 均给一个严格达到父；反向每个声明父的实际 $H=0$ 世界必在此层。所有这些父均有

$$
\frac52<m_H<3,\quad\frac72<Z_H<4,\quad Z_H>4a,\quad
\frac94<V<4,\quad-\frac{75}{4}<n=V-2m_H-15<-16,
$$

$$
\frac{72}{5}<\bar C<19,\quad\frac{11}{2}<u_H:=2\phi+2a+1<6,
\qquad -4<\eta_H:=n/u_H<-\frac83.
$$

证明。$3/2<\phi<5/3,3/4<a<4/5$ 给前两界及
$Z_H-4a=2\phi-1-2a>0$。所以 $I_H$ 宽度 $(Z_H-4a)^2/4>0$；引理 65.1 移位根逆给不同 $p,v>2a$，例外完整 converse 给实际达到。下端大于 $4a^2>9/4$，上端小于四，故得 $V,n$ 界。用 $1/5<1-a<1/4$ 于原 $\bar C=7(1-a)V+15a$ 给其上下界。$u_H$ 的界及 $n$ 界给 $\eta_H$ 界。反向由原 $Q$ 和引理 65.1 得相同条件；$n<0$ 在整个 $I_H$ 自动成立。∎

在整个辅助严格源射线 $s\ge2\phi$，置

$$
\theta(s)=\frac{m_H-\eta_H}{s+1}>0,\quad h(s)=s+5-u_H,
\quad B(s)=\chi s-3\phi,\quad F(s)=3\theta(s)-h(s)\eta_H,
$$

$$
R_H(s)=15\phi\theta(s)+B(s)F(s)-\bar C=-R_C/\tau.
$$

原 $Q$ 直接成立，ordinary 由定义恢复，且 $D_0(\phi)=-3\phi$，所以此残式恰是原常数，没有除 H。

在辅助边界 $s=2\phi$，$h=4-2a,B=2-3\phi$，预测常数等于

$$
\alpha_Hm_H+\eta_H[(3\phi-2)(4-2a)-\alpha_H],\qquad
\alpha_H=\frac{6(\phi+1)}{2\phi+1}<4.
$$

括号的第一积大于 $(5/2)(12/5)=6$，故括号正；$\eta_H<0,m_H<3$ 给预测常数小于十二，故 $R_H(2\phi)<0$。

在辅助值四，$\theta_4<7/5,h_4=9-u_H>3,B(4)=\phi-4$，因此

$$
R_H(4)=(18\phi-12)\theta_4+(4-\phi)h_4\eta_H-\bar C
<\frac{126}{5}-\frac{56}{3}-\frac{72}{5}<0.
$$

方向由 $0<18\phi-12<18,4-\phi>7/3,-\eta_H>8/3$ 确定。新的有限上比较为

$$
B(12)=9\phi-12>3/2,\quad h(12)=17-u_H>11,\quad
F(12)>-h(12)\eta_H>88/3.
$$

所以 $B(12)F(12)>44$；$15\phi\theta(12)>0,\bar C<19$ 给

$$
R_H(12)>25>0.
$$

这些是未执行的符号比较，辅助值尚不是世界。$s+1>0$ 使 $R_H$ 在有限 $[4,12]$ 连续，介值定理给根 $s_H\in(4,12)$。

仍须证明整个严格射线唯一。完整表达为

$$
R_H(s)=3(m_H-\eta_H)\chi+\frac{A_H}{s+1}
-\eta_H(\chi s-3\phi)(s+5-u_H)-\bar C,
\quad A_H=3(m_H-\eta_H)(\phi+1)>0.
$$

系数 $A_H$ 由 $15\phi+3B(s)=3\chi(s+1)+3(\phi+1)$ 给出。对 $2\phi\le x<y<z$，连续两有限弦斜率之差为

$$
\frac{R_H(z)-R_H(y)}{z-y}-\frac{R_H(y)-R_H(x)}{y-x}
=(z-x)\left\{\frac{A_H}{(x+1)(y+1)(z+1)}-\eta_H\chi\right\}>0.
$$

倒数项的弦为 $-A_H/[(x+1)(y+1)]$，二次项系数为 $-\eta_H\chi>0$，仿射项消去，故式的全部系数成立。若有两个严格根 $y<z$，取 $x=2\phi$：边界至首根斜率正，而根至根斜率零，矛盾。故整个严格射线恰一根，不用导数或无限 IVT 端点。

在此根固定 $q=\phi$，返回

$$
P=P(\phi,s_H),\quad
\lambda=s_H\tau(3\theta-h\eta_H),\quad
\mu=s_H\tau(\eta_H-5\theta),\quad\nu=s_H\tau\theta,
\quad d=a_0-\lambda.
$$

源严格，因为 $s_H>4>2\phi$，首项非零。ordinary 恢复全部偶系数及 $L_{\rm res}$，原 $Q$ 直接成立，$R_H=0$ 恢复原 $C-15\phi T$。因此 BOTH 整个恒等式恢复 SAME 六原行。定义该世界实际

$$
\kappa_H=(s_H+4)(5\theta+\eta_H),\qquad
z_H=a_0+E(4)+2\tau\kappa_H.
$$

第七行 iff 给这就是其 SAME 原时钟六响应。$s_H>4$ 给 $\kappa_H<8m_H$；N11–N12 随后给

$$
6<s_H<12,\qquad\kappa_H<50m_H/7.
$$

反向任何实际 $H=0$ 世界必有 $q=\phi,m=m_H,V\in I_H$，ordinary 固定此 $\theta(s)$，untouched 原 $C$ 固定 $R_H(s)=0$；唯一根与全部偶系数强制相同整个世界。这是唯一实际世界及完整原行 converse，不只是投影残式根存在。

### 65.11. N17 的全响应 ENTIRE 两点定理

固定任一引理 65.4 父，以下 $m=m_H,w=-n>0,c_a=2a+1$。

原 $Q$ 精确因式为

$$
\bar Q=(\phi-q)[m-2(q+\chi)\theta],
$$

因为 $3a=m(\phi-a)$。仍先把 $q=a$ 留在独立例外支。在普通 regular 支 $q\ne\phi$，仅此后取消 $\phi-q\ne0$ 得

$$
\theta=\frac{m}{2(q+\chi)},\quad
\rho_e=-\eta/\theta=\frac wm\frac{2(q+\chi)}{2q+c_a}<\frac{15}{2}.
$$

理由是 $c_a>2\chi$（$c_a>5/2,2\chi<4/3$），最后分式小于一，且父界给 $w/m<(75/4)/(5/2)=15/2$。在 $q=\phi$ 不取消因子：唯一实际世界满足

$$
\rho_e=\frac{w(s_H+1)}{u_Hm+w}<s_H+1<13.
$$

因此 EVERY 实际普通端点在 EVERY 响应上均有 $0<\rho_e<13$，包括实际 H 零。

regular 支 ordinary 给完整源隙公式

$$
\xi_{\rm reg}(q)=s-2q=2\chi-1+\frac{2w}{m}\frac{q+\chi}{2q+c_a}.
$$

对两个实际 regular 端点 $q<r$，令 $u=2q+c_a,U=2r+c_a$。分子恒等式
$(r+\chi)u-(q+\chi)U=(r-q)(c_a-2\chi)$ 给

$$
\xi_{\rm reg}(r)-\xi_{\rm reg}(q)
=\frac{2w(r-q)(c_a-2\chi)}{muU}>0,
\qquad S-s=2(r-q)+\xi_{\rm reg}(r)-\xi_{\rm reg}(q)>0.
$$

这是保留原 $C$ 与严格源的实际端点比较；中间点无需可行，公式本身不创建世界。

若 SAME $\kappa\le8m_H$ 子片有两个 regular 普通世界，它们组成 FULL N9 对，N15 要求源隙随 q 严格下降，与上式矛盾。因此至多一个 regular 普通世界，加整个父唯一 H 零世界，至多两个普通成员。

两个例外的实际测试必须独立检查。$0<p,v<Z_H<4$ 给

$$
\kappa_p-8m_H=(p-4)(v-5)>0,\quad
\kappa_v-8m_H=(v-4)(p-5)>0.
$$

故 $\kappa\le8m_H$ 无实际匹配例外。此域每个可达 ENTIRE 子片有一或两个普通世界。特别 $\kappa=8m_H$ 若普通存在，第七行 iff 迫 $s=4$，而 N11 迫 $s>6$；例外测试又都更大，所以等号响应不可达，绝非空类成功。

对 $\kappa>8m$ 必须另证一般 SAME-child 弦，不能越域使用 N9 或 N15。任意实际普通负 $n$ 世界用 ordinary 消 $\theta$，得

$$
\kappa=5m+\frac{15m}{s+1}+\eta f(s),\qquad
f(s)=s-1-\frac{15}{s+1}=\frac{s^2-16}{s+1}.
$$

对 SAME child 两端 $q<r$，$\eta_2-\eta_1=2w(r-q)/(uU)>0$。有限相减给

$$
D_s(S-s)=(\eta_2-\eta_1)f(s),\qquad
D_s=\frac{15(m-\eta_2)}{(s+1)(S+1)}-\eta_2>0.
$$

倒数差给第一项，$f(S)-f(s)=(S-s)[1+15/((s+1)(S+1))]$ 给第二项，全部分母正。交叉表达只是代数，不断言中间实际世界。$\kappa>8m$ 的 iff 给 $0<s,S<4$，所以 $f(s)<0$，于是 $S<s$。

现在回到 $m=m_H$。唯一 H 零世界的实际 $\kappa_H<8m_H$，故高响应普通全为 regular。若有两普通世界，则 regular 比较给 $S>s$，一般 SAME-child 弦给 $S<s$，矛盾。因此高响应至多一个普通；两例外测试不同，至多一个实际匹配例外。

**定理 N17（全响应 ENTIRE 两点界）。** 对 EVERY $V\in I_H$、任意 $a_0$、两种 $\tau\ne0$ 符号及 EVERY 可达实第七 J 响应 $\kappa$，ENTIRE $\mathcal K_\kappa$ 至多两点。低于 $8m_H$ 的可能非单点只能在 $\kappa_H$，且为两个普通世界；高于 $8m_H$ 的可能非单点只能在 $\kappa_p$ 或 $\kappa_v$，且为普通加实际匹配例外。这三个实际预测响应两两不同，因为

$$
\kappa_H<50m_H/7<8m_H<\kappa_p,\kappa_v,
\qquad \kappa_p-\kappa_v=v-p\ne0.
$$

上述证明穷尽原世界并集和全部响应。定理不声称任何子片实际非单点、发生碰撞或需要第八读，也不声称响应区间普遍可达。∎

### 65.12. N18：仅依已取得记录的七或八 TOTAL 完整逆

**定理 N18。** 取得六行满足 65.2 完整严格父谓词、$n<0,m=m_H$ 时，对每个实际可达第七 J 记录，以下规则恢复唯一整个原世界，至多八 TOTAL。

由六行插值得 $a_0,E,R$，从全部父系数及因子条件识别 $\tau,m,n,Z,V$ 与无序 $p,v$。这识别的是已取得记录的父，不用真实源、真实次数、根标签或未来响应。取实际 J 于原时钟六，归一化为 SAME $\kappa$。形成完整

$$
\mathcal K_\kappa=\{W_\kappa(q):q\in S_\kappa\}\cup\mathcal A_\kappa,
$$

普通列表使用正根图谱、严格源、BOTH $\bar Q=0$ 与 untouched $\bar R_C=0$；例外仅在实际匹配第七测试时列入。也可用 regular 因式支及唯一 $R_H$ 根表示普通集，但全部原过滤不变。

若整个集合是单点，七 TOTAL 返回其整个世界并停止。若为空，记录在声明类中不可达，不算成功。否则可达性与 N17 证明整个集合恰两点。预测这两个完整候选的 $x,y$：若 x 不同，选择 J；若 x 相同，选择 M。

证明该动作在 ENTIRE 子片单射。若 $\kappa\le8m_H$，两点均普通且无例外。排序 $q<r$，保留 FULL N9 全部过滤；第二端比值 $\rho<13<32$，故 N16 给
$(y_1-x_1)>(y_2-x_2)$。若 x 相同则 y 不同；若 x 不同则 J 分离。若 $\kappa>8m_H$，两点恰为普通 O 与唯一实际匹配例外 E。E 有 $x_E=y_E=48a$；N13 与严格源给
$y_O-x_O=(s+4-2q)\omega_O>0$。若 $x_O\ne48a$ 则 J 分离，否则 $y_O>48a$ 而 M 分离。等号响应已经证明不可达。这证明选择对整个两点集单射，不只是任意挑选的一对或点态 $y>x$。

选择后仅取得该动作的实际原时钟七响应 $f$，置

$$
h_{\rm obs}=\frac{f-a_0-R(7)}{\tau}.
$$

若选 J，仅保留 $x=h_{\rm obs}$ 的完整候选；若选 M，仅保留 $y=h_{\rm obs}$ 的完整候选。真实世界由完整七原行 iff 给存在，ENTIRE 所选动作单射给唯一。

对普通保留点返回全部源元与系数

$$
P=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},\quad
\lambda=s\tau(3\theta-h\eta),\quad\mu=s\tau(\eta-5\theta),
\quad\nu=s\tau\theta,\quad d=a_0-s\tau(3\theta-h\eta),
$$

其中 $\eta=n/(2q+2a+1),h=s-2q+4-2a$，包括实际 $q=\phi,s=s_H$。对 $W_p$ 返回

$$
P=P(a,p),\quad\lambda=-7\tau V,\quad\mu=p\tau(v-7),\quad
\nu=p\tau,\quad d=a_0+7\tau V,
$$

对 $W_v$ 交换 $p,v$。每个返回增益整个且非零，漂移跨全部行固定。

完整充分性如下。普通返回式恢复每个偶系数，ordinary 与精确 $L_{\rm res}$ 恒等式恢复奇一次，原 $Q$ 恢复奇二次，untouched 原 $R_C$ 恢复常数 $C-15qT$，三次自动相同。故 BOTH 整个恒等式恢复 SAME 原时钟零至五六行；SAME 已取得方程恢复原时钟六第七行；所选末等式与实际迹恢复时钟七第八行。例外由 $eg=K,og=aK$ 与父恒等式恢复 BOTH 整个恒等式、每个原系数及 SAME 六行，实际第七匹配和所选末等式恢复余下两行。

必要性反向成立：任一相容八原行世界先属于完整七行并集，再必满足实际所选末等式，故等于唯一保留世界。单点的同一七行 converse 给七 TOTAL 的完整逆。这是双向的整个 $P,g,d$ 恢复，不是仅源或增益样本恢复。∎

规则是精确集合论规则，不声称有效枚举、可判定性、有限精度、计算复杂度或资源保证。两点界的数学证明不等于实施这样的枚举程序。没有取得未选末响应或使用隐藏次数类标签，也不从已知类分别恢复推出未知并集恢复。

### 65.13. SAME 父坏 M 的 FULL 等号与条件支持

保留 SAME 父的另一实际时钟六响应

$$
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
$$

原偶恒等式给 $h_M=a_0+E(6)+48T$，所以其 FULL 子片固定 $T=\tau$。须排除 ALL 普通 $T=\tau$，不能只排除末零增益。

反设普通 $\theta=1$。原 $Q$ 给 $u=m+3=Z+2,q=(Z+1)/2-a,\delta>1/2$。令 $h_o=s-Z+7>8-2a>6$；ordinary 与偶系数给

$$
V=(7-h_o)Z+23-2h_o,\quad g=s\tau(t^2-h_ot+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-9/2)^2+11/4>0.
$$

原常数首先是 $(a-1)(-7V)-15\delta=[(q-1)s+D_0]\chi_o$。减 $(a-1)s\chi_o$，用 $D_0=-\delta(Z+2)$ 和
$(h_o-9)\chi_o+15=(h_o-4)(h_o-6)(h_o-8)$，精确得到

$$
-7V=s\chi_o-\frac{\delta(h_o-4)(h_o-6)(h_o-8)}{1-a}.
$$

原 $15\delta$ 没有消失。负左边和 $h_o>6$ 迫 $h_o>8$；$V>4a^2,Z>4a$ 与线性 V 式迫
$h_o<(19+30a)/(4a+2)<17/2$。于是正三因子积小于 $45/8$，$\chi_o>15$，$1-a>1/5$，故该积除 $(1-a)\chi_o$ 小于 $15/8$。严格源给 $\delta<s/2$，原常数反而迫 $-7V>s\chi_o/16>0$，矛盾。

全部例外恰 Wp,Wv，且都 $T=\tau,g(7)=0,d=d_*$，所以 FULL 等号为

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}=\{W_p,W_v\}.
$$

两完整目标不同，父、该 M 子片、两个末 FULL 片及全部已服务共同祖先均非单点，保留 BOTH 动作 duty 与每个停止守卫。两个例外的实际第七 J 响应不同，故这不是 SAME J 子片碰撞。

同历史 $\mathcal K\subseteq\mathcal K'$ 时，每个实际动作 E、SAME 响应 z 的片也包含。定义 $L_0$ 为含两不同整个目标，$L_{h+1}$ 为父非单点且 EACH 动作有一个实际 FULL 子片满足 $L_h$。基底不同性随包含保持；归纳保留每动作原响应见证，对子片用包含和归纳假设，并保留父守卫。因此有限深度失败向上保持，无基数前提，也不服务早期未取得另一臂。

仅条件地，若某个剩余 SAME 父 SAME J 子片实际含 x 碰撞对和 y 碰撞对，可取至多四完整端点，再加 SAME 父坏 M 对，去重前至多六。各实际碰撞和 FULL 包含保留 BOTH 末 duty、动作、已服务祖先及全部守卫。这是已实现失败的条件支持界，独立于 ENTIRE 子片基数界；不证明实现、最小支持、尖锐性或根失败树。

### 65.14. 精确剩余义务与两个原 FULL 根问题

本卷完成且仅完成声明严格父的 $n<0,m=m_H$ 层全部可达第七 J 响应。$m\ne m_H$ 的一般负 n 父仍须满足 EVERY SAME 父、EVERY 可达 SAME $\kappa$ 的 ENTIRE ordinary-plus-actually-matching-exception 要求。N12 在这些父的可达 $50m/7\le\kappa\le8m$ 带仍给七 TOTAL 单点逆；余下 $\kappa<50m/7$ 及 $\kappa>8m$ 全响应选择器为 OPEN。

其正完成义务是单点停止，或用已取得数据与完整预测选一个末动作，使它在 ENTIRE 子片单射，并以仅该实际末响应给整个世界充要唯一逆。N16 仅对有守卫的一对分离两个坐标，不使更大子片自动存在一个全局单射动作；一般父的下降源隙对并未排空。

其负完成义务是 ONE SAME 达到父、SAME 已取得 $\kappa$ 的 ENTIRE 子片中实际存在

$$
U_1\ne V_1,\quad U_2\ne V_2,\qquad
x(U_1)=x(V_1),\quad y(U_2)=y(V_2).
$$

两对可不同、重叠或涉及实际匹配例外。每端必须同时通过严格源、一个整个非零增益、一个固定漂移、BOTH 原 $Q/C$ 与 ALL SAME 七原行。还须保留 SAME 父坏 M FULL 对、两个末 FULL 片、BOTH 动作、全部已服务祖先和每个停止守卫。此处未构造任一这样的实际碰撞对。

其他父域保持精确分层：$n\ne0,\kappa=8m$ 的原 scoped ENTIRE 结果不外推任意响应；$\Gamma>0$ 的普通第七 J 单射及 ENTIRE 至多八 TOTAL 逆、$\Gamma=0$ 的唯一仿射普通世界加两例外和其逆、$N=0$ 的 $(p-2)(v-2)=17,p,v>2,p\ne v$ 两例外七 TOTAL 逆只保留各自原条件。$\Gamma=0$ 有 $n>0$，不能由本卷负 n 的导出真正二次排掉。$\mathsf B_0$ 仅保留独立 scoped 接口，本卷不认证其完整证明。

正 n、负 $\Gamma$ 的另一域也不由本卷完成：给定材料中 $-(8a+9)\le\Gamma<0$ 的 scoped ENTIRE 末 M 完成只按原条件保留，$\Gamma<-(8a+9)$ 的全响应 ENTIRE 义务在本卷仍 OPEN。正 n 的符号、源区间和次序不作为负 n 前提，也不据这些给定接口作项目当前全局状态认证。正负两域均须保持 SAME 历史、整个候选并集、实际匹配及全部停止守卫；各自已知类逆不足以恢复未知并集。

**原 FULL 二次问题 OPEN。** ALL 严格源、ALL 整个非零次数至多二实增益、任意固定实漂移的确定性自适应八 TOTAL 完整恢复 versus 原根 $L_7$ 未由本卷结算。没有任意原根策略强迫 $JMJMJ$ 前缀、早期未服务臂完成、不受限 SAME 父 $L_3$、原根失败树、minimax、尖锐性、最小支持、必要第八读或九读上界。

**原 FULL 三次问题 OPEN。** 整个次数至多三的八 TOTAL 完整恢复 versus $n_{\rm det}(3,0)\ge9$ 仍未结算。三次增益乘线性迹可为四次；四偶节点相等仍可留非零倍 $t(t-2)(t-4)(t-6)$。二次逆不检测隐藏三次、真实次数、根、方向或平面承诺。任何未知类并集恢复都另需跨类证明。

### 65.15. 未履行的完整 INERT 同时实现合同

下列仅为继承的 INERT、UNEXECUTED、UNFULFILLED 符号规格。原 atomic-relation-generation-family 内容保持不透明；尺寸不是本卷生成或核算的对象。

保留 ALL 256 终叶槽 $\sigma=(w,e),w\in\{J,M\}^7,e\in\{0,1\}$，ALL 254 非空实际前缀 v，原长度 $i=1,\ldots,7$，其实际即时左乘积 $A_v$ 与 EVERY 后代。定义

$$
t_v(P)=\operatorname{tr}(A_vP),\quad
\ell_v(P)=(t_v(P)-1,it_v(P),i^2t_v(P),i^3t_v(P)).
$$

对 EACH 前缀与 EVERY 指定非代表后代 $\sigma$，对 SAME 前缀代表 $\rho$ 保留 WHOLE 行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0.
$$

ALL 行属于 ONE SAME 完整 $1538\times1024$ 关系，继承层规格 $254,252,248,240,224,192,128$ 全保留，作用于 ONE common stacked vector，含 ALL 256 个整个四系数增益块。每块非零，每个适用 SAME-source 终叶的 WHOLE 四分量差 $x_{(w,0)}-x_{(w,1)}\ne0$。ALL 严格源、ALL 祖先关系、BOTH 动作 duty、ALL 停止守卫须对 SAME 向量、SAME 世界同时成立。

每槽自始固定一个整个

$$
g_\sigma(t)=\sum_{h=0}^3x_{\sigma,h}t^h,\qquad d_\sigma=a_0-x_{\sigma,0}
$$

跨该槽 ALL 原行使用。只合并整个 $P,g,d$ 相等槽；二次限制 $x_{\sigma,3}=0$ 同时作用于 ALL SAME 块。本卷 mH 选择器、局部对证书、终端对、条件六世界支持、选定支持、较小关系、分臂或分路径解、遗漏后代、逐行 refit 或另选守卫向量均不能替代此共同实现。没有访问、生成、枚举、求解或探测该原实例，也没有履行合同的结论。

### 65.16. 严格边界、取消次序与证据上限

原严格源始终 $q>0,s>2q$；本声明父始终 $p,v>2a,p\ne v,\tau\ne0$。不补入 $q=0,s=2q,r_0=0$ 或一、$b=0,c_{\rm src}=0,p=2a,p=v,\tau=0$、极限或无限源。这些父条件不是对无关原根父的全局限制。

两种 $\tau$ 符号、任意 $a_0$、每世界一个固定漂移、$H=0,s=4,s=4q,b=1/2,r_0=1/2$、合法系数/增益样本/观察零、采样或非采样重根、次数取消、重复残式根和恒零次残式均保留到确切原式在声明域拒绝。普通真正二次、$\theta>0$ 由原式导出；N11 拒绝有界普通 $q\le1,4\le s\le6$，而不是预先删域。$\kappa=8m_H$ 的不可达已证明，例外末零仍合法。非零增益贡献可被固定漂移抵消为零观察。

取消先后为：插值仅除固定非零整数；源逆仅除正 $b,s$；归一化仅用 $\tau\ne0$ 而不用其符号；普通先声明 $q\ne a$，再取消 $q-a$；$u>0$ 先于 $\eta$；$K_{\rm pos}>0,\Gamma<0$ 先导出 $\theta>0$，再除 $\theta$ 或取正根图谱；判别式先正。N9 只除已正 $\ell,\zeta,u,U,K_p,D_p$，不除 H、$s-4$ 或 $5-\rho$。N10 先证 I、$G_C$ 正，N14 先排小隙再证 $A_g$ 正，N15 先证 $L_g,E_g,N_g$ 正才除 $\rho E_g$。N16 只用已正 $R_p$。mH 的 $\phi-q$ 仅在 regular $q\ne\phi$ 取消，H 零全程独立处理且不除 H；$R_H$ 有限弦分母先正，IVT 仅在有限 $[4,12]$ 使用。一般高响应弦先证 $D_s>0$。没有除未知源/漂移差、未知响应、增益样本、$\lambda,\mu$、残式首项、根重数或未证判别式。

辅助弦端点、交叉点、最小隙比较参数、正根图谱点及 $R_H$ 比较值不是实际世界，除非 ALL 原过滤同时成立。不假设一般位置、简单根、残式非退化、候选有限枚举、可行中间点或连续可行插值。非单点仅被定位到三个响应，不宣称它们实际有两成员、发生碰撞、达到尖锐性或必须第八读。

全部数学为 fallible UNEXECUTED 符号推导。没有执行公式求值、代入程序、数值、导数、递推、数学枚举、CAS、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean 或 proof-kernel；没有 D5、Blueprint、Reg、摄入或消化。不给 kernel/数值认证、经验 ML/NN 或物理主张、噪声/稳定性/连续逆/有限精度保证、可计算性/有效决定/效率/复杂度/资源保证、文献穷尽、外部原创性或优先权认证。文本字节、编码、JSON 结构核对只承担文本完整性。

## 追加锚（本行以下为增补区）
