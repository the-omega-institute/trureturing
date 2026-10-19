# FIB 二次负 n 的 mH 以下精确响应分类与严格有界源图谱

本卷独立为第 67 节。对下文声明的实际已服务 $JMJMJ$ 严格 $\beta=7$ 父，若 $n<0,4a-1<m<m_H$，则所有可达 $\kappa\ge50m/7$ 恰为两个不同的例外测试，每个 ENTIRE 子片都是一个完整例外世界，七 TOTAL 即有整个 $P,g,d$ 的充要唯一逆。每个其余可达低响应子片 ENTIRELY 只含普通世界，且全部位于严格有界区域

$$
1<q<2,\qquad 6<s<11,\qquad \frac13<\theta<1,\qquad
0<\rho=-\eta/\theta<7.
$$

普通正根图谱同时保留 BOTH 原 $Q$ 与 untouched 原 $C/15qT$ 后，连同这些冗余必要界，恰为该低响应 ENTIRE 原世界集合，包含双向完整原行 converse。上分支另有 $s<10,\rho<6$。这把未决问题局限于有界源域；普通存在、子片基数、ENTIRE 单末动作单射及实际双动作碰撞仍为 OPEN。

T1–T3 的无高响应普通世界及例外逆事实上对 $4a-1<m\le3$ 成立；N26–N28 的严格有界定位用于 $m<m_H$。与既有 $m=m_H$ 结果结合，还得到新的边界定位：该层可能非单点只在唯一实际 $H=0$ 世界的响应 $\kappa_H$；其余可达响应全为单点。既有 $m\ge m_H$ 至多八 TOTAL 选择器不计作本卷新的低层完成。

本文为 `repo-derived` 符号综合，复用插值、因子定理、次数根数、Vieta、有限弦恒等式与有限区间介值定理，不作外部原创性或优先权主张。全部数学为 fallible UNEXECUTED 符号推导，不是 Lean/kernel 或数值认证。两个原 FULL 根问题仍为 OPEN。

## 67. 精确高响应逆、低响应有界图谱与未决全称义务

### 67.1. 原完整世界、实际左动作与读数

一个完整目标自始固定为

$$
W=(P,g,d),\quad P=\begin{pmatrix}r_0&b\\c_{\rm src}&1-r_0\end{pmatrix},\quad
0<r_0<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r_0(1-r_0),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
$$

四源元严格正，迹一、行列式零；非零迹排除秩零，故秩恰一。原域允许所有低次、两种尺度符号、合法系数零、样本零、观察零、采样或非采样根与重根。每个世界跨全部行使用 SAME 一个整个增益和一个固定实漂移。不同候选的固定漂移可以不同；相等与去重只按整个三元组。

实际即时左动作及读数为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
$$

纸面恒等式

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r_0+A_{21}b+A_{12}c_{\rm src}
$$

与左 J 交换旧两行、左 M 取旧第二行和旧两行之和，给下列全部相关实际响应。记 $j=b+c_{\rm src}$；左下元乘 $b$。

| 原时钟、实际动作 | 实际响应 |
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

至时钟五的乘积依次为 $I,J,\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right),\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right),\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right),\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$；六 J 回到原时钟四的乘积，七 JJ 与 JM 分别为 $\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right),\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$。这些均为未执行的符号恒等式。

$JMJMJ$ 给原时钟零至五，共六 TOTAL；时钟六选 J 取得 $z$，七 TOTAL；至多再选一个时钟七动作，八 TOTAL。重复乘积仍用新原时钟样本。没有重置、复制、跳读、平移时钟、额外端口、隐藏源/根/次数标签、逐行 refit 或未选实际响应输入。

令 $\mathcal S(\mathcal H_5)$ 为满足取得六行的 ALL 原世界，定义 FULL 子片

$$
\mathcal K_{6,E,z}=\{W\in\mathcal S(\mathcal H_5):h_E(W)=z\}.
$$

可达恰指非空，空片不构成停止成功。

### 67.2. 父谓词、全部系数与精确达到区域

由取得行置 $a_0=y_0,v_i=y_i-a_0$，定义

$$
E(t)=Lt+At^2,\quad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{v_4-2v_2}{8},\quad L=\frac{4v_2-v_4}{4},\quad
D=\frac{v_5-2v_3+v_1}{8},\quad B=\frac{v_3-v_1-8D}{2},\quad C=v_1-B-D.
$$

这些式恢复偶节点 $0,2,4$ 与奇节点 $1,3,5$；次数至多二之差有三个不同根即恒零，故唯一。$C$ 始终是这个原奇插值常数。

令

$$
a=\frac{\sqrt{17}-1}{4},\quad 2a^2+a=2,\quad \epsilon=1-a,\quad c=2a+1,\quad d_0=4-2a,
$$

$$
\Sigma:\ B+5D=a(L+5A),\quad \tau=\frac{D-aA}{3a}\ne0,\quad
\Lambda=\frac{C-15a\tau}{a-1},
$$

$$
U_0=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5),\quad
K=\Lambda+E+\tau U_0=\tau(t+p)(t+v)(t-7),\quad p,v>2a,\quad p\ne v.
$$

这是本卷的完整严格 $\beta=7$ 父谓词。基本恒等式为 $ac=2,c^2=c+4,(4a+1)^2=17$。正数 $x$ 的
$f(x)=x^2+x/2-1=(x-a)(x+a+1/2)$，以及 $f(3/4)=-1/16,f(4/5)=1/25$ 给 $3/4<a<4/5$。

定义固定父坐标

$$
Z=p+v=m+1,\qquad V=pv=n+2m+15,\qquad n<0.
$$

$K/\tau$ 全部升幂系数是 $(-7V,V-7Z,Z-7,1)$。逐项比较并用 $\Sigma$ 得

$$
\Lambda=-7\tau V,\quad A=\tau m,\quad L=\tau(n-5m),\quad
D=a\tau(m+3),\quad B=a\tau(n-5m-15),\quad C=\tau\bar C,
$$

$$
\bar C=7\epsilon V+15a,\qquad
R=aE+a\tau(U_0-V_o)+(a-1)\Lambda.
\tag{67.1}
$$

最后整个恒等式包括常数，因为 $U_0-V_o=3t^2-15t+15$。固定 SAME 父同时固定 $a_0,\tau,m,n$ 和全部原系数；根交换只换名字。

**父区域引理。** 除 $n<0$ 外，精确达到区域是

$$
Z>4a,\qquad 2aZ-4a^2<V<Z^2/4,
$$

等价地

$$
m>4a-1,\qquad (2a-2)m+4a-19<n<\frac{m^2-6m-59}{4}.
\tag{67.2}
$$

证明。移位根 $p-2a,v-2a$ 的和与积为 $Z-4a,V-2aZ+4a^2$，均正；不同性给 $Z^2-4V>0$。反向这些严格式使移位二次式有正判别式、正和、正积，其两个不同实根只能都正。移回得不同 $p,v>2a$。用 $4a^2=4-2a$ 得展开区域。67.5 的完整例外 converse 实际达到每个这样的父，对任意 $a_0$ 和两种 $\tau\ne0$ 符号均成立；充分性因而也是实际达到充分性。特别 $m>0,V>4a^2>0$。∎

### 67.3. 源双射、BOTH 整个恒等式与每个原系数

整个严格源域与下列开域双射：

$$
q=r_0/b>0,\quad s=2/b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},\quad
j=q+\frac{2(1-q^2)}s.
\tag{67.3}
$$

正向 $s-2q=2(1-r_0)/b>0$，秩一给 $c_{\rm src}$ 的逆式。反向四元严格正、迹一、$bc_{\rm src}=r_0(1-r_0)$，且返回相同 $q,s$。没有预删任何对角侧、对称源、$s=4$ 或 $s=4q$。

定义

$$
D_0=2-q-2q^2,\quad H=D_0+3q=2+2q-2q^2,\quad
e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,\quad T=\nu/s.
$$

**六原行 iff。** 六行当且仅当严格源、整个 $g\ne0$、$d=a_0-\lambda$ 和 BOTH 整个多项式恒等式

$$
-\lambda+eg=E+TU_0,\qquad -\lambda+og=R+qTV_o.
\tag{67.4}
$$

证明。$e,o$ 在各原偶、奇节点恰为实际迹。偶差次数至多三、三次系数为 $T$，且在 $0,2,4$ 为零；减去 $TU_0$ 后次数至多二且仍有三个不同根，故恒零。奇差在 $1,3,5$ 同理，减去 $qTV_o$。反向在这些原节点取值。此论证不除任何增益样本，允许降次与零观察。

全部偶升幂系数是

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T),
$$

可逆重建为

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad
\lambda=sF_{\rm orig},\quad d=a_0-sF_{\rm orig}.
\tag{67.5}
$$

全部奇左升幂系数是

$$
\big((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\big),
$$

右侧是 $(C-15qT,B+23qT,D-9qT,qT)$。三次自动相同，其余恰为

$$
Q=D-qA-HT=0,\quad
L_{\rm res}=B-qL+15qT-D_0[A-T(s+6)]=0,
$$

$$
R_C=C-15qT-[(q-1)s+D_0]F_{\rm orig}=0.
\tag{67.6}
$$

二次比较为 $D-9qT=q(A-6T)+D_0T$，一次为 $B+23qT=q(L+8T)+D_0[A-T(s+6)]$；常数就是 untouched 原 $C-15qT$。每步反向恢复整个奇式，故这些是充要原式。∎

### 67.4. 普通符号的导出与完整七行正根图谱

FIRST 声明普通 $q\ne a$，才置

$$
\delta=q-a,\quad u=2q+c>0,\quad \theta=T/\tau,\quad \eta=n/u<0,\quad
h=s+5-u=s-2q+d_0>0.
$$

由 $ac=2$ 有 $D_0=-\delta u,H=3q-\delta u$。归并完整原残式得精确可逆恒等式

$$
\bar Q:=Q/\tau=3a-\delta m-H\theta,\qquad
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}-5\bar Q.
\tag{67.7}
$$

因此只取消已非零的 $\delta,\tau$ 后，$Q=L_{\rm res}=0$ iff

$$
3a-\delta m-H\theta=0,\qquad m=(s+1)\theta+\eta.
\tag{67.8}
$$

定义 $\Gamma=n-(4a+1)m-6a<0$。用 $u-(4a+1)=2\delta$ 与 (67.8)，

$$
\Gamma=-K_{\rm pos}\theta,\qquad
K_{\rm pos}=u(s+1)+2H=u(s-2q+c)+6q>0.
$$

故先导出 $\theta>0$，再允许除 $\theta$；没有全局除 $H$。普通真正二次 $\nu=s\tau\theta\ne0$ 是原式结论，原域没有预先删除低次。

全部偶系数给

$$
F:=F_{\rm orig}/\tau=n-(s+5)m+(s+2)(s+4)\theta
=3\theta-h\eta>0,
$$

$$
g(t)=s\tau[\theta t^2+(\eta-5\theta)t+F],\quad
\lambda=s\tau F,\quad\mu=s\tau(\eta-5\theta),\quad\nu=s\tau\theta,\quad d=a_0-s\tau F.
\tag{67.9}
$$

常数归并用 $n=u\eta,m=(s+1)\theta+\eta$，$\theta$ 系数为三、$\eta$ 系数为 $-h$。

原时钟四与六 J 的迹相同，均为 $1+4/s$。SAME 整个增益给 $g(6)-g(4)=2s\tau(5\theta+\eta)$。已取得量

$$
\kappa=\frac{z-a_0-E(4)}{2\tau}
$$

的第七行 iff 是未除的

$$
\kappa=(s+4)(5\theta+\eta)=5m+15\theta+(s-1)\eta
=(s+4)[m-(s-4)\theta],
$$

$$
\kappa-8m=(s-4)(\eta-3\theta).
\tag{67.10}
$$

$\eta-3\theta<0$，所以 $\kappa<8m\iff s>4$，等号 iff $s=4$，$\kappa>8m\iff s<4$，全部方向成立。

对每个辅助 $q>0$ 和实 $\kappa$，定义

$$
b_\kappa=\kappa-5m+2\eta,\quad
\Delta=b_\kappa^2-60\eta(m-\eta)>b_\kappa^2,
$$

$$
\theta=\frac{b_\kappa+\sqrt\Delta}{30}>0,\qquad s=\frac{m-\eta}{\theta}-1.
\tag{67.11}
$$

来源是 $15\theta^2-b_\kappa\theta+\eta(m-\eta)=0$；常数负，故恰一正根，另一根负。辅助点仅当同时满足

$$
q\ne a,\quad s>2q,\quad \bar Q=3a-(q-a)m-H\theta=0,
$$

$$
\bar R_C:=\bar C-15q\theta-[(q-1)s+D_0](3\theta-h\eta)=0
\tag{67.12}
$$

才属于 $S_\kappa$，才成为实际普通世界。

**完整普通 converse。** 每个保留点以 (67.3)、(67.9) 给唯一普通世界，全部普通原世界也都这样出现。

证明。严格源已 imposed，首项 $s\tau\theta\ne0$。$s$ 定义给 $m=(s+1)\theta+\eta$ 和 $u\eta=n$。逐项核对全部偶系数：

$$
\nu/s=T,\qquad \nu+\mu/s=\tau[(s-5)\theta+\eta]=A-6T,
$$

$$
\mu+\lambda/s=\tau[(u-5)\eta+(3-5s)\theta]=L+8T.
$$

偶常数为零。原 $\bar Q$ 恢复奇二次，精确 (67.7) 恢复奇一次，untouched $\bar R_C$ 恢复常数 $C-15qT$，奇三次 $q\nu/s=qT$ 自动相同。因此 EVERY 奇偶系数与 BOTH (67.4) 恢复 SAME 原时钟零至五六行。正根方程仅除已正 $\theta$，反向恢复 SAME (67.10) 与实际第七行 $z$。一个严格 $P$、一个整个非零 $g$、一个固定 $d$ 同时承担这些行。

反向任一普通原世界先由原式导出 $\theta>0$，故必取 (67.11) 唯一正根；ordinary 强制此 $s$，全部偶系数强制相同整个 $g,d$，原 $Q,C$ 强制全部过滤。等 $q$ 固定整个世界，不同 $q$ 给不同源，因为 $q=r_0/b$ 可由源恢复。投影、必要符号或单个残式均不能替代这个双向逆。∎

### 67.5. 例外穷尽、实际测试、ENTIRE 并集与末函数

在 $q=a$ 不使用普通取消。$D_0=0,H=3a$，原 $Q$ 迫 $T=\tau$；原 $R_C$ 迫 $(a-1)\lambda=C-15a\tau$，即 $\lambda=\Lambda$。偶式成为 $eg=K$，整个多项式增益要求 $K(-s)=0$。严格 $s>2a$ 恰接受 $s=p$ 或 $v$；正根七要求 $s=-7$，不合法。全部例外因此恰为

$$
W_p=(P(a,p),\ p\tau(t+v)(t-7),\ d_*),\qquad
W_v:\ p,v\text{ 交换},\qquad d_*=a_0+7\tau V.
\tag{67.13}
$$

反向 $p>2a$ 给严格源，首项 $p\tau\ne0$，且

$$
\lambda=-7\tau V,\quad \mu=p\tau(v-7),\quad \nu=p\tau,\quad d=d_*.
$$

$eg=K,og=aK$ 与 (67.1) 恢复 BOTH (67.4)。更明确地，全部偶向量为

$$
(0,\tau(V-7Z),\tau(Z-7),\tau)=(0,L+8\tau,A-6\tau,\tau),
$$

全部奇向量为

$$
((a-1)\Lambda,a(L+8\tau),a(A-6\tau),a\tau)
=(C-15a\tau,B+23a\tau,D-9a\tau,a\tau).
$$

因此 EVERY 原系数，包括原 $C/15a\tau$，及 SAME 六原行均恢复，漂移从始至终为 $d_*$。交换根的证明相同。不同 $b=2/p,2/v$ 给不同整个世界。这也完成 (67.2) 每个父、任意 $a_0$、任一非零 $\tau$ 符号的实际达到证明。

实际六 J 迹为 $1+4/p$，且 $g_p(6)=-p\tau(6+v)$，所以

$$
z_p=d_*-\tau(p+4)(6+v),\qquad z_v=d_*-\tau(v+4)(6+p).
$$

减 $a_0+E(4)$ 并除 $2\tau$，用 $V=n+2m+15,Z=m+1$，得到

$$
\kappa_p=(p+4)(v+3),\qquad \kappa_v=(v+4)(p+3),\qquad
\kappa_p-\kappa_v=v-p\ne0.
\tag{67.14}
$$

例如第一式展开为 $V+3p+4v+12$，与归一化原行的全部项相同。只附加 SAME 已取得测试实际匹配的例外，至多一个，记为 $\mathcal A_\kappa$。

源双射把任何原世界分为 $q=a$ 与 $q\ne a$；两支完整必要性和充分性证明 BOTH 集合包含，故

$$
\mathcal K_\kappa:=\mathcal K_{6,J,z}
=\{W_\kappa(q):q\in S_\kappa\}\cup\mathcal A_\kappa.
\tag{67.15}
$$

没有随意附加未匹配例外。所有去重按整个三元组，可达性针对这个 ENTIRE 并集。

为陈述未决选择器，普通世界置

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta
=32\theta+n+\eta+5m-\kappa.
$$

原奇式在七给 $o(7)g(7)=\lambda+R(7)+48qT$；实际 JJ 迹为 $o(7)-2q/s$，JM 多 $(s+4-2q)/s$。因此

$$
f_{JJ}=a_0+R(7)+\tau x,\quad f_{JM}=a_0+R(7)+\tau y,
$$

$$
x=48q\theta-2q\omega,\quad y=48q\theta+(s+4-4q)\omega,\quad
y-x=(s+4-2q)\omega.
\tag{67.16}
$$

共同加项是已取得 $a_0+R(7)$，不是各世界可能不同的固定 $d$。例外 $g(7)=0$，故 $x=y=48a$。

### 67.6. N19 的完整原 C 全域屏障

先给后续 T1 所需、无响应限制的全部桥梁。$f(11/14)=1/98>0$ 给 $a<11/14$。令 $W=(p-2a)(v-2a)>0$，原父系数给

$$
I=\frac{C-3D}{\tau}=7\epsilon V-3aZ+9a
=7\epsilon W+a(11-14a)Z+a(37-42a)>0.
$$

各项正，且 $37-42a>4$。实际普通端点置

$$
B_{\rm src}=(q-1)s+D_0,\qquad G_C=hB_{\rm src}+3q.
$$

原常数减三倍原二次式，并用 ordinary，精确得

$$
I=3(q-s)\theta-G_C\eta.
\tag{67.17}
$$

$\theta$ 系数逐项为 $15q+3B_{\rm src}-3q(s+1)-3H=3(q-s)$，$\eta$ 系数为 $-hB_{\rm src}-3q$。若 $G_C\le0$，则 $s>2q,\theta>0,\eta<0$ 使右边负，矛盾。因此 $G_C>0$，这是原 $Q$ 与 ORIGINAL $C$ 的必要后果，不能替代二者。

固定 $q$ 定义完整二次式

$$
G_q(S)=(S-2q+d_0)[(q-1)S+D_0]+3q.
$$

其首项为 $q-1$，在 $L<R$ 上有精确有限弦恒等式

$$
G_q(S)=\frac{(R-S)G_q(L)+(S-L)G_q(R)}{R-L}
-(q-1)(S-L)(R-S).
\tag{67.18}
$$

**N19。** 任意响应上的实际普通负 $n$ 世界均满足 $s<3$ 或 $s>6$；特别 $q\le1$ 必有 $s<3$。

证明第一段。$12/5<d_0<5/2$。对 $0<q\le1$ 置 $x=1-q\in[0,1)$，全部三端点展开为

$$
G_q(3)=2-d_0+(2d_0-3)x+(2-2d_0)x^2-4x^3=-Q_3-4x^3,
$$

$$
Q_3=d_0-2-(2d_0-3)x+B_3x^2,\qquad B_3=2d_0-2>0.
$$

精确平方为

$$
4B_3Q_3=[2B_3x-(2d_0-3)]^2+4d_0^2-12d_0+7
=[2B_3x-(2d_0-3)]^2+39-48a>0.
$$

余项 $39-48a>3/5$，故 $G_q(3)<0$。另

$$
B_{{\rm src},3}=3(q-1)+D_0=-2(q-1/2)^2-1/2<0,\quad h_3=3-2q+d_0>0.
$$

对 $v_*\ge0$，全部有限差为

$$
G_q(3+v_*)-G_q(3)=v_*[B_{{\rm src},3}+(q-1)h_3]+(q-1)v_*^2\le0.
$$

所以包括 $q=1$ 在内，$q\le1$ 的实际端点不能有 $s\ge3$。

证明第二段。若 $3\le s\le4$，剩余严格源迫 $1<q<2$。置 $x=q-1\in(0,1)$，完整端点为

$$
\begin{aligned}
G_q(3)&=2-d_0+(3-2d_0)x+(2-2d_0)x^2+4x^3\\
&\le2-d_0+(3-2d_0)x+(6-2d_0)x^2\\
&\le2-d_0+(9-4d_0)x<0,
\end{aligned}
$$

$$
\begin{aligned}
G_q(4)&=1-d_0+(3-d_0)x+(-2d_0-2)x^2+4x^3\\
&\le1-d_0+(3-d_0)x+(2-2d_0)x^2\le4-2d_0<0.
\end{aligned}
$$

第一行先用 $x^3\le x^2$，再在正系数 $6-2d_0>0$ 下用 $x^2\le x$；此时 $2-d_0<0,9-4d_0<0$。第二行先用 $x^3\le x^2$，再丢负二次项并用 $3-d_0>0,x\le1$。两端负及正首项 $q-1$ 的 (67.18) 在 $[3,4]$ 排除该区间。

证明第三段。若 $4\le s\le6$，第一段排除 $q\le1$，严格源给 $1<q<3$。对 $x=q-1\in[0,1]$，完整端点为

$$
\begin{aligned}
G_q(4)&=2a-3+(2a-1)x+(4a-10)x^2+4x^3\\
&\le2a-3+(2a-1)x+(4a-6)x^2\le4a-4<0,
\end{aligned}
$$

$$
G_q(6)=2a-5+(13-2a)x+(4a-18)x^2+4x^3\le-Q_6,
$$

$$
Q_6=(14-4a)x^2-(13-2a)x+5-2a,
$$

$$
4(14-4a)Q_6=[2(14-4a)x-(13-2a)]^2+139-154a>0.
$$

最后余项因 $a<4/5$ 严格正。对 $y=q-2\in[0,1]$，

$$
\begin{aligned}
G_q(6)&=4a-6+(6a-11)y+(4a-6)y^2+4y^3\\
&\le4a-6+(6a-11)y+(4a-2)y^2\\
&\le4a-6+(10a-13)y<0.
\end{aligned}
$$

方向依次用 $y^3\le y^2$、正系数 $4a-2$ 下的 $y^2\le y$。另对 $q\ge2$，

$$
G_q(2q)=8-4a+(6a-9)q\le8a-10<0.
$$

对 $1<q\le2$ 用弦 $[4,6]$；对 $2<q<3$ 用正长度弦 $[2q,6]$。两端负及 (67.18) 与 $G_C>0$ 矛盾。所有辅助端点只承担多项式比较，不被当作世界。三段合并得全域无 $3\le s\le6$。∎

独立地，若 $\kappa>8m$，先由 (67.10) 得 $s<4$，再由 N19 得 $s<3,q<s/2<3/2<\phi$，其中 $\phi=(1+\sqrt5)/2$。这里没有越域使用有界响应的 N9、N15 或 N16。

### 67.7. T1：m 不超过三的任意响应普通排除

**T1。** 对 EVERY 达到父 $n<0,4a-1<m\le3$，EVERY 实际普通世界在 ANY 响应上均有

$$
s>6,\qquad q>1,\qquad \kappa<50m/7.
\tag{67.19}
$$

证明父界。$a>3/4$ 给 $m>2$。置 $w=-n=2m+15-V>0$。严格父上界给

$$
w>2m+15-\frac{(m+1)^2}{4}
=\frac{67}{4}+\frac{(m-2)(4-m)}4>\frac{67}{4},
$$

包括 $m=3$。

第一步只在 $0<q\le Q_0=5/4$。定义

$$
N(q)=3a+m(a-q)=m(z_Q-q),\qquad z_Q=a+3a/m.
$$

$m\le3$ 给 $z_Q\ge2a>3/2>Q_0$，所以 $N>0$。又

$$
H(q)-11/8=2(Q_0-q)(q+1/4)\ge0.
$$

先有 $H\ge11/8>0$，ONLY HERE 才由 ORIGINAL $Q$ 写 $\theta=N/H$。ordinary 给

$$
s+1=\frac{H(mu+w)}{uN},\qquad
(s-3)uN=D_{\rm small}:=H(mu+w)-4uN.
$$

完整三次展开为

$$
\begin{aligned}
D_{\rm small}(q)={}&-4mq^3+[(10-4a)m-2w]q^2\\
&+[(10+4a)m+2w-24a]q+2[w-(3-2a)m-12].
\end{aligned}
\tag{67.20}
$$

为逐项核对所有系数，$Hmu$ 贡献
$m[-4q^3+(4-2c)q^2+(4+2c)q+2c]$，$Hw$ 贡献 $-2wq^2+2wq+2w$，$4uN$ 贡献 $-8mq^2+(-4m+24a)q+8m+24$。相减并用 $ac=2$ 正好得到 (67.20) 的四个系数。

第二步证明整个有限区间正。三次系数负；二次系数负，因为 $(10-4a)m<21<2w$。在零，

$$
(3-2a)m+12<33/2,\qquad D_{\rm small}(0)>2(67/4-33/2)=1/2.
$$

在 $Q_0$，$u_0=2a+7/2$，精确归组为

$$
D_{\rm small}(Q_0)=\frac{11}{8}w+u_0B_0,\qquad
B_0=(51/8-4a)m-12a.
$$

$51/8-4a>0,m>2$ 给 $B_0>51/4-20a>-13/4$，且 $0<u_0<21/4$。必须先分符号：若 $B_0\ge0$，则 $u_0B_0\ge0>-273/16$；若 $B_0<0$，乘 $u_0<21/4$ 时反向，给

$$
u_0B_0>(21/4)B_0>-273/16.
$$

两种情形均成立，而 $(11/8)w>737/32$，故

$$
D_{\rm small}(Q_0)>737/32-273/16=191/32.
$$

对 $0\le q\le Q_0$，$q^2\le Q_0q,q^3\le Q_0^2q$，乘两个负高次系数时方向反转，无需一次系数的符号，得到完整有限三次弦下界

$$
D_{\rm small}(q)\ge(1-q/Q_0)D_{\rm small}(0)+(q/Q_0)D_{\rm small}(Q_0)>0.
$$

这是辅助多项式比较，不假定中间点可行。$uN>0$ 已先证明，故实际 $q\le5/4$ 必有 $s>3$。

第三步排除全部 $s<3$。反设实际 $s<3$，上一步迫 $q>5/4$，严格源给 $q<s/2<3/2$。N19 在 $1<q<2$ 的完整 $G_q(3)<0$ 适用。另因 $6a-9<0$，

$$
G_q(2q)=8-4a+(6a-9)q
<8-4a+(6a-9)\frac54=\frac{14a-13}{4}<0.
$$

$2q<s<3$ 且 $3-2q>0$，完整弦为

$$
G_q(s)=\frac{(3-s)G_q(2q)+(s-2q)G_q(3)}{3-2q}
-(q-1)(s-2q)(3-s)<0.
$$

这与 ORIGINAL $Q/C$ 导出的 $G_C>0$ 矛盾。N19 已证明任意响应 $s<3$ 或 $s>6$，故现在 EVERY 实际普通有 $s>6$。N19 的 $q\le1\Rightarrow s<3$ 又给 $q>1$。最后

$$
7\kappa-50m=-15(s-6)\theta+(7s-22)\eta<0
$$

因为 $s>6,\theta>0,\eta<0$。整个无高响应普通排除在 ANY 响应上已独立建立，没有先导入有界响应对定理。∎

### 67.8. T2–T3：精确可达高响应与七 TOTAL 完整逆

**T2。** 固定 EVERY $n<0,4a-1<m\le3$ 达到父。其可达归一化响应集合满足

$$
\operatorname{ReachableKappa}\cap[50m/7,\infty)=\{\kappa_p,\kappa_v\},
\tag{67.21}
$$

两个测试不同、实际达到且均严格大于 $8m$；各 ENTIRE 子片恰为它的匹配例外。每个可达 $\kappa<50m/7$ 子片 ENTIRELY 只含普通世界。

证明。$Z=m+1\le4$ 且另一根严格正，故 $p,v<4$，包括 $m=3$。精确测试差为

$$
\kappa_p-8m=(p-4)(v-5)>0,\qquad
\kappa_v-8m=(v-4)(p-5)>0.
$$

$m>0$ 给 $8m>50m/7$。67.5 的完整例外 converse 在 SAME 父上构造 $W_p,W_v$，恢复每个原系数、全部六行及各自实际第七测试；故两个测试都真正可达，且由 $v-p\ne0$ 不同。

任何可达 $\kappa\ge50m/7$，T1 排除 ALL 普通，ENTIRE (67.15) 与例外穷尽迫其恰为一个实际匹配例外，响应必为两个测试之一。反向两个构造世界给 (67.21) 另一包含。不同测试给各完整子片单点。特别 CLOSED $[50m/7,8m]$ 无可达响应，两个边界也不是空类成功。低于阈值两个例外均不能匹配，ENTIRE 并集只剩完整普通图谱；不承诺每个低响应实数可达。∎

**T3。** 在相同父范围及已取得 $\kappa\ge50m/7$ 守卫上，原时钟零至六七 TOTAL 有整个 $P,g,d$ 的充要唯一逆，不取得原时钟七实际响应。

由六行插值得 $a_0,E,R$，核对完整父谓词、全部系数及严格因子条件，恢复 $\tau,m,n,Z,V$ 与无序 $\{p,v\}$。原时钟六选择指定 J，取得 $z$ 并形成 SAME $\kappa$。实际可达性及 T2 迫恰一个测试相等。若 $\kappa=\kappa_p$，返回

$$
P=\begin{pmatrix}2a/p&2/p\\a(1-2a/p)&1-2a/p\end{pmatrix},\quad
\lambda=-7\tau V,\quad\mu=p\tau(v-7),\quad\nu=p\tau,\quad d=a_0+7\tau V.
\tag{67.22}
$$

若 $\kappa=\kappa_v$，交换 $p,v$ 返回同型式。根交换只交换测试名字和对应表示，不改变返回的整个世界，不用隐藏根标签。

必要性：真世界属于完整七行并集，T1 排除 ALL 普通，不同实际测试唯一固定此例外。充分性：$p>2a$ 给每个源元严格，$p\tau\ne0$ 给整个增益非零，漂移为一个固定 $d_*$。67.5 明列的偶向量与奇向量逐项恢复 EVERY 系数，特别原 $C-15a\tau$，也等价于 $eg=K,og=aK$ 和 (67.1) 恢复 BOTH (67.4)。取同一个固定 $d=a_0-\lambda$，原节点取值恢复 SAME 六行；实际测试匹配恢复 SAME 第七行 $z$。反向任何与七原行相容的完整世界都在 (67.15)，从 T1 和例外穷尽只能等于这个返回世界。因此是双向整个目标逆。记录在谓词外不据此拒绝别类；空类不算成功。没有一般七读上界、必要第八读或未知类并集推断。∎

### 67.9. mH 以下父的严格有理界与正 θ 分支

令

$$
\phi=\frac{1+\sqrt5}{2},\quad \chi=\phi-1,\quad \chi^2+\chi=1,\quad\phi\chi=1,
\quad H(q)=2(\phi-q)(q+\chi),
$$

$$
m_H=\frac{3a}{\phi-a}=2(a+\chi).
$$

$H(a)=3a=2(\phi-a)(a+\chi)$ 给等式，$\phi-a>0$。对 $f$ 的正因子式，

$$
f(17/22)=-2/121<0,\qquad f(11/14)=1/98>0,
$$

给 $17/22<a<11/14$。对 $j(x)=x^2+x-1=(x-\chi)(x+\chi+1)$，

$$
j(1/2)=-1/4,\quad j(8/13)=-1/169,\quad j(5/8)=1/64
$$

给 $1/2<\chi,8/13<\chi<5/8$。特别 $\phi>21/13>8/5$。于是

$$
\frac52<m_H<\frac{79}{28}<\frac{17}{6}<3,\quad
\frac52<c<\frac{18}{7}<\frac{13}{5},\quad
\frac{12}{5}<d_0<\frac52,\quad c>2\chi.
\tag{67.23}
$$

此后固定目标范围 $m_0=4a-1<m<m_H$。T1 已在全部响应证明 $q>1,s>6,\kappa<50m/7$ 对每个实际普通成立，且 $m>2$。严格父上界给

$$
w>\frac{-m^2+6m+59}{4}>9+10a,
$$

第二差精确为 $(m-m_0)(6-m-m_0)/4>0$；$m<3,m_0<11/5$ 先保证后一因子正。另令 $M=79/28$，

$$
m^2+18m-59<M^2+18M-59=-199/784<0,
$$

方向来自差 $(M-m)(M+m+18)>0$，故 $w>6m$。结合 T1 父界及 $V>4a^2>9/4,m<3,Z<4,V<4$，得到

$$
9+10a<w,\quad \frac{67}{4}<w<\frac{75}{4},\quad w>6m,\quad \bar C<19.
\tag{67.24}
$$

上 $w$ 界由 $w=2m+15-V<6+15-9/4$；$\bar C<19$ 由 $\epsilon<1/4,V<4,a<4/5$。所有界均严格，非执行读数。

置 $z_Q=a+3a/m$。$m<m_H$ 给 $z_Q>\phi$。另一方面

$$
(z_Q(m_0)-2)m_0=6-8a<0,
$$

而 $m>m_0$ 使 $z_Q<z_Q(m_0)$，故

$$
\phi<z_Q<2.
$$

原 $Q$ 保持未除形式 $H(q)\theta=m(z_Q-q)$。若 $q=\phi$ 则原式迫 $m=m_H$，矛盾；若 $q=z_Q$ 则 $H(z_Q)\theta=0$，而 $H(z_Q)<0,\theta>0$，矛盾。先按原式排零，才在已签名支上使用

$$
\theta=\frac{m(z_Q-q)}{2(\phi-q)(q+\chi)}.
\tag{67.25}
$$

结合 $\theta>0,q>1$，实际普通只能在两个开分支

$$
1<q<\phi,\qquad z_Q<q<\infty.
\tag{67.26}
$$

下一节将上射线严格缩到二以下；原 $C$ 仍必须保留。

### 67.10. N26：原 Q 与原 C 迫 q 严格小于二

**N26。** 每个目标范围实际普通世界在固定响应前已有 $1<q<2$。

证明。反设 $q\ge2$。由 $z_Q<2$ 属上 signed 支，且 $q-z_Q<q-\phi$，所以仅在此已签名支可写

$$
0<\theta=\frac{m(q-z_Q)}{2(q-\phi)(q+\chi)}<\frac{m}{2(q+\chi)}.
$$

令 $X=s-2q>0$。ordinary 给

$$
X>2\chi-1+\frac{2(q+\chi)}u\frac wm.
\tag{67.27}
$$

对 $q\ge2$，有

$$
\frac{2(q+\chi)}u>\frac{2q+16/13}{2q+18/7}\ge\frac{238}{299}.
$$

第二比较交叉乘的差为 $2(q-2)(18/7-16/13)\ge0$，所有分母正；端点只是辅助比值，不作世界。$2\chi-1>3/13=69/299,w/m>6$ 使

$$
X>1497/299>5.
$$

原源常数因子精确为 $B_{\rm src}=(q-1)(X-3)-1>2q-3>0$。又

$$
\frac{2q-3}{2q+c}\ge\frac1{4+c}=\frac1{5+2a},
$$

交叉分子差为 $2(q-2)(c+3)\ge0$。所以 $B_{\rm src}/u>1/(5+2a)$，且 $h=X+d_0>9-2a$。用 ORIGINAL 常数而非投影，

$$
\bar C=15q\theta+B_{\rm src}F
>B_{\rm src}\frac{hw}{u}
>\frac{(9-2a)(9+10a)}{5+2a}>19.
$$

这里 $F=3\theta+hw/u>hw/u$；最后比较的差为

$$
\frac{(9-2a)(9+10a)}{5+2a}-19=\frac{44a-34}{5+2a}>0
$$

因为 $a>17/22$。这与 (67.24) 的同一个原 $\bar C<19$ 矛盾。所有分母先正，没有全局除 $H$，也没有用必要不等式创建世界。∎

### 67.11. N27：上分支隙界与全域 rho 界

**N27。** 上分支 $z_Q<q<2$ 的每个实际普通有 $X<6,0<\rho<6$；下分支 $1<q<\phi$ 有 $0<\rho<7$，其中 $\rho=-\eta/\theta=w/(u\theta)$。

证明上分支。若 $X\ge6$，则 $q>\phi>8/5$，

$$
B_{\rm src}=(q-1)(X-3)-1\ge3q-4>0.
$$

函数比值只作有限代数比较：对 $r>q$，

$$
\frac{3r-4}{2r+c}-\frac{3q-4}{2q+c}
=\frac{(r-q)(3c+8)}{(2r+c)(2q+c)}>0.
$$

因此

$$
\frac{B_{\rm src}}u\ge\frac{3q-4}{2q+c}
>\frac{4/5}{16/5+c}>\frac4{29},
$$

最后用 $c<13/5$。$h=X+d_0>42/5$ 与 $w>67/4$ 给原常数

$$
\bar C>\frac{B_{\rm src}hw}{u}
>\frac4{29}\frac{42}{5}\frac{67}{4}=\frac{2814}{145}>19,
$$

矛盾。故 $X<6$。上 signed 支的原 $Q$ 比较已给 $m/\theta>2(q+\chi)$；ordinary 因而给

$$
\rho=s+1-m/\theta<X+1-2\chi<X<6.
$$

证明下分支。$1<q<\phi$ 且 $q>a$，所以

$$
3a-(q-a)m>3a-(q-a)m_H=m_H(\phi-q)>0.
$$

先有 $H=2(\phi-q)(q+\chi)>0$，再除得

$$
\theta>\frac{m_H}{2(q+\chi)}.
$$

$c>2\chi$ 给 $u>2(q+\chi)$，所以 $u\theta>m_H$，$\rho<w/m_H$。严格父界使

$$
w=2m+15-V<2m_H+15-4a^2<7m_H.
$$

最后一步为 $15-4a^2=11+2a<5m_H$，等价于 $8a+10\chi>11$，由 $a>3/4,\chi>1/2$ 严格成立。因此下分支 $\rho<7$。全域 $\rho>0$ 早由 $\theta>0,\eta<0$ 导出。没有借用 $m>m_H$ 的相反几何符号。∎

### 67.12. N28：严格有界源域与低响应 ENTIRE 等号

**N28。** 每个目标范围实际普通世界满足

$$
1<q<2,\quad 6<s<11,\quad \frac13<\theta<1,\quad 0<\rho<7,
$$

$$
\frac2{11}<b<\frac13,\qquad \frac2{11}<r_0<\frac23,\qquad
\frac13<c_{\rm src}<2.
\tag{67.28}
$$

上分支还满足 $s<10,\rho<6$。这些均为严格必要界，不声称尖锐或普通存在。

证明。$s>6$ 来自 T1。上分支 $s=2q+X<4+6=10$。下分支由 N27，

$$
s+1=m/\theta+\rho<2(q+\chi)+7<2(\phi+\chi)+7=2\sqrt5+7<12,
$$

因为 $\sqrt5<5/2$，故 $s<11$。又 $u>2+c>9/2,m<17/6,w<75/4$，

$$
m+w/u<\frac{17}{6}+\frac{75/4}{9/2}=7.
$$

ordinary 给 $\theta=(m+w/u)/(s+1)<1$，因为 $s+1>7$。另一方面 $q<2$ 给 $u<5+2a$，N27 给 $\rho<7$，父界给 $w>9+10a$，所以

$$
\theta=\frac{w}{u\rho}>\frac{9+10a}{7(5+2a)}>\frac13.
$$

最后比较等价于 $16a>8$。由源双射，$b=2/s$ 立即给两个严格界；$r_0=2q/s$ 的下界来自 $q>1,s<11$，上界来自 $q<2,s>6$。最后

$$
c_{\rm src}=q(1-r_0)>1\cdot\frac13=\frac13,\qquad c_{\rm src}<q<2.
$$

每次乘除的正因子均已先确立。∎

**有界低响应图谱的精确双向性。** 固定 SAME 达到 $a_0,\tau,m,n$，其中 $4a-1<m<m_H$，再固定 SAME 实 $\kappa<50m/7$。对每个辅助 $q$ 使用 (67.11)，$\eta=n/(2q+c),h=s+5-u$。令 $S^{\rm box}_\kappa$ 为同时满足下列条件的 ALL 点：

$$
q\in(1,\phi)\cup(z_Q,2),\quad q\ne a,\quad s>2q,\quad 6<s<11,
\quad \frac13<\theta<1,\quad0<\rho<7,
$$

$$
q>z_Q\ \Longrightarrow\ s<10,\ \rho<6,\qquad
\bar Q=0,\quad \bar R_C=0.
\tag{67.29}
$$

可冗余保留 (67.28) 的源元界；它们绝不替代原残式。则精确 ENTIRE 等号是

$$
\mathcal K_\kappa=\{W_\kappa(q):q\in S^{\rm box}_\kappa\}.
\tag{67.30}
$$

必要包含：T2 使任何相容世界均普通；完整七行 iff 把它送入 $S_\kappa$，T1、(67.25)、N26–N28 给 EVERY 新严格界和两个 signed 分支，所以在有界列表中，无世界被删。充分包含：任一保留点仍有 SAME 父与 SAME $\kappa$、严格源、BOTH ORIGINAL $\bar Q,\bar R_C$，故 67.4 的逐系数 converse 恢复一个严格 $P$、一个整个非零二次 $g$、一个固定 $d$、全部奇偶系数、BOTH 恒等式及 ALL SAME 七原行。两个原残式中的 $C$ 和 $15qT$ 未更改。因而它确是原世界，而不是只有必要符号的有界投影。反向任何原相容世界都已包含，证明 BOTH 包含。可达时这集合非空；未取得的低实数允许空，不当作成功。

(67.30) 是对旧完整 iff 增加已证冗余界后的精确表示。必要有界性本身不给候选数、一个动作的 ENTIRE 单射、碰撞、有效枚举或普通存在。最终剩余上支是 $(z_Q,2)$，不再是不受界的射线。

### 67.13. 既有 mH 桥梁及新的唯一可能非单点响应

本段把既有第 65 节 N16–N18 的精确原世界范围与新 T1–T3 结合。既有 $m=m_H$ 全响应选择器、以及第 66 节 $m>m_H$ 全响应选择器都是 prior 内容；本卷不把它们计作一般低于 $m_H$ 的新完成。以下核对边界定位实际消费的桥梁。

**原常数的全域普通末正性。** 每个实际普通负 $n$ 世界在任意响应有 $\omega>0$。置 $\rho_e=-\eta/\theta>0$，ordinary 给 $\rho_e<s+1$。若 $h\ge7$ 立即正；若 $h<7,q\le3a-1$，

$$
\omega/\theta>17-(u+2-s)(s+1),\qquad
(u+2-s)(s+1)=\frac{(u+3)^2}{4}-\left(s-\frac{u+1}{2}\right)^2\le17,
$$

因为 $u+3\le2(4a+1),(4a+1)^2=17$。这覆盖 $q\le5/4$。其余 $q\ge5/4$ 有
$B_7=(q-1)(s+7)+D_0=(q-1)(s-2q)+4q-5>0$。
若 $\theta\ge1$，原偶式在七给

$$
(s+7)\omega=sF+7V+105(\theta-1)>0.
$$

若 $0<\theta<1$，在只恢复偶式和 $Q=L_{\rm res}=0$ 时奇差只剩 $-R_C$，在七与偶式相减得完整方向

$$
R_C/\tau=C_7-(105-48q)\theta-B_7\omega,\quad C_7=105-48a>0.
\tag{67.31}
$$

这里用 $E(7)=-\Lambda-105\tau,R(7)=-\Lambda-48a\tau$，故原 $C/15qT$ 被保留。实际 $R_C=0$ 时，若 $105-48q\ge0$，右预测给 $B_7\omega\ge C_7-(105-48q)=48(q-a)>0$；若该系数负，则 $B_7\omega>C_7>0$。于是全域正。例外仍合法地有 $\omega=0$。

**有界响应实际对的必要弦与反向源隙。** 本小段只用于 SAME 父和 SAME $\kappa\le8m$ 的两个实际普通世界。由 N19 及 (67.10) 先有 $q>1,s>6$。不同完整世界可由固定 $q$ 唯一性排序 $q<r$，令 $\ell=r-q>0,\zeta=\theta_2>0,\rho=-\eta_2/\zeta>0,u=2q+c,U=2r+c$。同 $n$ 迫 $\eta_1=-\rho\zeta U/u$。先不假定符号，定义

$$
\alpha=\frac{\theta_1-\theta_2}{\ell\zeta},\quad\beta=2\rho/u,\quad
k=(S-s)/\ell.
$$

同 $m,\kappa$ 给 $k=(s+1)\alpha-\beta$ 与 $k(5-\rho)=(s+4)(5\alpha-\beta)$，不除 $5-\rho$ 得

$$
K_p=15+(s+1)\rho>0,\quad L_p=s-1+\rho>0,\quad
R_p=2\rho/(uK_p)>0,
$$

$$
\alpha=R_pL_p>0,\quad\beta=R_pK_p,\quad k=R_p(s^2-16)>0.
\tag{67.32}
$$

这是实际端点的必要关系，没有把差式称为世界 iff；每端仍满足两个原残式及全部七行。

为完整保留 N15 原 $C$ 内容，置 $X=s-2q,Y=S-2r$，

$$
h_g(x)=x+d_0,\quad A_g(x)=h_g(x)(x-3)+3=x^2+(1-2a)x+6a-9.
$$

实际 $B_{\rm src}=(q-1)(X-3)-1,G_C=(q-1)A_g(X)+3-h_g(X)>0$。
若 $0<X\le2$，$s>6$ 迫 $q>2$。固定 $q$ 的二次式
$G(q,x)=(x+d_0)[(q-1)x+2-3q]+3q$ 首项正，端点
$G(q,0)<8a-10<0,G(q,2)=q(1-d_0)<0$；完整弦排除 $[0,2]$。故 $X>2$，同理 $Y>2$，再由 $G_C>0$ 得 $A_g(X),A_g(Y)>0$。

用 SAME 原 $I$ 而非两个正性界，(67.17) 加三倍 ordinary 逐端给

$$
I+3m=3(q+1)\theta+w\mathcal R(q,X),\quad
\mathcal R(q,x)=\frac{(q-1)A_g(x)-h_g(x)}{2q+c}.
$$

定义 $L_g=(c+2)A_g(X)+2h_g(X),E_g=(r-1)(X+Y+d_0-3)-1$。完整交叉乘得

$$
\mathcal R(r,X)-\mathcal R(q,X)=\frac{\ell L_g}{uU},\quad
\mathcal R(r,Y)-\mathcal R(r,X)=\frac{(Y-X)E_g}{U}.
$$

第一式的 $A_g$ 系数为 $\ell(c+2)$、$h_g$ 系数为 $2\ell$；第二式用 $A_g(Y)-A_g(X)=(Y-X)(X+Y+d_0-3)$。交叉点不作实际世界。$Y-X=\ell(k-2),w=U\rho\zeta$，减 SAME 不变量并仅除正 $\ell\zeta$ 得

$$
0=N_g+\rho(k-2)E_g,\qquad N_g=3[1-(q+1)\alpha]+\rho L_g/u.
$$

先证明全正。$X>2$ 给 $L_g>2h_g(X)>3$，且 $u<s+1$，故 $L_g/u>3/(s+1)$。取 $z=\min(X,Y)>2$，其实际端点坐标不大于 $r$。该端点原 $G_C>0$ 给 $(r-1)A_g(z)>h_g(z)-3$。$D_g=2z+d_0-3>0$，完整正恒等式

$$
[h_g(z)-3]D_g-A_g(z)=(d_0+2)(d_0-1)+(z-2)(z+2d_0-4)>0
$$

给 $(r-1)D_g>1$，再由 $X+Y\ge2z$ 得 $E_g>0$。又 $u>2(q+1)$，所以

$$
(q+1)\alpha<\frac{s-1+\rho}{s+1},\qquad
N_g>\frac6{s+1}+\rho\left[\frac{L_g}{u}-\frac3{s+1}\right]>0.
$$

此后才除 $\rho E_g>0$ 得 $k<2$。合 (67.32)，完整实际对满足

$$
0<k<2,\qquad Y<X.
\tag{67.33}
$$

若再有 $0<\rho\le32$，精确系数

$$
32L_p-K_p=(32-\rho)(s-6)+145+25\rho>0
$$

与 SAME-child $\omega$ 弦给 $\omega_1-\omega_2=\ell\zeta R_p(32L_p-K_p)>0$。全域普通末正性与 (67.33) 给

$$
(y_1-x_1)-(y_2-x_2)=(X+4)(\omega_1-\omega_2)+(X-Y)\omega_2>0.
\tag{67.34}
$$

这就是所消费 N16：x 碰撞则 y 分离，y 碰撞则 x 分离。它仅对该有守卫的一对，不证明更大集合有一个全局单射动作。

**唯一实际奇异世界与 regular 限制。** 在 $m=m_H$，精确达到层为

$$
Z_H=m_H+1,\quad V\in I_H=(2aZ_H-4a^2,Z_H^2/4),\quad n=V-2m_H-15.
$$

区间宽 $(Z_H-4a)^2/4>0$，因为 $Z_H-4a=2\phi-1-2a>0$；父区域逆及例外 converse 给实际达到。基本严格界为

$$
\frac94<V<4,\quad-\frac{75}{4}<n<-16,\quad\frac{72}{5}<\bar C<19,
\quad \frac{11}{2}<u_H=2\phi+c<6,\quad -4<\eta_H=n/u_H<-\frac83.
$$

$V$ 界由 $V>4a^2,Z_H<4$，$n$ 界由 $5/2<m_H<3$；$\bar C$ 下界为 $7(1/5)(9/4)+15(3/4)=72/5$，上界同 (67.24)。$u_H$ 界与 $n$ 界给 $\eta_H$ 界。

在辅助射线 $s\ge2\phi$ 置

$$
\theta(s)=\frac{m_H-\eta_H}{s+1}>0,\quad h=s+5-u_H,\quad B(s)=\chi s-3\phi,
$$

$$
R_H(s)=15\phi\theta(s)+B(s)[3\theta(s)-h\eta_H]-\bar C=-R_C/\tau.
$$

$q=\phi$ 的原 $Q$ 直接成立，不除 H；ordinary 由定义恢复。在边界 $2\phi$ 的预测常数为

$$
\alpha_Hm_H+\eta_H[(3\phi-2)(4-2a)-\alpha_H],\qquad
\alpha_H=\frac{6(\phi+1)}{2\phi+1}<4.
$$

括号第一积大于六，故括号正；预测常数小于十二，$R_H(2\phi)<0$。在四，$\theta_4<7/5,h_4>3$，

$$
R_H(4)=(18\phi-12)\theta_4+(4-\phi)h_4\eta_H-\bar C
<126/5-56/3-72/5<0.
$$

在十二，$B(12)=9\phi-12>3/2,h(12)>11,F(12)>88/3$，故 $R_H(12)>44-19>0$。$s+1>0$ 保证有限 $[4,12]$ 连续，IVT 给根 $s_H\in(4,12)$。

完整表达为

$$
R_H(s)=3(m_H-\eta_H)\chi+\frac{A_H}{s+1}
-\eta_H(\chi s-3\phi)(s+5-u_H)-\bar C,\quad
A_H=3(m_H-\eta_H)(\phi+1)>0.
$$

对 $2\phi\le x<y<z$，连续两弦斜率差为

$$
(z-x)\left[\frac{A_H}{(x+1)(y+1)(z+1)}-\eta_H\chi\right]>0.
$$

倒数弦为 $-A_H/[(x+1)(y+1)]$，二次系数为 $-\eta_H\chi>0$，仿射项消去。若有两严格根，边界到首根的弦正、两根间弦零，矛盾。故整个严格射线唯一根。此根的 $P(\phi,s_H)$、(67.9) 恢复 EVERY 偶系数、$L_{\rm res}$、直接原 $Q$、untouched $R_C$，故 BOTH 恒等式与 SAME 六行；它的实际

$$
\kappa_H=(s_H+4)(5\theta+\eta_H)
$$

由第七行 iff 给取得响应。反向任何 H 零世界必 $q=\phi,m=m_H$，ordinary 固定 $\theta(s)$，原 C 固定此唯一根，故整个世界唯一。T1 适用 $m_H<3$，所以 $6<s_H<12,\kappa_H<50m_H/7$。

在普通 regular 支 $q\ne\phi$，原 $Q$ 精确因式为

$$
\bar Q=(\phi-q)[m_H-2(q+\chi)\theta].
$$

仅在 regular 声明后取消 $\phi-q$ 得

$$
\theta=\frac{m_H}{2(q+\chi)},\qquad
\xi_{\rm reg}=s-2q=2\chi-1+\frac{2w}{m_H}\frac{q+\chi}{2q+c},
\qquad 0<\rho_e<\frac{w}{m_H}<\frac{15}{2}.
$$

因 $c>2\chi$，两实际 regular 端点 $q<r$ 有

$$
\xi_{\rm reg}(r)-\xi_{\rm reg}(q)
=\frac{2w(r-q)(c-2\chi)}{m_H(2q+c)(2r+c)}>0.
$$

对 SAME 低响应 $\kappa<50m_H/7<8m_H$，(67.33) 要求反向严格隙序，故至多一个 regular。奇异世界的 $\rho_e=w(s_H+1)/(u_Hm_H+w)<s_H+1<13$；regular 也 $\rho_e<13$。因此有两普通时满足 (67.34) 的守卫。

**新边界细化。** 对 EVERY 上述 $m=m_H$ 达到父、任意 $a_0$ 和任一 $\tau\ne0$ 符号，EVERY 可达 $\kappa\ne\kappa_H$ 的 ENTIRE 子片均为单点。唯一可能非单点在 $\kappa_H$，其整个集合为唯一奇异世界加至多一个 regular 普通世界。

完整证明。T1–T3 适用于 $m_H<3$，所以高响应 $\kappa\ge50m_H/7$ 恰为两个例外测试及其 ENTIRE 单点，普通完全不存在。此步把既有可能在 $\kappa_p,\kappa_v$ 的混合非单点全部排除。低响应无匹配例外；普通至多一个 regular，加整个父唯一奇异世界。若 $\kappa\ne\kappa_H$，奇异世界不匹配，至多一个 regular，可达性给恰一个。若 $\kappa=\kappa_H$，该奇异世界已实际构造并恢复 SAME 七行，另至多一个 regular。这些情形穷尽所有实响应与 ENTIRE (67.15)，故结论成立。没有假定 regular 或非单点实际存在，也没有第八读必要性断言。∎

既有 N18 选择器在此保留完整原世界含义：ENTIRE 单点七 TOTAL 停；若在 $\kappa_H$ 恰两普通，比较完整预测 x，不同选 J，相同选 M，(67.34) 保证分离。只取得所选时钟七实际响应 $f$，保留 $x=(f-a_0-R(7))/\tau$ 或对应 y 的完整候选。真实世界给存在，ENTIRE 两点的所选单射给唯一；67.4 的 EVERY 系数、BOTH 恒等式、SAME 六行和 SAME 第七行 converse，再加所选实际末等式给第八行。反向任何八行相容世界先在完整七行并集，再满足所选式，只能等于返回世界。返回 (67.3)、(67.9) 的全部源元和系数，包括 $q=\phi,s=s_H$；高响应返回 (67.22)。这是精确集合论规则，不是有效求解或有限精度程序。新增是可能非单点响应从既有三个预测值细化为唯一 $\kappa_H$，不是重报既有边界选择器。

### 67.14. SAME 父坏 M 的 FULL 等号与保留的失败义务

为保持原局部失败判据，另一实际时钟六响应为

$$
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
$$

原偶式给 $h_M=a_0+E(6)+48T$，故该 FULL 子片固定 $T=\tau$。需排除 ALL 普通 $T=\tau$，不能仅排除末零。

反设普通 $\theta=1$。原 $Q$ 给 $u=m+3=Z+2,q=(Z+1)/2-a,\delta>1/2$。置 $h_o=s-Z+7>8-2a>6$；ordinary 和全部偶系数给

$$
V=(7-h_o)Z+23-2h_o,\quad g=s\tau(t^2-h_ot+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-9/2)^2+11/4>0.
$$

原常数为 $(a-1)(-7V)-15\delta=B_{\rm src}\chi_o$。减 $(a-1)s\chi_o$，用 $D_0=-\delta(Z+2)$ 和
$(h_o-9)\chi_o+15=(h_o-4)(h_o-6)(h_o-8)$，精确得到

$$
-7V=s\chi_o-\frac{\delta(h_o-4)(h_o-6)(h_o-8)}{1-a}.
$$

原 $15\delta$ 未消失。负左边与 $h_o>6$ 迫 $h_o>8$；$V>4a^2,Z>4a$ 与线性 V 式迫
$h_o<(19+30a)/(4a+2)<17/2$，最后比较为 $4a-2>0$。于是正三因子积小于 $45/8$，$\chi_o>15$，$1-a>1/5$，该积除 $(1-a)\chi_o$ 小于 $15/8$。严格源给 $0<\delta<q<s/2$，原常数反而迫 $-7V>s\chi_o/16>0$，矛盾。

例外穷尽遂给 FULL 等号

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}=\{W_p,W_v\}.
$$

两个增益在七为零，漂移同为 $d_*$，两个完整目标不同。父、该 M 子片、BOTH 末 FULL 片及全部已服务共同祖先的非单点停止守卫保留。两个例外 J 测试不同，故这不是 SAME J 子片碰撞。

同历史 $\mathcal K\subseteq\mathcal K'$ 时，每个实际动作与 SAME 响应的片也包含。定义 $L_0$ 为至少两不同整个目标，$L_{h+1}$ 为父非单点且 EACH 动作有一个实际 FULL 子片满足 $L_h$。基底不同性随包含保持；归纳保留每动作原响应见证，对子片用包含和归纳假设，并保留父守卫。因此任意基数、有限深度失败向上保持，不服务早期未取得另一臂。

仅条件地，若剩余 SAME 父 SAME J child 实际有 x 碰撞对和 y 碰撞对，两对至多四完整端点，加 SAME 父坏 M 对，去重前至多六。各相应实际响应片含其原碰撞对，增加成员不删除碰撞；FULL 包含保留 BOTH 动作、两个末 duty、已服务祖先和 ALL 停止守卫。这是已实现失败的条件支持界，不是实现、一般子片基数、最小支持、尖锐性或根失败；不从非终端失败族擅自抽一对。

### 67.15. 精确剩余低响应目标与两个原 FULL 根

对 EVERY SAME 达到 $4a-1<m<m_H,n<0$ 父和 EVERY 实际 $\kappa<50m/7$，剩余对象是 (67.30) 的 ENTIRE exclusively ordinary 集合，具备 $1<q<2,6<s<11,1/3<\theta<1,0<\rho<7$、signed 分支 $(1,\phi)$ 与 $(z_Q,2)$、BOTH 原残式及 ALL SAME 七原行。上分支另有 $s<10,\rho<6$。

正完成 OPEN：证明每个这样的完整非空子片单点可停，或至少一个实际末函数 x、y 在 ENTIRE 子片单射，由已取得记录与完整预测选该动作，再由仅所选实际响应给整个 $P,g,d$ 的充要唯一逆。普通第七 J 的一般单射及子片基数也未由本卷证明。必要有界性、有限性、固定 q 唯一性或一对互补分离均不承担全称完成。如果这个低响应子片有实际普通对，则 N27 的第二端 $0<\rho<7<32$ 自动满足 (67.34) 的守卫；其 SAME $\kappa<50m/7<8m$ 及全部原过滤也已具备，所以 x 碰撞时 y 分离、y 碰撞时 x 分离。不同两对仍可分别碰撞，故这一条件对推论不改变 ENTIRE 全称义务。

负完成 OPEN：在 ONE SAME 达到父和 ONE SAME 已取得低响应内，实际构造

$$
U_1\ne V_1,\quad U_2\ne V_2,\qquad
x(U_1)=x(V_1),\quad y(U_2)=y(V_2),\qquad U_i,V_i\in\mathcal K_\kappa.
$$

两对可不同或重叠；每端必须有一个严格 P、一个整个非零 gain、一个 individually fixed d，BOTH 原 Q/C 和 ALL SAME 七行。还须保留 SAME 父坏 M FULL 对、两个末 FULL 片、BOTH 动作、全部已服务祖先和所有停止守卫。不同父、不同响应、投影点、分别可达最优值、单个碰撞或联合两坐标分点均不满足此共同 duty。本卷没有构造任何实际碰撞对。

低于 $m_H$ 的原 Q 隙弦不能移用上层正号。具体地置 $L_*=w/m,v_0=2z_Q+c,H_0=H(z_Q)<0$，由原 Q 及 ordinary 得

$$
\xi(q)=s-2q=2z_Q-3+L_*+\frac{A_0}{z_Q-q}-\frac{B_0}{2q+c},
\quad A_0=H_0(1+L_*/v_0)<0,\quad B_0=3cL_*/v_0>0.
$$

两个部分分式的分子恒等式为
$H=2(q+z_Q-1)(z_Q-q)+H_0$ 与
$H/[u(z_Q-q)]=1+H_0/[v_0(z_Q-q)]-3c/(v_0u)$；后式乘分母核对二次、一次、常数，用 $c^2=c+4$ 恢复 $H$。同支两端的有限差为

$$
\xi(r)-\xi(q)=(r-q)\left[\frac{A_0}{(z_Q-r)(z_Q-q)}+\frac{2B_0}{(2q+c)(2r+c)}\right].
$$

第一项负、第二项正，本文不赋总符号；中间点无需可行。这个未证符号不因有界化而自动解决。N26–N28 不预设任何有限枚举、一对实现或双碰撞实现。

其他既有 scoped 接口只按原条件保留，不作为本卷未给证明的全局认证：$m=m_H$ 的 N17–N18 及 $m>m_H$ 的全响应 ENTIRE 选择器；$n\ne0,\kappa=8m$；$\Gamma>0$；$\Gamma=0$ 的唯一仿射普通世界加两例外；$N=L+5A=0$ 的 $(p-2)(v-2)=17,p,v>2,p\ne v$ 两例外七 TOTAL 逆。$\Gamma=0$ 有 $n>0$，不能用本卷负 n 的导出真正二次排掉。$\mathsf B_0$ 保留其独立 scoped 接口，不认证未列完整证明。正 n 的另域也不由本卷完成；其符号、源区间和次序不作负 n 前提，已知类各自逆不成为未知并集逆。

**原 FULL 二次问题 OPEN。** ALL 严格源、ALL 整个非零次数至多二实增益、任意固定实漂移的确定性自适应八 TOTAL 完整恢复 versus 原根 $L_7$ 仍未结算。没有任意根策略强迫 $JMJMJ$ 前缀、早期未服务臂完成、不受限 SAME 父 $L_3$、原根失败树、minimax、必要第八读、尖锐性、最小支持或九读上界。

**原 FULL 三次问题 OPEN。** 整个次数至多三的八 TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$ 仍未结算。三次 gain 乘线性迹可为四次；四偶节点相等仍可留非零倍 $t(t-2)(t-4)(t-6)$。二次逆不检测隐藏三次、真实次数、根、方向或平面承诺。未知类并集恢复另需跨类证明。

### 67.16. 完整 INERT 同时实现合同

以下仅为继承的 INERT、UNEXECUTED、UNFULFILLED 符号规格。原 atomic-relation-generation-family 内容保持不透明，尺寸不是本卷生成或核算的读数。

保留 ALL 256 终叶槽 $\sigma=(w,e),w\in\{J,M\}^7,e\in\{0,1\}$，ALL 254 非空实际前缀 v，原长度 $i=1,\ldots,7$，其实际即时左乘积 $A_v$ 与 EVERY 后代。定义

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,it_v(P),i^2t_v(P),i^3t_v(P)).
$$

EACH 前缀的 EVERY 指定非代表后代 $\sigma$ 对 SAME 前缀代表 $\varrho$ 保留 WHOLE 行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\varrho)x_\varrho=0.
$$

ALL 行属于 ONE SAME 完整 $1538\times1024$ 关系，继承层规格 $254,252,248,240,224,192,128$ 全保留，作用于 ONE common stacked vector，含 ALL 256 整个四系数 gain 块。每块非零，每个适用 SAME-source 终叶的 WHOLE 四分量差 $x_{(w,0)}-x_{(w,1)}\ne0$。ALL 严格源、ALL 祖先关系、BOTH 动作 duty、ALL 停止守卫须对 SAME 向量、SAME 世界同时成立。

每槽自始固定

$$
g_\sigma(t)=\sum_{h=0}^3x_{\sigma,h}t^h,\qquad d_\sigma=a_0-x_{\sigma,0}
$$

跨该槽 ALL 原行使用。只合并整个 $P,g,d$ 相等槽；二次限制 $x_{\sigma,3}=0$ 同时作用于 ALL SAME 块。本卷局部分类、有界图谱、末对、条件六世界支持、选定支持、较小或投影关系、分臂或分路径解、遗漏后代、逐行 refit 或另选守卫向量，均不替代此共同实现。没有访问、生成、枚举、求解或探测该原实例，也没有履行合同的结论。

### 67.17. 严格边界、取消次序与证据上限

严格源始终 $q>0,s>2q$；声明父始终 $p,v>2a,p\ne v,\tau\ne0$。不补入 $q=0,s=2q,r_0=0$ 或一、$b=0,c_{\rm src}=0,p=2a,p=v,\tau=0$、极限或无限源。父条件不成为对无关原根父的全局限制。

两种 $\tau$ 符号、任意 $a_0$、各世界一个固定漂移完整保留。合法 $H=0,s=4,s=4q,b=1/2,r_0=1/2$、系数/样本/观察零、采样或非采样重根、次数取消、重复残式根和恒零次残式均保留到确切原式在声明域拒绝。普通真正二次与 $\theta>0,F>0$ 是原式结论；T1、N26–N28 的排除是证明，不是先删域。例外末零仍合法。非零 gain 贡献可以被固定漂移抵消为零观察。mH 奇异世界不以普通取消或极限替代。

取消先后为：插值只除固定非零整数；源逆用正 b,s；归一化只用 $\tau\ne0$ 而不用符号；普通先声明 $q\ne a$；u 正先于 eta；Kpos 正、Gamma 负先导出 theta 正，判别式先正才用根式。T1 仅在 $0<q\le5/4$ 先证明 H、N 正才用原 Q 比值；三次弦不除高次系数且先分端点括号符号。N19 平方的乘子及有限弦区间长度先正。低层 Q 分支先由原方程排 H 零和 q=zQ，再按已签名支除 H；N26 原常数先有 Bsrc 正，N27 下支先有 H 正；rho 的 theta 已正。N28 每次乘除用已正 u、rho、s。边界 regular 仅在 q≠phi 取消 phi−q，奇异 IVT 仅在有限 [4,12]；实际对只除正 ell、zeta、u、Kp，先证 Eg、Ng 正才除 rhoEg。不除 $5-\rho,s-4$、未知源/漂移差、未知响应、gain 样本、lambda、mu、源行列式、残式首项、根重数或未证判别式。

辅助弦端点、交叉点、正根图谱点、比值比较端点及 IVT 边界都不是实际世界，除非 ALL 原过滤同时成立。不假定一般位置、简单根、残式非退化、可行中间点、连续可行插值或有效有限枚举。严格界不声称可达尖锐性、普通存在、实际非单点、实际碰撞或第八读必要性。

全部数学为 fallible UNEXECUTED 符号推导。没有执行公式求值、代入程序、数值、导数、递推、数学枚举、CAS、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean 或 proof-kernel；没有 D5、Blueprint、Reg、摄入或消化。不给 kernel/数值认证、经验 ML/NN 或物理主张、噪声/稳定性/连续逆/有限精度保证、可计算性/有效决定/效率/复杂度/资源保证、一般 gain 空间逆或 gain 跨度下界、文献穷尽、外部原创性或优先权认证。文本字节、编码及结构检查只承担文本完整性。

## 追加锚（本行以下为增补区）
