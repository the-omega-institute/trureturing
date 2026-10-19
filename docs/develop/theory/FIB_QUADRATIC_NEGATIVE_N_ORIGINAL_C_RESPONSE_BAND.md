# FIB 负 n 父的原 C 不变量、响应带完整逆与全响应末增益正性

本卷独立为第 63 节。对象是实际五动作 $JMJMJ$ 后的严格 $\beta=7$ 父：严格正、秩一、迹一源，一个整个非零次数至多二实增益，以及跨该世界全部原行固定的任意实漂移。父参数满足 $n<0$。原奇插值常数 $C$ 给出正不变量 $(C-3D)/\tau$；它排除 $\kappa\le8m$ 内的全部普通 $q\le1$ 及 $4\le s\le6$，进一步给普通严格界 $\kappa<50m/7$。因此 EVERY 可达的闭带 $50m/7\le\kappa\le8m$ 取得记录有 ENTIRE 七 TOTAL 唯一逆。另在任意实际响应上证明普通归一化末增益严格正，并保留实际 $H=0$ 族。

闭带逆的全称量词以实际可达记录为域。一个明确 $p=5$ 族还证明带内确有实际记录；它不证明每个父或带内每个数值都可达。一般负 $n$ 的 ENTIRE 单末动作选择器在闭带外仍为 OPEN；原 FULL 二次与三次根问题也为 OPEN。

本文为 `repo-derived` 纯理论综合。多项式插值、因子定理、Vieta、有限割线与介值定理是复用工具；全部数学是 fallible UNEXECUTED 符号推导，不承担 Lean kernel、数值、外部原创性或优先权认证。

## 63. 原 C 的正性、完整排除与七 TOTAL 响应带

### 63.1. 同一个完整世界、原时钟与取得父

一个世界固定为

$$
W=(P,g,d),\quad P=\begin{pmatrix}r_0&b\\c_{\rm src}&1-r_0\end{pmatrix},\quad
0<r_0<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r_0(1-r_0),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
$$

四元严格正、迹一、行列式零，非零迹排除秩零。一个世界在所有行使用 SAME $P$、整个 $g$ 和一个固定 $d$。相等与去重只按整个三元组。原域保留常数、仿射、二次、两种尺度符号、各系数零、各样本零、观察零、采样或非采样根及重根；只预先排除整个零增益。

实际即时左动作、原时钟与响应为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+\operatorname{tr}(Q_iP)g(i).
$$

已服务 $JMJMJ$ 给原时钟 $0,\ldots,5$，SIX TOTAL；只选时钟六的 $J$ 取得 $z$，SEVEN TOTAL；若再选一个时钟七动作才是 EIGHT TOTAL。重复乘积使用新时钟样本。没有重置、复制、跳读、时钟平移、隐藏源/根/次数标签、逐行 refit、额外端口或未选响应输入。

由六个取得数置 $a_0=y_0,x_i=y_i-a_0$，令

$$
E(t)=Lt+At^2,\quad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
$$

这些式恢复偶节点 $0,2,4$ 和奇节点 $1,3,5$。两个次数至多二的候选之差有三个不同根，故恒零，证明唯一性。本文 $C$ 始终是这个 ORIGINAL 奇常数。

令

$$
a=\frac{\sqrt{17}-1}{4},\quad a^2+a/2=1,\quad \frac34<a<\frac45,
\quad U_0=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5).
$$

正数 $x$ 上 $x^2+x/2-1=(x-a)(x+a+1/2)$ 的符号给上述有理界。固定 ONE SAME 实际达到的严格父

$$
B+5D=a(L+5A),\quad \tau=\frac{D-aA}{3a}\ne0,\quad
\Lambda=\frac{C-15a\tau}{a-1},\quad
K=\Lambda+E+\tau U_0=\tau(t+p)(t+v)(t-7),
$$

$$
p\ne v,\quad p,v>2a,\quad Z=p+v=m+1,\quad V=pv=n+2m+15,\quad n=V-2Z-13<0.
$$

比较 $K$ 全部系数与父关系得到

$$
\begin{aligned}
A&=\tau m,&L&=\tau(n-5m),&\Lambda&=-7\tau V,\\
D&=a\tau(m+3),&B&=a\tau(n-5m-15),&C&=\tau\bar C,\\
\bar C&=7(1-a)V+15a.
\end{aligned}
$$

因为 $U_0-V_o=3t^2-15t+15$，逐系数还给整个父恒等式

$$
R=aE+a\tau(U_0-V_o)+(a-1)\Lambda.
$$

父的确切区域是

$$
m>4a-1,\qquad (2a-2)m+4a-19<n<\frac{m^2-6m-59}{4},\qquad n<0.
$$

等价地，$Z>4a$ 且 $2aZ-4a^2<V<Z^2/4$，再附 $n<0$。必要性来自 $p-2a,v-2a$ 的正和、正积及 $(p-v)^2>0$。反向这些不等式使移位二次式的判别式、根和、根积都正，故其两不同实根都正；移回即得 $p,v>2a$。代入 $Z=m+1,V=n+2m+15$ 并用 $4a^2=4-2a$ 给展开区域。63.4 的例外构造实际达到 EVERY 这样的父，任意 $a_0$、两种 $\tau\ne0$ 符号均可。特别 $m>0,V>4a^2>0$ 是达到父的事实。

### 63.2. 完整严格源双射、全部原行与双恒等式

整个严格源域双射于

$$
q=r_0/b>0,\quad s=2/b>2q,\quad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},\quad
j=b+c_{\rm src}=q+\frac{2(1-q^2)}s.
$$

正向 $s-2q=2(1-r_0)/b>0$，秩一强制 $c_{\rm src}$ 的显示逆式。反向四元正、迹一且 $bc_{\rm src}=r_0(1-r_0)$，并返回 $q,s$，故没有漏源。

对任意左乘积 $A_0$，直接相加两个对角元给

$$
\operatorname{tr}(A_0P)=(A_0)_{22}+[(A_0)_{11}-(A_0)_{22}]r_0
 +(A_0)_{21}b+(A_0)_{12}c_{\rm src}.
$$

左 $J$ 交换旧两行；左 $M$ 取旧第二行与旧两行之和。这些行恒等式给本卷需要的 ALL SAME 七原行：

$$
\begin{aligned}
d+g(0)&=a_0,\\
d+jg(1)&=a_0+R(1),\\
d+(1+b)g(2)&=a_0+E(2),\\
d+(j+r_0)g(3)&=a_0+R(3),\\
d+(1+2b)g(4)&=a_0+E(4),\\
d+(j+2r_0)g(5)&=a_0+R(5),\\
d+(1+2b)g(6)&=z.
\end{aligned}
$$

接取得 $J$ 后两个实际末迹分别为 $j+2r_0$ 与 $1+j+r_0+2b$。另一个时钟六动作 $M$ 的迹为 $1+3b$；接它的末迹为 $j+3r_0$ 与 $1+2r_0+4b+c_{\rm src}$。这些是同一固定世界的预测，未选者不作为输入。

记

$$
D_0=2-q-2q^2,\quad H=D_0+3q=2+2q-2q^2,\quad
e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,\quad T=\nu/s.
$$

e,o 在原偶、奇节点恰为相应实际迹。六原行当且仅当源严格、整个 $g\ne0$、$d=a_0-\lambda$ 且 BOTH 整个多项式恒等式

$$
-\lambda+eg=E+TU_0,\qquad -\lambda+og=R+qTV_o.
\tag{63.1}
$$

证明必要性：两节点差的三次系数分别为 $T,qT$，减去 $TU_0,qTV_o$ 后各剩次数至多二且有三个原不同节点根，故恒零。充分性是在相同节点求值。该论证不除任何样本，涵盖样本零与降次。

偶式完整升幂系数为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T).
$$

逐项可逆地给

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad d=a_0-sF_{\rm orig}.
$$

奇式左边完整系数为

$$
\big((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\big),
$$

右边为 $(C-15qT,B+23qT,D-9qT,qT)$。三次自动相同；其余 ALL 比较恰为

$$
\begin{aligned}
Q&=D-qA-HT=0,\\
L_{\rm res}&=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&=C-15qT-B_{\rm src}F_{\rm orig}=0,\quad B_{\rm src}=(q-1)s+D_0.
\end{aligned}
\tag{63.2}
$$

反向恢复这些比较即恢复整个奇式和全部原行。原 $C$ 及 $15qT$ 的项和符号不可更换。

### 63.3. 普通世界的全响应正根图谱与完整 converse

先声明普通 $q\ne a$，才令 $\delta=q-a\ne0$ 并作普通消去。置

$$
u=2q+2a+1>0,\quad \theta=T/\tau,\quad \eta=n/u<0,\quad
h=s+5-u=s-2q+4-2a>0.
$$

这里公式左边的 $u$ 是正源坐标，不是增益二次系数 $\nu$。由 $a$ 的方程得 $D_0=-\delta u,H=3q-\delta u$。原残式精确满足

$$
Q/\tau=3a-\delta m-H\theta,\quad
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}-5Q/\tau.
$$

所以 $Q=L_{\rm res}=0$ 当且仅当 $Q=0$ 且

$$
m=(s+1)\theta+\eta.
\tag{63.3}
$$

只取消已声明的 $\delta,\tau\ne0$。令

$$
\Gamma=n-(4a+1)m-6a<0.
$$

因 $u-(4a+1)=2\delta$，(63.3) 与 $Q$ 给

$$
\Gamma=-K_{\rm pos}\theta,\quad
K_{\rm pos}=u(s+1)+2H=u(s-2q+2a+1)+6q>0.
$$

故 $\theta>0$ 是原式的结论，包含 $H=0$。全部偶系数随后给

$$
F:=F_{\rm orig}/\tau=n-(s+5)m+(s+2)(s+4)\theta=3\theta-h\eta>0,
$$

$$
\lambda=s\tau F,\quad \mu=s\tau(\eta-5\theta),\quad \nu=s\tau\theta,\quad
 g(t)=s\tau[\theta t^2+(\eta-5\theta)t+F],\quad d=a_0-s\tau F.
\tag{63.4}
$$

普通真正二次及其系数符号是推论，没有作为原域附加承诺。

原时钟四与取得六 $J$ 的迹同为 $1+4/s$。同一个 gain 有 $g(6)-g(4)=2s\tau(5\theta+\eta)$。因此 SAME 第七原行 iff

$$
\kappa:=\frac{z-a_0-E(4)}{2\tau}
=(s+4)(5\theta+\eta)=(s+4)[m-(s-4)\theta]
=5m+15\theta+(s-1)\eta.
\tag{63.5}
$$

精确相减为

$$
\kappa-8m=(s-4)(\eta-3\theta),\qquad \eta-3\theta<0.
\tag{63.6}
$$

故 $\kappa<8m\iff s>4$，等号 iff $s=4$，$\kappa>8m\iff s<4$，特别 $\kappa\le8m\iff s\ge4$。没有除 $s-4$ 或样本。

对固定父与任意实 $\kappa$，先在 EVERY 辅助 $q>0$ 上置

$$
\eta=n/u,\quad b_\kappa=\kappa-5m+2\eta,\quad
\Delta=b_\kappa^2-60\eta(m-\eta)>b_\kappa^2,
$$

$$
\theta_\kappa(q)=\frac{b_\kappa+\sqrt\Delta}{30}>0,\qquad
s_\kappa(q)=\frac{m-\eta}{\theta_\kappa(q)}-1.
\tag{63.7}
$$

由 (63.3)、(63.5) 消去 $s$ 得

$$
15\theta^2-b_\kappa\theta+\eta(m-\eta)=0.
$$

常数负、$m-\eta>0$，判别式严格大于 $b_\kappa^2$，两根异号；(63.7) 是唯一正根，另一根严格负。辅助 $s$ 此时仅知 $s>-1$，不是实际世界。

精确集合 $S_\kappa$ 保留 ALL

$$
q>0,\quad q\ne a,\quad s_\kappa>2q,\quad
3a-(q-a)m-H\theta_\kappa=0,
$$

$$
\bar C-15q\theta_\kappa-[(q-1)s_\kappa+D_0](3\theta_\kappa-h\eta)=0.
\tag{63.8}
$$

**完整普通原世界 iff。** 任一实际普通七行世界由上面的必要性给 (63.7)、(63.8)。反向任一保留 $q$，用 $P(q,s)$、(63.4) 的整个 gain 和固定 $d$：严格源成立，首项 $s\tau\theta\ne0$。$s$ 的定义恢复 (63.3)，故恢复全部偶系数及 $L_{\rm res}$；$Q$ 恢复奇二次，untouched 常数恢复 $R_C$，奇三次自动相同。因此 BOTH (63.1) 及 ALL SAME 六原行成立。正根方程只除已证正 $\theta$ 就恢复 (63.5)，继而恢复 SAME 第七原行。反向全部偶系数迫正是这个整个 gain 与固定漂移，故同一个 $q$ 固定整个世界，不同 $q$ 给不同源。此 iff 保留 $H=0,s=4$；任何后述必要不等式都不替换 (63.8)。

### 63.4. 穷尽例外、实际达到与 ENTIRE 等号

在 $q=a$，$D_0=0,H=3a$。原 $Q$ 迫 $T=\tau$，原常数迫 $(a-1)\lambda=C-15a\tau$，所以 $\lambda=\Lambda$。偶恒等式为 $eg=K$；整个多项式 $g$ 要求 $K(-s)=0$。严格 $s>2a$ 只接受 $s=p,v$，正根七对应 $s=-7$ 不合法。因此全部例外恰为

$$
W_p=(P(a,p),\ p\tau(t+v)(t-7),\ d_*),\quad
W_v=(P(a,v),\ v\tau(t+p)(t-7),\ d_*),\quad d_*=a_0+7\tau V.
\tag{63.9}
$$

反向四元源正，二次首项 $p\tau$ 或 $v\tau$ 非零，常数 $\Lambda=-7\tau V$，漂移自始为同一 $d_*$。$eg=K,og=aK$ 与父恒等式给

$$
-\Lambda+eg=E+\tau U_0,\quad -\Lambda+og=R+a\tau V_o.
$$

故恢复每个奇偶系数、原 $C/15qT$ 与 ALL SAME 六原行。特别每个 63.1 的严格父都实际达到，不依赖普通存在。其共同六行可写为 $y_0=a_0$，偶 $i=2,4$ 时 $y_i=d_*+K(i)$，奇 $i=1,3,5$ 时 $y_i=d_*+aK(i)$；两世界各使用其原迹与整个 gain。

其实际取得响应与测试是

$$
z_p=d_*-\tau(p+4)(6+v),\quad z_v=d_*-\tau(v+4)(6+p),
$$

$$
\kappa_p=(p+4)(v+3),\quad \kappa_v=(v+4)(p+3),\quad
\kappa_p-\kappa_v=v-p\ne0,\quad z_p-z_v=2\tau(v-p)\ne0.
\tag{63.10}
$$

例外只在 SAME 实际 $\kappa$ 匹配其测试时才加入，至多一个。两 gain 在七为零；两个归一化末值均为 $48a$。

令 $\mathcal A_\kappa$ 为这个实际匹配例外集。由源双射的 $q=a/q\ne a$ 分割与两支完整 converse，

$$
\mathcal K_\kappa=\{W_\kappa(q):q\in S_\kappa\}\cup\mathcal A_\kappa
\tag{63.11}
$$

是 ENTIRE 七原行子片的等号。两种包含均已证明。允许普通集或匹配例外集为空；可达 iff 整个集合非空。空集绝非停止成功。

### 63.5. N10：达到父的正不变量与原 C 源约束

**定理 63.1。** 对每个严格达到父，$I=(C-3D)/\tau>0$；此父结论不需要 $n$ 的符号。对其每个实际普通负 $n$ 世界，在任意取得 $\kappa$ 上，

$$
G_C(q,s):=hB_{\rm src}+3q>0,\qquad
\rho_eG_C>3(s-q)>0,\quad \rho_e=-\eta/\theta>0.
\tag{63.12}
$$

证明。先有 $a<11/14$：$f(x)=x^2+x/2-1=(x-a)(x+a+1/2)$ 在 $11/14$ 等于 $1/98>0$，第二因子正。因此 $11-14a>0$、$37-42a>4>0$、$\epsilon=1-a>0$。由原父系数

$$
I=7\epsilon V-3aZ+9a.
$$

严格达到给 $W=(p-2a)(v-2a)=V-2aZ+4a^2>0$。以 $V=W+2aZ-4a^2$ 代换，并用 $a^2+a/2=1$，所有系数精确为

$$
I=7\epsilon W+a(11-14a)Z+a(37-42a)>0.
\tag{63.13}
$$

其中 $Z$ 系数是 $14a(1-a)-3a$，常数是 $9a-28(1-a)a^2$，分别化为显示系数；每项严格正，不添加任何父承诺。

实际普通的 untouched 原常数与原二次式分别给

$$
C/\tau=15q\theta+B_{\rm src}(3\theta-h\eta),\qquad
D/\tau=qm+H\theta.
$$

前者减三倍后者，用 SAME (63.3)，$\theta$ 系数是

$$
15q+3B_{\rm src}-3q(s+1)-3H=3(q-s),
$$

$\eta$ 系数是 $-hB_{\rm src}-3q$。故精确恒等式为

$$
I=3(q-s)\theta-G_C\eta.
\tag{63.14}
$$

这一步保留了原 $15qT$。严格源 $s>2q>0$、$\theta>0,\eta<0$ 使第一项严格负；若 $G_C\le0$，第二项非正，与 $I>0$ 矛盾。先证明 $G_C>0$，再除已正 $\theta$ 得 $I/\theta=\rho_eG_C-3(s-q)>0$。只有此后才可再除 $G_C$。源约束是实际必要条件，不替换 BOTH 原残式。∎

### 63.6. N11：完整排除低 q 与闭区间四至六

**定理 63.2。** ONE SAME 负 $n$ 父的每个实际普通 $\kappa\le8m$ 成员满足 $q>1,s>6$。

证明先用 (63.6) 得 $s\ge4$。若 $0<q\le1$，则 $q-1\le0$，

$$
B_{\rm src}\le4(q-1)+D_0=-2q^2+3q-2
=-2(q-3/4)^2-7/8\le-7/8.
$$

又 $h=s-2q+4-2a\ge6-2a>22/5$，$3q\le3$。负乘积方向给

$$
G_C=hB_{\rm src}+3q<-77/20+3=-17/20<0,
$$

与定理 63.1 矛盾。这里包括 $q=1$，而 $q=a$ 自始属于完整例外支，没有被普通消去。

余下反设 $4\le s\le6,q>1$。严格源给 $1<q<s/2\le3$。定义辅助多项式

$$
G_q(S)=(S-2q+4-2a)[(q-1)S+D_0]+3q.
$$

关于 $S$ 的二次系数是 $q-1>0$。对 $L<R,L\le S\le R$，精确有限弦式为

$$
G_q(S)=\frac{(R-S)G_q(L)+(S-L)G_q(R)}{R-L}
 -(q-1)(S-L)(R-S).
\tag{63.15}
$$

分母正，两端严格负就使整个闭区间严格负。辅助点不需要实际达到。

对 $1\le q\le2$，写 $x=q-1\in[0,1]$。全部端点系数为

$$
G_q(4)=2a-3+(2a-1)x+(4a-10)x^2+4x^3.
$$

先用 $x^3\le x^2$ 得上界 $2a-3+(2a-1)x+(4a-6)x^2$。因 $2a-1>0,4a-6<0$，舍去非正平方项再用 $x\le1$，得到 $G_q(4)\le4a-4<0$。

同一 $x$ 下

$$
G_q(6)=2a-5+(13-2a)x+(4a-18)x^2+4x^3\le-Q_x,
$$

$$
Q_x=(14-4a)x^2-(13-2a)x+5-2a.
$$

置 $A_6=14-4a>0$，精确平方恒等式是

$$
4A_6Q_x=[2A_6x-(13-2a)]^2+139-154a.
\tag{63.16}
$$

常数来自 $4A_6(5-2a)-(13-2a)^2=139-154a$，化简只用 $a^2+a/2=1$。$a<4/5$ 给 $139-154a>79/5>0$，所以 $Q_x>0,G_q(6)<0$，包含 $x=0,1$。

对 $2\le q\le3$，写 $y=q-2\in[0,1]$。全部系数是

$$
G_q(6)=4a-6+(6a-11)y+(4a-6)y^2+4y^3.
$$

先用 $y^3\le y^2$，上界为 $4a-6+(6a-11)y+(4a-2)y^2$。此时 $4a-2>0$，才用 $y^2\le y$，得

$$
G_q(6)\le4a-6+(10a-13)y<0.
$$

最后常数和一次系数均严格负；没有把负平方系数错误地替换为一次项。

对 $1<q\le2$，用长度二的 $[4,6]$ 弦，两端已严格负，故 $G_q(s)<0$。对 $2<q<3$，用长度 $6-2q>0$ 的 $[2q,6]$ 弦。辅助左端

$$
G_q(2q)=(4-2a)(2-3q)+3q=8-4a+(6a-9)q\le8a-10<0,
$$

因为 $6a-9<0,q\ge2$。右端由 $y$ 展开严格负。严格源使实际 $s\in(2q,6]$，故也有 $G_q(s)<0$。两种弦覆盖所有可能的 $q$，都与实际必要 $G_C>0$ 矛盾。于是 $s>6$，包含对 $s=4,6$ 的原式排除；没有删除源域或除 $H$。本证明没有导数、执行求值、数值、CAS、辅助点达到或尖锐性断言。∎

### 63.7. N12：严格响应界与 ENTIRE 七 TOTAL 完整逆

**定理 63.3。** 实际普通 $\kappa\le8m$ 必有 $\kappa<50m/7$。EVERY 实际可达的 SAME 闭带记录

$$
50m/7\le\kappa\le8m
\tag{63.17}
$$

的 ENTIRE 子片恰为唯一实际匹配例外；无需取得时钟七响应，SEVEN TOTAL 就恢复整个世界。

证明。普通定理 63.2 给 $s>6$。由未除的 SAME (63.3)、(63.5)，所有系数相减为

$$
\begin{aligned}
7\kappa-50m
&=7(s+4)(5\theta+\eta)-50[(s+1)\theta+\eta]\\
&=-15(s-6)\theta+(7s-22)\eta<0.
\end{aligned}
\tag{63.18}
$$

两项各严格负，因为 $s>6,\theta>0,\eta<0,7s-22>0$。只除正的七。该响应界只在 $\kappa\le8m$ 证明，不外推到 $\kappa>8m$。

对 (63.17)，(63.11) 的任何普通成员都违反严格界。例外实际测试互不相同，故至多一个匹配。实际可达性供应至少一个完整成员，因此恰有一个匹配例外，ENTIRE 子片是单点。这包含闭带两端，既不用空集成功，也不推定普通基数或普通存在。

取得记录上的 dispatch 如下。只用六原行插值 $E,R$，恢复 $a_0,\tau,\Lambda,K$，以 63.1 的全部系数、精确因子和严格区域识别声明的负 $n$ 父，恢复无序 $p,v$。选择时钟六 $J$ 并取得 $z$ 后才形成 SAME $\kappa$。若它在闭带，比较两个明确测试 (63.10)；在可达域恰一个匹配。若匹配 $\kappa_p$，返回 ALL 源元、ALL gain 系数及固定漂移

$$
P=\begin{pmatrix}2a/p&2/p\\a(1-2a/p)&1-2a/p\end{pmatrix},\quad
\lambda=-7\tau pv,\quad\mu=p\tau(v-7),\quad\nu=p\tau,\quad d=a_0+7\tau pv.
\tag{63.19}
$$

若匹配 $\kappa_v$，交换 $p,v$，明确返回

$$
P=\begin{pmatrix}2a/v&2/v\\a(1-2a/v)&1-2a/v\end{pmatrix},\quad
\lambda=-7\tau pv,\quad\mu=v\tau(p-7),\quad\nu=v\tau,\quad d=a_0+7\tau pv.
$$

两种 $\tau$ 符号合法，源四元严格正，整个 gain 非零。

逆的两个方向都在原世界成立。充分性由 $eg=K,og=aK$ 恢复 BOTH (63.1)、每个奇偶系数、原 $C/15qT$ 及上面 ALL SAME 六原行；实际匹配 (63.10) 恢复 SAME 第七原行。必要性由 ENTIRE (63.11) 排除普通后，只能是这个匹配例外，偶系数及例外必要性强制返回的每个 gain 系数与固定漂移。真实世界给存在，ENTIRE 单点性给唯一，根名交换不改变返回世界。至此在 SEVEN TOTAL 停，不取得任何末响应。

若两个测试都不匹配，则这份带记录在声明类中不可达，不是成功停止。定理是取得记录上的精确集合论逆，不声称有效可判定、可计算或任何枚举资源界；也不声称每个父能到带内、带内每值可达或 $50m/7$ 尖锐。∎

### 63.8. 一个实际带内族及其全部七行 converse

**定理 63.4。** 对 EVERY

$$
p=5,\quad 2a<v<5,\quad a_0\in\mathbb R,\quad\tau\ne0,
\tag{63.20}
$$

同一个父有一个严格带内例外记录和一个上端点例外记录，各在自己的实际子片具有定理 63.3 的完整逆。

证明。$5>2a,v>2a,p\ne v$；$Z=5+v,V=5v,m=v+4,n=3v-23<-8<0$。这是 63.1 严格根区域内的实际父，而非投影例。具体原系数为

$$
\begin{aligned}
A&=\tau(v+4),&L&=\tau(-2v-43),\\
D&=a\tau(v+7),&B&=a\tau(-2v-58),\\
C&=\tau[35(1-a)v+15a],&\Lambda&=-35\tau v,
\end{aligned}
$$

$$
K=\tau(t+5)(t+v)(t-7),\qquad B+5D=a(L+5A).
$$

两个完整世界分别为

$$
\begin{aligned}
P_5&=\begin{pmatrix}2a/5&2/5\\a(1-2a/5)&1-2a/5\end{pmatrix},&
g_5(t)&=5\tau(t+v)(t-7),\\
P_v&=\begin{pmatrix}2a/v&2/v\\a(1-2a/v)&1-2a/v\end{pmatrix},&
g_v(t)&=v\tau(t+5)(t-7),
\end{aligned}
$$

二者漂移各自固定为 SAME $d_*=a_0+35\tau v$。源严格、迹一、秩一；gain 系数分别是 $(-35\tau v,5\tau(v-7),5\tau)$ 与 $(-35\tau v,-2v\tau,v\tau)$，首项均非零。对各自源的 $e,o$，有 $eg=K,og=aK$，所以 BOTH 整个恒等式及全部原系数成立，特别原常数没有改动。具体 SAME 六行是

$$
\begin{aligned}
y_0&=a_0,\\
y_1&=a_0+\tau[35v-36a(1+v)],\\
y_2&=a_0+\tau[35v-35(2+v)],\\
y_3&=a_0+\tau[35v-32a(3+v)],\\
y_4&=a_0+\tau[35v-27(4+v)],\\
y_5&=a_0+\tau[35v-20a(5+v)].
\end{aligned}
\tag{63.21}
$$

每行都由其一个固定 $P,g,d_*$ 的原迹得到。第七原行分别是

$$
z_5=d_*-9\tau(v+6),\quad z_v=d_*-11\tau(v+4),\quad
\kappa_5=9(v+3),\quad\kappa_v=8(v+4)=8m.
\tag{63.22}
$$

它们来自原迹 $1+4/5$ 与 $1+4/v$ 及 SAME gain 在六的值，也等于 $a_0+E(4)+2\tau\kappa_i$，故是真正取得响应。

严格带不等式是

$$
7\kappa_5-50m=13v-11>26a-11>0,\qquad
\kappa_5-8m=v-5<0.
$$

其中 $a>3/4$ 已足以给 $26a-11>0$。另一世界 $\kappa_v=8m>50m/7$，因为 $m>0$。两个测试差 $v-5\ne0$。因此同父有两个不同实际带记录，各完整 ENTIRE 子片由定理 63.3 为对应单例。

反向若原七行世界符合这个父及任一指定 (63.22) 带记录，定理 63.3 和例外穷尽迫它等于显示的对应世界；ALL 源元、整个 gain 系数和固定 $d_*$ 因而也被强制。这补足该族的整个原世界 converse。其量词是 (63.20) 的父及这两个响应，不是每个父、每个带值或下端点达到，也不是响应界尖锐性。两个不同响应不能充作 SAME 子片碰撞。∎

### 63.9. N13：任意响应的普通末增益正性

定义普通末归一化量

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta
=32\theta+n+\eta+5m-\kappa.
\tag{63.23}
$$

先给所用两个原式桥梁的完整证明。

对 $q\le3a-1$，令 $\rho_e=-\eta/\theta>0$。$m/\theta=s+1-\rho_e>0$ 给 $\rho_e<s+1$。若 $h\ge7$，则 $\omega=17\theta+(7-h)\eta>0$。若 $h<7$，$c=u+2-s=7-h>0$，故

$$
\omega/\theta=17-c\rho_e>17-c(s+1),\quad
c(s+1)=\frac{(u+3)^2}{4}-\left[s-\frac{u+1}{2}\right]^2.
$$

因 $u+3\le2(4a+1)$ 且 $(4a+1)^2=17$，右边乘积至多十七；前一严格号仍给 $\omega>0$，包括平方为零的端点。这是 bounded N6，任意 $\kappa$、$H=0$ 均无除法问题。特别 $3a-1>5/4$。

另一个桥梁直接来自原 $C$。偶重建且 $Q=L_{\rm res}=0$ 时，奇差 $-\lambda+og-R-qTV_o$ 仅余常数 $-R_C$。在七减去偶恒等式，使用 $K(7)=0$ 与父 $R$ 恒等式给

$$
E(7)=-\Lambda-105\tau,\qquad R(7)=-\Lambda-48a\tau.
$$

因此精确取向为

$$
R_C/\tau=C_7-(105-48q)\theta-B_7\omega,\quad C_7=105-48a>0,
$$

$$
B_7=(q-1)(s+7)+D_0=(q-1)(h+2a)-1
=(q-1)(s-2q)+4q-5.
\tag{63.24}
$$

这仍是原常数及 $15qT$，不是替代残式。

**定理 63.5。** EVERY 实际普通负 $n$ 世界在任意实际取得 $\kappa$ 上有 $\omega>0$，含 $H=0$ 和两种 $\tau$ 符号。例外仍有 $g(7)=0$。

证明。$q\le5/4$ 由 N6 完整覆盖。$q\ge5/4$ 时先用严格 $\xi=s-2q>0$ 得

$$
B_7=(q-1)\xi+4q-5>0.
$$

这包含 $q=5/4$，其第二项为零但第一项严格正。

若 $\theta\ge1$，用 ORIGINAL 偶恒等式在七，而非猜测常数符号。$E(7)/\tau=7V-105$、$\lambda/\tau=sF$ 给

$$
(s+7)\omega=sF+7V+105(\theta-1)>0.
\tag{63.25}
$$

$s,F,V>0$，最后项非负，且 $s+7>0$，故 $\omega>0$，包括 $\theta=1$。

若 $0<\theta<1$，用 (63.24) 的原取向

$$
B_7\omega=C_7-A_C\theta,\qquad A_C=105-48q.
$$

若 $A_C>0$，$\theta<1$ 给右边 $>C_7-A_C=48(q-a)>0$；若 $A_C=0$，右边正是 $C_7>0$；若 $A_C<0$，右边 $>C_7>0$。已证 $B_7>0$，所以各情形 $\omega>0$。低 $q$ 与两种 $\theta$ 情形穷尽所有实际普通，因为全域已从原式推出 $\theta>0$。证明从未使用 $\kappa\le8m$，也未除 $H$。∎

普通实际 $g(7)$ 的符号因此为 $\tau$ 的符号，绝不推出漂移或带漂移观察值的符号。由原奇恒等式和两个实际末迹，

$$
f_{JJ}=a_0+R(7)+\tau x,\quad f_{JM}=a_0+R(7)+\tau y,
$$

$$
x=48q\theta-2q\omega,\quad y=48q\theta+(s+4-4q)\omega,\quad
 y-x=(s+4-2q)\omega>0.
\tag{63.26}
$$

这里 $o(7)g(7)=\lambda+R(7)+48qT$，$JJ$ 迹为 $o(7)-2q/s$，$JM$ 比它多 $(s+4-2q)/s$，证明全部公式。共同偏移是取得量 $a_0+R(7)$，不是逐候选重设的 $d$。负 $\tau$ 反转实际顺序但保持相等与分离。若普通与匹配例外在 $J$ 碰撞 $x=48a$，其 $y>48a$；若在 $M$ 碰撞 $y=48a$，则 $x<48a$。这只分离该点对的另一个动作，不证明整个较大子片有一个统一单射动作。

### 63.10. 实际 H 零族的完整保留与推出的更强界

令

$$
\phi=(1+\sqrt5)/2,\quad\chi=\phi-1,\quad
H(q)=2(\phi-q)(q+\chi),\quad
m_H=\frac{3a}{\phi-a}=2(a+\chi),\quad Z_H=m_H+1.
$$

$\phi^2=\phi+1,\phi\chi=1$ 给因子式，唯一正零点是 $\phi$。$H(a)=3a$ 给 $3a=2(\phi-a)(a+\chi)$，证明两种 $m_H$ 表达式。$Q$ 在 $H=0$ 必迫 $m=m_H$，不能除去这个分支。

对 EVERY

$$
V\in I_H=(2aZ_H-4a^2,Z_H^2/4),\quad n=V-2m_H-15,
$$

移位根 converse 给严格达到父。由 $3/2<\phi<5/3,3/4<a<4/5$，

$$
5/2<m_H<3,\quad7/2<Z_H<4,\quad Z_H>4a,\quad |I_H|=(Z_H-4a)^2/4>0,
$$

$$
9/4<V<4,\quad-75/4<n<-16,\quad72/5<\bar C<19,\quad
11/2<u_H=2\phi+2a+1<6,\quad-4<\eta=n/u_H<-8/3.
$$

在 $s\ge2\phi$ 置

$$
\theta(s)=\frac{m_H-\eta}{s+1}>0,\quad h=s+5-u_H,\quad B_H=\chi s-3\phi,
$$

$$
R_H(s)=15\phi\theta+B_H(3\theta-h\eta)-\bar C=-R_C/\tau.
$$

$Q$ 直接成立，$\theta$ 定义恢复 ordinary；保留原常数 $R_H=0$。在辅助边界 $2\phi$，预测常数为

$$
\alpha_Hm_H+\eta[(3\phi-2)(4-2a)-\alpha_H],\quad
\alpha_H=\frac{6(\phi+1)}{2\phi+1}<4.
$$

第一乘积 $(3\phi-2)(4-2a)>6$，方括号正，故预测常数 $<12<\bar C$，所以 $R_H(2\phi)<0$。边界不是世界。

在四，$\theta_4<7/5,h_4=9-u_H>3,B_H(4)=\phi-4$，从而

$$
R_H(4)=(18\phi-12)\theta_4+(4-\phi)h_4\eta-\bar C
<126/5-56/3-72/5=54/5-56/3<0.
$$

方向来自 $0<18\phi-12<18,4-\phi>7/3,-\eta>8/3$。

精确改写为

$$
R_H(s)=c_Hs^2+b_Hs+d_H+\frac{A_H}{s+1},
$$

$$
\begin{aligned}
c_H&=-\eta\chi>0,& A_H&=3(m_H-\eta)(\phi+1)>0,\\
b_H&=-\eta[\chi(5-u_H)-3\phi],&
d_H&=3(m_H-\eta)\chi+3\eta\phi(5-u_H)-\bar C.
\end{aligned}
$$

有限 $S$ 取大于 $4,1,2|b_H|/c_H,\sqrt{2(|d_H|+1)/c_H}$，即有 $R_H(S)>0$。有限区间 $[4,S]$ 的 IVT 给 $s_H>4$。对 $2\phi\le x<y<z$，连续弦斜率之差恰为

$$
(z-x)\left\{\frac{A_H}{(x+1)(y+1)(z+1)}-\eta\chi\right\}>0.
$$

二次贡献是 $c_H(z-x)$，倒数项弦为 $-A_H/[(x+1)(y+1)]$，仿射项抵消，证明这个式子。若有两严格根，取 $x=2\phi,y,z$ 为两根，边界到首根斜率正、两根间斜率零，与严格增长矛盾。因此整个严格源射线只有这个根。

在根处，固定 $P=P(\phi,s_H)$，用 (63.4) 的全部系数与固定 $d$。严格源、非零首项、ordinary、$Q$ 和 untouched 原 $C$ 全部成立，故 63.2 的系数 converse 给 BOTH 恒等式和 ALL SAME 六行。实际第七响应定义为

$$
\kappa_H=(s_H+4)(5\theta+\eta),\quad z_H=a_0+E(4)+2\tau\kappa_H;
$$

(63.5) 证明它恰是这个世界原时钟六的取得响应。反向任何实际 $H=0$ 世界必 $q=\phi,m=m_H,V\in I_H$，ordinary 迫 $\theta(s)$，原常数迫 $R_H=0$，唯一根与偶系数迫整个显示世界。这是完整世界 iff，不是必要源投影。

原有界 $\kappa_H-8m_H=(s_H-4)(\eta-3\theta)<0$；因此定理 63.2、63.3 进一步给

$$
s_H>6,\qquad \kappa_H<50m_H/7.
$$

这两个更强界只经已证一般定理推出。实际族保留。因 $p,v<Z_H<4$，例外测试满足

$$
\kappa_p-8m_H=(p-4)(v-5)>0,\quad
\kappa_v-8m_H=(v-4)(p-5)>0.
$$

故这些父在 ANY $\kappa\le8m_H$ 子片都没有匹配例外，但其 ENTIRE 普通集仍须完整保留。另一个 SAME 六行普通支不曾被证明共享 $\kappa_H$；这里没有普通碰撞、单点子片或统一选择器结论。

### 63.11. 保留 BOTH 原 Q/C 的精确有序对 iff

为明确剩余问题，给出所用 N9 关系的全套过滤与双向原行桥梁。固定 ONE SAME 严格达到 $a_0,\tau,m,n<0$ 父与 SAME $\kappa\le8m$。取 $0<q<r,q,r\ne a,\ell=r-q>0,s\ge4,\rho>0,t>0$；本节 $t=\theta_2$，不是原时钟。定义

$$
\begin{aligned}
u&=2q+2a+1>0,&U&=2r+2a+1=u+2\ell>0,\\
K_p&=15+(s+1)\rho>0,&L_p&=s-1+\rho>0,\\
D_p&=uK_p>0,&R_p&=2\rho/D_p>0,\quad V_p=s^2-16\ge0,\\
S&=s+\ell R_pV_p,&\alpha&=R_pL_p,\quad\beta=R_pK_p=2\rho/u,\\
M_p&=S+1-\rho.
\end{aligned}
$$

两端为

$$
(q_1,s_1,\theta_1,\eta_1)=(q,s,t(1+\ell\alpha),-\rho tU/u),\quad
(q_2,s_2,\theta_2,\eta_2)=(r,S,t,-\rho t).
$$

ALL 必需过滤是

$$
s>2q,\quad S>2r,\quad tM_p=m,\quad-U\rho t=n,\quad(S+4)(5-\rho)t=\kappa,
$$

$$
t[(r-a)M_p+H(r)]=3a,\qquad M_p=H(q)\alpha+2(q+r-1),
$$

$$
C_i:=\bar C-15q_i\theta_i-[(q_i-1)s_i+D_0(q_i)]F_i=0\quad(i=1,2),
\quad h_i=s_i+5-(2q_i+2a+1),\quad F_i=3\theta_i-h_i\eta_i.
\tag{63.27}
$$

同时保留原父严格区域与 SAME $a_0,\tau$。两 $Q$ 是方程，即使某个 $H$ 为零；两 ORIGINAL $C_i$ 分别施加，不以末比较替换。

必要性证明。任一实际不同普通对由固定 $q$ 刚性可排序 $q<r$。取 $s=s_1,t=\theta_2,\rho=-\eta_2/t$。SAME $n$ 给 $\beta=(\eta_2-\eta_1)/(\ell t)=2\rho/u$。暂不假设 $\alpha=(\theta_1-\theta_2)/(\ell t)$ 的符号，令 $k_s=(s_2-s_1)/\ell$。SAME $m,\kappa$ 的精确差给

$$
k_s=(s+1)\alpha-\beta,\quad k_s(5-\rho)=(s+4)(5\alpha-\beta).
$$

不除 $5-\rho$，消去得 $\alpha K_p=\beta L_p$。$K_p,L_p,u,\beta>0$，故 $\alpha=R_pL_p>0$，且 $k_s=R_p[(s+1)L_p-K_p]=R_pV_p$，恢复全部参数。第二端给 SAME 参数过滤与其 $Q$；两 $Q$ 相减用 $H(q)-H(r)=2\ell(q+r-1)$，只除 $\ell t>0$，得另一个 $Q$ 过滤。每端原常数当然必需。

充分性证明。$u\eta_1=U\eta_2=n$；恒等式 $(s+1)\alpha-\beta=R_pV_p$ 给两端相同 $m$。又

$$
5\alpha-\beta=R_p(s-4)(5-\rho),\quad S-s=\ell R_p(s-4)(s+4)
$$

恢复两端相同 (63.5)，含 $s=4,5-\rho=0,\kappa=0$，没有除它们。第二端 $Q$ 与反向差恢复 BOTH $Q$，两常数各在。逐端重建 $P(q_i,s_i)$、整个 $g_i(z)=s_i\tau[\theta_i z^2+(\eta_i-5\theta_i)z+F_i]$、固定 $d_i=a_0-s_i\tau F_i$。两源严格，首项非零；SAME $m,n$ 恢复全部偶系数与 $L_{\rm res}$，$Q,C_i$ 恢复全部奇系数及 untouched $C/15qT$。BOTH 整个恒等式恢复 ALL SAME 六行，取得式恢复 SAME 第七行。不同 $q,r$ 给不同完整源。因此这是精确 original-world pair iff。

末有限比较定义为

$$
\begin{aligned}
B_p&=8L_p-K_p=8s-23+(7-s)\rho,\\
C_p&=32L_p-K_p=32s-47+(31-s)\rho,\quad A_p=s+4-4q,\\
W_p^{\rm pol}&=D_p[17+(s-U-2)\rho]+2\ell\rho^2V_p,\\
P_J&=D_p[7+(U+2-s)\rho]-2\ell\rho^2V_p+2q\rho B_p,\\
P_M&=48D_p^2-(96q\rho L_p+2A_p\rho C_p)D_p
 +(2\rho V_p-4D_p)W_p^{\rm pol}.
\end{aligned}
$$

此 $W_p^{\rm pol}$ 不是例外世界。令 $w_2=\omega_2/t=17+(S-U-2)\rho=W_p^{\rm pol}/D_p$；SAME 子片给 $\omega_1/t=w_2+\ell(32\alpha-\beta)$。直接有限相减 (63.26) 得

$$
\frac{x_2-x_1}{2\ell t}=24-w_2+q(8\alpha-\beta)=P_J/D_p,
$$

$$
\frac{y_2-y_1}{\ell t}=48-48q\alpha+(R_pV_p-4)w_2-A_p(32\alpha-\beta)=P_M/D_p^2.
$$

后式用 $A_2-A_1=\ell(R_pV_p-4)$；代入 $\alpha=2\rho L_p/D_p$、$32\alpha-\beta=2\rho C_p/D_p$ 即逐项恢复 $P_M$。$\ell,t,D_p>0$，所以 WITH ALL (63.27)，$P_J=0$ iff 该实际普通对 $J$ 碰撞，$P_M=0$ iff 该对 $M$ 碰撞。没有全过滤的多项式零点不是世界。

定理 63.2、63.3 使任何实际该对进一步满足

$$
1<q<r,\quad s>6,\quad S>s,\quad\kappa<50m/7,
$$

$$
G_C(q_i,s_i)>0,\quad(-\eta_i/\theta_i)G_C(q_i,s_i)>3(s_i-q_i).
$$

$S>s$ 来自 $\ell R_p(s^2-16)>0$。定理 63.5 还给

$$
W_p^{\rm pol}>0,\qquad W_p^{\rm pol}+2\ell\rho C_p>0,
$$

它们分别等于 $D_p\omega_2/t,D_p\omega_1/t$。没有假定 $B_p,C_p$ 的符号，也没有替换任何 SAME $m,n,\kappa$、BOTH $Q$、BOTH original $C$ 或 strict source 过滤。$P_J$ 在整个存活关系的非零或正性仍未证明，亦未构造通过全部过滤的碰撞元组。正 $\omega$ 不给 $w_2<24$ 或另一弦项符号。

### 63.12. 旧局部接口与剩余 ENTIRE 选择器的精确范围

旧 $q<1$ 普通 $J$ 单射及其部分 ENTIRE guard，和旧 $s=4/\kappa=8m$ 普通接口，各在原声明范围内仍有效。对本卷 SAME 严格负 $n$ 父的 $\kappa\le8m$ 目标，定理 63.2 证明其普通域实际为空；在可达 $\kappa=8m$ 处只有匹配例外。这是原式证明的加强，不是把旧 scoped 选择器改判为假，也不把旧低 $q$ guard 当作任意响应的全称 guard。

闭带以外，特别 $\kappa<50m/7$ 与 $\kappa>8m$，一般负 $n$ ENTIRE 单动作恢复仍为 OPEN。正完成义务是：对 EVERY 声明达到父和 EVERY 可达 SAME 取得子片，证明单点可停，或至少一个实际末函数 $x$、$y$ 在 ENTIRE (63.11) 单射；只由取得数据和完整预测选动作。

若另有已证取得 guard 保证该单射，选其动作，只取得它在原时钟七的实际响应 $f$，归一化 $(f-a_0-R(7))/\tau$，保留所选 $x$ 或 $y$ 等于该值的完整候选。真实世界给存在，ENTIRE 单射给唯一；63.3、63.4 的 converse 恢复 BOTH 恒等式与 ALL SAME 七行，所选末等式恢复第八原行。单点在七 TOTAL 停；空集永不成功。这是条件集合论逆，不是无条件 dispatch 或有效求解承诺。

负完成义务仍要求 ONE SAME 达到父、ONE SAME 实际取得 $\kappa$ 的 ENTIRE 子片包含

$$
U_1\ne V_1,\quad U_2\ne V_2,\quad x(U_1)=x(V_1),\quad y(U_2)=y(V_2).
$$

两对可不同或重叠，均须 SAME 严格源、整个非零 gain、各自固定漂移、BOTH 原残式及 ALL SAME 七行。普通/例外混合碰撞只在实际匹配例外存在时才分别测试 $x=48a,y=48a$。其点对方向已有 63.9，但没有全域排除或共同实现。一个碰撞、SAME 六行多重性、不同父或不同 $\kappa$、有限基数、固定 $q$ 刚性、正 $\omega$、单个点对两坐标分离，都不代替 ENTIRE 单函数单射或两对共同碰撞。

其他已知类的 $\Gamma>0,\Gamma=0,N=0$ 与单独 $\mathsf B_0$ 接口只保留原假设。$\Gamma=0$ 的唯一仿射普通世界在不同的 $n>0$ 范围，不被本卷导出的真正二次结论删除；$N=0$ 的两例外轨迹 $(p-2)(v-2)=17,p,v>2,p\ne v$ 是另一范围。正 $n$ 的符号、源区间、选择器或历史范围以外 OPEN 语句均不作为本卷负 $n$ 证明或当前项目全域状态。没有跨类证明时，已知各类逆不构成未知并集逆。既有 at-most-six ENTIRE 子片基数界与下面的条件支持界不同，二者都不单独证明注入、实现或尖锐性。

### 63.13. SAME 父坏 M 的 FULL 等号与包含逻辑

在 SAME 父，原 $M$ 六迹为 $e(6)$，偶恒等式给

$$
h_M=a_0+E(6)+48T,\quad z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
$$

这是实际响应，完整子片恰要求 $T=\tau$。证明 FULL 等号需要排除 ALL 普通 $T=\tau$，不能只排除末零 gain。

反设普通 $\theta=1$。原 $Q$ 给 $\delta(u-m-3)=0$，所以 $u=Z+2,q=(Z+1)/2-a,\delta>1/2$。令 $h_o=s-Z+7>8-2a>6$，ordinary 与全部偶系数给

$$
V=(7-h_o)Z+23-2h_o,\quad g=s\tau(t^2-h_ot+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-9/2)^2+11/4>0.
$$

ORIGINAL 常数是 $(a-1)(-7V)-15\delta=B_{\rm src}\chi_o$。减去 $(a-1)s\chi_o$，用 $D_0=-\delta(Z+2)$ 及

$$
(h_o-9)\chi_o+15=(h_o-4)(h_o-6)(h_o-8)
$$

精确得到

$$
-7V=s\chi_o-\frac{\delta(h_o-4)(h_o-6)(h_o-8)}{1-a}.
$$

负左边、正 $s\chi_o,\delta$ 和 $h_o>6$ 迫 $h_o>8$。$V>4a^2,Z>4a$ 与上面 $V$ 方程给 $V<23+28a-(4a+2)h_o$，所以

$$
h_o<\frac{19+30a}{4a+2}<17/2.
$$

末比较由 $4a-2>0$。在 $8<h_o<17/2$，正三因子积 $<45/8$，$\chi_o>15$ 因为 $\chi_o-15=(h_o-8)(h_o-1)>0$，且 $1-a>1/5$。故该积除 $(1-a)\chi_o$ 小于 $15/8$。$0<\delta<q<s/2$ 使原常数反而迫 $-7V>s\chi_o/16>0$，矛盾。此证明保持原 $15\delta$，不要求 $\tau>0$。

两例外都有 $T=\tau$，因此 FULL 等号为

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}
=\{W_p,W_v\}.
$$

两整个 gain 在七为零，各漂移固定 $d_*$。不同完整目标保留在父、这个 $M$ 子片、BOTH 末 FULL 片及 ALL 已服务共同祖先中，所有对应非单点停止守卫都保留。两例外的取得 $J$ 响应不同，故这不是 SAME $J$ 子片碰撞，也不服务较早未取得的另一臂。

同历史 $K\subseteq K'$ 的每个实际 $E,z$ 片都包含于相应 FULL 片。定义 $L_0$ 为至少两个不同完整目标，$L_{h+1}$ 为父非单点且 EACH 动作有一个实际 FULL 响应子片满足 $L_h$。基步不同性随包含保持；归纳保留每动作原见证响应，利用片包含及子片归纳假设，同时保留父守卫。于是任意基数、每个有限深度失败向上保持，BOTH 动作和全部相关已服务守卫完整保留。

条件地，若某个 SAME 取得 $J$ 子片实际具备两末碰撞 duty，可各取一实际点对，至多四个完整端点；加入 SAME 父坏 $M$ 对至多再两端。并集在相应实际响应片包含每原碰撞；FULL 包含保留 BOTH 末片、BOTH 动作及 ALL 相关祖先/停止守卫。这只是已实现局部失败的 at-most-six SUPPORT，不证明实现、最小支持、尖锐性、非终端抽对或原根树。

### 63.14. 原根 OPEN 与完整 INERT 共同实现合同

FULL 严格源、整个非零次数至多二、任意固定漂移的确定性自适应 EIGHT TOTAL 恢复 versus 原根 $L_7$，仍为 OPEN。FULL 次数至多三 EIGHT TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$ 也仍为 OPEN。没有任意根策略被强迫进入 $JMJMJ$、早期未服务臂完成、不受限 SAME 父 $L_3$、根失败树、minimax、八读必要性或九读上界。三次 gain 乘线性迹可为四次；四偶节点相等仍可留非零倍 $t(t-2)(t-4)(t-6)$。本二次逆不检测隐藏三次次数或给未知类并集逆。

以下保留完整 INERT、UNEXECUTED、UNFULFILLED 合同；原 atomic-relation-generation-family 内容保持不透明。ALL 256 终叶槽 $\sigma=(w,e),w\in\{J,M\}^7,e\in\{0,1\}$，ALL 254 非空实际前缀 $v$，长度 $i=1,\ldots,7$，其实际即时左乘积 $A_v$ 与 EVERY 后代共同受约束。令

$$
t_v(P)=\operatorname{tr}(A_vP),\quad
\ell_v(P)=(t_v(P)-1,it_v(P),i^2t_v(P),i^3t_v(P)).
$$

对 EVERY 前缀的 EVERY 指定非代表后代 $\sigma$ 及 SAME 前缀代表 $\rho$，保留 WHOLE 行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0
$$

在 ONE SAME 完整 $1538\times1024$ 关系中，继承层规格为 $254,252,248,240,224,192,128$。ONE common stacked vector 包含 ALL 256 WHOLE 四系数 gain 块；每个整个块非零，每个适用 SAME-source 终叶的 WHOLE 四分量差 $x_{(w,0)}-x_{(w,1)}$ 非零。ALL strict sources、ALL ancestors、BOTH action duties、ALL stopguards 须对 SAME 向量与 SAME 世界同时成立。

每槽自始固定 $g_\sigma(t)=\sum_{h=0}^3x_{\sigma,h}t^h$ 与 $d_\sigma=a_0-x_{\sigma,0}$，跨该槽 ALL 原行不变。只合并 ENTIRE $P,g,d$ 相等的槽。二次限制 $x_{\sigma,3}=0$ 同时作用于 ALL SAME 块。尺寸是继承符号规格，不是执行计数或认证。任何局部源不等式、响应带逆、有序对 iff、终端对、条件六端支持、较小关系、选定支持、分臂或分路径解、遗漏后代、独立守卫向量或逐行 refit 都不履行这个共同实现。

### 63.15. 严格边界、除法与证据上限

始终 $q>0,s>2q,p,v>2a,p\ne v,\tau\ne0$。$q=0,s=2q,r_0=0,1,b=0,c_{\rm src}=0,p=2a,p=v,\tau=0$、无限或极限源不补作世界。父条件只限声明的二例外类，不加给其他原模型父。辅助弦端点、IVT 边界、有限大 $S$、无穷极限、根式辅助点均不是实际世界，除非通过全部原过滤。

两种 $\tau$ 符号、任意 $a_0$、每个世界的固定实漂移、合法 $H=0,s=4,s=4q,b=1/2,r_0=1/2$、各系数/样本/观察零、采样或非采样及重复 gain 根、残式降次、重根或恒零，均保留至原式拒绝。本卷在指定普通 $\kappa\le8m$ 域以原 $C$ 证明拒绝 $q\le1,4\le s\le6$，没有把它们设为非法源承诺。普通真正二次由原式推出，例外保留合法末零。固定漂移可把非零 gain 贡献抵消为零观察。

除法顺序为：插值只除固定非零整数；源逆只除 $b,s>0$；父归一化只除已声明 $\tau\ne0,a>0,a-1\ne0$；普通先声明 $q-a\ne0$；$u>0$ 先于 $\eta$；$K_{\rm pos}>0,\Gamma<0$ 先推出 $\theta>0$，再用正根与 $\rho_e$。判别式先严格正才用根式。先证明 $I>0,G_C>0$ 才除后者。弦长、$A_6$、所有符号在其不等式替换前已证。$B_7>0$ 只在指定高 $q$ 部分使用，不全域相除。$H$ 从未全域相除；$s-4,5-\rho$ 在 pair iff 中不除。H 族的 $s+1,u_H,c_H$ 及各弦分母先正。没有取消未知样本、源/漂移差、gain 样本、$\lambda,\mu$、源行列式、残式首项、重数或未证判别式。

这些是 fallible UNEXECUTED 符号数学。没有执行公式求值或代入、数值、导数、递推、枚举、CAS、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean 或 kernel 验证；没有 D5、Blueprint、Reg、摄入或消化。不给 ML/NN、物理、噪声、稳定性、连续逆、有限精度、可计算性、有效决策、效率、复杂度、资源、文献穷尽、外部原创性或优先权认证。没有普通碰撞元组、两对共同实现、普通多重性、响应界尖锐性、最小支持或原根结算的断言。文本完整性检查只证明字节、编码与结构。

## 追加锚（本行以下为增补区）
