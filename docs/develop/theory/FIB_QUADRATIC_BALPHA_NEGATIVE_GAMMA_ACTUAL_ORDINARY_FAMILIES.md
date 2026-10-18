# FIB 二次负 Γ 父的完整联合图谱与实际普通世界族

本卷独立为第 54 节。在原实际五动作 $JMJMJ$ 后取得的六次 TOTAL 记录上，研究严格正、秩一、迹一源、整个非零次数至多二实增益及任意固定实漂移的 ENTIRE 父。本文给出负 $\Gamma$、$N\ne0$ 普通世界的未除联合充要图谱，保留 $H=0$ 与 $s=4$；构造所有 $V\in I_H$ 上唯一的 $H=0,N/\tau<0$ 实际普通分支；除一个明确非零三次式的至多三个零点外，在 SAME 六读父再构造不同的普通世界；并在 EVERY 达到的 $\Gamma=0$ 基点附近构造 $\Gamma<0,N/\tau>0$ 的实际普通扰动。

这些是整个原世界的存在、分类与同父关系，不是只有必要符号的源条带。SAME 六读父不等于 SAME 取得 J 子片：固定父须同时固定 $a_0,\tau,m,n$，固定 J 子片还须固定 SAME $k$。两普通世界的构造没有令其 k 相等，也没有构造任何末碰撞。负 $\Gamma$ 上 EVERY 可达 ENTIRE SAME-k 子片的单末函数选择器，以及一个 SAME 子片内两实际末函数分别碰撞的共同实现，均为 OPEN。

本文是 `repo-derived` 理论综合。插值、因子定理、次数根数、Vieta、严格秩一代数与介值定理是复用工具。正 $\Gamma$ 的 ENTIRE 至多八 TOTAL 恢复、$\Gamma=0$ 的三世界恢复、$N=0$ 的七 TOTAL 恢复及一般普通末零排除在其确切范围内保留。以下数学全部是 fallible UNEXECUTED 符号推导，不是 kernel、数值或外部原创性认证。

## 54. 负 Γ 的完整原行图谱、实际族与 SAME-k 边界

### 54.1. 原完整世界、实际时钟与 FULL 集合

一个世界自始固定为

$$
W=(P,g,d),\qquad P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),
$$

$$
g(x)=\lambda+\mu x+\nu x^2\in\mathbb R[x]\setminus\{0\},\qquad d\in\mathbb R.
\tag{54.1}
$$

四源元严格正、迹一且行列式零；非零迹排除秩零，故秩恰一。相等和去重仅按整个 $P,g,d$。原域包含常数、非恒定仿射、真正二次、两种增益尺度符号、全部合法系数零、样本与观察零、采样或非采样根及重根。两对角侧、对称与非对称源及无界正非对角元均在。d 是跨全部行的一个固定实数。

实际即时左动作与原时钟读数是

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{54.2}
$$

相加 QP 的对角元给

$$
\operatorname{tr}(QP)=Q_{22}+(Q_{11}-Q_{22})r+Q_{21}b+Q_{12}c.
$$

左下元乘 b。左 J 交换旧两行；左 M 取旧第二行与旧两行之和。这些行恒等式给下列原响应，记 $j=b+c$：

| 原时钟与实际动作 | 实际响应 |
| --- | --- |
| $0$ | $d+g(0)$ |
| $1,J$ | $d+jg(1)$ |
| $2,M$ | $d+(1+b)g(2)$ |
| $3,J$ | $d+(j+r)g(3)$ |
| $4,M$ | $d+(1+2b)g(4)$ |
| $5,J$ | $d+(j+2r)g(5)$ |
| $6,J$ | $h_J=d+(1+2b)g(6)$ |
| $7,J$ 接 J | $f_{JJ}=d+(j+2r)g(7)$ |
| $7,M$ 接 J | $f_{JM}=d+(j+r+1+2b)g(7)$ |
| $6,M$ | $h_M=d+(1+3b)g(6)$ |
| $7,J$ 接 M | $f_{MJ}=d+(j+3r)g(7)$ |
| $7,M$ 接 M | $f_{MM}=d+(1+2r+4b+c)g(7)$ |

$JMJMJ$ 后原时钟零至五是六次 TOTAL。只选一个原时钟六动作取得第七次 TOTAL，至多再选一个原时钟七末动作取得第八次 TOTAL。重复乘积仍用新时钟样本。未选响应仅为同一固定世界的预测，不是取得输入。没有重置、复制、跳读、时钟平移、额外端口、隐藏源/根/次数标签或逐行 refit。

令 $\mathcal S(\mathcal H_5)$ 为满足取得六行 $\mathcal H_5=(y_0,\ldots,y_5)$ 的 ALL (54.1) 世界。对实际动作 E 与响应 z，

$$
\mathcal K_{6,E,z}=\{W\in\mathcal S(\mathcal H_5):h_E(W)=z\}.
\tag{54.3}
$$

这是 FULL 定义。可达恰指非空，不假设有限、孤立、一般位置或已知真实次数。

### 54.2. 全部原系数与六行的必要且充分基底

由取得数据置 $a_0=y_0,x_i=y_i-a_0$，定义

$$
E(x)=Lx+Ax^2,\quad R(x)=Dx^2+Bx+C,
$$

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
\tag{54.4}
$$

代回分别恢复偶节点零、二、四及奇节点一、三、五；两个次数至多二的候选之差有三个不同根即恒零，故唯一。C 始终是原奇插值常数。

整个严格源域与下列开域双射：

$$
q=r/b>0,\quad s=2/b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},\quad
j=q+\frac{2(1-q^2)}s.
\tag{54.5}
$$

正向 $s-2q=2(1-r)/b>0$，秩一强制 c 的逆式。反向四元正、迹一、$bc=r(1-r)$ 且返回原 q,s。故 $s=4$ 和 $s=4q$ 也完整保留。

记

$$
D_0=2-q-2q^2,\quad H=D_0+3q=2+2q-2q^2,\quad
e(x)=1+x/s,\quad o(x)=qe(x)+D_0/s,\quad T=\nu/s,
$$

$$
U=x(x-2)(x-4)=x^3-6x^2+8x,\qquad
V_o=(x-1)(x-3)(x-5)=x^3-9x^2+23x-15.
\tag{54.6}
$$

e,o 在各原偶、奇节点恰为实际迹。

**引理 54.1（完整原行逆）。** 六原行当且仅当源严格、整个 g 非零、$d=a_0-\lambda$ 且 BOTH 整个多项式恒等式

$$
-\lambda+eg=E+TU,\qquad -\lambda+og=R+qTV_o.
\tag{54.7}
$$

全部偶系数可逆重建为

$$
\nu=sT,\quad\mu=sA-sT(s+6),\quad
F=\lambda/s=L-sA+T(s+2)(s+4),\quad\lambda=sF,\quad d=a_0-sF.
\tag{54.8}
$$

保留的全部奇非自动残式是

$$
\begin{aligned}
Q&:=D-qA-HT=0,\\
L_{\rm res}&:=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&:=C-15qT-B_{\rm src}F=0,\qquad B_{\rm src}=(q-1)s+D_0.
\end{aligned}
\tag{54.9}
$$

证明。初读固定 d。$-\lambda+eg-E$ 有三个偶根和三次系数 T；减 TU 后次数至多二且仍有三个根，故恒零。奇支同理。反向在原节点取值恢复六行，包括 gain 样本零。

偶式左右的完整升幂系数是

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T).
$$

逆解恰给 (54.8)。奇式左升幂系数为

$$
\left((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\right),
$$

右边为 $(C-15qT,B+23qT,D-9qT,qT)$。三次自动相同；二次给 $D-9qT=q(A-6T)+D_0T$；一次给 $B+23qT=q(L+8T)+D_0[A-T(s+6)]$；常数恰给原 $R_C=0$。这正是 (54.9)。反向逐系数恢复 BOTH 恒等式，故充分性是完整世界的充分性。没有除 H、T 或样本。∎

置

$$
a=\alpha=\frac{\sqrt{17}-1}{4},\quad a^2+a/2=1,\quad \frac34<a<\frac45,
$$

$$
\Sigma:\ B+5D=a(L+5A),\qquad \tau=\frac{D-aA}{3a},\qquad N=L+5A.
\tag{54.10}
$$

正数 x 的 $x^2+x/2-1=(x-a)(x+a+1/2)$ 给所用严格界。在 Σ 上 $D=aA+3a\tau,B=aL-15a\tau$。ordinary 仅指 $q\ne a$。置 $\delta=q-a\ne0,u=2q+2a+1>0$，则 $D_0=-\delta u,H=3q-\delta u$。保留 Q=0 时，原一次式可逆地等价于

$$
N=u[A-(s+1)T].
\tag{54.11}
$$

具体地 Q 给 $3(a\tau-qT)=\delta(A-uT)$；一次式两边分别为 $-\delta(N-5uT)$ 与 $-\delta u[A-(s+6)T]$。仅取消已非零 δ 即得 (54.11)，逆向同样成立。故普通六行完整 iff 为：严格源、整个 g 非零、偶重建、(54.11)、BOTH Q=0 与 untouched $R_C=0$。任何必要源条带均不替代这两个原残式。

### 54.3. 达到的 β=7 父、全部例外与固定父数据

取全部

$$
p\ne v,\qquad p,v>2a,\qquad \tau\ne0,\qquad a_0\in\mathbb R.
\tag{54.12}
$$

令

$$
Z=p+v,\quad V=pv,\quad m=Z-1>0,\quad n=N/\tau=V-2Z-13,
$$

$$
\Lambda=-7\tau V,\quad d_*=a_0+7\tau V,\quad K=\tau(x+p)(x+v)(x-7),
$$

$$
\begin{aligned}
A&=\tau m,&L&=\tau(V-7Z-8),\\
D&=a\tau(Z+2),&B&=a\tau(V-7Z-23),\\
C&=\tau[7(1-a)V+15a],&\Gamma&=V-(4a+3)Z-12-2a.
\end{aligned}
\tag{54.13}
$$

展开全部系数给

$$
K=\Lambda+E+\tau U,\qquad
R=aE+a\tau(U-V_o)+(a-1)\Lambda.
\tag{54.14}
$$

在 q=a，Q 迫 T=τ，原常数迫 λ=Λ，故 eg=K。严格源要求 $-s<-2a$ 是 K 的根，恰有 -p,-v 两选择。全部例外因此恰为

$$
W_p:\quad P_p=P(a,p),\quad g_p=p\tau(x+v)(x-7),\quad d_p=d_*;
\qquad W_v:\ p,v\text{ 交换}.
\tag{54.15}
$$

反向 p>2a 给四元正、迹一、秩一，首项 pτ 非零；egp=K、ogp=aK 及 (54.14) 恢复 BOTH 恒等式和全部原系数。逐行共同响应为

$$
\begin{aligned}
y_0&=a_0,\\
y_1&=a_0+\tau[7V-6a(1+p)(1+v)],\\
y_2&=a_0+\tau[7V-5(2+p)(2+v)],\\
y_3&=a_0+\tau[7V-4a(3+p)(3+v)],\\
y_4&=a_0+\tau[7V-3(4+p)(4+v)],\\
y_5&=a_0+\tau[7V-2a(5+p)(5+v)].
\end{aligned}
\tag{54.16}
$$

这是每组参数的实际六读父达到证明。两个 b 不同，世界不同；常数 gain 因 A=τm≠0 已由偶式排除。普通世界是否存在不参与父达到的前提。全部实际 $\mathsf B_\alpha$ 标志的既有穷尽恰为 (54.12)、β=7；下文使用这一精确族，不把部分普通过滤设置成标志。

固定一个取得父即固定其 $a_0,\tau,m,n$，从而固定 $Z=m+1,V=n+2m+15$ 和全部 (54.13)。这些量不随该父的候选变化；p,v 的交换只换名字。例外的实际 J 响应是

$$
z_p=d_*-\tau(p+4)(6+v),\quad z_v=d_*-\tau(v+4)(6+p),\quad
z_p-z_v=2\tau(v-p)\ne0.
\tag{54.17}
$$

故 SAME J 子片至多匹配一个例外。

### 54.4. 首项符号、整个 gain 与原常数的未除表达

由 (54.11) 减去 2D 与 $(2a+1)A$，并用 Q=0，A 系数因 u=2q+2a+1 消去，得到

$$
\tau\Gamma=-[u(s+1)+2H]T=-K_{\rm pos}T,\qquad
K_{\rm pos}=u(s-2q+2a+1)+6q>0.
\tag{54.18}
$$

正性只用 q>0、s>2q、a>0。故负 Γ 上 EVERY 实际普通世界有 $\theta:=T/\tau>0$，$\nu=s\tau\theta\ne0$，真正二次是结论而非次数承诺。

令

$$
\eta=n/u,\qquad h=s+5-u=s-2q+4-2a>4-2a.
$$

ordinary 给 $m=(s+1)\theta+\eta$，全部偶系数给

$$
\frac\mu{s\tau}=\eta-5\theta,\qquad F/\tau=3\theta-h\eta,
\qquad \frac{g(x)}{s\tau}=\theta(x^2-5x+3)+\eta(x-h),
$$

$$
\omega:=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta.
\tag{54.19}
$$

证明完整系数：置 ζ=N/u，$A=(s+1)T+\zeta,L=-5(s+1)T+(u-5)\zeta$。偶 F 中 T 系数为 $-5(s+1)-s(s+1)+(s+2)(s+4)=3$，ζ 系数为 u−5−s=−h，故 F=3T−hζ，μ/s=ζ−5T。没有除 θ、η 或样本，也没有假定它们的附加符号。

记

$$
B_7=(q-1)(s+7)+D_0=(q-1)(h+2a)-1,\quad
C_7=105-48a,\quad A_7=17B_7+105-48q.
$$

对任何偶重建且 Q=$L_{\rm res}$=0 的普通元组，奇整个差的唯一剩余系数为常数 $-R_C$。在七将其与偶式比较，先有 $-R_C=E(7)-R(7)+(105-48q)T+B_7\Omega$，其中 Ω=g(7)/s。再使用 (54.14) 给的 $E(7)=-\Lambda-105\tau,R(7)=-\Lambda-48a\tau$，得到精确恒等式

$$
\frac{R_C}\tau=C_7-(105-48q)\theta-B_7\omega
=C_7-A_7\theta-B_7(7-h)\eta.
\tag{54.20}
$$

这是 untouched 原 C 的恒等式，包含原 $15qT$ 的贡献；不是替代投影。下文的 $R_H,R_G,R_b$ 均等于 **$-R_C/\tau$**，不等于 $R_C/\tau$。

### 54.5. 新未除联合图谱：整个类的双向充要性

**定理 54.2（完整联合图谱）。** 取 ALL 实 $q,h,\theta,\eta$ 满足

$$
q>0,\quad q\ne a,\quad h>4-2a,\quad\theta>0,
\qquad u=2q+2a+1,\quad\delta=q-a,\quad s=h+u-5,
$$

$$
\delta\eta+[\delta(h-4)+3q]\theta=3a,\qquad
A_7\theta+B_7(7-h)\eta=C_7.
\tag{54.21}
$$

不解系数行列式，保留这两个方程。定义

$$
m=(h+u-4)\theta+\eta,\quad n=u\eta,\quad Z=m+1,\quad V=n+2m+15,
$$

并保留 ALL 严格过滤

$$
n\ne0,\qquad Z>4a,\qquad Z^2-4V>0,\qquad V-2aZ+4a^2>0.
\tag{54.22}
$$

然后取

$$
p=\frac{Z+\sqrt{Z^2-4V}}2,\qquad v=\frac{Z-\sqrt{Z^2-4V}}2,
\tag{54.23}
$$

或交换，选任意非零 τ、任意实 a0，以 (54.13)、T=τθ、(54.8) 与 P(q,s) 重建整个世界。所得列表恰为 EVERY 达到的 $\Gamma<0,N\ne0$ 父的 ENTIRE 普通世界，连同其父参数。

证明严格性。判别式先由过滤证明正，才取根式。两移位根 p−2a、v−2a 的和 Z−4a 正、积 V−2aZ+4a² 正，故二者都正；反向不同 p,v>2a 也恰给这些过滤。源有 s−2q=h+2a−4>0，故 s>0、P 严格。θ>0 和 τ≠0 给 ν≠0，整个 gain 合法。

证明充分性。将 m=(s+1)θ+η 代入归一化 ORIGINAL 二次式

$$
\delta m+H\theta=3a
$$

恰得 (54.21) 第一式，因为 H=3q−δu。n=uη 恢复 ordinary (54.11)，Q 与其可逆性恢复原一次式。第二式由 (54.20) 恰恢复 untouched $R_C=0$，即完整原常数

$$
C-15qT=[(q-1)s+D_0]F.
$$

全部偶系数由 (54.8) 恢复，奇三次自动相同；引理 54.1 给 BOTH 恒等式和每条原六行。这是同一个固定 P、整个 g、固定 d 的原行充分性。同父的 Wp,Wv 由 54.3 实际存在。再用 (54.18) 得 Γ=−Kposθ<0，n≠0 恰给 N≠0。

证明必要性。任一该域实际普通世界由源双射给 q,s，由 (54.18) 给 θ>0，由 (54.19) 给 h,η,m,n 的全部定义，由 Q 和 untouched 原常数给两联合方程；其已达到根参数给全部严格过滤。故没有遗漏任何实际普通分支。

固定 SAME 取得父时，必须额外令 $a_0,\tau,m,n$ 等于它的固定取得值；固定 SAME J 子片还须附 54.9 的 SAME k 方程。自由变化这些量的类图谱不是固定子片关系。联合图谱不除 H、s−4、η、θ 或系数行列式；奇异线性系统、消去的系数、恒零方程都仍作方程。H=0 直接在内；s=4 恰为 h=9−u，也直接在内。不假设解有限或孤立。∎

### 54.6. 新 H=0、N/τ<0 的实际族与整个分支唯一性

令

$$
\phi=\frac{1+\sqrt5}{2},\quad\chi=\phi-1=1/\phi,\quad
H(q)=2(\phi-q)(q+\chi),
$$

$$
m_H=2(a+\chi)=\frac{3a}{\phi-a},\qquad Z_H=m_H+1.
\tag{54.24}
$$

最后等式由 H(a)=3a 与因子式得来，φ−a>0。界 $3/2<\phi<5/3$、$3/4<a<4/5$ 给 $5/2<m_H<3$、$7/2<Z_H<4$ 及 ZH>4a。严格非空开区间为

$$
I_H=\left(2aZ_H-4a^2,\ \frac{Z_H^2}{4}\right),\qquad
|I_H|=\frac{(Z_H-4a)^2}{4}>0.
\tag{54.25}
$$

**定理 54.3（所有 V 的实际 H 零分支）。** 对 EVERY $V\in I_H$、任意 τ≠0、a0 实，取 Z=ZH、m=mH，按 (54.23) 得 p,v。该父存在且恰有一个 H=0 普通世界。

先有不同 p,v>2a。由区间得 $9/4<V<4$，因 $V>2aZ_H-4a^2>4a^2>9/4$。故

$$
-\frac{75}{4}<n=V-2m_H-15<-16,\quad q_0:=D/A=a+3a/m_H=\phi,
$$

$$
\frac{72}{5}<\bar C:=7(1-a)V+15a<19.
\tag{54.26}
$$

Cbar 的下界由 1−a>1/5、V>9/4、a>3/4，及上界由 1−a<1/4、V<4、a<4/5 给出。n<0 与 $\Gamma=n-2D/\tau-(2a+1)m_H$、D/τ=φmH>0 给 Γ<0。

固定此 ONE 父的 $u_H=2\phi+2a+1>0,\eta=n/u_H<0$。对全部 $s\ge2\phi$ 定义

$$
\theta(s)=\frac{m_H-\eta}{s+1}>0,\quad h(s)=s+5-u_H,\quad
B(s)=(\phi-1)s-3\phi,\quad \bar F(s)=3\theta(s)-h(s)\eta,
$$

$$
R_H(s)=15\phi\theta(s)+B(s)\bar F(s)-\bar C=-R_C/\tau.
\tag{54.27}
$$

Q=0 不需除 H：D=φA、H(φ)=0。θ 的定义恢复 ordinary。只剩原常数 $R_H=0$。边界 s0=2φ 仅用于符号，不作世界。

在 s0，B=2−3φ、h0=4−2a，预测常数为

$$
\alpha_H m_H+\eta[(3\phi-2)h_0-\alpha_H],\qquad
\alpha_H=\frac{6(\phi+1)}{2\phi+1}<4.
$$

这里 (3φ−2)h0>6，故方括号大于 6−4>0。η<0、mH<3 使预测常数小于 12，而 Cbar>72/5>12，故 $R_H(2\phi)<0$。

s+1>0 给整个区间连续。精确改写为

$$
\begin{aligned}
R_H(s)={}&3(m_H-\eta)(\phi-1)
+\frac{3(m_H-\eta)(\phi+1)}{s+1}\\
&-\eta[(\phi-1)s-3\phi](s+5-u_H)-\bar C.
\end{aligned}
\tag{54.28}
$$

二次首项 −η(φ−1)>0，故趋正无穷。于是存在有限 S>2φ 使 RH(S)>0，介值定理在有限闭区间给根 sH>2φ。无穷不是端点世界。

还须证明唯一。对 $2\phi\le x<y<z$，连续两割线斜率之差恰为

$$
\frac{R_H(z)-R_H(y)}{z-y}-\frac{R_H(y)-R_H(x)}{y-x}
=(z-x)\left\{\frac{3(m_H-\eta)(\phi+1)}{(x+1)(y+1)(z+1)}-\eta(\phi-1)\right\}>0.
\tag{54.29}
$$

若边界右侧有两根，取 x=2φ、y,z 为这两根，则第一条边界到根割线斜率严格正，后一条根到根斜率零，与 (54.29) 矛盾。因此 sH 唯一；未使用导数或执行根计算。

在 sH 固定

$$
q=\phi,\quad T=\tau\theta(s_H),\quad F=\tau\bar F(s_H),\quad
\lambda=s_HF,\quad\mu=s_H\tau(\eta-5\theta),\quad\nu=s_H\tau\theta,\quad d=a_0-\lambda.
\tag{54.30}
$$

P=P(φ,sH) 严格，ν≠0。L/τ=n−5mH 及 mH=(s+1)θ+η 使 F/τ=3θ−hη 恰为 (54.8) 的 F；故全部偶系数恢复。Q 直接成立，ordinary 恢复原奇一次，RH=0 恢复原 C−15qT=BsrcF。BOTH 整个恒等式恢复 SAME (54.16) 每条原行，而不是只恢复归一化参数。

反向任一 H=0 严格普通世界必 q=φ，因为 H 另一根 −χ 为负；其 ordinary 式必给 θ(s)，常数必给 RH(s)=0。因此唯一 sH 穷尽此 ONE 父的 ENTIRE H=0 分支。其他 q 分支未被排除。所得实际世界有 q=q0=φ>1、η<0、θ>0、$F/\tau=3\theta-h\eta>0$、$\mu/(s\tau)=\eta-5\theta<0$，其中 h>4−2a>0。全负 Γ 普通排除、全域 H>0 或 η>0 的断言因而不成立；不从这些系数符号推出末碰撞。∎

### 54.7. 新 SAME 父第二普通世界与明确三次例外集

保持定理 54.3 中 ONE 父的 $a_0,\tau,m=m_H,n,V$ 全部不变。对 EVERY 实 $q\ge1$ 定义

$$
u=2q+2a+1,\quad\theta_q=\frac{m}{2(q+\chi)}>0,\quad\eta_q=\frac nu<0,
$$

$$
s_q=\frac{m-\eta_q}{\theta_q}-1,\quad h_q=s_q+5-u,
$$

$$
R_G(q)=15q\theta_q+[(q-1)s_q+D_0(q)](3\theta_q-h_q\eta_q)-\bar C=-R_C/\tau.
\tag{54.31}
$$

各分母 q+χ、u、m、θq 均严格正。因为 m(φ−a)=3a，归一化 Q 因式为

$$
(\phi-q)[m-2(q+\chi)\theta_q]=0.
$$

它在 q=φ 也直接成立，不取消 φ−q。又

$$
s_q-2q=2\chi-1-\frac{2(q+\chi)n}{um}>0,
\tag{54.32}
$$

因为 χ>1/2、n<0。q≥1>a 保证普通，θ 定义恢复 ordinary 及全部偶系数。因此 R_G 的任一零点，由 ORIGINAL 常数和引理 54.1 给这个 SAME 父的实际完整普通世界。

**引理 54.4（边界负与无穷正）。** $R_G(1)<0$ 且 $\lim_{q\to+\infty}R_G(q)>0$。

证明 q=1。令 ε=1−a，则 1/5<ε<1/4、$2\epsilon^2-5\epsilon+1=0$、ε(3+2a)=1。原 Q 给 $\theta=(3a-\epsilon m)/2>0$，u=1/ε，h=s+2ε，$\eta=m-(h+1-2\epsilon)\theta<0$。将 V=uη+2m+15 代入 untouched 常数并 regroup，得精确等式

$$
R_G(1)=(h-7)\eta-20\epsilon m-105\epsilon+3a.
\tag{54.33}
$$

若 h≥7，首项非正，其余之和严格负。若 h<7，写成 $mD(h)+E(h)$，其中

$$
D(h)=(h-7)\left[1+\frac\epsilon2(h+1-2\epsilon)\right]-20\epsilon<0,
$$

$$
E(h)=\frac{3a}{2}(7-h)(h+1-2\epsilon)-105\epsilon+3a.
$$

源严格给 h>2+2ε，D 中括号为正。由

$$
(7-h)(h+1-2\epsilon)=(4-\epsilon)^2-(h-3-\epsilon)^2
$$

及 ε 的二次关系，

$$
E(h)\le\frac{177-951\epsilon}{8}<0.
$$

最后严格号用 ε>1/5。故所有情形 RG(1)<0，包括 h=7。

证明无穷端。置 ℓ=−n/m>16/3。由显示的有理表达式，

$$
h_q\longrightarrow h_\infty=2\chi+3-2a+\ell>0,\qquad
\frac{(q-1)s_q+D_0(q)}q\longrightarrow b_\infty=2\chi-4+\ell>\frac73.
$$

同时 qθq→m/2、qηq→n/2，故

$$
\lim R_G(q)=\frac{15m}{2}+\frac{b_\infty(3m-h_\infty n)}2-\bar C
>11m-\bar C>\frac{17}{2}>0.
\tag{54.34}
$$

只用了 m>5/2、n<0、Cbar<19；这是符号有理极限。连续性与正极限给有限 qU>1 的正值，介值定理在 [1,qU] 给至少一个 qG>1 的零点。不声称根唯一，也不把无穷源补入。∎

**定理 54.5（除至多三个 V 外的实际同父普通多重性）。** 置

$$
\theta_b=\frac{m_H}{2(\phi+\chi)},\quad
\eta_b=\frac{V-2m_H-15}{u_H},\quad
s_b=\frac{m_H-\eta_b}{\theta_b}-1,\quad h_b=s_b+5-u_H,
$$

$$
\Phi_H(V)=15\phi\theta_b+[(\phi-1)s_b-3\phi](3\theta_b-h_b\eta_b)
-[7(1-a)V+15a].
\tag{54.35}
$$

这是明确三次多项式，其首项系数为

$$
-\frac{\phi-1}{u_H^3\theta_b^2}\ne0.
\tag{54.36}
$$

证明：θb 为独立于 V 的正数；ηb 的 V 一次系数为 1/uH，sb,hb 为 −1/(uHθb)。因此 B 项一次首项乘 F 项二次首项恰给 (54.36)，其余项次数较低。非零三次式至多三个实零点，不能填满非空开 IH。对 EVERY $V\in I_H$ 且 $\Phi_H(V)\ne0$，引理 54.4 的零点 qG 不可能等于 φ，因为 RG(φ)=ΦH(V)。所以 H(qG)≠0，它与定理 54.3 唯一 H=0 世界的 q 不同，整个目标不同。

两世界保持 SAME a0、τ、m、n、V，分别由完整偶重建、Q、ordinary 和原常数恢复 BOTH 恒等式及 SAME 全部六原行；每个都有一个严格 P、一个整个非零二次 gain、一个固定 d。因而这是实际同父多重性，不是必要条带相交。被排除的至多三个 V 上不作第二世界断言。

但各端的原 J 行仍分别为

$$
\frac k\tau=(s+4)[m-(s-4)\theta].
\tag{54.37}
$$

本文没有证明这两个端点的值相等。故既未证明 SAME-k 多重性，也未证明 ordinary J 非单射、X 或 Y 碰撞、终端非单射或局部两动作失败。∎

### 54.8. 新 EVERY Γ 零基点附近的正 N 实际负 Γ 扰动

令

$$
\gamma=4a+3,\quad\eta_{\rm aff}=12+2a,\quad
\kappa_{\rm aff}=\gamma^2+\eta_{\rm aff}>0.
$$

**引理 54.6（全部基点的完整参数与逆）。** 不同接受根 p0,v0>2a 的 Γ0=0 基点，恰在交换意义下为

$$
p_0=\gamma+w,\quad v_0=\gamma+\kappa_{\rm aff}/w,
\qquad w>0,\quad w^2\ne\kappa_{\rm aff}.
\tag{54.38}
$$

证明。Γ0=0 等价于 $(p_0-\gamma)(v_0-\gamma)=\kappa_{\rm aff}$。两移位因子同号且非零。若均负，接受根界使其乘积小于 $(\gamma-2a)^2<\kappa_{\rm aff}$，矛盾；后一不等式由 γ>2a>0、ηaff>0 给出。因此二者正，取 w=p0−γ 得显示参数，p0≠v0 恰为 w²≠κaff。反向这些式直接给接受根、不同性和 Γ0=0。故量词是 EVERY 基点，不是一个示例。∎

固定任一这样的基点，任意 τ≠0、a0 实。令

$$
Z_0=p_0+v_0,\quad V_0=p_0v_0,\quad m_0=Z_0-1,\quad n_0=V_0-2Z_0-13,
\quad q_b=a+\frac{3a}{m_0},\quad u_b=2q_b+2a+1.
$$

Γ0=0 的坐标给 n0=ubm0>0。又 $V_0=\gamma Z_0+\eta_{\rm aff}>6Z_0$、V0≤Z0²/4 给 Z0>24，故

$$
a<q_b<\frac{104}{115}<1,\qquad H(q_b)>0.
\tag{54.39}
$$

先建立实际仿射基点。对 h>7 令 $B_{7,b}(h)=(q_b-1)(h+2a)-1<0$。函数

$$
m_0[(1-q_b)(h+2a)+1](h-7)
\tag{54.40}
$$

在七为零，h>7 两正因子随 h 增加，第二个严格增加，故严格增加、连续且无界。C7>0，介值定理与严格单调性给唯一 h0>7 使它等于 C7。置 θ0=0、η0=m0、s0=h0+ub−5。归一化 Q 为 (qb−a)m0=3a，ordinary 为 n0=ubm0，(54.40)=C7 恰是 untouched RC=0。s0−2qb=h0+2a−4>0，所以完整原行逆给实际非恒定仿射世界

$$
g_0=s_0\tau m_0(x-h_0),\qquad d_0=a_0+s_0\tau m_0h_0.
\tag{54.41}
$$

斜率非零，不依赖未证明的存在断言。

**定理 54.7（EVERY 基点的实际负 Γ、正 N 扰动）。** 固定 qb,ub。对 t>0 置

$$
\theta=t,\quad m(t)=\frac{3a-H(q_b)t}{q_b-a},\quad
s=h+u_b-5,\quad \eta(h,t)=m(t)-(h+u_b-4)t,
$$

$$
n(h,t)=u_b\eta(h,t),\quad Z=m(t)+1,\quad V=n+2m(t)+15,
$$

$$
R_b(h,t)=B_{7,b}(h)(7-h)\eta(h,t)
+[17B_{7,b}(h)+105-48q_b]t-C_7=-R_C/\tau.
\tag{54.42}
$$

分母 qb−a>0。m(t) 的定义使 Q 恒成立，η 的定义使 ordinary 恒成立。只须找 RC=0 的根并保留全部严格条件。

取任意有限 $7<h_L<h_0<h_U$。t=0 时，由 (54.40) 的严格单调性，$R_b(h_L,0)<0<R_b(h_U,0)$。Rb 为这些变量的连续表达式，故存在正的小 t 范围，使两端严格符号对 EACH 该范围 t 同时保持。

还须给统一严格余量。在固定紧区间 [hL,hU]，m(t)→m0；h 有界使 $(h+u_b-4)t$ 一致趋零，故 η→m0、n→n0、Z→Z0、V→V0 一致。基点满足 ALL 正余量

$$
n_0>0,\quad Z_0-4a>0,\quad
Z_0^2-4V_0=(p_0-v_0)^2>0,\quad
V_0-2aZ_0+4a^2=(p_0-2a)(v_0-2a)>0.
\tag{54.43}
$$

由一致收敛和有限个连续多项式，这些量对整个 [hL,hU] 在足够小 t 时各大于其基点正值的一半；m(t)>0 也保持。s−2qb=h+2a−4>0 对整个区间已严格。将这个 t 范围与端点符号范围相交仍为正范围。对 EACH 这样的 t，Rb 在有限区间连续且两端异号，介值定理给至少一个 $h_t\in(h_L,h_U)$ 使 Rb=0。

对 EVERY 保留根 ht，用 (54.23) 得 p_t,v_t 不同且 >2a，令 P=P(qb,s)，以 (54.8) 重建 λ、μ、ν、d。所有偶系数、Q、ordinary、untouched 原常数同时成立，故 BOTH 恒等式和该新父 SAME 六原行全部恢复，两个例外也实际达到该父。ν=sτt≠0，n>0，(54.18) 给

$$
\Gamma=-K_{\rm pos}t<0,\qquad N/\tau=n>0.
\tag{54.44}
$$

每个世界一个整个 gain 与固定 d，τ 两种符号、任意 a0 均保留。取任意窄的初始 h 括区间，再取小 t，父根与完整世界可以落入基点的任意给定邻域；没有假设可微、隐函数、唯一扰动分支或任意根选择的连续性。m(t) 随 t 改变，且 n 也可随 ht 改变，所以这些是改变父的扰动，不是不同 t 端点的 SAME 父关系。

可选末符号仅限进一步缩窄的此族。在 (h0,0)，$\omega=(7-h_0)m_0<0$，且

$$
Y/\tau=(s_0+4-4q_b)\omega<0,
$$

因为 qb<1、s0>2qb 使源因子正。先将 [hL,hU] 缩窄到 h0 周围使这两个连续表达式在 t=0 均有统一负余量，再缩小 t，就对该区间 EVERY 保留根保持两严格负号。这个结果不外推为负 Γ 全域末符号或 ENTIRE 子片分离。∎

### 54.9. SAME 取得 J 的 ENTIRE 原行逆：一般支与独立 s=4

固定一个 (54.12) 且 N≠0 的取得父，只选择时钟六 J，取得实际 z，定义

$$
k=\frac{z-a_0-E(4)}2.
$$

由实际迹和全部偶系数，

$$
h_J-a_0=4L+(2s+24)A+2(16-s^2)T,\qquad
k=(s+4)[A-(s-4)T].
\tag{54.45}
$$

这是 SAME 原第七行的未除表达，在 s=4、g(6)=0 也成立。固定子片须固定本式 SAME k 以及 $a_0,\tau,m,n$。

一般普通支 $\mathcal G_z$ 取 ALL 实 s>0、s≠4，置

$$
D_s=(s+4)(s-4),\quad U_s=A(s+4)-k,\quad
V_s=k(s+1)-5A(s+4).
$$

实际成员先有

$$
T=U_s/D_s,\qquad A-(s+1)T=V_s/D_s,\qquad uV_s=ND_s.
\tag{54.46}
$$

因 NDs≠0，先证明实际 Vs≠0，随后才解

$$
q=\frac{ND_s}{2V_s}-a-\frac12,\qquad F=L-sA+T(s+2)(s+4).
\tag{54.47}
$$

以 (54.5)、(54.8) 重建整个世界，保留 ALL 过滤：q>0、s>2q、q≠a、整个 g≠0 以及 BOTH ORIGINAL Q=0、RC=0。反向显示定义恢复 (54.46)、ordinary、全部偶系数和 SAME k；Q 与 ordinary 恢复原奇一次，RC 恢复 untouched 原奇常数。因此 BOTH 整个恒等式与 ALL SAME 七原行同时成立。没有除 H。

若需要清分母，完整等价表可写为

$$
Q_s=ND_s-(2a+1)V_s,\quad
f_s=(L+10A-k)s+8A-4L-2k,
$$

$$
J_s=(Q_sV_s-2V_s^2)s+4V_s^2-Q_sV_s-Q_s^2,
$$

$$
P_s=(2DV_s-AQ_s)V_sD_s-U_s(4V_s^2+2Q_sV_s-Q_s^2),
$$

$$
R_s=2CV_s^2D_s-15Q_sV_sU_s-J_sf_s(s+4).
\tag{54.48}
$$

其理由是 q=Qs/(2Vs)、$F=f_s/(s-4)$，以及

$$
P_s=2V_s^2D_sQ,\qquad R_s=2V_s^2D_sR_C.
$$

F 的恒等式来自 $(L-sA)(s-4)+U_s(s+2)=f_s$；Bsrc=Js/(2Vs²) 与 H=(4Vs²+2QsVs−Qs²)/(2Vs²) 逐项恢复两乘子。特别原常数中的 15qT 给 −15QsVsUs，最后 F 项给 −Jsfs(s+4)，均未丢失。乘子先已非零，可为负，等价不要求正。所有实解、重根、次数取消或恒零残式仍按等式保留；不从单变量表推有限性。

独立 $s=4$ 普通支 $\mathcal H_z$ 在 k≠8A 时为空；k=8A 时取 ALL

$$
0<q<2,\quad q\ne a,\quad u=2q+2a+1>0,
$$

$$
T=\frac{A-N/u}{5},\quad F=L-4A+48T,\quad
\lambda=4F,\quad\mu=4A-40T,\quad\nu=4T,\quad d=a_0-\lambda.
\tag{54.49}
$$

取 P(q,4)，保留整个 g≠0 与 BOTH

$$
D-qA=HT,\qquad C-15qT=[4(q-1)+D_0]F.
$$

必要性由未除 J 式给 k=8A，ordinary 给 T，偶系数给其余全部系数；严格源域恰为 0<q<2。逆向上述定义与两原残式恢复 ordinary、全部奇偶系数及 BOTH 恒等式，k=8A 恢复第七原行。只除正 u 与固定五，完全不使用固定 b 的一般分支捷径。

令 $\mathcal A_z=\{W_p:z=z_p\}\cup\{W_v:z=z_v\}$，则

$$
\mathcal K_{6,J,z}=\mathcal G_z\cup\mathcal H_z\cup\mathcal A_z.
\tag{54.50}
$$

q=a/q≠a 和普通的 s=4/s≠4 穷尽源双射，每支各有完整原行 iff，故这是 ENTIRE 等号。若 Vs 恒零，一般实际支由 uVs=NDs 排空，独立 s=4 仍须检查。所有解、不同 T、不同 b、ordinary-only 子片、重复或恒零残式保留，去重只按整个世界。联合图谱在固定 $a_0,\tau,m,n$、附 SAME (54.45) 时给同一普通集合；H=0 未被任何分母删除。

### 54.10. 保留的一般普通末零排除与实际末函数

此处的末零定理只需取得数据满足 Σ、τ≠0、K(7)=0，其中

$$
\Lambda=\frac{C-15a\tau}{a-1},\qquad K=\Lambda+E+\tau U.
$$

不要求接受根、达到参数 p,v、N 或 Γ 符号或有限父。Σ 与 Λ 定义逐系数给 (54.14)，包括 untouched 原 C。由 ordinary 与全部偶系数，不借父根参数即有整个恒等式

$$
\frac{g(x)}s=T(x^2-5x+3)+\frac Nu(x-h),\qquad h=s+5-u.
$$

它只用正 u，不除 T 或 N；下述证明在这个一般域使用此形式。

**定理 54.8（复用的一般普通末零排除）。** 在这个确切域中，每个实际 ordinary 世界 g(7)≠0。

证明。反设普通末零。BOTH 原恒等式在七给

$$
\lambda-\Lambda=105(\tau-T)=48(a\tau-qT),\qquad
(35-16q)T=(35-16a)\tau.
\tag{54.51}
$$

令 $21<c_*=35-16a<35$、$\kappa=105/c_*$，则 3<κ<5。未除的 (54.51) 右边非零，先证明 T≠0 与 35−16q≠0。现在 $\tau/T=(35-16q)/c_*$，且 $(a\tau-qT)/T=-35\delta/c_*$。由 $Q=\delta(uT-A)+3(a\tau-qT)=0$ 除已非零 T，再仅取消普通 δ≠0，给

$$
A/T=u-\kappa,\qquad (N/u)/T=4-h-\kappa.
$$

完整 gain 正规形强制

$$
\frac\Omega T=17+(7-h)(4-h-\kappa)
=\left[h-\frac{11-\kappa}{2}\right]^2+\frac{68-(\kappa+3)^2}{4}>1,
\qquad \Omega=g(7)/s.
\tag{54.52}
$$

因为 0<κ+3<8，常数余项严格大于一。这与 Ω=0 矛盾。此平方约束是反设末零及原式的后果，不是任意普通非末零世界上的无条件不等式。无 H、N、样本或 s−4 除法，N=0、H=0 和两种 τ 符号均覆盖。∎

强制普通末零公式只能是必要候选，不能当作实际达到。对 (54.12)，这些公式为

$$
B_{\rm den}=16Z+54-32a>0,\quad
q_* =\frac{35Z+67-70a}{B_{\rm den}},\quad
35-16q_*=818/B_{\rm den}>0,
$$

$$
T_* =\tau\frac{c_*}{35-16q_*},\quad u_*=2q_*+2a+1,\quad
s_* =\frac{A-N/u_*}{T_*}-1.
\tag{54.53}
$$

$q_*-3/2=(11Z-14-22a)/B_{\rm den}>0$，所以 u*>0、T*≠0、T*/τ>0，分母先合法。这些定义恢复 Q*=0 和 ordinary，但 (54.52) 仍给 Ω*/T*>1。若 s*≤2q*，源不严格；若严格，

$$
B_{7,*}=(q_*-1)(s_*-2q_*)+4q_*-5>1,
\quad \frac{R_{C,*}}\tau=-B_{7,*}\frac{\Omega_*}{T_*}\frac{T_*}\tau<0.
\tag{54.54}
$$

最后等式由 (54.20) 和 (54.51) 的候选消去关系给出。故没有候选通过原常数和实际末零测试；必要源符号不构成可行性。

对 EVERY 实际父世界，包括例外，定义

$$
\Omega=F+7A+7(1-s)T=g(7)/s,\qquad
X=48qT-2q\Omega,\qquad Y=48qT+(s+4-4q)\Omega.
\tag{54.55}
$$

原奇式在七给 $o(7)g(7)=\lambda+R(7)+48qT$。JJ 实际迹为 o(7)−2q/s，JM 比它多 (s+4−2q)/s，故

$$
f_{JJ}=a_0+R(7)+X,\quad f_{JM}=a_0+R(7)+Y,\quad
Y-X=(s+4-2q)\Omega,\quad s+4-2q>0.
\tag{54.56}
$$

共同加项是 a0+R(7)，不是各世界可能不同的 d；没有除最终 gain。例外 Ω=0、q=a、T=τ，故 X=Y=48aτ。完整例外列表与定理 54.8 给

$$
\{W\in\mathcal S(\mathcal H_5):g_W(7)=0\}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,J,z}:g_W(7)=0\}=\mathcal A_z.
\tag{54.57}
$$

后者是单点或空，不是整个子片的等号。任一末碰撞对必须含普通非末零端点；不排除普通—普通或普通—例外碰撞。末零子集上的单射不承担 ENTIRE 子片选择器。

### 54.11. 保留的 ENTIRE 正 Γ 类与至多八 TOTAL 完整逆

**定理 54.9（复用的正 Γ 完成）。** EVERY (54.12) 且 Γ>0 的达到父，其每个可达 J 子片为单点或恰一普通加一匹配例外；实际末 M 在 ENTIRE 子片单射。只依取得数据选 J，单点七 TOTAL 停，否则只取末 M，即至多八 TOTAL 得整个 P,g,d 的必要且充分唯一逆。

给出支撑此 ENTIRE 量词的证明。置 θ=−ρ<0，由 (54.18) 先得 ρ>0；Γ>0 给 V>6Z、V≤Z²/4，故 Z>24、$a<q_0=a+3a/m<104/115<1$。归一化 Q 为 m(q0−q)=−Hρ。若 q≥φ，左负右非负，矛盾，故

$$
q_0<q<\phi<5/3,\quad H>0,\quad
\eta=n/u=m+(s+1)\rho>0,\quad n>0.
\tag{54.58}
$$

全 gain 是 $g/(s\tau)=-\rho(x^2-5x+3)+\eta(x-h)$；F/τ=−3ρ−hη<0。原末常数恒等式给未除积

$$
B_7\omega=C_7+(105-48q)\rho>0,\qquad
\omega=-17\rho+(7-h)\eta.
\tag{54.59}
$$

q≤1 时 D0=−(q−a)u<0，所以 B7<0，ω<0。q≥1 的 h>7 必须由原常数证明，不能只用必要源区间。

令 ε=1−a、t=q−1∈[0,2/3)。εu=1+2εt、s=h+2t−2ε、Bsrc=t(h−5−2ε)−1。以 V=(u+2)m+15+u(s+1)ρ 代入 untouched 原常数，它精确等价于

$$
0=Gm+J_c\rho-K_c,\qquad K_c=105\epsilon+15a>0,
$$

$$
M_c=h-7+t[-h^2+(5+2\epsilon)h-14\epsilon],\quad
G=M_c-14\epsilon,\quad
J_c=M_c(s+1)-12-3t(h-2\epsilon).
\tag{54.60}
$$

逐项依据是 $G=-B_{\rm src}h-7\epsilon(u+2)$ 和 $J_c=M_c(s+1)-3B_{\rm src}-15q$，完整保留原 15a。若 h≤7，方括号 f(h)≤0 时 Mc≤0；若 f(h)>0，则由 1/5<ε<1/4、h>0 得 $f(h)<-h^2+(11/2)h-14/5$，从 t<2/3 得

$$
M_c<h-7+\frac23\left[-h^2+\frac{11}{2}h-\frac{14}{5}\right]
=-\frac23(h-7/2)^2-\frac7{10}<0.
$$

因此 G<0、Jc<0，与 m,ρ,Kc>0 的 (54.60) 矛盾，包括 q=1、h=7。故实际 q≥1 必 h>7，从全 gain 得 ω<0；(54.59) 再得 B7<0。此结论仅在正 Γ 的实际世界使用。

证明原 J 在 ENTIRE 普通总体单射。定义

$$
w=m+(s-4)\rho=\eta-5\rho,\qquad k/\tau=(s+4)w.
$$

若 q≤1，则 H≥2，$0<\rho/m=(q-q_0)/H<\epsilon/2<1/8$，s>0 给 w>m−4ρ>m/2>0；若 q≥1，h>7 给 s>4，故 w>m>0。两个实际 SAME 父普通世界若 q1<q2，精确相减得

$$
\rho_2-\rho_1=
\frac{2m(q_2-q_1)[1+q_0-q_0^2+(q_1-q_0)(q_2-q_0)]}{H_1H_2}>0.
\tag{54.61}
$$

它来自 $H_2-H_1=2(q_2-q_1)(1-q_1-q_2)$；全部分母先正，括号因 0<q0<1、qi>q0 严格正。同一个 n>0 给 η1>η2；$\eta_i-m=(s_i+1)\rho_i>0$ 给 s1>s2，并给 w1>w2>0。因此

$$
\frac{k_1-k_2}{\tau}=(s_1-s_2)w_1+(s_2+4)(w_1-w_2)>0.
\tag{54.62}
$$

等 q 时 H>0 的 Q 固定相同 ρ、T，ordinary 再固定 s；源双射和全部偶系数固定整个 P,g,d。故每个 SAME k 子片至多一个普通世界，没有有限性假设。例外的 (54.17) 非零差给至多一个匹配例外。

因 q<2、s>2q，有 s+4−4q>4−2q>0，故

$$
Y_{\rm ordinary}/\tau=-48q\rho+(s+4-4q)\omega<0<48a
=Y_{\rm exception}/\tau.
\tag{54.63}
$$

这分离可能的混合对，两种 τ 符号均给实际响应不等，不要求各自漂移相同。

完整逆只用实际取得行。由 (54.4)、(54.10) 求 a0,E,R,Σ,τ,N，再求 Λ=(C−15aτ)/(a−1)、K=Λ+E+τU。识别父的精确谓词是 Σ、τ≠0 及

$$
K=\tau(x+p)(x+v)(x-7),\quad p\ne v,\quad p,v>2a,\quad\Gamma>0.
\tag{54.64}
$$

必要性由父系数，充分性由固定例外的实际原行证明。也可取 Z=A/τ+1、V=−Λ/(7τ)，保留全部父系数与精确因子核对；没有未来响应或隐藏标签。

父有两个例外而非单点。选 J，取得 z、求 SAME k，按 54.9 全部一般支、独立 s=4 支及匹配例外构成 Lz。双向原行证明给 $\mathcal L_z=\mathcal K_{6,J,z}$，真实世界给非空，J 单射与例外分离给单点或混合两点。单点在七 TOTAL 返回完整世界；否则只选时钟七 M，取得 y7，仅保留

$$
y_7=a_0+R(7)+Y(W),\qquad W\in\mathcal L_z.
\tag{54.65}
$$

真实世界给存在，(54.63) 给唯一；各支全部七原行 converse 与所选精确末式给逆的必要且充分性。接受条件是整个等式，不能只用归一化符号。父谓词外不据此排除别类；子片空或所选末式无解表示本类无世界。记录须遵守单点停止、否则选 M 的分支。未选响应不是输入。这里不要求每个正 Γ 父有普通世界，也不从子片至多两点推出整父至多两点。∎

正 Γ 的窄必要界 $q_0<q<1+1/(7+2a)$ 也保留：q>1 时 B7=(q−1)(h+2a)−1<0 和 h>7 给界，q≤1 自动满足。它不作为充分性过滤。正 Γ 的 q0<1、H>0、η>0、θ<0、ω<0、w>0 及严格 J 序不移用到负 Γ；54.6 的实际族已经阻止其中数项的全域延伸。

### 54.12. 另外已完成的范围

Γ=0 时 (54.18) 对 EVERY 普通世界迫 T=0，A≠0 排除常数。Q 固定 qb=a+3a/m，ordinary 固定 η=m、n=ubm。全部普通 h>0、qb<1 给 B7<0，原常数 C7=B7(7−h)m>0 先迫 h>7。54.8 的全部基点参数与唯一严格递增原常数根 h0>7 给唯一实际仿射世界 Waff；这不只是一个可能子集。完整例外列表遂给

$$
\mathcal S(\mathcal H_5)=\{W_{\rm aff},W_p,W_v\}.
\tag{54.66}
$$

三者不同。J 子片为匹配这些世界的完整列表，至多仿射加一个例外；单点七 TOTAL 停，混合时 (s+4−4qb)m(7−h0)<0<48a 给实际末 M 分离，完整原行与仅选中末式给至多八 TOTAL 的整个 P,g,d 充要唯一逆。

N=0 的精确轨迹是

$$
V=2Z+13\iff(p-2)(v-2)=17,\qquad
p=2+x,\quad v=2+17/x,\quad x>0,\quad x^2\ne17.
\tag{54.67}
$$

两移位因子不能都负，因为 p,v>2a>3/2 会使其乘积小于 1/4 而不是 17，所以 p,v>2。其整个父没有普通世界：ordinary 给 A=(s+1)T，全部偶系数给 $g=sT(x^2-5x+3)$。若 A 或 T 为零则整个 gain 零，先排除后由原 Q、RC 得

$$
\frac{C-3D}{3A}=\frac{q-s}{s+1}\in(-1,0).
$$

但该达到父的同一比值为

$$
\frac{(14-17a)Z+91-82a}{3(Z-1)}>0,
$$

因 a<4/5、Z>4a>3，矛盾。这是所有 T 的排除，不只是指定 M 片。因此 ENTIRE 父恰为 Wp,Wv，J 响应不同，七 TOTAL 按实际匹配给完整唯一逆。τ 两种符号及任意 a0 保留，等根参数不加入。

另一路 $\mathsf B_0$ 的既有 scoped 八 TOTAL 完成保留其原范围；本文的新负 Γ 证明不依赖其未在本文给出的证明。上述各已知类的恢复不在没有跨类证明时升级为未知并集恢复。旧范围较大的 OPEN 语句不改变这些完成类的精确结论。

### 54.13. SAME 父的精确坏 M、两个末 FULL 片与全部已服务守卫

对 ALL (54.12)，M 行由偶式给

$$
h_M=a_0+E(6)+48T,\qquad
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
\tag{54.68}
$$

它把 SAME FULL M 子片精确固定为 T=τ。须排除 EVERY 普通 T=τ 世界，不能用仅末零排除替代。

该排除的原常数证明如下。反设有实际普通 T=τ。Q 的二次式一根是 a，另一普通根强制

$$
q=(Z+1)/2-a,\quad\delta=q-a>1/2,\quad S=Z-7,\quad h_o=s-S=s-Z+7>8-2a>6.
$$

原一次式给 $V=(7-h_o)Z+23-2h_o$，全部偶式给

$$
g=s\tau(x^2-h_ox+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-9/2)^2+11/4>0.
$$

untouched 常数精确为

$$
-7V=s\chi_o-\frac{\delta(h_o-4)(h_o-6)(h_o-8)}{1-a}.
\tag{54.69}
$$

依据是原常数 $(a-1)(-7V)-15\delta=B_{\rm src}\chi_o$，减去 (a−1)sχo 并用 D0=−δ(S+9)，得到 $(a-1)(-7V-s\chi_o)=\delta[(h_o-9)\chi_o+15]$；方括号恰为 (ho−4)(ho−6)(ho−8)，给 (54.69)。这一步不丢原 15δ。

负左边、sχo>0、δ>0 与 ho>6 迫 ho>8。原一次式及 Z>4a、V>4a² 给

$$
h_o<\frac{19+30a}{4a+2}<17/2.
$$

于是 $0<(h_o-4)(h_o-6)(h_o-8)<45/8$，而 χo−15=(ho−8)(ho−1)>0。1−a>1/5 给三因子除以 (1−a)χo 小于 15/8。严格源又有 0<δ<q<s/2，所以 (54.69) 反而强制 $-7V>s\chi_o/16>0$，矛盾。该证明不要求 N 或 Γ 符号，也不假设 τ 正。

例外列表遂给精确 FULL 等号

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}
=\{W_p,W_v\}.
\tag{54.70}
$$

两个 gain 均在七为零，故两个实际末动作都给同一 d*。这些是 SAME M 子片及两个末片的等号，不是一般整个六读父等号。两个固定不同世界还满足每个已服务取得祖先；这些祖先、父、M 子片和两末片的非单点停止守卫全部保留。

同历史 K⊆K′ 时，对于 EACH 实际 E 和 SAME z，

$$
\{W\in K:h_E(W)=z\}\subseteq\{W\in K':h_E(W)=z\}.
$$

定义 L0 为至少两个不同完整目标，L(m+1) 要求父非单点且 EACH 可用动作有一个实际 FULL 响应片满足 Lm。m=0 的不同性随包含保持；归纳保留每动作原响应见证，对子片包含用归纳假设，父守卫也保持。因此任意基数、任意有限深度的失败向上保持；不服务早期未取得另一臂。

条件地，若一个剩余 SAME J 子片确有两末非单射，各实际终端取一个碰撞对至多四端，加 SAME 父坏 M 对至多两端。并集在各臂同响应片包含原碰撞端点，增加成员不消除 duty，向上包含恢复 FULL 与全部相关守卫。因此至多六完整端点可保留该已实现局部两步失败。此条件结论不证明实现、最小支持、尖锐性或根失败；只在实际终端抽对，不从任意非终端失败族抽一对。

### 54.14. 精确剩余 SAME-k 义务与未完成目标

余下标志层为 EVERY (54.12) 且 $\Gamma<0,N\ne0$ 的达到父和 EVERY 可达 ENTIRE SAME 取得 J 子片。N/τ 两符号不能删除；54.6 与 54.8 已分别给实际世界。完整候选集合是 (54.50)，或固定 $a_0,\tau,m,n$ 并附 SAME k 的联合图谱与匹配例外。每个候选必须同时满足

$$
\begin{aligned}
d+g(0)&=a_0,\\
d+jg(1)&=a_0+R(1),\\
d+(1+b)g(2)&=a_0+E(2),\\
d+(j+r)g(3)&=a_0+R(3),\\
d+(1+2b)g(4)&=a_0+E(4),\\
d+(j+2r)g(5)&=a_0+R(5),\\
d+(1+2b)g(6)&=z.
\end{aligned}
\tag{54.71}
$$

跨七行是同一个严格 P、一个整个非零 g、一个固定 d；BOTH ORIGINAL Q、untouched RC 与 SAME k 不省略。

**正完成 OPEN。** 对 EVERY 该父及 EVERY 可达 ENTIRE SAME-k 子片，证明其单点可停，或至少一个实际末函数 X、Y 在 ENTIRE 子片单射。动作只由取得数据选择，完整列表加仅所选一个实际末响应须给整个 P,g,d 充要唯一逆。任意非空 K 的停止成功 iff 单点；余一次动作成功 iff 某个实际末函数在 ENTIRE K 单射。非单射给不同整目标同响应，单射由真实世界给存在及唯一。这证明判据本身，不是证明全称选择器。

**负完成 OPEN。** 在 ONE SAME 达到的负 Γ、N≠0 父及 ONE SAME 取得 k 中，实际构造

$$
U_1\ne V_1,\quad U_2\ne V_2,\qquad
X(U_1)=X(V_1),\quad Y(U_2)=Y(V_2),\qquad
U_i,V_i\in\mathcal K_{6,J,z}.
\tag{54.72}
$$

两对可不同或重叠，distinct 指整个世界。每端通过 ALL (54.71)、严格源、整个 gain、固定漂移、BOTH 原残式与 SAME k；每对至少一个普通非末零端点。共同加项 a0+R(7) 使 (54.72) 充要等价于两实际末函数各非单射，反向非单射各供应一对，不需要有限性。同时保留 SAME 父 (54.70) 的坏 M 对、两个末 FULL 片、BOTH 动作、全部已服务祖先和每个父/子/末片停止守卫，才得到该父局部 L2。

本文没有构造 (54.72) 任一对，也未排除该剩余层的实现。SAME 六读父多重性、不同父或不同 k 的世界、源投影、必要残式、共同符号、末零子集单射、联合两坐标对点分离、固定 b 单射、基数或一个碰撞，均不替代 ENTIRE SAME-k 上所需单函数单射或两个实际碰撞 duty。第二普通族尤其不声称共享 k。

**原 FULL 二次问题 OPEN。** ALL 严格源、ALL 整个非零次数至多二实 gain、任意固定漂移的确定性自适应八 TOTAL 完整恢复 versus 原根 L7，仍未结算。其他六读父、早期未服务臂、剩余标志选择器仍未完成。没有任意原根策略强迫 JMJMJ 前缀、不受限同父 L3、原根失败树、minimax、尖锐性、最小支持或九读上界。

**原 FULL 三次问题 OPEN。** 整个次数至多三八 TOTAL 完整恢复 versus $n_{\rm det}(3,0)\ge9$ 仍未结算。三次 gain 乘线性迹可为四次，四个偶节点相等仍可留非零倍 $x(x-2)(x-4)(x-6)$。二次恒等式不检测未知次数、三次、根、方向或平面承诺。已知类分别恢复没有跨类证明不能成为未知并集逆。

### 54.15. 完整 INERT 全局同时实现合同

以下完整合同仅为 INERT、未履行且未经执行的共同实现义务，原生成族未被访问。ALL 256 终叶槽

$$
\sigma=(w,\varepsilon),\qquad w\in\{J,M\}^7,\quad\varepsilon\in\{0,1\};
$$

ALL 254 非空实际前缀 v，原长度 i=1 至七，其实际左乘积 Av 与全部后代共同受约束。记

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,\ it_v(P),\ i^2t_v(P),\ i^3t_v(P)).
\tag{54.73}
$$

SAME 整个 $1538\times1024$ 关系针对每个前缀的每个非代表后代 σ 与同前缀代表 ρ 保留整行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0.
\tag{54.74}
$$

继承层行数为 254、252、248、240、224、192、128；尺寸与层行数是给定符号规格，不是执行生成或核验的读数。ONE 同一共同堆叠向量包含 ALL 256 整个四系数 gain 块；每块 $x_\sigma\ne0$，每个适用同源终叶的整个四分量差 $x_{(w,0)}-x_{(w,1)}\ne0$。每个 Pσ 均满足 (54.1) 的严格源条件；ALL 严格源、全部祖先、BOTH 动作 duty、所有停止守卫须同时成立。

每槽自始固定

$$
g_\sigma(t)=\sum_{h=0}^3x_{\sigma h}t^h,\qquad d_\sigma=a_0-x_{\sigma0},
\tag{54.75}
$$

跨该槽每条原行使用 SAME 一个整个 gσ 与固定 dσ。只合并整个 P,g,d 相等的槽；二次限制 $x_{\sigma3}=0$ 同时作用于 SAME 全部 256 块。局部联合或单变量图谱、终端对、条件六端点、选定支持、源投影、较小关系、分路径或分臂解、逐行 refit 或分别选择守卫向量，均不能替代 SAME256slots254prefixes1538x1024ONEcommonvector/wholeblocks/strictsources/ancestors/BOTHactions/stopguards 的共同实现。没有生成、枚举、矩阵、秩、核、区间或证书计算，也没有本合同已满足的断言。

### 54.16. 严格零层、除法与证据边界

源始终 q>0、s>2q；父根始终 p,v>2a、p≠v、τ≠0。q=0、s=2q、r=0 或 1、b=0、c=0、p=2a、p=v、τ=0、极限或无限源不补作世界。IVT 的边界值与符号无穷极限不是实际世界。只有整个零 gain 预先非法；各低次排除都由原式在声明范围内推出。普通真正二次在负 Γ 由 Kpos>0 推出，普通末零只在 Σ、τ≠0、K(7)=0 的定理域排除。例外保持真正二次及末零。合法 H=0、s=4、s=4q、r=1/2、b=1/2、λ 或 μ 零、g(6)=0、零观察、非采样和重复 gain 根、降次或恒零残式均完整保留到确切原式拒绝。非零 gain 贡献可被固定漂移抵消成零观察。两种 τ 符号、任意固定实漂移、两对角侧、对称/非对称及无界正非对角元不缩域。

除法先后如下：插值只除固定非零整数；源逆只除 b,s>0；例外用 a>0、a−1≠0、τ≠0 与精确整除；ordinary 仅取消 q−a≠0；u>0 先于 η、ζ 定义。Kpos 先证正，联合图谱不除 H、系数行列式、θ、η 或 s−4。接受根判别式先严格正才用根式。H 族的 s+1、uH 与正固定常数先非零；第二族的 q+χ、u、m、θq 先正，φ−q 不取消。扰动先证 qb−a>0 与全部一致严格余量才用介值定理。一般 J 支先分 s≠4，由 NDs≠0 证明 Vs≠0，非零乘子不要求正；独立 s=4 支只除正 u 和固定五。末零反设先证明 T 与 35−16q 非零；候选先证明 Bden>0、u*>0、T*≠0。正 Γ 证明先有 H、ρ、m 正才取比值，同父差式先有 Hi>0；q−1 仅在 q>1 的窄界使用，q=1 保留。没有取消未知源/漂移差、λ、μ、g(6)、g(7)、1−2r、1−2b、源行列式或未证判别式。

当前成果只包含上述定义、完整原行 converse、符号存在及分类、已完成类接口和精确 OPEN 义务。全部数学为 fallible UNEXECUTED 符号推导；没有执行数学求值、代入、数值、导数、递推、枚举、CAS、矩阵/秩/核/区间/证书计算、实验、测试、构建、renderer、probe、Lean 或 proof-kernel 验证；没有 D5、Blueprint、Reg、摄入或消化。不给 kernel 或数值认证、经验 ML/NN、物理、噪声、稳定性、连续逆、有限精度、可计算性、效率、复杂度、资源、一般 gain 空间逆、gain 跨度下界、任意混合失败删除、非终端抽对、最小支持、文献穷尽、原创性或优先权认证。

## 追加锚（本行以下为增补区）
