# FIB 二次负 n 的高 q 实际族与精确同子片对关系

本卷独立为第 62 节。固定实际五动作 $JMJMJ$ 的严格 $\beta=7$ 父、$\tau\ne0$、不同接受根 $p,v>2a$ 及 $n<0$，给出四项结果：任意取得响应下有界 $q$ 的归一化最终增益正性；原奇常数强制的低、高坐标排除；全部实际 $H=0$ 分支在 $\kappa<8m$ 的定位；固定 $\kappa\le8m$ 上普通世界对的原行充要关系及两个精确末比较多项式。

这些结果增加高坐标覆盖和共同实现约束。一般负 $n$、任意响应的 ENTIRE 选择器仍为 OPEN，连 $\kappa\le8m$ 的剩余部分也未完成。原 FULL 二次八 TOTAL 恢复 versus 原根 $L_7$，以及原 FULL 三次八 TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$，均为 OPEN。

本文为 `repo-derived` 理论综合；插值、因子定理、次数根数、Vieta、有限平方及有限区间介值定理是复用工具。全部证明是可错的、未经执行的符号数学，不是 Lean kernel、数值或外部原创性认证。

## 62. 负 n 高坐标与原世界对的精确约束

### 62.1. 一个完整世界、原时钟与达到的父

一个世界跨全部原行固定为

$$
W=(P,g,d),\qquad
P=\begin{pmatrix}r_0&b\\c_{\rm src}&1-r_0\end{pmatrix},\quad
0<r_0<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r_0(1-r_0),
$$

$$
g(x)=\lambda+\mu x+\nu x^2\in\mathbb R[x]\setminus\{0\},\qquad d\in\mathbb R.
$$

四源元严格正，迹一，秩恰一。原模型只排除整个零增益，包含全部低次、合法系数零、样本零、观察零及两种非零尺度符号。去重只按整个 $P,g,d$。不同候选可有不同的固定漂移；同一世界不能逐行改变增益或漂移。

实际即时左动作与读数为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
$$

已服务 $JMJMJ$ 给原时钟零至五的六次 TOTAL。时钟六选 $J$ 取得 $z$ 为七次 TOTAL；时钟七只选一个末动作，才有八次 TOTAL。没有重置、复制、跳读、时钟平移、额外端口、隐藏源/根/次数标签、逐行 refit 或未选响应输入。

令 $a_0=y_0$。偶插值 $E=Lx+Ax^2$ 在零、二、四恢复 $y_i-a_0$，奇插值 $R=Dx^2+Bx+C$ 在一、三、五恢复 $y_i-a_0$。次数至多二的差有三个不同根即为零，故它们唯一，$C$ 始终是原奇常数。令 $j=b+c_{\rm src}$，所需 SAME 七行明确为

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
\tag{62.1}
$$

迹恒等式

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r_0+A_{21}b+A_{12}c_{\rm src}
$$

与左 $J$ 交换旧两行、左 $M$ 取旧第二行及旧行和的规则给这些迹。实际末 $JJ,JM$ 的迹分别为 $j+2r_0$、$1+j+r_0+2b$。重复乘积仍使用新时钟的增益样本。

固定

$$
a=\frac{\sqrt{17}-1}{4},\quad a^2+\frac a2=1,\quad \frac34<a<\frac45,
$$

$$
\Sigma:\ B+5D=a(L+5A),\quad \tau=\frac{D-aA}{3a}\ne0,\quad
U_0=x(x-2)(x-4),\quad V_o=(x-1)(x-3)(x-5),
$$

$$
\Lambda=\frac{C-15a\tau}{a-1},\qquad
K=\Lambda+E+\tau U_0=\tau(x+p)(x+v)(x-7),\quad p\ne v,\quad p,v>2a.
\tag{62.2}
$$

正数 $x$ 的 $x^2+x/2-1=(x-a)(x+a+1/2)$ 给所用 $a$ 的严格界。固定父即固定 $a_0,\tau$ 及

$$
Z=p+v=m+1,\quad V=pv=n+2m+15,\quad n=V-2Z-13<0.
$$

展开 $K$ 并使用父条件得

$$
\begin{aligned}
A&=\tau m,&L&=\tau(n-5m),\\
D&=a\tau(m+3),&B&=a\tau(n-5m-15),\\
\Lambda&=-7\tau V,&C&=\tau\bar C,\quad \bar C=7(1-a)V+15a,
\end{aligned}
$$

$$
R=aE+a\tau(U_0-V_o)+(a-1)\Lambda.
\tag{62.3}
$$

最后式的常数是原 $C$，因为 $U_0-V_o=3x^2-15x+15$。另记 $N=L+5A=\tau n$。

精确父区域为

$$
Z>4a,\qquad 2aZ-4a^2<V<\frac{Z^2}{4},\qquad n<0,
$$

或等价地

$$
m>4a-1>0,\qquad
(2a-2)m+4a-19<n<\frac{m^2-6m-59}{4},\qquad n<0.
\tag{62.4}
$$

必要性由 $p-2a,v-2a$ 的正和、正积及 $(p-v)^2>0$ 给出。反向这些不等式给移位二次式的正判别式、正和、正积，故两根实、不同且都正，加 $2a$ 恢复所需 $p,v$。62.3 的例外构造对每个该参数、任意 $a_0$ 和两种 $\tau$ 符号实际达到此父；这里没有未达到的形式父。

### 62.2. 完整原行桥梁与全普通图谱

源坐标双射为

$$
q=r_0/b>0,\quad s=2/b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix}.
\tag{62.5}
$$

正向 $s-2q=2(1-r_0)/b>0$，秩一强制下左元的公式。反向四元正、迹一且 $bc_{\rm src}=r_0(1-r_0)$；非零迹排除秩零，且返回原 $q,s$。这覆盖 ENTIRE 严格源域，包括 $s=4$ 与 $s=4q$。另有 $j=q+2(1-q^2)/s$。

置

$$
D_0=2-q-2q^2,\quad H=D_0+3q=2+2q-2q^2,\quad
e(x)=1+x/s,\quad o(x)=qe(x)+D_0/s,\quad T=\nu/s.
$$

在原偶、奇节点，$e,o$ 恰为相应迹。六原行当且仅当源严格、整个 $g\ne0$、$d=a_0-\lambda$ 且 BOTH 整个恒等式

$$
-\lambda+eg=E+TU_0,\qquad -\lambda+og=R+qTV_o.
\tag{62.6}
$$

证明必要性：相应差各有三个原节点根及三次系数 $T,qT$；减去相应节点三次式后次数至多二，三个不同根使其恒零。充分性在 SAME 节点取值即得六行，不除任何增益样本。

全部偶升幂系数为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T),
$$

故可逆地

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad
\lambda=sF_{\rm orig},\quad d=a_0-sF_{\rm orig}.
\tag{62.7}
$$

奇左升幂系数是

$$
\big((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\big),
$$

右边是 $(C-15qT,B+23qT,D-9qT,qT)$。三次自动相同，其余恰为

$$
\begin{aligned}
Q&=D-qA-HT=0,\\
L_{\rm res}&=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&=C-15qT-[(q-1)s+D_0]F_{\rm orig}=0.
\end{aligned}
\tag{62.8}
$$

逐系数反向恢复 BOTH 恒等式。因此原 $C$ 和 $15qT$ 都必须保留。

ordinary 先声明 $q\ne a$。置

$$
\delta=q-a,\quad u=2q+2a+1>0,\quad \theta=T/\tau,\quad
\eta=n/u<0,\quad h=s+5-u=s-2q+4-2a>0.
$$

$a$ 的方程给 $D_0=-\delta u,H=3q-\delta u$。原系数逐项收集得

$$
Q/\tau=3a-\delta m-H\theta,\qquad
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}-5Q/\tau.
\tag{62.9}
$$

只在 $q\ne a,\tau\ne0$ 后取消，得到 $Q=L_{\rm res}=0$ iff $Q=0$ 与 $m=(s+1)\theta+\eta$。没有除 $H$。

令 $\Gamma=n-(4a+1)m-6a<0$。由 $u-(4a+1)=2\delta$，

$$
\Gamma=-K_{\rm pos}\theta,\qquad
K_{\rm pos}=u(s+1)+2H=u(s-2q+2a+1)+6q>0.
$$

故每个实际普通世界均推得 $\theta>0$，包括 $H=0$。每个偶系数于是恢复为

$$
F:=F_{\rm orig}/\tau=3\theta-h\eta>0,\qquad
g(x)=s\tau[\theta x^2+(\eta-5\theta)x+F],\quad d=a_0-s\tau F.
\tag{62.10}
$$

特别真正二次是原式的结论。常数计算中
$F=n-(s+5)m+\theta(s+2)(s+4)$；代 $n=u\eta,m=(s+1)\theta+\eta$，$\theta$ 系数恰为三，$\eta$ 系数为 $-h$。

定义 SAME 实际取得响应

$$
\kappa=\frac{z-a_0-E(4)}{2\tau}.
$$

时钟四和时钟六 $J$ 的迹同为 $1+4/s$，固定增益给 $g(6)-g(4)=2s\tau(5\theta+\eta)$。因此第七原行 iff

$$
\begin{aligned}
\kappa&=(s+4)(5\theta+\eta)=(s+4)[m-(s-4)\theta]\\
&=5m+15\theta+(s-1)\eta,\\
\kappa-8m&=(s-4)(\eta-3\theta).
\end{aligned}
\tag{62.11}
$$

因为 $\eta-3\theta<0$，$\kappa<8m$ iff $s>4$，等号 iff $s=4$，$\kappa>8m$ iff $s<4$。没有取消 $s-4$ 或零样本。

完整的一个 $q$ 图谱可直接由取得数据给出。对辅助 $q>0$ 置

$$
b_\kappa=\kappa-5m+2\eta,\quad
\Delta=b_\kappa^2-60\eta(m-\eta)>b_\kappa^2,\quad
\theta=\frac{b_\kappa+\sqrt\Delta}{30}>0,\quad
s=\frac{m-\eta}{\theta}-1.
\tag{62.12}
$$

这是 $15\theta^2-b_\kappa\theta+\eta(m-\eta)=0$ 的唯一正根：常数严格负，判别式严格大于 $b_\kappa^2$，另一根严格负。辅助点还不是世界。定义 $S_\kappa$ 为恰好通过 ALL 过滤的 $q$：

$$
q>0,\quad q\ne a,\quad s>2q,\qquad
3a-(q-a)m-H\theta=0,
$$

$$
\bar C-15q\theta-[(q-1)s+D_0](3\theta-h\eta)=0.
\tag{62.13}
$$

反向每个保留点用 (62.5)、(62.10) 固定一个 $P,g,d$。$s$ 的定义恢复 ordinary 及全部偶系数；$Q$ 与 (62.9) 恢复奇二次、一次；原常数恢复奇常数，三次自动。故 BOTH 恒等式及 SAME 六行全部恢复。只除已正的 $\theta$，正根方程反向恢复 (62.11) 及 SAME 第七行。正向任一实际普通世界推得此唯一正根、此 $s$ 及所有过滤。因此这是 ENTIRE 普通原世界 iff。等 $q$ 固定整个世界，不同 $q$ 给不同源；不能从此固定坐标唯一性推出普通集合单点。

### 62.3. 完整例外、ENTIRE 并集与实际末式

在 $q=a$，$D_0=0,H=3a$。原 $Q$ 迫 $T=\tau$；原常数给 $(a-1)\lambda=C-15a\tau$，即 $\lambda=\Lambda$。偶恒等式成为 $eg=K$，所以 $K(-s)=0$。严格 $s>2a$ 恰接受 $s=p$ 或 $v$，正根七只会给负 $s$。

因此全部例外为

$$
W_p=(P(a,p),\ p\tau(x+v)(x-7),\ d_*),\quad
W_v=(P(a,v),\ v\tau(x+p)(x-7),\ d_*),\quad d_*=a_0+7\tau V.
\tag{62.14}
$$

反向两源严格、首项非零、常数均为 $\Lambda$，各漂移固定为 $d_*$。它们满足 $eg=K,og=aK$，(62.3) 恢复 BOTH (62.6) 和全部 SAME 六原行，因而也证明每个 (62.4) 父确实达到。两个源因 $p\ne v$ 不同。

其实际第七 $J$ 检验为

$$
\kappa_p=(p+4)(v+3),\qquad \kappa_v=(v+4)(p+3),\qquad
\kappa_p-\kappa_v=v-p\ne0.
\tag{62.15}
$$

例如实际响应为 $z_p=d_*-\tau(p+4)(6+v)$，等于 $a_0+E(4)+2\tau\kappa_p$；交换得另一式。仅附 SAME 取得 $\kappa$ 实际匹配的例外，至多一个。由源域 $q=a/q\ne a$ 的穷尽及两边完整 converse，

$$
\mathcal K_\kappa=\{W_\kappa(q):q\in S_\kappa\}\cup
\{W_p:\kappa=\kappa_p\}\cup\{W_v:\kappa=\kappa_v\}
\tag{62.16}
$$

是 ENTIRE 原七行子片的精确等号。只合并整个三元组相同者。取得可达 iff 此集合非空；空集合不是成功停止。

定义

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta
=32\theta+n+\eta+5m-\kappa.
$$

原奇恒等式在七给 $o(7)g(7)=\lambda+R(7)+48qT$。实际 $JJ$ 迹为 $o(7)-2q/s$，$JM$ 比它多 $(s+4-2q)/s$。所以

$$
\begin{aligned}
f_{JJ}&=a_0+R(7)+\tau x,\quad x=48q\theta-2q\omega,\\
f_{JM}&=a_0+R(7)+\tau y,\quad y=48q\theta+(s+4-4q)\omega,\\
y-x&=(s+4-2q)\omega,\qquad s+4-2q>4.
\end{aligned}
\tag{62.17}
$$

共同加项为已取得的 $a_0+R(7)$，不随候选漂移改变。两例外在七增益为零，$x=y=48a$。普通与实际匹配例外的 $J,M$ 碰撞分别恰为 $x=48a,y=48a$，不除 $H,B_7$ 或 $\omega$。

### 62.4. N6：任意响应下有界坐标的归一化最终增益正性

**定理 62.1。** 对 EVERY (62.2)–(62.4) 实际普通世界，在 ANY 取得 $\kappa$ 下，若 $q\le3a-1$，则 $\omega>0$。

证明。已推得 $\theta>0,\eta<0$，故可置 $\rho=-\eta/\theta>0$。ordinary 给

$$
0<m/\theta=s+1-\rho,\qquad \rho<s+1.
$$

若 $h\ge7$，$(7-h)\eta\ge0$，故 $\omega=17\theta+(7-h)\eta>0$，包含 $h=7$。

若 $h<7$，则 $7-h=u+2-s>0$，严格 $\rho<s+1$ 给

$$
\frac\omega\theta=17-(u+2-s)\rho>
17-(u+2-s)(s+1).
$$

有限平方恒等式是

$$
(u+2-s)(s+1)=\frac{(u+3)^2}{4}-\left[s-\frac{u+1}{2}\right]^2.
$$

在所述坐标域，$0<u+3=2q+2a+4\le2(4a+1)$，且

$$
(4a+1)^2=16a^2+8a+1=17.
$$

故该乘积至多十七；前一严格不等式即使在平方为零及上界取等时仍给 $\omega/\theta>0$。两分支穷尽。另由 $a>3/4$ 有 $3a-1>5/4$。本证明不除 $H$，不替换原 $C$，不借正 $n$ 符号。∎

### 62.5. N7：原常数定向、低域排空与高域必要源隙

先保留原常数的方向。对偶重建且 $Q=L_{\rm res}=0$ 的元组，奇整个差只余常数 $-R_C$。在七减去偶式；$K(7)=0$ 与 (62.3) 给

$$
E(7)=-\Lambda-105\tau,\qquad R(7)=-\Lambda-48a\tau.
$$

置

$$
C_7=105-48a>57,\quad B_7=(q-1)(s+7)+D_0=(q-1)(h+2a)-1,
$$

$$
D_7=-B_7=(1-q)(s-2q)+5-4q.
$$

于是精确地

$$
R_C/\tau=C_7-(105-48q)\theta-B_7\omega.
\tag{62.18}
$$

因此 untouched 原 $R_C=0$ 恰为

$$
D_7\omega=(105-48q)\theta-C_7.
\tag{62.19}
$$

这是保留原 $C$ 与 $15qT$ 的方程，不是仅末函数投影。

**定理 62.2。** 实际普通世界中没有 $a<q\le1$。每个实际普通 $1<q\le5/4$ 均有 $\omega>0,B_7>0$，并满足必要条件

$$
h>\frac1{q-1}-2a
\quad\Longleftrightarrow\quad
s>2q-4+\frac1{q-1}
\quad\Longleftrightarrow\quad
s-2q>\frac{5-4q}{q-1}.
\tag{62.20}
$$

这些条件不宣称存在或充分性。

证明低域。令

$$
R_7=m+2-2(q+a),\quad b_7=H\theta=3a-(q-a)m,\quad
M_7=C_7R_7+48b_7.
$$

由 $H(a)=3a$ 与 $H(q)-H(a)=2(q-a)(1-q-a)$ 得

$$
H(\theta-1)=-(q-a)R_7,
$$

$$
H[(105-48q)\theta-C_7]=-(q-a)M_7,
$$

$$
M_7=(105-48q)m+306-210a-(210-96a)q.
\tag{62.21}
$$

在 $0<q\le1$，严格源首先给 $H=2+2q(1-q)\ge2$、$D_7\ge1$。在除它们以前，$M_7$ 的 $q$ 系数 $-(48m+210-96a)<0$，所以

$$
M_7\ge57m+96-114a>114a+39>0
$$

使用 $m>4a-1$。现在 (62.19) 才允许写

$$
\omega=-\frac{(q-a)M_7}{HD_7}.
$$

其符号为 $a-q$；但定理 62.1 在整个 $q\le1$ 给 $\omega>0$，因 $1<3a-1$。故 $a<q\le1$ 不可能。$q=1$ 被原方程排除，没有从源域删除；$q=a$ 不属于 ordinary，由完整例外处理。因此实际 ordinary 的 $q<1$ 部分必为 $q<a$。

证明高条带。$1<q\le5/4$ 时

$$
H(q)-H(5/4)=2(5/4-q)(q+1/4)\ge0,\qquad H\ge11/8>0.
$$

又 $R_7>2a+1-2q\ge2a-3/2>0$。$q-a>0$ 及 (62.21) 给已正的 $\theta<1$。因 $105-48q\ge45>0$，

$$
(105-48q)\theta-C_7<(105-48q)-C_7=-48(q-a)<0.
$$

定理 62.1 给 $\omega>0$，故原积 (62.19) 迫 $D_7<0$，即 $B_7>0$；这一步没有除 $D_7$。只在已知 $q-1>0$ 后，由 $B_7=(q-1)(h+2a)-1>0$ 除它，得到 (62.20)。在 $q=5/4$ 仍有效，此时源隙条件恰回到严格源。若另在 $\kappa\le8m$ 子片，还必须有 $s\ge4$。这些都是必要过滤，未给高条带的实际存在。∎

### 62.6. N8：全部实际 H 零族的取得响应定位

令

$$
\phi=\frac{1+\sqrt5}{2},\quad \chi=\phi-1,\quad
m_H=2(a+\chi)=\frac{3a}{\phi-a},\quad Z_H=m_H+1,
$$

$$
I_H=\left(2aZ_H-4a^2,\ \frac{Z_H^2}{4}\right).
\tag{62.22}
$$

**定理 62.3。** 对 EVERY $V\in I_H$、任意 $a_0$ 和两种 $\tau\ne0$ 符号，取 $m=m_H,n=V-2m_H-15$ 的 SAME 父，恰有一个实际 $H=0$ 世界。它的 $s_H>4$，实际取得 $\kappa_H<8m_H$，且两个例外都不匹配这个子片。反向，声明的负 $n$ 父类中每个实际 $H=0$ 世界都在此族。此唯一性只针对 $H=0$ 分支，不针对整个取得子片。

证明参数与范围。$\phi^2=\phi+1,\phi\chi=1$ 给

$$
H(q)=2(\phi-q)(q+\chi).
$$

唯一正零为 $q=\phi$。原 $Q$ 在 $H=0$ 直接迫 $m=3a/(\phi-a)$。因 $H(a)=3a$，$3a=2(\phi-a)(a+\chi)$，而 $\phi-a>0$，故 (62.22) 的两个 $m_H$ 表达一致。

$3/2<\phi<5/3$ 与 $3/4<a<4/5$ 给

$$
5/2<m_H<3,\quad 7/2<Z_H<4,\quad
Z_H-4a=2\phi-1-2a>0.
$$

所以 $I_H$ 的宽度为 $(Z_H-4a)^2/4>0$，并且 (62.4) 精确等价于 $V\in I_H$。移位根证明给不同实际 $p,v>2a$。所有该参数满足

$$
\frac94<V<4,\qquad -\frac{75}{4}<n<-16,\qquad
\frac{72}{5}<\bar C=7(1-a)V+15a<19.
\tag{62.23}
$$

这里下端 $V>2aZ_H-4a^2>4a^2>9/4$；$n$ 界由 $V,m_H$ 界给出。$\bar C$ 下界使用 $1-a>1/5,V>9/4,a>3/4$，上界使用 $1-a<1/4,V<4,a<4/5$。又

$$
11/2<u_H=2\phi+2a+1<6,\qquad -4<\eta=n/u_H<-8/3.
\tag{62.24}
$$

所有界严格，故整个父区间自动有 $n<0$。

对辅助 $s\ge2\phi$ 设

$$
\theta(s)=\frac{m_H-\eta}{s+1}>0,\quad h(s)=s+5-u_H,\quad
B(s)=\chi s-3\phi,\quad F(s)=3\theta(s)-h(s)\eta,
$$

$$
R_H(s)=15\phi\theta(s)+B(s)F(s)-\bar C.
\tag{62.25}
$$

$q=\phi$ 给 $D_0=-3\phi$，原 $Q$ 直接成立，$\theta$ 定义恢复 ordinary；$B=(q-1)s+D_0$，所以 EXACTLY $R_H=-R_C/\tau$。没有除 $H$，也没有改动原常数。

先证两个负值。在辅助边界 $s_0=2\phi$，$h_0=4-2a,B(s_0)=2-3\phi$。预测常数可精确改写为

$$
\alpha_Hm_H+\eta[(3\phi-2)h_0-\alpha_H],\qquad
\alpha_H=\frac{6(\phi+1)}{2\phi+1}.
$$

分母正；$\phi>1$ 给 $\alpha_H<4$。又 $3\phi-2>5/2,h_0>12/5$，故方括号大于 $6-4>0$。因 $\eta<0,m_H<3$，预测常数小于十二，而 $\bar C>72/5>12$。所以 $R_H(2\phi)<0$；边界不作世界。

由于 $4>2\phi$，坐标四严格位于源射线内。置 $\theta_4=(m_H-\eta)/5<7/5,h_4=9-u_H>3$，且 $B(4)=\phi-4$。于是

$$
R_H(4)=(18\phi-12)\theta_4+(4-\phi)h_4\eta-\bar C.
$$

$0<18\phi-12<18$ 给第一项小于 $126/5$。$4-\phi>7/3,h_4>3,-\eta>8/3$ 给第二项小于 $-56/3$。减去 $\bar C>72/5$，得到

$$
R_H(4)<54/5-56/3<0.
\tag{62.26}
$$

各负项的估计方向均由已证符号给出。

有限存在与全射线唯一性。连续表达式精确为

$$
R_H(s)=3(m_H-\eta)\chi+\frac{3(m_H-\eta)(\phi+1)}{s+1}
-\eta(\chi s-3\phi)(s+5-u_H)-\bar C.
$$

写作

$$
R_H(s)=c_Hs^2+b_Hs+d_H+\frac{A_H}{s+1},
$$

$$
\begin{aligned}
c_H&=-\eta\chi>0,&A_H&=3(m_H-\eta)(\phi+1)>0,\\
b_H&=-\eta[\chi(5-u_H)-3\phi],&
d_H&=3(m_H-\eta)\chi+3\eta\phi(5-u_H)-\bar C.
\end{aligned}
$$

取有限 $S$ 严格大于 $4,1,2|b_H|/c_H$ 及 $\sqrt{2(|d_H|+1)/c_H}$；分母 $c_H>0$，这些量有限。于是
$c_HS^2+b_HS+d_H>1$，且 $A_H/(S+1)>0$，故 $R_H(S)>0$。介值定理只在有限区间 $[4,S]$ 使用，给 $s_H>4$ 的根。

对 $2\phi\le x<y<z$，相邻有限割线斜率的差恰为

$$
\frac{R_H(z)-R_H(y)}{z-y}-\frac{R_H(y)-R_H(x)}{y-x}
=(z-x)\left\{\frac{A_H}{(x+1)(y+1)(z+1)}-\eta\chi\right\}>0.
\tag{62.27}
$$

倒数项的割线是 $-A_H/[(x+1)(y+1)]$；二次项的相邻割线差是 $-\eta\chi(z-x)$，仿射项消失，给上式。每个分母严格正。若严格源射线有两根 $y<z$，取 $x=2\phi$，边界到首根斜率为正，根到根斜率为零，与 (62.27) 矛盾。故整个严格射线恰有一个根，且它必为已证 $s_H>4$。

完整世界与 converse。在根处固定

$$
P=P(\phi,s_H),\quad \theta=\theta(s_H),\quad F=3\theta-h\eta,
$$

$$
\lambda=s_H\tau F,\quad \mu=s_H\tau(\eta-5\theta),\quad
\nu=s_H\tau\theta\ne0,\quad d=a_0-s_H\tau F.
\tag{62.28}
$$

源严格，整个增益非零。ordinary 恢复全部偶系数，原 $Q$ 不经除法成立，(62.9) 恢复原奇一次；$R_H=0$ 恰恢复
$C-15\phi T=[(\phi-1)s_H+D_0]F_{\rm orig}$。奇三次自动，故 BOTH (62.6) 及 SAME (62.1) 的前六行全部成立。每一行使用 SAME 源、整个增益及这个固定漂移。

反向实际 $H=0$ 必 $q=\phi,m=m_H,V\in I_H$，ordinary 必给此 $\theta(s)$，原常数必给 $R_H(s)=0$；唯一根与偶系数遂固定 (62.28) 的整个世界。因此量词是整个实际 $H=0$ 族。

定义此世界实际第七响应

$$
\kappa_H=(s_H+4)(5\theta+\eta),\qquad
z_H=a_0+E(4)+2\tau\kappa_H.
$$

未除的 (62.11) 证明 $z_H$ 就是同一世界原时钟六 $J$ 的实际响应。并有

$$
\kappa_H-8m_H=(s_H-4)(\eta-3\theta)<0.
\tag{62.29}
$$

同父 $0<p,v<Z_H<4$；两个实际例外检验满足

$$
\kappa_p-8m_H=(p-4)(v-5)>0,\qquad
\kappa_v-8m_H=(v-4)(p-5)>0.
$$

故此父任何 $\kappa\le8m_H$ 都没有匹配例外，特别 $\kappa_H$ 没有。其他普通候选仍由完整 $S_{\kappa_H}$ 保留，未证整个子片单点。其他六行普通分支不被声称共享 $\kappa_H$。∎

定理 62.3 只否定“$\kappa\le8m$ 迫所有实际 ordinary 的 $q<1$”这条覆盖捷径。$q=\phi>1$ 的实际端点不是碰撞对；另一个六行世界也不是 SAME 子片的端点见证。这里没有反驳末单射或选择器。

### 62.7. N9：固定 κ≤8m 的完整原世界对 iff

所有参数固定 SAME 已达到的 $a_0,\tau,m,n$（其中 $n<0$）和 SAME 取得 $\kappa\le8m$，保留 (62.4)。局部 $r$ 是第二个 $q$ 坐标，不是源元 $r_0$；$t$ 是第二端的 $\theta$，不是原时钟。

取

$$
0<q<r,\quad q,r\ne a,\quad \ell=r-q>0,\quad s\ge4,\quad \rho>0,\quad t>0.
$$

设

$$
\begin{aligned}
u&=2q+2a+1>0,&U&=2r+2a+1=u+2\ell>0,\\
K_p&=15+(s+1)\rho>0,&L_p&=s-1+\rho>0,\\
D_p&=uK_p>0,&R_p&=2\rho/D_p>0,\quad V_p=s^2-16\ge0,\\
S&=s+\ell R_pV_p,&\alpha&=R_pL_p,\quad \beta=R_pK_p=2\rho/u,\\
M_p&=S+1-\rho.
\end{aligned}
\tag{62.30}
$$

$V_p$ 不是父乘积 $V$。定义两端

$$
(q_1,s_1,\theta_1,\eta_1)=
(q,s,t(1+\ell\alpha),-\rho tU/u),\qquad
(q_2,s_2,\theta_2,\eta_2)=(r,S,t,-\rho t).
\tag{62.31}
$$

两端 $\theta_i>0,\eta_i<0$ 在除法前已明。

**定理 62.4。** 所有不同实际普通世界对在 SAME 子片中，按 $q_1<q_2$ 排序后，恰为 (62.30)–(62.31) 通过以下 ALL 过滤所得对：

$$
s>2q,\qquad S>2r,
\tag{62.32}
$$

$$
tM_p=m,\qquad -U\rho t=n,\qquad (S+4)(5-\rho)t=\kappa,
\tag{62.33}
$$

$$
t[(r-a)M_p+H(r)]=3a,\qquad
M_p=H(q)\alpha+2(q+r-1),
\tag{62.34}
$$

以及 EACH 端的 untouched 原常数

$$
\begin{aligned}
h_i&=s_i+5-(2q_i+2a+1),\quad F_i=3\theta_i-h_i\eta_i,\\
C_i&=\bar C-15q_i\theta_i-[(q_i-1)s_i+D_0(q_i)]F_i=0,
\qquad i=1,2.
\end{aligned}
\tag{62.35}
$$

严格父域、SAME $a_0,\tau,m,n,\kappa$、BOTH 严格源、BOTH $Q$、BOTH 原 $C$ 均是必要的保留条件。

证明必要性。不同实际世界若 $q$ 相同，由 (62.12)–(62.13) 固定整个三元组，矛盾。因此可排序 $q<r$。取 $s=s_1,t=\theta_2>0,\rho=-\eta_2/t>0$，由 (62.11) 得 $s\ge4$。SAME $n$ 给

$$
\eta_1=-\rho tU/u,\qquad
\beta=\frac{\eta_2-\eta_1}{\ell t}=2\rho/u>0.
$$

先只定义 $\alpha=(\theta_1-\theta_2)/(\ell t)$，不预设其符号；置 $k_s=(s_2-s_1)/\ell$。相减 SAME $m$ 和 SAME $\kappa$ 的两式，给

$$
k_s=(s+1)\alpha-\beta,\qquad
k_s(5-\rho)=(s+4)(5\alpha-\beta).
$$

消元不除 $5-\rho$，得到

$$
\alpha[15+(s+1)\rho]=\beta[s-1+\rho].
$$

现在 $s\ge4,\rho>0$ 使两括号都正，故直接由固定方程推得
$\alpha=\beta L_p/K_p=R_pL_p>0$。无需借旧屏障或次序定理。于是

$$
k_s=R_p[(s+1)L_p-K_p]=R_p(s^2-16),
$$

给全部坐标及 $S=s_2$，包含 $s=S=4$。第二端给 (62.33) 和第一个 (62.34)。从 $Q_2-Q_1=0$ 得

$$
0=\ell m+t[H(r)-H(q)-\ell H(q)\alpha].
$$

$H(q)-H(r)=2\ell(q+r-1)$，只除已正的 $\ell t$ 后得第二个 (62.34)。两端原常数各自给 (62.35)。必要性完成。

证明充分性。取通过 ALL 过滤的任意元组。首先

$$
u\eta_1=U\eta_2=-U\rho t=n.
$$

又 $(s+1)\alpha-\beta=R_pV_p$，故

$$
(s+1)\theta_1+\eta_1
=t[(s+1-\rho)+\ell((s+1)\alpha-\beta)]
=t(S+1-\rho)=m.
$$

第二端的 ordinary 直接由 $tM_p=m$ 成立。再有精确恒等式

$$
5\alpha-\beta=R_p(s-4)(5-\rho),\qquad
S-s=\ell R_p(s-4)(s+4).
$$

因此

$$
(s+4)(5\theta_1+\eta_1)=(S+4)(5-\rho)t=\kappa,
$$

第二端由过滤也给 SAME $\kappa$。这里保留 $5-\rho=0,\kappa=0,s=4$，没有取消它们。

第一个 (62.34) 恢复第二端 $Q$；将第二个乘 $\ell t$ 并反向上述 $Q$ 差式，恢复第一端 $Q$。两个 $C_i=0$ 各自独立保留。对 EACH 端固定

$$
P_i=P(q_i,s_i),\quad
g_i(x)=s_i\tau[\theta_i x^2+(\eta_i-5\theta_i)x+F_i],\quad
d_i=a_0-s_i\tau F_i.
\tag{62.36}
$$

严格源过滤给严格 $P_i$，$s_i\tau\theta_i\ne0$ 给整个非零增益。SAME $m,n$ 恢复每个偶系数及 (62.9) 的原一次式；各 $Q$ 与 untouched $C_i$ 恢复奇二次和常数，三次自动。因此 EACH 世界满足 BOTH 整个恒等式、ALL SAME 六行及 SAME 第七响应 $z$。不同 $q,r$ 给不同源及整个目标，完成原世界对 iff。∎

没有除 $H,B_7,D_7,s-4,s-4q,5-\rho$、样本、残式首项或判别式。$H=0$ 可在任一端，$D_7,B_7$ 零点仍按方程保留。$q=1$ 在原坐标域合法，由定理 62.2 和完整过滤拒绝。若实际对跨低、高两域，则必 $q<a,r>1$，同一 iff 仍适用。定理不主张存在不同普通对，且不延伸到 $\kappa>8m$。

### 62.8. N9：正分母的精确末比较多项式

在定理 62.4 的全部过滤下，定义以下多项式：

$$
\begin{aligned}
B_p&=8L_p-K_p=8s-23+(7-s)\rho,\\
C_p&=32L_p-K_p=32s-47+(31-s)\rho,\\
A_p&=s+4-4q,\\
W_p^{\rm pol}&=D_p[17+(s-U-2)\rho]+2\ell\rho^2V_p,\\
P_J&=D_p[7+(U+2-s)\rho]-2\ell\rho^2V_p+2q\rho B_p,\\
P_M&=48D_p^2-(96q\rho L_p+2A_p\rho C_p)D_p
+(2\rho V_p-4D_p)W_p^{\rm pol}.
\end{aligned}
\tag{62.37}
$$

$W_p^{\rm pol}$ 是多项式名，不是例外世界 $W_p$。

**定理 62.5。** 对上述每个实际对，

$$
x_2-x_1=\frac{2\ell tP_J}{D_p},\qquad
y_2-y_1=\frac{\ell tP_M}{D_p^2}.
\tag{62.38}
$$

证明完整有限消元。第二端的整个增益给

$$
w_2:=\omega_2/t=17+(S-U-2)\rho
=\frac{W_p^{\rm pol}}{D_p},
$$

因为 $S=s+2\ell\rho V_p/D_p$。两端 SAME 子片的
$\omega=32\theta+n+\eta+5m-\kappa$ 给

$$
\omega_1/t=w_2+\ell(32\alpha-\beta).
$$

在 $x_i=48q_i\theta_i-2q_i\omega_i$ 中相减、按 $\ell$ 收集，得

$$
\frac{x_2-x_1}{2\ell t}=24-w_2+q(8\alpha-\beta).
$$

而 $8\alpha-\beta=2\rho B_p/D_p$。代入 $w_2$ 后分子为
$24D_p-D_p[17+(s-U-2)\rho]-2\ell\rho^2V_p+2q\rho B_p$，恰为 $P_J$，得到第一式。

令 $A_1=A_p,A_2=A_p+\ell(k_s-4),k_s=R_pV_p$。在
$y_i=48q_i\theta_i+A_i\omega_i$ 中相减得

$$
\frac{y_2-y_1}{\ell t}
=48-48q\alpha+(k_s-4)w_2-A_p(32\alpha-\beta).
$$

逐项代入

$$
\alpha=\frac{2\rho L_p}{D_p},\quad k_s=\frac{2\rho V_p}{D_p},\quad
32\alpha-\beta=\frac{2\rho C_p}{D_p},\quad w_2=\frac{W_p^{\rm pol}}{D_p},
$$

乘 $D_p^2$，恰得 $P_M$ 的全部四项，得到第二式。$B_p,C_p$ 的每个系数直接由 $L_p,K_p$ 收集；没有引入可行中间世界。∎

$\ell,t,u,K_p,D_p$ 均严格正，故归一化 $J,M$ 差的符号分别恰为 $P_J,P_M$ 的符号。实际响应差再乘 SAME $\tau\ne0$：负 $\tau$ 反转大小，不改变相等或不等。

WITH 全部固定父、固定 $\kappa$、BOTH 严格源、BOTH $Q$ 和 BOTH 原 $C$ 过滤，$P_J=0$ iff 此实际普通对在 $J$ 碰撞，$P_M=0$ iff 在 $M$ 碰撞。脱离这些过滤，多项式零点不是实际碰撞。没有证明任一多项式在整个过滤关系上有普遍符号，也没有给出可行碰撞元组。

同一子片两动作均失败，可以由 TWO DIFFERENT 普通对给两零式，或涉及实际匹配例外。它不要求一个普通对同时满足 $P_J=P_M=0$。精确关系消元是新的约束进展，不是已经完成的选择器。

### 62.9. 继承的低坐标守卫与仅选中响应的完整逆

复用的负 $n$ 屏障为每个实际普通六行端点
$s>\sigma=(1+6a)/(4+2a)>1$；在 SAME 取得子片上 $q$ 增加时 $\theta$ 严格下降；$\kappa<8m$ 时 $s$ 严格增加，$\kappa=8m$ 时 $s=4$，$\kappa>8m$ 时 $s$ 严格下降。它们均为原式的必要后果，不替代原常数。

复用的低坐标结果还包括：实际 $0<q<1$ 有 $w=\omega/\theta<24$；固定 $\kappa\le8m$ 时 ordinary 低坐标 $J$ 严格单射。原来的上低坐标 $a<q<1$ 的 $M$ 单射只保留其范围；定理 62.2 已证明这里实际该部分为空。低域 $M$ 带在剩余 $q<a$ 有 $y>48a$，不等于两个低普通端点之间的 $M$ 单射。

该 $M$ 带可由精确原式直接核对。令 $A_7=s+4-4q>0$、$U_7=m-u\theta$。在 $0<q<1$ 已有 $H,D_7>0$，且

$$
HU_7=3[(m-2a)q-2],\qquad q\theta-a=-(q-a)U_7/3.
$$

所以

$$
y-48a=-(q-a)W_7,\qquad
W_7=16U_7+\frac{A_7M_7}{HD_7}.
$$

$m-2a>0$ 给 $[(m-2a)q-2]>-2$；(62.21) 给 $M_7>114a+39>120$，且

$$
\frac54A_7-D_7=(q+1/4)(s-2q)+\frac32q>0.
$$

故 $HD_7W_7>-96D_7+A_7M_7>A_7(M_7-120)>0$。实际低坐标必 $q<a$，遂 $y>48a$，与匹配例外的 $y=48a$ 分离。

另一个复用桥梁是普通 $g(7)\ne0$，只需 $\Sigma,\tau\ne0,K(7)=0,q\ne a$。给出其条件反证以限定平方的用途。置 $\zeta=(L+5A)/u$，一般 ordinary 偶式给
$g/s=T(x^2-5x+3)+\zeta(x-h)$。若 $g(7)=0$，BOTH 恒等式给

$$
\lambda-\Lambda=105(\tau-T)=48(a\tau-qT),\qquad
(35-16q)T=c_*\tau,\quad c_*=35-16a.
$$

$21<c_*<35,\tau\ne0$ 先证明 $T$ 和 $35-16q$ 都非零。置 $k_0=105/c_*\in(3,5)$，原 $Q$ 仅除已非零 $T$、取消已声明 $q-a$ 后给
$A/T=u-k_0$，ordinary 给 $\zeta/T=4-h-k_0$。于是

$$
\frac{g(7)}{sT}=17+(7-h)(4-h-k_0)
=\left[h-\frac{11-k_0}{2}\right]^2+\frac{68-(k_0+3)^2}{4}>1,
$$

矛盾。平方仅在反设末零方程下使用，不能作无条件增益界。因此一个 ordinary 与匹配例外若在 $J$ 碰撞，由 $(s+4-2q)\omega\ne0$ 知这 TWO-POINT 对在 $M$ 分离，仍不能据此保证整个更大子片的 $M$ 单射。

精确继承守卫为

$$
G_{\rm low}:\quad \kappa\le8m\quad\text{且 ENTIRE }\mathcal K_\kappa
\text{ 的每个 ordinary 都有 }q<1.
$$

它是完整取得候选集合的性质，不是隐藏真实源标签。可达集合单点就在七 TOTAL 停。$G_{\rm low}$ 下，无匹配例外或没有 ordinary 的 $x=48a$ 时，低普通 $J$ 单射与至多一个例外给 ENTIRE $J$ 单射。若有例外 $J$ 碰撞，且低 ordinary 至多一个，则低 $M$ 带给 ENTIRE $M$ 单射。这是充分守卫，不声称该基数条件对 $M$ 成功必要。守卫以外没有由这些低域定理给出的动作保证。N8 证明 $G_{\rm low}$ 即使在 $\kappa<8m$ 也不普遍成立；N9 增加精确关系而未补齐这个守卫缺口。

对 ANY 已证明某动作在 ENTIRE 非空 $\mathcal K_\kappa$ 单射的取得记录，动作只依取得数据与完整候选预测选择。取得 ONLY 选中动作的时钟七实际响应 $f$，置

$$
h_{\rm obs}=(f-a_0-R(7))/\tau.
$$

选 $J$ 就仅保留 $x=h_{\rm obs}$，选 $M$ 就仅保留 $y=h_{\rm obs}$。真实世界及 (62.16) 给存在，ENTIRE 单射给唯一。普通与例外的完整 converse 恢复 ALL SAME 七行，所选末等式恢复第八行；反向每个兼容世界都通过。所得是一个严格源、一个整个非零增益及一个固定漂移的必要且充分集合论逆。没有未选响应、有效求解、枚举、可计算性或有限精度保证。

已完成的 $n\ne0,\kappa=8m$ ENTIRE 选择器，包括负 $n$ 的 $s=4$，保持其原范围。另保留 $\Gamma>0$、$\Gamma=0$ 的唯一仿射 ordinary 加例外及相应逆、$N=0$ 的精确两例外父和七 TOTAL 恢复，后者在 $(p-2)(v-2)=17,p,v>2,p\ne v$。$\mathsf B_0$ 与独立有限纤维界只保留各自范围；它们不是 N6–N9 新成果。分别已知类的逆不自动成为未知并集的逆。

### 62.10. SAME 父坏 M 的 FULL 等号与所有已服务守卫

本父实际时钟六 $M$ 的迹为 $e(6)$，偶恒等式给

$$
h_M=a_0+E(6)+48T,\qquad
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
$$

这把指定 FULL $M$ 子片固定为 $T=\tau$。为得完整等号，必须排除 ALL ordinary $T=\tau$，不能只排末零者。

反设这样的 ordinary 存在。$Q$ 给

$$
u=m+3=Z+2,\quad q=(Z+1)/2-a,\quad \delta=q-a>1/2.
$$

令 $h_o=s-Z+7>8-2a>6$。原一次式及每个偶系数给

$$
V=(7-h_o)Z+23-2h_o,\quad
g=s\tau(x^2-h_ox+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-9/2)^2+11/4>0.
$$

untouched 原常数精确为

$$
-7V=s\chi_o-\frac{\delta(h_o-4)(h_o-6)(h_o-8)}{1-a}.
\tag{62.39}
$$

确切依据是 $(a-1)(-7V)-15\delta=[(q-1)s+D_0]\chi_o$。移去 $(a-1)s\chi_o$ 后余项为 $\delta[(h_o-9)\chi_o+15]$，括号恰为三个因子之积，故原 $15\delta$ 没有丢失。

负左边、$s\chi_o>0,\delta>0,h_o>6$ 迫 $h_o>8$。由 $V>4a^2,Z>4a$ 及 $7-h_o<0$，

$$
V<23+28a-(4a+2)h_o,\qquad
h_o<\frac{19+30a}{4a+2}<17/2,
$$

最后比较等价于 $4a-2>0$。所以正三因子积小于 $45/8$，$\chi_o>15$ 因 $\chi_o-15=(h_o-8)(h_o-1)>0$，且 $1-a>1/5$。因而该积除以 $(1-a)\chi_o$ 小于 $15/8$。严格源给 $0<\delta<q<s/2$，(62.39) 反而迫 $-7V>s\chi_o/16>0$，矛盾。这排除两种 $\tau$ 符号下的 ALL ordinary $T=\tau$。

完整例外列表遂证明

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}
=\{W_p,W_v\}.
\tag{62.40}
$$

两增益在七为零、固定漂移均为 $d_*$，所以 BOTH 实际末 FULL 片都恰为 SAME 对。它们在父、指定 $M$ 子片、两末片和所有已服务共同祖先中始终为不同完整目标，保持全部相应非单点停止守卫。其第七 $J$ 响应不同，故不构成 SAME $J$ 子片碰撞。

FULL 包含逻辑也保持。对同历史 $\mathcal K\subseteq\mathcal K'$，每个 SAME 实际动作 $E$、响应 $z$ 的片都有

$$
\{W\in\mathcal K:h_E(W)=z\}\subseteq
\{W\in\mathcal K':h_E(W)=z\}.
$$

定义 $L_0$ 为有两个不同完整目标，$L_{h+1}$ 为父非单点且 EACH 动作有一个实际 FULL 子片满足 $L_h$。基步不同性随包含保持；归纳保留每个动作的原响应见证，对其子片用包含与归纳假设，父守卫也保持。因此任意基数、任意有限深度的失败向上保持，但不服务早期未取得的另一臂。

条件地，若 SAME 取得 $J$ 子片实际已有一个 $x$ 碰撞对及一个 $y$ 碰撞对，最多四个完整端点支持这两终端 duty；加 SAME 父坏 $M$ 对至多再加两个。并集保留每个原碰撞在相应实际 FULL 响应片中，包含归纳保持 BOTH 动作、两末 FULL duty、已服务祖先及 ALL 停止守卫。这只是已实现局部失败的条件至多六端点支持，不证明实现、最小支持、尖锐性、非终端抽对或原根失败；也不同于独立的 ENTIRE 子片基数界。

### 62.11. 整个 INERT 全局共同实现合同

以下合同保持 INERT、UNEXECUTED、UNFULFILLED；原 atomic-relation-generation-family 内容不参与本卷证明。

保留 ALL 256 终叶槽 $\sigma=(w,\varepsilon)$，$w\in\{J,M\}^7,\varepsilon\in\{0,1\}$；ALL 254 非空实际前缀 $v$，其原长度 $i=1,\ldots,7$、实际即时左乘积 $A_v$ 及 EVERY 后代。置

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,\ it_v(P),\ i^2t_v(P),\ i^3t_v(P)).
$$

对 EACH 前缀及 EACH 规定的非代表后代 $\sigma$，与 SAME 前缀代表 $\varrho$ 保留整行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\varrho)x_\varrho=0.
$$

ALL 行属于 ONE SAME ENTIRE $1538\times1024$ 关系，继承层规格为 $254,252,248,240,224,192,128$。ONE 共同堆叠向量包含 ALL 256 WHOLE 四系数增益块；每个整个块非零，每个适用的 SAME 源终叶 WHOLE 四分量差 $x_{(w,0)}-x_{(w,1)}$ 非零。ALL 严格源、ALL 祖先关系、BOTH 动作 duty 和 ALL 停止守卫必须在 SAME 向量及 SAME 世界同时成立。

每槽自始固定

$$
g_\sigma(x)=\sum_{h=0}^3x_{\sigma,h}x^h,\qquad d_\sigma=a_0-x_{\sigma,0}
$$

跨其全部原行。仅合并整个 $P,g,d$ 相同者。二次限制 $x_{\sigma,3}=0$ 同时作用于 ALL 块。尺寸是保留的符号规格，不是执行枚举或计算的读数。局部高坐标族、精确对关系、终端碰撞、条件六世界支持、较小关系、选定支持、分别路径或分别动作臂解、遗漏后代、逐行 refit 或分别守卫向量，均不履行这个共同实现。这里没有生成实例、求秩、求核、区间或证书计算。

### 62.12. 精确未决义务、零层与证据界限

一般负 $n$ arbitrary-response ENTIRE 选择器仍为 OPEN。正完成须对 EVERY 达到的声明父和 EVERY 可达 SAME $\kappa$，证明单点七 TOTAL 停，或至少一个实际末函数在 ENTIRE ordinary 加实际匹配例外的集合单射；只依取得记录选择它，并由 ONLY 所选实际响应及完整 converse 给唯一原世界逆。

$\kappa\le8m$ 仍不完整：N8 给实际高 $q$ 端点，N9 未给全过滤 $P_J/P_M$ 的普遍符号，亦未排净高域或跨域的实际普通对和混合例外碰撞。完成可允许不同动作在不同子片互补；不必证明两多项式处处同号、每项统一严格正或所有 ordinary 子片单点。这些更强路线并非原目标必要条件。$\kappa>8m$ 仍为 OPEN，且在 N9 参数范围之外。

负完成须在 ONE SAME 达到父和 ONE SAME 取得 $J$ 响应中，实际实现

$$
U_1\ne V_1,\quad U_2\ne V_2,\qquad
x(U_1)=x(V_1),\quad y(U_2)=y(V_2),\qquad U_i,V_i\in\mathcal K_\kappa.
$$

两对可不同、可重叠，也可涉及实际匹配例外；不是要求一个共同 $P_J=P_M=0$ 对。每端同时通过严格源、一个整个非零增益、一个固定漂移、BOTH 原残式、SAME 父和 ALL SAME 七行。还须保留 SAME 父坏 $M$ FULL 对、BOTH 末 FULL 片、BOTH 动作、全部已服务祖先和 ALL 停止守卫。N8 与 N9 没有实现任一所需碰撞对，也不证明普通非单点子片存在。

原 FULL 二次八 TOTAL 恢复 versus original-root $L_7$，以及原 FULL 三次八 TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$，仍为 OPEN。本卷不强迫任意根策略走 $JMJMJ$，不完成早期未服务臂、不受限同父 $L_3$、原根失败树、minimax、第八读必要性或第九读上界。三次增益乘线性迹可为四次，四个偶节点相等仍可留非零倍 $x(x-2)(x-4)(x-6)$；二次逆不检测隐藏三次次数，也不恢复未经跨类证明的未知并集。

严格源边界 $q=0,s=2q,r_0=0$ 或一、$b=0,c_{\rm src}=0$，父边界 $p=2a,p=v,\tau=0$，以及无限或极限源均不补作世界。父条件只约束声明的两例外父类，不约束无关根模型父。辅助 IVT 边界、割线点和多项式变量不是世界，必须通过全部原过滤后才有原世界意义。

合法 $H=0,s=4,s=4q,b=1/2,r_0=1/2$、两种 $\tau$ 符号、个别系数/样本/观察零、采样或非采样根、重增益根、重残式根、首项取消和恒零次残式均保留至原式拒绝。$q=1$ 由 N7 原方程排空；ordinary 真正二次及 $\theta,F$ 正性是推导；例外 $g(7)=0$ 合法，固定漂移也可将非零增益贡献抵消成零观察。

所有除法先证条件：源逆用 $b,s>0$；归一化用 $\tau\ne0$ 而不假设其正；ordinary 先声明 $q\ne a$；$u>0$ 先于 $\eta$，$K_{\rm pos}>0$ 先于 $\theta>0$ 及其除法。N6 不除 $H$。N7 先证低域 $H,D_7>0$ 才作受限除法，高条带先由原积推出 $D_7<0$，再只除 $q-1>0$。N8 的 $\phi-a,u_H,s+1,c_H$ 及割线分母先正。N9 的 $\ell,t,u,U,K_p,L_p,D_p$ 先正，不除 $5-\rho,s-4,H,B_7,D_7$。末零反证先证 $T,35-16q$ 非零。没有取消未知源/漂移差、未知响应、$\lambda,\mu$、增益样本、残式首项、根重数或未证判别式。

证据仅为经过独立符号审阅的 fallible UNEXECUTED 数学。没有执行公式求值、代入、数值、导数、递推、枚举、CAS、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean/D5/Blueprint/Reg、摄入或消化。不给 kernel 或数值认证、ML/NN、物理、噪声、稳定性、连续逆、有限精度、可计算性、有效判定、效率、复杂度、资源、最小支持、尖锐性、文献穷尽、外部原创性或优先权认证。

## 追加锚（本行以下为增补区）
