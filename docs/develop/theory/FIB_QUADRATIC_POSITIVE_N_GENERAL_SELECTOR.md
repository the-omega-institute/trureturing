# FIB 二次标志父的正 n 原常数屏障与任意响应完整末 M 逆

本文独立续为第 61 节。固定一个实际六读 $JMJMJ$、$\beta=7$ 标志父，在 $n>0,\Gamma<0$ 的整个范围，原奇插值常数强制每个实际下侧普通世界满足 $s>4$。结合有限同子片比较、上侧单射及三带分离，对任意实际取得的第七 J 响应，末 M 在 ENTIRE 原兼容子片单射。单点子片七次 TOTAL 停止；否则在原时钟七只选择 M，八次 TOTAL 唯一恢复整个 $P,g,d$。

此结论包括 $\Gamma<-(8a+9)$，不要求特殊响应 $\kappa=8m$。第 60 节的 $-(8a+9)\le\Gamma<0$ 恢复带是本节完整正 n 局部完成的复用特例。新增结果是原常数下侧屏障及其完整选择器后果；源图谱、上侧比较和有限对比较是所需的复用桥梁，以下给出完整使用范围与证明，不重复既有全表。

本文是 `repo-derived` 参考理论，证据为可出错的 **UNEXECUTED 符号数学**，不是 Lean/kernel 或执行证书。负 n 的端点屏障仅提供方法启发，其符号和结论不作为本节前提。原 FULL 二次、三次根问题仍为 OPEN；局部完成不证明八读必要、普通世界或非单点子片存在、有效求根、资源界、外部原创性或优先权。

## 61. 正 n 原常数屏障与完整原世界选择器

### 61.1. 原世界、动作与取得历史

一个世界从开始固定为整个三元组

$$
W=(P,g,d),\qquad P=\begin{pmatrix}r&b\\c_{\rm src}&1-r\end{pmatrix},\quad
0<r<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r(1-r),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
\tag{61.1}
$$

源四元严格正、迹一、行列式零，非零迹排除秩零。不同候选可有不同但各自固定的 d；相等与去重只按整个 $P,g,d$。原域保留两种非零 gain 尺度符号、常数与仿射、零系数、零读数、采样或非采样根、重根及合法消去；进一步排除须来自原式。

动作即时左乘，原时钟与一个整 gain 不变：

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{61.2}
$$

对任意 A，两个对角元相加给

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r+A_{21}b+A_{12}c_{\rm src}.
$$

左 J 交换旧两行，左 M 取旧第二行和旧两行之和。沿 $JMJMJ$，乘积依次为

$$
I,\ J,\ \begin{pmatrix}1&0\\1&1\end{pmatrix},\
\begin{pmatrix}1&1\\1&0\end{pmatrix},\
\begin{pmatrix}1&0\\2&1\end{pmatrix},\
\begin{pmatrix}2&1\\1&0\end{pmatrix}.
$$

置 $j=b+c_{\rm src}$、$a_0=y_0$。下面所定义的取得插值使六原行恰为

$$
\begin{aligned}
d+g(0)&=a_0,\\
d+jg(1)&=a_0+R(1),\\
d+(1+b)g(2)&=a_0+E(2),\\
d+(j+r)g(3)&=a_0+R(3),\\
d+(1+2b)g(4)&=a_0+E(4),\\
d+(j+2r)g(5)&=a_0+R(5).
\end{aligned}
\tag{61.3}
$$

所选 J 后 $Q_6=Q_4$，实际取得第七行

$$
h_J=d+(1+2b)g(6)=z_{\rm obs}.
\tag{61.4}
$$

再选 J 或 M 的实际末迹分别为 $j+2r$、$1+j+r+2b$，所以预测函数是

$$
f_{JJ}=d+(j+2r)g(7),\qquad f_{JM}=d+(1+j+r+2b)g(7).
\tag{61.5}
$$

原时钟零至五为六次 TOTAL，六为七次 TOTAL，七为八次 TOTAL。相同乘积仍采样新时钟的 SAME gain。实际只取得所选动作的响应，没有重置、复制、跳读、源或根标签、额外端口、未选响应、逐行 gain 或响应后漂移 refit。

记 $\mathcal S(\mathcal H_5)$ 为满足 (61.1)、全部六原行 (61.3) 的 ENTIRE 父，$\mathcal H_5=(y_0,\ldots,y_5)$。对所取得响应，定义

$$
\mathcal K_z=\{W\in\mathcal S(\mathcal H_5):h_J(W)=z_{\rm obs}\}.
$$

实际取得性使此集合非空；这不是源投影的候选集。

### 61.2. 固定实际父与导出的严格界

令 $x_i=y_i-a_0$，取得插值为

$$
E(t)=Lt+At^2,\quad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
\tag{61.6}
$$

这些式恢复偶节点 $0,2,4$ 与奇节点 $1,3,5$；至多二次之差有三个不同根即恒零，故插值唯一。C 始终是这个取得的原奇常数。

置

$$
a=\frac{\sqrt{17}-1}{4},\quad 2a^2+a=2,\quad
\frac34<a<\frac45,\quad \epsilon=1-a,\quad c=2a+1,\quad d_a=4a+1.
$$

于是 $1/5<\epsilon<1/4$、$ac=2$、$\epsilon(c+2)=1$；a 的严格界由正平方比较得到，c 不表示源元 $c_{\rm src}$。

固定 ONE SAME 实际父，明确假设为

$$
B+5D=a(L+5A),\qquad \tau=\frac{D-aA}{3a}\ne0,
$$

$$
U=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5),\quad
\Lambda=\frac{C-15a\tau}{a-1},
$$

$$
K=\Lambda+E+\tau U=\tau(t+p)(t+v)(t-7),\qquad p\ne v,\quad p,v>2a.
\tag{61.7}
$$

以下直接以此为假设；不须在本文重做其他父的标志分类。置

$$
Z=p+v=m+1,\quad V=pv=n+2m+15,\quad n=V-2Z-13>0,
$$

$$
\Gamma=n-d_am-6a<0,\qquad G=-\Gamma>0.
\tag{61.8}
$$

整 K 的降幂系数为 $\tau(1,Z-7,V-7Z,-7V)$；和 $\Lambda+E+\tau U$ 比较，再用 (61.7) 的定义，得到全部父系数

$$
\begin{aligned}
A&=\tau m,&L&=\tau(n-5m),\\
D&=a\tau(m+3),&B&=a\tau(n-5m-15),\\
C&=\tau\bar C,&\bar C&=7\epsilon V+15a,\qquad\Lambda=-7\tau V.
\end{aligned}
\tag{61.9}
$$

因为 $U-V_o=3t^2-15t+15$，二次、一次、常数逐项给原恒等式

$$
R=aE+a\tau(U-V_o)+(a-1)\Lambda.
\tag{61.10}
$$

**父界。** 本父导出 $p,v>2$、$m>5+8a>11$。事实上 $(p-2)(v-2)=n+17>17$，非正积不可能；若两因子同负，$p,v>2a>3/2$ 使乘积小于 $1/4$。故两因子正。不同 p、v 给 $V<Z^2/4$，n 正给 $V>2Z+13$，于是 $(Z-4)^2>68$；$Z>4$ 选择 $Z>4+2\sqrt{17}$，即所述 m 界。

定义

$$
q_0=a+\frac{3a}{m},\quad b_0=a(m+3)=mq_0,\quad
l_0=(2-a)m-3a,\quad l_1=(3-2a)m-6a.
\tag{61.11}
$$

由 $3a/\epsilon=6+6a<5+8a<m$，得 $a<q_0<1$。又 $l_0=m+(\epsilon m-3a)>0$，$l_1-l_0=\epsilon m-3a>0$。这些均是原父假设的结论，未另加源或尺度承诺。所有比较固定 SAME $a_0,\tau,m,n$，不拼接不同父。

### 61.3. 严格源双射、BOTH 整恒等式与所有系数

严格源精确双射为

$$
q=\frac rb>0,\quad s=\frac2b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},\qquad
j=q+\frac{2(1-q^2)}s.
\tag{61.12}
$$

正向 $s-2q=2(1-r)/b>0$，秩一给 $c_{\rm src}=r(1-r)/b$。反向所写四元严格正、迹一且 $bc_{\rm src}=r(1-r)$，非零迹使秩恰一，并恢复 q、s。故没有遗漏原严格源。

置

$$
\delta=q-a,\quad u=2q+c>0,\quad D_0=2-q-2q^2=-\delta u,\quad
H=D_0+3q=2+2q-2q^2,
$$

$$
e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,\quad T=\nu/s.
\tag{61.13}
$$

e、o 在各原偶、奇节点分别等于 (61.3) 的实际迹。

**六原行 iff。** 在严格源与整个 $g\ne0$ 下，六原行等价于 $d=a_0-\lambda$ 及 BOTH 整多项式恒等式

$$
-\lambda+eg=E+TU,\qquad -\lambda+og=R+qTV_o.
\tag{61.14}
$$

必要性：初行固定 d。偶 discrepancy 有根 $0,2,4$，次数至多三、三次系数 T；减 TU 后至多二次且有三个不同根，故恒零。奇式同理用 $1,3,5$ 与 qT。充分性：在各原节点取值恢复全部六行，包括零样本，使用 SAME gain 和固定 d。

完整偶升幂系数比较为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T),
$$

从而

$$
\nu=sT,\quad\mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad
\lambda=sF_{\rm orig},\quad d=a_0-sF_{\rm orig}.
\tag{61.15}
$$

完整奇左升幂系数是

$$
\left((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
\ q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\right),
$$

奇右升幂系数是

$$
(C-15qT,\ B+23qT,\ D-9qT,\ qT).
$$

代全部偶重建后，三次自动相等，余三式恰为

$$
\begin{aligned}
Q&=D-qA-HT=0,\\
L_{\rm res}&=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&=C-15qT-[(q-1)s+D_0]F_{\rm orig}=0.
\end{aligned}
\tag{61.16}
$$

例如二次式来自 $D-9qT=q(A-6T)+D_0T$，一次式来自 $B+23qT=q(L+8T)+D_0[A-T(s+6)]$；常数就是原奇常数比较。反向逐系数恢复 BOTH (61.14)，所以这些条件也充分。C 与 $15qT$ 未拟合、删除或替换。

### 61.4. 普通约化、H 排除与精确严格源区间

仅在声明普通 $q\ne a$ 后取消 $\delta$。置 $\theta=T/\tau$。Q 给

$$
H\theta=b_0-mq=3a-\delta m,\qquad
3(a-q\theta)=\delta(m-u\theta).
$$

在 Q 成立时，原一次残差满足

$$
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}.
\tag{61.17}
$$

其直接来源是 $B-qL+15qT=-\delta L-15(a\tau-qT)$；Q 把除 τ 后的值变为 $-\delta[n-5u\theta]$，再减 $D_0[A-T(s+6)]/\tau$ 即得。因此只取消已知非零 $\delta,\tau$ 后，普通约化为

$$
H\theta=b_0-mq,\qquad n=u[m-(s+1)\theta],\qquad R_C=0.
\tag{61.18}
$$

联立前两式消去 m 给

$$
[u(s+1)+2H]\theta=G,\qquad
K_{\rm pos}:=u(s+1)+2H=u(s-2q+c)+6q>0.
\tag{61.19}
$$

这里 $u$ 是 (61.13) 的辅助函数。严格源先给正系数，继而 $\theta>0$、$\nu=s\tau\theta\ne0$；真正二次是导出结论，两种 τ 符号都保留。

若 H=0，Q 迫 $q=q_0<1$，但 $H(q_0)>0$，矛盾。H 非零时，Q 还给

$$
m-(2q+1)\theta=\frac{l_0+l_1q}{H}.
\tag{61.20}
$$

H<0 会使右端负，而独立原一次式使左端为 $(s-2q)\theta+n/u>0$。所以 H>0，此后才以 H 为正除数；Q 与 $\theta>0$ 给 $0<q<q_0<1$。

在辅助区间 $(0,q_0)$ 定义

$$
\theta(q)=\frac{b_0-mq}{H}>0,\quad\eta(q)=\frac n{u}>0,\quad
s(q)+1=\frac{m-\eta}{\theta},\quad
M_{\rm src}=\eta+(2q+1)\theta.
\tag{61.21}
$$

严格源恰为 $M_{\rm src}<m$，因为 $s-2q=(m-M_{\rm src})/\theta$。对 $0<q<r<q_0$，直接有限通分给

$$
\eta(q)-\eta(r)=\frac{2n(r-q)}{u(q)u(r)}>0,
$$

$$
\frac{l_0+l_1r}{H(r)}-\frac{l_0+l_1q}{H(q)}
=\frac{2(r-q)\{l_1(1+qr)+l_0(q+r-1)\}}{H(q)H(r)}>0.
\tag{61.22}
$$

花括号等于 $(l_1-l_0)+l_1qr+l_0(q+r)>0$，故 $(2q+1)\theta$ 与 $M_{\rm src}$ 严格递减。端点仅为辅助值：

$$
M_{\rm src}(0)=n/c+b_0/2,\qquad M_{\rm src}(q_0-)=n/u(q_0)<m,
$$

因为 $mu(q_0)=n+G$。左端不超过 m 等价于 $n\le cl_0/2=2am-3$。连续性与严格递减于是给精确严格源区间

$$
I=\begin{cases}
(0,q_0),&0<n\le2am-3,\\
(q_{\min},q_0),&n>2am-3,
\end{cases}
\tag{61.23}
$$

其中 $q_{\min}$ 是唯一 $M_{\rm src}=m$ 点，也即区间内 $u(l_0+l_1q)-nH=0$ 的唯一根；这是因为 $m-M_{\rm src}=[u(l_0+l_1q)-nH]/(uH)$。临界等号的下端仍是排除的 q=0。边界与极限不补作世界，普通分支再除去 q=a。

### 61.5. 普通原世界的完整 iff 与有限次序

在 $q\in I\setminus\{a\}$ 置

$$
h=s+5-u=s-2q+4-2a,\quad\phi=3\theta-h\eta,\quad J_0=(q-1)s+D_0,
$$

$$
\mathcal C_{\rm orig}=\bar C-15q\theta-J_0\phi.
\tag{61.24}
$$

全部实际普通六行世界恰为这些 q 中 $\mathcal C_{\rm orig}=0$ 的点，唯一重建为

$$
P=P(q,s),\qquad g(t)=s\tau\{\theta(t^2-5t+3)+\eta(t-h)\},
$$

$$
(\lambda,\mu,\nu)=s\tau(\phi,\eta-5\theta,\theta),\qquad
 d=a_0-s\tau\phi.
\tag{61.25}
$$

必要性：前节强制 $\theta,\eta,s$，而偶系数给

$$
m-(s+6)\theta=\eta-5\theta,
$$

$$
F_{\rm orig}/\tau=n-(s+5)m+\theta(s+2)(s+4)
=3\theta-(s+5-u)\eta=\phi.
\tag{61.26}
$$

原 $R_C/\tau$ 正是 $\mathcal C_{\rm orig}$。充分性：$m=(s+1)\theta+\eta$、$n=u\eta$ 与 Q 恢复完整 $L_{\rm res}$；(61.26) 恢复全部偶系数；$\mathcal C_{\rm orig}=0$ 恢复原 C 和 $15qT$。故 (61.16) 与所有系数比较恢复 BOTH 整恒等式，继而全部六原行。$s>0,\tau\ne0,\theta>0$ 保证 whole gain 非零。相同 q 固定整个世界，不同 q 给不同源。仅落在 I 的源曲线点不是世界。

还需有限弦：

$$
\theta(q)-\theta(r)=\frac{2m(r-q)D_{\rm ch}}{H(q)H(r)}>0,
$$

$$
D_{\rm ch}=1+qr+q_0(1-q-r)
=1+q_0-q_0^2+(q_0-q)(q_0-r)>0.
\tag{61.27}
$$

这是 $m(q_0-q)/H(q)$ 的交叉分子；分母和末式均正。它与 η 弦都跨辅助删点 a 成立。在 I 上 $Z_{\rm src}=m-M_{\rm src}>0$ 严格增加，$\xi=s-2q=Z_{\rm src}/\theta$ 有精确商差

$$
\xi(r)-\xi(q)=\frac{Z_{\rm src}(r)-Z_{\rm src}(q)}{\theta(r)}
+Z_{\rm src}(q)\left[\frac1{\theta(r)}-\frac1{\theta(q)}\right]>0.
\tag{61.28}
$$

故 $s(r)-s(q)>2(r-q)>0$。不需要导数或对任何辅助点作可达性断言。

### 61.6. 第七原行、全部例外与 ENTIRE 子片

定义取得量

$$
\kappa=\frac{z_{\rm obs}-a_0-E(4)}{2\tau}.
$$

时钟四和所选 J 的时钟六有相同迹 $1+4/s$；固定 gain 给 $g(6)-g(4)=2s\tau(5\theta+\eta)$。所以实际第七行在普通图谱中双向等价于

$$
\kappa=(s+4)(5\theta+\eta)=(s+4)[m-(s-4)\theta].
\tag{61.29}
$$

反向结合已恢复的时钟四行即恢复原第七行。此式不除 s-4，在 s=4 恰为 $\kappa=8m$。θ、η 下降和 s 上升不自动给 κ 次序：κ 的弦是

$$
[s(r)-s(q)](5\theta(r)+\eta(r))
-[s(q)+4]\{5[\theta(q)-\theta(r)]+\eta(q)-\eta(r)\},
$$

为两个正量之差，未证明全局 acquired-J 单射。

在独立原分支 q=a，$D_0=0,H=3a$，Q 迫 $T=\tau$；原常数迫 $\lambda=\Lambda$，因为 $a-1\ne0$。于是 $eg=K$，严格 $s>2a$ 迫 $K(-s)=0$，只可 $s=p$ 或 v，根七对应非法 s=-7。全部例外恰为

$$
W_p=(P(a,p),p\tau(t+v)(t-7),d_*),\quad
W_v=(P(a,v),v\tau(t+p)(t-7),d_*),\quad d_*=a_0+7\tau V.
\tag{61.30}
$$

反向两个源均严格、gain 非零；$eg=K,o=ae$ 与 (61.10) 给

$$
-\Lambda+og=-\Lambda+aK=R+a\tau V_o.
$$

故 BOTH 恒等式及全部六原行成立。这也证明每个所列父实际达到；不同 p、v 给不同整个世界。

实际第七响应与归一化值分别为

$$
z_p=d_*-\tau(p+4)(6+v),\quad z_v=d_*-\tau(v+4)(6+p),\quad
z_p-z_v=2\tau(v-p)\ne0,
$$

$$
\kappa_p=(p+4)(v+3),\qquad\kappa_v=(v+4)(p+3).
\tag{61.31}
$$

定义 $\mathcal E_z$ 为且仅为实际响应匹配 $z_{\rm obs}$ 的这些例外，至多一个。定义 $\mathcal O_\kappa$ 为 (61.25) 中全部满足

$$
q\in I\setminus\{a\},\quad\mathcal C_{\rm orig}=0,\quad
(s+4)(5\theta+\eta)=\kappa
\tag{61.32}
$$

的世界。则 ENTIRE 原二次域实际子片满足精确等号

$$
\mathcal K_z=\mathcal O_\kappa\cup\mathcal E_z,\qquad |\mathcal E_z|\le1.
\tag{61.33}
$$

证明：q=a 和 q 非 a 穷尽源双射；两分支各有原六行必要性与充分性；普通的 (61.29) 和例外的实际匹配分别恢复且只恢复同一个第七行。因此等号针对 entire $P,g,d$，不是源投影或所选根支。

### 61.7. 实际末函数、原常数方向与三带

普通世界置

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(u+2-s)\eta=17\theta+(7-h)\eta,
\qquad A_7=s+4-4q.
$$

奇整恒等式在七用 $V_o(7)=48$，参考迹 $o(7)=j+3r$。实际 JJ 迹少 $2q/s$，JM 迹多 $A_7/s$，所以 SAME gain 与 d 的实际末响应为

$$
f_{JJ}=a_0+R(7)+\tau x,\qquad f_{JM}=a_0+R(7)+\tau y,
$$

$$
x=48q\theta-2q\omega,\qquad y=48q\theta+A_7\omega,
\quad y-x=(s+4-2q)\omega.
\tag{61.34}
$$

例外在七 gain 为零，故 $x=y=48a$。

保留原常数的符号至关重要。偶重建与 $Q=L_{\rm res}=0$ 下，整个奇 discrepancy 恰为常数 $-R_C$。在七减偶式，得到

$$
B_7\omega=\frac{R(7)-E(7)}\tau+(48q-105)\theta-R_C/\tau,
\quad B_7=(q-1)(s+7)+D_0.
$$

$K(7)=0$ 与 (61.10) 给 $E(7)=-\Lambda-105\tau$、$R(7)=-\Lambda-48a\tau$。因此

$$
R_C/\tau=C_7-(105-48q)\theta-B_7\omega,\qquad C_7=105-48a.
\tag{61.35}
$$

这是含原 C、$15qT$ 的原残差恒等式。令

$$
D_7=-B_7=(1-q)\xi+5-4q>0,\quad
\mathscr R_7=m+2-2(q+a)>m-2>9,
$$

$$
\mathscr M_7=C_7\mathscr R_7+48(b_0-mq)>0.
$$

Q 给

$$
\theta-1=-\frac{(q-a)\mathscr R_7}{H},\quad
F_7=(105-48q)\theta-C_7=-\frac{(q-a)\mathscr M_7}{H}.
$$

原 $R_C=0$ 因而给

$$
D_7\omega=F_7,\qquad
\omega=-\frac{(q-a)\mathscr M_7}{HD_7}.
\tag{61.36}
$$

所有分母已经正；故下侧 $q<a$ 有 ω 正，上侧 $q>a$ 有 ω 负，无普通末零。还因 $h=\xi+4-2a>2$，归一化整二次在二的值为 $-3\theta+(2-h)\eta<0$，首项正，故有两不同实根分居二的两侧；上根在下侧低于七、上侧高于七。这些是导出事实，不是原域承诺，也未移用负 n 符号。

Q 还给

$$
m-u\theta=\frac{3[(m-2a)q-2]}H,\qquad
q\theta-a=-\frac{q-a}{3}(m-u\theta).
$$

于是

$$
y-48a=-(q-a)W_7,\qquad
W_7=16(m-u\theta)+\frac{A_7\mathscr M_7}{HD_7}.
\tag{61.37}
$$

第一项不能假设非负。实际有 $A_7=\xi+4-2q>0$，

$$
\frac54 A_7-D_7=(q+1/4)\xi+\frac32q>0.
$$

且 $C_7>57$、$\mathscr R_7>9$ 给 $\mathscr M_7>57\cdot9>120$；$(m-2a)q-2>-2$。所以按负系数的正确方向，

$$
HD_7W_7=48[(m-2a)q-2]D_7+A_7\mathscr M_7
>-96D_7+A_7\mathscr M_7>A_7(\mathscr M_7-120)>0.
$$

故 ALL 实际下侧普通世界 $y>48a$、ALL 上侧 $y<48a$、例外 $y=48a$。三带不交；τ 负只反转实际序，不损分离。带不证明普通存在。

### 61.8. 复用的上侧有限比较

对辅助 $0<q<1,\xi>0$，令

$$
\rho(q,\xi)=\frac{\xi+4-2q}{(1-q)\xi+5-4q}.
$$

分母正。固定 q 的有限 ξ 弦和固定 ξ 的有限 q 弦分别为

$$
\rho(q,\xi_2)-\rho(q,\xi_1)
=\frac{(\xi_2-\xi_1)[H(q)-1]}{D_7(q,\xi_1)D_7(q,\xi_2)}>0,
$$

$$
\rho(r,\xi)-\rho(q,\xi)
=\frac{(r-q)(\xi^2+6\xi+6)}{D_7(q,\xi)D_7(r,\xi)}>0.
\tag{61.38}
$$

这里 $H-1=1+2q(1-q)>0$。ξ 随 q 严增，故 $\rho=A_7/D_7$ 严增，交叉辅助点无须实际兼容。

对任何同父实际 $a<q<r<q_0$，$A_7-D_7=q(\xi+2)-1>2a-1>0$，故 ρ>1，且 $F_7<0$。固定 $\rho_1=\rho(q)$，定义

$$
\mathcal H(x)=[105\rho_1+48x(1-\rho_1)]\theta(x)-C_7\rho_1.
$$

x<1 使方括号大于 $57\rho_1+48>0$，并严格递减；θ 正且严格递减。用 A(x) 暂记方括号，有限乘积差

$$
A(q)\theta(q)-A(r)\theta(r)
=[A(q)-A(r)]\theta(q)+A(r)[\theta(q)-\theta(r)]>0
$$

给 $\mathcal H(r)<\mathcal H(q)$。再由原常数式

$$
y(r)=\mathcal H(r)+[\rho(r)-\rho_1]F_7(r)
<\mathcal H(q)=y(q).
\tag{61.39}
$$

故上侧末 M 严格单射，甚至无需 SAME κ。这里每个端点仍须是原世界，非把整个辅助曲线当作世界。

### 61.9. 新原常数恒等式与下侧符号

**原常数屏障定理。** 在 (61.7)、(61.8) 的固定父，每个实际普通六行世界若 $q<a$，则 $s>4$。结论在第七响应取得前成立，对任意实际 κ 一致。

固定这样的世界，令

$$
k_a=a-q>0,\quad z_e=\eta/\theta>0,\quad
P_h=h^2-5h+5,\quad R_h=h(h-2)(h-4).
$$

$k_a$ 不表示 κ 或弦斜率。先有 $s>2q>0$、$h>4-2a>2$、$k_a<a<4/5$。

从 BOTH (61.14) 减 a 倍偶式，用原 (61.10) 及 $o-ae=\delta(t+s-u)/s$，得

$$
(a-1)(\lambda-\Lambda)+\delta(t+s-u)g/s
=a(\tau-T)U+(qT-a\tau)V_o.
\tag{61.40}
$$

Q 给 $3(a\tau-qT)=\delta(A-uT)$ 和 $a(\tau-T)=\delta[A+(3-u)T]/3$。仅在已知 $\delta\ne0,\tau\ne0,s>0$ 后除，使用 $(U-V_o)/3=t^2-5t+5$，得到精确整恒等式

$$
\boxed{\frac{(a-1)(\lambda-\Lambda)}{\delta\tau}
+\frac{(t+s-u)g}{s\tau}
=\theta U+(m-u\theta)(t^2-5t+5).}
\tag{61.41}
$$

为逐系数核对，置 $B_*=m-u\theta=(h-4)\theta+\eta$。左侧除标量外为

$$
(t+h-5)[\theta t^2+(\eta-5\theta)t+\phi].
$$

它的三次、二次、一次系数依次是

$$
\theta,\quad(h-10)\theta+\eta=B_*-6\theta,\quad
(28-5h)\theta-5\eta=8\theta-5B_*.
$$

这正是右侧三个非恒定系数。常数比较为

$$
\frac{(a-1)(\lambda-\Lambda)}{\delta\tau}+(h-5)\phi=5B_*,
$$

所以，保留原 Λ 及原奇常数，

$$
\epsilon\frac{\lambda-\Lambda}{\tau}
=k_a[(2h-5)\theta+P_h\eta].
\tag{61.42}
$$

SAME 固定 $\lambda=s\tau(3\theta-h\eta)$、$\Lambda=-7\tau V$，而 $V=n+2m+15$、$n=u\eta$、$m=(s+1)\theta+\eta$，给

$$
\frac{\lambda-\Lambda}{\tau}
=(17s+14)\theta+(s+7)(7-h)\eta+105.
$$

θ 系数来自 $3s+14(s+1)$，η 系数来自 $-sh+7u+14=(s+7)(7-h)$；105 是原常数项。因此原平衡恰为

$$
A_c\theta+B_c\eta+105\epsilon=0,
$$

$$
A_c=\epsilon(17s+14)-k_a(2h-5),\qquad
B_c=\epsilon(s+7)(7-h)-k_aP_h.
\tag{61.43}
$$

先证明系数符号。$h=s+4\epsilon+2k_a$ 给

$$
A_c=s(17\epsilon-2k_a)+14\epsilon+k_a(5-8\epsilon-4k_a).
$$

其中 $17\epsilon-2k_a>9/5>0$，且 $5-8\epsilon-4k_a>5-8\epsilon-4a=4a-3>0$。故 $A_c>0$；现在才由 $\theta,\eta,\epsilon>0$ 和原平衡推出 $B_c<0$。

进一步 h>4。若 $2<h\le4$，$P_h-1=(h-1)(h-4)\le0$，故即使 $P_h$ 负也有 $P_h\le1$。同时 $7-h\ge3,s+7>7$，于是 $B_c>21\epsilon-k_a>17/5>0$，矛盾。这里未除 $P_h$ 或 $B_c$。

### 61.10. 完整屏障证明的两段正性

反设这个实际端点 $s\le4$，包括等号。q 正与已证 h>4 给

$$
4<h=s-2q+4-2a<8-2a<13/2<7.
\tag{61.44}
$$

原 Q 在下侧写成 $H\theta=3a+k_am$，而 $H=3q+k_au$。用 $m=(s+1)\theta+\eta$，得到

$$
3a/\theta=3q+k_a(4-h-z_e).
$$

先有正 $k_a,\theta$，才定义

$$
z_{\max}=3q/k_a+4-h=3a/k_a+1-h,\qquad
z_{\max}-z_e=\frac{3a}{k_a\theta}>0.
\tag{61.45}
$$

故 $z_{\max}>z_e>0$ 在使用前成立。它是辅助上界，绝非另一个世界。

有限恒等式 $(2h-5)+(1-h)P_h=-R_h$ 给

$$
A_c+B_cz_{\max}=T_h+\epsilon(s+7)(7-h)z_{\max},
$$

$$
T_h=\epsilon(17s+14)-3aP_h+k_aR_h.
\tag{61.46}
$$

第二项严格正，下面对全部 (61.44) 证明 $T_h>0$。

**第一段 $4<h\le5$。** $R_h>0$ 且 $k_a<a$，故 $s=h-4\epsilon-2k_a>h-4\epsilon-2a$，于是

$$
T_h>F(h):=\epsilon(17h-54+34a)-3a(h^2-5h+5).
$$

用 $2a^2+a=2$，精确端点为

$$
F(4)=34a-20>0,\qquad F(5)=5a-3>0.
$$

二次系数为 $-3a$，完整有限凹弦为

$$
F(h)=(5-h)F(4)+(h-4)F(5)+3a(h-4)(5-h).
\tag{61.47}
$$

在 $[4,5]$ 权重非负、和一、端值正、余项非负，故 F 正，T 正。弦点仅为辅助实数，不须假设实际可达。

**第二段 $5\le h<13/2$。** 三个正因子给 $R_h\ge15$，$\epsilon<1/4$ 先给

$$
R_h-34\epsilon>15-17/2>0.
$$

由 $s\le4$，

$$
k_a\ge(h-8+4a)/2>0,
$$

末项正来自 $h\ge5$ 与 $4a-3>0$。重写再按已证正系数代下界：

$$
\begin{aligned}
T_h&=\epsilon(17h+14-68\epsilon)-3aP_h+k_a(R_h-34\epsilon)\\
&\ge G(h):=82\epsilon-3aP_h+(h-8+4a)R_h/2.
\end{aligned}
\tag{61.48}
$$

ε 项的常数是 82，因为 $17h+14-68\epsilon-17(h-8+4a)=82$。

置 $t_h=h-5$，$0\le t_h<3/2$。手工收集所需全部系数：

$$
P_h=5+5t_h+t_h^2,\qquad R_h=15+23t_h+9t_h^2+t_h^3,
$$

$$
\begin{aligned}
2G(5+t_h)
&=164\epsilon-6a(5+5t_h+t_h^2)
 +(t_h+4a-3)(15+23t_h+9t_h^2+t_h^3)\\
&=(119-134a)+(62a-54)t_h+(30a-4)t_h^2
 +(4a+6)t_h^3+t_h^4.
\end{aligned}
\tag{61.49}
$$

由 $3/4<a<4/5$，常数 $>59/5$，一次系数 $>-15/2$，二次、三次系数均正，四次系数为一。所以

$$
2G(5+t_h)>59/5-(15/2)t_h>59/5-45/4=11/20>0.
\tag{61.50}
$$

$t_h=0$ 也因常数严格界而严格；h=5 在两段均保留，s=4 在非严格 $k_a$ 下界中保留。故第二段也有 $T_h\ge G(h)>0$。

两段穷尽反设范围。因此 $A_c+B_cz_{\max}>0$。$B_c<0$ 和 $z_e<z_{\max}$ 给

$$
A_c+B_cz_e>A_c+B_cz_{\max}>0.
$$

但只除正 θ 的原平衡给 $A_c+B_cz_e=-105\epsilon/\theta<0$，矛盾。由此每个实际下侧普通六行端点 s>4。证明未改变原 C、未选 τ 符号、未除样本或 s-4、未将必要条件当存在，且发生于第七取得之前。∎

### 61.11. 任意同子片下侧对的完整有限比较

取任意两个不同实际普通下侧成员 $q_1=q<q_2=r<a$，固定 SAME 父与 SAME 实际 κ，两端均保留 $Q=L_{\rm res}=R_C=0$、严格源与第七原行。令

$$
\ell=r-q>0,\quad\vartheta=\theta_2>0,\quad s=s_1>4,
$$

$$
\alpha=\frac{\theta_1-\theta_2}{\ell\vartheta},\quad
\beta_{\rm ch}=\frac{\eta_1-\eta_2}{\ell\vartheta},\quad
z=\frac{\eta_2}{\vartheta},\quad
K_s=\frac{s_2-s_1}{\ell},\quad w=\frac{\omega_2}{\vartheta},\quad A_7=s+4-4q.
\tag{61.51}
$$

s>4 由新屏障覆盖每个实际对；$\beta_{\rm ch}$ 不是父的根参数七。

θ 弦给 $\alpha=2D_{\rm ch}/[H(q)(q_0-r)]$。其正分子减正分母为

$$
2\{1+r(1-q_0)-(q_0-r)(2q-q^2)\}>0,
$$

因为 $0<q_0-r<1$、$0<2q-q^2<1$，故 α>1。η 弦给

$$
\beta_{\rm ch}=2z/u_1>0,\quad u_1=2q+c>c>5/2,
$$

源弦给 $K_s>2$。比较两端 SAME m 与 SAME κ，分别得到

$$
K_s=(s+1)\alpha+\beta_{\rm ch},\qquad
K_s(5+z)=(s+4)(5\alpha+\beta_{\rm ch}),
$$

$$
\alpha[(s+1)z-15]+\beta_{\rm ch}(z+1-s)=0.
\tag{61.52}
$$

s>4 使 $15/(s+1)<s-1$。z 不超过前者会使第一项非正、第二项严格负；z 不小于后者会使第一项严格正、第二项非负。故

$$
15/(s+1)<z<s-1<s_2-1.
\tag{61.53}
$$

分母在使用前均正。

将 $n=u\eta,m=(s+1)\theta+\eta$ 代 ω，给

$$
\omega=n+(2-s)m+(s^2-s+15)\theta.
$$

加上 $\kappa=(s+4)m-(s^2-16)\theta$ 再代一次 m，得 SAME 子片恒等式

$$
\omega=n+5m-\kappa+32\theta+\eta,
\quad\omega_1=\omega_2+\ell\vartheta(32\alpha+\beta_{\rm ch}).
\tag{61.54}
$$

它没有丢掉任一端原常数条件。第二个实际下侧端点原 C 给 w>0，而整 gain 给 $w=17+(u_2+2-s_2)z$。若后项系数非正，则 $w\le17$。若正，置 $X=s_2-1>0$，用 z<X 与非负平方，

$$
(u_2+2-s_2)z<X(u_2+1-X)\le (u_2+1)^2/4<169/25<7,
$$

因为 $u_2<4a+1<21/5$。故两种符号及零系数都给

$$
0<w<24.
\tag{61.55}
$$

在实际 x、y 中代 $\theta_1=\vartheta(1+\ell\alpha)$、$A_{7,2}=A_7+\ell(K_s-4)$ 与 (61.54)，完整有限弦恰为

$$
D_y:=\frac{y_2-y_1}{\ell\vartheta}
=48-48q\alpha+(K_s-4)w-A_7(32\alpha+\beta_{\rm ch}),
$$

$$
D_x:=\frac{x_2-x_1}{\ell\vartheta}
=48-2w+q(16\alpha+2\beta_{\rm ch})>0.
\tag{61.56}
$$

两式均用共同的实际父偏移，非拟合端点差。

若 $K_s\le4$，用 w>0、$A_7>4-2q>0$、α>1：

$$
D_y\le48-\alpha(48q+32A_7)-A_7\beta_{\rm ch}
<48-(128-16q)<0.
\tag{61.57}
$$

若 $K_s>4$，其乘数正，使用 w<24 与固定 m 式给

$$
D_y<-48-\alpha(8s+104-80q)+\beta_{\rm ch}(20-s+4q).
\tag{61.58}
$$

α 的系数 $>72$，因为 s>4、q<a<4/5。若 $20-s+4q\le0$ 已严格负；否则 $\beta_{\rm ch}<2(s-1)/u_1$，非负平方给

$$
\beta_{\rm ch}(20-s+4q)
<\frac{2(s-1)(20+4q-s)}{u_1}
\le\frac{(19+4q)^2}{2u_1}<529/5.
$$

所以 $D_y<-48-72+529/5=-71/5<0$。两种 $K_s$ 情况穷尽，包括等号四；$\ell\vartheta>0$ 给 $y_2<y_1$、$x_2>x_1$。SAME 非零 τ 保留两动作分离，负 τ 只反转实际序。新屏障使此比较覆盖 EVERY 实际下侧同子片对，原先 s1<4 的必要碰撞区域在原 C 轨迹上为空；必要不等式从未充当存在证据。

**普通末 J 推论。** 对任意有序普通同子片对 $q<r<q_0$，包括跨 a，(61.56) 的 x 弦及正 α、$\beta_{\rm ch}$ 仍成立。若 r<a，用上述下侧证明；若 r>a，原 C 给 $\omega_2<0$，故 w<0，(61.56) 再给 $D_x>0$，不论首端在哪侧。普通 r=a 不在此分支。这穷尽普通有序对，因此末 J 在普通部分单射。没有比较普通与实际匹配例外，也没有证明 acquired κ 单射或 ENTIRE 末 J 单射。

### 61.12. ENTIRE 完成、取得数据派发与全部原行逆

**完整正 n 局部选择器定理。** 对每个 (61.7)、(61.8) 的实际父及每个任意实际取得的第七 J 响应，末 M 在 ENTIRE $\mathcal K_z$ 单射。

证明。(61.33) 穷尽为实际下侧普通、实际上侧普通、至多一个实际匹配例外。屏障与有限对证明分离所有下侧同子片对；(61.39) 分离所有上侧对；三带分离每个跨部分对；同子片至多一个例外。因此每个不同整个世界对都由 y 分离，τ 非零使实际 M 响应也单射。论证不要求普通非空、任一侧多点、子片有限、残式简单根或一般次数，涵盖 ordinary-only、exception-only、单点、空下侧或空上侧，以及原式允许的重根、消去和恒零次级残式。整个实际子片非空由真实性提供。∎

这里只用 n>0、Γ<0，故包括原 $\Gamma<-(8a+9)$ 的整个剩余区。第 60 节旧带也精确保留：$G\le8a+9$ 等价于 $n\ge d_a(m-c)$，因为 $d_ac=2a+9$；辅助 $\theta(a)=1$、$M_{\rm src}(a)=c+n/d_a\ge m$ 与严格递减排除全部普通 $q\le a$。等号处普通辅助 a 是严格源边界，不能删除单独原分支的例外。因此第 60 节旧带是本定理的特例；正 n、Γ 负指定父上的任意实际响应局部选择器在本文范围内完整成立。

派发只使用已取得记录：由六行形成插值并确认明确父假设；只在原时钟六取得 J，形成 κ；按 (61.32) 构造 ALL 普通候选，并按 (61.31) 附加且仅附加实际匹配例外。只合并完整相同三元组。由 (61.33)，这是非空 ENTIRE 候选并集。

若该并集单点，返回其完整世界，在七次 TOTAL 停止。否则只选择 M，在原时钟七取得 $f_{\rm obs}$，以已知非零 τ 归一化

$$
y_{\rm obs}=\frac{f_{\rm obs}-a_0-R(7)}{\tau}.
\tag{61.59}
$$

若 $y_{\rm obs}=48a$，唯一实际匹配例外是逆，其整个世界由 (61.30) 恢复。否则逆是且仅是满足

$$
q\in I\setminus\{a\},\quad \mathcal C_{\rm orig}(q)=0,\quad
(s+4)(5\theta+\eta)=\kappa,\quad y(q)=y_{\rm obs}
\tag{61.60}
$$

的唯一完整普通候选。$y_{\rm obs}>48a$ 给下侧，$y_{\rm obs}<48a$ 给上侧；这是原 C 的结论，不是对未知源的额外承诺。用 (61.12)、(61.25) 恢复 ALL 源元、ALL gain 系数与固定 d。

存在性由实际世界提供；唯一性由 ENTIRE 单射提供。必要性是原式推导。充分性从全部系数 iff 恢复 BOTH 整恒等式、六原行；未除 s-4 的 κ 式恢复 SAME 原第七 J 行；y 等式恢复且只恢复所选原第八 M 行。例外的整恒等式逆与实际匹配同样恢复所有行。因此一个固定严格源、一个 whole 非零 gain、一个各自固定 d 同时满足全部所选原行，没有逐行拟合，也未用未选末 J 响应。

这是精确集合论选择器与必要充分的 whole-world 逆；不认证有效求根、可计算单点判断、有限精度或资源保证，不证明普通或非单点子片存在，也不证明第八读必要。

### 61.13. SAME 父坏 M 的 FULL 对与两末 FULL 切片

在 SAME 父，另一时钟六动作 M 的实际迹为 $e(6)=1+3b$，原偶恒等式给

$$
h_M=a_0+E(6)+48T,\qquad
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
\tag{61.61}
$$

其 FULL 子片固定恰好 $T=\tau$。当前正 n、Γ 负范围内 (61.36) 前的 $\theta-1=-(q-a)\mathscr R_7/H$ 及 $\mathscr R_7,H>0$ 直接排除一切普通 θ=1；两个例外均 θ=1 且匹配。因此 FULL 子片精确为 $\{W_p,W_v\}$，非从更大切片抽选的一对。

复用的更一般 $\beta=7$ 原常数证明也保留：若普通 T=τ 合法，Q 给 $q=(Z+1)/2-a$、$\delta>1/2$；置 $h_o=s-Z+7>8-2a>6$。完整一次与偶系数给

$$
V=(7-h_o)Z+23-2h_o,\quad
 g=s\tau(t^2-h_ot+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-6)(h_o-3)+5>0.
$$

原常数保留 $15\delta$ 后等价为

$$
-7V=s\chi_o-\frac\delta\epsilon(h_o-4)(h_o-6)(h_o-8),
$$

因为 $J_0=-\epsilon s+\delta(h_o-9)$、$\bar C-15q=7\epsilon V-15\delta$，且 $(h_o-9)\chi_o+15=(h_o-4)(h_o-6)(h_o-8)$。左端负迫 h_o>8。由 $Z>4a,V>4a^2$ 和负系数 $7-h_o$，原一次式给 $h_o<(19+30a)/(4a+2)<17/2$。在此区间，正三次积小于 $45/8$，$\chi_o>15$、ε>1/5，所以该积除 $\epsilon\chi_o$ 小于 $15/8$。严格源又给 $\delta<q<s/2$；同一个原常数遂迫 $-7V>s\chi_o/16>0$，矛盾。此证明排除 ALL 普通 T=τ 世界，不预删末零竞争者。

故 SAME 父完整等号与 BOTH 末 FULL 切片为

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\},
$$

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}
=\{W_p,W_v\}.
\tag{61.62}
$$

两 gain 在七均为零、两漂移均为 d_*，且两源不同。于是父、坏 M 子片、BOTH 末 FULL 切片、全部已服务共同祖先的非单点停止守卫由 SAME 对保留。这是坏 M 臂，非本定理实际取得 J 子片；两例外在 J 上响应不同。局部正完成不服务更早未取得的另一臂，也不迫任意根策略进入 $JMJMJ$。

### 61.14. FULL 包含、条件六端支持与惰性共同合同

对同历史 $K\subseteq K'$，每个实际动作／响应 FULL 切片也包含。定义 $\mathsf L_0(K)$ 为 K 非单点；$\mathsf L_{h+1}(K)$ 为父非单点且 EACH 动作各有一个实际响应，其 FULL 子片满足 $\mathsf L_h$。h=0 的不同完整目标在包含下保留；归纳步逐动作保留原实际响应，对其切片包含用归纳假设，并保留父非单点守卫。故所有有限深度 $\mathsf L_h$ 向上保持，不要求有限基数。

IF 其他范围某一个 SAME 实际 J 子片同时实际实现 x 碰撞对及 y 碰撞对，可取两对至多四个完整端点，再加 SAME 父坏 M 对至多两个，给条件至多六端点支持。FULL 包含保留 BOTH 动作、实际响应、已服务祖先和全部停止守卫。它只在共同实现前提下成立，不构造缺失对、不证明尖锐或最小、不替代无条件 ENTIRE 子片基数定理，也不产生原根失败树。当前正 n 范围因 ENTIRE y 单射已排除这种双对实现。

完整原根联合义务保持 **INERT、UNEXECUTED、UNFULFILLED**。保留 ALL 256 槽

$$
\sigma=(w,e),\quad w\in\{J,M\}^7,\quad e\in\{0,1\},
$$

ALL 254 非空实际前缀 v（原长度 i=1 至七）、各自即时左乘积 $A_v$、ALL 后代。置

$$
t_v(P)=\operatorname{tr}(A_vP),\quad
\ell_v(P)=(t_v(P)-1,\ it_v(P),\ i^2t_v(P),\ i^3t_v(P)).
$$

对 EVERY 前缀、EVERY 指定非代表后代 σ，和 SAME-prefix 代表 ρ 保留整行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0
\tag{61.63}
$$

于 ONE SAME ENTIRE $1538\times1024$ 关系，层规格 $254,252,248,240,224,192,128$。ONE 共同向量堆叠 ALL 256 whole 四系数块。每个 whole 块 $x_\sigma\ne0$，每个适用 SAME-source 终叶 whole 四分量差 $x_{(w,0)}-x_{(w,1)}\ne0$；ALL 严格源、ALL 祖先关系、BOTH 动作与 ALL 停止守卫须对 SAME 向量及 SAME 世界同时成立。

每槽从开始固定

$$
g_\sigma(t)=\sum_{h=0}^3x_{\sigma h}t^h,\qquad d_\sigma=a_0-x_{\sigma0}
$$

跨 ALL 原行使用；只合并整个 $P,g,d$ 相同世界，二次限制 $x_{\sigma3}=0$ 须同时施于 ALL 块。以上尺寸仅为继承的惰性规格，没有访问原关系生成族或生成实例，没有枚举、矩阵、秩、核、区间或证书计算。局部 q 图谱、终端对、条件六端支持、投影、较小关系、分臂／分路径解、遗漏后代、逐行 gain、独立守卫向量都不替代这 ONE 共同实现。

### 61.15. 复用范围与仍 OPEN 的原问题

以下既有结果仅保留在原明确假设内，不由本节推导扩张，也不计为新增数学：n 非零、κ=8m 的正／负 n ENTIRE 末 J 选择器；Γ>0 的取得子片完成；Γ=0 恰为唯一非恒定仿射普通世界与 $W_p,W_v$ 的父及其末 M 逆；N=0、$N=L+5A=\tau n$ 的整个例外对父与七次 TOTAL J 逆；B0 仅在既给完成接口。它们不证明未知并集可恢复。

继承的 n 非零 ENTIRE J 子片至多六界仍只在原过滤和独立奇异支的精确范围内成立，本文未消费该界；它不证明某末动作单射、六尖锐、最小或实际六点达到，也不同于条件六端支持。实际负 n 的 H=0 家族、同六行额外普通成员及改变父参数的正 n、Γ<0 延续保留各自六行存在含义，不是 SAME 父 SAME κ 碰撞。负 n 的端点屏障和弦序不被移用为正 n 定理。

任意实际 κ 的负 n 普通 acquired-J 单射和 ENTIRE 一末动作选择器仍为 OPEN；其他父类及 B0 超出既给接口的 duty 仍为 OPEN。本节没有证明 acquired 第七 J 全局单射、普通与例外的末 J 分离或当前一般层 ENTIRE 末 J 选择器。

原 FULL 严格源、whole 非零 degree-at-most-two、任意各自固定漂移的确定性自适应八次 TOTAL 恢复与原根 $\mathsf L_7$ 选择仍为 OPEN。本节不证明 root forcing、更早未服务臂、无条件同父 $\mathsf L_3$、完整根失败树、八读必要或九读上界。

原 FULL degree-at-most-three 的八次 TOTAL 恢复与 $n_{\rm det}(3,0)\ge9$ 仍为 OPEN。三次 gain 乘线性迹可四次，四偶节点相等仍可留下非零倍 $t(t-2)(t-4)(t-6)$。二次逆不检测未知三次次数、根、源、方向或平面承诺；分别可逆的已知类不自动给未知并集逆。

### 61.16. 退化、除法与证据边界

原合法 s=4、s=4q、两种 τ 符号、任意固定 d、零系数与读数、gain 采样根或非采样根、重根、残式重根、次数消去及恒零次级残式始终受完整原式约束。whole 零 gain 本来非法；当前正 n、Γ 负普通层的 H>0、θ>0、真正二次、两不同实根和普通 $g(7)\ne0$ 都是已证明的结论，不能反灌成全域承诺。新屏障包含 s=4 的反设，只在实际下侧排除它，未全局删除 s=4、上侧或例外。

q=0、s=2q、q=q0、存在时 q=qmin、r=0 或一、b=0、csrc=0、p=2a、τ=0 和无限／极限源不补作世界；p=v 不在不同两根标志内。普通辅助 q=a 不代替例外分支。相同 q 在已证图谱就是相同 entire 世界。

插值只除固定非零整数；源双射只除 b、s 正量；父归一化只除已知 τ 非零及 a、a-1 的已知非零量。普通先声明 q-a 非零才取消；正 $K_{\rm pos}$ 先于 θ 正；H=0、H<0 在用 H 正除法前排除。u、θ、D7、ε 等分母先证正；新屏障先有 ka>0，先证 zmax>ze>0，先证 Rh-34ε>0 才代 ka 下界。有限对只除正 ell、vartheta、u1、s+1，末响应只除已知 τ。没有取消 $g(6),g(7),\lambda,\mu,s-4,s-4q$、未知判别式、残式、残式导数、源差、漂移差、源行列式、$1-2r$ 或 $1-2b$。

全部数学为可出错的 UNEXECUTED 符号推导。没有执行数学公式求值、代入、数值、导数、递推、枚举、CAS、矩阵／秩／核／区间／证书计算、实验、数学测试、渲染、探测、构建或 Lean 核验；没有 D5、Blueprint、Reg、摄入或消化交付。字节、编码、哈希和 JSON 结构检查不验证数学。没有机器学习、神经网络、物理、噪声、稳定性、连续逆、有限精度、可计算性、效率、复杂度、资源、文献穷尽、原创性或优先权认证。

## 追加锚（本行以下为增补区）
