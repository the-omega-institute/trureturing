# FIB 二次标志父的正 n 任意取得响应几何与末 M 恢复带

本文独立续为第 60 节。在已经实际取得的六读 $JMJMJ$、$\beta=7$ 标志父上，固定 $n>0$ 与 $\Gamma<0$，给出全部普通世界的原行充要图谱、精确严格源区间、全部有限弦序及实际末动作的三带分离；末 M 在整个上侧普通族严格单射。在

$$
-(8a+9)\le\Gamma<0
$$

内，严格源条件排除整个普通下侧。因此对每个任意实际取得的第七 J 响应，同一个末动作 M 在 ENTIRE 原兼容子片单射。子片单点时七次 TOTAL 停止；否则原时钟七选择 M，八次 TOTAL 恢复整个 $P,g,d$。此结果不要求特殊响应 $\kappa=8m$，也不证明八次必要。

本文为 `repo-derived` 参考理论。证据上限是经过独立符号审阅、仍可出错的 **UNEXECUTED 符号数学**；不是 Lean/kernel、数值或执行证书。新内容是正 n 任意响应的源几何、上侧末 M 单射与上述全响应带。既有第 48、49、51 至 56 节及正 n 特殊响应推导只在各自明确假设内复用。插值、因子定理、有限次数根数、Vieta、有限差分与严格源代数是复用工具；综合推导不取得外部原创性或优先权认证。

## 60. 正 n 任意响应的完整原世界图谱与七／八读选择器

### 60.1. 一个固定世界、取得历史与准确读数计数

原世界从开始固定为

$$
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c_{\rm src}&1-r\end{pmatrix},\quad
0<r<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r(1-r),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
\tag{60.1}
$$

源四元严格正、迹一、行列式零；迹非零排除秩零，故秩恰一。完整目标相等指整个三元组相等。原域包含非零常数、仿射、真正二次、两种 gain 尺度符号、零系数、零读数、采样根、非采样根与重根。不同候选可有不同、但各自固定的 d。任何排除都须由原式证明。

动作即时左乘，原时钟不变：

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{60.2}
$$

对任意矩阵 A，直接相加 AP 两个对角元有

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r+A_{21}b+A_{12}c_{\rm src}.
\tag{60.3}
$$

左乘 J 交换旧两行，左乘 M 取旧第二行与旧两行之和。因此前缀的实际乘积依次为

$$
I,\quad J,\quad
\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
\begin{pmatrix}1&1\\1&0\end{pmatrix},\quad
\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad
\begin{pmatrix}2&1\\1&0\end{pmatrix}.
$$

记 $j=b+c_{\rm src}$。全部六原行明确为

$$
\begin{aligned}
d+g(0)&=y_0,\\
d+jg(1)&=y_1,\\
d+(1+b)g(2)&=y_2,\\
d+(j+r)g(3)&=y_3,\\
d+(1+2b)g(4)&=y_4,\\
d+(j+2r)g(5)&=y_5.
\end{aligned}
\tag{60.4}
$$

选择 J 后，时钟六乘积回到 $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$，实际第七行为

$$
h_J=d+(1+2b)g(6)=z.
\tag{60.5}
$$

再接 J、M 的乘积分别为 $\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$、$\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$，故两个互择末响应为

$$
f_{JJ}=d+(j+2r)g(7),\qquad
f_{JM}=d+(1+j+r+2b)g(7).
\tag{60.6}
$$

这里 $JMJMJ$ 是原时钟零至五的六次 TOTAL；所选 J 在六给七次 TOTAL；所选末 M 在七给八次 TOTAL。相同乘积仍读新时钟的同一个固定 gain。互择函数仅是固定世界的预测，实际只取得所选动作的响应。没有重置、复制、跳读、源标签、额外端口或响应后 refit。

令 $\mathcal S(\mathcal H_5)$ 为满足 (60.1)、(60.4) 的 ENTIRE 父，$\mathcal H_5=(y_0,\ldots,y_5)$。实际 J 子片为

$$
\mathcal K_z=\{W\in\mathcal S(\mathcal H_5):h_J(W)=z\}.
\tag{60.7}
$$

可达 z 使它非空；去重只按完整世界，不按某个源坐标、重复残式根或表项。

### 60.2. P0：取得父、参数对应与严格父界

令 $a_0=y_0,x_i=y_i-a_0$，用实际六行定义唯一取得插值

$$
E(t)=Lt+At^2,\qquad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
\tag{60.8}
$$

这些式分别恢复 $0,2,4$ 与 $1,3,5$ 三节点；至多二次多项式之差有三个不同根即恒零，故唯一。始终保留这个原奇插值 R 与其原常数 C。

置

$$
a=\frac{\sqrt{17}-1}{4},\quad a^2+\frac a2=1,\quad
\frac34<a<\frac45,\quad \epsilon=1-a,\quad c=2a+1,\quad d_a=4a+1.
\tag{60.9}
$$

c 是常数，绝不表示源元 $c_{\rm src}$；t 始终表示 gain 的时间变量。平方根的正平方比较给两个严格 a 界。

本文固定 ONE SAME 实际 $\beta=7$ 标志父，满足

$$
\Sigma:\ B+5D=a(L+5A),\quad
\tau=\frac{D-aA}{3a}\ne0,\quad
U=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5),
$$

$$
\Lambda=\frac{C-15a\tau}{a-1},\qquad
K=\Lambda+E+\tau U=\tau(t+p)(t+v)(t-7),\quad
p\ne v,\quad p,v>2a.
\tag{60.10}
$$

实际标志的 $\beta=7$ 耗尽结论在第 49 节的原世界范围内复用；以下直接以 (60.10) 为明确假设，并由例外世界证明其达到。置

$$
Z=p+v=m+1,\quad V=pv=n+2m+15,\quad
n=V-2Z-13>0,
$$

$$
\Gamma=n-d_am-6a<0,\qquad G=-\Gamma>0.
\tag{60.11}
$$

全篇每一对世界的比较都固定同一个 $a_0,\tau,m,n$，不是分别选可达的父。取得系数完整对应为

$$
\begin{aligned}
A&=\tau m,&L&=\tau(n-5m),\\
D&=a\tau(m+3),&B&=a\tau(n-5m-15),\\
C&=\tau\bar C,&\bar C&=7\epsilon V+15a,\qquad \Lambda=-7\tau V.
\end{aligned}
\tag{60.12}
$$

同时有整个原奇插值恒等式

$$
R=aE+a\tau(U-V_o)+(a-1)\Lambda.
\tag{60.13}
$$

其二次、一次、常数分别是 $a(A+3\tau),a(L-15\tau),(a-1)\Lambda+15a\tau$，正好为 D、B、C。

**引理 P0。** 本父满足

$$
p,v>2,\qquad m>3+2\sqrt{17}=5+8a>11.
\tag{60.14}
$$

定义

$$
q_0=a+\frac{3a}{m},\quad b_0=a(m+3)=mq_0,\quad
l_0=(2-a)m-3a,\quad l_1=(3-2a)m-6a.
\tag{60.15}
$$

则 $a<q_0<1$，$l_1>l_0>0$。

证明。$(p-2)(v-2)=n+17>17$。两因子同号；若同负，$p,v>2a>3/2$ 使两个绝对值均小于 $1/2$，乘积小于 $1/4$，矛盾。故 p、v 均大于二。不同 p、v 给 $V<Z^2/4$，而 n 正给 $V>2Z+13$；因 Z>4，得到 $Z>4+2\sqrt{17}$，即 m 的严格界。由定义二次式

$$
\frac{3a}{\epsilon}=6+6a<5+8a<m.
$$

因此 $3a/m<\epsilon$，$q_0<1$；又 $l_0=m+(\epsilon m-3a)>0$，$l_1-l_0=\epsilon m-3a>0$。后文所有这些符号均在除法前确定。∎

### 60.3. P1：完整源双射与六原行的双向恒等式

严格源域和以下开域双射：

$$
q=\frac rb>0,\quad s=\frac2b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},
$$

$$
j=q+\frac{2(1-q^2)}s.
\tag{60.16}
$$

证明。正向 $s-2q=2(1-r)/b>0$；秩一给 $c_{\rm src}=r(1-r)/b$，恰为所写逆式。反向 $q>0,s>2q$ 给四元严格正、迹一、$bc_{\rm src}=r(1-r)$，迹非零给秩恰一，并返回原 q、s。因此这是整个原源域双射，保留 $s=4$ 即 $b=1/2$，也保留 $s=4q$ 即 $r=1/2$。∎

置

$$
u(q)=2q+c>0,\quad D_0(q)=2-q-2q^2=-(q-a)u(q),\quad
H(q)=D_0(q)+3q=2+2q-2q^2,
$$

$$
e(t)=1+t/s,\quad o(t)=qe(t)+D_0(q)/s,\quad T=\nu/s.
\tag{60.17}
$$

这里 u 是源辅助函数，$\nu$ 是 gain 二次系数，二者不同。式 (60.16) 使 e、o 在偶、奇原节点恰为 (60.4) 的迹。

**引理 P1a（全部原行 iff）。** 六原行等价于源严格、整个 $g\ne0$、$d=a_0-\lambda$，以及 BOTH 整个多项式恒等式

$$
-\lambda+eg=E+TU,\qquad -\lambda+og=R+qTV_o.
\tag{60.18}
$$

证明。初读给漂移等式。偶式左减 E 在三个偶节点为零，三次系数 T；减 TU 后次数至多二且仍有三根，因此恒零。奇式相同，三次系数 qT。反向在各自三个原节点取值，恢复 (60.4) 全部行，包括零样本。此处只用整个多项式，未除任何 gain 样本。∎

完整偶升幂系数是

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T).
\tag{60.19}
$$

反解全部系数给

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F=\lambda/s=L-sA+T(s+2)(s+4),\quad \lambda=sF,\quad d=a_0-sF.
\tag{60.20}
$$

完整奇左升幂系数为

$$
\left((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
\ q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\right),
$$

右升幂系数为

$$
(C-15qT,\ B+23qT,\ D-9qT,\ qT).
\tag{60.21}
$$

三次自动一致；二次比较为 $D-9qT=q(A-6T)+D_0T$，一次为 $B+23qT=q(L+8T)+D_0[A-T(s+6)]$，常数为原 (60.21) 常数。故剩余恰为

$$
\begin{aligned}
Q&=D-qA-HT=0,\\
L_{\rm res}&=B-qL+15qT-D_0[A-T(s+6)]=0,\\
R_C&=C-15qT-[(q-1)s+D_0]F=0.
\end{aligned}
\tag{60.22}
$$

反向 (60.20)、(60.22) 逐系数恢复 BOTH 恒等式，因此恢复全部六原行。特别保留 C、$15qT$ 与原符号；普通源曲线从不替代最后一式。

**引理 P1b（普通约化与导出次数）。** 仅在声明 $q\ne a$ 后，令 $\delta=q-a$、$\theta=T/\tau$。普通兼容等价于保留 $R_C=0$、(60.20)、原严格域及

$$
H\theta=b_0-mq,\qquad n=u[m-(s+1)\theta].
\tag{60.23}
$$

而且原式强制 $\theta>0$。

证明。Q 由 (60.12) 给第一式。Q 又给

$$
3(a\tau-qT)=\delta(A-uT).
$$

在该等式成立时，完整奇一次的残差恰为

$$
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}.
\tag{60.24}
$$

具体地，$B-qL+15qT=-\delta L-15(a\tau-qT)$；代上式后除 $\tau$ 是 $-\delta[n-5u\theta]$。再减 $D_0[A-T(s+6)]/\tau$ 即得 (60.24)。只取消已经声明非零的 $\delta,\tau$；反向 (60.23) 与 Q 恢复完整奇一次，而原 $R_C$ 单独保留。

把第二式与两倍第一式相加有

$$
[u(s+1)+2H]\theta=G.
$$

其系数恒等于

$$
K_{\rm pos}=u(s-2q+c)+6q>0,
\tag{60.25}
$$

因为原严格域给 $s-2q>0$，且 $u,c,q>0$。G 正故 $\theta>0$。继而 $\nu=s\tau\theta\ne0$，所以这里排除仿射和常数是原方程的结论，未预设 gain 符号或次数。τ 仍可正可负。∎

### 60.4. P2：H 的完全排除与精确源区间

**引理 P2a。** 每个实际普通世界有

$$
H>0,\qquad 0<q<q_0<1.
\tag{60.26}
$$

证明。若 H=0，Q 强制 $q=b_0/m=q_0<1$，但 $0<q_0<1$ 使 $H(q_0)>0$，矛盾；此前未除 H。若 H 非零，Q 给精确式

$$
m-(2q+1)\theta=\frac{l_0+l_1q}{H}.
\tag{60.27}
$$

若 H<0，P0 与 q 正使右端负；而原普通式给左端

$$
(s-2q)\theta+n/u>0,
$$

矛盾。因此 H>0，Q 及 $\theta>0$ 给 $b_0-mq>0$，所以 $q<q_0$。∎

在整个形式区间 $(0,q_0)$，定义

$$
b(q)=b_0-mq>0,\quad \theta(q)=\frac{b(q)}{H(q)}>0,\quad
\eta(q)=\frac n{u(q)}>0,\quad s(q)+1=\frac{m-\eta(q)}{\theta(q)}.
\tag{60.28}
$$

b(q) 只是辅助线性式，不是原源元 b；原源 b 始终为 $2/s$。定义

$$
M_{\rm src}(q)=\eta(q)+(2q+1)\theta(q),\qquad
s-2q=\frac{m-M_{\rm src}(q)}{\theta(q)}.
\tag{60.29}
$$

因此该 Q／$L_{\rm res}$ 曲线的严格源条件恰为 $M_{\rm src}<m$。

取 $0<q<r<q_0$。不使用微分，直接有限相减有

$$
\eta(q)-\eta(r)=\frac{2n(r-q)}{u(q)u(r)}>0,
\tag{60.30}
$$

$$
\frac{l_0+l_1r}{H(r)}-\frac{l_0+l_1q}{H(q)}
=\frac{2(r-q)[l_1(1+qr)+l_0(q+r-1)]}{H(q)H(r)}>0.
\tag{60.31}
$$

括号等于 $(l_1-l_0)+l_1qr+l_0(q+r)>0$。由 (60.27)，(60.31) 同时是

$$
(2q+1)\theta(q)-(2r+1)\theta(r)>0.
$$

和 (60.30) 相加，$M_{\rm src}$ 严格递减。

连续端点值为

$$
M_{\rm src}(0)=n/c+b_0/2,\qquad
M_{\rm src}(q_0-)=n/u(q_0)<m,
\tag{60.32}
$$

因为 $mu(q_0)=n+G>n$。左端不超过 m 等价于

$$
n\le n_{\rm crit}:=\frac{cl_0}{2}=2am-3.
\tag{60.33}
$$

最后等号只用 a 的定义二次式。

**引理 P2b（精确区间）。** 若 $n\le n_{\rm crit}$，严格源区间是 $(0,q_0)$；若 $n>n_{\rm crit}$，存在唯一 $q_{\min}\in(0,q_0)$ 满足 $M_{\rm src}(q_{\min})=m$，严格源区间是 $(q_{\min},q_0)$。这个唯一边界点恰为区间内

$$
\Psi(q)=u(q)(l_0+l_1q)-nH(q)=0
\tag{60.34}
$$

的唯一根。

证明。连续、严格递减和两个端点值给两种情况及唯一性。$m-M_{\rm src}=\Psi/(uH)$ 且 $uH>0$，故边界等价。$n=n_{\rm crit}$ 的等号只在排除的 q=0，所有正 q 仍严格。∎

以下称此开区间为 I。普通世界再删 $q=a$。q=0、$q=q_0$、$q=q_{\min}$ 或任何 $s=2q$ 端点都不补作世界。这个区间只处理 Q、$L_{\rm res}$ 与源严格性，尚须原常数和实际响应过滤；它不证明普通世界存在。

### 60.5. P2：完整 q 图谱及原行逆向恢复

在 $q\in I\setminus\{a\}$，用 (60.28) 定义

$$
h=s+5-u=s-2q+4-2a,\quad
\phi=3\theta-h\eta,\quad J_0=(q-1)s+D_0,
$$

$$
\mathcal C_{\rm orig}(q)=\bar C-15q\theta-J_0\phi.
\tag{60.35}
$$

$\phi$ 是归一化 gain 常数，稍后的 $\omega$ 是末 gain；二者均不替代原奇插值 R。

**定理 P2c（完整普通世界 iff）。** 全部实际六行普通世界恰为所有上述 q 中满足 $\mathcal C_{\rm orig}=0$ 的点，逐点重建为

$$
P=P(q,s),\qquad
g(t)=s\tau\{\theta(t^2-5t+3)+\eta(t-h)\},
$$

$$
(\lambda,\mu,\nu)=s\tau(\phi,\eta-5\theta,\theta),\qquad
d=a_0-s\tau\phi.
\tag{60.36}
$$

证明必要性。P1、P2a 强制 $\theta=b/H$、$\eta=n/u=m-(s+1)\theta$，因此强制 s。完整偶一次系数给

$$
\mu/(s\tau)=m-(s+6)\theta=\eta-5\theta.
$$

偶常数重建式给

$$
F/\tau=n-(s+5)m+\theta(s+2)(s+4)=3\theta-(s+5-u)\eta=\phi.
\tag{60.37}
$$

故三个 gain 系数与 d 均为 (60.36)；原 $R_C/\tau$ 正好是 $\mathcal C_{\rm orig}$，所以必须为零。

证明充分性。给定保留 q，源严格，且 $s>0,\tau\ne0,\theta>0$ 使整个 gain 是非零二次。$\eta=m-(s+1)\theta$ 与 (60.37) 恢复 (60.20) 每个偶系数。$H\theta=b_0-mq$ 恢复 Q；(60.24) 恢复原 $L_{\rm res}$；$\mathcal C_{\rm orig}=0$ 恢复原 $R_C$，包括原 C 与 $15qT$。于是 (60.21) 全部奇系数恢复，BOTH 整个恒等式成立，(60.4) 的六个原行在 SAME 固定 $P,g,d$ 上全部成立。

相同 q 固定 $\theta,\eta,s$、所有 gain 系数和 d，因此固定整个世界；不同 q 由源双射给不同源。此证明从未除 $s-4$，也未除 $1-2r,1-2b,\lambda,\mu$ 或任何样本，故 s=4、s=4q、零合法系数、残式重根、次数取消及残式恒零均按原过滤完整保留。∎

### 60.6. P3：全部有限弦与实际第七 J 的 iff

除 (60.30)、(60.31) 外，任取 $0<q<r<q_0$，有

$$
\theta(q)-\theta(r)=\frac{2m(r-q)D_{\rm ch}}{H(q)H(r)}>0,
$$

$$
D_{\rm ch}=1+qr+q_0(1-q-r)
=1+q_0-q_0^2+(q_0-q)(q_0-r)>0.
\tag{60.38}
$$

这是对 $b/H$ 的有限通分；$q_0<1$ 给首项严格正。故 $\theta$ 严格递减。

在 I 上记 $Z_{\rm src}=m-M_{\rm src}>0$，源间隙用 $\xi=s-2q$ 表示，绝不与时间 t 混名。$Z_{\rm src}$ 递增、$\theta$ 正且递减，精确有限商差为

$$
\xi(r)-\xi(q)=\frac{Z_{\rm src}(r)-Z_{\rm src}(q)}{\theta(r)}
+Z_{\rm src}(q)\left(\frac1{\theta(r)}-\frac1{\theta(q)}\right)>0.
\tag{60.39}
$$

因此 $s=\xi+2q$ 递增。独立的 s 弦还可写为

$$
s(r)-s(q)=\frac{[m-\eta(r)][\theta(q)-\theta(r)]}{\theta(q)\theta(r)}
+\frac{\eta(q)-\eta(r)}{\theta(q)}>0,
\tag{60.40}
$$

其中 $m-\eta(r)=[s(r)+1]\theta(r)>0$。这些弦只用正分母，不需要微积分。

对实际取得 z 定义

$$
k=\frac{z-a_0-E(4)}2,\qquad \kappa=k/\tau.
\tag{60.41}
$$

原时钟四与所选 J 后时钟六的迹相同，而整个固定 gain 满足

$$
g(6)-g(4)=2\mu+20\nu=2s[A-(s-4)T].
$$

因此原第七行恰等价于

$$
k=(s+4)[A-(s-4)T],\qquad
\kappa=(s+4)[m-(s-4)\theta]=(s+4)(5\theta+\eta).
\tag{60.42}
$$

反向只用已经恢复的时钟四原行与同迹差，所以确实恢复 (60.5)，包括 s=4 与零 gain 样本。无需未选响应。

若 q<r，记 $\Delta s=s(r)-s(q)>0$、$\Delta\theta=\theta(q)-\theta(r)>0$、$\Delta\eta=\eta(q)-\eta(r)>0$，则

$$
\kappa(r)-\kappa(q)=\Delta s[5\theta(r)+\eta(r)]-[s(q)+4](5\Delta\theta+\Delta\eta).
\tag{60.43}
$$

两项均为正量而相减。相反的因子顺序不推出 $\kappa$ 的全局顺序、单射或单峰。SAME 响应必须保留 (60.42) 的等式与 $\mathcal C_{\rm orig}=0$，不能凭曲线次序推断。

### 60.7. P4：全部例外、实际匹配与 ENTIRE 子片等号

在单独的原分支 q=a，$D_0=0,H=3a$，Q 强制 $T=\tau$。原常数式给

$$
(a-1)\lambda=C-15a\tau,\quad \lambda=\Lambda,
$$

偶恒等式给 $eg=K$。严格源 $s>2a$ 迫 $K(-s)=0$，所以 $s=p$ 或 v，正根七不接受。全部例外恰为

$$
W_p=(P(a,p),\ p\tau(t+v)(t-7),\ d_*),\qquad
W_v=(P(a,v),\ v\tau(t+p)(t-7),\ d_*),
$$

$$
d_*=a_0+7\tau V.
\tag{60.44}
$$

证明完整逆。各源由 p、v>2a 严格，gain 首项非零、漂移固定；$eg=K$，而 $o=ae$，再用 (60.13)，得到

$$
-\lambda+og=-\Lambda+aK=R+a\tau V_o.
$$

故 BOTH 恒等式成立，全部六原行成立。这也对任意所列 $p,v,\tau,a_0$ 证明实际达到该父，两例外不同源保证目标不同。例外列表没有额外根、低次或标签分支。

两个实际 J 响应与归一化响应是

$$
z_p=d_*-\tau(p+4)(6+v),\quad z_v=d_*-\tau(v+4)(6+p),
$$

$$
z_p-z_v=2\tau(v-p)\ne0,\qquad
\kappa_p=(p+4)(v+3),\quad\kappa_v=(v+4)(p+3).
\tag{60.45}
$$

只在各自实际 z 等于所取得响应时附加该世界，至多附一个。此匹配使用已取得 z，不使用真实根标签。两 gain 在七均为零，所以两末响应都为 $d_*$。

定义 $\mathcal O_\kappa$ 为 (60.36) 中满足

$$
q\in I\setminus\{a\},\quad \mathcal C_{\rm orig}(q)=0,\quad
(s+4)(5\theta+\eta)=\kappa
\tag{60.46}
$$

的全部世界；$\mathcal E_z$ 为按 (60.45) 实际匹配的例外集合。则

$$
\boxed{\mathcal K_z=\mathcal O_\kappa\cup\mathcal E_z,\qquad |\mathcal E_z|\le1.}
\tag{60.47}
$$

证明。源双射的 q=a 与 q 非 a 穷尽原域；普通分支与例外分支各有必要性及全部原行充分性。普通实际第七行由 (60.42) 双向恢复，例外由实际匹配恢复，故每个右端世界满足全部七行，任一左端世界也必在右端。这里等号针对 ENTIRE 原 degree-at-most-two 子片，不是源投影、特定 s 支、固定 T 支或例外子集。∎

### 60.8. P5：整 gain 根、实际末函数与原常数在七的方向

归一化整 gain 为

$$
\widehat g(t)=g(t)/(s\tau)=\theta(t^2-5t+3)+\eta(t-h).
$$

其首项 $\theta>0$，而

$$
\widehat g(2)=-3\theta+(2-h)\eta<0,
\quad h=\xi+4-2a>4-2a>2.
\tag{60.48}
$$

故它有两个不同实根，分居二的两侧；例如完成平方后的负最小值及正首项给两根，二处的负值使二位于根间。乘非零 $s\tau$ 不改变根，τ 的符号没有限制。

置

$$
\omega=\frac{g(7)}{s\tau}=17\theta+(7-h)\eta.
\tag{60.49}
$$

原奇恒等式在七给 $-\lambda+o(7)g(7)=R(7)+48qT$。实际 JJ 迹为 $o(7)-2q/s$，JM 迹再多 $(s+4-2q)/s$，因此

$$
f_{JJ}=a_0+R(7)+\tau x,\quad f_{JM}=a_0+R(7)+\tau y,
$$

$$
x=48q\theta-2q\omega,\qquad y=48q\theta+(s+4-4q)\omega,
$$

$$
y-x=(s+4-2q)\omega,\qquad s+4-2q>0.
\tag{60.50}
$$

这个正源因子本身没有单射含义。

必须保留原常数的方向。Q、$L_{\rm res}$ 为零时，奇 discrepancy $-\lambda+og-R-qTV_o$ 正是常数 $-R_C$。在七减去偶恒等式，得

$$
-R_C=E(7)-R(7)+(105-48q)T+
[(q-1)(s+7)+D_0]g(7)/s.
$$

$K(7)=0$ 给 $E(7)=-\Lambda-105\tau$；(60.13) 给 $R(7)=-\Lambda-48a\tau$。于是

$$
R_C/\tau=C_7-(105-48q)\theta-B_7\omega,\quad C_7=105-48a,
$$

$$
B_7=(q-1)(s+7)+D_0=(q-1)(h+2a)-1.
\tag{60.51}
$$

这是原 $C,15qT$ 的残差恒等式，不是换过原奇常数的方程。

因为 $0<q<q_0<1,\xi>0$，有

$$
D_7=-B_7=5-4q+(1-q)\xi>0.
$$

为避免与 R(t) 混名，用 $\mathscr R_7$ 表示几何线性式：

$$
\mathscr R_7=m+2-2(q+a)>m-2>9,\quad
M_7=C_7\mathscr R_7+48b(q)>0.
\tag{60.52}
$$

Q 的有限差式给

$$
\theta-1=-\frac{(q-a)\mathscr R_7}{H},\quad
F_7:=(105-48q)\theta-C_7=-\frac{(q-a)M_7}{H}.
\tag{60.53}
$$

第二式可从 $(105-48q)(\theta-1)-48(q-a)$ 及 $H\theta=b(q)$ 得到。原 $R_C=0$ 与 (60.51) 于是给

$$
\boxed{\omega=\frac{F_7}{D_7}=-\frac{(q-a)M_7}{HD_7}.}
\tag{60.54}
$$

分母已经逐项严格正。普通下侧 $q<a$ 有 $\omega>0$，上侧 $q>a$ 有 $\omega<0$，没有普通末零。结合 (60.48) 和七大于二，上根在下侧低于七、上侧高于七。这里从当前原常数重新证明末零排除，没有把既有带条件的 finalzero 平方用于其假设外。

### 60.9. P5：完整末 M 三带与可能负项的严格控制

记

$$
A_7=s+4-4q=\xi+4-2q>0,\qquad Z_7=\frac{M_7}{HD_7}>0.
$$

原 Q 与 (60.28) 有精确恒等式

$$
m-u\theta=\frac{3[(m-2a)q-2]}H,\qquad
q\theta-a=-\frac{q-a}{3}(m-u\theta).
\tag{60.55}
$$

所以

$$
y-48a=-(q-a)W_7,\qquad W_7=16(m-u\theta)+A_7Z_7.
\tag{60.56}
$$

不能预设 $m-u\theta$ 正。用有限差

$$
\frac54A_7-D_7=(q+1/4)\xi+\frac32q>0.
\tag{60.57}
$$

又 $C_7>57,\mathscr R_7>9$，故 $M_7>57\cdot9>120$；且 $m-2a>0,q>0$ 给 $(m-2a)q-2>-2$。乘以正 $HD_7$ 得

$$
\begin{aligned}
HD_7W_7
&=48[(m-2a)q-2]D_7+A_7M_7\\
&>-96D_7+A_7M_7\\
&>A_7(M_7-120)>0.
\end{aligned}
\tag{60.58}
$$

中间一行按负系数 $-96$ 的正确方向使用 $D_7<(5/4)A_7$。因此即使 (60.55) 第一项负，也有 $W_7>0$。

**定理 P5。** 任一实际普通下侧世界有 $y>48a$，任一实际上侧世界有 $y<48a$；例外世界有 $x=y=48a$。

证明。普通结论来自 (60.56)。例外 $\theta=1,q=a,\omega=0$，代 (60.50) 即得。实际响应均加同一 $a_0+R(7)$、乘同一非零 τ，因此三带始终不交；τ 负时实际大小方向反转，分离性不变。没有由曲线或带推出任何普通存在性。∎

### 60.10. P6：同父任意上侧世界的末 M 严格单射

先对辅助 $0<q<1,\xi>0$ 定义

$$
\rho(q,\xi)=\frac{\xi+4-2q}{5-4q+(1-q)\xi}.
\tag{60.59}
$$

分母正。固定 q、$\xi_1<\xi_2$ 的精确弦为

$$
\rho(q,\xi_2)-\rho(q,\xi_1)
=\frac{(\xi_2-\xi_1)[H(q)-1]}{D_7(q,\xi_1)D_7(q,\xi_2)}>0,
\tag{60.60}
$$

其中 $H(q)-1=1+2q(1-q)>0$。固定 $\xi$、q<r 的弦为

$$
\rho(r,\xi)-\rho(q,\xi)
=\frac{(r-q)(\xi^2+6\xi+6)}{D_7(q,\xi)D_7(r,\xi)}>0.
\tag{60.61}
$$

沿严格源曲线，q、$\xi(q)$ 均严格增加，所以分成这两个有限差即得 $\rho(q):=A_7/D_7$ 严格增加。比较的中间交叉点只是辅助有理式点，不宣称满足原常数或实际响应。

**定理 P6。** 同父任意两个实际上侧普通世界 $a<q<r<q_0$ 都有 $y(r)<y(q)$。无需 SAME $\kappa$。

证明。上侧有

$$
A_7-D_7=q(\xi+2)-1>2a-1>0,
$$

所以 $\rho>1$；又 $F_7<0$。实际世界由原常数式有

$$
y=48q\theta+\rho F_7.
\tag{60.62}
$$

固定两端并置 $\rho_1=\rho(q)>1$。辅助函数

$$
\mathcal H(x)=[105\rho_1+48x(1-\rho_1)]\theta(x)-C_7\rho_1
\tag{60.63}
$$

在 q 至 r 上的方括号严格递减且正，因为 x<1 使它大于 $57\rho_1+48>0$；$\theta$ 也正且严格递减。若用 $A(x)$ 暂记该方括号，则精确有限乘积差

$$
A(q)\theta(q)-A(r)\theta(r)
=[A(q)-A(r)]\theta(q)+A(r)[\theta(q)-\theta(r)]>0
$$

证明 $\mathcal H(r)<\mathcal H(q)$。进一步

$$
y(r)=\mathcal H(r)+[\rho(r)-\rho_1]F_7(r)
<\mathcal H(r)<\mathcal H(q)=y(q).
\tag{60.64}
$$

校正项严格负。故归一化值严格递减，实际响应对两种 τ 符号都单射。整个论证只要求同父两端实际兼容，不要求相同响应 $\kappa$。∎

**推论（精确剩余部分）。** 对 $n>0,\Gamma<0$ 任一实际取得 J 子片，末 M 在 ENTIRE 子片单射，当且仅当它在该子片全部实际下侧普通成员上单射。

证明。必要性是限制；充分性由三带互不交、上侧单射及至多一个匹配例外拼合。下侧必须同时满足 I、原 $\mathcal C_{\rm orig}=0$ 与 SAME 取得 $\kappa$，不是整个形式源曲线。下侧空或单点足够；多点不被断言非单射。∎

### 60.11. P7：任意实际响应的闭端恢复带

**定理 P7（任意取得响应带）。** 固定 (60.10)、(60.11) 的 SAME 实际父。如果

$$
0<G\le8a+9\qquad\text{即}\qquad -(8a+9)\le\Gamma<0,
\tag{60.65}
$$

那么对 EVERY 实际取得的 $\kappa$，原末 M 在 ENTIRE $\mathcal K_z$ 单射。

证明。a 的定义式给

$$
d_ac=(4a+1)(2a+1)=2a+9.
$$

在已经固定 G>0 下，(60.65) 等价于

$$
n\ge d_am-2a-9=d_a(m-c).
\tag{60.66}
$$

这是取得父的守卫，不含未选响应或真实源标签。

形式普通曲线在 q=a 定义良好，且

$$
\theta(a)=1,\quad u(a)=d_a,\quad M_{\rm src}(a)=c+n/d_a\ge m.
\tag{60.67}
$$

由已证严格递减，对所有 $0<q\le a$ 有 $M_{\rm src}(q)\ge m$，不能满足严格源 $M_{\rm src}<m$。故所有实际普通世界均在上侧。

当 $G=8a+9$，形式 q=a 点有 $s=2a$，只是排除的严格源边界。该计算属于取消过 q-a 的普通曲线；单独原分支 q=a 的实际例外源仍是 s=p 或 v>2a，不能据此删除。

P6 分离所有实际上侧普通世界，P4 使每个实际 J 子片至多一个例外，P5 又分离例外与每个普通世界。P4 的原域等号 (60.47) 穷尽 ENTIRE 子片，所以末 M 全集单射。证明未使用 $\kappa=8m$，未除 s-4，未假设残式次数、简单根或普通非空。∎

### 60.12. 精确选动作与全部原行的完整逆

取得六父行，按 (60.8) 至 (60.12) 确认本定理假设与带守卫。此条件是取得记录的属性；没有向原世界域额外承诺根、次数、源或 gain 符号。接下来只选 J，在原时钟六取得 z，构造 $\kappa$，按 (60.46)、(60.45) 形成 ALL 普通候选与实际匹配例外。每端保留整个 $P,g,d$。

由 (60.47)，这是确切的非空 ENTIRE 子片。若它单点，返回其完整世界并在七次 TOTAL 停止；没有必要读取第八行。

若它非单点，仅选 M，在原时钟七取得 $f_{\rm obs}$，定义

$$
y_{\rm obs}=\frac{f_{\rm obs}-a_0-R(7)}\tau.
\tag{60.68}
$$

若 $y_{\rm obs}=48a$，唯一实际匹配例外是逆；它的 $P,g,d$ 由 (60.44) 恢复。否则真实性与带内三带定理给 $y_{\rm obs}<48a$，其唯一逆为满足

$$
q\in I\setminus\{a\},\quad\mathcal C_{\rm orig}=0,\quad
(s+4)(5\theta+\eta)=\kappa,\quad y(q)=y_{\rm obs}
\tag{60.69}
$$

的完整普通候选，用 (60.36) 恢复源、三个 gain 系数与各自固定漂移。

存在性由实际世界提供；唯一性由 ENTIRE 末 M 单射提供。充分性逐层逆推：q 图谱恢复 BOTH 全多项式、全部六原行，$\kappa$ 式恢复原时钟六的实际 J 行，最后 $y=y_{\rm obs}$ 恢复且仅恢复所选原时钟七 M 行。例外亦由各自原行逆向证明与实际匹配恢复。因此一个 SAME 固定 $P,g,d$ 满足所有八原行，不是逐行拟合。没有取得互择末 J 的响应。

此为精确集合论逆与选择器，不承诺有效求根器、单点判定算法、可计算性、有限精度、效率、复杂度或资源界。它不推出普通世界存在、非单点子片存在或八读必要。

### 60.13. 复用的完整坏 M 对与 BOTH 末 FULL 切片

以下结果复用第 49 节的原常数证明，适用于所有 (60.10) 的 $\beta=7$ 父，不靠本节 n 正或带守卫。第六 M 的实际迹是 $1+3b=e(6)$，故

$$
h_M=a_0+E(6)+48T,\quad
z_M=a_0+E(6)+48\tau=d_*-\tau(6+p)(6+v).
\tag{60.70}
$$

两个例外 T=τ 同属该 FULL 子片。须排除所有普通 T=τ 世界，才能说完整等号。

若普通 T=τ 合法，原 Q 强制

$$
q=(Z+1)/2-a,\quad \delta=q-a>1/2,\quad
h_o=s-Z+7>8-2a>6.
$$

原完整奇一次再给

$$
V=(7-h_o)Z+23-2h_o,
$$

偶全部系数给一个固定

$$
g=s\tau(t^2-h_ot+\chi_o),\quad
\chi_o=h_o^2-9h_o+23=(h_o-6)(h_o-3)+5>0.
\tag{60.71}
$$

这里 $Z>4a$、s>2q，先于使用以上分母。原常数保持 $15\delta$，等价为

$$
-7V=s\chi_o-\frac\delta\epsilon(h_o-4)(h_o-6)(h_o-8).
\tag{60.72}
$$

具体地，$J_0=-\epsilon s+\delta(h_o-9)$，而 $\bar C-15q=7\epsilon V-15\delta$；代原 $R_C=0$ 得 (60.72)，其中

$$
(h_o-9)\chi_o+15=(h_o-4)(h_o-6)(h_o-8).
$$

左端负、$s\chi_o>0$、$h_o>6$，迫 $h_o>8$。利用 $V>4a^2,Z>4a$ 与 $7-h_o<0$，(60.71) 迫

$$
h_o<\frac{19+30a}{4a+2}<17/2.
$$

最后一步的正分母比较只需 a>1/2。因此

$$
0<(h_o-4)(h_o-6)(h_o-8)<45/8,\quad\chi_o>15,\quad\epsilon>1/5,
$$

$$
\frac{(h_o-4)(h_o-6)(h_o-8)}{\epsilon\chi_o}<15/8.
$$

严格源又给 $\delta<s/2$。故 (60.72) 右端严格大于 $s\chi_o/16>0$，与左端负矛盾。所有普通 T=τ 都被原常数排除，未删除末零或低次后再论证。

于是精确有

$$
\mathcal K_{6,M,z_M}=\{W_p,W_v\}.
\tag{60.73}
$$

M 后的两末迹分别为 $j+3r$、$1+2r+4b+c_{\rm src}$；两个 gain 在七同零，故 BOTH 末 FULL 切片分别是

$$
\{W\in\mathcal K_{6,M,z_M}:f_{MJ}(W)=d_*\}
=\{W\in\mathcal K_{6,M,z_M}:f_{MM}(W)=d_*\}
=\{W_p,W_v\}.
\tag{60.74}
$$

这只是该 FULL M 子片的完整对，不把 n 非零的整个六读父说成一对。两世界在每个已服务祖先都同历史且不同，所以这些祖先不能共同唯一停止。M 子片及 BOTH 末片的非单点停止守卫由同一对实际世界同时服务。

### 60.14. 精确复用层、有限子片界与负 Gamma 实际族

以下仅作为已给结果在其原假设中的复用，不计为本节新增数学内容，也不替代 P0–P7。

- 特殊响应 $\kappa=8m$、n 非零的 ENTIRE J 子片已有末 J 选择器：正 n 的一般／一般、一般／s=4、s=4／s=4 与实际匹配例外组合均包括；负 n 的第 56 节及其独立原式推导也包括 H=0 与实际匹配例外。子片单点七次停止，否则只选末 J，八次 TOTAL。两种 n 符号的特殊响应完成不等于任意响应完成。
- 第 52 节的 $\Gamma>0$、实际取得 ENTIRE J 子片已有单点七读、否则末 M 八读恢复。第 51 节 $\Gamma=0$ 的整个父恰为唯一仿射普通世界与 $W_p,W_v$，并有相应 ENTIRE 子片末 M 逆。其符号推导不转用于本节 $\Gamma<0$。
- 第 48 节 N=0、$N=L+5A=\tau n$ 的整个父恰为 $W_p,W_v$，精确轨迹为 $(p-2)(v-2)=17,p\ne v,p,v>2$。原普通全 T 比值矛盾排除了整个普通父，不只 T=τ。两个实际 J 响应不同，所以每个可达 J 子片单点，七次 TOTAL 即恢复。
- $\mathsf B_0$ 只保留既给接口的范围；它与 $\Sigma$ 的不共存或固定 b 子纤维的选择器不删除整个 B0 父的其他竞争者。不据此认证整个 B0 duty。

第 55 节对 n 非零、两种符号的每个 SAME 实际 J 子片给无条件 $|\mathcal K_z|\le6$。一般消元支在非特殊响应有非零见证

$$
P_n(4)=-75c(\kappa-8m)^3\ne0;
$$

特殊响应的一般支有非零常数见证 $3mc/2$；独立 s=4 支有三次系数 $4m\ne0$。这些在原充要过滤、独立奇异支和实际匹配例外下才给 ENTIRE 子片界；不是本节重新计算的多项式或证书。此界不证明某个末动作单射，也不证明六尖锐、更小统一界或实际六点可达。P2 的源曲线不能取代这些原过滤。

第 54 节的负 Γ 实际族保留以下精确范围。为避免与 gain 常数 $\phi$ 冲突，记其黄金比参数为

$$
\varphi_H=(1+\sqrt5)/2,\quad \chi_H=\varphi_H-1,\quad
m_H=2(a+\chi_H),\quad Z_H=m_H+1,
$$

$$
I_H=(2aZ_H-4a^2,\ Z_H^2/4).
$$

对 EVERY $V\in I_H$、任意 τ 非零、a0 实，$Z=Z_H,n=V-2m_H-15<0$ 的实际父恰有一个 H=0 普通世界，其 q 为 $\varphi_H$，并有 Γ<0；整个其他 q 分支未被排除。除至多三个 V 外，同父另有 H 非零普通世界。该例外集合可精确定义：令

$$
u_H=2\varphi_H+c,\quad\theta_b=\frac{m_H}{2(\varphi_H+\chi_H)},\quad
\eta_b=\frac{V-2m_H-15}{u_H},\quad
s_b=\frac{m_H-\eta_b}{\theta_b}-1,\quad h_b=s_b+5-u_H,
$$

$$
\Phi_H(V)=15\varphi_H\theta_b+
[(\varphi_H-1)s_b-3\varphi_H](3\theta_b-h_b\eta_b)
-[7\epsilon V+15a].
$$

这是首项系数 $-(\varphi_H-1)/(u_H^3\theta_b^2)\ne0$ 的三次式。$\Phi_H(V)\ne0$ 时的两个实际世界保持 SAME $a_0,\tau,m_H,n,V$ 和全部六原行，但未证明实际 J 响应相等；因此不是 SAME $\kappa$ 碰撞。这里的 H=0、n 负世界不在本节 n 正排除结论的假设内。

同节还在 EVERY 实际 $\Gamma=0$ 基点的任意邻域给 $\Gamma<0,n>0$ 的实际普通二次延续；父参数随延续改变。该结论不要求可微、隐函数、唯一分支或任意根选择的连续性，不供应不同延续端点的 SAME 父、SAME $\kappa$ 关系。

第 53 节的原普通末零排除在 $\Sigma,\tau\ne0,K(7)=0$ 的完整原域复用：每个实际普通世界 $g(7)\ne0$。其证明中的平方约束只在反设末零并结合原式时成立，不是所有普通非末零世界上的无条件不等式。本节 (60.54) 在自己的 n 正、G 正层另给直接证明。

### 60.15. 剩余下侧、实际共同碰撞与条件支持

本节完成带外的精确剩余正 n 域是

$$
n>0,\qquad \Gamma<-(8a+9).
\tag{60.75}
$$

对 SAME 实际父、SAME 实际 $\kappa$，下侧集合必须是

$$
\{q\in I:\ q<a,\ \mathcal C_{\rm orig}(q)=0,\
(s(q)+4)(5\theta(q)+\eta(q))=\kappa\}.
\tag{60.76}
$$

P6 没有延伸为这个集合的末 M 单射，也没有证明它发生末 M 碰撞。由 P6 推论，M 全集单射恰归于它的单射；整体一末读正完成只须 x 或 y 至少一个在 ENTIRE 子片单射，仍可有互补路线。

实际坏 J 的共同实现义务是：在 ONE SAME 实际父、ONE SAME 实际 J 响应的 (60.47) 中，有完整不同目标

$$
U_1\ne V_1,\quad U_2\ne V_2,\qquad
x(U_1)=x(V_1),\quad y(U_2)=y(V_2).
\tag{60.77}
$$

两对可重叠或不同，必须同时满足全部七原行、严格源与原常数，不能把不同父、不同响应、辅助曲线点或分别可达的最优值合并。本节没有构造这个关系；(60.75) 中全响应选择器和实际共同碰撞均为 OPEN。负 n 的非特殊任意响应完成也为 OPEN；没有整个 $\Gamma<0$ 完成、J 单峰、全局 J 单射、实际坏族或原根强迫结论。

为任意同历史集合定义 $\mathsf L_0(K)$ 为 K 非单点；$\mathsf L_{h+1}(K)$ 要求父非单点且 BOTH 动作各有实际响应，其 FULL 子片满足 $\mathsf L_h$。同历史 $K\subseteq K'$ 时，$\mathsf L_h(K)$ 向上保持：h=0 保留不同目标；归纳步保留每个动作的原实际响应，其 FULL 响应片也包含，应用归纳假设，父非单点守卫同时保持。此证明允许任意基数。

若未来实际 SAME J 子片的 (60.77) 被实现，可各抽一末碰撞对，至多四端，再并入 SAME 父 (60.73) 的坏 M 对，合计至多六端；FULL 包含保持 BOTH 动作、所有已服务祖先及停止守卫。这是有实际共同实现前提的 **至多六端点支持**，不同于上一节无条件 ENTIRE J 子片至多六的界。两者都不证明实现、最小性、尖锐性或从任意非终端失败族抽对。已服务前缀的局部结论不服务更早未取得的另一动作臂，也不迫任意原根策略进入 JMJMJ。

### 60.16. 完整惰性联合合同与原根边界

原完整二次域的八次 TOTAL 恢复与原根 $\mathsf L_7$ 仍为 OPEN。本节只完成指定实际父上的带，不完成全部 Bα、B0、全部 JMJMJ 父、早期未服务动作或任意原根失败树，也不给九读上界。

原完整三次域的八次 TOTAL 恢复与 $n_{\rm det}(3,0)\ge9$ 仍为 OPEN。三次 gain 乘线性迹可为四次；四偶节点相等仍可留下非零倍 $t(t-2)(t-4)(t-6)$。二次逆不检测未知次数、根、源、方向或平面承诺；已知类分别可恢复，不经跨类证明不能升级为未知并集。

保留未执行、未履行的完整原根共同实现合同。ALL 256 终叶槽为

$$
\sigma=(w,e),\quad w\in\{J,M\}^7,\quad e\in\{0,1\}.
$$

保留 ALL 254 非空前缀 v，原长度 i=1 至七、实际即时左乘积 $A_v$、每个后代及其共同历史。定义

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,\ it_v(P),\ i^2t_v(P),\ i^3t_v(P)).
\tag{60.78}
$$

每个前缀对每个非代表后代 σ 与同前缀代表 ρ，保留整行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0
\tag{60.79}
$$

在 SAME ENTIRE $1538\times1024$ 关系中。七层行数为 $254,252,248,240,224,192,128$；ALL 256 个整个四系数块组成 ONE 共同堆叠向量。必须同时满足每个整个块 $x_\sigma\ne0$，每个适用 SAME-source 终叶整个四分量差 $x_{(w,0)}-x_{(w,1)}\ne0$，全部严格源、全部祖先、BOTH 动作 duty 及所有停止守卫。

每槽从开始固定同一个整个

$$
g_\sigma(t)=\sum_{h=0}^3x_{\sigma h}t^h,\qquad d_\sigma=a_0-x_{\sigma0},
\tag{60.80}
$$

跨其 ALL 行使用；合并只按整个 $P,g,d$ 相等。二次限制须同时施于 SAME 合同的 ALL 块。以上只是惰性符号合同，没有生成、枚举或计算矩阵、秩、核、区间或证书，也没有取得原生成族。局部 q 图谱、终端对、选定支持、较小矩阵、投影、分臂或分路径解、逐行 refit、分别选择守卫向量，均不替代这 ONE 共同实现。

### 60.17. 除法、退化范围与证据上限

插值只除固定非零整数；源双射只除原正 b、s。例外用 a>0、a-1 非零、τ 非零与精确因子整除。普通推导先声明 q 非 a，再取消 q-a；Kpos 正先于 $\theta>0$，H=0、H<0 在除 H 前分别排除；此后 H、u、$\theta$、$D_7$ 的所有分母均已严格正。第七读与末响应归一化只除已知 τ 非零。坏 M 对证明只除正 ε 与已证正 $\chi_o$。

没有取消未知的 $g(6),g(7),\lambda,\mu$、源差、漂移差、源行列式、判别式、$1-2r$ 或 $1-2b$。s=4、s=4q、零合法系数、零读数、残式重根、残式恒零与次数取消都按完整原式处理；整个零 gain 本来非法。当前 n 正、G 正层中真正二次、两根与普通末零排除均是结论，不能回灌成原域承诺。原源边界及极限点不补作世界；普通曲线 q=a 边界绝不代替实际例外分支。τ 负时只反转实际序，不损分离与单射。

本文数学仅为可出错的、经独立符号审阅的 UNEXECUTED 推导。没有执行公式求值、代入、数值、微分、递推、枚举、CAS、矩阵／秩／核／区间／证书计算、实验、测试、构建或 Lean 核验；没有 D5、Blueprint、Reg、摄入或消化交付。没有网络或外部研究、Pro／Nyx／oracle、额外模型或代理数学认证。文字与字节完整性不验证数学。没有神经网络、经验机器学习、物理、噪声、稳定性、连续逆、有限精度、可计算性、资源、效率、复杂度、文献穷尽、原创性或优先权认证。当前已完成结论限于 P0–P7 的原世界充要图谱、任意取得响应带与其精确集合论逆；以上剩余 duty 保持 OPEN。

## 追加锚（本行以下为增补区）
