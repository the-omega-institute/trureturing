# FIB 二次低响应层的取得记录域、完整根模型与实际达到

本文独立为第 70 节。在第 68 节严格 $\beta=7$ 父的 $n<0,\ m_0<m<m_H$ 层，原时钟六实际取得 J 响应且 $\kappa<50m/7$ 时，整个七行原世界与一个严格过滤的单变量公共根集合双射。取得记录域上的主方程恒非零、次数至多五；实际取得所选末 J 后，另有恒非零、次数至多四的方程。全部目标坐标生成的扩域恰由源比 $q$ 生成。若该比在七行域上的次数为五，实际第八读使全部目标落入八行域。一般的逐历史域下降仍为 OPEN。

本节还给出 $s=8,n=-17$ 的严格内部实际世界：一个由完整原常数残式确定的代数比 $q_*\in(8/5,\phi)$，对任意 $a_0$、任一非零 $\tau$ 符号均实际达到上述低响应层。这个构造不决定其 ENTIRE 七行子片的基数，也不证明任何实际域不下降或次数上界达到。

第 69 节已经完成原 FULL 二次世界的精确实数集合论八 TOTAL 恢复与原根 no-$\mathsf L_7$；这里不重新打开该问题。第 68 节的完整选择器、插值、因子定理、标准域论与实多项式工具均为复用。本文是仓内符号综合，不作外部原创性、优先权或文献穷尽声明；全部证明保持 fallible UNEXECUTED symbolic mathematics。

## 70. 原世界、取得域与局部算术

### 70.1. SAME 原世界、原行与精确范围

每个完整世界自始固定为

$$
W=(P,g,d),\quad
P=\begin{pmatrix}r&b\\c_{\rm src}&1-r\end{pmatrix},\quad
0<r<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r(1-r),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
\tag{70.1}
$$

四元严格正，迹一且秩一。候选世界可以有不同漂移，但每个世界跨 ALL SAME 原行使用一个固定 $P$、一个 entire 非零次数至多二增益和一个 individually fixed $d$。完整目标相等指 ALL 四源元、ALL 三增益系数及漂移相等。

原即时左动作和读数为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{70.2}
$$

初读是原时钟零并计入 TOTAL。只取得所选动作的一个即时响应，不重置、复制、跳读、平移时钟、增加端口或逐行 refit。令 $j=b+c_{\rm src}$；前五动作 $JMJMJ$，其实际迹和本层使用的后续迹为

| 原时钟与动作 | 实际迹 |
| --- | --- |
| $0$ | $1$ |
| $1,J$ | $j$ |
| $2,M$ | $1+b$ |
| $3,J$ | $j+r$ |
| $4,M$ | $1+2b$ |
| $5,J$ | $j+2r$ |
| $6,J$ | $1+2b$ |
| $7,JJ$ | $j+2r$ |

这些迹由 $\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r+A_{21}b+A_{12}c_{\rm src}$ 与实际左乘得到；左下元乘 $b$。末行的 JJ 指原时钟六、七各取 J，原时钟没有重新编号。

取得 $a_0=y_0$，置 $z_i=y_i-a_0$。六行插值为

$$
E(t)=Lt+At^2,\qquad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{z_4-2z_2}{8},\quad L=\frac{4z_2-z_4}{4},\quad
D=\frac{z_5-2z_3+z_1}{8},\quad
B=\frac{z_3-z_1-8D}{2},\quad C=z_1-B-D.
\tag{70.3}
$$

它们分别插值原偶节点 $0,2,4$ 与奇节点 $1,3,5$，且由三根次数界唯一。$C$ 始终是这个 ORIGINAL 奇常数。

固定

$$
a=\frac{\sqrt{17}-1}{4},\quad 2a^2+a=2,\quad
c=2a+1,\quad \epsilon=1-a,\quad
\chi=\frac{\sqrt5-1}{2},\quad \phi=1+\chi,
$$

$$
m_0=4a-1,\qquad m_H=2(a+\chi).
$$

本文的六行父严格满足第 68 节 (68.1)：

$$
B+5D=a(L+5A),\quad
\tau=\frac{D-aA}{3a}\ne0,\quad
\Lambda=\frac{C-15a\tau}{a-1},
$$

$$
K_{\rm father}(t)=\Lambda+E(t)+\tau U_0(t)
=\tau(t+p)(t+v)(t-7),\quad
p,v>2a,\quad p\ne v,
$$

$$
U_0=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5).
\tag{70.4}
$$

使用 $K_{\rm father}$ 与下面的域 $\mathbb K_N$ 区分。令

$$
m=A/\tau=p+v-1,\quad n=(L+5A)/\tau=pv-2(p+v)-13,\quad
V=n+2m+15=pv.
$$

比较 EVERY 父系数得

$$
A=\tau m,\quad L=\tau(n-5m),\quad D=a\tau(m+3),\quad
B=a\tau(n-5m-15),
$$

$$
C=\tau\bar C,\qquad
\bar C=7(1-a)V+15a,\qquad \Lambda=-7\tau V.
\tag{70.5}
$$

范围限为 $n<0,\ m_0<m<m_H$，任意实 $a_0$ 和任一非零 $\tau$ 符号。原时钟六实际选择 J、取得 $y_6$ 后置

$$
\kappa=\frac{y_6-a_0-E(4)}{2\tau}<\frac{50m}{7}.
\tag{70.6}
$$

这是实际取得响应的条件，不是对某个辅助点预设未取得值。$\mathcal C_7$ 定义为满足 ALL SAME 七原行的 ALL (70.1) 世界；后文始终指 ENTIRE child，非选定支持或真实世界的已知子类。可达记录给 $\mathcal C_7\ne\varnothing$。

若且仅若 ENTIRE $\mathcal C_7$ 单点，在 $N=7$ 停止。否则原时钟七选 J 并实际取得 $f=y_7$，到 $N=8$；记

$$
x=\frac{f-a_0-R(7)}{\tau}.
\tag{70.7}
$$

第 68 节定理 68.1 证明本层 JJ 在 ENTIRE child 单射，所以这正是第 69 节 Balpha 的 canonical J-first 选择。并非只分开一个选定对，也不把预测当作取得行。

### 70.2. 源图谱、原残式与除法之前的局部排除

严格源域与

$$
q=r/b>0,\qquad s=2/b>2q
$$

双射，逆式为

$$
P(q,s)=
\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix}.
\tag{70.8}
$$

正向由秩一和 $s-2q=2(1-r)/b>0$ 得到；反向四元正、迹一、行列式零且返回同一 $q,s$。

置

$$
D_0=2-q-2q^2,\quad H=D_0+3q=2+2q-2q^2,\quad
e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,\quad T=\nu/s.
$$

六行 iff 严格源、whole $g\ne0$、$d=a_0-\lambda$ 及 BOTH entire identities

$$
-\lambda+eg=E+TU_0,\qquad -\lambda+og=R+qTV_o.
\tag{70.9}
$$

必要性：两边差次数至多三，三次项分别为 $T,qT$；在三个相应原节点相等，减去显示三次项后次数至多二且有三个不同根。充分性是在原节点取值。EVERY 偶系数给

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4),\quad d=a_0-sF_{\rm orig}.
\tag{70.10}
$$

EVERY 奇系数的残式恰为

$$
Q=D-qA-HT,\quad
L_{\rm res}=B-qL+15qT-D_0[A-T(s+6)],
$$

$$
R_C=C-15qT-[(q-1)s+D_0]F_{\rm orig}.
\tag{70.11}
$$

三式全为零 iff 剩余奇系数相等。尤其常数是 untouched $C-15qT$，不是投影得到的替代条件。

下面精确复用第 68 节 68.5—68.9 的低层排除，说明其假设及参数身份。该节 $r_0,b,c_{\rm src},q,s,T,a,c,u,m,n,\tau,\kappa$ 分别就是本文同名量，$r_0=r$；其 $K$ 是 $K_{\rm father}$，其 $\bar C$ 是 (70.5) 中 ORIGINAL $C/\tau$。其父就是 (70.4)，strict $p,v>2a$、不同根、任意 $a_0$、两种 $\tau$ 符号全保留；七行片恰是 (70.6) 定义的 ALL 原世界。其候选 gain 域也是整个次数至多二非零类，未只约束真实世界。

排除的顺序与范围如下。由 $m<m_H<3$，$p+v=m+1<4$，所以 $p,v<4$。第 68 节完整 $q=a$ converse 的两个世界，其实际响应满足

$$
\kappa_p=(p+4)(v+3),\quad
\kappa_v=(v+4)(p+3),
$$

$$
\kappa_p-8m=(p-4)(v-5)>0,\quad
\kappa_v-8m=(v-4)(p-5)>0.
$$

由于 $\kappa<50m/7<8m$，没有一个匹配。源图谱穷尽给 EVERY $\mathcal C_7$ 成员 ordinary $q\ne a$，此后才取消 $q-a$。

令 $u=2q+c>0,\ \eta=n/u,\ \theta=T/\tau$。原 $Q,L_{\rm res}$ 精确等价于

$$
H\theta=3a-(q-a)m,\qquad m=(s+1)\theta+\eta,
\tag{70.12}
$$

因为

$$
L_{\rm res}/\tau
=(q-a)\{u[m-(s+1)\theta]-n\}-5(Q/\tau).
\tag{70.13}
$$

同时第 68 节 (68.11) 的未除恒等式为

$$
\Gamma=n-(4a+1)m-6a=-K_{\rm pos}\theta,\quad
K_{\rm pos}=u(s-2q+c)+6q>0.
$$

$n<0,m>0,a>0$ 给 $\Gamma<0$，故先导出 $\theta>0$，此时尚未除 $H$ 或 $\theta$。因此 EVERY 成员的 $T=\tau\theta,\nu=s\tau\theta$ 非零；本层没有被无声遗漏的常数或仿射竞争者。

(70.9) 和实际六 J 给

$$
\kappa=(s+4)(5\theta+\eta),\qquad
\kappa-8m=(s-4)(\eta-3\theta).
\tag{70.14}
$$

$\eta<0,\theta>0,\kappa<8m$ 先迫 $s>4$。令
$h=s+5-u=s-2q+4-2a$、$B_{\rm src}=(q-1)s+D_0$。第 68 节 68.7 保留 SAME ORIGINAL Q/C 的恒等式为

$$
I=\bar C-3a(m+3)
=7(1-a)(p-2a)(v-2a)+a(11-14a)(p+v)+a(37-42a)>0,
$$

$$
I=3(q-s)\theta-(hB_{\rm src}+3q)\eta.
$$

它先迫 $hB_{\rm src}+3q>0$，再用其完整有限弦屏障排除 $q\le1$ 与 $4<s\le6$；结论是 $q>1,s>6$。这一复用只消费 68.7 的 SAME 原式端点界，未消费其他符号层选择器或以必要屏障替换 $R_C$。

最后置 $z_Q=a+3a/m$。$m_0<m<m_H$ 给 $\phi<z_Q<2$，未除原 Q 是

$$
H(q)\theta=m(z_Q-q),\qquad H(q)=2(\phi-q)(q+\chi).
$$

它先排 $q=\phi$、$q=z_Q$，再得 $1<q<\phi$ 或 $q>z_Q$；故 $H$ 与
$v_Q=3a-(q-a)m$ 均非零。第 68 节 68.8 的 ORIGINAL C 上界 $\bar C<19$ 和其正分母屏障排除 $q\ge2$：若 $q\ge2$，原 Q 给 $\theta<m/[2(q+\chi)]$；其父界 $w=-n>9+10a,\ w/m>6$ 迫 $s-2q>5$、$B_{\rm src}>2q-3>0$，于是

$$
\bar C>
\frac{(9-2a)(9+10a)}{5+2a}>19,
$$

最后差为 $(44a-34)/(5+2a)>0$。这和 SAME $\bar C<19$ 矛盾。因而本文每个完整成员满足

$$
1<q<2,\quad s>6,\quad s>2q,\quad
\theta>0,\quad u\ne0,\ H\ne0,\ v_Q\ne0,\ uv_Q\ne0.
\tag{70.15}
$$

所有这些排除都来自第 68 节在已匹配原假设下的数学证明，非其状态或票数。它们仅在本低层成立；其他父层合法的 $H=0,T=0,s=4$、低次、样本零、重根及奇异情形不受此排除。

### 70.3. 精确取得记录域的两个包含

定义

$$
\mathbb K_N=\mathbb Q(a,y_0,\ldots,y_{N-1}),\qquad N=7\text{ 或实际到达的 }8.
\tag{70.16}
$$

这里只显式加入固定常数 $a$ 与 ALL 实际取得读数；没有加入 $\phi,\chi,m_H$、hidden $p,v,q,s$、未选响应或未来预测。

**命题 70.1。**

$$
\mathbb K_7=\mathbb Q(a,a_0,\tau,m,n,\kappa),\qquad
\mathbb K_8=\mathbb K_7(x)=\mathbb K_7(f).
\tag{70.17}
$$

证明。插值 (70.3) 用有理系数，$a,\tau$ 非零；故归一化的
$a_0,\tau,m,n,\kappa$ 全在 $\mathbb K_7$，得右域包含于左域。反向 (70.5) 把 $A,L,D,B,C$ 全写为右域元素，其中 $V=n+2m+15$，不需要 hidden 根。前六读为 $a_0$ 加相应 $E,R$ 节点值；$y_6=a_0+E(4)+2\tau\kappa$，故 ALL 七读都在右域，得反向包含。

实际第八读后，$x=(f-a_0-R(7))/\tau$ 与
$f=a_0+R(7)+\tau x$ 互为 $\mathbb K_7$ 上的仿射式，$\tau\ne0$；故第二组两个包含均成立。第七次停止时不定义取得值 $f$ 或 $x$ 来扩大 $\mathbb K_7$。$\phi,\chi,m_H$ 在范围证明中出现不等于被加入记录域。∎

### 70.4. 全部显式多项式、严格过滤与有理重建

以下在 $\mathbb K_7[X]$ 中定义，$X$ 是形式不定元：

$$
u=2X+c,\quad H=2+2X-2X^2,\quad v_Q=3a-(X-a)m,\quad
D_0=2-X-2X^2,\quad D_\star=uv_Q,
$$

$$
S=H(mu-n)-D_\star,\qquad
W_{\rm shift}=S+(5-u)D_\star,
$$

$$
B_{\rm num}=(X-1)S+D_0D_\star,\qquad
F_{\rm num}=3u^2v_Q^2-nW_{\rm shift}H,
$$

$$
F_7=15u^2v_Q^2-\big((\kappa-5m)u+2n\big)uv_QH
+n(mu-n)H^2,
$$

$$
F_C=(\bar C H-15Xv_Q)u^3v_Q^2-B_{\rm num}F_{\rm num}.
\tag{70.18}
$$

$mu$ 在此是 $m\cdot u$，不是增益系数 $\mu$。实际取得 $f,x$ 之后，且仅在此之后，定义 $\mathbb K_8[X]$ 中的

$$
b_{\rm rec}=n+5m-\kappa,\qquad
F_8=(x+2Xb_{\rm rec})uH+16Xuv_Q+2XnH.
\tag{70.19}
$$

不要把 $F_8$ 当作七行已取得方程。

对实 $X$ 的完整严格过滤为

$$
1<X<2,\qquad H(X)v_Q(X)>0,\qquad
\big(S(X)-2XD_\star(X)\big)D_\star(X)>0.
\tag{70.20}
$$

在过滤下 $u>0$；中式使 $H,v_Q,D_\star$ 非零且 $\theta=v_Q/H>0$。最后一个式是
$(s-2X)D_\star^2>0$，其中 $s=S/D_\star$，不预设 $D_\star$ 的符号。对任何过滤点定义

$$
q=X,\quad \theta=\frac{v_Q}{H},\quad \eta=\frac n u,\quad
s=\frac S{D_\star},\quad
h=\frac{W_{\rm shift}}{D_\star}=s+5-u,\quad
F=\frac{F_{\rm num}}{u^2v_QH}=3\theta-h\eta.
\tag{70.21}
$$

这些有理式恒满足 $H\theta=v_Q,\ m=(s+1)\theta+\eta$。重建全部目标为

$$
P_{11}=\frac{2q}s,\quad P_{12}=\frac2s,\quad
P_{21}=q\left(1-\frac{2q}s\right),\quad P_{22}=1-\frac{2q}s,
$$

$$
\lambda=s\tau F,\quad
\mu=s\tau(\eta-5\theta),\quad
\nu=s\tau\theta,\quad d=a_0-s\tau F.
\tag{70.22}
$$

$s>2q>0$ 给四元正、迹一、秩一；$\tau\ne0,\theta>0$ 给 $\nu\ne0$。因此这是一个 entire 非零二次 gain 和一个跨 ALL 行固定的 $d$。没有除任何 gain 样本、$\lambda,\mu,C,b_{\rm rec},s-4$、残式首项或根重数。

### 70.5. ENTIRE 七行根模型的 BOTH 包含与 EVERY 系数

**定理 70.2。** 在 (70.4)—(70.6) 的范围，$\mathcal C_7$ 与通过 (70.20) 的 $F_7,F_C$ 的实公共根双射，逆为 (70.21)—(70.22)。不同 $q$ 给不同完整世界；空根集恰为空原片，可达条件下两者均非空。

证明先从任一完整七行世界出发。70.2 的局部排除给 (70.15)，故全部随后使用的分母非零。由原 (70.12) 得 $\theta=v_Q/H,\eta=n/u$；ordinary 关系给 $s=S/D_\star$，再给 (70.21) 的 $h,F$。严格源给最后一个过滤不等式；所以 (70.20) 必要。

实际第七行的 (70.14) 与 $s+4=(m-\eta)/\theta+3$ 等价于

$$
15\theta^2-(\kappa-5m+2\eta)\theta+\eta(m-\eta)=0.
\tag{70.23}
$$

乘非零 $u^2H^2$ 恰得 $F_7(q)=0$，每步可逆。这里 $\eta<0,m-\eta>0$，故常数负；该二次式的两个实根异号，重建的正 $\theta$ 正是第 68 节唯一正根图谱的同一点，没有另一正分支被丢弃。

另一方面

$$
B_{\rm src}=\frac{B_{\rm num}}{D_\star},\qquad
F=\frac{F_{\rm num}}{u^2v_QH}.
$$

将原归一化常数
$\bar C-15q\theta-B_{\rm src}F=0$
乘非零 $u^3v_Q^2H$ 恰得 $F_C(q)=0$。乘回 $\tau$ 就是 ORIGINAL
$C-15qT-B_{\rm src}F_{\rm orig}=0$，$F_{\rm orig}=\tau F=\lambda/s$。
等式清分母不需要乘子为正。由偶式 (70.10) 或 (70.12) 的归并得到 (70.22)，所以任一原世界必进入显示根模型。

反向，取任一严格过滤公共根，按 (70.21)—(70.22) 定义一个完整原世界。EVERY 偶升幂系数为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s).
$$

其中

$$
\nu/s=T=\tau\theta,\qquad
\nu+\mu/s=\tau[(s-5)\theta+\eta]=A-6T,
$$

$$
\mu+\lambda/s
=\tau[(u-5)\eta+(3-5s)\theta]=L+8T.
$$

最后式用 $u\eta=n$ 和 $m=(s+1)\theta+\eta$；偶常数是零，故整个第一式 (70.9) 成立，非仅采样投影。

EVERY 奇左系数为

$$
\big((q-1+D_0/s)\lambda,\ 
q(\mu+\lambda/s)+(D_0/s)\mu,\
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\big).
$$

三次是 $qT$。二次由 $H\theta=v_Q$ 即 $Q=0$ 得

$$
q(A-6T)+D_0T=D-9qT.
$$

因为 $q>1>a$，普通身份合法；(70.13) 与 $u[m-(s+1)\theta]=n$ 给原 $L_{\rm res}=0$，故一次为

$$
q(L+8T)+D_0[A-T(s+6)]=B+23qT.
$$

$F_C=0$ 可逆恢复 untouched $R_C=0$，所以常数为 $C-15qT$。因此整个奇右向量是

$$
(C-15qT,\ B+23qT,\ D-9qT,\ qT),
$$

恰为 $R+qTV_o$ 的 EVERY 系数；第二 entire identity (70.9) 成立。

在原节点 $0,2,4$ 取第一式，在 $1,3,5$ 取第二式，加 SAME $d=a_0-\lambda$，恢复 ALL SAME 六行。实际时钟四和六 J 都有迹 $1+4/s$，而 SAME gain 给

$$
g(6)-g(4)=2s\tau(5\theta+\eta).
$$

由 $F_7=0$ 反向的 (70.23)、(70.14)，得实际
$y_6-y_4=2\tau\kappa$；于是 SAME 第七取得行也恢复。一个 $P,g,d$ 同时承担全部原行。

过滤没有显式写 $s>6$，这没有放宽原模型；每个根已重建 ALL 原行，原 68.7 排除再适用，自动得 $s>6$。等 $q$ 由全部有理式固定同一个 entire world；不同 $q$ 因 $q=P_{11}/P_{12}$ 且 $P_{12}>0$，源必不同。因此两个包含及双射成立。没有一般位置、简单根、有限性、已知真次数或逐行重拟合前提。∎

### 70.6. 实际末 J、完整八行逆与单点语义

在同一个七行世界上令 $\omega=g(7)/(s\tau)$。由 (70.21)—(70.23) 得

$$
\omega=17\theta+(7-h)\eta
=32\theta+n+\eta+5m-\kappa.
\tag{70.24}
$$

整个奇式在原七给
$-\lambda+o(7)g(7)=R(7)+48qT$。
实际 JJ 迹是 $o(7)-2q/s$，所以所选实际响应恰为

$$
f=a_0+R(7)+\tau(48q\theta-2q\omega),\qquad
x=-16q\theta-2q(n+\eta+5m-\kappa).
\tag{70.25}
$$

将 $\theta=v_Q/H,\eta=n/u$ 代入末式、乘非零 $uH$，恰为 $F_8(q)=0$，且反向成立。这是一条所选实际 J 行，没有使用末 M 响应。

第 68 节 68.10 的单射在此可精确核对如下。任一完整端点满足两分支之一：
$1<q<\phi$ 或 $z_Q<q<2$。其原 Q/C 同时给下支
$\rho=-\eta/\theta<60/11<11/2,\ \omega/\theta<191/8$；
上支给 $\rho<6,\ \omega/\theta<23$。
这些是同一个实际端点的界，均不要求 $\omega>0$。

对两个不同完整世界按 $q<r$ 排，令
$\ell=r-q>0,\zeta=\theta_2>0,\rho=-\eta_2/\zeta$，
$\alpha=(\theta_1-\zeta)/(\ell\zeta)$，
$\beta=(\eta_2-\eta_1)/(\ell\zeta)=2\rho/(2q+c)>0$。
SAME $m,\kappa$ 给

$$
\alpha[15+(s_1+1)\rho]=\beta(s_1-1+\rho).
$$

因此
$8\alpha-\beta=
\frac{\beta}{15+(s_1+1)\rho}[8s_1-23+(7-s_1)\rho]>0$。
若 $6<s_1\le7$，两所需项分别正、非负；若 $s_1>7$，用 $\rho<6$ 时负系数反向，括号严格大于 $2s_1+19>0$。从 (70.24)—(70.25) 的逐项差得到

$$
x_2-x_1
=2\ell\zeta[24-\omega_2/\zeta+q(8\alpha-\beta)]
>\ell\zeta/4>0.
$$

任一 $\tau$ 符号均给实际响应差非零。这是 SAME ENTIRE child 的任意对，等 $q$ 已是相同完整世界，无基数前提。

故实际第八取得后，过滤的 $F_7,F_C,F_8$ 公共实根与 ENTIRE 八行原像双射：七行双射给前七行，$F_8$ iff 给 SAME 第八行，反向任一八行世界进入全部方程。真世界给存在，ENTIRE 单射给唯一。单点七行恰为一个严格过滤根；只有该情形在 $N=7$ 停止。非单点才实际取第八行。空片、空末交集都不是成功。这只是精确集合论规则，不包含有效单点测试或根枚举。

### 70.7. 非零次数界、完整世界数与目标域

**定理 70.3。** 对 EVERY 本层实际记录，$F_7$ 非零且次数至多五，故 ENTIRE 七行世界至多五。实际第八取得后 $F_8$ 非零且次数至多四。

证明 $ac=2,c^2=c+4$。在形式多项式商环 $\mathbb K_7[X]/(u)$ 中有

$$
2X=-c,\qquad H=-3c/2,\qquad
F_7\equiv-n^2H^2=-9c^2n^2/4\ne0.
\tag{70.26}
$$

这里 $n<0,c>0$，所以常数非零，$F_7$ 不可能为零多项式。实际第八取得后同一形式商环给

$$
F_8\equiv2XnH=3c^2n/2\ne0
\quad\pmod u.
\tag{70.27}
$$

这是形式商恒等式，不是执行代入或辅助世界测试。$u,v_Q$ 次数至多一，$H$ 至多二；$F_7$ 三项次数至多 $4,5,5$，$F_8$ 三项至多 $4,3,3$。非零多项式的不同实根数至多其次数，结合 ENTIRE 双射即得七行上界五。没有以有限性作先前单射的前提。所有首项抵消、降次、重复根、$F_C\equiv0$ 和其他次级退化均保留；不声称任何上界实际达到。∎

对 $N=7$ 或实际 $8$，令 $\mathbb K_N(W)$ 表示在 $\mathbb K_N$ 上加入 ALL 四源元、$\lambda,\mu,\nu,d$。

**命题 70.4。**

$$
\mathbb K_N(W)=\mathbb K_N(q).
\tag{70.28}
$$

证明 (70.21)—(70.22) 的全部有理式系数在 $\mathbb K_N$，所以左域包含于右域。反向 $q=P_{11}/P_{12}$、$P_{12}>0$，故 $q$ 在左域；两个包含给等号。由非零方程，$q$ 在 $\mathbb K_7$ 上代数、次数至多五；实际第八后在 $\mathbb K_8$ 上次数至多四。全部目标在记录域 iff $q$ 在记录域；不下降时至少 $P_{11},P_{12}$ 之一不在记录域。∎

这些是相对于精确记录域的代数性。允许 $a_0,\tau$ 或读数超越时，不推出目标对 $\mathbb Q$ 的绝对代数性；后面的特定代数构造也不改变这个全范围区别。

### 70.8. 实际取得的中间域与五次下降

在实际走到第八行时，设

$$
L_{\rm field}=\mathbb K_7(q),\quad
d_7=[L_{\rm field}:\mathbb K_7],\quad
e_8=[L_{\rm field}:\mathbb K_8].
$$

SAME world 的 (70.25) 是 $\mathbb K_7(q)$ 中的有理式，故

$$
\mathbb K_7\subseteq\mathbb K_8=\mathbb K_7(x)=\mathbb K_7(f)
\subseteq L_{\rm field},\qquad \mathbb K_8(q)=L_{\rm field}.
$$

非零次数界保证有限扩张；标准塔式给

$$
d_7=e_8[\mathbb K_8:\mathbb K_7],\qquad d_7\le5,\quad e_8\le4.
\tag{70.29}
$$

若 $d_7=5$，正整数 $e_8$ 整除素数五且不超过四，所以 $e_8=1$。因此 $\mathbb K_8=L_{\rm field}$，$q$ 与 ALL 目标坐标均在 $\mathbb K_8$。这个结论只在 ACTUAL 第八读之后成立，不能把 prospective $f$ 加入七行域。

八行不下降的必要可能性精确为：

| $d_7$ | 不下降所需 $e_8$ | $[\mathbb K_8:\mathbb K_7]$ |
| --- | --- | --- |
| $2$ | $2$ | $1$ |
| $3$ | $3$ | $1$ |
| $4$ | $4$ | $1$ |
| $4$ | $2$ | $2$ |

$d_7=1$ 和 $5$ 均下降。前两行要求实际所选 $f$ 已在 $\mathbb K_7$；四次的第一种也如此。这是整数塔式允许的必要模式，未给任何 actual history 实现。单点 $N=7$ 没有末塔细化；其潜在不下降次数仍可能是 $2,3,4,5$，但未证明这些模式实际出现。

### 70.9. 理论公共因式、线性因子 iff 与仍缺的实际历史义务

不执行任何 gcd 或分解，理论定义

$$
G_7=\operatorname{monicgcd}_{\mathbb K_7[X]}(F_7,F_C),\qquad
G_8=\operatorname{monicgcd}_{\mathbb K_8[X]}(F_7,F_C,F_8).
\tag{70.30}
$$

$F_7\ne0$ 保证它们定义为非零首一多项式，$F_C=0$ 时取 $F_7$ 的首一伴随。gcd 整除每个输入多项式，Bezout 又把 gcd 表为输入的多项式线性组合；故某个实数是公共根 iff 是相应 $G_N$ 的根，两向都成立，重复根不需排除。实际存在给 $G_N$ 非常数，且 $\deg G_7\le5,\deg G_8\le4$。

在一个已经完成的历史，严格过滤在 $G_N$ 的实根中恰选一个 $q$。由 (70.28)，全部目标属于 $\mathbb K_N$ iff $G_N$ 在 $\mathbb K_N[X]$ 中有一个线性因子 $X-r$，其 $r\in\mathbb K_N$ 通过完整过滤。正向若目标属于域，则 $q\in\mathbb K_N$，因子定理给 $X-q$；反向该过滤根重建完整兼容世界，完成历史唯一性迫 $r=q$。

一次 gcd 充分；更高 gcd 次数本身不证明不下降，因为其他因子可不合法而仍有一个合法线性因子。唯一合法实根也不证明线性：共轭可非实，或违反 $1<q<2,\theta>0,s>2q$；没有已证的共轭保序前提。

因此普遍域下降仍为 OPEN，两个停止时刻的义务分别是：

- 对 EVERY ACTUAL 单点七行历史，证明唯一严格过滤公共根在精确 $\mathbb K_7$ 中；或构造一个确已达到的单点历史，证明其所选不可约因子在该域上次数为 $2,3,4$ 或 $5$。
- 对 EVERY 从非单点七行 child 实际选末 J 的八行完成，证明 $F_7,F_C,F_8$ 的合法线性因子存在；或构造实现 (70.29) 剩余模式的 actual history，并证明该 $q\notin\mathbb K_8$。

任何反例都必须满足严格父、BOTH entire identities、untouched $C-15qT$、ALL SAME 实际行、协议的完整单点或非单点停止条件；八行时还要使用 SAME world 的所选实际 J 值，并证明在 ALL acquired 读数生成的域上确实不下降。必要投影、一般根式例子、选定碰撞对或未取得响应都不够。70.10—70.13 的达到构造解决非空性，尚不满足上述算术反例义务。

逐点属于记录域，不自动给一条统一有理译码器或有限分片有理公式；后者需要额外的统一性、分片及全部例外层证明。唯一半代数图也不推出域成员性。先前有限一阶和实闭域策略存在属于复用；存在代数见证的转移不固定给定的超越读数，也不把实闭包中的根变成未闭记录域的元素。这里的 gcd 是精确理论准则，没有给 gcd、因子或根的计算算法。

### 70.10. 实际达到的标量构造与原常数

以下给出本层非空的完整原世界，不以条件逆的存在措辞代替实际构造。暂在闭区间 $I=[8/5,\phi]$ 定义函数，只在严格内部取得最后的世界。令 $M=m_H=2(a+\chi)$；二次恒等式给

$$
3a=M(\phi-a),\quad
M^2+(2-4a)M-6a=0.
\tag{70.31}
$$

精确有理符号界如下。对
$f(t)=t^2+t/2-1=(t-a)(t+a+1/2)$，
$f(39/50)=-1/625,\ f(781/1000)=461/1000000$；
对 $j(t)=t^2+t-1=(t-\chi)(t+\chi+1)$，
$j(309/500)=-19/250000,\ j(619/1000)=2161/1000000$。因此

$$
\frac{39}{50}<a<\frac{781}{1000}<\frac45,\quad
\frac{309}{500}<\chi<\frac{619}{1000}<\frac58,
$$

$$
\frac85<\phi<\frac{13}8,\quad
\frac{699}{250}<M<\frac{14}5<3,\quad
\frac52<c<\frac{13}5,\quad 0<\epsilon<\frac14.
\tag{70.32}
$$

下列 $u,H,D_0$ 是 (70.18) 中的同一多项式，但本小节不以预先的记录参数 $m,n$ 定义 $\theta$。置

$$
\delta(X)=X-a,\quad \mathcal D(X)=H(X)+9\delta(X),\quad
N_\theta(X)=3au(X)+17\delta(X),
$$

$$
B_8(X)=8(X-1)+D_0(X)=(2X-3)(2-X),\quad h(X)=13-u(X),
$$

$$
\alpha(X)=126\epsilon-15X-3B_8(X),
$$

$$
P_*(X)=\alpha N_\theta+(29a-14)u\mathcal D
-17(14\epsilon+B_8h)\mathcal D\in\mathbb Q(a)[X].
\tag{70.33}
$$

$P_*$ 是标量多项式，区别于源矩阵；$\mathcal D$ 区别于取得奇系数 $D$。在 $I$ 上定义

$$
\theta=\frac{N_\theta}{u\mathcal D},\quad \eta=-17/u,\quad
m=9\theta+\eta,\quad F=3\theta-h\eta,
$$

$$
\bar C=14\epsilon(m-1)+15a,\qquad
\mathcal R=\bar C-15X\theta-B_8F.
\tag{70.34}
$$

按原常数逐项归并，恰有

$$
\mathcal R=\alpha\theta+(29a-14)
-\frac{17(14\epsilon+B_8h)}u,\qquad
P_*=u\mathcal D\mathcal R.
\tag{70.35}
$$

这里保留原 $-15X\theta$，未换成更弱投影。

在 $I$ 上，有限差
$H(r)-H(q)=2(r-q)(1-r-q)$ 与 $H(\phi)=0$ 给
$0\le H\le H(8/5)=2/25$。由 (70.32) 可得

$$
\frac45<\delta<\frac{17}{20},\quad
\frac{17}3<u<6,\quad
\frac{36}5<\mathcal D<8,\quad
4<d_a:=4a+1<\frac{21}5.
\tag{70.36}
$$

例如 $u>57/10>17/3,\ u<117/20<6$，$\mathcal D=H+9\delta$ 给其界。令
$b_\theta=3a+17\delta/u$，则

$$
\frac92<b_\theta<5,\qquad
\frac12<\theta<\frac23.
\tag{70.37}
$$

下界由 $3a>9/4,\ 17\delta/u>34/15$ 及 $\mathcal D<8$ 得；上界由
$\theta\le a/(3\delta)+17/(9u)<1/3+1/3$ 得。所有分母正，因此这些有理函数在 $I$ 上连续，端点没有隐藏极点。

### 70.11. 两端原常数的精确身份与有限差唯一性

在左端 $X=8/5$，用 $2a^2+a=2$ 逐项归并：

$$
u=(21+10a)/5,\quad
\mathcal D=(362-225a)/25,\quad
B_8=2/25,\quad h=(44-10a)/5,
$$

$$
\theta=\frac{25(166-37a)}{5352+20a},\qquad
\mathcal R(8/5)=
\frac{8(8497045a-6615924)}
{25(21+10a)(5352+20a)}>0.
\tag{70.38}
$$

为明确核对这个大系数身份，(70.35) 中
$\alpha=(2544-3150a)/25$，
$\alpha\theta+(29a-14)=(464506-520665a)/(5352+20a)$，
$14\epsilon+B_8h=(1838-1770a)/125$。通分后分子为
$8(8497045a-6615924)$，即上式。分母正，且

$$
50(8497045a-6615924)
>39\cdot8497045-50\cdot6615924=588555>0.
$$

在右端 $X=\phi$，(70.31) 给

$$
u=M+3,\quad \mathcal D=9(\phi-a),\quad m=M,\quad
\theta=\frac{M+17/(M+3)}9,\quad B_8=5\phi-8,\quad h=10-M.
$$

同一个 untouched 残式满足

$$
6(M+3)\mathcal R(\phi)
=4[(282a-984)M+529+2056a]<0.
\tag{70.39}
$$

该身份可以完全用 $M$ 展开核对：置 $\phi=1+M/2-a$，则
$B_8=5M/2-5a-3$；$3(M+3)\mathcal R$ 的展开为

$$
-5M^3+(305/2-32a)M^2-(1435+264a)M+2981a+1370.
$$

用 $M^2=(4a-2)M+6a$、$M^3=(20-18a)M+24-24a$ 后等于
$2[(282a-984)M+529+2056a]$，故 (70.39) 每项一致。负号由正因子比较给出：

$$
(984-282a)M-(529+2056a)
>
\left(984-282\frac{781}{1000}\right)\frac{699}{250}
-\left(529+2056\frac{781}{1000}\right)
=\frac{182842}{250000}>0.
$$

端点仅用于符号证明，不断言它们是构造世界。

下面不用导数证明严格唯一性。取任意 $q<r$ 于 $I$，
$\Delta=r-q>0$，用下标记端点。令
$K_{\rm diff}=11-2(r+q)$，则 $9/2<K_{\rm diff}<23/5$，且

$$
\mathcal D_r-\mathcal D_q=\Delta K_{\rm diff},\qquad
(b_\theta)_r-(b_\theta)_q=
\frac{17d_a\Delta}{u_qu_r}.
$$

因此

$$
\frac{\theta_q-\theta_r}{\Delta}
=\frac{(b_\theta)_qK_{\rm diff}-A_{\rm aux}}{\mathcal D_q\mathcal D_r},
\quad
A_{\rm aux}=\frac{17d_a\mathcal D_q}{u_qu_r}.
$$

(70.36)—(70.37) 同时给

$$
\frac{68}5<A_{\rm aux}<\frac{25704}{1445}<18,\qquad
\frac{81}4<(b_\theta)_qK_{\rm diff}<23.
$$

分子正且小于 $47/5$；分母大于 $(36/5)^2$，所以

$$
0<\theta_q-\theta_r<\frac{235}{1296}\Delta<\Delta/5.
\tag{70.40}
$$

于是
$r\theta_r-q\theta_q
=\Delta\theta_r+q(\theta_r-\theta_q)>7\Delta/40>0$。

又由 $m=9\theta-17/u$，
$m_r-m_q<34\Delta/(u_qu_r)<306\Delta/289$，
故 $\bar C_r-\bar C_q<1071\Delta/289<4\Delta$；
不需假定 $m_r-m_q$ 正。$B_8$ 为正且

$$
(B_8)_r-(B_8)_q
=\Delta[7-2(r+q)]>\Delta/2,\qquad
B_8\le B_8(\phi)=5\phi-8<1/8.
$$

$F=3\theta+221/u-17>119/6>19$，其有限差为负且大于

$$
F_r-F_q>-(3/5+14)\Delta=-73\Delta/5,
$$

因为 $442/(u_qu_r)<3978/289<14$。因此保持同一两个端点、先分解再用符号，

$$
(B_8)_rF_r-(B_8)_qF_q
=((B_8)_r-(B_8)_q)F_r+(B_8)_q(F_r-F_q)
>\frac{307}{40}\Delta>7\Delta.
$$

结合 $\mathcal R=\bar C-15X\theta-B_8F$ 得

$$
\mathcal R(r)-\mathcal R(q)<4\Delta-0-7\Delta=-3\Delta<0.
$$

故 $\mathcal R$ 在 $I$ 严格递减。连续性和两端异号给唯一
$q_*\in(8/5,\phi)$ 使 $\mathcal R(q_*)=0$；因 $u\mathcal D>0$，等价于 $P_*(q_*)=0$。端点异号也证明 $P_*$ 非零；其系数在代数域 $\mathbb Q(a)$，所以 $q_*$ 是实代数数。这里没有执行求根、区间计算或数值证书。

### 70.12. 构造的严格父根、低守卫与固定完整世界

在 $q=q_*$ 取 (70.33)—(70.34) 的同一 $u,\delta,H,\mathcal D,\theta,\eta,m,h,F$。这些是符号定义，不是执行求值。由
$\mathcal D\theta=3a+17\delta/u$ 和 $m=9\theta-17/u$ 得

$$
H\theta=3a-\delta m,\qquad m=9\theta+\eta,\qquad u\eta=-17.
\tag{70.41}
$$

先证 $m<M$，不以右端极限代替严格内部结论。由 (70.31)、(70.41)，

$$
\mathcal D(m-M)
=(\phi-q)\{9M-2(q+\chi)(M+17/u)\}.
$$

在 $I$，$q+\chi>11/5,\ u\le M+3<29/5$，
$0<9-2(q+\chi)<23/5$。因此

$$
[9-2(q+\chi)]M<322/25,\quad
34(q+\chi)/u>374/29,\quad
374/29-322/25=12/725>0.
$$

大括号严格负，$q_*<\phi,\mathcal D>0$，所以 $m<M$。

再由 $H\le2/25,\theta<2/3,\delta<13/8-a$ 得

$$
m=\frac{3a-H\theta}{\delta}
>\frac{3a-4/75}{13/8-a}>1+2a,
$$

因为后一差的正分母分子为
$193/600-a/4>73/600>0$。故

$$
p=2,\quad v=m-1,\quad
2a<v<2=p,\quad
m_0<m<m_H,\quad
V=pv=2m-2,\quad n=V-2(p+v)-13=-17<0.
\tag{70.42}
$$

这两个父根真实、不同且严格超过 $2a$。

固定任意 $a_0\in\mathbb R,\tau\in\mathbb R\setminus\{0\}$，设

$$
s=8,\quad
P=\begin{pmatrix}q/4&1/4\\q(1-q/4)&1-q/4\end{pmatrix},
$$

$$
\lambda=8\tau F,\quad
\mu=8\tau(\eta-5\theta),\quad
\nu=8\tau\theta,\quad
g(t)=\lambda+\mu t+\nu t^2,\quad d=a_0-\lambda.
\tag{70.43}
$$

$8/5<q<\phi<13/8<4$ 给所有源元正；迹一，
$\det P=(q/4)(1-q/4)-(1/4)q(1-q/4)=0$，非零迹排除秩零。$\tau\ne0,\theta>0$ 给 $\nu\ne0$，故一个 whole 非零二次 gain；$d$ 是同一个固定实数。

定义实际归一化候选

$$
\kappa=12(5\theta+\eta).
$$

直接归并而不取消符号不明项，

$$
7\kappa-50m=-30\theta+34\eta=-30\theta-578/u<0.
\tag{70.44}
$$

下面证明这个 $\kappa$ 正是 (70.43) 的 actual clock-six 读数归一化，因此此严格式不是必要投影。两个非零 $\tau$ 符号同样有效。

### 70.13. 构造的 BOTH 整式、EVERY 系数与 ALL SAME 原行

以 (70.43) 的一个固定世界定义

$$
A=\tau m,\quad L=\tau(-17-5m),\quad D=a\tau(m+3),\quad
B=a\tau(-32-5m),\quad C=\tau[14\epsilon(m-1)+15a],
$$

$$
E=Lt+At^2,\quad R=Dt^2+Bt+C,\quad
\Lambda=-14\tau(m-1)=-7\tau V,\quad T=\tau\theta.
\tag{70.45}
$$

这些系数满足
$B+5D=a(L+5A)$、
$(D-aA)/(3a)=\tau$、
$(C-15a\tau)/(a-1)=\Lambda$，
且

$$
\Lambda+E+\tau U_0=\tau(t+2)(t+m-1)(t-7).
\tag{70.46}
$$

两边升幂向量均为
$(-7\tau V,\tau(V-7Z),\tau(Z-7),\tau)$，$Z=m+1,V=2m-2$。因此得到精确父因子，而非只匹配其根。

用 $e=1+t/8,\ o=qe+D_0/8$，EVERY 偶左系数如下：

$$
\nu/8=T,\qquad
\nu+\mu/8=\tau(3\theta+\eta)=A-6T,
$$

$$
\mu+\lambda/8
=\tau(8\eta-40\theta+F)
=\tau[(u-5)\eta-37\theta]=L+8T,
$$

常数为零；最后等式用 $u\eta=-17,\ m=9\theta+\eta$。故第一 whole identity
$-\lambda+eg=E+TU_0$ 在每个系数成立。

EVERY 奇左向量是

$$
\big((q-1+D_0/8)\lambda,\
q(\mu+\lambda/8)+(D_0/8)\mu,\
q(\nu+\mu/8)+(D_0/8)\nu,\ q\nu/8\big).
$$

三次是 $qT$；二次为

$$
\tau[qm+(D_0-6q)\theta]
=\tau[qm+(H-9q)\theta]=D-9qT
$$

由 (70.41) 得到。原一次残式满足精确归并

$$
L_{\rm res}/\tau
=(q-a)\{u[m-9\theta]-(-17)\}
-5\{3a-(q-a)m-H\theta\}=0.
$$

又 $A-14T=\tau(\eta-5\theta)=\mu/8$，所以奇一次是 $B+23qT$。最后奇常数为

$$
(q-1+D_0/8)\lambda=\tau B_8F=C-15qT,
$$

因为 $\mathcal R(q_*)=0$ 正是 $\bar C-15q\theta=B_8F$。因此 EVERY 奇系数为
$(C-15qT,B+23qT,D-9qT,qT)$，第二 whole identity
$-\lambda+og=R+qTV_o$ 完整成立，原 $C-15qT$ 未改。

$d+g(0)=a_0$；在原偶节点 $0,2,4$，$U_0=0$；在原奇节点 $1,3,5$，$V_o=0$。实际 JMJMJ 迹正是这些节点的 $e,o$，故 SAME world 给

$$
y_0=a_0,\quad y_2=a_0+E(2),\quad y_4=a_0+E(4),\quad
y_1=a_0+R(1),\quad y_3=a_0+R(3),\quad y_5=a_0+R(5).
$$

三根唯一插值反向保证取得的 $A,L,D,B,C$ 就是 (70.45)，特别 $C$ 真是取得的 ORIGINAL 奇常数；父并非独立于实际历史另行赋值。

原时钟六 J 与时钟四有 SAME 迹 $1+4/8=3/2$，同一个 gain 给

$$
g(6)-g(4)=16\tau(5\theta+\eta),\qquad
y_6-y_4=24\tau(5\theta+\eta)=2\tau\kappa.
$$

故 $(y_6-a_0-E(4))/(2\tau)=\kappa$ 是实际第七取得行，(70.44) 为 actual 低响应守卫。所有原时钟 $0,\ldots,6$ 同时由 (70.43) 的同一个 strict $P$、whole $g\ne0$、fixed $d$ 承担。

反向身份也清楚：$P_*=u\mathcal D\mathcal R$ 且乘子正，故标量构造方程 iff ORIGINAL 常数；(70.41) 恢复原 Q 与原一次残式；完整系数向量 iff BOTH 整式，而两整式与原六行通过三根论证互相恢复。实际六 J 迹给第七方程的 iff。没有必要残式冒充充分世界。

取 $a_0=0,\tau=1$ 即给一个完全指定的代数世界；任意 $a_0$ 与非零 $\tau$ 给同一规范化代数源的家族。每个构造点是 (70.20) 的严格过滤点：$1<q<2$，
$H>0,\ v_Q=H\theta>0$，
$s=8>2q$，因而 $D_\star\ne0$ 且最后过滤式正。
它也进入 $F_7,F_C$ 的完整七行根模型。

这里唯一的是 $s=8,n=-17$ 构造切片上的 $q_*$；ENTIRE 七行 child 还可含不同 $s$ 的世界，未证明其单点或非单点。没有实际八读必要性、实际域不下降或上界达到结论。对本家族若协议需要末读，仍按 SAME world 的 (70.25) 实际取得，不凭预测加入记录域。

### 70.14. 语义、完整未执行合同与边界

第 69 节定理 69.2 与推论 69.4 已给 ALL 原严格源、ALL whole 非零 real degree-at-most-two gain、任意 fixed 实漂移的精确实数集合论至多八 TOTAL 完整恢复及 EVERY 原初读后 no-$\mathsf L_7$。本节只细化其一个实际低层的算术；它不增加有效性、资源或噪声语义。三次 EIGHT-TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$ 仍为 OPEN；三次乘线性迹可四次，二次的三次整式不提供未知三次或未知 gain-class union 的逆。

这里不补入 $q=0,s=2q,r=0,1,b=0,c_{\rm src}=0$、极限或无限源、whole 零 gain。父条件也不补入 $p=v,p=2a,v=2a,\tau=0$。其他原层合法的系数零、样本或观察零、增益重根、$H=0,T=0,s=4$、重复或降次多项式与恒零次级残式，仍按原式保留；(70.15) 的排除只在已声明低域成立。所有重建在实际清分母前已经排除所需零点；没有取消残式首项、根重数或未知增益样本。

继承的 simultaneous common-vector 合同保持 COMPLETE INERT、UNEXECUTED、UNFULFILLED。全部 $256$ 终叶槽 $\sigma=(w,e)$，$w\in\{J,M\}^7,e\in\{0,1\}$；全部 $254$ 非空 actual prefixes $v$，原长度 $i=1,\ldots,7$、即时左乘积 $A_v$ 及 EVERY 后代均保留。定义

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,it_v(P),i^2t_v(P),i^3t_v(P)).
$$

EACH prefix 的 EVERY 指定非代表后代 $\sigma$ 相对 SAME-prefix 代表 $\varrho$ 保留 WHOLE 行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\varrho)x_\varrho=0.
$$

ALL 行属于 SAME 完整 $1538\times1024$ 关系，继承层规格
$254,252,248,240,224,192,128$，表达 $2^i(2^{8-i}-1)=256-2^i$。
ONE SAME common stacked vector 含 ALL $256$ whole 四系数 gain 块，每块非零；每槽固定一个 strict $P_\sigma$、一个 whole
$g_\sigma(t)=\sum_{j=0}^3x_{\sigma,j}t^j$ 与
$d_\sigma=a_0-x_{\sigma,0}$，跨 ALL SAME 原行不变。每个 terminal pair 的完整目标不同；适用 SAME-source pair 保留 WHOLE 四分量差
$x_{(w,0)}-x_{(w,1)}\ne0$。ALL strict sources、ALL 祖先方程、BOTH action duties、ALL 父/子/末非单点 stopguards 必须在 SAME 向量和 SAME entire worlds 同时成立；只合并整个 $P,g,d$ 相等槽。二次限制 $x_{\sigma,3}=0$ 同时施于 ALL SAME blocks。

本节局部公共根模型、实际达到、末 J 单射与域塔均不替代该共同实现；选定支持、投影或较小关系、分路径或分臂向量、逐行 gain/drift refit、遗漏后代和独立守卫向量也不替代它。没有生成、枚举、求解、归约、测试或机械认证该关系，没有核对其编码与递归失败谓词等价。第 69 节逻辑 no-$\mathsf L_7$ 与这一未履行编码合同的界限不变。

所有多项式和代数均是未执行符号推理。没有执行公式求值或代入程序、数值、导数、递推、数学枚举、CAS、gcd 或因式分解、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean、D5、Blueprint、Reg、摄入或消化。文本字节、UTF-8、LF、哈希与 strict JSON 检查只验证文本完整性，不验证数学。

不主张可计算性、有效 guard/root/factor 算法、BSS、有限位、复杂度、效率、可行性、资源、噪声、稳定性、连续逆、ML/NN、尖锐性、minimax、第八次必要、次数上界达到或一般 gain 空间逆。逐历史域下降和其实际反例义务仍如 70.9 所述 OPEN；本节的达到定理只关闭严格低响应层非空性。

## 追加锚（本行以下为增补区）
