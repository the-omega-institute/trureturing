# FIB 二次低响应层的实际源生成元与取得记录有理重建

本文独立为第 71 节。对第 70 节严格 $\beta=7$、$n<0,m_0<m<m_H$、实际原时钟六 J 响应 $\kappa<50m/7$ 的完整原世界，在 $N=7$ 或实际到达的 $N=8$，全部目标扩域恰为

$$
\mathbb K_N(W)=\mathbb K_N(s)=\mathbb K_N(q).
$$

因此该层逐历史的全部目标域下降，精确等价于单个实际源坐标 $s=2/P_{12}$ 属于实际记录域。这是生成元等价，不是普遍成员性证明。若实际 $s\in\mathbb Q(a)$，则七读已经使全部目标属于 $\mathbb K_7$；若协议实际继续，所选第八读属于同一域，故 $\mathbb K_8=\mathbb K_7$。

在实际 $s=8$ 时，全文给出只用取得参数的有理式。复用第 70 节 $s=8,n=-17$ 的完整达到定理，得到非空实际家族，并证明其精确取得域为 $\mathbb Q(a,a_0,\tau,q_*)$。这不决定 ENTIRE 七行子片基数，不证明第八读必要或任何域不下降。

新增内容是实际模型的 $s$ 生成元等价及取得记录有理重建。第 70 节完整根模型、$q$ 生成元、标量根的达到与有限差唯一性，以及第 69 节原 FULL 二次精确实数至多八 TOTAL 恢复，均为复用。全部数学保持 fallible UNEXECUTED symbolic mathematics；不作外部原创性、优先权或文献穷尽声明。

## 71. 实际低响应记录上的源生成元

### 71.1. 原世界、时钟、ENTIRE 子片与取得域

每个原世界自始固定为

$$
W=(P,g,d),\quad P=\begin{pmatrix}r&b\\c_{\rm src}&1-r\end{pmatrix},\quad
0<r<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r(1-r),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
\tag{71.1}
$$

四源元严格正、迹一、秩一。完整目标指 ALL 四源元、ALL 三增益系数和漂移。候选世界可以有不同漂移，但每个世界跨 ALL 原行只有一个 fixed $d$ 和一个 entire $g$。

原即时左动作与读数为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{71.2}
$$

初读 $y_0$ 计入 TOTAL。前五动作是 $JMJMJ$，服务原时钟零至五；原时钟六实际选 J、取得 $y_6$。这些时钟的迹依次为
$1,j,1+b,j+r,1+2b,j+2r,1+2b$，其中 $j=b+c_{\rm src}$。若再选 J，原时钟七的实际 JJ 迹是 $j+2r$。重复迹仍乘新原时钟的 SAME gain 样本。

置 $a_0=y_0,z_i=y_i-a_0$。取得插值与归一化为

$$
E(t)=Lt+At^2,\quad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{z_4-2z_2}{8},\quad L=\frac{4z_2-z_4}{4},\quad
D=\frac{z_5-2z_3+z_1}{8},\quad B=\frac{z_3-z_1-8D}{2},\quad C=z_1-B-D.
\tag{71.3}
$$

固定常数和父条件为

$$
a=\frac{\sqrt{17}-1}{4},\quad 2a^2+a=2,\quad c=2a+1,\quad
\chi=\frac{\sqrt5-1}{2},\quad\phi=1+\chi,
$$

$$
m_0=4a-1,\quad m_H=2(a+\chi),\quad
B+5D=a(L+5A),\quad\tau=\frac{D-aA}{3a}\ne0,
$$

$$
\Lambda=\frac{C-15a\tau}{a-1},\quad U_0=t(t-2)(t-4),\quad V_o=(t-1)(t-3)(t-5),
$$

$$
\Lambda+E+\tau U_0=\tau(t+p)(t+v)(t-7),\qquad p,v>2a,\quad p\ne v.
\tag{71.4}
$$

置

$$
m=A/\tau=p+v-1,\quad n=(L+5A)/\tau=pv-2(p+v)-13,\quad V=n+2m+15=pv.
$$

本节精确范围是

$$
n<0,\quad m_0<m<m_H,\quad
\kappa=\frac{y_6-a_0-E(4)}{2\tau}<\frac{50m}{7}.
\tag{71.5}
$$

$a_0$ 任意，$\tau$ 两种非零符号均保留；$\kappa$ 来自 SAME world 的实际取得行。父系数逐项为

$$
A=\tau m,\quad L=\tau(n-5m),\quad D=a\tau(m+3),\quad B=a\tau(n-5m-15),
$$

$$
C=\tau\bar C,\quad \bar C=7(1-a)V+15a,\quad\Lambda=-7\tau V.
\tag{71.6}
$$

令 $\mathcal C_7$ 是满足 SAME 七原行的 ALL (71.1) 世界，始终不对竞争者加 $s$ 有理、$s=8$ 或构造切片承诺。实际世界保证非空。若且仅若 ENTIRE $\mathcal C_7$ 单点，在 $N=7$ 停止；否则在原时钟七实际选 J，取得 $y_7$ 后到 $N=8$。第 70 节 70.6 的 ENTIRE J 单射在这些相同假设下给终片唯一性。

定义

$$
\mathbb K_N=\mathbb Q(a,y_0,\ldots,y_{N-1}),\qquad N=7\text{ 或实际到达的 }8.
\tag{71.7}
$$

第 70 节命题 70.1 的两个包含在此直接可见：插值与非零 $a,\tau$ 给 $a_0,\tau,m,n,\kappa\in\mathbb K_7$；反向 (71.6) 给全部插值系数，前六读为 $a_0$ 加相应节点值，第七读为 $a_0+E(4)+2\tau\kappa$。故

$$
\mathbb K_7=\mathbb Q(a,a_0,\tau,m,n,\kappa).
\tag{71.8}
$$

实际第八取得后才有 $\mathbb K_8=\mathbb K_7(y_7)$。没有把 $\phi,\chi,m_H,p,v,q,s$、未选响应或未来值加入定义域。

### 71.2. 原整式接口、局部排除与参数身份

源坐标与其逆为

$$
q=r/b>0,\quad s=2/b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix}.
\tag{71.9}
$$

正向由秩一强制此逆式，反向四元正、迹一、行列式零且返回同一 $q,s$。置

$$
D_0=2-q-2q^2,\quad H=D_0+3q,\quad
\delta=q-a,\quad u=2q+c,\quad T=\nu/s.
$$

第 70 节 70.2 的六行 iff 保留 BOTH entire identities

$$
-\lambda+(1+t/s)g=E+TU_0,\qquad
-\lambda+[q(1+t/s)+D_0/s]g=R+qTV_o,
\tag{71.10}
$$

以及 $d=a_0-\lambda$。其 EVERY 偶系数给

$$
\nu=sT,\quad\mu=sA-sT(s+6),\quad
F_{\rm orig}=\lambda/s=L-sA+T(s+2)(s+4).
$$

其 EVERY 奇系数的三个原残式是

$$
Q=D-qA-HT=0,\qquad
L_{\rm res}=B-qL+15qT-D_0[A-T(s+6)]=0,
$$

$$
R_C=C-15qT-[(q-1)s+D_0]F_{\rm orig}=0.
\tag{71.11}
$$

$C$ 是 (71.3) 的 ORIGINAL 奇常数；以下不改变 $C-15qT$。

本节与第 70 节的 $W,P,r,b,c_{\rm src},g,d,Q_i,y_i,a_0,E,R,A,L,D,B,C$ 逐项同一；其父 $K_{\rm father}$ 是 (71.4) 的整式，$p,v,a,c,\tau,m,n,V,\kappa,q,s,T,H,u$ 也逐项同一。取得零至六的动作和原时钟同一，候选域都是 ALL whole 非零次数至多二 gain，绝非已知真次数子类。

据此复用第 70 节 70.2 对 SAME 原式的完整排除：EVERY $\mathcal C_7$ 成员 ordinary $q\ne a$，且 $1<q<2,s>6,\theta:=T/\tau>0$，$H\ne0$。这些结论的原范围恰为 (71.4)—(71.5)。其中 ordinary 排除来自两个完整例外 $s=p,v$ 的响应
$\kappa_p=(p+4)(v+3),\kappa_v=(v+4)(p+3)$，二者均大于 $8m$；这里 $p+v=m+1<4$，而取得值小于 $50m/7<8m$。正 $\theta$ 来自未除恒等式

$$
\Gamma=n-(4a+1)m-6a=-[u(s-2q+c)+6q]\theta<0.
\tag{71.12}
$$

方括号严格正，故结论不是假定二次次数。进一步的 $q>1,s>6,H\ne0$ 消费的是该节 ORIGINAL Q/C 的有限弦和带符号分支证明，不把必要屏障代替原常数。

本节新证明只需先得到 $q\ne a,\theta>0,\eta:=n/u<0$；71.5 的 $q$ 方向另用上述 $H\ne0$。所有复用都是这些已显示数学命题在同一原参数上的应用，不重新证明其他父层选择器或原根恢复。

### 71.3. 取得线性系统及清分母前的非零性

**引理 71.1。** 对 EVERY 本层实际世界，原 ordinary 方程和实际第七行给可逆系统

$$
m=(s+1)\theta+\eta,\qquad
\kappa=(s+4)(5\theta+\eta),\qquad
n=(2q+c)\eta.
\tag{71.13}
$$

其中 $\theta>0,\eta<0,s>4$，所以 $(s+4)(s-4)$ 与 $\eta$ 均非零。

证明。$ac=2$ 给 $D_0=-\delta u,H=3q-\delta u$。原系数归并为

$$
Q/\tau=3a-\delta m-H\theta,
$$

$$
L_{\rm res}/\tau=\delta\{u[m-(s+1)\theta]-n\}-5(Q/\tau).
\tag{71.14}
$$

因为已经证明 $\delta,\tau$ 非零，$Q=L_{\rm res}=0$ iff
$H\theta=3a-\delta m$ 与系统第一、三式。这里先由 $u>0,n<0$ 得 $\eta<0$；(71.12) 再得 $\theta>0$，没有除 $H$。

偶系数和前两式给

$$
F:=F_{\rm orig}/\tau
=n-(s+5)m+(s+2)(s+4)\theta
=3\theta-(s+5-u)\eta,
$$

$$
\lambda=s\tau F,\quad\mu=s\tau(\eta-5\theta),\quad
\nu=s\tau\theta,\quad d=a_0-\lambda.
\tag{71.15}
$$

归并时 $\theta$ 系数为三，$\eta$ 系数为 $u-s-5$。原时钟四与六 J 的 SAME 迹为 $(s+4)/s$，而 SAME gain 给
$g(6)-g(4)=2s\tau(5\theta+\eta)$。由于 $y_4=a_0+E(4)$，取得定义恰给系统第二式；反向同一式恢复 SAME 第七行。

在尚未除 $s-4$ 时相减得

$$
\kappa-8m=(s-4)(\eta-3\theta).
\tag{71.16}
$$

左边严格负，$\eta-3\theta<0$，故 $s>4$。因而 $s+4>0,s-4>0$，所需共同分母已经严格正；$\eta<0$ 也在随后除它之前成立。第 70 节的更强 $s>6$ 与此一致。整个系统可逆性只使用已声明的非零量和 SAME 行。∎

### 71.4. 给定实际 s 的有理重建与完整 converse

令 $\Delta_s=(s+4)(s-4)$。两条取得线性式分别作线性组合，得

$$
(s+4)m-\kappa=\Delta_s\theta,
$$

$$
(s+1)\kappa-5(s+4)m=\Delta_s\eta.
\tag{71.17}
$$

因此 EVERY 实际世界都满足

$$
\theta=\frac{(s+4)m-\kappa}{(s+4)(s-4)},\quad
\eta=\frac{(s+1)\kappa-5(s+4)m}{(s+4)(s-4)},\quad
q=\frac{n/\eta-c}{2}.
\tag{71.18}
$$

共同分母和 $\eta$ 已先证非零。第三式由 $u\eta=n$ 恢复 $u$，不是选取某个投影根。再用 (71.9)、(71.15) 得 ALL 四源元、$\lambda,\mu,\nu,d$ 为取得参数和实际 $s$ 的有理式。源式的 $s$ 也已正。

为精确区分这些条件式和完整逆，固定一个满足 (71.4)—(71.5) 的实际取得七行记录，取任意实 $\sigma>4$。正分母 $\Delta_\sigma$ 允许先用 (71.18) 的前两式定义 $\Theta,\mathcal E$。先要求 $\Theta>0,\mathcal E<0$；在此非零条件下才定义 $q=(n/\mathcal E-c)/2$，再要求

$$
q>0,\quad\sigma>2q,
$$

$$
H(q)\Theta=3a-(q-a)m,
$$

$$
\bar C-15q\Theta-[(q-1)\sigma+D_0(q)]
[3\Theta-(\sigma+5-2q-c)\mathcal E]=0.
\tag{71.19}
$$

则且仅则该 $\sigma$ 给一个完整兼容世界，逆为 (71.9)、(71.15)，其中 $\theta=\Theta,\eta=\mathcal E,s=\sigma$。

证明必要性由前面原式和局部排除。充分性首先是线性逆本身：将两个分子代回，得
$(\sigma+1)\Theta+\mathcal E=m$ 与
$(\sigma+4)(5\Theta+\mathcal E)=\kappa$，而定义 $q$ 给 $(2q+c)\mathcal E=n$。这是 (71.17) 在 $\Delta_\sigma\ne0$ 下的反向，不需任何符号不明的消去。

由严格源和 $\tau\ne0,\Theta>0$，重建的源严格合法、$\nu=\sigma\tau\Theta\ne0$。其偶升幂向量为

$$
(0,\mu+\lambda/\sigma,\nu+\mu/\sigma,\nu/\sigma)
=(0,L+8T,A-6T,T),\quad T=\tau\Theta.
$$

具体地二次项为 $\tau[(\sigma-5)\Theta+\mathcal E]=A-6T$，一次项为
$\tau[(u-5)\mathcal E+(3-5\sigma)\Theta]=L+8T$，因为 $u\mathcal E=n$。原 Q 由 (71.19) 恢复，(71.14) 给原 $L_{\rm res}=0$，没有反向除 $q-a$；最后一式乘 $\tau$ 正是 ORIGINAL $R_C=0$。所以奇升幂向量完整等于

$$
(C-15qT,\ B+23qT,\ D-9qT,\ qT).
$$

BOTH (71.10) 在 EVERY 系数成立。在原偶节点零、二、四及奇节点一、三、五取值，加 SAME $d=a_0-\lambda$ 恢复 ALL 六原行；实际六 J 迹和恢复的第二线性式给 $y_6-y_4=2\tau\kappa$，恢复 SAME 第七行。因此一个 fixed $P,g,d$ 同时承担所有取得行。实际世界的反向又给全部条件，故两个包含成立。

对不同 $\sigma$，$P_{12}=2/\sigma>0$ 不同，整个世界不同；给定 $\sigma$ 的上述有理式固定全部目标。此 converse 没有把任意取得数据无条件变成世界，也没有丢弃 ORIGINAL 常数或限制 ENTIRE 竞争者。∎

### 71.5. 实际目标域的两个生成元

**定理 71.2。** 令 $\mathbb K_N(W)$ 是在 (71.7) 上加入 ALL 四源元、$\lambda,\mu,\nu,d$ 的域。对 $N=7$ 或实际到达的 $N=8$，

$$
\boxed{\mathbb K_N(W)=\mathbb K_N(s)=\mathbb K_N(q)}.
\tag{71.20}
$$

证明先取 $F_N=\mathbb K_N$。取得参数都在 $\mathbb K_7\subseteq F_N$。由 (71.18)、(71.9)、(71.15) 且全部分母非零，ALL 目标属于 $F_N(s)$，故 $F_N(W)\subseteq F_N(s)$。反向严格 $P_{12}>0$，所以 $s=2/P_{12}\in F_N(W)$，得 $F_N(s)\subseteq F_N(W)$。这是两向包含，不以完整历史唯一性代替域运算。

为核对 $q$ 的等号，原 Q 和第 70 节已证的 $H\ne0$ 给

$$
\theta=\frac{3a-(q-a)m}{H(q)},\quad\eta=\frac n{2q+c},\quad
s=\frac{m-\eta}{\theta}-1.
\tag{71.21}
$$

这里 $2q+c>0,\theta>0$，所以 $s\in F_N(q)$。再用全部目标有理式得 $F_N(W)\subseteq F_N(q)$。反向 $q=P_{11}/P_{12}$ 且 $P_{12}>0$，故 $F_N(q)\subseteq F_N(W)$。这也精确复现第 70 节命题 70.4 的原范围，没有新增一个无关的根恢复结论。两组包含合并即 (71.20)。∎

于是 ALL 目标属于实际 $\mathbb K_N$ iff 实际 $s\in\mathbb K_N$ iff 实际 $q\in\mathbb K_N$。任意固定 $N$ 的完整生成扩域相同，也有相同的相对次数；第 70 节给出的代数性和次数界可直接转用。它们相对于取得域，不要求任意实读数对 $\mathbb Q$ 代数。

特别，证明一个 hidden $s$ 只是代数的、唯一合法的或落在某区间，都没有证明其属于 $\mathbb K_N$。这里把剩余障碍精确压成一个实际源坐标，没有消除该障碍。

### 71.6. 实际有理 s 轨迹及第八读不扩域

**推论 71.3。** 在上述原低层，若 ACTUAL $s\in\mathbb K_7$，则 ALL 目标属于 $\mathbb K_7$。尤其对任意 $\sigma\in\mathbb Q(a)$，每个 ACTUAL $s=\sigma$ 的原世界均满足此结论。若该世界实际到达 $N=8$，则 $\mathbb K_8=\mathbb K_7$。

证明由 (71.20) 在 $N=7$ 得 $\mathbb K_7(W)=\mathbb K_7(s)=\mathbb K_7$。在实际第八分支，所选 J 的原响应是

$$
y_7=d+(j+2r)(\lambda+7\mu+49\nu),\quad j=P_{12}+P_{21},\quad r=P_{11}.
\tag{71.22}
$$

右侧 ALL 因子已在 $\mathbb K_7$，故实际 $y_7\in\mathbb K_7$。两向包含
$\mathbb K_7\subseteq\mathbb K_8=\mathbb K_7(y_7)\subseteq\mathbb K_7$
给等号。若在七读停，没有取得第八值，也不将 (71.22) 的 prospective 值加入记录域。∎

条件是关于真实世界的逐点成员性，没有把 $s$ 当取得标签。它不要求、也不允许把所有兼容世界先限制为 $s\in\mathbb Q(a)$。即使真实世界满足条件，ENTIRE $\mathcal C_7$ 仍按 (71.1) 定义。七读是否足以完整辨认所有竞争者，仍只由该 ENTIRE 集合是否单点决定。

对一个明确承诺且给定 $\sigma$ 的输入类，(71.18) 提供其条件有理公式；没有这个承诺，逐点域成员性不自动提供统一有理公式、有限分片、有效判据或完整七读译码器。若后来证明实际 $s\in\mathbb K_8$，同一定理也给八行下降；本推论没有为任意实际 $s$ 提供这种证明。

### 71.7. 实际 s 等于八的显式取得式

**推论 71.4。** 对 EVERY ACTUAL $s=8$ 的本层原世界，令

$$
D_{\rm rec}=3\kappa-20m.
$$

则

$$
\theta=\frac{12m-\kappa}{48}>0,\qquad
\eta=\frac{D_{\rm rec}}{16}<0,\qquad D_{\rm rec}<0,
$$

$$
q=\frac{8n}{D_{\rm rec}}-\frac c2,\qquad
P=\begin{pmatrix}q/4&1/4\\q(1-q/4)&1-q/4\end{pmatrix},
\tag{71.23}
$$

$$
\lambda=\tau(136m-20\kappa+8n),\quad
\mu=\frac{\tau(7\kappa-60m)}3,\quad
\nu=\frac{\tau(12m-\kappa)}6,\quad d=a_0-\lambda.
\tag{71.24}
$$

证明 $\Delta_8=48$，所以 (71.18) 给
$\theta=(12m-\kappa)/48$ 与
$\eta=(9\kappa-60m)/48=D_{\rm rec}/16$。原范围的 $\theta>0,\eta<0$ 给两个所需符号；特别在除 $D_{\rm rec}$ 前它严格负。$n=u\eta$ 给所示 $q$，源逆在正 $s=8$ 下给全部四元。

归一化截距为

$$
F=3\theta-(13-u)\eta=3\theta-13\eta+n
=17m-\frac52\kappa+n.
$$

乘 $8\tau$ 得 $\lambda$。另外

$$
8(\eta-5\theta)=\frac{7\kappa-60m}{3},\qquad
8\theta=\frac{12m-\kappa}{6},
$$

分别给 $\mu,\nu$，$d$ 由初读恢复。所有等式都是 (71.17) 和偶系数的可逆代数；若从这些取得式返回，便恢复 $m=9\theta+\eta$、$\kappa=12(5\theta+\eta)$ 与 $u\eta=n$。完整原世界仍须且只须 71.4 的严格过滤、原 Q 和 untouched 原 C；不对任意数据无条件断言合法。∎

本证明没有除 $H$、$\lambda$、$\mu$、gain 样本、残式首项、判别式或根重数。所有在原范围允许的系数抵消、观察抵消、样本零和次级方程降次均保留。$\theta>0$ 导出的 $\nu\ne0$ 和 $D_{\rm rec}<0$ 不是额外一般位置假设。

### 71.8. 复用完整达到与该家族的精确记录域

为给推论一个非空实际家族，精确消费第 70 节 70.10—70.13 的达到定理，包括其 ORIGINAL 常数、端点符号、有限差唯一性、严格父守卫和 ALL SAME 行 converse。下面列出所用构造及参数对应，不另作第二次达到发现。

在 $I=[8/5,\phi]$，置 $\epsilon=1-a$，并使用 (71.9) 的同一源比坐标作为形式变量 $X$：

$$
u(X)=2X+c,\quad H(X)=2+2X-2X^2,\quad\delta(X)=X-a,
$$

$$
\mathcal D=H+9\delta,\quad N_\theta=3au+17\delta,\quad
B_8=(2X-3)(2-X),\quad h=13-u,
$$

$$
\alpha=126\epsilon-15X-3B_8,\quad
P_* =\alpha N_\theta+(29a-14)u\mathcal D
-17(14\epsilon+B_8h)\mathcal D.
\tag{71.25}
$$

该节在同一闭区间上证明 $u,\mathcal D>0$，并以

$$
\theta=\frac{N_\theta}{u\mathcal D},\quad\eta=-17/u,\quad
m=9\theta+\eta,\quad F=3\theta-h\eta,\quad
\bar C=14\epsilon(m-1)+15a
$$

定义 $\mathcal R=\bar C-15X\theta-B_8F$，证明精确
$P_*=u\mathcal D\mathcal R$。其端点原式给
$\mathcal R(8/5)>0>\mathcal R(\phi)$，有限差证明严格递减，因而存在唯一 $q_*\in(8/5,\phi)$ 使 $P_*(q_*)=0$。这是原常数的唯一标量构造根，不是 ENTIRE 七行根的唯一性。

此处 $q_*,u,H,\delta,\mathcal D,N_\theta,B_8,h,P_*,\theta,\eta,m,F,\bar C$ 分别就是第 70 节 (70.33)—(70.34) 的相同量；$\mathcal D$ 不同于取得奇系数 $D$，$P_*$ 不同于源矩阵 P。该节完整证明进一步给

$$
\tfrac12<\theta<\tfrac23,\quad H\theta=3a-(q_*-a)m,\quad
p=2,\quad v=m-1,\quad 2a<v<2=p,
$$

$$
n=-17,\quad m_0<m<m_H,\quad s=8>2q_*,\quad
\kappa=12(5\theta+\eta)<50m/7.
\tag{71.26}
$$

对每个任意实 $a_0$、每个 $\tau\ne0$，同一世界为 (71.9)、(71.15) 的 $s=8,q=q_*$。其 BOTH entire identities 在 EVERY 系数成立，包括 ORIGINAL $C-15q_*T$；实际时钟六的 SAME gain 差证明显示的 $\kappa$ 真是取得值。因而这正落在 (71.4)—(71.5) 的实际范围，无需额外接受根、真次数或低响应标签。

此家族可以实际走到七读。其 SAME 六行父含两个完整例外

$$
W_p=(P(a,p),p\tau(t+v)(t-7),a_0+7\tau pv),\qquad W_v:\ p,v\text{ 交换}.
$$

它们来自 (71.4) 的两个不同严格根；$e g=\tau(t+p)(t+v)(t-7)$，$D_0(a)=0$ 给 $o=ae$，而父整式关系
$R=aE+a\tau(U_0-V_o)+(a-1)\Lambda$
恢复另一整式的所有系数。所以二者满足 SAME 六行、不同 $P_{12}=2/p,2/v$，也同时匹配每个较短共享前缀。每个这些 FULL 前缀非单点，早停没有被绕过。两例外均不匹配实际低第七行，仍不限制其他 ordinary 竞争者。

**定理 71.5。** 对这个非空实际家族，

$$
\boxed{\mathbb K_7=\mathbb Q(a,a_0,\tau,q_*)}.
\tag{71.27}
$$

若协议实际到八读，则 $\mathbb K_8=\mathbb K_7$。取 $a_0=0,\tau=1$ 时，精确域是 $\mathbb Q(a,q_*)$。

证明正向逐个取得量核对。在构造中 $u(q_*),\mathcal D(q_*)$ 非零，故 $\theta,\eta,m,F,\bar C,\kappa$ 全是 $\mathbb Q(a,q_*)$ 的有理式。SAME 七行显式为

$$
y_0=a_0,\quad y_1=a_0+\tau[\bar C-a(4m+29)],\quad
y_2=a_0+\tau(-34-6m),
$$

$$
y_3=a_0+\tau[\bar C-a(6m+69)],\quad
y_4=a_0+\tau(-68-4m),\quad y_5=a_0+\tau(\bar C-85a),
$$

$$
y_6=a_0+\tau(-68-4m+2\kappa).
\tag{71.28}
$$

这些是同一 $E=\tau[(-17-5m)t+mt^2]$、
$R=\tau[a(m+3)t^2+a(-32-5m)t+\bar C]$ 在原节点的值，末行用实际 $y_6=y_4+2\tau\kappa$。因此 ALL 七读在 $\mathbb Q(a,a_0,\tau,q_*)$，给 $\mathbb K_7\subseteq\mathbb Q(a,a_0,\tau,q_*)$。

反向 $a$ 已在定义域，$a_0=y_0$ 是取得量；(71.3) 及非零固定 $a$ 给取得的 $\tau\in\mathbb K_7$。推论 71.4 在 $n=-17$ 的实际恒等式给

$$
q_*=-\frac{136}{3\kappa-20m}-\frac c2\in\mathbb K_7,
\qquad 3\kappa-20m<0.
\tag{71.29}
$$

故 $\mathbb Q(a,a_0,\tau,q_*)\subseteq\mathbb K_7$，完成两向。$s=8\in\mathbb Q(a)$，所以 ALL 目标已在该域。若 ENTIRE 七行片单点，合法在 $N=7$ 停；否则实际选末 J，复用完整 J 单射得实际 $N=8$，推论 71.3 给其取得值也在 SAME $\mathbb K_7$。这两个实际分支穷尽，不需要先决定该家族究竟落在哪一支。∎

若确实取得末行，也可在同一世界写成

$$
\omega=g(7)/(8\tau)=17\theta+(u-6)\eta,
$$

$$
y_7=a_0+\tau[\bar C+a(14m-77)+14q_*\theta-2q_*(u-6)\eta].
\tag{71.30}
$$

因为原奇整式在七给 $48q_*T$，实际 JJ 迹少 $2q_*/8$，末归一化项是 $48q_*\theta-2q_*\omega$；且 $R(7)/\tau=\bar C+a(14m-77)$。所以 (71.30) 是 SAME world 的所选实际行，不是另取末 M。七读停止时不将它作为取得量。

$P_*$ 的非零性、代数根存在、有限差唯一性都复用第 70 节证明；未求其不可约次数。即使 $q_*$ 在 $\mathbb Q(a)$ 上有较大次数，(71.29) 仍证明它在实际 $\mathbb K_7$ 中。标量构造根的绝对或底域次数不等于目标对实际取得域的次数；这里后者为一。

### 71.9. 未决下降、原 FULL 恢复与严格边界

普遍实际低层域下降仍为 OPEN。定理 71.2 将它精确化为：在 EVERY 实际完成的本层历史证明 $s\in\mathbb K_N$，或给一个满足完整原式及实际停止规则的历史并证明 $s\notin\mathbb K_N$。七行时必须是 ENTIRE 单点；八行时必须由 ENTIRE 非单点实际选 J，并在 ALL acquired 读数生成的域上判定成员性。唯一合法实根、构造多项式的次数或其某个非线性因子都不足以完成该义务。

本节正面覆盖实际 $s\in\mathbb K_7$，尤其 $s\in\mathbb Q(a)$ 的条件与其非空 $s=8,n=-17$ 家族；没有把所有实际 $s$ 无条件放进记录域。第 70 节的非零次数界、塔式、理论 gcd 和合法线性因子 iff 保持原范围，不在此重复计新或执行；本节没有新的因式分解或不下降反例。

第 69 节定理 69.2 与推论 69.4 的原 FULL 二次精确实数集合论至多八 TOTAL 完整恢复及 EVERY 原初读后 no-$\mathsf L_7$ 保持已证的组合范围。它们不依赖本节取得域下降。三次 EIGHT-TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$ 仍为 OPEN；二次 gain 的整式不提供未知三次或未知 gain-class union 的逆。

本节不补入 $q=0,s=2q,r=0,1,b=0,c_{\rm src}=0$、秩零、极限或无限源、whole 零 gain，也不补入父的 $p=v,p=2a,v=2a,\tau=0$。任意 $a_0$、两种非零 $\tau$ 符号全保留。其他父层合法的低次、$H=0,T=0,s=4$、重根和零层不受本局部排除；在本低层的真正二次、$\theta>0,\eta<0,s>4$ 都来自原式。合法样本零、观察零、系数抵消、次级残式恒零、首项抵消与降次未被新公式额外删除。共同分母、$\eta,s,P_{12}$ 均在使用逆之前证明非零。

取得域成员性、已承诺参数的条件公式、ENTIRE full-model 停止和统一有效译码器是不同结论。本文不提供有效单点、根、guard、因式或源承诺判定，不主张 BSS、有限位、复杂度、资源、噪声、连续逆、稳定性、ML/NN、minimax、尖锐性、第八读必要性或一般 gain 空间逆。精确实表达式没有取得 hidden $s$、未来或反事实响应，也没有增加现场能力。

第 70 节 70.14 与第 69 节 69.9 的完整 simultaneous common-vector 合同保持 INERT、UNEXECUTED、UNFULFILLED：ALL 槽、ALL 原前缀和后代、SAME common whole gain blocks、严格源、固定漂移、BOTH actions duties 与 ALL stopguards 均不因局部有理重建而结算。未访问其原始或链接目标，未生成、归约、枚举、求解、测试或认证该关系；本节不声称其编码与递归失败谓词等价。

全部证明是未执行符号数学；没有公式求值或代入程序、数值、导数、递推、数学枚举、CAS、gcd/因式分解、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean/D5/Blueprint/Reg、摄入或消化。字节、UTF-8、LF、哈希和 strict JSON 检查只验证文本完整性，不验证数学。

## 追加锚（本行以下为增补区）
