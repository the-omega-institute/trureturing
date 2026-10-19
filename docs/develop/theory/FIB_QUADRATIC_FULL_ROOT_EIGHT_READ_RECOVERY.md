# FIB 原 FULL 二次世界的八次 TOTAL 根恢复与原根 L7 排除

本文独立为第 69 节。在下述精确实数、取得记录的集合论模型中，对 EVERY 原严格正、迹一、秩一源，ONE entire 非零实次数至多二增益及 ONE individually fixed 任意实漂移，存在一个确定性自适应策略，至多八次 TOTAL 观察充要恢复整个 $P,g,d$。其初读后的 EVERY 原完整根集合均不满足 $\mathsf L_7$。

新增内容是原根接口的完整组合：第 49 节实际标志穷尽把第 68 节 EVERY 实际 Balpha 选择器接到原完整父，解除条件根桥梁的 H；再与第 44 节 universal 未标志 M 解及第 47 节 EVERY B0 解组成一条策略。原世界、全部系数、时钟、FULL 子片、因果性、逆和计数的对应在本文给出。局部选择器本身不重复计为新定理；原根结论由这些接口及本节组合证明承担。

全部数学是 repo-derived、fallible UNEXECUTED 符号证明，不是 Lean/kernel 或计算认证。这里的“恢复”严格指本节定义的集合论策略与唯一完整原像。原 FULL 三次问题仍为 OPEN。

## 69. 原世界到完整局部选择器的因果组合

### 69.1. 原模型、SAME 历史与完整目标

固定世界域 $\mathcal W_2$ 的每个元素为

$$
W=(P,g,d),\qquad P=\begin{pmatrix}r&b\\c_{\rm src}&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c_{\rm src}>0,\quad bc_{\rm src}=r(1-r),
$$

$$
g(t)=\lambda+\mu t+\nu t^2\in\mathbb R[t]\setminus\{0\},\qquad d\in\mathbb R.
\tag{69.1}
$$

四元严格正、迹一、行列式零；迹一排除秩零，故秩恰一。每个世界从开始至结束固定 SAME $P$、SAME entire $g$、SAME 一个 $d$。不同候选可有不同漂移。目标相等恰为全部四源元、全部三个增益系数和漂移相等。

$\mathcal W_2$ 含非零常数、非恒定仿射、真正二次，任一尺度符号，合法系数零、截距零、读数零、采样或非采样根、重 gain 根及末增益零。两对角侧、$r=1/2$、对称与非对称、$b=1/2$ 及无上界正非对角元保留。整个零 gain 与非严格或极限源不在原域。

原动作及读数为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad y_i=d+\operatorname{tr}(Q_iP)g(i).
\tag{69.2}
$$

只取得所选动作的一个即时响应。初读是原时钟零，计入 TOTAL；没有重置、复制、跳钟、空动作、额外端口或行间重拟合。

对取得动作响应历史 $H_i=(y_0,E_1,y_1,\ldots,E_i,y_i)$，定义

$$
\mathcal C(H_i)=\{W\in\mathcal W_2:\text{式 (69.2) 的 ALL SAME 已取得原行成立}\}.
\tag{69.3}
$$

它包含 ALL 原兼容世界，只按完整目标去重。对下一动作 E 定义同一历史上的预测和 FULL 子片

$$
h_{H_i,E}(W)=d+\operatorname{tr}(EQ_iP)g(i+1),\qquad
\mathcal C(H_i;E,z)=\{W\in\mathcal C(H_i):h_{H_i,E}(W)=z\}.
\tag{69.4}
$$

可达响应恰使此片非空。空记录为不一致记录，不能算恢复；非空单点可立即输出其唯一完整世界。集合可有任意基数。

### 69.2. 实际左乘积与同一原时钟

对形式矩阵 A，相加 AP 的对角元得

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r+A_{21}b+A_{12}c_{\rm src}.
\tag{69.5}
$$

左下元乘 b。左 J 交换旧两行，左 M 取旧第二行与旧两行之和；这两条符号行恒等式从 I 依序给下表。置 $j=b+c_{\rm src}$。

| 原时钟及动作 | SAME 实际左乘积 | 实际迹 |
| --- | --- | --- |
| $0$ | $\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)$ | $1$ |
| $1,J$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $j$ |
| $2,M$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $1+b$ |
| $3,J$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $j+r$ |
| $4,M$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $1+2b$ |
| $5,J$ | $\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$ | $j+2r$ |
| $6,J$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $1+2b$ |
| $6,M$ | $\left(\begin{smallmatrix}1&0\\3&1\end{smallmatrix}\right)$ | $1+3b$ |
| $7,JJ$ | $\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$ | $j+2r$ |
| $7,JM$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $j+r+1+2b$ |
| $7,MJ$ | $\left(\begin{smallmatrix}3&1\\1&0\end{smallmatrix}\right)$ | $j+3r$ |
| $7,MM$ | $\left(\begin{smallmatrix}3&1\\4&1\end{smallmatrix}\right)$ | $1+2r+4b+c_{\rm src}$ |

每个实际响应是 d 加该迹乘 SAME $g(i)$。JJ 等后缀的首字母是原时钟六选择，末字母是原时钟七选择。重复乘积仍用新原时钟样本。前五动作 $JMJMJ$ 加初读服务零至五，共六 TOTAL；再至多两个动作服务六、七。

### 69.3. 完整源双射、BOTH 整式与 EVERY 原系数

令六行父 $F=\mathcal C(H_5)$ 来自此实际前缀。取得 $a_0=y_0,x_i=y_i-a_0$，定义

$$
E(t)=Lt+At^2,\qquad R(t)=Dt^2+Bt+C,
$$

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
\tag{69.6}
$$

这些式恢复偶节点零、二、四和奇节点一、三、五。两个次数至多二插值之差有三个不同根即恒零，故唯一。C 始终是 ORIGINAL 奇常数。

整个严格源域与下述开域双射：

$$
q=r/b>0,\quad s=2/b>2q,\qquad
P(q,s)=\begin{pmatrix}2q/s&2/s\\q(1-2q/s)&1-2q/s\end{pmatrix},\quad
j=q+\frac{2(1-q^2)}s.
\tag{69.7}
$$

正向 $s-2q=2(1-r)/b>0$，秩一给 $c_{\rm src}=r(1-r)/b$，强制逆式。反向 $q>0,s>2q$ 给四元正、迹一、$bc_{\rm src}=r(1-r)$，并返回原 q、s。故没有丢失源对称、$s=4$ 或 $s=4q$。

置

$$
D_0=2-q-2q^2,\quad H_q=D_0+3q,\quad e(t)=1+t/s,\quad o(t)=qe(t)+D_0/s,
$$

$$
T=\nu/s,\quad U=t(t-2)(t-4)=t^3-6t^2+8t,\quad
V_o=(t-1)(t-3)(t-5)=t^3-9t^2+23t-15.
$$

e、o 在相应原偶、奇父节点就是实际迹。六原行当且仅当严格源、whole $g\ne0$、$d=a_0-\lambda$ 和 BOTH entire 恒等式

$$
-\lambda+eg=E+TU,\qquad -\lambda+og=R+qTV_o.
\tag{69.8}
$$

必要性：初读固定漂移；偶差至多三次、三次系数 T、有根零、二、四，减 TU 后至多二次且仍有这三个不同根，故恒零。奇差同理减 $qTV_o$，用根一、三、五。充分性是在全部原节点取值，零样本也恢复。

EVERY 偶升幂系数为

$$
(0,\mu+\lambda/s,\nu+\mu/s,\nu/s)=(0,L+8T,A-6T,T).
$$

逐项可逆得到完整增益与同一个漂移：

$$
\nu=sT,\quad \mu=sA-sT(s+6),\quad
F_{\rm orig}=L-sA+T(s+2)(s+4),\quad
\lambda=sF_{\rm orig},\quad d=a_0-sF_{\rm orig}.
\tag{69.9}
$$

EVERY 奇左升幂系数为

$$
\big((q-1+D_0/s)\lambda,\ q(\mu+\lambda/s)+(D_0/s)\mu,
q(\nu+\mu/s)+(D_0/s)\nu,\ q\nu/s\big),
$$

右侧为 $(C-15qT,B+23qT,D-9qT,qT)$。二次、一次、常数比较分别是

$$
D-qA=H_qT,
$$

$$
B-qL+15qT=D_0[A-T(s+6)],
$$

$$
C-15qT=[(q-1)s+D_0]F_{\rm orig}.
\tag{69.10}
$$

奇二次原比较为 $D-9qT=q(A-6T)+D_0T$；奇一次为 $B+23qT=q(L+8T)+D_0[A-T(s+6)]$；奇常数保持 ORIGINAL $C-15qT$；三次已相同。反向 (69.9)—(69.10) 恢复 EVERY 系数和 BOTH 整式。因此 ALL $q>0,s>2q,T\in\mathbb R$，经 (69.7)、(69.9) 重建并保留 whole $g\ne0$ 及全部 (69.10)，恰为整个父 F，且 q、s、T 唯一对应整个世界。

上述证明没有除 $H_q,T,D_0$ 或任何 gain 样本。常数、仿射、H 零、系数零、采样根和重根均保留，直到原式或被调用的精确分类排除。

两个原时钟六行及 J 后两个原末函数在该同一图谱上为

$$
h_M=a_0+E(6)+48T,
$$

$$
h_J-a_0=4L+(2s+24)A+2(16-s^2)T,
\qquad k:=\frac{z-a_0-E(4)}2=(s+4)[A-(s-4)T],
\tag{69.11}
$$

$$
\Omega=F_{\rm orig}+7A+7(1-s)T=g(7)/s,
$$

$$
f_{JJ}=a_0+R(7)+X_T,\quad f_{JM}=a_0+R(7)+Y_T,
$$

$$
X_T=48qT-2q\Omega,\quad Y_T=48qT+(s+4-4q)\Omega.
\tag{69.12}
$$

证明 M 行用 e(6) 与 U(6)；J 迹比 e(6) 少 $2/s$，偶重建给第二式。奇式在七给 $-\lambda+o(7)g(7)=R(7)+48qT$；实际 JJ 迹少 $2q/s$，JM 比 JJ 多 $(s+4-2q)/s$，给 (69.12)。它们是符号恒等式，不是另行取得响应。不除 $s-4$、$\Omega$ 或末 gain。

因而把 (69.11) 的所选新行附加到 ALL 父图谱，恰得相应 FULL 七行子片。再附加所选实际末方程，恰得 FULL 八行纤维；每个接受点始终是同一个完整原世界。这给后面所有局部表回到原模型的必要充分桥梁。

### 69.4. 完整父标志与三个精确接口

置 $a=(\sqrt{17}-1)/4$，$2a^2+a=2,3/4<a<4/5$。定义父记录谓词

$$
\mathsf B_0:\quad A\ne0,\quad D=A/2,\quad B=L/2+A,
$$

并且

$$
p_0(s)=-(A/2)s^2+(A+L/2)s+C-L
\tag{69.13}
$$

有两个不同严格根 $s>1$。

另置

$$
\Sigma:\ B+5D=a(L+5A),\quad \tau=(D-aA)/(3a).
$$

只在 $\Sigma,\tau\ne0$ 下定义

$$
\Lambda=(C-15a\tau)/(a-1),\quad d_*=a_0-\Lambda,\quad K=\Lambda+E+\tau U.
\tag{69.14}
$$

完整例外组 $\mathcal A_\tau$ 为 K 的 ALL 不同严格根 $-s<-2a$ 给出的原世界

$$
P=P(a,s),\qquad g=sK/(t+s),\qquad d=d_*.
$$

因子整除给 whole gain，(69.8)—(69.10) 恢复所有原行。普通组定义为

$$
\mathcal O_\tau=\{W\in F:q(W)\ne a,\ T(W)=\tau\},
\tag{69.15}
$$

其中 F 是 ALL 原六行父；等价地使用全部严格源、whole gain 非零、(69.9)—(69.10) 的完整过滤，不接受单独消元根。

$\mathsf B_\alpha$ 要求 $\Sigma,\tau\ne0,|\mathcal A_\tau|\ge2$，且 K(7)=0，或 K(7) 非零并有 $U_\alpha\in\mathcal A_\tau,V\in\mathcal O_\tau$ 满足 SAME 原 $f_{MM}(U_\alpha)=f_{MM}(V)$。这是完整 actual 标志；T=τ 是父确定的候选 M 响应层，并未取得未来 M 响应。所有组和预测都由取得六行定义。

两个标志互斥。B0 的两严格根给 $l=L/A=s_1+s_2-2>0$，而

$$
\frac{B+5D-a(L+5A)}A=(1/2-a)l+7/2-5a<0.
\tag{69.16}
$$

两项因 $a>3/4$ 严格负，A 两种符号均不能令分子为零，所以 B0 排除 Σ。故 B0、Balpha、两者均假是互斥且 Boolean 完备的三个父记录分支。

以下精确复用完整先前定理，均是数学陈述的模块化应用，不以状态、审查意见或票数作前提。

**未标志接口：第 44 节《FIB 二次第六 M 臂、两步策略与整个父恢复》定理 44.6。** 它的完整父为 (69.1)—(69.3) 在 SAME JMJMJ 的 F；其引理 44.1 与 (69.8)—(69.10) 同式。对 EVERY 可达且两个标志均假的父，在响应前选六 M；对 EVERY 实际响应 z，由该行取得 $T=(z-a_0-E(6))/48$，整个子片单点停，否则选择

$$
M\ (T=0),\qquad J\ (T\ne0,\ m_\alpha\le1),\qquad M\ (T\ne0,\ m_\alpha\ge2),
\tag{69.17}
$$

其中 $m_\alpha$ 是此 FULL 子片完整例外组大小。所选末函数在 ENTIRE 子片单射并有原完整逆。

其 universal 范围由完整分类承担：非零 T 的比例二次式使普通每比至多一，唯一例外 q=a 保留全部严格因子；MJ 分开不同 q，MM 的例外内差与 ALL 实际普通交叉比较恰给 Balpha。零 T 穷尽非零常数与仿射；常数的 MM 逆覆盖两种带符号无限半线，仿射的两严格根末差恰把坏型限定为 B0，降次一次式和重根独立保留。因此 44.6 覆盖所有父、所有可达 M 响应和任意基数的合法子片；它不依赖其指定有理例或互反例的性质。

**B0 接口：第 47 节《FIB 二次 B0 全子片的严格响应序与八次 TOTAL 因果恢复》定理 47.9。** 它的 B0 就是 (69.13)。$l=L/A,k_0=l-1-2C/A$ 使 $l>0,0<k_0<l^2/4$，并以 SAME acquired $A\ne0$ 双射归一化 entire 原域：

$$
g=A G,\qquad d=a_0-A\lambda_G.
\tag{69.18}
$$

该 prior 的 E、R、T 分别是本节 $E/A,R/A,T/A$；q、s 不变。任意 A 符号保持响应相等与单射，逆时 ALL gain 系数乘 SAME A。其完整父表含恰两仿射及 ALL 接受二次；其实际六 J 行用

$$
w=\frac{(z-a_0)/A-4l-24}{2}
$$

并保留 BOTH 原系数过滤，恰等于本节 FULL J child。定理 47.5 的严格响应序给每片至多一个二次与一个仿射；47.7 的混合双末碰撞排除，结合整个片至多二，才给整个片至少一个末函数单射。因此 EVERY B0 父、EVERY 实际 J 响应单点停，否则两个成员 JJ 预测不同选 J，相同选 M，完整恢复全部 $P,g,d$。不是只服务那两个仿射世界；跨次数竞争者由完整表同时保留。

**实际标志穷尽：第 49 节《FIB 二次例外标志的完全穷尽与恰二世界坏 M 全子片》定义 49.3、定理 49.8。** 其模型、父、T、实际 MM、Σ、τ、Λ、K 与 (69.1)—(69.15) 逐项相同。它的实际 flag 恰为 ALL

$$
K=\tau(t+p)(t+v)(t-7),\quad p,v>2a,\quad p\ne v,\quad \tau\ne0,\quad a_0\in\mathbb R.
\tag{69.19}
$$

必要性先由全部严格根和 actual 普通过滤得 β>6；β 非七时 actual cross-MM 迫 β<7，但保留 ORIGINAL 常数的完整证明排除 $6<\beta\le7$ 中所有普通 T=τ 世界，故无此分支。充分性由 EVERY 参数的两个固定例外

$$
W_p=(P(a,p),\ p\tau(t+v)(t-7),\ a_0+7\tau pv),\qquad W_v:\ p,v\text{ 交换}
\tag{69.20}
$$

实现同一原六行并设置 flag。该定理是 actual iff 和全参数达到，不是根因子必要性或选定例子的推广。其 49.9 给指定坏 M FULL 片恰为这对；不把整个父或 J child 缩为这对。第 49 节另引的 Section-48 接口不作为本文另一个前提；这里仅用其直接证明的实际 iff、原系数与坏 M 等号。

### 69.5. 从实际 flag 到 Section 68：H 已解除

条件根桥梁所需 H 精确定义如下：EVERY 原实际 Balpha 六行父 F、EVERY 原时钟六可达 J 响应 z 的 ENTIRE

$$
C_z=\{W\in F:d+(1+2b)g(6)=z\}
\tag{69.21}
$$

单点可停；否则至少一个由该取得父及 z 决定的原末 J/M 函数在 ENTIRE $C_z$ 单射，且用仅该所选实际响应有全部原方程的充要完整逆。

**引理 69.1（原 H 的全范围消去）。** H 在本节模型中由第 68 节《FIB 二次全部实际 Balpha 父的完整选择器与局部 L2 排除》定理 68.3、推论 68.4 得到，不再是待验前提。

证明。任取实际 Balpha 父。由第 49 节 49.8，取得 K、τ 必且恰有 (69.19) 的两个不同严格负根；取 p<v 仅是命名。令

$$
Z=p+v,\quad V=pv,\quad m=Z-1,\quad n=V-2Z-13,\quad N=L+5A.
$$

其 SAME acquired 系数逐项是

$$
A=\tau m,\quad L=\tau(n-5m),\quad D=a\tau(m+3),
$$

$$
B=a\tau(n-5m-15),\quad C=\tau[7(1-a)V+15a],\quad N=\tau n.
\tag{69.22}
$$

这是 K 的升幂系数与 $\Sigma,\tau,\Lambda$ 的定义比较，保留原 C；没有重新选定记录。第 68 节 $r_0,c_{\rm src}$ 对应本节 $r,c_{\rm src}$；其 $a,U_0,V_o,D_0,H,T,q,s$ 对应本节相同量，$U_0=U,H=H_q$。其 entire gain 类就是 (69.1)，其 $d=a_0-\lambda$ 是 SAME individually fixed 漂移，未规范为统一物理漂移。

第 68 节父谓词 (68.1) 即 (69.19)，其 m、n 是上述量；其

$$
\Gamma=\frac{N-2D-(2a+1)A}{\tau}=n-(4a+1)m-6a
\tag{69.23}
$$

没有新增假设。任意 N、n、Γ 包括零及两侧均在 68.3 的范围。特别不把旧的 $N/u$ 混作 n，也不把仿射轨迹的常数混作 Γ。

对任一可达 SAME z，其统一完整候选式 (68.38) 就是本节 (69.7)、(69.9)、ALL (69.10)、whole gain 非零和 (69.11) 的 SAME k。它不除 $n,\Gamma,H_q,T,s-4$。由 69.3 的双向证明，它与 (69.21) 逐世界相等；不是选择一组支持、已知次数或例外存在的子域。其 $\kappa=(z-a_0-E(4))/(2\tau)=k/\tau$，无需对负 τ 搬动不等式。其 $\Omega,X_T,Y_T$ 和实际 JJ/JM 就是 (69.12)，共用相同偏移 $a_0+R(7)$、原时钟七和实际左乘积。

68.3 在此 ENTIRE 子片上给单点停止或一个所选末函数单射及充要完整逆；68.4 与实际 iff 已把它量化到 EVERY actual Balpha 父。其范围同时含 ordinary-only、所有跨源/跨次数/例外—普通比较、H 零、T 零、s=4 及每个原式允许的零/重根层；无 n、Γ 或基数附加守卫。该 exact delivered 定理的内部子家族为其证明模块，不再扩读其引用链或重复其内部表。

因此上述所有原父假设和 child、action、clock、parameter、domain、target 身份逐一满足，逐父逐 z 应用即得 H。任意 $a_0$ 和任一非零 τ 符号均保留，H 在组合中已被证明消去。∎

为使选择成为单一函数，可对非空 $C_z$ 规定：单点停，否则若 $f_{JJ}$ 在 ENTIRE $C_z$ 单射则选 J，若不单射则选 M。H 保证后一函数在 ENTIRE $C_z$ 单射。这不要求 source68 在各层使用同一种末动作，也不把两个坐标合起来点分离冒充一个坐标单射。存在一个成功末动作足以保证这个 J-first 规范选择。

### 69.6. 一条确定性取得记录策略

定义策略 $\pi$。在 EVERY 已取得历史先形成原 FULL $\mathcal C(H)$：空集返回“不一致记录”且不作恢复断言，非空单点停止并输出其唯一完整世界，其余继续。

从原初读后到原时钟五，继续分支依次取自己的前五动作 $JMJMJ$。原时钟五之后只用取得六行构成 (69.6) 和完整两个父标志。原时钟六规定

$$
E_6=\begin{cases}
J,&\mathsf B_0,\\
J,&\mathsf B_\alpha,\\
M,&\neg\mathsf B_0\land\neg\mathsf B_\alpha.
\end{cases}
\tag{69.24}
$$

标志互斥且与未标志情形穷尽全部父。取得唯一实际响应 $z_6$，在其 ENTIRE child 再用相同空/单点守卫；否则原时钟七规定：

| SAME acquired 分支 | 末动作 |
| --- | --- |
| B0 后 J child | 两成员 JJ 预测不等选 J，相等选 M |
| Balpha 后 J child | JJ 在 ENTIRE child 单射选 J，否则选 M |
| 未标志后 M child | 由 NOW acquired M 行求 T，按 (69.17) 选择 |

取得这个所选动作唯一实际 $y_7$，返回其 FULL 非空响应纤维的唯一世界。偏离此前缀的历史可固定取 J 来补全动作映射；原合法执行不会进入未定义恢复分支。策略不需要为未到达历史承诺八次恢复。

**因果性证明。** 插值、Σ、τ、K、严格根集合、完整 ordinary 过滤、两标志都是六行记录的集合论函数；候选的反事实预测是这些记录所定义世界的函数，不是未选动作的实际观察。第六动作不使用将来的 M 响应、未知真 T、源或次数标签。第七选择仅用 SAME 已取得六/七行及其 ENTIRE 子片。B0 的归一化用 acquired A；Balpha 的 J-first 单射谓词由 acquired 子片决定；未标志 T 仅在实际选 M 并取得响应后使用。因此所有共享同一取得历史的原世界得到 SAME 动作和停止决定。没有隐藏 true-member、gain 根、次数或源输入，也未取得未选响应。

每个继续历史只按这些互斥规则选一个动作，J-first 消除了任意选择。非空单点有唯一输出，终端纤维也有唯一输出；故这是一条确定性取得记录的集合论策略。

### 69.7. 原 FULL 八次 TOTAL 充要恢复

**定理 69.2。** 对 EVERY $W\in\mathcal W_2$，策略 $\pi$ 在其实际原初读后至多七个进一步动作、即至多八次 TOTAL 观察内输出精确完整 W。停止时 W 是 ALL SAME 已取得原行的唯一原世界；必要与充分两向均成立。

证明实际世界存在。初读时 $W\in\mathcal C(H_0)$。每次所选动作的实际响应按 (69.2) 来自此同一个 W，故 W 留在 FULL child。实际执行从不会空。任一单点守卫触发即正确返回 W。否则继续至其自己的 JMJMJ 六行父，仍非空。

在该父，69.4 的三个 Boolean 分支穷尽。B0 分支由 47.9 给 EVERY 实际 J child 的完整成功；Balpha 分支由引理 69.1 给 EVERY 实际 J child 的完整成功；未标志分支由 44.6 给 EVERY 实际 M child 的完整成功。三者都在父记录决定第六动作之后，对实际响应全称量化。若七行片尚非单点，69.6 选定函数在 ENTIRE 片单射。W 的所选实际末值给非空原像，故最终 FULL 纤维存在。

证明唯一与全部原竞争者。设 $W'\in\mathcal W_2$ 满足 SAME 最终取得原行。则在每个较短取得前缀也兼容；因确定性及前缀记录相同，它得到相同停止判断和动作，不能进入另一个父标志分支。在八读终止情形，W' 属于 SAME 六行父、SAME 第六所选动作的 ENTIRE 七行 child，并满足 SAME 所选末响应。

B0 完整归一化和父/child iff 收进全部跨次数 W'；未标志完整 M 分类收进全部 ordinary、exception、零 T 和无限常数层 W'；Balpha 完整候选与 (69.21) 的逐世界等号收进全部 W'。各分支所选函数的 ENTIRE 单射迫 $W'=W$。早期单点停止的唯一性直接由 (69.3) 给出。未删除任何源投影外、偏好支持外或未知次数的原竞争者。

证明反向充分及完整 inverse。对任一所接受的非空响应纤维成员，必须保留 $q>0,s>2q$、whole gain 非零和 ALL 原残式。由 (69.7) 得 EVERY 源元，由 (69.9) 得 EVERY gain 系数及 SAME 一个 d。全部偶系数和原奇 $C-15qT$ 等所有奇系数反向恢复 BOTH (69.8)，所以同时恢复 SAME 六原行；不是只恢复消元投影。

在未标志 M 分支，取得 T 的 (69.11) 恰恢复 SAME 原时钟六 M 行；在 B0、Balpha 的 J 分支，(69.11) 的 k 方程恰恢复 SAME 原时钟六 J 行。B0 使用 normalized prior 逆时，所有三个 gain 系数统一乘 acquired A，漂移统一恢复为 $a_0-A\lambda_G$，从而回到相同原单位和时钟。最后加入的过滤就是所选一个实际原末响应方程；J 分支用 (69.12)，M 分支用 69.2 的实际 MJ/MM 迹。因此每个返回世界用 ONE strict P、ONE entire nonzero g、ONE fixed d 同时满足 ALL SAME 已取得原行。反向任何满足全部原行的世界由 69.3 及各 child iff 进入此表，并满足该末过滤；上述单射迫其为唯一返回世界。

这也允许直接把逆定义为 FULL 原方程纤维中的唯一元素：存在、唯一和原域成员资格已分别证明。若只在早期单点停止，(69.3) 本身给全部已取得原行的必要充分逆。空表或实际末等式无解不接受为成功。

证明计数。零至五为六 TOTAL；原时钟六是第七次；原时钟七至多再取一次，是第八次。非空单点可在每一阶段提前停，包括七次停；没有八次“额外动作”、第九读或反事实读。计数与上面 FULL 充要逆共同证明断言。∎

该正策略可选择自己的前缀。无需证明任意其他策略被迫进入 JMJMJ，也无需逐一完成自己未走过的较早另一臂。固定词的晚期坏 J 与其父较早的 M 修复相容；Balpha 指定坏 M FULL pair 与其父成功 J 解相容。

具体地，第 49 节 49.9 仍在精确范围内给

$$
\mathcal C(H_5;M,a_0+E(6)+48\tau)=\{W_p,W_v\},
$$

两个时钟七末 gain 均零，两个末响应均为 $d_*$，各 FULL 末片仍是同一对。它们的实际六 J 响应之差 $2\tau(v-p)\ne0$，故这对属于不同 J child。该坏 M 事实不声称同一个 J child 坏，不能反驳 (69.24)。第 44 节所述固定词晚期障碍也只约束它自己的已服务历史及实际选择，没有对所有自适应策略量化。

### 69.8. 任意基数的有限 h 引理与 EVERY 原根 no-L7

在 SAME 实际历史 H 与其非空 FULL 集合 K 上，递归定义

$$
\mathsf L_0(H,K)\iff\exists W\ne W'\in K,
$$

$$
\mathsf L_{h+1}(H,K)\iff\mathsf L_0(H,K)\ \land\
\forall E\in\{J,M\}\ \exists z\in h_{H,E}(K):
\mathsf L_h\bigl(H\mathbin{\frown}(E,z),\{W\in K:h_{H,E}(W)=z\}\bigr).
\tag{69.25}
$$

每个 z 必实际可达，每个子片必须 FULL；父非单点守卫和 EACH 两可用动作 duty 均在。原产品和下一时钟随 SAME 历史，不另编号。写 $\mathsf L_h(K)$ 时仍保留这些历史参数。

**引理 69.3。** 对 EVERY 有限 h、任意基数非空 SAME full K，若存在一个取得记录确定性策略，对 K 的 EVERY 世界保证至多 h 个进一步实际动作恢复完整目标，则 $\neg\mathsf L_h(H,K)$。

证明用有限 h 归纳。h=0 时所有世界共享同一已取得历史，策略没有新动作而输出同一个完整目标。保证对 EVERY 世界正确，迫 K 单点，所以 $\mathsf L_0$ 假。

假设结论对 h 成立，取保证至多 h+1 动作的策略。若此历史立即停，保证正确仍迫 K 单点，$\mathsf L_{h+1}$ 的父守卫假。否则策略在 SAME 记录选择一个动作 $E_*$。对 EVERY 可达 $z\in h_{H,E_*}(K)$，其 continuation 必须对 ENTIRE FULL 子片全部成员保证至多 h 动作成功：每个成员本来就在 K 且产生 SAME 第一步响应，故原保证逐成员保留。归纳假设在每个这样的非空 child 给 no-$\mathsf L_h$，包括单点 child；空片不作可达见证。

于是存在这个 $E_*$，它没有任何可达 z 使 FULL child 满足 $\mathsf L_h$。这恰否定 (69.25) 所需的 EVERY action / EXISTS attainable response 条件，得到 no-$\mathsf L_{h+1}$。没有交换量词、假定有限基数或删去任一停止守卫。∎

**推论 69.4（EVERY 原初读的 FULL L7 排除）。** 对每个实际原初读 $a_0$，令

$$
K_0(a_0)=\{W\in\mathcal W_2:d+g(0)=a_0\}.
\tag{69.26}
$$

则 $\neg\mathsf L_7(H_0,K_0(a_0))$。

证明。它是原初读后的 ALL 原世界，不对 P、gain 次数或根另加承诺；$d=a_0-\lambda$ 仅是原初读的漂移平移双射。任意实 a0 均可由固定合法 P、一个非零常数 gain 和相应固定 d 达到。定理 69.2 给 SAME K0 上一条策略保证至多七个进一步动作，故引理取 h=7 即得。初读计入八 TOTAL 但不计入这七个进一步动作。∎

这是正策略蕴含该精确定义递归失败谓词的逻辑排除，不声称其逆命题、另一个未核对编码的证书或共同向量计算。原 FULL 二次根的此集合论恢复与 no-L7 已由上述组合结算，不再留 H 为假设。

### 69.9. 精确策略语义、严格范围与完整 INERT 规格

策略的定义域是精确取得实记录。FULL 原方程集合、单点谓词、完整父标志、根集合和 ENTIRE 单射谓词是集合论定义；确定动作及唯一输出是上面所证明的含义。没有由此证明有效实根枚举、单点或单射判定可决定、可计算性、BSS 实现、有限精度、连续性、稳定性、噪声鲁棒性、效率、复杂度或资源界。

只有当 $n_{\rm det}(2,0)$ 的策略类恰允许这些集合论记录映射且总计数包含初读时，才可将定理记为 $n_{\rm det}(2,0)\le8$。若另指更强机器实数语义，仍缺明确计算模型及上述停止、标志、全片选择和逆在 EVERY 原记录上的可实现性证明；观察数本身不提供该桥梁。

原域全程严格。$q=0,s=2q,r=0,1,b=0,c_{\rm src}=0$、无限或极限源、whole 零 gain 不加入。Balpha 父的 $p=2a,p=v,\tau=0$ 不属于其严格标志，但其他父的合法重 gain 根和低次世界全保留。父分类不把其局部原式排除变为原根额外假设。插值只除固定非零整数，源逆只除正 b、s；B0 normalization 先 A 非零；Balpha normalization 先 τ 非零，且任一符号允许；其余奇异和零层依精确 prior 的独立分类。原根桥梁没有取消 $H_q,T,D_0,s-4,g(6),g(7)$、漂移差、源差、判别式或未知首项。

原 FULL 三次的 EIGHT-TOTAL 恢复 versus $n_{\rm det}(3,0)\ge9$ 仍为 OPEN。三次 gain 乘线性迹可四次；四个偶节点一致仍可保留非零倍 $t(t-2)(t-4)(t-6)$，本二次恒等式没有消去它。未知三次或未知 gain-class union 不在定理 69.2 中。

不主张第八次必要、尖锐最小值、minimax 等式、九读上界、gain 跨度、最小支持、非单点低层存在、有限界达到、非终端抽对、一般 gain 空间逆、ML/NN、物理、数值或 kernel 结果，也不主张文献穷尽、外部原创性或优先权。新意限于本库结果间已写明的完整原根组合。

以下保留 COMPLETE INERT、UNEXECUTED、UNFULFILLED 共同合同，原 scope 不变。全部 $256$ 终叶槽 $\sigma=(w,e)$，$w\in\{J,M\}^7,e\in\{0,1\}$；全部 $254$ 非空实际前缀 v、原长度 $i=1,\ldots,7$、即时左乘积 $A_v$ 及 EVERY 后代。记

$$
t_v(P)=\operatorname{tr}(A_vP),\quad
\ell_v(P)=(t_v(P)-1,it_v(P),i^2t_v(P),i^3t_v(P)).
$$

EACH 前缀的 EVERY 非代表后代 σ 与 SAME-prefix 代表 ρ 保留 WHOLE 行

$$
\ell_v(P_\sigma)x_\sigma-\ell_v(P_\rho)x_\rho=0.
$$

ALL 行组成 SAME 完整 $1538\times1024$ 比较关系，继承层数 $254,252,248,240,224,192,128$，给定表达 $2^i(2^{8-i}-1)=256-2^i$。ONE SAME common stacked vector 含 ALL 256 whole 四系数 gain 块，每块非零。每槽固定 ONE strict $P_\sigma$、ONE whole

$$
g_\sigma(t)=\sum_{j=0}^3x_{\sigma,j}t^j,\qquad d_\sigma=a_0-x_{\sigma,0},
$$

跨 ALL SAME 原行不变。每个 terminal e pair 必须有不同完整目标；适用 SAME-source pair 保留 WHOLE 四分量差 $x_{(w,0)}-x_{(w,1)}\ne0$。ALL 严格源、ALL 祖先方程、BOTH 动作 duties、ALL 父/子/末非单点 stopguards 必须在 SAME 向量与 SAME entire worlds 同时成立。只合并整个 P,g,d 相等槽。二次限制 $x_{\sigma,3}=0$ 同时施于 ALL SAME blocks。

局部对、条件端点支持、单变量图谱、源投影、较小关系、分别可行路径或臂、选定支持、逐行 gain/drift refit、独立守卫向量均不能替代共同实现。此合同保持未履行规格：没有访问、生成、枚举、求解、测试、归约或给出其机械可行/不可行证书。若某一关系被另证恰编码 (69.25)，推论 69.4 的逻辑排除适用于那个已证对应；本文没有核对该机械编码，更没有把继承尺寸或文字当作编码正确性证明。

全部证明是未执行符号数学。没有执行公式求值或代入程序、数值、导数、递推、数学枚举、CAS、矩阵/秩/核/区间/证书计算、实验、数学测试、构建、renderer、probe、Lean、D5、Blueprint、Reg、摄入或消化。文本字节、UTF-8、LF、哈希和 strict JSON 仅验证工件完整性，不验证数学。

## 追加锚（本行以下为增补区）
