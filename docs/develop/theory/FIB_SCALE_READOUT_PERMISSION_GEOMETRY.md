# FIB 尺度读出与逆许可几何

## 1. 有限预算的尺度读出与逆许可分离

**定义 1.1（共同来源、组成预算与末端响应）。** 令 $\mathcal T$ 为非空有限有序二叉树的集合，每个内节点恰有左右两个子树，每片叶标记为 $\alpha$ 或 $\beta$。组成计数 $c(T)=(a,b)^{\mathsf T}$ 的两个坐标分别是 $\alpha$ 叶数与 $\beta$ 叶数。全局替换 $\rho$ 在每片叶上按 $\alpha\mapsto\beta$、$\beta\mapsto\langle\beta,\alpha\rangle$ 作用，并以 $\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle$ 保持有序二叉括号；对应规则见[延拓卷 §1](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#1-原始层关系先于数量解释)。叶地址是从根出发的有限左右词，左边记 $0$、右边记 $1$；地址、标签与括号属于来源，而本节恢复目标只取组成 $c(T)$。对整数 $H\ge1$，定义初始来源域及其任务商

$$
\mathcal T_H=\{T\in\mathcal T:|\operatorname{Leaves}(T)|\le H\},\qquad
D_H=c(\mathcal T_H)
=\{(a,b)\in\mathbb N_0^2:1\le a+b\le H\}.
\tag{1.1}
$$

每个 $(a,b)\in D_H$ 都可实现：把 $a$ 个 $\alpha$ 和 $b$ 个 $\beta$ 排成叶序列，再任选完整二叉括号。不同叶序与括号可以有同一组成。按总叶数 $s=1,\ldots,H$ 分层，每层有 $s+1$ 个组成，故 $|D_H|=H(H+3)/2$。

本节的格坐标实现、允许的前向动作及其数量响应分别为

$$
\begin{gathered}
\gamma(T)=Bc(T)\in\mathbb R^2,\qquad
B=\begin{pmatrix}2&3\\1&2\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\\
S=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
C=BSB^{-1}=\begin{pmatrix}3&2\\2&1\end{pmatrix},\qquad
q=(2,3).
\end{gathered}
$$

已知整数 $L\ge0$ 表示恰好 $3L$ 次全局替换 $\rho$。由 $c\rho=Mc$，

$$
\gamma(\rho^{3L}T)=C^L\gamma(T),\qquad
n_L=qS^L=(F_m,F_{m+1}),\qquad m=3L+3,
\tag{1.2}
$$

其中 Fibonacci 数列由 $F_0=0,F_1=F_2=1$ 及 $F_{j+2}=F_{j+1}+F_j$（$j\ge0$）定义。对 $x=(a,b)$ 写 $n_L(x)=F_ma+F_{m+1}b$；它也是 $C^LBx$ 的第一坐标。$B$ 仅作可逆换坐标，没有把原始组成认作五窗计数实现。$H$ 只限制初始叶数，替换中的来源及末端来源允许超过 $H$。

末端观察合同固定已知 $E\in\mathbb Q_{\ge0}$，只给出一个 $r\in\mathbb Q$，其允许响应关系为

$$
\mathcal E_{H,L,E}
=\{(x,r)\in D_H\times\mathbb Q:|r-n_L(x)|\le E\}.
\tag{1.3}
$$

不提供早先读数档案、第二通道、叶标签或地址读取。令

$$
\phi=(1+\sqrt5)/2,\qquad \lambda=\phi^3,\qquad
\widehat r=\lambda^{-L}r,\qquad \eta=\lambda^{-L}E.
$$

归一化报告与归一化真值的误差至多 $\eta$；因 $L$ 已知，这个缩放不增加观察信息。统一精确组成恢复指存在同一个 $R:\mathbb Q\to D_H$，使所有 $(x,r)\in\mathcal E_{H,L,E}$ 都满足 $R(r)=x$；恢复器可使用已知的 $H,L,E$。误差关系是数学传感器假设，不含实际设备的精度或执行结论。

本来源域接受任意叶组成，不附加规范五窗的接缝、单位位或收缩条带。正数量规范来源的开条带另见[母卷命题 182.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md#182-收缩窗口对规范来源的识别与范数预算)；它与 [Gazeau–Verger-Gaugry，Proposition 3.1／式 (3.2)、(3.11)](https://doi.org/10.5802/aif.2245) 中非负黄金基整数的条带合同的坐标对应见[来源联合完成卷约定 1.3](FIB_SOURCE_COMPLETION_DYNAMICS.md#1-有限来源组成与经典条带)。以下碰撞不反驳那些受限来源上的识别结论。

**定理 1.2（有限组成的精确 Fibonacci 间距与取得深度）。** 在定义 1.1 的同一合同下，令

$$
d(H,L)=\min_{\substack{x,x'\in D_H\\x\ne x'}}
|n_L(x)-n_L(x')|.
$$

该最小值存在，且准确为

$$
\boxed{
 d(H,L)=
 \begin{cases}
 0,&H\ge F_{m+1},\\
 F_{m-j},&H<F_{m+1},\quad
 j=\max\{i\ge1:F_{i+1}\le H\}.
 \end{cases}}
\tag{1.4}
$$

正间距由同域的不同轴组成 $(F_{j+1},0)$、$(0,F_j)$ 达到；零间距由 $(F_{m+1},0)$、$(0,F_m)$ 达到。完整组成的统一精确恢复存在，当且仅当

$$
\boxed{\quad 2E<d(H,L)\quad}
\qquad\Longleftrightarrow\qquad
2\eta<\lambda^{-L}d(H,L).
\tag{1.5}
$$

因此归一化误差的严格阈值为 $\lambda^{-L}d(H,L)/2$，等号也不能统一恢复。固定 $H$ 并保持式 (1.4) 的 $j$ 时，

$$
\lim_{L\to\infty}\lambda^{-L}d(H,L)
=\frac{\phi^{3-j}}{\sqrt5}>0.
\tag{1.6}
$$

任意固定有限 $L$ 在无界初始叶数域上都有上述精确碰撞。

对 $x\in D_H$，以组成祖先的存在性定义

$$
h(x)=\max\{k\ge0:S^{-k}x\in\mathbb N_0^2\},\qquad
h_{\max}(H)=\max_{x\in D_H}h(x).
$$

非负逆归约的既有规则见[母卷定义 263.1 与定理 263.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#263-规范来源的约化核心与-robin-候选的绝对深度亏损)；此处只按三次替换一组计数组成祖先，不增加规范来源、互素或 Robin 预算条件。上述两个最大值有限，且

$$
\boxed{
\begin{aligned}
h_{\max}(H)&=\max\{k\ge0:F_{3k+1}\le H\},\\
n_L|_{D_H}\text{ 单射}
&\quad\Longleftrightarrow\quad h_{\max}(H)\le L.
\end{aligned}}
\tag{1.7}
$$

故无误差时，只取得一个末端数量报告所需的最小推进深度是 $L=h_{\max}(H)$。间距极小值与祖先深度极大值不要求由同一个来源达到；$h$ 也不恢复指定树的语法祖先。正误差的恢复仍须满足式 (1.5)。

证明。记 $A=F_m$、$B_{\mathrm{num}}=F_{m+1}$。$D_H$ 至少含 $(1,0),(0,1)$，故不同点对的集合非空且有限。当 $H\ge B_{\mathrm{num}}$ 时，所列两个非空轴组成都属于 $D_H$，读数同为 $AB_{\mathrm{num}}$，于是 $d=0$。

以下设 $H<B_{\mathrm{num}}$。$F_2=1\le H$ 保证 $j$ 存在，且

$$
1\le j\le m-1,\qquad F_{j+1}\le H<F_{j+2}.
$$

这里保留 $F_1=F_2$，没有删去重复的初值。使用经典 Fibonacci 加法式与 Cassini 公式；仓内的矩阵式及 Cassini 整数基应用见[母卷命题 105.2 的证明](FIBONACCI_ATOMIC_RELATION_GENERATION.md#1052-标量返回位置构成循环相位的子群)。取整数向量

$$
w_j=(F_{j+1},F_j),\qquad w_{j+1}=(F_{j+2},F_{j+1}).
$$

这些经典恒等式在本节的具体索引下给出

$$
\begin{aligned}
\det(w_j,w_{j+1})&=F_{j+1}^2-F_jF_{j+2}=(-1)^j,\\
AF_{j+1}-B_{\mathrm{num}}F_j&=(-1)^jF_{m-j},\\
AF_{j+2}-B_{\mathrm{num}}F_{j+1}&=(-1)^{j+1}F_{m-j-1}.
\end{aligned}
\tag{1.8}
$$

因此 $w_j,w_{j+1}$ 是整个 $\mathbb Z^2$ 的一组基。最后一式允许 $j=m-1$，此时其残差就是 $F_0=0$；前一式的残差仍为 $F_1=1$。

对任意不同 $x,x'\in D_H$，两个差坐标的绝对值均不超过 $H$。若差坐标同号，或其中一个为零，则数量差的绝对值至少为 $A$；而 $F_{m-j}\le F_{m-1}<A$。若差坐标异号，交换两点后可写成 $(u,-v)$，其中 $0<u,v\le H$。将正坐标对展开为

$$
(u,v)=p w_j+t w_{j+1},\qquad p,t\in\mathbb Z.
$$

置 $f=F_{m-j}\ge1$、$g=F_{m-j-1}\ge0$，式 (1.8) 给

$$
Au-B_{\mathrm{num}}v=(-1)^j(pf-tg).
\tag{1.9}
$$

若 $p,t\ge0$，则 $u\le H<F_{j+2}$ 强制 $t=0$，随后 $u>0$ 强制 $p\ge1$，故 $|pf-tg|\ge f$。若 $p,t\le0$，则 $u\le0$，不可能。若 $p\ge0,t<0$，$u>0$ 强制 $p\ge1$，且残差同向相加为 $pf+|t|g\ge f$。若 $p<0,t\ge0$，$u>0$ 强制 $t\ge1$，且残差的绝对值为 $|p|f+tg\ge f$。这些情形包括零系数，覆盖全部整数展开，也覆盖 $g=0$ 的端点。因此全部不同点对的间距至少为 $f$。所列轴点的叶数分别是 $F_{j+1},F_j\le H$，式 (1.8) 给间距恰为 $f$，证明式 (1.4)。

这里不假定最短点对唯一。若 $j<m-1$，则 $g>0$，上述取等只能来自 $p=1,t=0$，故最短差方向是 $\pm(F_{j+1},-F_j)$。若 $j=m-1$，则 $f=1,g=0$，取等须 $|p|=1$；结合 $0<u\le H<B_{\mathrm{num}}$，只能是 $(p,t)=(1,0)$ 或 $(-1,1)$。第二种给

$$
w_m-w_{m-1}=w_{m-2}.
$$

故这一档的最短差方向是 $\pm(F_m,-F_{m-1})$ 与 $\pm(F_{m-1},-F_{m-2})$，两组轴点都在同域内并列达到间距一。对这些点对加共同非负平移，只要仍在 $D_H$ 内，也可产生并列最短对；这不改变最小值。零间距则由式 (1.4) 的另一个分支处理。

现在对每个有理报告定义有限候选集

$$
\mathcal C(r)=\{x\in D_H:|r-n_L(x)|\le E\}.
$$

若 $2E<d$，两个不同候选会使其读数差至多为 $2E<d$，矛盾；故候选集至多有一个元素。在非空时输出唯一候选，在空时输出固定的 $(1,0)$，就得到所需总恢复器。允许响应保证真组成在候选集中，证明充分性。这是至多 $H(H+3)/2$ 个组成的有限枚举存在构造，不附加最优复杂度或设备实现主张。

反向，取达到 $d$ 的不同点 $x,x'$，令

$$
r_*=[n_L(x)+n_L(x')]/2\in\mathbb Q.
$$

若 $2E\ge d$，则这个共同有理中点到两读数的距离均为 $d/2\le E$。同一个恢复器在同一个报告上不能输出两个不同组成，所以失败侧包括等号。若 $d=0$，共同报告已是精确整数，$E=0$ 也失败。这是闭误差区间的纤维论证；一般候选纤维恢复结构直接复用[恢复几何卷 §3.1](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md#31-候选纤维半径与恢复的最小最坏误差)，不另立一般最近邻定理。乘以已知正数 $\lambda^{-L}$ 即得归一化条件。

固定 $H$ 时，充分大的 $L$ 满足 $H<F_{3L+4}$，此后 $j$ 不变。用[母卷命题 18.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#18-minkowski-双坐标窗口与全息解释边界) 所用的经典双根表达，令 $\psi=-\phi^{-1}$，有

$$
\lambda^{-L}F_{3L+3-j}
=\frac{\phi^{3-j}-\phi^{-3L}\psi^{3L+3-j}}{\sqrt5}.
$$

第二项趋零，得到式 (1.6)。固定有限 $L$ 而取消 $H$ 上界，则零间距分支的两个轴组成仍为合法非空来源，证明无界域碰撞。

最后，$S$ 是整数可逆矩阵。对 $k\ge0$，$S^k$ 两列的叶数和分别是 $F_{3k+1},F_{3k+2}$；$k=0$ 时两者同为一，对 $k\ge1$ 使用上述母卷命题 105.2 的 Fibonacci 矩阵幂。若 $y=S^{-k}x\in\mathbb N_0^2$，则 $y\ne0$，并且

$$
x_1+x_2=F_{3k+1}y_1+F_{3k+2}y_2\ge F_{3k+1}.
$$

所以 $x\in D_H$ 的每个组成祖先深度都满足 $F_{3k+1}\le H$，最大值有限。反向，只要 $F_{3k+1}\le H$，$x=S^k(1,0)$ 就在 $D_H$ 内并具有深度至少 $k$。这证明式 (1.7) 的第一式，且没有要求这一来源同时达到间距极小值。由式 (1.4)，单射等价于 $H<F_{3L+4}$；由于 $F_{3k+1}$ 随 $k\ge0$ 严格递增，这又等价于 $h_{\max}(H)\le L$。取最小 $L$ 即得所述无误差取得深度。这里的组成祖先存在，仅保证有某棵组成正确的前驱树；没有断言指定原始树属于相应替换像。证毕。

**定义 1.3（组成逆许可任务）。** 沿用定义 1.1 的共同来源与响应合同，另取二值目标

$$
\begin{aligned}
\chi(a,b)=1
&\quad\Longleftrightarrow\quad S^{-1}(a,b)\in\mathbb N_0^2\\
&\quad\Longleftrightarrow\quad 3a\le2b\ \text{且}\ b\le2a,
\end{aligned}
\qquad
S^{-1}=\begin{pmatrix}-3&2\\2&-1\end{pmatrix}.
\tag{1.10}
$$

统一恢复此任务指存在同一个 $P:\mathbb Q\to\{0,1\}$，对全部 $(x,r)\in\mathcal E_{H,L,E}$ 输出 $P(r)=\chi(x)$。这个目标判定初始组成是否具有一个非负三步组成祖先；它不授权实际逆操作，也不判定指定树的三步语法祖先。

**定理 1.4（完整组成失效后的许可窗口与尖锐噪声边界）。** 记

$$
A=F_m,\qquad B_{\mathrm{num}}=F_{m+1},\qquad
K=B_{\mathrm{num}}+A/2,\qquad m=3L+3.
$$

$A$ 是偶数，故 $K$ 为整数，且 $B_{\mathrm{num}}<K$。在同一个任意叶组成域上，有准确分离：

$$
\boxed{
\begin{array}{ll}
B_{\mathrm{num}}\le H<K:
 &\text{完整组成在 }E=0\text{ 时已不能恢复，}\quad
   \chi\text{ 统一可恢复}\ \Longleftrightarrow\ 2E<1;\\[2pt]
H\ge K:
 &\chi\text{ 在 }E=0\text{ 时也不能统一恢复。}
\end{array}}
\tag{1.11}
$$

第一行的归一化许可阈值是 $2\eta<\lambda^{-L}$，等号失败。若 $H<B_{\mathrm{num}}$，式 (1.5) 的组成恢复条件足以恢复 $\chi$，但不主张它是这个二值任务的最优条件。特别地，$H=1,2$ 时没有许可组成，$\chi$ 为常值零，对任意 $E$ 都可恢复。全部结论包括 $L=0$：这时 $A=2,B_{\mathrm{num}}=3,K=4$，许可窗口是 $H=3$，在 $H=4$ 已有精确跨类碰撞。

证明。$S\equiv I\pmod2$，因此 $(A,B_{\mathrm{num}})=qS^L\equiv(0,1)\pmod2$，给出 $A$ 偶数。$m\ge3$ 保证 $0<A<B_{\mathrm{num}}$。Cassini 等式 $F_m^2-F_{m-1}F_{m+1}=(-1)^{m-1}$ 给 $\gcd(A,B_{\mathrm{num}})=1$，故数量行的整数核准确为

$$
\ker_{\mathbb Z} n_L=\mathbb Z(B_{\mathrm{num}},-A).
\tag{1.12}
$$

设许可点 $x=(a,b)\ne0$ 与另一个非负整数点 $x'$ 有相同读数。由式 (1.12)，存在非零整数 $z$ 使

$$
x'=x+z(B_{\mathrm{num}},-A).
$$

若 $z>0$，非负性给 $b\ge zA$，许可不等式 $b\le2a$ 给 $a\ge zA/2$，所以

$$
x'_1+x'_2=a+b+z(B_{\mathrm{num}}-A)
\ge z(B_{\mathrm{num}}+A/2)=zK\ge K.
$$

若 $z=-s<0$，非负性给 $a\ge sB_{\mathrm{num}}$，许可不等式 $3a\le2b$ 给 $b\ge3sB_{\mathrm{num}}/2$。于是

$$
a+b\ge(5/2)sB_{\mathrm{num}}\ge sK\ge K,
$$

其中 $K=B_{\mathrm{num}}+A/2<(3/2)B_{\mathrm{num}}$。这分别处理了两个核方向：任何许可点与不同非负点的共同初始预算至少为 $K$。因此 $H<K$ 时，每个包含许可点的精确读数纤维都是单点；两个不同的非许可点仍可处在同一纤维。

当 $H\ge B_{\mathrm{num}}$ 时，定理 1.2 的两个轴组成已给出完整组成的精确碰撞；这两个轴组成的 $\chi$ 都是零，并未构成许可标签碰撞。在 $B_{\mathrm{num}}\le H<K$ 内，任意跨类读数都是不同整数，故其间距至少为一。

为证明该跨类间距准确为一，令

$$
u=F_{m-1},\qquad v=F_{m-2},\qquad t=\lceil v/2\rceil,
\qquad x_+=(t,2t),\qquad x_-=(t+u,2t-v).
\tag{1.13}
$$

这里 $u\ge v\ge1$、$1\le t\le v$，且 $2t-v\in\{0,1\}$。$x_+$ 在许可锥的上边界 $b=2a$，故 $\chi(x_+)=1$；$x_-$ 的第二坐标至多一，第一坐标至少二，故 $3(x_-)_1>2(x_-)_2$，于是 $\chi(x_-)=0$。又由 $B_{\mathrm{num}}=2u+v$，

$$
|x_+|_1=3t\le3v\le2u+v=B_{\mathrm{num}},\qquad
|x_-|_1=u+3t-v\le u+2v\le2u+v.
$$

因此两点都属于 $D_{B_{\mathrm{num}}}\subseteq D_H$。在式 (1.8) 中取 $j=m-2$，经典 Cassini 残差给

$$
|n_L(x_-)-n_L(x_+)|
=|Au-B_{\mathrm{num}}v|=1.
$$

$m=3$ 时 $u=v=t=1$，仍是非空合法点 $(1,2)$ 与非许可点 $(2,1)$，没有退化索引。

若 $2E<1$，同一有理报告的有限候选集 $\mathcal C(r)$ 不能同时含两个不同许可标签：否则相应跨类整数读数的距离至多 $2E<1$。非空候选集上的共同标签定义 $P(r)$，空候选集取零，便得到统一许可恢复器。反向，式 (1.13) 的两读数有共同有理中点，到两者距离均为 $1/2$；它在 $2E\ge1$ 时同时允许，且两个正确标签不同。因此等号及更大误差均不能恢复。乘以 $\lambda^{-L}$ 给出归一化边界。

预算达到 $K$ 时，取

$$
x_{\mathrm{yes}}=(A/2,A),\qquad
x_{\mathrm{no}}=(K,0).
\tag{1.14}
$$

前者非零且 $S^{-1}x_{\mathrm{yes}}=(A/2,0)\in\mathbb N_0^2$，后者不满足许可不等式。它们的叶数分别为 $3A/2\le K$ 与 $K$，而

$$
x_{\mathrm{no}}-x_{\mathrm{yes}}=(B_{\mathrm{num}},-A),\qquad
n_L(x_{\mathrm{yes}})=AK=n_L(x_{\mathrm{no}}).
$$

所以 $H=K$ 已有合法的精确跨类碰撞，每个更大 $H$ 继续包含该对；任何非负误差预算也继续允许共同精确报告。这证明式 (1.11) 的第二行。$H=1,2$ 的常值条款来自许可非零整数点必有 $a\ge1$、$b\ge\lceil3a/2\rceil$，故叶数至少为三。$H<B_{\mathrm{num}}$ 时，先用定理 1.2 的恢复器取得组成再计算式 (1.10)，给出所声明的充分性，不对二值任务额外作最优性断言。

组成许可与树语法逆的区别已见[母卷定义 116.2 后的语法逆边界](FIBONACCI_ATOMIC_RELATION_GENERATION.md#116-规范数值的前缀隐藏尾部与接缝密度)。在本节的三步合同下，同样可直接比较实际树

$$
\rho^3(\alpha)=\langle\langle\beta,\alpha\rangle,\beta\rangle,
\qquad
T'=\langle\beta,\langle\beta,\alpha\rangle\rangle.
$$

两者组成同为 $(1,2)$，所以在 $H\ge3$ 时具有同一个许可标签一。若 $T'$ 是某棵树 $U$ 的 $\rho^3$ 像，则由 $S$ 两列的叶数三、五，$3c(U)_1+5c(U)_2=3$ 强制 $c(U)=(1,0)$。唯一的一叶来源是 $\alpha$，其三步像是上面第一棵树，左右结构与 $T'$ 不同，矛盾。因此即使完整组成及其许可都已恢复，也没有判定指定树的三步逆语法。

最后，格坐标的代数守恒直接引用[母卷命题 145.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md#145-五窗递归中的守恒异号扇区与勾股的适用对象)：$Q(y)=y_1^2-y_1y_2-y_2^2$ 满足 $Q(C^2y)=Q(y)$。该式不给来源锥 $\mathcal K=B\mathbb N_0^2$ 上的群作用。例如在环境整数格中，

$$
C^{-2}B\binom10=B\binom{13}{-8}=\binom2{-3}\notin\mathcal K,
\tag{1.15}
$$

因为 $B^{-1}$ 将它送到含负坐标的 $(13,-8)$。许可条件属于非负组成锥，二次型守恒属于环境线性坐标；两者条件不同。本定理只针对定义 1.1 的一个末端有理报告和任意叶组成域，不恢复完整关系来源、不取得实际逆执行，也不将代数洛伦兹型二次式解释为现实相对论。证毕。

## 追加锚（本行以下为增补区）

## 2. 许可预算阶梯与深层碰撞前沿

**定义 2.1（深度许可、跨类间距与统一任务恢复）。** 完全沿用定义 1.1 的非空有序完全二叉树、替换 $\rho$、初始组成域 $D_H$、已知整数 $H\ge1,L\ge0$ 和单个末端报告合同 $\mathcal E_{H,L,E}$，其中 $E\in\mathbb Q_{\ge0}$。记

$$
m=3L+3,\qquad A=F_m,\qquad B_{\mathrm{num}}=F_{m+1},
\qquad v=F_{m-1}=B_{\mathrm{num}}-A.
$$

对整数 $k\ge1$，定义深度许可目标

$$
\chi_k(c)=\mathbf1_{\{S^{-k}c\in\mathbb N_0^2\}},
\qquad S=M^3,
\qquad \chi_0(c)=1\quad(c\in D_H).
\tag{2.1}
$$

因此 $\chi_1$ 就是定义 1.3 的 $\chi$；$k=0$ 只给定义边界。许可表示存在具有相应组成的非空祖先树，不判定指定树是否具有该语法祖先，也不授权实际逆执行；这一区别直接沿用定理 1.4。定理 1.2 的 $h(c)$ 仍只计数组成祖先深度，母卷定义 263.1 与定理 263.2 的规范来源条件保持其原有适用域。

定义跨类末端读数间距

$$
\delta_k(H,L)=
\min_{\substack{x,y\in D_H\\\chi_k(x)\ne\chi_k(y)}}
|n_L(x)-n_L(y)|,
\tag{2.2}
$$

跨类点对集合为空时取 $+\infty$，故 $\delta_0(H,L)=+\infty$。统一恢复 $\chi_k$ 指存在同一个 $P:\mathbb Q\to\{0,1\}$，使全部 $(c,r)\in\mathcal E_{H,L,E}$ 都满足 $P(r)=\chi_k(c)$；$P$ 可使用已知的 $H,L,E,k$。观察仍只有这一个报告，不增加历史、第二通道、标签或地址。归一化仍为定义 1.1 的 $\eta=\lambda^{-L}E$，$\lambda=\phi^3$。

**定理 2.2（单步许可的全预算噪声阶梯）。** 在定义 2.1 的合同下，令 $K_1=B_{\mathrm{num}}+A/2$。则对所有整数 $H\ge1$，

$$
\boxed{
\delta_1(H,L)=
\begin{cases}
+\infty,&H\le2,\\
F_{m-1},&H=3,\\
F_{m-j},&4\le H<K_1,\quad
j=\max\{i\ge3:F_{i+3}\le2H\},\\
0,&H\ge K_1.
\end{cases}}
\tag{2.3}
$$

第三分支的指标满足 $3\le j\le m-1$；$L=0$ 时该分支为空。单步任务统一可恢复的准确条件为

$$
\boxed{2E<\delta_1(H,L)}
\qquad\Longleftrightarrow\qquad
2\eta<\lambda^{-L}\delta_1(H,L).
\tag{2.4}
$$

在 $+\infty$ 分支，$\chi_1$ 恒为零，每个有限 $E$ 都可恢复；在有限间距分支，等号失败。

更具体地，对每个整数 $j\ge3$，差方向 $\pm(F_{j+1},-F_j)$ 的跨许可点对所需的最小共同叶预算为

$$
\begin{aligned}
C_j
&=\min_{\substack{x,y\in\mathbb N_0^2\setminus\{0\}\\
\chi_1(x)\ne\chi_1(y),\ y-x=\pm(F_{j+1},-F_j)}}
\max\{|x|_1,|y|_1\}\\
&=F_{j+1}+\lceil F_j/2\rceil
=\lceil F_{j+3}/2\rceil.
\end{aligned}
\tag{2.5}
$$

这里 $\chi_1$ 按式 (2.1) 定义在所有非零非负组成上，$|c|_1$ 是叶数。该最小值由实际完整树的组成达到；当 $3\le j\le m$ 时，这对组成的读数间距为 $F_{m-j}$。

证明。定理 1.4 已给出 $A$ 偶数、$K_1$ 整数以及 $H\ge K_1$ 的实际零间距点对，直接得到式 (2.3) 的最后分支。其常值条款也给 $H\le2$ 的第一分支。

先证明式 (2.5) 的叶预算几何。任意跨类异号差，交换坐标差方向后写为 $(u,-w)$，其中 $u,w>0$。若许可点 $x=(a,b)$ 与非许可点 $y=x+(u,-w)$ 相配，则 $b\ge w$；式 (1.10) 给 $a\ge b/2$，所以

$$
|y|_1=a+b+u-w\ge u+w/2.
$$

若非许可点为 $y=x-(u,-w)$，则 $a\ge u$，许可不等式又给 $b\ge3a/2$，从而 $|x|_1\ge5u/2$。特别在 $u>w$ 时，两种方向均给

$$
\max\{|x|_1,|y|_1\}\ge\ell(u,w),
\qquad \ell(u,w)=u+w/2.
\tag{2.6}
$$

取 $u=F_{j+1},w=F_j$，$j\ge3$ 保证 $u>w\ge2$，共同整数预算至少为 $u+\lceil w/2\rceil$。令 $t=\lceil F_j/2\rceil$，取

$$
x_{\mathrm{yes}}=(t,F_j),\qquad
x_{\mathrm{no}}=(t+F_{j+1},0).
\tag{2.7}
$$

当 $F_j=2$ 时 $3t\le2F_j$ 直接成立；当 $F_j\ge3$ 时，$t\le(F_j+1)/2\le2F_j/3$。同时 $F_j\le2t$，故 $x_{\mathrm{yes}}$ 满足两个许可不等式。$x_{\mathrm{no}}$ 是非零横轴点，许可为零。由于 $F_j\le F_{j+1}$，两者最大叶数恰为 $t+F_{j+1}$。定义 1.1 的实际树实现给两棵合法非空来源；还可先实现 $S^{-1}x_{\mathrm{yes}}\in\mathbb N_0^2\setminus\{0\}$ 的祖先组成，再施加 $\rho^3$。递推给 $F_{j+3}=2F_{j+1}+F_j$，证明式 (2.5)。当 $j\le m$ 时，式 (1.8) 的经典残差给式 (2.7) 两点的间距 $F_{m-j}$，包括 $j=m$ 的零值。

$H=3$ 时，许可非零点只能是 $(1,2)$。其余八点均非法；与 $(2,1)$ 和 $(0,3)$ 的读数差绝对值都是 $B_{\mathrm{num}}-A=v$。与另外六点 $(1,0),(0,1),(2,0),(1,1),(0,2),(3,0)$ 的差绝对值依次为

$$
2B_{\mathrm{num}},\quad A+B_{\mathrm{num}},\quad
2B_{\mathrm{num}}-A,\quad B_{\mathrm{num}},\quad A,\quad
2(B_{\mathrm{num}}-A),
$$

每个均不小于 $v$。这证明第二分支。$L=0$ 时 $A=2,B_{\mathrm{num}}=3,v=1,K_1=4$，故 $H=3$ 仍严格小于首次零碰撞预算，且没有退化指标。

现在设 $4\le H<K_1$。由 $F_6=8\le2H$，式 (2.3) 的指标集合非空。由 $F_{m+3}=A+2B_{\mathrm{num}}=2K_1$，最大指标满足 $j\le m-1$。式 (2.5) 等价地给

$$
C_j\le H<C_{j+1},\qquad
C_m=K_1.
$$

考虑任意跨类点对。差坐标同号或其中一个为零时，读数差绝对值至少为 $A$。差坐标异号时写为 $(u,-w)$，$u,w>0$。若 $u\le w$，则

$$
|Au-B_{\mathrm{num}}w|
=B_{\mathrm{num}}w-Au\ge(B_{\mathrm{num}}-A)w
\ge F_{m-1}\ge F_{m-j}.
$$

余下设 $u>w$。式 (2.6) 给 $\ell(u,w)\le H$。$\ell(u,w)$ 与 $\ell(F_{j+2},F_{j+1})$ 都是半整数；因 $H$ 为整数且 $H<C_{j+1}=\lceil\ell(F_{j+2},F_{j+1})\rceil$，有

$$
\ell(u,w)\le H<\ell(F_{j+2},F_{j+1}).
$$

直接使用式 (1.8) 的经典整数基，唯一写成

$$
(u,w)=p(F_{j+1},F_j)+s(F_{j+2},F_{j+1}),\qquad p,s\in\mathbb Z.
$$

置 $f=F_{m-j}\ge1$、$g=F_{m-j-1}\ge0$，仍由式 (1.8) 得

$$
Au-B_{\mathrm{num}}w=(-1)^j(pf-sg).
\tag{2.8}
$$

若 $p,s\ge0$，$\ell$ 的严格上界强制 $s=0$，随后 $u>0$ 强制 $p\ge1$，所以残差绝对值至少为 $f$。若 $p,s\le0$，则 $u\le0$，不可能。若 $p\ge0,s<0$，$u>0$ 强制 $p\ge1$，而残差绝对值为 $pf+|s|g\ge f$。若 $p<0,s\ge0$，$u>0$ 强制 $s\ge1$，而残差绝对值为 $|p|f+sg\ge f$。这些情形覆盖所有整数系数，也覆盖末档 $g=F_0=0$。同号差的下界 $A$ 亦大于 $f$，故所有跨类间距至少为 $F_{m-j}$。式 (2.7) 的实际点对在 $D_H$ 内达到该值，证明第三分支；该上界来自整数来源，并未仅在连续锥上取极值。

最后，对每个有理报告使用定理 1.2 证明中的有限候选集 $\mathcal C(r)$，但只要求候选标签相同。若 $2E<\delta_1$，一个报告不能同时容许异标签候选，因为其读数差至多为 $2E$。非空候选集输出共同标签，空候选集输出零，便给所需总恢复器。若跨类集合非空且 $2E\ge\delta_1$，取达到最小值的实际两点，其两整数读数的有理中点同时是允许报告，两个正确标签不同，故统一恢复失败。跨类集合为空时直接输出零即可。这是[恢复几何卷 §3.1](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md#31-候选纤维半径与恢复的最小最坏误差) 的候选目标纤维判据在本任务中的应用，也沿用定理 1.4 的闭误差论证。乘以已知正数 $\lambda^{-L}$ 得归一化式；共同中点使等号仍属失败侧。证毕。

**定理 2.3（任意深度的首次碰撞、单位间距窗口与深度边界）。** 对定义 2.1 的任意整数 $k\ge1$，令 $t=3k$，并定义

$$
r_k=\min\left\{\frac{F_{t-1}}{F_t},\frac{F_t}{F_{t+1}}\right\},
\qquad
R_k=\max\left\{\frac{F_{t-1}}{F_t},\frac{F_t}{F_{t+1}}\right\}.
$$

则非零非负整数组成的许可锥、斜率宽度与最小许可叶预算分别为

$$
\begin{gathered}
\chi_k(a,b)=1\quad\Longleftrightarrow\quad
b>0\ \text{且}\ r_kb\le a\le R_kb,\\
W_k=R_k-r_k=\frac1{F_{3k}F_{3k+1}},\qquad
N_k=F_{3k+1}.
\end{gathered}
\tag{2.9}
$$

$k$ 奇数时 $r_k=F_{3k-1}/F_{3k}$，偶数时 $r_k=F_{3k}/F_{3k+1}$。$N_k$ 由实际树 $\rho^{3k}(\alpha)$ 达到。

定义首次跨类精确碰撞预算为

$$
K_{k,L}=\min\{H\ge1:\delta_k(H,L)=0\}.
$$

该最小值存在，且

$$
\boxed{
K_{k,L}=
\begin{cases}
B_{\mathrm{num}}+\lceil Ar_k\rceil,&1\le k\le L+1,\\
N_k,&k\ge L+2.
\end{cases}}
\tag{2.10}
$$

特别地，所有整数 $H\ge1$ 的无噪统一恢复条件准确为 $H<K_{k,L}$。$H<N_k$ 时 $\chi_k$ 恒为零，对每个有限 $E$ 都可恢复；$H\ge K_{k,L}$ 时 $\delta_k=0$，任意 $E\ge0$ 都不能统一恢复。对于 $1\le k\le L+1$，还成立

$$
\boxed{
B_{\mathrm{num}}\le H<K_{k,L}
\quad\Longrightarrow\quad
\delta_k(H,L)=1,
\qquad
\chi_k\text{ 统一可恢复}\ \Longleftrightarrow\ 2E<1
\ \Longleftrightarrow\ 2\eta<\lambda^{-L}.}
\tag{2.11}
$$

等号失败。存在某个预算 $H$ 使 $\chi_k|_{D_H}$ 非恒值且可无噪统一恢复，当且仅当 $k\le L+1$；此处是预算的存在量词。

临界深度 $k=L+1$ 满足 $N_k=B_{\mathrm{num}}$ 和 $K_{k,L}=B_{\mathrm{num}}+v=2B_{\mathrm{num}}-A$，其全部预算与噪声分支为

$$
\boxed{
\begin{array}{ll}
H<B_{\mathrm{num}}:&\chi_{L+1}\text{ 恒为零，任意有限 }E\text{ 可恢复};\\
B_{\mathrm{num}}\le H<2B_{\mathrm{num}}-A:
&\chi_{L+1}\text{ 可恢复}\ \Longleftrightarrow\ 2E<1;\\
H\ge2B_{\mathrm{num}}-A:
&\chi_{L+1}\text{ 在 }E=0\text{ 时已不能恢复}.
\end{array}}
\tag{2.12}
$$

对于 $k\ge L+2$，全部预算只有 $H<N_k$ 的常值零分支和 $H\ge N_k$ 的精确失败分支。对于 $2\le k\le L$、$N_k\le H<B_{\mathrm{num}}$ 的小预算域，本定理只给无噪恢复，不给最优正噪声间距；$k=1$ 的全预算间距由定理 2.2 给出。

证明。经典 Fibonacci 矩阵幂直接使用[母卷命题 105.2 的证明](FIBONACCI_ATOMIC_RELATION_GENERATION.md#1052-标量返回位置构成循环相位的子群)，在本卷的记号下为

$$
S^k=M^t=\begin{pmatrix}F_{t-1}&F_t\\F_t&F_{t+1}\end{pmatrix},
\qquad
S^{-k}=(-1)^t\begin{pmatrix}F_{t+1}&-F_t\\-F_t&F_{t-1}\end{pmatrix}.
$$

Cassini 给行列式 $(-1)^t$，因此逆矩阵为整数矩阵。由两列的斜率，$S^k\mathbb R_{\ge0}^2$ 正是式 (2.9) 的闭锥；更明确地，当 $t$ 奇数时，逆坐标非负等价于
$F_ta\ge F_{t-1}b$ 和 $F_{t+1}a\le F_tb$，当 $t$ 偶数时两式反向。非零许可点必有 $b>0$。Cassini 又给

$$
\frac{F_{t-1}}{F_t}-\frac{F_t}{F_{t+1}}
=\frac{(-1)^t}{F_tF_{t+1}},
$$

确定端点次序及宽度。因为整数点的逆坐标自动为整数，闭锥条件同时充分保证非负整数祖先，故并非只有实锥松弛。

若祖先组成为 $y=S^{-k}c\in\mathbb N_0^2\setminus\{0\}$，则其当前叶数是

$$
|c|_1=F_{t+1}y_1+F_{t+2}y_2\ge F_{t+1}.
$$

此叶预算计算已见定理 1.2 的证明。取 $y=(1,0)$，实际树 $\rho^{3k}(\alpha)$ 组成是 $(F_{t-1},F_t)$，叶数为 $N_k$，故下界达到。每个许可整数点的非零整数祖先也可由定义 1.1 实现为完整树，再施加 $\rho^{3k}$；这里不要求任意指定括号都属于替换像。若 $j\le k$，则 $S^{-j}c=S^{k-j}y$ 非负，因而许可锥嵌套，尤其 $\chi_k=1$ 蕴含 $\chi_1=1$。

先设 $1\le k\le L+1$。同一组成

$$
c_*=(v,A)=S^{L+1}(1,0)
\tag{2.13}
$$

在每个这样的许可锥中。因此 $Ar_k\le v\le AR_k$。记 $a_k=\lceil Ar_k\rceil$，则 $1\le a_k\le v\le AR_k$；式 (2.9) 保证 $(a_k,A)$ 许可。取

$$
x=(a_k,A),\qquad y=(B_{\mathrm{num}}+a_k,0).
\tag{2.14}
$$

$y$ 是非许可轴点，$y-x=(B_{\mathrm{num}},-A)$ 属于式 (1.12) 的整数核。因为 $A<B_{\mathrm{num}}$，两点最大叶数恰为 $B_{\mathrm{num}}+a_k$；$x$ 可用其整数祖先再施加替换实现，$y$ 可用任意完整括号的全 $\alpha$ 叶实现。这给首次碰撞预算的上界。

反向，任一许可 $x=(a,b)$ 和不同的非负点 $x'$ 有相同整数读数时，直接由式 (1.12) 得 $x'=x+z(B_{\mathrm{num}},-A)$，$z\in\mathbb Z\setminus\{0\}$。若 $z>0$，非负性给 $b\ge zA$，许可锥给 $a\ge\lceil r_kb\rceil$，所以

$$
\begin{aligned}
|x'|_1
&=a+b+z(B_{\mathrm{num}}-A)\\
&\ge zB_{\mathrm{num}}+\lceil zAr_k\rceil
\ge B_{\mathrm{num}}+\lceil Ar_k\rceil.
\end{aligned}
\tag{2.15}
$$

若 $z=-s<0$，非负性给 $a\ge sB_{\mathrm{num}}$。由许可锥嵌套及式 (1.10)，$b\ge3a/2$，于是

$$
|x|_1\ge\frac52sB_{\mathrm{num}}
>B_{\mathrm{num}}+v
\ge B_{\mathrm{num}}+a_k,
$$

其中 $v<B_{\mathrm{num}}$。两个核方向都被处理，故预算小于式 (2.14) 的最大叶数时不存在跨类精确碰撞，证明式 (2.10) 的第一分支。

再设 $k\ge L+2$，取最小许可来源

$$
x=S^k(1,0)=(F_{3k-1},F_{3k}),\qquad
 y=x-(B_{\mathrm{num}},-A).
\tag{2.16}
$$

因 $3k-1\ge m+2$，$y$ 的第一坐标非负，第二坐标严格为正。它的叶数为 $N_k-(B_{\mathrm{num}}-A)=N_k-v<N_k$，所以由最小许可叶预算必有 $\chi_k(y)=0$。两点读数相同，且都由实际非空树实现，在 $H=N_k$ 已跨类碰撞。预算小于 $N_k$ 时没有许可点，故无法更早跨类碰撞。这证明第二分支，也给其完整两态结论。

对于无噪报告，$H<K_{k,L}$ 的每条精确读数纤维具有共同标签；[恢复几何卷 §3.1](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md#31-候选纤维半径与恢复的最小最坏误差) 的目标纤维判据给统一恢复。$H\ge K_{k,L}$ 时上述实际反标签点对的共同精确报告否定恢复，并在任意更大误差合同中继续允许。$H<N_k$ 时输出零即可。

为求式 (2.11) 的正间距，用同一个 $c_*$ 及一个非法轴组成

$$
z_*=(0,A+F_{m-2}).
$$

它们均在 $D_{B_{\mathrm{num}}}$ 内，因为 $|c_*|_1=v+A=B_{\mathrm{num}}$，且 $A+F_{m-2}\le A+v=B_{\mathrm{num}}$。$c_*$ 对全部 $k\le L+1$ 许可，$z_*$ 对全部 $k\ge1$ 非许可。经典加法式及式 (1.8) 在 $j=m-2$ 的残差给

$$
\begin{aligned}
n_L(c_*)&=A(v+B_{\mathrm{num}})=F_{2m},\\
n_L(z_*)-n_L(c_*)&=B_{\mathrm{num}}F_{m-2}-Av
=(-1)^{m-1}=(-1)^L.
\end{aligned}
\tag{2.17}
$$

当 $B_{\mathrm{num}}\le H<K_{k,L}$ 时，没有跨类相等的整数读数，故跨类间距至少为一，而这两个实际组成达到一。定理 2.2 证明中的闭候选标签论证给 $2E<1$ 的充分性；共同报告

$$
r_*=F_{2m}+(-1)^L/2\in\mathbb Q
$$

在 $2E\ge1$ 时距两真值都不超过 $E$，给等号及以上的失败。这证明式 (2.11)，归一化只乘以已知正数 $\lambda^{-L}$。指定树 $\rho^{3(L+1)}(\alpha)$ 是 $c_*$ 的实际来源见证，其历史不作为恢复器的额外输入。

当 $k=L+1$ 时，$N_k=F_{m+1}=B_{\mathrm{num}}$。若 $k$ 奇数，则 $r_k=v/A$，故 $a_k=v$；若 $k$ 偶数，则 $r_k=A/B_{\mathrm{num}}$，而 Cassini 给 $vB_{\mathrm{num}}-A^2=1$，故 $a_k=\lceil v-1/B_{\mathrm{num}}\rceil=v$。由此得到式 (2.12)。当 $k\le L+1$ 时 $N_k\le B_{\mathrm{num}}<K_{k,L}$，取 $H=B_{\mathrm{num}}$，域中有许可 $c_*$ 和非许可轴点，同时可无噪恢复。反向，$k\ge L+2$ 时 $H<N_k$ 恒值，$H\ge N_k$ 已精确失败，所以不存在非恒值的可恢复预算。这证明预算存在量词的准确边界。小预算 $2\le k\le L$、$N_k\le H<B_{\mathrm{num}}$ 的跨类读数仍为不同整数，因而 $\delta_k\ge1$，但单位间距见证未在这些预算中给出，此下界不被当作最优正噪声值。证毕。

**定理 2.4（奇偶饱和与同一实际来源的深度、间距和碰撞连接）。** 设 $1\le k\le L+1$，沿用定理 2.3 的 $a_k=K_{k,L}-B_{\mathrm{num}}$ 与 $v=F_{m-1}$。则精确取整亏量为

$$
\boxed{
a_k=
\begin{cases}
v-\left\lfloor F_{m-3k}/F_{3k}\right\rfloor,&k\text{ 奇},\\
v-\left\lfloor F_{m-3k-1}/F_{3k+1}\right\rfloor,&k\text{ 偶且 }k\le L,\\
v,&k=L+1\text{ 偶}.
\end{cases}}
\tag{2.18}
$$

第三分支独立处理，全部 Fibonacci 指标非负。首次碰撞预算达到 $B_{\mathrm{num}}+v$ 的准确条件为

$$
\boxed{
K_{k,L}=B_{\mathrm{num}}+v
\quad\Longleftrightarrow\quad
\begin{cases}
2k>L+1,&k\text{ 奇},\\
2k\ge L+1,&k\text{ 偶}.
\end{cases}}
\tag{2.19}
$$

式 (2.9) 的锥宽 $W_k$ 随 $k\ge1$ 严格减少，而式 (2.19) 的预算在所述域内已饱和；这里的饱和只指 $k\le L+1$ 的首次精确碰撞预算。

同一实际许可树

$$
T_* =\rho^{3(L+1)}(\alpha),\qquad c(T_*)=c_*=(v,A),
\qquad |\operatorname{Leaves}(T_*)|=B_{\mathrm{num}}
$$

在每个 $B_{\mathrm{num}}\le H<K_{k,L}$ 的窗口都满足

$$
h(c_*)=h_{\max}(H)=L+1,
\qquad
|n_L(c_*)-n_L(z_*)|=\delta_k(H,L)=1,
\quad z_*=(0,A+F_{m-2}).
\tag{2.20}
$$

若且仅若式 (2.19) 的饱和条件成立，$c_*$ 还在首次碰撞预算 $H=K_{k,L}$ 与轴点 $(B_{\mathrm{num}}+v,0)$ 碰撞。式 (2.20) 的单位间距和该零间距属于不同预算。

证明。以下仅把[母卷命题 105.2 证明中的经典矩阵幂、加法式与 Cassini 等式](FIBONACCI_ATOMIC_RELATION_GENERATION.md#1052-标量返回位置构成循环相位的子群)用于取整。写 $t=3k$。当 $m>t$ 时，比较 $M^m=M^{m-t}M^t$ 的第一列，令 $d=m-t\ge1$，得到

$$
\begin{aligned}
v&=F_{d-1}F_{t-1}+F_dF_t,\\
A&=F_{d-1}F_t+F_dF_{t+1},\\
vF_t-AF_{t-1}
&=F_d(F_t^2-F_{t-1}F_{t+1})=(-1)^{t-1}F_d.
\end{aligned}
$$

因此当 $k$ 奇且 $k\le L$ 时，$vF_t-AF_{t-1}=F_{m-t}$；奇数对角 $k=L+1$ 时 $m=t$，该差直接为零，仍等于 $F_0$。当 $k$ 偶且 $k\le L$ 时，$d'=m-t-1\ge2$，比较 $M^m=M^{d'}M^{t+1}$ 的第一列，同样给

$$
vF_{t+1}-AF_t
=F_{d'}(F_{t+1}^2-F_tF_{t+2})
=(-1)^tF_{d'}=F_{m-t-1}.
$$

偶数对角 $k=L+1$ 则由 $t=m$ 及 Cassini 直接给

$$
vB_{\mathrm{num}}-A^2=1.
\tag{2.21}
$$

据式 (2.9) 的奇偶端点，前两种情形分别有

$$
Ar_k=v-\frac{F_{m-3k}}{F_{3k}},\qquad
Ar_k=v-\frac{F_{m-3k-1}}{F_{3k+1}}.
$$

整数 $v$ 满足 $\lceil v-x\rceil=v-\lfloor x\rfloor$，故得式 (2.18) 的前两分支。偶数对角由式 (2.21) 得 $Ar_k=v-1/B_{\mathrm{num}}$，因 $B_{\mathrm{num}}>1$，向上取整为 $v$。全过程不使用负索引 Fibonacci 数。

奇数分支饱和恰在 $F_{m-3k}<F_{3k}$。$m-3k=3(L+1-k)$ 或为零，或至少为三；$3k\ge3$，而 Fibonacci 数在指标至少二时严格递增。因此该不等式等价于 $m-3k<3k$，亦即 $2k>L+1$。偶数非对角分支饱和恰在 $F_{m-3k-1}<F_{3k+1}$；两个指标分别至少二和七，故等价于

$$
m-3k-1<3k+1
\quad\Longleftrightarrow\quad
6k>3L+1
\quad\Longleftrightarrow\quad
2k\ge L+1.
$$

偶数对角总已饱和，也满足最后的整数条件。由此证明式 (2.19)。由于 $F_{3k}F_{3k+1}$ 随 $k\ge1$ 严格增加，式 (2.9) 给宽度严格递减；取整后的碰撞预算可保持不变。

实际树 $T_*$ 的组成与叶数直接由 $c\rho=Mc$ 得出，且 $S^{-(L+1)}c_*=(1,0)$，所以 $h(c_*)\ge L+1$。又

$$
B_{\mathrm{num}}\le H<K_{k,L}
\le B_{\mathrm{num}}+v<F_{m+4}=N_{L+2}.
$$

定理 1.2 的最小祖先叶预算和式 (1.7) 排除任何 $D_H$ 组成具有第 $L+2$ 个祖先，故 $h(c_*)=h_{\max}(H)=L+1$。式 (2.17) 的同域实际跨类点对同时给单位间距，证明式 (2.20)。这是同一 $c_*$ 同时达到该窗口的深度极大值并参与间距极小值，未把来自不同来源的两种极值强行合并。

轴点 $y_*=(B_{\mathrm{num}}+v,0)$ 与 $c_*$ 的差为 $(B_{\mathrm{num}},-A)$，故读数相等，轴点对 $k\ge1$ 非许可。两者最大叶数为 $B_{\mathrm{num}}+v$，正好是首次预算当且仅当式 (2.19) 成立。还可排除 $c_*$ 在非饱和域参与另一对更早的精确碰撞：任何同读数的不同非负点为 $c_*+z(B_{\mathrm{num}},-A)$。因 $c_*$ 的第二坐标恰为 $A$，$z>0$ 时只能有 $z=1$，得到 $y_*$；因 $v<B_{\mathrm{num}}$，$z<0$ 会使第一坐标为负。故 $c_*$ 的首次跨类碰撞预算总是 $B_{\mathrm{num}}+v$，只有饱和域才与 $K_{k,L}$ 重合。

式 (2.18) 的一个具体参数取值是 $L=3$，此时 $(A,B_{\mathrm{num}},v)=(144,233,89)$，$k=1,2,3,4$ 的首次碰撞预算分别为 $305,322,322,322$；其中 $W_2=1/104$、$W_3=1/1870$，锥宽不同而碰撞前沿相同。

另取 $L=1,H=17$，则 $(A,B_{\mathrm{num}},v)=(8,13,5)$，$K_{1,1}=17$、$K_{2,1}=18$。定理 1.4 给 $\chi_1$ 在此域精确失败，而定理 2.3 给全域 $\chi_2$ 统一恢复恰在 $E<1/2$。同域实际组成 $(4,8)$ 和 $(17,0)$ 都读出 $136$，但二者 $\chi_2$ 都为零：前者斜率 $1/2<r_2=8/13$，后者是非许可轴点。全域恢复的充分性来自定理 2.3，而非这个同标签点对。再取 $L=0,k=2,H=13=N_2$，则 $(5,8)=S^2(1,0)$ 许可，$(2,10)$ 的叶数为十二而小于 $N_2$，所以非法；两点同域且读数都是 $34$，给首次许可即碰撞的实际反例。上述比较均使用定义 1.1 的同一报告合同。证毕。

## 追加锚（本行以下为增补区）

## 3. 任意中间深度的许可噪声阶梯与共同实现预算

**定义 3.1（中间深度与方向预算）。** 沿用定义 1.1、2.1 的实际非空有序完全二叉树、全局替换 $\rho$、初始组成域 $D_H$ 与单个末端有理报告合同。以下固定整数 $L\ge2$、$2\le k\le L$，并记

$$
\begin{gathered}
t=3k,\qquad m=3L+3,\qquad
A=F_m,\qquad B_{\mathrm{num}}=F_{m+1},\\
a_0=F_{t-1},\qquad b_0=F_t,\qquad
N=F_{t+1}=a_0+b_0,\qquad Q=N+a_0,\\
r_k=\min\{a_0/b_0,b_0/N\},\qquad
R_k=\max\{a_0/b_0,b_0/N\},\qquad
K=B_{\mathrm{num}}+\lceil Ar_k\rceil.
\end{gathered}
\tag{3.1}
$$

这里 $N=N_k$、$K=K_{k,L}$ 分别复用式 (2.9)、(2.10)。对所有整数 $j\ge t-2$，定义

$$
C_{k,j}=
\begin{cases}
N,&j=t-2,\\
2b_0,&j=t-1,\\
F_{j+1}+\lceil r_kF_j\rceil,&j\ge t.
\end{cases}
\tag{3.2}
$$

将式 (2.1) 的 $\chi_k$ 仍定义在全部非零非负整数组成上。差方向的最小共同实际来源叶预算为

$$
\mathfrak B_{k,j}=
\min_{\substack{x,y\in\mathbb N_0^2\setminus\{0\}\\
\chi_k(x)\ne\chi_k(y),\ y-x=\pm(F_{j+1},-F_j)}}
\max\{|x|_1,|y|_1\}.
\tag{3.3}
$$

组成点的实际来源均取自定义 1.1 的树域；祖先树只作存在见证，不成为观察输入。$H$ 只界定初始来源叶数，末端仍恰好经过 $3L$ 次 $\rho$。$k=1$ 的全部分支引用定理 2.2，$k=L+1$ 与 $k\ge L+2$ 的全部分支引用定理 2.3；以下不重证这些深度。

**定理 3.2（全部 Fibonacci 方向的尖锐共同预算）。** 在定义 3.1 的条件下，对每个整数 $j\ge t-2$，式 (3.3) 的集合非空，最小值存在且

$$
\boxed{\mathfrak B_{k,j}=C_{k,j}.}
\qquad
C_{k,t}=Q,\quad C_{k,m}=K,\quad N<2b_0<Q.
\tag{3.4}
$$

$C_{k,j}$ 在 $j\ge t$ 上严格递增。该方向预算结论不要求 $j\le m$。当 $t-2\le j\le m$ 时，下面构造的跨类点对还满足

$$
|n_L(y)-n_L(x)|=F_{m-j}.
\tag{3.5}
$$

证明。由式 (2.9)，非零许可点恰为 $S^k(p,q)$，其中 $(p,q)\in\mathbb N_0^2\setminus\{0\}$，其叶数为

$$
|S^k(p,q)|_1=Np+F_{t+2}q.
\tag{3.6}
$$

由于 $t\ge6$，Fibonacci 递推给

$$
\begin{aligned}
2b_0-N&=b_0-a_0=F_{t-2}>0,\\
Q-2b_0&=2a_0-b_0=F_{t-3}>0,\\
2N-Q&=b_0>0,\\
F_{t+2}-Q&=b_0-a_0>0.
\end{aligned}
\tag{3.7}
$$

所以 $N<2b_0<Q<\min\{2N,F_{t+2}\}$。由式 (3.6)，叶数严格小于 $Q$ 的许可组成只能是

$$
x_0=(a_0,b_0)=S^k(1,0).
\tag{3.8}
$$

此处唯一的是组成，不是实现它的实际树；$\rho^t(\alpha)$ 是其中一个见证。任意非零许可点的叶数至少为 $N$。

先给任意异号方向的必要预算。令 $u>w>0$ 为整数，许可点为 $x=(a,b)$，另一点为 $y=x\pm(u,-w)$，两点均非零非负。由式 (2.9)，$0<r_k\le R_k<1$ 且 $r_kb\le a\le R_kb$。正方向时 $b\ge w$，又因 $u>w$，最大叶数是 $|y|_1$，故

$$
\max\{|x|_1,|y|_1\}
=a+b+u-w\ge u+r_kw.
\tag{3.9}
$$

负方向时 $a\ge u$，最大叶数是 $|x|_1$，并且

$$
\max\{|x|_1,|y|_1\}
=a+b\ge(1+1/R_k)u>2u>u+r_kw.
\tag{3.10}
$$

两种方向都给共同整数预算至少 $u+\lceil r_kw\rceil$。这只是必要条件；此处没有断言对任意 $u,w$ 都存在达到该预算的许可点。

对于 $j=t-2$，任何跨类点对都包含许可点，故共同预算至少为 $N$。取 $x_0$ 和

$$
y_0=(0,b_0+F_{t-2}),\qquad
y_0-x_0=-(F_{t-1},-F_{t-2}).
\tag{3.11}
$$

$y_0$ 是非许可纵轴点；因 $F_{t-2}<a_0$，两点的最大叶数恰为 $N$。所以 $\mathfrak B_{k,t-2}=N$。

对于 $j=t-1$，取 $x_0$ 和

$$
y_1=(N,F_{t-2}),\qquad
y_1-x_0=(F_t,-F_{t-1}),\qquad |y_1|_1=2b_0.
\tag{3.12}
$$

$N>F_{t-2}>0$，而许可点的第一坐标严格小于第二坐标，故 $y_1$ 非许可。这对来源的共同预算为 $2b_0$。若有此方向的跨类点对共同预算严格小于 $2b_0<Q$，则其许可端点由式 (3.8) 只能是 $x_0$。负方向会使第一坐标为 $a_0-b_0<0$；正方向只能得到式 (3.12) 的 $y_1$，其叶数已经是 $2b_0$，矛盾。因此 $\mathfrak B_{k,t-1}=2b_0$。

对全部 $j\ge t$，直接使用[母卷命题 105.2 证明中的经典 Fibonacci 矩阵幂](FIBONACCI_ATOMIC_RELATION_GENERATION.md#1052-标量返回位置构成循环相位的子群)，令 $e_1=(1,0)^{\mathsf T}$。有

$$
M^je_1=(F_{j-1},F_j)^{\mathsf T}
=S^kM^{j-t}e_1.
\tag{3.13}
$$

$M^{j-t}e_1$ 为非零非负整数祖先，其中 $j=t$ 时取 $M^0=I$。于是式 (2.9) 给

$$
r_kF_j\le F_{j-1}\le R_kF_j,\qquad
r_kF_j\le a_j:=\lceil r_kF_j\rceil
\le F_{j-1}\le R_kF_j.
\tag{3.14}
$$

因此

$$
x_j=(a_j,F_j),\qquad y_j=(a_j+F_{j+1},0)
\tag{3.15}
$$

分别许可与非许可，且差为 $(F_{j+1},-F_j)$。两点的最大叶数是 $F_{j+1}+a_j=C_{k,j}$。必要预算式 (3.9)、(3.10) 用于 $u=F_{j+1}>F_j=w$，给出反向下界，故式 (3.4) 对全部 $j\ge t$ 成立。

当 $k$ 奇数时，式 (2.9) 给 $r_kb_0=a_0$；当 $k$ 偶数时，Cassini 等式给 $a_0N-b_0^2=1$，因而

$$
r_kb_0=b_0^2/N=a_0-1/N,\qquad
\lceil r_kb_0\rceil=a_0.
\tag{3.16}
$$

所以两种奇偶情形都有 $x_t=x_0$、$y_t=(Q,0)$，以及 $C_{k,t}=Q$。定义又直接给 $C_{k,m}=B_{\mathrm{num}}+\lceil r_kA\rceil=K$。对 $j\ge t$，由于 $r_k>0$ 且 $F_{j+1}>F_j$，

$$
C_{k,j+1}-C_{k,j}
=F_j+\lceil r_kF_{j+1}\rceil-\lceil r_kF_j\rceil
\ge F_j>0.
\tag{3.17}
$$

这证明严格递增；结合式 (3.7)，全部已定义预算按指标递增，并且趋向无穷。

上述每个非零非负组成都能由定义 1.1 的实际完整树实现。对于许可 $x$，整数祖先 $S^{-k}x$ 非零非负，先构造其完整树，再施加 $\rho^t$ 即给一个组成为 $x$ 的代表；非许可点可直接按其叶组成加完整括号实现。这只建立存在见证，不把任意指定括号判为替换像，也不增添逆操作或观察通道。对 $j\le m$，在式 (1.8) 中使用相应指标，所列差方向的末端残差绝对值就是 $F_{m-j}$，包括 $j=m$ 的零值，得到式 (3.5)。当 $j>m$ 时，式 (3.4) 仍是共同叶预算结论，不使用负索引 Fibonacci 数。证毕。

**定理 3.3（任意中间深度的完整最优噪声阶梯）。** 在定义 3.1 的同一来源、响应和许可合同下，对每个整数 $H\ge1$，

$$
\boxed{
\delta_k(H,L)=
\begin{cases}
+\infty,&H<N,\\
F_{m-t+2},&N\le H<2b_0,\\
F_{m-t+1},&2b_0\le H<Q,\\
F_{m-j},&Q\le H<K,\quad
j=\max\{i\ge t:C_{k,i}\le H\},\\
0,&H\ge K.
\end{cases}}
\tag{3.18}
$$

第四分支的最大指标存在且满足 $t\le j\le m-1$。所有有限分支均由同一个 $D_H$ 内的两棵实际初始来源树达到。

证明。$H<N$ 时，式 (2.9) 已排除许可点，所以跨类集合为空。$H\ge K$ 的零间距分支直接复用式 (2.10) 与其实际碰撞点对。余下证明不假定任意差方向是 Fibonacci 方向。

对任意不同点对，若差坐标同号或其中一个为零，数量差的绝对值至少为 $A$。若差坐标异号，则取其正负坐标绝对值 $(u,w)$，$u,w>0$，其数量差绝对值为 $|Au-B_{\mathrm{num}}w|$。当 $u\le w$ 时，

$$
|Au-B_{\mathrm{num}}w|
=B_{\mathrm{num}}w-Au
\ge(B_{\mathrm{num}}-A)w\ge F_{m-1}.
\tag{3.19}
$$

以下候选阶梯的最大值 $F_{m-t+2}$ 不超过 $F_{m-1}<A$；因而上述差类型均不会小于候选值。只需处理 $u>w>0$ 的任意整数方向，并把许可端点记为 $x$，另一端点写成 $x\pm(u,-w)$。

为给这些方向统一下界，直接复用式 (1.8) 的整数基

$$
w_j=(F_{j+1},F_j),\qquad
w_{j+1}=(F_{j+2},F_{j+1}),\qquad
\det(w_j,w_{j+1})=(-1)^j.
$$

对 $t-2\le j\le m-1$，任意整数 $(u,w)$ 唯一展开为 $p w_j+s w_{j+1}$，$p,s\in\mathbb Z$。置 $f=F_{m-j}\ge1$、$g=F_{m-j-1}\ge0$，式 (1.8) 给

$$
Au-B_{\mathrm{num}}w=(-1)^j(pf-sg).
\tag{3.20}
$$

设实线性泛函 $\ell$ 在 $w_j,w_{j+1}$ 上均为正，并有 $\ell(u,w)<\ell(w_{j+1})$。当 $p,s\ge0$ 时，严格上界强制 $s=0$；随后 $u>0$ 强制 $p\ge1$，残差绝对值至少为 $f$。当 $p,s\le0$ 时，因两基向量的第一坐标为正，$u\le0$，不可能。当 $p\ge0,s<0$ 时，$u>0$ 强制 $p\ge1$，残差绝对值为 $pf+|s|g\ge f$。当 $p<0,s\ge0$ 时，$u>0$ 强制 $s\ge1$，残差绝对值为 $|p|f+sg\ge f$。四种符号情形覆盖全部整数展开，包含零系数；末档 $j=m-1$ 的 $g=F_0=0$ 也仍满足这些不等式。由此得到

$$
\ell(w_j)>0,\quad\ell(w_{j+1})>0,\quad
\ell(u,w)<\ell(w_{j+1})
\quad\Longrightarrow\quad
|Au-B_{\mathrm{num}}w|\ge F_{m-j}.
\tag{3.21}
$$

这一用法只要求 $\ell$ 在所选两个基向量上为正，不要求它在整个正象限为正。

先设 $N\le H<Q$。定理 3.2 的式 (3.8) 强制许可端点为 $x_0$。若另一点为 $y=x_0-(u,-w)$，非负性给 $u\le a_0<b_0$。在式 (3.21) 中取 $j=t-2$ 和 $\ell(u,w)=u$，两基上的值为 $a_0,b_0>0$，故

$$
|n_L(y)-n_L(x_0)|\ge F_{m-t+2}.
\tag{3.22}
$$

该下界同时覆盖这两个早期分支的负方向。

若 $y=x_0+(u,-w)$，因为 $u>w$，$|y|_1=N+u-w\le H$，所以 $u-w\le H-N$。当 $N\le H<2b_0$ 时，

$$
u-w\le H-N<2b_0-N=F_{t-2}.
\tag{3.23}
$$

取 $j=t-2$ 和 $\ell(u,w)=u-w$；两基上的值分别是 $F_{t-3}>0$ 和 $F_{t-2}>0$。式 (3.21) 给读数差至少 $F_{m-t+2}$，而式 (3.11) 的点对在共同预算 $N$ 达到此值。结合式 (3.19)、(3.22) 及同号差下界，得到式 (3.18) 的第二分支。

当 $2b_0\le H<Q$ 时，同样有

$$
u-w\le H-N<Q-N=a_0=F_{t-1}.
\tag{3.24}
$$

这次取 $j=t-1$ 和 $\ell(u,w)=u-w$；两基上的正值为 $F_{t-2}$、$F_{t-1}$，式 (3.21) 给下界 $F_{m-t+1}$。负方向的式 (3.22) 更强，其他差类型的式 (3.19) 和 $A$ 下界亦足够。式 (3.12) 的同域点对在共同预算 $2b_0$ 达到 $F_{m-t+1}$，得到第三分支。

最后设 $Q\le H<K$。由 $C_{k,t}=Q$、$C_{k,m}=K$ 和严格递增趋向无穷，最大指标 $j$ 存在且

$$
t\le j\le m-1,\qquad C_{k,j}\le H<C_{k,j+1}.
\tag{3.25}
$$

取 $\ell(u,w)=u+r_kw$。式 (3.9)、(3.10) 给任意实际跨类点对的 $\ell(u,w)\le H$，两基上的 $\ell$ 均为正。又因 $F_{j+2}$ 是整数，

$$
C_{k,j+1}
=\left\lceil F_{j+2}+r_kF_{j+1}\right\rceil
=\lceil\ell(w_{j+1})\rceil.
$$

整数 $H<\lceil\ell(w_{j+1})\rceil$ 意味着
$H\le\lceil\ell(w_{j+1})\rceil-1<\ell(w_{j+1})$，于是

$$
\ell(u,w)\le H<\ell(w_{j+1}).
\tag{3.26}
$$

式 (3.21) 对全部这类整数方向给下界 $F_{m-j}$；其他差类型也已给不小于它的下界。定理 3.2 的式 (3.15) 在共同预算 $C_{k,j}\le H$ 达到该值，故第四分支准确。这里包含 $j=m-1$，没有排除 $g=0$ 或并列单位残差。所有达到点均由定理 3.2 的实际树存在见证实现；它们共享同一个初始域和报告合同。证毕。

**定理 3.4（最早单位间距与准确闭噪声边界）。** 在定义 3.1 的条件下，令

$$
U=C_{k,m-2}=F_{m-1}+\lceil r_kF_{m-2}\rceil.
\tag{3.27}
$$

则

$$
\boxed{Q<U<A<B_{\mathrm{num}},\qquad
\delta_k(H,L)=1\ \Longleftrightarrow\ U\le H<K.}
\tag{3.28}
$$

对每个整数 $H\ge1$ 与每个已知有理数 $E\ge0$，统一恢复 $\chi_k$ 的准确条件为

$$
\boxed{2E<\delta_k(H,L)}
\qquad\Longleftrightarrow\qquad
2\eta<\lambda^{-L}\delta_k(H,L).
\tag{3.29}
$$

$+\infty$ 分支允许任意有限 $E$；零间距分支在 $E=0$ 也失败；全部有限正间距分支在等号处失败。

证明。$m-t=3(L+1-k)\ge3$，所以 $m-2\ge t+1$。由定理 3.2 的严格递增，$U>C_{k,t}=Q$。在式 (3.14) 中取 $j=m-2$，得 $\lceil r_kF_{m-2}\rceil\le F_{m-3}$，故

$$
U\le F_{m-1}+F_{m-3}
<F_{m-1}+F_{m-2}=A<B_{\mathrm{num}}.
\tag{3.30}
$$

这里 $m\ge9$，严格不等式无重复初值问题。

定理 3.3 的前两个有限间距分别至少为 $F_5=5$ 与 $F_4=3$。其第四分支中，若 $j\le m-3$，则 $F_{m-j}\ge F_3=2$；若 $j=m-2$ 或 $j=m-1$，则分别为 $F_2=1$ 和 $F_1=1$。因此相邻的两档

$$
[\,C_{k,m-2},C_{k,m-1}\,),\qquad
[\,C_{k,m-1},C_{k,m}\,)
\tag{3.31}
$$

都有单位间距。预算严格递增，所以首次出现于 $m-2$ 档的 $U$，不是 $m-1$ 档；合并这两档即得式 (3.28)。$H<N$ 的间距是无穷，$H\ge K$ 的间距是零，均不会增添单位间距预算。

恢复条件直接应用定理 2.2 证明中已经给出的闭候选标签纤维论证，候选仍取定理 1.2 的 $\mathcal C(r)$，目标改为同一 $\chi_k$。若 $2E<\delta_k$，每个非空候选集具有共同标签，输出该标签、空集输出零就是统一恢复器。$H<N$ 时没有许可点，常值零恢复器对任意有限 $E$ 有效。有限跨类集合非空时，定理 3.3 给达到最小值的同域实际点对 $x,y$；其共同有理中点

$$
r_*=[n_L(x)+n_L(y)]/2\in\mathbb Q
\tag{3.32}
$$

到两真值的距离都是 $\delta_k/2$。只要 $2E\ge\delta_k$，该报告就同时允许两个相反标签，任何统一恢复器都失败。因此等号属于失败侧；$\delta_k=0$ 时共同报告已精确，$E=0$ 仍失败。已知的正数 $\lambda^{-L}$ 缩放不增加信息，给式 (3.29) 的归一化形式。祖先树、括号、叶标签、规范地址和早先读数均未加入恢复输入。恢复的是组成祖先许可，不是指定完整树的语法祖先，也不是实际逆执行；环境坐标上的代数守恒仍不承担物理对应。证毕。

**命题 3.5（加权必要成本不是早期共同实现的充分条件）。** 对 $L=k=2$，有

$$
\begin{gathered}
t=6,\quad m=9,\quad A=34,\quad B_{\mathrm{num}}=55,\\
a_0=5,\quad b_0=8,\quad N=13,\quad Q=18,\quad
r_2=8/13,\quad R_2=5/8,\quad K=76.
\end{gathered}
\tag{3.33}
$$

方向 $(8,-5)$ 满足必要加权成本

$$
8+r_2\cdot5=144/13<13,
\tag{3.34}
$$

但这个方向的实际跨 $\chi_2$ 点对最小共同预算是 $16$，不是 $13$。同一合同的完整间距为

$$
\boxed{
\delta_2(H,2)=
\begin{cases}
+\infty,&H<13,\\
5,&13\le H<16,\\
3,&16\le H<18,\\
2,&18\le H<29,\\
1,&29\le H<76,\\
0,&H\ge76.
\end{cases}}
\tag{3.35}
$$

因此该反例否定的是把必要加权成本当作早期充分性的推断，不否定定理 3.3 的阶梯。

证明。上述数值直接来自 Fibonacci 递推；$K=55+\lceil34\cdot8/13\rceil=76$。在 $H=13<Q$，式 (3.8) 给唯一许可组成为 $(5,8)$。沿方向 $(8,-5)$ 的负向端点为 $(-3,13)$，不在非负组成域；正向端点为 $(13,3)$，非许可且叶数为 $16$。所以即使式 (3.34) 已满足，$D_{13}$ 内也没有该方向的实际跨类点对。定理 3.2 的 $j=t-1=5$ 分支给方向最小预算 $2b_0=16$，由 $(5,8),(13,3)$ 达到。

必要成本所提示的取整纵坐标锚为

$$
(\lceil r_2\cdot5\rceil,5)=(4,5).
$$

但 $4/5>R_2=5/8$，它不在许可锥内。缺失的是同一整数许可来源的共同实现，不能用仅有下边界加权不等式补足上边界。

式 (3.2) 给

$$
C_{2,6}=18,\qquad C_{2,7}=29,\qquad
C_{2,8}=47,\qquad C_{2,9}=76.
\tag{3.36}
$$

定理 3.3 在前两档的残差分别为 $F_5=5$、$F_4=3$，后三个方向的残差依次为 $F_3=2,F_2=1,F_1=1$，于是合并相邻单位档便得式 (3.35)。第一档可见证为 $(5,8),(0,11)$，共同预算 $13$，读数分别为 $610,605$；第二档为 $(5,8),(13,3)$，共同预算 $16$，读数分别为 $610,607$。后续达到点及全整数方向的下界已由定理 3.2、3.3 给出，这些具体数值不替代其无界指标与全方向证明。证毕。

## 追加锚（本行以下为增补区）

## 4. 隐藏阶段的整数纤维与初始许可首次失效

**定义 4.1（两阶段联合来源与初始许可目标）。** 沿用定义 1.1 的非空有限有序完全二叉树、叶标签、全局替换 $\rho$ 及初始组成 $c(T)$。以下对每个 $\ell\in\mathbb N_0$、$d,k,H\in\mathbb N_{\ge1}$ 和已知 $E\in\mathbb Q_{\ge0}$，联合来源恰为

$$
\begin{gathered}
\mathcal T_H\times\{\ell,\ell+d\},\qquad
D_H=\{(a,b)\in\mathbb N_0^2:1\le a+b\le H\},\\
\mathcal E^{\mathrm{hid}}_{H,k,\ell,d,E}
=\{((T,s),r):T\in\mathcal T_H,\ s\in\{\ell,\ell+d\},
r\in\mathbb Q,\ |r-qS^sc(T)|\le E\},\\
S=\begin{pmatrix}1&2\\2&3\end{pmatrix}=M^3,\qquad q=(2,3),\qquad
\chi_k(c(T))=\mathbf1_{\{S^{-k}c(T)\in\mathbb N_0^2\}}.
\end{gathered}
\tag{4.1}
$$

阶段 $s$ 表示报告前恰好进行 $3s$ 次 $\rho$。参数 $\ell,d,k,H,E$ 已知，实际选择的 $s$ 隐藏；唯一观察是未归一化的有理标量 $r$。观察不含 $s$、依赖实际 $s$ 的归一化、祖先记录、叶地址或第二通道。统一恢复指存在同一个 $P:\mathbb Q\to\{0,1\}$，使式 (4.1) 中每个允许响应都满足 $P(r)=\chi_k(c(T))$。预算 $H$ 同时限制两个阶段各自的初始树，替换中的树及末端树可超过 $H$。目标取报告前选定的初始组成，而非末端组成；许可仍仅表示组成祖先的存在，不判定指定树的语法祖先或实际逆执行。

记 $e_1=(1,0)^{\mathsf T}$，并对 $L,j\in\mathbb N_0$ 设

$$
\begin{gathered}
A_L=F_{3L+3},\qquad B_L=F_{3L+4},\qquad
n_L=qS^L=(A_L,B_L),\qquad v_L=B_L-A_L>0,\\
N_j=F_{3j+1},\qquad
r_k=\min\left\{\frac{F_{3k-1}}{F_{3k}},\frac{F_{3k}}{F_{3k+1}}\right\},\qquad
R_k=\max\left\{\frac{F_{3k-1}}{F_{3k}},\frac{F_{3k}}{F_{3k+1}}\right\}.
\end{gathered}
\tag{4.2}
$$

$N_0=1$，而 $S^je_1=(F_{3j-1},F_{3j})^{\mathsf T}$ 只用于 $j\ge1$；$j=0$ 时取 $e_1$。以下首次跨阶段反标签碰撞预算与联合无噪首次失效预算分别记为

$$
\begin{aligned}
J_{k,\ell,d}
&=\min_{\substack{x,y\in\mathbb N_0^2\setminus\{0\}\\
\chi_k(x)\ne\chi_k(y),\ n_\ell(x)=n_{\ell+d}(y)}}
\max\{|x|_1,|y|_1\},\\
G_{k,\ell,d}
&=\min\{H\ge1:\text{式 (4.1) 在 }E=0\text{ 时不存在统一恢复器 }P\}.
\end{aligned}
\tag{4.3}
$$

其中 $x$ 始终是低阶段初始组成，$y$ 始终是高阶段初始组成；两者许可标签的方向不预先指定。两个最小值的存在性由定理 4.3、4.4 给出。

有限族中实际线性映射未知的观察形态参见 Manolis C. Tsakiris 与 Liangzu Peng，[*Homomorphic Sensing*, PMLR 97 (2019)，6335–6344，§1.2、§2.2 与 Definition 1](https://proceedings.mlr.press/v97/tsakiris19a/tsakiris19a.pdf)。该文的对象是已知线性子空间上的向量与有限族线性自映射，恢复目标是完整向量；其通用位置子空间保证带有维数和余维条件。本节的 $D_H$ 是受预算约束的非负整数三角域，两条数量行有固定 Fibonacci 结构，目标是闭锥二值标签。因此这里只借用有限族未知映射的对应，不以其完整向量恢复定理推出本节的整数预算阈值。[来源联合完成卷定义 1.1、2.1 与 §5](FIB_SOURCE_COMPLETION_DYNAMICS.md#5-合法前缀完整共同尾与带时差群胚) 的对象则是规范地址与 profinite 算术坐标；其共同尾同时保留符号尾、算术尾、合法前缀域和长度差，不能充当式 (4.1) 中缺失的阶段观察。

**引理 4.2（完整整数仿射纤维、共同预算与闭许可区间）。** 在定义 4.1 的条件下，对任意非零非负整数组成 $y$，写 $S^dy=(a,b)^{\mathsf T}$、$Q=a+b$。满足跨阶段读数等式的全部整数解，且仅有这些解，是

$$
n_\ell(x)=n_{\ell+d}(y)
\quad\Longleftrightarrow\quad
x=x_z=(a+zB_\ell,b-zA_\ell)^{\mathsf T},\qquad z\in\mathbb Z.
\tag{4.4}
$$

若 $|y|_1\le H$，则 $x_z\in D_H$ 的允许参数准确为 $\mathbb Z\cap I_H(y)$，其中

$$
I_H(y)=
\left[
\max\left\{\left\lceil\frac{-a}{B_\ell}\right\rceil,
\left\lceil\frac{1-Q}{v_\ell}\right\rceil\right\},
\min\left\{\left\lfloor\frac b{A_\ell}\right\rfloor,
\left\lfloor\frac{H-Q}{v_\ell}\right\rfloor\right\}
\right].
\tag{4.5}
$$

左端大于右端时此区间为空；若 $|y|_1>H$，该 $y$ 没有共同预算内的联合来源对。在允许区间内，$\chi_k(x_z)=1$ 当且仅当 $z\in P_k(y)$，其中闭许可参数区间为

$$
P_k(y)=
\left[
\left\lceil\frac{r_kb-a}{B_\ell+r_kA_\ell}\right\rceil,
\left\lfloor\frac{R_kb-a}{B_\ell+R_kA_\ell}\right\rfloor
\right].
\tag{4.6}
$$

因而给定预算内的全部反标签跨阶段解准确对应

$$
\begin{cases}
\mathbb Z\cap I_H(y)\cap P_k(y),&\chi_k(y)=0,\\
\mathbb Z\cap\bigl(I_H(y)\setminus P_k(y)\bigr),&\chi_k(y)=1.
\end{cases}
\tag{4.7}
$$

这些式子包括 $z=0$、正负两向平移及许可锥的两个闭端点。

证明。$n_{\ell+d}=n_\ell S^d$，故读数相等当且仅当 $x-S^dy$ 属于 $n_\ell$ 的整数核。式 (1.12) 已给出 $\gcd(A_\ell,B_\ell)=1$ 和该核恰为 $\mathbb Z(B_\ell,-A_\ell)$，直接得到式 (4.4)，不删除任何整数平移。两个坐标非负分别要求 $z\ge\lceil-a/B_\ell\rceil$、$z\le\lfloor b/A_\ell\rfloor$；其叶数是 $Q+zv_\ell$，非空与预算上界分别要求 $z\ge\lceil(1-Q)/v_\ell\rceil$、$z\le\lfloor(H-Q)/v_\ell\rfloor$。四项相交恰给式 (4.5)。

复用式 (2.9) 的闭锥判据，将 $r_k(b-zA_\ell)\le a+zB_\ell\le R_k(b-zA_\ell)$ 分别解为 $z$ 的下界和上界。两个分母严格为正，整数取整即为式 (4.6)。允许点已经非零且非负；若许可区间内的第二坐标为零，上边界会强制第一坐标也为零，与非空性矛盾，故式 (2.9) 的 $b_z>0$ 无须另加条件。固定 $y$ 的标签后，取许可区间或其在允许区间内的补集即得式 (4.7)，因此两种标签方向均完整。证毕。

**定理 4.3（跨阶段首次反标签碰撞的尖锐预算）。** 对所有 $k,d\ge1$、$\ell\ge0$，式 (4.3) 的跨阶段最小值存在，且

$$
\boxed{
J_{k,\ell,d}=
\begin{cases}
N_k,&1\le d\le k,\\
N_d-\tau_{k,\ell,d}v_\ell,&d>k,
\end{cases}\qquad
\tau_{k,\ell,d}=
\left\lfloor\frac{a_d-r_kb_d}{B_\ell+r_kA_\ell}\right\rfloor,
\quad a_d=F_{3d-1},\quad b_d=F_{3d},}
\tag{4.8}
$$

其中 $\tau_{k,\ell,d}$ 只在 $d>k$ 分支使用。在该分支，唯一达到最小值的有序组成对为

$$
(x,y)=\bigl(x_{\min},e_1\bigr),\qquad
x_{\min}=(a_d-\tau_{k,\ell,d}B_\ell,
 b_d+\tau_{k,\ell,d}A_\ell)^{\mathsf T}.
\tag{4.9}
$$

$x_{\min}$ 的两个坐标严格为正，且在闭 $k$ 许可锥内。唯一性仅针对组成对，不针对完整树形。$d\le k$ 分支不主张全部最小组成对唯一；两个分支的极小预算均由实际有限初始树达到。

证明。先设 $1\le d\le k$。任一反标签对包含许可组成，式 (2.9) 给其叶数至少为 $N_k$，故 $J_{k,\ell,d}\ge N_k$。取

$$
x=S^ke_1,\qquad y=S^{k-d}e_1,
\qquad n_\ell(x)=n_{\ell+d}(y),\qquad
|x|_1=N_k,\quad |y|_1=N_{k-d}\le N_k.
\tag{4.10}
$$

对每个 $j\ge0$，$S^je_1$ 的前 $j$ 次组成逆步非负，而再一步给 $S^{-1}e_1=(-3,2)^{\mathsf T}$。许可锥嵌套保证不存在更深的非负祖先，故定理 1.2 中的 $h(S^je_1)=j$。于是式 (4.10) 中 $x$ 许可、$y$ 非许可，下界达到，包括 $d=k$ 时 $y=e_1$ 的端点。

这一最小预算处的反向标签不能发生。若高阶段 $y$ 许可，则 $y=S^ku$，$u$ 是非零非负整数向量，从而

$$
\begin{aligned}
n_{\ell+d}(y)&\ge A_{\ell+d+k}\ge A_{\ell+k+1}
=n_\ell(S^{k+1}e_1)\\
&=A_\ell F_{3k+2}+B_\ell F_{3k+3}
>B_\ell N_k.
\end{aligned}
\tag{4.11}
$$

最后的严格不等式来自 $F_{3k+3}>F_{3k+1}=N_k$。低阶段的任何 $x\in D_{N_k}$ 却满足 $n_\ell(x)\le B_\ell N_k$，所以高阶段许可、低阶段非许可的对不能在预算 $N_k$ 或以下碰撞。这不排除同一预算内其他高阶段非许可最小组成对。

再设 $d>k$。先排除高阶段 $y\ne e_1$ 的全部来源，不预设其标签。对每个 $L\ge0$，Fibonacci 递推给 $A_L<B_L<2A_L$。若 $y$ 的第二坐标为正，其读数至少为 $B_{\ell+d}$；若第二坐标为零，$y\ne e_1$ 使第一坐标至少为二，读数至少为 $2A_{\ell+d}>B_{\ell+d}$。矩阵幂及行乘法给

$$
B_{\ell+d}=A_\ell b_d+B_\ell N_d>B_\ell N_d.
\tag{4.12}
$$

故与这种 $y$ 碰撞的低阶段 $x$ 必满足 $B_\ell|x|_1\ge n_\ell(x)=n_{\ell+d}(y)>B_\ell N_d$，即 $|x|_1>N_d$。这同时排除了高阶段许可的反向标签，因为 $e_1$ 本身非许可，也排除了全部其他高阶段非许可来源在 $N_d$ 或以下达到极小值。

剩余高阶段来源是 $y=e_1$，其标签为零。$S^de_1$ 在 $k$ 许可锥严格内部：$S^{-k}S^de_1=S^{d-k}e_1$ 的两个坐标严格为正，而 $S^k$ 把正正象限送入两条边界之间。因此

$$
a_d-r_kb_d>0,\qquad R_kb_d-a_d>0.
\tag{4.13}
$$

令 $\tau=\tau_{k,\ell,d}\ge0$。引理 4.2 中的许可参数区间，此时左端为 $-\tau$，右端非负。$x_z$ 的叶数为 $N_d+zv_\ell$，随整数 $z$ 严格递增，故许可纤维中最小叶数候选恰为式 (4.9) 的 $x_{\min}=x_{-\tau}$。

该候选确为允许的非空整数点，并同时满足两条锥边界。因为 $r_k>0$，

$$
0\le\tau\le\frac{a_d-r_kb_d}{B_\ell+r_kA_\ell}
<\frac{a_d}{B_\ell},
\tag{4.14}
$$

所以其第一坐标严格为正，第二坐标也严格为正。由取整定义，

$$
(a_d-\tau B_\ell)-r_k(b_d+\tau A_\ell)
=(a_d-r_kb_d)-\tau(B_\ell+r_kA_\ell)\ge0.
\tag{4.15}
$$

另一方面，其坐标比不超过 $a_d/b_d<R_k$，故上边界成立。式 (4.15) 的等号是合法的闭端点；$z=-\tau-1$ 则严格越过下边界。所有更负平移、正平移及越过上边界的情形均由式 (4.5)–(4.7) 纳入或排除，没有遗漏另一个核方向。于是该纤维的最小共同预算是 $|x_{\min}|_1=N_d-\tau v_\ell\le N_d$。式 (4.12) 已使全部 $y\ne e_1$ 的碰撞成本严格大于 $N_d$，因此这一候选给全域下界及达到性，证明式 (4.8)。叶数随 $z$ 严格增加，又证明 $d>k$ 时极小有序组成对唯一。

达到点均可取为定义 1.1 的实际初始树。$d\le k$ 时，式 (4.10) 分别由 $T_{\mathrm{low}}=\rho^{3k}(\alpha)$ 与 $T_{\mathrm{high}}=\rho^{3(k-d)}(\alpha)$ 达到；这两棵树再按各自选择的报告阶段进行替换。$d>k$ 时取高阶段初始树为单叶 $\alpha$。由于 $S^{-k}$ 是整数矩阵且 $x_{\min}$ 在闭许可锥内，$u=S^{-k}x_{\min}$ 是非零非负整数向量。用定义 1.1 的完整二叉括号实现 $u$ 为树 $U$，低阶段初始树取 $\rho^{3k}U$，其组成恰为 $x_{\min}$。初始叶数分别为 $J_{k,\ell,d}$ 和一。报告阶段的后续树可超过预算；这些树只作为存在见证，其历史和地址均不进入观察。证毕。

**定理 4.4（联合首次失效预算与全参数简式）。** 对定义 4.1 的全部参数，复用式 (2.10) 的同阶段阈值

$$
K_{k,L}=
\begin{cases}
B_L+\lceil A_Lr_k\rceil,&1\le k\le L+1,\\
N_k,&k\ge L+2.
\end{cases}
\tag{4.16}
$$

联合无噪首次失效预算准确为

$$
\boxed{
G_{k,\ell,d}=\min\{K_{k,\ell},K_{k,\ell+d},J_{k,\ell,d}\}
=\begin{cases}
N_{\max(k,d)},&\max(k,d)\le\ell+1,\\
K_{k,\ell},&\max(k,d)>\ell+1.
\end{cases}}
\tag{4.17}
$$

对每个整数 $H\ge1$，隐藏阶段下初始 $\chi_k$ 的统一无噪恢复存在，当且仅当 $H<G_{k,\ell,d}$。$H\ge G_{k,\ell,d}$ 的失败由实际有限初始树的精确反标签碰撞见证，对每个 $E\ge0$ 继续成立。

证明。两个反标签联合来源的阶段位置只有三种：同在 $\ell$，同在 $\ell+d$，或分别处在两个阶段。前两种首次共同预算直接是既有式 (2.10) 的 $K_{k,\ell}$ 与 $K_{k,\ell+d}$，第三种由定理 4.3 给 $J_{k,\ell,d}$。因此预算低于三者最小值时，每条非空精确观察纤维具有同一个目标标签；在非空纤维上取此标签，空纤维上取零，得到总函数 $P:\mathbb Q\to\{0,1\}$。这直接复用定理 2.3 证明中的目标纤维判据，不另立一般恢复定理。预算达到三者最小值时，相应实际初始树对具有同一个整数报告和不同正确标签，否定任意 $P$；更大的 $H$ 保留该对，任意非负 $E$ 也允许这个精确报告。由此证明式 (4.17) 的第一个等号及首次失效性质。

为证明全参数简式，先比较两个同阶段阈值。若 $k\ge\ell+2$，则 $K_{k,\ell}=N_k$；任何反标签对都含许可组成，其预算至少为 $N_k$，所以 $K_{k,\ell+d}\ge K_{k,\ell}$。若 $k\le\ell+1$，定理 2.3 的式 (2.13) 给 $A_\ell r_k\le v_\ell$，故

$$
K_{k,\ell}\le B_\ell+v_\ell<2B_\ell,
\qquad
K_{k,\ell+d}\ge B_{\ell+d}>2B_\ell.
\tag{4.18}
$$

后一严格不等式由 $d\ge1$ 及 $B_{\ell+1}=2A_\ell+3B_\ell$ 得到。于是所有参数都满足 $K_{k,\ell+d}\ge K_{k,\ell}$。

设 $\max(k,d)\le\ell+1$。当 $d\le k$ 时，定理 4.3 给 $J=N_k$。当 $k<d$ 时，$N_d\le B_\ell$ 且 $a_d<N_d$，故式 (4.14) 的取整量满足 $0\le\tau<a_d/B_\ell<1$，即 $\tau=0$，于是 $J=N_d$。两个情形合为 $J=N_{\max(k,d)}\le B_\ell<K_{k,\ell}$，因此三者最小值就是式 (4.17) 的第一分支。

在其余参数中，若 $k\ge\ell+2$，则 $K_{k,\ell}=N_k$；同阶段和跨阶段的任一反标签对均有成本至少 $N_k$，所以三者最小值是 $K_{k,\ell}$。最后只余 $k\le\ell+1$、$d\ge\ell+2$。Fibonacci 递推给

$$
b_d\ge F_{3\ell+6}=A_\ell+2B_\ell,\qquad
A_{\ell+d}=A_\ell a_d+B_\ell b_d
>2B_\ell^2>B_\ell K_{k,\ell}.
\tag{4.19}
$$

每个非零高阶段来源的报告至少为 $A_{\ell+d}$，而共同预算不超过 $K_{k,\ell}$ 的低阶段来源报告至多为 $B_\ell K_{k,\ell}$，故此预算内甚至没有任何跨阶段相等报告，必有 $J_{k,\ell,d}>K_{k,\ell}$。结合高阶段同阶段阈值比较，三者最小值仍为 $K_{k,\ell}$。这覆盖所有参数并证明第二分支。证毕。

**推论 4.5（阶段参照的严格损失与非恒值窗口）。** 在定义 4.1 的同一初始树域上，若增加实际阶段 $s$ 的观察，则共同预算的无噪首次失效阈值为 $K_{k,\ell}$。隐藏该阶段参照严格降低首次失效预算的充要条件是

$$
\boxed{\quad G_{k,\ell,d}<K_{k,\ell}
\quad\Longleftrightarrow\quad\max(k,d)\le\ell+1.\quad}
\tag{4.20}
$$

联合目标在 $H<N_k$ 时恒为零，对所有 $E\ge0$ 均可统一恢复；在 $H\ge N_k$ 时非恒值。存在非恒值且可统一无噪恢复的共同预算，当且仅当 $k\le\ell+1$ 且 $d>k$。固定 $\ell,k$ 时，阶段差 $d$ 的完整零噪声窗口为

$$
\boxed{
\begin{array}{ll}
k\le\ell+1,\ 1\le d\le k:
 &G=N_k,\quad\text{不存在非恒值恢复预算};\\
k\le\ell+1,\ k<d\le\ell+1:
 &G=N_d,\quad N_k\le H<N_d;\\
k\le\ell+1,\ d\ge\ell+2:
 &G=K_{k,\ell},\quad N_k\le H<K_{k,\ell};\\
k\ge\ell+2,\ d\ge1:
 &G=N_k,\quad\text{不存在非恒值恢复预算}.
\end{array}}
\tag{4.21}
$$

因此 $d=1$ 对每个 $k\ge1$ 都使最早许可来源在隐藏阶段下已不能统一判定。$G$ 对固定 $\ell,k$ 随 $d$ 非减；当 $k\le\ell+1$ 时，它在 $d\ge\ell+2$ 达到并保持已知阶段的阈值。这些是替换阶段差的陈述；$d$ 只计 $3d$ 次替换的差，不给物理时钟、实际流逝时间或逆执行解释。

证明。增加 $s$ 后，可分别在两个阶段的精确纤维上取目标标签，所以共同预算首次失效为 $\min\{K_{k,\ell},K_{k,\ell+d}\}=K_{k,\ell}$，其中阈值比较已由定理 4.4 证明。若 $\max(k,d)\le\ell+1$，式 (4.17) 给 $G=N_{\max(k,d)}\le B_\ell<K_{k,\ell}$；否则 $G=K_{k,\ell}$，证明式 (4.20)。

式 (2.9) 的最小许可预算是 $N_k$，故 $H<N_k$ 时输出零对每个误差合同都正确。$H\ge N_k$ 时，实际树 $\rho^{3k}(\alpha)$ 许可，而单叶 $\alpha$ 非许可，两者均在初始域内，证明非恒值。于是非恒值无噪窗口恰为整数预算 $N_k\le H<G$。将定理 4.4 的两分支按 $k,d$ 的相对位置展开即得式 (4.21)。当 $k\le\ell+1$ 时，$K_{k,\ell}>B_\ell\ge N_k$，而 $N_d>N_k$ 当且仅当 $d>k$，故窗口存在的条件准确如述。在 $d\le k\le\ell+1$，已知阶段的整个非恒值窗口消失；在 $k<d\le\ell+1$，该窗口缩短为 $N_k\le H<N_d$；在 $d\ge\ell+2$，同阶段碰撞先发生；在 $k\ge\ell+2$，低阶段已无非恒值恢复窗口。$N_d$ 严格递增且 $N_{\ell+1}=B_\ell<K_{k,\ell}$，由式 (4.21) 得 $G$ 的非减及饱和性。定理 4.4 给全部首次失效侧对 $E\ge0$ 的失败延续；本推论不据此给出首次失效之前的完整最优正噪声阶梯。证毕。

**命题 4.6（跨阶段极值与全局阈值的三个实际来源实例）。** 在定义 4.1 的合同下，下列数值及来源对成立。首先，$\ell=0,k=1,d=3$ 时有

$$
\begin{gathered}
A_0=2,\quad B_0=3,\quad r_1=1/2,\quad R_1=2/3,\quad
S^3e_1=(21,34)^{\mathsf T},\quad N_3=55,\\
\tau_{1,0,3}=1,\quad x_{\min}=(18,36)^{\mathsf T},\quad y=e_1,\quad
n_0(x_{\min})=n_3(y)=144,\\
J_{1,0,3}=54,\quad K_{1,0}=4,\quad K_{1,3}=305,\quad G_{1,0,3}=4.
\end{gathered}
\tag{4.22}
$$

其次，$\ell=0,k=1,d=1$ 时有

$$
x=(1,2)^{\mathsf T},\quad y=e_1,\quad
n_0(x)=n_1(y)=8,\quad
J_{1,0,1}=G_{1,0,1}=N_1=3<K_{1,0}=4.
\tag{4.23}
$$

最后，$\ell=2,k=1,d=2$ 时有

$$
\begin{gathered}
A_2=34,\quad B_2=55,\quad S^2e_1=(5,8)^{\mathsf T},\quad
\tau_{1,2,2}=0,\quad n_2(5,8)=n_4(e_1)=610,\\
J_{1,2,2}=G_{1,2,2}=N_2=13<K_{1,2}=72,\qquad
3\le H<13\quad\text{为非恒值无噪恢复窗口}.
\end{gathered}
\tag{4.24}
$$

三组跨阶段对的低阶段初始标签均为一，高阶段初始标签均为零。

证明。第一组的取整值为 $\lfloor(21-34/2)/(3+2/2)\rfloor=1$，沿整数核方向取 $z=-1$ 得 $(18,36)$。该点满足闭下边界 $a=b/2$，且 $S^{-1}(18,36)^{\mathsf T}=(18,0)^{\mathsf T}$；取十八片 $\alpha$ 叶的完整树 $U$，低阶段初始树 $\rho^3U$ 有五十四片叶，高阶段初始树为单叶 $\alpha$。两报告分别为 $2\cdot18+3\cdot36=144$ 与 $A_3=F_{12}=144$。式 (4.8) 给 $J=55-(3-2)=54$；式 (4.16) 给 $K_{1,0}=3+\lceil2/2\rceil=4$、$K_{1,3}=233+\lceil144/2\rceil=305$，故式 (4.17) 给 $G=4$。在这个预算四处，同阶段的组成 $(1,2)$ 与 $(4,0)$ 已具有共同低阶段报告八及反标签，分别由 $\rho^3(\alpha)$ 与四片 $\alpha$ 叶的完整树达到。因此跨阶段整数平移虽将 $J$ 从五十五降至五十四，全局首次失效仍由较小的同阶段预算四决定。

第二组直接取初始树 $\rho^3(\alpha)$ 与 $\alpha$，在各自阶段的读数都为八；式 (4.8)、(4.17) 给 $J=G=3$，所以唯一已知低阶段的非恒值预算 $H=3$ 在隐藏阶段下消失。第三组中 $a_2-r_1b_2=5-4=1$，而 $B_2+r_1A_2=72$，故 $\tau=0$。取低阶段初始树 $\rho^6(\alpha)$ 与高阶段初始树 $\alpha$；$S^{-1}(5,8)^{\mathsf T}=(1,2)^{\mathsf T}$ 非负，而 $S^{-1}e_1=(-3,2)^{\mathsf T}$ 含负坐标，故标签确为一和零。读数 $34\cdot5+55\cdot8=610=A_4$，$K_{1,2}=55+\lceil34/2\rceil=72$。定理 4.3、4.4 与推论 4.5 给出所列阈值及窗口。这些实例的极小性来自上述全参数证明，具体数值不替代全整数纤维与实际来源的下界。证毕。

## 追加锚（本行以下为增补区）

## 5. 共同原始噪声下的阶段参照与尖锐许可间距

**定义 5.1（隐藏与显露阶段的共同原始间距）。** 完全沿用定义 4.1 的联合初始树域 $\mathcal T_H\times\{\ell,\ell+d\}$、同一个组成域 $D_H$、初始组成许可 $\chi_k$ 和原始数量报告 $r$，其中 $\ell\in\mathbb N_0$、$k,d,H\in\mathbb N_{\ge1}$。记

$$
\begin{aligned}
\delta_{\mathrm{hid}}(H;k,\ell,d)
&=\min_{\substack{x,y\in D_H,\ s,s'\in\{\ell,\ell+d\}\\
\chi_k(x)\ne\chi_k(y)}}|n_s(x)-n_{s'}(y)|,\\
\delta_{\mathrm{cal}}(H;k,\ell,d)
&=\min_{\substack{x,y\in D_H,\ s\in\{\ell,\ell+d\}\\
\chi_k(x)\ne\chi_k(y)}}|n_s(x)-n_s(y)|.
\end{aligned}
\tag{5.1}
$$

空的反标签点对集合取最小值 $+\infty$。每个组成由定义 1.1 的实际初始树实现，所以两个最小值也就是相应树来源上的反标签间距。下标 $\mathrm{cal}$ 表示额外显露实际阶段 $s$，此时观察为 $(s,r)$；对每个已知 $E\in\mathbb Q_{\ge0}$，允许响应仍满足同一个 $|r-n_s(c(T))|\le E$。显露阶段只容许按 $s$ 选择恢复器，不改变原始读数或 $E$ 的单位。隐藏阶段仍只观察 $r$，没有依赖实际 $s$ 的归一化、历史、地址、标签或第二通道。$H$ 只约束两个分支各自的初始树，后续替换树可超过 $H$。

**定理 5.2（共同原始间距的准确阶段比较与碰撞截断）。** 对定义 5.1 的所有参数，复用式 (2.2) 的 $\delta_k$ 和式 (4.17) 的 $G_{k,\ell,d}$，有

$$
\boxed{
\begin{aligned}
\delta_{\mathrm{cal}}(H;k,\ell,d)
&=\min\{\delta_k(H,\ell),\delta_k(H,\ell+d)\}
=\delta_k(H,\ell),\\
\delta_{\mathrm{hid}}(H;k,\ell,d)
&=\begin{cases}
\delta_k(H,\ell),&H<G_{k,\ell,d},\\
0,&H\ge G_{k,\ell,d}.
\end{cases}
\end{aligned}}
\tag{5.2}
$$

第一行对每个 $H\ge1$ 成立。所有有限最小值均由同一联合合同中的实际初始树对达到；在 $H<G_{k,\ell,d}$ 的有限正间距分支，可将达到点对的两个报告阶段都取为 $\ell$。

证明。置

$$
m=3\ell+3,\qquad A=A_\ell=F_m,\qquad
B=B_\ell=F_{m+1},\qquad v=B-A=F_{m-1},\qquad
\Delta=\delta_k(H,\ell),\qquad K=K_{k,\ell}.
$$

先比较两个同阶段间距。式 (5.1) 直接给第一行的第一个等号。若 $H<N_k$，式 (2.9) 给两个阶段的目标都恒为零，两个间距同为 $+\infty$。若 $H\ge K$，定理 2.3 给 $\Delta=0$，故两间距的最小值为零。只余 $N_k\le H<K$；由式 (2.10)，这强制 $k\le\ell+1$，且式 (4.18) 给 $H<K_{k,\ell+d}$。

若 $k=\ell+1$，式 (2.12) 给 $\Delta=1$；高阶段的反标签集合非空，且尚无反标签相等的整数读数，所以 $\delta_k(H,\ell+d)\ge1$。若 $k\le\ell$，则 $k=1$ 使用定理 2.2，$2\le k\le\ell$ 使用定理 3.3。单步的 $H=3$ 分支在两个阶段分别为 $F_{m-1}$ 和 $F_{m+3d-1}$；其后各档由式 (2.5) 中与阶段无关的预算选出同一个最大指标 $j$。中间深度的两个早期间距分支的预算分界 $N_k$、$2F_{3k}$、$N_k+F_{3k-1}$ 同样与阶段无关，后续预算 $C_{k,j}$ 由式 (3.2) 给出，也选出同一个 $j$。这些分支从低阶段改到高阶段，只将相应 Fibonacci 残差的下标增加 $3d$，故高阶段间距不小于 $\Delta$。这证明对所有 $H$ 的校准间距等式；所复用的有限阶梯和零分支均已有实际来源达到点。

再求隐藏阶段间距。$H<N_k$ 时没有反标签来源，故为 $+\infty$。$H\ge G_{k,\ell,d}$ 时，定理 4.4 的实际反标签精确碰撞给出零值。由同阶段点对包含在隐藏阶段点对中，$H<G_{k,\ell,d}$ 时已有 $\delta_{\mathrm{hid}}\le\Delta$。只须在剩余非恒值域证明反向不等式。式 (4.21) 给

$$
N_k\le H<G_{k,\ell,d}
\quad\Longrightarrow\quad
k\le\ell+1,\qquad d>k,\qquad H<K,\qquad
0<\Delta\le v<A<B.
\tag{5.3}
$$

最后一串不等式来自定理 2.2、2.3、3.3 的正间距阶梯。同阶段反标签间距已经由校准等式界定为至少 $\Delta$。对跨阶段对，把低阶段初始组成记为 $x\in D_H$，高阶段初始组成记为 $y\in D_H$；交换来源的书写次序不改变读数差绝对值。

若 $d\ge\ell+2$，式 (4.19) 对每个非零高阶段来源给 $n_{\ell+d}(y)\ge A_{\ell+d}>BK$，而 $n_\ell(x)\le BH$。因此

$$
n_{\ell+d}(y)-n_\ell(x)>B(K-H)\ge B>\Delta.
$$

这里 $K-H$ 是正整数，故这个分支的全部跨阶段对都满足所需下界，无须预设标签方向。

以下设 $k<d\le\ell+1$。式 (4.17) 给 $G_{k,\ell,d}=N_d$，所以 $H<N_d$。记

$$
a=F_{3d-1},\qquad b=F_{3d},\qquad
z=S^de_1=(a,b)^{\mathsf T},\qquad a<b,\qquad a+b=N_d.
$$

先处理所有高阶段 $y\ne e_1$。若 $y$ 有 $\beta$ 叶，其报告至少为 $B_{\ell+d}$；否则它至少有两片 $\alpha$ 叶，其报告至少为 $2A_{\ell+d}>B_{\ell+d}$。这是定理 4.3 证明中式 (4.12) 的全来源排除，其行乘法还给 $B_{\ell+d}=Ab+BN_d$。故

$$
n_{\ell+d}(y)-n_\ell(x)
\ge Ab+B(N_d-H)>B>\Delta.
$$

唯一余下的实际高阶段来源组成为 $y=e_1$，其初始标签是零，报告为 $n_{\ell+d}(e_1)=n_\ell(z)$。$z$ 的叶数为 $N_d>H$，所以 $z\notin D_H$；这里仅用它表达这个报告，绝不将其作为允许的低阶段初始来源。对每个实际低阶段 $x\in D_H$，令 $h=x-z$，则

$$
h\in\mathbb Z^2\setminus\{0\},\qquad
h_1+h_2=|x|_1-N_d<0,\qquad
|n_\ell(x)-n_{\ell+d}(e_1)|=|n_\ell(h)|.
$$

令 $t=3k$、$Q=N_k+F_{t-1}$。若 $H<Q$，则 $d>k$ 给 $a\ge F_{t+2}>Q$，而 $b>a$。每个 $x$ 的两个坐标都不超过 $H$，所以 $h$ 的两个坐标均为负，$|n_\ell(h)|\ge A>\Delta$。若 $k=\ell+1$，式 (2.12) 给 $Q=B+v=K$，所以该临界深度已被这个早期情形全部覆盖。

只余 $H\ge Q$，此时 $k\le\ell$。对 $i\ge t$ 写

$$
\begin{gathered}
C_{k,i}=F_{i+1}+\lceil r_kF_i\rceil,\qquad
j=\max\{i\ge t:C_{k,i}\le H\},\\
t\le j\le m-1,\qquad
C_{k,j}\le H<C_{k,j+1},\qquad \Delta=F_{m-j}.
\end{gathered}
\tag{5.4}
$$

当 $k=1$ 时这些是 $r_1=1/2$ 下的式 (2.5) 和定理 2.2；当 $k\ge2$ 时是式 (3.2)、(3.18)、(3.25)。若 $h$ 的两个坐标弱同号，非零性给 $|n_\ell(h)|\ge A$。若 $h=(u,-w)$，$u,w>0$，则 $h_1+h_2<0$ 给 $u<w$，从而

$$
|n_\ell(h)|=Bw-Au\ge(B-A)w\ge v\ge\Delta.
$$

最后一个差符号情形是 $h=(-u,w)$，其中 $u>w>0$。由 $x_1=a-u\ge0$ 和 $x_2=b+w$，有 $u\le a$、$b+w\le|x|_1\le H$。定义线性泛函 $\Lambda(u,w)=u+r_kw$；因为 $0<r_k<1$，

$$
\begin{aligned}
\Lambda(u,w)&\le a+r_kw<a+w<b+w\le H,\\
\Lambda(w_j)&>0,\qquad \Lambda(w_{j+1})>0,\\
H&<C_{k,j+1}=\lceil\Lambda(w_{j+1})\rceil
\quad\Longrightarrow\quad H<\Lambda(w_{j+1}),\\
w_j&=(F_{j+1},F_j),\qquad
w_{j+1}=(F_{j+2},F_{j+1}).
\end{aligned}
\tag{5.5}
$$

其中取整后的蕴含使用 $H$ 是整数：$H\le\lceil\Lambda(w_{j+1})\rceil-1<\Lambda(w_{j+1})$。这样已经核对了式 (3.21) 的全部实际假设：$(u,w)$ 是正整数方向，$t\le j\le m-1$，所选相邻整数基上的泛函值为正，且 $\Lambda(u,w)<\Lambda(w_{j+1})$。当 $k\ge2$ 时直接应用该式；当 $k=1$ 时直接应用定理 2.2 证明中式 (2.8) 的同一全整数系数估计，其泛函正是 $u+w/2$。两者都给

$$
|n_\ell(h)|=|Au-Bw|\ge F_{m-j}=\Delta.
$$

这些估计覆盖整数基展开的全部系数符号，包括末档 $j=m-1$ 的第二基残差 $g=F_0=0$；不把方向限于 Fibonacci 向量，也不要求 $z$ 是初始来源。至此，全部同阶段和跨阶段反标签对均具有至少 $\Delta$ 的间距。

为达到这个下界，临界深度 $k=\ell+1$ 使用式 (2.13)、(2.17) 的 $(v,A)$ 与 $(0,A+F_{m-2})$，共同预算不超过 $B\le H$，间距为一。单步且 $k\le\ell$ 时，$H=3$ 使用 $(1,2)$ 与 $(2,1)$，其后正间距档使用式 (2.7) 的实际点对。中间深度 $2\le k\le\ell$ 的三个正间距分支依次使用式 (3.11)、(3.12)、(3.15) 的点对，其共同初始叶预算分别为 $N_k$、$2F_{3k}$、$C_{k,j}$，均不超过各分支的 $H$。这些点的反标签、读数残差及实际完整树实现已经由定理 2.2、2.3、3.2 证明。取相应两棵实际初始树，并把两者的报告阶段都设为 $\ell$，便在定义 4.1 的同一个联合来源域达到 $\Delta$。原树仍只受初始预算约束，后续替换照原合同执行。结合下界、空集合分支和定理 4.4 的实际零碰撞分支，得到式 (5.2)。证毕。

**定理 5.3（共同原始有理噪声的尖锐恢复条件）。** 对定义 5.1 的全部参数及每个已知 $E\in\mathbb Q_{\ge0}$，定义 4.1 的隐藏阶段初始组成许可统一恢复存在，当且仅当

$$
\boxed{\quad H<G_{k,\ell,d}\quad\text{且}\quad
2E<\delta_k(H,\ell).\quad}
\tag{5.6}
$$

若显露实际阶段 $s$，保持同一个原始报告与误差关系，则存在统一的 $P_{\mathrm{cal}}:\{\ell,\ell+d\}\times\mathbb Q\to\{0,1\}$ 对所有允许响应输出正确初始标签，当且仅当

$$
\boxed{\quad2E<\delta_k(H,\ell).\quad}
\tag{5.7}
$$

$H<N_k$ 的空反标签集合给间距 $+\infty$，允许任意有限 $E$。每个有限间距的等号均在失败侧，零间距在 $E=0$ 也失败。阶段仍只计替换次数；恢复目标仍是组成祖先存在，不是完整树、规范地址、指定树的语法祖先或实际逆执行。

证明。直接将定理 2.2 证明及定理 3.4 使用的闭候选目标纤维判据应用于定义 4.1 的联合来源。若 $2E<\delta_{\mathrm{hid}}$，同一个允许报告不能同时对应两个相反初始标签，否则两真值的距离至多为 $2E$，与间距矛盾。因而每条非空候选纤维有共同标签，原判据给所需统一恢复器。$H<N_k$ 时所有初始标签为零，常值零恢复器对任意有限 $E$ 有效。

若隐藏间距有限且 $2E\ge\delta_{\mathrm{hid}}$，定理 5.2 给达到它的实际初始树对 $T,T'$ 及其报告阶段 $s,s'$。记 $x=c(T)$、$y=c(T')$，其共同有理中点

$$
r_*=\frac{n_s(x)+n_{s'}(y)}2\in\mathbb Q
\tag{5.8}
$$

到两个真值的距离都是 $\delta_{\mathrm{hid}}/2\le E$，所以同一个报告同时允许两个不同正确标签，任何统一恢复器均失败。这包括有限正间距的等号；零间距时共同报告已经精确。故隐藏阶段的条件恰为 $2E<\delta_{\mathrm{hid}}$。代入式 (5.2)，得到式 (5.6)，因为 $H\ge G_{k,\ell,d}$ 时 $2E<0$ 不成立。

显露阶段后，在两个已知阶段分别应用同一个既有目标纤维判据；存在按实际 $s$ 选择的恢复器，当且仅当 $2E$ 同时严格小于两个同阶段间距，即 $2E<\delta_{\mathrm{cal}}$。式 (5.2) 给式 (5.7)。有限间距的失败可取同在低阶段的实际达到点对，式 (5.8) 的中点也具有相同的阶段标记，因此显露阶段仍不能消除等号失败。两个结论都使用原始数量单位中的同一个 $E$，没有作依赖实际阶段的尺度归一化。证毕。

## 追加锚（本行以下为增补区）

## 6. 共同相对响应下的阶段隐藏与许可分离

**定义 6.1（原始相对响应与反标签比值）。** 沿用定义 1.1、4.1 的非空有限有序完全二叉树、全局替换 $\rho$、联合初始来源 $\mathcal T_H\times\{\ell,\ell+d\}$、初始组成域 $D_H$ 与初始组成许可 $\chi_k$，其中 $\ell\in\mathbb N_0$、$k,d,H\in\mathbb N_{\ge1}$。各阶段的原始真值仍是式 (4.2) 的正整数 $n_s(x)=A_sx_1+B_sx_2$。对共同已知的 $\epsilon\in\mathbb Q_{\ge0}$，定义单个原始有理报告的允许响应关系

$$
\mathcal R^{\mathrm{hid}}_{H,k,\ell,d,\epsilon}
=\left\{((T,s),r):
T\in\mathcal T_H,\ s\in\{\ell,\ell+d\},\ r\in\mathbb Q,
\ |r-n_s(c(T))|\le\epsilon n_s(c(T))\right\}.
\tag{6.1}
$$

参数 $H,k,\ell,d,\epsilon$ 已知，实际阶段 $s$ 隐藏，观察恰为 $r$，不作依赖实际 $s$ 的归一化。预算仍只限制两个分支各自的初始树，后续替换树可超过 $H$。显露阶段的合同额外给出 $s$，允许响应仍是式 (6.1)，观察为 $(s,r)$。隐藏阶段统一恢复指存在总函数 $P:\mathbb Q\to\{0,1\}$，对每个允许响应输出 $\chi_k(c(T))$；显露阶段的恢复器是 $P_{\mathrm{cal}}:\{\ell,\ell+d\}\times\mathbb Q\to\{0,1\}$。目标仅取初始组成祖先的存在，不恢复完整树、规范地址、指定树的语法祖先或实际逆执行。相对响应是数学关系假设，不给设备或物理对应。

对正数 $u,v$ 记 $\mathfrak r(u,v)=|u-v|/(u+v)$，并定义

$$
\begin{aligned}
\theta_k(H,s)
&=\min_{\substack{x,y\in D_H\\\chi_k(x)\ne\chi_k(y)}}
\mathfrak r(n_s(x),n_s(y)),\qquad s\in\mathbb N_0,\\
\theta_{\mathrm{cal}}(H;k,\ell,d)
&=\min\{\theta_k(H,\ell),\theta_k(H,\ell+d)\},\\
\theta_{\mathrm{hid}}(H;k,\ell,d)
&=\min_{\substack{x,y\in D_H,\ s,s'\in\{\ell,\ell+d\}\\
\chi_k(x)\ne\chi_k(y)}}
\mathfrak r(n_s(x),n_{s'}(y)).
\end{aligned}
\tag{6.2}
$$

每个空的反标签集合取最小值 $+\infty$。两个同阶段比值都保留在 $\theta_{\mathrm{cal}}$ 中，使用同一个 $D_H$ 与同一个 $\epsilon$。

有限未知线性映射的背景可参见 [Tsakiris–Peng，Homomorphic Sensing](https://proceedings.mlr.press/v97/tsakiris19a.html)。[Peng–Tsakiris，Homomorphic Sensing of Subspace Arrangements，§2.1，Theorem 1](https://arxiv.org/html/2006.05158v3#Thmtheorem1) 的结论针对泛型 $p$ 维子空间，要求每个映射的秩至少为 $2p$，并满足所列余维条件；这里 $\operatorname{span}_{\mathbb R}D_H=\mathbb R^2$，但每个 $n_s$ 的秩只有一，不满足该秩条件。该文 [§2.3，Theorem 3](https://arxiv.org/html/2006.05158v3#Thmtheorem3) 在完整向量的 homomorphic sensing 性质下，按其式 (4) 的条件控制加性 Euclidean 噪声，并用伪逆表示向量误差；该前提在此完整二维张成空间上已经失败，因为 $0$ 与非零向量 $(B_s,-A_s)$ 具有相同的 $n_s$ 读数。本节的有限整数来源、二值初始目标与相对响应须在式 (6.1) 的合同内处理，下面的比值结论由本卷的整数与许可锥关系证明。

**定理 6.2（隐藏阶段的准确相对间距与跨阶段严格排除）。** 对定义 6.1 的所有参数，复用式 (4.17) 的联合精确碰撞预算 $G_{k,\ell,d}$，有

$$
\boxed{
\theta_{\mathrm{hid}}(H;k,\ell,d)
=\begin{cases}
\theta_{\mathrm{cal}}(H;k,\ell,d),&H<G_{k,\ell,d},\\
0,&H\ge G_{k,\ell,d}.
\end{cases}}
\tag{6.3}
$$

当 $N_k\le H<G_{k,\ell,d}$ 时，对所有 $x,y\in D_H$ 满足 $\chi_k(x)\ne\chi_k(y)$，更有

$$
\mathfrak r(n_\ell(x),n_{\ell+d}(y))
>\theta_k(H,\ell).
\tag{6.4}
$$

当 $H<N_k$ 时三个间距均为 $+\infty$。式 (6.2) 的每个有限最小值均由相应合同中的实际初始树及其阶段达到；在 $H<G_{k,\ell,d}$ 的有限分支，隐藏间距可由同阶段的实际来源对达到。

证明。式 (2.9) 给最小许可初始叶数 $N_k$。故 $H<N_k$ 时全部初始标签为零，反标签集合为空。若 $H\ge G_{k,\ell,d}$，定理 4.4 给同一联合初始来源域中的实际反标签精确碰撞，式 (6.2) 的非负比值因而最小为零。只须证明非恒值的碰撞前域。由式 (4.21)，该域必满足

$$
\begin{gathered}
N_k\le H<G_{k,\ell,d},\qquad
k\le\ell+1,\qquad d>k,\qquad H<K_{k,\ell},\\
\begin{cases}
G_{k,\ell,d}=N_d,\quad H<N_d,&k<d\le\ell+1,\\
G_{k,\ell,d}=K_{k,\ell},&d\ge\ell+2.
\end{cases}
\end{gathered}
\tag{6.5}
$$

以下在此域内简记

$$
m=3\ell+3,\qquad A=A_\ell=F_m,\qquad
B=B_\ell=F_{m+1},\qquad v=B-A=F_{m-1},\qquad K=K_{k,\ell}.
$$

这里 $B$ 是正整数读数系数；Fibonacci 递推给 $B>A>B/2>0$。式 (2.10)、(2.13) 给 $K=B+\lceil Ar_k\rceil\le B+v=2B-A$。

先在原始预算内建立一个严格小于 $1/9$ 的同阶段比值。取许可锥壁上的组成

$$
p=S^ke_1=(F_{3k-1},F_{3k}),\qquad
p'=\begin{cases}
p+(-1,1),&k\text{ 为奇数},\\
p+(1,-1),&k\text{ 为偶数}.
\end{cases}
$$

两点非负非零，叶数都恰为 $N_k\le H$。式 (2.9) 表明，奇数 $k$ 时 $p$ 位于闭下壁，$p'$ 的第一坐标与第二坐标之比严格下降到该壁外；偶数 $k$ 时 $p$ 位于闭上壁，$p'$ 的比值严格上升到该壁外。因此 $\chi_k(p)=1$、$\chi_k(p')=0$。两种奇偶的读数差绝对值均为 $v$。由 $p\ge(1,2)$ 逐坐标成立，

$$
\begin{aligned}
n_\ell(p)+n_\ell(p')
&\ge2n_\ell(p)-v
\ge2(A+2B)-v=3(A+B),\\
\theta_k(H,\ell)
&\le\mathfrak r(n_\ell(p),n_\ell(p'))
\le\frac{v}{3(A+B)}<\frac19.
\end{aligned}
\tag{6.6}
$$

最后的严格不等式等价于 $B<2A$。两点由定义 1.1 实现为实际初始树，许可端点可直接取 $\rho^{3k}(\alpha)$；偶数 $k\ge2$ 时第二坐标减一仍为正，奇数 $k\ge1$ 时第一坐标减一仍非负。

若 $d\ge\ell+2$，则 $m+3d\ge2m+3$。Fibonacci 加法式在这些索引下给

$$
\begin{aligned}
A_{\ell+d}
&\ge F_{2m+3}=A^2+2AB+2B^2
>2B(2B-A)\ge2BK>2BH.
\end{aligned}
\tag{6.7}
$$

严格比较的差为 $A^2+4AB-2B^2>0$，因为 $2A>B$。每个实际高阶段来源的读数至少为 $A_{\ell+d}$，每个低阶段来源的读数至多为 $BH$。故任意跨阶段比值都严格大于 $1/3$，再由式 (6.6) 得式 (6.4)，包括两个可能的标签方向。

以下设 $k<d\le\ell+1$，所以 $d\ge2$。记

$$
a=F_{3d-1},\quad b=F_{3d},\quad c=F_{3d-2},\quad
N=N_d=a+b,\quad z=S^de_1=(a,b),\quad Z=Aa+Bb.
\tag{6.8}
$$

此时 $a+c=b$、$H<N$，且 $A_{\ell+d}=Z$、$B_{\ell+d}=Ab+BN$。比较组成 $z$ 的叶数为 $N>H$，所以 $z\notin D_H$，不能充当允许的低阶段初始来源；读数 $Z$ 所对应的实际高阶段初始来源是单叶 $\alpha$，组成为 $e_1\in D_H$。

对任意高阶段初始组成 $y\ne e_1$，若它含至少一个 $\beta$ 叶，则读数至少为 $B_{\ell+d}$；否则它至少含两个 $\alpha$ 叶，而 $2A_{\ell+d}>B_{\ell+d}$。故令 $V=n_{\ell+d}(y)$、$X=n_\ell(x)$，每个这样的跨阶段来源对满足

$$
V\ge Ab+BN,\qquad X\le BH<BN,\qquad
\mathfrak r(X,V)
>\frac{Ab}{Ab+2BN}>\frac19.
\tag{6.9}
$$

最后一步等价于 $4(A/B)(b/N)>1$，由 $A/B>1/2$ 与 $b/N>1/2$ 得到。这一界对所有低阶段 $x$ 成立，故式 (6.6) 已排除所有高阶段 $y\ne e_1$。

只余高阶段 $y=e_1$。其初始标签为零，所以反标签的低阶段组成 $x$ 必须满足 $\chi_k(x)=1$。置

$$
j=3d-2,\qquad t=\lceil r_kc\rceil,\qquad C=a+t.
\tag{6.10}
$$

由 $0<r_k<1$ 与正整数 $c$，有 $1\le t\le c$、$C\le a+c=b$。若 $H<C$，则 $X\le BH<BC\le Bb$，于是

$$
\mathfrak r(X,Z)
>\frac{Aa}{Aa+2Bb}>\frac19.
$$

这里最后一步等价于 $4(A/B)(a/b)>1$；$d\ge2$ 给 $a/b>1/2$，故严格成立。这也由式 (6.6) 排除。

设 $C\le H<N$。先对每个实际许可 $x\in D_H$ 证明整数分子下界

$$
|n_\ell(x)-Z|\ge g,
\qquad g=F_{m-3d+6}.
\tag{6.11}
$$

因为 $2\le d\le\ell+1$，指数 $m-3d+6$ 在 $6$ 与 $m$ 之间，故 $0<g\le A$。令 $h=x-z$，则 $h_1+h_2=|x|_1-N\le H-N<0$。若两个坐标均非正，则 $h\ne0$，其非零整数性给 $|n_\ell(h)|\ge A\ge g$。若 $h=(u,-w)$、$u,w>0$，则 $u<w$，从而

$$
|Au-Bw|=B(w-u)+vu>B>A\ge g.
$$

坐标为零时，负坐标和零坐标归入第一种情形；正坐标和零坐标与严格负的坐标和矛盾。

剩下 $h=(-u,w)$、整数 $u>w>0$。许可锥嵌套给 $\chi_k(x)=1\Rightarrow\chi_1(x)=1$，所以 $a-u\ge(b+w)/2$，即

$$
2u+w\le2a-b=F_{3d-3}.
\tag{6.12}
$$

$d=2$ 时右边为 $F_3=2$，但左边至少为五，这种情形不存在。若 $d\ge3$，则 $F_{3d-3}<2F_{3d-4}$，式 (6.12) 给 $u<F_{3d-4}$。把定理 1.2 应用于两个辅助整数组成 $(u,0),(0,w)\in D_u$：它们不同、非零，且 $w<u$。这里用于整数间距估计的辅助预算是 $u$，没有把这两个辅助组成或 $z$ 加入原始来源域。令

$$
i=\max\{q\ge1:F_{q+1}\le u\}.
$$

因 $u\ge2$，该指标存在；$u<F_{3d-4}$ 给 $i\le3d-6$，而 $3d-4\le m-4$ 给 $u<F_{m+1}=B$。定理 1.2 的正间距分支因而给

$$
|Au-Bw|\ge F_{m-i}\ge F_{m-3d+6}=g.
\tag{6.13}
$$

这些情况覆盖全部整数差 $h$，证明式 (6.11)。

现构造保持原预算、并控制分母的同阶段反标签对。由 $d>k$ 与 $d\le\ell+1$，有 $3k\le j\le m-2$。式 (3.13) 的矩阵恒等式对这些整数指数直接给

$$
M^je_1=(F_{j-1},c)=S^kM^{j-3k}e_1.
$$

右端祖先为非零非负整数向量；因此式 (2.9) 的闭锥判据给

$$
r_kc\le t\le F_{j-1}\le R_kc.
\tag{6.14}
$$

这里中间的取整界使用 $r_kc\le F_{j-1}$ 且 $F_{j-1}$ 为整数。这是式 (3.14) 的整数锥构造；当 $k=1$ 时也直接成立，与式 (2.7) 相合，不要求定义 3.1 的中间深度范围。于是

$$
P=(t,c),\qquad Q=(t+a,0),\qquad
\chi_k(P)=1,\quad\chi_k(Q)=0,\quad
\max\{|P|_1,|Q|_1\}=a+t=C\le H.
$$

由式 (3.15) 的相同差方向及式 (1.8)，它们满足

$$
\begin{aligned}
f&=F_{m-j}=F_{m-3d+2}>0,\\
|n_\ell(Q)-n_\ell(P)|&=|Aa-Bc|=f,\\
D:=n_\ell(P)+n_\ell(Q)&=A(2t+a)+Bc,\qquad
\theta_k(H,\ell)\le\frac fD.
\end{aligned}
\tag{6.15}
$$

两点均为实际原始预算内的组成：定义 1.1 可直接赋予完整有序二叉括号；$S^{-k}P$ 为非零非负整数，也可先实现该祖先再施加 $\rho^{3k}$，而 $Q$ 可由全 $\alpha$ 叶实现。

许可锥嵌套给 $r_k\ge r_1=1/2$，所以 $2t\ge c$。再由 $A>B/2$、$a+c=b$ 与 $b=2c+F_{3d-3}<3c$，可逐项控制同阶段分母：

$$
\begin{aligned}
D&\ge A(a+c)+Bc=Ab+Bc
>\frac B2b+Bc
>\frac B2(b+a)=\frac{BN}{2},\\
\theta_k(H,\ell)&\le\frac fD<\frac{2f}{BN}.
\end{aligned}
\tag{6.16}
$$

第二个严格不等式使用 $2c>a$，它等价于 $3c>b$。另一方面，当前实际低阶段读数 $X$ 与高阶段 $e_1$ 的读数 $Z$ 满足

$$
\begin{aligned}
X+Z&\le BH+Aa+Bb<BN+Aa+Bb<2BN,\\
g&=F_{m-3d+6}=2F_{m-3d+2}+3F_{m-3d+3}\ge5f.
\end{aligned}
\tag{6.17}
$$

分母的最后一步使用 $Aa+Bb<B(a+b)=BN$。分子的递推中 $m-3d+2\ge2$，所以 $F_{m-3d+3}\ge F_{m-3d+2}=f$。将式 (6.11)、(6.16)、(6.17) 应用于这一实际反标签对，得到

$$
\mathfrak r(X,Z)
\ge\frac{g}{X+Z}
>\frac{g}{2BN}
\ge\frac{5f}{2BN}
>\frac{2f}{BN}
>\theta_k(H,\ell).
\tag{6.18}
$$

这里分别控制同阶段实际见证的分母 $D$ 与当前跨阶段实际来源的分母 $X+Z$，而不是用绝对最小间距除以任意读数和。结合式 (6.9) 和 $H<C$ 的分支，所有反标签跨阶段来源均满足式 (6.4)。式 (6.7) 则已处理较大的 $d$，故两种碰撞前参数域都完整。

同阶段反标签点对本来就在隐藏阶段的联合域中，所以 $\theta_{\mathrm{hid}}\le\theta_{\mathrm{cal}}$。非恒值碰撞前域中，式 (6.4) 给每个跨阶段比值严格大于 $\theta_k(H,\ell)\ge\theta_{\mathrm{cal}}$；其余比值恰是两个同阶段集合，故隐藏最小值就是两者的最小值。这不需要比较两个同阶段相对间距的先后次序，得到式 (6.3)。

最后，$D_H$ 与阶段集合有限，故每个非空反标签集合的最小值均存在且为非负有理数。定义 1.1 把每个达到组成实现为非空完整有序树，选择其达到阶段就给实际联合来源；显露阶段的最小值使用同一阶段。非恒值时许可来源 $\rho^{3k}(\alpha)$ 与非许可单叶 $\alpha$ 已保证反标签集合非空。结合常值分支及定理 4.4 的实际精确碰撞，取得性覆盖全部参数。证毕。

**定理 6.3（闭相对响应的尖锐恢复阈值与调和报告）。** 对定义 6.1 的全部参数及每个共同已知的 $\epsilon\in\mathbb Q_{\ge0}$，隐藏阶段初始组成许可的统一恢复存在，当且仅当

$$
\boxed{\quad
\epsilon<\theta_{\mathrm{hid}}(H;k,\ell,d)
\quad\Longleftrightarrow\quad
H<G_{k,\ell,d}\ \text{且}\
\epsilon<\min\{\theta_k(H,\ell),\theta_k(H,\ell+d)\}.
\quad}
\tag{6.19}
$$

显露实际阶段而保持式 (6.1) 的同一个响应关系时，统一恢复存在，当且仅当 $\epsilon<\theta_{\mathrm{cal}}(H;k,\ell,d)$。$H<N_k$ 的空反标签集合允许每个有限 $\epsilon$。每个有限相对间距的等号均在失败侧，零间距在 $\epsilon=0$ 时也失败；失败由相应合同中的实际初始树对及共同有理报告达到。

证明。对每个 $r\in\mathbb Q$，定义原联合组成域内的有限候选集与总函数

$$
\begin{aligned}
\mathcal C_\epsilon(r)
&=\{(x,s)\in D_H\times\{\ell,\ell+d\}:
|r-n_s(x)|\le\epsilon n_s(x)\},\\
P_\epsilon(r)
&=\begin{cases}
1,&\mathcal C_\epsilon(r)\ne\varnothing\ \text{且}\
\chi_k(x)=1\ \text{对每个 }(x,s)\in\mathcal C_\epsilon(r),\\
0,&\text{其余情形}.
\end{cases}
\end{aligned}
\tag{6.20}
$$

若一个候选集包含相反标签，其两个正整数真值 $u,v$ 必须满足

$$
|u-v|\le|u-r|+|r-v|\le\epsilon(u+v),
$$

因而 $\mathfrak r(u,v)\le\epsilon$。当 $\epsilon<\theta_{\mathrm{hid}}$ 时这不可能，故每个非空候选集都有共同标签。每个实际允许响应的来源都在该候选集中，式 (6.20) 因而总是输出正确标签；空候选集的零值使恢复器在全部有理报告上定义。若 $H<N_k$，所有候选初始标签都是零，同一函数就是常值零恢复器。

反之，若 $\theta_{\mathrm{hid}}$ 有限，定理 6.2 给达到它的实际初始树 $T,T'$ 及阶段 $s,s'$。令 $u=n_s(c(T))>0$、$v=n_{s'}(c(T'))>0$、$\theta=\mathfrak r(u,v)=\theta_{\mathrm{hid}}$。两初始标签相反，且共同有理报告

$$
\begin{aligned}
r_*&=\frac{2uv}{u+v}\in\mathbb Q_{>0},\\
|r_*-u|&=\frac{u|v-u|}{u+v}=\theta u,\qquad
|r_*-v|=\frac{v|v-u|}{u+v}=\theta v
\end{aligned}
\tag{6.21}
$$

在 $\epsilon=\theta$ 时已经同时合法，在每个更大 $\epsilon$ 时继续合法。因此任何单报告恢复器都须对同一个 $r_*$ 输出两个不同标签，统一恢复失败。$u=v$ 时调和报告就是共同精确读数，包含零间距端点。空反标签集合没有这一阻碍，并已由常值恢复器处理。于是隐藏阶段恢复恰在 $\epsilon<\theta_{\mathrm{hid}}$；代入定理 6.2 得式 (6.19)。

显露阶段时，把式 (6.20) 的候选集限制为报告所给的那个 $s$，同一个三角不等式证明两个阶段分别在 $\epsilon<\theta_k(H,s)$ 时可恢复；共同合同要求两者同时成立，恰为 $\epsilon<\theta_{\mathrm{cal}}$。若这个最小值有限，选取达到它的同阶段实际树对，式 (6.21) 的调和报告与相同阶段标记同时合法，故等号及以上仍失败。该闭区间交叠论证是本卷定理 2.2、3.4 所用候选标签纤维判据在式 (6.1) 下的应用；其尖锐端点使用相对半径对应的调和报告。所有阈值仍判定初始组成许可，阶段只计替换次数。证毕。

## 追加锚（本行以下为增补区）
