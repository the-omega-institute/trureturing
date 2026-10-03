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

## 7. 固定许可深度的最终精确极小对与尖锐预算包络

**定义 7.1（原始来源上的相对极限量）。** 固定整数 $k\ge1$。来源仍为[定义 1.1](#1-有限预算的尺度读出与逆许可分离)的非空有限有序完全二叉树，叶标记为 $\alpha,\beta$，替换仍为 $\rho$；对整数 $H\ge1$，初始组成域仍为 $D_H=\{(a,b)\in\mathbb N_0^2:1\le a+b\le H\}$，目标仍为[定义 2.1](#2-许可预算阶梯与深层碰撞前沿)的初始组成许可 $\chi_k(c)=\mathbf1_{\{S^{-k}c\in\mathbb N_0^2\}}$。在已知有限阶段 $L\ge0$，恰好施加 $3L$ 次替换，真值仍为 $n_L(c)=F_{3L+3}c_1+F_{3L+4}c_2$；观察仅为一个 $r\in\mathbb Q$，满足 $|r-n_L(c)|\le\epsilon n_L(c)$，其中共同的 $\epsilon\in\mathbb Q_{\ge0}$ 已知。这是[定义 6.1](#6-共同相对响应下的阶段隐藏与许可分离)的固定阶段分支，预算只计初始树的叶数。

令 $t=3k$、$\phi=(1+\sqrt5)/2$、$\psi=-1/\phi$，复用式 (2.9) 的 $r_k,R_k,N_k$，并记

$$
\begin{gathered}
r_-=r_k,\qquad r_+=R_k,\qquad
s=1+r_-,\qquad g=\phi+r_-,\qquad \kappa=\frac gs,\\
N=N_k=F_{t+1},\qquad Q=N+F_{t-1},\\
\ell(a,b)=a+\phi b,\qquad \ell'(a,b)=a+\psi b=a-b/\phi.
\end{gathered}
\tag{7.1}
$$

对 $j\ge t$ 和整数 $H\ge1$ 定义

$$
\begin{aligned}
C_j=C_{k,j}&=F_{j+1}+\lceil r_-F_j\rceil,\\
\Theta_k(H)&=
\min_{\substack{x,y\in D_H\\\chi_k(x)\ne\chi_k(y)}}
\frac{|\ell(x)-\ell(y)|}{\ell(x)+\ell(y)}.
\end{aligned}
\tag{7.2}
$$

空集合的最小值取 $+\infty$。$\ell,\ell'$ 和 $\Theta_k(H)$ 是证明中的数学量，不是额外观察、无穷阶段报告或隐藏阶段归一化。这里的 $\ell$ 不等于[延拓卷定义 14.1、定理 14.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#14-规范五窗的黄金双读出与进位方向)中作用于规范五窗组成的整数行 $r_G=(1,2)$。本来源域不附加[母卷命题 182.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md#182-收缩窗口对规范来源的识别与范数预算)的单位位、规范接缝和严格共轭条带条件。目标在实际来源纤维上取值、恢复目标与完整隐藏状态有别的范围约定参见[有效分辨率卷 §§10.1–10.4](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md#10-分辨率恢复动态自然性与实际误差)；其中的近似恢复与归一化原则不提供式 (7.2) 的整数极小值。

**定理 7.2（最终精确极小对、方向切换与尖锐固定深度包络）。** 在定义 7.1 的合同下，取充分起点

$$
J=6k+1=2t+1,\qquad H_0=C_{k,J}.
\tag{7.3}
$$

对每个整数 $H\ge H_0$，存在唯一 $j\ge J$ 使 $C_j\le H<C_{j+1}$。令

$$
\begin{gathered}
u=F_{j+1},\qquad w=F_j,\qquad
 e=u-\phi w=(-1)^j\phi^{-j},\\
\tau=H-u+w,\qquad B_H=\left\lfloor\frac\tau s\right\rfloor,\\
x_H=(\tau-B_H,B_H),\qquad
y_H=(\tau-B_H+u,B_H-w),\\
D_{j,H}=\ell(x_H)+\ell(y_H)
=2\tau+2(\phi-1)B_H+e.
\end{gathered}
\tag{7.4}
$$

这两个组成由同一个初始预算内的实际树实现，且

$$
\boxed{
\chi_k(x_H)=1,\quad \chi_k(y_H)=0,\quad
|x_H|_1=\tau\le H,\quad |y_H|_1=H,\quad
\Theta_k(H)=\frac{\phi^{-j}}{D_{j,H}}.}
\tag{7.5}
$$

除差方向 $\pm(F_{j+1},-F_j)$ 外的全部反标签对，其相对比值严格更大；在该方向上，式 (7.4) 的平移使分母最大。因此 $C_j$ 不仅是这一差方向的共同来源预算，还在 $C_j\ge H_0$ 后成为式 (7.2) 极小差方向的准确切换预算。$H_0$ 是充分起点，不断言它是最小起点。

对每个固定 $k$，尖锐渐近包络为

$$
\boxed{
\begin{aligned}
\liminf_{H\to\infty}H^2\Theta_k(H)
&=\frac{\phi+r_-}{2\sqrt5},\\
\limsup_{H\to\infty}H^2\Theta_k(H)
&=\frac{(\phi+r_-)(1+r_-)\phi^2}
 {2\sqrt5(2+\phi r_-)}.
\end{aligned}}
\tag{7.6}
$$

这里 $H$ 只沿正整数趋于无穷。两条预算墙子列分别达到这两个极限：

$$
\begin{aligned}
\lim_{j\to\infty}C_j^2\Theta_k(C_j)
&=\frac g{2\sqrt5},\\
\lim_{j\to\infty}(C_{j+1}-1)^2\Theta_k(C_{j+1}-1)
&=\frac{gs\phi^2}{2\sqrt5(2+\phi r_-)}.
\end{aligned}
\tag{7.7}
$$

证明。闭锥、整数祖先与最小许可预算直接复用[定理 2.3](#2-许可预算阶梯与深层碰撞前沿)。Fibonacci 递推及双根式给

$$
\frac12\le r_-<\frac1\phi<r_+\le\frac23,
\qquad r_+-r_- =\frac1{F_tF_{t+1}},
\qquad
\chi_k(a,b)=1\ \Longleftrightarrow\ b>0,\ r_-b\le a\le r_+b.
\tag{7.8}
$$

具体地，相邻倒比值 $F_{n-1}/F_n$ 位于 $1/2$ 与 $2/3$ 之间，并由 $F_{n-1}+\phi F_n=\phi^n$ 的共轭式交替处于 $1/\phi$ 两侧；Cassini 确定两端差为式 (7.8)。这些双根表达复用[母卷定义 18.1、命题 18.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#18-minkowski-双坐标窗口与全息解释边界)。

$k\ge2$ 时，选一个辅助整数 $L^\dagger\ge k$，在[定理 3.2](#3-任意中间深度的许可噪声阶梯与共同实现预算)的条件下只取其方向预算结论；该结论允许任意 $j\ge t$，与 $L^\dagger$ 无关。$k=1$ 时直接用定理 2.2 的式 (2.5)。两者都给 $C_t=Q$、$C_j$ 严格递增且无界，故预算窗口指标唯一。这一步不把式 (3.5) 的有限输出残差延伸到 $j>3L+3$。

先证式 (7.4) 的真实可行性。使用[母卷命题 105.2 证明中的矩阵幂与加法式](FIBONACCI_ATOMIC_RELATION_GENERATION.md#105-实际联合可达性标量返回与精确自主记忆)，有

$$
F_J=F_{2t+1}=F_t^2+F_{t+1}^2
\ge2F_tF_{t+1}>sF_tF_{t+1}
=\frac{s}{r_+-r_-}.
\tag{7.9}
$$

因为 $s\le5/3<2$，最后比较严格。$j\ge J$ 因而给 $w\ge s/(r_+-r_-)$。由 $H\ge C_j\ge u+r_-w$，得 $\tau\ge sw$ 和 $B_H\ge w$。另一方面

$$
0\le\tau-sB_H<s\le(r_+-r_-)B_H,
\qquad
r_-B_H\le\tau-B_H\le r_+B_H.
\tag{7.10}
$$

所以 $x_H$ 为许可非零整数组成。利用 $H,C_{j+1}$ 都是整数，$H<C_{j+1}=u+w+\lceil r_-u\rceil$ 蕴含 $H<su+w$，因为 $\lceil r_-u\rceil-1<r_-u$。于是

$$
0\le B_H-w
\le\frac{H-u-r_-w}{s}
<\frac{r_-u+(1-r_-)w}{s}<u.
\tag{7.11}
$$

$y_H$ 的第一坐标至少为 $u$，第二坐标小于 $u$；而 $r_+<1$，故它非许可。两点的叶数恰为 $\tau,H$，且 $u>w$ 保证 $\tau<H$。其差为 $(u,-w)$，双根式给分子 $|e|=\phi^{-j}$。

现在排除全部竞争方向。对任意反标签对，若差在交换符号后为 $(p,-z)$，其中整数 $p>z>0$，将许可端点记为 $a=(a_1,a_2)$。当另一端为 $a+(p,-z)$ 时，$a_2\ge z$ 且 $a_1\ge r_-a_2$，较大的叶数至少是 $p+r_-z$。当另一端为 $a-(p,-z)$ 时，$a_1\ge p$ 且 $a_2\ge a_1/r_+$，许可端点的叶数至少为 $(1+1/r_+)p>p+r_-z$。故两种方向都有必要条件

$$
\Lambda(p,z):=p+r_-z\le H.
\tag{7.12}
$$

这重用式 (3.9)、(3.10) 的必要成本机制，不把它当作任意方向的可行性充分条件。

Cassini 给 $\det((u,w),(u+w,u))=(-1)^j$，故两向量是整个整数格的一组基。唯一写成

$$
(p,z)=h(u,w)+i(u+w,u),\qquad h,i\in\mathbb Z,
\qquad p-\phi z=e(h-i/\phi).
\tag{7.13}
$$

后一式由 $u-\phi w=e$ 及 $(u+w)-\phi u=-e/\phi$ 得到。整数条件和 $H<C_{j+1}$ 又给
$\Lambda(p,z)\le H<\Lambda(u+w,u)$。若 $h,i\ge0$，则 $i\ge1$ 已违反此严格预算界，所以 $i=0$，$h\ge1$；除 $(h,i)=(1,0)$ 外，残差至少为 $2|e|$。若两系数均非正，不能产生 $p,z>0$。若两系数异号且都非零，则 $|h-i/\phi|\ge1+1/\phi=\phi$。一个系数为零的其余情形或者已包含在第一种，或者不能产生正坐标。因此除 $(p,z)=(u,w)$ 外，这类方向的残差至少为 $\phi|e|$。

若原差两个坐标同号，或一个坐标为零，其非零整数性给残差至少为一。异号差若写成 $(p,-z)$ 且 $p\le z$，则 $|p-\phi z|\ge(\phi-1)z\ge1/\phi$。$j\ge3$ 时，这两类也严格大于 $\phi|e|$。所以全部非 Fibonacci 竞争方向都已有严格分子间隙；尚须比较它们的相对分母。

许可点 $a\in D_H$ 满足 $a_2\le H/s$，因而 $\ell(a)=|a|_1+(\phi-1)a_2\le\kappa H$；任意点 $b\in D_H$ 满足 $\ell(b)\le\phi H$。每个反标签分母因此至多为 $(\kappa+\phi)H$。式 (7.4) 的 $y_H$ 有叶数 $H$，故

$$
D_{j,H}=2\ell(y_H)-e\ge2H-|e|,
\qquad
\phi-\kappa=\frac{r_-}{\phi(1+r_-)}\ge\frac1{3\phi}.
\tag{7.14}
$$

由 $H\ge3$、$j\ge3$，

$$
\phi D_{j,H}-(\kappa+\phi)H
\ge(\phi-\kappa)H-\phi|e|
\ge\frac1\phi-\phi^{-2}>0.
\tag{7.15}
$$

因此任何非 Fibonacci 方向的比值至少为 $\phi|e|/((\kappa+\phi)H)>|e|/D_{j,H}$，分母不能逆转严格分子间隙。

只剩 Fibonacci 方向。许可端点 $a$ 与另一端 $a-(u,-w)$ 的方向不可能：它要求 $|a|_1\ge(1+1/r_+)u\ge5u/2$，而 $H<su+w\le7u/3$；后一个弱界使用 $s\le5/3$ 及 $w/u\le2/3$。在另一方向，写许可端点为 $(a,b)$，非许可端点为 $(a+u,b-w)$。后者预算给 $a+b\le\tau$，许可锥给 $a\ge r_-b$，所以 $b\le B_H$，进而

$$
\ell(a,b)=a+b+(\phi-1)b
\le\tau+(\phi-1)B_H.
\tag{7.16}
$$

已构造的 $x_H$ 达到两个上界，故使 $2\ell(a,b)+e$ 最大。分子在此方向固定为 $|e|$，这证明式 (7.5) 及严格方向排除。

这些可行点不是实锥替身。$S^{-k}$ 是整数矩阵，$S^{-k}x_H$ 为非零非负整数组成。按定义 1.1 先选一个具有此组成的完整有序树 $U$，再取初始树 $T_H=\rho^{3k}(U)$，就得到 $c(T_H)=x_H$、叶数 $\tau$。按 $y_H$ 的非负叶组成选择叶序与完整二叉括号，得到另一初始树 $T'_H$，叶数 $H$。随后才在这两棵初始树上施加合同规定的 $3L$ 次替换。此构造证明代表树存在，不断言任何指定树有这一语法祖先，不恢复括号或地址，也不授权逆执行。

最后证明尖锐包络。经典 Binet 式与上述双嵌入表达在同一索引下给

$$
C_j=\frac{g\phi^j}{\sqrt5}+O_k(1),\qquad
\frac{C_{j+1}}{C_j}\longrightarrow\phi,\qquad
D_{j,H}=2\kappa(H-F_{j-1})+O_k(1).
\tag{7.17}
$$

分母式由 $u-w=F_{j-1}$、$B_H=\tau/s+O(1)$ 及 $e=O(\phi^{-j})$ 得到，误差在整个窗口内有界。令 $h=H/C_j$，则 $1\le h<C_{j+1}/C_j$，Binet 还给 $F_{j-1}/C_j\to1/(\phi g)$。式 (7.5) 因而在窗口内一致给

$$
H^2\Theta_k(H)=f_k(h)+o(1),\qquad
f_k(h)=\frac{gsh^2}{2\sqrt5(gh-1/\phi)}.
\tag{7.18}
$$

一致性来自窗口内有界的 $h$ 与严格正的分母下界 $g-1/\phi=s$；$k$ 在此保持固定。导数为

$$
f'_k(h)=\frac{gs}{2\sqrt5}
\frac{h(gh-2/\phi)}{(gh-1/\phi)^2}>0
\quad(1\le h\le\phi),
\tag{7.19}
$$

因为 $g\ge\phi+1/2>2/\phi$。在窗口上端稍超过 $\phi$ 的区间导数也仍正，且上端趋于 $\phi$，所以全部整数预算的极限下、上包络分别为 $f_k(1)$、$f_k(\phi)$。用 $g-1/\phi=s$ 与 $g\phi-1/\phi=2+\phi r_-$ 化简，得到式 (7.6)。取 $H=C_j$ 时 $h=1$；取 $H=C_{j+1}-1$ 时 $h\to\phi$，得到式 (7.7)。两个常数严格不同，因此不能将结论写成一个普遍常数乘 $H^{-2}$ 的渐近等式。证毕。

**定理 7.3（全部非恒值预算的来源敏感范数下界与实际上界）。** 在定义 7.1 的条件下，令

$$
\begin{gathered}
c_k=\frac{1+r_-}{\phi(\phi+\kappa)},\\
E_k=\frac{\phi^{-(t-2)}}
 {F_{t-1}+\phi F_t+\phi(F_t+F_{t-2})},\qquad
U_k=\max\{3,(Q-1)^2E_k\}.
\end{gathered}
\tag{7.20}
$$

$H<N$ 时 $\Theta_k(H)=+\infty$，且所有有限阶段的 $\theta_k(H,L)=+\infty$。对每个整数 $H\ge N$，反标签集合非空，式 (7.2) 的最小值正且由实际初始树对达到，并有

$$
\boxed{
\frac{c_k}{H^2}\le\Theta_k(H)\le\frac{U_k}{H^2},
\qquad
\begin{cases}
\Theta_k(H)\le E_k,&N\le H<Q,\\
\Theta_k(H)<3/H^2,&H\ge Q.
\end{cases}}
\tag{7.21}
$$

在 $H\ge H_0$ 的范围，式 (7.5) 还给 $\Theta_k(H)<g/H^2$。这些有限预算界与式 (7.6) 的尖锐渐近常数具有不同的适用断言。

证明。由[定理 2.3](#2-许可预算阶梯与深层碰撞前沿)，每个许可初始组成的叶数至少为 $N$，$S^k(1,0)$ 则达到 $N$；非零坐标轴点非许可。因此反标签集合恰在 $H\ge N$ 时非空，且有限。对非零整数差 $d=(d_1,d_2)$，重用[母卷定义 15.5](FIBONACCI_ATOMIC_RELATION_GENERATION.md#definition-155-共轭与范数)与[定义 18.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md#definition-181-算术的两个实嵌入)的范数及两个实嵌入，有

$$
\mathcal N(d)=d_1^2+d_1d_2-d_2^2
=\ell(d)\ell'(d)\in\mathbb Z\setminus\{0\}.
\tag{7.22}
$$

非零性可直接核对：若 $d_2=0$，范数就是非零平方；若 $d_2\ne0$ 且范数为零，$d_1/d_2$ 会是 $z^2+z-1=0$ 的无理根，矛盾。因此 $|\mathcal N(d)|\ge1$，也给 $\ell$ 在整数组成上的单射性。每个非空有限反标签集合的比值遂正且取得。

取许可端点 $x$ 和任意另一端 $y\in D_H$。对 $x$ 用闭锥，对 $y$ 用原始整数三角域，得到

$$
\begin{gathered}
H\frac{r_- -1/\phi}{1+r_-}
\le\ell'(x)\le
H\frac{r_+ -1/\phi}{1+r_+},\qquad
-\frac H\phi\le\ell'(y)\le H,\\
|\ell'(x-y)|\le\frac{\phi H}{1+r_-},\qquad
\ell(x)+\ell(y)\le(\kappa+\phi)H.
\end{gathered}
\tag{7.23}
$$

第一行中关于 $x$ 的两端来自函数 $(v-1/\phi)/(1+v)$ 在 $v\in[r_-,r_+]$ 上递增，以及 $|x|_1\le H$；下端为负，上端为正，故缩小叶数仍保持这两个界。两端相减的两个可能绝对上界分别为 $\phi H/(1+r_-)$ 与 $\phi r_+H/(1+r_+)$。因为 $r_-r_+<1$，后者不大于前者。结合式 (7.22)，每个反标签比值满足

$$
\frac{|\ell(x-y)|}{\ell(x)+\ell(y)}
=\frac{|\mathcal N(x-y)|}
 {|\ell'(x-y)|\,[\ell(x)+\ell(y)]}
\ge\frac{c_k}{H^2}.
\tag{7.24}
$$

这是保留许可来源条件的下界，而非用一个任意实锥极值替换实际端点。

给出全部预算的实际上界。在 $N\le H<Q$，取

$$
x_0=(F_{t-1},F_t)=c(\rho^t(\alpha)),\qquad
y_0=(0,F_t+F_{t-2}).
\tag{7.25}
$$

$x_0$ 许可，$y_0$ 非许可；其叶数分别为 $N$、$F_t+F_{t-2}\le N$，包含 $k=1$ 的等号情形。$x_0-y_0=(F_{t-1},-F_{t-2})$，正确的 Fibonacci 双根残差给分子 $\phi^{-(t-2)}$；分母恰是式 (7.20) 保留的三项和，所以比值为 $E_k$。这里 $F_{t-1}+\phi F_t=\phi^t$ 可由初值 $(F_0,F_1)$ 和乘以 $\phi$ 的递推验证，但无须将其他 Fibonacci 加权和替换为幂。$y_0$ 由全 $\beta$ 叶的完整有序树实现。

对 $H\ge Q=C_t$，取唯一 $j\ge t$ 满足 $C_j\le H<C_{j+1}$，并令 $a_j=\lceil r_-F_j\rceil$。实际点对

$$
\widetilde x_j=(a_j,F_j),\qquad
\widetilde y_j=(a_j+F_{j+1},0),\qquad
\frac{|\ell(\widetilde x_j)-\ell(\widetilde y_j)|}
 {\ell(\widetilde x_j)+\ell(\widetilde y_j)}
=\frac{\phi^{-j}}{2a_j+F_{j+1}+\phi F_j}
\tag{7.26}
$$

是[定理 3.2 的式 (3.14)、(3.15)](#3-任意中间深度的许可噪声阶梯与共同实现预算)所给来源构造；$k\ge2$ 仍只在辅助 $L^\dagger\ge k$ 下调用方向预算，$k=1$ 取定理 2.2 的式 (2.7)。也可直接核对 $M^je_1=S^kM^{j-t}e_1$，其中祖先非零非负且整数，故 $r_-F_j\le a_j\le F_{j-1}\le r_+F_j$。两点分别许可与非许可，共同叶数为 $C_j\le H$；每点按定义 1.1 实现，许可端点还可先实现其整数祖先再替换。

同一整数锥构造用于 $j+1$，给 $a_{j+1}\le F_j=w$。记 $u=F_{j+1}$，则 $H<C_{j+1}\le u+2w\le4w$；又因 $j\ge3$，$u\ge3w/2$，故式 (7.26) 的分母严格大于 $3w$。Binet 给 $w\phi^{-j}\le(1+\phi^{-6})/\sqrt5$。于是

$$
H^2\frac{\phi^{-j}}{2a_j+u+\phi w}
<\frac{16(1+\phi^{-6})}{3\sqrt5}
<\frac{6344}{2187}<3.
\tag{7.27}
$$

第二个严格界只用 $\phi>3/2$、$\sqrt5>2$。早期预算则有 $H^2E_k\le(Q-1)^2E_k$，合并即得式 (7.21)。这些上界全部由初始非零整数点及实际树代表给出。

在 $H\ge H_0$，式 (7.14) 给 $D_{j,H}>H$。递推归纳给 $F_{j+1}\le\phi^j$、$F_j\le\phi^{j-1}$，再用 $H<su+w$，得到 $H\phi^{-j}<s+1/\phi=g$，故式 (7.5) 给更强的最终上界。

该实际极小差 $d=(u,-w)$ 还满足

$$
\ell(d)=(-1)^j\phi^{-j},\qquad
\ell'(d)=u+w/\phi=F_{j-1}+\phi F_j=\phi^j,
\qquad \mathcal N(d)=(-1)^j.
\tag{7.28}
$$

中间等式使用 $u=w+F_{j-1}$、$1+1/\phi=\phi$，再用已经验证的幂表达。因而范数一的整数差确由极小实际来源对实现。$\ell$ 作为实线性泛函有核 $\mathbb R(\phi,-1)$，但该核不含非零整数点；预算增长中的相对裕度消失不是整数核非零。不同实际树仍可共享同一组成，整数组成单射不分离那些树。证毕。

**定理 7.4（有限阶段行列式误差、实际调和报告与未定比较带）。** 对定义 7.1 的任意整数 $L\ge0$，令

$$
\begin{gathered}
m=3L+3,\qquad \xi_L=\frac{F_{m+1}}{F_m},\qquad
\delta_L=|\xi_L-\phi|
=\frac{\phi^{-m}}{F_m}
=\frac{\sqrt5}{\phi^{2m}-(-1)^m},\\
R_z(x,y)=\frac{|x_1-y_1+z(x_2-y_2)|}
 {x_1+y_1+z(x_2+y_2)}\quad(z>0).
\end{gathered}
\tag{7.29}
$$

对同一个 $D_H$ 内的任意实际组成对 $x,y$，置 $A=x_1+y_1$、$B=x_2+y_2$，则

$$
\begin{aligned}
|R_{\xi_L}(x,y)-R_\phi(x,y)|
&\le E_L(x,y),\\
E_L(x,y)&=
\frac{2\delta_L|\det(x,y)|}
 {(A+\xi_LB)(A+\phi B)}
\le E_L:=\frac{2\delta_L}{(\sqrt{\xi_L}+\sqrt\phi)^2}
\le\frac{\delta_L}{3}
\le\frac{\sqrt5}{3(\phi^{6L+6}-1)}.
\end{aligned}
\tag{7.30}
$$

该行列式误差保留同一实际点对，不要求差方向指标 $j\le m$。对每个 $H\ge N$，

$$
\boxed{
|\theta_k(H,L)-\Theta_k(H)|\le E_L,
\qquad
\lim_{L\to\infty}\theta_k(H,L)=\Theta_k(H).}
\tag{7.31}
$$

对 $H<N$，两个量始终为 $+\infty$，不作无穷值相减。

在固定已知阶段分支，共同有理误差 $\epsilon<\Theta_k(H)-E_L$ 足以保证初始许可恢复。对 $H\ge H_0$，使用式 (7.4) 的实际树对，$\epsilon\ge\Theta_k(H)+E_L(x_H,y_H)$ 足以保证失败。因此，仅由这两个比较作出的判断留下如下带：

$$
\epsilon\in\mathbb Q_{\ge0},\qquad
\Theta_k(H)-E_L\le\epsilon
<\Theta_k(H)+E_L(x_H,y_H).
\tag{7.32}
$$

此带内的恢复与失败不能由上述误差夹逼决定，须使用准确的有限阶段 $\theta_k(H,L)$；在它的等号处失败。任意准确有限阈值都由达到它的实际反标签初始树对及一个共同有理调和报告实现。对任意 $0<\eta<1$，还有有限阶段的联合充分范围

$$
\phi^{6L+6}\ge1+\frac{\sqrt5H^2}{3\eta c_k},\quad H\ge N
\quad\Longrightarrow\quad
\theta_k(H,L)\ge(1-\eta)\frac{c_k}{H^2}.
\tag{7.33}
$$

本定理只比较同一已知阶段的组成对，不凭这一界分类隐藏阶段联合域的跨阶段间距。

证明。由[母卷命题 18.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#18-minkowski-双坐标窗口与全息解释边界)的双嵌入式，在本合同中 Binet 正确给
$n_L(c)=(\phi^m\ell(c)-\psi^m\ell'(c))/\sqrt5$。同时 $F_{m+1}-\phi F_m=(-1)^m\phi^{-m}$，并且 $F_m=(\phi^m-(-1)^m\phi^{-m})/\sqrt5$，所以式 (7.29) 的 $\delta_L$ 等式成立。对非空初始组成，两种 $R_z$ 的分母都正；有限阶段比值恰为 $R_{\xi_L}(x,y)$，此等式只是约去共同正系数 $F_m$，未给观察增加或变更任何报告。

暂时去掉绝对值，写 $S_z=(x_1-y_1+z(x_2-y_2))/(A+zB)$。直接交叉相减给

$$
S_{\xi_L}-S_\phi
=\frac{-2\det(x,y)(\xi_L-\phi)}
 {(A+\xi_LB)(A+\phi B)}.
\tag{7.34}
$$

用 $\bigl||a|-|b|\bigr|\le|a-b|$ 得来源敏感误差。非负坐标保证 $|\det(x,y)|\le AB$；而

$$
\begin{aligned}
(A+\xi_LB)(A+\phi B)
&=A^2+(\xi_L+\phi)AB+\xi_L\phi B^2\\
&\ge(\sqrt{\xi_L}+\sqrt\phi)^2AB.
\end{aligned}
\tag{7.35}
$$

当 $AB>0$ 时相除即得 $E_L(x,y)\le E_L$；当 $AB=0$ 时行列式为零，两个比值相等。Fibonacci 比值满足 $\xi_L\ge3/2$，且 $\phi>3/2$，故 $(\sqrt{\xi_L}+\sqrt\phi)^2>6$，给 $E_L\le\delta_L/3$；式 (7.29) 的分母至少为 $\phi^{6L+6}-1$，完成式 (7.30)。

$H\ge N$ 时，两种比值在同一个非空有限反标签集合上取最小值。对达到任一最小值的点对应用式 (7.30)，分别得到两方向的不等式，从而证明式 (7.31)。这也是有限族的最小值连续性在本整数任务上的应用，直接识别固定 $H$ 的数学极限，没有引入无限观察。

固定阶段的准确恢复判据 $\epsilon<\theta_k(H,L)$ 直接复用[定理 6.3](#6-共同相对响应下的阶段隐藏与许可分离)的显露阶段证明，将候选限制为此阶段即可。其充分性来自同一允许报告不能包含反标签候选。若相应最小值有限，取实际达到点对 $T,T'$，置 $U=n_L(c(T))>0$、$V=n_L(c(T'))>0$，则

$$
\begin{gathered}
r_* =\frac{2UV}{U+V}\in\mathbb Q_{>0},\qquad
\vartheta=\frac{|U-V|}{U+V}=\theta_k(H,L),\\
|r_*-U|=\vartheta U,\qquad
|r_*-V|=\vartheta V.
\end{gathered}
\tag{7.36}
$$

$\vartheta$ 本身也是有理数。故 $\epsilon=\vartheta$ 时报告已经同时合法，且两标签相反；更大的共同误差继续允许它。若 $U=V$，这一式仍给 $\vartheta=0$ 及共同精确报告，包含有限阶段的精确碰撞。来源实现由定义 1.1 保证，所以等号失败有实际初始树见证。

由式 (7.31)，$\epsilon<\Theta_k(H)-E_L$ 保证 $\epsilon<\theta_k(H,L)$。对最终实际极小对，式 (7.30) 给 $R_{\xi_L}(x_H,y_H)\le\Theta_k(H)+E_L(x_H,y_H)$；故达到或超过右端的 $\epsilon$ 允许这对树的共同调和报告，得到失败侧及式 (7.32)。比较带并非对准确有限阈值的不可判断言，而是这些充分条件没有决定的范围。式 (7.33) 则使 $E_L\le\eta c_k/H^2$，再结合定理 7.3 的下界即可。$\ell,\xi_L$ 及以上代数比较始终只在证明中使用；观察仍是原合同的单个有理 $r$，没有历史、伴随通道、无理报告或依赖隐藏阶段的缩放。证毕。

**命题 7.5（起点与渐近常数的两个精确早期反例）。** 定理 7.2 的起点条件不能直接删去，式 (7.6) 的下包络常数也不能直接充作全部非恒值预算的下界。具体地，$k=1,H=5$ 时预算窗口为 $C_{1,3}=4\le5<C_{1,4}=7$，将式 (7.4) 的取整构造直接代入会给

$$
u=3,\quad w=2,\quad \tau=4,\quad B_H=2,\quad
x_H=(2,2),\quad y_H=(5,0),\qquad
S^{-1}x_H=(-2,2).
\tag{7.37}
$$

因而两端均非许可，该构造不是反标签见证。另在 $k=1,H=4$，实际树
$T=\rho^3(\alpha)=\langle\langle\beta,\alpha\rangle,\beta\rangle$ 和
$T'=\langle\alpha,\langle\alpha,\langle\alpha,\alpha\rangle\rangle\rangle$
满足

$$
\begin{gathered}
c(T)=(1,2),\quad c(T')=(4,0),\quad
\chi_1(c(T))=1,\quad \chi_1(c(T'))=0,\\
\Theta_1(4)\le\frac{2\phi-3}{5+2\phi},\qquad
16\frac{2\phi-3}{5+2\phi}
<\frac{\phi+1/2}{2\sqrt5}.
\end{gathered}
\tag{7.38}
$$

证明。第一项直接使用[定义 1.3](#1-有限预算的尺度读出与逆许可分离)的整数矩阵 $S^{-1}=\begin{pmatrix}-3&2\\2&-1\end{pmatrix}$；负的祖先坐标否定许可。它只否定将取整构造外推到每个 $H\ge C_{1,3}$，不否定定理 7.2 的最终范围。

第二项两棵树的初始叶数为三、四，均在 $\mathcal T_4$ 内。许可点的祖先组成为 $(1,0)$，横轴点非许可。两个 $\ell$ 值为 $1+2\phi$、$4$，且 $2\phi>3$，故分子为 $2\phi-3$、分母为 $5+2\phi$。最后的严格比较用 $\sqrt5=2\phi-1$ 和 $\phi^2=\phi+1$ 交叉相乘，等价于

$$
439<272\phi
\quad\Longleftrightarrow\quad
303<136\sqrt5;
\qquad
303^2=91809<92480=5\cdot136^2.
\tag{7.39}
$$

所以 $\Theta_k(H)\ge(\phi+r_k)/(2\sqrt5H^2)$ 的全预算断言已被这对实际来源否定。式 (7.21) 的来源敏感有限下界与式 (7.6) 的渐近下包络必须各守其范围。证毕。

**定义 7.6（早期预算与变动深度的未定范围）。** 以 $C_j$ 的严格递增窗口定义每个 $H\ge Q$ 的指标 $j(H)$，并用式 (7.4) 定义形式上的取整点对及分母。令

$$
H_k^*=\min\left\{h\in\mathbb Z_{\ge Q}:
\begin{array}{l}
\text{对每个整数 }H\ge h,\ \text{式 (7.4) 的点对属于 }D_H,\\
\chi_k(x_H)=1,\ \chi_k(y_H)=0,\\
\Theta_k(H)=\phi^{-j(H)}/D_{j(H),H}
\end{array}\right\}.
\tag{7.40}
$$

定理 7.2 保证此定义的集合非空，并给 $Q\le H_k^*\le C_{k,6k+1}$。这里未确定最小起点 $H_k^*$，也未分类全部 $N_k\le H<C_{k,6k+1}$ 的精确极小对。定理 7.2 的两个包络只取固定 $k$ 的极限；允许 $k=k(H)$ 增长时的统一窗口误差、最小起点和渐近常数范围仍是待定数学问题。式 (7.33) 是逐参数的有限阶段充分条件，不交换 $H\to\infty$ 与 $L\to\infty$，也不填补这些变动深度问题。以上范围始终针对原始初始树域与组成许可，不扩大为指定树祖先、完整树或规范地址恢复以及实际逆执行。

## 追加锚（本行以下为增补区）

## 8. 全预算相对极小对的实际域相邻性与整数平移优化

**定义 8.1（实际三角域的读数次序与许可朝向）。** 沿用定义 1.1、2.1、7.1 的非空有限有序完全二叉树、叶标签 $\alpha,\beta$、全局替换 $\rho$、初始叶预算、组成许可和有限阶段的单个有理响应。对整数 $k,H\ge1$，置

$$
\begin{gathered}
D_H=\{(a,b)\in\mathbb N_0^2:1\le a+b\le H\},\qquad
\ell(a,b)=a+\phi b,\qquad \phi=(1+\sqrt5)/2,\\
t=3k,\qquad v=F_t,\qquad N=N_k=F_{t+1},\\
r=r_k=\min\{F_{t-1}/F_t,F_t/F_{t+1}\},\qquad
R=R_k=\max\{F_{t-1}/F_t,F_t/F_{t+1}\}.
\end{gathered}
\tag{8.1}
$$

许可标签仍为 $\chi_k(a,b)=\mathbf1_{\{S^{-k}(a,b)^{\mathsf T}\in\mathbb N_0^2\}}$；由式 (2.9)、(7.8)，它在 $D_H$ 上等价于 $b>0$ 且 $rb\le a\le Rb$，其中 $1/2\le r<1/\phi<R\le2/3$。$\Theta_k(H)$ 仍取式 (7.2) 的反标签相对比值最小值，空集合取 $+\infty$。整数点上的 $\ell$ 单射且在 $D_H$ 上严格为正，故它赋予 $D_H$ 一个严格全序；相邻指整个 $D_H$ 中没有读数严格介于两端之间的点。对 $j\ge1$，记

$$
u_j=F_{j+1},\qquad w_j=F_j,\qquad
 d_j=(u_j,-w_j),\qquad
 e_j=\ell(d_j)=(-1)^j\phi^{-j}.
\tag{8.2}
$$

反标签点对的朝向 $\sigma\in\{+1,-1\}$ 以许可端点 $x=(a,b)$ 为起点，非许可端点为 $y=x+\sigma d_j$。这里的 $\ell$、$e_j$ 和 $\Theta_k(H)$ 只作证明量；实际观察仍为定义 7.1 的有限阶段有理响应。许可只取组成祖先存在性，树的括号、叶序、规范地址和指定树的语法祖先均不由该标签决定，实际逆执行也不包含在该定义中。

**定理 8.2（原预算域中的相邻方向与全部相对极小对的限制）。** 对每个整数 $H\ge1$，$D_H$ 中任意读数相邻的两个点，其差必为某个 $\pm d_j$，$j\ge1$；该 $d_j$ 为原始整数向量，即两坐标互素。对每个整数 $k\ge1$ 和 $H\ge N_k$，每个达到 $\Theta_k(H)$ 的反标签组成对均在整个 $D_H$ 的读数次序中相邻，因而也具有这样的差。特别地，相邻差不含非原始倍数，且所用指标满足 $F_{j+1}\le H$。

证明。$\phi$ 无理，故 $\ell$ 在整数点上单射。设一个反标签对的读数为 $0<U<V$，且实际组成 $z\in D_H$ 满足 $U<Z:=\ell(z)<V$。二值标签 $\chi_k(z)$ 必与一端相同；将它与另一端配对仍为反标签。两个可能的新比值均严格减小，因为

$$
\frac{Z-U}{Z+U}<\frac{V-U}{V+U},\qquad
\frac{V-Z}{V+Z}<\frac{V-U}{V+U}.
\tag{8.3}
$$

交叉相乘时，两项严格不等式的正差分别为 $2U(V-Z)$、$2V(Z-U)$。$H\ge N_k$ 时，许可组成 $c(\rho^{3k}\alpha)$ 与非许可单叶组成 $(1,0)$ 均在 $D_H$ 中，故反标签集合非空且有限，极小对存在。这说明每个极小对必须相邻，而不是仅在各自标签类中相邻。

下面对任意相邻点对证明差的限制。若两端逐坐标可比，将较小端记为 $x$，差取非零非负整数向量。若差的坐标和至少为二，沿其中一个正坐标作单位步所得点非零、逐坐标处于两端之间、叶数不超过较大端，并且读数严格处于两端之间，矛盾。若差为 $(0,1)$，点 $x+(1,0)$ 的叶数等于较大端，读数增量 $1$ 严格介于 $0$ 与 $\phi$ 之间，也矛盾。若差为 $(1,0)$，写 $x=(a,b)$：$a\ge1$ 时，点 $x+(-1,1)$ 非负非零、叶数不变，读数增量 $\phi-1\in(0,1)$；$a=0$ 时，非空性给 $b\ge1$，点 $x+(2,-1)$ 非负非零、叶数为 $b+1$，等于较大端的叶数，读数增量 $2-\phi\in(0,1)$。两种情形都有中间点。因此相邻两端不可逐坐标比较。

对不可比两端，交换端点后将差写成 $(p,-q)$，其中 $p,q$ 为正整数；令 $y=x+(p,-q)$。若 $p\le q$ 且 $(p,q)\ne(1,1)$，则 $q\ge2$，并有

$$
\phi q-p\ge(\phi-1)q>\phi-1.
$$

因 $x_2\ge q$，点 $z=x+(1,-1)$ 非负非零且叶数等于 $x$ 的叶数。它的读数增量 $1-\phi$ 严格介于 $p-\phi q$ 与 $0$ 之间，与相邻性矛盾。故 $p\le q$ 只可能留下 $(p,q)=(1,1)$，即 $d_1$。

余下设 $p>q$。在本证明内部记 $v_h=(F_{h+1},F_h)$，$h\ge0$，并将 $v_0=(1,0)$ 作为辅助向量。复用 Fibonacci 递推、Cassini 和双根式，有

$$
\det(v_h,v_{h+2})=(-1)^h,\qquad
F_{h+1}-\phi F_h=(-1)^h\phi^{-h}.
\tag{8.4}
$$

第二式在 $h=0,1$ 分别为 $1$ 和 $1-\phi=-\phi^{-1}$；递推使两端满足相同的二阶关系，因此对所有 $h\ge0$ 成立。行列式由 $v_{h+2}=v_{h+1}+v_h$ 和 Cassini 得到。对正分母，偶数 $h$ 的斜率 $F_{h+1}/F_h$ 从上方严格下降到 $\phi$，奇数 $h$ 的斜率从 $1$ 开始严格上升到 $\phi$；$v_0$ 的斜率约定为 $+\infty$。相邻同奇偶斜率的严格次序来自式 (8.4) 的行列式，极限来自双根式。

上述收敛框架可参见 [Jaroslav Hančl 与 Ondřej Turek，*One-sided Diophantine approximations*，arXiv:1809.01013v2，§3 式 (8)、(9)、Proposition 3.2 及 §4 Theorem 4.5](https://arxiv.org/pdf/1809.01013v2)。其连分数取实数 $\alpha=[a_0;a_1,\ldots]$，$a_0\in\mathbb Z$、$a_n\in\mathbb N$（$n\ge1$），逼近分母为正整数。这里 $\alpha=\phi=[1;1,1,\ldots]$，按该文的零起编号，$p_n=F_{n+2}$、$q_n=F_{n+1}$；因此本证明的 $h\ge1$ 对应 $n=h-1$。奇数 $h$ 是下侧收敛子，偶数 $h$ 是上侧收敛子。所有部分商均为一，所以该文式 (14) 的 $0<s<a_{n+1}$ 没有整数取值，没有另需加入的严格半收敛子；Theorem 4.5 中的端点分式给同一收敛子族。$v_0$ 的零分母只用于整数锥分解，不作为该文正分母逼近结论的实例。该文的误差目标及分母限制不含本定理的实际三角域、二值许可标签或相对比值分母；以下域内构造提供这些条件之间的桥梁。

由于 $p/q$ 有理而 $\phi$ 无理，$p/q\ne\phi$。若 $p/q>\phi$，它处于某个相邻偶数指标斜率的闭区间内；若 $1<p/q<\phi$，它处于某个相邻奇数指标斜率的闭区间内。故存在有限指标 $h\ge0$，使

$$
(p,q)=A v_h+B v_{h+2},\qquad A,B\in\mathbb N_0.
\tag{8.5}
$$

斜率夹持先给非负实系数，式 (8.4) 的行列式为 $\pm1$ 再给整数系数。边界斜率也允许，其中一个系数可为零。$A+B\ge1$；若 $A+B=1$，差已经是 $d_h$ 或 $d_{h+2}$。整个差不可比，故不可能只取 $v_0$，留下的指标至少为一。

若 $A+B\ge2$，从有正系数的向量中取一项 $(u,w)=v_i$，$i\in\{h,h+2\}$，并置 $z=x+(u,-w)$。非负展开给 $0\le u\le p$、$0\le w\le q$，所以 $z$ 的两个坐标非负。每项都有 $u-w\ge0$；所有项的这些差之和为 $p-q$，故

$$
1\le|x|_1\le|z|_1=|x|_1+u-w
\le|x|_1+p-q=|y|_1\le H.
\tag{8.6}
$$

因此 $z$ 非零且仍在原来的 $D_H$ 内。式 (8.4) 使同奇偶项的读数增量都具有同一严格符号；至少还有一项留在余和中，故 $u-\phi w$ 严格介于 $0$ 与 $p-\phi q$ 之间。这给真实中间读数，矛盾。特别地，非原始倍数也在这一情形中被排除。留下的 Fibonacci 相邻坐标互素，这是 Cassini 的直接结果。最后，差为 $\pm d_j$ 时，第一坐标相差 $F_{j+1}$，某端的第一坐标至少为该数，叶预算遂给 $F_{j+1}\le H$。证毕。

**定义 8.3（许可行的半群前驱与两个朝向的候选）。** 对定义 8.1 的 $k$，记

$$
\mathcal S_k=\{v m+N n:m,n\in\mathbb N_0\}.
$$

对整数 $B$，定义

$$
M_k(B)=
\begin{cases}
-\infty,&B<0,\\[2pt]
\displaystyle\max_{0\le n\le\min\{v-1,\lfloor B/N\rfloor\}}
\left\{Nn+v\left\lfloor\frac{B-Nn}{v}\right\rfloor\right\},&B\ge0,
\end{cases}
\tag{8.7}
$$

其中 $n$ 取整数；$B\ge0$ 时允许 $n=0$，故最大值存在。对每个整数 $j\ge1$ 满足 $u=F_{j+1}\le H$，置 $w=F_j$、$T_+=H-u+w$，并定义

$$
\begin{aligned}
L_+&=w,&
B_+&=\min\left\{
\left\lfloor\frac{T_+}{1+r}\right\rfloor,
 w+\left\lceil\frac{H}{1+R}\right\rceil-1\right\},&
b_+&=M_k(B_+),\\
L_-&=\left\lceil\frac uR\right\rceil,&
B_-&=\min\left\{H-u,
\left\lfloor\frac{H}{1+r}\right\rfloor\right\},&
b_-&=M_k(B_-).
\end{aligned}
\tag{8.8}
$$

仅当 $b_\sigma\ge L_\sigma$ 时保留朝向 $\sigma$，并对保留项置

$$
\begin{aligned}
a_+&=\min\{\lfloor Rb_+\rfloor,T_+-b_+\},\\
a_-&=\min\{\lfloor Rb_-\rfloor,H-b_-,
 u+\lceil r(b_-+w)\rceil-1\}.
\end{aligned}
\tag{8.9}
$$

记所有保留项组成的有限集为 $\mathcal I_k(H)$。对 $(j,\sigma)\in\mathcal I_k(H)$，定义

$$
\begin{gathered}
x_{j,\sigma}=(a_\sigma,b_\sigma),\qquad
 y_{j,\sigma}=(a_\sigma+\sigma u,b_\sigma-\sigma w),\\
D_{j,\sigma}=2a_\sigma+\sigma u+
 \phi(2b_\sigma-\sigma w),\qquad
W_{j,\sigma}=\phi^j D_{j,\sigma}.
\end{gathered}
\tag{8.10}
$$

**定理 8.4（全部深度和预算的精确得分规则与所有并列取得对）。** 对每个整数 $k\ge1$ 和 $H\ge N_k$，定义 8.3 的集合 $\mathcal I_k(H)$ 非空。其每项给原初始预算内的实际反标签组成对，而且

$$
\boxed{\quad
\Theta_k(H)=\frac{1}{\displaystyle\max_{(j,\sigma)\in\mathcal I_k(H)}W_{j,\sigma}}.
\quad}
\tag{8.11}
$$

每个最大得分项均达到此值；反过来，每个达到此值的组成对，在交换端点之外，恰为某个最大得分项的 $(x_{j,\sigma},y_{j,\sigma})$。所有相等的最大得分都须保留，不能仅按指标大小选一项。对每个固定 $(j,\sigma)$，式 (8.8)、(8.9) 是该方向和朝向下唯一的最大分母平移。每个取得组成的任意完整有序树代表均为合法初始来源。$H<N_k$ 时仍有 $\Theta_k(H)=+\infty$。

证明。先核对许可行与整数来源的对应。复用定理 2.3 的整数逆和矩阵幂：$S^k=M^t$ 的两列分别是 $(F_{t-1},F_t)^{\mathsf T}$、$(F_t,F_{t+1})^{\mathsf T}$，行列式为 $(-1)^t=\pm1$。它们生成闭许可锥；整数点在此闭锥中时，唯一实逆系数非负，而整数逆矩阵使这两个系数同时为整数。于是对每个整数 $b\ge0$，

$$
\begin{aligned}
\lceil rb\rceil\le\lfloor Rb\rfloor
&\quad\Longleftrightarrow\quad
\exists a\in\mathbb N_0:\ rb\le a\le Rb\\
&\quad\Longleftrightarrow\quad
b=vm+Nn\text{，其中 }m,n\in\mathbb N_0.
\end{aligned}
\tag{8.12}
$$

$b=0$ 时，两边共同对应零组成；它只用于行判据，后面的 $L_\sigma>0$ 排除零来源。$b>0$ 时对应的组成与祖先均非零。这不是连续锥的松弛，而是原整数组成的准确等价。

$\gcd(v,N)=1$，且任何半群表示 $b=vm+Nn$ 都可将 $n=n_0+vh$ 归约为

$$
b=v(m+Nh)+Nn_0,\qquad 0\le n_0<v,\quad h\in\mathbb N_0.
$$

新系数仍非负。对于固定余数 $n_0$ 和上界 $B\ge0$，必须有 $Nn_0\le B$；最大允许的第一系数为 $\lfloor(B-Nn_0)/v\rfloor$。因此式 (8.7) 恰为 $\mathcal S_k$ 中不超过 $B$ 的最大元素；$B<0$ 时没有非负半群元素。该余数公式保留了所有行空洞。

固定方向 $u=F_{j+1}$、$w=F_j$，其中 $u\ge w\ge1$。在正朝向 $y=(a+u,b-w)$ 下，非负性要求 $b\ge w$，且 $y$ 的第一坐标为正。许可端点满足 $a\ge rb$，因此 $a+u-r(b-w)\ge u+rw>0$，另一端不能落在下墙外。由于许可墙闭合，它非许可的准确条件是

$$
a+u>R(b-w)
\quad\Longleftrightarrow\quad
 a\ge\lfloor R(b-w)\rfloor-u+1.
\tag{8.13}
$$

两端叶数分别为 $a+b$、$a+b+u-w$；因 $u-w\ge0$，共同预算准确归结为 $a+b\le T_+$。在给定 $b\ge w$ 的行上，允许整数 $a$ 的完整区间遂为

$$
\max\{\lceil rb\rceil,\lfloor R(b-w)\rfloor-u+1\}
\quad\le a\le\quad
\min\{\lfloor Rb\rfloor,T_+-b\}.
\tag{8.14}
$$

额外越界下端总不大于 $\lfloor Rb\rfloor$，因为 $u\ge1$、$R\ge0$ 及 $b-w\le b$。故除式 (8.12) 的行条件之外，只须使两个下端均不超过 $T_+-b$。下墙给

$$
\lceil rb\rceil\le T_+-b
\quad\Longleftrightarrow\quad
 b\le\left\lfloor\frac{T_+}{1+r}\right\rfloor.
$$

越界下端给严格的整数墙：

$$
\begin{aligned}
\lfloor R(b-w)\rfloor-u+1\le T_+-b
&\quad\Longleftrightarrow\quad
 R(b-w)<H+w-b\\
&\quad\Longleftrightarrow\quad
 (1+R)b<H+(1+R)w\\
&\quad\Longleftrightarrow\quad
 b\le w+\left\lceil\frac H{1+R}\right\rceil-1.
\end{aligned}
\tag{8.15}
$$

因此正朝向可行的行恰为 $b\in\mathcal S_k\cap[L_+,B_+]$，没有删去轴情形 $b=w$；此时 $y$ 在非零横轴上，式 (8.13) 仍是严格外墙。半群前驱为最大可行行，当且仅当 $M_k(B_+)\ge L_+$ 才有可行行。

在负朝向 $y=(a-u,b+w)$ 下，非负性要求 $a\ge u$，且 $y$ 的第二坐标为正。$a\le Rb$ 给 $a-u-R(b+w)\le-u-Rw<0$，故另一端不能落在上墙外；其非许可条件准确为

$$
a-u<r(b+w)
\quad\Longleftrightarrow\quad
 a\le u+\lceil r(b+w)\rceil-1.
\tag{8.16}
$$

较大叶数在 $x$，共同预算为 $a+b\le H$，故行上完整区间为

$$
\max\{u,\lceil rb\rceil\}
\quad\le a\le\quad
\min\{\lfloor Rb\rfloor,H-b,
 u+\lceil r(b+w)\rceil-1\}.
\tag{8.17}
$$

因 $r(b+w)>0$、$u\ge1$ 及 $\lceil r(b+w)\rceil\ge\lceil rb\rceil$，额外越界上端同时不小于 $u$ 和 $\lceil rb\rceil$。除式 (8.12) 之外，剩余条件恰为

$$
u\le\lfloor Rb\rfloor,\qquad u\le H-b,\qquad
\lceil rb\rceil\le H-b,
$$

也就是 $b\ge\lceil u/R\rceil$、$b\le H-u$、$b\le\lfloor H/(1+r)\rfloor$。所以负朝向可行的行恰为 $b\in\mathcal S_k\cap[L_-,B_-]$，存在性准确等价于 $M_k(B_-)\ge L_-$。此处 $L_->0$；$x$ 的第一坐标至少为 $u$，$y$ 的第二坐标至少为 $w$，两端均非零。$a=u$ 的非零纵轴终点也保留在式 (8.17) 中。以上推导在 $j=1$ 的 $u=w=1$、两端叶数相等时同样成立。

在固定可行行 $b$ 上，分母 $2(a+\phi b)+\sigma e_j$ 随整数 $a$ 严格增加，故唯一最大值在式 (8.14) 或 (8.17) 的上端。正朝向的 $a_{\max}(b)+\phi b$ 是

$$
\min\{\lfloor Rb\rfloor+\phi b,
 T_++(\phi-1)b\};
$$

负朝向的相应量是

$$
\min\{\lfloor Rb\rfloor+\phi b,
 H+(\phi-1)b,
 u+\lceil r(b+w)\rceil-1+\phi b\}.
$$

每个分支都随整数 $b$ 严格增加：取整项非递减，且 $\phi>1$。有限个严格递增分支的最小值也严格递增，因为较大 $b$ 的每个分支值都严格大于较小 $b$ 的最小分支值。因此即使可行行有空洞，唯一最大分母仍在最大可行行 $b_\sigma=M_k(B_\sigma)$，再取式 (8.9) 的 $a_\sigma$。

两朝向的分子均为 $|e_j|=\phi^{-j}$，所以比值为 $1/W_{j,\sigma}$。定理 8.2 把每个全局极小对限制在有限指标 $F_{j+1}\le H$ 的两朝向中，而刚才的整数区间已在每个朝向中给唯一最大分母平移。若极小对采用了该朝向的另一平移，换成最大分母平移会严格减小同一分子的比值，矛盾。这证明式 (8.11) 及全部取得对的双向刻画，也证明 $\mathcal I_k(H)$ 非空。它使用原三角域的相邻性与逐朝向的显式平移最大化，不要求枚举并排序全部来源。

所有得分比较均可在 $\mathbb Q(\phi)$ 中精确进行。复用式 (7.8) 证明中的正确幂表达 $\phi^j=F_{j-1}+F_j\phi$（$j\ge1$），置 $A=2a_\sigma+\sigma u$、$B=2b_\sigma-\sigma w$，由 $\phi^2=\phi+1$ 得

$$
W_{j,\sigma}=
(F_{j-1}A+F_jB)+(F_jA+F_{j+1}B)\phi.
\tag{8.18}
$$

两得分相等，当且仅当这两个整数系数分别相等，因为 $\phi$ 无理。比较差 $c+d\phi$ 时，比较两倍的差 $(2c+d)+d\sqrt5$ 即可。若 $2c+d$ 与 $d$ 同号，或其中一个为零，符号直接确定；两者异号时，比较 $(2c+d)^2$ 与 $5d^2$，较大绝对项的符号就是总和的符号。非零整数的平方不可能等于另一个非零整数平方的五倍，故异号比较没有未定等号。两个整数系数都为零时才是得分并列，此时必须保留全部对应项。

最后，定义 1.1 使每个非零非负取得组成都能由原预算内的完整有序树实现；证明量仅依赖组成，故同一组成的任意树代表均达到同一比值。许可端点的整数祖先非零，可以实现后施加 $\rho^{3k}$ 取得一个具有该组成的来源，但不由此断言任意选定括号树具有此语法祖先。$H<N_k$ 时没有许可来源，结论直接复用定理 7.3。证毕。

**命题 8.5（预算五的两个全局并列取得方向）。** 对 $k=1,H=5$，$r=1/2$、$R=2/3$，全部无序极小组成对恰为

$$
\{(1,2),(4,0)\},\qquad
\{(2,3),(0,4)\},\qquad
\Theta_1(5)=\frac1{9+16\phi}.
\tag{8.19}
$$

第一对采用 $(j,\sigma)=(3,+1)$，第二对采用 $(j,\sigma)=(2,-1)$；较小指标和较大指标都必须保留。

证明。$F_{j+1}\le5$ 的指标为 $j=1,2,3,4$。式 (8.7)—(8.9) 在这些指标下准确留下五项，其端点与得分为

$$
\begin{array}{c|c|c|c}
(j,\sigma)&x_{j,\sigma}&y_{j,\sigma}&W_{j,\sigma}\\\hline
(1,+1)&(2,3)&(3,2)&5+10\phi\\
(1,-1)&(2,3)&(1,4)&7+10\phi\\
(2,+1)&(1,2)&(3,1)&7+10\phi\\
(2,-1)&(2,3)&(0,4)&9+16\phi\\
(3,+1)&(1,2)&(4,0)&9+16\phi
\end{array}
\tag{8.20}
$$

其余朝向为空：$(3,-1)$ 的下界 $L_-=5$ 而 $B_-=2$；$(4,+1)$ 的 $L_+=3$ 而 $B_+=2$；$(4,-1)$ 的 $L_-=8$ 而 $B_-=0$。可行五项的前驱行分别为 $3,3,2,3,2$，都在半群 $\{2m+3n:m,n\ge0\}$ 内，表中 $a$ 是相应区间的唯一最大上端。由式 (8.18)，最后两项得分相等，且严格大于前三项。因此定理 8.4 排除所有其他方向和平移，给式 (8.19)。

两取得对的分母分别为 $5+2\phi$、$2+7\phi$，乘以 $\phi^3$、$\phi^2$ 均为 $9+16\phi$。许可点 $(1,2)$ 在闭下墙，$(2,3)$ 在闭上墙；两轴点非许可。两对叶数分别为 $(3,4)$ 和 $(5,4)$，都在初始预算五内。许可祖先分别为 $(1,0)$、$(0,1)$；定义 1.1 实现全部四个组成。这说明该并列是实际来源的全局极小值并列，而非连续锥或必要成本的并列。证毕。

**命题 8.6（预算一百零二的唯一极小对与最大指标选择失效）。** 对 $k=3,H=102$，唯一无序极小组成对为

$$
\{(34,55),(68,34)\},\qquad
\Theta_3(102)=\frac{\phi^{-8}}{102+89\phi}
=\frac1{2\phi^{18}+1}.
\tag{8.21}
$$

该对的差为 $d_8=(34,-21)$。指标九已有实际可行反标签对，但其最佳得分严格较小；仅按第一坐标预算可负担的最大指标十则没有可行朝向。因此选择最大可行指标或最大坐标可负担指标，均不能给全部预算的相对最优规则。

证明。$t=9$ 时，闭锥两列为 $(21,34)$、$(34,55)$。整数祖先 $(m,n)$ 的初始来源叶数为 $55m+89n$。预算 $102$ 只允许非零祖先 $(1,0)$、$(0,1)$，故许可来源组成恰为

$$
x_0=(21,34),\qquad x_1=(34,55),\qquad
\ell(x_0)=\phi^9,\qquad\ell(x_1)=\phi^{10}.
\tag{8.22}
$$

这里 $r=21/34$、$R=34/55$。对每个 $1\le j\le8$，$u_j\le34$、$w_j\le21$，并有 $0\le u_j-w_j\le13$；故从 $x_1$ 出发的两个朝向都非负非零，叶数为 $89\pm(u_j-w_j)\le102$。正朝向从闭上墙严格向上越界，因为 $34=R\cdot55$；负朝向严格越过下墙，因为

$$
34-r\cdot55=1/34<u_j+rw_j.
$$

因此它们都是实际反标签对。在这两个朝向中取 $\sigma=(-1)^j$，读数增量为 $+\phi^{-j}$，最大分母及得分为

$$
D_j=2\phi^{10}+\phi^{-j},\qquad
W_j=2\phi^{j+10}+1.
\tag{8.23}
$$

同一 $j$ 的另一个朝向得分小二。任何从 $x_0$ 出发的可行对，其分母至多为 $2\phi^9+\phi^{-j}<D_j$，所以式 (8.23) 是该方向的唯一最好平移和朝向。$\phi>1$ 使这些最好得分随 $j=1,\ldots,8$ 严格增加。

$j=9$ 时，$u=55,w=34$。从 $x_1$ 正向平移的叶数为 $110>102$，负向平移的第一坐标为负；从 $x_0$ 负向也有负第一坐标。唯一可行项从 $x_0$ 正向达到 $(76,0)$，叶数为 $76$，该非零横轴点非许可。因 $e_9=-\phi^{-9}$，其得分为

$$
W_9=\phi^9(2\phi^9-\phi^{-9})=2\phi^{18}-1.
\tag{8.24}
$$

$j=10$ 时，$u=89,w=55$，只有 $x_1$ 的第二坐标足够作正向平移，但平移后的叶数为 $123>102$；两个许可点的第一坐标都小于 $89$，均不能作负向平移。更高指标满足 $F_{j+1}\ge144>102$，被原叶预算排除。故 $W_8=2\phi^{18}+1$ 比 $W_9$ 恰好大二，也严格大于所有较小指标的最好得分。由定理 8.4，唯一无序极小对就是 $x_1$ 与 $x_1+d_8=(68,34)$，分母为 $102+89\phi$，给式 (8.21)。

许可端点可取实际树 $\rho^{10}(\alpha)$，其组成为 $(34,55)$，叶数为 $89$；另一端可取任何具有 $68$ 个 $\alpha$ 叶和 $34$ 个 $\beta$ 叶的完整有序树，叶数为 $102$。两端均在同一初始预算中，且前者的组成祖先是单叶 $\beta$。较高指标九的可行性与较小得分同时发生在该原来源域内，因而确实否定最大可行指标选择规则，而非仅否定某个松弛预算规则。证毕。

## 追加锚（本行以下为增补区）

## 9. 固定初始预算的有限阶段极小对与奇偶稳定

**定义 9.1（极限并列项与原来源的有限阶段比值）。** 固定整数 $k\ge1$、$H\ge N_k=F_{3k+1}$，再令整数 $L\ge0$ 变化。来源、初始叶预算与许可沿用[定义 1.1](#1-有限预算的尺度读出与逆许可分离)、[定义 2.1](#2-许可预算阶梯与深层碰撞前沿)、[定义 7.1](#7-固定许可深度的最终精确极小对与尖锐预算包络)：$\mathcal T_H$ 包含全部非空有限有序完全二叉树，叶标记为 $\alpha,\beta$，$D_H=c(\mathcal T_H)$，$\chi_k(c)=\mathbf1_{\{S^{-k}c\in\mathbb N_0^2\}}$。置

$$
\begin{gathered}
\ell_z(a,b)=a+zb,\qquad
\phi=(1+\sqrt5)/2,\qquad \psi=1-\phi,\\
m=3L+3,\qquad A_L=F_m,\qquad B_L=F_{m+1},\qquad
\xi_L=B_L/A_L,\\
R_L(x,y)=\frac{|n_L(x)-n_L(y)|}{n_L(x)+n_L(y)}
=\frac{|\ell_{\xi_L}(x-y)|}{\ell_{\xi_L}(x+y)},\qquad
n_L(a,b)=A_La+B_Lb.
\end{gathered}
\tag{9.1}
$$

允许响应仍为单个 $r\in\mathbb Q$ 满足 $|r-n_L(c(T))|\le\epsilon n_L(c(T))$，其中 $L,H,k$ 和共同的 $\epsilon\in\mathbb Q_{\ge0}$ 已知；$H$ 计 $T$ 的初始叶数。$\ell_\phi,\ell_\psi$ 是代数量，不属于允许响应的坐标。

取[定义 8.3、定理 8.4](#8-全预算相对极小对的实际域相邻性与整数平移优化)的全部最大得分项，记

$$
\begin{gathered}
\mathcal J_k(H)=\{i=(j,\sigma)\in\mathcal I_k(H):W_i=W\},\qquad
W=\max_{h\in\mathcal I_k(H)}W_h,\\
x_i=(a_\sigma,b_\sigma),\qquad
y_i=x_i+\sigma(F_{j+1},-F_j),\\
\alpha_i=x_{i,1}+y_{i,1},\qquad
\beta_i=x_{i,2}+y_{i,2},\qquad
s_i=(-1)^j,\qquad T_i(L)=A_L\alpha_i+B_L\beta_i.
\end{gathered}
\tag{9.2}
$$

$\mathcal J_k(H)$ 非空，$x_i$ 许可而 $y_i$ 非许可。其全部项均保留；按定理 8.4，$\{\{x_i,y_i\}:i\in\mathcal J_k(H)\}$ 恰为全部无序极限极小组成对。对组成 $c\in D_H$，记原来源纤维 $\mathcal F_H(c)=\{T\in\mathcal T_H:c(T)=c\}$。

**定理 9.2（整个初始域的严格比较保持与有效起点）。** 对每个整数 $H\ge1$，定义

$$
L_*(H)=\min\{L\in\mathbb N_0:F_{3L+3}\ge2H^2\}.
\tag{9.3}
$$

此最小值存在，且

$$
L_*(H)\le\min\{L\in\mathbb N_0:2^L\ge H\}.
\tag{9.4}
$$

若 $L\ge L_*(H)$，则 $\ell_{\xi_L}$ 在整个 $D_H$ 上的严格次序与 $\ell_\phi$ 相同。对 $D_H$ 中任意两个不同端点的无序组成对 $P,Q$，它们在 $\phi$ 处的相对比值若严格不等，该严格次序在 $\xi_L$ 处保持。因此，对定义 9.1 的每个固定 $k,H$，所有有限阶段极小组成对都属于 $\mathcal J_k(H)$ 给出的极限极小组成对集合。

证明。使用[母卷定义 15.5](FIBONACCI_ATOMIC_RELATION_GENERATION.md#definition-155-共轭与范数)、[定义 18.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md#definition-181-算术的两个实嵌入)的共轭及整数范数。对每个 $c=(a,b)\in D_H$，非负性与 $a+b\le H$ 给

$$
\psi H\le\ell_\psi(c)\le H.
$$

故对不同 $x,y\in D_H$，$|\ell_\psi(x-y)|\le(1-\psi)H=\phi H$。$\ell_\phi(x-y)$ 非零，其范数

$$
\ell_\phi(x-y)\ell_\psi(x-y)
=(x_1-y_1)^2+(x_1-y_1)(x_2-y_2)-(x_2-y_2)^2
$$

是非零整数，因而

$$
|\ell_\phi(x-y)|\ge\frac1{\phi H}.
\tag{9.5}
$$

[定理 7.4](#7-固定许可深度的最终精确极小对与尖锐预算包络)及[母卷命题 18.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#18-minkowski-双坐标窗口与全息解释边界)的 Fibonacci 双根式给

$$
\eta_L:=|\xi_L-\phi|=\frac{\phi^{-m}}{F_m}.
$$

$F_2<\phi^2/2$、$F_3<\phi^3/2$，由两边相同的加法递推，归纳得到 $F_n<\phi^n/2$ 对所有 $n\ge2$ 成立。因此，当 $A_L\ge2H^2$ 时，

$$
\eta_L<\frac1{2A_L^2}\le\frac1{8H^4},\qquad
|\ell_{\xi_L}(x-y)-\ell_\phi(x-y)|
\le H\eta_L<\frac1{8H^3}<\frac1{\phi H}.
\tag{9.6}
$$

最后一个严格不等式对 $H\ge1$ 成立，因为 $\phi<2<8H^2$。这证明整个来源组成域的次序保持，并排除该阶段的不同组成碰撞。

将 $P,Q$ 的端点各按 $\phi$ 读数记为 $p_+,p_-$ 和 $q_+,q_-$，高端在前。置整数系数多项式

$$
Z(z)=\ell_z(p_+)\ell_z(q_-)-\ell_z(p_-)\ell_z(q_+).
$$

其相对比值之差在这些朝向保持时等于

$$
\frac{2Z(z)}
{\ell_z(p_++p_-)\ell_z(q_++q_-)}.
\tag{9.7}
$$

若两比值在 $\phi$ 处严格不等，则 $Z(\phi)\ne0$。将 $Z$ 按 $z^2=z+1$ 归约为 $u+vz$，其中 $u,v\in\mathbb Z$，其范数 $Z(\phi)Z(\psi)=u^2+uv-v^2$ 是非零整数。任意两个 $\ell_\psi(c)$ 的乘积都在 $[\psi H^2,H^2]$ 内：异号时下界为 $\psi H^2$，同号时上界不超过 $H^2$，其中两负数相乘也因 $\psi^2<1$ 而满足该上界。遂有

$$
|Z(\psi)|\le(1-\psi)H^2=\phi H^2,
\qquad |Z(\phi)|\ge\frac1{\phi H^2}.
\tag{9.8}
$$

$\xi_L,\phi\in[1,2]$。在此区间，$0<\ell_z(c)\le2H$ 且 $0\le c_2\le H$。每个乘积 $\ell_z(c)\ell_z(d)$ 的导数在 $[0,4H^2]$ 内；$Z'$ 是两个这样的非负导数之差，故 $|Z'(z)|\le4H^2$。于是

$$
|Z(\xi_L)-Z(\phi)|
\le4H^2\eta_L<\frac1{2H^2}<\frac1{\phi H^2}.
\tag{9.9}
$$

$Z$ 的非零符号保持；结合已经证明的端点朝向保持和式 (9.7) 的正分母，全部严格比值比较都保持。每个极限落败对与一个极限极小对有严格比值差，因而不能在此阶段达到极小值。极限极小对的完整刻画直接取自定理 8.4，这证明最后一项，而无需先限制有限阶段的差方向。

最后，Fibonacci 递推给 $F_{n+3}=3F_n+2F_{n-1}\ge4F_n$（$n\ge3$），因为 $F_n\le2F_{n-1}$。由 $F_3=2$ 归纳得 $F_{3L+3}\ge2\cdot4^L$。$2^L\ge H$ 即蕴含 $F_{3L+3}\ge2H^2$，证明存在性与式 (9.4)。$F_{3L+3}$ 随 $L$ 严格增加，所以条件在 $L_*(H)$ 以后一直成立。证毕。

**定理 9.3（全部极限并列项的精确有限比较）。** 对定义 9.1 的 $k,H$，$\mathcal J_k(H)$ 的不同项具有不同指标 $j$。将共同最大得分写成 $W=U+V\phi$，则 $U,V$ 为正整数。对每个整数 $L\ge0$ 满足 $m=3L+3>\max_{i\in\mathcal J_k(H)}j_i$，有

$$
R_L(x_i,y_i)
=\frac{F_{m-j_i}}{T_i(L)}
=\frac1{U+V\,F_{m-j_i+1}/F_{m-j_i}}.
\tag{9.10}
$$

任意两项 $i=(j,\sigma)$、$h=(q,\tau)$ 的准确差为

$$
\begin{gathered}
c_{ih}=s_hF_q\beta_i-s_iF_j\beta_h\in\mathbb Z,\\
R_L(x_i,y_i)-R_L(x_h,y_h)
=\frac{(-1)^{L+1}c_{ih}}{T_i(L)T_h(L)}.
\end{gathered}
\tag{9.11}
$$

当 $i\ne h$ 时 $c_{ih}\ne0$。这些项按比值从小到大的完整次序是：先取 $j\equiv m\pmod2$ 的全部指标，按 $j$ 严格递减排列；再取另一奇偶的全部指标，按 $j$ 严格递增排列。空的一组略去。

证明。若两个并列项具有同一指标 $j$，其 $W$ 相等给 $\alpha_i+\phi\beta_i=\alpha_h+\phi\beta_h$，无理性使两整数坐标分别相等。若朝向也相同，式 (9.2) 的和、差确定相同端点，从而是同一项。若朝向相反，将正朝向记为 $i$，则

$$
2x_i+d_j=2x_h-d_j\quad\Longrightarrow\quad x_h=x_i+d_j=y_i.
$$

左边的 $x_h$ 许可，右边的 $y_i$ 非许可，矛盾。这证明同一指标没有两个极限并列项。

复用[式 (8.18)](#8-全预算相对极小对的实际域相邻性与整数平移优化)和[母卷命题 105.2 证明中的矩阵幂](FIBONACCI_ATOMIC_RELATION_GENERATION.md#1052-标量返回位置构成循环相位的子群)，有

$$
\binom UV=M^j\binom{\alpha_i}{\beta_i},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
M^j=\begin{pmatrix}F_{j-1}&F_j\\F_j&F_{j+1}\end{pmatrix}.
\tag{9.12}
$$

许可端点的第二坐标为正，故 $\beta_i>0$，而 $\alpha_i\ge0$、$j\ge1$，所以 $U,V>0$。对 $m>j$，经典 Fibonacci 加法式和 Cassini 在这些索引下给

$$
A_LF_{j+1}-B_LF_j=(-1)^jF_{m-j},\qquad
(F_{m-j},F_{m-j+1})M^j=(F_m,F_{m+1}).
$$

第一式确定绝对值分子；第二式与式 (9.12) 给 $T_i(L)=UF_{m-j}+VF_{m-j+1}$，从而证明式 (9.10)。

为得式 (9.11)，在证明中记 $N_i(z)=s_i(F_{j+1}-F_jz)$、$D_i(z)=\alpha_i+\beta_i z$。$N_i(\phi)=\phi^{-j}>0$，且 $N_i(\phi)/D_i(\phi)=1/W$。因此

$$
N_i(z)D_h(z)-N_h(z)D_i(z)
=c_{ih}(z^2-z-1),
\tag{9.13}
$$

因为左边为至多二次的整数多项式、在 $\phi$ 处为零，其二次项系数恰为 $c_{ih}$；$z^2-z-1$ 是 $\phi$ 的最小多项式。$m>j,q$ 时两个 $N(\xi_L)$ 均为正，上式就是准确比值差的交叉分子。Cassini 给

$$
\xi_L^2-\xi_L-1
=\frac{F_{m+1}^2-F_mF_{m+1}-F_m^2}{F_m^2}
=\frac{(-1)^m}{A_L^2},
$$

而 $D_i(\xi_L)=T_i(L)/A_L$、$m\equiv L+1\pmod2$，证明式 (9.11)。

最后置 $q_t=F_{t+1}/F_t$（$t\ge1$）。Fibonacci 双根残差及 Cassini 给

$$
q_t-\phi=\frac{(-1)^t\phi^{-t}}{F_t},\qquad
q_{t+2}-q_t=\frac{(-1)^{t+1}}{F_tF_{t+2}}.
\tag{9.14}
$$

故偶数 $t$ 的 $q_t$ 全部大于 $\phi$，随 $t$ 严格下降；奇数 $t$ 的 $q_t$ 全部小于 $\phi$，随 $t$ 严格上升。这正是经典收敛子的交替单调性，参见 [Hančl–Turek，*One-sided Diophantine approximations*，§3 Proposition 3.2](https://arxiv.org/pdf/1809.01013v2)：在 $\phi=[1;1,1,\ldots]$ 下，该文零起指标 $n=t-1$ 的 $p_n/q_n$ 对应这里的 $F_{t+1}/F_t$。

式 (9.10) 因 $V>0$ 而随 $q_{m-j}$ 严格下降。$m-j$ 为偶数的一组先于奇数组；在前一组中，$j$ 越大、$m-j$ 越小、$q_{m-j}$ 越大；在后一组中，$j$ 越小、$m-j$ 越大、$q_{m-j}$ 越大。由指标互异，得到所述严格全序。特别地不同项的准确比值不相等，式 (9.11) 的 $c_{ih}$ 遂非零。证毕。

**定理 9.4（完整有限极小来源集的奇偶稳定）。** 固定定义 9.1 的任意 $k,H$。令 $\mathcal J_{\mathrm o}$、$\mathcal J_{\mathrm e}$ 分别为 $\mathcal J_k(H)$ 中奇指标、偶指标的子集，定义唯一项 $i_0,i_1$ 如下：$\mathcal J_{\mathrm o}\ne\varnothing$ 时 $i_0$ 取其最大指标，否则取 $\mathcal J_{\mathrm e}$ 的最小指标；$\mathcal J_{\mathrm e}\ne\varnothing$ 时 $i_1$ 取其最大指标，否则取 $\mathcal J_{\mathrm o}$ 的最小指标。则对每个 $L\ge L_*(H)$，置 $p=L\bmod2$，全部无序有限极小组成对恰为

$$
\left\{\{x_{i_p},y_{i_p}\}\right\},\qquad
\theta_k(H,L)=\frac{F_{3L+3-j_{i_p}}}{T_{i_p}(L)}.
\tag{9.15}
$$

因而对每个固定奇偶，完整极小组成对集合自这个充分起点起稳定。两个奇偶的稳定集合不同，当且仅当 $|\mathcal J_k(H)|>1$。若 $|\mathcal J_k(H)|=1$，这个集合从起点起也恰为极限极小集合；若其大于一，每个有限阶段的极小集合从起点起都是极限极小集合的一个严格单元素子集。

对原来的有序来源对 $(T,T')\in\mathcal T_H^2$，反标签有限极小对的完整集合则为

$$
\bigl(\mathcal F_H(x_{i_p})\times\mathcal F_H(y_{i_p})\bigr)
\ \cup\
\bigl(\mathcal F_H(y_{i_p})\times\mathcal F_H(x_{i_p})\bigr).
\tag{9.16}
$$

共同有理相对误差的准确恢复阈值仍是 $\epsilon<\theta_k(H,L)$。等号处已有原来源对与共同有理报告

$$
r_*=
\frac{2n_L(x_{i_p})n_L(y_{i_p})}
{n_L(x_{i_p})+n_L(y_{i_p})}
\tag{9.17}
$$

使恢复失败。

证明。由定理 9.2，起点后的所有有限极小组成对已经落在全部极限极小对中。每个保留指标满足 $F_{j+1}\le H$，而 $F_m\ge2H^2>H$；Fibonacci 数在指标二以后严格增加，故 $m>j$。可对全部保留项应用定理 9.3。因 $m\equiv L+1\pmod2$，它的最小项在偶数 $L$ 时正是 $i_0$，在奇数 $L$ 时正是 $i_1$，且没有任何有限并列。这证明式 (9.15) 和两条固定奇偶的稳定性。

若 $\mathcal J_k(H)$ 只有一项，两种选择相同。若两种指标奇偶均存在，$i_0,i_1$ 的指标奇偶不同，故是不同项；若仅一种指标奇偶存在而总项数超过一，则两个选择分别取这一组的最大、最小指标，同样不同。定理 8.4 和定理 9.3 的指标唯一性使不同项对应不同无序组成对。这证明两个奇偶集合不同的充要条件及有限、极限集合间的准确关系。

定义 1.1 的组成映射满射到 $D_H$，每个纤维非空。有限比值与许可标签都只依赖组成，故同一取得组成的每个完整有序树代表都取得相同比值；反之，任一极小来源对的组成必须是式 (9.15) 的唯一无序对。这证明整个纤维与两种端点排列都恰由式 (9.16) 保留，而不是选定一棵代表树。许可端点的 $S^{-k}x_{i_p}$ 是非零非负整数组成，实现它再作 $3k$ 次 $\rho$ 可得到一个具有组成 $x_{i_p}$ 的树；式 (9.16) 本身允许该组成的所有叶序与括号。

恢复阈值复用[定理 7.4 的式 (7.36)](#7-固定许可深度的最终精确极小对与尖锐预算包络)。具体地，记 $u=n_L(x_{i_p})$、$v=n_L(y_{i_p})$，它们是正整数。式 (9.17) 属于 $\mathbb Q_{>0}$ 且

$$
|r_*-u|=\theta_k(H,L)u,\qquad
|r_*-v|=\theta_k(H,L)v.
$$

两端标签相反，所以等号及更大的共同误差都允许这个失败见证；严格小于阈值时，任意共同允许报告不可能同时来自反标签点。式 (9.11)、(9.15)、(9.17) 的有限阶段比较和报告均为有理数，$\mathbb Q(\phi)$ 的比较仅用于确定式 (9.2) 的数学极限并列项。所有量词保持先固定 $k,H$ 再令 $L$ 增加。证毕。

**命题 9.5（预算五的两个不同奇偶稳定集合）。** 对 $k=1,H=5$，式 (9.3) 给 $L_*(5)=3$。对每个 $L\ge3$，偶数 $L$ 的唯一无序极小组成对为 $\{(1,2),(4,0)\}$，奇数 $L$ 的唯一无序极小组成对为 $\{(2,3),(0,4)\}$。两对在所有 $L\ge0$ 下的准确比值差为

$$
R_L((1,2),(4,0))-R_L((2,3),(0,4))
=\frac{16(-1)^{L+1}}
{(5A_L+2B_L)(2A_L+7B_L)}.
\tag{9.18}
$$

证明。[命题 8.5](#8-全预算相对极小对的实际域相邻性与整数平移优化)给全部极限并列项恰为 $(3,+1)$、$(2,-1)$，共同得分为 $9+16\phi$。$F_9=34<50\le F_{12}=144$，故起点为三。定理 9.4 于是分别选择奇指标三、偶指标二，得到两个不同的稳定集合。

第一对的分子为 $2B_L-3A_L$，第二对的分子为 $2A_L-B_L$；$m\ge3$ 时 Fibonacci 比值位于 $[3/2,2)$，这两个分子均非负，包含 $m=3$ 的第一分子为零。交叉相减给

$$
\begin{aligned}
&(2B_L-3A_L)(2A_L+7B_L)
 -(2A_L-B_L)(5A_L+2B_L)\\
&\qquad=16(B_L^2-A_LB_L-A_L^2)=16(-1)^m.
\end{aligned}
$$

因此式 (9.18) 对所有所述有限阶段成立。许可端点可以分别取 $\rho^3(\alpha)$、$\rho^3(\beta)$，其叶数为三、五，组成祖先分别为 $(1,0)$、$(0,1)$；另两端分别取任意四片 $\alpha$ 叶、四片 $\beta$ 叶的完整有序树。全部来源都在原始 $\mathcal T_5$ 内，闭许可墙与非零轴标签由定义 8.1 确定。证毕。

**命题 9.6（早期阶段的非原始差与不同分母的并列）。** 对 $k=1,H=8,L=0$，$\{(1,2),(4,0)\}$ 和 $\{(2,4),(8,0)\}$ 都是原反标签域中的无序有限极小组成对，极小值为零，分母分别为十六、三十二。第二对的差为 $2d_3=(6,-4)$，不是原始整数向量。

证明。$S(1,0)^{\mathsf T}=(1,2)^{\mathsf T}$、$S(2,0)^{\mathsf T}=(2,4)^{\mathsf T}$，所以这两个端点许可；非零横轴端点均非许可。四个组成的初始叶数为三、四、六、八，均不超过八。阶段零给 $A_0=2,B_0=3$，从而

$$
n_0(1,2)=n_0(4,0)=8,\qquad
n_0(2,4)=n_0(8,0)=16.
$$

两个比值为零，非负性保证它们都达到全局最小值。其正分母为十六、三十二，而 $(8,0)-(2,4)=(6,-4)=2(F_4,-F_3)$。实际许可树可取 $\rho^3(\alpha)$ 和 $\rho^3(\langle\alpha,\alpha\rangle)$，另外两端取四片、八片 $\alpha$ 叶的完整有序树；其组成与叶预算由[定义 1.1](#1-有限预算的尺度读出与逆许可分离)实现。故有限阶段的全体极小对不具有无条件的原始差限制或唯一平移性质；定理 9.4 的结论保留了有效起点条件。证毕。

## 追加锚（本行以下为增补区）

## 10. 原始共同来源比较与有限阶段唯一响应对

**命题 10.1（低于首次跨类碰撞预算的单位响应隙与唯一组成对）。** 固定整数 $L\ge1$、$1\le k\le L$，令

$$
 m=3L+3,\qquad A=F_m,\qquad B=F_{m+1},\qquad
 v=F_{m-1}=B-A,\qquad w=F_{m-2}=A-v,
$$

并令 $r=r_k$、$R=R_k$、$K=B+\lceil Ar\rceil$。取整数预算

$$
 B\le H<K,\qquad
 D_H=\{(a,b)\in\mathbb N_0^2:1\le a+b\le H\},\qquad
 n_L(a,b)=Aa+Bb,
$$

以及定理 2.3 的初始组成标签 $\chi_k$。反标签组成对的有限阶段相对值为

$$
q_L(x,y)=\frac{|n_L(x)-n_L(y)|}{n_L(x)+n_L(y)},\qquad
 \chi_k(x)\ne\chi_k(y),\quad x,y\in D_H.
$$

记

$$
 \theta_k(H,L):=
 \min_{\substack{x,y\in D_H\\ \chi_k(x)\ne\chi_k(y)}}q_L(x,y).
$$

在单个已知阶段，对共同已知的 $\epsilon\in\mathbb Q_{\ge0}$ 和有理报告 $q\in\mathbb Q$，采用相对响应合同
$|q-n_L(c)|\le\epsilon n_L(c)$。所有达到 $\min q_L$ 的组成对都满足

$$
 |n_L(x)-n_L(y)|=1.
$$

记 $\mathcal I_k(H)$ 为定义 8.3 的已有候选槽，并在其中保留单位差方向

$$
 \mathcal I_k^{(1)}(H)=\mathcal I_k(H)\cap
 \{(m-2,+),(m-2,-),(m-1,+)\}.
 \tag{10.1}
$$

这里的槽公式、合法行和每一方向的唯一最大平移均按定义 8.3 与定理 8.4 原样使用；$\mathcal I_k^{(1)}(H)$ 非空。对其每一项 $i=(j_i,\sigma_i)$，置

$$
 D_i=n_L(x_{j_i,\sigma_i})+n_L(y_{j_i,\sigma_i}),\qquad
 D_{\max}=\max_{i\in\mathcal I_k^{(1)}(H)}D_i.
 \tag{10.2}
$$

把定理 7.4 的有限阶段阈值写作 $\theta_k(H,L)$，则

$$
 \theta_k(H,L)=\frac1{D_{\max}},\qquad
 \exists!\,i_*\in\mathcal I_k^{(1)}(H)\quad D_{i_*}=D_{\max}.
 \tag{10.3}
$$

因此唯一的无序极小组成对是
$\{x_{i_*},y_{i_*}\}$。若

$$
 \mathcal F_H(c)=\{T\in\mathcal T_H:c(T)=c\},
$$

则全部有序原始树极小对恰为

$$
 \bigl(\mathcal F_H(x_{i_*})\times\mathcal F_H(y_{i_*})\bigr)\,\cup\,
 \bigl(\mathcal F_H(y_{i_*})\times\mathcal F_H(x_{i_*})\bigr).
 \tag{10.4}
$$

这里唯一性只针对组成对；它不选择括号、叶序、地址或指定树的语法祖先，也不推出实际逆执行。进一步，两个端点的整数响应组成纤维均为单点：对 $c\in\{x_{i_*},y_{i_*}\}$，有

$$
 \{z\in D_H:n_L(z)=n_L(c)\}=\{c\}.
 \tag{10.5}
$$

若 $U=n_L(x_{i_*})$、$V=n_L(y_{i_*})$，则 $|U-V|=1$，并且已有调和有理报告

$$
 q_*=\frac{2UV}{U+V}\in\mathbb Q_{>0}
 \tag{10.6}
$$

满足

$$
 |q_*-U|=\theta_k(H,L)\,U,\qquad
 |q_*-V|=\theta_k(H,L)\,V.
 \tag{10.7}
$$

所以 $\epsilon<\theta_k(H,L)$ 足以统一恢复 $\chi_k$，而 $\epsilon=\theta_k(H,L)$ 已由同一个 $q_*$ 给出反标签允许报告。

证明。由定理 2.3，$1\le k\le L$ 时 $Ar\le v$。置 $h=H-B$，则

$$
 h<Ar\le v,\qquad H<B+v<2B,\qquad h\le v-1.
 \tag{10.8}
$$

所有 $c=(a,b)\in D_H$ 的响应都是正整数，且

$$
 1\le n_L(c)\le BH,
 \tag{10.9}
$$

因为 $B>A>0$。预算低于 $K$，再用定理 2.3 的首次碰撞结论，反标签组成不能有相同响应。

先构造单位隙见证。令

$$
 x_0=(v,A)=S^{L+1}(1,0),\qquad y_0=(0,A+w).
 \tag{10.10}
$$

前者对每个 $k\le L$ 都许可，后者是非许可轴点；两者的叶预算分别为 $B$ 与 $A+w\le B$。记 $s=(-1)^m$。定理 2.3 的式 (2.17) 给出

$$
 n_L(x_0)-n_L(y_0)=s,\qquad
 D_0:=n_L(x_0)+n_L(y_0)=2B(A+w)+s.
 \tag{10.11}
$$

矩阵递推给 $v<2w$，故

$$
 D_0-B(B+v)=B(3w-v)+s>0.
 \tag{10.12}
$$

于是 $D_0>BH$。任意反标签对的整数隙若不为一则至少为二，由 (10.9) 其相对值满足

$$
 q_L(x,y)\ge\frac2{2BH}=\frac1{BH}>\frac1{D_0}=q_L(x_0,y_0).
 \tag{10.13}
$$

所以每一个有限阶段相对极小对的原始整数响应隙都等于一。

现在处理响应组成纤维。由定理 1.4 证明中的整数核式 (1.12)，同一响应的两个不同非负组成之差是 $z(B,-A)$。在 $H<2B$ 下只能取 $|z|=1$；交换两端后可写成

$$
 c_0=(a,A+b),\qquad c_1=(a+B,b),\qquad a,b\ge0,\qquad T:=a+b\le h<v.
 \tag{10.14}
$$

两点都非许可：$a\le T<Ar\le r(A+b)$，而 $c_1$ 的第一坐标至少为 $B$、第二坐标小于 $v$，故 $a+B>Rb$。因此每个非单点响应纤维恰由这两个非许可表示组成。

另一方面，式 (1.8) 在 $j=m-2$ 给出
$Av-Bw=s$。因此满足 $n_L(d)=s$ 的全部整数差写成

$$
 d=(v,-w)+z(B,-A),\qquad z\in\mathbb Z.
$$

对 $d_1$ 使用 $|d_1|\le H<B+v$，并用 $B=2v+w>2v$，只可能有 $z=0,-1$；反向处理 $n_L(d)=-s$。所以所有单位响应差的方向只能是

$$
 \pm d_{m-2}=\pm(v,-w),\qquad
 \pm d_{m-1}=\pm(A,-v).
 \tag{10.15}
$$

对 (10.14) 的四个有向平移作直接坐标检查。由 $a<v<A$，从 $c_0$ 减去任一方向的第一坐标为负；从 $c_0$ 加上 $d_{m-1}$ 得 $(a+A,b+w)$，而 $b+w<A\le a+A$，故在上墙 $a\le Rb$ 之外；唯一可能的许可邻点是

$$
 x=c_0+d_{m-2}=(a+v,b+v).
 \tag{10.16}
$$

从 $c_1$ 作同样检查，减去 $d_{m-1}$ 给出同一个 $x$，减去 $d_{m-2}$ 给出上述上墙外点；加上 $d_{m-2}$ 时非负情形的第二坐标小于 $v$ 而第一坐标至少为 $B$，加上 $d_{m-1}$ 时第二坐标为负。因此若某个相对极小对的端点响应有非单点组成纤维，其许可端点必为 (10.16)。

这类碰撞端点可以用共同来源严格改进。令

$$
 p=F_{m-4},\qquad q_0=F_{m-3},\qquad g=(p,q_0)=S^L(1,0).
 \tag{10.17}
$$

Fibonacci 递推给

$$
 p+q_0=w,\qquad A+q_0=2v,\qquad p<v.
 \tag{10.18}
$$

因为 $k\le L$，$g$ 的 $k$ 级整数祖先非负；许可锥的加法封闭性故使 $x+g$ 许可。又由 $x$ 的上墙条件和 $R\le2/3$，

$$
 3(a+v)\le2(b+v),\qquad 3a+v\le2b.
 \tag{10.19}
$$

结合 $a<v$ 得 $b>2a$，再结合 $p<v$ 得

$$
 2(a+p)<b+2v.
 \tag{10.20}
$$

由 $r\ge1/2$，(10.18) 和 (10.20) 表明

$$
 c_0+g=(a+p,b+2v)
$$

严格位于下墙之外，因而仍为非许可组成。两组新组成仍在预算域内，因为

$$
 |x+g|_1=T+2v+w=T+B\le H,\qquad
 |c_0+g|_1=T+A+w\le T+B\le H.
 \tag{10.21}
$$

且 $n_L(g)>0$。平移前后的反标签响应隙仍为一，而响应和增加了 $2n_L(g)$，所以相对值严格减小。这与极小性矛盾；若原端点取的是 $c_1$，则先用 $n_L(c_1)=n_L(c_0)$ 换成 $c_0$，结论相同。故极小对的两个端点响应组成纤维都必须是单点，得到 (10.5)。

剩下的单位方向正是 (10.1) 所列的三个朝向。槽 $(m-2,-)$ 由 (10.10) 实际取得，故保留集非空；$(m-2,+)$、$(m-1,+)$ 只有在定义 8.3 的精确行条件可行时保留，而 $(m-1,-)$ 的许可端若为 $(a,b)$，则 $a\ge A$、$b\ge3a/2$，其预算至少为 $5A/2>B+v>H$，所以不可能出现。定理 8.4 的行端点和唯一平移证明只用到加权斜率大于一；把其中的 $\phi$ 换成当前有限响应的 $\xi=B/A>1$，同一单调性给出每个保留朝向的唯一最大 $D_i$。

由于 $D_H$ 有限且 (10.10) 给出反标签对，$\theta_k(H,L)$ 的极小值存在。每个极小对都已被证明为单位隙对，因而属于某个保留槽的方向；其响应和不超过相应的 $D_i\le D_{\max}$。有限非空的保留集有最大分母槽，且它的实际反标签端点具有单位隙，所以其比值为 $1/D_{\max}$。这在尚未要求最大槽唯一时已经给出 $\theta_k(H,L)=1/D_{\max}$。任何单位隙对若不是相应槽的唯一最大平移，或来自较小分母的保留槽，其比值都严格大于 $1/D_{\max}$。

对每个达到此值的对，记其两个正整数响应为 $U,V$。由 $|U-V|=1$ 和 $U+V=D_{\max}$，$D_{\max}$ 是同一个奇数，且所有极小对有同一无序响应对 $\{(D_{\max}-1)/2,(D_{\max}+1)/2\}$。前面已证明每个极小端点的响应组成纤维为单点，所以这两个响应确定同一个无序组成对。不同保留槽不能给出该同一组成对：$d_{m-2}=(v,-w)$ 与 $d_{m-1}=(A,-v)$ 的行列式为 $Aw-v^2=(-1)^{m-1}\ne0$，两方向不平行；而 $(m-2,+)$ 与 $(m-2,-)$ 都按定义 8.1、8.3 以唯一的许可端点为起点，若两者给同一无序对，就必须从该同一起点到同一非许可端点同时取 $d_{m-2}$ 与 $-d_{m-2}$，与 $d_{m-2}\ne0$ 矛盾。因此最大分母槽唯一，完成 (10.2)–(10.3) 及唯一无序组成对的结论。每个端点组成的全部完整有序树代表具有同一响应与许可标签，故全部有序原始树极小对恰为 (10.4)。这里使用的全部树存在性仍是定义 1.1 的完整有序树实现，未把组成祖先提升为指定树的逆执行。

最后，(10.6)–(10.7) 是定理 7.4 式 (7.36) 对 $|U-V|=1$ 的直接应用。定理 7.4 的有限候选纤维判据给出 $\epsilon<\theta_k(H,L)$ 的充分性；在等号处，同一个有理调和报告同时满足两端的闭相对误差约束，因而反标签仍不可统一恢复。证毕。

## 追加锚（本行以下为增补区）

## 11. 临界深度窗口的预算、奇偶与完整响应纤维

**命题 11.1（临界深度的有限相对极小对与等号报告候选）。** 沿用[定义 1.1](#1-有限预算的尺度读出与逆许可分离)的全部非空完整有序树、初始叶预算、组成映射及响应，并沿用[定义 2.1、定理 2.3](#2-许可预算阶梯与深层碰撞前沿)的组成祖先许可。对每个整数 $L\ge1$，置

$$
\begin{gathered}
k=L+1,\qquad m=3L+3,\qquad
A=F_m,\quad B=F_{m+1},\quad v=F_{m-1},\quad w=F_{m-2},\\
s=(-1)^m,\qquad N=F_{2m},\qquad
x_0=(v,A),\quad y_0=(0,A+w),\quad y_1=(2v,v),\quad y_2=(B,w).
\end{gathered}
\tag{11.1}
$$

本命题中的 $B$ 是标量响应权重。取任意整数 $B\le H<B+v$，保持原域
$\mathcal T_H$、$D_H=\{(a,b)\in\mathbb N_0^2:1\le a+b\le H\}$、$S=M^3$、$\chi_k(c)=\mathbf1_{\{S^{-k}c\in\mathbb N_0^2\}}$ 及 $n_L(a,b)=Aa+Bb$。在单个共同已知阶段 $L$，对共同已知的 $\epsilon\in\mathbb Q_{\ge0}$，只观察一个 $r\in\mathbb Q$，合同为 $|r-n_L(c)|\le\epsilon n_L(c)$。统一恢复指存在同一个 $P:\mathbb Q\to\{0,1\}$，对全部 $T\in\mathcal T_H$ 及其全部允许报告输出 $P(r)=\chi_k(c(T))$。记

$$
\begin{gathered}
\mathcal F_H(c)=\{T\in\mathcal T_H:c(T)=c\},\qquad
\Gamma(U)=\{c\in D_H:n_L(c)=U\},\\
q_L(x,y)=\frac{|n_L(x)-n_L(y)|}{n_L(x)+n_L(y)},\qquad
\theta=\theta_k(H,L)=
\min_{\substack{x,y\in D_H\\\chi_k(x)\ne\chi_k(y)}}q_L(x,y).
\end{gathered}
$$

则许可组成与三个严格有序的预算阈值准确为

$$
\{c\in D_H:\chi_k(c)=1\}=\{x_0\},\qquad
B<3v<B+w=2A<B+v.
\tag{11.2}
$$

三个相邻响应的完整组成纤维为

$$
\begin{aligned}
\Gamma(N)&=\{x_0\},\\
\Gamma(N-s)&=
\begin{cases}
\{y_0\},&B\le H<B+w,\\
\{y_0,y_2\},&B+w\le H<B+v,
\end{cases}\\
\Gamma(N+s)&=
\begin{cases}
\varnothing,&B\le H<3v,\\
\{y_1\},&3v\le H<B+v.
\end{cases}
\end{aligned}
\tag{11.3}
$$

所有反标签有限相对极小对的响应隙都等于一。令 $Y$ 表示这些极小对的全部非许可组成端点，则

$$
(\theta,Y)=
\begin{cases}
\bigl(\dfrac1{2N+1},\{y_0\}\bigr),
 &L\text{ 偶数},\ B\le H<B+w,\\[3pt]
\bigl(\dfrac1{2N+1},\{y_0,y_2\}\bigr),
 &L\text{ 偶数},\ B+w\le H<B+v,\\[3pt]
\bigl(\dfrac1{2N-1},\{y_0\}\bigr),
 &L\text{ 奇数},\ B\le H<3v,\\[3pt]
\bigl(\dfrac1{2N+1},\{y_1\}\bigr),
 &L\text{ 奇数},\ 3v\le H<B+v.
\end{cases}
\tag{11.4}
$$

全部无序极小组成对、全部有序极小组成对以及全部有序原始树极小对分别为

$$
\begin{gathered}
\bigl\{\{x_0,y\}:y\in Y\bigr\},\qquad
\bigcup_{y\in Y}\{(x_0,y),(y,x_0)\},\\
\bigcup_{y\in Y}
\left[
\bigl(\mathcal F_H(x_0)\times\mathcal F_H(y)\bigr)
\cup
\bigl(\mathcal F_H(y)\times\mathcal F_H(x_0)\bigr)
\right].
\end{gathered}
\tag{11.5}
$$

因此无序极小响应对总是唯一；无序极小组成对恰在 $L$ 偶数且 $H\ge B+w$ 时有两对，其余分支只有一对。这里所有 $\mathcal F_H(c)$ 都保留全部叶序和完整二叉括号，没有选择树代表。

对任意 $y\in Y$，响应 $V_*=n_L(y)$ 与 $y$ 的选择无关，且 $|V_*-N|=1$。使用[定理 7.4 式 (7.36)](#7-固定许可深度的最终精确极小对与尖锐预算包络)的调和报告，令

$$
\begin{gathered}
r_* =\frac{2NV_*}{N+V_*}\in\mathbb Q_{>0},\qquad
\mathcal C_\theta(r_*)=\{c\in D_H:|r_*-n_L(c)|\le\theta n_L(c)\},\\
\mathcal C_\theta^{\mathrm{tree}}(r_*)=
\{T\in\mathcal T_H:|r_*-n_L(c(T))|\le\theta n_L(c(T))\}.
\end{gathered}
$$

在等号合同 $\epsilon=\theta$ 下，完整候选集准确为

$$
\mathcal C_\theta(r_*)=\{x_0\}\cup Y,\qquad
\mathcal C_\theta^{\mathrm{tree}}(r_*)=
\mathcal F_H(x_0)\cup\bigcup_{y\in Y}\mathcal F_H(y).
\tag{11.6}
$$

在上述同一原始来源域和报告合同上，统一恢复 $\chi_k$ 当且仅当 $\epsilon<\theta$。许可目标只断言非负组成祖先存在；它不识别指定完整树的替换祖先、规范地址或实际逆执行。

证明。直接使用[定理 2.3 证明中的 Fibonacci 矩阵幂与临界窗口式 (2.12)](#2-许可预算阶梯与深层碰撞前沿)。由于 $3k=m$，每个许可组成都可且只能写成 $c=M^m(p,q)^{\mathsf T}$，其中 $(p,q)\in\mathbb N_0^2\setminus\{(0,0)\}$，并且

$$
M^m=\begin{pmatrix}v&A\\ A&B\end{pmatrix},\qquad
|c|_1=Bp+(A+B)q.
\tag{11.7}
$$

$m\ge6$，故 $w<v<2w$，其中第二个严格不等式来自 $v=w+F_{m-3}$ 及 $F_{m-3}<w$。递推给 $A=v+w$、$B=2v+w$，于是 $B+v<2B$ 且 $B+v<A+B$。因此 $|c|_1\le H<B+v$ 排除 $q\ge1$ 和 $p\ge2$；非零性迫使 $(p,q)=(1,0)$。反向，此祖先给 $c=x_0$，其叶数为 $v+A=B\le H$。这证明唯一许可组成。又有

$$
3v-B=v-w>0,\qquad
(B+w)-3v=2w-v>0,\qquad
(B+v)-(B+w)=v-w>0,
$$

且 $B+w=2(v+w)=2A$，证明 (11.2) 的全部阈值。

直接复用[定理 2.3 式 (2.17)](#2-许可预算阶梯与深层碰撞前沿)中的倍角响应与 Cassini 残差 $Av-Bw=s$，在本证明内得到

$$
\begin{aligned}
n_L(x_0)&=A(v+B)=N=F_{2m}\ge F_{12}=144,\\
n_L(y_0)&=B(A+w)=N-s,\\
n_L(y_2)&=AB+Bw=N-s,\\
n_L(y_1)&=2Av+Bv=N+s.
\end{aligned}
\tag{11.8}
$$

接下来对每个响应保留全部整数表示，而非只取上式的一个见证。由[定理 1.4 证明的整数核式 (1.12)](#1-有限预算的尺度读出与逆许可分离)，同一响应的全部整数解由任意一个解加 $t(B,-A)$、$t\in\mathbb Z$ 得到。响应 $N$ 的解为 $x_0+t(B,-A)$；由 $v<B$，非负第一坐标迫使 $t\ge0$，由第二坐标 $A-tA\ge0$ 迫使 $t\le1$。故其全部非负解为 $x_0$ 和 $(B+v,0)$。后一组成的叶数为 $B+v>H$，所以 $\Gamma(N)=\{x_0\}$。

响应 $N-s$ 的解为 $y_0+t(B,-A)$。第一坐标为 $tB$，迫使 $t\ge0$；$0<w<A$ 和第二坐标 $A+w-tA\ge0$ 迫使 $t\le1$。全部非负解恰为 $y_0,y_2$。$|y_0|_1=A+w<B$，故 $y_0$ 始终在域内；$|y_2|_1=B+w$，所以 $y_2$ 恰在 $H\ge B+w$ 时加入。响应 $N+s$ 的解为 $y_1+t(B,-A)$。$2v<B$ 排除全部 $t<0$，$v<A$ 排除全部 $t>0$，因此只剩 $y_1$；其叶数为 $3v$，恰在 $H\ge3v$ 时加入。所有这些组成都非空，且 $y_0,y_1,y_2$ 与 $x_0$ 不同；已经证明的唯一许可组成说明它们在各自合法时都非许可。于是 (11.3) 是完整纤维裁剪。

任一反标签对都含 $x_0$。设另一端的正整数响应为 $T$。由 $\Gamma(N)=\{x_0\}$，其整数隙 $d=|T-N|$ 至少为一。若 $d\ge2$，则 $T\le N+d$，并且

$$
\frac{d}{N+T}
\ge\frac{d}{2N+d}
\ge\frac1{N+1}
>\frac1{2N-1}.
\tag{11.9}
$$

中间不等式等价于 $N(d-2)\ge0$；最后一步使用 $N\ge144>2$。另一方面，始终合法的 $y_0$ 给单位隙及比值 $1/(2N-s)\le1/(2N-1)$。所以全部 $d\ge2$ 的对严格劣于这个实际反标签见证，所有极小对只能取 $T=N-1$ 或 $T=N+1$。当高响应 $N+1$ 存在时，其比值 $1/(2N+1)$ 严格小于低响应的 $1/(2N-1)$，故只保留高响应的全部组成纤维；高响应不存在时，始终存在的低响应纤维全部达到极小值。

因 $m=3L+3$，$L$ 偶数时 $s=-1$，所以高响应是 $N-s$，其全部组成由 $H=B+w$ 分成 $\{y_0\}$ 和 $\{y_0,y_2\}$；另一阈值 $3v$ 只加入较差的低响应。$L$ 奇数时 $s=1$，所以在 $H<3v$ 只有低响应 $N-s$，且 $3v<B+w$ 保证其纤维仅为 $\{y_0\}$；在 $H\ge3v$ 高响应纤维恰为 $\{y_1\}$，其后加入的 $y_2$ 仍是较差的低响应。这证明 (11.4)，并证明唯一无序极小响应对和所述组成对数量。

定义 1.1 的组成映射 $c:\mathcal T_H\to D_H$ 满射，每个纤维非空。树的许可标签和响应都通过 $c$ 因子化。因此原始树极小对的组成必为已经列尽的极小组成对；反向，对任何 $y\in Y$，$\mathcal F_H(x_0)$ 和 $\mathcal F_H(y)$ 中的任意两棵树都有相反标签和相应极小比值。两个次序都合法，得到 (11.5) 的两个完整 Cartesian 乘积。这两方向只用原域的全部树，未附加叶序、括号、地址或指定树的替换像条件。

现在 $V_*$ 在每个分支固定为 $N-1$ 或 $N+1$，且 $\theta=1/(N+V_*)<1$。调和报告及两端误差等式直接复用[定理 7.4 式 (7.36)](#7-固定许可深度的最终精确极小对与尖锐预算包络)。对任意正整数真实响应 $T$，等号合同等价于

$$
\frac{r_*}{1+\theta}\le T\le\frac{r_*}{1-\theta},\qquad
\frac{r_*}{1+\theta}=\min\{N,V_*\},\qquad
\frac{r_*}{1-\theta}=\max\{N,V_*\}.
\tag{11.10}
$$

两端是相邻整数，所以允许的整数真实响应准确为 $N,V_*$。用 (11.3) 和各分支的 $Y$ 裁剪，便得 (11.6) 的完整组成候选集；再取 $c$ 的全部逆像便得完整树候选集。

若 $\epsilon<\theta$，同一个报告下出现反标签候选 $x,y$ 会由三角不等式给
$|n_L(x)-n_L(y)|\le\epsilon(n_L(x)+n_L(y))$，与极小值定义矛盾。因 $D_H$ 有限，非空候选集有共同标签；输出该标签，并在空候选集输出零，即得所需总恢复器。若 $\epsilon\ge\theta$，报告 $r_*$ 对 $x_0$ 及任意 $y\in Y$ 都允许，而它们的标签相反，故同一个恢复器不可能对二者均正确。由满射，两端均有原域实际树代表，证明恢复充要条件。

[命题 10.1](#10-原始共同来源比较与有限阶段唯一响应对)使用 $g=S^L e_1$ 的共同平移，其中 $e_1=(1,0)^{\mathsf T}$；其许可保持条件是 $k\le L$。在本命题的 $k=L+1$ 下，$x_0=S^{L+1}e_1$，而

$$
S^{-k}(x_0+S^Le_1)
=e_1+S^{-1}e_1
=(1,0)^{\mathsf T}+(-3,2)^{\mathsf T}
=(-2,2)^{\mathsf T}.
\tag{11.11}
$$

负的第一祖先坐标否定组成许可。矩阵幂给 $|S^Le_1|_1=w$，故即使 $H\ge B+w$ 使 $x_0+S^Le_1$ 仍在原预算域内，该平移也不能保持反标签对的许可端点。这是许可锥的精确适用域边界。

具体地，在同一命题取 $L=2,k=3,H=68$，则 $m=9$、$A=34$、$B=55$、$v=21$、$w=13$、$s=-1$、$N=2584$，且

$$
\begin{gathered}
55<63<68=2A<76,\qquad
x_0=(21,34),\quad y_0=(0,47),\quad y_1=(42,21),\quad y_2=(55,13),\\
\Gamma(2584)=\{(21,34)\},\qquad
\Gamma(2585)=\{(0,47),(55,13)\},\qquad
\Gamma(2583)=\{(42,21)\},\\
\theta=\frac1{5169},\qquad Y=\{(0,47),(55,13)\},\qquad
r_* =\frac{2\cdot2584\cdot2585}{5169}.
\end{gathered}
\tag{11.12}
$$

这里 $n_L(a,b)=34a+55b$，三条纤维逐项由上述整数核裁剪取得；$y_1$ 虽然合法，响应较低而不达到相对极小值。无序极小组成对恰为 $\{x_0,y_0\}$、$\{x_0,y_2\}$，而等号报告的组成候选恰为 $\{x_0,y_0,y_2\}$，树候选和两个次序的全部树极小对仍分别由 (11.6)、(11.5) 给出。证毕。

## 追加锚（本行以下为增补区）

## 12. 完整树替换像的计数密度、祖先混合与共轭来源偏差

**定义 12.1（完整来源纤维与两个叶数尺度）。** 沿用[定义 1.1](#1-有限预算的尺度读出与逆许可分离)的非空有限有序完全二叉树集合 $\mathcal T$、叶标签 $\alpha,\beta$、组成 $c$ 及保持左右括号的替换 $\rho$。树的相等取原始自由语法相等，保留每个括号和每片叶的次序；其完整代码与全部路径读数的等价刻画分别由[母卷定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)供应。对 $a,b\in\mathbb N_0$、$a+b\ge1$，记

$$
\mathcal T_{a,b}=\{T\in\mathcal T:c(T)=(a,b)^{\mathsf T}\}.
$$

取任意整数 $k\ge1$、$p,q\ge0$、$t=p+q\ge1$，置

$$
\begin{gathered}
d=3k,\qquad
\binom ab=M^d\binom pq=S^k\binom pq,
\qquad M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad S=M^3,\\
a=F_{d-1}p+F_dq,\qquad
b=F_dp+F_{d+1}q,\qquad n=a+b,\\
\mathcal I_{k,p,q}=\mathcal T_{a,b}\cap\rho^d(\mathcal T),
\qquad R_{k,p,q}=\frac{|\mathcal I_{k,p,q}|}{|\mathcal T_{a,b}|},
\qquad N_{t,p}=C_{t-1}\binom tp,\quad
C_m=\frac1{m+1}\binom{2m}{m}.
\end{gathered}
\tag{12.1}
$$

Fibonacci 编号仍为 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。若使用既有有限预算 $H$，要求 $H\ge n$；待判定的初始树纤维 $\mathcal T_{a,b}$ 因而包含在 $\mathcal T_H$ 内。这里 $d$ 是检验该初始树的组成祖先及语法祖先的替换深度，不是数量观察的末端阶段 $L$。组成许可沿用[定义 2.1、定理 2.3](#2-许可预算阶梯与深层碰撞前沿)；$R_{k,p,q}$ 是该许可组成纤维内部指定树属于替换像的计数比例。

对连续参数 $x\in[0,1]$ 定义

$$
\begin{gathered}
u_k(x)=F_{d-1}x+F_d(1-x),\qquad
v_k(x)=F_dx+F_{d+1}(1-x),\\
\ell_k(x)=u_k(x)+v_k(x)
=F_{d+1}x+F_{d+2}(1-x),\qquad
 y_k(x)=\frac{u_k(x)}{\ell_k(x)},\\
h(z)=-z\log z-(1-z)\log(1-z),\quad h(0)=h(1)=0,
\qquad g(z)=\log4+h(z),\\
J_k(x)=\ell_k(x)g(y_k(x))-g(x),\qquad
\Gamma_k(x)=\frac{J_k(x)}{\ell_k(x)},\\
\phi=\frac{1+\sqrt5}{2},\qquad
\eta=\phi^{-2},\qquad B=g(\eta).
\end{gathered}
\tag{12.2}
$$

全部对数为自然对数。对整数来源参数，以下简写 $x=p/t$、$\ell=\ell_k(x)=n/t$、$y=y_k(x)=a/n$。连续延拓 $J_k$ 比较相同祖先叶数尺度上的指数损失；只有网格 $x=p/t$ 对应实际整数组成。$R_{k,p,q}$ 的定义不赋予实际来源概率律。若另给 $\mathcal T_{a,b}$ 上的均匀律，它才等于该律下的替换像概率；组成、代码、路径读数及计数比例均不自行授权实际逆执行，也不指定物理解释。

**定理 12.1（许可纤维内实际像的统一密度、混合曲率与黄金归一化边界）。** 在定义 12.1 的全部参数范围内，实际像与祖先纤维满足

$$
\mathcal I_{k,p,q}=\rho^d(\mathcal T_{p,q}),\qquad
|\mathcal I_{k,p,q}|=N_{t,p}.
\tag{12.3}
$$

对每个允许的三元组存在实数 $e_{k,p,q}$，使

$$
\boxed{\quad
R_{k,p,q}
=4\pi\sqrt2\,N_{t,p}n^2\sqrt{y(1-y)}
 \exp\bigl(-ng(y)+e_{k,p,q}\bigr),
\qquad |e_{k,p,q}|\le\frac2n.
\quad}
\tag{12.4}
$$

祖先因子 $N_{t,p}$ 在本式中保持精确，包括 $p=0$、$q=0$、$t=1$ 及有界的 $\min(p,q)$。删除指数余项后，所得近似与真实 $R_{k,p,q}$ 的相对误差至多 $\exp(2/n)-1$，所以沿任意允许的 $n\to\infty$ 序列均为相对等价；这包括 $t$ 固定、$k\to\infty$，不要求两个祖先坐标同时增长。

其统一指数损失满足

$$
\begin{gathered}
\left|\log R_{k,p,q}+tJ_k(x)\right|
\le3\log(n+1)+3,\\
\Gamma_k(x)\ge\gamma_*:=\log2+h(1/3)>0.
\end{gathered}
\tag{12.5}
$$

故沿任意 $n\to\infty$ 的允许序列，$R_{k,p,q}\to0$，且 $-\log R_{k,p,q}/n$ 与 $\Gamma_k(x)$ 的差一致趋零。递归深度与祖先规模同时变化时，进一步有

$$
\boxed{\quad
\left|-\frac{\log R_{k,p,q}}n-B\right|
\le\frac{\log8}{F_{d+1}}
 + (\log2)\phi^{-2d}
 +\frac{3\log(n+1)+3}{n}.
\quad}
\tag{12.6}
$$

因此 $k\to\infty$ 时，每片目标叶的实际像指数损失一致趋于 $B$，一致性覆盖所有非零祖先规模及两类祖先叶的全部混合比例。

在 $0<x<1$ 上，连续祖先速率的曲率为

$$
J_k''(x)
=\frac1{x(1-x)}
 -\frac1{\ell_k(x)u_k(x)v_k(x)}
\ge\frac{23}{6}.
\tag{12.7}
$$

每个 $k\ge1$ 恰有一个连续最小点 $x_k\in(1/2,1)$。令 $y_k^*=y_k(x_k)$，它由

$$
\frac{x_k}{1-x_k}
=4^{F_d}(y_k^*)^{-F_{d-2}}(1-y_k^*)^{-F_{d-1}}
\tag{12.8}
$$

确定，并对所有 $x\in[0,1]$ 满足

$$
J_k(x)\ge J_k(x_k)+\frac{23}{12}(x-x_k)^2.
\tag{12.9}
$$

因此两个纯祖先端点均有严格更大的连续指数损失。对每个固定 $k$，整数网格的最大密度仅在指数尺度上满足

$$
\lim_{t\to\infty}
-\frac1t\log\left(\max_{p\in\{0,\ldots,t\}}
R_{k,p,t-p}\right)=J_k(x_k).
\tag{12.10}
$$

若比较时保留共同预算 $H_t$，须取 $H_t\ge F_{d+2}t$，以包含整张祖先网格对应的初始树纤维。本式不指定有限 $t$ 的精确最大点，也不将固定 $k$ 的网格结论扩展成增长 $k$ 的最优前因子。连续最小点的少数祖先叶比例由同一个 $B$ 控制，且对所有 $k\ge1$ 有

$$
\boxed{\quad
\left|-\log(1-x_k)-F_d B\right|\le\frac5{F_d}.
\quad}
\tag{12.11}
$$

定义带符号的共轭来源偏差及黄金组成归一化因子

$$
\begin{gathered}
D_{k,p,q}=a-\eta n
=(-1)^k\phi^{-(d+1)}(p-q/\phi),\\
\mathcal G_{k,p,q}
=4\pi\sqrt2\,N_{t,p}n^2\sqrt{\eta(1-\eta)}\exp(-nB).
\end{gathered}
\tag{12.12}
$$

它们对所有参数同时满足

$$
\boxed{\quad
\left|\log\frac{R_{k,p,q}}{\mathcal G_{k,p,q}}
 + (\log\phi)D_{k,p,q}\right|
\le\frac94\frac{D_{k,p,q}^2}{n}
 +\frac34\frac{|D_{k,p,q}|}{n}+\frac2n.
\quad}
\tag{12.13}
$$

对任意允许的整数参数序列 $(k_i,p_i,q_i)$，只要求 $k_i\to\infty$，不限制 $t_i=p_i+q_i$ 的增长，则

$$
\boxed{\quad
\frac{R_{k_i,p_i,q_i}}{\mathcal G_{k_i,p_i,q_i}}\longrightarrow1
\quad\Longleftrightarrow\quad D_{k_i,p_i,q_i}\longrightarrow0.
\quad}
\tag{12.14}
$$

更一般地，对任意 $z\in\mathbb R$，$D_{k_i,p_i,q_i}\to z$ 时该比值趋于 $\phi^{-z}$；偏差趋于 $+\infty$ 时比值趋于零，偏差趋于 $-\infty$ 时比值趋于 $+\infty$。每个有限 $z$ 都可由合法整数组成达到。允许抵消的混合祖先可以在规模无上界的同时令 $D_{k_i,p_i,q_i}\to0$，故黄金组成归一化的相对有效性由此联合来源偏差决定，不能仅由深度或祖先总规模代替。

证明。由[母卷定理 3.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md#theorem-34-组成观察下的闭合动力学)的组成动力学及其迭代，有 $c\rho^d=M^dc$。直接复用[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的完整树替换单射性，$\rho^d$ 仍为单射。若 $U\in\mathcal T_{a,b}$ 且 $U=\rho^d(T)$，则 $M^dc(T)=M^d(p,q)^{\mathsf T}$。因 $\det M=-1$，$M^d$ 在整数上可逆，强制 $c(T)=(p,q)^{\mathsf T}$。反向每棵 $\mathcal T_{p,q}$ 的树都映到 $\mathcal T_{a,b}$。于是 $\rho^d$ 在这两个集合之间给出到 $\mathcal I_{k,p,q}$ 的双射；这一步使用原有单射，不以矩阵可逆性替代树语法单射。

具有 $s\ge1$ 片有序叶的完全二叉树形状有 $C_{s-1}$ 个，复用 [Flajolet–Sedgewick，《Analytic Combinatorics》，第 6–7 页](https://algo.inria.fr/flajolet/Publications/book.pdf) 的 Catalan 计数及 [Stanley，《Enumerative Combinatorics》第二卷，习题 6.19(b)、(d)](https://math.mit.edu/~rstan/ec/catalan.pdf) 的二叉括号与平面完全二叉树对应。每个形状有固定的从左到右叶序，任选 $a$ 个位置放置 $\alpha$ 给 $\binom{s}{a}$ 种着色。这既不将括号取商，也不将叶位置取商。因此这些既有计数在当前纤维上给

$$
|\mathcal T_{a,b}|=C_{n-1}\binom na,
\qquad |\mathcal I_{k,p,q}|=|\mathcal T_{p,q}|=C_{t-1}\binom tp,
\qquad
R_{k,p,q}=\frac{N_{t,p}}{C_{n-1}\binom na}.
\tag{12.15}
$$

这证明（12.3），同时给出后续联合估计的精确分子。所有纤维非空且有限，故其对数有定义。

由既有深度许可锥，$S^k(p,q)^{\mathsf T}$ 是一步许可组成；一步矩阵的两列比例给

$$
\frac13\le y\le\frac25,\qquad
n\ge F_{d+1}t\ge3t.
\tag{12.16}
$$

同样的界在整个连续区间上成立。特别地 $u_k(x)\ge F_{d-1}\ge1$、$v_k(x)\ge F_d\ge2$、$\ell_k(x)\ge F_{d+1}\ge3$，没有零目标坐标。经典双根表达直接复用[母卷定义 18.1、命题 18.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#18-minkowski-双坐标窗口与全息解释边界)的两个嵌入：

$$
F_s=\frac{\phi^s-(-\phi^{-1})^s}{\sqrt5}.
$$

代入 $a-\eta n$，两个来源列的系数分别为 $(-1)^d\phi^{-(d+1)}$ 和 $-(-1)^d\phi^{-(d+2)}$，给出（12.12）；$(-1)^d=(-1)^k$。递推与 $\phi^2=\phi+1$ 给 $F_s\ge\phi^{s-2}$（$s\ge2$）及 $F_s\le\phi^s$（$s\ge0$）。从两列各自的偏差除以叶数，并按其叶数作非负加权平均，遂有

$$
|y-\eta|=\frac{|D_{k,p,q}|}{n}\le\phi^{-2d}.
\tag{12.17}
$$

具体地，第一列界为 $\phi^{-(d+1)}/F_{d+1}\le\phi^{-2d}$，第二列界为 $\phi^{-(d+2)}/F_{d+2}\le\phi^{-2d-2}$。该论证也覆盖连续混合。

下面只在正整数上调用 [Robbins，*A Remark on Stirling's Formula*，第 26 页式（1）–（2）](https://dornsife.usc.edu/sergey-lototsky/wp-content/uploads/sites/211/2024/02/Stirling-Robbins.pdf)：

$$
m!=\sqrt{2\pi}\,m^{m+1/2}e^{-m}\exp(r_m),
\qquad \frac1{12m+1}<r_m<\frac1{12m},\qquad m\ge1.
\tag{12.18}
$$

本证明没有把此供应扩展到零或任意正实数。由标准恒等式 $C_{m-1}=\binom{2m}{m}/(4m-2)$，其对数形式给

$$
\begin{gathered}
C_{m-1}=\frac{4^m}{4\sqrt\pi\,m^{3/2}}\exp(E_m),\\
E_m=-\log\left(1-\frac1{2m}\right)+r_{2m}-2r_m,
\qquad 0<E_m<\frac1m.
\end{gathered}
\tag{12.19}
$$

最后的界可直接从供应余项取得：下界用 $-\log(1-1/(2m))\ge1/(2m)$ 和 $2r_m<1/(6m)$；上界用

$$
-\log\left(1-\frac1{2m}\right)
=\sum_{j\ge1}\frac1{j2^jm^j}\le\frac{\log2}{m},
\qquad r_{2m}<\frac1{24m},
\qquad \log2+1/24<1.
$$

因此 $m=1$ 同样在范围内。在目标二项式上 $a,b,n\ge1$，由（12.18）得

$$
\binom na
=\frac{\exp(nh(y))}{\sqrt{2\pi n y(1-y)}}
 \exp(r_n-r_a-r_b).
$$

乘上（12.19）在 $m=n$ 的值，再取倒数，得到（12.4），其中

$$
e_{k,p,q}=-E_n-r_n+r_a+r_b.
$$

因为 $y\in[1/3,2/5]$，有 $1/a+1/b\le9/(2n)$。故

$$
-\frac{13}{12n}<e_{k,p,q}<\frac3{8n},
$$

足以给出所用的 $2/n$。祖先二项式没有作渐近替换，所以纯祖先、固定少数叶、固定 $t$ 及所有端点仍由同一式覆盖。对正近似因子乘上 $\exp(e_{k,p,q})$，即得所述相对误差界。

为取得整个祖先区间上的指数估计，置

$$
\omega_{t,p}=\binom tp\exp(-th(p/t)).
$$

有

$$
\frac1{t+1}\le\omega_{t,p}\le1.
\tag{12.20}
$$

$p=0,t$ 时直接等于一；若 $0<p<t$，二项式恒等式 $\sum_{j=0}^t\binom tj x^j(1-x)^{t-j}=1$ 在 $x=p/t$ 的最大项位于 $j=p$。相邻项的比值为 $(t-j)x/((j+1)(1-x))$，随 $j$ 递减，在 $j=p-1$ 时大于一，在 $j=p$ 时小于一。这最大项就是 $\omega_{t,p}$，所以至少为 $1/(t+1)$，至多为一。这只是一条有限多项式不等式，没有给实际树来源赋律。

把（12.19）用于 $m=t$，并保持 $\omega_{t,p}$ 精确，（12.4）成为对数恒等式

$$
\begin{aligned}
\log R_{k,p,q}+tJ_k(x)
={}&2\log n-\frac32\log t
 +\frac12\log\bigl(2\pi y(1-y)\bigr)\\
&+\log\omega_{t,p}+E_t+e_{k,p,q}.
\end{aligned}
\tag{12.21}
$$

在（12.16）的区间内，$0<\tfrac12\log(2\pi y(1-y))<1/2$。上界由 $\log\omega\le0$、$E_t\le1$、$|e|\le2/3$ 得到 $2\log n+3$；下界由 $\log\omega\ge-\log(t+1)$、$E_t\ge0$ 得到 $-\tfrac52\log(n+1)-2/3$。两者给（12.5）的绝对误差。又因 $h(x)\le\log2$、$h(y)\ge h(1/3)$ 及 $\ell\ge3$，

$$
\Gamma_k(x)=g(y)-\frac{g(x)}\ell
\ge\log4+h(1/3)-\frac{\log8}{3}=\gamma_*.
$$

正的统一下界和（12.5）证明任意 $n\to\infty$ 序列的衰减。$\eta\in[1/3,2/5]$，且在此区间 $|h'|\le\log2$。由（12.17）、$\ell\ge F_{d+1}$ 及 $g(x)\le\log8$，

$$
|\Gamma_k(x)-B|
\le (\log2)\phi^{-2d}+\frac{\log8}{F_{d+1}}.
$$

再用（12.5）除以 $n$，得到（12.6）。函数 $(3\log(n+1)+3)/n$ 对 $n\ge1$ 递减，而 $n\ge F_{d+1}\to\infty$，所以这确实是对全部祖先规模和混合比例的一致深度极限，不只是逐点极限。

以下曲率将两个来源列的联合约束保留在同一个实现中。为简写置 $j=F_{d-2}$、$f=F_{d-1}$、$w=F_d=j+f$。则 $u=w-jx$、$v=f+w-fx$、$\ell'= -w$。Cassini 等式给

$$
u'v-uv'=f(f+w)-w^2=(-1)^d.
$$

熵的齐次表达为

$$
\ell h(u/\ell)=\ell\log\ell-u\log u-v\log v.
$$

对仿射函数 $u,v$ 连续求导两次，得到

$$
\begin{aligned}
\bigl(\ell h(u/\ell)\bigr)''
&=\frac{(u'+v')^2}{\ell}-\frac{(u')^2}{u}-\frac{(v')^2}{v}\\
&=-\frac{(u'v-uv')^2}{\ell uv}=-\frac1{\ell uv}.
\end{aligned}
$$

$\ell\log4$ 为仿射项，$h''(x)=-1/(x(1-x))$，所以得（12.7）；$\ell uv\ge6$ 且 $x(1-x)\le1/4$ 给下界 $4-1/6=23/6$。一次导数为

$$
J_k'(x)
=\log\frac{x}{1-x}
 -j\log\frac{4\ell}{u}-f\log\frac{4\ell}{v}.
\tag{12.22}
$$

后两个对数在闭区间有限且为正。故 $J_k'(0+)=-\infty$、$J_k'(1-)=+\infty$、$J_k'(1/2)<0$。严格递增的导数恰有一个零点，位于 $(1/2,1)$，就是连续最小点；在零点代入（12.22）得（12.8）。从 $x_k$ 到任意内部 $x$ 积分曲率下界两次，得（12.9）；由连续性延到两个端点。

对固定 $k$，整张网格的 $n$ 处于 $F_{d+1}t$ 与 $F_{d+2}t$ 之间。因此（12.5）除以 $t$ 的误差对 $p=0,\ldots,t$ 一致趋零。连续函数 $J_k$ 的网格最小值趋于 $J_k(x_k)$：下界来自连续最小值，上界取距 $x_k$ 至多 $1/(2t)$ 的网格点并用连续性。$-\log$ 把最大密度变成最小指数损失，遂得（12.10）。这一论证不决定精确有限网格最优点；当 $k$ 增长时，连续最小点到端点的距离还可以小于网格间距。

为取得深层最小点的定量少数比例，令

$$
A_k=\log\frac{x_k}{1-x_k}
=w\log4-j\log y_k^*-f\log(1-y_k^*).
$$

双根式给 $|j-\eta w|=\phi^{-d}$；又有 $w\le\phi^d$。在 $[1/3,2/5]$ 上，$|\log z-\log\eta|\le3|z-\eta|$，$|\log(1-z)-\log(1-\eta)|\le(5/3)|z-\eta|$。用（12.17）的连续版本及 $j+f=w$，得到

$$
\begin{aligned}
|A_k-wB|
&\le(3j+5f/3)|y_k^*-\eta|
 +|j-\eta w|\left|\log\frac{1-\eta}{\eta}\right|\\
&\le3w\phi^{-2d}+\phi^{-d}\log\phi
<\frac4w.
\end{aligned}
$$

另一方面 $A_k\ge w\log4$，所以

$$
0\le-\log(1-x_k)-A_k
=\log(1+e^{-A_k})\le4^{-w}\le\frac1w.
$$

相加即为（12.11）。这将每片目标叶的深度熵常数 $B$ 与连续最优祖先的少数叶边界联系起来；其中的少数比例不是有限网格的已取得祖先组成。

最后考察黄金组成归一化的相对有效性。以下简写 $D=D_{k,p,q}$、$R=R_{k,p,q}$、$\mathcal G=\mathcal G_{k,p,q}$。从（12.4）精确相减得到

$$
\log\frac R{\mathcal G}
=-n\bigl(h(y)-h(\eta)\bigr)
 +\frac12\log\frac{y(1-y)}{\eta(1-\eta)}+e_{k,p,q}.
\tag{12.23}
$$

$h'(\eta)=\log\phi$，且连接 $\eta,y$ 的整个区间位于 $[1/3,2/5]$，其上 $|h''|\le9/2$。Taylor 定理与 $y-\eta=D/n$ 给

$$
\left|n\bigl(h(y)-h(\eta)\bigr)-(\log\phi)D\right|
\le\frac94\frac{D^2}{n}.
$$

函数 $z\mapsto\tfrac12\log(z(1-z))$ 的导数在同一区间的绝对值至多 $3/4$。将这两个界及 $|e|\le2/n$ 代入（12.23），得到（12.13）。该 Taylor 界同时保留偏差的符号、二次余项和前因子误差，没有先取深度极限。

对任何 $k_i\to\infty$ 的允许序列，（12.17）给 $|D_i|/n_i\le\phi^{-2d_i}\to0$，而 $n_i\ge F_{d_i+1}\to\infty$。因而（12.13）可写为

$$
\log\frac{R_i}{\mathcal G_i}=-(\log\phi)D_i+\varepsilon_i,
\qquad
|\varepsilon_i|\le c_i|D_i|+b_i,
\quad
c_i=\frac94\phi^{-2d_i}\to0,
\quad
b_i=\frac34\phi^{-2d_i}+\frac2{n_i}\to0.
$$

偏差有有限极限时，余项趋零，给出 $\phi^{-z}$；偏差趋正无穷或负无穷时，主项的符号和绝对值支配余项，给出零或正无穷的比值极限。特别地 $D_i\to0$ 蕴含比值趋一。反向，比值趋一使其对数趋零；当 $c_i\le(\log\phi)/2$ 时，上式强制

$$
\frac{\log\phi}{2}|D_i|
\le\left|\log\frac{R_i}{\mathcal G_i}\right|+b_i\longrightarrow0.
$$

这证明（12.14）的必要性，未对变化的祖先规模添加条件，也没有把振荡偏差赋予不存在的极限。

各有限相位由实际整数来源实现。沿偶数 $k\to\infty$，若 $z>0$，取 $q=0$、$p=\lfloor z\phi^{d+1}\rfloor$；若 $z<0$，取 $p=0$、$q=\lfloor(-z)\phi^{d+2}\rfloor$。在充分大的深度这些来源非空，取整误差乘以相应收缩因子趋零，故 $D\to z$。$z=0$ 时取 $p=1,q=0$ 即可。另一方面，对每个深度任选正整数 $q$，取距 $q/\phi$ 最近的整数 $p$，则

$$
|p-q/\phi|\le\frac12,\qquad
|D|\le\frac12\phi^{-(d+1)}\longrightarrow0.
$$

$q$ 可以随深度任意快速增长，例如取 $q\ge\lceil\phi^{4d}\rceil$，仍有同一偏差界与相对等价；此时总规模的增长不能替代来源抵消关系。上述序列的每个组成都有完整有序祖先树代表，使用预算时取 $H\ge n$ 即仍在原域内。全部结论只是这些完整树纤维之间的计数及近似关系；它们不增加数量读出、代码或路径观察的取得权限，不将组成祖先许可提升为指定树的逆执行许可。证毕。

## 追加锚（本行以下为增补区）

## 13. 完整树像密度的全网格极值与联合少数叶转变

**定义 13.1（原始树网格与少数叶参数）。** 沿用[定义 1.1](#1-有限预算的尺度读出与逆许可分离)、[定义 2.1](#2-许可预算阶梯与深层碰撞前沿)和[定义 12.1](#12-完整树替换像的计数密度祖先混合与共轭来源偏差)的非空自由有序完全二叉树、叶标签、组成及替换 $\rho$。固定任意整数 $k\ge1,t\ge1$，本章所有缩写均在这两个参数下使用，置

$$
\begin{gathered}
d=3k,\qquad E=F_{d-2},\quad A=F_{d-1},\quad D=F_d=E+A,
\quad L=F_{d+1}=A+D,\\
0\le j\le t,\qquad p=t-j,\quad q=j,\\
a_j=At+Ej,\qquad b_j=Dt+Aj,\qquad n_j=Lt+Dj,\\
V_j=|\mathcal T_{a_j,b_j}|=C_{n_j-1}\binom{n_j}{a_j},\qquad
R_j=R_{k,t-j,j}=\frac{C_{t-1}\binom tj}{V_j},
\qquad C_s=\frac1{s+1}\binom{2s}{s}.
\end{gathered}
\tag{13.1}
$$

这里 $R_j$ 是实际集合 $\rho^d(\mathcal T_{t-j,j})$ 在完整目标树纤维中的密度，复用（12.3）、（12.15），不将括号、叶序或树的来源取商。若另保留有限预算，整个网格使用同一个 $H_t\ge F_{d+2}t$。本章的 $L$ 只缩写一个 Fibonacci 数，不表示观察阶段。规范代码和全部路径仍按[母卷定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)描述完整树；它们不成为这里的额外观察输入。计数密度不指定实际来源的概率律、物理时间或几何，组成祖先许可及下列极值也不授权指定树的实际逆执行。

对 $z\in[0,1]$，定义

$$
\begin{gathered}
u(z)=A+Ez,\qquad v(z)=D+Az,\qquad \ell(z)=L+Dz,\\
K(z)=\ell(z)g\bigl(u(z)/\ell(z)\bigr),\qquad
P(z)=\ell(z)\sqrt{u(z)v(z)},\qquad
K(z)-g(z)=J_k(1-z),\\
\kappa=\frac1{LAD},\qquad
\sigma=\frac DL+\frac E{2A}+\frac A{2D},\qquad
\delta=E\log\frac{4L}{A}+A\log\frac{4L}{D},\\
r=1-x_k\in(0,1/2),\qquad \mu=tr,\qquad
\lambda=t e^{-\delta},\qquad \varepsilon=\kappa+\frac3t.
\end{gathered}
\tag{13.2}
$$

$g$、$J_k$ 和连续最小点 $x_k$ 均取第12章的原定义，包括熵的端点约定；$r$ 是连续少数比例，不预先断言整数极值的位置。对 $s\ge0$ 再记

$$
M(s)=\max_{h\in\mathbb N_0}\frac{s^h}{h!},\qquad
\Pi(s)=e^{-s}M(s),\qquad 0^0=1.
\tag{13.3}
$$

最大项存在，因为 $s>0$ 时相邻项之比为 $s/(h+1)$，而 $s=0$ 时只有零次项非零。这些只是指数级数的系数，不附带抽样模型。以下称最大化 $R_j$ 的整数 $j$ 为网格极值指标。

**定理 13.1（全网格严格曲率、精确并列与有界少数叶的联合最优密度）。** 在定义 13.1 的全部原参数范围内，以下结论同时成立。

（一）当 $t\ge2$ 且 $1\le j\le t-1$ 时，整张祖先网格满足

$$
\Delta^2\log R_j
:=\log R_{j+1}-2\log R_j+\log R_{j-1}
<-\frac{55}{36t}<0.
\tag{13.4}
$$

记正整数的上升乘积为 $(x)_h=\prod_{s=0}^{h-1}(x+s)$，$(x)_0=1$。全部相邻比值准确为

$$
Q_j:=\frac{R_{j+1}}{R_j}
=\frac{t-j}{j+1}\,
\frac{(n_j)_D(a_j+1)_E(b_j+1)_A}
     {(2n_j-1)_{2D}},\qquad 0\le j<t.
\tag{13.5}
$$

$t\ge2$ 时 $Q_0,\ldots,Q_{t-1}$ 严格递减。集合 $\{j\in\{0,\ldots,t-1\}:Q_j\le1\}$ 总非空，令其最小元素为 $m_*$。若 $Q_{m_*}<1$，唯一极值指标为 $m_*$；若 $Q_{m_*}=1$，恰有 $m_*,m_*+1$ 两个极值指标。所有极值指标都满足

$$
0\le q\le\lfloor t/2\rfloor,\qquad p=t-q.
\tag{13.6}
$$

其中的上界是全网格结论，不是比较域的预先限制。每个有限并列恰由以下正整数等式判定：

$$
(t-j)(n_j)_D(a_j+1)_E(b_j+1)_A
=(j+1)(2n_j-1)_{2D},\qquad 0\le j<t.
\tag{13.7}
$$

满足等式时，且仅在此时，$j,j+1$ 同为全局极值指标；这里不将参数对的等号集合另作枚举。

（二）在整张有限网格上存在实数 $\theta_j$，使

$$
Q_j=\frac{\lambda}{j+1}\left(1-\frac jt\right)e^{\theta_j},
\qquad |\theta_j|\le\varepsilon,\qquad 0\le j<t.
\tag{13.8}
$$

置 $w_\pm=e^{-\delta\pm\varepsilon}$、$\nu_\pm=(t+1)w_\pm/(1+w_\pm)$，每个极值指标 $q$ 满足

$$
\max\{0,\lceil\nu_--1\rceil\}\le q
\le\min\{t,\lfloor\nu_+\rfloor\}.
\tag{13.9}
$$

全部 $0\le j\le t$ 同时满足远网格控制与局部对数误差界

$$
\frac{R_j}{R_0}\le\frac{(\lambda e^\varepsilon)^j}{j!},
\tag{13.10}
$$

$$
-\frac{j(j-1)}{2(t-j+1)}-\frac4{Lt}
\le\log\frac{j!R_j}{\lambda^jR_0}
\le\frac{\kappa j^2}{2t}+\frac{\sigma j}{t}+\frac4{Lt}.
\tag{13.11}
$$

（三）连续少数比例和整数比值参数在每个有限 $(k,t)$ 下满足

$$
\log\frac\lambda\mu=-\log(1-r)-\Delta,
\qquad \Delta=\delta-K'(r)\in[0,\kappa r],
\qquad
(1-\kappa)r\le\log\frac\lambda\mu\le\frac r{1-r}.
\tag{13.12}
$$

对任意整数序列 $k_i\to\infty,t_i\to\infty$，只要求 $\mu_i=t_i(1-x_{k_i})$ 有界，将 $R_j$ 在 $j>t_i$ 时延为零，则

$$
\sum_{j=0}^{\infty}
\left|\frac{R_j}{R_0}-\frac{\mu_i^j}{j!}\right|
\longrightarrow0.
\tag{13.13}
$$

此式的 $R_j,R_0$ 取同一 $(k_i,t_i)$。它是完整树密度的 $\ell^1$ 相对剖面，不要求 $\mu_i$ 收敛，也不是实际来源的概率分布断言。

（四）在（三）的联合序列上，若 $\mu_i\to\tau\in[0,1)$，最终唯一极值指标为 $q=0$；若 $\tau>0$ 不是整数，最终唯一极值指标为 $q=\lfloor\tau\rfloor$。若 $\mu_i\to m\in\mathbb N_{>0}$，最终每个极值指标都属于 $\{m-1,m\}$，且有限指标的精确选择为

$$
\begin{array}{c|c}
Q_{m-1}<1&\{m-1\}\\
Q_{m-1}>1&\{m\}\\
Q_{m-1}=1&\{m-1,m\}.
\end{array}
\tag{13.14}
$$

一个整数临界极限本身不保证有限并列。对每个固定正整数 $m$，两个邻近的唯一极值指标确实都能由同一个临界极限实现：令

$$
\zeta_k=\sqrt{\kappa+r},\qquad
t_k^- =\left\lfloor\frac{m-\zeta_k}{r}\right\rfloor,
\qquad
t_k^+ =\left\lfloor\frac{m+\zeta_k}{r}\right\rfloor.
\tag{13.15}
$$

在充分大的 $k$，两个祖先规模均为正整数并趋于无穷，$t_k^\pm r\to m$；负号序列最终唯一极值指标为 $m-1$，正号序列最终唯一极值指标为 $m$。使用预算时分别取共同的 $H_{t_k^\pm}\ge F_{3k+2}t_k^\pm$，每条序列的全网格均处于原树域内。

（五）对（三）的每个联合序列，最优完整树像密度具有原连续速率下的相对渐近式

$$
\boxed{\quad
\max_{0\le p\le t}R_{k,p,t-p}
=(1+o(1))\sqrt{2\pi}\,L\sqrt{AD}\,\sqrt t\,
\exp\bigl(-tJ_k(x_k)\bigr)\Pi(\mu).
\quad}
\tag{13.16}
$$

最大值仍遍历全部整数 $p$。此式保留精确的 $k$ 依赖指数和 Fibonacci 前因子；有界少数叶条件只施加于本联合渐近式及（三）、（四）的联合极限，不限制（一）、（二）或（13.12）的有限参数结论。

证明。首先固定任意 $(k,t)$，在整张网格上使用同一树来源与替换。由[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)供应的树替换单射性，第12章已取得实际像的双射（12.3），故可直接使用完整树计数（12.15）。其形状因子所用的经典 Catalan 供应是 [Stanley，*Enumerative Combinatorics* 第二卷，习题 6.19(b)、(d)](https://math.mit.edu/~rstan/ec/catalan.pdf) 的有序括号和有序完全二叉树计数，不把组成点当作树代表来计数。代入（13.1）并消去阶乘，给

$$
V_j=\frac{(2n_j-2)!}{(n_j-1)!\,a_j!\,b_j!},
\qquad
\frac{V_j}{V_{j+1}}
=\frac{(n_j)_D(a_j+1)_E(b_j+1)_A}{(2n_j-1)_{2D}}.
\tag{13.17}
$$

同时 $n_j\le(L+D)t=F_{d+2}t$，所以定义中的共同预算包含每个目标纤维，不随待比较的 $j$ 删减来源。$a_j\ge At\ge1$、$b_j\ge Dt\ge2$、$n_j\ge Lt\ge3t$。直接复用（12.4）和第12章证明在（12.19）后取得的带符号余项，置 $e_j=e_{k,t-j,j}$，得到恒等式

$$
\begin{gathered}
\log R_j=\mathcal C_t+\log\binom tj-tK(j/t)+\log P(j/t)+e_j,\\
\mathcal C_t=\log\bigl(4\pi\sqrt2\,C_{t-1}t^2\bigr),\qquad
-\frac{13}{12n_j}<e_j<\frac3{8n_j},\qquad |e_j|\le\frac2{n_j}.
\end{gathered}
\tag{13.18}
$$

这里祖先二项式保持精确，$j=0,t$ 和 $t=1$ 都在同一式内。余项供应来自 [Robbins，*A Remark on Stirling's Formula*，第26页式（1）–（2）](https://dornsife.usc.edu/sergey-lototsky/wp-content/uploads/sites/211/2024/02/Stirling-Robbins.pdf) 在正整数上的阶乘界及其既有应用；没有对零阶乘或实数参数调用该供应，也没有给 $e_j$ 添加导数假设。

下面核算平滑部分与离散余项各自的曲率。Cassini 等式 $|A^2-DE|=1$ 给 $(Ev-uA)^2=1$。使用第12章已有的齐次熵计算，有

$$
\begin{aligned}
K(z)&=\ell\log4+\ell\log\ell-u\log u-v\log v,\\
K'(z)&=E\log\frac{4\ell}{u}+A\log\frac{4\ell}{v},
\qquad K'(0)=\delta,\\
K''(z)&=\frac{D^2}{\ell}-\frac{E^2}{u}-\frac{A^2}{v}
=-\frac{(Ev-uA)^2}{\ell uv}=-\frac1{\ell uv},\\
(\log P)'(z)&=\frac D\ell+\frac E{2u}+\frac A{2v},\\
(\log P)''(z)&=-\frac{D^2}{\ell^2}-\frac{E^2}{2u^2}-\frac{A^2}{2v^2}<0.
\end{aligned}
\tag{13.19}
$$

因此在 $[0,1]$ 上

$$
-\kappa\le K''<0,\qquad
0\le\delta-K'(z)\le\kappa z,\qquad
0<(\log P)'\le\sigma.
\tag{13.20}
$$

Fibonacci 递推给 $E\le A\le2E$，故 $E/A\in[1/2,1]$。由此 $D/L\le2/3$、$E/(2A)\le1/2$、$A/(2D)\le1/3$；并且 $LAD\ge6$。所以

$$
\kappa\le\frac16,\qquad \sigma\le\frac32,\qquad L\ge3,
\qquad \sigma+\frac4L\le\frac{17}{6}<3.
\tag{13.21}
$$

对 $1\le j\le t-1$，精确二项式的离散二阶差为

$$
\Delta^2\log\binom tj
=-\log\left(1+\frac1j\right)-\log\left(1+\frac1{t-j}\right)
\le-\frac4{t+1}.
\tag{13.22}
$$

为验证最后一步，对 $s\ge0$，$\log(1+s)-2s/(2+s)$ 在零点为零，其导数为 $s^2/((1+s)(2+s)^2)\ge0$。分别代入 $s=1/j,1/(t-j)$，再用两个正数倒数和的界，得到 $2/(2j+1)+2/(2(t-j)+1)\ge4/(t+1)$。

对（13.20）的二阶导数界作三角核积分，得 $\Delta^2[-tK(j/t)]\le\kappa/t$；$\log P$ 的凹性给 $\Delta^2\log P(j/t)\le0$。带符号的离散余项直接给

$$
\Delta^2e_j
<\frac38\left(\frac1{n_{j+1}}+\frac1{n_{j-1}}\right)
  +\frac{13}{6n_j}
\le\frac{35}{12Lt}.
\tag{13.23}
$$

合并以上各项，当 $t\ge2$ 时

$$
\begin{aligned}
\Delta^2\log R_j
&<-\frac4{t+1}+\frac1t\left(\kappa+\frac{35}{12L}\right)\\
&\le-\frac4{t+1}+\frac{41}{36t}
\le-\frac{55}{36t}.
\end{aligned}
\tag{13.24}
$$

最后一步使用 $4t/(t+1)\ge8/3$，包含 $t=2$ 的等号；总不等式仍因（13.23）而严格。这证明（13.4），其离散曲率是分子对目标熵曲率和真实余项的联合支配，不要求 $V_j$ 对数凸。

由（13.17）和祖先二项式的相邻比立即取得（13.5）。$\log Q_j-\log Q_{j-1}=\Delta^2\log R_j<0$，给严格递减。为证明全部端点的交叉存在以及（13.6），令 $V(a,b)=C_{a+b-1}\binom{a+b}{a}$。在任意正整数 $a,b$、$n=a+b$ 下，精确计数给

$$
\frac{V(a+1,b)}{V(a,b)}=\frac{2(2n-1)}{a+1}>1,
\qquad
\frac{V(a,b+1)}{V(a,b)}=\frac{2(2n-1)}{b+1}>1.
\tag{13.25}
$$

由 $a+1,b+1\le n$ 可直接验证严格性。$j$ 增加一时两个坐标分别增加正整数 $E,A$，故 $V_{j+1}>V_j$，从而

$$
Q_j<\frac{t-j}{j+1},\qquad
Q_{\lfloor t/2\rfloor}<1.
\tag{13.26}
$$

该索引在 $t\ge1$ 下总小于 $t$。于是首个 $Q_j\le1$ 存在；此前序列严格上升，此后严格下降，只有该比值等于一时才在这一步相邻并列。若此步就在 $\lfloor t/2\rfloor$，其比值已严格小于一；若更早并列，第二点也不超过 $\lfloor t/2\rfloor$。这同时证明全部极值的上界。$t=1$ 时只有 $Q_0<1$，唯一极值为零，不需要二阶差。清除（13.5）的正整数分母得到（13.7），严格递减保证任何一个等号必是唯一的交叉等号，因而必给全局并列。

为取得不依赖网格位置的比值控制，在（13.18）相邻相减，准确写成（13.8），其中

$$
\begin{aligned}
\theta_j={}&\delta-t\bigl[K((j+1)/t)-K(j/t)\bigr]\\
&+\log\frac{P((j+1)/t)}{P(j/t)}+e_{j+1}-e_j.
\end{aligned}
\tag{13.27}
$$

（13.20）使第一行位于 $[0,\kappa(j+1/2)/t]$，第二行的对数位于 $[0,\sigma/t]$；$|e_{j+1}-e_j|\le4/(Lt)$。因 $j<t$，再用（13.21），得 $|\theta_j|\le\kappa+(\sigma+4/L)/t\le\varepsilon$。

每个极值指标 $q$ 若 $q>0$，有 $Q_{q-1}\ge1$；结合（13.8）的上界，$1\le w_+(t-q+1)/q$，等价于 $q\le\nu_+$。若 $q<t$，有 $Q_q\le1$；结合下界，$w_-(t-q)/(q+1)\le1$，等价于 $q\ge\nu_--1$。缺失的端点条件分别由 $q=0\le\nu_+$ 和 $q=t>\nu_--1$ 自动成立。取整数即得（13.9）。连乘 $Q_h\le\lambda e^\varepsilon/(h+1)$，得（13.10），包括 $j=0,t$。

从（13.18）在 $j$ 与零相减并保留精确祖先二项式，得到

$$
\begin{aligned}
\log\frac{j!R_j}{\lambda^jR_0}
={}&\sum_{h=0}^{j-1}\log\left(1-\frac ht\right)
 +j\delta-t\bigl[K(j/t)-K(0)\bigr]\\
&+\log\frac{P(j/t)}{P(0)}+e_j-e_0.
\end{aligned}
\tag{13.28}
$$

空和取零。因为 $h\le j-1<t$，$\log(1-s)\ge-s/(1-s)$ 给第一项的上下界 $-j(j-1)/(2(t-j+1))$ 与零，包括 $j=t$。积分（13.20）给第二项位于 $[0,\kappa j^2/(2t)]$，第三项位于 $[0,\sigma j/t]$，第四项绝对值至多 $4/(Lt)$。这证明（13.11）和（二）的全部全网格估计。

现在连接连续与离散参数。第12章（12.7）–（12.11）供应唯一连续最小点及其少数比例；$J_k(1-z)=K(z)-g(z)$ 的驻点条件准确为

$$
K'(r)=\log\frac{1-r}{r}.
\tag{13.29}
$$

以（13.20）代入 $z=r$，得 $0\le\Delta\le\kappa r$，同时

$$
\log\frac\lambda\mu=-\delta-\log r
=-\log(1-r)-\Delta.
$$

由 $r\le-\log(1-r)\le r/(1-r)$，即得（13.12）。这一等式在任意有限 $k,t$ 都成立；连续少数比例没有被直接舍入成整数极值指标。

沿（三）任意指定的联合序列，第12章（12.11）给 $r\to0$；又 $L,A,D\to\infty$，故 $\kappa\to0$，而 $\varepsilon\to0$。由（13.12），$\lambda/\mu\to1$。$\mu$ 有界使 $\lambda-\mu\to0$，且 $\lambda$ 有界。对任意固定非负整数 $j$，$t\to\infty$ 后 $j\le t$；（13.11）的两个误差端点都趋零，故

$$
\frac{R_j}{R_0}=\frac{\lambda^j}{j!}(1+o(1)),
\qquad
\left|\frac{R_j}{R_0}-\frac{\mu^j}{j!}\right|\to0.
\tag{13.30}
$$

对 $j=0$ 两者都等于一；$\mu$ 即使趋零也只需有界性和 $\lambda-\mu\to0$，不作除以 $\mu^j$ 的极限操作。可以选同一个有限常数 $C$，在序列的充分大位置使 $\lambda e^\varepsilon\le C$ 和 $\mu\le C$。于是（13.10）连同零延拓，对全部 $j\ge0$ 给

$$
0\le\frac{R_j}{R_0}\le\frac{C^j}{j!},\qquad
0\le\frac{\mu^j}{j!}\le\frac{C^j}{j!}.
\tag{13.31}
$$

级数 $\sum C^j/j!$ 收敛；先选有限头部以使两条尾和任意小，再在头部使用（13.30），证明（13.13）。这明确控制全部远网格，没有把逐点收敛直接换成无界求和或最大值收敛。

若进一步 $\mu\to\tau$，则 $w_\pm=\lambda e^{\pm\varepsilon}/t$，从而

$$
\nu_\pm
=\frac{(1+1/t)\lambda e^{\pm\varepsilon}}
       {1+\lambda e^{\pm\varepsilon}/t}
\longrightarrow\tau.
\tag{13.32}
$$

若 $0<\tau<1$，两个 $\nu$ 最终都在 $(0,1)$，（13.9）只允许零；$\tau=0$ 时 $\nu_+<1$ 最终成立，同样只允许零。若 $\tau>0$ 非整数，设 $h=\lfloor\tau\rfloor$，两个 $\nu$ 最终都在 $(h,h+1)$，整数包络只允许 $h$。若 $\tau=m\ge1$ 为整数，两个 $\nu$ 最终都在 $(m-1,m+1)$，包络只允许 $m-1,m$；且 $t\to\infty$ 保证 $Q_{m-1}$ 有定义。由（一）的严格交叉，$Q_{m-1}-1$ 的负号、正号或零值恰给（13.14）。这里极限系数在 $m-1,m$ 的相等，不被当作有限 $R_{m-1}=R_m$ 的证据。

为验证（13.15）的两个实现，固定 $m\ge1$。$\zeta_k\to0$，因此 $m-\zeta_k>0$ 最终成立，而 $r\to0$ 使两个 $t_k^\pm\to\infty$。取整误差给

$$
\mu_k^\pm=t_k^\pm r=m\pm\zeta_k+O(r),\qquad
\frac1{t_k^\pm}=O(r),\qquad
\varepsilon=O(\kappa+r).
\tag{13.33}
$$

（13.12）给 $\lambda=\mu+O(r)$，再代入（13.32）的准确式，有 $\nu_\pm=\mu+O(\kappa+r)=\mu+O(\zeta_k^2)$，这些估计的常数只需对固定 $m$ 有界。由于 $r\le\zeta_k^2$，负号序列两个包络端点最终严格位于 $(m-1,m)$，正号序列最终严格位于 $(m,m+1)$。因此（13.9）分别只允许 $m-1$ 与 $m$，证明两侧的唯一性。这也表明临界极限单独不能选择有限胜点。例如取 $t_k=\lfloor(3/4)/r\rfloor$，则 $t_kr\to3/4$，唯一极值最终是零，尽管连续少数叶数的最近整数最终是一。

最后取得原速率的相对最优前因子。第12章（12.19）的祖先 Catalan 界与（13.18）在 $j=0$ 联用，给准确端点式

$$
R_0=\sqrt{2\pi}\,L\sqrt{AD}\,\sqrt t\,
\exp\bigl(-tJ_k(1)+E_t+e_0\bigr),\qquad
0<E_t<\frac1t,\quad |e_0|\le\frac2{Lt}.
\tag{13.34}
$$

这是 $P(0)=L\sqrt{AD}$ 的精确代入；$E_t$ 是（12.19）原有的 Catalan 对数余项，不是局部 Fibonacci 数 $E$。所以沿任意 $t\to\infty$，端点式相对等价于去掉 $E_t+e_0$ 的右侧，误差对 $k$ 一致，不以黄金组成归一化因子替换 $R_0$。

由（13.13）及任意两个有界序列的上确界差不超过其逐项绝对差之和，

$$
\max_{0\le j\le t}\frac{R_j}{R_0}=M(\mu)+o(1).
\tag{13.35}
$$

$M(\mu)\ge1$，故这也是相对等价；最大值变换已经由可和尾控制，而非仅凭局部展开。还须将精确端点速率换回精确连续最优速率。由（13.29）和熵表达，直接计算

$$
\begin{gathered}
J_k(1)-J_k(x_k)
=K(0)-K(r)+h(r)=-\log(1-r)-I,\\
I=\int_0^r\bigl(K'(s)-K'(r)\bigr)\,ds,
\qquad 0\le I\le\frac{\kappa r^2}{2}.
\end{gathered}
\tag{13.36}
$$

最后的界来自 $K'$ 的单调性及（13.20）的 Lipschitz 界。再用 $0\le-\log(1-r)-r\le r^2/(2(1-r))$，在同一联合序列上得到

$$
\left|t\bigl[J_k(1)-J_k(x_k)\bigr]-\mu\right|
\le\frac{\mu r}{2(1-r)}+\frac{\kappa\mu r}{2}
\longrightarrow0.
\tag{13.37}
$$

把（13.34）、（13.35）、（13.37）合并，$e^{-\mu}M(\mu)=\Pi(\mu)$ 正好留下（13.16）的前因子。该证明始终使用同一 $(k,t,j)$ 的完整来源树和实际替换像；局部误差、可和尾、临界选择及连续速率转换全部在这些原对象上成立。证毕。

## 追加锚（本行以下为增补区）

## 14. 完整来源网格的严格横向穿越与少数叶临界读出

**定义 14.1（固定祖先少数坐标的实有限乘积延拓）。** 固定整数 $k\ge1$、$j\ge0$，置

$$
 d=3k,\qquad E=F_{d-2},\quad A=F_{d-1},\quad D=F_d=E+A,\quad L=F_{d+1}=A+D.
$$

对实数 $t\ge j+1$ 定义

$$
 a=At+Ej,\qquad b=Dt+Aj,\qquad n=Lt+Dj,
$$

并用 $(x)_m=\prod_{h=0}^{m-1}(x+h)$、$(x)_0=1$ 记上升乘积。置

$$
 H_{k,j}(t)=\frac{(a+1)_E(b+1)_A}{4^D(n-\tfrac12)_D},
 \qquad q_{k,j}(t)=\frac{t-j}{j+1}H_{k,j}(t).
 \tag{14.1}
$$

在整数 $t\ge j+1$ 上，定义 13.1 的相邻密度比为 $Q_{k,t,j}=q_{k,j}(t)$。这是因为

$$
 (2n-1)_{2D}=4^D(n-\tfrac12)_D(n)_D,
 \tag{14.2}
$$

而（13.5）中的 $(n)_D$ 正好约去。故 $q$ 在非整数处只是有限乘积的实辅助延拓，那里没有实叶数的树；整数网格仍由完整有序树、其组成祖先和替换像给出。由（12.3）、（12.15）及[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)，每个整数网格使用同一个来源计数和生产者单射性；若同时保留 $0\le j\le t$ 的整张网格，可取共同预算

$$
 H_t\ge F_{d+2}t.
 \tag{14.3}
$$

**定理 14.2（全实域严格增加与唯一穿越）。** 定义 14.1 中 $q_{k,j}$ 在 $[j+1,\infty)$ 上严格增加，并且

$$
 \frac{q_{k,j}(t)}t\longrightarrow\frac{c_k}{j+1},\qquad
 c_k=\frac{A^E D^A}{4^D L^D}>0.
 \tag{14.4}
$$

存在唯一实数 $\tau_{k,j}$ 使 $q_{k,j}(\tau_{k,j})=1$，且

$$
 2j+1<\tau_{k,j}<U_{k,j}:=j+\frac{j+1}{c_k}.
 \tag{14.5}
$$

对所有合法整数 $t\ge j+1$，$Q_{k,t,j}<1$、$=1$ 或 $>1$ 分别当且仅当 $t<\tau_{k,j}$、$t=\tau_{k,j}$ 或 $t>\tau_{k,j}$。因此每个 $(k,j)$ 至多有一个整数并列。

证明。先记 $g(t)=(\log q_{k,j})'(t)$。对 $x>0$ 和整数 $m\ge1$，凸性和梯形求积给出

$$
 \sum_{i=1}^{m}\frac1{x+i}\ge
 \int_0^m\frac{ds}{x+s}-\frac{m}{2x(x+m)}.
 \tag{14.6}
$$

对 $n\ge3$，中点求积先给出
$\sum_{h=0}^{D-1}(n+h+\tfrac12)^{-1}\le\int_0^D(n+s)^{-1}ds$。把采样点向左移一格后，各差分在求和时望远镜相消，且

$$
 \sum_{h=0}^{D-1}\left((n+h-\tfrac12)^{-1}-(n+h+\tfrac12)^{-1}\right)
 =\frac{D}{(n-\tfrac12)(n+D-\tfrac12)},
$$

得到

$$
 \sum_{h=0}^{D-1}\frac1{n+h-\tfrac12}\le
 \int_0^D\frac{ds}{n+s}+\frac{D}{(n-\tfrac12)(n+D-\tfrac12)}.
 \tag{14.7}
$$

对 $0\le s\le1$ 置

$$
 a_s=At+E(j+s),\quad b_s=Dt+A(j+s),\quad n_s=Lt+D(j+s).
$$

Cassini 等式 $(A^2-DE)^2=1$ 的直接展开给出

$$
 \frac{AE}{a_s}+\frac{AD}{b_s}-\frac{LD}{n_s}
 =-\frac{t(j+s)}{a_sb_sn_s}.
 \tag{14.8}
$$

由于 $a_s\ge At$、$b_s\ge Dt$、$n_s\ge Lt$，三项未移位积分的总和至少为

$$
 -\frac{\kappa_k(j+\tfrac12)}{t^2},\qquad \kappa_k=\frac1{LAD}.
 \tag{14.9}
$$

由（14.6）–（14.9），对全部 $t\ge j+1$ 有

$$
\begin{aligned}
 g(t)\ge{}&\frac1{t-j}-\frac{\kappa_k(j+\tfrac12)}{t^2}
 -\frac{AE}{2a(a+E)}-\frac{AD}{2b(b+A)}\\
 &-\frac{LD}{(n-\tfrac12)(n+D-\tfrac12)}.
 \tag{14.10}
\end{aligned}
$$

当 $t\ge2$ 时，Fibonacci 比值给
$E/A\le1$、$A/D\le2/3$、$D/L\le2/3$、$L\ge3$、$\kappa_k\le1/6$。因而

$$
 \frac{AE}{2a(a+E)}\le\frac1{2t^2},\qquad
 \frac{AD}{2b(b+A)}\le\frac1{3t^2},\qquad
 \frac{LD}{(n-\tfrac12)(n+D-\tfrac12)}\le
 \frac8{11t^2}.
 \tag{14.11}
$$

最后一个界使用 $n-\tfrac12\ge L(t-\tfrac16)$、$n+D-\tfrac12\ge Lt$ 以及 $t\ge2$。在 $j\le t-1$ 下，故

$$
 g(t)\ge\frac1t-\frac{t-\tfrac12}{6t^2}-\frac{103}{66t^2}
 =\frac{5}{6t}-\frac{65}{44t^2}>0.
 \tag{14.12}
$$

还剩 $j=0$、$1\le t<2$。当 $k\ge2$ 时，递推给

$$
 \frac35\le\frac EA,\frac AD,\frac DL\le\frac58,\qquad L\ge13,\qquad \kappa_k\le\frac1{520}.
 \tag{14.13}
$$

于是（14.10）的两个分子修正各不超过 $25/(128t)$。置 $u=(2L)^{-1}$、$r=D/L$；函数 $t\mapsto t/[(t-u)(t+r-u)]$ 在 $t\ge1$ 上下降，且（14.13）给出

$$
 \frac{LD}{(n-\tfrac12)(n+D-\tfrac12)}\le\frac{13}{30t},\qquad
 \frac{\kappa_k}{2t^2}\le\frac1{1040t}.
 \tag{14.14}
$$

所以

$$
 g(t)\ge\frac1t-\frac{25}{64t}-\frac{13}{30t}-\frac1{1040t}
 =\frac{437}{2496t}>0.
 \tag{14.15}
$$

当 $k=1$、$j=0$ 时，$E=A=1,D=2,L=3$，故

$$
 q_{1,0}(t)=\frac{t(t+1)(2t+1)}{4(36t^2-1)},
$$

其导数的正分母之外的符号为
$72t^4-42t^2-6t-1$。对 $t\ge1$，

$$
 72t^4-42t^2-6t-1
 =23t^2+(t-1)(72t^3+72t^2+7t+1)>0.
 \tag{14.16}
$$

这覆盖了端点 $t=1$，从而 $g>0$ 的全域证明完成。

在 $t=2j+1$ 时，$q$ 是完整目标纤维的相邻密度比。令
$V(a,b)=C_{a+b-1}\binom{a+b}{a}$；已有完整树计数给出[（12.15）](#12-完整树替换像的计数密度祖先混合与共轭来源偏差)，而

$$
 \frac{V(a+1,b)}{V(a,b)}=\frac{2(2(a+b)-1)}{a+1}>1,\qquad
 \frac{V(a,b+1)}{V(a,b)}=\frac{2(2(a+b)-1)}{b+1}>1.
 \tag{14.17}
$$

从而 $q_{k,j}(2j+1)<(2j+1-j)/(j+1)=1$。另一方面（14.1）的最高次项给（14.4），故连续性和严格增加性产生唯一根，并给出根的下界。

为证更强的上界，令

$$
 H(t)=\frac{(a+1)_E(b+1)_A}{4^D(n-\tfrac12)_D},\qquad
 H_0(t)=\frac{a^Eb^A}{4^Dn^D}.
$$

右端点求积和左移半步的单调性给

$$
 \log\frac{H(t)}{H_0(t)}\ge
 \int_0^1\!\left[E\log\left(1+\frac{Es}{a}\right)+A\log\left(1+\frac{As}{b}\right)-D\log\left(1+\frac{Ds}{n}\right)\right]ds.
 \tag{14.18}
$$

括号内函数在 $s=0$ 为零，且其导数为

$$
 \frac{E^2}{a+Es}+\frac{A^2}{b+As}-\frac{D^2}{n+Ds}
 =\frac{(Eb-Aa)^2}{(a+Es)(b+As)(n+Ds)}>0,
 \tag{14.19}
$$

因为 $Eb-Aa=t(ED-A^2)$ 且 $|ED-A^2|=1$。故 $H(t)>H_0(t)$。令 $z=j/t$；同一 Cassini 展开给

$$
 \frac{d}{dz}\log\frac{(A+Ez)^E(D+Az)^A}{(L+Dz)^D}
 =\frac1{(L+Dz)(A+Ez)(D+Az)}>0.
 \tag{14.20}
$$

于是 $H_0(t)\ge c_k$，且严格不等式 $H(t)>c_k$ 在整个合法域成立。由（14.1），在 $U_{k,j}$ 处
$q_{k,j}(U_{k,j})>c_k(U_{k,j}-j)/(j+1)=1$，这证明（14.5）及全部整数比较。证毕。

**定理 14.3（有限精确阈值与整数边界）。** 定义

$$
\begin{aligned}
 \mathsf P_{k,j}(T):={}&(T-j)\prod_{i=1}^{E}(AT+Ej+i)\prod_{s=1}^{A}(DT+Aj+s)\\
 &-(j+1)2^D\prod_{h=0}^{D-1}(2LT+2Dj+2h-1).
 \tag{14.21}
\end{aligned}
$$

并令

$$
 T_{k,j}=\min\left\{T\in\mathbb Z:\ 2j+2\le T\le\lceil U_{k,j}\rceil,\quad
 \mathsf P_{k,j}(T)\ge0\right\}.
 \tag{14.22}
$$

该集合非空，且 $T_{k,j}=\lceil\tau_{k,j}\rceil$。所有合法 $t<T_{k,j}$ 满足 $Q_{k,t,j}<1$，所有 $t>T_{k,j}$ 满足 $Q_{k,t,j}>1$；在 $T_{k,j}$ 处，恰当且仅当 $\mathsf P_{k,j}(T_{k,j})=0$ 时有整数并列 $Q_{k,T_{k,j},j}=1$。因此这是有限的精确 tie 决定，而不是对所有 $(k,j)$ 的无并列分类。

证明。由（14.1）、（14.2）清除正分母，得到

$$
 \operatorname{sgn}(q_{k,j}(T)-1)=\operatorname{sgn}\mathsf P_{k,j}(T).
 \tag{14.23}
$$

定理 14.2 给出根在 $2j+1$ 与 $U_{k,j}$ 之间，且在 $\lceil U_{k,j}\rceil$ 处符号为正，所以集合非空。严格增加性说明第一个非负整数正是 $\lceil\tau_{k,j}\rceil$，并给出两个分支及至多一个等号。证毕。

**定理 14.4（固定 $j$ 的横向位移）。** 对每个固定 $j\ge0$，令

$$
 \kappa_k=\frac1{LAD},\qquad
 \sigma_k=\frac DL+\frac E{2A}+\frac A{2D},\qquad
 B_{k,j}=\sigma_k+\kappa_k\left(j+\tfrac12\right).
$$

则 $k\to\infty$ 时

$$
 \tau_{k,j}=\frac{j+1}{c_k}+j-\sigma_k-\kappa_k\left(j+\tfrac12\right)+O_j(Dc_k).
 \tag{14.24}
$$

这里的余项对固定 $j$ 给出完整有限乘积控制：若 $t\ge2(j+1)$，则

$$
 \log\frac{H(t)}{c_k}=\frac{B_{k,j}}t+\mathcal R_{k,j}(t),\qquad
 |\mathcal R_{k,j}(t)|\le\frac{2D(j+1)^2}{t^2}.
 \tag{14.25}
$$

证明。把每个有限因子按 $t$ 归一化，置

$$
 \alpha_i=\frac{Ej+i}{A}\ (1\le i\le E),\quad
 \beta_s=\frac{Aj+s}{D}\ (1\le s\le A),\quad
 \gamma_h=\frac{Dj+h-\tfrac12}{L}\ (0\le h<D).
$$

则

$$
 \frac{H(t)}{c_k}=\frac{\prod_i(1+\alpha_i/t)\prod_s(1+\beta_s/t)}{\prod_h(1+\gamma_h/t)},
$$

且直接求和得到

$$
 \sum_i\alpha_i+\sum_s\beta_s-\sum_h\gamma_h
 =\sigma_k+\kappa_k\left(j+\tfrac12\right)=B_{k,j}.
 \tag{14.26}
$$

这里 $E^2/A+A^2/D-D^2/L=\kappa_k$，仍是 Cassini 恒等式。所有这些偏移的绝对值不超过 $j+1$。当 $t\ge2(j+1)$ 时，$|x|\le1/2$ 且
$|\log(1+x)-x|\le x^2$；分子、分母合计 $2D$ 个因子，故得（14.25）。

令 $M=(j+1)/c_k$。有 $c_k\le4^{-D}$，所以 $Dc_k\to0$。由（14.25），$q_{k,j}(M/2)<1$ 对充分大的 $k$ 成立，而定理 14.2 给 $\tau_{k,j}<M+j$；故 $\tau_{k,j}\asymp M$，并可在根处使用（14.25）。精确根方程为

$$
 \left|\log\frac{\tau_{k,j}-j}{M}+\frac{B_{k,j}}{\tau_{k,j}}\right|\le
 \frac{2D(j+1)^2}{\tau_{k,j}^2}.
 \tag{14.27}
$$

在 $\log(1+u)=u+O(u^2)$ 中令
$u=(\tau_{k,j}-M-j)/M$，并用 $\tau_{k,j}\asymp M$，即得
$\tau_{k,j}=M+j-B_{k,j}+O_j(D/M)$，这就是（14.24）。证明中的 $O_j(D/M)$ 完全由（14.27）及（14.25）给出，而 $1/M=c_k/(j+1)$。证毕。

为比较（14.24）与连续少数坐标，以下在本章另记
$r_k:=1-x_k$；它只表示定义 12.1 的连续最小点少数比例，不表示定义 2.1 的许可斜率。由（13.12）及其驻点方程，若
$\Delta_k=\delta-K'(r_k)$，则

$$
 \frac{c_k}{r_k}=(1-r_k)^{-1}e^{-\Delta_k},\qquad
 0\le\Delta_k\le\kappa_k r_k.
 \tag{14.28}
$$

因此 $r_k\to0$、$\kappa_k\to0$、$\sigma_k\to2/\phi$，并且

$$
 \frac1{c_k}-\frac1{r_k}\longrightarrow-1,\qquad
 \tau_{k,j}-\frac{j+1}{r_k}\longrightarrow
 -1-\frac2\phi=-\sqrt5.
 \tag{14.29}
$$

这个极限固定 $j$；它是加性穿越位移，不是把 $j$ 或 $t$ 一起增长的均匀估计。

**定理 14.5（固定正整数临界中心的整网格唯一模式）。** 对每个固定正整数 $m$，令

$$
 t_k^-=\left\lfloor\frac m{r_k}\right\rfloor,\qquad
 t_k^+=\left\lceil\frac m{r_k}\right\rceil.
 \tag{14.30}
$$

充分大的 $k$ 下，二者均为合法整数，且

$$
 t_k^\pm>\tau_{k,m-1}.
 \tag{14.31}
$$

于是 $Q_{k,t_k^\pm,m-1}>1$；结合（13.14）的固定 $m$ 临界范围，两个整网格的唯一极值指标均为 $m$。两条序列最终都严格避开整数 tie。

证明。由（14.29），
$\frac m{r_k}-\tau_{k,m-1}\to\sqrt5$。故
$t_k^--\tau_{k,m-1}\ge\frac m{r_k}-1-\tau_{k,m-1}\to$ 一个严格大于零的下界 $\sqrt5-1$，而 $t_k^+\ge m/r_k$；（14.31）成立。又 $t_k^\pm r_k\to m$，所以可对两条序列应用（13.14）：有限极值指标只能是 $m-1$ 或 $m$。严格不等式 $Q_{k,t_k^\pm,m-1}>1$ 排除 $m-1$，故唯一指标为 $m$。定义 14.1 的实延拓不把实数树引入结论；所有模式结论都回到整数来源网格和（12.3）的完整树像。证毕。

**推论 14.6（可核验的无并列子族与剩余整数边界）。** 当 $k=1$ 且 $j\equiv0\pmod3$ 时，不存在合法整数 $t$ 使 $Q_{1,t,j}=1$。任意其他 $(k,j)$ 的整数 tie 恰由（14.21）的正整数方程

$$
 (t-j)(a+1)_E(b+1)_A
 =(j+1)2^D\prod_{h=0}^{D-1}(2n+2h-1)
 \tag{14.32}
$$

决定；本章不把该剩余的参数集合分类为全无并列。

证明。在 $k=1$ 时 $E=A=1,D=2,L=3$，（14.32）化为

$$
 (t-j)(t+j+1)(2t+j+1)
 =4(j+1)\bigl(4(3t+2j)^2-1\bigr).
 \tag{14.33}
$$

若 $j\equiv0\pmod3$，左边模 $3$ 为 $t(t+1)(2t+1)\equiv0$，右边模 $3$ 为 $-1\equiv2$，矛盾。其余情形仍由（14.22）给出逐个有限的精确判定。证毕。

本章的 $q_{k,j}(t)$ 只是在完整树密度比的整数值上方延拓的有限乘积；它不表示实大小树、概率律、物理时间、Lorentz 含义或指定树的实际逆执行许可。上述跨越、阈值和唯一模式均限于定义 12.1 的组成、完整有序树计数与实际替换像。

## 追加锚（本行以下为增补区）

## 15. 完整来源密度的整数并列、本原尺度与首深度有限性

**定义 15.1（完整树来源与原整数域的并列多项式）。** 沿用[定义 1.1](#1-有限预算的尺度读出与逆许可分离)、[定义 2.1](#2-许可预算阶梯与深层碰撞前沿)及[定义 12.1](#12-完整树替换像的计数密度祖先混合与共轭来源偏差)。$\mathcal T$ 是所有非空有限自由有序完全二叉树，每片叶标记为 $\alpha$ 或 $\beta$，二元构造不附加交换律或结合律；组成 $c(T)$ 只计数两类叶，保留树本身的全部括号与从左到右叶序。替换仍为

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle U,V\rangle)=\langle\rho(U),\rho(V)\rangle.
$$

完整序列化复用[母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)：
$\operatorname{code}(\alpha)=\alpha\alpha$、$\operatorname{code}(\beta)=\alpha\beta$、$\operatorname{code}(\langle U,V\rangle)=\beta\operatorname{code}(U)\operatorname{code}(V)$，其唯一解析与前缀自由刻画原始树。全部路径观察复用同节定理 9.3：对每个有限左右词，包括空词所指的根，读取 $\alpha$、$\beta$、分支或不存在；这些读数共同恢复原始树。它们不成为定义 1.1 的单个末端数量报告的附加输入。

固定任意整数 $k\ge1$，仍记

$$
d=3k,\qquad E=F_{d-2},\quad A=F_{d-1},\quad
D=F_d=E+A,\quad L=F_{d+1}=A+D.
$$

对每个整数 $t\ge1$，整张网格取 $0\le j\le t$，祖先组成为 $(t-j,j)$，目标组成为
$a_j=At+Ej$、$b_j=Dt+Aj$，目标叶数为 $n_j=Lt+Dj$。由[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的树替换单射性及（12.3）、（12.15），所比较的密度准确为

$$
R_{k,t-j,j}
=\frac{|\rho^{3k}(\mathcal T_{t-j,j})|}{|\mathcal T_{a_j,b_j}|}
=\frac{C_{t-1}\binom tj}{C_{n_j-1}\binom{n_j}{a_j}},\qquad
Q_{k,t,j}=\frac{R_{k,t-j-1,j+1}}{R_{k,t-j,j}}\quad(0\le j<t).
\tag{15.1}
$$

每张 $(k,t)$ 网格若保留有限预算，使用自己的共同预算 $H_t\ge F_{3k+2}t$，包含全部目标树纤维。组成祖先许可 $S^{-k}c\in\mathbb N_0^2$、指定树属于 $\rho^{3k}(\mathcal T)$、以及允许的实际逆执行是三个不同关系；（15.1）只比较第二个关系在许可组成纤维内的实际集合计数。这里 $L$ 只缩写 Fibonacci 数，密度不指定实际来源的概率律，环境坐标的代数守恒也不提供物理对应。

对相邻比较置 $m=j+1$，故原整数域准确为 $m\ge1,t\ge m$。在整数多项式环 $\mathbb Z[T,m]$ 中定义

$$
\begin{aligned}
\mathcal A_k(T,m)
&=(T-m+1)\prod_{r=0}^{E-1}(AT+Em-r)
                    \prod_{s=0}^{A-1}(DT+Am-s),\\
\mathcal B_k(T,m)
&=2^D m\prod_{h=0}^{D-1}(2LT+2Dm-2D+2h-1),\\
\mathsf P_k(T,m)&=\mathcal A_k(T,m)-\mathcal B_k(T,m),\\
G_k&=AD(E-1)!(A-1)!,\qquad
K_k=2^D\prod_{h=0}^{D-1}(2h+3).
\end{aligned}
\tag{15.2}
$$

这两个新常数不改变第14章的 $\kappa_k$。多项式的原点及其他域外代入只作辅助代数，不表示合法树。对素数 $p$，$v_p$ 表示非零有理数的通常 $p$ 进赋值，并约定 $v_p(0)=+\infty$。

**定理 15.2（原域精确等价与全深度共同素数约束）。** 对全部合法整数 $k\ge1,m\ge1,t\ge m$，有

$$
\mathcal B_k(t,m)>0,\qquad
Q_{k,t,m-1}=\frac{\mathcal A_k(t,m)}{\mathcal B_k(t,m)},\qquad
\operatorname{sgn}(Q_{k,t,m-1}-1)=\operatorname{sgn}\mathsf P_k(t,m).
\tag{15.3}
$$

特别地，原树网格的精确并列当且仅当 $\mathsf P_k(t,m)=0$。此外

$$
\mathsf P_k(T,m)=G_kT^2-K_km+\mathcal R_k(T,m),\qquad
\mathcal R_k\in(T^3,Tm,m^2)\subset\mathbb Z[T,m].
\tag{15.4}
$$

若合法点精确并列，且素数 $p>2D+1$ 同时整除 $t,m$，置 $f=v_p(t)\ge1$、$e=v_p(m)\ge1$，则

$$
e=2f,\qquad
G_k\left(\frac{t}{p^f}\right)^2
\equiv K_k\frac{m}{p^{2f}}\pmod p.
\tag{15.5}
$$

$p>2D+1$ 是下述单位系数比较所需的范围，不得从该证明省去；本结论不对遗漏的小素数或非共同素数作同一推断。

证明。将（14.21）中的 $j$ 换成 $m-1$，两个分子块分别反向编号为
$\prod_{r=0}^{E-1}(AT+Em-r)$ 与 $\prod_{s=0}^{A-1}(DT+Am-s)$，分母块得到（15.2）。在合法域，$n=Lt+D(m-1)\ge Lt\ge3$，所以每个分母因子 $2n+2h-1$ 都为正；$m>0$。于是（14.1）、（14.2）直接给（15.3），没有改变树网格的定义域。

由 $M^3=\left(\begin{smallmatrix}1&2\\2&3\end{smallmatrix}\right)\equiv I\pmod2$，其迭代的非对角元 $D=F_{3k}$ 为偶数。在 $(T,m)=(0,0)$，两个分子块各恰有一个零端点，其余常数的乘积为
$(-1)^{D-2}(E-1)!(A-1)!=(E-1)!(A-1)!$。因而模理想 $(T^3,Tm,m^2)$，分子恰为 $G_kT^2$。分母除去 $m$ 后的常数因子是 $-3,-5,\ldots,-(2D+1)$；$D$ 偶数使其乘积为正，故分母恰为 $K_km$ 模同一理想。这证明（15.4）。在首深度 $E=A=1,D=2,L=3$，直接展开同一个多项式还得到

$$
\mathsf P_1(t,m)
=2t^3+(2-143m)t^2+(-194m^2+195m)t
 -65m^3+129m^2-60m.
\tag{15.6}
$$

若 $p>2D+1$，$G_k$ 的全部素因子来自 $A,D$ 及两个阶乘，$K_k$ 的全部素因子来自 $2$ 和不超过 $2D+1$ 的奇数，故两者都是 $p$ 进单位。将（15.4）代入并列点，两个显示项的赋值分别为 $2f,e$；余项每个单项式的赋值至少为
$\min\{3f,f+e,2e\}$。若 $e<2f$，只有 $-K_km$ 的赋值最小；若 $e>2f$，只有 $G_kt^2$ 的赋值最小。有限和中唯一最低赋值项不能被其他项消去，两种情形都与等于零矛盾。因此 $e=2f$。此时余项的赋值至少为 $3f>2f$，除以 $p^{2f}$ 后模 $p$ 即得（15.5）。小素数处显示系数可能不为单位，故上述唯一最低赋值论证不适用。证毕。

**定理 15.3（本原方向与共同尺度的严格约束）。** 对任意合法精确并列，置

$$
x=t-j=t-m+1,\qquad y=j+1=m,\qquad
g=\gcd(x,y)=\gcd(t+1,m),\qquad u=x/g,\quad v=y/g,
$$

并定义仅依赖固定 $k$ 的正整数

$$
B_k^*=\frac{(L-1)!}{(A-1)!},\qquad
C_k^*=2^D\prod_{h=0}^{D-1}(2L+2h+3).
\tag{15.7}
$$

则 $u>v\ge1$、$\gcd(u,v)=1$，且

$$
1<\frac uv<\frac1{c_k}<\frac{C_k^*}{B_k^*},\qquad
g\mid(C_k^*v-B_k^*u),\qquad
0<g\le C_k^*v-B_k^*u,
\tag{15.8}
$$

其中 $c_k$ 是（14.4）的原常数。尤其

$$
g^2<(C_k^*-B_k^*)y,\qquad
y<(C_k^*-B_k^*)v^2.
\tag{15.9}
$$

对每个固定 $k$ 和整数 $V\ge1$，约分后分母 $v\le V$ 的全部合法并列点只有有限多个，并且 $j+1<(C_k^*-B_k^*)V^2$；一个固定互素方向 $(u,v)$ 不能在无界共同尺度上并列。在 $k=1$ 时，这些约束具体为

$$
B_1^*=2,\quad C_1^*=396,\qquad
g\mid2(198v-u),\qquad g^2<394(j+1).
\tag{15.10}
$$

证明。复用定理 14.2 的严格根区间，精确并列满足
$2j+1<t<j+(j+1)/c_k$，所以 $1<u/v<1/c_k$。将
$t=g(u+v)-1$、$j=gv-1$ 代入，目标坐标准确为

$$
a=g(Au+Dv)-D,\qquad
b=g(Du+Lv)-L,\qquad
n=g(Lu+(L+D)v)-(L+D).
$$

（14.32）的两边各含同一个因子 $g>0$。约去后，将剩余式写为整数多项式 $\Phi(z)$ 在 $z=g$ 处等于零，其中

$$
\begin{aligned}
\Phi(z)={}&u\prod_{i=1}^{E}\bigl(z(Au+Dv)-D+i\bigr)
              \prod_{s=1}^{A}\bigl(z(Du+Lv)-L+s\bigr)\\
&-v2^D\prod_{h=0}^{D-1}
 \bigl(2z(Lu+(L+D)v)-2(L+D)+2h-1\bigr).
\end{aligned}
\tag{15.11}
$$

在 $z=0$，两个分子块合为
$(-1)^D(D-1)!/(A-1)!\cdot(L-1)!/(D-1)!=B_k^*$。分母块反向编号后合为 $C_k^*$。因此
$\Phi(0)=uB_k^*-vC_k^*$，而 $\Phi(g)=0$ 蕴含 $g\mid\Phi(0)$。这里的 $z=0$ 只是整数多项式常数项，不是树来源。

为统一确定常数项的符号，令 $s=ED-A^2\in\{1,-1\}$。Cassini 与递推给
$AD=EL-s$、$D^2=AL+s$。将带重数的 $D$ 个分数

$$
\left\{\frac iA:0\le i<E\right\}
\mathbin{\sqcup}\left\{\frac rD:0\le r<A\right\}
$$

按非降次序写成 $z_0,\ldots,z_{D-1}$。对 $0\le h\le D-1$，有

$$
\frac{Ah}{L}\le E-\frac{A+s}{L}<E,\qquad
\frac{Dh}{L}\le A-\frac{D-s}{L}<A.
\tag{15.12}
$$

两处严格性分别用 $A+s>0$、$D-s>0$；$k=1$ 时 $s=1,A=1,D=2$ 也成立。因此计数没有端点截断，小于等于 $h/L$ 的上述分数数目准确为
$\lfloor Ah/L\rfloor+\lfloor Dh/L\rfloor+2\ge h+1$，因为 $A+D=L$。故 $z_h\le h/L$。相同的两个连续整数块给

$$
\frac{B_k^*}{A^ED^A}=\prod_{h=0}^{D-1}(1+z_h)
<\prod_{h=0}^{D-1}\left(1+\frac{h+3/2}{L}\right)
=\frac{C_k^*}{4^DL^D}.
\tag{15.13}
$$

每个匹配因子都严格小于右侧因子，于是 $C_k^*/B_k^*>1/c_k$。特别地 $C_k^*>B_k^*$，因为 $c_k<1$。结合并列方向的 $u/v<1/c_k$，得 $C_k^*v-B_k^*u>0$；正整数被 $g$ 整除便至少为 $g$，证明（15.8）。又 $u>v$，分别将尺度上界乘以 $g$ 和 $v$，得到

$$
g^2\le g(C_k^*v-B_k^*u)<(C_k^*-B_k^*)gv,
\qquad
y=gv\le C_k^*v^2-B_k^*uv<(C_k^*-B_k^*)v^2.
$$

这就是（15.9）及严格平方根界 $g<\sqrt{(C_k^*-B_k^*)y}$。固定 $k,V$ 后，$y$ 有统一整数上界，且定理 14.2 再给 $t<y-1+y/c_k$，所以两个原整数参数均有界。固定 $(u,v)$ 的尺度上界则直接来自（15.8）。代入首深度的四个 Fibonacci 数即得（15.10）。本定理的共同因子是 $\gcd(t+1,m)$，与定理 15.2 的 $\gcd(t,m)$ 不同。证毕。

**定理 15.4（首深度的联合有限性与整网格最终唯一模式）。** 原整数域中的集合

$$
\mathcal Z_1=\{(t,j)\in\mathbb Z^2:j\ge0,\ t\ge j+1,\ Q_{1,t,j}=1\}
\tag{15.14}
$$

是有限集。这是同时遍历 $t,j$ 的有限性，未对 $j$ 预设上界。因而存在整数 $T_0\ge1$，使每个整数 $t\ge T_0$ 的整个 $k=1$ 来源网格都恰有一个最大密度指标。该结论不提供有效截止或例外点列表；$\mathcal Z_1$ 是否非空及其全部合法整数点仍未由此确定，也不推出 $k\ge2$ 或增长深度下的联合有限性。

证明。由（15.3）、（15.6），将 $m=j+1$ 代回原整数坐标，合法并列恰是下列三次式的合法整数零点：

$$
\begin{aligned}
P(t,j)={}&2t^3-(143j+141)t^2+(-194j^2-193j+1)t\\
&-65j^3-66j^2+3j+4.
\end{aligned}
\tag{15.15}
$$

它的射影齐次化可直接从（14.33）写为

$$
F(T,J,Z)=(T-J)(T+J+Z)(2T+J+Z)
 -4(J+Z)\bigl(4(3T+2J)^2-Z^2\bigr).
\tag{15.16}
$$

其 $Z=1$ 仿射嵌入就是 $(t,j)$，没有作有理坐标变换。模 $11$ 的三个偏导准确为

$$
\begin{aligned}
\overline F_T&=6T^2+4J^2+4TZ+5JZ+Z^2,\\
\overline F_J&=8TJ+5TZ+3J^2+3Z^2,\\
\overline F_Z&=2T^2+5TJ+2TZ+6JZ+Z^2.
\end{aligned}
\tag{15.17}
$$

以下消去在 $\overline{\mathbb F}_{11}$ 上进行。在 $Z=0$，若 $J=0$，$\overline F_T=0$ 迫使 $T=0$，不能给射影点。若 $J\ne0$，置 $x=T/J$；$\overline F_J=0$ 迫使 $8x+3=0$，即 $x=1$，但这时 $\overline F_T/J^2=6+4=10\ne0$。所以无穷远处没有共同偏导零点。在 $Z\ne0$，缩放为 $Z=1$，偏导的恒等式

$$
\overline F_J-6\overline F_Z+2\overline F_T=T-4J-1
$$

迫使任何共同零点满足 $T=4J+1$。代入后

$$
\overline F_T=J(J+3),\qquad
\overline F_J=2J(J+3)+8,
\tag{15.18}
$$

两式不能同时为零。因此该射影三次曲线模 $11$ 光滑；这不是只检查有限域有理点，而是排除了代数闭包中的全部奇点。

若特征零曲线存在代数奇点，其坐标落在某个数域。在一个位于 $11$ 上方的离散赋值环中，将齐次坐标共同缩放为全体整且至少一项为单位。整数系数的 $F$ 及其三个齐次偏导仍全部为零，约化便给模 $11$ 代数闭包中一个非零射影共同零点，与上述消去矛盾。因此 $F=0$ 在 $\overline{\mathbb Q}$ 上也光滑。

此非零三次式定义平面 Cartier 曲线，故等维为一且无嵌入点。[Stacks Project，Plane curves，Lemma 53.9.3（tag 0BYA）](https://stacks.math.columbia.edu/tag/0BYA)在 $\overline{\mathbb Q}$ 上给 $H^0(\mathcal O)=\overline{\mathbb Q}$ 及亏格 $(3-1)(3-2)/2=1$。第一式使曲线连通，光滑性使其约化；不同不可约分量若相交，交点局部环便不是正则的一维局部环，故光滑曲线的分量互不相交。连通性于是给几何不可约，从而它是几何整的光滑射影亏格一曲线。$Z=0$ 上的非零齐次三次式有代数零点，所以 $Z=1$ 部分是删去非空无穷远边界所得的光滑仿射曲线，其光滑射影完成仍是这条曲线。

现在将 [Aaron Levin，*Integral points of bounded degree on affine curves*，arXiv:1402.2346v1，引言及 Theorem 1.1](https://arxiv.org/pdf/1402.2346v1)所述的 Siegel 正亏格仿射整点有限性直接用于此原仿射嵌入。数域取 $\mathbb Q$，有限位集取 $S=\{\infty\}$；$\mathcal O_{\mathbb Q,S}=\mathbb Z$，故其 $S$ 整点准确是 $P(t,j)=0$ 的原坐标整数点。同文定理 1.2 后的正规化说明与这里相容：已经光滑的仿射曲线就是自身的正规化，不需从另一个有理模型运输整性。亏格为一使该整数点集有限，合法子集 $\mathcal Z_1$ 因而有限。

取 $T_0$ 严格大于 $\mathcal Z_1$ 的全部 $t$ 坐标；若该集为空可取 $T_0=1$。对 $t\ge T_0$，全网格没有任何相邻比值等于一。复用定理 13.1（一）的严格相邻比下降与端点交叉，最大密度指标便唯一；$t=1$ 的唯一性也已在该定理内。每张网格仍取共同预算 $H_t\ge F_5t=5t$。Siegel 的有限性在此未附带可计算的高度上界，故不能据此枚举例外，也不能把首深度结论外推到其他深度。证毕。

**定理 15.5（首深度互素排除与平方自由无并列族）。** 每个合法 $k=1$ 精确并列都满足 $\gcd(t,j+1)>1$。因此，对所有 $j\ge0$，若 $m=j+1$ 平方自由且 $\gcd(m,30)=1$，则每个合法整数 $t\ge m$ 都有 $Q_{1,t,j}\ne1$。

证明。假设 $\gcd(t,m)=1$ 且存在合法并列。（15.6）模 $m$ 为 $2t^2(t+1)$，故 $m\mid2(t+1)$。直接代入同一个三次式给

$$
\begin{aligned}
\mathsf P_1(71m-1,m)&=m(-18880m^2+14310m-256)<0,\\
\mathsf P_1(73m-1,m)&=m(1760m^2+14120m-252)>0
\qquad(m\ge1).
\end{aligned}
\tag{15.19}
$$

第一行括号至多为 $-4570m-256$；第二行括号至少为 $1760+14120-252>0$。两个横坐标都在 $t\ge m$ 的合法实延拓域内。由（15.3）及定理 14.2 的唯一穿越，任何并列必须严格满足 $71m-1<t<73m-1$。于是
$r=2(t+1)/m$ 是严格位于 $142$ 与 $146$ 之间的整数，只能取 $143,144,145$。这是整除性强制的三个方向。

在这些方向，原三次式准确化为

$$
\begin{array}{c|c}
r=143,\ t=143m/2-1
&\mathsf P_1(t,m)=\dfrac m2(-27872m^2+28531m-510)\\[3pt]
r=144,\ t=72m-1
&\mathsf P_1(t,m)=m(-8849m^2+14219m-254)\\[3pt]
r=145,\ m=2h,\ t=145h-1
&\mathsf P_1(t,2h)=2h(-14470h^2+28341h-253).
\end{array}
\tag{15.20}
$$

第一行中 $t$ 整数迫使 $m$ 为偶数，故 $m\ge2$；括号至多为 $-27213m-510<0$。第二行的二次式在 $m\ge1$ 严格下降，在 $1,2$ 处分别为 $5116,-7212$，所以没有正整数零点。第三行中 $h\ge1$，二次式也严格下降，在 $1,2$ 处分别为 $13618,-1451$，也没有正整数零点。三个方向都不能并列，证明互素排除。

若 $m$ 平方自由且与 $30$ 互素，任何同时整除 $t,m$ 的素数 $p$ 都大于 $5=2D+1$，且 $v_p(m)=1$。定理 15.2 却要求 $1=2v_p(t)$，矛盾。因此精确并列会迫使 $\gcd(t,m)=1$，又被刚证的首深度互素排除否定。$m=1$ 也由该互素排除涵盖。这一无界族包括 $m=11,j=10$，但没有排除全部非平方自由参数或全部与 $30$ 不互素的参数。证毕。

**定理 15.6（联合实精度与任意固定有限素数精度的严格非并列）。** 对每个固定整数 $k\ge1$ 和 $B\ge2$，存在无穷多个不同合法整数对 $(t_N,j_N)$，使

$$
Q_{k,t_N,j_N}>1,\qquad Q_{k,t_N,j_N}\longrightarrow1,
\qquad
v_p(Q_{k,t_N,j_N}-1)\ge v_p(B)\quad\text{对每个 }p\mid B.
\tag{15.21}
$$

因此，对任意给定实误差 $\epsilon>0$ 和任意给定有限组素数及其正整数精度，同时满足 $0<Q-1<\epsilon$ 与这些 $p$ 进精度的合法点仍可严格非并列。这些固定精度条件不蕴含精确等号；本结论不否定定理 14.3 对每个 $(k,j)$ 的自适应精确整数判定。

证明。先在（15.4）的辅助整数多项式中代入
$T=K_k Z$、$m=G_kK_kZ^2$。两个显示的二次项相消，理想中的三个生成元分别带至少三次的 $Z$，所以存在 $U,V\in\mathbb Z[Z]$，使

$$
\mathsf P_k(K_kZ,G_kK_kZ^2)=Z^3U(Z),\qquad
\mathcal B_k(K_kZ,G_kK_kZ^2)=Z^2V(Z),\qquad
V(0)=V_0:=G_kK_k^2>0.
\tag{15.22}
$$

最后的常数再次由 $D$ 偶数及分母奇数块的常数项得到。取 $Z_0=V_0B$，定义整数 $t_0=K_kZ_0$、$m_0=G_kK_kZ_0^2$。这只是代数剩余类种子，不要求 $t_0\ge m_0$，不把它当作合法树网格。因为 $t_0,m_0\ge1$，$Lt_0+D(m_0-1)\ge L$，故其分母值
$b_0:=\mathcal B_k(t_0,m_0)>0$。

对每个 $p\mid B$，写 $b=v_p(B)\ge1$、$v_0=v_p(V_0)$。由 $V(Z)=V_0+ZW(Z)$、$W\in\mathbb Z[Z]$ 及 $v_p(Z_0)=v_0+b>v_0$，得到 $v_p(V(Z_0))=v_0$。因而（15.22）给

$$
v_p\left(\frac{\mathsf P_k(t_0,m_0)}{b_0}\right)
\ge v_p(Z_0)-v_0=b.
\tag{15.23}
$$

这一步对整除 $G_k,K_k$ 的小素数也成立，没有要求分母在 $p$ 处为单位。

令 $\Lambda=Bb_0>0$。对每个整数 $N\ge0$，取

$$
\begin{gathered}
m_N=m_0+\Lambda N,\qquad j_N=m_N-1,\\
t_N=t_0+\Lambda\left(
\left\lfloor\frac{\tau_{k,j_N}-t_0}{\Lambda}\right\rfloor+1\right).
\end{gathered}
\tag{15.24}
$$

定理 14.2 给 $\tau_{k,j_N}>2m_N-1\ge m_N$，取整公式给
$\tau_{k,j_N}<t_N\le\tau_{k,j_N}+\Lambda$。所以 $t_N$ 是合法整数且严格在穿越右侧，$Q_{k,t_N,j_N}>1$。不同 $N$ 的 $m_N$ 不同，所得合法对无穷多个。

同时 $(t_N,m_N)\equiv(t_0,m_0)\pmod\Lambda$，两个整数多项式的值都保持该同余。固定 $p\mid B$，置 $d_0=v_p(b_0)$，则 $v_p(\Lambda)=d_0+b>d_0$，从而
$v_p(\mathcal B_k(t_N,m_N))=d_0$。由（15.23），$v_p(\mathsf P_k(t_0,m_0))\ge d_0+b$，而同余进一步给
$v_p(\mathsf P_k(t_N,m_N))\ge d_0+b$。用（15.3）相除即得（15.21）的全部赋值条件。这里保留了每个模数素因子处的真实分母赋值，而不是只对未约分的分子作同余比较。

最后固定 $m=m_N$，在 $\tau_{k,m-1}\le t\le t_N$ 上使用（14.1）的实辅助延拓。它的对数导数为

$$
\frac1{t-m+1}
+\sum_{i=1}^{E}\frac A{At+E(m-1)+i}
+\sum_{s=1}^{A}\frac D{Dt+A(m-1)+s}
-\sum_{h=0}^{D-1}\frac{2L}{2Lt+2D(m-1)+2h-1}.
$$

丢去最后的负项；前面两块共有 $E+A=D$ 项，每项至多为 $1/t\le1/m$，而 $t>2m-1$ 给 $1/(t-m+1)<1/m$。定理 14.2 又保证对数导数为正，所以从根处 $\log q=0$ 积分得到

$$
0<\log Q_{k,t_N,j_N}
\le\frac{(D+1)(t_N-\tau_{k,j_N})}{m_N}
\le\frac{(D+1)\Lambda}{m_N}\longrightarrow0.
\tag{15.25}
$$

这证明实数比值趋于一。对任意有限组素数精度，取 $B$ 为相应素数幂的乘积即可；若组为空，可取 $B=2$。每个最终点的两端祖先组成为 $(t_N-j_N,j_N)$ 和 $(t_N-j_N-1,j_N+1)$，都是原域内的非空整数组成，全部有完整有序树代表；各自的实际替换像仍由（15.1）计数，每张网格取 $H_{t_N}\ge F_{3k+2}t_N$。种子的域外代入及证明中的实积分都未取代这些最终合法树。所构造的点全部严格非并列，并不确定精确并列是否存在、首深度全部合法整点或增长深度的无界本原方向分类。证毕。

## 追加锚（本行以下为增补区）


## 16. 实际树像与尖锐有限路径观察前沿

**定义 16.1（原始路径视界、实际像指标与联合观察）。** 沿用[定义 1.1](#1-有限预算的尺度读出与逆许可分离)的非空有限有序满二叉树集合 $\mathcal T$、叶标记 $\alpha,\beta$、组成 $c$ 及替换 $\rho$。这里的树相等仍是自由语法相等；左地址记为 $\mathtt L=0$，右地址记为 $\mathtt R=1$。对有限地址 $u\in\{\mathtt L,\mathtt R\}^*$，令 $\operatorname{out}_T(u)$ 为沿 $u$ 行走时的原始终点结果：若抵达内节点则记 $\mathsf{branch}$，若抵达 $\alpha$ 或 $\beta$ 叶则分别记 $\mathsf{leaf}_\alpha$ 或 $\mathsf{leaf}_\beta$，若在某个叶处继续行走则记 $\mathsf{absent}$。空地址 $\varepsilon$ 也在定义域内，因而根的实际结果被保留。对原始深度 $h\in\mathbb N_0$，定义完整有限路径窗口

$$
\Sigma_{\le h}=\{u\in\{\mathtt L,\mathtt R\}^*:|u|\le h\},\qquad
O_h(T)=\bigl(\operatorname{out}_T(u)\bigr)_{u\in\Sigma_{\le h}}.
\tag{16.1}
$$

母卷定理 9.2 的唯一解析码与定理 9.3 的全路径恢复保证：当 $h\ge\operatorname{ht}(T)$ 时，$O_h(T)$ 已确定整个 $T$；这里 $\operatorname{ht}$ 取叶高为 $0$、内节点高为左右子树高的最大值加 $1$。给定替换迭代数 $d=3k$（$k\ge1$），令

$$
\mathcal I_d=\rho^d(\mathcal T),\qquad
\iota_d(T)=\mathbf 1_{\{T\in\mathcal I_d\}},\qquad
\mathcal T_H=\{T\in\mathcal T:|\operatorname{Leaves}(T)|\le H\}.
\tag{16.2}
$$

$\iota_d$ 是目标实际像指标；它只判定指定完整树是否属于实际替换像。组成 $c$ 是与 $O_h$ 同时给定的数学观察输入，不是由本节另行取得的物理量。对 $V\in\mathcal T_H$，记联合观察纤维为

$$
\mathcal F^{c,O}_{H,h}(V)=\{U\in\mathcal T_H:c(U)=c(V),\ O_h(U)=O_h(V)\},
\tag{16.3}
$$

并称其在 $\iota_d$ 下单色，当且仅当 $\iota_d$ 在该集合上为常值。原始深度 $h$ 只计地址窗口 $\Sigma_{\le h}$ 的层数；替换迭代 $d$ 只计 $\rho$ 的次数。二者都不是墙钟时间、物理尺度或任何未给定的实现参数。

**定理 16.1（实际像正纤维的尖锐性）。** 设 $V\in\mathcal I_d$，$H\ge|\operatorname{Leaves}(V)|$。则

$$
\mathcal F^{c,O}_{H,h}(V)\text{ 在 }\iota_d\text{ 下单色}
\quad\Longleftrightarrow\quad
h\ge\operatorname{ht}(V).
\tag{16.4}
$$

当 $h\ge\operatorname{ht}(V)$ 时，纤维恰为 $\{V\}$。当 $h<\operatorname{ht}(V)$ 时，纤维中存在 $W$ 满足

$$
\iota_d(W)=0,\qquad c(W)=c(V),\qquad O_h(W)=O_h(V),\qquad
|\operatorname{Leaves}(W)|=|\operatorname{Leaves}(V)|.
\tag{16.5}
$$

证明。规范编译卷命题 4.3 已给出树作用的单射性及其实际像的非满性；这里沿用该作用，只分析固定实际像中的有限路径纤维。先记录一个由替换规则直接得到的像障碍：任何 $\rho$-像中的 $\alpha$ 叶都来自某个 $\beta$ 叶的替换 $\langle\beta,\alpha\rangle$，而任意来源子树的像都不以 $\alpha$ 为根（命题 4.3 的实际像描述）。因此 $\rho(\mathcal T)$ 中不存在以 $\alpha$ 为左孩子的叶。

对任意树 $X$，$\rho^2(X)$ 的每个末端樱桃都是 $\langle\beta,\alpha\rangle$。确实，$\rho^2(\alpha)=\langle\beta,\alpha\rangle$，$\rho^2(\beta)=\langle\langle\beta,\alpha\rangle,\beta\rangle$；若 $X=\langle X_0,X_1\rangle$，则 $\rho^2(X)=\langle\rho^2(X_0),\rho^2(X_1)\rangle$，末端樱桃不会跨过来源二叉节点。因 $d\ge3$，$\mathcal I_d\subseteq\rho^2(\mathcal T)$，故 $V$ 的每个末端樱桃（特别是最深叶所在的那个）均为 $\langle\beta,\alpha\rangle$。

若 $h\ge\operatorname{ht}(V)$，有限窗口已经包含 $V$ 的所有节点。沿根递归比较，另一棵具有相同 $O_h$ 的树在每个已见节点都必须有相同的分支或叶；叶处的结果又禁止继续延伸。因此另一棵树只能等于 $V$，纤维为单点。

反设 $h<\operatorname{ht}(V)=D$。取深度为 $D$ 的一片叶。其兄弟必也是叶，否则会出现更深叶；故其父节点是深度 $D-1$ 的末端樱桃 $\langle\beta,\alpha\rangle$。把该处替换成 $\langle\alpha,\beta\rangle$ 得树 $W$。括号形状、所有叶地址及组成均不变，只有深度 $D>h$ 的两片叶标签互换；所以所有地址的分支和 $\mathsf{absent}$ 结果都不变，且 $O_h(W)=O_h(V)$。新树有一个 $\alpha$ 左孩子，故由上述像障碍 $W\notin\rho(\mathcal T)$，从而 $W\notin\mathcal I_d$。它与 $V$ 叶数相同，故 $W\in\mathcal T_H$，得到（16.5）。证毕。

**定义 16.2（块尺度与首个歧义预算）。** 置 $T_j=\rho^j(\alpha)$，并置

$$
A_d=\rho^d(\alpha)=T_d,\qquad B_d=\rho^d(\beta)=T_{d+1},\qquad
a=|\operatorname{Leaves}(A_d)|=F_{d+1},\qquad
b=|\operatorname{Leaves}(B_d)|=F_{d+2}.
\tag{16.6}
$$

母卷定理 3.2--3.4 给出 $T_{j+2}=\langle T_{j+1},T_j\rangle$ 及组成递推；因而

$$
\operatorname{ht}(A_d)=d-1,\quad \operatorname{ht}(B_d)=d,\quad
c(A_d)=(F_{d-1},F_d),\quad c(B_d)=(F_d,F_{d+1}),\quad
b=a+F_d<2a.
\tag{16.7}
$$

对 $h\in\mathbb N_0$ 定义实际像的首个歧义预算

$$
\Lambda_d(h)=\min\{|\operatorname{Leaves}(V)|:V\in\mathcal I_d,\ \operatorname{ht}(V)>h\}.
\tag{16.8}
$$

这里的最小值取实际替换像，而非仅取组成可逆或组成祖先许可；定理 12.1 的固定组成纤维公式仍按其原范围使用。

**定理 16.2（加权实际像高度前沿及同组成见证）。** 对每个 $h\in\mathbb N_0$，有

$$
\boxed{\quad
\Lambda_d(h)=
\begin{cases}
a,&0\le h\le d-2,\\[2pt]
b+a(h-d+1),&h\ge d-1.
\end{cases}\quad}
\tag{16.9}
$$

而且每个边界都有同组成的实际像/非像见证。若 $0\le h\le d-2$，取 $V=A_d$，在地址 $\mathtt L^{\,d-2}$ 的子树 $\langle\beta,\alpha\rangle$ 换成 $\langle\alpha,\beta\rangle$ 得 $W$。若 $h\ge d-1$，置 $m=h-d+1$，定义右梳来源

$$
U_0=\beta,\qquad U_{r+1}=\langle\alpha,U_r\rangle,\qquad
V=\rho^d(U_m).
\tag{16.10}
$$

则 $V$ 在地址 $\mathtt R^{\,m}$ 有 $B_d$ 块，在其余 $m$ 个梳侧有 $A_d$ 块；在地址 $\mathtt R^{\,m}\mathtt L^{\,d-1}$ 的末端樱桃换序得到 $W$。两种情形均满足

$$
V\in\mathcal I_d,\quad W\notin\mathcal I_d,\quad
c(W)=c(V),\quad O_h(W)=O_h(V),\quad
|\operatorname{Leaves}(V)|=\Lambda_d(h).
\tag{16.11}
$$

证明。由（16.7），每个来源叶在 $d$ 次替换后变成 $A_d$ 或 $B_d$ 块，且来源深度为 $e$ 的 $\alpha$ 叶、$\beta$ 叶所产生的最深输出叶深度分别为 $e+d-1$、$e+d$。沿到该来源叶的路径有 $e$ 个非空兄弟子树；每个兄弟子树的实际像至少含 $a$ 片叶。这给出两种路径成本：$\alpha$ 块的总叶数至少为 $a(e+1)$，$\beta$ 块的总叶数至少为 $b+ea$。

若 $h\le d-2$，每个实际像至少有 $a$ 片叶，而 $A_d$ 的高度为 $d-1>h$，所以 $\Lambda_d(h)=a$。$A_d=T_d$ 在地址 $\mathtt L^{\,d-2}$ 的子树正是 $T_2=\langle\beta,\alpha\rangle$；换序只改深度 $d-1>h$ 的两个叶标签，得到所述 $W$。其组成与 $V$ 都是 $(F_{d-1},F_d)$，且 $W$ 的 $\alpha$ 左孩子障碍由定理 16.1 的证明排除其实际像。

以下设 $h\ge d-1$，置 $m=h-d+1\ge0$。若高度超过 $h$ 的最深叶来自 $\beta$ 块，则其来源深度 $e$ 满足 $e+d>h$，即 $e\ge m$，故总叶数至少为 $b+ea\ge b+ma$。若来自 $\alpha$ 块，则 $e+d-1>h$，即 $e\ge m+1$，总叶数至少为 $a(e+1)\ge a(m+2)>b+ma$，最后的不等式使用 $b<2a$。因此所有候选像都满足 $\lvert V\rvert\ge b+ma$。

右梳 $U_m$ 有 $m$ 片 $\alpha$ 侧叶和地址 $\mathtt R^{\,m}$ 的一片 $\beta$ 叶，故 $V=\rho^d(U_m)$ 的叶数为 $b+ma$，其右端 $B_d=T_{d+1}$ 的高度为 $d$，总高度为 $m+d>h$。它的组成明确为

$$
c(V)=S^k\binom m1
=\binom{F_{d-1}m+F_d}{F_dm+F_{d+1}},
\tag{16.12}
$$

其中 $S=M^3$；这只是实际来源的组成读数，未把矩阵逆当作语法逆。$B_d=T_{d+1}$ 在地址 $\mathtt L^{\,d-1}$ 的子树为 $\langle\beta,\alpha\rangle$，故在整体地址 $\mathtt R^{\,m}\mathtt L^{\,d-1}$ 换序得到 $W$。两个叶位于深度 $m+d=h+1$，所以全体深度不超过 $h$ 的路径结果相等；组成也不变。换序后的 $\alpha$ 左孩子又给 $W\notin\mathcal I_d$。于是下界达到，得到（16.9）和（16.11）。证毕。

**定义 16.3（联合观察与单独路径观察的统一深度）。** 对整数 $H\ge1$，令 $\nu_d(H)$ 为使 $\iota_d$ 在 $\mathcal T_H$ 的每个联合纤维 $\mathcal F^{c,O}_{H,h}(V)$ 上单色的最小 $h\in\mathbb N_0$；令 $\nu_d^{O}(H)$ 为删去组成条件、只要求 $\iota_d$ 在

$$
\mathcal F^{O}_{H,h}(V)=\{U\in\mathcal T_H:O_h(U)=O_h(V)\}
\tag{16.13}
$$

的每个纤维上单色的最小 $h$。两者都只针对给定有限预算内的实际完整树；不引入墙钟、物理尺度或窗口外的执行权限。

**定理 16.3（严格整数反演与单独路径窗口的同一前沿）。** 对 $d=3k$、$k\ge1$，有

$$
\boxed{\quad
\nu_d(H)=\nu_d^{O}(H)=
\begin{cases}
0,&1\le H<a,\\[2pt]
d-1+\left\lfloor\dfrac{H-F_d}{a}\right\rfloor,&H\ge a.
\end{cases}\quad}
\tag{16.14}
$$

在 $H=a$ 处等式预算由 $A_d$ 达到；对每个 $q\ge1$，在严格等式预算 $H=F_d+qa$ 处，右梳 $U_{q-1}$ 的像具有恰好 $H$ 片叶并达到高度 $d-1+q$，所以取整边界属于歧义一侧的下一层。组成 $c$ 在全局统一深度上没有降低该前沿，但在受限纤维中仍可切开只由 $O_h$ 合并的不同组成。

证明。若 $H<a$，任何 $d$ 次实际像至少有 $a$ 片叶，故 $\mathcal T_H$ 内目标指标恒为零，$h=0$ 已足够。设 $H\ge a$，置

$$
q=\left\lfloor\dfrac{H-F_d}{a}\right\rfloor.
\tag{16.15}
$$

考察预算不超过 $H$ 的任意实际像，取其最深输出叶所在的来源叶。若为 $\alpha$ 块，路径成本给 $a(e+1)\le H$，从而 $e\le\lfloor H/a\rfloor-1\le\lfloor(H-F_d)/a\rfloor=q$，其中第二个不等式使用 $0<F_d<a$；其输出深度至多 $e+d-1\le d-1+q$。若为 $\beta$ 块，路径成本给 $b+ea\le H$，即 $e\le q-1$，其输出深度至多 $e+d\le d-1+q$。因此所有预算内实际像的高度至多 $d-1+q$。

反向地，若 $q=0$，$A_d$ 在预算 $a\le H$ 内且高度为 $d-1$；若 $q\ge1$，取 $U_{q-1}$，其像叶数

$$
b+a(q-1)=F_d+aq\le H
\tag{16.16}
$$

且高度为 $d+q-1=d-1+q$。由（16.9）还可直接看出严格的整数反演：当 $q=0$ 时 $\Lambda_d(d-2)=a\le H< b=\Lambda_d(d-1)$；当 $q\ge1$ 时 $\Lambda_d(d-2+q)=F_d+aq\le H< F_d+a(q+1)=\Lambda_d(d-1+q)$。定理 16.1 说明：在 $h$ 小于这个最大高度时，存在同组成的正/负交换见证；在 $h$ 等于或大于最大高度时，每个正像由有限路径窗口唯一确定，所有正纤维均单点，故联合观察的最小深度正是（16.14）。

对只给 $O_h$ 的观察，下界仍由定理 16.2 的同组成见证给出。上界不使用组成：当 $h$ 不小于上述最大实际像高度时，任一与正像 $V$ 具有同一 $O_h$ 的树都因有限路径递归比较而等于 $V$；没有正像的观察纤维则全为负类。因此 $\nu_d^{O}(H)$ 与 $\nu_d(H)$ 相同。这个相等不表示 $c$ 在每个受限纤维上无用。例如 $h=0$ 且 $H\ge a$ 时，$A_d$ 与 $\langle\alpha,\alpha\rangle$ 都只显示根为分支，故具有相同 $O_0$；但它们的组成分别为 $(F_{d-1},F_d)$ 与 $(2,0)$，组成观察把这两个候选分开。证毕。

## 追加锚（本行以下为增补区）

## 17. 已知正实例的地址证书基数与尖锐深度障碍

**定义 17.1（选址正证书与查询基数）。** 固定 $d=3k$、$k\ge1$，取实际像中的正实例 $V\in\mathcal I_d$，并把其完整组成

$$
c(V)=(a,b)^{\mathsf T}
$$

作为已知输入。对 $h\in\mathbb N_0$，令 $Q$ 遍历 $\Sigma_{\le h}$ 的有限子集；$Q$ 中每个地址只查询一次，并以定义 16.1 的四值结果

$$
\mathsf{leaf}_\alpha,\qquad \mathsf{leaf}_\beta,\qquad \mathsf{branch},\qquad \mathsf{absent}
$$

与 $V$ 的结果逐项比较。称 $Q$ 对 $(V,h)$ **有声**，若对每一棵合法的完整有序树 $U\in\mathcal T$，都有

$$
c(U)=c(V)\quad\text{且}\quad
\bigl(\forall u\in Q,\ \operatorname{out}_U(u)=\operatorname{out}_V(u)\bigr)
\quad\Longrightarrow\quad U\in\mathcal I_d .
\tag{17.1}
$$

定义

$$
\tau_d(V,h)=
\min\bigl\{|Q|:Q\subseteq\Sigma_{\le h}\text{ 有声}\bigr\},
\qquad \min\varnothing=+\infty .
\tag{17.2}
$$

这里的选择是在 $V$ 与精确的 $c(V)$ 已知后进行；$h$ 只限制地址长度，$|Q|$ 只计不同地址的数目，不另行计地址描述所含的比特或定位成本。树 $U$ 的竞争范围是全部 $\mathcal T$ 中的同组成树，不加预算截断，不要求前缀闭包，也不引入自适应次序、随机化、发现算法或物理取得模型。因此 $\tau_d(V,h)$ 是正实例证书的基数—深度关系；它既不是从未知树中寻找 $Q$ 的复杂度，也不是组成逆像或实际逆执行的许可。

**定理 17.1（实际像正实例的精确证书基数）。** 对每个 $d=3k$、$k\ge1$，每个 $V\in\mathcal I_d$ 及每个 $h\in\mathbb N_0$，若 $c(V)=(a,b)^{\mathsf T}$，则

$$
\boxed{\qquad
\tau_d(V,h)=
\begin{cases}
+\infty,&h<\operatorname{ht}(V),\\[2pt]
a,&h\ge\operatorname{ht}(V).
\end{cases}\qquad}
\tag{17.3}
$$

**证明。** 先作结构桥接。由

$$
\rho^2(\alpha)=\langle\beta,\alpha\rangle,
\qquad
\rho^2(\beta)=\langle\langle\beta,\alpha\rangle,\beta\rangle
$$

可见每个叶块含有一片 $\alpha$，且块内每个内节点都有 $\alpha$ 后代。若来源节点本身是分支，替换后的左右两个非空子树也各含有 $\alpha$ 后代；对来源树作结构归纳，得到 $V$ 的每个内节点都是某个 $\alpha$ 叶地址的严格前缀。这只使用 $d\ge3$ 给出的 $\mathcal I_d\subseteq\rho^2(\mathcal T)$，并沿用[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的树作用单射与实际像边界；完整地址读数的唯一解析仍由[母卷定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)供应。

令 $Q_\alpha(V)$ 为 $V$ 的全部 $\alpha$ 叶地址。其基数是 $a$。若 $h\ge\operatorname{ht}(V)$，这些地址都属于 $\Sigma_{\le h}$。设 $U$ 与 $V$ 具有相同组成并匹配 $Q_\alpha(V)$ 的全部 $\mathsf{leaf}_\alpha$ 结果。对 $V$ 的任一内节点，结构桥接给出一个 $\alpha$ 叶后代；该叶地址的每个真前缀在 $V$ 中都是分支，匹配结果遂迫使这些前缀在 $U$ 中也都是分支。因此 $V$ 的分支地址集包含于 $U$ 的分支地址集。两树都有 $n=a+b$ 片叶，而完整有序二叉树的分支数恒为 $n-1$；这里复用钉版 Mathlib 的 [`BinaryTree.numLeaves_eq_numNodes_succ`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Tree/Basic.lean#L138)，其叶数等于内节点数加一。于是两个分支地址集相等。分支地址集确定相同的叶槽位；已查询的 $a$ 个槽位已经给出 $U$ 的全部 $\alpha$ 叶，组成又规定其余槽位全为 $\beta$，故 $U=V$。于是 $Q_\alpha(V)$ 有声，得到 $\tau_d(V,h)\le a$。

再证有限证书的下界。上述两个 $\rho^2$ 叶块均只有一个末端樱桃 $\langle\beta,\alpha\rangle$，且它们的 $\alpha$ 叶恰为该樱桃的右端；这些块在 $V$ 中彼此不交。因此 $V$ 的 $a$ 片 $\alpha$ 叶给出 $a$ 个两两不交的端点对 $\{r\mathtt L,r\mathtt R\}$，其中 $r$ 是末端樱桃地址。对任一这样的 $r$，在该处把 $\langle\beta,\alpha\rangle$ 换成 $\langle\alpha,\beta\rangle$，得到树 $U_r$。它与 $V$ 的组成相同；所有严格后代地址在两棵树中都给出 $\mathsf{absent}$，而除 $r\mathtt L,r\mathtt R$ 外的地址结果相同。另一方面，$U_r$ 有一片作为左孩子的 $\alpha$ 叶，故不属于 $\rho(\mathcal T)$，从而不属于 $\mathcal I_d$。若有声的 $Q$ 不含这两个端点中的任一个，$U_r$ 就匹配 $Q$ 的全部结果并构成反例；所以 $Q$ 必须命中每个不交端点对，因而 $|Q|\ge a$。

最后处理深度。若 $h<\operatorname{ht}(V)=D$，取深度为 $D$ 的叶。它的兄弟也必须是叶，故其父是末端樱桃；结构桥接及叶块形状把它确定为 $\langle\beta,\alpha\rangle$。对这个樱桃作上述交换得到 $U_r$。两个改变的端点都在深度 $D>h$，所以任何长度不超过 $h$ 的地址在 $V$ 与 $U_r$ 上都有相同的四值结果；组成相同而 $U_r\notin\mathcal I_d$，于是没有有声的 $Q$，即 $\tau_d(V,h)=+\infty$。当 $h\ge D$ 时，前面的 $Q_\alpha(V)$ 已给出大小 $a$ 的有声证书，且下界已经证明任何有声证书至少有 $a$ 个地址。式（17.3）得证。证毕。

端点命中本身并非充分条件。取

$$
V=\rho^3(\alpha)=\langle\langle\beta,\alpha\rangle,\beta\rangle,
\qquad
U=\langle\langle\beta,\beta\rangle,\alpha\rangle .
$$

两者组成都是 $(1,2)$。$V$ 的唯一末端樱桃位于地址 $0$，其左端地址为 $00$；取 $Q=\{00\}$ 虽然命中了这个樱桃，却有 $\operatorname{out}_V(00)=\operatorname{out}_U(00)=\mathsf{leaf}_\beta$。树 $U$ 的根右侧 $\alpha$ 叶的左兄弟是内节点而不是 $\beta$ 叶，故 $U\notin\rho(\mathcal T)$，从而 $Q$ 不有声。相反，$\{01\}$ 在 $h\ge2=\operatorname{ht}(V)$ 时按定理 17.1 给出大小为一的尖锐证书；在 $h<2$ 时则不存在任何证书。

## 追加锚（本行以下为增补区）

## 18. 精确组成最优证书的唯一性与无承诺叶前沿

**定义 18.1（正实例的两类叶地址）。** 沿用定义 16.1、17.1 的自由有序满二叉树、实际替换像与地址查询。固定 $d=3k$、$k\ge1$，以及已知的完整正实例 $V\in\mathcal I_d$，记

$$
\begin{gathered}
c(V)=(a,b)^{\mathsf T},\qquad n=a+b,\qquad D=\operatorname{ht}(V),\\
A(V)=\{u:\operatorname{out}_V(u)=\mathsf{leaf}_\alpha\},\\
L(V)=\{u:\operatorname{out}_V(u)\in
\{\mathsf{leaf}_\alpha,\mathsf{leaf}_\beta\}\}.
\end{gathered}
\tag{18.1}
$$

因而 $|A(V)|=a$、$|L(V)|=n$，且 $A(V)$ 就是定理 17.1 证明中的 $Q_\alpha(V)$。对任意整数 $j\ge1$，仍记 $\mathcal I_j=\rho^j(\mathcal T)$。查询地址集合始终是某个 $\Sigma_{\le h}$ 的有限子集，结果仍为 $\mathsf{leaf}_\alpha$、$\mathsf{leaf}_\beta$、$\mathsf{branch}$、$\mathsf{absent}$ 四值；选择在完整 $V$ 已知后进行，查询基数只数不同地址，深度只限制地址长度，不计地址描述位数与定位成本，也不要求地址集合前缀闭合。

**定理 18.1（精确组成最优证书的唯一性）。** 对定义 18.1 的每个 $V$，每个 $h\ge D$ 与每个有限集合 $Q\subseteq\Sigma_{\le h}$，有

$$
\boxed{\quad
Q\text{ 按定义 17.1 有声且 }|Q|=a
\quad\Longleftrightarrow\quad Q=A(V).
\quad}
\tag{18.2}
$$

因此定理 17.1 的有限最小值 $a$ 只有这一组地址达到；$h<D$ 时的无证书结论仍直接取自定理 17.1。

**证明。** 定理 17.1 已证明 $A(V)$ 有声、其基数为 $a$，并在证明中给出 $a$ 个两两不交的末端樱桃端点对

$$
\{r\mathtt L,r\mathtt R\},\qquad
V|_r=\langle\beta,\alpha\rangle.
\tag{18.3}
$$

这些端点对包含全部 $\alpha$ 叶；任一有声集合都必须命中每一对。于是有声且大小为 $a$ 的 $Q$ 必须在每一对中恰取一个端点，且不能含有这些端点之外的地址。

严格的 $\beta$ 盈余由同一实际来源给出。写 $V=\rho^d(T)=\rho^3(Z)$，其中 $Z=\rho^{d-3}(T)\in\mathcal T$，并记 $c(Z)=(x,y)^{\mathsf T}$。由定义 1.1 的组成作用 $M^3$，

$$
a=x+2y,\qquad b=2x+3y,\qquad
b-a=x+y\ge1.
\tag{18.4}
$$

因此除（18.3）中的 $a$ 片 $\beta$ 左端叶外，还有 $b-a$ 片不属于任何末端樱桃端点对的 $\beta$ 叶；它们都不在 $Q$ 中。式（18.4）也给出 $n=3x+5y\ge3$，所以 $V$ 的根不是叶。

若 $Q\ne A(V)$，取一片未查询的 $\alpha$ 叶地址 $s=r\mathtt R$，并取一片上述未配对的 $\beta$ 叶地址 $t$。只把 $s$ 的标签改成 $\beta$、把 $t$ 的标签改成 $\alpha$，得到合法完整树 $W$。形状和叶地址保持相同，且

$$
c(W)=c(V),\qquad
\operatorname{out}_W(u)=\operatorname{out}_V(u)\quad
(u\notin\{s,t\}).
\tag{18.5}
$$

后一等式覆盖全部有限地址：内节点不变，除两片叶外的叶标签不变，在任何叶处继续行走仍为 $\mathsf{absent}$。故 $W$ 匹配 $Q$ 的全部四值结果。

[运输记忆完成卷命题 22.2 的式（RA.2207）](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#22-一次全局替换的实际节点单孔边界与来源恢复)给出的实际一步像语法要求，每片 $\alpha$ 叶都是扩张块 $\langle\beta,\alpha\rangle$ 的右端。若 $t$ 是左孩子，$W$ 的新 $\alpha$ 叶立即违反该要求。若 $t$ 是右孩子，其左兄弟在 $V$ 中必为内节点：否则 $t$ 所在末端樱桃的右端为 $\beta$，与定理 16.1、17.1 证明中全部末端樱桃均为 $\langle\beta,\alpha\rangle$ 的性质矛盾。改标保持形状，所以该左兄弟在 $W$ 中仍为内节点；新 $\alpha$ 叶也违反一步像语法。因此

$$
W\notin\mathcal I_1,\qquad W\notin\mathcal I_d.
\tag{18.6}
$$

这与 $Q$ 的有声性矛盾，故 $Q=A(V)$。这里直接使用既有像语法；树替换的单射性由[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)供应，完整树编码由[母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)供应。证毕。

**定义 18.2（无组成与叶数承诺的有声性）。** 对定义 18.1 的 $V$、$h\in\mathbb N_0$ 与有限集合 $Q\subseteq\Sigma_{\le h}$，称 $Q$ **无承诺有声**，若

$$
\forall U\in\mathcal T,\qquad
\bigl(\forall u\in Q,\ \operatorname{out}_U(u)=\operatorname{out}_V(u)\bigr)
\quad\Longrightarrow\quad U\in\mathcal I_d.
\tag{18.7}
$$

定义相应最小查询基数

$$
\tau_d^{\mathrm{un}}(V,h)=
\min\{|Q|:Q\subseteq\Sigma_{\le h}\text{ 无承诺有声}\},
\qquad \min\varnothing=+\infty.
\tag{18.8}
$$

$V$ 仍是选址时的已知正实例，成本仍按定义 17.1 计算。竞争树 $U$ 遍历全部 $\mathcal T$，既不要求 $c(U)=c(V)$，也不要求任何叶数上界；$c(V)$ 在此仅用于记下 $V$ 自身的叶数。实际像目标仍取完整树的 $U\in\mathcal I_d$，不取组成祖先许可，且不附加实际逆执行动作。

**定理 18.2（无承诺证书的完整叶条件与唯一最优解）。** 对每个定义 18.1 的 $V$，每个 $h\in\mathbb N_0$ 与每个有限集合 $Q\subseteq\Sigma_{\le h}$，有

$$
\boxed{\quad Q\text{ 无承诺有声}\quad\Longleftrightarrow\quad L(V)\subseteq Q.\quad}
\tag{18.9}
$$

特别地，

$$
\boxed{\qquad
\tau_d^{\mathrm{un}}(V,h)=
\begin{cases}
+\infty,&h<D,\\[2pt]
n,&h\ge D,
\end{cases}
\qquad}
\tag{18.10}
$$

而 $h\ge D$ 时唯一达到最小值的集合是 $Q=L(V)$。

**证明。** 先证每片叶均必须被查询。设 $s\in L(V)\setminus Q$。若 $s\in A(V)$，只将该 $\alpha$ 标签改成 $\beta$ 得 $W$。它把 $s$ 所在的 $\langle\beta,\alpha\rangle$ 末端樱桃改成 $\langle\beta,\beta\rangle$。定理 16.1、17.1 的结构桥接说明，每棵 $\mathcal I_2$ 中的树的全部末端樱桃都为 $\langle\beta,\alpha\rangle$，所以

$$
W\notin\mathcal I_2,\qquad W\notin\mathcal I_d.
\tag{18.11}
$$

此处只需要排除二步像，并不声称改标后一定离开一步像。

若 $s\in L(V)\setminus A(V)$，只将该 $\beta$ 标签改成 $\alpha$。由（18.4），$s$ 不是根。若它是左孩子，新的 $\alpha$ 左孩子违反（RA.2207）；若它是右孩子，原来的左兄弟必为内节点，否则原末端樱桃的右端将是 $\beta$。改标后左兄弟仍为内节点，所以新的 $\alpha$ 右孩子也违反（RA.2207）。因此这一次有

$$
W\notin\mathcal I_1,\qquad W\notin\mathcal I_d.
\tag{18.12}
$$

两种改标都只改变地址 $s$ 的四值结果；形状相同，所有严格后代地址仍为 $\mathsf{absent}$，其余地址的结果相同。因为 $s\notin Q$，$W$ 匹配全部查询而在实际像外，故 $Q$ 不无承诺有声。这证明（18.9）的必要性。

反之，设 $L(V)\subseteq Q$，且 $U\in\mathcal T$ 匹配 $Q$。每片 $V$ 叶在 $U$ 中必须位于同一地址且标签相同。$V$ 的每个内节点都是某片叶地址的真前缀，所以该地址在 $U$ 中也必须是分支。另一方面，$U$ 不能越过任何已强制为叶的 $V$ 叶地址继续产生节点；有限满二叉树中的每条延伸路径都会经过这些叶中的一片。因此两树的全部节点、叶标签及不存在地址的结果相同。直接应用[母卷定理 9.3 的全路径恢复](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，得到 $U=V\in\mathcal I_d$，故 $Q$ 无承诺有声。

无承诺有声必然蕴含定义 17.1 的同组成有声，因而 $h<D$ 的无证书结论也直接由定理 17.1 的高度障碍给出。若 $h\ge D$，$L(V)$ 已在允许地址域中；（18.9）说明每个有声集合都至少含有这 $n$ 个地址，而且 $L(V)$ 本身有声。因此最小基数为 $n$，大小为 $n$ 的有声集合只能等于 $L(V)$，得到（18.10）及唯一性。证毕。

**命题 18.3（平衡二步像与单叶改标的边界）。** 有如下两个实例。

1. 将定义 17.1 的证书合同取为 $d=2$、$V=\rho^2(\alpha)=\langle\beta,\alpha\rangle$、精确组成 $(1,1)^{\mathsf T}$ 时，$h\ge1$ 的最小查询基数为一，且恰有两个最优集合 $\{\mathtt L\}$、$\{\mathtt R\}$；$h=0$ 时不存在有声集合。因此没有严格 $b-a>0$ 时，定理 18.1 的唯一性不能按此方式延伸到全部二步像。
2. 对 $V=\rho^3(\alpha)$，把地址 $\mathtt L\mathtt R$ 的 $\alpha$ 改成 $\beta$ 得到 $W$，满足 $W\in\mathcal I_1\setminus\mathcal I_2$。所以定理 18.2 的 $\alpha\mapsto\beta$ 反例只能按其所用障碍排除二步像，不能据此排除一步像。

**证明。** 第一项中，同组成的完整树只有 $\langle\beta,\alpha\rangle$ 与 $\langle\alpha,\beta\rangle$。后者含有 $\alpha$ 左孩子，故不在 $\mathcal I_1$，从而不在 $\mathcal I_2$。查询左叶的 $\mathsf{leaf}_\beta$ 或右叶的 $\mathsf{leaf}_\alpha$ 均排除后者，因此两个单地址集合都有声。空集合不能区分它们；其余单地址要么是两树共有的根分支，要么在两树中都不存在，也不能区分。因此恰有上述两个一查询最优解；$h=0$ 的全部查询集合也都不能区分。此例的 $b-a=0$。

第二项明确为

$$
\begin{gathered}
V=\langle\langle\beta,\alpha\rangle,\beta\rangle,\qquad
W=\langle\langle\beta,\beta\rangle,\beta\rangle,\\
W=\rho\bigl(\langle\langle\alpha,\alpha\rangle,\alpha\rangle\bigr).
\end{gathered}
\tag{18.13}
$$

后一等式给出 $W\in\mathcal I_1$ 的实际完整来源；其 $\langle\beta,\beta\rangle$ 末端樱桃排除 $W\in\mathcal I_2$。两树的组成分别为 $(1,2)^{\mathsf T}$ 与 $(0,3)^{\mathsf T}$，所以这个单叶改标见证属于定义 18.2 的无承诺竞争域，不是定义 17.1 的同组成竞争见证。证毕。

## 追加锚（本行以下为增补区）

## 19. 纯数量竞争域的尖锐地址证书前沿

**定义 19.1（纯数量有声性与地址成本）。** 沿用定义 16.1、17.1、18.1 的自由有序满二叉树集合 $\mathcal T$、四值原始路径读数、实际像 $\mathcal I_d=\rho^d(\mathcal T)$ 及地址窗口 $\Sigma_{\le h}$。对树 $T$ 写

$$
m(T)=2\,|A(T)|+3\,|B(T)|,
\tag{19.1}
$$

其中 $A(T)$、$B(T)$ 分别是 $\alpha$、$\beta$ 叶地址集。固定 $d=3k$、$k\ge1$，以及已知的正实例 $V\in\mathcal I_d$。令

$$
A=A(V),\qquad B=B(V),\qquad a=|A|,\qquad b=|B|,
\qquad D=\operatorname{ht}(V).
\tag{19.2}
$$

对有限的 $Q\subseteq\Sigma_{\le h}$，称 $Q$ 对 $(V,h)$ **纯数量有声**，若

$$
\forall U\in\mathcal T,\qquad
\left(m(U)=m(V)\ \land\ \forall u\in Q,
\operatorname{out}_U(u)=\operatorname{out}_V(u)\right)
\Longrightarrow U\in\mathcal I_d.
\tag{19.3}
$$

竞争者遍历全部非空有限自由有序满二叉树，只保留精确数量 $m(U)=m(V)$；不附加组成相等、实际像承诺、叶数预算、前缀闭包或高度上界。查询基数 $|Q|$ 只计不同地址，深度成本只由 $h$ 限制地址长度，不计地址文字长度、定位成本、自适应次序或实际逆执行。定义

$$
\tau_d^{\,m}(V,h)=
\min\{|Q|:Q\subseteq\Sigma_{\le h}\text{ 纯数量有声}\},
\qquad \min\varnothing=+\infty.
\tag{19.4}
$$

**定理 19.1（纯数量的尖锐证书前沿与全部极小解）。** 对每个定义 19.1 的 $V$，有 $a\ge1$，并且

$$
\boxed{
\tau_d^{\,m}(V,h)=+\infty\qquad(h<D).
}
\tag{19.5}
$$

当 $h\ge D$ 时，若 $a\ge2$，则

$$
\boxed{
\tau_d^{\,m}(V,h)=b,
\qquad\text{唯一达到极小值的集合为 }Q=B.
}
\tag{19.6}
$$

若 $a=1$，则必有

$$
 d=3,\qquad
 V=\rho^3(\alpha)=\langle\langle\beta,\alpha\rangle,\beta\rangle,
 \qquad b=2,
\tag{19.7}
$$

并且

$$
\boxed{
\tau_d^{\,m}(V,h)=2,
}
\tag{19.8}
$$

恰有三组极小查询，即该树三片叶地址的三组二元子集

$$
\{\mathtt{LL},\mathtt{LR}\},
\qquad
\{\mathtt{LL},\mathtt R\},
\qquad
\{\mathtt{LR},\mathtt R\}.
\tag{19.9}
$$

**证明。** 先记下三个结构事实。每个非空树的数量至少为 $2$，且数量为 $2$ 的非空树恰为单叶 $\alpha$；这是叶权重为 $2,3$ 与满二叉结构的直接归纳。其次，$d\ge3$ 时每个实际像树的每个分支都有一个 $\beta$ 叶后代：两个基本块 $\rho^d(\alpha)$、$\rho^d(\beta)$ 都含有 $\beta$ 叶，分支递归保持这一性质。最后，$\mathcal I_d\subseteq\mathcal I_2$，故 $V$ 的每个末端樱桃均为 $\langle\beta,\alpha\rangle$，沿用定理 16.1、17.1 的结构桥接与 [RA.2207](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#22-一次全局替换的实际节点单孔边界与来源恢复) 的一步像语法。地址读数的唯一解析与全路径恢复沿用[母卷定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)；这里只使用其既有读数接口，不重复解析或恢复证明。

若 $h<D$，取 $V$ 的深度为 $D$ 的叶及其末端樱桃，交换该樱桃的两个叶标签得到 $W$。定理 17.1 已给出

$$
O_h(W)=O_h(V),\qquad c(W)=c(V),
\qquad W\notin\mathcal I_d.
\tag{19.10}
$$

组成相同遂数量相同，故任意 $Q\subseteq\Sigma_{\le h}$ 都被同一个 $W$ 反例击中，得到（19.5）。

以下设 $h\ge D$。先证明全 $\beta$ 查询的充分性。令 $Q=B$，设 $U$ 匹配所有查询且 $m(U)=m(V)$。$V$ 的每个分支都是某个 $\beta$ 叶地址的严格前缀；因该叶在 $U$ 中仍是 $\mathsf{leaf}_\beta$，这些前缀在 $U$ 中全是分支。于是 $U$ 的骨架只能由在 $V$ 的每个 $\alpha$ 叶槽位处替换非空子树得到：记这些子树为 $S_x$（$x\in A$），则

$$
 m(U)=3b+\sum_{x\in A}m(S_x),
 \qquad m(S_x)\ge2.
\tag{19.11}
$$

而 $m(V)=3b+2a$。数量相等迫使每个 $m(S_x)=2$，从而每个 $S_x=\alpha$，故 $U=V\in\mathcal I_d$。因此 $B$ 有声，且 $\tau_d^{\,m}(V,h)\le b$。

现在给出任意有声集合的二分支约束。若 $Q$ 同时遗漏 $x\in A$ 与 $y\in B$，就在保持括号形状的条件下把 $x$ 的标签 $\alpha$ 改为 $\beta$，把 $y$ 的标签 $\beta$ 改为 $\alpha$，得到 $W$。交换只改变两个叶端点的结果，故

$$
 m(W)=m(V),
\qquad
\operatorname{out}_W(u)=\operatorname{out}_V(u)
\quad\bigl(u\notin\{x,y\}\bigr).
\tag{19.12}
$$

其中严格后代在两树中都为 $\mathsf{absent}$，并且

$$
\{u:\operatorname{out}_W(u)\ne\operatorname{out}_V(u)\}=\{x,y\}.
$$

同时 $W\notin\mathcal I_1$：若新 $\alpha$ 叶在左孩子位置，直接违反一步像语法；若它在右孩子位置，则其左兄弟不能是 $\beta$ 叶，因为 $V$ 的末端樱桃全为 $\langle\beta,\alpha\rangle$，故左兄弟为内节点，而 [RA.2207](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#22-一次全局替换的实际节点单孔边界与来源恢复) 要求像中的 $\alpha$ 右孩子左邻为 $\beta$。所以 $W\notin\mathcal I_d$。这与有声性矛盾，遂有

$$
Q\supseteq A\quad\text{或}\quad Q\supseteq B.
\tag{19.13}
$$

还需处理全 $\alpha$ 分支。设 $Q\supseteq A$，并令 $R=B\setminus Q$ 为遗漏的 $\beta$ 叶地址。若 $x,y\in R$ 为两个不同地址，且 $Q$ 不含 $y\mathtt L$、$y\mathtt R$，就在 $y$ 处把单叶 $\beta$ 换成 $\langle\alpha,\alpha\rangle$，在 $x$ 处把 $\beta$ 改成 $\alpha$，得到 $W$。组成变化为

$$
\Delta(a,b)=(3,-2),
\qquad
\Delta m=2\cdot3+3\cdot(-2)=0,
\tag{19.14}
$$

故 $m(W)=m(V)$。唯一改变的地址响应恰为

$$
\{x,y,y\mathtt L,y\mathtt R\};
\tag{19.15}
$$

在 $y$ 的更深后代处，两树均先到达叶而为 $\mathsf{absent}$，在 $x$ 的更深后代也同样如此。新树含有以 $\alpha$ 为左孩子的节点，因而 $W\notin\mathcal I_1$。这与 $Q$ 有声矛盾。因此，只要 $|R|\ge2$，每个遗漏的 $\beta$ 地址 $y$ 都必须在 $Q$ 中带有至少一个立即孩子 $y\mathtt L$ 或 $y\mathtt R$；不同遗漏地址的立即孩子互不相同，从而

$$
|Q|\ge a+(b-|R|)+|R|=a+b.
\tag{19.16}
$$

这一步也说明了为什么只查分支或更深的缺失地址不能替代该立即孩子判别器。

若 $|R|=0$，则 $Q$ 至少含有 $A\cup B$，故 $|Q|\ge a+b$；若 $|R|=1$，则 $|Q|\ge a+b-1$。结合（19.13），当 $a\ge2$ 时，全 $\alpha$ 分支的下界始终严格大于 $b$，而全 $\beta$ 分支的下界为 $b$，且等号只可能是 $Q=B$。连同（19.11），得到（19.6）。

若 $a=1$，写来源组成 $c(T)=(x,y)^{\mathsf T}$，其中 $V=\rho^{3k}(T)$。由[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的组成作用，

$$
(a,b)^{\mathsf T}=S^k(x,y)^{\mathsf T},
\qquad
S=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix}.
\tag{19.17}
$$

若 $k\ge2$，则 $S^k$ 的第一行每个系数至少为 $5$，与 $a=1$ 矛盾；故 $k=1$。此时 $x+2y=1$，所以 $(x,y)=(1,0)$，来源树只能是单叶 $\alpha$。这给出（19.7），其叶地址为

$$
\mathtt{LL}\mapsto\beta,\qquad
\mathtt{LR}\mapsto\alpha,\qquad
\mathtt R\mapsto\beta.
\tag{19.18}
$$

全 $\beta$ 集合 $\{\mathtt{LL},\mathtt R\}$ 由（19.11）有声。两个混合二元集合也有声：$\{\mathtt{LL},\mathtt{LR}\}$ 固定左子树，剩余右槽位的数量必须为 $3$；$\{\mathtt{LR},\mathtt R\}$ 固定右叶及左子树的右叶，剩余左槽位的数量必须为 $3$。非空树数量为 $3$ 恰唯一实现为单叶 $\beta$，故两者都迫使 $U=V$。

最后，任意有声集合都满足（19.13）。若它含有全部两个 $\beta$ 地址，则在基数为 $2$ 时恰为 $\{\mathtt{LL},\mathtt R\}$；否则它必须含有唯一的 $\alpha$ 地址。若还遗漏两个 $\beta$ 地址，则（19.16）的立即孩子要求使基数至少为 $3$；故基数为 $2$ 时第二个地址必是一个 $\beta$ 叶，恰得到另外两组（19.9）。所以三组且仅三组达到（19.8）。在这个特例中，旧的单独 $\alpha$ 证书确实失败：令

$$
U_8=\langle\langle\alpha,\alpha\rangle,
             \langle\alpha,\alpha\rangle\rangle.
\tag{19.19}
$$

则 $m(U_8)=8=m(V)$，$\operatorname{out}_{U_8}(\mathtt{LR})=\mathsf{leaf}_\alpha$ 与 $V$ 相同，但 $U_8\notin\mathcal I_1$，且相对 $V$ 的精确改变支持为

$$
\{\mathtt{LL},\mathtt R,\mathtt{RL},\mathtt{RR}\}.
\tag{19.20}
$$

这完成了全部情形。证毕。

## 追加锚（本行以下为增补区）

## 20. 已给阶段标量的尖锐地址证书与全部最优解

**定义 20.1（同源阶段标量与原始地址证书）。** 沿用定义 16.1 的非空有限自由有序满二叉树集合 $\mathcal T$、替换 $\rho$、实际像 $\mathcal I_d=\rho^d(\mathcal T)$、四值原始地址响应 $\operatorname{out}$ 与窗口 $\Sigma_{\le h}$。树替换的组成作用直接取自[规范编译卷命题 4.2](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)，树作用的单射性与实际像边界取自同卷命题 4.3；完整树编码及全路径读数接口取自[母卷定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)。固定 $d=3k$、$k\ge1$，以及完整已知的正实例 $V\in\mathcal I_d$，记

$$
c(V)=(a,b)^{\mathsf T},\qquad
A=A(V),\qquad B=B(V),\qquad
|A|=a,\quad |B|=b,\quad D=\operatorname{ht}(V).
$$

$A,B$ 始终是原始 $V$ 的字面 $\alpha,\beta$ 叶地址。另给已知整数 $L\ge0$，并按定义 1.1 的式（1.2）给出精确标量

$$
f=F_{3L+3},\qquad g=F_{3L+4},\qquad
N=n_L(c(V))=fa+gb.
\tag{20.1}
$$

$N$ 与地址响应共同来源于同一棵 $V$，作为已给输入；其取得不计入查询成本，也不属于本合同授予的操作。替换像的迭代数 $d$、标量阶段 $L$ 与独立地址深度上限 $h\in\mathbb N_0$ 分别固定，地址查询不转移到 $\rho^{3L}(V)$ 上。

对任意有限集合 $Q\subseteq\Sigma_{\le h}$，称 $Q$ **阶段标量有声**，当且仅当

$$
\forall U\in\mathcal T,\qquad
\left(
n_L(c(U))=N
\ \land\
\forall u\in Q,\
\operatorname{out}_U(u)=\operatorname{out}_V(u)
\right)
\Longrightarrow U\in\mathcal I_d.
\tag{20.2}
$$

竞争树 $U$ 遍历全部合法非空有限自由有序满二叉树，不附加组成相等、实际像、括号形状、叶数或高度承诺。$Q$ 可以含空地址、原始分支地址及原始缺失地址，不要求前缀闭包。成本只计原始 $V$ 上不同地址的数目 $|Q|$，不计地址描述与定位成本；选址在完整 $V$ 已知后进行。定义

$$
\tau_{d,L}(V,h)
=\min\{|Q|:Q\subseteq\Sigma_{\le h}
\text{ 阶段标量有声}\},
\qquad \min\varnothing=+\infty.
\tag{20.3}
$$

这里的结论只取完整树的实际像成员关系，不取组成祖先许可或逆执行动作。

**定理 20.1（任意已知阶段的精确极小值与全部达到集合）。** 对定义 20.1 的每个 $d,L,V,h$，有 $b>a\ge1$。当 $h<D$ 时不存在阶段标量有声集合。当 $h\ge D$ 时，置

$$
t=\max(0,b-f+1),\qquad M=\min(b,a+t).
$$

则

$$
\boxed{
\tau_{d,L}(V,h)=
\begin{cases}
+\infty,&h<D,\\[2pt]
\min\bigl(b,a+\max(0,b-f+1)\bigr),&h\ge D.
\end{cases}
}
\tag{20.4}
$$

在 $h\ge D$ 时，全部达到极小值的查询集合恰为

$$
\boxed{
\{B\mid b=M\}
\ \cup\
\{A\cup C\mid C\subseteq B,\ |C|=t,\ a+t=M\}.
}
\tag{20.5}
$$

第一项在 $b\ne M$ 时为空，第二项在 $a+t\ne M$ 时为空。没有任何最优集合含原始根、分支或缺失地址。利用 $b>a\ge1$，全部阶段区间等价地写为：

- 若 $f\le a$，极小值为 $b$，唯一最优集合为 $B$。
- 若 $f=a+1$，极小值为 $b$；$B$ 及每个 $A\cup C$、$C\subseteq B$、$|C|=b-a$ 同时最优。
- 若 $a+1<f\le b$，极小值为 $a+b-f+1$；最优集合恰为所有 $A\cup C$、$C\subseteq B$、$|C|=b-f+1$。
- 若 $f>b$，极小值为 $a$，唯一最优集合为 $A$。

对固定 $V$ 与 $h\ge D$，极小值随整数 $L$ 增大不增，且最终为 $a$。这一价格关系不使全域 $\mathcal T$ 上单个阶段标量的观察纤维形成嵌套细化链。

**证明。** 式（18.4）直接给出 $b>a\ge1$。以下复用定理 17.1 的精确组成 $A$ 刚性与高度障碍、定理 19.1 证明中的 $\beta$ 骨架及端点换标，并用[运输记忆完成卷命题 22.2 的式（RA.2207）](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#22-一次全局替换的实际节点单孔边界与来源恢复)判定实际一步像。

当 $L=0$ 时，$(f,g)=(2,3)$，定义 20.1 就是定义 19.1 的竞争合同，全部结论直接取自定理 19.1：若 $a\ge2$，则 $a+t=a+b-1>b$，唯一最优集合是 $B$；若 $a=1$，该定理已给出 $V=\rho^3(\alpha)$、$b=2$，于是 $t=1$，最优集合为 $B$ 和两组 $A$ 加一个 $\beta$ 端点，恰为式（19.9）的三组。低于 $D$ 的无证书结论也由该定理直接供应。以下证明其余已知阶段 $L\ge1$。

由定义 1.1 的 Fibonacci 递推，有

$$
\begin{gathered}
p=g-f=F_{3L+2}>0,\qquad
q=2f-g=F_{3L+1}>0,\\
p+q=f,\qquad 2p+q=g,\qquad f<g<2f.
\end{gathered}
\tag{20.6}
$$

相同标量的组成关系直接由定理 1.4 的式（1.12）供应：若 $n_L(c(U))=N$，则存在 $z\in\mathbb Z$ 使

$$
c(U)=(a+zg,b-zf)^{\mathsf T}.
\tag{20.7}
$$

若 $h<D$，定理 17.1 的高度障碍已经给出合法树 $W\notin\mathcal I_d$，满足 $c(W)=c(V)$ 且 $O_h(W)=O_h(V)$。组成相同也使 $n_L(c(W))=N$，所以任何 $Q\subseteq\Sigma_{\le h}$ 都不能有声。这证明式（20.4）的无穷分支；以下设 $h\ge D$。

先证两个候选上界。定理 19.1 证明式（19.11）所用的 $\beta$ 骨架说明：匹配 $B$ 的树 $U$ 保留 $V$ 的全部分支与 $\beta$ 叶槽位，剩余变化只能是在各原始 $\alpha$ 叶槽位 $x\in A$ 填入非空树 $S_x$。将其中的数量权重换成定义 20.1 的 $f,g$，得到

$$
n_L(c(U))
=gb+\sum_{x\in A}n_L(c(S_x))
\ge gb+fa=N.
\tag{20.8}
$$

每个非空树 $S$ 的标量至少为 $f$，且等号只在 $S=\alpha$ 时成立：单叶 $\beta$ 的权重为 $g>f$，任何分支树至少有两片叶，权重至少为 $2f>f$。因此相同标量迫使所有 $S_x=\alpha$，从而 $U=V$。这证明 $B$ 有声，成本为 $b$，只在既有骨架内使用新权重。

再取任意 $C\subseteq B$、$|C|=t$，并令 $Q=A\cup C$。匹配这些字面端点的树 $U$ 至少有 $a$ 片 $\alpha$ 叶和 $t$ 片 $\beta$ 叶。代入式（20.7），由于 $g>0$，得到

$$
z\ge0,\qquad zf\le b-t=\min(b,f-1)<f.
\tag{20.9}
$$

整数 $z$ 只能为零，所以 $c(U)=c(V)$。现在直接应用定理 17.1 证明中全 $A$ 的精确组成刚性，得到 $U=V$。因此每个这样的 $A\cup C$ 有声，成本为 $a+t$。两种候选只使用原始叶地址，已在 $h=D$ 时全部可用，遂有 $\tau_{d,L}(V,h)\le M$。

下界针对任意原始地址集合，不预设查询叶。复用定理 19.1 证明式（19.12）–（19.13）的形状保持端点换标：若 $Q$ 同时遗漏 $x\in A$ 与 $y\in B$，交换它们的标签所得到的树保持整个组成，精确响应改变支持恰为 $\{x,y\}$，并由该证明的（RA.2207）像语法论证排除在 $\mathcal I_1$ 之外。组成保持使每个 $n_L$ 保持，故它仍是式（20.2）的反例。于是任何有声 $Q$ 必满足

$$
A\subseteq Q\qquad\text{或}\qquad B\subseteq Q.
\tag{20.10}
$$

严格后代在这一换标中仍为缺失，因而任意分支与缺失查询都不改变该二分约束。

全 $B$ 分支立即给出 $|Q|\ge b$，等号只在 $Q=B$ 时成立。考虑全 $A$ 分支，令

$$
R=B\setminus Q,\qquad r=|R|,\qquad
e=|Q\setminus(A\cup B)|,
\qquad |Q|=a+b-r+e.
$$

仅当 $y\mathtt L$ 或 $y\mathtt R$ 至少有一个属于 $Q$ 时，才称遗漏的 $\beta$ 槽位 $y\in R$ 被阻挡。这个条件只看字面立即孩子，不把更深的缺失查询或其前缀视为已查询。

设 $r\ge f$，且至少存在 $p$ 个未被阻挡的槽位。选这些槽位中的 $p$ 个组成 $Y$；再从 $R\setminus Y$ 选 $q$ 个组成 $X$。后一步可行，因为 $r-p\ge f-p=q$。在每个 $y\in Y$ 处把原始 $\beta$ 叶替换成 $\langle\alpha,\alpha\rangle$，在每个 $x\in X$ 处把原始 $\beta$ 叶改成 $\alpha$，得到 $W$。所有操作位置都是原始叶，彼此不可比，所以这些同时替换产生一棵合法非空有限有序满二叉树。组成变化及标量变化为

$$
c(W)-c(V)
=(2p+q,-p-q)^{\mathsf T}
=(g,-f)^{\mathsf T},\qquad
n_L(c(W))-N=fg-gf=0.
\tag{20.11}
$$

这里构造了实际树，而不只是在组成格上取一个核向量。每个嫁接都产生一个 $\alpha$ 左孩子，且 $p>0$ 保证至少有一次嫁接；由（RA.2207），$W\notin\mathcal I_1$，从而 $W\notin\mathcal I_d$。

这棵树在全部有限原始地址上的精确改变支持为

$$
\{u:\operatorname{out}_W(u)\ne\operatorname{out}_V(u)\}
=
X\cup Y\cup
\{y\mathtt L,y\mathtt R:y\in Y\}.
\tag{20.12}
$$

在 $X$ 中只改变端点标签；在 $Y$ 中端点由 $\beta$ 叶变为分支，其两个立即孩子由缺失变为 $\alpha$ 叶。嫁接槽位下相对深度至少为二的所有地址，在两棵树中都为缺失；改标槽位的严格后代也仍为缺失。原始分支、其他叶及其余全部地址都未变。由于 $X\cup Y\subseteq R$，这些端点不在 $Q$ 中；$Y$ 未被阻挡，所以其立即孩子也不在 $Q$ 中。因此 $W$ 匹配全部查询，违反有声性。

故当 $r\ge f$ 时，有声性迫使未被阻挡的遗漏槽位至多有 $p-1$ 个，至少有 $r-p+1$ 个被阻挡。每个被阻挡槽位至少消耗一个属于 $Q$ 的立即孩子地址。这些地址在原始 $V$ 中都为缺失，位于 $A\cup B$ 之外；不同原始叶的孩子互不相同。因此 $e\ge r-p+1$，并有

$$
|Q|
\ge a+(b-r)+(r-p+1)
=a+b-p+1
=a+b-f+1+q
=a+t+q
>a+t\ge M.
\tag{20.13}
$$

其中 $r\ge f$ 保证 $b\ge f$，所以 $t=b-f+1$。这只给出该区域内有声集合的必要成本下界；严格的 $q>0$ 已足以排除它们达到极小值。

余下 $r<f$ 时，$r\le\min(b,f-1)$，因而

$$
|Q|=a+b-r+e
\ge a+b-\min(b,f-1)
=a+t.
\tag{20.14}
$$

等号当且仅当 $r=\min(b,f-1)$ 且 $e=0$。这等价于 $Q=A\cup C$，其中 $C\subseteq B$、$|C|=t$。在 $b<f$ 时等号给出 $r=b$、$Q=A$；在 $b\ge f$ 时等号给出 $r=f-1$，恰查询 $b-f+1$ 个 $\beta$ 端点。这保留了 $b=f-1$ 时 $t=0$ 与 $b=f$ 时 $t=1$ 的边界。与全 $B$ 分支的等号条件比较，两项上界及全部下界证明了式（20.4）–（20.5）。特别地，达到值 $M$ 时全 $A$ 分支必须满足 $a+t=M$，全 $B$ 分支必须满足 $b=M$；任何额外原始根、分支或缺失查询都会破坏相应等号。

上述支持计算也覆盖深度边界。当 $h=D$ 时，遗漏的深度 $D$ 叶的立即孩子不在查询窗口内，所以该槽位自动未被阻挡。嫁接树可有深度 $D+1$，但竞争树本来没有高度承诺。对于任意更大的 $h$，能阻挡该嫁接的仍只有其两个立即孩子；无论允许的缺失地址有多深，在嫁接下相对深度至少为二的结果仍与原始树相同。因而本证明适用于 $h=D$ 及全部 $h>D$，也不使用前缀闭包。

由 $b>a$，在 $b\ge f$ 的区域比较 $a+t-b=a-f+1$，得到 $f\le a$、$f=a+1$ 及 $a+1<f\le b$ 的三个区间；在 $b<f$ 的区域有 $t=0$，唯一最优集合为 $A$。于是四个区间穷尽全部阈值与并列。固定 $V$ 时，$F_{3L+3}$ 随整数 $L$ 严格增大且无界，$t$ 因而不增，$M$ 也不增，最终 $f>b$、$M=a$。阶段序列可以跳过某个阈值，这不改变逐阶段结论。

全域上的单阶段标量纤维并不因此嵌套。由规范编译卷命题 4.2 的组成实现，$(3,0)$ 与 $(0,2)$ 都有合法满二叉树实现；它们在 $L=0$ 的标量均为 $6$，在 $L=1$ 的标量分别为 $24,26$。反向地，$(13,0)$ 与 $(0,8)$ 也都有合法实现，在 $L=1$ 的标量均为 $104$，在 $L=0$ 的标量分别为 $26,24$。所以 $L=0,1$ 的两种标量观察核互不包含。已知正实例的极小价格不增，是上述证书公式的结论。

例如，取

$$
T=\langle\langle\alpha,\alpha\rangle,
         \langle\alpha,\alpha\rangle\rangle,
\qquad V=\rho^3(T).
$$

由既有组成作用及 $\rho^3(\alpha)$ 的树形，得到 $(a,b)=(4,8)$、$D=4$。在同一个原始 $V$ 上，对任意 $h\ge4$，$L=0,1,2$ 的极小值分别为 $8,5,4$。$L=1$ 时 $(f,g)=(8,13)$、$N=136$，所有 $A$ 加一个 $\beta$ 端点的集合都最优。单独 $A$ 则不有声：在五个 $\beta$ 槽位嫁接 $\langle\alpha,\alpha\rangle$，把其余三个 $\beta$ 槽位改成 $\alpha$，得到组成 $(17,0)$ 的实际合法树，其标量仍为 $136$，匹配全部 $A$，却因 $\alpha$ 左孩子而不属于 $\mathcal I_1$。这正是式（20.11）–（20.12）在该实例中的嫁接与改标。证毕。

## 追加锚（本行以下为增补区）

## 21. 固定标量纤维的未知来源发现与正实例费用耦合

**定义 21.1（未知完整树的固定纤维与发现费用）。** 沿用[定义 16.1](#16-实际树像与尖锐有限路径观察前沿)的非空有限自由有序满二叉树集合 $\mathcal T$、替换 $\rho$、四值原始地址响应 $\operatorname{out}$ 与窗口 $\Sigma_{\le h}$，固定实际像迭代数 $d=3$。树形和叶标记不取任何结合或交换商；组成 $c(U)=(a(U),b(U))^{\mathsf T}$ 只计两类叶。完整来源编码与全部路径恢复的接口取自[母卷定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)。给定已知整数 $L\ge0$，按[定义 1.1 的式（1.2）](#1-有限预算的尺度读出与逆许可分离)置

$$
\begin{gathered}
f_L=F_{3L+3},\qquad g_L=F_{3L+4},\qquad f=f_L,\quad g=g_L,\\
m=3f+5g,\qquad
X_L=\{U\in\mathcal T:n_L(c(U))=m\},\\
P=\rho^3(\langle\alpha,\beta\rangle),\qquad
Q=\rho^3(\langle\beta,\alpha\rangle),\qquad
\iota_3(U)=\mathbf1_{\{U\in\rho^3(\mathcal T)\}}.
\end{gathered}
\tag{21.1}
$$

实际输入是未知的 $U\in X_L$；精确标量 $m$ 与所有地址响应来自这同一棵原始 $U$。候选全集恰为 $X_L$ 中的全部合法树，不另给实际像、组成、形状、叶数或高度承诺。标量的取得及控制器计算在下述收费和授权的观察操作之外；观察只是在原始 $U$ 上选取 $u\in\Sigma_{\le h}$ 并返回 $\operatorname{out}_U(u)$，不改变 $U$，不转移到 $\rho^{3L}(U)$，也不解锁动作。$h\in\mathbb N_0$ 独立固定，不要求所选地址前缀闭合。任务的终端值只取 $\iota_3(U)$；组成祖先许可与实际逆执行各是另一个目标。

确定性策略在每个有限地址—响应记录后，依据已知 $L,m,h$ 与该记录选择下一个合法地址，或输出 $0,1$ 并停止。策略不能读取该记录以外的 $U$ 信息。允许缓存重复地址的响应；若在 $U$ 上有限停止，记其所查询的不同地址集合为 $J_\pi(U)$，费用为

$$
C_\pi(U)=|J_\pi(U)|.
\tag{21.2}
$$

费用不计地址文字长度、定位、标量取得或控制器计算。令 $\Pi_{L,h}$ 为在每棵 $U\in X_L$ 上均有限停止且输出 $\iota_3(U)$ 的确定性策略族，并定义全输入最坏费用

$$
D_{L,h}=\inf_{\pi\in\Pi_{L,h}}\ \sup_{U\in X_L}C_\pi(U),
\qquad \inf\varnothing=+\infty.
\tag{21.3}
$$

有限候选集与纯观察决策的解释沿用[延拓卷定义 11.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#11-自适应分辨率何时可以停止递归)：停止叶须在全部仍相容的候选上给出同一个任务值。此处证书检查属于控制器计算，所声明的费用只为不同地址数。

**定理 21.1（固定纤维的两个实际正例与确定性发现代价）。** 对定义 21.1 的每个 $L$，整个 $X_L$ 有限，其组成集合恰为

$$
c(X_L)=
\begin{cases}
\{(0,7),(3,5),(6,3),(9,1)\},&L=0,\\[2pt]
\{(3,5)\},&L\ge1,
\end{cases}
\qquad
X_L\cap\rho^3(\mathcal T)=\{P,Q\},\quad P\ne Q.
\tag{21.4}
$$

每组组成的全部自由有序满二叉树实现都保留在 $X_L$ 中。置

$$
k_L=
\begin{cases}
5,&L=0,\\
3,&L\ge1.
\end{cases}
\tag{21.5}
$$

若 $h<4$，则 $\Pi_{L,h}=\varnothing$。若 $h\ge4$，每个 $\pi\in\Pi_{L,h}$ 都满足

$$
C_\pi(P)\ge k_L,\qquad C_\pi(Q)\ge k_L,\qquad
C_\pi(P)+C_\pi(Q)\ge2k_L+1,
\tag{21.6}
$$

并有精确的全输入最优值

$$
\boxed{
D_{L,h}=
\begin{cases}
+\infty,&h<4,\\
6,&h\ge4,\ L=0,\\
4,&h\ge4,\ L\ge1.
\end{cases}}
\tag{21.7}
$$

对于 $h\ge4$，有两种在整个 $X_L$ 上正确的策略 $\pi_P,\pi_Q$，仅查询深度至多 $4$ 的地址，不重复地址，全部输入的费用均至多 $k_L+1$，而正例费用分别为

$$
\bigl(C_{\pi_P}(P),C_{\pi_P}(Q)\bigr)=(k_L,k_L+1),\qquad
\bigl(C_{\pi_Q}(P),C_{\pi_Q}(Q)\bigr)=(k_L+1,k_L).
\tag{21.8}
$$

**证明。** 先确定完整竞争域。由[定理 1.4 的整数核式（1.12）](#1-有限预算的尺度读出与逆许可分离)，与组成 $(3,5)$ 具有相同 $n_L$ 的整数点全部形如

$$
(a(U),b(U))=(3+zg,5-zf),\qquad z\in\mathbb Z.
\tag{21.9}
$$

当 $L=0$ 时，$f=2,g=3$；两个坐标非负恰给 $-1\le z\le2$，四个整数值分别产生（21.4）中的四组组成。当 $L\ge1$ 时，$f\ge8,g\ge13$；$z\ge1$ 会使第二坐标为负，$z\le-1$ 会使第一坐标为负，故仅有 $z=0$。[规范编译卷命题 4.2](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)供应每个非零非负组成的树实现；标量只依组成，所以对应组成的全部形状及叶序都属于 $X_L$。上述四组的总叶数依次为 $7,8,9,10$，而 $L\ge1$ 时总叶数为 $8$。满二叉树的分支数为叶数减一，沿用定理 17.1 证明中的既有计数恒等式；母卷定理 9.2 的单射结构码对 $n$ 片叶的长度为 $2n+(n-1)=3n-1$。因此 $X_L$ 的结构码长度至多为 $29$，来自有限二字母词集，整个 $X_L$ 有限。这是由给定标量导出的结论，不是输入的叶数承诺。

现在只在条件 $U\in\rho^3(\mathcal T)$ 下取一个实际前像 $T\in\mathcal T$，$U=\rho^3(T)$。由规范编译卷命题 4.2 的组成作用，

$$
\begin{gathered}
c(U)=S\,c(T),\qquad S=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\\
(f_{L+1},g_{L+1})=(f,g)S=(f+2g,2f+3g),\\
n_{L+1}(c(T))=n_L(c(U))=3f+5g=f_{L+1}+g_{L+1}.
\end{gathered}
\tag{21.10}
$$

把定理 1.4 的式（1.12）应用于阶段 $L+1$，相同读数的前像组成必为

$$
c(T)=(1+z g_{L+1},1-z f_{L+1})^{\mathsf T},\qquad z\in\mathbb Z.
\tag{21.11}
$$

由于 $f_{L+1}\ge8,g_{L+1}\ge13$，非负性迫使 $z=0$。所以 $T$ 有且仅有两片叶，一片 $\alpha$、一片 $\beta$；自由有序满二叉语法只允许 $\langle\alpha,\beta\rangle$ 和 $\langle\beta,\alpha\rangle$。两者的三步像正是 $P,Q$，组成均为 $S(1,1)^{\mathsf T}=(3,5)^{\mathsf T}$，因而都在 $X_L$ 中。[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的树作用单射性及其迭代直接给出 $P\ne Q$。这证明实际正例分类；式（21.11）只约束已经假设存在的实际前像，不从组成逆运算授予任意树前像。

为使用既有证书供应，写 $A_P=A(P),B_P=B(P),A_Q=A(Q),B_Q=B(Q)$。由替换的字面树形，

$$
\begin{gathered}
A_3=\rho^3(\alpha)=\langle\langle\beta,\alpha\rangle,\beta\rangle,\\
B_3=\rho^3(\beta)=
\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,
       \langle\beta,\alpha\rangle\rangle,\\
P=\langle A_3,B_3\rangle,\qquad Q=\langle B_3,A_3\rangle.
\end{gathered}
\tag{21.12}
$$

它们的所有原始叶地址及标签为

$$
\begin{aligned}
A_P&=\{\mathtt{LLR},\mathtt{RLLR},\mathtt{RRR}\},\\
B_P&=\{\mathtt{LLL},\mathtt{LR},\mathtt{RLLL},\mathtt{RLR},\mathtt{RRL}\},\\
A_Q&=\{\mathtt{LLLR},\mathtt{LRR},\mathtt{RLR}\},\\
B_Q&=\{\mathtt{LLLL},\mathtt{LLR},\mathtt{LRL},\mathtt{RLL},\mathtt{RR}\}.
\end{aligned}
\tag{21.13}
$$

在 $A_P,A_Q$ 中的响应是 $\mathsf{leaf}_\alpha$，在 $B_P,B_Q$ 中是 $\mathsf{leaf}_\beta$；各树未列的真叶前缀为分支，越过叶的地址为缺失。特别地，两树高度都是 $4$，并且

$$
A_P\cap A_Q=\varnothing,\qquad B_P\cap B_Q=\varnothing.
\tag{21.14}
$$

对于这两棵已知正例，证书的竞争合同恰是[定义 20.1](#20-已给阶段标量的尖锐地址证书与全部最优解)中标量为 $m$ 的整个 $X_L$，没有删去负例。$L=0$ 时直接复用[定理 19.1](#19-纯数量竞争域的尖锐地址证书前沿)的 $a=3\ge2,b=5$ 情形：最小证书基数是 $5$，唯一最小集合分别是 $B_P,B_Q$。$L\ge1$ 时 $f\ge8>b=5$，直接复用[定理 20.1 的式（20.4）–（20.5）](#20-已给阶段标量的尖锐地址证书与全部最优解)：最小基数是 $3$，唯一最小集合分别是 $A_P,A_Q$。因而对 $h\ge4$，可统一记唯一最小集合为

$$
K_P=
\begin{cases}B_P,&L=0,\\A_P,&L\ge1,\end{cases}
\qquad
K_Q=
\begin{cases}B_Q,&L=0,\\A_Q,&L\ge1,\end{cases}
\qquad |K_P|=|K_Q|=k_L,\quad K_P\cap K_Q=\varnothing.
\tag{21.15}
$$

有声性、唯一性与全部地址下界由这些供应直接给出，不另限制证书必须查询叶。

深度障碍同样复用[定理 17.1](#17-已知正实例的地址证书基数与尖锐深度障碍)。在 $P$ 的深度 $3$ 地址 $\mathtt{RLL}$ 处，把最深末端樱桃 $\langle\beta,\alpha\rangle$ 换序，得到该定理的见证 $W$。于是对每个 $h<4$，

$$
c(W)=c(P)=(3,5)^{\mathsf T},\qquad O_h(W)=O_h(P),\qquad
W\notin\rho^3(\mathcal T).
\tag{21.16}
$$

这里的非像结论使用既有[运输记忆完成卷命题 22.2 的式（RA.2207）](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#22-一次全局替换的实际节点单孔边界与来源恢复)：交换产生 $\alpha$ 左孩子，违反实际一步像语法。组成相同给 $W\in X_L$。任何确定性策略在 $P,W$ 上从相同空记录开始；每次查询的地址和响应相同，下一步也相同。有限停止时两输入输出相同，不能分别等于 $1,0$。故 $h<4$ 时没有全输入正确策略。

以下设 $h\ge4$，取任意 $\pi\in\Pi_{L,h}$。在正例 $V\in\{P,Q\}$ 上，它有限停止并接受。其接受路径的不同地址集合 $J_\pi(V)$ 必是定义 20.1 的有声集合。事实上，若 $U\in X_L$ 匹配该集合上的全部 $V$ 响应，则按路径长度归纳：初始记录相同；若前面的有序记录相同，确定性使下一次所选地址相同，该地址属于 $J_\pi(V)$，故下一次响应也相同；重复地址的缓存响应同样相同。于是 $U$ 跟随整个同一接受路径并在同一处停止。全输入正确性给 $U\in\rho^3(\mathcal T)$，恰为有声性所需的全纤维蕴含。因此（21.15）给 $C_\pi(P),C_\pi(Q)\ge k_L$。

由（21.16），$X_L$ 同时有正例和负例，所以全输入正确的策略不能在空记录上停止，必有一个第一查询地址 $u_0$；它在 $P,Q$ 上相同。若两正例费用同时为 $k_L$，唯一最优证书性迫使

$$
J_\pi(P)=K_P,\qquad J_\pi(Q)=K_Q.
$$

但第一地址属于两个接受路径集合，这要求 $u_0\in K_P\cap K_Q$，与（21.15）矛盾。费用是整数且各至少 $k_L$，故费用和至少 $2k_L+1$。全输入最坏费用因包含 $P,Q$，至少为 $\lceil(2k_L+1)/2\rceil=k_L+1$。这证明（21.6）及（21.7）的有限分支下界。

上界由两个总策略给出。对有限叶地址集合 $S$ 与标签 $\ell\in\{\alpha,\beta\}$，在本证明中记 $\mathrm T_\ell(S)$ 为以下有限测试：按 $\mathtt L<\mathtt R$ 的字典序依次查询 $S$；每次只有响应 $\mathsf{leaf}_\ell$ 时继续，其余三个响应各立即输出 $0$ 并停止；全部通过后输出 $1$ 并停止。此记法只描述所列固定纤维的策略分支。下表定义首次查询及其全部四种响应分支，$\mathrm{Reject}$ 表示立即输出 $0$ 并停止。

| 阶段及策略 | 首地址 | $\mathsf{leaf}_\alpha$ | $\mathsf{leaf}_\beta$ | $\mathsf{branch}$ | $\mathsf{absent}$ |
|---|---|---|---|---|---|
| $L=0,\ \pi_P$ | $\mathtt{LR}$ | $\mathrm{Reject}$ | $\mathrm T_\beta(B_P\setminus\{\mathtt{LR}\})$ | $\mathrm T_\beta(B_Q)$ | $\mathrm{Reject}$ |
| $L=0,\ \pi_Q$ | $\mathtt{RR}$ | $\mathrm{Reject}$ | $\mathrm T_\beta(B_Q\setminus\{\mathtt{RR}\})$ | $\mathrm T_\beta(B_P)$ | $\mathrm{Reject}$ |
| $L\ge1,\ \pi_P$ | $\mathtt{LLR}$ | $\mathrm T_\alpha(A_P\setminus\{\mathtt{LLR}\})$ | $\mathrm T_\alpha(A_Q)$ | $\mathrm{Reject}$ | $\mathrm{Reject}$ |
| $L\ge1,\ \pi_Q$ | $\mathtt{RLR}$ | $\mathrm T_\alpha(A_Q\setminus\{\mathtt{RLR}\})$ | $\mathrm T_\alpha(A_P)$ | $\mathrm{Reject}$ | $\mathrm{Reject}$ |

由（21.12）–（21.13），首地址在两正例上的实际响应为

$$
\begin{array}{c|cc}
 &P&Q\\\hline
\mathtt{LR}&\mathsf{leaf}_\beta&\mathsf{branch}\\
\mathtt{RR}&\mathsf{branch}&\mathsf{leaf}_\beta\\
\mathtt{LLR}&\mathsf{leaf}_\alpha&\mathsf{leaf}_\beta\\
\mathtt{RLR}&\mathsf{leaf}_\beta&\mathsf{leaf}_\alpha
\end{array}
\tag{21.17}
$$

故 $P,Q$ 在每一种策略下都进入对应的完整证书检查并通过。任意接受路径要么把首次符合预期的叶响应与余下测试合成整个 $K_P$ 或 $K_Q$，要么在另一首次响应后检查整个另一正例证书。供应定理的有声性在整个 $X_L$ 上有效，故每次接受都判定了真实正例。反过来，实际正例只有 $P,Q$，且两者均按（21.17）接受；因此每次拒绝都属于负例。表中每个首次响应以及每次后续响应均有指定的有限终端行为，策略在每棵输入上总定义且有限停止。

每条测试最多含 $k_L$ 个地址；在偏向的正例路径上首次地址已经属于其证书，余下只有 $k_L-1$ 个，而另一正例路径需在首次查询后另查 $k_L$ 个。首次地址不属于另一证书，来自（21.14）；测试内部每个地址只列一次。因此所有输入的费用至多 $k_L+1$，两正例的费用恰为（21.8），没有重复地址。所列地址全部长度至多 $4$，故在每个 $h\ge4$ 可用。最坏费用由不受偏向的那个正例达到，结合下界得到（21.7）。证毕。

**定义 21.2（全纤维逐输入零错误与正例期望费用）。** 固定定义 21.1 的 $L,h$。随机策略使用一个与输入 $U$ 无关的概率空间 $(\Omega,\mathcal A,\mu)$；种子 $\omega$ 固定后得到同一合法接口上的确定性策略 $\pi_\omega$。对于每个有限记录，下一地址或停止值作为 $\omega$ 的函数可测。要求对整个 $X_L$ 的每个输入分别满足

$$
\forall U\in X_L,\qquad
\mu(E_U)=1,\qquad
E_U=\{\omega:\pi_\omega\text{ 在 }U\text{ 上有限停止且输出 }\iota_3(U)\}.
\tag{21.18}
$$

这些要求同时包含正确性和有限终止，且包括每个负例；$E_U$ 是可测事件。终止时 $C_\omega(U)$ 仍按（21.2）计不同地址，未终止时约定为 $+\infty$。费用是非负可测随机变量，期望只对这一种子律取。没有给输入 $U$ 赋予概率律，也不允许为不同输入更换种子律。定义

$$
R^+_{L,h}
=\inf_{(\Omega,\mathcal A,\mu,\pi_\omega)\ \text{满足（21.18）}}
\max\{\mathbb E_\mu C_\omega(P),\mathbb E_\mu C_\omega(Q)\},
\qquad\inf\varnothing=+\infty.
\tag{21.19}
$$

这是在全纤维上要求逐输入零错误、仅在两个正例上取期望费用最大值的目标；它与（21.3）的全输入确定性最坏费用分别定义。这里沿用 [Frédéric Magniez、Ashwin Nayak、Miklos Santha、Jonah Sherman、Gábor Tardos、David Xiao，*Improved bounds for the randomized decision tree complexity of recursive majority*，arXiv:1309.7565v1，第2页](https://arxiv.org/pdf/1309.7565v1#page=2) 的分布在确定性决策策略上、固定输入费用取该分布期望的框架。该页的标准零错误 $R_0$ 在整个布尔输入域取最大期望费用；（21.19）只对 $P,Q$ 取最大值，因而不定义此纤维的全输入随机最优费用。本文的四值地址查询也不继承该文布尔函数或递归多数函数的数值界。

**定理 21.2（固定纤维的共同种子事件与尖锐正例期望值）。** 在定义 21.2 的合同下，$h<4$ 时不存在满足（21.18）的随机策略。对于每个 $h\ge4$，任意满足（21.18）的策略都有

$$
\mathbb E_\mu C_\omega(P)+\mathbb E_\mu C_\omega(Q)\ge2k_L+1.
\tag{21.20}
$$

其正例期望费用的精确最优值为

$$
\boxed{
R^+_{L,h}=
\begin{cases}
+\infty,&h<4,\\[2pt]
11/2,&h\ge4,\ L=0,\\[2pt]
7/2,&h\ge4,\ L\ge1.
\end{cases}}
\tag{21.21}
$$

有限值由以同一个公平种子在定理 21.1 的 $\pi_P,\pi_Q$ 中择一达到；这个达到策略对每个种子、每个 $U\in X_L$ 都正确并有限终止。

**证明。** 定理 21.1 已证明整个 $X_L$ 有限，因此（21.18）的全部事件，包括每个负例的事件，有一个共同的满概率交集

$$
E=\bigcap_{U\in X_L}E_U,\qquad\mu(E)=1.
\tag{21.22}
$$

对每个固定 $\omega\in E$，$\pi_\omega$ 在整个 $X_L$ 上正确且有限停止，而不仅是在两个正例上正确。在这个固定纤维上，每个输入的执行路径有限，有限多个输入的这些路径的并集也有限；删去不能由 $X_L$ 输入到达的分支，并把已问地址用缓存响应继续，得到有限的纯观察决策树，费用仍计原来的不同地址数。每个终端记录的相容候选全部输出同一个正确任务值，所以它符合[延拓卷定义 11.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#11-自适应分辨率何时可以停止递归)的有限认证模型。此处只把该固定纤维的有限路径放入既有模型，不另建立解析、单射或 Bellman 结论。

若 $h<4$，（21.16）的 $P,W$ 具有相同的全部合法地址响应。对任何同一个固定种子，它们的执行记录逐步相同；若二者都有限终止，则终端值相同，不能同时正确。故 $E_P\cap E_W$ 为空，与（21.18）要求它为满概率事件矛盾。这个障碍针对共享的输入无关种子，允许任意自适应查询及重复缓存。

设 $h\ge4$。对 $E$ 中的每个种子，定理 21.1 的确定性接受路径论证和两个唯一最小证书适用，给

$$
C_\omega(P)+C_\omega(Q)\ge2k_L+1.
$$

对共同种子律积分，非负费用的期望可加性给（21.20）；若任一期望为无穷，下界同样成立。于是

$$
\max\{\mathbb E_\mu C_\omega(P),\mathbb E_\mu C_\omega(Q)\}
\ge\frac{\mathbb E_\mu C_\omega(P)+\mathbb E_\mu C_\omega(Q)}2
\ge k_L+\frac12.
\tag{21.23}
$$

上界取 $\Omega=\{P\text{ 偏向},Q\text{ 偏向}\}$，两种子各占概率 $1/2$，依次使用 $\pi_P,\pi_Q$。定理 21.1 已给出这两种策略对全纤维的每种输入都正确、有限终止及其完整四响应行为；故此同一分布满足（21.18），而且正确性和有限终止对每个种子都成立。由（21.8），

$$
\mathbb E_\mu C_\omega(P)
=\mathbb E_\mu C_\omega(Q)
=\frac{k_L+(k_L+1)}2
=k_L+\frac12.
\tag{21.24}
$$

这达到（21.23），给出（21.21）。每个种子上的全部输入费用仍分别受 $6$ 或 $4$ 限制，但（21.21）的优化域只取正例期望费用；它不结算全输入随机期望费用的最优值。所有期望都来自策略种子，未引入输入先验。证毕。

## 追加锚（本行以下为增补区）
## 22. 可数只读记录的有声返回与终止、精确探针许可的分界

**定义 22.1（完整初始化纤维、记录与逐来源部分正确性）。** 在带选择公理的通常集合论中，设 $X\ne\varnothing$ 是实际来源集合，$\tau:X\to\mathbb B$，$\mathbb B=\{0,1\}$。全部 $x\in X$ 位于同一完整可访问初始化 $I_0$ 的纤维；$I_0$ 包含已经取得的联合记录、控制器初态、已知设置、接口与任务承诺。$X$ 保留符合这些条件的全部实际实现，不以期望的答案删去竞争来源。来源在以下操作中不改变。

取可数的完整动作—报告字母表 $\mathcal L$。动作的精确查询地址、参数及有效设置均在记录中；种子生成的参数也不能从记录中略去。每一步的动作菜单是此前可见记录的函数，合法性对匹配该记录的来源相同。实际报告由同一来源、此前记录及所选完整动作确定；执行耗时、费用、许可变化或其他量若可被策略观察，须作为报告保留。无报告的内部状态与种子不要求属于可数字母表，但在固定种子后，内部状态、控制、停止与输出须能由 $I_0$ 和此前完整记录重建，不能另外读取来源。

令 $\mathcal H\subseteq\mathcal L^{<\mathbb N}$ 为该接口的全部实际可行有限记录，包括空记录；可行性只依接口和实际来源域，不依某个选定策略。对 $h\in\mathcal H$ 定义完整实际相容纤维

$$
\mathcal C(h)=\{x\in X:\text{依次执行 }h\text{ 中的合法动作时，全部报告恰为 }h\text{ 所记}\},
\qquad \mathcal C(h)\ne\varnothing.
\tag{22.1}
$$

终端记录 $(h,y)$ 的有声性定义为 $\tau(\mathcal C(h))=\{y\}$。这是[延拓卷定义 11.1、11.2](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#11-自适应分辨率何时可以停止递归)在完整实际竞争域上的停止证书合同；这里只使用其纤维判据，不把证书存在当作免费取得或有效认证。静态查询族的判据另由既有 [`QueryFamilyIdentification` 的 `identification_iff_kernel_inclusion`](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.lean)供应。

随机策略 $\pi$ 使用与输入无关的同一个概率空间 $(\Omega,\mathcal A,\mu)$。固定 $\omega$ 后策略确定，所有实际随机选择均包含在 $\omega$ 中；动作须对每个实际运行合法。若该种子在 $x$ 上生成有限前缀 $h$，则它在每个 $z\in\mathcal C(h)$ 上生成相同前缀；若此处返回 $y$，在这些 $z$ 上也同时返回 $y$。此同种子重放采用[运输记忆完成卷第 6.4 节、式（CE.19）—（CE.21）之后的完整初始化合同](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#64-商观察的全部未来与行为纤维)的下降条件；这里的操作是只读接口，不假设平移群或赋予来源平移权限。

记错误返回与未终止的种子集合为

$$
\begin{aligned}
W_x^\pi&=\{\omega:\pi_\omega\text{ 在 }x\text{ 上有限返回 }y\ne\tau(x)\},\\
N_x^\pi&=\{\omega:\pi_\omega\text{ 在 }x\text{ 上不有限终止}\}.
\end{aligned}
\tag{22.2}
$$

核心正确性合同仅为 $W_x^\pi\in\mathcal A$ 及 $\mu(W_x^\pi)=0$，对每个 $x\in X$ 分别要求。它不包含有限终止，不要求各个历史事件可测，不给 $X$ 指定 $\sigma$ 代数、来源概率律或来源—种子联合可测性。涉及终止概率或费用期望时，另要求相应 $N_x^\pi$ 或费用随机变量可测。携带来源信息的种子不属于此输入无关合同。

在原始有限 FIB 树接口上，可取既有定义 21.1 的 $X_L$、$\tau=\iota_3$ 和原始地址四值响应；这不改变定义 21.2 只在 $P,Q$ 上优化的 $R^+_{L,h}$。完整树码与全部路径响应采用[母卷定理 9.2、9.3](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，实际替换单射性采用[规范编译卷命题 4.3](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/docs/develop/theory/FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)。组成、规范数量地址、原始树响应、组成祖先许可与实际逆执行是不同对象或任务；组成上的代数逆不增加此只读菜单，也不供应实际树前像。

**定理 22.1（策略无关的可数错误见证域与有声有限返回）。** 在定义 22.1 的合同下，存在至多可数的实际来源集合 $D\subseteq X$：为每个 $h\in\mathcal H$ 的每个已出现目标值，至多选取一个实际代表。固定这些选择后，$D$ 只依接口、来源域与任务，不依策略、种子空间或种子律。对每个满足同种子重放的策略，逐种子有精确集合等式

$$
\bigcup_{x\in X}W_x^\pi=\bigcup_{d\in D}W_d^\pi.
\tag{22.3}
$$

因此，对每个满足核心正确性合同的 $\pi$，有可测的共同满测度集合

$$
G_\pi=\Omega\setminus\bigcup_{d\in D}W_d^\pi,
\qquad \mu(G_\pi)=1.
\tag{22.4}
$$

对每个 $\omega\in G_\pi$ 及每个实际来源，凡有限返回的终端记录均有声。$G_\pi$ 可依赖 $\pi$；本结论不对所有策略再取共同交集，也不要求 $G_\pi$ 上的策略在任何来源上终止。

其不同查询数的推论须满足以下附加合同：动作只读取固定的确定性查询族 $q_a:X\to Y_a$，不改变来源或解锁查询；记录中其他报告均由 $I_0$、精确查询及已获响应决定，不额外区分来源；查询权限与所比较确定性证书完全相同。对实际来源 $x$ 定义

$$
\begin{aligned}
k(x)=\inf\bigl\{|J|:\;&J\text{ 是该接口允许的有限查询集合，}\\[-2pt]
&\forall z\in X,\ (\forall a\in J,\ q_a(z)=q_a(x))\Longrightarrow\tau(z)=\tau(x)\bigr\},
\qquad \inf\varnothing=+\infty.
\end{aligned}
\tag{22.5}
$$

这里比较的是相同原始来源域、初始化、参数精度、报告和许可上的证书，不是删除竞争来源后的证书。有限返回时以 $J_\pi(\omega,x)$ 表示所问的不同查询集合，重复查询只用缓存；未终止时费用规定为 $+\infty$。若这一费用 $C_\pi(\cdot,x)$ 可测，则对每个 $x$ 有

$$
C_\pi(\omega,x)\ge k(x)\quad(\omega\in G_\pi),
\qquad \mathbb E_\mu C_\pi(\cdot,x)\ge k(x).
\tag{22.6}
$$

更一般地，若可测非负费用 $K_\pi(\cdot,x)$ 在未终止时为 $+\infty$，而相同费用合同下每个有声有限记录在 $x$ 上均至少花费 $\lambda(x)\in[0,+\infty]$，则 $\mathbb E_\mu K_\pi(\cdot,x)\ge\lambda(x)$，包括 $\lambda(x)=+\infty$。这一积分结论只使用有声返回下界；依赖全输入有限终止的确定性不等式，须另满足其全输入有限终止及其他实际前提才能使用。

若 $X$ 本身有限或可数，且另有每个 $N_x^\pi\in\mathcal A$、$\mu(N_x^\pi)=0$，则

$$
G_\pi^{\mathrm{tot}}=G_\pi\setminus\bigcup_{x\in X}N_x^\pi,
\qquad \mu(G_\pi^{\mathrm{tot}})=1,
\tag{22.7}
$$

其中每个种子在整个 $X$ 上正确且有限终止。有限 $X$ 时每个这样的种子有一个覆盖该有限域的有限执行步数上界；可数 $X$ 时不保证存在这种统一上界。

对于只把输出 $1$ 解释为接受的合同，同一结论有接受专用子句：只要求每个负来源 $x\in\tau^{-1}(0)$ 的错误接受事件可测且为零测，即可使共同满测度种子上的每个有限接受记录满足 $\mathcal C(h)\subseteq\tau^{-1}(1)$。不要求负返回有声、正来源被接受或任何来源终止。

**证明。** 对每个可行 $h$ 及每个 $b\in\tau(\mathcal C(h))$，在通常的选择集合论中固定

$$
d_{h,b}\in\mathcal C(h),\qquad \tau(d_{h,b})=b,
\qquad
D=\{d_{h,b}:h\in\mathcal H,\ b\in\tau(\mathcal C(h))\}.
\tag{22.8}
$$

$\mathcal H$ 可数，每个记录至多选两个代表，故 $D$ 至多可数。此选取是证明中的实际见证，不授予策略发现代表或读取来源的权限。

任取 $\omega\in W_x^\pi$。设它在 $x$ 上返回 $(h,y)$，则 $x\in\mathcal C(h)$，$\tau(x)=1-y$。代表 $d_{h,1-y}$ 已固定；同种子重放给它完全相同的返回 $(h,y)$，故 $\omega\in W_{d_{h,1-y}}^\pi$。这给（22.3）的一向；另一向由 $D\subseteq X$ 即得。等式是集合论等式，没有把可能不可测的逐历史事件拿来求并。其右边是可数个可测零测集的并，标准可数零测并的测度仍为零，得到（22.4），同时得到左边并集的可测性。未使用来源上的积分、逐历史可测性或联合可测性。

取 $\omega\in G_\pi$ 上实际返回的 $(h,y)$。若存在 $z\in\mathcal C(h)$、$\tau(z)\ne y$，同种子重放使它在 $z$ 上错误返回；由（22.3）这使 $\omega\notin G_\pi$，矛盾。于是该记录有声。这一步使用完整相容纤维；只比较已经运行过的来源不足以给该结论。

在（22.5）的静态只读合同下，若 $z$ 匹配 $J_\pi(\omega,x)$ 上的全部响应，则它匹配执行记录的全部原始报告；其余报告不带额外来源信息，菜单也相同，故 $z\in\mathcal C(h)$。有声性因此使 $J_\pi(\omega,x)$ 成为同一合同下的确定性证书，给 $|J_\pi(\omega,x)|\ge k(x)$。未终止的费用为无穷，同样满足下界。可测非负函数的扩展积分在满测度集上保持下界，给（22.6）；即使零测集上的费用为无穷，该零测部分的非负积分仍为零。一般费用 $K_\pi$ 同理；$\lambda(x)=+\infty$ 时，每个有声有限返回的费用与未终止费用都为 $+\infty$，故费用几乎处处无穷。证书取得或验证若另有收费动作、额外报告或来源相关许可，必须把它们放入新的费用及接口合同，不能沿用（22.5）未计入的资源。

静态证书的使用只取其已知纤维含义。有限布尔坐标域上的标准先例是 [Chandrima Kayal、Sophie Laplante、Émile Larroque、Krišjānis Prūsis、Jevgenijs Vihrovs，*Certification complexity of Boolean functions*，arXiv:2609.26757v1，定义 1—2、定理 3(1)](https://arxiv.org/pdf/2609.26757v1#page=3)：该文的已知输入认证与证书复杂度等式属于有限布尔查询域。这里（22.3）的任意实际来源域及完整自适应报告合同由上述代表构造承担，不由该有限域等式扩张而来。

若另满足终止假设，有限或可数个 $N_x^\pi$ 的并可测且零测，得（22.7）。有限 $X$ 上取各来源有限执行步数的最大值即得该种子的有限上界；此上界未被要求对种子一致。可数域上取来源 $x^{(m)}=0^{m-1}10^\infty$，$m\ge1$，只读二元档案坐标，任务恒为 $0$。确定性策略按顺序查询到第一个 $1$ 后返回 $0$，在每个来源上有限且正确，终止步数恰为 $m$，却无有限的全来源上界。该例满足相同初始化和可数记录合同。

接受专用子句只为每个 $h$ 中存在的负来源固定 $d_{h,0}$。若某种子在某负来源上接受，同种子重放在相应代表上也接受，故全部负来源错误接受事件的并等于这些代表事件的可数并。去除此零测并后，任何实际接受记录若含相容负来源便有相同矛盾。它没有给拒绝记录或终止添加结论。证毕。

**定义 22.2（另行声明的无限二元档案及五窗嵌入）。** 取实际来源域 $X_\infty=\mathbb B^{\mathbb N_{\ge1}}$，$\tau(x)=x_1$，共同初始化只含这一域、任务及接口声明，不含 $x$ 的坐标或有限支持承诺。动作 $q_n$ 只读原始 $x_n$，$n\ge1$，所有坐标始终可用；费用计所问的不同坐标，未终止时为 $+\infty$。种子域 $\Omega_\infty=\mathbb B^{\mathbb N_{\ge1}}$ 配备乘积 $\sigma$ 代数和独立公平二元乘积概率 $\mu_\infty$，与来源无关。来源域无需概率律。

相应的另一实际对象域可明确声明为无限低到高窗口流

$$
\varepsilon=0,\qquad
w_{n-1}(x)=
\begin{cases}
\mathsf E=000=\mathrm{null},&x_n=0,\\
\mathsf B=010=[3],&x_n=1.
\end{cases}
\tag{22.9}
$$

这里 $[3]$ 是窗口模式名，不是窗口在任意位置的整数权重。只读第 $n-1$ 个窗口并区分这两个模式对应 $q_n$；费用仍为一次坐标查询。模式、单位位与有限接缝采用[规范编译卷定义 13.2、命题 13.4](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/docs/develop/theory/FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#13-canonical-position-temporal-iteration-and-modulus-precision)。此域中的对象是已声明的无限流，不要求最终为零，不含 $\mathrm{End}$ 查询或终端证书；$\mathsf E$ 消耗三个位置而不终止。有限自然数编码、完整有限树、组成祖先许可及物理实现都未被声明为该无限流的来源。

**定理 22.2（共同有声性不推出共同终止）。** 在定义 22.2 的二元档案域，考虑以下同种子策略：依次查询 $q_1,q_2,\ldots$，在第一次 $x_n\ne\omega_n$ 时停止并返回已经观察到的 $x_1$。令

$$
T_x(\omega)=\inf\{n\ge1:x_n\ne\omega_n\},\qquad \inf\varnothing=+\infty.
\tag{22.10}
$$

每个实际 $x$ 的 $T_x$ 和费用可测，且对每个整数 $n\ge0$，

$$
\mu_\infty(T_x>n)=2^{-n},\qquad
\mu_\infty(T_x<\infty)=1,\qquad
\mathbb E_{\mu_\infty}C_x=2.
\tag{22.11}
$$

每个种子上的每个有限返回记录均有声，然而

$$
\forall\omega\in\Omega_\infty\ \exists x\in X_\infty,\quad T_x(\omega)=+\infty,
\qquad
\bigcap_{x\in X_\infty}\{\omega:T_x(\omega)<\infty\}=\varnothing.
\tag{22.12}
$$

相同结论在（22.9）明确声明的无限窗口流接口上成立。（22.11）是此特定策略的期望费用，不是最优费用断言；一次确定性查询 $q_1$ 已可返回目标，费用为 $1$。

**证明。** $\{T_x>n\}$ 正是前 $n$ 个种子坐标与实际 $x$ 匹配的柱集；$n=0$ 时为全空间。各柱集可测，独立公平坐标给测度 $2^{-n}$。$\{T_x=\infty\}$ 是这些递减柱集的交，即单点 $\{x\}$，其测度为 $\lim_n2^{-n}=0$。同时 $\{T_x=n\}$ 是两个可测柱集之差，故 $T_x$ 可测，且几乎处处有限。查询从 $1$ 开始且不重复，费用等于 $T_x$，包含无穷的情形。非负整数值变量的尾和公式给

$$
\mathbb E_{\mu_\infty}C_x
=\sum_{n=0}^{\infty}\mu_\infty(T_x>n)
=\sum_{n=0}^{\infty}2^{-n}=2.
\tag{22.13}
$$

每条有限返回记录包含真实 $x_1$；全部相容档案的第一位等于这一报告，所以返回对整个纤维有声，而不仅对该次运行正确。特别地，定义 22.1 的全部错误返回事件为空，共同部分正确性集合可取整个种子域。另一方面，对任意声明种子 $\omega$，实际来源 $x=\omega$ 与它每一位相同，永不触发停止，给（22.12）。于是逐来源零测的未终止事件在这个不可数域上的并是整个种子空间；并没有与（22.3）关于错误返回的可数见证关系冲突。

对窗口流，$\mathsf E$ 与 $\mathsf B$ 的首末位都为零，内部无相邻的两个 $1$；$\varepsilon=0$，故每个有限首窗接缝及窗口间接缝都满足定义 13.2 的乘积为零条件。读取模式逐坐标返回同一二元值，完整相容记录和费用随（22.9）保持，故档案证明原样适用于这个已声明流域。命题 13.4 的 $\mathrm{null}\ne\mathrm{End}$ 防止把匹配到空窗误作终止；没有由合法有限接缝推出整条流有有限支持或有限树实现。确定性读 $q_1$ 返回 $x_1$ 的策略直接给费用 $1$，故期望 $2$ 的扫描不是优化结论。证毕。

**定义 22.3（精确实参数探针及两种逐种子合同）。** 另取实际来源域

$$
X_{\mathrm{probe}}=[0,1]\times\mathbb B,
\qquad \tau(x,b)=b,
\qquad O_a(x,b)=b\mathbin\oplus\mathbf1_{\{a=x\}},\quad a\in[0,1],
\tag{22.14}
$$

其中 $\oplus$ 是二元异或。共同初始化只给出此来源域、任务和探针规则，不给任何 $x$、$b$、身份或类别信息。每个实参数 $a$ 始终可选，查询只读 $O_a$，不改变来源、不解锁动作；动作和记录保留 $a$ 的精确值，不把实参数编码的位长算入费用。有限记录 $h=((a_1,r_1),\ldots,(a_m,r_m))$ 的完整相容纤维为

$$
\mathcal C_{\mathrm{probe}}(h)
=\{(z,c)\in[0,1]\times\mathbb B:
\forall i\le m,\ c\oplus\mathbf1_{\{a_i=z\}}=r_i\}.
\tag{22.15}
$$

每次有限终止的费用为不同精确参数的个数；任意未终止运行的费用为 $+\infty$，即使它只重复有限个参数或在内部计算中停滞。控制器的纯计算、随机种子取得、相等判断及比较不收费。本接口授予理想精确实参数查询，不声明这些操作在有限表示、图灵机或物理装置上的实现。

有限记录空间取各 $([0,1]\times\mathbb B)^m$ 的不交并及其 Borel 结构。策略允许自适应与重复参数；在给定种子和记录后决定下一个精确参数、有限返回值或不再返回的内部停滞，控制映射须对种子—记录乘积可测。采用同一输入无关概率空间 $(\Omega,\mathcal A,\mu)$，相同种子与相同记录的内部状态和决定相同，不能隐读来源。来源域在此另配积 Borel 结构，以核对响应的联合可测性，仍不给来源概率律。要求每个来源上的终止、错误事件和扩展非负费用可测。

令 $\Pi_{\mathrm{det}}$ 为在整个 $X_{\mathrm{probe}}$ 上正确且有限终止的确定性策略族；令 $\Pi_{\mathrm w}$ 为对每个固定来源分别以概率一正确且有限终止的策略族；令 $\Pi_{\mathrm s}$ 为对每个声明种子、每个实际来源都正确且有限终止的策略族。强合同中的“每个种子”包含零测种子，不仅指概率一事件。定义

$$
\begin{aligned}
D_{\mathrm{probe}}&=\inf_{\pi\in\Pi_{\mathrm{det}}}\ \sup_{(x,b)\in X_{\mathrm{probe}}}C_\pi(x,b),\\
R_{\mathrm w}&=\inf_{\pi\in\Pi_{\mathrm w}}\ \sup_{(x,b)\in X_{\mathrm{probe}}}\mathbb E_\mu C_\pi(\omega;x,b),\\
R_{\mathrm s}&=\inf_{\pi\in\Pi_{\mathrm s}}\ \sup_{(x,b)\in X_{\mathrm{probe}}}\mathbb E_\mu C_\pi(\omega;x,b).
\end{aligned}
\tag{22.16}
$$

每个期望只对各策略自己的共同种子律取，$\inf\varnothing=+\infty$。它们在全来源域取上确界，与定义 21.2 的正例专用目标不同。固定输入的查询期望惯例采用 [Magniez、Nayak、Santha、Sherman、Tardos、Xiao，*Improved bounds for the randomized decision tree complexity of recursive majority*，arXiv:1309.7565v1，第 2 页](https://arxiv.org/pdf/1309.7565v1#page=2)；该页的输入为有限布尔词，不能将其有限域合同无条件移到此实参数域。

弱合同只要求可测性及逐来源概率一性质，不等于在全输入正确策略上取分布。它也不提供可计算表示或失败识别： [Vasco Brattka、Guido Gherardi、Rupert Hölzl，*Probabilistic Computability and Choice*，arXiv:1312.7305v3，定义 3.1](https://arxiv.org/pdf/1312.7305v3#page=13)的 Las Vegas 可计算性在表示空间上要求可计算 $F_1,F_2$，后者在每个输入表示名及建议上定义，用 Sierpiński 输出识别失败，且前者在成功建议上正确。这些额外合同未包含在（22.14）—（22.16）中，不能仅由弱合同赋予无条件的标准 Las Vegas 算法称谓。

**定理 22.3（证书、确定性发现及两种随机合同的锐值）。** 在定义 22.3 的理想探针接口上，每个实际来源的最小有声证书均需且只需 $2$ 个不同精确参数；而全输入优化值分别为

$$
\boxed{D_{\mathrm{probe}}=3,\qquad R_{\mathrm w}=1,\qquad R_{\mathrm s}=2.}
\tag{22.17}
$$

这些下界对自适应、重复参数及允许零查询返回的策略均成立。弱值由在 $[0,1]$ 上均匀抽取 $u$，只查询 $O_u$ 并返回该响应达到：每个 $(x,b)$ 的错误种子集恰为单点 $\{x\}$，但每个声明种子都有错误来源。

强值可用 $u$ 在 $[0,1)$ 上的均匀律达到。先查询

$$
a=u,\qquad
c=s(u)=
\begin{cases}
u+\tfrac12,&0\le u<\tfrac12,\\
u-\tfrac12,&\tfrac12\le u<1.
\end{cases}
\tag{22.18}
$$

若两个响应相等则返回其值；若不同则查询常数参数 $1$ 并返回第三个响应。每个声明种子在每个来源上正确并有限终止，且

$$
\forall(x,b),\quad \mathbb E C(\cdot;x,b)=2,
\qquad
\forall u\in[0,1),\quad \sup_{(x,b)}C(u;x,b)=3.
\tag{22.19}
$$

响应、两种达到策略的控制、错误和终止事件以及费用均按定义 22.3 可测。

**证明。** 先在同一个实际域上确定证书。空记录的纤维含两种目标。只问一个不同参数 $a$，即使重复任意有限次，得到的唯一响应 $r$ 仍同时匹配来源

$$
(a,1-r),\qquad (z,r)\quad(z\in[0,1]\setminus\{a\}).
\tag{22.20}
$$

它们的目标相反，所以零或一个不同参数不能有声。对任意给定来源 $(x,b)$，选两个互异参数 $a,c\ne x$；这种选择始终存在，包括 $x=0,1$。两个响应都为 $b$。任意匹配来源 $(z,d)$ 若有 $d=1-b$，须同时满足 $z=a$ 和 $z=c$ 才能将两个响应都翻成 $b$，与 $a\ne c$ 矛盾。因此完整纤维的目标恰为 $b$，得到每个来源的最小证书数 $2$。此存在证书的参数选择可依赖已经指定的来源；它不等于未知来源下的两查询发现策略。

现在取任意全输入正确且有限终止的确定性策略。它不能零查询返回，由（22.20）也不能在只问过一个不同参数时返回。其首个参数记为 $a$，固定首响应 $r\in\mathbb B$。在实际来源 $(a,1-r)$ 上首响应就是 $r$；有限终止及上述证书障碍迫使它在有限时刻第一次查询不同于 $a$ 的参数 $c$。截至这一时刻，控制只依由重复 $a$ 形成的同一记录，故 $c$ 也在另一实际来源 $(c,r)$ 上被同样选取。两来源截至第二个不同参数的全部有序响应一致，最后这次的响应都为 $1-r$：前者在 $a$ 翻转、在 $c$ 不翻转，后者在 $a$ 不翻转、在 $c$ 翻转。

这两个相容来源的目标相反。以后只重复 $a,c$ 也保持相同记录，不能产生正确停止叶；有限终止要求沿这条共同前缀询问第三个不同参数。因此该策略的全输入最坏费用至少为 $3$。这同时处理自适应第二参数、任意重复查询及内部停滞；全输入总性排除在该实际前缀停滞。上界固定查询 $0,\tfrac12$：响应相等时返回共同响应，不同时查询 $1$ 并返回第三响应。相等时实际 $x$ 不等于前两参数；不同时 $x$ 恰是前两参数之一，所以 $x\ne1$，第三响应为 $b$。所有输入均正确、至多三次，且 $x=0$ 或 $\tfrac12$ 时恰三次，故 $D_{\mathrm{probe}}=3$。

弱合同下先排除零查询降低期望。设 $A_j$ 是策略不问任何参数而有限返回 $j$ 的种子事件，$j=0,1$。这些事件由相同初始化和种子决定，与实际来源无关，并按控制可测性可测。在任意固定来源 $(0,1-j)$ 上，$A_j$ 都是错误返回事件的子集，因此弱正确性给 $\mu(A_j)=0$。对任意固定来源，有限终止具有概率一，且 $A_0\cup A_1$ 零测，故费用至少为 $1$ 几乎处处，扩展非负期望也至少为 $1$；未终止的零测种子不降低下界。这适用于全部弱策略，不要求固定种子在全来源上正确。

弱达到策略取 Lebesgue 概率空间 $[0,1]$，精确查询 $u$ 并返回 $O_u(x,b)$。所有来源、所有种子都在一次查询后返回，费用恒为 $1$。固定 $(x,b)$ 时仅 $u=x$ 翻转正确目标，其错误集 $\{x\}$ 可测且零测，包括两个端点；故逐来源正确且有限终止具有概率一。对每个声明的 $u$，来源 $(u,0)$ 使它错误返回 $1$，于是

$$
\bigcup_{(x,b)\in X_{\mathrm{probe}}}\{u:O_u(x,b)\ne b\}=[0,1],
\qquad
\bigcap_{(x,b)}\{u:O_u(x,b)=b\}=\varnothing.
\tag{22.21}
$$

结合弱下界得到 $R_{\mathrm w}=1$。单点错误随实际坐标 $x$ 改变，不随标签 $b$ 改变。固定任何种子得到的策略均不是全输入正确策略，所以这个达到分布不在全输入正确确定性策略族上。

强合同下，每个种子在所有实际来源上正确且有限终止。同种子重放使任意有限终端记录有声，故由（22.20）每个来源、每个种子的费用至少为 $2$，积分给 $R_{\mathrm s}\ge2$。不需要把不可数来源的逐来源零测集求并，因为强合同本身逐种子规定全部来源。

对于（22.18）的达到策略，$u,s(u)$ 都属于 $[0,1)$；两者相差 $\tfrac12$ 或 $-\tfrac12$，故始终互异，而且都不同于常数 $1$。这些断言对 $u=0,\tfrac12$ 也成立：两参数分别是 $(0,\tfrac12)$、$(\tfrac12,0)$，没有重合端点。当 $x$ 不在前两参数中，两响应相同且等于 $b$；当 $x$ 恰等于其中一个时，两响应相反，且 $x<1$，第三参数 $1$ 不翻转，返回 $b$。当 $x=1$ 时，前两参数均不翻转，立即以费用 $2$ 返回 $b$。因此每个种子、每个标签、每个来源都有限且正确。

具体费用为

$$
C(u;x,b)=2+\mathbf1_{\{x=u\ \mathrm{或}\ x=s(u)\}}.
\tag{22.22}
$$

固定 $x<1$ 时，$s(s(x))=x$ 且 $s(x)\ne x$，额外一次查询的种子恰为 $\{x,s(x)\}$；固定 $x=1$ 时该集合为空。这些有限种子集的 Lebesgue 测度均为零，给所有来源期望恰为 $2$。反之，对任意固定 $u$，来源 $x=u$ 需要第三参数，不论标签，费用为 $3$；所有来源费用又至多 $3$，得（22.19）并证明强上界 $R_{\mathrm s}\le2$。因此三个锐值都已在原对象、原权限和原费用下达到，而逐种子最坏费用与逐来源期望上确界分别为 $3$ 与 $2$。

最后核对测度合同。精确响应的异常集合

$$
\{(a,x,b):a=x\}\subseteq[0,1]\times[0,1]\times\mathbb B
\tag{22.23}
$$

是闭对角线与离散标签域的乘积，所以 $O_a(x,b)$ 联合 Borel 可测。$s$ 是在两个 Borel 半区间上定义的平移，故 Borel；比较两个二元响应、返回其值或选择常数 $1$ 的控制是可测分支。有限次响应组合保持可测性；（22.22）的两条对角线条件是 Borel，费用可测。弱策略的错误集为可测单点、终止事件为全空间、费用恒定；强策略错误集为空、终止事件为全空间、费用由（22.22）给出。对允许的一般可测控制，逐步组合可测控制与（22.14）给可测有限执行事件，正确返回与终止是其可数并；非终止是补集。不同参数数目在每个有限记录上由有限个对角线相等判断给出，连同非终止费用为无穷的约定得到可测扩展费用。

该接口的参数记录不可数：例如单查询记录 $(a,r)$ 随 $a$ 连续变化。因此定义 22.1 的可数完整记录假设不满足，（22.21）不反驳定理 22.1。既有 [`UncountableSingletonCutCountermodel` 的 `uncountable_singleton_cut_countermodel`](https://github.com/the-omega-institute/trureturing/blob/b992b308b8905fad449b1c0ceb7f7bbeb3c0333d/D5/S3/ConceptDynamics/EscapeSpectrum/UncountableSingletonCutCountermodel.lean)供应不可数单点切割的静态零测现象；（22.17）—（22.22）另外使用此处精确响应、完整相容来源和发现策略，静态现象本身不授予探针权限或任何上述费用最优值。整个论证未把来源分布、有限树实现或物理测量添入模型。证毕。

## 追加锚（本行以下为增补区）

## 23. 全有限来源上两个指定正例的共同最优地址费用

**定义 23.1（全来源的两正例费用合同）。** 取非空有限自由有序满二叉树集合

$$
\mathcal T=\{\alpha,\beta\}\cup\{\langle S,T\rangle:S,T\in\mathcal T\},
\qquad
\rho(\alpha)=\beta,\quad
\rho(\beta)=\langle\beta,\alpha\rangle,\quad
\rho(\langle S,T\rangle)=\langle\rho(S),\rho(T)\rangle.
\tag{23.1}
$$

树相等保留字面的次序、括号形状和叶标记，不取结合或交换商。固定 $d=3k$、整数 $k\ge1$，目标为 $\iota_d(U)=\mathbf 1_{\{U\in\mathcal I_d\}}$，其中 $\mathcal I_d=\rho^d(\mathcal T)$。固定两个完整描述已知的正例 $P,Q\in\mathcal I_d$，仅把它们指定为费用评价的对象。全部未知输入 $U\in\mathcal T$ 有同一个与输入无关的完整初始化；其中可含固定的 $d,P,Q$ 和策略，但不含输入的组成、数量、大小、高度、叶数、正性、所属子类或身份承诺。尤其不承诺 $U\in\{P,Q\}$。

每个有限地址 $u\in\{\mathtt L,\mathtt R\}^{<\mathbb N}$，包括空地址 $\varepsilon$，始终合法。查询只读同一棵不变的 $U$，报告为[定义 16.1](#16-实际树像与尖锐有限路径观察前沿)的四值 $\operatorname{out}_U(u)\in\{\mathsf{leaf}_\alpha,\mathsf{leaf}_\beta,\mathsf{branch},\mathsf{absent}\}$；没有其他携带来源信息的报告或访问途径。策略的有限返回值属于 $\{0,1\}$。费用只数所问的不同地址，重复地址复用缓存；地址定位、地址长度、控制器计算和取得种子不收费。未有限终止的费用为 $+\infty$。

记 $\mathfrak D_d$ 为对每个 $U\in\mathcal T$ 都正确返回 $\iota_d(U)$ 且有限终止的确定性策略集合，$C_\pi(U)$ 为其不同地址费用。记 $\mathfrak R_d$ 为以下随机策略集合：使用一个与输入无关的概率空间 $(\Omega,\mathcal A,\mu)$，所有随机选择均包含在种子 $\omega$ 中，固定种子后控制、查询、缓存、停止和输出都由共同初始化及此前完整地址—响应记录决定，并满足同种子重放。对每个 $U\in\mathcal T$ 分别要求错误返回事件、未有限终止事件和非负扩展费用 $C_\Pi(\cdot,U)$ 可测，前两个事件的测度均为零。此处允许零测种子例外，不要求每个声明种子都全域正确；也不为来源指定概率律。记

$$
\begin{aligned}
L_P&=L(P),& L_Q&=L(Q),& n_P&=|L_P|,&n_Q&=|L_Q|,\\
H(P,Q)&\ \Longleftrightarrow\quad
\exists u\in L_P\cap L_Q:\quad
\operatorname{out}_P(u)\ne\operatorname{out}_Q(u),\\
D_d^+(P,Q)&=\inf_{\pi\in\mathfrak D_d}
\max\{C_\pi(P),C_\pi(Q)\},\\
R_d^+(P,Q)&=\inf_{\Pi\in\mathfrak R_d}
\max\{\mathbb E_\mu C_\Pi(\cdot,P),\mathbb E_\mu C_\Pi(\cdot,Q)\}.
\end{aligned}
\tag{23.2}
$$

$L$ 沿用定义 18.1，故 $H(P,Q)$ 恰指某个共享叶地址有相反的 $\alpha/\beta$ 标签。期望是两个固定来源各自对同一输入无关种子律的期望，可以为 $+\infty$；式（23.2）既不是输入先验的平均，也不是在整个 $\mathcal T$ 上优化最坏费用。完整来源、组成 $c$、规范数量地址、原始地址报告、组成祖先许可与实际逆执行分别保留其对象和操作意义；本合同只判完整树的实际像成员身份，不授权逆操作，也不把环境代数中的守恒或可逆性解释成物理对应。

**定理 23.2（叶地址与标签的共同取得判据及两正例锐值）。** 在定义 23.1 的合同下，确定性费用与随机期望费用同时达到两个个体下界 $(n_P,n_Q)$ 的充要条件均为

$$
P=Q\quad\text{或}\quad H(P,Q).
\tag{23.3}
$$

其中 $P=Q$ 只复用同一个正例的最优证书。若 $P\ne Q$ 且 $H(P,Q)$ 不成立，则每个 $\pi\in\mathfrak D_d$ 及每个 $\Pi\in\mathfrak R_d$ 分别满足

$$
\begin{aligned}
C_\pi(P)+C_\pi(Q)&\ge n_P+n_Q+1,\\
\mathbb E_\mu C_\Pi(\cdot,P)+\mathbb E_\mu C_\Pi(\cdot,Q)&\ge n_P+n_Q+1.
\end{aligned}
\tag{23.4}
$$

确定性费用对 $(n_P,n_Q+1)$ 和 $(n_P+1,n_Q)$ 分别由一个全域正确且有限终止的策略取得。两个目标的精确值为

$$
\begin{aligned}
D_d^+(P,Q)&=
\begin{cases}
n+1,&P\ne Q,\ \neg H(P,Q),\ n_P=n_Q=n,\\
\max\{n_P,n_Q\},&\text{其余情形},
\end{cases}\\[3pt]
R_d^+(P,Q)&=
\begin{cases}
n+\tfrac12,&P\ne Q,\ \neg H(P,Q),\ n_P=n_Q=n,\\
\max\{n_P,n_Q\},&\text{其余情形}.
\end{cases}
\end{aligned}
\tag{23.5}
$$

式（23.2）的下确界全部达到。所有策略均须在全部 $\mathcal T$ 上满足其正确性和终止合同；取得性不附加未知输入承诺。

**证明。** 先把确定性接受运行的记录接到已有证书。固定 $\pi\in\mathfrak D_d$ 和 $V\in\{P,Q\}$，以 $J_V$ 记它在 $V$ 上终止前所问的不同地址集合。全域有限终止使记录有限；令 $h$ 为其中地址长度的最大值，空记录时取 $h=0$，则 $J_V\subseteq\Sigma_{\le h}$。任何匹配这些四值响应的 $U\in\mathcal T$，在共同初始化下逐步生成相同地址、缓存响应和控制状态，故在同一处返回 $1$。全域正确性使 $J_V$ 按定义 18.2 无承诺有声。直接应用[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)，有

$$
L(V)\subseteq J_V,\qquad C_\pi(V)=|J_V|\ge |L(V)|.
\tag{23.6}
$$

这使用每条实际有限终端记录自己的 $h$，没有预置高度或统一视界。空记录也在该论证内，不能接受这些非空叶前沿的正例。同一已知结果还保证：匹配 $V$ 全部带标签叶响应的完整树只能是 $V$；这一步的完整树恢复直接取自[母卷定理 9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，不重新建立个体证书结论。有限返回所需的任务恒值和认证资源合同取自[延拓卷定义 11.1、11.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#11-自适应分辨率何时可以停止递归)；这里只用终端纤维与证书意义，不把定义 11.2 的有限候选集递推套到无限的 $\mathcal T$。

设 $P\ne Q$。两次运行从同一初始化开始，在第一次不同响应之前，其全部历史、内部控制、查询选择和停止决定相同。这样的不同响应必在任一接受运行停止前出现：若在较早终止处仍未出现，两者将以相同记录同时接受；该记录按（23.6）已包含 $L_P$，而 $Q$ 匹配其全部带标签叶响应，因而 $Q=P$，矛盾。因此存在第一次响应不同的查询，地址记为 $u$，两次运行都实际问了它。$u$ 是新地址：若此前问过，不变来源及缓存使它的响应等于此前已经相同的响应，不可能第一次产生差异。这个前缀归纳使用[运输记忆完成卷第 6.4 节式（CE.19）—（CE.21）之后的完整初始化下降合同](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#64-商观察的全部未来与行为纤维)；这里核对的是只读接口的同记录控制条件，不引入该节的群平移操作。

若 $\neg H(P,Q)$，共享叶地址的标签全部相同，所以这个 $u$ 不在 $L_P\cap L_Q$ 中。它至少位于一方的必查叶集合之外，却在该方运行中被计费；该方的（23.6）下界遂增加一，另一方仍有其全部必查叶费用，得到（23.4）的确定性不等式。论证没有限制第一次查询，也没有假设策略不自适应；重复查询不能成为第一次差异，任何较早停止已由完整叶证书排除。

以下取得构造共用一个后备判定。任一原型测试不匹配时，从空地址起探索实际 $U$，复用全部已缓存答案；仅在报告 $\mathsf{branch}$ 的实际节点处继续查询左右孩子，报告叶时不再扩展。$U$ 有限，所以有限步即恢复整个字面树和实际测得的叶数 $m$，所恢复描述按母卷定理 9.3 唯一。$m$ 是此运行取得的量，不是初始化承诺。随后枚举叶数至多 $m$ 的全部带 $\alpha/\beta$ 标记的有序满二叉树 $T$；有限叶数给有限个形状，每个形状给有限个标记，故这是一个可穷尽的有限枚举。逐个计算描述 $\rho^d(T)$ 并与已恢复的 $U$ 比较，命中则返回 $1$，穷尽而未命中则返回 $0$。每个计算和比较均有限。

一次 $\rho$ 把 $\alpha$ 叶换成一片叶、把 $\beta$ 叶换成两片叶，并保留已有二叉节点，故从不减少叶数。因而 $U=\rho^d(T)$ 的任何实际前像均在这次有限枚举内，正例必命中，负例必穷尽拒绝。[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)已供应树替换的单射性，迭代后命中的完整前像也唯一；判定只需要其存在性。计算枚举对象的替换描述不对未知来源执行替换或逆替换。仅不断搜索直到找到前像不能替代此后备：命题 4.3 已排除 $\alpha\in\rho(\mathcal T)$，所以实际负输入 $\alpha\notin\mathcal I_d$ 上那种无穷搜索不终止。上述有限枚举在 $m=1$ 时仍能穷尽拒绝。后备的运行时间可以依输入增长；这里只要求每个有限来源都有限终止。

若 $P=Q$，依固定次序查询它的全部叶，全部带标签响应匹配则接受，任一不匹配即进入后备。完整匹配唯一确定 $U=P$，所以该策略全域正确且有限终止，在两个相同评价对象上费用均为 $n_P$。

若 $H(P,Q)$，选一个标签冲突的共享叶地址 $u$ 首先查询。响应精确等于 $P$ 在 $u$ 的叶标签时选择 $P$ 测试，精确等于 $Q$ 的相反叶标签时选择 $Q$ 测试；其他两个响应均进入后备。被选原型的其余叶依固定次序查询，全部匹配才接受，任一不匹配则进入后备。每次接受都有完整带标签叶证书，故正确；其余来源由后备正确处理。$P,Q$ 各自选中自己的测试且没有额外叶外查询，因此费用对恰为 $(n_P,n_Q)$。

最后设 $P\ne Q$、$\neg H(P,Q)$。有限满二叉树的两个叶前沿不能严格包含：若 $L_P\subseteq L_Q$，每片 $P$ 叶在 $Q$ 中也为叶，其所有真前缀在两树中都是分支，而这些叶截住了每条向下路径，故两树的形状相同，$L_P=L_Q$。再由共享叶标签相同，得到 $P=Q$，矛盾。因此存在 $p\in L_P\setminus L_Q$，也存在 $q\in L_Q\setminus L_P$。

先查询 $p$，把它的精确 $P$ 叶响应作为选择 $P$ 测试的分支，把精确 $\operatorname{out}_Q(p)$ 作为选择 $Q$ 测试的分支。因为 $p\notin L_Q$，后者必为 $\mathsf{branch}$ 或 $\mathsf{absent}$，与前者不同；每个其他首响应均进入后备。选择 $P$ 后查询其余叶，选择 $Q$ 后查询其全部叶；任一后续不匹配均进入后备，完整匹配才接受。这样在 $P$ 上花费 $n_P$，在 $Q$ 上花费 $n_Q+1$，在所有其他来源上仍正确且有限终止。交换两原型并从 $q$ 开始，取得 $(n_P+1,n_Q)$。原型不匹配本身从未被当作负来源证据。

随机下界须使用全域正确且终止的同一种子策略。由[母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，$\mathcal T$ 单射编码进两字母的有限词，因而可数。全部有限地址可数，四响应字母表有限，有限地址—响应记录包括空记录也可数。定义 23.1 的完整初始化、合法菜单、不变来源、无额外来源报告和同种子重放满足[定理 22.1](#22-可数只读记录的有声返回与终止精确探针许可的分界)的合同：其式（22.4）提供策略各自的共同满测度有声返回集合。还须分别使用式（22.7）的共同总性子句：本域 $\mathcal T$ 可数，每个来源的未终止事件已要求可测且零测，故有策略各自的共同满测度集合 $G_\Pi^{\mathrm{tot}}$，在其每个种子上固定种子策略都属于 $\mathfrak D_d$。有声返回本身不供应这一全域终止结论；此处也不对所有随机策略取共同种子交集，不声称统一全来源运行时间上界。

于是（23.6）及已经证明的确定性联合不等式均逐种子适用于 $G_\Pi^{\mathrm{tot}}$。对可测非负扩展费用积分，得到每个固定来源的期望下界，以及（23.4）的随机不等式；两来源费用和的非负积分可相加，包括无穷值，零测种子例外不改变这些不等式。因此 $P\ne Q$ 且 $\neg H(P,Q)$ 时，两期望不可能同时等于 $(n_P,n_Q)$；其他情形已经由确定性构造在单点种子空间上取得。这证明（23.3）。

若无冲突且 $n_P=n_Q=n$，（23.4）及确定性费用的整数性给 $\max\{C_\pi(P),C_\pi(Q)\}\ge n+1$，任一端点构造达到它。随机方面，两个期望的最大值至少为其平均，故至少为 $n+\tfrac12$；用一次与输入无关的公平二元种子选择上述两个全域正确且有限终止的端点策略，两个固定来源的期望均为 $n+\tfrac12$。所有种子在所有有限来源上都正确且终止，费用与事件在这个有限种子空间上可测。若无冲突而叶数不等，令较大者为 $n_P>n_Q$，则整数性给 $n_Q+1\le n_P$；费用对 $(n_P,n_Q+1)$ 已达到两个目标的个体下界最大值 $n_P$。$n_Q>n_P$ 时用另一端点。其余情形用已取得的 $(n_P,n_Q)$ 即可。因此（23.5）的每个下确界均由满足全来源合同的策略取得。证毕。

**命题 23.3（实际 FIB 来源的无共享叶族与同组成严格对照）。** 对每个 $d=3k\ge3$，置

$$
A=\rho^d(\alpha),\qquad
B=\rho^{d+2}(\alpha)=\rho^2(A),\qquad
P_{\mathrm{dis}}=\langle A,B\rangle,\qquad
Q_{\mathrm{dis}}=\langle B,A\rangle.
\tag{23.7}
$$

这两个不同正例的叶地址集合互不相交，叶数均为

$$
n=F_{d+1}+F_{d+3},\qquad F_0=0,\quad F_1=1,\quad F_{j+2}=F_{j+1}+F_j.
\tag{23.8}
$$

在定义 23.1 的全来源合同下，$D_d^+(P_{\mathrm{dis}},Q_{\mathrm{dis}})=n+1$、$R_d^+(P_{\mathrm{dis}},Q_{\mathrm{dis}})=n+\tfrac12$。

特别地，在 $d=3$ 置

$$
E=\langle\beta,\alpha\rangle,\qquad
A=\langle E,\beta\rangle,\qquad
C=\langle A,E\rangle,\qquad
B=\langle C,A\rangle,
\tag{23.9}
$$

并另取

$$
P_{\mathrm{con}}=\langle\langle A,A\rangle,C\rangle,
\qquad
Q_{\mathrm{con}}=\langle\langle A,C\rangle,A\rangle.
\tag{23.10}
$$

四棵指定树均为实际 $\rho^3$ 像，均有 $c=(4,7)^{\mathsf T}$、$n=11$、$q=2\cdot4+3\cdot7=29$；其中

$$
\operatorname{out}_{P_{\mathrm{con}}}(\mathtt L\mathtt R\mathtt L\mathtt R)
=\mathsf{leaf}_\alpha,
\qquad
\operatorname{out}_{Q_{\mathrm{con}}}(\mathtt L\mathtt R\mathtt L\mathtt R)
=\mathsf{leaf}_\beta.
\tag{23.11}
$$

因此同一组成和数量读数的两个指定正例对有严格不同的尖锐费用：

$$
\begin{aligned}
(D_3^+,R_3^+)(P_{\mathrm{dis}},Q_{\mathrm{dis}})&=(12,\tfrac{23}{2}),\\
(D_3^+,R_3^+)(P_{\mathrm{con}},Q_{\mathrm{con}})&=(11,11).
\end{aligned}
\tag{23.12}
$$

这些组成相等只比较指定的实际评价对象，不向未知输入域增加组成、数量或大小承诺。

**证明。** 由替换的二叉同态规则，式（23.7）分别有完整前像

$$
P_{\mathrm{dis}}=
\rho^d\bigl(\langle\alpha,\langle\beta,\alpha\rangle\rangle\bigr),
\qquad
Q_{\mathrm{dis}}=
\rho^d\bigl(\langle\langle\beta,\alpha\rangle,\alpha\rangle\bigr).
\tag{23.13}
$$

两前像字面不同，其像的不同性亦直接由规范编译卷命题 4.3 的单射性得到。$\rho^2(\alpha)=\langle\beta,\alpha\rangle$ 和 $\rho^2(\beta)=\langle\langle\beta,\alpha\rangle,\beta\rangle$ 均非叶，所以在 $B=\rho^2(A)$ 中，$A$ 的每片叶都被非叶子树替换；$B$ 的每个叶地址严格延长某个 $A$ 叶地址。$A$ 的叶前沿前缀自由，故没有一个 $A$ 叶地址同时是 $B$ 的叶地址。于是

$$
\begin{aligned}
L(P_{\mathrm{dis}})&=\mathtt L L(A)\ \cup\ \mathtt R L(B),\\
L(Q_{\mathrm{dis}})&=\mathtt L L(B)\ \cup\ \mathtt R L(A),\\
L(P_{\mathrm{dis}})\cap L(Q_{\mathrm{dis}})&=\varnothing,
\end{aligned}
\tag{23.14}
$$

其中 $\mathtt L L(A)=\{\mathtt L u:u\in L(A)\}$，其他前缀集合相同解释。直接复用[母卷定理 3.2 的种子树递推](FIBONACCI_ATOMIC_RELATION_GENERATION.md#3-fibonacci-替换与组成动力学)：种子轨道的叶数从 $1,1$ 开始按 Fibonacci 递推，故 $|L(\rho^j\alpha)|=F_{j+1}$。相加得到（23.8），再用定理 23.2 得到一般族的费用。这里保留 $d=3k\ge3$ 的证书适用范围。

在 $d=3$，同一个既有种子递推给 $E=\rho^2\alpha$、$A=\rho^3\alpha$、$C=\rho^4\alpha=\rho^3\beta$、$B=\rho^5\alpha$，恰为（23.9）的字面展开。除（23.13）的两前像外，另两棵树的完整前像为

$$
P_{\mathrm{con}}=
\rho^3\bigl(\langle\langle\alpha,\alpha\rangle,\beta\rangle\bigr),
\qquad
Q_{\mathrm{con}}=
\rho^3\bigl(\langle\langle\alpha,\beta\rangle,\alpha\rangle\bigr).
\tag{23.15}
$$

由这些实际前像及 $\rho^3$ 的二叉同态性，四树均在 $\mathcal I_3$。组成加性给 $c(E)=(1,1)^{\mathsf T}$、$c(A)=(1,2)^{\mathsf T}$、$c(C)=(2,3)^{\mathsf T}$、$c(B)=(3,5)^{\mathsf T}$，所以 $c(A)+c(B)=2c(A)+c(C)=(4,7)^{\mathsf T}$，叶数为 $11$，定义 1.1 的数量读数为 $29$。在 $P_{\mathrm{con}}$ 上沿 $\mathtt L\mathtt R$ 到 $A$，再沿 $\mathtt L\mathtt R$ 到 $\alpha$；在 $Q_{\mathrm{con}}$ 上沿 $\mathtt L\mathtt R$ 到 $C$，再沿 $\mathtt L\mathtt R$ 到其左子树 $A$ 的右叶 $\beta$。这证明（23.11），所以该对满足 $H$，而无共享叶对不满足 $H$。定理 23.2 遂给（23.12）。

这两个对照也显示后备判定的必要性：$A=\rho^3\alpha\in\mathcal I_3$ 在 $\mathtt L\mathtt L\mathtt L$ 上报告 $\mathsf{absent}$，而 $P_{\mathrm{dis}}$、$Q_{\mathrm{dis}}$ 分别报告 $\mathsf{leaf}_\beta$、$\mathsf{branch}$；在 $\mathtt L\mathtt R\mathtt L\mathtt R$ 上 $A$ 同样报告 $\mathsf{absent}$，与冲突对的两叶报告都不同。故无论从这里的无共享叶测试地址还是共享冲突测试地址开始，原型之外都存在合法实际正来源；把这种首响应直接判负会违反全来源正确性。定理 23.2 的构造将它们送入有限后备判定。证毕。

## 追加锚（本行以下为增补区）

## 24. 两两叶最优与三个实际来源的共同费用障碍

**定义 24.1（三个固定正例的全来源费用合同）。** 将[定义 23.1](#23-全有限来源上两个指定正例的共同最优地址费用)的深度固定为 $d=3$，费用评价对象增为三棵完整描述已知的正例 $P_1,P_2,P_3\in\mathcal I_3$。策略仍在全部非空有限自由有序满二叉树 $\mathcal T$ 上判定 $\iota_3$；共同初始化可含这三个固定描述，却不含未知输入的组成、数量、大小、高度、正性或身份承诺。尤其不承诺未知输入属于 $\{P_1,P_2,P_3\}$。查询仍是任意有限左右地址的原始四值只读报告，费用仍计不同地址并复用缓存，未有限终止时为 $+\infty$，没有其他来源信息渠道。

沿用定义 23.1 的确定性全域正确有限终止策略合同 $\mathfrak D_3$，以及输入无关同种子重放、逐来源几乎处处正确且有限终止、相关事件及非负扩展费用可测的随机策略合同 $\mathfrak R_3$，定义

$$
\begin{aligned}
D_3^+(P_1,P_2,P_3)
&=\inf_{\pi\in\mathfrak D_3}\max_{1\le i\le3}C_\pi(P_i),\\
R_3^+(P_1,P_2,P_3)
&=\inf_{\Pi\in\mathfrak R_3}\max_{1\le i\le3}
\mathbb E_\mu C_\Pi(\cdot,P_i).
\end{aligned}
\tag{24.3}
$$

三项期望使用同一个与输入无关的种子律；没有未知输入先验。随机目标是三个期望的最大值，另一个量 $\mathbb E_\mu\max_i C_\Pi(\cdot,P_i)$ 不作为式（24.3）的目标。正确性与终止仍遍及全部 $\mathcal T$，最优化只评价三个固定来源。实际像成员身份、组成读数与实际逆执行保留定义 23.1 的不同任务含义。

**定理 24.2（同组成实际三正例的两两叶最优与确定性、随机锐值）。** 复用[命题 23.3](#23-全有限来源上两个指定正例的共同最优地址费用)在 $d=3$ 的字面树，置

$$
\begin{gathered}
E=\langle\beta,\alpha\rangle,\qquad
A=\langle E,\beta\rangle=\rho^3(\alpha),\qquad
C=\langle A,E\rangle=\rho^3(\beta),\\
U=\langle\langle A,A\rangle,C\rangle=P_{\mathrm{con}},\qquad
V=\langle\langle A,C\rangle,A\rangle=Q_{\mathrm{con}},\qquad W=A,
\end{gathered}
\tag{24.4}
$$

并定义三个固定评价来源

$$
\begin{aligned}
P_1&=\langle\langle U,U\rangle,A\rangle,\\
P_2&=\langle\langle V,A\rangle,U\rangle,\\
P_3&=\langle\langle A,V\rangle,V\rangle.
\end{aligned}
\tag{24.5}
$$

令 $u_0=\langle\langle\alpha,\alpha\rangle,\beta\rangle$、$v_0=\langle\langle\alpha,\beta\rangle,\alpha\rangle$。这些来源的完整前像为

$$
\begin{aligned}
U&=\rho^3(u_0),& V&=\rho^3(v_0),\\
P_1&=\rho^3\bigl(\langle\langle u_0,u_0\rangle,\alpha\rangle\bigr),\\
P_2&=\rho^3\bigl(\langle\langle v_0,\alpha\rangle,u_0\rangle\bigr),\\
P_3&=\rho^3\bigl(\langle\langle\alpha,v_0\rangle,v_0\rangle\bigr).
\end{aligned}
\tag{24.6}
$$

三者两两不同，且

$$
P_i\in\mathcal I_3,\qquad
c(P_i)=(9,16)^{\mathsf T},\qquad
|L(P_i)|=25,\qquad q(P_i)=66
\quad(1\le i\le3).
\tag{24.7}
$$

在定义 24.1 的全来源合同下，每个两元素评价对可由一个共同策略同时取得两个个体最小费用 $25$，即

$$
D_3^+(P_i,P_j)=R_3^+(P_i,P_j)=25
\quad(1\le i<j\le3).
\tag{24.8}
$$

三个对允许选择不同策略。对三元素评价集合，存在三个全域正确且有限终止的确定性策略，其费用向量依次为

$$
(25,25,26),\qquad(25,26,25),\qquad(26,25,25).
\tag{24.9}
$$

每个 $\pi\in\mathfrak D_3$ 及每个 $\Pi\in\mathfrak R_3$ 均满足

$$
\begin{gathered}
\sum_{i=1}^3 C_\pi(P_i)\ge76,\qquad
\sum_{i=1}^3\mathbb E_\mu C_\Pi(\cdot,P_i)\ge76,\\
\boxed{\quad D_3^+(P_1,P_2,P_3)=26,\qquad
R_3^+(P_1,P_2,P_3)=\frac{76}{3}.\quad}
\end{gathered}
\tag{24.10}
$$

两个下确界均达到。随机锐值由一次共同、输入无关的均匀三元种子选择式（24.9）的三个策略取得；在这一混合上，三个固定来源的期望各为 $76/3$，而 $\mathbb E_\mu\max_i C_\Pi(\cdot,P_i)=26$。因此两两共同取得叶数个体最小值，不足以使同一个策略对这三个指定实际正来源共同取得。

**证明。** 命题 23.3 的式（23.9）、（23.10）、（23.15）已给出 $A,C,U,V$ 的字面展开与实际完整前像。将这些前像代入定义 23.1 的二叉替换同态规则，直接得到式（24.6），所以三个 $P_i$ 都是实际三步像。式（24.6）的三个前像两两字面不同；[规范编译卷命题 4.3 的树替换单射性](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)在三次迭代后仍单射，因而三棵像树两两不同，且这些完整前像各自唯一。这里的前像由实际树替换给出，不从组成上的逆矩阵推断。

命题 23.3 已供应 $c(A)=(1,2)^{\mathsf T}$ 和 $c(U)=c(V)=(4,7)^{\mathsf T}$。组成在二叉拼接下相加，故

$$
\begin{aligned}
c(P_1)&=2c(U)+c(A),\\
c(P_2)&=c(V)+c(A)+c(U),\\
c(P_3)&=c(A)+2c(V),\\
2(4,7)^{\mathsf T}+(1,2)^{\mathsf T}&=(9,16)^{\mathsf T},\\
9+16&=25,\qquad 2\cdot9+3\cdot16=66.
\end{aligned}
\tag{24.11}
$$

最后一个读数使用定义 1.1 的 $q=(2,3)$，得到式（24.7）。这些相等是对三个固定完整来源的读数计算，不加入未知输入承诺。

取三个地址

$$
s_{12}=\mathtt L\mathtt L\mathtt L\mathtt R\mathtt L\mathtt R,
\qquad
s_{13}=\mathtt L\mathtt R\mathtt L\mathtt R\mathtt L\mathtt R,
\qquad
s_{23}=\mathtt R\mathtt L\mathtt R\mathtt L\mathtt R.
$$

其完整响应表为

$$
\begin{array}{c|ccc}
\text{地址}&\operatorname{out}_{P_1}&\operatorname{out}_{P_2}&\operatorname{out}_{P_3}\\ \hline
s_{12}&\mathsf{leaf}_\alpha&\mathsf{leaf}_\beta&\mathsf{absent}\\
s_{13}&\mathsf{leaf}_\alpha&\mathsf{absent}&\mathsf{leaf}_\beta\\
s_{23}&\mathsf{absent}&\mathsf{leaf}_\alpha&\mathsf{leaf}_\beta
\end{array}
\tag{24.12}
$$

逐行从式（24.4）、（24.5）核对。第一行在 $P_1$ 上先沿 $\mathtt L\mathtt L$ 到 $U$，再沿 $\mathtt L\mathtt R$ 到 $A$，最后沿 $\mathtt L\mathtt R$ 到 $\alpha$；在 $P_2$ 上先沿 $\mathtt L\mathtt L$ 到 $V$，再沿 $\mathtt L\mathtt R$ 到 $C$，最后沿 $\mathtt L\mathtt R$ 到 $C$ 左子树 $A$ 的右叶 $\beta$；在 $P_3$ 上先沿 $\mathtt L\mathtt L$ 到 $A$，再沿 $\mathtt L\mathtt R$ 到叶 $\alpha$，剩余的 $\mathtt L\mathtt R$ 越过该叶，故报告不存在。

第二行在 $P_1$ 上先沿 $\mathtt L\mathtt R$ 到 $U$，再沿 $\mathtt L\mathtt R$ 到 $A$，最后沿 $\mathtt L\mathtt R$ 到 $\alpha$；在 $P_2$ 上先沿 $\mathtt L\mathtt R$ 到 $A$，再沿 $\mathtt L\mathtt R$ 到叶 $\alpha$，剩余的 $\mathtt L\mathtt R$ 越过该叶；在 $P_3$ 上先沿 $\mathtt L\mathtt R$ 到 $V$，再沿 $\mathtt L\mathtt R$ 到 $C$，最后沿 $\mathtt L\mathtt R$ 到 $\beta$。这分别给出第二行的 $\mathsf{leaf}_\alpha$、$\mathsf{absent}$、$\mathsf{leaf}_\beta$。

第三行在 $P_1$ 上先沿 $\mathtt R$ 到 $A$，再沿 $\mathtt L\mathtt R$ 到叶 $\alpha$，剩余的 $\mathtt L\mathtt R$ 越过该叶；在 $P_2$ 上先沿 $\mathtt R$ 到 $U$，再沿 $\mathtt L\mathtt R$ 到 $A$，最后沿 $\mathtt L\mathtt R$ 到 $\alpha$；在 $P_3$ 上先沿 $\mathtt R$ 到 $V$，再沿 $\mathtt L\mathtt R$ 到 $C$，最后沿 $\mathtt L\mathtt R$ 到 $\beta$。这给出第三行。三行中的 $U,V$ 局部标签冲突正是命题 23.3 式（23.11）的 $t=\mathtt L\mathtt R\mathtt L\mathtt R$ 冲突在不同外层位置的应用；上述逐行核对还保留了第三个来源的不存在响应。

于是 $s_{ij}$ 是 $P_i,P_j$ 标签相反的共享叶地址，三个对分别满足定理 23.2 的 $H$ 判据。直接应用该定理，得到每对存在共同策略取得 $(25,25)$，以及式（24.8）。个体下界由[定理 18.2 的完整叶条件](#18-精确组成最优证书的唯一性与无承诺叶前沿)供应，其深度条件在这里为 $d=3=3\cdot1$。并未把三个分别优化的费用对视作同一个策略。

接着核对三重叶交集。由 $A=\langle\langle\beta,\alpha\rangle,\beta\rangle$，以及 $U,V$ 的字面定义，有

$$
\begin{gathered}
L(A)=\{\mathtt L\mathtt L,\mathtt L\mathtt R,\mathtt R\},\\
U|_{\mathtt L\mathtt L}=A,\quad
U|_{\mathtt L\mathtt R}=A,\quad U|_{\mathtt R}=C,\\
V|_{\mathtt L\mathtt L}=A,\quad
V|_{\mathtt L\mathtt R}=C,\quad V|_{\mathtt R}=A,\\
L(A)\cap L(U)=L(A)\cap L(V)=\varnothing.
\end{gathered}
\tag{24.13}
$$

因为 $A,C$ 都为分支，$U,V$ 在 $A$ 的全部三个叶地址上均报告 $\mathsf{branch}$，故最后一行成立。三个互不为前缀的外层位置 $\mathtt L\mathtt L$、$\mathtt L\mathtt R$、$\mathtt R$ 覆盖每棵 $P_i$ 的全部叶，其子树分别为

$$
\begin{array}{c|ccc}
\text{外层位置}&P_1&P_2&P_3\\ \hline
\mathtt L\mathtt L&U&V&A\\
\mathtt L\mathtt R&U&A&V\\
\mathtt R&A&U&V
\end{array}
\qquad
\boxed{\ L(P_1)\cap L(P_2)\cap L(P_3)=\varnothing.\ }
\tag{24.14}
$$

确切地说，每个共同叶地址必落在这三个位置中的同一个位置内；该位置上的三个叶集合交集是该前缀与 $L(U)\cap L(V)\cap L(A)$ 的拼接，而式（24.13）使它为空。三个位置的祖先在各树中都是分支，所以祖先自身也不是共同叶。由此得到式（24.14）。

固定任意 $\pi\in\mathfrak D_3$。在第一次查询前，控制、内部计算、停止及输出只依共同初始化，不依输入。它不能不作查询而有限返回：$A\in\mathcal I_3$，而规范编译卷命题 4.3 给 $\alpha\notin\rho(\mathcal T)$，从而 $\alpha\notin\mathcal I_3$，同一个无查询返回值不能同时正确处理这两个输入。它也不能在无查询状态永久内部计算，因为这违反全域有限终止。因此必在有限内部计算后作一个首查询，其地址 $s$ 在所有输入上相同，且因尚无查询而是首次计费地址。

令 $J_i$ 为该策略在 $P_i$ 上有限接受前所问的不同地址集合。直接应用定理 23.2 证明中的终端记录结论（23.6），有 $L(P_i)\subseteq J_i$。该结论使用每条实际终端记录自己的有限最大地址长度，并由定理 18.2 供应完整叶必要性，不需要预置高度。式（24.14）使这个共同首地址 $s$ 至少不属于一个 $L(P_i)$，但 $s\in J_i$ 对三个 $i$ 都成立。故至少一项费用在其 $25$ 个必查叶之外多计一个地址，其余两项仍至少为 $25$，从而

$$
\sum_{i=1}^3 C_\pi(P_i)\ge25+25+26=76,
\qquad
\max_i C_\pi(P_i)\ge
\left\lceil\frac{76}{3}\right\rceil=26.
\tag{24.15}
$$

这一论证允许任意自适应后续查询、任意地址长度及重复查询；首次地址即已造成联合费用障碍。

为取得式（24.9），分别从式（24.12）的三行地址开始构造策略。对某一行，首先查询其地址。该行的三个不同响应各自选择对应的 $P_i$ 作暂定原型，包括 $\mathsf{absent}$ 所对应的原型；尚未使用的第四个响应 $\mathsf{branch}$ 直接进入定理 23.2 证明中已有的全有限来源后备判定。选中某一原型后，依固定次序核对它的全部 $25$ 个带标签叶地址，复用此前缓存。任一后续叶响应不匹配即进入同一个后备判定；只有全部带标签叶响应匹配时才接受。

定理 18.2 的充分性及其引用的[母卷定理 9.3 的字面恢复](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)保证，完整叶匹配的未知树只能等于所选原型，故该处接受正确。首响应只选择暂定测试，尤其不存在响应既不证明树身份，也不证明正性。其余输入由定理 23.2 已证明全域正确且有限终止的后备处理；缓存只复用已取得的确定性响应。原型测试至多核对有限的 $25$ 个叶，因而整个策略在每个实际有限树上都有限终止。原型之外的正来源与全部负来源都保留在这个合同内：它们不能完整匹配一个原型的带标签叶证书，故由首分支或后续不匹配送入后备，而不因测试失败直接判负。

在被评价的 $P_i$ 上，首响应恰选中自己，后续全部匹配。首地址若为其叶，则已查询的那个叶由缓存计入 $25$ 个完整叶，总费用为 $25$；若为不存在地址，则不在叶集合内，完整叶仍需全部查询，总费用为 $26$。式（24.12）的三个不存在位置依次是 $P_3,P_2,P_1$，遂逐一得到式（24.9）。结合式（24.15），确定性锐值为 $26$。

现在固定任意 $\Pi\in\mathfrak R_3$。由[母卷定理 9.2 的单射有限词编码](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，整个 $\mathcal T$ 可数；全部有限地址可数，四值响应有限，因此完整有限地址—响应记录也可数。定义 24.1 继承的输入无关初始化、任意地址合法菜单、固定只读来源、无额外来源报告及同种子重放，满足[定理 22.1](#22-可数只读记录的有声返回与终止精确探针许可的分界)的合同。其式（22.4）给该策略自己的共同满测度有声有限返回集合 $G_\Pi$。

还必须另行应用该定理的总性子句（22.7）：$\mathcal T$ 可数，且对每个实际来源分别要求未有限终止事件可测并为零测，所以存在 $G_\Pi^{\mathrm{tot}}\subseteq G_\Pi$，测度为 $1$，其中每个固定种子策略都在整个 $\mathcal T$ 上正确且有限终止。仅有（22.4）的有声返回不能替代这个全域总性条件。共同满测度集合可依赖 $\Pi$；这里没有对所有随机策略取共同种子交集，也没有使用统一全来源运行时间上界。

对每个 $\omega\in G_\Pi^{\mathrm{tot}}$，该固定种子策略属于 $\mathfrak D_3$，故式（24.15）的同一策略费用和下界逐种子成立。对三个可测非负扩展费用积分，有限和的非负积分可相加，包括无穷值，得到

$$
\begin{aligned}
\sum_{i=1}^3\mathbb E_\mu C_\Pi(\cdot,P_i)
&=\int_\Omega\sum_{i=1}^3 C_\Pi(\omega,P_i)\,d\mu(\omega)
\ge76,\\
\max_i\mathbb E_\mu C_\Pi(\cdot,P_i)&\ge\frac{76}{3}.
\end{aligned}
\tag{24.16}
$$

零测种子例外不改变这些非负积分不等式。这不是把三对分别优化的结果相加，而是先在每个共同正确且全域终止的种子上比较三个实际运行，再对同一策略积分。

最后，在共同初始化下取输入无关的均匀种子 $\omega\in\{1,2,3\}$，分别选择式（24.9）的三个确定性策略；只取这一次种子，不按未知输入再选择策略。每个声明种子在全部 $\mathcal T$ 上都正确且有限终止，有限种子空间上的相关事件和费用均可测，所以该混合属于 $\mathfrak R_3$。每个固定来源恰在两个种子上费用为 $25$、一个种子上费用为 $26$，从而

$$
\mathbb E_\mu C_\Pi(\cdot,P_i)=\frac{25+25+26}{3}
=\frac{76}{3}\quad(1\le i\le3),
\qquad
\mathbb E_\mu\max_i C_\Pi(\cdot,P_i)=26.
\tag{24.17}
$$

式（24.16）与（24.17）给随机锐值和取得性，完成式（24.10）的全部结论。证明只针对式（24.5）的三个实际三步像及声明的全有限来源四值接口；不要求未知输入承诺，也不推出任意三来源分类或这一见证的全局最小规模。证毕。

## 追加锚（本行以下为增补区）
## 25. 有限正来源族的遗传共享叶分离与四元共同费用

**定义 25.1（遗传信息叶与共同取得）。** 将[定义 23.1](#23-全有限来源上两个指定正例的共同最优地址费用)固定为 $d=3$，沿用其 $\mathcal T$、$\rho$、$\mathcal I_3$、$\iota_3$、$\mathfrak D_3$、$\mathfrak R_3$ 和费用 $C$。未知输入仍遍历全部非空有限自由有序满二叉 $\alpha/\beta$ 树；有限评价族 $F\subseteq\mathcal I_3$ 的完整描述可在共同初始化中给定，却不构成输入属于 $F$ 的承诺。每个有限左右地址，包括空地址，均合法；报告仅为不变来源的原始 $\mathsf{leaf}_\alpha$、$\mathsf{leaf}_\beta$、$\mathsf{branch}$、$\mathsf{absent}$。费用只计缓存后的不同地址，其他计算、地址长度、定位和种子取得均不收费，未有限终止时为 $+\infty$。确定性策略在整个 $\mathcal T$ 上正确且有限终止；随机策略使用一个输入无关的可测种子律，满足同种子重放、逐来源几乎处处正确且有限终止，以及非负扩展费用可测的合同。

对 $P\in\mathcal I_3$，令 $L(P)$ 为叶地址集，$\lambda_P:L(P)\to\{\alpha,\beta\}$ 为叶标签，$n_P=|L(P)|$。对有限非单元素族 $S\subseteq\mathcal I_3$，定义其信息性共同叶集

$$
\Delta(S)=\left\{u\in\bigcap_{P\in S}L(P):
\{\lambda_P(u):P\in S\}=\{\alpha,\beta\}\right\}.
\tag{25.7}
$$

称有限族 $F$ **确定性相容**，若存在一个 $\pi\in\mathfrak D_3$ 对所有 $P\in F$ 同时有 $C_\pi(P)=n_P$；称其 **期望相容**，若存在一个 $\Pi\in\mathfrak R_3$ 对所有 $P\in F$ 同时有 $\mathbb E_\mu C_\Pi(\cdot,P)=n_P$。空族的这些要求为空约束。对非空 $F$，记

$$
\begin{aligned}
D_3^+(F)&=\inf_{\pi\in\mathfrak D_3}\max_{P\in F}C_\pi(P),\\
R_3^+(F)&=\inf_{\Pi\in\mathfrak R_3}\max_{P\in F}
\mathbb E_\mu C_\Pi(\cdot,P).
\end{aligned}
\tag{25.8}
$$

这里的随机目标是固定来源各自期望的最大值，不是期望最大值，也没有来源先验。叶安全只表示一次查询属于当前原型的必需叶证书，不缩小合法地址菜单。对非空 $F$，**叶安全递归路由树**是以下有限二叉路由：根标为 $F$，非单元素节点 $S$ 选 $u\in\Delta(S)$，两个孩子分别为 $S_\alpha=\{P\in S:\lambda_P(u)=\alpha\}$、$S_\beta=\{P\in S:\lambda_P(u)=\beta\}$，终端节点为单元素族；到终端后还须核对该原型的全部带标签叶，任何非叶路由响应或核对不匹配均转入定理 23.2 证明中的全域后备判定。路由节点的 $S$ 只保留匹配历史的评价原型，不是全部实际相容来源纤维。

个体最小费用 $n_P$ 及其完整叶证书直接采用[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)，其条件在此为 $d=3=3\cdot1$。已知输入认证的有限布尔域合同见 [Kayal、Laplante、Larroque、Prūsis、Vihrovs，*Certification complexity of Boolean functions*，arXiv:2609.26757v1，定义 1—2、定理 3(1)](https://arxiv.org/pdf/2609.26757v1#page=3)；本定义保留整个 $\mathcal T$ 上的判定合同，不采用该文已知输入认证问题的缩减输入域。完整来源、组成、规范数量地址、原始地址响应、组成祖先许可与实际逆执行仍是定义 23.1 的不同对象和任务。

**定理 25.2（有限族的遗传信息叶判据）。** 对每个有限族 $F\subseteq\mathcal I_3$，有

$$
\boxed{\quad
F\text{ 确定性相容}
\ \Longleftrightarrow\
F\text{ 期望相容}
\ \Longleftrightarrow\
\forall S\subseteq F,\ |S|\ge2\Longrightarrow\Delta(S)\ne\varnothing.
\quad}
\tag{25.9}
$$

对非空 $F$，这些条件亦等价于存在定义 25.1 的叶安全递归路由树。其路由路径至多使用 $|F|-1$ 个不同地址，接上完整叶核对和全域后备后，对每个 $P\in F$ 的总费用恰为 $n_P$。

**证明。** 先设一个 $\pi\in\mathfrak D_3$ 同时取得全部 $n_P$，任取 $S\subseteq F$、$|S|\ge2$。令 $J_P$ 为该策略在 $P$ 上接受前所问的不同地址集合。直接使用定理 23.2 证明中的式（23.6），得到 $L(P)\subseteq J_P$；费用等于 $n_P$ 遂使 $J_P=L(P)$。式（23.6）适用于各自实际有限记录的最大地址长度，不预置未知输入高度。

所有 $P\in S$ 的运行具有相同初始化。在第一次响应差异之前，同记录重放保证查询、缓存、内部控制和停止决定相同；这里直接使用[运输记忆完成卷第 6.4 节、式（CE.19）—（CE.21）之后的完整初始化下降合同](https://github.com/the-omega-institute/trureturing/blob/3b7e298150f95ea135afc222e230c614d03c02e1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#64-商观察的全部未来与行为纤维)的只读同历史条件，不调用群平移。第一次差异必在任一运行停止前发生。否则，在最早停止时所有运行都凭同一记录同时接受；该记录含任取一个 $P$ 的全部带标签叶，而所有其他成员均匹配它。定理 18.2 所供应的完整叶恢复使每个成员都等于 $P$，与 $|S|\ge2$ 矛盾。因此确有第一次差异地址 $u$，且每个 $P\in S$ 都实际问了 $u$。由 $J_P=L(P)$，$u$ 是所有成员的叶；不同的叶响应必包含两种标签，故 $u\in\Delta(S)$。不变来源上的重复地址不能产生第一次响应差异。任意 $S$ 均满足所需条件。

反之，设式（25.9）的遗传条件成立，先取 $F\ne\varnothing$。在所有有限地址的固定短词优先次序下，非单元素节点 $S$ 选择有限非空集 $\Delta(S)$ 的首地址。两种叶标签将 $S$ 分成两个非空真子集；每个非单元素孩子仍满足遗传条件，故按 $|S|$ 归纳得到有限路由树。选中的分离地址不曾在同一路径上查询：先前记录中的每个地址在当前全部幸存原型上具有相同响应，不能属于 $\Delta(S)$。每次路由严格减少原型数，因而每条路径至多有 $|F|-1$ 个不同路由地址。

将此路由实际用于未知 $T\in\mathcal T$。路由查询报告叶时进入相应孩子，报告分支或不存在时进入定理 23.2 证明中的后备。达到单元素节点 $\{P\}$ 后按固定次序核对 $P$ 的全部带标签叶，复用缓存；任一不匹配进入同一后备，完整匹配才返回 $1$。完整匹配的充分性与字面唯一性直接取自定理 18.2 及其引用的[母卷定理 9.3](https://github.com/the-omega-institute/trureturing/blob/3b7e298150f95ea135afc222e230c614d03c02e1/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，故接受正确。原型路由与核对均有限；其余来源直接交给已有后备：它恢复实际有限树及实际叶数 $m$，在叶数至多 $m$ 的前像树中作有限穷尽判定，适用于全部正来源与负来源。此调用使用定理 23.2 已证的替换不减叶数与全域终止结论，不把原型不匹配当作负性证明。

在固定评价来源 $P\in F$ 上，每次路由都保留 $P$，全部路由地址均为 $P$ 的叶；终端核对恰补齐 $L(P)$，没有额外地址。因此该全域策略的费用为 $n_P$。$F=\varnothing$ 时直接采用同一已有全域后备即可。确定性相容又以单点种子律给期望相容。

现在设 $\Pi\in\mathfrak R_3$ 同时取得每个 $n_P$ 的期望。由[母卷定理 9.2 的单射有限词编码](https://github.com/the-omega-institute/trureturing/blob/3b7e298150f95ea135afc222e230c614d03c02e1/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，整个 $\mathcal T$ 可数；有限地址和完整有限四值记录也可数。定义 25.1 的接口满足[定理 22.1](#22-可数只读记录的有声返回与终止精确探针许可的分界)：先由其式（22.4）取该策略的共同满测度有声返回集 $G_\Pi$，再另行应用总性子句（22.7），得到共同满测度集 $G_\Pi^{\mathrm{tot}}\subseteq G_\Pi$，其中每个固定种子策略都属于 $\mathfrak D_3$。这一步分别用到全部来源可数和逐来源可测零测未终止事件；有声返回本身不蕴含总性。

对 $\omega\in G_\Pi^{\mathrm{tot}}$，式（23.6）给每个 $P\in F$ 的 $C_\Pi(\omega,P)\ge n_P$。已知期望恰为有限值 $n_P$，所以可测非负超额 $(C_\Pi(\cdot,P)-n_P)_+$ 的积分为零，从而 $C_\Pi(\cdot,P)=n_P$ 几乎处处。有限交集因此满足

$$
G_\Pi^*=G_\Pi^{\mathrm{tot}}\cap
\bigcap_{P\in F}\{\omega:C_\Pi(\omega,P)=n_P\},
\qquad \mu(G_\Pi^*)=1.
\tag{25.10}
$$

取其中一个种子便得同时取得全部 $n_P$ 的全域正确总策略，已证的必要性遂给遗传条件。满测度集允许依赖 $\Pi$，没有对所有随机策略取共同交集，也没有要求统一全来源时间界。

最后，任一这样的递归路由树接上核对与后备，已由上述构造给确定性相容，进而给遗传条件；遗传条件又已构造路由树。因此所述路由等价也成立。证毕。

**推论 25.3（三元均取得时的四元条件）。** 设 $F\subseteq\mathcal I_3$ 有四个元素，每个三元素子族都确定性相容，或等价地都期望相容。则

$$
\boxed{\quad
F\text{ 确定性相容}
\ \Longleftrightarrow\
F\text{ 期望相容}
\ \Longleftrightarrow\
\Delta(F)\ne\varnothing.
\quad}
\tag{25.11}
$$

**证明。** 共同取得在限制评价族后仍成立，所以每个二元素子族也相容。定理 25.2 因而已保证所有真非单元素子族的 $\Delta$ 非空；四元族只剩 $\Delta(F)$ 这一个条件。再用该定理即得式（25.11）。这里需要在四者之间产生不同叶标签的共同叶；四者标签相同的共同叶不属于 $\Delta(F)$，不能分裂共同历史。证毕。

**定义 25.4（循环四孔实际来源）。** 直接复用[命题 23.3 的式（23.9）、（23.10）、（23.15）](#23-全有限来源上两个指定正例的共同最优地址费用)，记

$$
\begin{gathered}
E=\langle\beta,\alpha\rangle,\quad
A=\langle E,\beta\rangle=\rho^3(\alpha),\quad
C=\langle A,E\rangle=\rho^3(\beta),\\
u_0=\langle\langle\alpha,\alpha\rangle,\beta\rangle,
\quad v_0=\langle\langle\alpha,\beta\rangle,\alpha\rangle,\\
U=\langle\langle A,A\rangle,C\rangle=\rho^3(u_0),
\qquad V=\langle\langle A,C\rangle,A\rangle=\rho^3(v_0).
\end{gathered}
\tag{25.12}
$$

定义四孔拼接映射 $B:\mathcal T^4\to\mathcal T$ 和孔地址

$$
B(x_1,x_2,x_3,x_4)=\langle\langle x_1,x_2\rangle,\langle x_3,x_4\rangle\rangle,
\qquad (p_1,p_2,p_3,p_4)=(\mathtt{LL},\mathtt{LR},\mathtt{RL},\mathtt{RR}).
\tag{25.13}
$$

四个完整评价来源及指定完整前像为

$$
\begin{aligned}
P_1&=B(A,U,U,V)=\rho^3\bigl(B(\alpha,u_0,u_0,v_0)\bigr),\\
P_2&=B(V,A,U,U)=\rho^3\bigl(B(v_0,\alpha,u_0,u_0)\bigr),\\
P_3&=B(U,V,A,U)=\rho^3\bigl(B(u_0,v_0,\alpha,u_0)\bigr),\\
P_4&=B(U,U,V,A)=\rho^3\bigl(B(u_0,u_0,v_0,\alpha)\bigr),
\qquad F_4=\{P_1,P_2,P_3,P_4\}.
\end{aligned}
\tag{25.14}
$$

对完整树 $X$，以 $\mathcal F(X)=\{(u,\lambda_X(u)):u\in L(X)\}$ 记其带标签叶前沿；地址拼接记为 $pu$。以下下标均按四循环解释，$P_{j+4}=P_j$、$p_{j+4}=p_j$。本定义只指定完整来源与观察地址，不从组成逆矩阵生成树前像，也不向未知输入提供免费读数。

**定理 25.5（循环四族的完整前沿与三元可取得、四元不可取得）。** 定义 25.4 的四棵树是两两不同的实际三步像，式（25.14）给各自唯一完整前像；每个前像的组成为 $(7,3)^{\mathsf T}$，且

$$
P_i\in\mathcal I_3,\qquad
c(P_i)=(13,23)^{\mathsf T},\qquad n_{P_i}=36,\qquad q(P_i)=95
\quad(1\le i\le4).
\tag{25.15}
$$

三个块的全部带标签叶前沿为

$$
\begin{aligned}
\mathcal F(A)=\{& (\mathtt{LL},\beta),(\mathtt{LR},\alpha),(\mathtt R,\beta)\},\\
\mathcal F(U)=\{& (\mathtt{LLLL},\beta),(\mathtt{LLLR},\alpha),(\mathtt{LLR},\beta),\\
& (\mathtt{LRLL},\beta),(\mathtt{LRLR},\alpha),(\mathtt{LRR},\beta),\\
& (\mathtt{RLLL},\beta),(\mathtt{RLLR},\alpha),(\mathtt{RLR},\beta),\\
& (\mathtt{RRL},\beta),(\mathtt{RRR},\alpha)\},\\
\mathcal F(V)=\{& (\mathtt{LLLL},\beta),(\mathtt{LLLR},\alpha),(\mathtt{LLR},\beta),\\
& (\mathtt{LRLLL},\beta),(\mathtt{LRLLR},\alpha),(\mathtt{LRLR},\beta),\\
& (\mathtt{LRRL},\beta),(\mathtt{LRRR},\alpha),\\
& (\mathtt{RLL},\beta),(\mathtt{RLR},\alpha),(\mathtt{RR},\beta)\}.
\end{aligned}
\tag{25.16}
$$

对式（25.14）的每一行 $(X_1,X_2,X_3,X_4)$，该目标的全部 $36$ 片带标签叶精确给为

$$
\mathcal F\bigl(B(X_1,X_2,X_3,X_4)\bigr)
=\bigsqcup_{h=1}^4\{(p_hu,\ell):(u,\ell)\in\mathcal F(X_h)\}.
\tag{25.17}
$$

令 $t=\mathtt{LRLR}$、$q_j=p_jt$，其完整四值响应表为

$$
\begin{array}{c|cccc}
\text{地址}&\operatorname{out}_{P_1}&\operatorname{out}_{P_2}&\operatorname{out}_{P_3}&\operatorname{out}_{P_4}\\ \hline
q_1=\mathtt{LLLRLR}&\mathsf{absent}&\mathsf{leaf}_\beta&\mathsf{leaf}_\alpha&\mathsf{leaf}_\alpha\\
q_2=\mathtt{LRLRLR}&\mathsf{leaf}_\alpha&\mathsf{absent}&\mathsf{leaf}_\beta&\mathsf{leaf}_\alpha\\
q_3=\mathtt{RLLRLR}&\mathsf{leaf}_\alpha&\mathsf{leaf}_\alpha&\mathsf{absent}&\mathsf{leaf}_\beta\\
q_4=\mathtt{RRLRLR}&\mathsf{leaf}_\beta&\mathsf{leaf}_\alpha&\mathsf{leaf}_\alpha&\mathsf{absent}
\end{array}
\tag{25.18}
$$

每个三元素子族同时取得三个个体最小费用 $36$，而四元族不相容。更确切地，

$$
q_j\in\Delta(F_4\setminus\{P_j\})\quad(1\le j\le4),
\qquad \bigcap_{i=1}^4L(P_i)=\varnothing,
\qquad \Delta(F_4)=\varnothing.
\tag{25.19}
$$

**证明。** 式（25.12）的完整块前像取自命题 23.3；$\rho^3$ 保持二叉构造，故拼接这些前像便给式（25.14）的完整实际等式。四个前像在 $\alpha$ 原子所在孔位上不同，因而两两字面不同。[规范编译卷命题 4.3 的树替换单射性](https://github.com/the-omega-institute/trureturing/blob/3b7e298150f95ea135afc222e230c614d03c02e1/docs/develop/theory/FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)经三次复合仍单射，给四个像的不同性和前像唯一性。该命题的字面树结论与其组成逆公式分别使用。

$u_0,v_0$ 各有两片 $\alpha$ 和一片 $\beta$，所以四个前像均有 $7$ 片 $\alpha$、$3$ 片 $\beta$。命题 23.3 已给 $c(A)=(1,2)^{\mathsf T}$、$c(U)=c(V)=(4,7)^{\mathsf T}$。各行有一个 $A$、三个 $U/V$，由[母卷定义 3.3、定理 3.4 的组成加性与替换作用](https://github.com/the-omega-institute/trureturing/blob/3b7e298150f95ea135afc222e230c614d03c02e1/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#3-fibonacci-替换与组成动力学)，有

$$
(1,2)^{\mathsf T}+3(4,7)^{\mathsf T}=(13,23)^{\mathsf T},
\qquad 13+23=36,
\qquad 2\cdot13+3\cdot23=95.
\tag{25.20}
$$

最后一式使用定义 1.1 的数量读数。这些都是固定完整原型的静态计算，不是未知来源运行中免费取得的组成、数量或叶数报告。

为核对式（25.16），$A$ 的两片左叶来自 $E$，右叶为 $\beta$。$C=\langle A,E\rangle$ 的全部叶为 $\mathtt{LLL}:\beta$、$\mathtt{LLR}:\alpha$、$\mathtt{LR}:\beta$、$\mathtt{RL}:\beta$、$\mathtt{RR}:\alpha$。$U$ 在孔位 $\mathtt{LL},\mathtt{LR},\mathtt R$ 分别放入 $A,A,C$，$V$ 在这三个孔位分别放入 $A,C,A$；将这些完整前沿逐一加上相应前缀，恰得到式（25.16）的每一项，分别共 $3,11,11$ 项。四孔上下文的全部叶均位于四个互不为前缀的 $p_h$ 下，所以其带标签前沿正是式（25.17）的不交并，没有省略的子树。

$t=\mathtt{LRLR}$ 在 $A$ 上先到 $\mathtt{LR}$ 的 $\alpha$ 叶，再越过该叶，故响应为不存在；在 $U,V$ 上的响应分别是 $\alpha,\beta$ 叶，这两项直接复用命题 23.3 的式（23.11），也由式（25.16）给出。将这三个局部响应按式（25.14）放入每个孔，便逐项给出式（25.18）。省去 $P_j$ 后，第 $j$ 行的三个剩余响应含一个 $\beta$ 叶和两个 $\alpha$ 叶，故 $q_j\in\Delta(F_4\setminus\{P_j\})$。六个二元子族 $(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)$ 分别在 $q_4,q_2,q_3,q_1,q_1,q_2$ 上有相反叶标签；因此所有真非单元素子族都满足定理 25.2 的分离条件，各三元族相容。

四重叶交集必须检查全部地址。由式（25.12），$U,V$ 在 $A$ 的全部三个叶地址 $\mathtt{LL},\mathtt{LR},\mathtt R$ 上均为分支，故 $L(A)\cap L(U)=L(A)\cap L(V)=\varnothing$。每个孔位 $p_h$ 在四个目标中恰有一个 $A$ 和三个 $U/V$，所以该孔位内不可能有四者共同叶。其余可能的节点只有上下文祖先 $\varepsilon,\mathtt L,\mathtt R$，均为分支；所有叶均由式（25.17）覆盖。因而四重叶交集为空，$\Delta(F_4)$ 也为空。定理 25.2 或推论 25.3 遂给四元不相容，得到式（25.19）及全部取得结论。证毕。

**定理 25.6（同一策略联合费用下界与循环端点锐值）。** 对定义 25.4 的 $F_4$，存在四个 $\pi_j\in\mathfrak D_3$，满足

$$
C_{\pi_j}(P_i)=36+\mathbf1_{\{i=j\}},
\qquad
\bigl(C_{\pi_j}(P_1),\ldots,C_{\pi_j}(P_4)\bigr)=
\begin{cases}
(37,36,36,36),&j=1,\\
(36,37,36,36),&j=2,\\
(36,36,37,36),&j=3,\\
(36,36,36,37),&j=4.
\end{cases}
\tag{25.21}
$$

每个 $\pi\in\mathfrak D_3$ 和每个 $\Pi\in\mathfrak R_3$ 分别有

$$
\sum_{i=1}^4C_\pi(P_i)\ge145,
\qquad
\sum_{i=1}^4\mathbb E_\mu C_\Pi(\cdot,P_i)\ge145.
\tag{25.22}
$$

因此两个优化值均达到，且精确为

$$
\boxed{\qquad D_3^+(F_4)=37,
\qquad R_3^+(F_4)=\frac{145}{4}.\qquad}
\tag{25.23}
$$

均匀选取 $j\in\{1,2,3,4\}$ 并运行 $\pi_j$ 的共同输入无关混合，使每个固定 $P_i$ 的期望为 $145/4$；对这个混合，另一个量 $\mathbb E_\mu\max_i C_\Pi(\cdot,P_i)$ 等于 $37$。

**证明。** 固定 $j$，先查询 $q_j$。若为 $\mathsf{absent}$，暂定原型为 $P_j$；若为 $\mathsf{leaf}_\beta$，暂定为 $P_{j+1}$；若为 $\mathsf{leaf}_\alpha$，再查询 $q_{j+1}$，第二响应为 $\mathsf{leaf}_\beta$ 时暂定为 $P_{j+2}$，为 $\mathsf{leaf}_\alpha$ 时暂定为 $P_{j+3}$。第一响应为分支，或第二响应为分支、不存在时，直接进入定理 23.2 已证的全域后备。选中原型后核对式（25.17）的全部带标签叶，复用缓存；任何不匹配进入同一后备，完整匹配才接受。

定理 18.2 的完整叶充分性保证这里的接受正确。路由至多两次，原型核对只有有限片叶，后备对实际有限来源全域正确且有限终止，所以这些 $\pi_j$ 都属于 $\mathfrak D_3$。不存在响应只用于暂定选择，不承担身份或正性结论；原型之外的正来源和负来源都由完整核对或已有后备处理。

在 $P_j$ 上，式（25.18）使首响应为不存在，$q_j\notin L(P_j)$；核对仍需全部 $36$ 片叶，费用为 $37$。在 $P_{j+1}$ 上首响应为 $\beta$ 叶，首查询已经属于其完整叶前沿，费用为 $36$。在 $P_{j+2},P_{j+3}$ 上首响应均为 $\alpha$ 叶，第二响应分别为 $\beta,\alpha$ 叶；两个查询位于不同孔，地址不同且均属于相应来源的叶，完整核对复用二者，费用仍为 $36$。每个评价来源都暂定选中自己且全部核对匹配，故没有进入后备，得到式（25.21）。特别地，$\pi_j$ 对省去 $P_j$ 的三元族同时取得所有个体最小值。

现固定任意一个 $\pi\in\mathfrak D_3$。它必须在有限内部计算后作首查询。否则，无查询的有限返回在共同初始化下对所有输入相同，不能同时正确处理 $A=\rho^3(\alpha)\in\mathcal I_3$ 与 $\alpha\notin\mathcal I_3$；后一个负性直接取自规范编译卷命题 4.3 的 $\alpha\notin\rho(\mathcal T)$。无查询而永久内部计算又违反全域有限终止。于是首地址 $s$ 在四个目标上相同，且是首次计费地址。

式（25.19）的四重叶交集为空，故 $s\notin L(P_i)$ 至少对一个 $i$ 成立。另一方面，四个接受运行均满足定理 23.2 证明中的式（23.6）：其不同地址集 $J_i$ 包含全部 $36$ 个必查叶，同时 $s\in J_i$。至少一个运行额外计一个叶外地址，故

$$
\sum_{i=1}^4C_\pi(P_i)\ge4\cdot36+1=145,
\qquad \max_i C_\pi(P_i)\ge37.
\tag{25.24}
$$

这是一项对同一策略四个实际运行的联合不等式，允许全部自适应后续和任意长地址，不是四个分别优化的三元族不等式之和。式（25.21）的任一端点策略取得最大费用 $37$，给确定性锐值。

固定 $\Pi\in\mathfrak R_3$。与定理 25.2 的证明相同，母卷定理 9.2 给全来源可数；先应用定理 22.1 的有声返回式（22.4），再另行应用其共同总性式（22.7），得到该 $\Pi$ 的可测满测度集 $G_\Pi^{\mathrm{tot}}$。每个 $\omega$ 在这个集合上给一个属于 $\mathfrak D_3$ 的固定种子策略，所以式（25.24）的同策略和下界逐种子成立。可测非负扩展费用的有限和允许积分相加，包括无穷期望，得到

$$
\sum_{i=1}^4\mathbb E_\mu C_\Pi(\cdot,P_i)
=\int_\Omega\sum_{i=1}^4 C_\Pi(\omega,P_i)\,d\mu(\omega)
\ge145,
\qquad
\max_i\mathbb E_\mu C_\Pi(\cdot,P_i)\ge\frac{145}{4}.
\tag{25.25}
$$

例外零测种子不改变非负积分下界；这里仍只对一个固定 $\Pi$ 取共同种子集。

最后，取一次输入无关的均匀四元种子，选择式（25.21）的四个策略。每个声明种子都已全域正确且有限终止，有限种子空间使全部所需事件与费用可测，所以此混合属于 $\mathfrak R_3$。每个固定 $P_i$ 恰在一个种子上费用为 $37$、三个种子上费用为 $36$，于是

$$
\mathbb E_\mu C_\Pi(\cdot,P_i)
=\frac{37+36+36+36}{4}=\frac{145}{4}\quad(1\le i\le4),
\qquad
\mathbb E_\mu\max_i C_\Pi(\cdot,P_i)=37.
\tag{25.26}
$$

结合式（25.25）得到随机锐值、取得性及式（25.22）、（25.23）的全部结论。所有量仅涉及指定实际四族及定义 25.1 的全域接口，不推出任意四来源的锐值分类、最小见证规模、一般遗传模式的实际替换实现或物理逆操作。证毕。

## 追加锚（本行以下为增补区）

## 26. 同组成实际三步像的有限遗传相容模式与无统一 Helly 阶数

**定义 26.1（全域合同、指标信息叶与全孔上下文）。** 固定[定义 25.1](#25-有限正来源族的遗传共享叶分离与四元共同费用)的全部合同：未知输入为所有非空有限自由有序满二叉 $\alpha/\beta$ 树组成的 $\mathcal T$，$d=3$，$\mathcal I_3=\rho^3(\mathcal T)$，目标为 $\iota_3(T)=\mathbf1_{\{T\in\mathcal I_3\}}$。树的次序、括号和标签均保留。所有有限左右地址，包括空地址 $\varepsilon$，均合法；查询只报告同一不变来源的原始 $\mathsf{leaf}_\alpha$、$\mathsf{leaf}_\beta$、$\mathsf{branch}$ 或 $\mathsf{absent}$。费用只计缓存后的不同地址，未有限终止时为 $+\infty$。地址长度、定位、计算和种子取得沿用原费用约定；地址查询无须先查询其前缀。

$\mathfrak D_3$ 中每个策略在整个 $\mathcal T$ 上正确且有限终止。$\mathfrak R_3$ 中每个策略带有一个输入无关的可测种子律，满足同种子重放、逐来源几乎处处正确且有限终止，以及非负扩展费用可测。每个策略的完整初始化与实际输入无关，可包含固定的完整评价原型，作为取得费用的设计资料；这不承诺输入的正性、身份、组成、叶数、深度或所属子族，也不产生额外免费来源报告。对子族共同取得费用，必须使用同一个全域策略；随机情形同时固定它的同一个种子律，分别计算每个实际来源上的期望，不给来源先验，也不把这些期望换成期望最大费用。接受仍须完成[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)的全部带标签叶证书，原型不匹配仍由[定理 23.2](#23-全有限来源上两个指定正例的共同最优地址费用)已有的全域有限后备处理。

设 $\boldsymbol P=(P_1,\ldots,P_m)$ 是一个有限指标树族。对非空 $S\subseteq[m]=\{1,\ldots,m\}$，定义

$$
\Delta_{\boldsymbol P}(S)=
\left\{w\in\bigcap_{i\in S}L(P_i):
\{\lambda_{P_i}(w):i\in S\}=\{\alpha,\beta\}\right\}.
\tag{26.1}
$$

该式允许不同指标对应同一棵树。若 $P_i$ 两两不同且 $|S|\ge2$，它就是定义 25.1 的 $\Delta(P_S)$，其中 $P_S=\{P_i:i\in S\}$；单元素指标集的信息叶集为空。

直接沿用[命题 23.3 的式（23.9）、（23.10）、（23.15）](#23-全有限来源上两个指定正例的共同最优地址费用)及[定义 25.4](#25-有限正来源族的遗传共享叶分离与四元共同费用)的完整块和前像：

$$
\begin{gathered}
E=\langle\beta,\alpha\rangle,\quad
A=\langle E,\beta\rangle=\rho^3(\alpha),\quad
C=\langle A,E\rangle=\rho^3(\beta),\\
u_0=\langle\langle\alpha,\alpha\rangle,\beta\rangle,
\qquad v_0=\langle\langle\alpha,\beta\rangle,\alpha\rangle,\\
U=\langle\langle A,A\rangle,C\rangle=\rho^3(u_0),
\qquad V=\langle\langle A,C\rangle,A\rangle=\rho^3(v_0),\\
c(A)=(1,2)^{\mathsf T},\qquad c(U)=c(V)=(4,7)^{\mathsf T}.
\end{gathered}
\tag{26.2}
$$

[定理 25.5 的完整前沿式（25.16）](#25-有限正来源族的遗传共享叶分离与四元共同费用)供应

$$
L(A)\cap L(U)=L(A)\cap L(V)=\varnothing,
\qquad
D:=\Delta(\{U,V\})\ni t:=\mathtt{LRLR}.
\tag{26.3}
$$

同一既有前沿给 $U,V$ 在 $A$ 的三个叶地址 $\mathtt{LL},\mathtt{LR},\mathtt R$ 上均为分支，且

$$
\bigl(\operatorname{out}_A(t),\operatorname{out}_U(t),
\operatorname{out}_V(t)\bigr)
=(\mathsf{absent},\mathsf{leaf}_\alpha,\mathsf{leaf}_\beta).
\tag{26.4}
$$

对整数 $T\ge1$，定义每片叶都是孔的有序满二叉上下文

$$
\begin{aligned}
B_1(x_1)&=x_1,\\
B_T(x_1,\ldots,x_T)&=
\langle x_1,B_{T-1}(x_2,\ldots,x_T)\rangle\quad(T\ge2).
\end{aligned}
\tag{26.5}
$$

孔按叶序编号，地址记为 $p_1,\ldots,p_T$。$T=1$ 时 $p_1=\varepsilon$；$T\ge2$ 时 $p_j=\mathtt R^{j-1}\mathtt L$（$j<T$），$p_T=\mathtt R^{T-1}$。上下文没有孔以外的字面叶。记 $pD=\{pw:w\in D\}$，$p\prec w$ 表示 $p$ 是 $w$ 的真前缀。

**引理 26.2（任意块表的全部地址报告与信息叶恒等式）。** 给定整数 $m,T\ge1$ 和任意表 $X_{ij}\in\{A,U,V\}$，令 $P_i=B_T(X_{i1},\ldots,X_{iT})$。对每个有限地址 $w$，原始四值报告精确为

$$
\operatorname{out}_{P_i}(w)=
\begin{cases}
\mathsf{branch},&w\prec p_j\text{ 对某个 }j,\\
\operatorname{out}_{X_{ij}}(v),&w=p_jv\text{ 对唯一的 }j.
\end{cases}
\tag{26.6}
$$

两种情形互斥且穷尽。对每个 $S\subseteq[m]$、$|S|\ge2$，有精确不交并

$$
\boxed{\quad
\Delta_{\boldsymbol P}(S)=
\bigsqcup_{\substack{1\le j\le T\\
\{X_{ij}:i\in S\}=\{U,V\}}}p_jD.
\quad}
\tag{26.7}
$$

因此，信息叶非空当且仅当某列在 $S$ 上同时出现 $U,V$ 且不出现 $A$。

**证明。** 上下文的孔地址前缀自由。沿任意有限词 $w$ 从根下降，或者该词在上下文内节点处结束，或者经过唯一一个孔 $p_j$ 后继续读取残词 $v$。上下文有限且满二叉，所以没有未到孔便离开上下文的第三种路径。前一种情形等价于 $w$ 是某个孔的真前缀，且该节点在全部 $P_i$ 中均为分支。后一种情形恰读取已填入的 $X_{ij}$：它包含残词为空时的块根报告，也包含越过块叶之后的不存在报告。这证明式（26.6），包括空地址与所有任意长地址。

特别地，各行的全部带标签叶前沿为

$$
\mathcal F(P_i)=
\bigsqcup_{j=1}^T
\{(p_jv,\ell):(v,\ell)\in\mathcal F(X_{ij})\}.
\tag{26.8}
$$

若 $w$ 是全部 $i\in S$ 的共同叶，它不能是上下文内节点。式（26.6）及孔地址的唯一性使它在每一行都位于同一个孔 $p_j$ 下；残词 $v$ 必为该列全部块的共同叶。由此逐列检查即可穷尽全部共同叶，没有跨孔拼接产生的叶。

一列在 $S$ 上只有一种块时，所有共同叶的标签都相同，故无信息叶。一列同时含 $A$ 和 $U$ 或 $V$ 时，式（26.3）的叶地址不交关系使它没有共同叶。其余可能的非恒定列恰含 $U,V$ 而不含 $A$，共同叶中标签不同的残词正是 $D$，其贡献为 $p_jD$。这些情况穷尽三种块的所有列模式。不同孔的贡献不交，得到式（26.7）；再用 $t\in D$，得到非空性的充要条件。证毕。

**定理 26.3（面表、无信息补齐与同组成完整前像）。** 设 $m\ge2$，$K\subseteq2^{[m]}$ 下闭且包含每个单元素集：

$$
S\in K,\ R\subseteq S\Longrightarrow R\in K,
\qquad \{i\}\in K\quad(1\le i\le m).
\tag{26.9}
$$

令 $\mathcal M(K)$ 为 $K$ 的全部极大面。它们非空且覆盖 $[m]$。对每个 $F\in\mathcal M(K)$ 和 $k\in F$，建立一列 $(F,k)$，在行 $i$ 填入

$$
X_{i,(F,k)}=
\begin{cases}
V,&i=k,\\
U,&i\in F\setminus\{k\},\\
A,&i\notin F.
\end{cases}
\tag{26.10}
$$

置

$$
N=\sum_{F\in\mathcal M(K)}|F|,
\qquad
\ell_i=\sum_{\substack{F\in\mathcal M(K)\\i\in F}}|F|,
\qquad M=\max_{1\le i\le m}\ell_i.
\tag{26.11}
$$

对每个行 $i$，再添加 $M-\ell_i$ 个分别属于该行的列；每个这样的列只在行 $i$ 填 $U$，其余行全部填 $A$。最终列数为

$$
T=N+\sum_{i=1}^m(M-\ell_i)\ge1.
\tag{26.12}
$$

固定全部列的一个次序，在同一个 $B_T$ 中填入最终表，得到 $P_i$。同时把表中 $A,U,V$ 分别换成 $\alpha,u_0,v_0$，记所得条目为 $Z_{ij}$，并定义完整树

$$
Q_i=B_T(Z_{i1},\ldots,Z_{iT}).
\tag{26.13}
$$

则 $Q_1,\ldots,Q_m$ 两两不同，$P_1,\ldots,P_m$ 也两两不同，各 $Q_i$ 是 $P_i$ 的唯一完整三步前像，且

$$
\begin{aligned}
\rho^3(Q_i)&=P_i\in\mathcal I_3,\\
c(Q_i)&=(T+M,M)^{\mathsf T},\\
c(P_i)&=(T+3M,2T+5M)^{\mathsf T},
\qquad n_{P_i}=3T+8M.
\end{aligned}
\tag{26.14}
$$

对每个 $S\subseteq[m]$、$|S|\ge2$，还同时有

$$
\boxed{\quad \Delta(P_S)\ne\varnothing\ \Longleftrightarrow\ S\in K.\quad}
\tag{26.15}
$$

**证明。** 因 $K$ 有限且含每个 $\{i\}$，每个面包含于一个极大面，每个指标属于一个极大面；空面不可能极大。因此式（26.10）的原始列存在，$N\ge m$，各 $\ell_i\ge1$。固定 $S$ 且 $|S|\ge2$。若 $S\in K$，取极大面 $F\supseteq S$ 和 $k\in S$。列 $(F,k)$ 在行 $k$ 为 $V$，在其余 $S$ 行为 $U$，因此由引理 26.2 提供非空的信息叶贡献。

若 $S\notin K$，没有极大面包含 $S$，否则下闭性会给 $S\in K$。故对每一原始列 $(F,k)$，$S$ 上至少出现一个 $A$：$S\cap F=\varnothing$ 时全部是 $A$，$S\cap F\ne\varnothing$ 时同时出现 $A$ 和非 $A$ 块。两种情况在式（26.7）中均无贡献。原始列遂恰编码所有非单元素面。

再固定一个属于行 $i$ 的补齐列。若 $i\notin S$，该列在 $S$ 上恒为 $A$；若 $i\in S$，因 $|S|\ge2$，它在 $S$ 上同时出现 $U,A$。故每个补齐列在每个非单元素 $S$ 上的信息叶贡献都为空。全部列一次填入最终的 $B_T$ 后，原始列保留其局部块关系，孔地址由这个最终上下文统一确定。引理 26.2 排除了补齐后产生跨列或上下文共同信息叶的可能，原始列所得非空性等价关系因而仍成立。

每行原有 $\ell_i$ 个非 $A$ 块，又在自己的补齐列增加 $M-\ell_i$ 个 $U$，别人的补齐列在该行都是 $A$。于是最终每行恰有 $M$ 个 $U/V$ 和 $T-M$ 个 $A$。由式（26.2）及[母卷定义 3.3、定理 3.4 的组成加性与替换作用](FIBONACCI_ATOMIC_RELATION_GENERATION.md#3-fibonacci-替换与组成动力学)，有

$$
\begin{aligned}
c(P_i)&=(T-M)(1,2)^{\mathsf T}+M(4,7)^{\mathsf T}
=(T+3M,2T+5M)^{\mathsf T},\\
c(Q_i)&=(T-M)(1,0)^{\mathsf T}+M(2,1)^{\mathsf T}
=(T+M,M)^{\mathsf T}.
\end{aligned}
\tag{26.16}
$$

相加像的两个组成坐标即得 $n_{P_i}=3T+8M$。这些计数是指定完整树的构造读数，不是未知输入的初始化承诺。

$\rho^3$ 保持每个二叉构造；式（26.2）已给三个块的字面前像。因此将式（26.13）的每个孔分别替换，直接得到

$$
\rho^3(Q_i)
=B_T\bigl(\rho^3(Z_{i1}),\ldots,\rho^3(Z_{iT})\bigr)
=B_T(X_{i1},\ldots,X_{iT})=P_i.
\tag{26.17}
$$

这是完整实际树的等式。对 $i\ne j$，选一个含 $i$ 的极大面 $F$。原始列 $(F,i)$ 在行 $i$ 是 $V$，在行 $j$ 则为 $U$ 或 $A$；对应前像在同一个孔分别为 $v_0$ 和 $u_0$ 或 $\alpha$。三个前像字面不同，固定上下文的该孔子树不同就使完整树不同，所以 $Q_i\ne Q_j$。添加列保留了此原始列，不能消去这处差别。

直接调用[规范编译卷命题 4.3 的树替换单射性](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)三次，得到 $\rho^3$ 单射、$P_i\ne P_j$，并得到式（26.13）前像的唯一性；该卷原子 $A,B$ 在这里分别对应 $\alpha,\beta$。此调用使用字面树的单射结论，组成逆公式不承担实际前像存在性。最终各行不同，使式（26.7）的指标信息叶就是 $\Delta(P_S)$，故此前的非空性等价给式（26.15）。证毕。

**定理 26.4（全部有限遗传相容模式的精确实际实现）。** 在定义 26.1 的全来源合同下，对每个 $m\ge2$ 和每个满足式（26.9）的 $K$，存在定理 26.3 的两两不同同组成完整树 $Q_i$ 及两两不同同组成正来源 $P_i=\rho^3(Q_i)$，使对每个 $S\subseteq[m]$，

$$
\boxed{
\begin{aligned}
S\in K
&\ \Longleftrightarrow\quad
\exists\pi\in\mathfrak D_3\ \forall i\in S:
C_\pi(P_i)=n_{P_i}\\
&\ \Longleftrightarrow\quad
\exists\Pi\in\mathfrak R_3\ \forall i\in S:
\mathbb E_\mu C_\Pi(\cdot,P_i)=n_{P_i}.
\end{aligned}}
\tag{26.18}
$$

反之，每个由有限个不同正来源的共同个体最优取得所定义的指标相容族，必下闭且包含空集和所有单元素集。因此，在此实际同组成接口中，这些条件完整刻画有限相容模式。

**证明。** 对 $|S|\ge2$，直接应用[定理 25.2](#25-有限正来源族的遗传共享叶分离与四元共同费用)，其确定性和期望相容都等价于

$$
\forall R\subseteq S,\quad |R|\ge2\Longrightarrow\Delta(P_R)\ne\varnothing.
\tag{26.19}
$$

定理 26.3 将每个这样的非空信息叶条件精确换成 $R\in K$。若 $S\in K$，下闭性给全部这些 $R\in K$；若 $S\notin K$，取 $R=S$ 即使条件失败。这证明非单元素子族的式（26.18）。这里调用的是既有相容定理的完整结论：它的取得策略在路由结束后补齐全部带标签叶，并在路由响应不是叶或核对不匹配时使用定理 23.2 的全域有限后备。因此这些策略仍处理全部 $\mathcal T$，并未因表的行数有限而缩减实际相容来源域。

此随机等价的前提亦保持原范围：[母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)供应全树域的单射有限词编码，母卷定理 9.3 与定理 18.2 供应完整叶恢复；定理 25.2 的随机论证分别使用[定理 22.1 的有声返回式（22.4）与另行要求总性的式（22.7）](#22-可数只读记录的有声返回与终止精确探针许可的分界)。其中共同满测度种子集属于一个固定随机策略，依赖该策略；没有覆盖所有策略的共同通用种子，也没有从有声返回单独推出全域终止。式（26.18）直接复用该结论及其前提，不另作种子交换或输入平均。

$S=\{i\}$ 时，定理 18.2 在 $d=3=3\cdot1$ 的范围内已给个体叶最小值及完整证书；采用定理 23.2 的单原型核对及已有后备即取得 $n_{P_i}$。这是既有个体结果的应用。确定性策略以单点种子律也属于 $\mathfrak R_3$，故期望同样取得。$S=\varnothing$ 时，全域有限后备本身给 $\mathfrak D_3\ne\varnothing$，其单点种子策略给 $\mathfrak R_3\ne\varnothing$，空约束也取得。式（26.9）本已使这些 $S$ 属于 $K$，从而涵盖所有子集。

反向，固定任意有限个不同正来源。某个策略在一族上取得所有个体最优时，将评价指标限制到任一子族，仍由同一个策略满足原全域合同且取得对应费用；随机情形连种子律也保持同一个。因此两种指标相容族都下闭。既有个体取得与全域后备使所有单元素集和空集在其中，而定理 25.2 使两种族一致。定理 26.3 与式（26.18）已经在同组成实际三步像中实现每个满足这些必要条件的 $K$，所以没有更多有限模式限制。共同组成为式（26.14）给出的每次构造的一个组成，允许随 $K,m$ 改变。证毕。

**定义 26.5（固定策略空间中的个体最优集合与 Helly 阶数）。** 对每个 $P\in\mathcal I_3$，在固定的全域确定性策略空间中定义

$$
\mathcal O(P)=\{\pi\in\mathfrak D_3:C_\pi(P)=n_P\}.
\tag{26.20}
$$

还固定一次种子概率空间

$$
(\Omega_{\mathrm u},\mathcal A_{\mathrm u},\mu_{\mathrm u})
=([0,1],\mathcal L,\operatorname{Leb}),
\tag{26.21}
$$

其中 $\mathcal L$ 为 Lebesgue 可测集。以 $\mathfrak R_3^{\mathrm u}$ 记恰在这个空间与种子律上满足定义 25.1 的随机策略集合，并定义

$$
\mathcal O_{\mathrm u}(P)=
\{\Pi\in\mathfrak R_3^{\mathrm u}:
\mathbb E_{\mu_{\mathrm u}}C_\Pi(\cdot,P)=n_P\}.
\tag{26.22}
$$

$\mathfrak R_3^{\mathrm u}$ 是指定种子空间的策略类；这里只按其合同将每个元素视为 $\mathfrak R_3$ 中的一个随机策略，不把不同种子空间与种子律的控制器相互识别。两个固定空间均由已有后备非空，每个上述个体最优集合也非空；确定性个体取得策略在固定均匀种子上作常值提升即可供应后一结论。空交分别解释为 $\mathfrak D_3$ 和 $\mathfrak R_3^{\mathrm u}$。

对任一固定空间中的集合系统，称整数 $h\ge1$ 是其有限 Helly 阶数，若每个有限子系统在所有至多 $h$ 个集合的交都非空时，全体交必非空。此处只比较集合系统 $\{\mathcal O(P):P\in\mathcal I_3\}$ 或 $\{\mathcal O_{\mathrm u}(P):P\in\mathcal I_3\}$；同组成限定表示每个被检验的有限来源族内部有一个共同组成。

**定理 26.6（任意规模的实际极小不相容族与无统一有限 Helly 阶数）。** 对每个 $m\ge2$，取

$$
K_m=2^{[m]}\setminus\{[m]\}.
\tag{26.23}
$$

用有序对 $(r,k)$、$r\ne k$ 编号各列，在行 $i$ 置

$$
X_{i,(r,k)}=
\begin{cases}
A,&i=r,\\
V,&i=k,\\
U,&i\notin\{r,k\}.
\end{cases}
\tag{26.24}
$$

固定列的一个次序，以 $p_{(r,k)}$ 记列 $(r,k)$ 的孔地址。在一个共同的 $B_T$ 中填入该表，并按式（26.13）构造完整前像，则得到两两不同的实际正来源 $P_1,\ldots,P_m$。无需补齐，各行的共同构造读数为

$$
\begin{aligned}
T&=m(m-1),\qquad M=(m-1)^2,\\
c(Q_i)&=\bigl((m-1)(2m-1),(m-1)^2\bigr)^{\mathsf T},\\
c(P_i)&=(m-1)(4m-3,7m-5)^{\mathsf T},\\
n_{P_i}&=(m-1)(11m-8).
\end{aligned}
\tag{26.25}
$$

在两个分别固定的策略空间中，同时有

$$
\begin{aligned}
\bigcap_{i\in S}\mathcal O(P_i)\ne\varnothing
&\ \Longleftrightarrow\ S\subsetneq[m],\\
\bigcap_{i\in S}\mathcal O_{\mathrm u}(P_i)\ne\varnothing
&\ \Longleftrightarrow\ S\subsetneq[m]
\qquad(S\subseteq[m]).
\end{aligned}
\tag{26.26}
$$

故每个规模 $m$ 都有实际同组成的极小不相容族：全部真子族取得各自全部个体最优，而全族不能取得。两个个体最优集合系统均没有统一有限 Helly 阶数，即使每个检验族均限制为两两不同的同组成正来源。

**证明。** $K_m$ 的极大面恰为 $F_r=[m]\setminus\{r\}$。式（26.24）是定理 26.3 的列 $(F_r,k)$ 的完整展开，各面有 $m-1$ 个指标，故列数为 $m(m-1)$。对固定行 $i$，$r=i$ 的 $m-1$ 列为 $A$，其余 $(m-1)^2$ 列均为 $U/V$，于是所有 $\ell_i$ 已等于 $M$。代入式（26.14）得到式（26.25）；完整前像、字面不同性及实际正性均由定理 26.3 直接供应。这些数值是该具体构造的组成与叶数，没有最小规模断言。

也可从全部地址恒等式直接读出此表的障碍。固定真非单元素 $S\subsetneq[m]$，选 $r\notin S$ 和 $k\in S$。列 $(r,k)$ 在 $S$ 上含一个 $V$ 和其余 $U$，所以 $p_{(r,k)}t\in\Delta(P_S)$。在全族上，每列既有行 $r$ 的 $A$，又有行 $k$ 的 $V$。式（26.3）与引理 26.2 的完整孔分解遂给

$$
\Delta(P_S)\ne\varnothing\quad(2\le|S|<m),
\qquad
\bigcap_{i=1}^mL(P_i)=\varnothing,
\qquad \Delta(P_{[m]})=\varnothing.
\tag{26.27}
$$

$m=2$ 时第一个范围为空，但每列的 $A,V$ 叶不交仍给后两个结论。定理 26.4，包括其单元素与空族结论，给式（26.26）的确定性等价。

更一般地，对定理 26.3 实现的任意 $K$，式（26.18）直接给

$$
\bigcap_{i\in S}\mathcal O(P_i)\ne\varnothing
\ \Longleftrightarrow\ S\in K.
\tag{26.28}
$$

若此确定性交非空，固定其中一个 $\pi$，在式（26.21）的种子空间上定义对所有 $\omega$ 都运行 $\pi$ 的常值策略。它在全部输入上正确且有限终止，各来源费用是种子的常值可测函数，故属于 $\mathfrak R_3^{\mathrm u}$，并同时取得该子族全部期望最优。反之，若 $\mathfrak R_3^{\mathrm u}$ 中某策略同时取得这些期望，它也是定义 25.1 合同下的一个 $\mathfrak R_3$ 策略，定理 25.2 已保证确定性相容，遂有同一个确定性策略取得全部对应个体最优。因此在固定均匀种子空间内也有

$$
\bigcap_{i\in S}\mathcal O_{\mathrm u}(P_i)\ne\varnothing
\ \Longleftrightarrow\ S\in K.
\tag{26.29}
$$

此论证不迁移或识别任何其他种子律；全族不可取得对所有原合同随机策略成立，而真子族的取得已在一个预先固定的均匀种子空间内完成。取 $K=K_m$ 即得式（26.26）的第二行。

现在任给候选阶数 $h\ge1$，取 $m=h+1$。在这 $m$ 个非空个体最优集合中，每个至多 $h$ 个集合的交都对应真子集，因此非空；全部 $m$ 个的交为空。这同时反驳两个固定空间各自的 $h$ 阶 Helly 性。每个 $h$ 都被实际同组成且不同的有限正来源族反驳，故没有统一有限阶数。共同组成随 $m$ 按式（26.25）变化；固定一个组成时，叶数固定，有序满二叉形状和叶标记只有有限种，因此本结论的量词不要求在一个对所有 $m$ 通用的固定组成内实现无界规模。整个结论只涉及 $d=3$ 下共同取得个体叶最优的交模式。证毕。

## 追加锚（本行以下为增补区）

## 27. 实际三步像的面费用核心与分数面覆盖锐值

**定义 27.1（指定私有列的完整表与原费用合同）。** 沿用[定义 26.1](#26-同组成实际三步像的有限遗传相容模式与无统一-helly-阶数)的全部来源和策略合同。未知输入遍历所有非空有限自由有序满二叉 $\alpha/\beta$ 树 $\mathcal T$，目标是 $\iota_3(W)=\mathbf1_{\{W\in\rho^3(\mathcal T)\}}$；每个有限左右地址都可直接查询，报告仍是同一不变来源的四个原始值，费用仍只计缓存后的不同地址。$\mathfrak D_3$ 要求每个有限输入都正确且有限终止；$\mathfrak R_3$ 要求一个输入无关的种子律、同种子重放、逐来源可测的零测错误及未终止事件，以及可测非负扩展费用。$\mathfrak R_3^{\mathrm u}$ 恰使用式（26.21）已经固定的 $([0,1],\mathcal L,\operatorname{Leb})$，不把其他种子空间或种子律与它识别。

固定整数 $m\ge2$ 和满足式（26.9）的有限下闭族 $K\subseteq2^{[m]}$。取定理 26.3 已完成补齐的表 $X^0=(X^0_{ij})$，其列数和每行非 $A$ 块数分别记为 $T_0,M_0$。全部块 $A,U,V$ 及其字面前像 $\alpha,u_0,v_0$ 直接取式（26.2），不另改块的树语法。固定原列次序，再在末尾对每个 $r\in[m]$ 添加恰一个指定列 $g_r=T_0+r$。置

$$
T=T_0+m,\qquad H=M_0+1,\qquad n_0=3T_0+8M_0.
\tag{27.1}
$$

最终的整个 $m\times T$ 表定义为

$$
X_{ij}=X^0_{ij}\quad(1\le j\le T_0),\qquad
X_{i,g_r}=\begin{cases}U,&i=r,\\ A,&i\ne r.\end{cases}
\tag{27.2}
$$

只使用一个最终上下文 $B_T$。所有原列和新列的孔地址都按这个 $B_T$ 重新确定；以前 $B_{T_0}$ 的最后一孔地址不能沿用。令 $Z_{ij}$ 是将最终表中的 $A,U,V$ 分别换成 $\alpha,u_0,v_0$ 的条目，定义

$$
\begin{gathered}
p_j=\mathtt R^{j-1}\mathtt L\quad(1\le j<T),\qquad
p_T=\mathtt R^{T-1},\\
Q_i=B_T(Z_{i1},\ldots,Z_{iT}),\qquad
P_i=B_T(X_{i1},\ldots,X_{iT})\quad(i\in[m]).
\end{gathered}
\tag{27.3}
$$

这里给的是实际完整前像和像的描述。初始化可含固定的 $K$、最终表、原型和策略，仍不含未知输入的身份、正性、组成、大小、高度或所属子族承诺。以下最大值只在非空评价指标集 $[m]$ 上取；空评价指标集没有这里的最大费用目标。

**定理 27.2（私有列保留相容模式并提供一个叶外分支）。** 定义 27.1 的 $Q_i$ 两两不同且同组成，$P_i$ 两两不同且同组成；$Q_i$ 是 $P_i$ 的唯一完整三步前像。其共同组成和共同叶数为

$$
\begin{aligned}
\rho^3(Q_i)&=P_i\in\mathcal I_3,\\
c(Q_i)&=(T+H,H)^{\mathsf T},\\
c(P_i)&=(T+3H,2T+5H)^{\mathsf T},\\
n:=|L(P_i)|&=3T+8H=n_0+3m+8.
\end{aligned}
\tag{27.4}
$$

对每个 $S\subseteq[m]$，该最终族满足

$$
\begin{aligned}
|S|\ge2&\ \Longrightarrow\quad
\bigl(\Delta(P_S)\ne\varnothing\ \Longleftrightarrow\ S\in K\bigr),\\
S\in K&\ \Longleftrightarrow\quad
\exists\pi\in\mathfrak D_3\ \forall i\in S:\ C_\pi(P_i)=n.
\end{aligned}
\tag{27.5}
$$

在指定地址 $a_r=p_{g_r}\mathtt{LL}$ 上，有

$$
\operatorname{out}_{P_i}(a_r)=
\begin{cases}
\mathsf{branch},&i=r,\\
\mathsf{leaf}_\beta,&i\ne r,
\end{cases}
\qquad
a_r\notin L(P_r),\quad a_r\in L(P_i)\ (i\ne r).
\tag{27.6}
$$

**证明。** 原表每行恰有 $M_0$ 个 $U/V$ 块。新增 $m$ 列在行 $i$ 中恰贡献一个 $U$ 和 $m-1$ 个 $A$，所以最终每行恰有 $H$ 个 $U/V$ 和 $T-H$ 个 $A$。式（26.2）的块组成及定理 26.3 所调用的组成加性，直接给式（27.4）的两个组成坐标和叶数。$\rho^3$ 保持每个有序二叉构造，且三个条目已有字面前像，故在最终的整个 $B_T$ 中逐孔替换就得到 $\rho^3(Q_i)=P_i$。这不是由组成逆矩阵推断树前像存在。

当 $i\ne j$，指定列 $g_i$ 在行 $i,j$ 的字面前像分别为 $u_0,\alpha$，它们不同；最终上下文的同一个孔子树不同，故 $Q_i\ne Q_j$。直接复用[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的树替换单射性并复合三次，得到 $P_i\ne P_j$ 及完整前像的唯一性。该命题的原子 $A,B$ 在此对应 $\alpha,\beta$，不对应本章作为完整块名字的 $A,U,V$。

固定 $|S|\ge2$。每个新列 $g_r$ 在 $S$ 上或者恒为 $A$，或者含一个 $U$ 和至少一个 $A$。由引理 26.2 的全部孔分解和式（26.7），两种模式均不贡献信息叶。原列的局部模式没有改变；定理 26.3 已证明它们在 $S$ 上贡献非空信息叶的充要条件是 $S\in K$。虽然原孔的完整地址可能改变，引理 26.2 仍在最终 $B_T$ 中排除了跨孔或上下文产生信息叶，故得到式（27.5）的第一行。下闭性再使每个非空面及其全部非单元素子面满足定理 25.2 的遗传条件；反向取子面 $S$ 本身。单元素面用既有单原型完整叶测试，空面用定理 23.2 的全域后备，得到第二行。

最后，式（26.2）给 $A=\langle\langle\beta,\alpha\rangle,\beta\rangle$，故 $\mathtt{LL}$ 在 $A$ 中是 $\beta$ 叶；$U=\langle\langle A,A\rangle,C\rangle$ 的 $\mathtt{LL}$ 子树是分支块 $A$。在最终孔 $p_{g_r}$ 下使用引理 26.2 的原始报告式（26.6）即得式（27.6）。不同孔地址前缀自由，所以全部 $a_r$ 两两不同。新增列对非单元素相容性中性，绝不表示对原始响应信息中性：式（27.6）的分支和叶报告正好区分评价行。证毕。

**引理 27.3（真实缓存供应的独立后续接）。** 设 $\sigma\in\mathfrak D_3$ 是一个固定全域策略。在任意实际 $W\in\mathcal T$ 上先作有限个合法原始查询，得到不同地址集合 $J$ 及其真实缓存。随后给 $\sigma$ 建立它单独运行时的初始化、空逻辑历史和初始控制状态；这个逻辑状态不预填扫描历史，也不把已有缓存当成 $\sigma$ 已执行过的步骤。每当它请求地址 $u$，若外层缓存已有 $u$ 就供应其中的真实报告，否则查询同一 $W$、存入外层缓存并供应报告。将每次请求及所供应报告写入 $\sigma$ 自己的逻辑历史，照它原控制继续。

这样得到的虚拟执行逐步等于 $\sigma$ 从头单独读取 $W$ 的执行，返回值和终止性相同。若 $J_\sigma(W)$ 是该单独执行请求的不同地址集合，则合成执行所付费的不同地址集合恰为

$$
J\cup J_\sigma(W).
\tag{27.7}
$$

此结论也适用于根据有限前缀的报告，从一个固定有限策略菜单中选择后续策略；每种选择都须从被选策略自己的初态开始。

**证明。** 单独执行与虚拟执行在第零步具有相同的 $\sigma$ 初始化、空逻辑历史和控制状态。若它们在某个有限逻辑步骤前相同，内部计算、停止判断和下一查询选择也相同。请求 $u$ 时，外层缓存若命中，其值正是先前对不变 $W$ 取得的 $\operatorname{out}_W(u)$；若未命中，新原始查询同样给 $\operatorname{out}_W(u)$。两执行因此写入相同的新逻辑记录，转到相同状态。归纳涵盖内部步骤、缓存重复请求、所有四值报告和最终返回。

单独的 $\sigma$ 在每个有限 $W$ 上有限终止，虚拟执行只在每个有限请求处做有限的缓存查找或一次合法查询，故也有限终止，且正确返回 $\iota_3(W)$。先前集合 $J$ 中的地址已经各付费一次；后续只有 $J_\sigma(W)\setminus J$ 中的地址新增付费，重复请求均免费。因此不同付费地址集合正是式（27.7）。从固定有限菜单选择一个策略后，同一归纳逐个适用；前缀只决定所选策略，不替它改变初始化或推断输入身份。证毕。

**定理 27.4（每个面的实际精确额外费用）。** 对定义 27.1 的最终族，每个 $F\in K$ 都有一个全域正确且有限终止的确定性策略 $\pi_F\in\mathfrak D_3$，使所有评价来源同时满足

$$
C_{\pi_F}(P_i)=b_F(i),\qquad
b_F(i):=n+\mathbf1_{\{i\notin F\}}\quad(i\in[m]).
\tag{27.8}
$$

更精确地，以 $J_{\pi_F}(P_i)$ 记接受前实际付费的不同地址集合，有

$$
J_{\pi_F}(P_i)=
\begin{cases}
L(P_i),&i\in F,\\
L(P_i)\cup\{a_i\},&i\notin F.
\end{cases}
\tag{27.9}
$$

**证明。** 先固定有限的后续策略菜单。对每个 $r$，令 $\sigma_r$ 为定理 23.2 已有的单原型全带标签叶测试：核对 $P_r$ 的全部叶，任何不匹配交给同定理的全域有限后备，完整匹配才接受。它在全部 $\mathcal T$ 上正确且有限终止，在 $P_r$ 上请求的不同地址恰为 $L(P_r)$。对非空 $F\in K$，式（27.5）和下闭性提供定理 25.2 的叶安全 $\{P_i:i\in F\}$ 路由；令 $\sigma_F$ 为该既有路由接完整带标签叶核对及同一后备的全域策略。它在每个 $P_i$、$i\in F$ 上请求的不同地址恰为 $L(P_i)$。单元素 $F$ 的路由没有分离节点，仍做完整核对。令 $\sigma_\varnothing$ 为定理 23.2 的全域有限后备本身。

策略 $\pi_F$ 按指标递增次序扫描全部 $r\notin F$ 的 $a_r$，精确响应为 $\mathsf{leaf}_\beta$ 时继续扫描；响应为 $\mathsf{branch}$ 时停止扫描，只暂选后续 $\sigma_r$；响应为另外两个原始值时停止扫描并暂选 $\sigma_\varnothing$。若扫描完成且全部报告均精确为 $\mathsf{leaf}_\beta$，则非空 $F$ 选择 $\sigma_F$，空 $F$ 选择 $\sigma_\varnothing$。扫描只作有限次查询，没有在此阶段返回任务答案。被选后续一律以引理 27.3 的独立逻辑历史和真实缓存供应执行；后续内部的不匹配仍由它自己的全域后备处理。

对每个实际有限 $W$，扫描有限，被选后续属于全域有限策略菜单。引理 27.3 保证其返回与单独执行相同，所以合成策略正确且有限终止。特别地，分支报告只暂选原型测试，并不证明 $W=P_r$ 或 $W\in\mathcal I_3$；即使全部扫描报告符合预期，也未证明输入属于 $F$。每次原型接受仍必须有完整带标签叶匹配。所有原型外正例和负例仍由既有后备正确处理。

现在只计算该全域策略在指定 $P_i$ 上的费用。若 $i\in F$，每个被扫描的 $r\notin F$ 都不同于 $i$，式（27.6）给响应 $\mathsf{leaf}_\beta$，且 $a_r\in L(P_i)$。全部扫描完成后选择 $\sigma_F$。其独立运行在 $P_i$ 上恰请求 $L(P_i)$；缓存只提前供应其中一些真实答案，式（27.7）遂给总付费集合 $L(P_i)$。

若 $i\notin F$，扫描到 $r=i$ 以前，每个被问 $a_r$ 都在 $L(P_i)$ 且报告 $\mathsf{leaf}_\beta$；到 $a_i$ 时报告 $\mathsf{branch}$，扫描立即停止并选择 $\sigma_i$。该地址不在 $L(P_i)$，而 $\sigma_i$ 的独立执行恰请求全部 $L(P_i)$ 并匹配接受。引理 27.3 给总集合恰为 $L(P_i)\cup\{a_i\}$，没有再扫描其他列或请求其他叶外地址。这证明式（27.9），式（27.8）由集合基数得到。

$F=\varnothing$ 时，在每个 $P_i$ 上总会先遇到它自己的分支并接 $\sigma_i$；扫描全部结束后的后备分支只处理其他实际输入，评价费用仍为 $n+1$。若 $[m]\in K$，取 $F=[m]$ 时没有扫描，直接执行 $\sigma_F$，每个评价费用为 $n$。空面、满面及单元素面均包含在同一全域构造中。证毕。

**定理 27.5（确定性费用的逐坐标核心与全部 Pareto 极小元）。** 固定定义 27.1 的最终族。对每个 $\pi\in\mathfrak D_3$，定义它在评价族上的零超额指标集

$$
Z_\pi=\{i\in[m]:C_\pi(P_i)=n\}.
\qquad
Z_\pi\in K,\qquad
b_{Z_\pi}(i)\le C_\pi(P_i)\quad(i\in[m]).
\tag{27.10}
$$

每个确定性费用向量都逐坐标大于或等于某个实际取得的极大面费用向量。以较小费用为优，定义性地称一个可取得向量 Pareto 极小，若没有另一个可取得向量逐坐标不大于它且至少一坐标严格较小。全部确定性 Pareto 极小向量恰为

$$
\{b_M:M\in\mathcal M(K)\}.
\tag{27.11}
$$

**证明。** 定理 18.2 和式（23.6）使每个正确接受 $P_i$ 的运行都查询全部 $L(P_i)$，所以 $C_\pi(P_i)\ge n$。同一个 $\pi$ 在 $Z_\pi$ 的所有坐标取得 $n$，式（27.5）遂给 $Z_\pi\in K$。在其余坐标，有限终止使费用为整数，严格大于 $n$ 就至少为 $n+1$，证明式（27.10）。空 $Z_\pi$ 也属于 $K$。

因 $K$ 有限，每个 $Z_\pi$ 包含于一个极大面 $M$，且 $b_M\le b_{Z_\pi}$。定理 27.4 已给实际 $\pi_M$ 取得 $b_M$，故它确是一个可取得的逐坐标支配向量。若原费用向量是 Pareto 极小，这个支配不能有严格坐标，原向量遂等于 $b_M$。

反之，设某可取得向量 $c$ 满足 $c\le b_M$，其中 $M$ 极大。对每个 $i\in M$，必需叶下界给 $c(i)=n$，因此 $M\subseteq Z_c$，这里 $Z_c$ 是取得 $c$ 的策略的零超额集。已证 $Z_c\in K$，极大性迫使 $Z_c=M$。对每个 $i\notin M$，整数费用于是至少为 $n+1$，而 $c\le b_M$ 又给至多 $n+1$，故 $c=b_M$。没有严格改进，得到式（27.11）。不同极大面互不包含，相应向量也不能严格支配彼此。这里刻画的是全部极小元和向下比较核心，不断言每个大于某个 $b_M$ 的数值向量均可由实际查询策略取得，也不建立确定性或实费用的完整向上闭包。证毕。

**定理 27.6（可测固定种子的同时面比较）。** 对定义 27.1 的最终族，固定任一 $\Pi\in\mathfrak R_3$ 及它自己的概率空间 $(\Omega,\mathcal A,\mu)$。存在可测满测度集合 $G_\Pi^{\mathrm{tot}}$，其每个种子在整个 $\mathcal T$ 上确定一个属于 $\mathfrak D_3$ 的策略。存在一个可测的有限值面变量 $Z:\Omega\to K$，使 $\mu$ 的面推前律 $p_F=\mu\{Z=F\}$ 满足

$$
\mathbb E_\mu C_\Pi(\cdot,P_i)
\ \ge\ \sum_{F\in K}p_F b_F(i)
\ =\ n+1-\sum_{\substack{F\in K\\i\in F}}p_F
\quad(i\in[m]).
\tag{27.12}
$$

允许左侧为无穷；全部坐标使用同一个面律。每个随机期望费用向量因而逐坐标大于或等于实际面费用向量的一个有限凸组合。

**证明。** [母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)已给整个 $\mathcal T$ 到有限两字母词的单射编码，故全来源域可数；有限地址和完整有限四值记录也可数。原始菜单、输入无关初始化、同种子重放和逐来源错误事件可测满足定理 22.1。先用其有声返回式（22.4）取得这个固定 $\Pi$ 的可测满测度 $G_\Pi$，再另外使用逐来源可测零测未终止事件及式（22.7），取得

$$
G_\Pi^{\mathrm{tot}}
=G_\Pi\setminus\bigcup_{W\in\mathcal T}
\{\omega:\Pi(\omega,W)\text{ 未有限终止}\},
\qquad \mu(G_\Pi^{\mathrm{tot}})=1.
\tag{27.13}
$$

因此每个 $\omega\in G_\Pi^{\mathrm{tot}}$ 的固定种子策略都全域正确且有限终止。仅有式（22.4）的有声有限返回不能供应这里的总性；也没有对所有随机策略取得一个通用种子集，或取得一个全来源统一终止步数。

定义

$$
Z(\omega)=
\begin{cases}
\{i\in[m]:C_\Pi(\omega,P_i)=n\},
&\omega\in G_\Pi^{\mathrm{tot}},\\
\varnothing,&\omega\notin G_\Pi^{\mathrm{tot}}.
\end{cases}
\tag{27.14}
$$

好种子上应用定理 27.5 得 $Z(\omega)\in K$；坏种子上空面也在 $K$。每个 $\{C_\Pi(\cdot,P_i)=n\}$ 可测，有限个这样的集合、补集与 $G_\Pi^{\mathrm{tot}}$ 的交并给每个 $\{Z=F\}$ 可测。面变量因此确有有限概率律，且 $\sum_{F\in K}p_F=1$。

在这个同一个好种子集上，定理 27.5 同时给所有 $i$ 的 $C_\Pi(\omega,P_i)\ge b_{Z(\omega)}(i)$。对非负扩展可测费用积分，忽略零测补集并用有限面分拆，得到式（27.12）；无穷期望同样满足该不等式。定理 27.4 使右侧每个 $b_F$ 都有真实全域策略，故它是实际向量的有限凸组合。这个结论是存在性的数值下比较：不提供从任意控制器计算 $p_F$、离线重放执行或计算全来源好种子事件的算法；也不称每个这种凸组合均 Pareto 极小，更不以此识别全部可取得的实期望向量。证毕。

**定义 27.7（顶点的分数面边覆盖与最小覆盖概率）。** 将 $[m]$ 作为有限超图的顶点，将 $\mathcal M(K)$ 的非空极大面作为边。定义分数边覆盖数

$$
\tau(K)=
\min\left\{
\sum_{M\in\mathcal M(K)}w_M:
w_M\ge0,\quad
\sum_{\substack{M\in\mathcal M(K)\\i\in M}}w_M\ge1
\ \ (i\in[m])\right\}.
\tag{27.15}
$$

这是用面边分数覆盖顶点，不是分数顶点覆盖边。每个顶点在某个极大面中，故存在有限覆盖。若改用 $K$ 的全部非空面作为边，给每个面选一个包含它的极大面并合并权重，不增加总权重而不减少任何顶点覆盖量；反向极大面本就在 $K$ 中，所以最小值不变。空面不覆盖任何顶点，可以直接删去其权重。

以 $\mathcal P(K)$ 记 $K$ 上的全部概率律，定义

$$
t(K)=\max_{p\in\mathcal P(K)}\min_{i\in[m]}q_i(p),
\qquad
q_i(p)=\sum_{\substack{F\in K\\i\in F}}p_F.
\tag{27.16}
$$

把任一面的概率质量转移到一个包含它的极大面，不减少全部 $q_i$；因此此最大值也可只在极大面概率律上取。面律是随机选择全域策略的律，没有在实际来源上设置概率先验。标准分数边覆盖定义及有限最优有理权重参见 [Martin Grohe、Dániel Marx，*Constraint Solving via Fractional Edge Covers*，arXiv:1711.04506v1，第 1 节和引理 3.2 的证明](https://arxiv.org/pdf/1711.04506v1#page=2)；这里只复用它们的有限超图覆盖对象与有理最优取得，不使用该文的 CSP 输入承诺或其复杂度结论。

**命题 27.8（覆盖归一化、有限对偶与有理最优面律）。** 对定义 27.7，最小值和最大值均取得，且有最优有理面律。准确的归一化关系是

$$
t(K)=\frac1{\tau(K)},\qquad
w_M=\frac{p_M}{t(K)}\ \text{ 对最优极大面律 }p,
\qquad
p_M=\frac{w_M}{\tau(K)}\ \text{ 对最优覆盖 }w.
\tag{27.17}
$$

其有限覆盖对偶为

$$
\tau(K)=
\max\left\{
\sum_{i=1}^m y_i:
y_i\ge0,\quad
\sum_{i\in M}y_i\le1
\ \ (M\in\mathcal M(K))\right\}.
\tag{27.18}
$$

这里的 $y_i$ 是解析上的 packing 见证，不是未知来源的抽样律。

**证明。** 概率单纯形有限维且紧，$\min_i q_i$ 连续，所以 $t(K)$ 取得。给每个单元素面概率 $1/m$ 就使每个顶点有覆盖概率 $1/m$，故 $t(K)>0$。每个顶点在一个极大面中，选择至多 $m$ 个这样的面并各赋单位权重，给覆盖总量至多 $m$。覆盖目标非负；将其限制到总量至多 $m$ 的非空可行子水平集，该集合闭且有界，故 $\tau(K)$ 取得。对任一顶点，它的 incident 权重和至少为 $1$，所以 $\tau(K)\ge1$。

取只支持极大面的最优 $p$，每个 $q_i(p)\ge t(K)$，于是 $w_M=p_M/t(K)$ 可行，给 $\tau(K)\le1/t(K)$。反向取最优覆盖 $w$，以 $p_M=w_M/\tau(K)$ 归一化，它的总质量为 $1$，且每个 $q_i(p)\ge1/\tau(K)$，故 $t(K)\ge1/\tau(K)$。两个不等式等价地给 $t(K)\le1/\tau(K)$ 和 $t(K)\ge1/\tau(K)$，得到等式及两个最优转换。特别地，从最优覆盖得到的最小覆盖概率不能严格大于 $1/\tau(K)$，否则第一个转换就产生更小覆盖。

式（27.15）是有限 $0/1$ incidence 矩阵的非负覆盖 LP。直接复用[运输记忆完成卷第 4.6.5 节式（TM.226）—（TM.227）](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#465-分数覆盖的直接对偶是支持次概率-packing)的有限覆盖—packing 对偶形式，以列对象为这里的面、被覆盖对象为这里的顶点、各列价格为 $1$，就得到式（27.18）。有限 LP 的强对偶及其可行性条件采用 [Stephen Boyd、Lieven Vandenberghe，*Convex Optimization*，第 5.2.3—5.2.4 节，尤其第 227 页的 “Lagrange dual of LP”](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=241)；原论证所用的覆盖集合在本应用中是面，并不引入运输记忆完成卷的实际逐步抽样合同。原问题已有限可行且有界；对偶零向量可行，每个 $i$ 所在的某面约束又使 $y_i\le1$，故对偶有界并取得。该覆盖、packing 与概率归一化的不同约束分别保留，不把非负见证质量直接当概率。

最优覆盖可取有理权重，直接采用 Grohe—Marx 引理 3.2 证明中使用的标准有限有理 LP 取得结果；本矩阵和右端均为整数，每个顶点都被覆盖，没有无覆盖顶点的退化情形。于是 $\tau(K)$ 为正有理数，式（27.17）得到有理最优面律。有限 LP 与上述归一化只处理已定义的有限 incidence 数据；实际查询取得性须由定理 27.4 和引理 27.3 另行承担。证毕。

**定理 27.9（原随机类与固定均匀种子类的共同锐值）。** 对定义 27.1 的最终族，原随机类与式（26.21）的固定均匀种子子类分别有达到的下确界，且

$$
\inf_{\Pi\in\mathfrak R_3}\max_{i\in[m]}
\mathbb E_\mu C_\Pi(\cdot,P_i)
=\inf_{\Pi\in\mathfrak R_3^{\mathrm u}}\max_{i\in[m]}
\mathbb E_{\mu_{\mathrm u}}C_\Pi(\cdot,P_i)
=n+1-\frac1{\tau(K)}.
\tag{27.19}
$$

取得策略可用有理有限混合构造，在每个种子及每个有限来源上均正确且有限终止。

**证明。** 对任意固定 $\Pi\in\mathfrak R_3$，定理 27.6 给同一个面概率律 $p$ 及逐坐标下界。因此即使某个期望无穷，也有

$$
\max_i\mathbb E_\mu C_\Pi(\cdot,P_i)
\ge\max_i\bigl(n+1-q_i(p)\bigr)
=n+1-\min_i q_i(p)
\ge n+1-t(K).
\tag{27.20}
$$

这里是固定来源期望向量的最大坐标，不是对来源积分。命题 27.8 将最后一项化为式（27.19）的右侧。

现取有理最优面律，只列出其正质量面 $F_1,\ldots,F_s\in\mathcal M(K)$ 及概率 $p_1,\ldots,p_s$。它们满足 $s\ge1$、$p_j>0$、$\sum_jp_j=1$。令 $r_0=0$、$r_j=\sum_{k=1}^jp_k$，所以所有端点有理且 $r_s=1$。在预先固定的 $\Omega_{\mathrm u}=[0,1]$ 上定义

$$
\Pi^{\mathrm{opt}}(\omega,\cdot)=
\begin{cases}
\pi_{F_j}(\cdot),&r_{j-1}\le\omega<r_j\quad(1\le j\le s),\\
\pi_{F_s}(\cdot),&\omega=1.
\end{cases}
\tag{27.21}
$$

这是以一次输入无关种子选择一个定理 27.4 的真实全域策略，选定后按该策略原始初始化和缓存合同执行。每个种子都选择到一个正确且有限终止的确定性策略，包括端点 $1$，所以每个有限 $W$ 的错误和未终止事件均为空。对任意固定有限 $W$，每个 $C_{\pi_{F_j}}(W)$ 是有限整数，且

$$
\begin{aligned}
C_{\Pi^{\mathrm{opt}}}(\omega,W)
&=\sum_{j=1}^s
\mathbf1_{[r_{j-1},r_j)}(\omega)C_{\pi_{F_j}}(W)
+\mathbf1_{\{1\}}(\omega)C_{\pi_{F_s}}(W),\\
\mathbb E_{\mu_{\mathrm u}}C_{\Pi^{\mathrm{opt}}}(\cdot,P_i)
&=\sum_{j=1}^s p_j b_{F_j}(i)
=n+1-q_i(p).
\end{aligned}
\tag{27.22}
$$

半开区间和单点都是 Lebesgue 可测集；固定来源的费用是有限阶梯函数，执行事件也是这些有限区间的并，满足原有可测合同和同种子重放。端点单点不改变积分，但其明确选择保证逐种子全域正确总性。于是 $\Pi^{\mathrm{opt}}\in\mathfrak R_3^{\mathrm u}$，最大期望费用为 $n+1-t(K)$，达到下界。该子类的元素也属于原 $\mathfrak R_3$，所以同一个已构造策略达到两类各自的下确界。两类种子合同保持不同，只是这个目标的锐值和取得性相同。证毕。

**定理 27.10（确定性最坏费用与期望最大费用的分离）。** 对同一最终族，分别定义

$$
D(K)=\inf_{\pi\in\mathfrak D_3}\max_{i\in[m]}C_\pi(P_i),
\qquad
W(K)=\inf_{\Pi\in\mathfrak R_3}
\mathbb E_\mu\left[\max_{i\in[m]}C_\Pi(\cdot,P_i)\right].
\tag{27.23}
$$

二者均取得，且

$$
D(K)=W(K)=
\begin{cases}
n,&[m]\in K,\\
n+1,&[m]\notin K.
\end{cases}
\tag{27.24}
$$

将 $W(K)$ 限制到 $\mathfrak R_3^{\mathrm u}$ 后值仍相同且取得。若 $[m]\notin K$，则

$$
1<\tau(K)\le m,\qquad 0<t(K)<1,\qquad
n<n+1-\frac1{\tau(K)}<n+1.
\tag{27.25}
$$

因而式（27.19）的 $\inf_\Pi\max_i\mathbb E C_\Pi(P_i)$ 严格小于 $W(K)$。

**证明。** 必需叶下界使任意确定性评价最大费用至少为 $n$。若 $[m]\in K$，下闭性给 $K=2^{[m]}$，定理 27.4 的 $\pi_{[m]}$ 在全部评价来源上取得 $n$，故 $D(K)=n$。其在固定均匀空间上的常值提升又使每个种子最大费用为 $n$，得到两种随机类的 $W(K)\le n$。定理 27.6 的好种子上全部费用至少为 $n$，积分给反向下界，故均为 $n$。

若 $[m]\notin K$，任一确定性 $\pi$ 的 $Z_\pi\in K$ 都是真子集，故至少一个坐标的整数费用为 $n+1$ 或更多。于是评价最大费用至少为 $n+1$。任选一个面 $F\in K$，定理 27.4 的 $b_F$ 在至少一个坐标等于 $n+1$、其余不超过 $n+1$，得到 $D(K)=n+1$ 并取得。对任意固定 $\Pi$，定理 27.6 的同一个可测满测度好种子集上，每个固定种子策略都满足这个确定性最大费用下界。有限个可测非负扩展费用的最大值可测，积分因此至少为 $n+1$。常值提升 $\pi_F$ 在固定均匀空间中取得该值，证明 $W(K)=n+1$ 以及限制子类的同值取得。这里逐种子先取最大值再积分；不能用各个坐标的最佳平均表现替代这个共同种子比较。

命题 27.8 的构造已给 $\tau(K)\le m$ 和 $t(K)>0$。若 $\tau(K)=1$，取其已取得的最优覆盖 $w$。对每个顶点 $i$，incident 权重和至少为 $1$，总权重也为 $1$，所以不含 $i$ 的全部面权重和为零。任何正权重面于是必须同时含全部顶点；至少有一个面正权重，这将使 $[m]\in K$，矛盾。因此 $\tau(K)>1$，再用 $t(K)=1/\tau(K)$ 得其余严格不等式。满面情形的最优覆盖只需给 $[m]$ 权重 $1$，故 $\tau(K)=t(K)=1$，式（27.19）也为 $n$。证毕。

**推论 27.11（极小不相容模式的覆盖费用）。** 对定理 26.6 已有的 $K_m=2^{[m]}\setminus\{[m]\}$，在定义 27.1 中只向其已完成的原表添加指定私有列，不另建立原表的规模定理。所得实际族的值为

$$
\begin{aligned}
\tau(K_m)&=\frac{m}{m-1},\qquad t(K_m)=\frac{m-1}{m},\\
\inf_{\Pi\in\mathfrak R_3}\max_i\mathbb E C_\Pi(\cdot,P_i)
&=n+\frac1m,\qquad D(K_m)=W(K_m)=n+1,\\
n&=(m-1)(11m-8)+3m+8.
\end{aligned}
\tag{27.26}
$$

固定均匀种子空间也取得相同随机锐值。

**证明。** 定理 26.6 已给原表 $T_0=m(m-1)$、$M_0=(m-1)^2$ 及 $n_0=(m-1)(11m-8)$，所以式（27.4）给所示 $n$。$K_m$ 的极大面为 $F_r=[m]\setminus\{r\}$。任意分数覆盖对全部顶点的约束求和，得到 $(m-1)\sum_rw_{F_r}\ge m$，故总量至少为 $m/(m-1)$；令每个 $w_{F_r}=1/(m-1)$ 就恰好覆盖每个顶点，取得该值。式（27.17）、（27.19）和（27.24）给全部目标值。最优面律可取各 $F_r$ 概率 $1/m$，用式（27.21）的区间构造即在固定均匀空间取得。$m=2$ 同样适用。这是已知模式在新增私有列族上的费用推论，不断言第26章未加指定列的原族具有同样完整费用核心，也不声称这里的叶数最小。证毕。

**命题 27.12（单指标边界）。** 若要求涵盖全部非空有限指标集，$m=1$ 的下闭且含单元素族只能是 $K=\{\varnothing,\{1\}\}$。可单独取实际来源 $P_1=U=\rho^3(u_0)$，其叶数为 $n=11$；完整带标签叶测试及 $\mathtt{LL}$ 先查再测试分别给

$$
b_{\{1\}}(1)=11,\qquad b_\varnothing(1)=12,
\qquad \tau(K)=t(K)=1.
\tag{27.27}
$$

确定性 Pareto 核心只含 $(11)$，三个最坏费用目标均为 $11$。

**证明。** 式（26.2）已给 $U$ 的组成 $(4,7)^{\mathsf T}$、完整前像及实际正性。定理 23.2 的单原型全叶测试在 $U$ 上恰花费 $11$，且在原型外使用既有全域有限后备。$\operatorname{out}_U(\mathtt{LL})=\mathsf{branch}$，故先查该地址再以引理 27.3 接同一测试，在 $U$ 上付费集合恰为 $L(U)\cup\{\mathtt{LL}\}$，花费 $12$；它在其他有限输入上仍正确且有限终止。唯一非空极大面为 $\{1\}$，覆盖值和覆盖概率均为 $1$。必需叶下界与全叶测试给确定性极小值 $11$，定理 22.1 的有声返回和总性桥梁给随机下界，常值提升给两种随机最大费用目标的取得。单指标费用没有跨来源次序交换，故两种随机目标在此一致。证毕。

**注记 27.13（实际取得与结论范围）。** 式（27.8）—（27.12）的对象是定义 27.1 特定构造的完整实际树族；共同组成允许依 $K,m$ 改变。相容模式本身不在本章被证明足以确定任意其他既有族的全部超额费用、随机锐值或最小实现叶数。确定性结果给极小元，随机结果给有限凸组合的下比较和一个指定目标的锐取得，未给全部真实费用的向上闭包、全部随机 Pareto 边界、任意策略的面律可计算性或离线执行恢复。有限覆盖的强对偶和有理最优属于既有有限 LP 结果；完整前像、最终地址上的私有列扫描、真实缓存后续接及同一好种子集上的面费用比较共同承担这里从覆盖数回到实际全域策略的关系。运输记忆完成卷第 4.6.4—4.6.5 节已经区分静态覆盖松弛与实际逐步取得，不能以一个 LP 可行点代替定理 27.4 的全域执行证明。

全部叶证书调用只在 $d=3=3\cdot1$ 的原范围内使用，不扩张到其他替换深度、改变输入承诺或另设查询精度。完整树来源、组成、规范数量地址、原始响应、组成祖先许可与实际逆执行仍是不同对象和任务；组成计数和有限种子混合不提供物理对应、实际逆操作许可或环境代数守恒的物理解释。有限分数边覆盖、LP 对偶、有理混合和母卷编码不被称为新建立的标准理论，实际构造与费用关系也不在未经相应文献论证的情况下被称为世界原创。

## 追加锚（本行以下为增补区）
## 28. 同组成与同零超额相容复形的实际取得费用分离

**定义 28.1（四来源评价与三个费用目标）。** 固定[定义 23.1](#23-全有限来源上两个指定正例的共同最优地址费用)、[定义 25.1](#25-有限正来源族的遗传共享叶分离与四元共同费用)和[定义 26.1](#26-同组成实际三步像的有限遗传相容模式与无统一-helly-阶数)的原合同，取 $d=3$。未知输入为全部非空有限自由有序满二叉 $\alpha/\beta$ 树 $T\in\mathcal T$，目标为 $\iota_3(T)=\mathbf1_{\{T\in\rho^3(\mathcal T)\}}$。次序、括号与叶标签都是字面结构。全部有限左右地址，包括 $\varepsilon$，始终合法，无须先访问前缀；查询只读同一不变输入的原始四值报告。重复地址使用真实缓存，费用计不同地址个数；计算、地址长度、定位与种子取得不收费，未有限终止费用为 $+\infty$。共同初始化可以含完整评价原型与策略，却不承诺未知输入属于原型，也不承诺其正性、组成、叶数、大小或高度。

沿用全域正确且有限终止的确定性类 $\mathfrak D_3$ 和原随机类 $\mathfrak R_3$。每个随机策略使用自己的一个输入无关概率空间 $(\Omega,\mathcal A,\mu)$，同种子与同完整记录决定相同控制、查询、缓存、停止和输出；每个固定 $T$ 的错误返回事件与未有限终止事件可测且零测，非负扩展费用可测。此合同允许零测种子例外。固定均匀子类 $\mathfrak R_3^{\mathrm u}$ 仍恰使用式（26.21）的 $([0,1],\mathcal L,\operatorname{Leb})$。对四个不同正来源的指标族 $\boldsymbol P=(P_1,P_2,P_3,P_4)$，定义

$$
\begin{aligned}
K_{\mathrm d}(\boldsymbol P)&=\{S\subseteq[4]:\exists\pi\in\mathfrak D_3\ \forall i\in S,
 C_\pi(P_i)=|L(P_i)|\},\\
K_{\mathrm e}(\boldsymbol P)&=\{S\subseteq[4]:\exists\Pi\in\mathfrak R_3\ \forall i\in S,
 \mathbb E_\mu C_\Pi(\cdot,P_i)=|L(P_i)|\},\\
D(\boldsymbol P)&=\inf_{\pi\in\mathfrak D_3}\max_{i\in[4]}C_\pi(P_i),\\
R(\boldsymbol P)&=\inf_{\Pi\in\mathfrak R_3}\max_{i\in[4]}\mathbb E_\mu C_\Pi(\cdot,P_i),\\
W(\boldsymbol P)&=\inf_{\Pi\in\mathfrak R_3}\mathbb E_\mu[\max_{i\in[4]}C_\Pi(\cdot,P_i)].
\end{aligned}
\tag{28.1}
$$

$R$ 先对每个固定来源取种子期望再取最大值；$W$ 在同一个种子下比较四次实际运行，先取最大值再积分。这里没有输入分布，也不对确定性策略空间规定测度。将随机下确界限制为 $\mathfrak R_3^{\mathrm u}$，分别记为 $R_{\mathrm u},W_{\mathrm u}$。固定输入期望后再取最坏输入的惯例参见 [Magniez、Nayak、Santha、Sherman、Tardos、Xiao，*Improved bounds for the randomized decision tree complexity of recursive majority*，arXiv:1309.7565v1，第 2 页](https://arxiv.org/pdf/1309.7565v1#page=2)；该文的输入是有限布尔词，本章的全有限树合同及共同种子桥梁另由第22、23章供应。

**定义 28.2（平衡六孔族与共同补块私有五孔族）。** 直接复用式（23.9）、（23.15）、（25.12）、（26.2）的字面块和来源：

$$
\begin{gathered}
E=\langle\beta,\alpha\rangle,\quad A=\langle E,\beta\rangle=\rho^3(\alpha),\quad
C=\langle A,E\rangle=\rho^3(\beta),\\
u_0=\langle\langle\alpha,\alpha\rangle,\beta\rangle,\qquad
U=\langle\langle A,A\rangle,C\rangle=\rho^3(u_0),\\
R_0=B_6(\alpha,\alpha,\alpha,\alpha,\beta,\beta),\qquad
R=B_6(A,A,A,A,C,C)=\rho^3(R_0).
\end{gathered}
\tag{28.2}
$$

$B_T$ 始终是式（26.5）的精确右梳上下文：

$$
\begin{aligned}
B_1(x_1)&=x_1,\qquad B_T(x_1,\ldots,x_T)=\langle x_1,B_{T-1}(x_2,\ldots,x_T)\rangle\quad(T\ge2),\\
p_j^{(T)}&=\mathtt R^{j-1}\mathtt L\quad(j<T),\qquad p_T^{(T)}=\mathtt R^{T-1}\quad(T\ge2).
\end{aligned}
\tag{28.3}
$$

取四行二元词 $b_1=000111$、$b_2=110001$、$b_3=101010$、$b_4=011100$，以 $0$ 填 $A$、$1$ 填 $U$。两族的完整块表为

$$
\begin{array}{c|cccccc}
\text{平衡族行}&1&2&3&4&5&6\\ \hline
1&A&A&A&U&U&U\\ 2&U&U&A&A&A&U\\ 3&U&A&U&A&U&A\\ 4&A&U&U&U&A&A
\end{array}
\qquad
\begin{array}{c|ccccc}
\text{私有族行}&1&2&3&4&5\\ \hline
1&U&A&A&A&R\\ 2&A&U&A&A&R\\ 3&A&A&U&A&R\\ 4&A&A&A&U&R
\end{array}
\tag{28.4}
$$

以 $X^{\mathrm b}_{ij},X^{\mathrm p}_{ij}$ 记条目，定义

$$
\begin{aligned}
P_i^{\mathrm b}&=B_6(X^{\mathrm b}_{i1},\ldots,X^{\mathrm b}_{i6}),&
Q_i^{\mathrm b}&=B_6(Z^{\mathrm b}_{i1},\ldots,Z^{\mathrm b}_{i6}),\\
P_i^{\mathrm p}&=B_5(X^{\mathrm p}_{i1},\ldots,X^{\mathrm p}_{i5}),&
Q_i^{\mathrm p}&=B_5(Z^{\mathrm p}_{i1},\ldots,Z^{\mathrm p}_{i5}).
\end{aligned}
\tag{28.5}
$$

$Z$ 逐项把 $A,U,R$ 换成 $\alpha,u_0,R_0$。私有族的字面括号是 $\langle X_{i1}^{\mathrm p},\langle X_{i2}^{\mathrm p},\langle X_{i3}^{\mathrm p},\langle X_{i4}^{\mathrm p},R\rangle\rangle\rangle\rangle$，第五孔为 $\mathtt{RRRR}$。$R$ 内部另有自己的六孔右梳，外层孔与内层孔分别保留。记 $\boldsymbol P^{\mathrm b}=(P_1^{\mathrm b},\ldots,P_4^{\mathrm b})$、$\boldsymbol P^{\mathrm p}=(P_1^{\mathrm p},\ldots,P_4^{\mathrm p})$。

**命题 28.3（字面来源、完整前沿与全部地址分类）。** 两族各自的四棵树两两不同，式（28.5）给各自唯一完整三步前像。每个评价来源及其前像满足

$$
\begin{gathered}
\rho^3(Q_i^{\mathrm b})=P_i^{\mathrm b}\in\mathcal I_3,\quad
\rho^3(Q_i^{\mathrm p})=P_i^{\mathrm p}\in\mathcal I_3,\\
c(Q_i^{\mathrm b})=c(Q_i^{\mathrm p})=(9,3)^{\mathsf T},\quad
c(P_i^{\mathrm b})=c(P_i^{\mathrm p})=(15,27)^{\mathsf T},\\
|L(P_i^{\mathrm b})|=|L(P_i^{\mathrm p})|=42,\quad
c(R_0)=(4,2)^{\mathsf T},\quad c(R)=(8,14)^{\mathsf T},\quad |L(R)|=22.
\end{gathered}
\tag{28.6}
$$

$A,U$ 的原始响应在所有有限残词 $v$ 上恰为下表。最后一行是前六行地址集合的补集，包含全部更长残词。

$$
\begin{array}{c|c|l}
\operatorname{out}_A(v)&\operatorname{out}_U(v)&v\\ \hline
\mathsf{branch}&\mathsf{branch}&\varepsilon,\ \mathtt L\\
\mathsf{leaf}_\beta&\mathsf{branch}&\mathtt{LL},\ \mathtt R\\
\mathsf{leaf}_\alpha&\mathsf{branch}&\mathtt{LR}\\
\mathsf{absent}&\mathsf{branch}&\mathtt{LLL},\ \mathtt{LRL},\ \mathtt{RL},\ \mathtt{RLL},\ \mathtt{RR}\\
\mathsf{absent}&\mathsf{leaf}_\alpha&\mathtt{LLLR},\ \mathtt{LRLR},\ \mathtt{RLLR},\ \mathtt{RRR}\\
\mathsf{absent}&\mathsf{leaf}_\beta&\mathtt{LLLL},\ \mathtt{LLR},\ \mathtt{LRLL},\ \mathtt{LRR},\ \mathtt{RLLL},\ \mathtt{RLR},\ \mathtt{RRL}\\
\mathsf{absent}&\mathsf{absent}&\text{其余全部有限词}
\end{array}
\tag{28.7}
$$

以 $\mathcal F(X)$ 记带标签叶前沿。$A,U$ 的前沿取自式（25.16）；共同补块继承的 $A,C$ 前沿完整写为

$$
\begin{aligned}
\mathcal F(A)&=\{(\mathtt{LL},\beta),(\mathtt{LR},\alpha),(\mathtt R,\beta)\},\\
\mathcal F(C)&=\{(\mathtt{LLL},\beta),(\mathtt{LLR},\alpha),(\mathtt{LR},\beta),
(\mathtt{RL},\beta),(\mathtt{RR},\alpha)\}.
\end{aligned}
\tag{28.8}
$$

令 $(s_1,\ldots,s_6)=(\mathtt L,\mathtt{RL},\mathtt{RRL},\mathtt{RRRL},\mathtt{RRRRL},\mathtt{RRRRR})$ 为 $R$ 内部六孔地址，其全部 $22$ 片带标签叶恰为

$$
\begin{aligned}
\mathcal F(R)=&\bigsqcup_{j=1}^4
\{(s_j\mathtt{LL},\beta),(s_j\mathtt{LR},\alpha),(s_j\mathtt R,\beta)\}\\
&\sqcup\bigsqcup_{j=5}^6\{(s_j\mathtt{LLL},\beta),(s_j\mathtt{LLR},\alpha),
(s_j\mathtt{LR},\beta),(s_j\mathtt{RL},\beta),(s_j\mathtt{RR},\alpha)\}.
\end{aligned}
\tag{28.9}
$$

对两族各自的 $T=6,5$ 及每个有限地址 $w$，全部上下文祖先报告分支，其余词唯一分解为 $p_j^{(T)}v$ 并读取该孔条目：

$$
\begin{aligned}
\operatorname{out}_{B_T(X_1,\ldots,X_T)}(w)&=
\begin{cases}\mathsf{branch},&w\prec p_j^{(T)}\text{ 对某个 }j,\\
\operatorname{out}_{X_j}(v),&w=p_j^{(T)}v\text{ 对唯一的 }j,\end{cases}\\
\mathcal F(B_T(X_1,\ldots,X_T))&=
\bigsqcup_{j=1}^T\{(p_j^{(T)}v,\ell):(v,\ell)\in\mathcal F(X_j)\}.
\end{aligned}
\tag{28.10}
$$

平衡族的任一非常值查询都恰产生 $2+2$ 划分；其在四行上为常值的查询全部报告非叶值。私有族的任一非常值查询都恰产生 $1+3$ 划分；第五孔的全部报告恒同。每个非常值查询的两个不同报告中，至少一个是非叶值；两族各自任意两行在共享叶地址上的标签都相同。

**证明。** $\rho^3$ 保留每个有序二叉构造，式（28.2）的 $A,U$ 是既有完整实际三步像，逐孔替换 $R_0$ 又给 $R$，所以式（28.5）的前像等式直接成立。平衡表每行三个 $A$、三个 $U$，前像三个 $\alpha$、三个 $u_0$；私有表每行三个 $A$、一个 $U$、一个 $R$，前像三个 $\alpha$、一个 $u_0$、一个 $R_0$。由[母卷定义 3.3、定理 3.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md#3-fibonacci-替换与组成动力学)的组成加性与替换作用，已知 $c(A)=(1,2)^{\mathsf T}$、$c(U)=(4,7)^{\mathsf T}$、$c(C)=(2,3)^{\mathsf T}$、$c(u_0)=(2,1)^{\mathsf T}$，得到

$$
\begin{aligned}
c(R)&=4(1,2)^{\mathsf T}+2(2,3)^{\mathsf T}=(8,14)^{\mathsf T},\\
c(Q_i^{\mathrm b})&=3(1,0)^{\mathsf T}+3(2,1)^{\mathsf T}=(9,3)^{\mathsf T},\\
c(Q_i^{\mathrm p})&=3(1,0)^{\mathsf T}+(2,1)^{\mathsf T}+(4,2)^{\mathsf T}=(9,3)^{\mathsf T},\\
c(P_i^{\mathrm b})&=3(1,2)^{\mathsf T}+3(4,7)^{\mathsf T}=(15,27)^{\mathsf T},\\
c(P_i^{\mathrm p})&=3(1,2)^{\mathsf T}+(4,7)^{\mathsf T}+(8,14)^{\mathsf T}=(15,27)^{\mathsf T}.
\end{aligned}
\tag{28.11}
$$

平衡表各行的前两位 $00,11,10,01$ 不同，故前像在至少一个相同孔分别为 $\alpha,u_0$，字面不同。私有表在自己的第 $i$ 孔为 $u_0$，其他行该孔为 $\alpha$，也使前像两两不同。直接调用[规范编译卷命题 4.3 的字面树替换单射性](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)，其三次复合使两族分别有不同的像与唯一完整前像。该命题中的原子 $A,B$ 在此对应 $\alpha,\beta$；组成逆公式不承担前像存在或字面恢复。

对有限树 $X$，令 $N(X)$ 为全部存在节点的地址集合，包括内节点与叶；它是 $L(X)$ 的全部前缀集合。式（25.16）的完整 $U$ 前沿给其内节点集合恰为

$$
\begin{aligned}
N(U)\setminus L(U)&=\{\varepsilon,\mathtt L,\mathtt{LL},\mathtt{LLL},\mathtt{LR},
\mathtt{LRL},\mathtt R,\mathtt{RL},\mathtt{RLL},\mathtt{RR}\},\\
N(A)&=\{\varepsilon,\mathtt L,\mathtt{LL},\mathtt{LR},\mathtt R\}\subseteq N(U).
\end{aligned}
\tag{28.12}
$$

$U$ 的其余存在节点正是式（25.16）的十一片叶，按标签分成式（28.7）的四个 $\alpha$ 地址与七个 $\beta$ 地址。$A$ 的两个内节点、三片叶在式（28.12）中全部列出，三片叶都变成 $U$ 的内节点。于是 $N(A)\cup N(U)=N(U)$ 的全部 $21$ 个节点逐项给出式（28.7）的前六行，集合外地址在两块中都不存在。这是有限节点集合及其补集的符号穷尽，不以有限长度截断代替任意长地址论证。特别地，$L(A)\cap L(U)=\varnothing$，任何不同的局部报告都不能同时是两片叶。

式（28.8）的 $A$ 前沿直接取式（25.16），$C$ 前沿取定理 25.5 证明对 $C=\langle A,E\rangle$ 的完整展开。加上内部孔前缀 $s_j$ 即得式（28.9）；孔地址前缀自由，各并互不交，总数 $4\cdot3+2\cdot5=22$。$R$ 的节点集合是这 $22$ 个叶地址的全部前缀：叶地址按式（28.9）给标签，真前缀报告分支，集合外的所有地址报告不存在。这也精确规定穿过任一补块叶之后的全部更长查询。

式（28.10）复用[引理 26.2 的全部地址上下文分解式（26.6）、（26.8）](#26-同组成实际三步像的有限遗传相容模式与无统一-helly-阶数)。其路径证明只用上下文满二叉、每片上下文叶都是孔以及孔前缀自由，与所填块的名字无关，故同一分解适用于第五孔的 $R$。路径或者结束于某个孔的真前缀，或者经过唯一孔而留下任意残词，没有第三类词。第五孔内部再用同一分解读取 $B_6(A,A,A,A,C,C)$，连同式（28.8）、（28.9）覆盖全部存在、缺失与任意长地址。平衡前沿给 $3\cdot3+3\cdot11=42$ 片；私有前四孔给 $3\cdot3+11=20$ 片，再加第五孔 $22$ 片也为 $42$。共同补块叶均包含在完整带标签前沿中。

平衡表每列恰有两个 $A$、两个 $U$。上下文祖先为常值分支；孔内两块响应相同只可能是式（28.7）的分支—分支或不存在—不存在，其余查询恰按该列分成两个二元素响应类。因此常值查询都是非叶，非常值查询都是 $2+2$，至少一类报告非叶。私有前四列各有一个 $U$、三个 $A$，同一表给 $1+3$；第五孔是完全相同的 $R$，其常值查询允许报告叶。在每个族内部，对任意两行，在不同块的孔内没有共同叶，在同块的孔内字面相同保证叶标签相同，上下文祖先不是叶。式（28.10）排除跨孔遗漏，故共享叶没有标签冲突。证毕。

**定理 28.4（两族相同的零超额相容复形）。** 两族在确定性与期望意义下均有且只有空面和四个单元素面：

$$
K_{\mathrm d}(\boldsymbol P^{\mathrm b})=K_{\mathrm e}(\boldsymbol P^{\mathrm b})
=K_{\mathrm d}(\boldsymbol P^{\mathrm p})=K_{\mathrm e}(\boldsymbol P^{\mathrm p})
=K_\circ:=\{\varnothing,\{1\},\{2\},\{3\},\{4\}\}.
\tag{28.13}
$$

**证明。** 命题 28.3 使每个族内部任意两行没有标签冲突的共同叶，故对每个二元素指标集 $S$，式（26.1）的 $\Delta_{\boldsymbol P}(S)$ 为空。直接应用[定理 25.2](#25-有限正来源族的遗传共享叶分离与四元共同费用)的遗传信息叶判据，所有二元素子族在确定性和期望意义下都不相容；较大子族含这样的子族，也不相容。恒同补块虽有 $22$ 片共同叶，但标签不变，不能贡献信息叶。单元素族采用定理 23.2 的单原型完整带标签叶测试与已有全域有限后备，取得个体下界 $42$；确定性常值提升也取得期望下界。空约束由同一后备满足，得到式（28.13）。这里复用零超额判据，不把它解释成超额费用分类。证毕。

**定理 28.5（条件共同历史中的新增收费下界）。** 固定任意 $\pi\in\mathfrak D_3$。对两族分别令 $J_i$ 为它在 $P_i$ 上有限接受前请求的不同地址集合，令 $e_i$ 为叶外地址数，则

$$
L(P_i)\subseteq J_i,\qquad C_\pi(P_i)=42+e_i,\qquad
 e_i=|J_i\setminus L(P_i)|\in\mathbb N_0.
\tag{28.14}
$$

平衡族有 $\sum_i e_i\ge4$ 且 $\max_i e_i\ge2$；私有族有 $\sum_i e_i\ge3$ 且 $\max_i e_i\ge1$。同一个全域策略的联合下界为

$$
\begin{array}{c|cc}
\text{评价族}&\sum_{i=1}^4 C_\pi(P_i)&\max_{i\in[4]}C_\pi(P_i)\\ \hline
\boldsymbol P^{\mathrm b}&\ge172&\ge44\\
\boldsymbol P^{\mathrm p}&\ge171&\ge43
\end{array}
\tag{28.15}
$$

**证明。** 四个评价树都是三步正像。全域总性给有限接受记录，同记录重放与全域正确性使各终端记录无承诺有声。直接使用[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)及其在式（23.6）中的运行应用，得到 $L(P_i)\subseteq J_i$，其条件恰为 $d=3=3\cdot1$。叶数为 $42$，有限集合分解给式（28.14），不预置查询视界或输入高度。

先处理平衡族。直到四次运行第一次出现不恒同的响应，它们的全部记录、缓存、内部控制、下一查询选择与停止决定相同，包括重复查询与内部计算。首次差异必在任何接受之前出现：否则最早接受处四者具有同一个记录并同时接受。该记录按式（28.14）包含任取一个 $P_i$ 的全部带标签叶，而所有其他行匹配它。定理 18.2 证明中的完整叶恢复使其他行都等于 $P_i$，与命题 28.3 的不同性矛盾。这一步用完整有限满树的带标签叶集决定字面树，并最终调用[母卷定理 9.3 的全路径恢复](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)。全域有限终止也排除共同前缀永久停滞。

设首个非常值查询的地址为 $a$，查询前四者共同的不同地址缓存为 $H$。$a\notin H$：若已在缓存中，不变来源使本次报告仍等于此前的共同报告，不能首次分裂。命题 28.3 给这次响应恰把指标分成两个二元素集 $S_0,S_1$。至少一个响应类是非叶，故存在 $S_\star\in\{S_0,S_1\}$，其两个成员都为 $a$ 支付一笔新的叶外费用。记这一地址的初次收费为

$$
a_i=\mathbf1_{\{a\notin L(P_i^{\mathrm b})\}},\qquad
\sum_{i=1}^4a_i\ge2,\qquad \sum_{i\in S_\star}a_i=2.
\tag{28.16}
$$

分别固定一个幸存对 $S=\{r,s\}\in\{S_0,S_1\}$。两次运行在首分裂之后仍有相同完整历史：此前共同记录与在 $a$ 上这一对共同的响应全部保留，共同缓存已经是 $H\cup\{a\}$。同历史控制归纳使此后直到该对首次响应不同，两运行的查询、内部状态与缓存仍相同。任意接受之前必须出现该对的首次差异；否则在较早接受处两者一起接受，记录包含 $P_r^{\mathrm b}$ 全部带标签叶，又为 $P_s^{\mathrm b}$ 匹配，完整叶恢复使二者相等，矛盾。有限接受与不同性保证该首次差异确在有限步骤出现。

记该地址为 $a_S$，问它之前这一对的整个共同不同地址缓存为 $H_S$。$H_S$ 包含 $H\cup\{a\}$ 以及首分裂后的全部同响应查询。必须有 $a_S\notin H_S$：若曾问过，两个不变输入的该地址报告早已相同，再次读取或缓存重放不能成为首次差异。因此此次收费对两个运行都是新收费，且与式（28.16）计入的 $a$ 不同。两行在同块列上的报告相同，故此次差异来自一个 $A/U$ 不同块列。式（28.7）没有不同标签的共同叶报告，至少一方报告非叶，该方支付一笔新的叶外费用。令

$$
b_i=\mathbf1_{\{a_S\notin L(P_i^{\mathrm b})\}}\quad(i\in S),\qquad
\sum_{i\in S}b_i\ge1\quad(S=S_0,S_1).
\tag{28.17}
$$

对每个指标 $i$，$a$ 与其所属对的 $a_S$ 都实际被请求且地址不同，所以 $e_i\ge a_i+b_i$。两个不同对的 $a_{S_0},a_{S_1}$ 可以是同一个字；它们属于不同实际运行，不会在同一运行重复收费。于是

$$
\sum_{i=1}^4e_i\ge\sum_{i=1}^4a_i+
\sum_{i\in S_0}b_i+\sum_{i\in S_1}b_i\ge2+1+1=4,\qquad
\sum_{i\in S_\star}e_i\ge2+1=3.
\tag{28.18}
$$

后一个不等式在同一二元素对内使用首轮两笔费用与该对后来新增的一笔，整数性使至少一个 $e_i\ge2$。单靠四个坐标和至少为 $4$ 不能给这个最大值下界，故须保留 $S_\star$ 的条件共同历史。首分裂前的常值查询在平衡族上全部报告非叶，其每个新地址额外增加四次运行的费用，不减弱下界；后续常值查询不能替代首次差异。这里未把无条件两来源费用不等式再加到首轮收费上，每项增量都由相对于该对整个共同缓存的新地址承担，因而没有重计。

私有族的共同补块含叶，不能沿用常值非叶断言。改用式（28.13）：同一个 $\pi$ 的零超额集 $Z=\{i:e_i=0\}$ 属于 $K_\circ$，故 $|Z|\le1$。其余至少三个有限整数 $e_i$ 大于零，各至少为 $1$，所以 $\sum_i e_i\ge3$、$\max_i e_i\ge1$。共同补块叶属于各行必查的 $42$ 叶；它们允许相同历史中的叶收费，但不改变零超额至多一个的结论。代回式（28.14）得到式（28.15）。证毕。

**定理 28.6（两个族的精确全域取得策略）。** 存在四个平衡策略 $\pi_t^{\mathrm b}\in\mathfrak D_3$ 和四个私有策略 $\pi_t^{\mathrm p}\in\mathfrak D_3$，其各自四个评价来源的超额向量依 $t=1,2,3,4$ 为

$$
\begin{aligned}
(C_{\pi_t^{\mathrm b}}(P_i^{\mathrm b})-42)_{i=1}^4&=
\begin{cases}(0,2,1,1),&t=1,\\(2,0,1,1),&t=2,\\(1,1,0,2),&t=3,\\(1,1,2,0),&t=4,\end{cases}\\
(C_{\pi_t^{\mathrm p}}(P_i^{\mathrm p})-42)_{i=1}^4&=
(\mathbf1_{\{i\ne t\}})_{i=1}^4.
\end{aligned}
\tag{28.19}
$$

每个策略在全部 $\mathcal T$ 上正确且有限终止。评价来源上最终核对全部 $42$ 片带标签叶，私有核对包含补块的全部 $22$ 片叶；路由本身从不接受。

**证明。** 固定一个有限后续菜单。对每个原型 $P_i$，取[定理 23.2](#23-全有限来源上两个指定正例的共同最优地址费用)已有的单原型策略 $\sigma_i$：从自己的空记录开始，按固定顺序测试全部带标签叶，任一不匹配进入同定理的全域有限后备，完整匹配才接受。它属于 $\mathfrak D_3$，在自身原型上请求的不同地址恰为 $L(P_i)$。另令 $\sigma_\perp$ 为该后备本身。后备从根探索实际有限输入，只扩展实际分支，复用真实缓存，恢复字面树与实际叶数 $m$，在叶数至多 $m$ 的全部字面前像中穷尽检验 $\rho^3$ 像成员身份。其正确总性已由定理 23.2 的替换不减叶数证明，这里直接复用，不把原型不匹配当作负性证明。

任一路由完成后，以[引理 27.3](#27-实际三步像的面费用核心与分数面覆盖锐值)接被选后续：建立该 $\sigma$ 自己的初始化、空逻辑历史与初始控制状态，外层缓存只在它请求地址时供应同一输入的真实报告，每个请求与报告记入它自己的逻辑历史。绝不把路由历史预填为它已经执行的步骤。若路由不同地址集为 $J_{\mathrm{route}}$，总不同付费地址精确为

$$
J_{\mathrm{route}}\cup J_\sigma(T).
\tag{28.20}
$$

引理 27.3 保证虚拟后续与 $\sigma$ 单独从头运行相同，任意有限路由选择都保持全域正确总性。

平衡策略固定目标行 $t$ 的前两位 $(b_{t1},b_{t2})$，依次为 $00,11,10,01$。对 $j=1,2$ 直接查询

$$
a_j^{(t)}=p_j^{(6)}v_{tj},\qquad
v_{tj}=\begin{cases}\mathtt{LL},&b_{tj}=0,\\\mathtt{LLLL},&b_{tj}=1.\end{cases}
\tag{28.21}
$$

目标位为 $0$ 时，允许的两个路由响应是精确的 $\mathsf{leaf}_\beta$ 与 $\mathsf{branch}$，分别记暂定观测位为 $0,1$；目标位为 $1$ 时，允许的两个响应是精确的 $\mathsf{leaf}_\beta$ 与 $\mathsf{absent}$，分别记暂定观测位为 $1,0$。其他原始报告立即选择 $\sigma_\perp$。两个允许的观测位完成后，按 $00,11,10,01$ 唯一暂选一行 $i$，以式（28.20）接 $\sigma_i$。二位选择只在评价原型间路由，未知输入仍可能是任何完整有限树，须经全叶核对或后备才返回答案。

在评价行 $i$ 上，式（28.7）说明每次路由的叶报告当且仅当 $b_{ij}=b_{tj}$；不匹配位报告分支或不存在。暂定观测位恰为自身真实块位，两位暂选 $i$，后续完整匹配接受。两个路由地址在不同孔，故互异；匹配位地址属于 $L(P_i^{\mathrm b})$，不匹配位地址不属于该叶集。式（28.20）给

$$
C_{\pi_t^{\mathrm b}}(P_i^{\mathrm b})=42+
\mathbf1_{\{b_{i1}\ne b_{t1}\}}+\mathbf1_{\{b_{i2}\ne b_{t2}\}}.
\tag{28.22}
$$

四个二位词的距离逐项给式（28.19）的平衡向量。没有从识别评价行直接接受，也没有多查上下文前缀。

私有策略固定 $t$，按指标递增的固定次序只扫描 $r\in[4]\setminus\{t\}$ 的地址

$$
a_r=p_r^{(5)}\mathtt{LL},\qquad
\operatorname{out}_{P_i^{\mathrm p}}(a_r)=
\begin{cases}\mathsf{branch},&i=r,\\\mathsf{leaf}_\beta,&i\ne r.\end{cases}
\tag{28.23}
$$

精确 $\beta$ 叶报告继续；精确分支报告停止扫描并暂选 $\sigma_r$；另外两个报告选择 $\sigma_\perp$。所有被扫描地址均报告 $\beta$ 叶时暂选 $\sigma_t$。全部后续仍按式（28.20）执行，扫描不返回任务值。

在 $P_t^{\mathrm p}$ 上，扫描地址都是自己的必查 $\beta$ 叶，$\sigma_t$ 补齐全部叶，总不同付费集恰为 $L(P_t^{\mathrm p})$。在 $P_i^{\mathrm p}$、$i\ne t$ 上，到 $i$ 之前所问地址均为自己的 $\beta$ 叶；问 $a_i$ 时得到分支并暂选 $\sigma_i$。此前地址均为自己的叶，只有 $a_i$ 是新的叶外地址，总集恰为 $L(P_i^{\mathrm p})\cup\{a_i\}$，超额为 $1$。$\sigma_i$ 按式（28.9）、（28.10）核对第五孔的全部带标签叶，扫描未替它省略补块核对。这给私有向量。

原型外任意实际输入的路由至多两次或三次，所选后续是全域正确且有限终止的固定菜单元素。引理 27.3 保证相同返回与有限终止，后续原型不匹配由已有后备处理，因此八个策略均属于 $\mathfrak D_3$。证毕。

**定理 28.7（原随机合同与固定均匀子类的三个锐值）。** 两族的全部下确界均达到，且

$$
\boxed{\begin{aligned}
(D,R,W)(\boldsymbol P^{\mathrm b})&=(44,43,44),\\
(D,R,W)(\boldsymbol P^{\mathrm p})&=\left(43,\frac{171}{4},43\right),\\
(R_{\mathrm u},W_{\mathrm u})(\boldsymbol P^{\mathrm b})&=(43,44),\\
(R_{\mathrm u},W_{\mathrm u})(\boldsymbol P^{\mathrm p})&=\left(\frac{171}{4},43\right).
\end{aligned}}
\tag{28.24}
$$

每个定理 28.6 的确定性目标策略都取得相应 $D$；各族均匀混合四个目标策略同时取得相应 $R,W$，并能在固定的 $[0,1]$ 种子空间中逐种子全域正确且有限终止地实现。

**证明。** 定理 28.5 给任意确定性全域策略的评价最大费用至少为 $44,43$。定理 28.6 的每个平衡向量最大超额是 $2$，每个私有向量最大超额是 $1$，加 $42$ 即取得下界，证明确定性锐值。

固定任意 $\Pi\in\mathfrak R_3$ 及它自己的种子律。[母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)的单射有限词编码使整个 $\mathcal T$ 可数；有限地址与完整有限四值记录也可数。原合同满足[定义 22.1、定理 22.1](#22-可数只读记录的有声返回与终止精确探针许可的分界)的只读菜单、同种子重放与逐来源错误事件可测条件。先由有声返回式（22.4）取得这个策略的可测满测度集 $G_\Pi$；再另行使用逐来源零测可测未终止事件与共同总性式（22.7），取得

$$
G_\Pi^{\mathrm{tot}}=G_\Pi\setminus\bigcup_{T\in\mathcal T}N_T^\Pi,
\qquad\mu(G_\Pi^{\mathrm{tot}})=1.
\tag{28.25}
$$

每个 $\omega\in G_\Pi^{\mathrm{tot}}$ 的固定种子策略在整个 $\mathcal T$ 上有声、正确且有限终止，属于 $\mathfrak D_3$。有声有限返回与全域有限终止分别来自（22.4）与（22.7），前者没有单独推出后者。这个可测好种子集依赖当前 $\Pi$；两个联合下界必须使用同一个 $G_\Pi^{\mathrm{tot}}$，不对所有随机策略取共同交集，也不声称全来源统一运行时间上界。

定理 28.5 的和与最大值下界在式（28.25）的同一集合上逐种子同时成立。四个可测非负扩展费用的和与最大值可测，分别积分得

$$
\begin{array}{c|cc}
\text{评价族}&\displaystyle\sum_{i=1}^4\mathbb E_\mu C_\Pi(\cdot,P_i)
&\displaystyle\mathbb E_\mu\max_{i\in[4]}C_\Pi(\cdot,P_i)\\ \hline
\boldsymbol P^{\mathrm b}&\ge172&\ge44\\
\boldsymbol P^{\mathrm p}&\ge171&\ge43
\end{array}
\tag{28.26}
$$

有限和的非负积分可相加，包括无穷期望；零测补集不降低下界。最大固定来源期望至少为四个期望的平均，故 $R(\boldsymbol P^{\mathrm b})\ge43$、$R(\boldsymbol P^{\mathrm p})\ge171/4$；另一列独立给 $W$ 的下界。不能把固定来源期望的最大值替换成同种子最大值的积分。推导没有输入分布或来源—种子联合积分，也没有先假设原随机类就是全域确定性策略上的分布；固定种子的全域性质由式（28.25）建立。

分别在两族上一次均匀选择 $t\in[4]$，运行定理 28.6 的对应策略。式（28.19）使每个平衡评价行的四个超额之和为 $4$，每个私有评价行的四个超额之和为 $3$；每个种子的评价最大超额分别恒为 $2,1$。故

$$
\begin{aligned}
\mathbb E C^{\mathrm b}(\cdot,P_i^{\mathrm b})&=42+\frac44=43,
&\mathbb E\max_i C^{\mathrm b}(\cdot,P_i^{\mathrm b})&=44,\\
\mathbb E C^{\mathrm p}(\cdot,P_i^{\mathrm p})&=42+\frac34=\frac{171}{4},
&\mathbb E\max_i C^{\mathrm p}(\cdot,P_i^{\mathrm p})&=43.
\end{aligned}
\tag{28.27}
$$

在预先固定的均匀空间上，令 $I_t=[(t-1)/4,t/4)$，在 $I_t$ 上选择目标策略 $t$；端点 $\omega=1$ 明确选择第四个目标策略。四个半开区间加该端点穷尽 $[0,1]$，每个种子都选到一个全域正确且有限终止的确定性策略。对任意固定实际 $T$，费用精确为

$$
C_{\Pi_{\mathrm u}^{\mathrm a}}(\omega,T)=
\sum_{t=1}^4\mathbf1_{I_t}(\omega)C_{\pi_t^{\mathrm a}}(T)
+\mathbf1_{\{1\}}(\omega)C_{\pi_4^{\mathrm a}}(T),
\qquad\mathrm a\in\{\mathrm b,\mathrm p\}.
\tag{28.28}
$$

每个确定性值是有限整数，半开区间与端点单集可测，所以固定来源费用是可测有限阶梯函数，错误和未终止事件均为空。同一可测四值选择决定各个固定输入的执行事件，选定后保留原策略的初始化及同种子重放。端点不改变积分，但明确选择保证每个声明种子的全域正确总性。因此两策略属于 $\mathfrak R_3^{\mathrm u}$，式（28.27）在该固定空间成立。子类中的策略亦属于原类，原类下界适用于子类，故两类下确界同值且均取得，完成式（28.24）。证毕。

**推论 28.8（组成与零超额相容复形的成对不足）。** 在定义 28.1 的全部来源、报告、权限、缓存费用及正确总性合同不变时，逐来源的组成与零超额相容复形这两项资料不能决定四来源评价的 $D,R,W$。式（28.5）的两族逐行具有相同组成 $(15,27)^{\mathsf T}$、相同叶数 $42$、相同确定性及期望复形 $K_\circ$，而式（28.24）的三个实际锐值逐项不同。

**证明。** 组成与叶数相等由命题 28.3 给出，两种相容复形相等由定理 28.4 给出，锐值及全域取得由定理 28.7 给出。若只按组成与复形确定任一锐值，就会在这两组相同资料上给相同结果，与 $44\ne43$、$43\ne171/4$、$44\ne43$ 分别矛盾。

两项资料在这两个构造中遗忘的是条件响应划分与叶／非叶的收费关系。平衡族首次非常值查询只能分成两对，至少一对的两个运行先各付一笔叶外费用；该对下一次分离又须相对于整个共同缓存新增收费。私有族的非常值查询分成一个单行与三个其余行，式（28.23）的扫描把叶外费用留给被扫描的自身私有列，共同补块增加必须核对的恒同带标签叶。两族没有信息性共同叶，零超额复形相同，却保留不同的条件取得结构。这些收费已由定理 28.5、28.6 在实际运行上证明。

按响应划分幸存假设的标准图景参见 [Robert D. Nowak，*The Geometry of Generalized Binary Search*，arXiv:0910.4397v5，第 I 节](https://arxiv.org/pdf/0910.4397v5#page=1)与 [Sanjoy Dasgupta，*Analysis of a greedy active learning strategy*，NIPS 2004，第 2 节](https://proceedings.neurips.cc/paper_files/paper/2004/file/c61fbef63df5ff317aecdc3670094472-Paper.pdf)。这里只借用响应分裂的关系图景；这些文献的假设类、查询域、损失和输入承诺不同，不供应全部有限树上的正确总性、完整叶证书或上述新增收费下界。Magniez 等的固定输入期望惯例只承担定义 28.1 注明的角色。实际前像、任意长地址穷尽、条件缓存收费与全域取得共同承担本章的具体分离；它不被称为这些标准查询理论的新建立，也不从所列有限文献范围推出世界原创。

结论只否定这两项资料对于所给成对实际费用的充分性，不给任意来源族的费用分类、一般费用核心或 Pareto 边界、费用向上闭包、最小实现族或叶数。所有叶证书只在 $d=3$ 的既有适用范围内调用，未推出其他替换深度的结论。完整树来源、组成、规范数量地址、原始响应、组成祖先许可与实际逆执行保持不同，此只读任务及代数组成不提供实际逆执行或物理世界对应。证毕。

## 追加锚（本行以下为增补区）

## 29. 任意有限实际正来源族的联合响应费用核心与全域取得

**定义 29.1（实际联合响应数据、分裂核心与费用目标）。** 沿用定义 23.1、28.1 的原始只读合同，固定 $d=3$。未知输入仍遍历全部非空有限自由有序满二叉 $\alpha/\beta$ 树 $U\in\mathcal T$，任务仍为 $\iota_3(U)=\mathbf1_{\{U\in\rho^3(\mathcal T)\}}$。共同初始化与输入无关；没有组成、叶数、大小、高度、正性或有限候选承诺。每个有限左右地址，包括 $\varepsilon$，始终可以直接查询，报告为同一不变输入的四值；费用只计不同实际地址，重复请求由真实缓存供应，未有限终止费用为 $+\infty$。计算、定位、地址长度与种子取得不收费。$\mathfrak D_3$、$\mathfrak R_3$、$\mathfrak R_3^{\mathrm u}$ 分别保留全域确定性正确总性、原逐来源随机合同及固定 $([0,1],\mathcal L,\operatorname{Leb})$ 种子合同；原随机空间不要求完备。

取整数 $m\ge1$ 及两两不同、完整描述已知的实际树 $F=(P_i)_{i\in[m]}$，其中 $P_i\in\rho^3(\mathcal T)$。它们仅是费用评价对象。定义

$$
\begin{gathered}
\mathcal B=\{\mathsf{leaf}_\alpha,\mathsf{leaf}_\beta,
                 \mathsf{branch},\mathsf{absent}\},\qquad
\Sigma=\{\mathtt L,\mathtt R\}^{<\mathbb N},\\
L_i=L(P_i),\qquad n_i=|L_i|,\qquad \boldsymbol n=(n_i)_{i\in[m]},\\
a(u)=(\operatorname{out}_{P_i}(u))_{i\in[m]}\in\mathcal B^{[m]},
\qquad \mathcal A_F=\{a(u):u\in\Sigma\},\\
\chi(\mathsf{leaf}_\alpha)=\chi(\mathsf{leaf}_\beta)=0,
\qquad \chi(\mathsf{branch})=\chi(\mathsf{absent})=1.
\end{gathered}
\tag{29.1}
$$

$\mathcal A_F$ 是实际联合响应向量的集合，不计相同向量出现于多少地址，不是任意填写的响应表。固定地址的短词优先次序，等长时取 $\mathtt L<\mathtt R$；对每个 $a\in\mathcal A_F$，以 $r_F(a)$ 记满足 $a(u)=a$ 的首个实际地址。令 $N_i$ 为 $P_i$ 的全部实际节点地址；确定这些代表可以使用有限集合 $\bigcup_iN_i$ 及其外首个地址。代表替换始终使用完整 $m$ 坐标向量。

对非空 $S\subseteq[m]$、$a\in\mathcal A_F$，定义

$$
S_{a,y}=\{i\in S:a_i=y\},\qquad
Y_a(S)=\{a_i:i\in S\},\qquad
\mathcal A_+(S)=\{a\in\mathcal A_F:|Y_a(S)|\ge2\}.
\tag{29.2}
$$

只在非空幸存指标集上递归定义非负整数向量集合 $\Gamma_F(S)\subseteq\mathbb N_0^S$：

$$
\begin{aligned}
\Gamma_F(\{i\})&=\{(0)\},\\
\Gamma_F(S)&=
\bigcup_{a\in\mathcal A_+(S)}
\left\{
 \bigl(\chi(a_i)+g^{a_i}_i\bigr)_{i\in S}:
 g^y\in\Gamma_F(S_{a,y})\ \text{对每个 }y\in Y_a(S)
\right\}\quad(|S|\ge2),\\
\mathcal V_F&=\{\boldsymbol n+g:g\in\Gamma_F([m])\}.
\end{aligned}
\tag{29.3}
$$

递归所选 $a\in\mathcal A_+(S)$ 的每个非空 $S_{a,y}$ 都是真子集，故这是按 $|S|$ 的有限递归；空孩子不进入递归。递归中的一个选择树在非单元素节点 $S$ 选择 $a\in\mathcal A_+(S)$，按实际报告进入相应非空孩子，到单点结束路由；单点本身不是未知输入的接受证书。这里不把已付费地址集 $Q$ 放入 $\Gamma_F$ 的自变量，实际执行仍保留完整地址缓存。

把定义 28.1 的目标推广到这 $m$ 个评价对象：

$$
\begin{aligned}
D(F)&=\inf_{\pi\in\mathfrak D_3}\max_{i\in[m]}C_\pi(P_i),\\
R(F)&=\inf_{\Pi\in\mathfrak R_3}\max_{i\in[m]}\mathbb E C_\Pi(\cdot,P_i),&
R_{\mathrm u}(F)&=\inf_{\Pi\in\mathfrak R_3^{\mathrm u}}\max_{i\in[m]}\mathbb E C_\Pi(\cdot,P_i),\\
W(F)&=\inf_{\Pi\in\mathfrak R_3}\mathbb E\!\left[\max_{i\in[m]}C_\Pi(\cdot,P_i)\right],&
W_{\mathrm u}(F)&=\inf_{\Pi\in\mathfrak R_3^{\mathrm u}}\mathbb E\!\left[\max_{i\in[m]}C_\Pi(\cdot,P_i)\right].
\end{aligned}
\tag{29.4}
$$

每个最大值中的各次评价使用同一控制器和同一种子；期望仅在该策略自己的输入无关种子律上取，不给 $F$ 或 $\mathcal T$ 设置来源先验。

**定理 29.2（实际全域取得与逐坐标支配的有限正规形）。** 定义 29.1 的 $\mathcal V_F$ 是非空有限集合。每个 $v\in\mathcal V_F$ 都由一个输入无关的固定策略 $\sigma_v\in\mathfrak D_3$ 同时取得；每个原确定性全域策略都被其中一个费用向量在 $F$ 上逐坐标支配：

$$
\begin{gathered}
\forall v\in\mathcal V_F\ \exists\sigma_v\in\mathfrak D_3\ \forall i\in[m],
\quad C_{\sigma_v}(P_i)=v_i,\\
\forall\pi\in\mathfrak D_3\ \exists v\in\mathcal V_F\ \forall i\in[m],
\quad v_i\le C_\pi(P_i),\\
\mathcal V_F\subseteq\prod_{i\in[m]}
\bigl(\{n_i,n_i+1,\ldots,n_i+m-1\}\bigr).
\end{gathered}
\tag{29.5}
$$

取得策略使用实际代表路由，再以单点选择相应原型的完整带标签叶测试。若 $B_v(i)$ 是它在 $P_i$ 上的路由地址集合，则同一路径的完整联合向量和实际代表地址都不重复，路由长至多 $m-1$，而最终不同付费地址集合与费用精确为

$$
\begin{aligned}
J_{\sigma_v}(P_i)&=B_v(i)\cup L_i,\\
e_v(i)&=|B_v(i)\setminus L_i|
       =\sum_{u\in B_v(i)}\chi(\operatorname{out}_{P_i}(u)),\\
C_{\sigma_v}(P_i)&=n_i+e_v(i)=v_i.
\end{aligned}
\tag{29.6}
$$

式（29.5）的支配只比较 $F$ 上的费用；在 $F$ 外要求新策略独立地正确且有限终止，不要求与原策略的行为或费用相同。

**证明。** 每个 $P_i$ 有有限个节点，故 $N=\bigcup_iN_i$ 有限。$u\notin N$ 时所有坐标都是 $\mathsf{absent}$；$u\in N$ 时由实际描述取得四值。因此 $\mathcal A_F$ 恰由 $N$ 上的实际向量及一个全不存在向量组成，既有限又有实际代表。短词优先次序使每个代表有限取得；全不存在向量的首代表是 $N$ 外首地址。这里仅从指定实际树的描述读出数据，没有为虚构向量建立实现。

若 $i\ne j$，两树不同，由[母卷定理 9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)有实际地址区分它们，故 $\mathcal A_F$ 分离所有不同指标。对每个非空 $S$，将既有 [AdaptiveSeparationDepthUpperBound](../../../D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound.lean) 的私有 exists_bounded_separating_protocol 及公开 adaptive_separation_depth_upper_bound 的有限候选含义用于状态 $S$、查询 $\mathcal A_F$、读数 $(a,i)\mapsto a_i$。它们供应实际分离读数上的有限协议与 $|S|-1$ 深度界；所用查询、响应及指标对应均已明确，不把有限候选识别当成全域成员判定。该构造在每个非单元素队列选择区分其中两个指标的向量，故所有非空响应孩子都是真子集；其终端记录在 $S$ 上单射，所以每个非空终端队列恰为单点。忽略空孩子后，这正是式（29.3）所枚举的选择树类型。因此每个 $\Gamma_F(S)$ 非空。每个节点的菜单有限，孩子严格较小，使用[延拓卷定义 11.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#11-自适应分辨率何时可以停止递归)的有限纯观察树形分解，在这有限菜单上按 $|S|$ 枚举所有孩子选择，得到全部选择树及有限 $\Gamma_F(S)$。该分解只用于有限候选上的严格缩小树形；这里的响应相关超额按式（29.3）逐坐标拼接，并由式（29.6）的实际不同地址集合核算，不直接代入定义 11.2 的固定动作价格 $c(a)$ 标量公式，也没有把无限的 $\mathcal T$ 代入有限候选递推。

固定式（29.3）的一棵选择树。任一先前选中的完整向量 $a$ 在所进入的孩子上有同一个响应 $y$，在其任意后代幸存集上仍是常值，所以不能再次属于 $\mathcal A_+(S)$。这同时排除不同地址携带相同完整向量而在同一路径上重复分裂。用 $r_F(a)$ 替换每个选择向量后，若同一路径两个代表地址相同，它们的完整向量也相同，与上述性质矛盾。互不相交的不同分支可以用同一代表；一次运行只走一条路径。每个非空孩子严格减少指标数，故该路径至多 $m-1$ 个地址。这解释了 $\Gamma_F$ 为什么无需 $Q$：在这种已限定的分裂路由内，再次使用任何已问向量必为常值，不能新增一个合法分裂。它没有删除运行缓存，也没有给一般历史、许可或费用状态的消去定理。

现把选择树编译为读取任意实际 $U\in\mathcal T$ 的策略。在节点 $S$ 实际请求 $r_F(a)$，只按真实四值报告更新：报告 $y\in Y_a(S)$ 时进入 $S_{a,y}$，任何其他报告立即选择定理 23.2 证明中的全域总后备。到达单点 $\{i\}$ 时仅选择该证明中取两个评价对象同为 $P_i$ 的全域单原型策略：依固定次序请求 $P_i$ 的全部带标签叶，全部精确匹配才接受；任何叶标签、分支或不存在的不匹配都进入同一后备。所选单原型策略从它自己的完整初始化、空逻辑历史和初始控制状态开始；每次进入后备，包括叶核对中发生不匹配后进入后备，也给后备建立其独立初态和空逻辑历史。应用[引理 27.3](#27-实际三步像的面费用核心与分数面覆盖锐值)，先前路由及叶核对的真实报告仍留在外层实际缓存中，但只在后续策略请求相同地址时供应，并将这次请求及报告写入该后续策略自己的逻辑历史。后备从根开始的请求因此逐步等于它单独运行的请求；没有把路由或核对历史预填进任何续接的初态。

完整叶核对的充分性与字面唯一性直接使用[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)及式（23.6）中的完整叶恢复，深度取其适用的 $d=3=3\cdot1$。因此任何接受都确实有 $U=P_i\in\rho^3(\mathcal T)$。单点路由本身不产生这种结论；不匹配也不被解释为负性证据。其余来源由定理 23.2 已证明的后备处理：从根起恢复实际有限树及实际测得叶数 $\ell$，只在分支处扩展，再对叶数至多 $\ell$ 的全部实际候选前像作有限枚举，比较其三步替换描述。该后备的完备性使用替换不减叶数，所需字面前像单射性与非满射性直接使用[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)。枚举的是已知描述，不对未知输入执行逆操作。

特别地，未知输入为根叶 $\alpha$ 或 $\beta$ 时，若路由出现意外报告便立即进入总后备；若全部路由报告仍沿某条原型路径，则有限路由终至单点。由式（18.4），每个 $P_i$ 至少有三片叶，其叶地址都非空，而未知根叶在每个这样的地址都报 $\mathsf{absent}$；所选原型测试遂发生叶响应不匹配并进入同一总后备。恢复所得 $\ell=1$，候选前像只有两种根叶，三步替换均为分支树，有限比较后拒绝。三步替换作用于原分支时也保留根分支，故这两种未知根叶确实都是负例。没有使用等待某个前像出现的无穷搜索。一般有限正负输入同样由既有后备有限终止，而路由和叶核对各自有限，故整个新策略在全部 $\mathcal T$ 上正确且有限终止；它的初始化仅依固定 $F$、选择树与既有测试。

在评价输入 $P_i$ 上，每个真实路由报告都在当前 $Y_a(S)$ 中并保留 $i$，最终恰选择自己的测试。它不会进入后备，后续测试的独立执行请求集合恰为 $L_i$。引理 27.3 遂给最终付费集合 $B_v(i)\cup L_i$。叶报告的路由地址属于 $L_i$，已包含在基线 $n_i$ 中，故其额外费用 $\chi$ 为零；分支或不存在地址都不属于 $L_i$，每个不同地址新增费用一，故其 $\chi$ 为一。同一路径地址无重复，所以额外费用正是式（29.6）的和。式（29.3）逐层拼接这些贡献，得到 $v_i=n_i+e_v(i)$，并由路由长度得式（29.5）的坐标界。于是每个数值核心向量都有一棵实际代表选择树和一个全域正确总控制器取得，不只是有限承诺域上的费用。

为证支配，固定任意 $\pi\in\mathfrak D_3$。它在每个 $P_i$ 上的完整有限请求—响应记录记为 $h_i$，重复缓存请求也保留；无报告内部计算和实际停止决定由共同初始化与该记录决定。以 $J_i$ 记其不同付费地址集。直接用式（23.6），有 $L_i\subseteq J_i$。若 $P_j$ 匹配 $h_i$ 的全部报告，则同记录重放使它在该处同时接受；这份记录已经包含 $P_i$ 的全部带标签叶，定理 18.2 的完整叶唯一性遂给 $P_j=P_i$，从而 $j=i$。因此每份接受记录在 $F$ 中的完整相容队列恰为 $\{i\}$，特别地，不同指标不能有相同完整终端记录。也不能有一个原型在另一原型的相同记录真前缀处接受：同记录停止决定会使后者同时停止，归入刚排除的情形。

全部 $h_i$ 的前缀并是有限的，全部出现过的原地址并 $Q_\pi=\bigcup_iJ_i$ 也有限。由这些实际运行作静态有限前缀树：在共同记录处采用原策略的下一请求，遇到实际响应分支后继续对应的原型子队列，终端保留原接受标签。同一共同记录的下一请求或停止决定由原控制唯一确定；已排除的终端真前缀情形保证这里不会同时要求停止与继续。内部计算仅确定这些已有节点，不充当新报告。把前缀树作为有限查询类型 $Q_\pi$ 上的只读选择器，实际原型运行与 $h_i$ 完全相同；在未出现的记录上固定返回接受标签，只用于定义这个有限设计对象，不把它当作未知输入上的正确策略。这个选择器的请求燃料可取 $1+\max_i|h_i|$，预算可取 $\max_i|h_i|$；它们由有限族的实际终端记录取得，不声称原 $\pi$ 有全树统一燃料。

现在直接复用 [PassivePolicyNormalization](../../../D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization.lean) 证明内的 normalize_bounded 有限剪枝及公开 result 的终端纤维、子序列和深度部分。对应取状态 $[m]$、查询 $Q_\pi$、共同四值响应、读数 $\operatorname{out}_{P_i}(u)$；可取唯一接受标签、恒真有限设计合法谓词、零终端价格、单位查询价格及上述预算，输出与目标取同一单点度量空间。公开结果要求的每个候选及响应纤维上免费合法标签于是均存在，实际原型运行的每次请求价格和也不超过预算；这个辅助预算只确保该有限设计满足原结果的假设，不替代不同地址费用合同。该已知剪枝给一个静态协议，其在 $P_i$ 上的完整请求—响应列 $t_i$ 是 $h_i$ 的子序列；每个终端相容队列与原记录的终端队列完全相同，每个保留查询的非空响应孩子严格较小，路径长至多 $m-1$。原终端队列已为单点，剪枝后仍是单点。这里使用的是已有有限剪枝的这些含义，不另外建立剪枝或深度包装命题。

缓存重复请求在当前队列上必为常值，常值地址的报告也只是在设计时由实际原型数据确定，因而这两类请求被删去。剪枝证明以这些设计常值选择静态子树；这不要求在新的实际运行中取得或伪造被删报告。删去的响应没有写入新运行的逻辑记录或外层缓存；新策略不恢复原 $\pi$ 的内部状态，也不以虚构的历史继续执行 $\pi$。有限承诺分裂的标准对应可参见 [Nowak，*The Geometry of Generalized Binary Search*，arXiv:0910.4397v5，第 I 节、第 II.A 节](https://arxiv.org/pdf/0910.4397v5#page=3) 的有限假设及查询等价分区，以及 [Dasgupta，*Analysis of a greedy active learning strategy*，第 2 节](https://proceedings.neurips.cc/paper_files/paper/2004/file/c61fbef63df5ff317aecdc3670094472-Paper.pdf#page=3) 的有限假设搜索。它们的有限目标假设与来源律不供应这里无承诺的 $\rho^3(\mathcal T)$ 成员判定。

在剪枝协议的一条原型路径上，某个已问地址的完整联合向量在对应后代队列上恒定，因此不能再次分裂；同一个完整向量的任何其他地址也不能在这条路径上分裂。由此，所有保留的原地址互异。对同一个实际 $P_i$，它们由 $t_i$ 是 $h_i$ 的子序列而都是原运行中的实际请求，所以每个保留的原非叶地址都是 $J_i\setminus L_i$ 的不同成员。四值中的叶报告恰指地址属于 $L_i$，分支与不存在恰指地址不属于 $L_i$，因而沿 $t_i$ 的 $\chi$ 和正是这些不同保留原非叶地址的个数，不超过 $|J_i\setminus L_i|$。这个结论同时覆盖原策略的重复缓存、常值查询和不收费内部计算；它没有从另一个原型的付费记录借用地址。

最后将每个保留原地址 $u$ 替换为 $r_F(a(u))$。完整 $m$ 坐标响应相同，故各原型的分支、终端单点与每个 $\chi$ 都保持；不能只保留当前队列上的局部向量后任意换址。前述常值后代性质排除完整向量在同一路径上重现，也排除两个代表在同一路径上别名为同一地址。代表替换不继承旧地址的缓存条目：只有这个实际代表已经在当前新运行中被请求才可命中缓存，而路径非重复使路由阶段没有这种命中。实际叶测试中可以命中同一代表地址的真实缓存，这正由式（29.6）计费。响应相关费用的有限测试模型可参见 [Saettler、Laber、Cicalese，*Trading off Worst and Expected Cost in Decision Tree Problems and a Value Dependent Model*，arXiv:1406.3655v1，第 1.1 节](https://arxiv.org/pdf/1406.3655v1#page=3)；其有限 DFEP 的固定测试费用版本见 [Cicalese、Laber、Saettler，*Decision Trees for Function Evaluation: Simultaneous Optimization of Worst and Expected Cost*，arXiv:1309.2796v2，第 2—3 页](https://arxiv.org/pdf/1309.2796v2#page=2)。这里的零或一是扣除完整叶基线后的超额，不是把原叶查询改为免费动作。

所得代表选择树属于式（29.3）的递归。接上已经证明全域正确总性的独立叶测试与后备，得到某个 $v\in\mathcal V_F$。被删去的原叶观察在最后的完整叶测试中恢复，它们的不同地址费用仍包含在一次性的 $n_i$ 内；不向新路由免费供应旧策略的未取得观察。因而对每个 $i$，新费用为 $n_i$ 加保留原非叶数，不超过 $n_i+|J_i\setminus L_i|=|J_i|=C_\pi(P_i)$。这证明全部支配子句。有限学习目标中删去单响应动作的另一表述是 [Sabato，*Submodular Learning and Covering with Response-Dependent Costs*，arXiv:1602.07120v3，第 2 节、引理 4.5](https://arxiv.org/pdf/1602.07120v3#page=12) 的 bifurcating 算法；其引理要求学习目标与既有最优算法，只在其有限动作—响应模型内使用。本证明的任意策略终端队列与子序列由上述既有有限剪枝供应，全域认证、代表实际计费和后备由前面的桥梁供应，不从该有限学习结论扩大输入域。证毕。

**定理 29.3（原随机合同的有限可测投影与全部五个锐值）。** 对每个定义 29.1 的原随机策略 $\Pi$，存在 $\mathcal V_F$ 上的概率向量 $p=(p_v)_{v\in\mathcal V_F}$ 及以同一所选控制器共同评价全部原型的有限混合 $\widehat\Pi$，使

$$
\begin{aligned}
\mathbb E C_{\widehat\Pi}(\cdot,P_i)
 &=\sum_{v\in\mathcal V_F}p_vv_i
 \le\mathbb E C_\Pi(\cdot,P_i)\quad(i\in[m]),\\
\mathbb E\!\left[\max_i C_{\widehat\Pi}(\cdot,P_i)\right]
 &=\sum_{v\in\mathcal V_F}p_v\max_i v_i
 \le\mathbb E\!\left[\max_i C_\Pi(\cdot,P_i)\right].
\end{aligned}
\tag{29.7}
$$

原期望允许无穷。每个概率向量 $p$ 的有限混合都可用固定 $[0,1]$ 种子空间实际取得，在每个声明种子和每个有限树上均正确且有限终止；每个固定树的费用是有限可测阶梯函数。于是

$$
\begin{aligned}
D(F)&=\min_{v\in\mathcal V_F}\max_i v_i,\\
R(F)=R_{\mathrm u}(F)
 &=\min_{p\in\Delta(\mathcal V_F)}\max_i\sum_{v\in\mathcal V_F}p_vv_i,\\
W(F)=W_{\mathrm u}(F)
 &=\min_{p\in\Delta(\mathcal V_F)}\sum_{v\in\mathcal V_F}p_v\max_i v_i
 =D(F),
\end{aligned}
\tag{29.8}
$$

其中 $\Delta(\mathcal V_F)=\{p:p_v\ge0,\ \sum_vp_v=1\}$。这些下确界全部有限取得，$R(F)$ 有理且有有理最优权重；其精确有限 LP 为

$$
\begin{aligned}
\text{最小化 }&t,\\
p_v&\ge0\quad(v\in\mathcal V_F),\qquad \sum_vp_v=1,\\
\sum_vp_vv_i&\le t\quad(i\in[m]),\qquad
0\le t\le M_F,\qquad M_F=\max_{v\in\mathcal V_F}\max_i v_i.
\end{aligned}
\tag{29.9}
$$

$m=1$ 时 $\mathcal V_F=\{(n_1)\}$，五个值均为 $n_1$。概率质量的存在不要求在线执行原策略的反事实评价、检验好种子集或计算任意原策略的律。

**证明。** [母卷定理 9.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)把全部 $\mathcal T$ 单射编码进有限二字母词，故整个未知输入域可数。全部地址和有限四值请求—响应记录也可数，原合同的完整初始化、合法菜单、来源不变与同种子重放恰满足定理 22.1 的原假设。对这一个 $\Pi$，先用式（22.4）取可测满测度有声返回集，再另用式（22.7）的全部来源未终止事件并，得到一个策略专属集合

$$
G_\Pi=G_\Pi^{\mathrm{sound}}\setminus
        \bigcup_{U\in\mathcal T}N_U^\Pi\in\mathcal A,
\qquad \mu(G_\Pi)=1,\qquad
\omega\in G_\Pi\Longrightarrow\Pi_\omega\in\mathfrak D_3.
\tag{29.10}
$$

第一步供应所有实际来源上的有声有限返回，第二步供应所有实际来源上的有限终止；不能以第一步代替第二步。可数并中的各事件可测且零测正是原随机合同，没有对所有策略取共同交集，也没有只在 $F$ 上取好种子或取得统一全树时间界。

枚举有限核心为互异向量 $v^1,\ldots,v^s$，$s\ge1$，为每个向量固定定理 29.2 的一个实际控制器 $\sigma_j$。令 $c_i(\omega)=C_\Pi(\omega,P_i)$，它们是原合同已经要求的非负扩展可测费用，有限最大值 $\max_i c_i$ 也因此可测，无须新增逐历史可测性合同。定义仅含有限数字比较的集合

$$
E_j=\bigcap_{i\in[m]}\{\omega:c_i(\omega)\ge v^j_i\}
\quad(1\le j\le s).
\tag{29.11}
$$

这些集合可测，包括费用为无穷的种子。对每个 $\omega\in G_\Pi$，定理 29.2 适用于同一个全域正确总策略 $\Pi_\omega$，所以至少一个 $E_j$ 包含该种子。采用固定顺序的首匹配单元

$$
\begin{aligned}
B_1&=(G_\Pi\cap E_1)\cup(\Omega\setminus G_\Pi),\\
B_j&=G_\Pi\cap\left(E_j\setminus\bigcup_{k<j}E_k\right)
\quad(2\le j\le s),\\
p_j&=\mu(B_j),\qquad
\theta(\omega)=j\quad(\omega\in B_j).
\end{aligned}
\tag{29.12}
$$

$B_j$ 两两不交且并为整个 $\Omega$，都属于原 $\mathcal A$，故 $p_j\ge0$ 且 $\sum_jp_j=1$。在 $G_\Pi$ 上，同一个 $\theta$ 同时满足全部坐标比较，并因而满足最大值比较：

$$
v^{\theta(\omega)}_i\le c_i(\omega)\quad(i\in[m]),
\qquad \max_i v^{\theta(\omega)}_i\le\max_i c_i(\omega).
\tag{29.13}
$$

这里未选择原型各自的不同控制器或不同种子。单元只由费用数值与一个已知可测的策略专属集合形成；没有使用逐历史事件、可测转录、策略空间测度或来源先验。在非完备空间上也成立：好集合及其整个补集都是已证明可测的集合，没有任取不可测的零测子集。式（29.12）在好集合外固定选 $1$，而不是赋予那些种子未经验证的原策略性质。

在同一 $\Omega$ 上把 $\theta$ 看作有限控制器的耦合选择，仅为比较取期望。非负扩展积分的几乎处处单调性及有限阶梯函数积分给

$$
\begin{aligned}
\int v^{\theta(\omega)}_i\,d\mu
 &=\sum_{j=1}^sp_jv^j_i\le\int c_i\,d\mu,\\
\int\max_i v^{\theta(\omega)}_i\,d\mu
 &=\sum_{j=1}^sp_j\max_i v^j_i
 \le\int\max_i c_i\,d\mu.
\end{aligned}
\tag{29.14}
$$

零测例外上的原费用即使为无穷也不改变这些积分比较；原期望无限时同一不等式仍成立。由此存在有限质量 $p$，而实际新混合只需把 $j$ 本身作为输入无关有限种子，并从 $\sigma_j$ 的完整初态运行。它没有在未知输入上计算 $\theta$、运行全部反事实原型、测试 $G_\Pi$ 或求取原策略律。式（29.12）仅为质量存在及同时支配的数学构造。

对任意给定概率向量 $p$，包括有零权重的情形，置 $q_0=0$、$q_j=\sum_{k=1}^jp_k$，故 $q_s=1$。在已经固定的均匀种子空间定义

$$
\sigma(\omega)=
\begin{cases}
\sigma_j,&0\le\omega<1,\quad q_{j-1}\le\omega<q_j,\\
\sigma_s,&\omega=1.
\end{cases}
\tag{29.15}
$$

正长度半开区间两两不交并覆盖 $[0,1)$；零权重的区间为空，不造成缺口。端点 $1$ 显式分配给 $\sigma_s$，即使 $p_s=0$，它仍是全域正确总控制器。选择仅依种子和固定菜单，所有输入使用同一规则。每个种子选中的控制器都对每个有限树正确且有限终止；对每个固定 $U$，费用在这些有限可测区间及端点上分别为有限常数 $C_{\sigma_j}(U)$。所以费用是有限可测阶梯函数，错误和未终止事件均为空，这确实属于 $\mathfrak R_3^{\mathrm u}$。在全部原型上同一个 $j$ 给费用向量 $v^j$，其坐标均值及同种子最大值均值正是式（29.7）的有限和。有限菜单取得性连同式（29.14）证明该式。

现在比较目标。对任意 $\pi\in\mathfrak D_3$，定理 29.2 供应某个 $v$ 满足 $\max_i v_i\le\max_i C_\pi(P_i)$；有限核心中最小的 $\max_i v_i$ 又由相应 $\sigma_v$ 取得。这给式（29.8）的 $D$ 等式。对任意原随机 $\Pi$，式（29.7）给某个有限 $p$ 的所有坐标均值同时不大于原值，因此有限概率单纯形上目标的最小值是 $R$ 的下界；反向由式（29.15）实现任意 $p$，特别是其最优 $p$，同时属于两种随机类，给 $R=R_{\mathrm u}$。同理，最大值的同种子比较给 $W$ 的下界，任意 $p$ 的实际混合给上界及 $W=W_{\mathrm u}$。令 $M(v)=\max_i v_i$，每个 $p$ 都满足 $\sum_vp_vM(v)\ge\min_vM(v)$，而把全部质量放在一个极小向量取得等号，故 $W=W_{\mathrm u}=D$。该论证保留了 $\max_i\mathbb E C_i$ 与 $\mathbb E\max_i C_i$ 的次序，不将二者互换。

$\mathcal V_F$ 非空有限，概率单纯形紧，$p\mapsto\max_i\sum_vp_vv_i$ 连续，故其最小值有限取得。式（29.9）只是此目标的有限 epigraph LP；对任意 $p$，取 $t=\max_i\sum_vp_vv_i$ 均有 $0\le t\le M_F$，所以此上界不删去任何概率向量的目标值。其系数及右端均为整数，约束后的多面体非空有界。复用[命题 27.8](#27-实际三步像的面费用核心与分数面覆盖锐值)所引用的标准有限有理 LP 取得事实；[Grohe、Marx，*Constraint Solving via Fractional Edge Covers*，arXiv:1711.04506v1，引理 3.2 的证明](https://arxiv.org/pdf/1711.04506v1#page=6) 在其有限覆盖 LP 中使用的正是有理最优权重事实。在这里，线性目标的非空最优面含有多面体的一个顶点；该顶点由等式及取等号约束中的满秩子系确定，整数系数的满秩线性系统有有理解。因此可以选有理最优 $p,t$，最优 $t=R(F)$ 也有理。这里只在上述实质定理的优化步骤内借用标准 LP 事实，未把式（29.9）称为分数覆盖，也未采用 CSP 输入承诺。有理最优 $p$ 给式（29.15）的有理端点及真实全域取得；$D,W,W_{\mathrm u}$ 则由整数核心的一个点质量取得。

最后 $m=1$ 时式（29.3）从单点零向量开始，完全没有路由，定理 29.2 仍接上完整叶测试与全域后备。故核心只有 $(n_1)$，其点质量和固定区间全部给费用 $n_1$；原随机下界仍由整个可数域的式（29.10）供应，五个值均为 $n_1$。没有额外的正性承诺或端点遗漏。证毕。

**推论 29.4（实际联合响应集合与叶数的数值充分性）。** 设 $F=(P_i)_{i\in[m]}$、$F'=(P'_i)_{i\in[m]}$ 都满足定义 29.1，且存在同一个指标置换 $\eta:[m]\to[m]$。对任意坐标向量 $x$，定义 $(T_\eta x)_{\eta(i)}=x_i$。若

$$
n'_{\eta(i)}=n_i\quad(i\in[m]),\qquad
\mathcal A_{F'}=\{T_\eta a:a\in\mathcal A_F\},
\tag{29.16}
$$

则其核心逐坐标对应，五个数值目标相等：

$$
\begin{gathered}
\Gamma_{F'}(\eta(S))=T_\eta\Gamma_F(S)
\quad(\varnothing\ne S\subseteq[m]),\qquad
\mathcal V_{F'}=T_\eta\mathcal V_F,\\
(D,R,R_{\mathrm u},W,W_{\mathrm u})(F')
 =(D,R,R_{\mathrm u},W,W_{\mathrm u})(F).
\end{gathered}
\tag{29.17}
$$

这是实际族之间对本合同的充分资料；不附带该资料的必要性、极小性或任意抽象响应表的实际可实现性。两个族各自使用自己的真实地址、代表、完整叶测试及后备。

**证明。** 对 $a'=T_\eta a$ 有 $a'_{\eta(i)}=a_i$，所以响应孩子满足 $\eta(S_{a,y})=\eta(S)_{a',y}$，报告字母及其 $\chi$ 相同，有用菜单也通过 $T_\eta$ 一一对应。单点递归的零向量对应；对 $|S|$ 归纳，式（29.3）的每个孩子向量及每个拼接贡献逐坐标对应，得到式（29.17）的 $\Gamma$ 等式。叶数的同一置换再给核心等式。对应的有限概率质量在核心间搬运，保留 $\max_i v_i$、各坐标均值的最大值以及 $\sum_vp_v\max_i v_i$，因此定理 29.3 的有限表达式给全部五个目标相同；有理最优质量也被保留。

对应只涉及实际原型上的完整联合向量。若 $r_F(a)$ 与 $r_{F'}(T_\eta a)$ 为不同地址，它们在各自原型族上分别实现所需向量；定理 29.2 各自在原合同下编译实际控制器，定理 29.3 各自把相同最优数值质量变为实际混合。故不需要跨族继承缓存或转移旧地址的记录，也没有证明在两个原型族之外的响应、行为或费用相同。共同叶数没有抹去叶标签与形状，完整向量集合没有被改成边缘响应或任意行可重排的局部数据；所有向量必须使用同一个置换 $\eta$。

式（29.5）只给一个实际可取得、逐坐标向下支配原评价费用的有限集合，式（29.7）只给同一有限混合的共同积分比较；它们未给全部可实现费用的向上集合等式。式（29.3）忽略地址重数的合法性限于纯只读、固定四值、不同地址收费及终端完整叶基线；实际缓存仍在控制器中。若改变为历史相关费用、许可变化、扰动或其他状态，前述常值删减与基线计费的假设不再由本合同供应，不能据此消去这些状态。全部叶证书只调用 $d=3$ 的既有适用范围，完整树来源、组成、规范数量地址、原始报告、组成祖先许可与实际逆执行保持不同。本结论的量词不含其他替换深度、物理对应、统一全树运行时间界或时间及位复杂度界；有限实际描述供应构造，但任意原随机策略的质量选择仅为存在结论。证毕。

## 追加锚（本行以下为增补区）

## 30. 实际三步像的分歧前沿、七叶分离与有限容量

**定义 30.1（等规模实际像与共享叶）。** 固定定义 23.1、29.1 的 $d=3$ 原始只读合同。来源域仍为全部非空有限自由有序满二叉 $\alpha/\beta$ 树 $\mathcal T$，正来源集合为 $\mathcal I_3=\rho^3(\mathcal T)$；来源相等保留字面括号、次序和叶标签。有限评价族的共同叶数只约束评价对象，不给未知输入任何组成、叶数、高度、正性或候选身份承诺。所有有限左右地址均合法，报告仍为同一不变来源的四值，费用仍计真实缓存后的不同实际地址。

对任意树 $P,Q$，记

$$
\begin{gathered}
n(P)=|L(P)|,\qquad
s(P,Q)=|L(P)\cap L(Q)|,\qquad
\nu(P,Q)=|L(P)\setminus L(Q)|=n(P)-s(P,Q),\\
\operatorname{NC}(P,Q)\quad\Longleftrightarrow\quad
\forall u\in L(P)\cap L(Q),\ \lambda_P(u)=\lambda_Q(u).
\end{gathered}
\tag{30.1}
$$

$\operatorname{NC}$ 只要求共享叶地址上的标签一致；它允许在同一地址分别报告叶、分支或不存在。沿用命题 23.3 的字面树

$$
E=\langle\beta,\alpha\rangle,\qquad
A=\langle E,\beta\rangle=\rho^3(\alpha),\qquad
C=\langle A,E\rangle=\rho^3(\beta),\qquad
B=\langle C,A\rangle.
\tag{30.2}
$$

它们的叶数分别为 $2,3,5,8$。由原替换的二叉同态规则，每个 $P\in\mathcal I_3$ 按其前像根类型写成 $A$、$C$ 或 $\langle X,Y\rangle$，其中 $X,Y\in\mathcal I_3$。该前像和相应递归解析的唯一性直接采用[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的单射性；这是对既有实际像的解析，不将组成点或任意响应表当作完整树。原语法、替换及编码分别沿用[母卷定义 2.1、3.1、9.1 与定理 9.2、9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)。

**引理 30.2（原子像与复合像的全部非冲突比较）。** 对 $X,Y\in\mathcal I_3$，原子像之间只有相同者满足 $\operatorname{NC}$。原子像与复合像的比较恰为以下情形：

$$
\begin{aligned}
\operatorname{NC}(A,\langle X,Y\rangle)
&\Longleftrightarrow X\ne A,\\
\operatorname{NC}(C,\langle X,Y\rangle)
&\Longleftrightarrow
Y\ne A\ \land\
\left(X=A\ \lor\
\bigl(\exists X_1,X_2\in\mathcal I_3,
X=\langle X_1,X_2\rangle\ \land\ X_1\ne A\bigr)\right).
\end{aligned}
\tag{30.3}
$$

第一行成立时，共享叶数为零，$n(\langle X,Y\rangle)\ge8$，且大小恰为 $8$ 的唯一可能是 $\langle X,Y\rangle=B$。第二行中，若 $X=A$，共享叶数恰为 $3$，两侧未共享叶数分别为 $2$ 和 $n(Y)\ge5$；若 $X$ 为其中的复合像，共享叶数为零，且 $n(X)\ge8$、$n(Y)\ge5$。因此每个非冲突的原子／复合比较中，原子侧严格较小，原子侧至少有 $2$ 片未共享叶，复合侧至少有 $5$ 片未共享叶；两侧总叶数分别至少为 $3$ 和 $8$。

**证明。** 每个实际三步像的根和左孩子都是分支：$A,C$ 的字面描述满足这一点，复合像的两个孩子本身都是实际三步像。按唯一前像的结构归纳，原子前像给大小 $3$ 或 $5$，分支前像的两个子像各至少有 $3$ 片叶，故每个实际像至少有 $3$ 片叶，复合像至少有 $6$ 片叶。因此大小 $3$ 只可能为 $A$；除 $A$ 外至少有 $5$ 片叶，大小 $5$ 只可能为 $C$。

$A$ 与 $C$ 在共同叶地址 $\mathtt{LR}$ 分别标记 $\alpha$ 与 $\beta$，故它们不满足 $\operatorname{NC}$。相同原子像则当然满足，穷尽了原子／原子比较。

$A$ 的叶地址是 $\mathtt{LL},\mathtt{LR},\mathtt R$。在 $\langle X,Y\rangle$ 中，$\mathtt R$ 的子树为 $Y$，$\mathtt{LL}$ 的子树为 $X$ 的左孩子，二者都为分支。若 $X=A$，地址 $\mathtt{LR}$ 在复合像中标记 $\beta$，与 $A$ 的 $\alpha$ 冲突。若 $X\ne A$，则 $X=C$ 或 $X$ 为复合像；其右孩子分别为 $E$ 或一个实际像，都为分支。因此 $A$ 的三个叶地址在该复合像中全部是分支，两树没有共享叶，且 $\operatorname{NC}$ 成立。此时 $n(X)\ge5$、$n(Y)\ge3$；大小 $8$ 强制 $X=C,Y=A$，得到唯一的 $B$。

比较 $C=\langle A,E\rangle$ 与 $\langle X,Y\rangle$ 时，$\operatorname{NC}$ 分别限制左子树 $A,X$ 和右子树 $E,Y$。$E$ 的叶地址是 $\mathtt L,\mathtt R$。若 $Y=A$，右端标签分别为 $\alpha,\beta$，发生冲突。若 $Y\ne A$，则 $Y=C$ 或为复合像；其左右孩子都是分支，故 $E,Y$ 没有共享叶，此时 $n(Y)\ge5$。左侧比较中，$X=A$ 给出完全相同的三片叶；$X=C$ 已被原子／原子冲突排除；$X=\langle X_1,X_2\rangle$ 时，已证的第一行说明它恰在 $X_1\ne A$ 时合法，且没有共享叶、$n(X)\ge8$。左右地址不交，故共享叶数和未共享叶数按两侧相加，得到全部陈述。原子侧大小为 $3$ 或 $5$，复合侧在相应情形至少为 $8$、$8$ 或 $13$，所以大小关系严格。证毕。

**引理 30.3（唯一前像上的有限分歧前沿与加法分解）。** 设 $P,Q\in\mathcal I_3$、$P\ne Q$ 且 $\operatorname{NC}(P,Q)$。存在有限非空前缀自由地址集 $H$，使得对每个 $w\in H$，两棵子树 $P_w=P|_w,Q_w=Q|_w$ 恰是一侧原子像、另一侧复合像的非冲突比较；在全部集合 $w\Sigma$（$w\in H$）之外，两树的四值报告相同。存在非负整数 $h_0$，为这些孔以外相同部分的叶数，满足

$$
\begin{aligned}
n(P)&=h_0+\sum_{w\in H}n(P_w),&
n(Q)&=h_0+\sum_{w\in H}n(Q_w),\\
s(P,Q)&=h_0+\sum_{w\in H}s(P_w,Q_w),\\
\nu(P,Q)&=\sum_{w\in H}\nu(P_w,Q_w),&
\nu(Q,P)&=\sum_{w\in H}\nu(Q_w,P_w),\\
n(P)-n(Q)&=\sum_{w\in H}\bigl(n(P_w)-n(Q_w)\bigr).
\end{aligned}
\tag{30.4}
$$

这里 $\Sigma=\{\mathtt L,\mathtt R\}^{<\mathbb N}$，$w\Sigma$ 包含孔根 $w$。每项大小差非零；其符号由原子／复合的朝向决定。

**证明。** 取既有单射性供应的唯一前像 $p,q$。在共同地址处递归比较前像子树。如果两前像子树相同，保留该相同子树并停止比较；若两者都是分支，保留共同的有序二叉节点，分别比较左右孩子；若恰有一者是原子，记录该地址为孔并停止比较。两者为不同原子的情形不可能出现：其像是 $A,C$，引理 30.2 给出局部共享叶标签冲突，而在共同地址前加同一个前缀会把它变成 $P,Q$ 的共享叶标签冲突。$\operatorname{NC}$ 因而排除了该情形。

每次递归进入更小的有限前像子树，所以比较有限终止；停止后不再比较该孔的后代，故 $H$ 前缀自由。若 $H$ 为空，所有终端前像子树都相同，共同构造逐层给出 $p=q$，从而 $P=Q$，矛盾。因此 $H$ 非空。替换保持每个原有二叉节点及其左右地址；在孔处，前像的原子或分支分别替换为原子像或复合像。任何该处的共享叶都前加同一个 $w$，所以其局部比较仍满足 $\operatorname{NC}$。

共同二叉节点、相同终端子树和记录的孔构成一个有限有序满二叉上下文；替换后，相同终端子树仍相同。孔外地址若在共同部分中，其四值报告相同；若越过共同部分的一片叶，其报告在两侧都为不存在。取 $h_0$ 为这些相同终端像的总叶数。孔的地址互不为前缀，因而不同孔内的叶地址集合不交，也不与共同部分的叶相交。全部叶恰由这些集合分割，共享叶也逐孔分割。由此得到前三个叶数等式，未共享叶和大小差等式随即由相减得到。各孔满足引理 30.2，其原子侧严格较小，故每个局部大小差均非零。证毕。

**定理 30.4（等规模非冲突实际像的七叶分离）。** 对任意不同的 $P,Q\in\mathcal I_3$，若 $n(P)=n(Q)=n$ 且 $\operatorname{NC}(P,Q)$，则

$$
\boxed{\qquad
n\ge11,\qquad
\nu(P,Q)=\nu(Q,P)\ge7,\qquad
s(P,Q)\le n-7.
\qquad}
\tag{30.5}
$$

未共享叶的常数 $7$ 在实际同组成来源中达到。具体地，

$$
\begin{gathered}
P_{13}=\langle C,\langle A,C\rangle\rangle
 =\rho^3\bigl(\langle\beta,\langle\alpha,\beta\rangle\rangle\bigr),\\
Q_{13}=\langle\langle A,C\rangle,C\rangle
 =\rho^3\bigl(\langle\langle\alpha,\beta\rangle,\beta\rangle\bigr),\\
c(P_{13})=c(Q_{13})=(5,8)^{\mathsf T},\qquad
n(P_{13})=n(Q_{13})=13,\qquad s(P_{13},Q_{13})=6.
\end{gathered}
\tag{30.6}
$$

**证明。** 在引理 30.3 的分解中，全部非零大小差的和为零。因此至少有一个孔在 $P$ 侧为原子像，另一个孔在 $Q$ 侧为原子像；只有一种朝向时，所有差同号，不可能相加为零。在这两个不同的孔上，$P$ 分别含有至少 $3$ 和至少 $8$ 片叶，$Q$ 也分别含有至少 $8$ 和至少 $3$ 片叶。其余项非负，故 $n\ge11$。同样，引理 30.2 使 $P$ 在这两孔分别至少有 $2$ 和 $5$ 片未共享叶，$Q$ 分别至少有 $5$ 和 $2$ 片；式（30.4）遂给两侧至少为 $7$。等叶数使两个未共享叶数相等，再用式（30.1）得到共享叶上界。

式（30.6）的前像由替换同态规则直接给出，两个前像字面不同，既有单射性供应像的不同性。比较 $C$ 与 $\langle A,C\rangle$ 时，引理 30.2 的 $X=A,Y=C$ 情形恰共享左侧的三片 $A$ 叶，其他叶均不共享，且共享标签相同。在根的左右孩子处各作一次相反朝向的该比较，所以 $P_{13},Q_{13}$ 满足 $\operatorname{NC}$，恰有以下六个共同带标签叶：

$$
\begin{array}{c|cccccc}
u&\mathtt{LLLL}&\mathtt{LLLR}&\mathtt{LLR}&\mathtt{RLLL}&\mathtt{RLLR}&\mathtt{RLR}\\
\lambda(u)&\beta&\alpha&\beta&\beta&\alpha&\beta
\end{array}
\tag{30.7}
$$

$A$ 的组成为 $(1,2)^{\mathsf T}$，$C$ 的组成为 $(2,3)^{\mathsf T}$，每棵所示树都由一个 $A$ 和两个 $C$ 组成，故组成为 $(5,8)^{\mathsf T}$、叶数为 $13$，两侧各有 $13-6=7$ 片未共享叶。这只取得式（30.5）的分离常数，不给后续容量上界的取等构造。证毕。

**定理 30.5（最小十一叶规模的完整分类）。** 对任意不同的 $P,Q\in\mathcal I_3$，若 $n(P)=n(Q)=11$ 且 $\operatorname{NC}(P,Q)$，则其无序对必为

$$
\boxed{\quad
\{P,Q\}=\{\langle A,B\rangle,\langle B,A\rangle\},
\qquad B=\langle C,A\rangle.
\quad}
\tag{30.8}
$$

反之，该对满足这些条件。它字面上就是命题 23.3 在 $d=3$ 时的 $P_{\mathrm{dis}},Q_{\mathrm{dis}}$；特别地，任意两两不同、两两 $\operatorname{NC}$ 的十一叶实际像族至多有两个元素。

**证明。** 在引理 30.3 的前沿中，定理 30.4 的证明已给两个相反朝向的孔。在 $P$ 中，这两孔的叶数下界之和为 $3+8=11$。既然总叶数恰为 $11$，这两个下界都取等，没有其他孔，也没有共同部分的叶，即 $h_0=0$。$Q$ 中同样强制叶数为 $8+3$。因此每个孔的原子侧都恰为三叶的 $A$，复合侧都恰为八叶；引理 30.2 的唯一八叶情形强制该复合侧为 $B=\langle C,A\rangle$。

比较上下文没有相同终端子树，因为任一这样的实际像至少贡献三片共同部分的叶，与 $h_0=0$ 矛盾。其终端恰为两个孔；一个有两个终端的有限满二叉上下文只能是根的左右两个孔：根为分支后，若任何一侧再分支，终端数就至少为三。因此孔地址恰为 $\mathtt L,\mathtt R$，两侧朝向相反，得到式（30.8）。

反向所需的实际前像、十一叶大小及无共享叶性质直接采用[命题 23.3 的式（23.7）—（23.9）、（23.13）](#23-全有限来源上两个指定正例的共同最优地址费用)，不另建来源对。若一个两两非冲突的十一叶族含任意两个不同元素，式（30.8）已固定这两个元素；第三个不同元素与其中任一个成对时仍须得到同一个无序对，故不能存在。证毕。

**定义 30.6（固定叶数的零超额容量）。** 对 $n,t\in\mathbb N_0$，令

$$
\begin{gathered}
\mathcal I_3(n)=\{P\in\mathcal I_3:n(P)=n\},\qquad
\mathcal N=\{3p+5q:p,q\in\mathbb N_0, p+q\ge1\},\\
K(F)=\left\{S\subseteq F:\exists\pi\in\mathfrak D_3,
\forall P\in S, C_\pi(P)=n(P)\right\},\qquad
K_\circ(F)=\{\varnothing\}\cup\{\{P\}:P\in F\},\\
\mathsf{Cap}(n,t)=\max\left\{|F|:
F\subseteq\mathcal I_3(n),\ F\text{ 有限},\
K(F)=K_\circ(F),\ D(F)\le n+t\right\}.
\end{gathered}
\tag{30.9}
$$

$D$ 对非空族仍是式（29.4）的全域确定性最坏取得费用；只为该容量定义约定 $D(\varnothing)=0$。空族允许，空或不可行叶数的容量取零。由[定理 25.2](#25-有限正来源族的遗传共享叶分离与四元共同费用)，$K(F)$ 亦等于共同取得全部个体最优期望所定义的复形。实际三步像的有限计数直接复用[第 12 章式（12.3）、（12.15）](#12-完整树替换像的计数密度祖先混合与共轭来源偏差)，记

$$
N_n=|\mathcal I_3(n)|=
\sum_{\substack{p,q\ge0,\ p+q\ge1\\3p+5q=n}}
\mathrm{Cat}_{p+q-1}\binom{p+q}{p},
\qquad
\mathrm{Cat}_j=\frac1{j+1}\binom{2j}{j},
\tag{30.10}
$$

空和为零；因此式（30.9）取有限集合上的最大值。这里的 Catalan 形状及有序叶着色计数沿用第 12 章所引 [Flajolet–Sedgewick，*Analytic Combinatorics*，第 6–7 页](https://algo.inria.fr/flajolet/Publications/book.pdf) 与 [Stanley，*Enumerative Combinatorics* 第二卷，习题 6.19(b)、(d)](https://math.mit.edu/~rstan/ec/catalan.pdf)。另定义用于路由计数的整数函数

$$
M(0,t)=M(r,0)=1\quad(r,t\ge0),\qquad
M(r,t)=M(r-1,t)+2M(r,t-1)\quad(r,t\ge1).
\tag{30.11}
$$

该函数的边界值 $1$ 是单个终端队列的计数界；它不是空孩子的元素数，空孩子始终贡献零。

**定理 30.7（实际分离约束下的有限容量上界）。** 设 $n\ge11$、$t\in\mathbb N_0$，$F\subseteq\mathcal I_3(n)$ 为非空有限族。若 $K(F)=K_\circ(F)$ 且 $D(F)\le n+t$，则

$$
\boxed{\quad
|F|\le M(n-6,t)
=\sum_{j=0}^{t}2^j\binom{n+j-7}{j},\qquad
\mathsf{Cap}(n,t)\le\min\{N_n,M(n-6,t)\}.
\quad}
\tag{30.12}
$$

对任意 $r\ge1,t\ge0$，式（30.11）的闭式为 $M(r,t)=\sum_{j=0}^t2^j\binom{r+j-1}{j}$。式（30.12）亦适用于将费用前提替换为 $W(F)\le n+t$ 或 $W_{\mathrm u}(F)\le n+t$ 的情形。

**证明。** 任意不同的 $P,Q\in F$ 都满足 $\operatorname{NC}(P,Q)$。否则它们有标签冲突的共享叶，即 $\Delta(\{P,Q\})\ne\varnothing$；对二元素族，定理 25.2 的全部非单元素子族只有它自身，所以该对属于 $K(F)$，与 $K(F)=K_\circ(F)$ 矛盾。于是定理 30.4 使任意不同的两者共享叶数至多为 $n-7$。

直接使用[定理 29.2、29.3 的式（29.5）、（29.6）、（29.8）](#29-任意有限实际正来源族的联合响应费用核心与全域取得)：$D(F)$ 由一个实际代表严格分裂路由及其全域正确总控制器取得。选择达到该最小值的路由树。每个非空孩子都是当前队列的真子集，终端是单点；同一路径的实际地址不重复。对任一原型 $P$，终端完整叶核对后费用恰为 $n$ 加该同一实际路径上的非叶报告数。因此在每条原型路由路径上，报告分支或不存在的地址数至多为 $t$。

固定这棵路由树中的一个非空队列 $S$。令 $f$ 为到此为止实际请求且报告叶的不同地址数，$c$ 为到此为止实际请求且报告分支或不存在的不同地址数。该节点的全部幸存原型具有同一个实际地址—响应历史；所以这 $f$ 个地址在每个原型中都确为同标签叶，这 $c$ 个地址在每个原型中都确为非叶。$f,c$ 来自同一历史，不从不同原型的分别最优运行拼接。

若 $|S|\ge2$，任选其两个不同原型，它们共享这 $f$ 片叶，因而 $f\le n-7$。故 $f=n-6$ 时队列已为单点。在任一严格分裂地址处，非冲突性还使至多一个叶响应孩子非空：若两个不同叶标签孩子都非空，从各取一个原型就会在该地址产生冲突。其余可能孩子只有分支和不存在两个，每个均使 $c$ 增加一；叶响应孩子使 $f$ 增加一。因此每个严格节点至多有一个不增加超额的孩子、两个增加一笔超额的孩子。严格分裂至少有两个非空响应孩子，故至少有一个非叶孩子。若 $c=t$ 仍有严格节点，选择该非叶孩子中的一个原型，其后续终端非叶数至少为 $t+1$，与所有原型路径的超额界矛盾。所以 $c=t$ 时队列也已为单点。

路由到单点即停止，故从严格节点的一次请求至多使 $f$ 从 $n-7$ 增至 $n-6$，不能再超过该值；各路径的终端超额界也给 $c\le t$。在节点处写非负剩余计数参数为 $r=n-6-f$、$b=t-c$。空孩子贡献零；单点终端贡献一。上段说明，$r=0$ 或 $b=0$ 的非空队列只能为单点。对于 $r,b\ge1$ 的严格节点，至多一个叶孩子具有参数 $(r-1,b)$，至多两个非叶孩子具有参数 $(r,b-1)$。按 $r+b$ 归纳，该子树的单点终端总数至多为

$$
M(r-1,b)+2M(r,b-1)=M(r,b).
\tag{30.13}
$$

缺失孩子的零贡献仍不超过相应项；不能把缺失孩子替换为一个实际单点。每个原型沿其真实报告恰到一个单点终端，根节点的参数为 $(n-6,t)$，于是 $|F|\le M(n-6,t)$。这是对已取得的实际路由的资源路径计数；式（30.11）的初等计数只作中间步骤。承重限制是实际像的七叶分离，以及它把同一历史的叶报告阈值降为 $n-6$。一般有限认证树的形状分解可参见[延拓卷定义 11.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md#11-自适应分辨率何时可以停止递归)；其固定动作价格不替代这里扣除完整叶基线后、依实际响应取值的超额。

为求闭式，令 $S_r(t)=\sum_{j=0}^t2^j\binom{r+j-1}{j}$，$r\ge1$。$S_r(0)=1$，且 $S_1(t)=2^{t+1}-1$ 满足 $S_1(t)=1+2S_1(t-1)$。$r\ge2,t\ge1$ 时，Pascal 恒等式给

$$
\begin{aligned}
S_r(t)-2S_r(t-1)
&=1+\sum_{j=1}^t2^j
\left[\binom{r+j-1}{j}-\binom{r+j-2}{j-1}\right]\\
&=\sum_{j=0}^t2^j\binom{r+j-2}{j}=S_{r-1}(t).
\end{aligned}
\tag{30.14}
$$

故它满足式（30.11）的全部所需边界及递推，按 $r+t$ 归纳即为 $M(r,t)$。代入 $r=n-6$，再用 $|F|\le N_n$，得到式（30.12）的容量结论；空评价族的大小零也满足该上界。$W(F)=W_{\mathrm u}(F)=D(F)$ 直接取自式（29.8），所以所列替换前提等价于本前提，没有把逐来源期望最大值 $R$ 或 $R_{\mathrm u}$ 代入同一证明。

最后核对原判定合同。$f=n-6$ 的结论只识别当前评价队列，不把未读叶变成缓存报告，也不允许据此接受未知来源。在原型 $P$ 上，路由已取得的 $f$ 个叶地址属于 $L(P)$；单点测试仍须真实请求全部 $n$ 个带标签叶，复用的仅是此前真实取得的相同地址，尚缺的 $n-f$ 个叶地址全部补查。路由的 $c$ 个非叶地址不属于 $L(P)$，实际付费地址总数因此仍为 $f+c+(n-f)=n+c$。完整叶认证及必要性采用[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)的 $d=3=3\cdot1$ 范围。意外路由响应或任一叶核对不匹配，都由定理 29.2 的独立初始化、保留真实外层缓存的全域有限后备处理；后备恢复实际有限输入并作有限前像比较，处理整个 $\mathcal T$，不把不匹配当成负性证明。本证明不增加输入承诺，不授予实际逆执行，也不改变地址长度不收费的约定。证毕。

**推论 30.8（可行叶数与十一叶容量的锐值）。** 定义 30.6 的可行叶数恰为

$$
\mathcal N=\{3,5,6\}\cup\{n\in\mathbb N:n\ge8\}.
\tag{30.15}
$$

若 $n\notin\mathcal N$，则对每个 $t\ge0$ 有 $\mathsf{Cap}(n,t)=0$，特别地 $\mathsf{Cap}(0,t)=0$。若 $n\in\mathcal N$ 且 $n<11$，则对每个 $t\ge0$ 有 $\mathsf{Cap}(n,t)=1$。对所有可行 $n$，还有 $\mathsf{Cap}(n,0)=1$。在最小非平凡规模，

$$
\boxed{\qquad
N_{11}=6,\qquad
\mathsf{Cap}(11,t)=
\begin{cases}
1,&t=0,\\
2,&t\ge1.
\end{cases}
\qquad}
\tag{30.16}
$$

$t\ge1$ 时取得二元素容量的族唯一为式（30.8）的旧来源对，其全域确定性最坏费用为 $12$。

**证明。** 对前像组成 $(p,q)^{\mathsf T}$，母卷定理 3.4 的组成作用给三步像组成 $(p+2q,2p+3q)^{\mathsf T}$，叶数为 $3p+5q$。每个非零 $(p,q)$ 均由实际自由树实现；第 12 章既有像双射与 Catalan 计数按这些组成分别相加，正是式（30.10），不重复建立树形计数。$3,5,6$ 可行，$8,9,10$ 分别为 $3+5,3+3+3,5+5$，再逐次加 $3$ 得所有 $n\ge8$。其余非负整数 $0,1,2,4,7$ 不能写成允许的 $3p+5q$，所以得到式（30.15）。不可行时只有空评价族，容量为零。可行时任取一棵对应实际像，其单元素族满足 $K=K_\circ$；定理 29.3 的单元素情形与定理 18.2 的完整叶下界已给 $D=n$，故对任何 $t\ge0$ 容量至少为一。

$K(F)=K_\circ(F)$ 已由定理 30.7 证明中的定理 25.2 应用迫使两两 $\operatorname{NC}$；该应用不依赖 $n\ge11$。若 $n<11$，定理 30.4 排除任意两个不同元素，故容量至多为一。对任意可行 $n$，若非空族满足 $D(F)\le n$，定理 29.3 取得该最小值的全域确定性策略在每个原型上费用至多为 $n$；定理 18.2 又使每个费用至少为 $n$。于是同一个策略共同取得全部个体最优，整个 $F$ 属于 $K(F)$。在 $K=K_\circ$ 条件下只能有 $|F|=1$，得到所有可行规模的零超额容量。

$3p+5q=11$ 的唯一解为 $(p,q)=(2,1)$，式（30.10）遂给 $N_{11}=\mathrm{Cat}_2\binom32=2\cdot3=6$。定理 30.5 已完整分类其中的非冲突对，故满足所需复形的族至多有两个元素，且二元素族只能是式（30.8）。该旧来源对无共享叶，定理 25.2 给出其复形恰为空集与单点。其原全域取得锐值 $D_3^+(P_{\mathrm{dis}},Q_{\mathrm{dis}})=12$ 直接采用[命题 23.3 的式（23.12）](#23-全有限来源上两个指定正例的共同最优地址费用)，不重证或改名交付旧费用定理。因此 $t\ge1$ 时该对达到容量二，$t=0$ 时只有容量一，得到式（30.16）。

七叶常数的取等与十一叶容量的取等是两个不同陈述；前者由式（30.6）取得，后者由完整分类及既有费用定理取得。式（30.12）对一般 $n,t$ 只给上界，没有断言其可取得或为锐值；逐来源期望目标 $R,R_{\mathrm u}$ 不由该确定性容量证明控制。上述对象及关系全部属于指定自由树、实际替换、原始地址报告和全域成员判定合同，组成守恒或形式代数的可逆性不作为物理对应或实际逆执行许可。证毕。

## 追加锚（本行以下为增补区）

## 31. 任意地址叶报告的块强制、单孔刚性与容量阈值

**定义 31.1（正评价族、实际历史与叶报告队列）。** 沿用[定义 29.1](#29-任意有限实际正来源族的联合响应费用核心与全域取得)的全有限树只读合同，固定 $d=3$。原始语法与替换仍为[母卷定义 2.1、3.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md#2-原始语法与结构解释)的

$$
\mathcal T:\quad U::=\alpha\mid\beta\mid\langle U,U\rangle,\qquad
\rho(\alpha)=\beta,\quad
\rho(\beta)=\langle\beta,\alpha\rangle,\quad
\rho(\langle X,Y\rangle)=\langle\rho(X),\rho(Y)\rangle .
\tag{31.1}
$$

相等保持左右次序、括号与叶标签。记 $\mathcal I_3=\rho^3(\mathcal T)$、$\Sigma=\{\mathtt L,\mathtt R\}^{<\mathbb N}$；所有 $u\in\Sigma$，包括 $\varepsilon$，均可直接查询同一不变输入的原始四值 $\mathsf{leaf}_\alpha,\mathsf{leaf}_\beta,\mathsf{branch},\mathsf{absent}$。未知输入始终遍历整个 $\mathcal T$。确定性策略属于 $\mathfrak D_3$，在全域正确且有限终止；费用只计真实缓存后的不同实际地址，计算、定位与地址长度不收费。

取整数 $m\ge1$ 及两两不同的评价对象 $F=(P_i)_{i\in[m]}$，其中每个 $P_i\in\mathcal I_3$ 有 $n$ 片叶。由[规范编译卷命题 4.3](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md#4-tree-action-seed-recurrence-and-composition-dynamics)的替换单射性复合三次，记其唯一前像为 $Q_i$，写 $c(Q_i)=(a_i,b_i)^{\mathsf T}$。令

$$
\Lambda_\alpha(P)=\{u\in\Sigma:\operatorname{out}_P(u)=\mathsf{leaf}_\alpha\},
\qquad
n=3a_i+5b_i,\qquad
s_i=|\Lambda_\alpha(P_i)|=a_i+2b_i,\qquad
s=\max_{i\in[m]}s_i .
\tag{31.2}
$$

式（31.2）的组成关系直接取自[母卷定理 3.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md#3-fibonacci-替换与组成动力学)。$s$ 数的是像树的 $\alpha$ 叶，不是前像的 $\alpha$ 叶。

有限实际请求—响应历史写为 $H=((u_j,y_j))_{j=1}^{\ell}$，允许一般历史含缓存重复请求。记 $H^{\mathrm{leaf}}$ 为其中报告叶的子列。定义

$$
\begin{aligned}
S_H&=\{i\in[m]:\forall j,\ \operatorname{out}_{P_i}(u_j)=y_j\},\\
\mathcal E_H&=\{P\in\mathcal I_3:
 \forall (u,y)\in H^{\mathrm{leaf}},\ \operatorname{out}_P(u)=y\},\\
f(H)&=|\{u_j:y_j\in\{\mathsf{leaf}_\alpha,\mathsf{leaf}_\beta\}\}|,\\
c(H)&=|\{u_j:y_j\in\{\mathsf{branch},\mathsf{absent}\}\}|.
\end{aligned}
\tag{31.3}
$$

以下只在 $S_H\ne\varnothing$ 时使用评价历史，故 $\mathcal E_H$ 非空。$\mathcal E_H$ 是只保留先前叶报告的正来源比较集合，不要求成员匹配非叶报告；$P_i$ 在 $i\in S_H$ 时属于它。严格路由节点在当前 $S_H$ 上选择至少有两个非空四值响应孩子的实际地址。历史、队列及后面的块强制仅描述同一次实际路由；逻辑推论不增加缓存条目，也不使未知输入取得正性、同叶数或候选身份承诺。

**引理 31.2（任意地址的完整位置分类与小子树唯一性）。** 采用[式（30.2）](#30-实际三步像的分歧前沿七叶分离与有限容量)的字面树

$$
E=\langle\beta,\alpha\rangle,\qquad
A=\langle E,\beta\rangle=\rho^3(\alpha),\qquad
C=\langle A,E\rangle=\rho^3(\beta).
\tag{31.4}
$$

对任意 $P=\rho^3(Q)\in\mathcal I_3$，$Q$ 的每片叶地址 $v$ 对应一个规范块：该叶标记 $\alpha$ 时 $P|_v=A$，标记 $\beta$ 时 $P|_v=C$。这些规范块的根前缀自由。每个任意地址 $u\in\Sigma$ 恰属于以下位置之一：

1. $u$ 是 $Q$ 的内部节点地址；此时 $P|_u=\langle X,Y\rangle$，其中 $X,Y\in\mathcal I_3$。
2. $u$ 是 $Q$ 的叶地址；此时它是一个规范 $A$ 或 $C$ 块的根。
3. $u=vz$，其中 $v$ 是 $Q$ 的叶地址，$z$ 非空，且它位于该规范块内。全部存在的真偏移及子树为

$$
\begin{array}{c|c|c}
\text{规范块}&z&P|_{vz}\\ \hline
A&\mathtt L&E\\
A&\mathtt{LL}&\beta\\
A&\mathtt{LR}&\alpha\\
A&\mathtt R&\beta\\ \hline
C&\mathtt L&A\\
C&\mathtt{LL}&E\\
C&\mathtt{LLL}&\beta\\
C&\mathtt{LLR}&\alpha\\
C&\mathtt{LR}&\beta\\
C&\mathtt R&E\\
C&\mathtt{RL}&\beta\\
C&\mathtt{RR}&\alpha
\end{array}
\tag{31.5}
$$

4. $u$ 严格延伸某片输出叶地址；此时报告 $\mathsf{absent}$。

因此每个 $A$ 子树出现位置恰为规范 $A$ 根或规范 $C$ 的立即左孩子，每个 $C$ 子树出现位置恰为规范 $C$ 根；每个 $E$ 出现位置恰为某个 $A$ 出现位置的立即左孩子，或某个规范 $C$ 的立即右孩子。在任何正来源的任意存在地址，二叶子树唯一为 $E$，三叶子树唯一为 $A$。根地址也在分类内；正来源的根总是分支，原子根只可能是未知输入的情形。

**证明。** 唯一前像及替换保持原有二叉节点的结论取自规范编译卷命题 4.3 和母卷定义 3.1，不另建立替换解析。若 $u$ 不是 $Q$ 的节点地址，沿 $u$ 在有限满二叉 $Q$ 中行走，必先到达唯一的一片叶 $v$；余下的字只能在该叶的替换块内继续。对式（31.4）列出全部节点，正是式（31.5）。其外地址必已越过块的一片叶，故为不存在。这同时穷尽上下文根、块根、块内分支、输出叶与不存在地址，不要求查询前缀闭合。

[引理 30.2 的证明](#30-实际三步像的分歧前沿七叶分离与有限容量)已给每个正来源至少三叶，复合正来源至少六叶。第一类地址因而不能产生二叶或三叶子树，第二类大小为三或五；第三类表中，二叶只有 $E$，三叶只有 $A$。同表又给 $A,C,E$ 的全部出现位置及所述父子关系。证毕。

**定义 31.3（由实际叶报告强制的块与被覆盖 $\alpha$）。** 对每个正来源兼容的叶报告，按下表定义唯一的强制块 $(w,T)$，其中 $T\in\{A,C\}$。$w$ 可以是空地址；表中的根不是预先给定的前像地址。

$$
\begin{array}{c|c|c}
\text{实际报告}&\text{强制块}&\text{该块的 }\alpha\text{ 地址}\\ \hline
\operatorname{out}(w\mathtt R)=\mathsf{leaf}_\beta
 &(w,A)&\{w\mathtt{LR}\}\\
\operatorname{out}(w\mathtt{LL})=\mathsf{leaf}_\beta
 &(w,A)&\{w\mathtt{LR}\}\\
\operatorname{out}(w\mathtt{LR})=\mathsf{leaf}_\alpha
 &(w,A)&\{w\mathtt{LR}\}\\
\operatorname{out}(w\mathtt{RL})=\mathsf{leaf}_\beta
 &(w,C)&\{w\mathtt{LLR},w\mathtt{RR}\}\\
\operatorname{out}(w\mathtt{RR})=\mathsf{leaf}_\alpha
 &(w,C)&\{w\mathtt{LLR},w\mathtt{RR}\}
\end{array}
\tag{31.6}
$$

令 $\mathcal B_H$ 为仅对 $H^{\mathrm{leaf}}$ 中实际叶报告应用式（31.6）所得的有限块集合，重复的块只保留一次；令

$$
\Gamma_H=
 \bigcup_{(w,T)\in\mathcal B_H}
 \{wv:v\in\Lambda_\alpha(T)\},
\qquad g(H)=|\Gamma_H|.
\tag{31.7}
$$

$\Gamma_H$ 是由先前叶报告固定的 $\alpha$ 地址并集；不将分支或不存在报告产生的推论加入此集合。它是集合并，不把重叠块重复计数。凡 $P\in\mathcal E_H$，均有 $P|_w=T$ 对所有 $(w,T)\in\mathcal B_H$ 成立，特别地 $\Gamma_H\subseteq\Lambda_\alpha(P)$。块中的其余带标签叶及分支也因此在正比较集合内固定，但仍不是实际缓存报告。

**引理 31.4（五行强制、块重叠与严格叶增益）。** 式（31.6）覆盖正来源的每片叶，且每行强制结论对全部 $\mathcal E_H$ 成立。两个在同一正来源内成立的 $A/C$ 块，只可能相同、根地址互不为前缀，或一个 $C$ 包含其立即左孩子 $A$。若 $H$ 后的下一实际地址 $u$ 在 $S_H$ 上严格分裂，且某个非空孩子报告叶 $y$，则在该孩子的新历史 $H'=H\mathbin{\frown}(u,y)$ 上有

$$
|\Gamma_{H'}\setminus\Gamma_H|\ge1.
\tag{31.8}
$$

因此从空历史开始的严格路由，每个非空队列的共同历史都满足 $g(H)\ge f(H)$。

**证明。** 引理 31.2 的表说明，$\beta$ 叶若是右孩子，其父必为 $A$：$E$ 的右孩子为 $\alpha$，上下文的孩子为正来源分支，不能给另一种 $\beta$ 右端。若 $\beta$ 是左孩子，其父必为 $E$。这个 $E$ 若在其父的左侧，父为 $A$；若在右侧，父为规范 $C$，分别给出后缀 $\mathtt{LL}$ 与 $\mathtt{RL}$ 两行。所有 $\alpha$ 叶都是 $E$ 的右孩子；$E$ 位于左侧或右侧时分别给 $\mathtt{LR}$ 与 $\mathtt{RR}$ 两行。正来源没有根叶，也没有深度一的 $\alpha$ 叶；深度一的 $\beta$ 叶只能是根 $A$ 的右端，已被第一行包含。故没有遗漏空根、短地址或嵌在 $C$ 左侧的 $A$。每一行仅使用正来源和当前的一个实际叶报告，所以凡匹配该报告的正来源都满足整块等式。

比较两个块根。若相同，字面树 $A\ne C$ 使类型也必须相同；若不可比，所在子树不交；若一个严格在另一个内，引理 31.2 的完整真偏移表只允许 $C$ 的立即左孩子为 $A$。特别地，共享 $\alpha$ 地址的两个块必为相同块，或上述 $C/A$ 包含情形。

在新叶孩子中选一个实际原型 $P$，令新报告按表强制块 $(w,T)$。全部旧块与新块都在这一个 $P$ 内成立，故可使用刚证的重叠分类。假设新块的 $\alpha$ 地址全部已在 $\Gamma_H$ 中。若 $T=A$，覆盖其唯一 $\alpha$ 地址的某个旧块必为同一个 $A$，或为包含这个 $A$ 的 $C$；两种情形都使 $P'|_w=A$ 对每个 $P'\in\mathcal E_H$ 已经成立。若 $T=C$，考虑其右侧 $\alpha$ 地址 $w\mathtt{RR}$。它不在该 $C$ 的左 $A$ 内；覆盖它的旧 $A/C$ 块按重叠分类只能是同一个 $C$。因此整个新块在 $\mathcal E_H$ 中也早已固定。两种情形下，地址 $u$ 是这个固定块的指定带标签叶，故对全部 $i\in S_H$ 都给同一个 $y$，与严格分裂矛盾。于是新块至少贡献一个此前未覆盖的 $\alpha$，得到式（31.8）。

严格节点不可能请求历史中已请求的地址，因为该响应在当前幸存队列上恒定。因此每次保留的叶报告使 $f$ 增加一，非叶报告不改变 $f$ 或 $\Gamma_H$。从 $f=g=0$ 开始逐节点应用式（31.8），得 $g\ge f$。这不是任意不同地址叶请求的结论，常值请求不满足严格性。证毕。

**引理 31.5（完整固定前沿、共同字面单孔与同规模正来源刚性）。** 对任意有限历史 $H$、任意 $P\in\mathcal E_H$，若

$$
|\Lambda_\alpha(P)\setminus\Gamma_H|\le1,
\tag{31.9}
$$

则每个 $P'\in\mathcal E_H$ 且 $n(P')=n(P)$ 都等于 $P$。更具体地，没有未覆盖 $\alpha$ 时，全部字面输出树已由强制块固定；恰有一片时，存在一个有限有序字面输出上下文 $J[\square]$ 及孔地址 $h$，使 $P=J[X]$，其中 $X=A$ 或 $X=E$，而每个 $P'\in\mathcal E_H$ 都写成同一个 $J[Y]$。这里的 $J$ 是输出树的字面上下文，不预设 $P,P'$ 有相同前像上下文。

**证明。** 先在 $P$ 自己的唯一前像上定位规范块，随后只使用它们在输出树中的地址和完整标签。若一个规范 $A$ 的 $\alpha$ 已覆盖，覆盖它的旧块按引理 31.4 只能是这个 $A$，或一个包含它的 $C$，所以这个 $A$ 的全部带标签叶固定。若一个规范 $C$ 的右 $\alpha$ 已覆盖，覆盖它的旧块只能是同一个 $C$，所以整个 $C$ 的全部带标签叶固定。若所有 $\alpha$ 均已覆盖，每个规范块因此完整固定；这些规范块的叶并恰为 $P$ 的完整叶前沿。采用[定理 18.2 证明中的完整带标签叶恢复](#18-精确组成最优证书的唯一性与无承诺叶前沿)及[母卷定理 9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md#9-不预置自然数的结构编码)，每个 $P'\in\mathcal E_H$ 都等于 $P$，此时不需要同叶数条件。

现在设唯一未覆盖的 $\alpha$ 地址为 $x$。若它属于规范 $A$，取孔为这个 $A$ 的根 $h$，令 $X=A$。若它属于规范 $C$，它不能是该块左 $A$ 的 $\alpha$：否则该块的右 $\alpha$ 已覆盖，会使整个 $C$ 固定，连 $x$ 也覆盖，矛盾。因此 $x$ 只能是该 $C$ 的右 $\alpha$；左 $\alpha$ 已覆盖，而整个 $C$ 尚未固定。重叠分类遂保证旧块中有该 $C$ 的左 $A$。取孔为此 $C$ 的立即右孩子 $h$，令 $X=E$。这是两种孔位置的全部情形。

除孔所在的特殊块外，每个规范 $A$ 的 $\alpha$、每个规范 $C$ 的右 $\alpha$ 均已覆盖，故其完整叶前沿都固定。在特殊 $C$ 情形，其孔外左 $A$ 的完整叶前沿也固定。因此 $P$ 在 $h\Sigma$ 外的每片带标签叶均位于某个旧固定块内。旧固定块不能穿过孔：在 $A$ 孔情形，任何相交的 $A/C$ 块按重叠分类都会包含 $x$；在右 $E$ 孔情形，位置分类使相交的 $A/C$ 块只能包含这个 $E$，同样会覆盖 $x$。两者均与 $x\notin\Gamma_H$ 矛盾。

把 $P$ 中的 $X$ 换成一个孔，得到字面输出上下文 $J[\square]$。为证明这个上下文对所有 $P'\in\mathcal E_H$ 相同，沿 $\varepsilon$ 到 $h$ 的路径考察每个严格前缀 $z$。该路径的另一个孩子是一个完整非空子树；其每片叶都在孔外，因而其完整带标签叶前沿由旧固定块给出。$P'$ 匹配这些叶：每个叶的真前缀必须为分支，叶本身不能再扩展；完整前沿没有其他可增加节点的位置。于是该旁支的全部四值读数固定，由母卷定理 9.3，它与 $P$ 的旁支字面相等。这个旁支的非空前沿还迫使 $z$ 为分支，所以路径上的下一个孩子以及最终的孔根 $h$ 都在 $P'$ 中存在。逐个旁支得到同一个 $J$，故 $P'=J[Y]$，其中 $Y=P'|_h$。这一步不比较两棵前像，也不假设它们的上下文相同。若 $h=\varepsilon$，没有旁支，$J$ 就是单孔，根存在由非空树语法给出；这包含 $P=A$、$\Gamma_H=\varnothing$ 的根孔情形。

令 $n(J)$ 表示 $J$ 孔外的叶数。由于上下文字面相同，

$$
n(P)=n(J)+n(X),\qquad n(P')=n(J)+n(Y).
\tag{31.10}
$$

同叶数遂给 $n(Y)=n(X)\in\{2,3\}$。此处 $P'$ 的正性使引理 31.2 适用于任意孔地址 $h$：二叶只能为 $E$，三叶只能为 $A$。故 $Y=X$，得到 $P'=P$。没有孔的情形已由完整前沿处理；根孔与非根孔均在上述推导内。证毕。

**命题 31.6（同规模、正性与严格性的必要边界）。** 字面树 $C$ 与 $\langle A,C\rangle$ 都为正来源，并共享立即左子树 $A$，但分别有五叶、八叶；$C$ 与 $\langle A,\langle\alpha,\beta\rangle\rangle$ 共享同一个左 $A$ 且都有五叶，但后者不是正来源。因此，引理 31.5 的同叶数与正性两项均不能删除。不同地址的常值叶请求也可以没有新增被覆盖 $\alpha$。

**证明。** $C=\rho^3(\beta)$，且 $\langle A,C\rangle=\rho^3(\langle\alpha,\beta\rangle)$，两者的叶数由式（31.4）分别为 $5,8$。单个实际报告 $\mathsf{leaf}_\alpha$ 于 $\mathtt{LLR}$ 只强制左 $A$，在 $C$ 中恰留下右侧的一片未覆盖 $\alpha$；所以删除同叶数时，这一历史兼容上述两个不同正来源。另一棵所示五叶树右孩子为 $\langle\alpha,\beta\rangle\ne E$，与 $C$ 字面不同；引理 31.2 的根分类使唯一五叶正来源为 $C$，故它是负来源。同一叶历史也匹配它，说明不能把正队列内的单孔结论扩张到任意未知输入。

在兼容 $C,\langle A,C\rangle$ 的叶历史 $(\mathtt{LLR},\mathsf{leaf}_\alpha)$ 后，再请求不同地址 $\mathtt{LR}$，两者都报告 $\mathsf{leaf}_\beta$。式（31.6）在两次报告中都只强制地址 $\mathtt L$ 处的同一个 $A$，被覆盖并集没有增长。该请求在队列上为常值，故不是严格节点；重复同一请求也必为常值。证毕。

**定理 31.7（实际严格叶增益给出的更低容量阈值）。** 对定义 31.1 的任意非空有限评价族 $F\subseteq\mathcal I_3(n)$ 及任意整数 $t\ge0$，若 $K(F)=K_\circ(F)$ 且 $D(F)\le n+t$，则

$$
\boxed{\quad |F|\le M(s-1,t).\quad}
\tag{31.11}
$$

$K,K_\circ$ 与 $M$ 分别就是[定义 30.6 的式（30.9）、（30.11）](#30-实际三步像的分歧前沿七叶分离与有限容量)，不另定义或改变计数函数。结论覆盖 $s=1$、$t=0$ 及全部可行的小叶数。费用前提可以等价替换为 $W(F)\le n+t$ 或 $W_{\mathrm u}(F)\le n+t$，仅使用既有 $W=W_{\mathrm u}=D$。

**证明。** 由[定理 25.2](#25-有限正来源族的遗传共享叶分离与四元共同费用)，$K(F)=K_\circ(F)$ 迫使不同评价来源两两 $\operatorname{NC}$；这是定理 30.7 证明中已作的同一应用，不要求 $n\ge11$。直接采用[定理 29.2、29.3 的式（29.5）、（29.6）、（29.8）](#29-任意有限实际正来源族的联合响应费用核心与全域取得)，选择取得 $D(F)$ 的实际代表严格路由。它在单点结束，同一路径的实际地址不重复；对每个 $P_i$，接上完整带标签叶核对后的费用恰为 $n$ 加其路由中分支或不存在报告的地址数。因此每条评价路径的最终 $c$ 至多为 $t$。

在任意非空队列 $S_H$ 上，所有成员匹配同一个实际历史。引理 31.4 给 $g(H)\ge f(H)$。若 $f(H)\ge s-1$，任取 $i\in S_H$，有

$$
|\Lambda_\alpha(P_i)\setminus\Gamma_H|
 =s_i-g(H)\le s-f(H)\le1.
\tag{31.12}
$$

引理 31.5 对所有其余幸存成员使用同叶数 $n$，使它们都等于 $P_i$；评价对象两两不同，故 $S_H$ 为单点。因此 $f=s-1$ 已是终端阈值。这个阈值由实际强制块的并集和共同字面单孔供应，不从旧同组成 $\alpha$ 证书推出；这里没有给未知输入组成或叶数。

在严格节点，两两 $\operatorname{NC}$ 使至多一个叶标签孩子非空；其余孩子只能是 $\mathsf{branch}$ 与 $\mathsf{absent}$。叶孩子使 $f$ 增加一而 $c$ 不变，非叶孩子使 $c$ 增加一而 $f$ 不变。严格节点至少有两个非空孩子，故至少有一个非叶孩子。若 $c=t$ 仍严格，选取这个非叶孩子中的一个实际原型，其终端非叶数至少为 $t+1$，与费用界矛盾。因此 $c=t$ 也迫使单点。

现在直接使用[第 30 章式（30.13）的资源路径计数](#30-实际三步像的分歧前沿七叶分离与有限容量)，其参数在这里为 $r=s-1-f(H)$、$b=t-c(H)$。非空边界 $r=0$ 或 $b=0$ 都已证明为单点；每个内部节点至多一个 $(r-1,b)$ 叶孩子、两个 $(r,b-1)$ 非叶孩子，空孩子贡献零。故既有计数 $M(r,b)$ 适用，根给 $M(s-1,t)$ 个单点终端上界。每个实际原型到自己的一个终端，得到式（31.11）。若 $s=1$，空历史已满足式（31.12），根直接是单点，使用 $M(0,t)=1$；若 $t=0$，根由非叶预算边界为单点，使用 $M(s-1,0)=1$。不排除任何可行小 $n$。

终端阈值只识别评价队列，不能替代对未知输入的接受核验。在实际原型上，路由的 $f$ 个叶地址是此前实际取得的叶报告；核对仍真实请求全部 $n$ 个带标签叶，只在请求同一实际地址时命中缓存。路由的 $c$ 个非叶地址不在该原型叶集中，所以实际不同付费地址总数为 $f+c+(n-f)=n+c$，不是 $g+c+(n-g)$ 的虚构缓存账。块强制所推出但未请求的叶仍需实际取得。全叶必要性、充分性与恢复沿用[定理 18.2](#18-精确组成最优证书的唯一性与无承诺叶前沿)的 $d=3=3\cdot1$ 范围；意外路由响应或叶核对不匹配仍按定理 29.2 接入独立初始化、保留真实外层缓存的全域有限后备。不匹配不被直接解释为负性，后备继续处理整个 $\mathcal T$。

最后，式（29.8）的 $W=W_{\mathrm u}=D$ 给两项替换前提；它没有把 $\max_i\mathbb E C_i$ 与 $\mathbb E\max_i C_i$ 互换，也没有将 $R,R_{\mathrm u}$ 纳入此界。证毕。

**推论 31.8（可行规模的组成最大值与一次超额界）。** 仅对[式（30.15）](#30-实际三步像的分歧前沿七叶分离与有限容量)中的可行叶数 $n\in\mathcal N=\{3,5,6\}\cup\{n\ge8\}$，定义

$$
q(n)=\max\{a+2b:a,b\in\mathbb N_0,\ 3a+5b=n,\ a+b>0\}.
\tag{31.13}
$$

对定理 31.7 的全部评价族及 $t\ge0$，有

$$
\boxed{\quad
|F|\le M(s-1,t)\le M(q(n)-1,t),\qquad
q(n)\le\left\lfloor\frac{2n}{5}\right\rfloor,\qquad
\mathsf{Cap}(n,t)\le\min\{N_n,M(q(n)-1,t)\}.
\quad}
\tag{31.14}
$$

特别地，$t=1$ 时 $|F|\le2s-1\le2q(n)-1$。不可行叶数不定义 $q(n)$，其容量零结论仍直接取自推论 30.8。

**证明。** 可行性使式（31.13）的有限集合非空，每个唯一前像组成属于此集合，故 $1\le s\le q(n)$。对每个可行组成，$5(a+2b)=2n-a\le2n$，给所列整数上界。$M$ 对第一参数的单调性及 $M(r,1)=1+2r$ 直接取自式（30.11）和定理 30.7 的既有闭式；$r=0$ 使用原边界 $M(0,t)=1$。结合定理 31.7 与原实际像计数 $N_n$，得到式（31.14）和一次超额结论。

例如 $n=14$ 的唯一前像组成是 $(3,1)$，故 $s=q(14)=5$。当 $t=1$ 时，上界为 $M(4,1)=9$，第 30 章的上界为 $M(8,1)=17$，其式（30.10）给 $N_{14}=20$。这些都是上界比较，不断言存在满足合同的九元素族，不断言一般达到性或锐值。可行小规模及零超额容量仍采用推论 30.8 的原结论。

上述关系均属于自由有序树、实际替换、原始地址响应和全域成员判定。母卷定理 9.2 的编码、规范编译卷命题 4.3 的单射性、定理 18.2 的完整叶条件、第 29 章的实际核心与全域续接、第 30 章的 $M$ 计数各在其原范围内使用。第 17 章及定理 18.1 的精确组成证书、第 19 章的纯数量证书、第 20 章的阶段标量证书分别附加各自读数条件，不能替代本合同的无承诺完整叶核对；有限决策树的文献背景沿用[第 29 章所引响应相关费用模型](#29-任意有限实际正来源族的联合响应费用核心与全域取得)。本结论不授予实际逆执行，不从组成守恒推导物理、时间、量子或 Lorentz 对应，也不声称文献范围外的原创性。证毕。

## 追加锚（本行以下为增补区）
