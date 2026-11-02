# AURIC：复合比较的有限变化见证、共同标定与量子生成

## 1. 内部关系与联合相容

**定义 1.1（活的有限关系球）。** 对每个指标 $s$，取有限维 Euclidean 空间 $V_s$，并令

$$
J_s=\mathbb R1_s\oplus V_s,\qquad
S_s((\alpha,u),(\beta,v))=(\alpha\beta+\langle u,v\rangle,\alpha v+\beta u).
$$

内积为 $g_s((\alpha,u),(\beta,v))=\alpha\beta+\langle u,v\rangle$。另给非零交替双线性映射 $B_s:V_s\times V_s\to V_s$，满足 Jacobi 律与度量不变性

$$
B_s(B_s(u,v),w)+B_s(B_s(v,w),u)+B_s(B_s(w,u),v)=0,
\qquad
\langle B_s(u,v),w\rangle=\langle u,B_s(v,w)\rangle.
$$

把 $B_s$ 延拓为消去单位及标量部分的运算。记 $L_ax=S_s(a,x)$、$D_ax=B_s(a,x)$。度量不变性使 $D_a$ 斜伴随，并直接给出

$$
D_aS_s(x,y)=S_s(D_ax,y)+S_s(x,D_ay).
$$

这里比较的球形、正定性、有限维、局部 Jacobi 及非零变化是明确前件；不从一个空的集合推出这些前件。

**定义 1.2（实联合关系及候选 C96）。** 对两个定义 1.1 的系统 $A,B$，取实代数张量空间 $J_{AB}=J_A\otimes_{\mathbb R}J_B$，使用乘积内积，给实参数 $\lambda$。在简单张量上规定

$$
\begin{aligned}
M_\lambda(a\otimes b,c\otimes d)
&=S_A(a,c)\otimes S_B(b,d)-\lambda B_A(a,c)\otimes B_B(b,d),\\
T(a\otimes b,c\otimes d)
&=B_A(a,c)\otimes S_B(b,d)+S_A(a,c)\otimes B_B(b,d),
\end{aligned}\tag{1.1}
$$

并双线性延拓。$M_\lambda$ 对称，$T$ 交替，$1_A\otimes1_B$ 是前者的单位并被后者消去。定义残差

$$
R_\lambda(H,X,Y)=T(H,M_\lambda(X,Y))
-M_\lambda(T(H,X),Y)-M_\lambda(X,T(H,Y)).\tag{1.2}
$$

唯一新增的候选相容条件为

$$
\boxed{R_\lambda(H,X,Y)=0\quad\text{对所有 }H,X,Y\in J_{AB}.}\tag{C96}
$$

其含义是：一个内部元 $H$ 引起的变化，作用于一对元的联合比较，等于先分别改变这两个元再比较的一阶总变化。它约束二元比较关系与二元变化关系的相互作用；第三元 $H$ 检查这两种关系是否保留同一联合记录。此处没有预设复合 Jordan 恒等式、复合 Jacobi 律或复 Hilbert 张量正锥。式 (1.1) 的联合模板及完整实张量空间仍是独立的组合前件。

**定义 1.3（完整标架上的有限见证）。** 固定 $b,d\in J_B$，使 $r_B=\|B_B(b,d)\|>0$。对 $V_A$ 的完整正交单位基 $e_1,\ldots,e_n$，令

$$
\begin{aligned}
G_A(\lambda)&=r_B^{-2}\sum_{i<j}\sum_k
\|R_\lambda(e_i\otimes b,e_k\otimes d,e_j\otimes1_B)\|^2,\\
Q_A&=-\sum_i\operatorname{ad}_{e_i}^{\,2},\qquad
\operatorname{ad}_uv=B_A(u,v).
\end{aligned}\tag{1.3}
$$

这是完整基上的有限未平均平方和。另一边的 $G_B$ 交换因子定义；没有看到的维度不得从求和中省略。

## 2. 从联合残差反推局部维数

**定理 2.1（混合残差因子化、尖锐维数阈值与精确端点）。** 对定义 1.1–1.3 的系统及任意实 $\lambda$，有

$$
\boxed{R_\lambda(a\otimes b,c\otimes d,e\otimes1_B)
=([L_a,L_e]+\lambda[D_a,D_e])c\otimes B_B(b,d).}\tag{2.1}
$$

因此

$$
\boxed{G_A(\lambda)=\tfrac12\|\lambda Q_A-2I\|_{\rm HS}^2+n(n-3).}\tag{2.2}
$$

$G_A$ 不依赖完整基或所选非零参照对。非零括号给 $n\ge3$，而

$$
\boxed{G_A(\lambda)<6
\iff n=3\ \text{且}\ 0<\lambda c_A^2<2,}\tag{2.3}
$$

其中三维时任取一个取向，$B_A(u,v)=c_Au\times v$、$c_A\ne0$。阈值 $6$ 尖锐：四维对象 $B_A=c_A\times\oplus0$ 在 $\lambda c_A^2=1$ 时恰达到 $6$。

此外，C96 当且仅当两边均为三维，并且在各自取向下

$$
\boxed{\lambda>0,\qquad \lambda c_A^2=\lambda c_B^2=1.}\tag{2.4}
$$

在此精确端点，复合 Jordan 性与复合 Jacobi 性成为结论。

证明。将式 (1.1) 代入式 (1.2)。乘 $S_B(b,d)$ 的系数为局部导子残差，因定义 1.1 为零。乘 $B_B(b,d)$ 的剩余系数为

$$
S_A(a,S_A(c,e))-S_A(S_A(a,c),e)-\lambda B_A(c,B_A(a,e)).
$$

前两项为 $[L_a,L_e]c$。Jacobi 给

$$
B_A(c,B_A(a,e))=-[D_a,D_e]c,
$$

于是得到 (2.1)，其中 $a,c,e$ 的标量部分也已包括。

对向量元定义

$$
K_{u,v}w=\langle v,w\rangle u-\langle u,w\rangle v.
$$

直接计算给 $[L_u,L_v]|_{V_A}=K_{u,v}$、$[D_u,D_v]=\operatorname{ad}_{B_A(u,v)}$。因而 (2.1) 将 (1.3) 化为

$$
G_A(\lambda)=\sum_{i<j}\|K_{e_i,e_j}+\lambda\operatorname{ad}_{B_A(e_i,e_j)}\|_{\rm HS}^2.
$$

使用[比较曲率 V95，定理 3.3](AURIC_COMPARISON_DYNAMICAL_CURVATURE_FINITE_FRAME_QUANTUM_V95.md)的完整标架恒等式，展开为

$$
G_A(\lambda)=n(n-1)-2\lambda\operatorname{tr}Q_A
+\tfrac{\lambda^2}{2}\operatorname{tr}Q_A^2.
$$

两边都是 $\lambda$ 的实多项式；逐项展开亦直接成立，所以不要求 $\lambda$ 有实平方根。配方得到 (2.2)。归一因子 $r_B^2$ 由张量范数乘法精确消去。

由度量不变性，$\phi(u,v,w)=\langle B_A(u,v),w\rangle$ 是非零交替三形式，故 $n\ge3$。若 $n\ge5$，(2.2) 给 $G_A\ge n(n-3)\ge10$。若 $n=4$，取向后写 $\phi=*v^\flat$，其中 $v\ne0$。由于 $\iota_v\phi=0$，$v$ 位于括号中心；在 $v^\perp$ 上，$\phi$ 为非零三维体积形式。因此四维括号正是 $c_A\times\oplus0$，有

$$
Q_A=(2c_A^2I_3)\oplus0,\qquad
G_A(\lambda)=6(\lambda c_A^2-1)^2+6.
$$

三维时，交替三形式唯一到实倍数，所以 $Q_A=2c_A^2I_3$，得到

$$
G_A(\lambda)=6(\lambda c_A^2-1)^2.
$$

这证明 (2.3) 及尖锐性。更一般地，若中心维数为 $z_0$，则 $Q_A$ 在中心为零，故任意实 $\lambda$ 均满足 $G_A\ge n(n-3)+2z_0$。

若 C96 成立，取 $B_B(b,d)\ne0$，(2.1) 强迫

$$
[L_a,L_e]+\lambda[D_a,D_e]=0
$$

对全部局部元成立。交换因子得到另一边的同式。对任意正交单位 $u,v$，令算符作用于 $v$ 并与 $u$ 配对，得到

$$
1-\lambda\|B_A(u,v)\|^2=0.
$$

所以 $\lambda>0$。两边的 $G$ 均为零，(2.3) 给出三维和 (2.4)，没有预先使用三维假设。

反过来，局部关系 $[L_a,L_e]+\lambda[D_a,D_e]=0$ 使

$$
m_s(a,c)=S_s(a,c)-i\sqrt\lambda B_s(a,c)
$$

结合：这是 V95 定理 2.1 的缩放应用。张量相乘后恰有

$$
m_A\otimes m_B=M_\lambda-i\sqrt\lambda T.\tag{2.5}
$$

结合代数的对称部分满足 Jordan 恒等式，交换子满足 Jacobi 和导子律，于是 C96 成立。该复结合合并是 Jordan–Lie 复合性的标准步骤，见 Grgin–Petersen，*Algebraic Implications of Composability of Physical Systems*，Commun. Math. Phys. 50，177–188，以及 [Kapustin，Theorem 3.1](https://arxiv.org/html/1303.6917v4)，其期刊版本 *Is quantum mechanics exact?*，DOI [10.1063/1.4811217](https://doi.org/10.1063/1.4811217)。这里承重的有限接口是 (2.1)–(2.3) 及其尖锐阈值；不把复合性产生复结构和共同参数这一成熟机制当作新发现。∎

## 3. 三个联合元暴露尺度失配

**定义 3.1（受限联合残差）。** 使用单位输入，令

$$
\begin{aligned}
\Delta_A(\lambda)&=\sup_{\|a\|=\|c\|=\|e\|=1}
\|([L_a,L_e]+\lambda[D_a,D_e])c\|,\\
\beta_B&=\sup_{\|b\|=\|d\|=1}\|B_B(b,d)\|,\\
\mathcal L_A(\lambda)&=\sup_{\|a\|=\|b\|=\|c\|=\|d\|=\|e\|=1}
\|R_\lambda(a\otimes b,c\otimes d,e\otimes1_B)\|.
\end{aligned}
$$

定义 $\mathcal L_B$ 时交换因子，并令 $\mathcal L=\max\{\mathcal L_A,\mathcal L_B\}$。这里始终只有简单张量输入，且一个比较元局限在单边；不把 $\mathcal L$ 等同于全部联合输入的残差上确界。

**定理 3.2（两条有限见证达到受限范数与尖锐最优标定）。** 任意维数下有精确因子化

$$
\boxed{\mathcal L_A(\lambda)=\beta_B\Delta_A(\lambda).}\tag{3.1}
$$

当双方三维时，记 $a=|c_A|>0,b=|c_B|>0$，则

$$
\boxed{\mathcal L(\lambda)
=\max\{b|1-\lambda a^2|,\ a|1-\lambda b^2|\},}\tag{3.2}
$$

并有唯一最优参数及精确剩余障碍

$$
\boxed{\inf_{\lambda\in\mathbb R}\mathcal L(\lambda)=|a-b|,
\qquad \lambda_*=(ab)^{-1}.}\tag{3.3}
$$

设

$$
A_i=e_i\otimes1,\quad B_j=1\otimes e_j,\quad C_{ij}=e_i\otimes e_j.
$$

以下两个单位范数三元输入已分别达到式 (3.2) 中的两项：

$$
\begin{aligned}
R_\lambda(C_{11},A_2,C_{22})&=c_B(1-\lambda c_A^2)C_{13},\\
R_\lambda(C_{11},B_2,C_{22})&=c_A(1-\lambda c_B^2)C_{31}.
\end{aligned}\tag{3.4}
$$

证明。式 (2.1) 的两组变量彼此独立，张量范数相乘，有限维单位球紧，故两个最大值可同时取到，得到 (3.1)。三维时

$$
[L_u,L_v]+\lambda[D_u,D_v]=(1-\lambda c_A^2)K_{u,v}
$$

在向量部分成立，标量部分为零。$\|K_{u,v}\|_{\rm op}\le\|u\|\|v\|$，正交单位 $u,v$ 达到 $1$，故 $\Delta_A=|1-\lambda c_A^2|$、$\beta_B=|c_B|$；另一边同理。

第一条有限见证的非零项为

$$
M_\lambda(A_2,C_{22})=B_2,\quad
T(C_{11},B_2)=c_BC_{13},\quad
T(C_{11},A_2)=c_AC_{31},
$$

以及 $M_\lambda(c_AC_{31},C_{22})=\lambda c_A^2c_BC_{13}$；$T(C_{11},C_{22})=0$。这给出 (3.4) 第一式。交换两边得到第二式。

令 $r_A=b(1-\lambda a^2)$、$r_B=a(1-\lambda b^2)$，恒等式

$$
a r_B-b r_A=a^2-b^2
$$

给出 $|a^2-b^2|\le(a+b)\mathcal L(\lambda)$，故下界为 $|a-b|$。在 $\lambda=(ab)^{-1}$ 时，$r_A=b-a$、$r_B=a-b$，达到下界。若 $a\ne b$，等号条件连同恒等式固定这两个残差，进而固定 $\lambda$；若 $a=b$，目标为 $a|1-\lambda a^2|$，也有唯一零点。∎

**定理 3.3（静态闭合与动态闭合的有限分离）。** 仍在三维参数类中，设 $\mu=\lambda c_Ac_B$，并定义左嵌套 Jacobi 残差

$$
\operatorname{Jac}_T(P,Q,R)=T(T(P,Q),R)+T(T(Q,R),P)+T(T(R,P),Q).
$$

则

$$
\operatorname{Jac}_T(C_{11},C_{21},C_{22})=(c_B^2-c_A^2)C_{12}.\tag{3.5}
$$

取 $x=A_1+B_1+C_{22}$、$y=C_{11}$、$x^2=M_\lambda(x,x)$，Jordan 缺陷为

$$
\boxed{M_\lambda(x^2,M_\lambda(x,y))-M_\lambda(x,M_\lambda(x^2,y))
=2(\mu^2-1)C_{22}.}\tag{3.6}
$$

$M_\lambda$ 为 Jordan 乘法恰当且仅当 $\mu^2=1$。在其两个实参数支上，受限动态残差分别为

$$
\mathcal L((ab)^{-1})=|a-b|,\qquad
\mathcal L(-(ab)^{-1})=a+b.\tag{3.7}
$$

所以静态 Jordan 比较允许的联合结构，仍可因共同变化不相容而被排除；即使 $a=b$，负参数支也不能满足 C96。

证明。$T(C_{11},C_{21})=c_AA_3$，再作用到 $C_{22}$ 给 $-c_A^2C_{12}$；$T(C_{21},C_{22})=c_BB_3$，再作用到 $C_{11}$ 给 $c_B^2C_{12}$；第三项为零，得到 (3.5)。

比较乘法的基关系为

$$
\begin{aligned}
M_\lambda(A_i,A_k)&=\delta_{ik}I,&
M_\lambda(B_j,B_l)&=\delta_{jl}I,&
M_\lambda(A_i,B_j)&=C_{ij},\\
M_\lambda(A_i,C_{kl})&=\delta_{ik}B_l,&
M_\lambda(B_j,C_{kl})&=\delta_{jl}A_k,\\
M_\lambda(C_{ij},C_{kl})&=\delta_{ik}\delta_{jl}I
-\mu\sum_{m,n}\epsilon_{ikm}\epsilon_{jln}C_{mn}.
\end{aligned}
$$

故 $x^2=3I+2C_{11}$，$M_\lambda(x,y)=A_1+B_1-\mu C_{33}$，而

$$
\begin{aligned}
M_\lambda(x^2,M_\lambda(x,y))&=5A_1+5B_1-3\mu C_{33}+2\mu^2C_{22},\\
M_\lambda(x,M_\lambda(x^2,y))&=5A_1+5B_1-3\mu C_{33}+2C_{22}.
\end{aligned}
$$

这证明必要性。若 $\mu=\pm1$，分别取两个局部单位叉积，必要时反转其中一个符号；其复结合张量积的对称部分恰为当前 $M_\lambda$，故满足 Jordan 恒等式。这里临时构造的单位括号不替代原有 $c_A,c_B$ 动力，因而不暗中证明原来的 $T$ 相容。最后直接代入 (3.2) 得到 (3.7)。若把 $x$ 归一为 $x/\sqrt3$，式 (3.6) 的系数相应成为 $2(\mu^2-1)/(3\sqrt3)$。∎

## 4. 删除前件、隐藏方向与尺度自由

**命题 4.1（非零活动与完整标架各有不可替代的用途）。** 删除定义 1.1 的非零括号要求后，有以下不同结果。

1. 双方均取三维关系球而 $B_A=B_B=0$ 时，C96 恒成立，但联合比较不满足 Jordan 恒等式。
2. 若一边是 $\dim V_A\ge2$ 的关系球且 $B_A=0$，另一边 $B_B\ne0$，则 C96 不成立。
3. 若把第一边改为真正的有限经典代数 $\mathbb R^m$，比较为逐点乘法、括号为零，另一边取任意定义 1.1 的系统，则复合导子律成立。
4. 四维 $c\times\oplus0$ 与三维 $c\times$ 的组合在 $\lambda c^2=1$ 时，对全部仅使用前三轴的输入通过 C96；完整四维见证却有 $G_A=6$。

证明。第一项因 $T=0$ 而残差为零，但定理 3.3 的比较乘法公式在 $\mu=0$ 时仍成立，Jordan 缺陷是 $-2C_{22}$。第二项由 (2.1) 得到 $K_{u,v}v\otimes B_B(b,d)=u\otimes B_B(b,d)\ne0$。第三项的联合空间同构于第二系统的 $m$ 个直和，比较与变化均逐点作用，故局部导子律逐块成立；它与第二项的非结合关系球不同，不排除经典记录与量子系统并置。第四项中前三轴构成封闭三维子空间，定理 2.1 给出其精确相容；完整残差取四维公式。∎

**命题 4.2（共同尺度与取向仍有自由）。** 精确 C96 不固定变化的绝对大小，也不固定两个局部取向的相对符号。对任意 $t\ne0$，变换

$$
B_s\longmapsto tB_s,\qquad \lambda\longmapsto\lambda/t^2
$$

保持 $M_\lambda$，并使 $T\mapsto tT$，因而保持 C96。另一方面，$c_A=-c_B\ne0$ 与 $\lambda=c_A^{-2}$ 也满足 C96。

证明。式 (1.1) 中的对称修正对括号二次，有向项对括号一次；残差因此整体乘 $t$。式 (2.4) 只包含 $c_A^2,c_B^2$，所以不排除反号。式 (2.5) 中反号的一边使用 opposite 乘法，这仍为复结合代数。尚未指定共同矩阵正锥和复取向时，不能把此抽象同构称为在既定联合锥上实施局部转置。∎

**命题 4.3（既定量子参考为何能区分局部转置）。** 已指定通常复矩阵联合锥时，单体转置虽保正，却不能对全部内部参考保正；一个二能级参考足以检出失败。

证明。在 $\mathbb C^2\otimes\mathbb C^2$ 上，令 $|\Phi\rangle=(|00\rangle+|11\rangle)/\sqrt2$。$|\Phi\rangle\langle\Phi|$ 的部分转置为交换算子的一半，在反对称向量 $(|01\rangle-|10\rangle)/\sqrt2$ 上的本征值为 $-1/2$。这区分的是在已经固定的复合正锥上的物理过程；它不取消命题 4.2 中选择不同代数识别的数学自由。该标准完全正性反例作为共同取向的接口使用。∎

## 5. 整体网络中的关系同步

**定义 5.1（共享局部关系的连接网络）。** 取有限无向连通图 $G=(W,E)$，至少两个顶点。每个顶点各有一个固定的定义 1.1 局部系统；同一顶点在各条关联边上使用同一个括号，不得按边另行重标。每条边 $vw$ 使用定义 1.2 的模板和参数 $\lambda_{vw}$，并对完整联合空间要求 C96。图连接表示共享系统的联合关系，不等同于预设物理空间距离。

**定理 5.2（精确同步与有限缺陷沿路径的尖锐传播）。** 定义 5.1 的网络中，每个局部向量空间均为三维，存在共同 $a>0$ 使

$$
|c_v|=a\quad(v\in W),\qquad
\lambda_{vw}=a^{-2}\quad(vw\in E).
$$

其复乘法可用同一个 $\sqrt\lambda=1/a$ 合并，并沿所有有限张量积一致延拓。

对另已处在三维的同图参数族，不要求精确 C96，令

$$
\varepsilon_{vw}=\inf_\lambda\mathcal L_{vw}(\lambda).
$$

则

$$
\varepsilon_{vw}=\big||c_v|-|c_w|\big|,\qquad
\big||c_v|-|c_w|\big|\le\sum_{e\in p}\varepsilon_e
$$

对任意连接 $v,w$ 的路径 $p$ 成立。特别地，若每条边 $\varepsilon_e\le\varepsilon$，图直径为 $D$，则

$$
\boxed{\inf_{a_0\in\mathbb R}\max_v\big||c_v|-a_0\big|
=\tfrac12(\max_v|c_v|-\min_v|c_v|)\le D\varepsilon/2.}\tag{5.1}
$$

末项常数尖锐。

证明。定理 2.1 在每条边给三维与端点大小相等；沿连通路径传递得到共同 $a$ 及全部边参数。每个局部复结合代数使用同一个系数，普通代数张量积的结合性保证多体括号选择一致；相反的局部取向通过各自的 opposite 识别处理，不必额外设 C96 的多体版本来选绝对单位。

非精确族的边等式是定理 3.2。路径不等式为这些精确差的三角不等式。有限实数集对一个常数的最佳最大偏差等于其极差的一半，取极值中点达到；这一步是标准实数与图路径估计。对长度 $D$ 的路径，取 $|c_k|=a+k\varepsilon$、$a>0$，每条边使用各自的最优 $\lambda$，全部边缺陷恰为 $\varepsilon$，总极差为 $D\varepsilon$，所以常数达到。这里的结论依赖共享同一个局部括号；允许每条边单独改时间单位会消除被比较的同一量。∎

## 6. 从有限关系见证到完整量子操作理论

**定义 6.1（内部生成闭包与完整解释）。** 从定义 5.1 的一个精确网络出发，允许任意有限张量积，并使用定理 2.1 构造的复结合乘法。另明确要求：

- 有限直和可用；
- 任意生成代数中的非零自伴随投影 $p$，其角代数 $p\mathcal Ap$ 可作为单位为 $p$ 的系统；
- 状态为全部正归一线性泛函，效果为全部 $0\le e\le1$，概率为泛函评价；
- 允许的线性过程恰为在每个可用有限参考上联合保正的过程，归一过程保迹；有结果的过程保留有限经典标签；
- 连续可逆时间族取连续一参数 $*$ 自同构族。

角闭包允许在联合系统中选择相干子空间，而非只能丢弃经典标签。状态、效果、参考、结果记录和时钟都属于同一对象族 $\Omega$；“都在内部”不省略这些供应条件。选定过程若存在局部终态，另记为 $\Omega_\rho$，不将它与全部内部关系结构等同。

**定理 6.2（有限见证端点的全维生成及既有量子公理接口）。** 在定义 6.1 的范围内，精确 C96 网络生成的有限系统恰为有限直和复矩阵代数。其完整状态、效果、过程及连续可逆时间分别具有通常有限量子理论的密度矩阵、Born 概率、完全正仪器及 Hamilton 形式。角闭包若省略，仅从任意多个二能级系统及有限直和不能得到每个单纯维数。

证明。先将定理 2.1 的有限残差端点接到代数生成。选局部取向，使 $B_s=c_s\times$，记 $s_s=\sqrt\lambda c_s\in\{1,-1\}$。用标准 Pauli 矩阵 $\sigma=(\sigma_1,\sigma_2,\sigma_3)$ 定义

$$
\Phi_s(\alpha,u)=\alpha I-s_su\cdot\sigma.
$$

Pauli 乘法公式给

$$
\Phi_s(S_s(x,y)-i\sqrt\lambda B_s(x,y))=\Phi_s(x)\Phi_s(y).
$$

复线性延拓后，$\Phi_s$ 是到 $M_2(\mathbb C)$ 的含幺 $*$ 同构。其自伴随平方锥为矩阵正锥：局部特征值为 $\alpha\pm\|u\|$，故正性等价于 $\alpha\ge\|u\|$。由 (2.5)，$N$ 个局部系统给 $M_{2^N}(\mathbb C)$。对任何 $d\ge1$，取 $2^N\ge d$ 并选秩 $d$ 的投影 $p$，角代数为 $M_d(\mathbb C)$；有限直和给所有有限复 $C^*$ 代数。张量积、有限直和及角运算也都保持此类，所以没有生成别的有限代数。若只用前两种操作，简单块的大小仍为 $2^N$，从而缺少 $M_3(\mathbb C)$。这些矩阵与角结构的标准事实在此承担由局部有限证书到全维供应的桥梁。

余下的状态—过程表示直接使用[比较曲率 V95，定义 5.1、定理 5.2](AURIC_COMPARISON_DYNAMICAL_CURVATURE_FINITE_FRAME_QUANTUM_V95.md)的完整有限接口。具体对应为

$$
\mathcal A=\bigoplus_sM_{d_s}(\mathbb C),\qquad
\rho_s\ge0,\qquad\sum_s\operatorname{Tr}\rho_s=1,
$$

以及

$$
p(j\mid\rho)=\sum_s\operatorname{Tr}(\rho_se_{j,s}),\qquad
 e_{j,s}\ge0,\quad\sum_je_{j,s}=I_{d_s}.
$$

纯态与秩一投影效果的概率为 $|\langle\phi,\psi\rangle|^2$。线性概率与完整菜单是定义 6.1 的解释前件；复平方形式由矩阵重构提供。复合使用同一 $m_A\otimes m_B$，所以得到通常复 Hilbert 张量积及纠缠正态，并且局部效果的张量线性张成联合自伴随空间。

所有有限矩阵参考已由角闭包供应，故“对全部参考保正”恰为完全正。标准 Choi–Kraus 表示于是给跨块过程

$$
\Phi(\rho)_t=\sum_{s,\nu}K_{ts\nu}\rho_sK_{ts\nu}^*,\qquad
\sum_{t,\nu}K_{ts\nu}^*K_{ts\nu}=I_{d_s}.
$$

结果标签 $j$ 给完全正分支 $\Phi_j$，总和保迹，记录为 $\sum_j\Phi_j(\rho)\otimes|j\rangle\langle j|$。指定投影测量可使用 $\rho\mapsto p_j\rho p_j$，但效果本身不唯一决定实际更新；相同效果可由不同仪器实现。连续可逆族逐矩阵块为酉共轭。对由本候选固定的括号，有

$$
B(H,X)=\frac{i}{2\sqrt\lambda}[H,X],\qquad
\dot\rho=-\frac{i}{2\sqrt\lambda}[H,\rho].
$$

纯态代表可取 $i(2\sqrt\lambda)\dot\psi=H\psi$。只有再把内部时间、能量与物理单位对应，才能把 $2\sqrt\lambda$ 记成物理 $\hbar$；命题 4.2 证明其数值仍可整体重标。连续的一参数自同构不会置换有限多个中心块，故存在超选择中心不妨碍这一结论。

上述有限 $C^*$、完全正、仪器和时间表示是标准工具及 V95 的复用；新联合限制是完整有限见证、其尺度失配的精确残差，以及沿共同局部系统的同步。在[二元参考与充分约化 V94，定理 4.2、9.1](AURIC_BINARY_REFERENCE_ENDOGENOUS_SUFFICIENT_REDUCTION_AND_QUANTUM_VISIBLE_ALGEBRA_V94.md#thm-c94-main)声明的全矩阵代数 $B(H)$ 合同下，若回缩保持全部可见读数、合并同资料态、固定忠实参照，并对一个二元参考上的全部联合正输入保正，则直接复用该卷的唯一完全正块重置结论。该特殊回缩的二元参考结论不把任意二正过程升级成完全正过程。

在此重构出的全矩阵块上选定同一个 CPTP 正向步长 $\Phi$，可进一步连接[手性、守恒关系与内生终态 V95，定义 3.1、定理 5.1](AURIC_CHIRAL_ORIENTATION_CONSERVED_RELATIONS_AND_ENDOGENOUS_QUANTUM_TERMINAL_STATES_V95.md#thm-c95-equivalence)。该卷的守恒读口为 $\mathcal S=\operatorname{Fix}\Phi^*\cap\operatorname{Herm}$；对其中每对同守恒资料、支撑正交的态要求某个有限正向延伸使输出不再正交，恰好等价于全部实际迭代收敛，并给出每个资料纤维内由 $\Phi$ 唯一决定的 $\Omega_\rho=\lim_n\Phi^n(\rho)$。这里只复用其已给定量子过程后的判据：C96 提供过程的复代数载体与共同变化尺度，终态判据另约束所选过程的衰减关系，不成为本候选的第二条公理。两者不互相替代，因为 C96 仍允许非平凡酉过程，而其任意两输入的迹距离不随迭代改变；由该卷命题 2.1，非固定初态没有吸引极限。取向的选择、变化尺度、衰减和终点因而是彼此不同的关系条件。∎

## 7. 内生约束的精确范围

**命题 7.1（关系内生与无前提唯一性的区分）。** 把全部元、比较、变化及联合嵌入放入同一个 $\Omega$，可使 C96 成为内部定义之间的约束，并使联合 Jordan 性、联合 Jacobi 性、局部三维及相对尺度从该约束推出。但仅有“所有对象均属于 $\Omega$”不能推出 C96、联合模板、完整菜单或绝对尺度。

证明。定理 2.1 给出前一组条件后果。对后一组，命题 4.1 第一项的两边零括号对象同样可全部收入一个 $\Omega$，却有不同的静态联合结构。取非零三维 $c_A=1,c_B=2$ 并使用 (1.1)，全部运算也在同一个实张量空间内闭合，而定理 3.2 给出不能消除的受限残差 $1$，故内部闭合不推出 C96。即使精确 C96 成立，命题 4.2 仍留下连续重标族。对同一生成代数取状态或效果的真子菜单，不改变任何代数恒等式，却失去定义 6.1 的完整供应。因此内部对象的存在、关系相容和全部操作可取得是不同的数学条件。∎

**定义 7.2（候选的有限理论边界）。** 本候选的结论限定在有限正关系球、非零局部度量 Lie 变化、式 (1.1) 的联合模板及明确的操作闭包内。一般非球形局部结构的选择、无限维极限、连续时空、具体 Hamiltonian、物理单位的经验标定及所有维数的 SIC 存在性，不是上述定理的结论。若要从更弱的内部比较关系推出这些前件，需要另给对象对应与证明，不能以同一术语替代该桥梁。

## 追加锚（本行以下为增补区）

## 8. 一般正比较场与不含外部标尺的候选

**定义 8.1（未预设 Lie 结构的内部比较场）。** 设 $J$ 是非零有限维实向量空间，$1\in J$，$S:J\times J\to J$ 是交换双线性运算，$g$ 是正定内积，满足

$$
S(1,a)=a,\qquad g(S(a,b),c)=g(b,S(a,c)).
$$

给实线性映射 $D:J\to\operatorname{Der}(J,S)$，并要求 $D\ne0$。记 $L_ab=S(a,b)$、$B(a,b)=D_ab$。此处不要求 $S$ 为 Jordan 乘法，不要求 $B$ 交替、自守、满足 Jacobi 或消去第一槽的单位，也不要求 $J$ 是关系球。维数 $n=\dim J$ 包括单位方向。

每个 $S$ 的导子都对 $g$ 斜伴随，直接复用[比较曲率 V95，定理 2.1 第一项](AURIC_COMPARISON_DYNAMICAL_CURVATURE_FINITE_FRAME_QUANTUM_V95.md)的有限正 Frobenius 论证；这个事实只依赖本定义中的比较前件。单位律给 $D_a1=0$，此时尚不能据此断言 $D_1a=0$。

**定义 8.2（未校准联合运算）。** 对两个定义 8.1 的场 $A,B$，在实张量空间上使用

$$
M_\lambda=S_A\otimes S_B-\lambda B_A\otimes B_B,
\qquad
T=B_A\otimes S_B+S_A\otimes B_B,
$$

其中 $\lambda$ 先仅为实代数变量。定义联合导子残差

$$
R_\lambda(H,X,Y)=T(H,M_\lambda(X,Y))
-M_\lambda(T(H,X),Y)-M_\lambda(X,T(H,Y)).\tag{8.1}
$$

此时不预设 $M_\lambda$ 对称或 $T$ 交替；它们是由局部定义给出的待检验运算。实张量空间及这两个联合模板仍为明确前件。

**定义 8.3（完整有限探针族）。** 对每个局部场 $J$ 取完整正交单位基 $e_1,\ldots,e_n$，并令

$$
\mathcal P_J=\{e_i:1\le i\le n\}
\cup\{(e_i+e_j)/\sqrt2:1\le i<j\le n\}.
$$

在另一场取一个固定的有序参照对 $(b,d)$，使 $v=D_bd\ne0$。取以下带标签的三元探针族：

$$
\begin{aligned}
\Pi_J^{\rm self}
&=\{(p\otimes d,p\otimes b,p\otimes1):p\in\mathcal P_J\},\\
\Pi_J^{\rm mix}
&=\{(e_i\otimes b,e_k\otimes d,e_j\otimes1):i<j,\ 1\le k\le n\}.
\end{aligned}\tag{8.2}
$$

自身探针交换了参照的两个槽，因此只需 $D_bd\ne0$，无需预先要求 $D_db\ne0$。对第二场按交换因子的顺序定义同样的族。两边残差所在空间的有限正交直和记为 $\mathcal H_\Pi$，其内积由各局部乘积内积给出。探针保留标签，数量按出现次数计算。

**定义 8.4（候选 C97：有限缺陷可由同一内部比例抵消）。** 在 $\mathcal H_\Pi$ 中定义

$$
P=(R_0(\pi))_{\pi\in\Pi},\qquad
Q=(R_0(\pi)-R_1(\pi))_{\pi\in\Pi}.
$$

残差关于 $\lambda$ 仿射，所以全部有限报告为 $P-\lambda Q$。令

$$
\lambda_*=
\begin{cases}
\langle P,Q\rangle/\|Q\|^2,&Q\ne0,\\
0,&Q=0,
\end{cases}
\qquad
\Gamma=\|P-\lambda_*Q\|^2.
$$

唯一候选条件为

$$
\boxed{\Gamma=0.}\tag{C97}
$$

$P,Q$ 都由已经定义的内部比较、变化及参照对产生；$\lambda_*$ 由它们定义，不是另行输入的数值。该条件要求同一比例消去全部有限联合缺陷，不允许逐探针选择比例。此处的投影是有限正内积空间的通常正交投影；$\lambda_*$ 的正号尚不是定义条件。

## 9. 有限报告推出局部 Lie 结构与全部联合相容

**定理 9.1（一般正场的有限压缩与内生量子端点）。** 对定义 8.1–8.4 的两个场，下列条件等价：

1. C97 成立；
2. 存在实数 $\lambda$，使全部联合输入满足 $R_\lambda(H,X,Y)=0$。

成立时，$\lambda=\lambda_*>0$ 唯一，且两边均有

$$
D_aa=0,\qquad B(a,b)=-B(b,a),\qquad D_1=0,
$$

以及 Jacobi 律和

$$
\boxed{[L_a,L_b]+\lambda_*[D_a,D_b]=0.}\tag{9.1}
$$

各局部复化上

$$
m(a,b)=S(a,b)-i\sqrt{\lambda_*}B(a,b)
$$

是具有忠实正 $*$ 表示的复结合乘法；原实场恰为其自伴部分。局部与联合的 Jordan 性、变化的交替性与 Jacobi 性因而都是结论。每方所用探针数为

$$
\boxed{|\Pi_J|=\frac{n(n+1)}2+\frac{n^2(n-1)}2=\frac{n^3+n}2.}\tag{9.2}
$$

该数量是一个充分证书，不主张最小性。

证明。首先不使用交替性，直接展开得到

$$
\boxed{
R_\lambda(a\otimes b,c\otimes d,e\otimes1)
=[L_a,L_e]c\otimes D_bd
+\lambda D_cD_ae\otimes D_db.
}\tag{9.3}
$$

乘 $S_B(b,d)$ 的项由局部导子律抵消，其他项正是上式。特别地，交换参照槽后

$$
\boxed{R_\lambda(p\otimes d,p\otimes b,p\otimes1)
=\lambda D_p^2p\otimes v.}\tag{9.4}
$$

$P\ne0$。否则混合探针的零参数报告给全部 $[L_{e_i},L_{e_j}]e_k=0$，故所有左乘算子对易。交换性继而给

$$
S(S(a,b),c)=L_cL_ab=L_aL_cb=S(a,S(b,c)),
$$

所以 $S$ 结合。全部 $L_a$ 自伴且可同时对角化，$L_a1=a$ 又使表示忠实，因而此有限正交换结合代数为若干个 $\mathbb R$ 的直积。其导子为零：对谱幂等元 $p$，$\delta p=2p\delta p$ 逐坐标强迫 $\delta p=0$。这与定义 8.1 的 $D\ne0$ 矛盾。

若 $\Gamma=0$，则 $P=\lambda_*Q$。$P\ne0$ 自动排除 $Q=0$ 和 $\lambda_*=0$，且全部有限探针在同一个非零参数上消失。由 (9.4) 及斜伴随性，

$$
0=-g(p,D_p^2p)=\|D_pp\|^2.
$$

对基向量及归一两两和均如此，极化遂给

$$
D_{e_i}e_j+D_{e_j}e_i=0,
$$

并由双线性扩展为全部 $a,b$ 的交替性。再由 $D_a1=0$ 得 $D_1a=0$。两边均先完成这一步，才在 (9.3) 中替换 $D_db=-D_bd$。

因此混合报告成为

$$
R_\lambda(a\otimes b,c\otimes d,e\otimes1)
=\bigl([L_a,L_e]+\lambda D_{B(a,e)}\bigr)c\otimes v.\tag{9.5}
$$

$[L_a,L_e]$ 和 $D_{B(a,e)}$ 对 $a,e$ 都交替；完整的 $i<j,k$ 族足以推出

$$
[L_a,L_e]= -\lambda_*D_{B(a,e)}
$$

对全部元成立。交换乘法的恒等式

$$
[L_a,L_e]c+[L_e,L_c]a+[L_c,L_a]e=0
$$

逐项抵消成立，因而给

$$
B(B(a,e),c)+B(B(e,c),a)+B(B(c,a),e)=0.
$$

这推出 Jacobi，而非预先使用它。于是 $[D_a,D_e]=D_{B(a,e)}$，得到 (9.1)。

为确定符号，定义正定迹比较

$$
q(a,b)=\operatorname{Tr}(L_aL_b).
$$

正定性来自 $L_a$ 自伴及 $L_a1=a$。任意比较导子 $\delta$ 满足

$$
q(\delta a,b)+q(a,\delta b)=\operatorname{Tr}[\delta,L_aL_b]=0.
$$

选 $v=D_ab\ne0$，记 $K=[L_a,L_b]$、$C=[D_a,D_b]$。由交替性和自守，$Ca=-D_a^2b$，故

$$
\operatorname{Tr}(CK)
=\operatorname{Tr}([C,L_a]L_b)
=q(Ca,b)=q(D_ab,D_ab)>0.
$$

$K=-\lambda_*C$ 且 $K$ 斜伴随，因此

$$
\boxed{\|K\|_{\rm HS}^2=\lambda_*q(D_ab,D_ab).}\tag{9.6}
$$

左侧非负、右侧第二因子正，结合 $\lambda_*\ne0$，给出 $\lambda_*>0$。每个非零变化对同时给出同一内部标尺

$$
\boxed{\lambda_*
=\frac{\|[L_a,L_b]\|_{\rm HS}^2}{q(D_ab,D_ab)}.}\tag{9.7}
$$

复结合重构现在直接复用比较曲率 V95 定理 2.1 的缩放形式。其左正则表示为

$$
\pi(a)=L_a-i\sqrt{\lambda_*}D_a,\qquad \pi(z)1=z.
$$

实元的左乘算子自伴，结合性使 $\pi$ 成为忠实含幺 $*$ 表示，有限维像因此为复 $C^*$ 代数。两边结合张量积的乘法恰为 $M_{\lambda_*}-i\sqrt{\lambda_*}T$，故全部联合导子残差消失。有限 $C^*$ 与动力对应的成熟重构在此仅作为有限证书端点的中间工具，出处同定理 2.1；不另认领该标准表示。

反过来，若某个参数上全部联合残差消失，则 $P=\lambda Q$。$P\ne0$ 迫使 $Q\ne0$，正交投影给 $\lambda_*=\lambda$、$\Gamma=0$，也证明该参数唯一。有限计数由两族的指标直接相加，得到 (9.2)。例如两个实自伴维数均为 $4$ 的场使用 $68$ 个带标签报告；逐一检查整个 $16$ 维联合空间上的全部基三元组则有 $16^3=4096$ 项。这里仅比较这两种明确证书，不声称排除了其他压缩方式。∎

## 10. 自守缺陷的有限正证书与尖锐误差律

**定理 10.1（尚未交替时的平方根界）。** 在定义 8.1–8.2 下，不要求 C97。固定另一边的 $v=D_bd\ne0$，令 $r=\|v\|$、$\lambda\ne0$，则每个局部元 $a$ 满足

$$
\boxed{\|D_aa\|^2
\le\frac{\|a\|\,
\|R_\lambda(a\otimes d,a\otimes b,a\otimes1)\|}{|\lambda|r}.}\tag{10.1}
$$

若

$$
\delta=\sup_{\|a\|=1}\|D_aa\|,\qquad
\varepsilon=\sup_{\|a\|=1}
\|R_\lambda(a\otimes d,a\otimes b,a\otimes1)\|,
$$

则 $\delta\le\sqrt{\varepsilon/(|\lambda|r)}$，平方根指数及常数 $1$ 均尖锐。该界只控制所定义自身探针族，不把它升级为任意近似量子代数的稳定性定理。

证明。式 (9.4) 与斜伴随性给

$$
\|D_aa\|^2=-g(a,D_a^2a)
\le\|a\|\|D_a^2a\|
=\frac{\|a\|\|R_{\rm self}\|}{|\lambda|r}.
$$

为达到等号，取 $J=\mathbb R1\oplus\mathbb R^2$ 的通常球比较，令 $J_0e_1=e_2$、$J_0e_2=-e_1$，定义

$$
D^t_{(\alpha,u)}(\beta,w)=(0,t u_1J_0w).
$$

$J_0$ 为旋转导子，所以该指派满足定义 8.1；$t\ne0$ 时非零。对单位向量 $a=e_1$ 有

$$
D_aa=te_2,\qquad D_a^2a=-t^2e_1.
$$

对任意单位 $a$ 又有 $\|D_aa\|\le|t|$、$\|D_a^2a\|\le t^2$，上式同时达到。因此

$$
\delta=|t|,\qquad \varepsilon=|\lambda|rt^2.
$$

这精确达到常数并在 $t\to0$ 时固定指数。若误差被定义为残差的平方或平方和，则相应是该平方误差的四分之一次幂；不能混同两种误差。此例没有让全部联合残差趋零的结论。∎

## 11. 未假设 Jacobi 时的内部标定障碍

**定理 11.1（有限迹缺额与正的最佳比例）。** 在定义 8.1 的单场中，另已得到或明确要求 $B(a,b)=-B(b,a)$，但不要求 Jacobi。记

$$
K_{ab}=[L_a,L_b],\qquad E_{ab}(\lambda)=K_{ab}+\lambda D_{B(a,b)},
\qquad q(a,b)=\operatorname{Tr}(L_aL_b).
$$

则

$$
\operatorname{Tr}(K_{ab}D_{B(a,b)})=q(B(a,b),B(a,b)).\tag{11.1}
$$

对完整正交基，定义

$$
\mathsf a=\sum_{i<j}\|K_{ij}\|_{\rm HS}^2,\quad
\mathsf h=\sum_{i<j}q(B(e_i,e_j),B(e_i,e_j)),\quad
\mathsf c=\sum_{i<j}\|D_{B(e_i,e_j)}\|_{\rm HS}^2.
$$

活动条件给 $\mathsf a,\mathsf h,\mathsf c>0$，并有精确恒等式

$$
\boxed{\sum_{i<j}\|E_{ij}(\lambda)\|_{\rm HS}^2
=\mathsf c\left(\lambda-\frac{\mathsf h}{\mathsf c}\right)^2
+\frac{\mathsf a\mathsf c-\mathsf h^2}{\mathsf c}.}\tag{11.2}
$$

因此最佳局部比例唯一且为正，剩余障碍为非负量 $\mathsf a\mathsf c-\mathsf h^2$。若另一场的括号也已交替，则在固定非零参照 $v$ 下，式 (9.5) 的完整混合残差平方和恰为式 (11.2) 乘 $\|v\|^2$。这里的 $E$ 使用 $D_{B(a,b)}$；在尚未得到 Jacobi 时，不得换成 $[D_a,D_b]$。

证明。令 $z=B(a,b)$，$D_z$ 仍为比较导子。迹循环性、交替性与 $q$ 的导子不变性给

$$
\begin{aligned}
\operatorname{Tr}(K_{ab}D_z)
&=\operatorname{Tr}([D_z,L_a]L_b)\\
&=q(D_za,b)=q(-D_a^2b,b)=q(z,z).
\end{aligned}
$$

这证明 (11.1)，完全没有使用 Jacobi。$K_{ab},D_z$ 均斜伴随，故其 Hilbert–Schmidt 内积为 $-q(z,z)$。逐对展开平方并配方，得到 (11.2)。

至少一个基对有 $z\ne0$，于是 $\mathsf h>0$；(11.1) 同时迫使该对的 $K_{ab},D_z$ 非零，故其余两数为正。把所有 $K_{ij}$ 与 $D_{B(e_i,e_j)}$ 当作有限直和中的两个向量，Cauchy–Schwarz 给 $\mathsf h^2\le\mathsf a\mathsf c$。等号、配合比例 $\lambda=\mathsf h/\mathsf c$，恰使全部 $E_{ij}$ 消失；随后定理 9.1 的循环抵消步骤给出 Jacobi。张量范数乘法则给所述联合残差对应。此处正交投影和 Cauchy–Schwarz 是标准工具，有限缺额针对的是当前未预设 Lie 的关系接口。∎

## 12. 一般有限量子理论及共同标尺的范围

**定理 12.1（有限证书的类别、单位自由与操作接续）。** C97 的每个局部场都同构于某个有限复 $C^*$ 代数的自伴部分，其复代数为

$$
\mathcal A\cong\bigoplus_sM_{d_s}(\mathbb C),
$$

且至少一个 $d_s\ge2$。反过来，每个具有非交换块的有限复 $C^*$ 代数，取任意正的逐块加权迹内积及共同 $\lambda>0$，并令

$$
S(a,b)=\tfrac12(ab+ba),\qquad D_ab=\frac{i}{2\sqrt\lambda}(ab-ba),
$$

即满足本候选。允许交换直和块；活动条件仅排除作为独立输入的纯交换场。

沿连通网络共享同一个局部定义时，各边精确 C97 的内部 $\lambda_*$ 一致。但共同重标 $D\mapsto tD$、$t\ne0$，给

$$
P\mapsto tP,\quad Q\mapsto t^3Q,\quad
\lambda_*\mapsto\lambda_*/t^2,\quad\Gamma\mapsto t^2\Gamma.
$$

故零缺陷与重构类别不变，绝对时间单位仍未由该候选固定。

证明。定理 9.1 的忠实正表示和标准有限 $C^*$ 结构定理给直和形式。若全部块交换，则交换子为零，与 $D\ne0$ 矛盾；反向代入给 $S-i\sqrt\lambda D=ab$，并由结合张量积得到全部联合残差为零。正加权迹形式保持 Frobenius 与正定性。此处的有限代数分类是成熟表示工具，不作为新发现。

每个固定局部非零变化对通过 (9.7) 唯一确定其 $\lambda_*$，所以同一顶点的各条边不能给不同参数。连通性沿边传播此等式。缩放时 $T$ 一次齐次、$M_0$ 不变、有向修正二次齐次，故零参数残差一次齐次、其参数系数三次齐次，得到所列缩放式。兼容端点的参数及候选真假不依赖完整基或活动参照对；非零 $\Gamma$ 的具体数值是已声明探针规范下的读数，不主张这种不变性。

其完整有限操作解释直接复用定理 6.2：全部正归一泛函和效果给密度矩阵与 Born 规则，所有有限参考上的联合保正及结果标签给完全正仪器，连续可逆自同构给 Hamilton 演化。该接续仍要求相应状态、效果与参考的完整供应。这里直接重构一般矩阵块，不再要求先把局部系统设成球再用角闭包生成每个被给定系统；但“所有维数的系统均可取得”仍是对象族的供应条件，不由一个固定有限场的分类推出。内生终态仍使用定理 6.2 所引的所选过程收敛判据，C97 本身不保证吸引终态。∎

## 13. 缺失前件的具体后果

**命题 13.1（活动、正性与有限族完整性的不同作用）。** 以下放宽不能保留定理 9.1 的全部结论。

- 删去双方活动要求时，即使全部联合残差恒为零，也不能推出复结合结构。
- 把正 Frobenius 内积换成非退化但不定的形式时，即使保留双方非零导子，也允许参数零的完整联合相容与自守失败。
- 在自身探针中只保留基向量、删去两两和时，基向量的自守不能推出全部元的自守。

证明。第一项取定理 4.1 的零括号关系球，其非结合比较已给出显式三元反例。真正的经典结合记录仍可依该定理与量子系统并置；它不属于本定理双方均活动的起点。

第二项取 $J=\mathbb R[\epsilon]/(\epsilon^2)$，比较为普通乘法，令 $g(a,b)=\tau(ab)$，其中 $\tau(1)=0,\tau(\epsilon)=1$。其矩阵为 $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，非退化且不定。定义导子 $\delta1=0,\delta\epsilon=\epsilon$，令 $D_{\alpha+\beta\epsilon}=\alpha\delta$。取两份此场，$\lambda=0$ 时 $M_0$ 为交换结合张量乘法，每个 $T_H$ 都是乘法乘以导子的有限和，因而为导子。但 $D_{1+\epsilon}(1+\epsilon)=\epsilon\ne0$，且非零自伴随幂零元不可能有忠实 $C^*$ 表示。正性被删除后原来的 Hilbert 投影规范本身也不再可用；此例针对的是即使完整联合导子律仍不足的强边界，不把不定形式冒称范数。

第三项取 $\mathbb R1\oplus\mathbb R^3$ 的球比较，令

$$
D_{(\alpha,u)}(\beta,w)=(0,u_1(e_1\times w)).
$$

它是比较导子指派。对基 $1,e_1,e_2,e_3$，均有 $D_{e_i}e_i=0$，但对 $p=(e_1+e_2)/\sqrt2$ 有 $D_pp=e_3/2\ne0$，因此在 $\lambda=1$ 时相应自身联合报告非零。这只反驳由基向量自守推出全体自守，不宣称该对象通过剩余混合族。∎

**定义 13.2（文献对应与本候选边界）。** Jordan–Lie 复合性产生复结构及共同参数的背景仍按定理 2.1 引用。另见 [Moldoveanu，*Quantum mechanics from invariance principles*，式 (6) 及其后的单位关系](https://arxiv.org/html/1303.3935)：该路线讨论从复合性导出交替性，但局部不变性对所列全部运算施加 Leibniz，包含有向运算自身，并明确输入 $1\alpha f=0$。当前有限证书只预设 $D_a$ 导出交换比较，未预设 $D_1=0$ 或有向运算的局部 Loday 律；两者的假设不相同。

本候选的有限压缩、尚未交替时的尖锐自身缺陷界及内部迹标定作为上述一般场中的推导使用，不据此主张文献原创优先权。正定 Frobenius 比较、有限维、双方活动、联合模板及完整参考供应仍为前件；联合模板的唯一来源、无限维极限和实际物理单位不是本候选的结论。

## 追加锚（本行以下为增补区）

## 14. 从局部关系通道到实际联合运算

**定义 14.1（四通道闭包与单位参照）。** 两个局部场 $J_A,J_B$ 满足定义 8.1，记其比较和变化为 $S_A,B_A$ 与 $S_B,B_B$。在 $J_A\otimes_{\mathbb R}J_B$ 上给两个实际双线性运算 $M,T$，均属于

$$
\mathcal C_{AB}=\operatorname{span}_{\mathbb R}
\{S_A\otimes S_B,S_A\otimes B_B,B_A\otimes S_B,B_A\otimes B_B\}.
\tag{14.1}
$$

要求两个局部单位嵌入保存原来的两种关系：

$$
\begin{aligned}
M(a\otimes1,c\otimes1)&=S_A(a,c)\otimes1,&
T(a\otimes1,c\otimes1)&=B_A(a,c)\otimes1,\\
M(1\otimes b,1\otimes d)&=1\otimes S_B(b,d),&
T(1\otimes b,1\otimes d)&=1\otimes B_B(b,d).
\end{aligned}\tag{14.2}
$$

四通道闭包是模型的明确范围：连接只使用两种已有二元运算的张量通道，不允许其他局部二元运算参与。它不等同于“所有对象均在 $\Omega$ 内”，也没有从任意联合双线性映射的空间推出。尚不预设 $M$ 交换、$T$ 交替、联合导子律、复数、外部共同参数或 $D_1=0$。联合内积取 $g_A\otimes g_B$。

**命题 14.2（实际单位嵌入留下两个内部系数）。** 定义 14.1 等价于存在唯一实数 $\kappa,\beta$，使

$$
\boxed{M=S_A\otimes S_B+\kappa B_A\otimes B_B,
\qquad
T=B_A\otimes S_B+S_A\otimes B_B+\beta B_A\otimes B_B.}
\tag{14.3}
$$

这里的系数由已经给定的实际运算决定，不是另行输入的常数。

证明。每个局部的 $S,B$ 作为双线性映射线性独立。若 $xS+yB=0$，在第二槽放单位，$S(a,1)=a$、$B(a,1)=0$ 给 $x=0$；活动条件再给 $y=0$。有限维下，双线性映射空间的张量积到相应联合映射空间的通常识别是单射，所以四个通道独立。

对一般八个系数代入 (14.2)。第一边嵌入迫使 $M$ 的 $SS,BS$ 系数为 $1,0$，$T$ 的对应系数为 $0,1$；第二边迫使 $M$ 的 $SB$ 系数为零、$T$ 的 $SB$ 系数为一。仅两个 $BB$ 系数留下。这里只用 $B(1,1)=0$，没有使用 $B(1,a)=0$。反向代入验证全部单位嵌入。∎

## 15. 三因子一致性及其所在的更大代数

**定义 15.1（关系通道的严格重分组）。** 对三个局部场 $A,B,C$，允许每次二元连接使用各自的式 (14.3) 系数。将 $M_{AB},T_{AB}$ 再与第三方连接，和先连接 $B,C$ 再连接 $A$，要求得到相同的两个三方双线性运算。两种括号由通常实张量结合识别比较。

这一定义先讨论二元关系通道的组合，不要求任意系数所产生的中间对象已经满足局部导子合同。中间对象仍属于定义 8.1 的类别，是另一项必须验证的条件。

**定理 15.2（重分组同步系数，但不选择量子分支）。** 定义 15.1 的两个输出一致，当且仅当

$$
\begin{aligned}
\kappa_{AB}=\kappa_{BC}=\kappa_{(AB)C}=\kappa_{A(BC)},\\
\beta_{AB}=\beta_{BC}=\beta_{(AB)C}=\beta_{A(BC)}.
\end{aligned}\tag{15.1}
$$

任何共同实数 $\kappa,\beta$ 都满足该关系。因此重分组本身不排除额外变化通道，也不选择 $\kappa$ 的符号。

证明。以 $SSS,SBS,\ldots,BBB$ 表示八个局部张量通道。它们由命题 14.2 的局部独立性而独立。两种比较输出分别为

$$
\begin{aligned}
M_{(AB)C}
&=SSS+\kappa_{AB}BBS+\kappa_{(AB)C}BSB
 +\kappa_{(AB)C}SBB+\kappa_{(AB)C}\beta_{AB}BBB,\\
M_{A(BC)}
&=SSS+\kappa_{A(BC)}BBS+\kappa_{A(BC)}BSB
 +\kappa_{BC}SBB+\kappa_{A(BC)}\beta_{BC}BBB.
\end{aligned}\tag{15.2}
$$

两种变化输出分别为

$$
\begin{aligned}
T_{(AB)C}
&=BSS+SBS+SSB+\beta_{AB}BBS+\beta_{(AB)C}BSB
 +\beta_{(AB)C}SBB\\
&\quad +(\kappa_{AB}+\beta_{(AB)C}\beta_{AB})BBB,\\
T_{A(BC)}
&=BSS+SBS+SSB+\beta_{A(BC)}BBS+\beta_{A(BC)}BSB
 +\beta_{BC}SBB\\
&\quad +(\kappa_{BC}+\beta_{A(BC)}\beta_{BC})BBB.
\end{aligned}\tag{15.3}
$$

比较 (15.2) 的 $BBS,BSB,SBB$ 系数给全部 $\kappa$ 相等，比较 (15.3) 的同三通道给全部 $\beta$ 相等。其余系数此时自动一致，也证明逆向。若全体活动对象可彼此组合且每个三元组都满足此条件，两次相邻三元组便同步任意两条边；若仅给部分三元组，同步只在这些等式生成的连通类内成立。∎

**命题 15.3（二维系数代数的三种分支）。** 固定共同 $\kappa,\beta$ 后，式 (14.3) 的通道组合由通常二维含幺交换实代数

$$
E_{\kappa,\beta}=\mathbb R[x]/(x^2-\beta x-\kappa)
\tag{15.4}
$$

表达。其判别式 $\Delta=\beta^2+4\kappa$ 分别为负、零、正时，代数分别同构于 $\mathbb C$、双数代数、$\mathbb R\oplus\mathbb R$。

证明。在形式系数 $x$ 下，两个局部关系 $S_A+xB_A$ 与 $S_B+xB_B$ 的乘积为

$$
S_AS_B+\kappa B_AB_B
+x(B_AS_B+S_AB_B+\beta B_AB_B)=M+xT.
$$

该系数代数的结合性解释任意共同参数的重分组。置 $y=x-\beta/2$，则 $y^2=\Delta/4$，按符号作标准实代数识别即可。这里是成熟的二维实代数正规形；系数代数结合不等于各局部双线性乘法已经结合，后者仍由联合残差判定。∎

## 16. 实际有限残差选择联合模板

**引理 16.1（立方比较量的零矩）。** 在定义 8.1 的任一局部场中，对任意元 $p$，

$$
\boxed{g(p,S(p,D_pp))=0.}\tag{16.1}
$$

证明。令 $\delta=D_p,z=\delta p$，记 $t=g(S(p,p),z)$。Frobenius 性和导子律给

$$
2t=g(p,\delta S(p,p))=-g(\delta p,S(p,p))=-t.
$$

中间负号使用每个比较导子对 $g$ 斜伴随，所需事实是比较曲率 V95 定理 2.1 的第一项，适用于这里未预设交替的场。实数中 $3t=0$ 给 $t=0$，再用 Frobenius 性即得结论。它是立方比较量 $g(p,S(p,p))$ 沿比较导子的无穷小守恒，不预设 $D_pp=0$。∎

**定义 16.2（实际残差与候选 C98）。** 对定义 14.1 的实际运算，定义

$$
R(H,X,Y)=T(H,M(X,Y))-M(T(H,X),Y)-M(X,T(H,Y)).
\tag{16.2}
$$

使用定义 8.3 的同一有限带标签探针族 $\Pi_A\sqcup\Pi_B$，在每方完整基向量、归一两两和以及完整混合族上计算实际残差。第二方经张量翻转使用同一对 $M,T$，不另选独立连接器。命题 14.2 的形式在翻转后保持同一 $\kappa,\beta$。唯一候选条件为

$$
\boxed{\Theta(M,T)=\sum_{\pi\in\Pi_A\sqcup\Pi_B}\|R(\pi)\|^2=0.}\tag{C98}
$$

这里不搜索参数，也不逐报告调参；$M,T$ 是已经给出的联合关系。正平方和的零条件同时要求全部规定报告为零。

**引理 16.3（尚未交替时的精确原始式）。** 记 $v=D_bd,w=D_db,K_{ae}=[L_a,L_e]$，则

$$
\boxed{R(a\otimes b,c\otimes d,e\otimes1)
=\bigl(K_{ae}c+\beta S(c,D_ae)\bigr)\otimes v
-\kappa D_cD_ae\otimes w.}\tag{16.3}
$$

特别地，交换参照槽后的自身报告为

$$
\boxed{R(p\otimes d,p\otimes b,p\otimes1)
=-\kappa D_p^2p\otimes v+\beta S(p,D_pp)\otimes w.}\tag{16.4}
$$

证明。$M(c\otimes d,e\otimes1)=S(c,e)\otimes d$，而 $T(a\otimes b,e\otimes1)=D_ae\otimes b$。在 (16.2) 展开后，乘 $S(b,d)$ 的三项由局部导子律抵消；两个 $\beta$ 项之差是

$$
\beta\bigl(D_aS(c,e)-S(D_ac,e)\bigr)\otimes v
=\beta S(c,D_ae)\otimes v.
$$

剩余两个普通比较项给 $K_{ae}c\otimes v$，有向比较修正给最后的 $-\kappa$ 项。所有消去的单位项只用 $B(a,1)=0$，没有使用 $B(1,a)=0$。取 $a=c=e=p$ 并交换参照槽即得 (16.4)。∎

**定理 16.4（有限报告同时推出模板、符号与量子端点）。** 在定义 14.1 下，C98 等价于对全部联合输入有 $R(H,X,Y)=0$。成立时，命题 14.2 的内部系数必满足

$$
\boxed{\beta=0,\qquad\kappa=-\lambda_*<0,}\tag{16.5}
$$

其中 $\lambda_*$ 是定义 8.4 的内部标尺。两方的自守、交替、$D_1=0$、Jacobi 及正共同曲率律均成立，实际联合运算恰为 C97 的模板。局部复乘法

$$
m=S-i\sqrt{\lambda_*}B
$$

具有忠实有限复 $C^*$ 表示；联合乘法为通常代数张量积。每方实维数为 $n$ 时使用 $(n^3+n)/2$ 个带标签向量报告，两方实维数均为四时共 $68$ 个。该计数以闭包和单位嵌入为模型前件，不主张最小性。

证明。先排除 $\kappa=0$。若它为零，完整混合探针由 (16.3) 给

$$
(K_{ij}+\beta L_{B(e_i,e_j)})e_k\otimes v=0
\qquad(i<j,\ 1\le k\le n),
$$

其中伙伴 $v\ne0$。完整的 $k$ 基给零算子。$K_{ij}$ 斜伴而 $L_{B(e_i,e_j)}$ 自伴，分离伴随部分给 $K_{ij}=0$。$K$ 本来交替，故全部左乘算子对易，交换比较遂结合。定理 9.1 的零参数论证表明：正有限含幺交换结合 Frobenius 代数同构于有限实直积，全部导子为零。这与活动条件矛盾，所以 $\kappa\ne0$。

将 (16.4) 的第一因子与 $p$ 配对。引理 16.1 消去全部 $\beta$ 项，斜伴随给

$$
(g(p,\cdot)\otimes I)R_{\rm self}
=\kappa\|D_pp\|^2v.
\tag{16.6}
$$

因 $\kappa,v$ 均非零，各规定 $p$ 都有 $D_pp=0$。对基向量和归一两两和极化，得到全部元的交替性，再由 $B(a,1)=0$ 得 $D_1=0$。两方均先完成此步，才替换 $w=-v$。

此时混合报告变为

$$
R(a\otimes b,c\otimes d,e\otimes1)
=\bigl(K_{ae}-\kappa D_{B(a,e)}+\beta L_{B(a,e)}\bigr)c\otimes v.
\tag{16.7}
$$

完整混合族给括号内零算子。前两项斜伴，最后一项自伴，故 $\beta L_{B(e_i,e_j)}=0$。活动与已经得到的交替性保证某个 $i<j$ 的 $z=B(e_i,e_j)\ne0$；$L_z1=z$ 又保证 $L_z\ne0$，于是 $\beta=0$。

现在实际运算恰为定义 8.2，参数 $\lambda=-\kappa\ne0$，同一有限族的残差为零。直接应用定理 9.1，得到 $\lambda=\lambda_*>0$、Jacobi、全部联合导子律及有限复 $C^*$ 重构。这里的 Jacobi、正号与结合表示均由该已有结果承担，不重认作新的表示定理。全输入残差为零显然推出有限平方和为零，完成等价。计数与定义 8.3 相同。∎

## 17. 局部盲核、联合诊断与条件误差界

**定理 17.1（简单张量全盲，两项联合向量达到最大读数）。** 在定义 14.1 下，不要求 C98。对任意 $H$ 及任意简单张量 $X$，均有

$$
g(X,T_HX)=0,
\qquad T_HX=T(H,X).
\tag{17.1}
$$

若固定 $H=h\otimes k$，且 $D_h,D_k$ 非零，则

$$
\boxed{\sup_{\|X\|=1}|g(X,T_HX)|
=|\beta|\,\|D_h\|_{\rm op}\|D_k\|_{\rm op}.}\tag{17.2}
$$

该上确界由一个实张量秩为二的联合向量达到。$\beta\ne0$ 时，秩一向量全盲，而秩二足以达到最强二次读数。

证明。固定简单 $H$ 时，

$$
T_H=D_h\otimes L_k+L_h\otimes D_k+\beta D_h\otimes D_k.
$$

前两项斜伴，最后一项自伴。对 $X=u\otimes v$，最后项的二次读数为 $\beta g(u,D_hu)g(v,D_kv)=0$，故 (17.1) 成立；任意 $H$ 由线性扩展得到。

选单位向量 $u,v$ 使 $r=\|D_hu\|>0,s=\|D_kv\|>0$，置

$$
u'=D_hu/r,\qquad v'=D_kv/s,\qquad
X_*=(u\otimes v+u'\otimes v')/\sqrt2.
$$

两对局部向量分别正交单位，所以 $\|X_*\|=1$、其张量秩为二。两个对角读数为零，两个交叉读数均为 $rs$，例如

$$
g(u,D_hu')g(v,D_kv')=(-r)(-s)=rs.
$$

因此

$$
\boxed{g(X_*,T_HX_*)=\beta rs.}\tag{17.3}
$$

任意单位 $X$ 的绝对读数至多为 $|\beta|\|D_h\|_{\rm op}\|D_k\|_{\rm op}$。有限维斜伴算子的最大旋转平面给单位 $u,v$ 达到 $r=\|D_h\|_{\rm op},s=\|D_k\|_{\rm op}$，上述构造达到该界。沿 $\dot X=T_HX$ 的范数平方初始变化率为两倍此读数；不把简单张量的初始零变化率说成其有限时间轨道保范数。$X_*$ 尚未被赋予状态正锥，因而这里只断言实张量秩，不把它称为量子纠缠态。∎

**定理 17.2（混合通道不污染自身缺陷的尖锐投影界）。** 在定义 14.1 下，对 $\kappa\ne0$、固定活动参照 $v=D_bd\ne0$，任意 $p$ 满足

$$
\boxed{\|D_pp\|^2
\le\frac{\|p\|\,\|R(p\otimes d,p\otimes b,p\otimes1)\|}
{|\kappa|\,\|v\|}.}\tag{17.4}
$$

不要求 $\beta=0$、交替或 C98。若全部单位向量的该自身报告统一至多为 $\varepsilon$，则自身改变量统一至多为 $\sqrt{\varepsilon/(|\kappa|\|v\|)}$；指数及常数一均尖锐。

证明。式 (16.6) 在残差不为零时仍是恒等式；算子 $g(p,\cdot)\otimes I$ 的范数为 $\|p\|$，取范数即得 (17.4)。定理 10.1 的旋转球例在 $\beta=0,\kappa=-\lambda$ 时达到等号，故常数和指数不能改善。此处消去任意 $\beta$ 的机制是零矩，不是预先假设其为零。该结论只控制自身报告族，不建立一般近似量子代数稳定性。∎

**定理 17.3（已交替但未 Jacobi 时的两参数正交缺额）。** 在定义 14.1 下，另已得到或明确要求两方 $B$ 交替，但不要求 Jacobi 或 C98。固定伙伴 $v\ne0$，令 $\mathcal W_{\rm mix}$ 为一方完整混合族的残差平方和，沿用定理 11.1 的正数 $\mathsf a,\mathsf h,\mathsf c$。则

$$
\boxed{\frac{\mathcal W_{\rm mix}(\kappa,\beta)}{\|v\|^2}
=\mathsf c\left(\kappa+\frac{\mathsf h}{\mathsf c}\right)^2
+\mathsf h\beta^2
+\frac{\mathsf a\mathsf c-\mathsf h^2}{\mathsf c}.}\tag{17.5}
$$

最佳两参数唯一为 $(-\mathsf h/\mathsf c,0)$，且

$$
|\beta|\le\sqrt{\mathcal W_{\rm mix}/(\|v\|^2\mathsf h)}
\tag{17.6}
$$

的常数一可达到。

证明。式 (16.7) 给混合算子 $E_{ij}=K_{ij}-\kappa D_z+\beta L_z$，其中 $z=B(e_i,e_j)$。前两项斜伴，$L_z$ 自伴，故两部分在 Hilbert–Schmidt 内积下正交。又 $\|L_z\|_{\rm HS}^2=q(z,z)$。定理 11.1 已在未假设 Jacobi 时证明 $\operatorname{Tr}(K_{ij}D_z)=q(z,z)$，故逐对求和、配方得到 (17.5)。三个系数严格为正和缺额非负也由该定理承担。两个平方项给唯一极小点与 (17.6)。两方取共同标尺的非交换有限复 $C^*$ 场，$\kappa$ 取其精确比较系数，则曲率平方和缺额均为零，任意 $\beta$ 达到 (17.6)。此定理的混合解释明确依赖双方已交替；不向交替前的全部噪声模型外推。∎

## 18. 删除连接条件的实际后果

**命题 18.1（三因子重分组不能替代联合导子律）。** 取两份单位关系球 $\mathbb R1\oplus\mathbb R^3$，$B(u,v)=u\times v$，采用任意共同 $\kappa,\beta$ 的式 (14.3)。它们的关系通道满足定理 15.2 的重分组，但联合导子残差一般不为零。具体取正交向量 $a=b=e_1,e=d=e_2$，则

$$
\begin{aligned}
R(e_1\otimes e_1,1\otimes e_2,e_2\otimes1)
 &=\beta e_3\otimes e_3,\\
R(e_1\otimes e_1,e_2\otimes e_2,e_2\otimes1)
 &=(1+\kappa)e_1\otimes e_3.
\end{aligned}\tag{18.1}
$$

证明。这里 $v=e_3$，$B(e_1,e_2)=e_3$。式 (16.7) 中 $K_{12}1=D_{e_3}1=0,L_{e_3}1=e_3$，给第一式。第二式用 $K_{12}e_2=e_1,D_{e_3}e_2=-e_1,L_{e_3}e_2=0$。这两个实际残差分别检出额外变化通道和错误比较系数；任意共同参数的形式重分组依然成立。∎

**命题 18.2（额外内部通道可保全部联合导子律而失去量子端点）。** 删去四通道闭包后，局部正比较、非零活动、实际单位嵌入、正的联合比较、全部联合导子律、全部联合范数守恒和严格三因子重分组可以同时成立，而局部仍不自守，也不属于有限复 $C^*$ 自伴类别。

证明。对任意定义 8.1 的局部场定义内部泛函和二元通道

$$
\tau_i(a)=\frac{g_i(1,a)}{g_i(1,1)},\qquad U_i(a,c)=\tau_i(a)c.
$$

在联合空间取

$$
\begin{aligned}
M'&=S_A\otimes S_B,\\
T'&=B_A\otimes U_B+U_A\otimes B_B,\\
D'_{a\otimes b}
&=\tau_B(b)D_a\otimes I+\tau_A(a)I\otimes D_b.
\end{aligned}\tag{18.2}
$$

$M'$ 是正内积下的含幺交换 Frobenius 比较；每个 $D'_H$ 是 $M'$ 的导子，因为 $D_a\otimes I$ 与 $I\otimes D_b$ 分别导出纯张量比较。它们斜伴，所以所有联合向量在其固定生成元流下保范数。双方单位嵌入由 $\tau_i(1)=1,D_a1=0$ 直接给出，也保留非零活动。故所有联合残差均为零。

联合单位与乘积内积给 $\tau_{AB}=\tau_A\otimes\tau_B$。两种三因子重分组均为 $M''=S_A\otimes S_B\otimes S_C$，且

$$
\begin{aligned}
D''_{a\otimes b\otimes c}
&=\tau_B(b)\tau_C(c)D_a\otimes I\otimes I\\
&\quad+\tau_A(a)\tau_C(c)I\otimes D_b\otimes I\\
&\quad+\tau_A(a)\tau_B(b)I\otimes I\otimes D_c.
\end{aligned}\tag{18.3}
$$

因此重分组严格一致，并可归纳到任意有限个输入；每个中间对象仍保持上述正比较与导子合同。

具体局部取 $J=\mathbb R1\oplus\mathbb R^2$ 的球比较及标准正内积，令 $J_0e_1=e_2,J_0e_2=-e_1$，取

$$
D_{(\alpha,u)}(\beta,w)=(0,u_1J_0w).
$$

旋转是球比较的导子，但 $D_{e_1}e_1=e_2\ne0$。该三维实场的比较也不结合：$(e_1\circ e_1)\circ e_2=e_2$，$e_1\circ(e_1\circ e_2)=0$。实自伴维数为三的有限复 $C^*$ 代数只能是三个一维块，其比较结合，因此不能与此场同构。

额外通道确实越出闭包。若 $U=xS+yB$，在第二槽放单位得 $\tau(a)1=xa$；令 $a=1$ 给 $x=1$，从而迫使全部 $a$ 为单位的倍数，与活动场维数大于一矛盾。将第一因子双线性映射空间对 $\operatorname{span}(S_A,B_A)$ 取商，$T'$ 的像为 $[U_A]\otimes B_B\ne0$，而所有四通道映射的像都为零。因此实际联合变化自身不在四通道张成中。

$\tau,U$ 都从已有单位、比较内积和线性运算内部定义；所以“没有额外外部原始数据”不能取代四通道闭包。此反例既通过全部有限残差，也通过全部输入残差，具体定位了闭包前件的作用。∎

## 19. 完整有限理论、单位自由与文献对应

**定理 19.1（实际连接候选的量子理论接续）。** 在定义 14.1 与 C98 下，局部及联合的复代数均为有限直和复矩阵代数，各局部至少有一个非交换块。若进一步提供定理 12.1 所列全部正归一状态、全部效果及有限参考，概率取状态评价，则得到密度矩阵与 Born 规则。若允许的线性过程恰为对全部有限参考联合保正的过程，有结果的过程保留有限标签且总和保迹，则得到完全正仪器。连续一参数 $*$ 自同构群给 Hamilton 演化。

证明。定理 16.4 已将实际运算归约到精确 C97，直接应用定理 12.1 及其所引定理 6.2。复代数的分类、状态与过程表示是成熟工具，不是四通道有限归约的额外新结论。给定对象族能取得所有维数的系统仍是供应条件，所选过程的吸引终态仍需另证其收敛；固定有限场的重构不蕴含这两项。∎

**命题 19.2（内生系数与绝对时钟单位）。** 共同重标 $B\mapsto tB$、$t\ne0$，并令实际 $M$ 保持、实际 $T\mapsto tT$，则

$$
\kappa\mapsto\kappa/t^2,\qquad
\beta\mapsto\beta/t,\qquad
R\mapsto tR.
$$

因此 C98 的真假和重构类别保持不变，绝对时间单位仍未固定。

证明。代入式 (14.3) 逐项比较，给前两式；残差在实际 $T$ 上一次齐次，给第三式。参照对在非零重标下仍活动，故同一有限族的零报告条件保持。∎

**定义 19.3（成熟机制与本候选的具体范围）。** 一般四通道连接及单位归约的原文对应见 [Moldoveanu，*Quantum mechanics from invariance principles*，arXiv:1303.3935，式 (6)–(9)](https://arxiv.org/html/1303.3935)。其中局部不变性对所列运算族施加 Leibniz，包含有向运算自身，并另给 $1\alpha f=0$。这里仅预设局部变化导出交换正比较，$D_1=0$、交替与 Jacobi 均由有限实际报告推出。

复合性与两运算重构的历史背景为 Grgin–Petersen，*Algebraic implications of composability of physical systems*，Commun. Math. Phys. 50，177–188，DOI [10.1007/BF01617995](https://doi.org/10.1007/BF01617995)。一般共同参数及复结构接续使用定理 2.1 已引的 [Kapustin，Theorem 3.1](https://arxiv.org/html/1303.6917v4)，动力对应接续使用比较曲率 V95 的原文对应。二维商代数、实斜伴旋转平面、张量算子范数和正交配方均为标准中间工具。

C98 在当前合同下的具体推导是：有限零矩排除自身报告中的额外混合干扰，同一有限族同时推出模板与量子符号；另有秩一观察的联合盲核、秩二尖锐诊断及额外内部通道反例。这些陈述不据限定检索主张文献原创优先权。四通道闭包、有限维、局部正 Frobenius 比较、活动及完整操作供应仍是明确前件；无限维极限、四通道闭包的唯一来源及物理单位数值不属于上述结论。

## 追加锚（本行以下为增补区）

## 20. 保留条件取值的实际关系延伸

**定义 20.1（局部作用与条件作用的同一延伸）。** 局部对象仍取定义 8.1 的有限正 Frobenius 比较场，不预设 Jordan、交替、Jacobi、$D_1=0$ 或复结构。两个对象 $A,B$ 的实际延伸，是实空间

$$
J_{AB}=J_A\otimes_{\mathbb R}J_B,
\qquad g_{AB}=g_A\otimes g_B
$$

上的交换含幺 Frobenius 比较 $M$，以及实线性映射 $\Gamma:J_{AB}\to\operatorname{End}(J_{AB})$。其单位是 $1_A\otimes1_B$，内积正定。要求以下定义间的约束对全部输入成立：

$$
\begin{aligned}
M(a\otimes1,c\otimes d)&=S_A(a,c)\otimes d,\\
M(1\otimes b,c\otimes d)&=c\otimes S_B(b,d),
\end{aligned}\tag{20.1}
$$

$$
\begin{aligned}
\Gamma_{a\otimes b}(c\otimes1)&=D_ac\otimes b,\\
\Gamma_{a\otimes b}(1\otimes d)&=a\otimes D_bd,
\end{aligned}\tag{20.2}
$$

以及实际联合比较的变化律

$$
\Gamma_HM(X,Y)=M(\Gamma_HX,Y)+M(X,\Gamma_HY).
\tag{20.3}
$$

式 (20.1) 是局部乘法在整体中的模作用。式 (20.2) 要求另一方的实际取值被完整保留：用 $a\otimes b$ 改变局部元 $c\otimes1$ 时，留下 $D_ac\otimes b$，而不是先将 $b$ 压成一个平均数。式 (20.3) 约束同一变化与同一二元比较的相容性。所有量来自这些实际关系，不给联合运算选择一个四通道张成空间，也不另给联合系数。

由 (20.2) 和局部活动性，$\Gamma\ne0$；由 (20.3)，这个实际整体本身又是定义 8.1 的对象。这里的有限维、正内积、实张量载体、单位与局部导子合同仍是明确的模型前件。

**定义 20.2（候选 C99：实际二元关系可再作一次活动延伸）。** 对定义 20.1 的一个给定实际二元延伸 $(AB,M,\Gamma)$，要求存在同一理论中的活动对象 $C$，使这个实际整体与 $C$ 再满足定义 20.1。外层必须使用已经给定的 $M,\Gamma$，不能为取得延伸而重选内层运算。记此条件为

$$
\boxed{(AB,M,\Gamma)\ \text{具有一个满足式 (20.1)–(20.3) 的活动延伸 }(AB)C.}
\tag{C99}
$$

这只要求一个括号方向的有限三方提升，不预设另一括号 $A(BC)$，也不预设重分组一致性。对一个关系体要求 C99，指其每条实际二元延伸都满足上述条件；见定义 25.1 的量词。

## 21. 不给通道闭包，也能反推出局部量子结构

**定理 21.1（条件作用确定完整变化，并强迫自守）。** 定义 20.1 的任何实际延伸必满足

$$
\boxed{\Gamma_{a\otimes b}=D_a\otimes L_b+L_a\otimes D_b.}
\tag{21.1}
$$

两方均有 $D_aa=0$、$B(a,c)=-B(c,a)$ 及 $D_1=0$。这三个性质不需要 C99 的第三方。

证明。式 (20.1) 给 $c\otimes d=M(c\otimes1,1\otimes d)$。用 (20.3) 对此比较求变化，再用 (20.2) 和两个模作用，得到

$$
\Gamma_{a\otimes b}(c\otimes d)
=D_ac\otimes S_B(b,d)+S_A(a,c)\otimes D_bd.
$$

简单张量张成全部联合空间，故得到 (21.1)。

记实际左乘为 $\mathbb L_XY=M(X,Y)$，局部曲率为 $K_{ac}=[L_a,L_c]$，并先使用未校正的差

$$
F(X,Y)=M(X,Y)-(S_A\otimes S_B)(X,Y).
$$

导子与左乘的交换关系 $[\Gamma_H,\mathbb L_X]=\mathbb L_{\Gamma_HX}$，配合 (21.1)，给

$$
\begin{aligned}
\mathbb L_{D_ac\otimes b}
 &=L_{D_ac}\otimes L_b+K_{ac}\otimes D_b,\\
\mathbb L_{a\otimes D_bd}
 &=L_a\otimes L_{D_bd}+D_a\otimes K_{bd}.
\end{aligned}\tag{21.2}
$$

第一式由与 $L_c\otimes I$ 取交换子得到，第二式由与 $I\otimes L_d$ 取交换子得到；此处没有把尚未证明的 $D_1=0$ 放入推导。

固定 $a$ 并令 $z=D_aa$。因 $K_{aa}=0$，第一式给 $F(z\otimes b,Y)=0$。另取 $w=D_fg$，第二式和 $F$ 的交换性给

$$
0=F(z\otimes b,c\otimes w)
 =F(c\otimes w,z\otimes b)
 =D_cz\otimes K_{fg}b.
\tag{21.3}
$$

活动伙伴必有某个 $K_{fg}\ne0$。否则全部左乘对易，交换比较结合；有限正含幺交换结合 Frobenius 代数是有限实直积，所有导子为零，和 $D\ne0$ 矛盾。这一步复用定理 9.1 的零参数论证。

选 $f,g,b$ 使 $K_{fg}b\ne0$，式 (21.3) 迫使 $D_cz=0$ 对全部 $c$ 成立，特别是 $D_az=0$。局部导子斜伴随，所以

$$
\|z\|^2=g(D_aa,z)=-g(a,D_az)=0.
$$

正定性给 $D_aa=0$。交换双方得到两边结论；对 $D_{a+c}(a+c)=0$ 极化得交替，再用 $D_a1=0$ 得 $D_1a=0$。∎

**定理 21.2（曲率经变化因子化，共同负比例由正性选出）。** 定义 20.1 的两方存在唯一共同 $\lambda>0$，使

$$
\boxed{K_{ac}=-\lambda D_{B(a,c)}.}
\tag{21.4}
$$

两方的 $B$ 满足 Jacobi，且

$$
m=S-i\sqrt\lambda B
\tag{21.5}
$$

在复化上是有忠实正 $*$ 表示的结合乘法；两方都是有限复 $C^*$ 代数的自伴部分，且各自至少有一个非交换矩阵块。对任意 $z=B(a,c)\ne0$，内部比例为

$$
\boxed{\lambda=
\frac{\operatorname{Tr}(L_z^2)}{\|D_z\|_{\rm HS}^2}.}
\tag{21.6}
$$

证明。令 $W=\operatorname{span}\{B(a,c):a,c\in J\}$。式 (21.2) 第一式说明：若 $\sum_jB(a_j,c_j)=0$，则

$$
\left(\sum_jK_{a_jc_j}\right)\otimes D_b=0
$$

对全部伙伴 $b$ 成立。选 $D_b\ne0$，得到 $\sum_jK_{a_jc_j}=0$。因此存在良定义线性映射 $\mathcal K:W\to\operatorname{End}(J)$，满足 $\mathcal K(B(a,c))=K_{ac}$。

由交替和斜伴随，$W^\perp=\ker D$：$c\perp W$ 等价于 $D_ac=0$ 对全部 $a$ 成立，也等价于 $D_c=0$。所以 $D|_W$ 单射，且 $W\ne0$。对 $z\in W_A,w\in W_B$，式 (21.2) 的两种计算给

$$
\mathcal K_A(z)\otimes D^B_w
 =D^A_z\otimes\mathcal K_B(w).
\tag{21.7}
$$

若一边 $\mathcal K$ 恒为零，则全部该边曲率为零，和活动性矛盾。选两边非零的基准值，用非零简单张量相等的比例性质，再固定其中一边，得到同一非零实数 $\kappa$，使

$$
\mathcal K_A(z)=\kappa D^A_z,
\qquad \mathcal K_B(w)=\kappa D^B_w.
$$

具体地，先选 $\mathcal K_A(z_0)\ne0$ 及任意 $w_0\ne0$；(21.7) 的左端非零，右端也非零，两对因子因此成比例。固定 $w_0$ 推广到全部 $z$，再固定 $z_0$ 推广到全部 $w$，不对各对输入另选比例。

定理 11.1 在尚未假设 Jacobi 时已经给出

$$
\operatorname{Tr}(K_{ac}D_z)=\operatorname{Tr}(L_z^2)>0
\qquad(z=B(a,c)\ne0).
$$

因 $D_z$ 非零且斜伴随，左端为 $-\kappa\|D_z\|_{\rm HS}^2$，故 $\kappa<0$。置 $\lambda=-\kappa$ 即得 (21.4)、(21.6) 及唯一性。

现在构造定义 8.2 的待检验标准模板，只用于调用已有重构结果。自守报告由定理 21.1 为零；混合报告由 $K_{ac}+\lambda D_{B(a,c)}=0$ 为零。因此定理 9.1 适用，给 Jacobi、式 (21.5) 的结合性及忠实正表示，定理 12.1 给有限矩阵直和分类。这里复用已有的动力对应与有限表示桥，不把它们另算为新的表示定理。∎

## 22. 两方约束留下的全部静态自由

**定理 22.1（实际联合比较的精确盲核分类）。** 在定义 20.1 下，使用定理 21.2 得到的共同 $\lambda$，记

$$
\begin{aligned}
M_{\rm q}&=S_A\otimes S_B-\lambda B_A\otimes B_B,\\
Z_i&=\ker D_i,
\qquad Z_i^0=Z_i\cap1_i^\perp,
\qquad V=Z_A^0\otimes Z_B^0.
\end{aligned}\tag{22.1}
$$

$Z_i$ 正是局部有限复代数的自伴中心。所有实际联合比较恰为

$$
\boxed{M(X,Y)=M_{\rm q}(X,Y)+C(P_VX,P_VY),}
\tag{22.2}
$$

其中 $P_V$ 是正交投影，$C:V\times V\to V$ 的配对

$$
\chi(u,v,w)=g_{AB}(C(u,v),w)
\tag{22.3}
$$

是任意全对称三线性型。反过来，每个这样的 $\chi$ 都保留定义 20.1 的全部条件，且实际 $\Gamma$ 始终是 (21.1)。若 $r_i=\dim Z_i$，自由空间的维数为

$$
\boxed{\dim\operatorname{Sym}^3(V^*)
=\frac{k(k+1)(k+2)}6,
\qquad k=(r_A-1)(r_B-1).}
\tag{22.4}
$$

任一方中心一维时，这个自由空间为零，两方条件已足以确定实际联合模板。

证明。在重构的矩阵代数中，$D_ac=i(ac-ca)/(2\sqrt\lambda)$，故 $Z_i$ 是中心，而 $W_i=Z_i^\perp$。令 $F_1=M-M_{\rm q}$。式 (21.2) 与 (21.4) 给

$$
F_1(z\otimes b,Y)=0\ (z\in W_A),
\qquad F_1(a\otimes w,Y)=0\ (w\in W_B).
\tag{22.5}
$$

$g_{AB}(F_1(X,Y),Z)$ 因交换及 Frobenius 性而全对称。所以其每一槽都只能落在 $(W_A\otimes J_B+J_A\otimes W_B)^\perp=Z_A\otimes Z_B$。式 (20.1) 又迫它在任一槽属于 $Z_A\otimes1+1\otimes Z_B$ 时为零；在中心张量空间内取其正交补恰得 $V$。Riesz 对应给 (22.2)–(22.3) 的唯一表达。

反向取任意这样的 $\chi$。补项交换、Frobenius，且遇局部模输入为零，也不改变单位；正内积本身没有改变。$\Gamma_H$ 消去 $Z_A\otimes Z_B$，并且由 (21.1) 对乘积内积斜伴随，故其像垂直于该中心张量空间。于是

$$
\Gamma_HC(P_VX,P_VY)=0,
\qquad C(P_V\Gamma_HX,P_VY)=C(P_VX,P_V\Gamma_HY)=0.
$$

标准量子部分满足导子律，补项的三项均为零，故实际 $M$ 仍满足完整 (20.3)。条件作用不变。有限维对称三线性型的标准维数公式给 (22.4)。∎

**命题 22.2（活动双方仍可保留一个非 Jordan 的整体）。** 定义 20.1 不蕴含实际 $M$ 为 Jordan，也不蕴含实际整体是有限复 $C^*$ 自伴部分。

证明。两方均取

$$
J=\operatorname{Herm}_2(\mathbb C)\oplus\mathbb R^2,
\qquad
S(a,c)=\tfrac12(ac+ca),
\qquad B(a,c)=\tfrac i2(ac-ca),
$$

并用正的逐块迹内积；在经典 $\mathbb R^2$ 块取 $\langle u,v\rangle=(u_1v_1+u_2v_2)/2$。它们活动，且共同 $\lambda=1$。令 $u=(1,1),z=(1,-1)$ 仅支持经典块。在双方的纯经典联合块上，以下四元正交归一：

$$
e=u\otimes u,\quad p=z\otimes u,
\quad r=u\otimes z,\quad q=z\otimes z.
$$

标准乘法满足 $p^2=r^2=q^2=e$、$pr=q,pq=r,rq=p$。$q\in V$。对任意实数 $t\ne0$，取

$$
M_t(X,Y)=M_{\rm q}(X,Y)
+t\,g_{AB}(q,X)g_{AB}(q,Y)q.
\tag{22.6}
$$

定理 22.1 保证全部局部模作用、条件作用、实际联合导子律、正 Frobenius 比较及活动性仍成立。补项仅将上述乘法表中的 $q^2$ 改为 $e+tq$。

但在这个实际整体中，取 $x=p+q$，有

$$
x^2=2e+2r+tq,
\qquad [\mathbb L_x,\mathbb L_{x^2}]p=2tq\ne0.
\tag{22.7}
$$

例如两种嵌套结果分别为 $4e+4r+3tq+tp$ 与 $4e+4r+tq+tp$。Jordan 恒等式失效，因此实际整体不能保持其比较而同构为有限复 $C^*$ 自伴部分。这里不是缺少非交换活动，而是所有已有变化都看不见的静态联合记录仍可被变形。∎

## 23. 第三方如何消掉整体内部的静态形变

**定理 23.1（一次活动提升认证原来的二元整体）。** 对一个给定的定义 20.1 实际延伸，C99 蕴含两方具有定理 21.2 的有限复 $C^*$ 重构，且其实际联合关系正好是

$$
\boxed{M=M_{\rm q},
\qquad \Gamma=B_A\otimes S_B+S_A\otimes B_B.}
\tag{23.1}
$$

此时原整体的复乘法是通常的代数张量乘法，第三方与原两方具有同一正内部标尺。第三方不必预先指定为量子比特；任何满足 C99 的活动第三方都至少为四维实空间。反向，每个具有 (23.1) 的实际整体都存在一个四维活动数学延伸；该延伸若由给定关系体供应，就满足 C99。

证明。若 C99 成立，对实际对象 $AB$ 与 $C$ 应用定理 21.2。它推出实际 $M$ 是 Jordan 比较，完全不需要先指定外层四通道或内层 Jordan 性。下面证明这会消去定理 22.1 的全部 $\chi$。

设 $e_i$ 是 $Z_A$ 的最小中心幂等元，$f_j$ 是 $Z_B$ 的相应幂等元。在联合 Jordan 代数中令 $e=e_i\otimes1$。由模作用，

$$
\mathbb L_e=L_{e_i}\otimes I,
\qquad \mathbb L_e^2=\mathbb L_e,
\qquad M(e,e)=e.
\tag{23.2}
$$

Jordan 恒等式 $[\mathbb L_y,\mathbb L_{M(y,y)}]=0$ 在 $y=e+tx$ 的一次项给

$$
2[\mathbb L_e,\mathbb L_{M(e,x)}]
=[\mathbb L_e,\mathbb L_x].
\tag{23.3}
$$

将 $x$ 分成 $\mathbb L_e$ 的零与一本征分量。在每个分量 $M(e,x)=\varepsilon x$，$\varepsilon\in\{0,1\}$，故 $(2\varepsilon-1)[\mathbb L_e,\mathbb L_x]=0$。于是 $\mathbb L_e$ 与所有实际左乘对易。对 $1\otimes f_j$ 同理。

在交换代数中，一个这样的元 $e$ 满足 $\mathbb L_{M(e,x)}=\mathbb L_e\mathbb L_x$：在任意 $y$ 上用两次左乘对易即可将 $M(M(e,x),y)$ 改写成 $M(e,M(x,y))$。因此

$$
\mathbb L_{e_i\otimes f_j}
=\mathbb L_{e_i\otimes1}\mathbb L_{1\otimes f_j}
=L_{e_i}\otimes L_{f_j}.
\tag{23.4}
$$

这与 $M_{\rm q}$ 的左乘相同。各 $e_i\otimes f_j$ 张成 $Z_A\otimes Z_B$；结合 (22.5)，全部 $F_1$ 为零，得到 (23.1)。变化模板已由定理 21.1 确定。

设外层得到的标尺是 $\lambda'$。其对实际 $AB$ 的曲率律限制到 $a\otimes1,c\otimes1$，给

$$
K^A_{ac}\otimes I
=-\lambda' D^A_{B_A(a,c)}\otimes I.
$$

内层同式的系数为 $\lambda$；活动性和 (21.6) 保证能选 $D^A_{B_A(a,c)}\ne0$，故 $\lambda'=\lambda$。此时

$$
m_{AB}=M-i\sqrt\lambda\,\Gamma=m_A\otimes m_B.
\tag{23.5}
$$

反向，若实际内层已有 (23.1)，取一个内部数学对象 $C=\operatorname{Herm}_2(\mathbb C)$，用同一 $\lambda$ 定义其交换子作用。对实际 $AB$ 与 $C$ 采用通常复代数张量乘法的实、虚两部分，即得满足定义 20.1 的活动延伸和乘积 Frobenius 内积。这证明作为代数模型的延伸存在；指定关系体是否已供应这个具体对象，要按定义 25.1 的对象供应判定。

由外层定理 21.2，任意可用的 $C$ 均有至少一个非交换复矩阵块，所以 $\dim_{\mathbb R}J_C\ge4$；上述量子比特构造达到四维。这里的三方提升指三个系统的关系，并不声称第三方的实维数为三。∎

**命题 23.2（静态参考不能替代活动参考，终层也不能越级认证）。** 若将 C99 的第三方活动要求删去，命题 22.2 的全部非 Jordan 实际整体仍可延伸到 $AB\otimes\mathbb R$。即使给出一个活动三方延伸，它也只认证被延伸的原二元整体，不自动认证新三方整体的实际比较。

证明。对任意实际 $AB$ 取 $J_C=\mathbb R$、$D^C=0$，外层比较和变化由 $AB$ 的原运算乘以标量定义；式 (20.1)–(20.3) 逐项成立，原来的 (22.7) 保持。因此静态一维参考没有排除力。

对第二项，令 $A,B,C$ 都取命题 22.2 的局部对象，内层 $AB$ 先用标准量子比较；这个整体有一个四维纯经典联合块。对外层 $(AB,C)$，在该块与 $C$ 的经典块中选取命题 22.2 的两个二值中心记录，施加同一非零三线性补项，便满足全部三方延伸合同，而内层 $AB$ 保持标准、外层非 Jordan。只有外层自己又有活动延伸，定理 23.1 才认证它。∎

## 24. 反事实、三元结构及定义约束的剩余前件

**命题 24.1（两种丢失条件具有不同的后果）。** 若保留局部单位嵌入与全部联合导子律，却把式 (20.2) 改成先平均另一方取值的作用，则局部自守也可以失效。若保持式 (20.2)，但删去 C99 的活动提升，则局部复量子结构仍被强迫，实际整体的静态三线性自由却不受约束。

证明。第一项由命题 18.2 的内部平均通道给出。其局部作用是 $\tau_B(b)D_ac\otimes1$，而不是 $D_ac\otimes b$；对非零且 $\tau_B(b)=0$ 的 $b$，两者可以分别为零与非零。该模型保留其完整联合导子律和任意有限重分组，但局部 $D_{e_1}e_1=e_2$。因此“全部材料都在内部”和重分组均不能补回被平均掉的条件取值。

第二项由定理 21.1–21.2 与命题 22.2 同时成立给出：局部重构已经完成，而 (22.7) 仍可失效。第三方的作用不是替局部再选一组参数，而是使原整体的比较本身也受到同一局部重构论证的约束。∎

**命题 24.2（第三方约束的较弱静态替代及有限性）。** 对一个定义 20.1 的二元延伸，以下纯静态条件也等价于 $M=M_{\rm q}$：

$$
\begin{aligned}
&M\bigl(M(z\otimes1,1\otimes w),k\bigr)\\
&\hspace{1em}=M\bigl(z\otimes1,M(1\otimes w,k)\bigr)
\quad(z\in Z_A,w\in Z_B,k\in Z_A\otimes Z_B).
\end{aligned}\tag{24.1}
$$

它只要求共同固定记录的混合接续结合。给定两层实际有限对象之后，所有恒等式都可在完整有限基上判定；这里不主张所需报告数最少。

证明。右端由两次局部模作用完全固定为标准中心乘法，左端为 $M(z\otimes w,k)$。两者之差恰为 $C(P_V(z\otimes w),P_Vk)$。中心简单张量张成全部中心张量空间，故 (24.1) 等价于 $C=0$。反向标准张量乘法在中心结合，等式成立。

有限性来自全部运算双线性、$\Gamma$ 对标签线性、(20.3) 对 $H,X,Y$ 三线性。将各自的所有变量遍历完整基足以判定相应恒等式；Frobenius 性也是有限三线性恒等式，正定性为有限 Gram 矩阵条件。C99 还要求存在一个实际活动延伸，不能把只检查内层有限报告说成已经取得外层对象。∎

## 25. 在整个关系体中使用同一个候选

**定义 25.1（可继用的活动关系体）。** 设 $\Omega$ 是一族定义 8.1 的对象及其指定实际二元延伸，满足：每个允许的二元延伸遵守定义 20.1；每个实际二元整体作为同一对象保留在 $\Omega$ 中，并至少有一个 $\Omega$ 内的活动对象可与之再作定义 20.1 的延伸。这就是对所有实际二元关系量化的 C99。

该定义不要求每两对象都可组合，也不预先给结合子或交换子；若要发展所有有限并置的理论，另外规定每对对象及所需有限重复副本都可组合。每个具体二元关系的认证仍只使用一次三方有限提升，不以一个完成的无限张量乘积为证明前提。

**定理 25.2（整个关系体的复量子表示与重分组）。** 在定义 25.1 下，每个实际二元整体都具有通常有限复 $C^*$ 张量表示；每个至少参与一条实际延伸的局部对象都是有限复 $C^*$ 自伴场。共享实际对象的连通延伸网络具有同一个正标尺。若相同有限输入的所有括号方向均被供应，则在通常实张量结合识别下，它们的实际比较与变化一致；无需另加通道重分组公理。

证明。对任一实际二元边，定义 25.1 给其活动提升，定理 23.1 直接确定该边。任一参与对象也由定理 21.2 得到局部表示。局部内部比值 (21.6) 不依赖伙伴，因此同一对象各边的标尺相同，再沿连通网络传播。

对已经确定的每条边，复乘法都是 $m_X\otimes m_Y$。有限复代数张量乘法的标准结合识别给全部括号的同一乘法；其自伴实部和按同一 $\sqrt\lambda$ 归一的虚部遂分别给同一实际 $M,T$。张量翻转给交换两方的相应识别。这是已知代数张量结构在本候选下的结果，而不是用形式系数结合性替代实际比较的结合表示。∎

## 26. 从这个候选接续完整有限量子理论

**定理 26.1（状态、概率、过程与连续运动的明确推导范围）。** 对定义 25.1 的关系体，在实际延伸和所需有限重复副本均被供应的范围内，令每个重构代数的正锥由其 $*$ 平方定义，状态为全部正归一线性泛函，效果为 $0\le E\le1$，概率为状态评价。对过程 $\Phi:X\to Y$，要求所用内部参考 $R$ 与实际输入、输出都能组合，联合过程由同一个 $\Phi\otimes\operatorname{id}_R$ 给出。令允许过程恰为对混合线性且对所有这些参考联合保正的映射；有结果的过程保留有限标签且总和归一。则得到有限复量子理论的密度矩阵、Born 概率、张量复合及完全正仪器。连续一参数 $*$ 自同构群具有 Hamilton 形式。

其中完全正性的参考判据只需一个活动内部对象的有限张量幂，不必另行预设每个矩阵维数的裸参考对象。

证明。定理 25.2 先给实际有限复代数

$$
\mathcal A=\bigoplus_sM_{d_s}(\mathbb C),
\qquad
\mathcal A_{AB}=\mathcal A_A\otimes_{\mathbb C}\mathcal A_B.
$$

以下步骤使用有限 $C^*$ 代数、有限迹对偶及 Choi–Kraus 表示这些成熟工具，接续定理 12.1、19.1 与其所引比较曲率 V95 定理 5.2。

正归一泛函唯一表示为 $\omega(a)=\sum_s\operatorname{Tr}(\rho_sa_s)$，其中 $\rho_s\ge0$、$\sum_s\operatorname{Tr}\rho_s=1$。所以任意效果族 $\sum_jE_j=1$ 有

$$
p(j)=\sum_s\operatorname{Tr}(\rho_sE_{j,s}).
\tag{26.1}
$$

自伴元的谱分解给投影测量及其 Born 概率。单一非交换块的纯态是秩一投影，其单位向量表示为相位商；通常复 Hilbert 表示和块内叠加由此取得，不将跨超选择中心块的相对相位当作额外可观测量。

现在取一个活动内部参考 $R$。它的重构代数有某个矩阵块 $M_r(\mathbb C)$，$r\ge2$。其 $k$ 次实际复合包含块 $M_{r^k}(\mathbb C)$。对给定有限输入代数选 $r^k\ge\max_sd_s$。过程与此实际参考联合保正，限制到这个参考块、再压缩到每个 $d_s$ 维角，便给每个输入矩阵块所需的 Choi 正性。因此过程完全正；反向完全正立即保证它在全部这些实际参考上保正。这个论证只用已有实际张量表示和有限矩阵角，不要求全部参考维数都作为独立活动对象出现。

状态过程于是有逐块 Kraus 形式。有标签的各分支均完全正，总和保迹，故为量子仪器；其效果给 (26.1)，而其条件后继由同一分支作用确定。连续一参数 $*$ 自同构不能连续置换有限中心块，每个矩阵块内的导子是内导子，故

$$
\dot a=\frac{i}{2\sqrt\lambda}[h,a],
\qquad \dot\rho=-\frac{i}{2\sqrt\lambda}[h,\rho].
\tag{26.2}
$$

加入能量与物理时间单位的标定后，这是通常 Heisenberg 与 Schrödinger 形式。自同构群的实际存在及所选 $h$ 仍是运动数据，不由比较合同选定。∎

**命题 26.2（没有被定义约束偷渡的物理选择）。** C99 不固定中心扇区数、全部系统的具体维数、实际 Hamiltonian、绝对时钟单位，或同一测量概率对应的唯一条件后继。将全部数学状态和效果解释为可取得的实际操作，仍需完整操作供应。

证明。有限矩阵直和的不同中心、块维数和正迹权均满足本候选，且都可作标准活动延伸，所以这些选择不唯一。共同重标 $D\mapsto tD$、$\Gamma\mapsto t\Gamma$、$\lambda\mapsto\lambda/t^2$ 保持实际比较和候选，故不选定绝对时钟。不同非中心 $h$ 给不同生成元，中心偏置又不改变交换子。

对同一效果族 $E_j$，$\rho\mapsto\sqrt{E_j}\rho\sqrt{E_j}$ 与 $\rho\mapsto\operatorname{Tr}(\rho E_j)\sigma_j$ 都是完全正分支，$\sigma_j$ 可取任意固定归一态。它们有相同结果概率，条件后继一般不同。因此候选和 Born 概率不唯一推出 Lüders 更新。限制状态、效果或控制菜单也不改变上述比较与变化恒等式；完整菜单必须作为操作解释的明确供应，而不是藏在代数表示结论里。∎

**定义 26.3（文献对应与本候选的数学边界）。** 两个局部模身份 (20.1) 的成熟先例正是 [Barnum–Wilce，*Local tomography and the Jordan structure of quantum theory*，arXiv:1202.4513v2，引言 Hanche-Olsen 定理的式 (1)](https://arxiv.org/html/1202.4513v2)。该定理原本假设局部为 JB／Euclidean Jordan 代数，并假设其与量子比特的张量空间已经带 Jordan 乘法。其 Proposition 1 另外使用可因子化的齐次自对偶概率理论、局部层析复合及一个量子比特。这里不从这些尚未给出的前件循环取得 Jordan 性。

动力对应与复结合表示的中间工具沿用定理 21.2 所引仓内结果及 [Niestegge，§5](https://arxiv.org/html/1402.0158v2)；一般复合理论的背景见 [Kapustin，arXiv:1303.6917v4，Theorem 3.1](https://arxiv.org/html/1303.6917v4) 和定义 19.3 的 Grgin–Petersen 文献。Kapustin 的对象一开始已有 Lie 代数及单体关联结构；这里的交替、Jacobi 与实际联合模板不作为这样的输入。

C99 在当前有限正 Frobenius 合同下的仓内综合推导是：保值条件作用强迫局部自守和共同曲率比例；两方实际比较的全部剩余恰为中心关联空间上的对称三次型；一次实际活动提升消掉这块自由，从而认证原二元量子张量关系。既有 Jordan 模身份、成熟表示工具与有限完全正判据均不主张为新发现；上述综合也不据限定文献核对主张原创优先权。有限维、正性、张量载体、局部活动、条件作用和逐边可再延伸都是明列前件；无限维极限、空间时空结构、特定物理动力学和经验实现不属于这些定理的结论。

## 追加锚（本行以下为增补区）

## 27. 任意实际正比较下的同一整体延伸

**定义 27.1（不指定乘积内积的实际合同）。** 局部对象取定义 8.1：有限非零实空间上的交换含幺正 Frobenius 比较场 $(J,S,g,1,D)$，其中 $D:J\to\operatorname{Der}(S)$ 实线性且非零。仍不预设 Jordan、自守、交替、Jacobi、$D_1=0$ 或复结构。对两个局部对象，实际整体为

$$
(J_A\otimes_{\mathbb R}J_B,M,\Gamma,G,1_A\otimes1_B),
$$

其中 $M$ 交换含幺，$G$ 是任意给定的正定对称双线性型，$M$ 对 $G$ 为 Frobenius；$\Gamma$ 对标签实线性并满足完整导子律 (20.3)。保留全部局部模块身份 (20.1) 和保值条件作用 (20.2)，对所有输入量化。这里没有 $G=g_A\otimes g_B$ 的要求。

同一实际整体作为下一层局部对象时，必须保留这个已经给定的 $M,\Gamma,G$。外层也仅要求某个实际正 Frobenius 内积，不要求它因子化。

**定义 27.2（候选 C100：任意正比较的实际整体可再活动延伸）。** 对一个定义 27.1 的给定实际 $AB$，要求同一关系体内存在活动对象 $C$，使原来的同一实际整体与 $C$ 再满足定义 27.1：

$$
\boxed{(AB,M,\Gamma,G)\ \text{具有保留其全部数据的实际活动延伸 }(AB)C.}
\tag{C100}
$$

它只要求一个括号方向的三方有限提升；第三方是一个系统，不是实维数等于三的空间。对整个关系体使用 C100，指每条实际二元边都满足它。两两可组合、有限重复副本和操作供应另按定理 26.1 明列，不包含在一次延伸的存在量词中。

**定理 27.3（局部重构主链不依赖联合内积因子化）。** 定义 27.1 的全部实际整体仍有唯一变化模板

$$
\Gamma_{a\otimes b}=D_a\otimes L_b+L_a\otimes D_b,
\tag{27.1}
$$

双方均自守、交替、满足 Jacobi 和 $D_1=0$，存在唯一共同 $\lambda>0$ 使

$$
[L_a,L_c]=-\lambda D_{B(a,c)},
\qquad m=S-i\sqrt\lambda B.
\tag{27.2}
$$

每个局部都是有限复 $C^*$ 代数的自伴部分，至少有一个非交换矩阵块。这里只推广定理 21.1–21.2 的适用前件，不把其已有表示桥重新认领为新表示定理。

证明。不能直接套用带乘积内积前件的旧陈述；核对其证明的实际依赖即可得到所需推广。首先，模块身份给

$$
c\otimes d=M(c\otimes1,1\otimes d).
$$

对它应用实际导子律和条件作用，得到 (27.1)，未使用任何联合内积。与两类局部左乘取交换子，仍逐项得到 (21.2)。令 $z=D_aa$，其第一式给 $F(z\otimes b,Y)=0$，第二式及交换性给

$$
D_cz\otimes K_{fg}b=0
\quad\text{对所有 }c,f,g,b,
\qquad K_{fg}=[L_f,L_g].
$$

活动伙伴不可能全部 $K_{fg}=0$：否则其正含幺交换比较结合，是有限实直积，导子全为零。故 $D_cz=0$；局部导子对自身正 Frobenius 内积斜伴随，给 $g(z,z)=-g(a,D_az)=0$。这个斜伴随事实只依赖各局部对象，复用比较曲率 V95 定理 2.1 的中心核证明，不使用 $G$。于是双方自守；极化给交替和 $D_1=0$。

再按定理 21.2，以 (21.2) 证明 $K_{ac}$ 经 $B(a,c)$ 良定义地因子化。局部 $W=\operatorname{span}B$ 上 $D$ 单射，双方的算子张量身份为

$$
\mathcal K_A(z)\otimes D^B_w
=D^A_z\otimes\mathcal K_B(w).
$$

非零简单张量的比例唯一性给一个双方共同的实比例 $\kappa$。局部正迹形式 $q(a,c)=\operatorname{Tr}(L_aL_c)$ 及定理 11.1 的

$$
\operatorname{Tr}(K_{ac}D_z)=q(z,z)>0
\quad(z=B(a,c)\ne0)
$$

给 $\kappa<0$，故 $\lambda=-\kappa>0$。其余 Jacobi、结合乘法和忠实正表示，沿定理 21.2 所用定理 9.1、12.1 的同一局部推导接续。上述每一步只用局部正内积与实际代数身份，因此适用于任意实际 $G$。∎

## 28. 实际联合内积的全部自由只在中心权重

记重构后的局部自伴中心为 $Z_A,Z_B$，最小中心幂等为 $e_i,f_j$，块投影为 $P_i=L_{e_i},Q_j=L_{f_j}$。令 $r_A=\dim Z_A,r_B=\dim Z_B$。以下使用 $g_0=g_A\otimes g_B$ 作为表示其他内积的辅助基准，不将它替换为实际 $G$。

**定理 28.1（正比较的完整中心权分类）。** 定义 27.1 下存在唯一逐项严格正的数组 $h_{ij}$，使

$$
\boxed{G(X,Y)=\sum_{i,j}h_{ij}\,
 g_0((P_i\otimes Q_j)X,(P_i\otimes Q_j)Y),
 \qquad h_{ij}>0.}
\tag{28.1}
$$

这里要求条目正，不要求把 $h$ 当作普通方阵时正半定。对标准实际量子比较与变化，每个这样的数组都确实给一个合法正 Frobenius 内积。

证明。存在唯一 $g_0$ 自伴正定算子 $H$，满足 $G(X,Y)=g_0(HX,Y)$。模块身份使 $L_a\otimes I,I\otimes L_b$ 都是实际联合左乘，故对 $G$ 自伴；局部 Frobenius 性又使它们对 $g_0$ 自伴。因此 $H$ 与两类算子全部对易。

为确定整个交换子空间，若局部算子 $T$ 与全部 $L_a$ 对易，则

$$
Ta=TL_a1=L_aT1=L_{T1}a.
$$

所以 $T=L_z$，$z=T1$，且 $[L_z,L_a]=0$。由 (27.2)，$D_{B(z,a)}=0$；而 $B(z,a)\in W$，$D|_W$ 单射，故 $B(z,a)=0$。因此 $z\in Z$。反向中心左乘显然对易，所以局部交换子空间恰为 $\operatorname{span}\{P_i\}$。这也排除了同构矩阵块之间的混合，因为各中心投影本身就在左乘族中。

在有限算子张量空间中，按第二个 End 空间的任意基展开 $H$，第一类对易条件使它成为 $\sum_iP_i\otimes R_i$；再用第二类条件，得到

$$
H=\sum_{i,j}h_{ij}P_i\otimes Q_j.
$$

各块投影非零且正交，故 $H$ 正定恰等价于全部 $h_{ij}>0$，得到 (28.1)。这是成熟有限交换子空间工具在实际模块身份上的应用。

反向，标准量子比较逐联合中心块作用，对 $g_0$ 为 Frobenius，其左乘因而与 $H$ 对易，对 $G$ 也为 Frobenius。标准变化逐块作用、对 $g_0$ 斜伴且消去中心，所以对 $G$ 也斜伴。模块、条件作用和导子律均不含权重，全部保持。∎

**命题 28.2（权重由同一比较内部读出）。** 记

$$
a_i=g_A(e_i,e_i)>0,
\quad b_j=g_B(f_j,f_j)>0,
\quad u_{ij}=e_i\otimes f_j,
\quad \mu_{ij}=h_{ij}a_ib_j.
$$

则

$$
\boxed{\mu_{ij}=G(u_{ij},u_{ij})
=G(e_i\otimes1,1\otimes f_j).}
\tag{28.2}
$$

证明。不同联合中心块对 $G$ 正交，且 $e_i\otimes1=\sum_ju_{ij}$、$1\otimes f_j=\sum_iu_{ij}$。展开即得。∎

所以 $h$ 不是为证明另设的一组联合系数，而是实际 $G$ 相对于已给局部比较的内部读数。矩阵块内部的度量被锁定，剩下的是不同共同固定扇区的比较权。

## 29. 中心关系表、四角循环与精确三次型盲核

令

$$
\begin{aligned}
K&=Z_A\otimes Z_B,\\
E&=Z_A\otimes1+1\otimes Z_B,\\
V_G&=K\cap E^{\perp_G},\\
U&=Z_A^{\perp_{g_A}}\otimes J_B
       +J_A\otimes Z_B^{\perp_{g_B}}.
\end{aligned}\tag{29.1}
$$

**定理 29.1（加权中心关联的全部静态自由）。** 取定理 27.3 的共同标尺，置 $M_{\rm q}=S_A\otimes S_B-\lambda B_A\otimes B_B$。固定一个 (28.1) 的实际 $G$ 后，定义 27.1 的所有实际比较恰为

$$
\boxed{M(X,Y)=M_{\rm q}(X,Y)
+F(P^G_{V_G}X,P^G_{V_G}Y),}
\tag{29.2}
$$

其中 $F:V_G\times V_G\to V_G$ 的 $G$ 配对为任意全对称三线性型。自由空间为 $\operatorname{Sym}^3(V_G^*)$，且

$$
\dim V_G=k=(r_A-1)(r_B-1),
\qquad \dim\operatorname{Sym}^3(V_G^*)=\frac{k(k+1)(k+2)}6.
\tag{29.3}
$$

一般 $V_G$ 不等于指定局部内积下的 $Z_A^0\otimes Z_B^0$。

证明。定理 28.1 的 $H$ 保持 $U,K$，所以 $U^{\perp_G}=K$。$M_{\rm q}$ 对 $G$ 也为 Frobenius。(21.2) 与共同曲率律仍给 $M-M_{\rm q}$ 在第一个输入属于 $U$ 时为零；模块身份又使它在 $E$ 上为零。差值的 $G$ 配对是全对称三线性型，因此全部三槽都只能支持在 $(U+E)^{\perp_G}=V_G$。有限 Riesz 对应给 (29.2)。

反向任取这样的三次型，补项遇局部输入为零，保持单位、模块和 Frobenius 性。标准 $\Gamma_H$ 消去 $K$，且对 $G$ 斜伴，故其像在 $K^{\perp_G}$。于是补项导子律的输出项和两个输入项分别为零；标准部分满足完整导子律，条件作用也不改变。正定 $G$ 本身未被改动。因此每个正数组与每个这样的三次型都实际可达。

最后 $\dim E=r_A+r_B-1$，因为其两部分仅交于单位直线；正定性给 $\dim V_G=\dim K-\dim E$，得到 (29.3)。∎

**命题 29.2（加权关联空间是完全二部图的循环空间）。** 中心元 $v=\sum_{ij}v_{ij}u_{ij}$ 属于 $V_G$ 当且仅当

$$
\sum_j\mu_{ij}v_{ij}=0\quad\text{对每个 }i,
\qquad
\sum_i\mu_{ij}v_{ij}=0\quad\text{对每个 }j.
\tag{29.4}
$$

映射 $v\mapsto f$，$f_{ij}=\mu_{ij}v_{ij}$，将它同构到完全二部图 $K_{r_A,r_B}$ 的零散度流空间，且

$$
\|v\|_G^2=\sum_{ij}\frac{f_{ij}^2}{\mu_{ij}}.
\tag{29.5}
$$

证明。$E$ 由各行、各列的单位嵌入张成，(28.2) 的正交展开恰给 (29.4)。把每条边从行顶点指向列顶点，顶点散度分别为行和及负列和，因此零散度就是同一条件，范数直接代换给 (29.5)。

固定末行 $r$、末列 $s$。对 $i<r,j<s$，在 $(i,j),(r,s)$ 放 $+1$，在 $(i,s),(r,j)$ 放 $-1$，其余放零。这 $(r-1)(s-1)$ 个四角流构成基：内部各格的系数分别唯一确定，而其余边由零行列和确定。除以各边的 $\mu$ 就给 $V_G$ 的显式基。这也复现边数减顶点数加一的标准连通图循环维数。∎

这个对应不是物理空间图：它把“两个局部记录各自不变，联合关系仍可改变”精确表示成四角之间的平衡搬运。若 $r_A=r_B=2$，一条非零方向就是

$$
v=\left(\frac1{\mu_{11}},-\frac1{\mu_{12}},
         -\frac1{\mu_{21}},\frac1{\mu_{22}}\right).
\tag{29.6}
$$

指定的旧零均值符号张量一般不再满足这些加权零边缘条件。四角方向的系数矩阵秩一恰等价于该四角的 $\mu$ 二阶子式为零；所有四角均如此恰等价于整个正权表秩一。

**命题 29.3（任意正相关权下仍有显式非 Jordan 二方模型）。** 两方均取 $(M_2(\mathbb C)\oplus M_2(\mathbb C))_{\rm sa}$，局部运算为共同 $\lambda=1$ 的标准量子关系，$G$ 可取任意严格正的中心权。将 (29.6) 归一为 $q\in V_G$。对任意 $t\ne0$，令

$$
M_t(X,Y)=M_{\rm q}(X,Y)
+tG(q,X)G(q,Y)q.
\tag{29.7}
$$

则全部二方合同保持，而同一实际 $M_t$ 非 Jordan。

证明。合同由定理 29.1 的反向得到。令 $e=e_1\otimes1$，$P=\mathbb L_e=P_1\otimes I$，$x=Pq,y=(I-P)q$。$q$ 在两个行块都非零，故

$$
\theta=G(q,Pq)=\|Pq\|_G^2\in(0,1).
$$

模块身份给 $e^2=e$、$M_t(e,x)=x$。标准中心乘法使 $M_{\rm q}(x,y)=0$，因此

$$
[P,\mathbb L_x]y=t\theta(1-\theta)Pq\ne0.
\tag{29.8}
$$

而 Jordan 恒等式在幂等 $e$ 处的一次线性化 (23.3)，代入 $M_t(e,x)=x$，会要求 $[P,\mathbb L_x]=0$，矛盾。这是符号反例，不依赖数值检验；正权相关性不会自动修复乘法缺陷。∎

## 30. 活动第三方认证乘法，不强迫中心权独立

**定理 30.1（C100 的精确端点）。** 给定定义 27.1 的实际整体。若它满足 C100，则

$$
\boxed{M=M_{\rm q},\qquad
\Gamma=D_A\otimes L_B+L_A\otimes D_B,\qquad
m_{AB}=m_A\otimes_{\mathbb C}m_B.}
\tag{30.1}
$$

内外层及第三方具有同一正内部标尺。实际内积 $G$ 的全部剩余自由恰为 (28.1) 的任意严格正中心权，没有额外秩一限制。反向，每个这样的标准实际整体及任意这样的 $G$ 都存在一个四维活动数学延伸。

证明。原整体由局部条件作用仍活动。将它作为同一个局部对象与 $C$ 继用时，其局部正内积就是原来的 $G$。对这对对象应用定理 27.3，外层内积无须因子化，已经推出同一个实际 $M$ 为有限复 $C^*$ 自伴比较，特别为 Jordan。

接着复用定理 23.1 的中心幂等论证，它也是纯代数的。对 $e=e_i\otimes1$，模块身份给 $\mathbb L_e=P_i\otimes I$，其谱只有零和一，且 $e^2=e$。Jordan 一次线性化在这两个本征空间分别给

$$
(2\varepsilon-1)[\mathbb L_e,\mathbb L_x]=0,
\qquad \varepsilon\in\{0,1\}.
$$

故 $\mathbb L_e$ 与全部实际左乘对易；列幂等同理。交换性再给

$$
\mathbb L_{e_i\otimes f_j}
=\mathbb L_{e_i\otimes1}\mathbb L_{1\otimes f_j}
=P_i\otimes Q_j.
$$

这与 $M_{\rm q}$ 在全部中心标签上一致，其他标签的一致性已由定理 29.1 给出，所以全部三次型为零。变化由 (27.1) 固定。外层曲率律限制到 $a\otimes1,c\otimes1$ 后，与内层只差正系数；活动性使某个 $D_{B(a,c)}\ne0$，因此内外标尺相同，得到 (30.1)。

反向，取同标尺量子比特 $C=\operatorname{Herm}_2(\mathbb C)$，用标准量子复合以及外层内积 $G\otimes g_C$，给一个合法活动延伸。这是存在见证；合同本身没有要求每个外层内积取这种形式。$G$ 的任意正权均保留，故 C100 不能强迫它们独立。第三方的实维数至少四，由定理 27.3 的活动非交换块界给出，上述构造达到它。∎

**推论 30.2（关系体的逐边理论及终层边界）。** 对全部实际二元边要求 C100 时，参与延伸的局部对象及每条实际整体都有有限复量子表示，共享对象的连通网络有共同 $\lambda$；所供应有限括号的实际比较和变化在标准张量识别下相同。只给一次活动延伸仍仅认证原内层，不能越级认证最外层；把第三方换成静态实标量也没有认证力。

证明。逐边应用定理 30.1，沿共享对象的内部比值传播标尺；结合性由标准复张量乘法得到。命题 29.3 的模型与 $\mathbb R$ 作标量延伸保留其全部缺陷。要展示活动最外层仍可有缺陷，先取标准 $AB$，再对 $(AB,C)$ 的非零中心关联空间施加定理 29.1 的非零三次型；其内层保持标准，而外层由同样中心幂等论证非 Jordan。∎

## 31. 独立性、局部等距和三方重分组是不同约束

**命题 31.1（实际因子化的准确判据）。** 相对于给定局部比较，$G=g_A\otimes g_B$ 当且仅当全部 $h_{ij}=1$，相差一个共同正倍数当且仅当全部 $h_{ij}$ 是同一常数。允许任意局部正内积重新加权后，$G$ 可因子化当且仅当 $h$ 秩一，亦即全部交叉比满足

$$
\frac{h_{ij}h_{i'j'}}{h_{ij'}h_{i'j}}=1.
\tag{31.1}
$$

若归一化 $g_A(1,1)=g_B(1,1)=1$，两个局部单位嵌入都对实际 $G$ 等距，当且仅当

$$
\sum_jh_{ij}b_j=1\quad\text{对所有 }i,
\qquad \sum_ih_{ij}a_i=1\quad\text{对所有 }j.
\tag{31.2}
$$

这些边缘条件不推出秩一。

证明。前三个等价直接由 (28.1) 的非零正交块分解与正数组秩一判据得到。若某个分解 $G=\widehat g_A\otimes\widehat g_B$ 起初未要求局部 Frobenius，局部左乘对它自伴已使每个 $\widehat g_i$ 为 Frobenius；定理 28.1 的单体交换子空间证明再使它们为各自正中心重权，因而仍只有 $h_{ij}=u_iv_j$ 的可能。

对任意局部 $x,y$ 展开 $G(x\otimes1,y\otimes1)$，每个第 $i$ 块得到系数 $\sum_jh_{ij}b_j$。等距恰给第一组条件，另一方同理。下述反例说明它们未强迫独立。∎

若某方中心一维，正权表没有真正的两方秩相关，但仍可不同于原指定乘积。双方中心均一维时，只剩一个整体正倍数。也不能把 $h$ 的普通矩阵正半定性误当 $G$ 的正定性。

**命题 31.2（保持所有局部比较却非因子化的精确量子整体）。** 两方均取 $\mathcal A=M_2(\mathbb C)\oplus M_2(\mathbb C)$，局部比较为

$$
g((x_+,x_-),(y_+,y_-))
=\frac{\operatorname{Tr}(x_+y_+)+\operatorname{Tr}(x_-y_-)}4.
$$

则 $a_+=a_-=b_+=b_-=1/2$。给定 $0<|\epsilon|<1$，令

$$
h=\begin{pmatrix}1+\epsilon&1-\epsilon\\
                  1-\epsilon&1+\epsilon\end{pmatrix}.
\tag{31.3}
$$

使用标准实际量子比较和变化，则全部 C100 条件及两个局部嵌入等距均成立，但实际 $G$ 不等于任何两个局部正内积的乘积。

证明。条目严格正，行列条件 (31.2) 成立；定理 28.1、30.1 的反向给全部合同及活动延伸。$\det h=4\epsilon\ne0$，由命题 31.1 它不能因子化。负 $\epsilon$ 同样可用，此时普通方阵 $h$ 有负特征值，但实际 $G$ 仍严格正定。代数、正锥及全部标准量子运算均保持。∎

**命题 31.3（三方等距重分组的精确条件）。** 假设各实际边均已由 C100 认证。记内层相对权为 $h^{AB}_{ij}$，外层相对于实际 $G_{AB}\otimes g_C$ 的权为 $h^{(AB)C}_{(ij),k}$，另一括号同理。标准结合识别保持两个实际三方内积，当且仅当

$$
\boxed{h^{AB}_{ij}h^{(AB)C}_{(ij),k}
=h^{BC}_{jk}h^{A(BC)}_{i,(jk)}\quad\text{对所有 }i,j,k.}
\tag{31.4}
$$

证明。相对于三个单体内积的乘积，各中心格上的总权分别为等式左右两端。非零正交块上的权相等恰等价于内积相等。∎

实际乘法的重分组由定理 30.1 自动成立；若连同指定比较内积也要求等距，才需 (31.4)。不能从代数结合性直接冒领实际等距性。对没有额外对象识别的有限有序词族，任选逐项正的总权 $\rho_U$，单体权取一，令

$$
h_{U,V}(u,v)=\frac{\rho_{UV}(u,v)}{\rho_U(u)\rho_V(v)}.
\tag{31.5}
$$

总权比值自动满足 (31.4)。反向，若全部括号的总权一致，便可用该总权定义 $\rho_U$ 得到 (31.5)。这里不声称任意带额外对象识别或环路的对象图上，每个抽象 cocycle 都是这种 coboundary。

**命题 31.4（全部有限重分组与局部等距仍容许相关中心权）。** 取命题 31.2 的相同单体，以 $s=\pm1$ 标中心块。固定 $0<\delta<1$，对 $n$ 个副本的标准量子张量代数，在相对于单体乘积比较的中心格上给总权

$$
\rho_n(s_1,\ldots,s_n)
=\frac12\left[\prod_{p=1}^n(1+\delta s_p)
              +\prod_{p=1}^n(1-\delta s_p)\right].
\tag{31.6}
$$

这个实际有限对象族满足 C100；全部比较正定归一，任意有限局部单位嵌入、重分组和排列识别均等距，但二方实际内积非因子化。

证明。两个乘积均严格正，所以每个总权严格正。$\rho_1=1$，且任意一项均匀平均给

$$
\frac12\sum_{s_n=\pm1}\rho_n(s_1,\ldots,s_n)
=\rho_{n-1}(s_1,\ldots,s_{n-1}).
\tag{31.7}
$$

反复平均给归一及任意边缘一致性。对任意局部算子 $X,Y$，单位嵌入后的配对就是在新增中心符号上求这些平均；新增矩阵块的归一迹在单位上为一，所以嵌入等距。使用 (31.5) 定义每条连接边的相对权，所有括号的总权均为同一 $\rho_n$；它对符号置换对称，故结合与排列识别均等距。标准实际量子运算满足全部合同，每个整体可再与一个活动单体延伸。

然而 $\rho_2(s,t)=1+\delta^2st$，其正权表行列式为 $4\delta^2>0$，由命题 31.1 非因子化。这是各有限阶段的显式构造，不需要无限概率极限。$\delta=0$ 回到乘积；$\delta=1$ 时混合符号格权为零，$n\ge2$ 的内积退化，已不属于严格正合同，也不能再用于 (29.6)、(31.5) 的除法。∎

## 32. 从中心比较自由接回完整有限量子理论

**定理 32.1（量子公理的接续与内积坐标）。** 对逐边满足 C100 的关系体，在所需有限复合与定理 26.1 明列的状态、效果、混合线性过程、内部参考及有标签仪器供应下，仍得到密度矩阵、Born 评价、标准量子张量积、完全正过程与仪器；连续一参数 $*$ 自同构仍具有 Hamilton 形式。任意允许的实际中心权不改变这些结论。

证明。定理 30.1 先给每条实际边的复 $C^*$ 张量乘法。正锥由 $*$ 平方确定，与中心比较权无关。对 $\mathcal A=\bigoplus_sM_{d_s}(\mathbb C)$，所有正归一泛函仍唯一为

$$
\omega(a)=\sum_s\operatorname{Tr}(\rho_sa_s),
\qquad \rho_s\ge0,\quad\sum_s\operatorname{Tr}\rho_s=1.
$$

效果 $0\le E\le1$ 的概率仍为 $\omega(E)$；谱投影和块内秩一纯态给通常 Hilbert 与 Born 表示。若把同一泛函写成实际内积坐标 $\omega(a)=g(r,a)$，而该内积在块 $s$ 是 $w_s\operatorname{Tr}(ab)$，则 $r_s=\rho_s/w_s$；改变权重改变密度坐标，不改变状态泛函和概率。

完全正性的参考判据仅依赖已经重构的代数张量正锥。一个活动内部参考有 $M_r(\mathbb C)$ 块，$r\ge2$；其有限张量幂包含任意所需大小的矩阵角。与这些实际参考联合保正遂给逐输入块的 Choi 正性，得到完全正及 Kraus 仪器；反向完全正保证所有参考上的联合保正。这里逐项使用定理 26.1 的同一过程和实际参考供应，不从单纯内积的分类推出完整操作菜单。

连续一参数自同构固定有限中心，块内生成元是内导子，所以仍为 (26.2) 的 Heisenberg／Schrödinger 形式。Hamiltonian、实际时钟标定与测量后继的选择保持为明确运动或操作数据。

若还要由内部关系选出一个共同态，可直接接续[有限内部约束 V97，定义 2.1、定理 4.1](https://github.com/the-omega-institute/trureturing/blob/f39cb044ab85fe5d0f02ef742b276fa9b84bede7/docs/develop/theory/AURIC_FINITE_INTERNAL_CONSTRAINTS_UNIQUE_WHOLE_SOURCE_AND_STABLE_QUANTUM_READOUT_V97.md)。参数对应是：其含幺复正代数取这里已重构的同一 $\mathcal A$，正关系取 $q_j\in\mathcal A_+$，效果取同一代数中的 $0\le B\le1$。若每份有限正零关系有解，且每个效果、每个精度都有该文 C97 的有限正序夹逼证书，则其定理 4.1 直接给唯一共同纯态。C100 提供的是此结论所需的量子代数输入；证书条件仍是独立的态选择供应，不能由正比较权或活动延伸冒领。以下对比较基准的构造不替代这一步。

为区分“存在可因子化基准”与“实际比较必须因子化”，在上述推导中可采用成熟的有限正则迹工具：仅由已重构的比较乘法定义

$$
\tau_{\rm can}(a)
=\frac{\operatorname{Tr}_{\mathbb R}(L_a)}{\dim_{\mathbb R}J}
=\frac{\sum_sd_s\operatorname{Tr}(a_s)}{\sum_sd_s^2},
\qquad g_{\rm can}(a,b)=\tau_{\rm can}(S(a,b)).
\tag{32.1}
$$

它是正 Frobenius、自对偶的归一比较，且对实际标准复张量结构满足

$$
g_{{\rm can},AB}=g_{{\rm can},A}\otimes g_{{\rm can},B}.
\tag{32.2}
$$

这个正则迹选择不要求既定实际 $G$ 等于它。在 $M_d(\mathbb C)_{\rm sa}$ 上，对角化 $a$ 可直接计算 $\operatorname{Tr}_{\mathbb R}L_a=d\operatorname{Tr}a$：对角坐标贡献 $\sum_pa_p$，每对非对角实坐标贡献 $a_p+a_q$，总计每个 $a_p$ 出现 $d$ 次。故 (32.1) 为严格正逐块迹权，得到正定、Frobenius、自对偶与归一。张量块维数为 $d_se_t$，总实维数为 $(\sum_sd_s^2)(\sum_te_t^2)$；迹与维数都相乘，得到 (32.2)。该构造复用有限正则迹工具，未给实际 $G$ 加任何新等式。∎

**定义 32.2（物理选择、文献量词与结论范围）。** 实际 $G$ 的归一单位配对 $G(1,-)/G(1,1)$ 若另被选为一个实际态，就给一个可带中心关联的迹态；该态选择不是全部物理状态的来源，也不是定义 27.1 自动指定的宇宙态。任意中心权、态菜单和实际动力仍须在其各自供应范围内解释。

模块身份的成熟先例仍是 [Barnum–Wilce，arXiv:1202.4513v2，引言 Hanche-Olsen 定理式 (1)](https://arxiv.org/html/1202.4513v2)。其 §3.2 明确区分一个指定自对偶内积因子化，与复合系统存在某个可选择的因子化自对偶内积；Proposition 1 使用后者及 HSD、两两局部层析复合和量子比特。命题 31.2、31.4 只证明指定实际 $G$ 可以非因子化；同一量子代数仍有 $g_0$ 或式 (32.1)–(32.2) 的因子化自对偶基准，故这些例子不反驳其存在性前件，也不证明该定理在原起点中可以直接删除因子化。

动力对应、有限复表示和复合历史沿用定义 26.3 的 Niestegge、Kapustin 与 Grgin–Petersen 来源。正形式的算子表示、有限交换子空间、正数组秩一判据、Jordan 幂等线性化、图循环空间、正则迹和 Choi–Kraus 工具均是成熟结果。当前合同下的仓内综合推导是：指定联合内积不必因子化，其全部自由为正中心权；两方的精确盲核是加权中心循环空间上的对称三次型；一次同一实际整体的活动提升恰消去乘法盲核，而不能消去中心比较相关性。限定文献核对不建立原创优先权。

有限维、正 Frobenius 比较、实张量载体、局部活动、保值条件作用和逐边可再活动延伸仍是明确前件。全部身份可在所给有限对象的完整基上检查，正定性是有限 Gram 条件。无限维极限、空间时空起源、特定 Hamiltonian 和完整操作供应的物理实现仍在这些定理之外。

白话说：把两个东西放在一起，不能先把另一方的取值抹成平均数；它怎样参与比较、怎样带动变化，都要留在同一张关系表里。这张表可以给不同的共同固定情形不同权重，甚至让两边的权重相关。只看两边，四个角之间还可以藏一种搬来搬去、两边各自账目都不变的乘法改动；再把这个原封不动的整体接到一个会变化的第三方上，并要求沿用同一套比较和变化关系，这种改动就被排除了。在明列的有限正比较前提下，留下的是通常复量子的乘法；权重相关仍可保留，而不是另写一条“必须独立”的命令。再按正文供应完整状态、效果和参考，并要求混合线性过程与参考联合保正、总过程归一，便得到 Born 概率与完全正仪器；另给连续一参数的乘法与伴随自同构群，才有 Hamilton 形式。

## 追加锚（本行以下为增补区）

## 33. 允许静态对象的活动伙伴候选

**定义 33.1（允许零指派的比较对象与实际边）。** 对象是有限非零实空间上的交换含幺正 Frobenius 比较场 $(J,S,g,1,D)$，但将定义 27.1 的局部活动前件放宽为

$$
D:J\longrightarrow\operatorname{Der}(S)\quad\text{实线性，允许 }D=0.
$$

称 $D\ne0$ 的对象为活动对象，$D=0$ 的对象为静态对象。这里的静态指所有标签生成元都为零，不是只把某个选定 Hamiltonian 取为零，也不是禁止随机过程或记录写入。

实际边 $A,B\to AB$ 仍具有实张量载体、交换含幺比较 $M$、任意给定正 Frobenius 内积 $G$ 和实线性导子指派 $\Gamma$，满足全部模块身份 (20.1)、保值条件作用 (20.2) 和实际导子律 (20.3)。原实际输出作为对象继用时保留同一个 $M,\Gamma,G$。局部与整体均不预设 Jordan、自守、交替、Jacobi 或复结构。

**定义 33.2（候选 C101：每个实际对象都有内部活动伙伴）。** 设 $\Omega$ 是非空对象族及其指定实际边，所有边均满足定义 33.1，实际输出仍属于 $\Omega$。唯一的伙伴要求是

$$
\boxed{\forall X\in\Omega\quad\exists R_X\in\Omega:
D_{R_X}\ne0\ \text{且同一实际 }X\text{ 有边 }X,R_X\to XR_X.}
\tag{C101}
$$

伙伴可以随 $X$ 改变，不预先指定一个共同量子比特，也不要求每两对象均可组合。量词包括每个已给实际整体；不能只对原始单体要求伙伴，再把新输出排除在条件之外。

**定理 33.3（无活动前件的变化模板与局部二分）。** 任意定义 33.1 的实际边都有

$$
\boxed{\Gamma_{a\otimes b}=D^A_a\otimes L^B_b
                         +L^A_a\otimes D^B_b,}
\tag{33.1}
$$

且

$$
\Gamma\ne0\quad\Longleftrightarrow\quad D_A\ne0\ \text{或 }D_B\ne0.
\tag{33.2}
$$

在 C101 下，每个静态对象恰为一个有限经典比较场 $\mathbb R^r$，其复化为 $\mathbb C^r$；每个活动对象为有限复 $C^*$ 代数的自伴部分，具有唯一正内部标尺 $\lambda_X$，且

$$
[L_a,L_c]=-\lambda_XD_{B(a,c)},
\qquad m_X=S_X-i\sqrt{\lambda_X}B_X.
\tag{33.3}
$$

活动对象至少有一个非交换矩阵块，静态对象没有可由这些恒等式识别的内在 $\lambda$。

证明。由模块身份 $c\otimes d=M(c\otimes1,1\otimes d)$，对其应用完整导子律和保值条件作用，直接得到 (33.1)；定理 27.3 的这一步不使用任何活动性。若双方 $D=0$，模板给 $\Gamma=0$；反向若 $\Gamma=0$，其在两个局部单位嵌入上的条件作用分别给 $D_A=D_B=0$，得到 (33.2)。

取静态对象 $X$ 及其活动伙伴 $R$。导子与左乘的交换关系给

$$
\begin{aligned}
0&=\mathbb L_{\Gamma_{a\otimes b}(c\otimes1)}\\
 &=[L_a\otimes D_b,L_c\otimes I]
 =[L_a,L_c]\otimes D_b.
\end{aligned}\tag{33.4}
$$

固定一个非零 $D_b$，得到全部 $[L_a,L_c]=0$。交换性遂给

$$
S(S(a,c),d)=L_dL_ac=L_aL_dc=S(a,S(c,d)),
$$

所以 $S$ 结合。局部左乘是相互对易的实自伴算子，且 $L_a1=a$ 使正则作用忠实；复用定理 9.1 的有限正交换结合分类，得到 $J\cong\mathbb R^r$，其内积为严格正的逐坐标权。这个成熟分类只是 (33.4) 的后继工具。

若 $X$ 活动，其伙伴也活动，定理 27.3 的全部前件对这对局部输入成立，直接给 (33.3) 及有限复表示，不要求它们的实际联合内积因子化。反向，有限复矩阵直和的标准指派 $D_ac=i(ac-ca)/(2\sqrt\lambda)$ 恒为零，当且仅当全部矩阵块阶数均为一。所以在本候选下，零指派与经典代数完全一致。对经典对象，曲率律两边均恒零，不能从 $0/0$ 读取一个标尺。∎

## 34. 经典与量子实际复合的完整分类

**定理 34.1（C101 认证全部三类实际张量关系）。** C101 下每条实际边都是通常有限复 $C^*$ 张量关系。其三种情况为

$$
\begin{array}{c|c|c}
(D_A,D_B)&M&\Gamma\text{ 的类型}\\\hline
D_A\ne0, D_B\ne0&S_A\otimes S_B-\lambda B_A\otimes B_B&\text{活动，共同 }\lambda\\
\text{恰有一方非零}&S_A\otimes S_B&\text{活动，沿用活动方 }\lambda\\
D_A=D_B=0&S_A\otimes S_B&\text{静态，无内在 }\lambda
\end{array}\tag{34.1}
$$

变化在三种情形均由 (33.1) 给出。相应复代数分别为通常矩阵直和的张量积、经典标签下的量子块直和，以及 $\mathbb C^{r_Ar_B}$。这些是同一候选的三个端点，不另设经典乘法公理。

证明。实际输出 $AB$ 本身属于 $\Omega$，所以定理 33.3 也适用于这个同一对象。若 $\Gamma\ne0$，原实际 $M$ 为复 $C^*$ 自伴比较；若 $\Gamma=0$，原实际 $M$ 为交换结合比较。两种情形都使 $M$ 为 Jordan。

若双方活动，定理 27.3 先给两方相同的 $\lambda$，定理 30.1 的中心幂等证明再给第一行。该证明只需要实际输出为 Jordan，其所用局部正比较和全部二元身份仍在此处成立。

若 $A$ 静态，取其完整经典幂等基 $e_i$。模块身份给 $p_i=e_i\otimes1$ 的实际左乘

$$
\mathbb L_{p_i}=P_i\otimes I,
\qquad \mathbb L_{p_i}^2=\mathbb L_{p_i},
\qquad p_i^2=p_i.
$$

Jordan 一次线性化 (23.3) 在零、一本征空间分别作用，给 $\mathbb L_{p_i}$ 与全部实际左乘对易，并给 $\mathbb L_{p_ix}=\mathbb L_{p_i}\mathbb L_x$。取 $x=1\otimes b$，遂有

$$
\mathbb L_{e_i\otimes b}
=(P_i\otimes I)(I\otimes L_b)=P_i\otimes L_b.
$$

各 $e_i\otimes b$ 张成全部联合空间，故 $M=S_A\otimes S_B$。另一方静态同理，得到后两行。至少一方活动时，输出的曲率律限制到该方单位嵌入，与其非零 $D_{B(a,c)}$ 比较，证明输出标尺等于该活动方标尺；双方静态时不作这种除法。

在活动情形，按对应标尺合并实部和虚部；在经典情形直接复化。三行均得到 $m_{AB}=m_A\otimes_{\mathbb C}m_B$。∎

**定理 34.2（允许静态因子的二方盲核仍恰为加权中心三次型）。** 先取已经具有定理 33.3 局部类型的两方，但暂不要求某条待比较边的输出继续有活动伙伴。若两方均活动且该边存在，则其标尺必相同；记其标准比较为 $M_0=S_A\otimes S_B-\lambda B_A\otimes B_B$。若至少一方静态，令 $M_0=S_A\otimes S_B$。记局部自伴中心为 $Z_A,Z_B$，静态一方的中心就是全部局部空间。

任意实际边的内积仍且仅能取 (28.1) 的严格正联合中心权。对固定实际 $G$，全部实际比较仍恰为

$$
\begin{aligned}
V_G&=(Z_A\otimes Z_B)\cap
       (Z_A\otimes1+1\otimes Z_B)^{\perp_G},\\
M(X,Y)&=M_0(X,Y)+F(P^G_{V_G}X,P^G_{V_G}Y),\\
G(F(u,v),w)&\in\operatorname{Sym}^3(V_G^*).
\end{aligned}\tag{34.2}
$$

其维数与加权四角循环仍由 (29.3)–(29.6) 给出。若此实际输出有一个活动伙伴，则全部 $F=0$；严格正中心比较权则仍可相关。

证明。定理 28.1 的度量证明只用全部局部左乘的交换子空间。经典 $\mathbb R^r$ 的这个空间也是其全部中心左乘，因此允许零指派并不增加矩阵块内部的度量自由。

令 $W_i=\operatorname{span}B_i=Z_i^\perp$，静态一方两边均为零。无活动前件的模板与左乘交换关系仍给 (21.2)。当两方均活动时使用共同曲率律；当某方静态时其 $D$ 与全部曲率都为零。两种计算均使 $M-M_0$ 在 $W_A\otimes J_B+J_A\otimes W_B$ 上消失。差值的实际 $G$ 配对全对称，模块身份再消去两个局部中心单位嵌入，所以定理 29.1 的三槽正交补证明逐项适用，得到 (34.2)。

反向，任意这样的三次型保持单位、模块、Frobenius、条件作用；标准 $\Gamma$ 消去中心且对实际 $G$ 斜伴，补项在完整导子律中的三项均为零。此处包括 $\Gamma=0$ 时三项自然皆零的情形。最后，输出有活动伙伴便由定理 33.3 为 Jordan；定理 34.1 的中心幂等论证消去所有补项。∎

**命题 34.3（经典标签也能藏非量子实际乘法）。** 即使局部经典类型已经确定，未经输出活动认证的二方或三方终层仍可非 Jordan。

证明。取 $A=\mathbb R^2,D_A=0$；取 $B=(M_2(\mathbb C)\oplus M_2(\mathbb C))_{\rm sa}$ 及标准非零指派。任取严格正中心权，双方中心维数均为二，所以 $V_G$ 一维。以 (29.6) 的四角方向归一为 $q$，令

$$
M_t(X,Y)=M_0(X,Y)+tG(q,X)G(q,Y)q,
\qquad t\ne0.
\tag{34.3}
$$

定理 34.2 给全部实际二方身份。对行幂等 $e=e_1\otimes1$ 及其投影 $P$，令 $x=Pq,y=(I-P)q$、$\theta=\|Pq\|_G^2\in(0,1)$，仍逐项有

$$
[P,\mathbb L_x]y=t\theta(1-\theta)Pq\ne0.
$$

Jordan 一次线性化却要求该交换子为零，所以实际 $M_t$ 非 Jordan。$B$ 本身可取标准 $\mathbb R^2\otimes\operatorname{Herm}_2(\mathbb C)$ 的实际内层，因而这个构造也给三个原始因子的非 Jordan 终层。它不能作为满足 C101 的实际输出；单体已有伙伴不能替它履行自己的延伸条件。双方都换成 $\mathbb R^2$ 时，同一构造给 $\Gamma=0$ 的静态非结合整体，也须由它自己的活动伙伴排除。∎

## 35. 共同标尺只沿活动关系传播

**定义 35.1（活动关联图）。** 顶点取 C101 关系体中的全部活动对象。对每条实际边 $A,B\to AB$，将其中所有活动输入与活动输出两两相连。静态对象不作为这个图的顶点。由 (33.2)，至少一个输入活动时输出也活动；输入都静态时输出静态。

**定理 35.2（逐活动分量的标尺与独立重标）。** 每个活动关联图的连通分量有一个共同正标尺。只在包含静态顶点的普通组合网络中连通，不足以推出一个全局标尺。对不同活动分量分别选任意 $t_C>0$，作

$$
D_X\longmapsto t_CD_X,
\qquad \lambda_X\longmapsto\lambda_X/t_C^2
\quad(X\text{ 属于活动分量 }C),
\tag{35.1}
$$

并相应重标同一分量内实际输出的 $\Gamma$，可以保持全部实际 $S,M,g,G$ 及 C101 不变。若所有活动对象都与某一个共同活动参考有实际边，或所有对象两两可组合，则全部活动标尺相同；仍不选定绝对时钟单位。

证明。两活动输入由定理 27.3 同标尺；活动输入与其活动输出由定理 34.1 的单位嵌入曲率限制同标尺。沿定义 35.1 的边传播即可。静态对象的曲率与指派均零，没有可传递的非零比例。

对 (35.1)，任一实际边上的全部活动参与者本就在同一分量，静态参与者指派保持零；因此变化模板整体只乘该分量的同一个 $t_C$。条件作用与实际导子律均随之齐次保持，已有比较与内积不变，伙伴的非零活动性也保持。标准复乘法中的 $\sqrt\lambda D$ 在正重标下不变，所以不改变已重构复代数。不同分量可以独立选值，证明静态桥不能约束它们的相对标尺。共同活动参考把全部活动对象连到同一顶点；两两可组合也使活动图连通，分别给所述充分条件。∎

**命题 35.3（共享经典记录但具有两个不同量子标尺的完整关系体）。** 存在满足 C101、普通组合网络连通的对象族，却有两个不同活动标尺。

证明。取 $\lambda_1\ne\lambda_2>0$。共享的经典对象为

$$
C_m=\mathbb C^{2^m},\qquad m\ge0,
$$

取其自伴部分和零指派。对 $p\in\{1,2\}$，另取活动对象

$$
A_{p,m,n}=\mathbb C^{2^m}\otimes M_{2^n}(\mathbb C),
\qquad m\ge0,\ n\ge1,
$$

取其自伴部分作为对象，其指派为 $D^p_a c=i(ac-ca)/(2\sqrt{\lambda_p})$。全部内积取正归一标准迹配对，全部实际比较取标准量子比较。供应所有经典对象之间的张量边，以及经典对象与任一活动分支、同一分支内对象之间的张量边；两个不同活动分支之间不供应边。结果仍在所列族中，指派与比较由标准复乘法的实虚部分给出，所以所有实际身份成立。

每个经典对象可选 $A_{1,0,1}$ 为活动伙伴；第 $p$ 支活动对象可选 $A_{p,0,1}$，实际输出仍满足同一规则。因此 C101 对全部对象成立。共享的二值记录 $C_1$ 与两个分支均有实际边，普通网络连通；但活动关联图有两个分量，内部比例分别为 $\lambda_1,\lambda_2$。即使两个分支的抽象矩阵代数同构，其不同的实际 $D$ 数据也没有被识别为同一对象。这个模型精确排除了借经典记录连接来免费同步两个量子标尺的推断。∎

## 36. 内部参考容量与经典读写的操作接口

**定理 36.1（活动伙伴产生任意大内部矩阵块）。** 记 $d(X)$ 为重构代数最大简单矩阵块的阶数。对任一活动 $T_0$ 及任意有限 $N$，C101 供应一个长度 $N$ 的实际延伸段，使全部活动对象处于同一活动分量，且

$$
T_{j+1}=T_jR_j,
\qquad d(T_N)\ge2^Nd(T_0),
\qquad \dim_{\mathbb R}J_{T_N}\ge4^N\dim_{\mathbb R}J_{T_0}.
\tag{36.1}
$$

这里不预先供应固定参考的全部张量幂，也不要求一个无限维对象。

证明。有限递推选择每个 $T_j$ 的活动伙伴 $R_j$。它们均由定理 33.3 有至少一个非交换块，所以 $d(R_j)\ge2$、$\dim J_{R_j}\ge4$。每条实际边由定理 34.1 为标准张量，故

$$
d(T_{j+1})=d(T_j)d(R_j),
\qquad \dim J_{T_{j+1}}=\dim J_{T_j}\dim J_{R_j}.
$$

递推得 (36.1)，标尺由定理 35.2 保持。对每个有限 $N$ 分别使用有限存在量词即可，不以一个先给的无限选择序列为前件。这也说明全部对象各自有限维，与整个对象族有限是不同陈述：满足 C101 的非空关系体必含无界的有限矩阵容量。∎

**定理 36.2（经典记录与量子过程的明确接续）。** 在已供应实际复合的范围内，采用定理 26.1 的全部正归一状态、效果、混合线性过程、有标签仪器与联合参考保正条件，C101 对所供应的经典对象、量子对象及其实际复合给出相应的有限复量子操作接口。C101 允许但不强迫纯经典对象实际存在；以下经典接口均以相应经典对象和过程被供应为前件。经典到经典的归一状态过程是随机矩阵；经典制备、量子测量及带经典结果的后继分别具有

$$
\begin{aligned}
p&\longmapsto\sum_i p_i\sigma_i,
 &&\sigma_i\ge0, \operatorname{Tr}\sigma_i=1,\\
\rho&\longmapsto\bigl(\operatorname{Tr}(\rho E_i)\bigr)_i,
 &&E_i\ge0, \sum_iE_i=1,\\
\rho&\longmapsto\sum_i |i\rangle\langle i|\otimes\Phi_i(\rho),
 &&\Phi_i\text{ 完全正，}\sum_i\Phi_i\text{ 保迹}.
\end{aligned}\tag{36.2}
$$

若过程的输入或输出代数是纯经典的，局部正性已蕴含完全正性。一般活动输入、输出仍须共同参考的联合保正供应，不能由候选中各自伙伴的存在代替。

证明。定理 34.1 给有限复 $C^*$ 直和及实际张量积，所以定理 32.1 的状态、Born、谱与过程推导适用，原有操作前件不被删去。对经典状态的坐标基输入，各输出是密度元 $\sigma_i$，线性性给第一式；量子到经典过程的各分量是正泛函，有限迹对偶给正效果 $E_i$，总归一给 $\sum_iE_i=1$，得到第二式。保留结果标签时，各完全正分支的输出置于相应经典直和块，给第三式。经典到经典时第一式的每个 $\sigma_i$ 是一个概率列向量，故得到非负且每列和为一的随机矩阵。

为核对经典端点的完全正性，在效果方向，正映射 $\Phi:\mathbb C^r\to\mathcal B$ 由 $A_i=\Phi(e_i)\ge0$ 确定。任意矩阵放大中的正输入为各 $X_i\ge0$，其输出是 $\sum_iA_i\otimes X_i\ge0$。反方向 $\Psi:\mathcal A\to\mathbb C^r$ 的每个坐标是正泛函 $\omega_i$；对 $[a_{uv}]\ge0$ 及任意向量 $z$，有

$$
\sum_{uv}\overline z_u\,\omega_i(a_{uv})z_v
=\omega_i\!\left(\sum_{uv}\overline z_u a_{uv}z_v\right)\ge0.
$$

故每个放大都正。有限迹对偶将这两种情况转回 (36.2) 的状态过程，得到经典输入或输出的自动完全正性。它们是成熟有限正映射事实在此候选所重构经典对象上的应用。

一般过程的证明仍需同一个实际参考能与其输入、输出同时组合，且联合映射确为同一个 $\Phi\otimes\operatorname{id}$。所供参考含 $M_r$ 块、$r$ 不小于所有输入块阶数时，压缩到各输入维数的角就给 Choi 正性。定理 36.1 只证明内部大参考存在，不证明该参考与指定过程的两端共同可组合，也不证明能从一个包含输入的嵌套整体中取得独立参考。若另外供应一个共同活动参考的所需有限张量幂，则定理 26.1 的判据直接满足。

这项供应不能只用局部正性替代：在所有对象及实际边均为标准量子的模型中，若操作菜单仅约束局部正性，它可以包含量子比特转置。该映射正，命题 4.3 已给其与二维参考对 Bell 投影的作用为交换算子的一半，在反对称向量上的值为 $-1/2$，所以并非完全正。这个成熟反例只是操作前件的必要边界，不改变 C101 已确定的代数结构。∎

## 37. 反事实、有限提升与理论范围

**命题 37.1（全静态相容世界仍可非量子）。** 若删去 C101 的活动伙伴要求，只保留定义 33.1 的全部实际身份，局部非结合模型仍可在所有有限层闭合。

证明。取 $J=\operatorname{Sym}_2(\mathbb R)$，$S(a,c)=(ac+ca)/2$、$g(a,c)=\operatorname{Tr}(ac)$、$D=0$。对 Pauli 实矩阵 $Z=\operatorname{diag}(1,-1)$、$X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，有 $[L_Z,L_X]X=Z\ne0$，所以它非结合。对象族取全部有限实张量词，实际比较与内积均取各单体的纯张量形式，全部指派取零。模块、条件作用、完整导子律及正 Frobenius 性逐项成立，且任意有限词仍属族中。

这个模型没有任何活动伙伴，故没有 (33.4) 的非零张量因子来排除其局部曲率。它也不能作为 C101 中的静态对象，因为定理 33.3 已要求静态对象为有限实直积。此处不把“其选定运动为零”当作普通复量子系统的零 Hamiltonian 情形；模型数据是对全部标签规定 $D_a=0$。∎

**推论 37.2（一次认证的目标、最小活动尺度与运动数据）。** 对某个给定实际整体 $AB$，它自己的一个活动伙伴已足以认证这个原整体，不预先认证新的最外层。C101 在整个关系体上重复这一同一要求，才使每条实际边都标准化。闭合关系体中的活动伙伴实维数至少四，标准量子比特达到该界。

证明。先只假设原实际 $AB$ 与一个活动伙伴 $R$ 有实际边，不调用整个关系体的 C101。若 $\Gamma=0$，对 $(AB,R)$ 使用 (33.4) 的证明，得到原实际 $M$ 结合；沿两个单位嵌入限制，局部比较也结合，(33.2) 又给 $D_A=D_B=0$。正比较分类使双方和原整体均为经典类型。

若 $\Gamma\ne0$，定理 27.3 可直接用于活动对 $(AB,R)$，得到原实际 $AB$ 的复量子比较、自守及曲率律。将 $\Gamma_HH=0$ 分别限制到 $H=a\otimes1$ 和 $H=1\otimes b$，得到双方局部自守。极化给交替；由每个导子都消去单位，进一步有 $D^A_1=D^B_1=0$。因此 (33.1) 在单位嵌入上化为 $\Gamma_{a\otimes1}=D_a\otimes I$，另一方同理。将原整体的曲率律限制到这两类嵌入，就得到双方的 (33.3)，使用原整体的同一 $\lambda$。零指派侧由零曲率成为结合比较，非零侧按既有局部重构成为有限复量子类型。

此时原实际 $M$ 已为 Jordan，双方局部类型也已取得；定理 34.1 的中心幂等证明便逐项给原整体的标准张量乘法。整个局部认证不要求新输出 $(AB)R$ 也有伙伴。其新输出仍须履行自己的伙伴要求；命题 34.3 展示不履行时的实际终层反例。闭合族中每个活动伙伴本身也有活动伙伴，所以定理 33.3 给其非交换复矩阵块，最小实维数为四；通常量子比特的标准复合给达到该界的模型。∎

**定义 37.3（完整理论的供应范围与来源）。** C101 允许将已供应的纯经典记录、带经典中心的量子对象与实际复合纳入同一关系体，但不强迫纯经典对象存在，也不单独供应全部效果、仪器、指定过程的共同参考、物理时钟或唯一整体态。所供连续一参数 $*$ 自同构群按定理 32.1 给 Hamilton 形式；有限经典代数的连续可逆自同构只能恒定，但随机信道、离散置换与不可逆 Markov 过程可以非平凡，所以零标签指派不禁止记录发生变化。共同源的唯一纯态仍按定理 32.1 已连接的 V97 选源定理，另给同一正代数中的有限相容与逐效果夹逼证书。

[Niestegge，arXiv:1402.0158v2，§5 Definition 1、Theorem 1、Corollary 1](https://arxiv.org/html/1402.0158v2) 的动力对应定义并不要求指派非零，复结合表示及正平方下的 $C^*$ 桥覆盖其零端点；这里不重认领该表示工具。新增的仓内推导是用一个活动伙伴的实际条件作用迫出零指派对象的结合性，再与原实际整体的继用、完整中心盲核和活动关联图接续。有限交换结合正比较分类、Jordan 幂等论证、随机矩阵、Choi 与经典端点完全正性均为成熟中间工具。

[Hanche-Olsen 的模块身份及 Barnum–Wilce，arXiv:1202.4513v2，引言定理与 Proposition 1](https://arxiv.org/html/1202.4513v2) 仍是重要先例，其局部 Jordan、已给量子比特、HSD／可因子化自对偶及复合供应前件按原文保留。本候选只预设伙伴的非零导子活动，不在输入中把它指定成量子比特；定理 33.3 在闭合族中重构它。限定检索不主张上述综合的原创优先权。

本候选仍以有限正 Frobenius 比较、实张量载体、模块作用、保值条件作用、实际导子相容及对象级活动伙伴为明确前件。一次提升的证明是有限的，整个非空闭合对象族却有定理 36.1 的无界有限容量。无限维统一对象、相对时钟的经验标定、时空几何及具体动力学不由这些定理给出。

白话说：在上述有限正比较和实际组合合同下，一张已供应的记录即使所有标签生成的变化都为零，只要它能原样接到会变化的东西上，并在正比较、局部作用和整体变化之间保留完整取值，它就不能随便编一套“静态乘法”；这些关系会把它锁成通常的经典记录。会变化的对象则沿同一合同得到复量子结构。把两者组成的实际整体也原封不动拿去再接一个活动伙伴，藏在联合关系里的额外乘法就被排除了，经典记录和量子系统因此属于同一套理论。经典记录可以连接两边，却不会自动替两边校准同一只钟；只有活动关系相接，量子标尺才传得过去。再按正文供应所需经典对象、完整状态和效果、共同参考，以及混合线性、联合保正且总归一的过程，就接回 Born 概率、经典读写与完全正仪器；另给连续一参数的乘法与伴随自同构群，才有 Hamilton 形式。

## 追加锚（本行以下为增补区）
