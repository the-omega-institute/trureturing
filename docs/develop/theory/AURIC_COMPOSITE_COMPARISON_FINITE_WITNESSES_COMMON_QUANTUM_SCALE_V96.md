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

## 38. 从对象伙伴到同一过程的内部伙伴

**定义 38.1（效果方向的实际过程）。** 沿用 C101 的对象族 $\Omega$、实际边及全部有限正比较前件。由定理 33.3、34.1，记对象 $X$ 的重构复代数为 $\mathcal A_X$，实际边 $X,R\to XR$ 给同一实际代数的标准识别 $\mathcal A_{XR}=\mathcal A_X\otimes\mathcal A_R$。指定实际 Frobenius 中心权仍可相关；下文正性取重构代数的通常 $*$ 正锥。

给定一个被供应的过程菜单 $\mathscr P$。状态方向 $X\to Y$ 的箭头，在效果方向记为正实线性映射 $\Phi:(\mathcal A_Y)_{\rm sa}\to(\mathcal A_X)_{\rm sa}$，并使用其唯一复线性延伸。不预设完全正性、归一、全部抽象正映射均被供应，或过程与标签生成元对易。菜单量词只遍历实际供应的箭头。

**定义 38.2（候选 C102：同一实际过程可再接活动伙伴）。** C102 包含 C101 的完整对象合同，并对每个 $\Phi\in\mathscr P$ 要求存在活动 $R\in\Omega$、两条实际边 $X,R\to XR$、$Y,R\to YR$，以及仍在 $\mathscr P$ 中的正联合箭头 $\Psi:\mathcal A_{YR}\to\mathcal A_{XR}$，满足

$$
\boxed{\begin{aligned}
\Psi(b\otimes1)&=\Phi(b)\otimes1&&\text{对全部 }b\in\mathcal A_Y,\\
\Psi(1\otimes r)&=1\otimes r&&\text{对全部 }r\in\mathcal A_R.
\end{aligned}}\tag{C102}
$$

作为下一次被延伸箭头时，必须继用这个同一实际 $\Psi$、它的两端及全部对象数据。伙伴可随箭头改变；不预给普遍参考、每对对象的复合、固定参考的全部幂，或 $\Psi=\Phi\otimes\operatorname{id}_R$。

若全部正归一态被供应，第一式等价于：对每个联合输入态，系统输出边际仍是原过程对系统输入边际的作用；第二式等价于：每个联合输入态的参考边际原样保留。它们量化全部联合态，包含相关和纠缠输入。把一份校准态或几项平均读数代替这个全取值合同，会改变条件。

## 39. 参考中心是二方过程的完整盲核

**定理 39.1（参考不变的全部中央控制自由及其锁定）。** 在 C101 重构的有限代数中，写

$$
\mathcal R=\bigoplus_j M_{r_j}(\mathbb C).
$$

全部正线性 $\Psi:\mathcal B\otimes\mathcal R\to\mathcal A\otimes\mathcal R$ 若固定参考 $\Psi(1\otimes r)=1\otimes r$，恰具有

$$
\boxed{\Psi=\bigoplus_j(\Phi_j\otimes\operatorname{id}_{r_j}),
\qquad \Phi_j(1)=1,\quad\Phi_j\text{ 为 }r_j\text{ 正映射}.}
\tag{39.1}
$$

这里 $k$ 正指 $\Phi_j\otimes\operatorname{id}_{M_k}$ 正。给定原箭头 $\Phi$ 后，C102 的系统嵌入条件恰等价于全部 $\Phi_j=\Phi$。因此每条 C102 实际联合箭头唯一地满足

$$
\boxed{\Psi=\Phi\otimes\operatorname{id}_{\mathcal R}.}
\tag{39.2}
$$

而且 $\Psi(1)=1$、$\Phi(1)=1$，无需另加独立归一公理。

证明。只用有限正锥的投影支撑。对 $b\ge0$ 及参考中任意投影 $p$，置 $P=1\otimes p$。参考固定与正性给

$$
0\le\Psi(b\otimes p)\le\|b\|P.
\tag{39.3}
$$

若 $0\le Z\le cP$，对 $v\in\ker P$ 有 $\langle v,Zv\rangle=0$，故 $Z^{1/2}v=0$，所以 $Z=PZP$。补投影的像同样支持在 $1-P$ 角。两项相加为 $Y_b=\Psi(b\otimes1)$，于是

$$
[Y_b,1\otimes p]=0,
\qquad \Psi(b\otimes p)=Y_b(1\otimes p).
\tag{39.4}
$$

全部参考投影张成其自伴部分，正元张成 $\mathcal B$ 的自伴部分；谱分解与复线性延伸遂给

$$
Y_b\in\mathcal A\otimes Z(\mathcal R),
\qquad\Psi(b\otimes r)=Y_b(1\otimes r).
$$

参考最小中心块唯一确定 $\Phi_j$，使 $Y_b=\bigoplus_j\Phi_j(b)\otimes1_{r_j}$。固定参考单位给每个 $\Phi_j$ 幺，逐块正性恰为 $r_j$ 正性。反向，每个所列正放大的有限直和确实正且固定全部参考，证明分类无遗漏。

系统嵌入条件逐中心块恰给 $\Phi_j(b)=\Phi(b)$，得到 (39.2)。最后在参考固定式取 $r=1$，再在系统式取 $b=1$，依次取得两项归一。因此不能把“只删除联合归一而保留全部参考固定”当成一个独立放宽。有限投影支撑是成熟中间工具；本条识别的是当前实际过程合同所留下的完整中心自由及其消除条件。∎

**命题 39.2（忠实单态校准仍不能识别同一过程）。** 存在正、幺且固定全部活动参考的联合箭头，对一份忠实参考态校准得到正幺但非完全正的系统映射；它不满足 C102 的全取值系统绑定。

证明。取 $\mathcal A=\mathcal B=M_d$、$d\ge2$，活动参考 $\mathcal R=\mathbb C\oplus M_2$，并取

$$
\Psi=T_d\oplus(\operatorname{id}_d\otimes\operatorname{id}_2),
\qquad
\tau(r_0\oplus r_1)=w r_0+(1-w)\operatorname{tr}_2(r_1),
\quad0<w<1.
\tag{39.5}
$$

这里 $T_d$ 为矩阵转置，$\operatorname{tr}_2$ 是归一迹。第一中心块上参考只是标量，第二块的映射为恒等，所以 $\Psi$ 正幺且固定全部参考。$\tau$ 在两个块上均忠实。单态切片却为

$$
\Phi_\tau(b)=(\operatorname{id}\otimes\tau)\Psi(b\otimes1)
=wT_d(b)+(1-w)b.
$$

记 $F_d$ 为交换算子、$\Omega_d=\sum_i e_i\otimes e_i$。其 Choi 矩阵为 $wF_d+(1-w)|\Omega_d\rangle\langle\Omega_d|$，在任意单位反对称向量上取值 $-w$，故非完全正。系统在两个参考中心块分别执行转置和恒等，没有被绑成同一个 $\Phi_\tau$。

也能在完全正映射内部展示单态资料的不可识别性。把转置换为 $\operatorname{Ad}_Z$、取 $d=2,w=1/2$，其中 $Z=\operatorname{diag}(1,-1)$。中央控制 $\Psi$ 与 $\overline\Phi\otimes\operatorname{id}_{\mathcal R}$ 均完全正、参考全固定，并有相同单态切片 $\overline\Phi=(\operatorname{Ad}_Z+\operatorname{id})/2$；前者按参考标签选择操作，后者不选择。它们在 $b=X$ 及第一中心块上的值分别为 $-X$ 和零，所以是两个实际不同的联合映射。相同校准资料不能恢复原资料已合并的联合区别。∎

## 40. 同一过程的有限继用迫出完全正性

**定理 40.1（按两端块阶停止的实际过程认证）。** 对给定箭头 $\Phi:\mathcal B\to\mathcal A$，记

$$
\mathcal A=\bigoplus_i M_{a_i},\quad
\mathcal B=\bigoplus_\ell M_{b_\ell},\quad
q=\min\{\max_i a_i,\max_\ell b_\ell\}.
\tag{40.1}
$$

设已经供应一段长度 $N$ 的 C102 实际过程延伸，每步伙伴为 $R_j$，最大矩阵块阶数为 $s_j$。若

$$
c_N=\prod_{j=0}^{N-1}s_j\ge q,
\tag{40.2}
$$

则原箭头 $\Phi$ 完全正。活动伙伴给 $s_j\ge2$，所以 $2^N\ge q$ 总是足够；$q=1$ 时长度零已经足够。这仅指完全正性证明所需的深度，不替箭头履行 C102 的实际伙伴供应。不需要把所有尾参考拼成一个独立供应的对象，也不需要认证一个无限维极限。

证明。从 $X_0=X,Y_0=Y,\Phi_0=\Phi$ 出发，两端必须逐次按同一个伙伴延伸：

$$
X_{j+1}=X_jR_j,\qquad Y_{j+1}=Y_jR_j,
\qquad\Phi_{j+1}:\mathcal A_{Y_{j+1}}\to\mathcal A_{X_{j+1}}.
\tag{40.3}
$$

定理 39.1 逐步给 $\Phi_{j+1}=\Phi_j\otimes\operatorname{id}_{R_j}$。在各条实际对象边的标准识别下，有限归纳得到一个实际存在的正映射

$$
\Phi_N=\Phi\otimes\operatorname{id}_{R_0}\otimes\cdots
             \otimes\operatorname{id}_{R_{N-1}}.
\tag{40.4}
$$

选择每个参考的最大矩阵块，再在实际输入、输出代数中压到同一组参考块，得 $\Phi\otimes\operatorname{id}_{c_N}$ 正；压到其较小角，得全部 $k\le c_N$ 的正性。实际存在的是式 (40.3) 的两个嵌套端点。尾部 $R_0\otimes\cdots\otimes R_{N-1}$ 是它们表示中的有限代数因子，不被冒认为一个已经可独立取得的 $\Omega$ 对象。

最后直接复用有限 Choi 判据。若 $\max b_\ell\le\max a_i$，$q$ 正性对每个输入块已给 Choi 正性。若 $\max a_i<\max b_\ell$，通常矩阵迹对偶 $\Phi^\dagger:\mathcal A\to\mathcal B$ 同样 $q$ 正：每个矩阵放大的正锥自对偶，使映射正与其迹对偶正等价。对偶的每个输入块阶数至多 $q$，Choi 判据给其完全正，迹对偶再给 $\Phi$ 完全正。零块分量自然为完全正，不需为它们引用非零形式的表示定理。这个最后的成熟判据不要求 $\Phi$ 幺；幺性已由实际参考合同取得。∎

**推论 40.2（候选的全过程结论与有限量词）。** C102 的每条被供应箭头均为幺完全正映射。对每条原箭头，只需选择满足 $2^N\ge q$ 的有限段即可；最坏量子比特伙伴深度为 $\lceil\log_2q\rceil$。不同箭头可用不同伙伴及不同长度，整个证明不以一条预先给定的无限选择序列为前件。

证明。对每个有限 $N$ 使用定义 38.2 的有限次存在量词；每个已经给出的联合箭头仍在菜单内，故下一步有其自己的伙伴。C101 的活动分类给 $s_j\ge2$，定理 40.1 完成认证。大于二的实际参考块可使 (40.2) 提前满足。∎

**命题 40.3（任意固定截止的锋利反模型）。** 对每个整数 $N\ge0$，存在长度 $N$、每步都用活动量子比特且满足全部二方过程合同的正幺延伸段，原箭头却非完全正。它不能在终点继续履行 C102。

证明。置 $k=2^N$，取 $d>k$，使用成熟 Tomiyama／广义 reduction 映射

$$
\mathcal T_{k,d}(b)=\frac{k\operatorname{Tr}(b)I_d-b}{kd-1}.
\tag{40.5}
$$

它幺且保迹，并且恰 $k$ 正而非 $(k+1)$ 正；该层级可直接复用 [Bera–Bhattacharya–Chruściński，arXiv:2604.18600v1，Theorem 1.1，式 (1)–(2)](https://arxiv.org/html/2604.18600v1)，参数为 $\alpha=kd/(kd-1)$。仓内 Tomiyama 对角扰动族中同一参数为 $\beta=0$ 的顶点，不把其已知正性另认领为新分类。

其失效方向也显式保留：对 $s=k+1\le d$ 和 $\Omega_s=\sum_{i=1}^s e_i\otimes f_i$，有

$$
(\mathcal T_{k,d}\otimes\operatorname{id}_s)
 (|\Omega_s\rangle\langle\Omega_s|)
=\frac{kI_d\otimes P_s-|\Omega_s\rangle\langle\Omega_s|}{kd-1},
\tag{40.6}
$$

在 $\Omega_s$ 方向的本征值为 $(k-s)/(kd-1)<0$。所以 $\Phi_j=\mathcal T_{k,d}\otimes\operatorname{id}_{2^j}$、$0\le j\le N$ 全部正幺，每一步确实是原箭头的同一张量延伸，保留系统及全部参考。再接任意活动伙伴，其某块阶数至少二，便要求至少 $2k$ 正，而 $k+1\le2k$，被 (40.6) 的角排除。

全部对象和对象边可仍取满足 C101 的标准量子关系体。缺失的是终层实际箭头的继续继用。取 $d=2^N+1$，原过程的界正好要求 $N+1$ 个量子比特层，所以不能把一个与原过程维数无关的固定层数代替推论 40.2。这里的新应用是成熟映射恰实现当前内部过程合同的截止边界。∎

## 41. 删除过程关系后留下的相容世界

**命题 41.1（静态旁观者不能替代活动过程伙伴）。** 即使对象世界完整满足 C101，若过程伙伴不要求活动，所有有限层的同一过程延伸仍可保留非完全正映射。

证明。对象及实际边取标准量子世界，原箭头取 $T_d$、$d\ge2$。每次只选经典参考 $\mathbb C^2$，联合箭头为前层箭头与其恒等的张量。与经典代数张量只是两份直和，故全部层均正幺，系统绑定及全部参考固定逐项成立。原 $T_d$ 的非完全正性仍由命题 4.3 的 Bell 负方向见证。对象自己的活动伙伴可以另行存在，却没有进入这些过程的共同检验。∎

**命题 41.2（擦除参考可让非完全正过程永远延伸）。** 若删除参考固定而保留活动伙伴、系统绑定、正性和实际箭头继用，则存在全部有限层相容的非完全正过程族。

证明。仍取标准对象世界、$\Phi_0=T_d$，每次取活动量子比特及一个固定态 $\omega$，递归定义

$$
\Phi_{j+1}(H)=
\Phi_j\bigl((\operatorname{id}\otimes\omega)(H)\bigr)\otimes I_2.
\tag{41.1}
$$

正切片、前层正映射和张量单位的复合为正，幺性保持，且 $\Phi_{j+1}(b\otimes1)=\Phi_j(b)\otimes1$。所有这些同一实际箭头都可留在菜单中继续递归。参考效果却变为 $\omega(r)I$，所以它被擦除重置。系统的原非完全正性不受这种单方检验约束。∎

**命题 41.3（两项参考读数、单态不变及乘积正性均不足）。** 把参考全固定减弱为只固定量子比特的 Pauli $X,Z$，或只固定参考最大混合态，均允许活动伙伴的全部有限层保留转置。仅对乘积正输入要求联合正，也不足以代替 C102 的完整联合正锥。

证明。取

$$
\Phi_j=T_d\otimes T_2^{\otimes j},\qquad d\ge2.
\tag{41.2}
$$

它是整个实际矩阵代数的转置，所以每层正幺，且保留前层系统嵌入。参考转置固定 $I,X,Z$，却把 $Y$ 反号；因此只固定两个互补可见量没有固定完整参考。最大混合态在转置下不变，部分迹又与转置交换，所以参考边际为该态的全部联合输入仍保持这一边际。原系统转置却非完全正。

若改用 $T_2\otimes\operatorname{id}_2$，它在每个乘积正元及其有限正和上为正，系统绑定及全部参考固定也成立；命题 4.3 的 Bell 投影却给负本征值 $-1/2$。所以“联合正”必须作用于已经重构的完整实际正锥。幺归一不能独立删除，原因已由定理 39.1 的单位代入给出；系统绑定的删除则由命题 39.2 的完整中央反例承担。∎

## 42. 实际过程的活动分量与量子仪器

**定理 42.1（共同过程参考约束两端的活动分量）。** C102 中一个过程若两端均活动，则两端处于定义 35.1 的同一个活动关联分量，故有共同 $\lambda$。在固定的部分可组合关系体上，抽象完全正不保证一个过程已有 C102 伙伴。

证明。共同活动 $R$ 与两端各有实际对象边，活动图分别把 $X,R$ 与 $Y,R$ 相连；定理 35.2 传递标尺。反向的缺口在命题 35.3 的完整两分量模型已可实现：两支量子比特之间有抽象幺完全正映射 $b\mapsto\operatorname{Tr}(b)I_2/2$，但任何同时可组合的活动 $R$ 都会迫使两个不同 $\lambda$ 相等，故不存在。这个限制来自共同实际对象的供应，不来自代数映射不完全正。相同活动分量也不被冒认为已经供应了任意指定的共同参考。∎

**定理 42.2（归一标签总箭头认证全部仪器分支）。** 若经典标签对象 $\mathbb C^t$ 及对应的实际输出被供应，令一条有结果的总过程在效果方向为

$$
\Theta:\mathcal B\otimes\mathbb C^t
=\bigoplus_{u=1}^t\mathcal B\longrightarrow\mathcal A.
\tag{42.1}
$$

若这个同一总箭头属于 C102 菜单，则其分量 $\Phi_u(b)=\Theta(b\otimes e_u)$ 全部完全正，并满足

$$
E_u=\Phi_u(1)\ge0,\qquad\sum_uE_u=1.
\tag{42.2}
$$

通常有限迹对偶给完全正、迹不增分支 $\mathcal I_u$，总和保迹，结果概率为 $\operatorname{Tr}(\rho E_u)$。不要求每个非归一分支自己满足“参考边际完全不变”。

证明。推论 40.2 给 $\Theta$ 幺完全正，直和块包含与它复合给每个 $\Phi_u$ 完全正。总单位为各块单位之和，故有 (42.2)。$E_u\le1$ 给状态分支迹不增，总和给保迹。总箭头的实际参考延伸限制到第 $u$ 块，便给同一 $\Phi_u\otimes\operatorname{id}$；无需为每个分支另造独立伙伴。各分支在参考效果上的作用通常为 $E_u\otimes r$，不能误写成 $1\otimes r$。∎

**定理 42.3（候选的标准满足模型及既有量子公理接续）。** C102 相容于完整通常有限复量子过程理论。对任一 C102 关系体，若按定理 36.2 供应全部正归一态、效果并以状态评价给概率，则有密度矩阵和 Born 规则；其实际确定过程及已给标签总箭头分别具有幺完全正、量子仪器形式。若另供同一对象上连续一参数的实际可逆过程群，则它自动为 $*$ 自同构群，并给 Hamilton 形式。

证明。状态与效果的表示直接复用定理 26.1、32.1。那里的“同一张量联合过程”和足够参考检验，在这里由定理 39.1、40.1 从实际过程合同取得，故不必再作为两项独立过程前件。有限 Choi–Kraus 表示给通常逐块矩阵形式，定理 42.2 处理结果分支。

对运动，明列另供 $\Phi_t\in\mathscr P$、$t\in\mathbb R$，满足 $\Phi_0=\operatorname{id}$、$\Phi_{t+s}=\Phi_t\circ\Phi_s$ 及连续性。$\Phi_t$ 与 $\Phi_{-t}$ 均由推论 40.2 为幺完全正。两方向的 Schwarz 不等式给

$$
a^*a\ge
\Phi_{-t}\bigl(\Phi_t(a)^*\Phi_t(a)\bigr)
\ge a^*a.
$$

于是等号成立，应用逆映射得 $\Phi_t(a^*a)=\Phi_t(a)^*\Phi_t(a)$；复极化给乘法保持，故每个 $\Phi_t$ 是 $*$ 自同构。连续群不能连续置换有限中心块；定理 32.1 的有限矩阵内导子表示遂给逐块 Heisenberg 形式 $\Phi_t(b)=e^{itH}be^{-itH}$，以及其迹对偶的 Hamilton 演化。$H$ 可差一个中心元，具体 $H$ 和经验时间单位不由 C102 选定。这里从另供的可逆过程关系推出自同构，没有把一般不可逆过程当成可逆群。

为给完整满足模型，取全部有限直和复矩阵代数的自伴对象、标准实际张量边、同一个正活动标尺及标准正迹比较。经典对象取零指派，活动对象取标准交换子指派。给全部幺完全正效果过程；每条过程都选一个量子比特伙伴，并给标准正张量延伸，延伸仍在同一菜单中。对象合同与过程合同均成立，且所有所需经典标签和有限矩阵过程皆在该模型内。

这个存在模型不把任一部分供应的 $\Omega,\mathscr P$ 自动扩大为完整菜单；定理 42.1 已给反例。相同 POVM 效果仍可有不同后继仪器，故没有唯一 Lüders 更新。共同源的唯一态依旧另需 V97 的有限相容与逐效果夹逼证书；未由过程延伸推出。∎

## 43. 关系的接续、来源与有限范围

**定义 43.1（过程候选的关系范围与成熟工具）。** C102 把对象级伙伴和箭头级伙伴分开：前者迫出经典／复量子代数及其实际乘法，后者要求同一个过程在共同实际两端继续存在。其二方自由是参考中心选择不同系统操作，系统全取值绑定消去这项自由，实际箭头继用再积累足够大的共同矩阵检验。这里各对象都有限维；不存在一个与维数无关的统一有限认证深度，也没有要求无限维对象。

有限投影角支撑、Choi–Kraus 判据和 Tomiyama 映射层级均为成熟中间工具。[Watrous，The Theory of Quantum Information，Theorem 2.22，印刷页 82–84](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf) 给完全正、输入维数放大正、Choi 正及 Kraus 表示的等价。式 (40.5) 的已知 $k$ 正层级由所引 Bera 等 Theorem 1.1 复用，不另列为新映射分类。当前仓内综合是全参考固定下的精确中央过程自由、同一实际箭头的有限伙伴继用、两端块阶停止界及其内部反模型；限定文献核对不建立原创优先权。

单态校准遗失中央关联的命题 39.2，与[统一联合律桥，Theorem 11.2、Proposition 11.3](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md#11-separate-coordinate-pages-do-not-supply-their-joint-continuation)的共同关系是：目标必须在保留资料的纤维上不变，资料才足够。前者给实际正映射在单态切片上的成对实现，后者给原生坐标档案在同摘要上的成对历史；对象、正锥及费用不同，两边的具体结论不互相替代。这里的修复是保留同一个参考全部取值及同一系统过程，而非对已平均的读数再作后处理。

白话说：一个过程接上一个旁观者后，旁观者每一种原来的取值都要原样留下；只看系统，也必须还是原来的那个过程。在 C101 已给出的有限经典—量子对象里，正性会把两者的交叉作用锁定，不能再暗中添一套联合操作。旁观者若带有经典标签，本来可以按标签换用不同过程；“始终是同一个系统过程”恰好锁住这项自由。再把刚得到的实际联合过程原封不动当成过程，继续接活动旁观者，每次沿用同样的关系。对一个给定有限过程，有限次就会积出足够大的共同检验，排除那些单独看合法、遇到纠缠却产生负概率的操作，留下完全正过程。结果标签若作为同一总过程保留，这项约束也传到每个结果分支，得到通常的量子仪器；它仍不会替我们供应全部抽象操作、指定唯一测量更新或选定具体运动。

## 追加锚（本行以下为增补区）

## 44. 同一实际过程的有限路径与共同经典点

**定义 44.1（有限实际路径及其边界映射）。** 沿用 C102 的全部对象、实际空间边和参考合同。给定基本确定过程及其实际输入、输出，将可首尾接续的有限箭头串称为实际路径；空串为同一对象的恒等路径。路径的效果方向边界映射为同一组箭头的通常反向复合：若状态方向为 $X\xrightarrow fY\xrightarrow gZ$，则

$$
(gf)^H=f^H\circ g^H:\mathcal A_Z\longrightarrow\mathcal A_X.
\tag{44.1}
$$

接续只连接同一个实际中间对象，不用抽象代数同构代替对象相同。不同路径可以有相同边界映射；不据此识别它们的历史、记录或资源。以下参考合同作用于该实际路径的同一边界映射，不额外要求其内部每个中间对象都已接上同一个参考。

**定义 44.2（候选 C103：内部经典点的可接路径）。** C103 保留 C102，并要求基本过程的全部有限可接路径都是允许过程，且 C102 的伙伴量词覆盖这些同一实际路径及其边界映射。另有一个共同内部对象 $I\in\Omega$，$\mathcal A_I=\mathbb C$，对每个 $X\in\Omega$ 各有至少一条实际准备 $p_X:I\to X$ 和实际丢弃 $d_X:X\to I$。

这不要求全部态、全部抽象完全正映射或任意两个对象的空间复合。路径接续是过程定义，所有这些路径都可被允许并继续满足参考合同是关系约束；它并非从一个未闭合菜单自动取得。$I$ 的经典类型也不把所有抽象同构于 $\mathbb C$ 的对象识别为这个同一实际对象。若另称 $I$ 为空间张量单位，须另外供应 $I,X\to X$ 的实际单位边；下列满足模型均可供应这些边，但标尺证明不使用它们。

## 45. 三个对象的有向接续锁定一个内部标尺

**定理 45.1（经典中介的入出分量约束）。** 在满足 C102 且实际过程对有限接续闭合的关系体中，两个活动对象只要有任一方向的有限有向实际路径，就处于同一个定义 35.1 的活动关联分量。特别地，对任一静态对象 $C$，记

$$
\begin{aligned}
\operatorname{In}(C)&=\{\alpha(X):X\text{ 活动，存在实际路径 }X\leadsto C\},\\
\operatorname{Out}(C)&=\{\alpha(Y):Y\text{ 活动，存在实际路径 }C\leadsto Y\},
\end{aligned}\tag{45.1}
$$

其中 $\alpha$ 是活动关联分量。若这两个集合都非空，则它们是同一个单点集。只给共同源叉或共同汇叉，不给活动到活动的有向接续，不蕴含这个结论。

证明。有限接续给两活动端点之间的同一允许过程；对该过程使用定理 42.1，便给端点分量相同。对 (45.1)，任取 $a\in\operatorname{In}(C)$、$b\in\operatorname{Out}(C)$，将其两条实际路径在这个同一 $C$ 接起来，所得允许过程迫使 $a=b$。固定其中一个元素，再分别遍历两个集合，即得单点性。共同源叉的两箭头不可反转成一条有向路，汇叉亦同；命题 46.1 给完整反模型。∎

**定理 45.2（共同经典点使全部活动对象同步）。** C103 中全部活动对象属于同一个活动关联分量，具有一个共同正标尺 $\lambda$。任意两个对象 $X,Y$ 都有一个共同实际活动参考，但该参考可随对象对改变。

证明。C102 已使所有允许确定过程的边界映射幺完全正。准备和丢弃在效果方向因而分别为

$$
p_Y^H(b)=\omega_Y(b),\qquad d_X^H(z)=z1_X,
\qquad \omega_Y\ge0,\quad\omega_Y(1)=1.
\tag{45.2}
$$

有限路径 $X\xrightarrow{d_X}I\xrightarrow{p_Y}Y$ 的同一边界映射是

$$
(p_Yd_X)^H(b)=\omega_Y(b)1_X.
\tag{45.3}
$$

这是已允许的替换过程，不是另从抽象完全正映射清单借来的箭头。其 C102 伙伴同时与 $X,Y$ 有实际对象边。若两端活动，定理 42.1 使其同分量；任意活动对象对均可这样取，定理 35.2 遂给一个共同 $\lambda$。对于任意静态或活动端点，C102 仍供应 (45.3) 的共同活动参考，证明后句。∎

**推论 45.3（相对标尺与过程语义的范围）。** 在 C103 中，式 (35.1) 的逐活动分量独立正重标只剩一个全局正重标。丢弃后再准备的过程不携带旧输入信息，但仍承担共同实际参考的标尺约束；它不选择绝对时间单位、具体 Hamiltonian 或唯一整体态。

证明。由定理 45.2，全部活动对象在同一分量，故 (35.1) 只有同一个 $t>0$。通常有限迹对偶将 (45.3) 写成 $\rho\mapsto\operatorname{Tr}(\rho)\sigma_Y$，其中 $\omega_Y(b)=\operatorname{Tr}(\sigma_Yb)$；其输出与旧归一输入无关。标尺关系来自这条实际路径自身的 C102 伙伴，不能从替换映射的抽象代数形式单独取得。

若只按边界映射相等取商，则 $\mathbb C\to\mathcal A_X$ 的幺线性映射唯一，所以这个算子商范畴中的 $I$ 是终对象；实际路径可以保留多条边界映射相同的丢弃历史，故不据此宣称实际路径范畴也是终的。更不把这个确定过程范畴当成所有箭头可逆的群胚。∎

## 46. 三角接续各项条件的完整反事实

**命题 46.1（准备叉、丢弃叉及不闭合菜单均能保留两个标尺）。** 去掉 C103 的丢弃、准备或有限接续闭合三项中的任一项，其余条件均可保留而有两个不同活动标尺。

证明。复用命题 35.3 的完整两标尺对象关系体：共享经典对象 $C_m=\mathbb C^{2^m}$，$m\ge0$；第 $p\in\{1,2\}$ 支为 $A_{p,m,n}=\mathbb C^{2^m}\otimes M_{2^n}$，$n\ge1$，标尺 $\lambda_1\ne\lambda_2$。标准实际空间边仅包含经典／经典、经典／活动及同支活动／活动，输出仍在对应族中。

下列方向都按状态过程叙述。每种菜单先给全部经典之间、同支活动之间的幺完全正效果箭头和恒等，再分别补充：

$$
\begin{array}{c|c|c}
\text{菜单}&\text{另给的方向}&\text{缺少的条件}\\\hline
\mathscr P_{\rm prep}&\text{经典}\to\text{任一活动支}&\text{活动对象丢弃到共同 }I\\
\mathscr P_{\rm disc}&\text{任一活动支}\to\text{经典}&\text{共同 }I\text{ 准备活动对象}\\
\mathscr P_{\rm both}&\text{上述两个方向}&\text{跨支接续所得过程}
\end{array}\tag{46.1}
$$

共同点取 $I=C_0$。第一种菜单对接续闭合：一旦从经典进入某活动支，就只能继续该支内部箭头，不能退出后再进入另一支。第二种方向对偶，亦闭合。第三种菜单有全部准备及丢弃，但 $A_1\to I\to A_2$ 的跨支复合不在其中，故恰缺接续闭合。

三种菜单都满足完整 C102。对涉及第 $p$ 支活动端点的任一箭头选 $R_p=A_{p,0,1}$；它与两个端点都有实际边，标准延伸 $\Phi\otimes\operatorname{id}_{R_p}$ 的两端均落在第 $p$ 支，因而仍在同一个菜单内。纯经典箭头任取 $p=1$。对这个同一联合箭头继续选同支伙伴即可任意有限继用。原对象体的 C101 不变，两个标尺始终不同。这也实现了定理 45.1 中一个入出集合为空、另一集合含多个分量的情形。∎

**命题 46.2（各处一个经典点不等于同一个经典点）。** 若将共同 $I$ 替为各活动区域各有一个抽象经典点，即使每区域完整准备、丢弃并对接续闭合，仍不必同步。

证明。取两个互不相认的通常有限复量子关系体，各自有全部标准空间边、全部幺完全正过程和自己的实际经典点 $I_p$，标尺分别为 $\lambda_p$。只给支内对象边和过程，取其不交并。每个对象及实际过程的参考均在自己区域内部，故 C101、C102 和有限接续闭合成立。$\mathcal A_{I_1}\cong\mathcal A_{I_2}\cong\mathbb C$ 并不供应一个把它们认作同一实际对象的关系，也不供应跨支箭头；两标尺可以不同。∎

## 47. 两端参考与整个过程图参考的算术分离

**定义 47.1（对象共同参考与过程图共同延伸）。** 对对象族 $F\subseteq\Omega$，共同活动参考是一个活动 $R$，使每个 $X\in F$ 均有实际边 $X,R\to XR$。对有限过程图，要求图中每个实际对象都接这个同一 $R$，每条生成箭头都有菜单内的同一张量延伸。按定理 39.1，若满足 C102 的两条绑定，这个延伸的边界映射必为 $\Phi\otimes\operatorname{id}_R$。

共同对象参考只是必要条件；一般部分菜单还须供应这些特定箭头。若生成箭头的延伸均已供应，有限路径闭合和

$$
(f^H\circ g^H)\otimes\operatorname{id}_R
=(f^H\otimes\operatorname{id}_R)\circ(g^H\otimes\operatorname{id}_R)
\tag{47.1}
$$

使图中各条路径在边界映射上相容，但不识别其原生历史。下面的反模型给全部幺完全正箭头，因而排除了缺少某条抽象延伸作为失败原因。

**定理 47.2（任意有限阶的共同参考障碍及精确块阶）。** 对每个 $m\ge2$，存在满足 C103 的关系体，供应任意已有对象之间的全部幺完全正过程，且具有以下性质。记 $K=2^m-1$，每个活动对象有一个非零颜色 $c\in\mathbb F_2^m$；对象族 $F$ 有共同活动参考，当且仅当其活动颜色没有占满全部 $K$ 个非零颜色。最少无共同参考的对象数恰为 $K$；若菜单按所列箭头的端点取共同参考，最少无共同参考的箭头数恰为 $\lceil K/2\rceil$。

更精确地，取不同素数 $p_1,\ldots,p_m$，对 $r\ne0$ 记

$$
b(r)=\prod_{j=1}^m p_j^{r_j},\qquad
\mathcal C(F)=\{c(X):X\in F\text{ 活动}\}.
\tag{47.2}
$$

若共同参考存在，其最大简单块阶数的最小可能值为

$$
\min_R d(R)=\min_{r\in\mathbb F_2^m\setminus(\{0\}\cup\mathcal C(F))} b(r).
\tag{47.3}
$$

证明。对 $d=\prod_jp_j^{a_j}$ 取颜色 $c(d)=(a_j\bmod2)_j$。静态对象给全部 $\mathbb C^t$；颜色 $c\ne0$ 的活动对象给全部非空有限直和 $\bigoplus_iM_{d_i}$，其中每个块阶数的颜色都恰为 $c$。颜色由简单块阶数决定，不依赖另加的对象副本。全部对象取标准量子比较、正归一标准迹配对及同一个正 $\lambda$；静态指派为零。

静态与任意对象之间供应标准实际张量边。两活动对象之间当且仅当颜色不同才供应标准张量边；输出块阶数的颜色为 $c+d\ne0$，故输出仍是同一对象族中的一个对象。对象族对同一颜色的任意经典标签直和封闭。空间单位边也给出。

每个活动对象可选另一个颜色的伙伴，经典对象任取活动伙伴，所以 C101 成立。过程给任意已有对象之间的全部幺完全正效果箭头，取共同 $I=\mathbb C$。恒等、接续、全部准备和丢弃均在菜单中。任一过程至多有两个活动端点颜色；因 $K\ge3$，可选不等于这两个颜色的 $r\ne0$ 及 $R=M_{b(r)}$。两个端点都与同一个 $R$ 有实际边，标准 $\Phi\otimes\operatorname{id}_R$ 仍幺完全正并在菜单中。它的两端仍属对象族，下一步对这个同一箭头重复颜色选择即可。因此完整 C102 和 C103 均成立，不需要固定参考的全部幂。

一个活动 $R$ 可与全部 $F$ 组合，当且仅当其颜色 $r$ 不在 $\mathcal C(F)$。所有未被排除的颜色都以 $M_{b(r)}$ 实现，证明存在判据。每个颜色 $r$ 的块阶数都是 $b(r)$ 乘一个正整数平方，所以不小于 $b(r)$；单块对象 $M_{b(r)}$ 达到界，给 (47.3)。

要占满 $K$ 个颜色至少需 $K$ 个活动对象，分别取 $M_{b(r)}$ 达到。每箭头最多覆盖两个端点颜色，所以至少需 $\lceil K/2\rceil$ 条；将全部非零颜色分成两两配对，最后未配对者用恒等箭头，菜单中的全部幺完全正箭头实现这个下界。对任意未占满颜色的有限图，选择剩余颜色的 $R$ 后全部生成箭头延伸都在菜单中，所以对象判据在此模型内也恰是过程图的判据。给定任意固定有限 $h$，选 $m$ 使 $K>2h$，则任意不超过 $h$ 条箭头都有共同参考，却仍有更大的有限菜单没有共同参考。因此不存在由统一固定有限阶的检查直接保证所有有限菜单共同参考的结论。∎

**命题 47.3（最小三对象过程图的参考不能拼接）。** 定理 47.2 取 $m=2$、$p_1=2,p_2=3$。对象 $M_2,M_3,M_6$ 两两有共同活动参考，任意允许过程以及它的任意有限接续也有 C102 参考；但这三个对象没有共同活动参考。因此一条经过这三个对象的两段实际路径，可以各段和整个复合都合法，却没有同一个参考能延伸完整路径图。

证明。三个颜色依次为 $(1,0),(0,1),(1,1)$。$M_2,M_3$ 可选 $M_6$ 作共同参考，实际输出为 $M_{12},M_{18}$；其余两对分别选 $M_2$ 或 $M_3$。任何活动参考恰有三个非零颜色之一，总会与其中一个对象同色，所以不可能同时组合三者。

任选菜单内的替换过程 $M_2\to M_3\to M_6$。两箭头和复合都在全部幺完全正菜单中；其伙伴可分别选与各自两端不同的颜色。但若要延伸完整两段路径，定义 47.1 要求三个顶点同时与同一个参考组合，这已被排除。这里的三对象提升检验的是同一个过程图的联合可实现性，不是把分别取得的三个伙伴并称为一个共同对象。∎

## 48. 有限参考、普遍参考与全部空间复合互不混同

**定理 48.1（全部有限菜单共有参考仍不供应普遍参考）。** 存在满足 C103、全部正归一态与全部幺完全正过程均被供应的关系体，使每个有限对象族及有限过程图都有共同活动参考，却没有一个活动参考能与所有对象实际组合。有限菜单所需的最小参考块阶也没有统一有限上界。

证明。将定理 47.2 的颜色群换成

$$
G=\bigoplus_{j\ge1}\mathbb F_2,
\qquad b(r)=\prod_{j:r_j=1}p_j,
\tag{48.1}
$$

其中 $p_j$ 遍历素数，每个 $r$ 只有有限支撑。每个矩阵块仍是有限整数阶；活动对象只取其全部块拥有同一个非零奇偶颜色的有限直和，静态对象及实际边规则不变。任意两个端点只排除有限多个颜色，标准张量延伸仍在全部幺完全正菜单中；故 C101、C102 及 C103 的验证逐项不变。

每个有限对象族只排除有限多个非零颜色，选择其外的 $r$ 就给共同参考和全部过程图延伸。反之，对任何指定活动 $R$，令其颜色为 $r$，对象 $M_{b(r)}$ 属于族中且与 $R$ 同色，二者没有实际边，所以没有普遍活动参考。

式 (47.3) 仍成立。给定任意整数 $B\ge2$，将所有满足 $b(r)\le B$ 的非零颜色各取一个对象 $M_{b(r)}$ 作为 $F_B$；这只是一个有限对象族，因为这些 $b(r)$ 是互不相同且不超过 $B$ 的整数。其共同参考只能使用 $b(r)>B$ 的颜色，故每个共同参考均有 $d(R)>B$，而仍可选择尚未出现的素数颜色得到参考。用这些对象的恒等箭头作为有限菜单亦然。这里的界只衡量简单矩阵块阶数，不冒充取得参考的原生费用或时间下界。∎

**定理 48.2（一个普遍量子比特参考和全部过程仍不供应全部空间并置）。** 存在满足 C103 的关系体，全部已有对象间的幺完全正过程、全部态、全部有限标签仪器均被供应，每条过程甚至都可沿用同一个普遍量子比特参考；但 $M_3$ 和 $M_5$ 没有实际空间复合。

证明。令

$$
S=\{2^n,\ 3\cdot2^n,\ 5\cdot2^n:n\ge0\}.
\tag{48.2}
$$

对象取全部非零有限直和 $\bigoplus_iM_{d_i}$，$d_i\in S$；给标准比较、正归一标准迹及同一个 $\lambda>0$ 的标准指派。对 $X=\bigoplus_iM_{d_i}$、$Y=\bigoplus_jM_{e_j}$，当且仅当全部 $d_ie_j\in S$ 时供应其标准实际张量边。每个对象都与 $Q=M_2$ 有实际边，因为 $S$ 对乘二封闭；所有经典对象、经典标签边和单位边也都存在。因此 C101 成立。

取全部对象对之间的所有幺完全正效果箭头作菜单。$I=\mathbb C$，准备、丢弃、恒等和接续均被供应。每条同一 $\Phi\otimes\operatorname{id}_Q$ 仍在菜单中且两端仍属对象族；任意有限继用同一个 $Q$ 均可。所以 C102、C103 以及普遍对象参考和普遍过程参考均成立。对任意 $t$，$\mathcal B\otimes\mathbb C^t=\bigoplus_{u=1}^t\mathcal B$ 仍是对象，所有归一标签总箭头及其仪器分支均已给出。

$M_3,M_5$ 在对象族内而 $M_{15}$ 不在。若二者有实际边，定理 34.1 使输出复代数必为 $M_3\otimes M_5\cong M_{15}$。有限矩阵直和的中心维数及简单块阶数唯一性排除族内另一个对象与 $M_{15}$ 同构：中心维数一迫使它是单块，块阶只能是 $15\notin S$。故该实际边不存在。此处没有否认抽象 $M_{15}$ 的数学存在，缺项是它在指定同一 $\Omega$ 中的实际供应。∎

## 49. 路径候选与现有量子公理的完整接续

**定理 49.1（C103 的量子表示、满足模型及剩余供应）。** C103 给所有已供应对象的有限经典／复量子表示、全部实际空间边的标准张量乘法、全部允许确定过程的幺完全正性、一个共同活动标尺，以及任意对象对的共同活动参考。若再给全部正归一态和效果、相应标签总过程、同一对象上菜单内的连续一参数实际可逆过程群，则分别得到密度矩阵与 Born 概率、量子仪器、Hamilton 形式。通常完整有限复量子理论满足 C103；上述接续不自动供应完整过程图的共同参考、普遍参考、全部空间复合、指定测量更新或具体运动。

证明。对象与实际边复用定理 33.3、34.1；过程、仪器和可逆群复用定理 39.1、40.1、42.2、42.3；共同标尺和对象对参考由定理 45.2 给出。取全部有限复矩阵直和对象、全部标准空间边和全部幺完全正效果箭头，任意状态作准备、唯一丢弃作返回，有限接续仍是允许过程；量子比特的标准张量延伸始终在同一个菜单内。这给完整标准满足模型，不把任意部分供应的关系体扩大成这个最大模型。

定理 47.2、48.1 分别排除由各过程的参考推出任意有限图共同参考、由全部有限图参考推出一个普遍参考；定理 48.2 即使额外供应普遍参考和全体已有对象间过程，仍排除全部空间复合。命题 46.1 隔离了准备、丢弃与有向接续，故不能把经典源叉或汇叉冒充三角路径。相同效果仍可给不同后继仪器，具体 $H$ 和绝对时间单位亦未由这些合同指定；原有 V97 共同源的唯一态继续需要其有限相容与逐效果夹逼证书。∎

**定义 49.2（关系范围与成熟来源）。** 本候选中的过程结合性、有限迹对偶、替换通道、完全正映射复合及有限矩阵直和分类是成熟工具。[Coecke，Terminality implies non-signalling，arXiv:1405.3681v1，§3 Definition 3.1、Proposition 3.2、Remark 3.3](https://arxiv.org/html/1405.3681v1) 将归一与丢弃后的终性联系起来；该文的过程理论已给平行组合，其对称幺半范畴前件不在这里由有限接续免费取得。这里的终对象断言只限推论 45.3 的算子商；[V83 命题 7.4](AURIC_REVERSE_CONTENT_COMPLETENESS_INTERNAL_RETURN_AND_UNITARY_RELATIONS_V83.md) 对全部箭头可逆群胚的结论不适用于一般准备、丢弃过程。

当前仓内综合是将同一实际路径的 C102 参考合同用于经典中介，使相对标尺同步，并给出按矩阵块素因子奇偶构造的完整参考交集层级与精确块阶，以及普遍参考仍不补齐空间对象的反模型。一般集合交集、有限支撑群和素因子分解不被重认领；限定文献核对不建立这些综合的原创优先权。实际路径与其边界映射的区别，也保留了[统一联合律桥 §11](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md#11-separate-coordinate-pages-do-not-supply-their-joint-continuation)中原生联合关系不由边缘摘要决定的边界；这里的块阶结论不转作原生档案费用结论。

白话说：把一个系统放下，再从同一个内部空白点准备另一个系统，这两步既然能接，就必须把接成的同一个过程继续交给伙伴关系检验。哪怕旧信息全被忘掉，这个过程的两端仍要能接上同一个活动旁观者；两端若都活动，其变化标尺便被连起来。只有共同起点或共同终点，还接不成这条有向路。所有活动对象因此共享一套相对标尺，却不等于它们共享一个旁观者：三个系统可以两两找到伙伴，各段过程与复合也都合法，但三者一起就找不到共同伙伴；即使每个有限场面都有伙伴，也未必存在覆盖整个世界的一个伙伴。更进一步，就算一个量子比特真能陪伴所有过程，先后能接仍不意味着任意两个系统都已作为同一个空间整体存在。这把量子对象、过程、标尺与联合空间分别锁在它们真正需要的内部关系上。

## 追加锚（本行以下为增补区）

## 50. 谱权重之间的二元合同与选定滤波族

**定义 50.1（所选谱框架和实际成功分支）。** 沿用 C103 的同一对象、实际空间边与过程菜单。定理 33.3、34.1、40.1、42.2 已分别给出有限复矩阵直和表示、实际张量乘法、确定过程的完全正性及标签总过程的仪器分支。以下在状态方向使用通常有限迹对偶，$\operatorname{Tr}$ 为各简单块通常矩阵迹之和。

对每个已有对象 $\mathcal A=\bigoplus_\alpha M_{d_\alpha}(\mathbb C)$，所选谱框架 $F=(P_{\alpha i})$ 是每块的一组正交秩一投影。给效果 $E=\sum_{\alpha i}x_{\alpha i}P_{\alpha i}$，$0\le x_{\alpha i}\le1$，指定一个仍在同一菜单内的带标签总过程，其成功分支记为 $T_{E,F}$，且成功效果为 $E$。由定理 42.2，这个分支完全正、迹不增，并满足

$$
T_{E,F}^{*}(1)=E.
\tag{50.1}
$$

不将非归一成功分支直接代入 C102 的幺合同。不同框架即使对角化同一个效果，起初也可指定不同分支；不预设 $T_{1,F}=\operatorname{id}$。各简单块内取与框架相容的矩阵单位 $E_{ij}=|i\rangle\langle j|$；改变向量相位不改变下述系数等式。

**定义 50.2（候选 C104：二元谱关系、共同调暗与一次三方向标定）。** C104 包含 C103、定义 50.1 的全族供应，以及以下关系。

1. 所选射线校准：$T_{E,F}(P_{\alpha i})=x_{\alpha i}P_{\alpha i}$。只要求所选框架的这些射线，不要求简并本征空间内的全部射线都不受扰动。
2. 二元环境兼容：存在同一个 $m:(0,1]^2\to\mathbb C$，使任一简单块内不同位置 $i\ne j$、$x_i,x_j>0$ 的 $E_{ij}$ 输出系数为 $m(x_i,x_j)$。这个系数只由有序权重对决定，与对象、框架、其余权重及块阶无关。射线校准将于定理 51.1 保证没有其余输出项。
3. 共同调暗：$T_{aE,F}=aT_{E,F}$，$0<a\le1$。
4. 等权处连续：$\lim_{r\uparrow1}m(1,r)/\sqrt r=m(1,1)$。这是一个二元关系的局部连续条件，不包含统一连续模量。
5. 在同一个已有简单块的三射线角上，供应同一 $E_*=\operatorname{diag}(1,1/2,1/3,0,\ldots)$ 的同一成功分支，以及两条准备—成功分支—末端读出路径。令 $Q_{ij}=|+_{ij}\rangle\langle+_{ij}|$、$|+_{ij}\rangle=(|i\rangle+|j\rangle)/\sqrt2$，这两条路径的准备和效果均为实际供应的 $Q_{12}$、$Q_{13}$，其未归一联合概率满足

$$
\begin{aligned}
\operatorname{Tr}\!\left[Q_{12}T_{E_*,F_*}(Q_{12})\right]
 &=\frac{(1+1/\sqrt2)^2}{4},\\
\operatorname{Tr}\!\left[Q_{13}T_{E_*,F_*}(Q_{13})\right]
 &=\frac{(1+1/\sqrt3)^2}{4}.
\end{aligned}
\tag{50.2}
$$

C101 的活动伙伴链给无界的实际简单块阶，因而有容纳三射线的实际块。任意有限谱列表可以放入足够大的已有块并补零；使用其主角矩阵检验正性，不要求这个角本身另有实际对象或可执行压缩过程。C104 指定理想滤波族；菜单中的其他仪器仍可任意，不要求全部测量分支都遵循同一种更新。式 (50.2) 也不是将成功后状态重新归一所得的条件概率。

## 51. 标定之前允许的全部谱关系

**定理 51.1（跨谱关系的正定核与残余退相干）。** 保留定义 50.2 的前四项而暂不要求式 (50.2)。则存在唯一连续正定函数 $\phi:\mathbb R\to\mathbb C$，$c=\phi(0)\in[0,1]$，使每个所选框架内

$$
\begin{aligned}
T_{E,F}(\rho)_{ii}&=x_i\rho_{ii},\\
T_{E,F}(\rho)_{ij}&=\sqrt{x_ix_j}\,
 \phi(\log x_i-\log x_j)\rho_{ij}\quad(i\ne j,\ x_ix_j>0).
\end{aligned}
\tag{51.1}
$$

涉及零权重的行列为零，中心块之间无转移。反之，每个这样的 $\phi$ 都给满足前四项的完全正、迹不增分支族；在完整通常有限量子菜单中，它们均可作为标签总过程的实际分支。这里正定指每个有限列表 $s_1,\ldots,s_k$ 的矩阵 $[\phi(s_i-s_j)]$ 半正定，允许列表重复。

证明。有限维 Kraus 表示是定理 42.2 之后的成熟工具。先取同一简单块：若 $T(\rho)=\sum_\nu K_\nu\rho K_\nu^*$，射线校准给

$$
\sum_\nu |K_\nu i\rangle\langle K_\nu i|=x_iP_i.
\tag{51.2}
$$

正项之和只有这一条支撑射线，故每个 $K_\nu|i\rangle$ 均与 $|i\rangle$ 成比例；$x_i=0$ 时各项均为零。因此 Kraus 算子在所选框架中全为对角，$T$ 为 Schur 乘法。直和情形对输入、输出块的每个 Kraus 分量同样应用 (51.2)：射线输出不能在其他中心块留下正项，故所有跨块分量为零。Schur 系数矩阵半正定，主对角为 $x_i$，其余系数由共同 $m$ 决定。特别有

$$
m(y,x)=\overline{m(x,y)},\qquad |m(x,y)|\le\sqrt{xy}.
\tag{51.3}
$$

共同调暗使 $m(ax,ay)=a\,m(x,y)$。两对正权重若比例相同，就能各自调暗到同一对权重，所以 $m(x,y)/\sqrt{xy}$ 只依赖 $\log x-\log y$。这定义唯一 $\phi$；$s\ge0$ 时可用 $(x,y)=(1,e^{-s})$ 取值，负半轴由共轭给出。第四项给 $\phi$ 在零处连续。

这里不能将 Schur 矩阵的主对角 $1$ 偷换为 $\phi(0)$：前者来自同一个位置，后者来自两个不同但权重相同的位置。对 $N$ 个重复正权重，其归一 Schur 主角的主对角为 $1$，非对角为同一个实数 $c$。零和向量及全一向量分别给 $c\le1$、$1+(N-1)c\ge0$。已有块阶无界，故 $0\le c\le1$。

进一步，给任意 $s_1,\ldots,s_k$，取 $x_i=r_0e^{s_i}\le1$，在足够大的实际块中每个权重重复 $N$ 次。在这些位置上令检验向量的第 $i$ 组每个分量为 $z_i/(N\sqrt{x_i})$。正性给

$$
\sum_{i,j}\overline z_i z_j\phi(s_i-s_j)
 +\frac{1-c}{N}\sum_i|z_i|^2\ge0.
\tag{51.4}
$$

令整数 $N$ 趋于无穷，即得 $\phi$ 正定。每一步只用了一个有限实际块，极限没有供应无限维对象。

正定核的有限 Gram 表示及 Cauchy–Schwarz 是成熟中间工具。取三个点可得

$$
|\phi(t+h)-\phi(t)|^2
\le 2c\bigl(c-\Re\phi(h)\bigr).
\tag{51.5}
$$

例如把左侧写成同范数 $\sqrt c$ 的第三个 Gram 向量与前两个向量之差的内积；后者范数平方为 $2c-2\Re\phi(h)$。零处连续遂给处处连续，包括 $c=0$ 时 $\phi=0$。

反向在正支撑上写完整 Schur 矩阵

$$
M_{ij}=\sqrt{x_ix_j}\phi(\log x_i-\log x_j)
 +(1-c)x_i\delta_{ij}.
\tag{51.6}
$$

第一项由正定性半正定，第二项也半正定，主对角为 $x_i$；故它给所需完全正分支，且效果恰为 $E$。分别对每个中心块处理并令零支撑消失即可。将 $T_{E,F}$ 与 $T_{1-E,F}$ 作为两个标签分支，效果之和为 $1$，于是它们的总过程保迹。完整有限量子菜单供应这个总过程及其 C102 伙伴。式 (51.1) 的非对角系数、齐次性和局部连续性均直接成立。∎

**命题 51.2（所选射线固定并不固定简并空间）。** 前四项允许 $c=0$ 的完整所选框架退相干，故不能从它们推出 $T_{1,F}=\operatorname{id}$，也不能预先推出框架无关性。

证明。取 $\phi=0$，式 (51.6) 给 $T_{E,F}(\rho)=\sum_i x_iP_i\rho P_i$。对 $E=1$，每个所选 $P_i$ 固定，而 $Q_{12}$ 变为 $(P_1+P_2)/2\ne Q_{12}$。不同简并框架可给不同退相干映射。它仍满足全部前四项和通常有限量子过程合同。∎

## 52. 同一三方向标定锁定整族平方根更新

**定理 52.1（C104 的有限标定刚性）。** C104 迫使对每个已有对象、每个效果和每个所选谱框架都有

$$
T_{E,F}(\rho)=\sqrt E\,\rho\,\sqrt E.
\tag{52.1}
$$

特别地，框架无关性、$T_1=\operatorname{id}$、简并本征空间内所有射线不受额外扰动，以及投影效果的 Lüders 更新都是结论。

证明。任一正权重对 $x_i,x_j$ 给

$$
\operatorname{Tr}[Q_{ij}T(Q_{ij})]
=\frac{x_i+x_j+2\Re m(x_i,x_j)}4
\le\frac{(\sqrt{x_i}+\sqrt{x_j})^2}{4}.
\tag{52.2}
$$

式 (51.3) 表明取等必须 $m(x_i,x_j)=\sqrt{x_ix_j}$，虚部也随之为零。因此同一分支的两条实际读数 (50.2) 给

$$
\phi(\log2)=\phi(\log3)=1.
\tag{52.3}
$$

先只用第一个等式。在另一个允许谱列表 $(1,1/2,1)$ 的三射线主角中，二元环境兼容及共轭性给归一 Schur 矩阵

$$
\begin{pmatrix}1&1&c\\1&1&1\\c&1&1\end{pmatrix}\ge0.
\tag{52.4}
$$

有限 Gram 表示中，内积为 $1$ 的两个单位向量相同；前两者相同，后两者也相同，所以第一与第三的内积必为 $1$，即 $c=1$。这是三射线正性迫出的归一化，没有另加全射线无扰动或 $T_1=\operatorname{id}$。

现在实际归一 Schur 矩阵就是 $[\phi(s_i-s_j)]$。若 $\phi(a)=1$，将任意三个实数 $0,a,t$ 同时平移到非正半轴后取指数，便能放进同一有限谱角。其前两个 Gram 向量相同，比较它们与第三者的内积，得到

$$
\phi(t+a)=\phi(t)\quad(t\in\mathbb R).
\tag{52.5}
$$

因此 $H_\phi=\{a:\phi(a)=1\}$ 是加法子群，并且因连续而闭。式 (52.3) 给 $\mathbb Z\log2+\mathbb Z\log3\subseteq H_\phi$。若 $\log3/\log2=p/q$ 为有理数，就有 $3^q=2^p$，与素因子唯一分解矛盾。两个不可公度实数生成稠密加法子群：将 $0,\alpha,\ldots,N\alpha$ 的模一余数分入 $N$ 个等长区间，得到任意小的非零整数线性组合，再取它的整数倍逼近任意实数。于是闭子群 $H_\phi=\mathbb R$，即 $\phi=1$。

代入式 (51.1) 给 (52.1) 的正支撑部分；式 (51.2) 使零支撑部分消失，逐中心块即得全部结论。锁定本身只需三射线正性与零处连续；定理 51.1 的任意重复次数用于更完整的自由族分类，并非偷偷增加一个无限对象。∎

## 53. 精确标定集合的算术判据

**定理 53.1（有限标定何时足够以及单一效果的三方向界）。** 在定义 50.2 前四项的滤波族内，给有限个正权重比的饱和读数，记其对数为 $a_1,\ldots,a_r$。这些读数迫使全族为 (52.1)，当且仅当 $\sum_j\mathbb Za_j$ 在 $\mathbb R$ 中稠密。

一个固定二方向效果的全部非平凡比值只有一对互反数，故不足以锁定全族；同一效果的三方向可用 $1,1/2,1/3$ 锁定。两个不同二方向效果也可给不可公度比值，故三方向只对“一个效果完成证书”具有上述最小性。

证明。稠密时至少一个 $a_j\ne0$；相应饱和边的三射线重复提升与 (52.4) 同理给 $c=1$。式 (52.5) 使整个生成子群都是周期，连续性给常值 $1$。

反向，非稠密子群的闭包是 $\{0\}$ 或 $a\mathbb Z$、$a>0$。这个成熟的一维闭子群分类可由“正元素下确界为零则稠密，下确界正则取得最小正元素”直接得到。前一情形任选 $t\ne0$，后一情形取 $t=2\pi/a$；连续正定核 $\phi(s)=e^{its}$ 在全部校准比值处等于 $1$，却不恒为 $1$。它对应

$$
T_E^{(t)}(\rho)=E^{1/2+it}\rho E^{1/2-it},
\tag{53.1}
$$

奇异效果的复幂在零支撑定义为零。例如 $1,1/2,1/4$ 的三条边即使全饱和，频率 $2\pi/\log2$ 仍不可见。二方向的单一非零对数只生成离散子群；三方向示例及两个二方向设置的结论由充分方向给出。模相位族 (53.1) 是既有序贯乘积先例，出处见定义 56.2；这里的判据针对跨全部谱列表的同一指定滤波族。∎

## 54. 逐项放松二元合同的完整反模型

**命题 54.1（没有连续性时，两个精确比值仍留下关系盲核）。** 删除定义 50.2 第四项后，其余项不迫使 (52.1)，即使将连续性替成 Borel 可测也不够。

证明。令 $H=\mathbb Z\log2+\mathbb Z\log3$，取 $\phi(s)=1_H(s)$。任意有限列表按模 $H$ 的陪集分组，其核矩阵是全一矩阵块的直和，故正定。$H$ 可数且稠密，故 $\phi$ 为 Borel 函数而在零处不连续。它在 $\log2,\log3$ 处均为 $1$，在 $\log5$ 处为 $0$：否则有 $5=2^m3^n$，清除负指数后仍违背素因子唯一性。

具体地，按 $\log x_i-\log x_j\in H$ 将正谱位置分成等价类 $C$，取 $K_C=\sum_{i\in C}\sqrt{x_i}P_i$、$T_{E,F}(\rho)=\sum_CK_C\rho K_C^*$。这给效果 $E$ 的完全正分支；射线校准、共同二元核、共同调暗与两条实际饱和标定全部成立。在 $(1,1/5)$ 的角上却消除相干，故不是平方根更新。以互补效果分支补成归一标签总过程，并放入完整通常有限量子菜单，C101–C103 仍成立。∎

**命题 54.2（没有共同调暗时，有限标定不能约束其他绝对权重）。** 删除定义 50.2 第三项后，其余项不迫使 (52.1)。

证明。取连续实函数 $h(x)=(x-1)(x-1/2)(x-1/3)$，定义 $K_E=\sqrt E\,e^{ih(E)}$、$T_E(\rho)=K_E\rho K_E^*$。它有成功效果 $E$、射线校准和共同二元系数

$$
m(x,y)=\sqrt{xy}\,e^{i(h(x)-h(y))}.
\tag{54.1}
$$

二元关系在等权处连续；三个标定权重的 $h$ 都为零，所以两读数精确饱和。但 $(1,1/2)$ 的相位为零，共同调暗至 $(1/2,1/4)$ 后，$h(1/2)=0$、$h(1/4)=-1/64$，相位变为 $1/64$。所以共同调暗失败，也并非全族平方根更新。互补分支及全部通常有限量子过程给完整满足其余合同的模型。∎

**命题 54.3（没有环境兼容时，同一对谱权重仍可受别处控制）。** 删除定义 50.2 第二项，并将第四项按每个固定对象、框架的二元系数在等权处连续解释，其余合同不迫使 (52.1)。

证明。设实际标定块阶为 $d_0\ge3$，另选一个已有阶数 $d_1\ne d_0$；C101 保证这种阶数存在。在每块使用式 (53.1)，但取 $t_{d_0}=0$、$t_{d_1}=1$，其他块任取固定频率。每块完全正、射线校准、共同调暗及各自的正等权连续性均成立；标定块内两读数均饱和。相同权重对 $(1,1/2)$ 在两块的系数却相差 $e^{i\log2}\ne1$，故无共同 $m$，也没有全族平方根更新。仍将每个分支以互补分支补齐并取完整有限量子菜单。

即使不借助不同块阶，旁观谱方向也能控制相位。对非零效果令

$$
t(E)=\frac{\operatorname{Tr}E}{\|E\|}-\frac{11}{6},
\qquad
T_E(\rho)=E^{1/2+it(E)}\rho E^{1/2-it(E)}.
\tag{54.2}
$$

取 $T_0=0$。迹与范数之比在共同调暗下不变；在非零效果处连续，复幂的正实部又保证秩变化处的连续延拓，零效果处由分支范数不超过 $\|E\|$ 给连续。对 $E_*$，该比值为 $11/6$，频率为零；对同阶谱 $(1,1/2,0,\ldots)$，比值为 $3/2$，频率为 $-1/3$。这两个效果保留同一对权重，却因第三个权重改变而给不同相位 $1$ 与 $e^{-i\log2/3}$，明确定位第二项所排除的自由度。∎

**命题 54.4（没有射线校准时，孤立谱方向可以被替换）。** 删除定义 50.2 第一项后，其余合同不迫使 (52.1)。

证明。在完整通常有限量子菜单中，对总矩阵秩至少为二的效果仍选平方根分支，对零效果选零分支。对秩一效果 $E=xP$ 则选 $T_E(\rho)=x\operatorname{Tr}(P\rho)\sigma_P$，其中 $\sigma_P$ 是同一对象内的正归一态；在某个阶至少二的简单块内，选其归一单位态 $\sigma_P\ne P$。这个测量后重新准备的分支完全正、成功效果恰为 $xP$，共同调暗不改变秩，故仍齐次。秩一效果没有两个正权重的不同位置，所以二元系数合同在这些效果上不作约束；在其余效果上同一个 $m(x,y)=\sqrt{xy}$、等权连续性和两条秩三标定仍全部成立。每个分支与平方根互补效果分支补成归一标签总过程，保留 C101–C103。可是 $T_{xP}(P)=x\sigma_P\ne xP$，故射线校准与平方根结论均失败。∎

## 55. 精确刚性没有仅靠个别连续性的统一带噪版本

**定理 55.1（误差趋零仍可在近单位效果上达到最大更新差异）。** 定义 50.2 的前四项加两条误差不超过 $\delta$ 的标定读数，不能给全族更新误差随 $\delta\to0$ 一致趋零的结论。存在一列连续滤波族，第一条标定精确、第二条标定误差趋零，但在同一固定实际块内有 $F_n\to1$、最终 $F_n\ge1/2$，使它们与平方根分支的 diamond 距离趋于 $2$。

证明。记 $a=\log2$、$b=\log3$。由无理数的有理逼近，存在整数 $q_n\to\infty$，使 $\|q_nb/a\|_{\mathbb R/\mathbb Z}\to0$；例如上述模一区间原理给任意小非零余数，若分母有界则这些余数不能趋零。令

$$
t_n=\frac{2\pi q_n}{a},\qquad
\phi_n(s)=e^{it_ns}.
\tag{55.1}
$$

每个族满足全部前四项，并且 $\phi_n(a)=1$、$\phi_n(b)\to1$。第二条联合概率距离饱和值的亏损为

$$
\Delta_n=
\frac{1-\cos(2\pi q_nb/a)}{2\sqrt3}\longrightarrow0.
\tag{55.2}
$$

在同一个实际简单块的前两位置取

$$
F_n=\operatorname{diag}(1,e^{-\pi/t_n},1,\ldots,1).
\tag{55.3}
$$

其他中心块取单位，故 $F_n\to1$ 且最终 $F_n\ge1/2$。两位置的模相位差恰为 $\pi$。对同一输入 $Q_{12}$，模相位分支与平方根分支之差主角为

$$
\begin{pmatrix}
0&-e^{-\pi/(2t_n)}\\
-e^{-\pi/(2t_n)}&0
\end{pmatrix},
\qquad
\bigl\|T_{F_n}^{(t_n)}(Q_{12})-\sqrt{F_n}Q_{12}\sqrt{F_n}\bigr\|_1
=2e^{-\pi/(2t_n)}\longrightarrow2.
\tag{55.4}
$$

这给 diamond 距离的同一下界；两条完全正、迹不增分支各自 diamond 范数不超过 $1$，故差的上界为 $2$。于是没有仅依赖 $\Delta_n$ 并趋于零的全族误差界。障碍来自频率无统一上界，而非效果接近零或无限维对象；获得稳健证书须另加共同的定量正则性或其他排除高频自由度的条件。∎

## 56. 滤波候选与量子理论的完整接续

**定理 56.1（C104 的标准满足模型、序贯概率与供应边界）。** 完整通常有限复量子理论满足 C104：指定全部平方根成功分支，并供应互补分支、相应标签总过程与两条标定路径即可。在任一 C104 关系体中，所有指定滤波族都具有式 (52.1)；对已经供应的态 $\rho$ 和后续效果 $B$，其序贯联合概率为

$$
p(E,B\mid\rho)
=\operatorname{Tr}\!\left[B\sqrt E\,\rho\,\sqrt E\right]
=\operatorname{Tr}\!\left[\rho\sqrt E\,B\,\sqrt E\right].
\tag{56.1}
$$

当 $p(E\mid\rho)=\operatorname{Tr}(\rho E)>0$ 时，成功后的归一状态为 $\sqrt E\,\rho\,\sqrt E/\operatorname{Tr}(\rho E)$；概率为零时不定义该条件状态。

证明。标准满足模型在定理 49.1 的完整有限量子模型上选 $T_E(\rho)=\sqrt E\,\rho\,\sqrt E$。其互补效果分支使总过程保迹；C102 的标准伙伴延伸、C103 的实际准备和丢弃接续均已存在。射线、二元核 $m(x,y)=\sqrt{xy}$、共同调暗、局部连续性及两条实际读数逐项成立。一般关系体的结论由定理 52.1 与有限迹循环性给出。

现有量子公理的接续分工因此明确：C101 给对象的有限经典／复量子表示与已给空间边的张量乘法；C102 给实际确定过程的完全正性及实际标签总过程的量子仪器；C103 给活动对象的共同相对标尺；C104 再选出指定理想成功分支的平方根更新和投影特例。C104 已由成功效果为 $E$ 的实际分支供应全部效果读出；若另供全部正归一态并以效果评价给概率，定理 36.2、42.3 给密度矩阵和 Born 规则；若另供同一对象上的连续一参数实际可逆过程群，定理 42.3 给 Hamilton 形式。

这套接续没有供应全部空间复合、任意有限过程图的共同参考、任意 POVM 的整套同时结果过程、任意一般仪器或具体 Hamilton 量。逐个二元滤波的供应尤其不等于多结果总过程的供应；若该总过程另已给定且每个分支选用平方根族，则有 $E_u$ 分支 $\sqrt{E_u}\rho\sqrt{E_u}$ 及 $\sum_uE_u=1$。C104 也不使共同源的唯一态、经验时间单位或定理 55.1 排除的统一噪声控制自动成立。∎

**定义 56.2（二元合同的内生范围与成熟先例）。** C104 把“滤波”的定义限制为同一实际过程关系体中具有射线校准、跨环境同一二元系数、共同调暗、局部连续性及有限饱和标定的指定族；平方根公式是这些关系的共同后果。它把原来单列的更新形式换成可独立删除和检验的定义间约束，没有宣称 C103 已经推出这五项，也没有以“所有东西都在 $\Omega$ 中”为由省略供应或兼容条件。定理 51.1 的自由族及命题 54.1–54.4、定理 53.1 给这些约束的实际区分。

有限 Kraus 表示、Schur／Gram 正性、正定核的 Cauchy–Schwarz 不等式、一维闭子群及无理数有理逼近均为成熟中间工具。[Liu–Wu，The Uniqueness Problem of Sequence Product on Operator Effect Algebra E(H)，arXiv:0812.0630v3，Theorem 4.3、Remark 1、Remark 3](https://arxiv.org/html/0812.0630v3) 已给出式 (53.1) 的实参数模相位序贯乘积先例，并指出其序贯乘积公理 (S1)–(S5) 不足以唯一选择 Lüders 形式。其效果方向公式与这里状态分支互为迹对偶，相位参数相差符号而遍历同一实参数族。这些替代族不被重新认领。

[N1 续卷](AURIC_COHERENT_BRIDGES_LOSSLESS_COMPATIBILITY_AND_EFFECTIVE_RESISTANCE_N1_V78_CONTINUATION.md) 已研究固定通道的 Schur／Gram 相干刚性；[V80](AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md) 的全纯射线无扰动路线不作为本合同的前件。这里的仓内综合是跨谱、跨环境整族的质量 $c\le1$ 分类、由同一三方向实际标定排除残余退相干并以不可公度比值锁定全族，以及与之配套的删项模型和近单位效果上的无统一噪声界。此综合不将成熟中间步骤另列为新增定理，也不以限定检索认领原创优先权。

白话说：把一次测量想成一块能透光的玻璃，每条本征方向透过多少先由自己的透光率决定，尚未确定的是两条方向之间留下多少干涉、是否偷偷多转了相位。要求同一对透光率换个系统、换掉旁边的方向、一起调暗时，彼此关系仍一致，而且接近等亮时不能突然跳变。先有一对方向的干涉达到上界，把它放进三方向结构，就能逼掉隐藏的退相干；再让同一块玻璃上的比例二和比例三都达到上界，剩余相位就必须按两种周期之比不是任何分数的节奏同时重复，连续性将所有缝补齐，最后只剩每个方向乘上透光率平方根这一种更新。这锁定的是已经指定并满足这些合同的理想滤波族；若读数只是接近上界，转得极快的相位仍能藏在误差里，便不能直接套用精确结论。

## 追加锚（本行以下为增补区）

## 57. 相干关系自身的距离与共同变化包络

**定义 57.1（不预设连续性的二元滤波合同）。** 沿用 C103、定义 50.1 的所选框架滤波供应及定义 50.2 第 1–3 项：成功效果为 $E$ 的实际分支、精确所选射线校准、跨对象与旁观谱的同一二元系数，以及共同调暗。暂不要求第 4 项或精确标定 (50.2)。定理 51.1 证明中不使用连续性的部分已经给出

$$
m(x,y)=\sqrt{xy}\,\phi(\log x-\log y),\qquad
c=\phi(0)\in[0,1],\qquad
[\phi(s_i-s_j)]\succeq0.
\tag{57.1}
$$

令 $\gamma=1-c$，在对数权重的有序关系上定义

$$
d_\phi(s,t)=d_\phi(s-t),\qquad
d_\phi(h)=\sqrt{2\bigl(c-\Re\phi(h)\bigr)}.
\tag{57.2}
$$

这是同一二元核的读数，未另供一个物理环境或时间参数。采用第二槽线性的内积约定，每个有限点表可取 Gram 向量，使 $\langle v_t,v_s\rangle=\phi(s-t)$；于是 $d_\phi(s,t)=\|v_s-v_t\|$。相同权重的不同框架位置仍可带有质量 $\gamma$ 的独立退相干，它不混入 $d_\phi(0)=0$，而在下文单列计费。

**定义 57.2（候选 C105：共同包络下的有限误差标定）。** 可用包络是有限值函数 $\omega:[0,\infty)\to[0,\infty)$，满足 $\omega(0)=0$、单调不减、次可加且 $\lim_{r\downarrow0}\omega(r)=0$。C105 的一个预算类 $\mathscr C_\omega$ 由满足定义 57.1 且

$$
d_\phi(h)\le\omega(|h|)\qquad(h\in\mathbb R)
\tag{57.3}
$$

的关系体组成；每个关系体仍供应定义 50.2 中同一 $E_*$、同一成功分支的两条实际准备—读出路径。记两条联合概率为 $p_a,p_b$，令 $a=\log2$、$b=\log3$，定义其归一亏损

$$
\begin{aligned}
\delta_a&=2\sqrt2\left(\frac{(1+1/\sqrt2)^2}{4}-p_a\right)
          =1-\Re\phi(a),\\
\delta_b&=2\sqrt3\left(\frac{(1+1/\sqrt3)^2}{4}-p_b\right)
          =1-\Re\phi(b).
\end{aligned}
\tag{57.4}
$$

给定亏损上界时，C105 的有限误差合同要求这两个实际量不超过各自上界。两条概率仍是未归一联合概率，不是成功后条件概率。正文先用实际 $\delta_a,\delta_b$ 写界；只知经过认证的上界时可单调代入。

同一个候选核有其内生包络

$$
\omega_\phi(r)=\sup_{|h|\le r}d_\phi(h).
\tag{57.5}
$$

若该核连续，则 $\omega_\phi$ 本身为可用包络。取它作为定义不等于已知它的数值；有限误差保证需要实际取得或另行证明的上包络。比较多个不确定候选时，式 (57.3) 必须使用同一个 $\omega$，不能分别选好各自包络后冒充一个共同预算。该合同只约束指定滤波族，其他允许仪器仍可存在。

## 58. 三点相容如何把局部变化接成全局几何

**定理 58.1（C105 的内部距离、局部特例及两条边的计费）。** 在定义 57.1 下，$d_\phi$ 是平移不变的 Hilbert 伪度量，满足

$$
d_\phi(u+v)\le d_\phi(u)+d_\phi(v),\qquad
0\le d_\phi(h)\le2\sqrt c.
\tag{58.1}
$$

它的包络 (57.5) 单调、次可加。C105 自动满足 C104 的等权连续性。若只在某个 $|h|\le h_0$ 邻域另有 $d_\phi(h)\le L|h|$，其中 $L<\infty$、$h_0>0$，则同一界对全部 $h$ 成立，因而 $\omega(r)=Lr$ 是 C105 的一个特例。

两条实际亏损同时约束独立退相干与生成边：

$$
\begin{aligned}
0\le\gamma&\le\delta_*:=\min(\delta_a,\delta_b),\\
d_\phi(a)&\le\eta_a:=\sqrt{2\delta_a},\qquad
d_\phi(b)\le\eta_b:=\sqrt{2\delta_b}.
\end{aligned}
\tag{58.2}
$$

证明。三个有限 Gram 点 $0,u,u+v$ 的三角不等式给第一式；向量范数均为 $\sqrt c$，故得第二式。对 $|h|\le r+t$，将 $h$ 按同一符号分成绝对值分别不超过 $r,t$ 的两段，便得 $\omega_\phi(r+t)\le\omega_\phi(r)+\omega_\phi(t)$。若 $\phi$ 在零处连续，则 $d_\phi(h)\to0$，给 (57.5) 在零处趋零。反向利用定理 51.1 证明内的有限 Gram 估计

$$
|\phi(s+h)-\phi(s)|\le\sqrt c\,d_\phi(h)
\tag{58.3}
$$

及 (57.3)，得到全局一致连续，特别是 C104 第四项。局部线性界则对任意给定 $h$ 取有限整数 $k$ 使 $|h|/k\le h_0$，反复使用三点三角不等式，得到 $d_\phi(h)\le k\,d_\phi(h/k)\le L|h|$。这没有使用无限维实际对象。

最后，正定性给 $\Re\phi(a),\Re\phi(b)\le c$，故 $1-c\le\delta_a,\delta_b$；又有 $c-\Re\phi(a)\le1-\Re\phi(a)=\delta_a$，对 $b$ 同理，得到 (58.2)。所有关系都来自同一 $\phi$，不是将分别可达的记录或最优值拼接。∎

## 59. 标定边在更大关系网中的最小路径预算

**定义 59.1（连续位移与两种标定步的共同包络）。** 给可用 $\omega$ 和两个非负边预算 $\eta_a,\eta_b$，定义

$$
D_{\omega,\eta}(s)=
\inf_{m,n\in\mathbb Z}
\left\{\omega(|s-ma-nb|)
+|m|\eta_a+|n|\eta_b\right\}.
\tag{59.1}
$$

这是同一个对数关系空间的路径预算：沿标定步 $a,b$ 走整数次，余下的一段由共同变化包络支付。它不是实际调用次数或过程费用。对整数 $N\ge0$ 和 $R>0$ 再定义有限点表及其覆盖半径

$$
\begin{aligned}
S_N&=\{ma+nb: m,n\in\mathbb Z,\ |m|+|n|\le N\},\\
r_N(R)&=\max_{s\in[-R,0]}\min_{u\in S_N}|s-u|,\\
\eta&=\max(\eta_a,\eta_b).
\end{aligned}
\tag{59.2}
$$

有限表的最近距离连续，故最大值存在。$S_N$ 是数学比较表，不另供这些字作为物理过程。

**定理 59.2（共同谱关系的路径控制与有限覆盖）。** 对 C105，

$$
d_\phi(s)\le D_{\omega,\eta}(s),\qquad
\sup_{s\in[-R,0]}d_\phi(s)
\le\omega(r_N(R))+N\eta.
\tag{59.3}
$$

并且对每个固定 $R$，$r_N(R)\downarrow0$。路径函数 $D_{\omega,\eta}$ 本身是平移不变伪度量的规范；在满足 $q(s)\le\omega(|s|)$、$q(a)\le\eta_a$、$q(b)\le\eta_b$ 的所有对称次可加规范 $q$ 中，它逐点最大。这项成熟的路径包络性质并不宣称存在量子核同时达到所有预算。

证明。式 (58.1) 及同一标定边的反向对称给

$$
d_\phi(s)\le
d_\phi(s-ma-nb)+|m|d_\phi(a)+|n|d_\phi(b).
\tag{59.4}
$$

代入 (57.3)、(58.2) 后对同一 $(m,n)$ 取下确界，得到第一式。对 $s\in[-R,0]$，在有限表中取最近点，其字长不超过 $N$，直接得到第二式；没有分别选择两个不相容的共同实现。

定理 52.1 的素因子论证已给 $a/b$ 无理，因此 $\bigcup_NS_N=\mathbb Za+\mathbb Zb$ 稠密。给 $\varepsilon>0$，逐点取距离小于 $\varepsilon/2$ 的一个群元素；其 $\varepsilon$ 邻域覆盖紧区间，有限子覆盖只用有限多个整数对。将其字长最大值记为 $N_0$，就有 $r_N(R)\le\varepsilon$（$N\ge N_0$）。单调性由 $S_N\subseteq S_{N+1}$ 给出。这只是有限覆盖存在与标量极限，没有未给出的无理逼近速率。

路径函数非负、对称、零处为零，且以 $m=n=0$ 可得 $D(s)\le\omega(|s|)$。将两条近最优整数路径相加并用 $\omega$ 次可加，得 $D(s+t)\le D(s)+D(t)$；令近最优余量趋零即可。取 $(m,n)=(1,0),(0,1)$ 给两生成元预算。任意其他 $q$ 对任意整数对均不超过 (59.1) 的被积预算，所以 $q\le D$。这些性质属于加权词／路径度量的成熟几何，在这里用于跨谱滤波的共同约束。∎

## 60. 两条有限误差读数控制全部效果与全部有限维数

**定理 60.1（C105 的全族有限证书）。** 记 $\mathcal L_E(\rho)=\sqrt E\,\rho\,\sqrt E$，$\eta_a,\eta_b,\eta,\delta_*$ 取 (58.2)、(59.2)。对任一 C105 关系体、任一已有有限对象、任一效果及所选框架，并对每个 $R>0$、整数 $N\ge0$，都有

$$
\boxed{
\|T_{E,F}-\mathcal L_E\|_\diamond
\le
\|E\|\min\left\{
2,\quad
2\delta_*+
\max\left[
2\omega(r_N(R))+2N\eta,\ 4e^{-R/2}
\right]
\right\}.
}
\tag{60.1}
$$

这里 diamond 范数采用未除二的通常约定。界与对象维数、中心块数、谱的秩和最小正谱值无关。它也没有把抽象参考的范数检验变成缺少的实际空间边。

证明。$E=0$ 时，成功效果为零的完全正分支为零，结论成立。$q=\|E\|>0$ 时，$A=E/q$ 仍是已供应的效果，共同调暗给 $T_{E,F}=qT_{A,F}$，而 $\mathcal L_E=q\mathcal L_A$。因此只需对范数为一的效果证明大括号内的界，再乘以 $q$。下文仍将这个归一效果写作 $E$。

先在一个简单块内处理。令 $\mathcal P_{E,F}(\rho)=\sum_i x_iP_i\rho P_i$，由定理 51.1 的系数分解有

$$
T_{E,F}=\mathcal K_E^\phi+\gamma\mathcal P_{E,F},
\qquad
\mathcal K_E^\phi(|i\rangle\langle j|)
 =\sqrt{x_ix_j}\phi(\log x_i-\log x_j)|i\rangle\langle j|.
\tag{60.2}
$$

式中 $\mathcal K_E^\phi$ 的主对角系数为 $cx_i$；零权重行列为零。对有限正谱点及另一个数学点 $0$ 同时取 Gram 向量，$\langle v_t,v_s\rangle=\phi(s-t)$、$\|v_s\|=\sqrt c$。定义两条有限 Stinespring 算子

$$
\begin{aligned}
V|i\rangle&=\sqrt{x_i}\,|i\rangle\otimes v_{\log x_i},\\
W|i\rangle&=\sqrt{x_i}\,|i\rangle\otimes v_0 .
\end{aligned}
\tag{60.3}
$$

零权重处均定义为零。它们分别实现 $\mathcal K_E^\phi$ 和 $c\mathcal L_E$，范数不超过 $\sqrt c$，且

$$
\|V-W\|=\max_{i:x_i>0}\sqrt{x_i}\,d_\phi(\log x_i).
\tag{60.4}
$$

使用成熟的 Stinespring 上界方向：对任意有限矩阵参考，将 $VXV^*-WXW^*$ 写成 $(V-W)XV^*+WX(V-W)^*$，再取环境偏迹，得到

$$
\|\mathcal K_E^\phi-c\mathcal L_E\|_\diamond
\le2\sqrt c\,
\max_{i:x_i>0}\sqrt{x_i}\,d_\phi(\log x_i).
\tag{60.5}
$$

这一上界适用于收缩算子，不把它们误当成保迹等距。因为 $\mathcal P_{E,F}$ 和 $\mathcal L_E$ 均完全正、迹不增，各自 diamond 范数不超过一，所以

$$
\|T_{E,F}-\mathcal L_E\|_\diamond
\le2\gamma+
2\sqrt c\,
\max_{i:x_i>0}\sqrt{x_i}\,d_\phi(\log x_i).
\tag{60.6}
$$

这也涵盖 $c=0$，没有除以 $c$。

对数权重 $s=\log x$ 位于 $[-R,0]$ 时，(59.3) 给 $d_\phi(s)\le\omega(r_N(R))+N\eta$，而 $e^{s/2}\le1$。$s<-R$ 时，用 $d_\phi(s)\le2\sqrt c$ 得 $2\sqrt c\,e^{s/2}d_\phi(s)\le4c e^{-R/2}\le4e^{-R/2}$。因此 (60.6) 的第二项由 (60.1) 中的最大值控制，第一项由 $\gamma\le\delta_*$ 控制；两条分支各自范数不超过一，再截断于二即可。

直和情形下，射线校准已排除跨中心转移，故两映射之差逐块作用。带任意参考的输入迹范数是各中心块迹范数之和，从而这个直和映射的 diamond 范数等于各块范数的最大值：上界逐块相加，下界把输入限于一块。所有块共享同一 $\phi,\omega,\delta_a,\delta_b$，所以同一个界仍成立。Stinespring 向量和参考仅用于证明范数，未供应新的实际对象或操作。∎

**推论 60.2（共同包络和标定预算的统一模量）。** 固定共同 $\omega$，令 $B_\omega(\delta_a,\delta_b)$ 为 (60.1) 中不含效果因子 $\|E\|$ 的无量纲最小值对 $R>0,N\ge0$ 的下确界，则

$$
\sup_{\mathscr C_\omega}\ \sup_{E,F}
\|T_{E,F}-\mathcal L_E\|_\diamond
\le B_\omega(\delta_a,\delta_b),
\qquad
B_\omega(\delta_a,\delta_b)\longrightarrow0
\quad(\delta_a,\delta_b\longrightarrow0).
\tag{60.7}
$$

第一个上确界只取实际亏损分别不超过所列预算的关系体。特别地，零亏损恢复全族精确平方根更新；在有限速度特例中，可将 $\omega(r_N)$ 直接替为 $Lr_N$。

证明。任给 $\varepsilon>0$，先选有限 $R$ 使 $4e^{-R/2}<\varepsilon/3$，再由 $r_N(R)\to0$ 及共同 $\omega$ 在零处趋零选有限 $N$，使 $2\omega(r_N(R))<\varepsilon/3$。固定这两个选择后，亏损趋零使 $2\delta_*\to0$、$2N\eta\to0$，故右侧可小于 $\varepsilon$。选择次序不依赖系统维数或某个效果。若只知亏损上界，$\delta_*$、$\eta$ 及各固定 $R,N$ 的界均单调，所以下确界仍可单调代入。这里给出可由有限比较表表达的证书，不主张其最优性、已计算的数值或实际取得费用。∎

## 61. 共同包络、不可公度与有限速度各自排除什么

**命题 61.1（每个候选各自光滑仍不能替代共同包络）。** 若将 C105 的同一个 $\omega$ 换成每个候选分别存在一个可用包络，定理 60.2 的跨候选统一趋零结论不成立，即使每个候选都有自己的有限线性速度。

证明。复用定理 55.1 的同一完整模型序列 $\phi_n(s)=e^{it_ns}$。各核有 $d_n(h)=2|\sin(t_nh/2)|\le |t_n||h|$，自己的最小线性速度为 $|t_n|$；两条标定亏损趋零，近单位效果上的更新距离仍趋二。对任何 $r>0$，充分大的 $n$ 使 $h_n=\pi/t_n\le r$，而 $d_n(h_n)=2$。故该序列的共同内生包络恰为 $\sup_n\omega_{\phi_n}(r)=2$（$r>0$），不能在零处趋零。失败处是共同量词，不是某一个固定关系体缺少连续性。∎

**命题 61.2（共同有限速度也不修复共度标定）。** 将两条标定对数替成同一离散群 $a_0\mathbb Z$ 中的有限集合，$a_0>0$，则即使给任意固定 $L>0$ 的共同包络 $\omega(r)=Lr$，零亏损也不必推出平方根更新。

证明。令 $\tau=2\pi/a_0$，取 $0<p\le\min(1/2,L^2/(2\tau^2))$，定义

$$
\phi(s)=(1-p)+p e^{i\tau s}.
\tag{61.1}
$$

这是两个字符的正凸组合，故连续正定，$c=1$。其距离满足 $d_\phi(h)=2\sqrt p\,|\sin(\tau h/2)|\le\sqrt p\,|\tau||h|\le L|h|$。所有标定对数处 $\phi=1$，却在 $s=a_0/2$ 处为 $1-2p\ne1$。定理 51.1 的反向构造给完整量子菜单中的满足模型；例如谱对 $(1,e^{-a_0/2})$ 的相干系数已经偏离平方根更新。这样任意小的正速度预算也不能代替稠密生成关系。$L=0$ 的退化情形不在本命题范围内。∎

**命题 61.3（共同包络严格弱于有限线性速度）。** C105 可包含没有有限线性速度的连续核族，并对其取得统一趋零结论。

证明。对 $0<\varepsilon\le1$ 取 $\phi_\varepsilon(s)=e^{-\varepsilon|s|}$。其正定性可用有限构造核对：将任意点表排序，相邻间隔记为 $\Delta_i\ge0$，递推取单位向量 $v_i=e^{-\varepsilon\Delta_i}v_{i-1}+\sqrt{1-e^{-2\varepsilon\Delta_i}}\,e_i$，其中新 $e_i$ 与此前向量正交。所得有限 Gram 矩阵恰为 $[e^{-\varepsilon|s_i-s_j|}]$，重复点亦可。

这里 $c=1$，且

$$
d_\varepsilon(h)=\sqrt{2(1-e^{-\varepsilon|h|})}
\le\sqrt{2|h|}.
\tag{61.2}
$$

所以全族共享可用包络 $\omega(r)=\sqrt{2r}$。但对每个固定 $\varepsilon>0$，$d_\varepsilon(h)/|h|\to\infty$，不存在有限线性速度。两条亏损 $1-e^{-\varepsilon a}$、$1-e^{-\varepsilon b}$ 随 $\varepsilon\downarrow0$ 趋零，故定理 60.2 仍给全部有限效果的统一平方根极限；直接由 (60.6) 和 $d_\varepsilon(-u)\le\sqrt{2\varepsilon u}$ 还可得上界 $2\sqrt{2\varepsilon/e}$。这说明有限速度是便于使用的充分特例，不是本候选的必要条件。∎

**命题 61.4（距离为零仍不能免除残余退相干）。** 即使 $d_\phi\equiv0$，残余质量 $\gamma$ 仍可非零；式 (60.6) 的维数统一残余系数二不能整体改小。

证明。取常核 $\phi(s)\equiv c\in[0,1]$，则 $T_{E,F}=c\mathcal L_E+\gamma\mathcal P_{E,F}$，$d_\phi\equiv0$，两条亏损均为 $\gamma$。在完整量子满足模型的任意 $d$ 阶块上取 $E=I$、均匀叠加态 $Q$，则 $\mathcal P_{I,F}(Q)=I/d$，从而

$$
\|(T_{I,F}-\operatorname{id})(Q)\|_1
=\gamma\|I/d-Q\|_1
=2\gamma(1-1/d).
\tag{61.3}
$$

令实际有限块阶增大便趋于 $2\gamma$。所以共同相干距离的控制与共同残余质量的控制是两项不同义务；两条亏损同时为它们付费。∎

## 62. 有限误差理论如何接续量子测量公理

**定理 62.1（满足模型、联合预测与成功后状态）。** 通常完整有限复量子理论中选定平方根分支，得到任意可用包络下的零亏损 C105 满足模型。一般 C105 模型中，每个指定分支的成功概率仍恰为 $\operatorname{Tr}(\rho E)$；令 $B$ 为定理 60.1 或推论 60.2 给出的更新误差界，则对任何已经供应的准备及后续效果，联合概率与平方根理论相差不超过 $B/2$，带参考的数学延伸亦然。若成功概率 $p=\operatorname{Tr}(\rho E)>0$，两个成功后归一状态的半迹距离不超过

$$
\min\left(1,\frac{B}{2p}\right).
\tag{62.1}
$$

证明。标准平方根族的 $\phi=1,c=1,d=0$，故任何可用包络都满足合同，实际标签总过程及标定路径由定理 56.1 的满足模型供应。一般两分支 $T_{E,F}$ 与 $\mathcal L_E$ 具有同一成功效果 $E$，所以对同一输入（含参考）输出差为迹零 Hermitian 算子。对 $0\le B_0\le1$ 的后续效果，通常二态判别不等式给期望差不超过输出差迹范数的一半，再用 diamond 界。成功后两态除以相同的 $p$，就得 (62.1)；$p=0$ 时不定义条件状态。无下界的成功概率不能由联合误差界免费取得统一条件态误差界。

若另已供应有限标签的同一个总仪器，且各结果分支都属于上述指定族、效果为 $E_u$、$\sum_uE_u=1$，则平方根标签总映射与它的 diamond 距离不超过 $\sum_uB_u$：输出标签直和的迹范数逐分支相加即可。这个结论需要总仪器的实际供应，逐个二元分支仍不自动补齐它。概率评价、全部态、全部空间复合、任意一般仪器和连续可逆群的供应边界继续按定理 56.1；若另供该可逆群，既有 Hamilton 表示照旧。零亏损 C105 恢复指定理想测量更新，正亏损 C105 给这一公理的统一误差理论，没有将近似更新冒认为精确更新。∎

## 63. 关系包络候选的范围与成熟来源

**定义 63.1（当前综合及其独立前提）。** C105 用同一二元核的距离、共同变化包络和两条实际标定预算约束整个滤波族。它由有限 Gram 几何进入平移不变关系网，再以路径预算和小权重衰减控制所有效果。共同包络不是从两条读数推出的结论；命题 61.1 给出删除它的完整失败模型。射线校准、二元环境兼容、共同调暗仍由命题 54.1–54.4 的相应模型区分，稠密生成由命题 61.2 单独检验。所选射线校准在本候选中保持精确；若射线本身也带误差，就不能直接套用 Schur 分解，需要另补从其实际误差到同一全族记录距离的桥梁。

有限 Gram 距离、三角不等式、加权路径包络、稠密子群的紧集有限覆盖和完全正分支的范数界均是成熟工具。[Pevnyi–Sitnik，Inequalities of M.G. Krein, Yu.V. Linnik and E.A. Gorin for positive definite functions，§2 式 (2)、定理 1 及推论 1](https://arxiv.org/pdf/1609.01218) 给出正定函数的三点变化估计和饱和值周期刚性；式 (58.3) 是该成熟估计的 Gram 表达，本文将它用于同一跨谱族的共同包络。[Kretschmann–Schlingemann–Werner，The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation，arXiv:quant-ph/0605009，§III.C 式 (15)–(16)、Theorem 1](https://arxiv.org/pdf/quant-ph/0605009)，以及库内[来源条目](../../../Library/QuantumChannels/kretschmann2008continuity.md)，给 Stinespring 比较的先例；本文只用其易向的算子展开，将因子二保留为 $\|V\|+\|W\|$ 来处理非归一完全正分支，不把该文通道版的完整双向定理直接套到分支。一般完全正映射的相应先例另见 [Kretschmann–Schlingemann–Werner，A Continuity Theorem for Stinespring’s Dilation，命题 3 式 (13)–(14)](https://arxiv.org/pdf/0710.2495)。[N1 续卷 §§7–9](AURIC_COHERENT_BRIDGES_LOSSLESS_COMPATIBILITY_AND_EFFECTIVE_RESISTANCE_N1_V78_CONTINUATION.md) 已把固定通道的有限比较网及基误差接到全参考范数；这里不重复认领那条固定通道路线。

当前仓内综合是：在 C104 的跨谱整族及残余质量分类上，用共同二元包络、两个近饱和读数和一个有限整数覆盖表，给独立于全部有限块阶、秩与谱最小值的更新证书，并将联合概率和条件态误差分开。路径预算的最大性只在所列伪度量类内成立，不被认作量子误差常数的最优性。无理数覆盖速率、共同包络的有限取得、统计置信率及物理资源成本没有由紧性或范数证明供应；限定来源检索不构成原创优先权结论。

白话说：两次干涉读数接近上界，只能说明两个地方接近理想，不能排除中间藏着飞快转动的相位。现在把“邻近透光率之间的关系最多能变多少”也写进同一关系网，所有待比较候选共用这条包络。沿比例二和比例三前后走若干步，就能靠近任意一小段对数透光率；走每一步付出读数误差，剩下的小缝由包络补上。透光率再小的远处，则由平方根衰减压低其影响。这样，两条有限误差读数就能控制所有有限系统的指定滤波更新。若每个候选各守自己的速度，却没有共同包络，快相位仍能藏进误差；若成功概率太小，成功后的归一状态也仍须单独付账。

## 追加锚（本行以下为增补区）

## 64. 只比较实际返回记录的零误差边界

**定义 64.1（所选滤波关系体与同一二射线探针）。** 保留定义 57.1：C103、全部效果的所选框架实际成功分支、精确所选射线校准、跨对象及旁观谱的同一二元系数、共同调暗。保留定义 57.2 的同一三方向效果 $E_*$ 上两条实际准备—读出路径，但不预设等权连续性、共同包络或精确饱和。由式 (57.1) 已有同一正定核 $\phi$、$c=\phi(0)\in[0,1]$、$\gamma=1-c$，令

$$
a=\log2,\qquad b=\log3,\qquad
\Delta=\max\{1-\Re\phi(a),\ 1-\Re\phi(b)\}.
\tag{64.1}
$$

$\Delta$ 由式 (57.4) 的两个实际联合概率决定，不是成功后条件概率。以下每个关系体固定使用这两条路径已有的同一校准对象、框架和 $Q=Q_{12}$ 准备及末端效果。在该对象上，对 $h\ge0$ 取

$$
H_h=I-(1-e^{-h})P_2,
\qquad
p_\phi(h)=\operatorname{Tr}\!\left[Q\,T_{H_h,F_*}(Q)\right],
\qquad
\kappa_\phi(h)=p_\phi(0)-p_\phi(h).
\tag{64.2}
$$

因此 $H_0=I$，其他谱位置及中心块取单位权重。全部效果的分支供应已经包含每个 $H_h$；同一个 $Q$ 也已由初始标定供应。若记录保留成功标签，就在其既有输出对象上取成功扇区的 $Q$、其他扇区的零效果；该效果同样由全效果合同供应，联合读数可由已有过程复合取得，不要求另供任意受控操作。这没有新增独立的准备或读出供应，也没有新增角对象、压缩或参考系统。起初 $T_{I,F_*}$ 可以不是恒等，$p_\phi(0)$ 是其实际读数。

**定义 64.2（候选 C106：标定边界上的实际返回连续性）。** 令 $\mathscr C$ 为指定的一类定义 64.1 的关系体；其中各关系体的对象和菜单可以不同，各自内部必须使用上述同一校准对象及分支族。定义完全由实际比较给出的曲面

$$
\chi_{\mathscr C}(r,\varepsilon)=
\sup\!\left(
\{\kappa_\phi(h):M\in\mathscr C,\ \Delta_M\le\varepsilon,
\ 0\le h\le r\}\cup\{0\}\right).
\tag{64.3}
$$

C106 对这类允许比较的关系体提出一条约束：

$$
\boxed{
\forall\tau>0\ \exists r_0>0\ \exists\varepsilon_0>0\quad
\forall M\in\mathscr C\ \forall h\in[0,r_0]:\quad
\Delta_M\le\varepsilon_0\ \Longrightarrow\quad
\kappa_{\phi_M}(h)\le\tau .
}
\tag{64.4}
$$

它要求标定亏损和效果到单位的偏离一起趋零时，实际返回概率之差也趋零；不先指定速度或包络。这里的共同量词是类的结构条件，不能由一个固定正亏损关系体的个别连续性代替。该约束不是两个标定读数自动推出的事实。空类或存在正标定间隙的类也可形式上满足 (64.4)，因此具体理论仍须给非空及可逼近零亏损的满足族；命题 67.1 将给出这样的非平凡族。

## 65. 三点几何将返回概率差接到共同相干距离

**定理 65.1（实际返回差的内部距离分解）。** 对定义 64.1 的每个关系体，记 $d_\phi$ 如式 (57.2)，则

$$
\begin{aligned}
p_\phi(h)&=\frac{1+e^{-h}+2e^{-h/2}\Re\phi(h)}4,\\
\kappa_\phi(h)
&=\frac{1-e^{-h}}4+
\frac c2(1-e^{-h/2})+
\frac{e^{-h/2}}4d_\phi(h)^2.
\end{aligned}
\tag{65.1}
$$

特别地，$0\le\kappa_\phi(h)\le1$，且

$$
d_\phi(h)\le2e^{h/4}\sqrt{\kappa_\phi(h)}.
\tag{65.2}
$$

在每个 $0\le h\le r$、$\Delta_M\le\varepsilon$ 的共同实现上，因而有

$$
d_{\phi_M}(h)\le
2e^{r/4}\sqrt{\chi_{\mathscr C}(r,\varepsilon)},
\qquad 0\le\gamma_M\le\varepsilon.
\tag{65.3}
$$

证明。将 $Q$ 的两个对角分量和两个非对角分量代入式 (51.1)，得到第一式；$p_\phi(0)=(1+c)/2$。再用 $d_\phi(h)^2=2(c-\Re\phi(h))$ 重排，得到第二式。正定性给 $c\ge0$、$d_\phi(h)^2\ge0$，故每项均非负；两概率本身在 $[0,1]$ 内，给上界一。丢去前两项便得 (65.2)。最后用同一 $\chi$ 的定义及 $\gamma\le\Delta$，得 (65.3)。这里没有先将 $c$ 归一成一。

式 (65.2) 的距离是有限 Gram 向量的距离；其三角不等式复用定理 58.1。因此返回差的局部控制可以沿同一 $a,b$ 标定边传播。初始正定核仍依赖任意有限重复谱列表的相容性，不能用三阶正性代替它；三点只承担已取得共同核后的距离传播。∎

## 66. 局部实际读数与整族量子更新稳定性的等价

**定义 66.1（全族误差及其标定分层）。** 对 $M\in\mathscr C$ 定义

$$
\begin{aligned}
\mathfrak D(M)&=\sup_{\mathcal A,E,F}
\|T^M_{E,F}-\mathcal L_E\|_\diamond,
\qquad\mathcal L_E(\rho)=\sqrt E\,\rho\,\sqrt E,\\
\mathfrak Q_{\mathscr C}(\varepsilon)
&=\sup\!\left(\{\mathfrak D(M):M\in\mathscr C,
\ \Delta_M\le\varepsilon\}\cup\{0\}\right).
\end{aligned}
\tag{66.1}
$$

第一个上确界只取该关系体已有有限对象及全部指定效果、框架，diamond 范数未除二，其约定为

$$
\|\Phi\|_\diamond=
\sup_{m\ge1}\ \sup_{0\ne X\in\mathcal A\otimes M_m(\mathbb C)}
\frac{\|(\Phi\otimes\operatorname{id}_m)(X)\|_1}{\|X\|_1}.
$$

这里 $X$ 可为任意矩阵输入，不限于正算子或归一态；迹范数按各中心块通常迹求和。因此 $0\le\mathfrak D,\mathfrak Q\le2$。$\mathcal L_E$ 在这里是数学参照，尚未据此供应新过程。

**定理 66.2（C106 的必要充分性与内生误差界）。** 对任何上述比较类，C106 当且仅当

$$
\lim_{\varepsilon\downarrow0}
\mathfrak Q_{\mathscr C}(\varepsilon)=0.
\tag{66.2}
$$

更具体地，对所有 $r,\varepsilon\ge0$，

$$
\chi_{\mathscr C}(r,\varepsilon)
\le\frac r2+\frac12\mathfrak Q_{\mathscr C}(\varepsilon).
\tag{66.3}
$$

反向，取式 (59.2) 的有限表和覆盖半径，记 $u=r_N(R)$，则对任意 $R>0$、整数 $N\ge0$、$\varepsilon\ge0$，

$$
\boxed{
\mathfrak Q_{\mathscr C}(\varepsilon)
\le\min\left\{2,\quad
2\varepsilon+
\max\left[
4e^{u/4}\sqrt{\chi_{\mathscr C}(u,\varepsilon)}
+2N\sqrt{2\varepsilon},\quad4e^{-R/2}
\right]\right\}.
}
\tag{66.4}
$$

因此，在定义 64.1 的共同二元与供应前提内，(64.4) 精确刻画整族统一重构所需的边界正则性。这个必要充分性没有把射线校准、环境兼容或共同调暗一并消掉。

证明。先证明必要方向的定量式。射线校准和二元完全正性给同一两权重处的概率上界

$$
p^*(h)=\frac{(1+e^{-h/2})^2}{4},
\qquad p_\phi(h)\le p^*(h).
\tag{66.5}
$$

这来自 $|m(1,e^{-h})|\le e^{-h/2}$，不以平方根更新为前提。平方根参照取得此上界，且与实际分支具有相同成功效果 $H_h$。两输出差迹为零，定理 62.1 的半迹范数估计给

$$
\begin{aligned}
\kappa_\phi(h)
&=1-p^*(h)-\frac\gamma2+
\bigl(p^*(h)-p_\phi(h)\bigr)\\
&\le\frac h2+\frac12\mathfrak D(M).
\end{aligned}
\tag{66.6}
$$

其中 $1-p^*(h)=(1-e^{-h})/4+(1-e^{-h/2})/2\le h/2$。对同一受限模型及 $h$ 取上确界，即得 (66.3)。若 (66.2) 成立，先把 $r/2$ 取小，再把 $\mathfrak Q(\varepsilon)/2$ 取小，便得 (64.4)。

充分方向复用定理 59.2、60.1 的承重证明，不要求预给 $\omega$。在 $s\in[-R,0]$ 上选同一最近表点 $ma+nb\in S_N$；其余位移的绝对值不超过 $u$。式 (65.3)、距离的反向对称及两条生成边的预算给

$$
d_\phi(s)\le
2e^{u/4}\sqrt{\chi_{\mathscr C}(u,\varepsilon)}
+N\sqrt{2\varepsilon}.
\tag{66.7}
$$

式 (60.6) 的有限共同 Stinespring 比较将它乘以至多二；$s<-R$ 的小权重部分仍由 $4e^{-R/2}$ 控制，残余质量项由 $2\gamma\le2\varepsilon$ 控制。各中心块取最大范数，效果共同调暗再给 $\|E\|$ 因子，最后对效果取上确界而用 $\|E\|\le1$，得到 (66.4)。零效果、零谱值和 $c=0$ 的处理均由该证明保留。

若 (64.4) 成立，给目标误差，先取有限 $R$ 控制尾项；再用 (64.4) 取得足够小的高度预算、一个 $r_0\le1$ 及 $\varepsilon_0$。由 $r_N(R)\downarrow0$ 选有限 $N$ 使 $u\le r_0$，此时 $e^{u/4}\le e^{1/4}$，局部项受所选高度控制。最后保持 $\varepsilon\le\varepsilon_0$ 并继续缩小它，使 $2\varepsilon$、$2N\sqrt{2\varepsilon}$ 足够小。所有选择对全部有限对象、效果和框架共同成立，故得到 (66.2)。

这里转换的是一个实际二射线标量关系与全对象、全谱及数学参考范数之间的控制，不是在定义中先写全族平方根误差趋零。候选仍独立要求边界关系成立；对 $\chi$ 的定义不自动认证其上界、取得方式或费用。∎

**定理 66.3（删除边界关系必有近单位的实际失败见证）。** 若 C106 不成立，则存在 $\tau_0>0$、关系体 $M_n$ 及 $h_n\downarrow0$ 的一个趋零序列，使 $\Delta_{M_n}\to0$，而同一关系体内的两条实际路径满足

$$
p_{\phi_n}(0)-p_{\phi_n}(h_n)>\tau_0,
\qquad
\|H_{h_n}-I\|\le h_n,
\qquad
\mathfrak D(M_n)\ge2\tau_0-h_n.
\tag{66.8}
$$

证明。否定 (64.4)，对 $r=1/n$、$\varepsilon=1/n$ 逐次取失败实现及 $0\le h_n\le1/n$，使返回差大于固定 $\tau_0$。必要时取子序列使 $h_n$ 严格递减；$h_n=0$ 不可能，因为返回差在零处为零。式 (66.6) 反向重排给最后一式，$1-e^{-h_n}\le h_n$ 给第二式。各见证只用其既有校准对象上的同一实际准备和读出；无需在不同关系体之间认定对象相同。∎

## 67. 任意快但任意浅的异常与有限标定的极限

**命题 67.1（C106 严格弱于每个固定误差层上的共同包络）。** 存在包含零亏损平方根族和非零亏损趋零族的完整量子满足类，满足 C106；但对任何固定 $\varepsilon_0>0$，其 $\Delta\le\varepsilon_0$ 子类仍不存在 C105 的共同趋零包络，即使每个核各自光滑。

证明。在完整通常有限复量子菜单中，取

$$
p_n=2^{-n-1},\qquad
t_{nk}=\frac{(2k+1)\pi}{a},\qquad
\phi_{nk}(s)=1-p_n+p_ne^{it_{nk}s}
\quad(n\ge1,\ k\ge0),
\tag{67.1}
$$

并加入 $\phi\equiv1$。每个核为两个字符的正凸组合，连续正定，$c=1$。定理 51.1 的反向构造给所有实际分支；具体为平方根分支和权重 $p_n$ 的模相位分支的凸组合。第一条亏损为 $2p_n$，第二条至多 $2p_n$，故 $\Delta_{nk}=2p_n\to0$。由两条迹不增分支的范数界，

$$
\mathfrak D(M_{nk})\le2p_n=\Delta_{nk},
\qquad
\kappa_{\phi_{nk}}(h)\le\frac h2+p_n.
\tag{67.2}
$$

所以 $\mathfrak Q(\varepsilon)\le\varepsilon$，且 $\chi(r,\varepsilon)\le(r+\varepsilon)/2$，直接满足 C106。

另一方面，任给固定 $\varepsilon_0>0$，选一个固定 $n$ 使 $2p_n\le\varepsilon_0$。对任意 $r>0$，再选充分大的 $k$，使 $h_{nk}=\pi/t_{nk}\le r$。此时

$$
d_{\phi_{nk}}(h_{nk})=2\sqrt{p_n}>0.
\tag{67.3}
$$

同一误差层内这个固定高度阻止任何共同包络在零处趋零；$k$ 的任意增大不改变该层的标定亏损。其相应二射线输出误差至少为 $2p_ne^{-\pi/(2t_{nk})}$，随 $k\to\infty$ 趋于 $2p_n$，所以 (67.2) 的行上确界亦为 $2p_n$。

这个类允许越来越细的振荡，只要求当标定误差趋零时振荡影响也趋零。它表明 (64.4) 的联合边界量词不能改成“存在某个固定正误差邻域，其全部成员共同等度连续”。C105 则通过 $\kappa_\phi(h)\le h/2+d_\phi(h)^2/4$ 给 $\chi(r,\varepsilon)\le r/2+\omega(r)^2/4$，因而蕴含 C106；逆向被本例否定。∎

**命题 67.2（任意固定有限谱标定不排除隐藏的高频）。** 任给有限个固定实对数步长 $s_1,\ldots,s_m$，只要求这些步长的干涉读数趋饱和及每个关系体分别连续，不能推出整族统一平方根误差趋零。这个结论也适用于任意固定有限组效果的全部谱对标定。更强地，可使这组固定效果上各完整分支的 diamond 误差都趋零，而全族误差仍趋二。

证明。存在 $t_j\to\infty$，使 $e^{it_js_\ell}\to1$ 对每个 $\ell$ 同时成立。若全部步长为零则任取 $t_j\to\infty$。否则取一个非零 $s_1$，令 $t=2\pi q/|s_1|$，对其余有限比值使用成熟的同时 Dirichlet 逼近：将有限维单位环面分成 $N^{m-1}$ 个边长 $1/N$ 的盒子，对连续 $N^{m-1}+1$ 个整数倍作抽屉比较，取得非零整数 $q$，使所有比值的 $q$ 倍到整数的距离至多 $1/N$。若这些 $q$ 沿精度趋零无界，取子序列即可；若有界，则某个非零 $q$ 沿子序列精确给出共同整数比值，它的任意大整数倍给精确回返。因此总能取趋无穷的 $t_j$。

取完整量子菜单中的 $\phi_j(s)=e^{it_js}$。全部有限标定同时趋饱和，各核解析；但在 $h_j=\pi/t_j\to0$ 上，$\Re\phi_j(h_j)=-1$。同一 $H_{h_j}$ 和 $Q$ 给

$$
\|T^j_{H_{h_j},F_*}-\mathcal L_{H_{h_j}}\|_\diamond
\ge2e^{-h_j/2}\longrightarrow2.
\tag{67.4}
$$

有限效果的全部正谱对只给有限多个这样的对数差，零谱位置本就消失，故同一构造适用。把原始 $a,b$ 并入有限表仍然有限，所以还可同时令定义 64.1 的 $\Delta_j\to0$。对每个固定效果及每个中心块，选一个正谱值作相位锚，令其 $E^{1/2+it_j}$ 实现乘上对应的逆公共相位。所有剩余对数相位差都在有限表中，故该实现算子在算子范数中趋于 $\sqrt E$；式 (60.5) 的同一展开给完整分支的 diamond 误差趋零。空支撑块直接为零，有限多个固定效果可同时取极限。式 (67.4) 与范数上界二则给全族误差趋二。这里排除的是从固定有限谱标定及个别连续性直接取得统一保证；它不否定带有独立边界约束的理论，也不评价自适应程序或物理取得成本。∎

**命题 67.3（正误差成员本身不连续也不妨碍零误差边界稳定）。** C106 不要求每个正亏损关系体分别满足 C104 的等权连续性。

证明。取 $0\le p\le1$，令

$$
\phi_p(s)=1-p+p\mathbf1_{\{0\}}(s).
\tag{67.5}
$$

指标核的有限 Gram 矩阵按相同参数分成全一块，故正定；这复用命题 54.1 的陪集分块机制，子群改为 $\{0\}$。此时 $c=1$，两个标定亏损均为 $p$。在完整量子菜单内，由正定核分类得到

$$
T^p_{E,F}(\rho)=(1-p)\mathcal L_E(\rho)
+p\sum_{\lambda>0}\lambda P_\lambda\rho P_\lambda,
\tag{67.6}
$$

其中 $P_\lambda$ 是各不同正谱值的完整投影。因此各分支完全正、成功效果为 $E$，精确射线校准、共同二元关系及共同调暗均成立。$p>0$ 时，$\phi_p(h)\to1-p\ne\phi_p(0)$，故逐成员连续性确实失败。

然而两分支差的范数至多 $2p$，且 $\kappa_{\phi_p}(h)\le h/2+p/2$，所以包含 $p=0$ 的整个类满足 C106，并有 $\mathfrak Q(\varepsilon)\le2\varepsilon$。事实上 $\mathfrak D(M_p)=2p$；这个上确界可由如下有限维极限逼近：在任意固定有限阶块选相互不同但趋于一的谱值，式 (67.6) 的第二项趋于所选框架的完全退相干；均匀叠加输入给极限 $2p(1-1/d)$，再让已有有限块阶增大即可。

正亏损 $p$ 固定时，即使效果任意接近单位，返回差仍可趋 $p/2$；让允许标定亏损也趋零，这一跳幅才一同消失。C106 约束的是这个联合边界，不是每个固定误差层的连续性。它因此不能被解释成从两个有限误差读数取得每个模型的精确连续律。∎

## 68. 从边界公理接回测量更新和顺序关系

**定理 68.1（C106 的精确量子层与近似顺序理论）。** 若 $\mathscr C$ 满足 C106，且 $M\in\mathscr C$ 的 $\Delta_M=0$，则对该关系体全部指定分支，

$$
T_{E,F}(\rho)=\sqrt E\,\rho\,\sqrt E.
\tag{68.1}
$$

于是指定分支与谱框架无关，单位效果给恒等过程，投影效果给 Lüders 更新及重复性。若已有同一个总仪器，效果是一组正交投影，且各结果分支正是这些指定分支，则其全部分支和不读取标签时的更新分别为 $P_u\rho P_u$ 和 $\sum_uP_u\rho P_u$。

对一般 $M$，令 $B=\mathfrak Q_{\mathscr C}(\Delta_M)$。任何已供应准备与后续效果的联合概率误差至多 $B/2$；成功概率 $p>0$ 时，成功后归一态的半迹距离至多 $\min(1,B/(2p))$。对同一个已有对象上的任意有限序列效果及所选框架，数学复合还满足

$$
\left\|T_{E_k,F_k}\cdots T_{E_1,F_1}
-\mathcal L_{E_k}\cdots\mathcal L_{E_1}\right\|_\diamond
\le kB\prod_{j=1}^k\|E_j\|.
\tag{68.2}
$$

若这些效果两两可交换，平方根复合恰为 $\mathcal L_{\prod_jE_j}$，故与任一指定框架的 $T_{\prod_jE_j,F}$ 相差至多 $(k+1)B\prod_j\|E_j\|$。这些数学估计不额外供应不在菜单中的顺序操作或总仪器。上述归一态估计针对单个成功分支；若再对完整历史归一，须使用该历史实际成功概率，不能直接沿用单步的 $p$。

证明。零亏损的固定 $M$ 属于每个 $\varepsilon>0$ 的子类，故 $\mathfrak D(M)\le\mathfrak Q(\varepsilon)\to0$，得到 (68.1)。投影更新及其重复性由 $P^2=P$ 直接计算；总仪器结论仍以其实际供应为前提。

一般情形由定义及共同调暗有 $\|T_{E,F}-\mathcal L_E\|_\diamond\le\|E\|B$，而完全正映射的成熟范数恒等式给 $\|T_{E,F}\|_\diamond=\|T_{E,F}^{*}(I)\|=\|E\|$，平方根分支同理。沿有限复合逐项替换并使用范数次乘性，得 (68.2)；含零效果时两复合均为零。交换情形利用 $\prod_j\sqrt{E_j}=\sqrt{\prod_jE_j}$，再加一次效果 $\prod_jE_j$ 的误差，并用 $\|\prod_jE_j\|\le\prod_j\|E_j\|$。这是成熟的有限乘积误差传播，用于本候选的全族界，不作为独立新机制认领。

Born 成功概率在所有亏损下仍精确为 $\operatorname{Tr}(\rho E)$。有限复矩阵直和表示、已有空间边的张量乘法、确定过程的完全正性及共同相对标尺继续由 C101–C103 承担；全部态、全部空间复合、任意一般仪器和具体 Hamilton 量仍不由 C106 供应。另行供应连续实际可逆群时，既有 Hamilton 表示才接入。C106 的新增等价是实际二射线返回关系与整个指定更新族的统一稳定性，不是从两个数无条件推出全部物理规律。∎

## 69. 允许关系族的边界约束与成熟来源

**定义 69.1（内生读数、独立约束与适用边界）。** C106 以实际返回差 $\kappa$ 及允许关系族自身的曲面 $\chi$ 取代预给包络函数；它是定义间的边界约束，不引入额外环境、时间或隐变量。比较类及其共同量词仍是理论的一部分，不能将“所有量都由关系定义”误作“该边界约束由其他前提自动证明”。定理 66.3 给出其失败的实际见证；命题 67.2 说明任意固定有限谱标定仍不能代替它。对单个固定正亏损对象，允许误差门槛任意缩小会使条件空洞，所以候选的承重对象始终是已指定的共同关系族。

有限正定核、三点 Gram 距离及连续性传播复用 §§51、58；整数标定网的紧集覆盖复用 §59；非归一完全正分支的共同 Stinespring 范数比较、中心直和与小谱值衰减复用 §60。其成熟原始来源为 §63 所引 [Pevnyi–Sitnik，§2](https://arxiv.org/pdf/1609.01218) 和 [Kretschmann–Schlingemann–Werner，命题 3](https://arxiv.org/pdf/0710.2495)。模相位族沿用 §56 所引 Liu–Wu 的先例；同时 Dirichlet 逼近是命题 67.2 中明示的成熟中间步骤；其有限相位盒机制在仓内[离散重构边界续卷定理 70.1](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_II.md)及[算术边界卷命题 35.12](ARITHMETIC_BOUNDARY_QUANTIZATION.md) 已有应用，这里仅把同时回返用于滤波标定的反例。固定通道的有限比较记录到全参考范数的路线已见 §63 所引 N1 续卷，本文不重复认领。在明确可容许集合上讨论条件稳定性的成熟先例见 [Werner–Hofmann，Assumption 2 式 (7)](https://arxiv.org/pdf/1905.09765v2)；渐近局部控制与逐成员连续性须分开的量词先例见 [Scholze–Steland，§2 条件 (AEC)](https://arxiv.org/pdf/2412.01635v2)。这里的确定性标定边界不直接套用该二文的 Hilbert 逆问题或随机过程定理，局部实际读数与全族范数的对应由定理 66.2 单独建立。

当前综合将“同一实际二射线在单位附近的返回读数”与“跨全部已有有限对象和效果的完整参考范数”双向连接，并用任意快但逐误差层变浅的满足类区分共同包络与联合边界条件。它不主张文献原创优先权、最优全族常数、有限数据对整个边界关系的认证、统计置信率或资源费用；这些内容没有由上确界定义和紧性证明供给。

白话说：先固定每条方向的透光量，要求同一对透光率搬到别的系统仍守同一个规则，一起调暗也不换规则。现在只看已有的同一对方向：几乎不遮光时，与单位效果下的实际返回记录相比，返回原来叠加状态的概率能不能突然少掉一截？新约束说，两条标定越来越准、遮光也越来越小时，这一截必须越来越小；不要求相位转得慢，也不预先规定速度。先有任意有限组都相容的共同谱关系网，再在其中取三个方向得到三角不等式；比例二和三把这条局部约束传到整张网，极暗方向的影响再由振幅衰减压低。这样一个实际局部读数的边界关系，就恰好等价于全部指定滤波统一接近平方根更新。相位可以任意快，只要它能造成的异常随标定误差一起变浅；若小缝里始终藏着固定高度的异常，就必有几乎不遮光的实际滤波明显偏离量子理想更新。

## 追加锚（本行以下为增补区）

## 70. 从逐射线精确校准转向二元切口预算

**定义 70.1（允许串扰的同一滤波关系体）。** 保留 C103、定义 50.1 的全部所选实际成功分支及其成功效果 $T_{E,F}^{*}(1)=E$，但不要求所选射线校准。保留共同调暗，并将二元环境合同明确限制为一个可压缩系数：在同一简单块内，若 $i\ne j$、$x_i,x_j>0$，则

$$
\langle i|T_{E,F}(E_{ij})|j\rangle=m(x_i,x_j),
\qquad T_{aE,F}=aT_{E,F}\quad(0<a\le1).
\tag{70.1}
$$

同一个 $m$ 适用于全部已有对象、框架、旁观谱及块阶；其他输出项暂不为零。零效果的成功分支因完全正性及成功效果为零而为零。矩阵单位的相位变换同时作用于输入和读出，故这个压缩系数不依赖表示矩阵单位时的向量相位。

对同一对象的全部所选秩一框架投影，包括不同中心块的标签，记

$$
\mathcal P_F=\left\{\sum_{i\in S}P_i:S\text{ 是框架位置的子集}\right\}.
$$

每个 $P\in\mathcal P_F$ 给二元分割 $(P,1-P)$。定义同一分支的切口泄漏及整个关系体的相对预算

$$
\begin{aligned}
\ell(T_{E,F})&=\max_{P\in\mathcal P_F}
 \|P\,T_{E,F}^{*}(1-P)\,P\|,\\
\lambda_M&=\sup_{E\ne0,F}
 \frac{\ell(T_{E,F})}{\|E\|}\in[0,1].
\end{aligned}
\tag{70.2}
$$

范数是该有限复矩阵直和内的算子范数，$P$ 可以跨越中心块。正性及 $T^*(1)=E$ 给 $0\le PT^*(1-P)P\le PEP\le\|E\|P$。等价地，$\lambda_M$ 是使所有同一实现上的 $PT_{E,F}^*(1-P)P\le\lambda_M\|E\|P$ 同时成立的最小共同常数。式 (70.2) 因而是已有正锥内的关系，不先要求供应实现该上确界的准备。若切口内相应纯准备确已供应，则其每个值是“先在这一边、成功后却到另一边”的联合概率；一般不将数学上确界冒充实际取得或有限认证。它包含任意大小的二元切口，不能只检查单个框架位置。

**定义 70.2（实际标定预算及候选 C107）。** 保留定义 50.2 中同一校准对象、同一 $E_*$ 成功分支及已有 $Q_{12},Q_{13}$ 准备—读出路径。令

$$
\begin{aligned}
q_j^*&=\frac{(1+1/\sqrt j)^2}{4},\\
\delta_M&=\max_{j=2,3}
 2\sqrt j\left|\operatorname{Tr}[Q_{1j}T_{E_*,F_*}(Q_{1j})]-q_j^*\right|,\\
\eta_M&=\max\{\lambda_M,\delta_M\}.
\end{aligned}
\tag{70.3}
$$

此时尚无射线合同，实际读数可以超过 $q_j^*$，所以这里取绝对差，不能预先把它叫作非负饱和亏损。沿定义 64.1 已有的同一 $Q=Q_{12}$ 和 $H_h=1-(1-e^{-h})P_2$，仍取

$$
p_M(h)=\operatorname{Tr}[Q T_{H_h,F_*}(Q)],\qquad
\kappa_M(h)=p_M(0)-p_M(h),\qquad h\ge0.
\tag{70.4}
$$

一般 $\kappa_M$ 可以为负。对指定的比较类 $\mathscr C$，定义

$$
\chi_{\mathscr C}(r,\varepsilon)=
\sup\left(\{[\kappa_M(h)]_+:M\in\mathscr C,
 \eta_M\le\varepsilon,\ 0\le h\le r\}\cup\{0\}\right),
\quad [t]_+=\max(t,0).
\tag{70.5}
$$

候选 C107 是定义 70.1 的合同连同以下联合边界关系：

$$
\boxed{\quad
\forall\tau>0\ \exists r_0,\varepsilon_0>0\quad
\forall M\in\mathscr C\ \forall h\in[0,r_0]:\quad
\eta_M\le\varepsilon_0\ \Longrightarrow\
 [p_M(0)-p_M(h)]_+\le\tau .\quad}
\tag{70.6}
$$

$\lambda$、$\delta$ 与 $\kappa$ 都属于同一关系体；不能把不同实现中分别可达的最小预算拼在一起。候选不预设任何成员逐点连续，也不预给连续包络。切口预算本身仍是全族关系，两个局部标定读数不自动给出它。比较类应另给非空及趋近零预算的实现，命题 74.1 将给完整满足族。

## 71. 二元切口的共同提升与保留谱关系的精确参照

**定理 71.1（保持同一二元系数的切口修复）。** 对定义 70.1 的每个关系体，存在唯一由其压缩系数决定的数学参照族 $R_{E,F}$，满足精确所选射线校准、成功效果 $E$、同一 $m$ 及共同调暗。它逐中心块为 Schur 乘法，且

$$
\|T_{E,F}-R_{E,F}\|_\diamond
 \le\|E\|\,b(\lambda_M),\qquad
b(t)=\min\{2,4\sqrt t+t\}\quad(t\ge0).
\tag{71.1}
$$

这里及下文 diamond 范数均用定义 66.1 的未除二、任意矩阵输入及任意数学参考约定。$R$ 是证明中构造的完全正映射，不据此断言它是菜单内另一个实际分支。

证明。先在一个有限对象内，将原完全正映射按输入、输出中心块取 Kraus 分量。把各分量嵌入全部块的 Hilbert 直和 $\mathcal H$，并给其独立环境标签，得到 $B(\mathcal H)$ 上的完全正延伸 $\widetilde T$；它先删除输入的跨中心项，输出仍在原直和内，$\widetilde T^*(1)=E$。因此原代数上及其任意参考上的差范数不超过该延伸上的相应范数。以下有限 Stinespring 算子 $V:\mathcal H\to\mathcal H\otimes\mathcal K$ 满足

$$
\widetilde T(X)=\operatorname{Tr}_{\mathcal K}(VXV^*),
\qquad V^*V=E,
\qquad \|V\|=\sqrt{\|E\|}.
\tag{71.2}
$$

令 $q=\|E\|>0$、$\ell=\ell(T)$。对每个框架切口 $P$，

$$
\|((1-P)\otimes1)V P\|^2
 =\|P T^*(1-P)P\|\le\ell.
\tag{71.3}
$$

其互补切口也在同一集合。取 $U_P=2P-1$，两个交叉角有正交的输入域和输出域，故

$$
\|(U_P\otimes1)V-VU_P\|
 =2\max\{\|(P\otimes1)V(1-P)\|,
          \|((1-P)\otimes1)VP\|\}
 \le2\sqrt\ell.
\tag{71.4}
$$

对全部框架符号有限平均，得到

$$
W=2^{-D}\sum_{U=\sum_i\epsilon_iP_i}(U\otimes1)VU
 =\sum_i(P_i\otimes1)V P_i,
\qquad \|V-W\|\le2\sqrt\ell,
\tag{71.5}
$$

其中 $D$ 为该对象全部框架位置数，$\epsilon_i\in\{-1,1\}$。全部切口属于同一个有限 Boolean 投影代数，其符号组成群 $(\mathbb Z/2\mathbb Z)^D$。式 (71.5) 取这个作用的共同交织部分：对每个切口都有 $(P\otimes1)W=WP$。这个有限平均是矩阵恒等式，不要求实际供应符号操作或其随机混合。每个 $W|i\rangle$ 只在输出射线 $i$ 上，故 $W^*W=\sum_i y_iP_i$，且

$$
0\le y_i=\langle i|T(P_i)|i\rangle\le x_i,
\qquad
0\le x_i-y_i=\operatorname{Tr}[(1-P_i)T(P_i)]\le\ell.
\tag{71.6}
$$

于是 $W^*W\le E$、$\|W\|\le\sqrt q$。令 $S(X)=\operatorname{Tr}_{\mathcal K}(WXW^*)$，并加回丢失的对角成功质量：

$$
R(X)=S(X)+\sum_i(x_i-y_i)P_iXP_i.
\tag{71.7}
$$

两项均完全正，$R^*(1)=E$、$R(P_i)=x_iP_i$，且没有跨中心转移。对原块内不同位置，$S(E_{ij})$ 的 $(i,j)$ 系数恰为 $\langle i|T(E_{ij})|j\rangle$，补项不改变它。涉及零权重的位置原 Kraus 列已为零。因而 $R$ 正是对角系数取 $x_i$、其余系数取原压缩系数的唯一 Schur 映射；它不依赖 Stinespring 表示选择。此显式描述也给共同调暗。

有限维迹对偶将任意输入 diamond 范数等同于伴随的完全有界算子范数；共同 Stinespring 差的成熟估计因而给

$$
\|\widetilde T-S\|_\diamond
 =\|\widetilde T^*-S^*\|_{\mathrm{cb}}
 \le(\|V\|+\|W\|)\|V-W\|
 \le4\sqrt{q\ell}.
\tag{71.8}
$$

补项是完全正映射，其 diamond 范数等于其伴随在单位上的算子范数，故不超过 $\ell$。限制回原代数并用 $\ell\le q\lambda_M$ 得 $q(4\sqrt{\lambda_M}+\lambda_M)$。两条成功效果同为 $E$ 的完全正映射各有范数 $q$，另给上界 $2q$，即得 (71.1)。$E=0$ 时两者均零。

范数桥复用 [Kretschmann–Schlingemann–Werner，命题 3](https://arxiv.org/pdf/0710.2495v1) 的共同 Stinespring 估计及有限迹对偶；有限符号平均复用 [Han–Liu，§2.2 的矩形 twirling 映射](https://arxiv.org/pdf/2311.16349v1)，这里的输出表示为 $U\otimes1$、输入表示为 $U$，共同交织部分正是其平均的像。这里将它们用于保留原二元谱系数和成功效果的同一修复，不把单独的范数估计或有限平均认领为新机制。∎

**定理 71.2（参照核及实际读数的误差桥）。** 数学族 $R$ 满足定义 57.1 的全部代数合同，所以有式 (57.1) 的共同有限正定核 $\phi$、$c\in[0,1]$ 及 $\gamma=1-c$，无需连续性。令 $\Delta_R$ 为式 (64.1)，$\kappa_R$ 为用 $R$ 代替 $T$ 的式 (70.4)。则

$$
\Delta_R\le\delta_M+\sqrt3\,b(\lambda_M),
\qquad
0\le\kappa_R(h)\le[\kappa_M(h)]_++b(\lambda_M).
\tag{71.9}
$$

证明。定理 51.1 中不使用连续性的部分只需要这些数学映射的完全正性、全部有限谱列表和精确射线合同；它不需要把 $R$ 另放入实际菜单。故它给同一 $\phi$。三点 Gram 距离及定理 65.1 同样成立。

$T$ 与 $R$ 成功效果相同，归一正输入的两输出差迹为零；任何效果的概率差至多其迹范数的一半。因此在范数至多一的每个效果处，两实际／参照概率之差至多 $b(\lambda_M)/2$。在 $E_*$ 上，参照的两个差满足

$$
q_j^*-\operatorname{Tr}[Q_{1j}R_{E_*,F_*}(Q_{1j})]
 =\frac{1-\Re\phi(\log j)}{2\sqrt j}\ge0.
\tag{71.10}
$$

三角不等式和 $j\le3$ 给第一界。在 $H_0=1$ 与同一 $H_h$ 上各比较一次，得 $|\kappa_R(h)-\kappa_M(h)|\le b(\lambda_M)$；定理 65.1 给 $\kappa_R\ge0$，从而得第二界。比较的是原路径的两个数学预测，不需要供应 $R$ 的准备、分支或读出。∎

## 72. 允许串扰的实际局部关系与全族更新等价

**定义 72.1（新预算分层的全族误差）。** 沿用定义 66.1 对实际族 $T$ 的 $\mathfrak D(M)$，但比较类用新的共同预算：

$$
\mathfrak Q_{\mathscr C}(\varepsilon)=
\sup\left(\{\mathfrak D(M):M\in\mathscr C,
 \eta_M\le\varepsilon\}\cup\{0\}\right).
\tag{72.1}
$$

以下 $\chi$ 专指式 (70.5)，不是将旧预算曲面直接换名。

**定理 72.2（C107 的全族必要充分性）。** 对任何定义 70.1–70.2 的比较类，C107 当且仅当

$$
\lim_{\varepsilon\downarrow0}\mathfrak Q_{\mathscr C}(\varepsilon)=0.
\tag{72.2}
$$

定量地，令 $b_\varepsilon=b(\varepsilon)$、$f_\varepsilon=\varepsilon+\sqrt3b_\varepsilon$，则

$$
\chi(r,\varepsilon)\le\frac r2+
 \frac12\mathfrak Q_{\mathscr C}(\varepsilon).
\tag{72.3}
$$

反向，取式 (59.2) 的同一整数标定表、覆盖半径 $u=r_N(R)$，对任意 $R>0$、整数 $N\ge0$，有

$$
\boxed{
\mathfrak Q_{\mathscr C}(\varepsilon)\le
\min\left\{2,\ b_\varepsilon+2f_\varepsilon+
\max\left[
4e^{u/4}\sqrt{\chi(u,\varepsilon)+b_\varepsilon}
 +2N\sqrt{2f_\varepsilon},\quad4e^{-R/2}
\right]\right\}.
}
\tag{72.4}
$$

所有参数共同作用于实际对象、效果和框架，没有块阶、秩或最小正谱值因子。

证明。必要方向不依赖修复。$T_{1,F_*}$ 保迹，故 $p_M(0)\le1$；$\mathcal L_{H_h}$ 的同一返回概率为 $p^*(h)=(1+e^{-h/2})^2/4$。它与实际分支有相同成功效果，所以

$$
\kappa_M(h)\le1-p^*(h)+p^*(h)-p_M(h)
 \le\frac h2+\frac12\mathfrak D(M).
\tag{72.5}
$$

右侧非负，故正部也受此界。取相同预算下的上确界即得 (72.3)，从而 (72.2) 蕴含 C107。

充分方向中，同一个 $\eta_M\le\varepsilon$ 给 $\lambda_M,\delta_M\le\varepsilon$。定理 71.1–71.2 因而给

$$
\Delta_R\le f_\varepsilon,\qquad
\kappa_R(h)\le\chi(u,\varepsilon)+b_\varepsilon
 \quad(0\le h\le u).
\tag{72.6}
$$

在修复族的同一有限 Gram 表示中，定理 65.1 把后一界变为局部距离界；定理 58.1 的三点三角不等式及两条标定边再给

$$
d_\phi(s)\le
2e^{u/4}\sqrt{\chi(u,\varepsilon)+b_\varepsilon}
 +N\sqrt{2f_\varepsilon}
 \quad(-R\le s\le0).
\tag{72.7}
$$

完全复用定理 60.1 的有限共同 Stinespring 比较、小权重尾界及中心直和论证，得到 $R$ 与平方根参照的误差界，即式 (72.4) 中去掉首项 $b_\varepsilon$ 的部分。这里不将 $\eta\le\varepsilon$ 子类偷换成全部 $\Delta_R\le f_\varepsilon$ 的模型：局部上界只对同一个原模型所得的修复族使用。再以定理 71.1 加上实际族到其修复族的误差，得 (72.4)。

若 C107 成立，先取有限 $R$ 控制尾项，再由联合边界关系取足够小的局部高度预算及 $r_0\le1$，再取有限 $N$ 使 $u\le r_0$。最后缩小 $\varepsilon$，同时控制 $b_\varepsilon$、$f_\varepsilon$ 及 $N\sqrt{2f_\varepsilon}$，并保持在所选联合边界预算内。因为 $b_\varepsilon,f_\varepsilon\to0$，全部项都可共同趋零。这给 (72.2)，没有预定收敛速度。∎

**定理 72.3（可检验的失效方向及预算的必要性）。** 对每个上述实际模型，

$$
\lambda_M\le\frac12\mathfrak D(M),\qquad
\delta_M\le\sqrt3\mathfrak D(M).
\tag{72.8}
$$

若 C107 的联合边界条件失败，则存在 $\tau_0>0$、$\eta_{M_n}\to0$、$h_n\downarrow0$，使同一实际准备—读出对满足

$$
p_{M_n}(0)-p_{M_n}(h_n)>\tau_0,
\qquad \mathfrak D(M_n)\ge2\tau_0-h_n.
\tag{72.9}
$$

证明。切口内归一正输入的平方根输出在切口外为零。实际与平方根分支成功效果相同，故切口外概率至多误差范数的一半。共同调暗使非零 $E$ 的误差除以 $\|E\|$ 等于归一效果 $E/\|E\|$ 的误差，因而对全部切口及效果取上确界得第一式。第二式在固定 $E_*$ 两条路径应用相同的半迹范数界，并乘以 $2\sqrt j$ 即得。

联合边界失败时，对逐次缩小的半径及预算取正部大于固定 $\tau_0$ 的实际实现；其返回差本身即为正且超过 $\tau_0$。如定理 66.3 取严格递减子序列，再重排 (72.5)，得到 (72.9)。这是已有实际校准对象上的失败见证，不承诺一个有限程序取得全部切口预算。∎

## 73. 每条射线都准仍会漏掉集体相干异常

**命题 73.1（保留共同二元合同的全菜单反例）。** 若在新预算中以逐射线误差代替所有二元切口预算，则即使逐射线完整输出误差统一趋零、两个实际标定趋准、同一局部返回关系成立，整族平方根误差仍可恒为二。

证明。在完整有限复量子菜单中固定校准简单块阶 $d_0\ge3$，取偶数 $d_n>d_0$、$d_n\to\infty$，令 $c_n=(1-2/d_n)^2$。在每个阶恰为 $d_n$ 的简单块及所选框架上，选单位向量

$$
s_F=d_n^{-1/2}\sum_i|i\rangle,\qquad U_F=1-2|s_F\rangle\langle s_F|.
\tag{73.1}
$$

这里的单方向相位翻转是成熟构造，可视为 [Sanders–Wallman–Sanders，定义 6、命题 1](https://arxiv.org/pdf/1501.04932v3) 的一般受控相位门在 $\theta=\pi$ 时的酉共轭。为每个投影框架一次选定相容向量代表以定义 $s_F$；不另要求射线相位选择或框架改变下的协变性。对所有效果指定

$$
T^n_{E,F}(\rho)=
\begin{cases}
 U_F\sqrt E\,\rho\,\sqrt E U_F^*,&\text{块阶为 }d_n,\\
 c_n\mathcal L_E(\rho)+(1-c_n)\sum_i x_iP_i\rho P_i,
   &\text{其他块阶}.
\end{cases}
\tag{73.2}
$$

直和逐块处理。两种分支均完全正、成功效果为 $E$，共同调暗成立；以互补效果分支补成归一标签总过程，全部 C103 空间边和过程供应仍在完整菜单中。第一种分支的每个对角酉元均为 $1-2/d_n$，所以全部块、效果及框架的同一个压缩系数恰为

$$
m_n(x,y)=c_n\sqrt{xy}.
\tag{73.3}
$$

对异常块的每条框架射线，

$$
\begin{aligned}
\frac{\operatorname{Tr}[(1-P_i)T^n_{E,F}(P_i)]}{\|E\|}
 &\le1-c_n,\\
\frac{\|T^n_{E,F}(P_i)-x_iP_i\|_1}{\|E\|}
 &\le2\sqrt{1-c_n}\longrightarrow0.
\end{aligned}
\tag{73.4}
$$

其他块上的这些误差为零。校准块不是异常块，故 $\delta_n=1-c_n\to0$；该块的局部返回差为

$$
\kappa_n(h)=\frac{1-e^{-h}}4+
 \frac{c_n}{2}(1-e^{-h/2})\le h/2.
\tag{73.5}
$$

具体地，若以 $\rho_M=\sup_{E\ne0,F,i}\|T_{E,F}(P_i)-x_iP_i\|_1/\|E\|$ 及 $\delta$ 定义 $\eta_{\rm ray}=\max(\rho_M,\delta_M)$，本例有 $\eta_{\rm ray}\to0$，且按此预算分层的联合局部条件依然满足。

但是在异常块的 $E=1$ 上，取任意单位 $v\perp s_F$，$(s_F+v)/\sqrt2$ 经 $U_F$ 后与原态正交，故 $\mathfrak D(M_n)=2$。取含恰好一半位置的切口 $P$，

$$
\|(1-P)U_FP\|
 =2\|(1-P)s_F\|\|Ps_F\|=1.
\tag{73.6}
$$

所以真正的 $\lambda_{M_n}=1$。异常在每条细射线上都很浅，却在一个半边与另一个半边之间完全相干叠加。新预算正是在这一处排除该模型，而非靠改变共同 $m$ 或另加连续性排除它。∎

## 74. 具有真实射线串扰的完整稳定满足族

**命题 74.1（小幅重新准备的全族模型）。** 存在满足 C107 的完整通常有限量子比较类，包含零预算模型及趋近零预算的正预算模型；每个正预算模型都不满足原来的精确射线合同。

证明。对每个有限对象 $\mathcal A=\bigoplus_\alpha M_{d_\alpha}$，取 $D=\sum_\alpha d_\alpha$ 及 $\sigma_{\mathcal A}=1_{\mathcal A}/D$。令 $0\le p\le1$，定义

$$
T^p_{E,F}(\rho)=(1-p)\sqrt E\,\rho\,\sqrt E
 +p\operatorname{Tr}(E\rho)\sigma_{\mathcal A}.
\tag{74.1}
$$

这是两个相同成功效果的完全正分支的凸组合，故成功效果为 $E$，共同调暗及同一个 $m_p(x,y)=(1-p)\sqrt{xy}$ 成立。完整菜单供应每个分支及其标签补全；C103 的条件仍全部成立。这个重新准备项在多个中心块之间也会转移质量。对框架切口 $P$，其全部框架位置数为 $r$ 时，

$$
P(T^p_E)^*(1-P)P=p(1-r/D)PEP.
\tag{74.2}
$$

故 $\lambda_{M_p}\le p$。取已有任意大块、秩一 $P$ 及 $E=P$，该比值为 $p(1-1/d)$，于是 $\lambda_{M_p}=p$。同一输入上实际输出与平方根输出的迹距离为 $2p(1-1/d)$；另一方面两条成功分支之差的范数至多 $2p\|E\|$，故

$$
\mathfrak D(M_p)=2p,\qquad
\eta_{M_p}\ge p,\qquad
\delta_{M_p}\le2\sqrt3p.
\tag{74.3}
$$

这些上确界由有限块阶趋大来逼近，不主张某个有限阶取得极限。由 (72.3)，也可直接由相同效果的概率比较得到

$$
\mathfrak Q_{\mathscr C}(\varepsilon)\le2\varepsilon,
\qquad \chi_{\mathscr C}(r,\varepsilon)\le r/2+\varepsilon.
\tag{74.4}
$$

所以整个 $p\in[0,1]$ 类满足 C107，并有非平凡的正预算趋零族。$p>0$、总维数至少二时，$T_P(P)=(1-p)P+p\sigma_{\mathcal A}\ne P$，精确射线校准确实不成立。这说明新条件允许真实串扰，不是把精确前提改一个名字。∎

**命题 74.2（相同二元合同内的平方根尺度）。** 存在满足 C107 的完整比较类，使 $\eta_M=t$ 时恰有 $\mathfrak D(M)=2\sqrt t$，$0\le t\le1$。所以即使局部返回曲面有共同线性半径界，也不能只由这种预算期待 $o(\sqrt\eta)$ 的普遍更新界。

证明。固定校准块阶 $d_0\ge3$，令 $0\le\theta\le\pi/2$、$t=\sin^2\theta$。在所有二阶简单块的所选框架中取成熟的实旋转酉

$$
U_\theta=\begin{pmatrix}\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta\end{pmatrix},
\qquad T_{E,F}=\operatorname{Ad}_{U_\theta}\mathcal L_E.
\tag{74.5}
$$

其他块取 $(1-t)\mathcal L_E+t\mathcal P_{E,F}$，直和逐块处理，向量代表按命题 73.1 一次选定。全部实际菜单供应、成功效果、共同调暗及同一个 $m(x,y)=(1-t)\sqrt{xy}$ 均成立。二阶块的非平凡切口泄漏是 $t x_i$，其他块为零，所以 $\lambda=t$；固定校准块给 $\delta=t$ 及 $\kappa(h)\le h/2$，从而 $\eta=t$，整个类满足 C107。

二态酉的成熟距离公式给 $\|\operatorname{Ad}_{U_\theta}-\operatorname{id}\|_\diamond=2\sin\theta$，其半距离及特征相位对应见 Sanders–Wallman–Sanders 的式 (17)、例 2。复合 $\mathcal L_E$ 后的范数至多 $2\sin\theta\|E\|$；其他块误差至多 $2t\|E\|$，不超过前者。二阶块 $E=1$ 取得 $2\sin\theta$，故 $\mathfrak D=2\sqrt t$，并有 $\mathfrak Q(\varepsilon)=2\sqrt\varepsilon$ 对 $0\le\varepsilon\le1$ 成立。这个标度结论只约束由同一粗预算和共同局部界出发的普遍估计，不声称式 (72.4) 的全部常数最优。∎

## 75. 零预算量子层、有限顺序理论及独立条件

**定理 75.1（新候选接回现有量子公理的范围）。** 若比较类满足 C107，则其中每个 $\eta_M=0$ 的模型全部指定成功分支均为

$$
T_{E,F}(\rho)=\sqrt E\,\rho\,\sqrt E.
\tag{75.1}
$$

对一般模型，令 $B=\mathfrak Q_{\mathscr C}(\eta_M)$，则实际分支与平方根参照之差至多 $\|E\|B$。同一已有对象上的有限顺序复合、已供应准备与后续效果的联合概率、单分支成功后状态，分别满足定理 68.1 的式 (68.2)、$B/2$ 及 $\min(1,B/(2p_{\rm succ}))$ 界。一般总仪器结论仍要求其结果分支确实是这些指定分支，完整历史归一仍须使用该历史实际成功概率。

证明。零预算模型属于每个正预算子类，定理 72.2 给其误差为零。一般范数界由共同调暗和定义给出。定理 68.1 后续的有限复合证明只使用同一对象、相同效果及完全正映射范数，不再需要原来的精确射线前提，故可直接复用。Born 成功概率始终精确为 $\operatorname{Tr}(\rho E)$，因为成功效果从未放松。

因此对象的有限复矩阵直和、已供应空间边的张量乘法、允许确定过程的完全正性和共同相对标尺仍由 C101–C103 承担；本候选把指定测量更新接入一个允许射线串扰的极限理论。全部态、全部空间复合、任意一般仪器及具体 Hamiltonian 不由修复或范数估计供应；连续实际可逆群另行供应后才接入既有 Hamilton 表示。

两个独立边界仍须保留：命题 73.1 排除以逐射线合同代替全部切口预算；原命题 67.2 的高频字符族具有 $\lambda=0$、$\delta\to0$，却不满足 (70.6)，因此即使切口完全无泄漏，也不能删除局部联合边界约束。全部量被关系定义，不使这些关系约束自动成为其他前提的定理。∎

## 76. 关系的集体缺陷、成熟来源及白话定义

**定义 76.1（数学归属与内生边界）。** 逐射线的完整误差与全部二元切口的共同误差是两个不同量词，命题 73.1 在保留同一谱对系数、共同调暗及固定校准对象的完整菜单中给出区分。定理 71.1 将后者接到保持原二元关系的精确数学参照，定理 72.2 再将原实际局部返回边界接到全部指定更新的统一稳定性。这是当前新增的综合桥，不主张全球原创优先权或最优常数。

有限 Kraus、Stinespring 及 CP 范数工具沿用 §§51、60，差范数不等式明确复用 [Kretschmann–Schlingemann–Werner，命题 3](https://arxiv.org/pdf/0710.2495v1)。有限符号平均直接对应 [Han–Liu，*Zero-Error Correctibility and Phase Retrievability for Twirling Channels*，§2.2](https://arxiv.org/pdf/2311.16349v1) 的矩形群平均，表示对应已在定理 71.1 中给出；不将这个成熟投影方法认领为新内容。仓内[算术全息续卷 §72](ARITHMETIC_HOLOGRAPHIC_RT_II.md#72-exact-physical-calibration-reduction-for-collapsed-fibre-channels) 已用正确输出 Stinespring 记录及相位平均处理特定目标的精确校准归约；其资源保持最优化结论不提供 (71.1) 的切口预算。平均性能与最坏误差不能混同的成熟量子先例见 [Sanders–Wallman–Sanders，*Bounding quantum gate error rate based on reported average fidelity*](https://arxiv.org/pdf/1501.04932v3)；本处直接复用其单方向相位翻转机制，将异常块与其余块的 Schur 分支配成同一个 $m_n$，再给逐框架射线及集体切口的相反读数；不把相位门本身或平均性能的警示认领为新内容。

最新[有限带噪报告续卷定理 6.1](AURIC_COMPOSITE_COMPARISON_FINITE_NOISY_REPORTS_V96_CONTINUATION.md) 以完整实际残差而非逐坐标平均量承担另一种局部到整体控制；本处与其共享“共同实现中的完整缺陷才可组合”的方法对应，但不借用其曲率下界、Hilbert–Schmidt 报告或平方根证书。这里的有限符号平均控制算子范数，后续三点几何则复用 §§58–60；没有把任意有限正定性缩减成三阶正性，也没有从数学环境或修复映射产生新的实际供应。有限标定认证、取得全部切口预算、统计置信率和操作费用仍不在这些定理的结论中。

白话说：不要只问每根细光线有没有跑偏，还要把任意一组光线当成一边，问它们合起来会不会漏到另一边。每根看着都只漏一点，许多小漏也能同相叠成一次完整翻转。新候选把“任意两边的集体泄漏”“已有两条标定的偏差”和“几乎透明时实际返回概率突然下降的幅度”放在同一个关系体里一起约束。先用所有二元切口把串扰压进一个共同预算，数学上整理成保留原谱对关系的精确参照；再用三个方向的距离关系和比例二、三的标定网传到全部权重。三种偏差共同消失时，所有指定滤波就统一接近平方根更新；预算为零时得到精确量子更新。参照只帮助证明，不能凭它宣布现实多了一种准备、复合或运动。

## 追加锚（本行以下为增补区）

## 77. 不共用谱对系数的互逆滤波关系

**定义 77.1（同一对象上的实际分支、支撑与有限迹）。** 保留 C103 及定义 50.1 的全部效果、所选谱框架和实际成功分支供应。每个已有对象仍表示为 $\mathcal A=\bigoplus_\alpha M_{d_\alpha}(\mathbb C)$；$\tau=\sum_\alpha\operatorname{Tr}_\alpha$ 为各简单块通常矩阵迹之和。状态方向的指定分支 $T_{E,F}:\mathcal A\to\mathcal A$ 完全正，成功效果满足 $`T_{E,F}^*(1)=E`$；星号始终是相对于 $\tau$ 的数学伴随。相应实际标签补全及允许的有限接续沿用原供应。暂不要求射线校准、共同谱对系数、共同调暗、框架无关性、连续性、协变性或 $T_{1,F}=\operatorname{id}$。

对非零效果 $E$，在原代数内部定义

$$
P_E=\operatorname{supp}E,\qquad q_E=\min\bigl(\sigma(E)\setminus\{0\}\bigr),\qquad E^\vee=q_EE^\dagger,
\tag{77.1}
$$

其中 $E^\dagger$ 在正谱上取倒数、在零谱上取零；$E^\vee$ 仍是效果，支撑同为 $P_E$。$\mathcal C_E=P_E\mathcal A P_E$ 只是数学角，不另外声明它是已有对象或可执行压缩。$E$、$E^\vee$、$\sqrt E$、$aE$ 均沿用同一所选细谱框架 $F$；重根不要求另择基。下文省略 $F$ 时仍固定这个框架。

**定义 77.2（候选 C108：返回、互易与半程拼接）。** C108 是定义 77.1 的关系体中满足以下三个关系的指定族：

$$
\begin{aligned}
\mathrm R:\quad &T_{E^\vee,F}T_{E,F}(X)=q_EX &&(X\in\mathcal C_E),\\
\mathrm S:\quad &\tau\bigl(BT_{E,F}(A)\bigr)=\tau\bigl(AT_{E,F}(B)\bigr) &&(A,B\ge0),\\
\mathrm H:\quad &T_{E,F}=T_{\sqrt E,F}^{\,2}.&&
\end{aligned}
\tag{77.2}
$$

R 对非零效果施加，S、H 对全部效果施加。R 也可只写于 $\mathcal C_E$ 的正锥，再由线性延拓；S 等价于 $`T_{E,F}=T_{E,F}^*`$。它们是同一实际族的映射关系，不能用数学伴随或压缩参照代替 R 中实际供应的 $T_{E^\vee,F}$。正锥全称量词不等于全部态已经实际可制备；若只比较少量实际概率，就须另证它们足以分离这些映射。

R 比较滤波与倒数补偿这两个元的接续；S 比较同一分支两端准备—读出的对换；H 比较一条整程与两条相同半程。三个关系一并定义“互易可拆滤波”，并不预先给出平方根更新公式。下面先只保留 R，研究它留下的全部自由，再把 S、H 接入同一个三角恒等式。

## 78. 一次实际返回排除角外泄漏并推出共同调暗

**定理 78.1（实际互逆分支的支撑平衡与自由自同构）。** 定义 77.1 中若 R 成立，则对每个非零 $E$，存在 $\mathcal C_E$ 的保星自同构 $\alpha_{E,F}$，满足 $\alpha_{E,F}(E)=E$，并且

$$
\begin{aligned}
T_{E,F}(X)&=\sqrt E\,\alpha_{E,F}(P_EXP_E)\sqrt E,\\
T_{E,F}(1)&=T_{E,F}^*(1)=E,\\
T_{E,F}T_{E,F}^*(X)&=T_{E,F}^*T_{E,F}(X)=EXE.
\end{aligned}
\tag{78.1}
$$

特别地，分支既不读取支撑外的输入，也不向支撑外输出；它可在等谱子空间内移动射线，或置换角中等阶的中心块。对所有 $a>0$、$aE\le1$，同框架的共同调暗

$$
T_{aE,F}=aT_{E,F}
\tag{78.2}
$$

是后果而不是额外假设。这里不把保星自同构或其逆宣布为实际供应的过程。

证明。固定 $E,F$，写 $P=P_E$、$q=q_E$、$S=T_E$、$U=T_{E^\vee}$、$\mathcal C=P\mathcal A P$。有限完全正映射可以按输入、输出简单块取 Kraus 表示。$S^*(1)=E$、$U^*(1)=qE^\dagger$ 在 $1-P$ 上均为零，所以各 Kraus 算子右侧都有 $P$，即两映射都只读取 $PXP$。这一步只用成功效果，尚未排除向角外输出。

定义数学压缩 $A(X)=PS(X)P$、$B(X)=PU(X)P$，$X\in\mathcal C$。R 与输入支撑给 $BA=q\operatorname{id}_{\mathcal C}$。同一个有限维空间上的 $A$ 因而可逆，$A^{-1}=q^{-1}B$；两者均完全正。特别地，$A$ 将 $\mathcal C$ 的正锥双射到自身。

对任意 $X\ge0$，未压缩的 R 还给 $U(A(X))=qX$。由正锥满射性，$U$ 把整个 $\mathcal C$ 输出到 $\mathcal C$。在角内伴随的意义下于是有

$$
(A^{-1})^*(P)=q^{-1}(U|_{\mathcal C})^*(P)=E^{-1},
\tag{78.3}
$$

右侧逆只在 $\mathcal C$ 内取。

这里复用完全序同构的成熟结构：若 $A$ 及其逆完全正，置 $G=A(P)>0$，则 $\beta(X)=G^{-1/2}A(X)G^{-1/2}$ 为幺完全正双射，其逆也幺完全正。对 $\beta$ 及其逆使用 Schwarz 不等式，得到 $\beta(X^*X)=\beta(X)^*\beta(X)$；极化后 $\beta$ 是保星自同构。有限复矩阵直和的保星自同构只在同阶简单块之间置换并在块内酉共轭，故保留通常迹之和。由 $A=\operatorname{Ad}_{G^{1/2}}\beta$ 直接计算得

$$
(A^{-1})^*(P)=G^{-1}.
\tag{78.4}
$$

这是一条已知完全序同构工具的内部应用，不将该结构定理另计为新增内容。

式 (78.3)–(78.4) 给 $A(P)=E$。另一方面，角内有 $A^*(P)\le E$，且

$$
\tau\bigl(A^*(P)\bigr)=\tau\bigl(A(P)\bigr)=\tau(E).
\tag{78.5}
$$

有限迹忠实，故 $A^*(P)=E$。因此 $S^*(1-P)=0$；逐 Kraus 项的非负平方和为零，迫使各 Kraus 算子左侧也有 $P$。这才排除了 $S$ 的角外输出，原分支 $S$ 恰等于其角内压缩 $A$，而不是另造一个修复分支。

在 $G=E$ 的上述结构中取 $\alpha=\beta$。$A^*(P)=\alpha^{-1}(E)=E$，所以 $\alpha(E)=E$。它与 $E$ 的函数演算及相应左右乘法相容，且伴随等于 $\alpha^{-1}$，由此得到 (78.1)。同一 $E^\vee$ 对应全部 $aE$，而 $q_{aE}=aq$。R 分别给 $U T_{aE}=aq\operatorname{id}$ 和 $U T_E=q\operatorname{id}$；两分支都已在同一个角内，$U$ 在角内可逆，因此得 (78.2)。零效果的分支由 $T_0^*(1)=0$ 已为零。∎

**定理 78.2（返回关系不等于射线或中心不动）。** R 不迫使所选谱射线逐一保留，也不迫使原代数的中心块逐一不动，即使全部指定分支都满足 S。

证明。在完整通常有限量子菜单中，对每个投影效果 $E=P$，在角 $\mathcal C_P$ 中任选一个迹保持的对合保星自同构 $\alpha_P$，并对整条射线 $aP$ 选 $T_{aP}(X)=a\alpha_P(PXP)$；其余效果选平方根分支。此时 $(aP)^\vee=P$，$T_PT_{aP}=a\operatorname{id}$，故 R 成立；对合自同构的伴随等于自身，故 S 成立。可在某个 $M_3$ 对象的 $E=1$ 上取交换前两条射线的酉对合，或在 $M_2\oplus M_2$ 的 $E=1$ 上取两个简单块的互换，其余投影取恒等。平方根不改变正谱射线的分组，所以这给全部效果和全部所选框架的单一完整族。每个分支与互补效果的分支共同补成归一标签过程。两例分别移动谱射线和中心块；H 在这些例子的 $E=1$ 上失败。∎

## 79. 同一三角恒等式给出无维数因子的稳定性

**定义 79.1（精确返回层内的两个关系缺陷）。** 暂只保留定义 77.1 和精确 R。记 $\mathcal L_E(X)=\sqrt E X\sqrt E$，在原有限代数和任意数学矩阵参考上使用未除以二的任意输入 diamond 范数：

$$
\|\Phi\|_\diamond=\sup_{k\ge1}\sup_{Z\ne0}
\frac{\|(\Phi\otimes\operatorname{id}_{M_k})(Z)\|_1}{\|Z\|_1}.
\tag{79.1}
$$

这里 $\|\cdot\|_1$ 使用通常迹之和与参考矩阵迹；数学参考的全称量词不增加实际空间边。对 $E\ne0$ 定义

$$
\begin{aligned}
r(E,F)&=\frac{\|T_{E,F}-T_{E,F}^*\|_\diamond}{\|E\|},\\
h(E,F)&=\frac{\|T_{E,F}-T_{\sqrt E,F}^{\,2}\|_\diamond}{\|E\|},\\
d(E,F)&=\frac{\|T_{E,F}-\mathcal L_E\|_\diamond}{\|E\|}.
\end{aligned}
\tag{79.2}
$$

取全部已有对象、非零效果和所选框架的上确界 $R_0=\sup r$、$H_0=\sup h$、$D=\sup d$，并令 $\eta=\max(R_0,H_0)$。共同调暗已由定理 78.1 导出，所以按 $\|E\|$ 归一与取范数为一的效果等价。

**定理 79.2（实际半程、互易缺陷与整体更新的双向线性界）。** 在定义 79.1 的范围内，所有缺陷都不超过 $2$，并有

$$
\begin{aligned}
d(E,F)&\le h(E,F)+r(\sqrt E,F),\\
r(E,F)&\le2d(E,F),\\
h(E,F)&\le d(E,F)+2d(\sqrt E,F).
\end{aligned}
\tag{79.3}
$$

从而

$$
D\le\min(2,H_0+R_0)\le\min(2,2\eta),\qquad \eta\le3D.
\tag{79.4}
$$

这些常数不含维数、秩或最小正谱值。对任意允许关系体类及其零缺陷边界，统一 $\eta\to0$ 与统一 $D\to0$ 等价；精确 C108 迫使全部指定族为平方根更新，因而也迫使框架无关性。

证明。有限完全正映射满足成熟范数公式 $\|T\|_\diamond=\|T^*(1)\|$。定理 78.1 给 $T_E(1)=T_E^*(1)=E$，因此 $\|T_E\|_\diamond=\|T_E^*\|_\diamond=\|\mathcal L_E\|_\diamond=\|E\|$。对 $A=\sqrt E$、$S=T_A$，同一定理给

$$
SS^*=\mathcal L_E,\qquad \|S\|_\diamond=\|A\|,\qquad (S^2)^*(1)=E.
\tag{79.5}
$$

最后一式由 $\alpha_A(A)=A$ 和 $S=\mathcal L_A\alpha_A$ 得到，故 $h$ 也不超过 $2$。现在在同一原代数的映射空间内，直接展开

$$
T_E-\mathcal L_E=(T_E-S^2)+S(S-S^*).
\tag{79.6}
$$

组合范数的次乘性与 $\|A\|^2=\|E\|$ 给 (79.3) 第一式。这三条边分别是实际整程到两个实际半程、半程到其数学伴随、以及两者合成后的平方根参照；参照只在证明中出现。

写 $T_E=\mathcal L_E\alpha_E$。因 $\alpha_E$ 保留 $E$，在支撑角内有

$$
T_E^*-\mathcal L_E=-\alpha_E^{-1}(T_E-\mathcal L_E).
\tag{79.7}
$$

保星自同构及其逆在所有矩阵参考上都是迹范数等距；角的包含也完全等距。故 (79.7) 两端的 diamond 距离相等，三角不等式给第二式。最后令 $L=\mathcal L_A$，使用

$$
S^2-L^2=(S-L)S+L(S-L),\qquad L^2=\mathcal L_E,
\tag{79.8}
$$

得到 $\|S^2-\mathcal L_E\|_\diamond\le2\|E\|d(A)$，即第三式。取上确界即得 (79.4)。未对 $q_E$ 作下界；其倒数只在精确代数可逆性的证明中使用，没有进入误差界。∎

**定理 79.3（三维谱角的有限提升与一般角的区别）。** 在精确 C108 中，若 $Q$ 是已有简单块内由 $E$ 的同一所选框架取出的三射线投影，则对 $X\in Q\mathcal A Q$ 有

$$
QT_E(X)Q=\sqrt{QEQ}\,X\sqrt{QEQ}.
\tag{79.9}
$$

对一般三维投影 $Q$，结论只是 $QT_E(X)Q=(Q\sqrt E Q)X(Q\sqrt E Q)$，不将它等同于效果 $QEQ$ 的平方根更新。有限接续的一般角压缩须按原完整路径先组合再压缩。仅检查三维角，不是整体 diamond 界的替代前提。

证明。定理 79.2 已在原完整代数上得到 $T_E=\mathcal L_E$。谱角中 $Q$ 与 $E$ 对易，$Q\sqrt E Q=\sqrt{QEQ}$，给 (79.9)；一般角直接插入 $X=QXQ$ 得所列压缩式。谱基下 (79.9) 把每个矩阵元 $X_{ij}$ 乘以 $\sqrt{x_ix_j}$，即三个方向中每一对关系的共同提升；任意中途压缩仍不是免费实际操作。式 (79.1)–(79.4) 的假设包括全部角和全部参考输入，未由三维读数恢复这些全称量词，也未产生三维角的实际对象供应。∎

## 80. 删除任一关系都会保留非量子更新

**定理 80.1（返回、互易、半程各有完整反模型）。** 从 C108 删除 R、S、H 中任一项，都存在保留其他两项和全部原供应的完整通常有限量子菜单，其指定更新不是平方根族。

证明。以下均取全部有限复矩阵直和、全部态与效果、全部完全正迹不增分支、相应标签总过程和全部标准空间复合。因此 C101–C103 成立；所选分支按下列统一规则供应于每个对象、每个效果与每个框架，互补分支使标签总映射保迹。

删除 R。令 $\Pi_E$ 是按 $E$ 的不同谱值子空间进行的 pinching，取 $T_E=\mathcal L_E\Pi_E$。谱投影自伴、相互正交，故完全正、成功效果为 $E$，且 S 成立。$E$ 与 $\sqrt E$ 的谱子空间相同，$\Pi_E^2=\Pi_E$，所以 H 成立。对 $E=\operatorname{diag}(1,1/4)$，倒数补偿仍按同一两个谱空间 pinching，$T_{E^\vee}T_E=(1/4)\Pi_E$，不能返回非零非对角矩阵。因此 R 失败。

删除 S。固定实数 $u\ne0$，取成熟的模相位族

$$
T_E^{(u)}(X)=E^{1/2+iu}X E^{1/2-iu},
\tag{80.1}
$$

零谱的相应列定义为零。成功效果为 $E$，$E^\vee$ 与 $E$ 的正谱乘积是 $q_E$，故两个 Kraus 算子相乘为 $q_E^{1/2+iu}P_E$，R 成立。对半根效果的 Kraus 算子平方恰等于原 Kraus 算子，故 H 成立。选择 $E=\operatorname{diag}(1,\exp(-\pi/(2|u|)))$，非对角系数具有非实相位，所以 S 失败且不是平方根更新。此模相位机制沿用 Liu–Wu，式 (80.1) 只作为反模型中间构造，不认领为新增理论。

删除 H。在每个二维简单块上，若 $E$ 满秩且有两个不同谱值 $x>y>0$，定义

$$
J_E=P_x-P_y,\qquad T_E=\operatorname{Ad}_{J_E\sqrt E};
\tag{80.2}
$$

二维标量效果、秩一效果、零效果以及其他阶的简单块一律选平方根分支；直和逐块按此规则处理。所有 Kraus 算子自伴，故 S 成立。倒数补偿把两个谱值的大小对换，$J_{E^\vee}=-J_E$；其共同系数 $q_E$ 可以由别的中心块决定，但两谱比和大小对换不变，负号只给无关块相位，故 R 仍成立。对任一上述非标量二维块，$J_{\sqrt E}=J_E$，半程平方的共轭算子为 $E^{1/2}$，所以 $T_{\sqrt E}^2=\mathcal L_E$，而 $T_E\ne\mathcal L_E$。因此 H 失败。三种规则均无需在谱简并处假设连续性。∎

## 81. 真正越出共同谱核的正误差满足族

**定理 81.1（低权重相位翻转的完整线性稳定族）。** 对每个 $0\le t<1$，存在定义 79.1 的完整满足模型 $M_t$，其精确 R、S 均成立，并且

$$
D(M_t)=H_0(M_t)=\eta(M_t)=2t,\qquad R_0(M_t)=0.
\tag{81.1}
$$

对 $t>0$，这个模型没有适用于全部对象和旁观谱的同一二元系数 $m(x,y)$，因此不属于 C104–C107 的共同谱核前提。它表明定理 79.2 适用范围确已扩大，并给任何统一界 $D\le c\eta$ 的必要条件 $c\ge1$；不声称 (79.4) 中常数 $2$ 最优。

证明。保留定理 80.1 的完整通常有限量子菜单。在每个二维简单块上，仅当效果满秩、非标量且谱比 $y/x\le t^2$ 时采用 (80.2)，其他情形全部选平方根分支；直和逐块处理，所有框架使用同一规则。倒数补偿保持谱比，故异常块仍彼此配对，定理 80.1 的证明给精确 R 和 S。每个所选半程的酉相位都是对合，所以在所有块上 $T_{\sqrt E}^2=\mathcal L_E$，无论 $E$ 与 $\sqrt E$ 是否同时越过阈值。因此 $h(E)=d(E)$。

在异常二维块的谱基中，$T_E-\mathcal L_E$ 只把两个非对角角块乘以 $-2\sqrt{xy}$。设 $Z=\operatorname{diag}(1,-1)$，则此差映射为

$$
T_E-\mathcal L_E=\sqrt{xy}\,(\operatorname{Ad}_Z-\operatorname{id}).
\tag{81.2}
$$

两个通道的 diamond 距离不超过 $2$；输入 $|+\rangle\langle+|$ 的两输出正交，故距离恰为 $2$。从而异常块上的归一误差是 $2\sqrt{y/x}\le2t$。直和映射的 diamond 范数取各块最大值：上界由输入直和迹范数逐块相加，下界由单块输入取得；再按整个 $\|E\|$ 归一，仍不超过 $2t$。当 $t>0$ 时，效果 $\operatorname{diag}(1,t^2)$ 取得等号。$t=0$ 时无异常块，全族为平方根更新，得 (81.1)。

对 $t>0$，在 $M_2$ 的权重对 $(1,t^2)$ 上，压缩非对角系数为 $-t$；在已有 $M_3$ 的效果 $\operatorname{diag}(1,t^2,0)$ 上，因异常规则仅作用于二维简单块，这个三维块采用平方根分支，相同两权重的系数为 $+t$。全菜单确实供应两对象和两效果，故不存在一个跨对象与旁观谱的 $m(1,t^2)$ 同时给这两个值。虽然族在阈值处可不连续，它的统一整体误差仍随 $t\downarrow0$ 线性趋零。∎

## 82. 从新关系接回 Born、投影、顺序概率及运动

**定理 82.1（C108 的完整标准满足模型和有限量子接续）。** 完整通常有限复量子理论在全部效果上指定 $T_E=\mathcal L_E$，满足 C108。在任一 C108 模型中，对已经供应的态 $\rho$、后续效果 $B$ 和同一对象上的有限指定滤波序列，分别有

$$
\begin{aligned}
p(E\mid\rho)&=\tau(\rho E),\\
p(E\text{ 后 }B\mid\rho)&=\tau\bigl(B\sqrt E\rho\sqrt E\bigr),\\
\rho_E&=\frac{\sqrt E\rho\sqrt E}{\tau(\rho E)}\quad\bigl(\tau(\rho E)>0\bigr),\\
T_{E_n}\cdots T_{E_1}(\rho)&=K\rho K^*,\qquad K=\sqrt{E_n}\cdots\sqrt{E_1}.
\end{aligned}
\tag{82.1}
$$

效果为投影时得到 Lüders 投影更新。对精确 R 但 $\eta>0$ 的模型，置 $b=\min(2,2\eta)$，则 $\|T_E-\mathcal L_E\|_\diamond\le\|E\|b$；同一成功效果的联合概率误差至多 $\|E\|b/2$，成功概率 $p(E\mid\rho)>0$ 时，成功后态的迹距离至多 $\min(1,\|E\|b/(2p(E\mid\rho)))$。对任意非零效果组成的给定有限序列，未归一映射误差至多

$$
\left(\prod_{i=1}^n\|E_i\|\right)\sum_{i=1}^n d(E_i,F_i).
\tag{82.2}
$$

证明。标准模型中两个倒数滤波的 Kraus 算子相乘为 $\sqrt{q_E}P_E$，S 由迹循环性给出，H 由同一正平方根相乘给出；全部供应按定理 49.1。一般模型的精确公式由定理 79.2 得到。任意亏损下，成功效果仍精确为 $E$，故 Born 成功概率不含误差。

差输出 $\Delta=(T_E-\mathcal L_E)(\rho)$ 自伴且迹为零，$\|\Delta\|_1\le\|E\|b$。正、负部各有至多 $\|E\|b/2$ 的迹，故 $|\tau(B\Delta)|\le\|E\|b/2$；相同成功概率下归一化后再除以二，得到上述迹距离。有限接续对每一位置作望远镜展开，使用 $\|T_{E_i}\|_\diamond=\|\mathcal L_{E_i}\|_\diamond=\|E_i\|$，即得 (82.2)。若序列含零效果，则实际序列与平方根序列映射都为零，单独处理而不使用未定义的 $d(0,F)$。完整历史归一仍按该历史实际成功概率处理，不用首步成功率代替。

现有量子公理的接续分工是：C101 给已有对象的有限经典／复矩阵直和表示与实际空间边的张量乘法；C102 给实际确定过程的完全正性和已供应标签总过程的仪器表示；C103 给活动对象的共同相对标尺；C108 在这些前提上唯一选出指定滤波的平方根更新。若另供全部正归一态，则原有态表示与效果评价给通常密度矩阵—Born 形式；若另供同一对象上的连续一参数实际可逆群，则原有表示给 Hamilton 形式，仍不选择具体 Hamiltonian。

逐个滤波和互补标签供应不产生任意 POVM 的共同总过程。若该总过程另已供应且各分支指定为本族、效果满足 $\sum_uE_u=1$，则它才是 $\rho\mapsto\bigoplus_u\sqrt{E_u}\rho\sqrt{E_u}$。全部态、全部空间复合、一般仪器、普遍参考、经验时间单位和唯一整体态均不由 (77.2) 自动供应。式 (79.4) 只允许 S、H 带误差；R 在这里始终精确。$q_E\downarrow0$ 时返回路径的成功率可以趋零，所以本定理没有给出有限认证程序、统计置信率或统一操作费用。∎

## 83. 关系闭合的成熟先例与白话定义

**定义 83.1（与既有序贯乘积的对应及新增边界）。** [Gudder–Latrémolière，*Characterization of the sequential product on quantum effects*，定义 3.1、定理 3.3](https://arxiv.org/pdf/0803.3867v1) 已以迹自对偶、双侧单位、平方拼接、强连续性及纯态保持刻画平方根序贯乘积；[van de Wetering，*Three characterisations of the sequential product*，定理 5.14](https://arxiv.org/pdf/1803.08453v1) 在 Hilbert sequential effect space 的完整公理下给无连续性版本。其效果方向的乘积 $a\circ b$ 对应这里 $`T_a^*(b)`$；在本节 S 成立后才可同写为 $T_a(b)$。本节 S 对应对称性，H 对应平方拼接。本节中“对称加平方排除自同构扭转”的精确选择机制属于这些成熟先例，不作为独立新结果。完全序同构的幺化、Schwarz 等号及完全正范数公式也只作为证明中的成熟工具。

本批承重综合是：以成功效果和同一实际倒数分支的一侧返回，先在原代数内部证明支撑双向无泄漏、通常迹平衡和共同调暗，再在这个精确返回层上把 S、H 的两个任意输入 diamond 缺陷与全部指定更新的整体误差建立 (79.3)–(79.4) 的无维数双向线性关系。没有预设完整 sequential effect space 的相容交换公理、全部纯映射或通用角—压缩性质。定理 81.1 给一个没有共同谱对系数但仍线性稳定的全菜单满足族，因而不是对 C104–C107 改记号。文献对应不等于原创优先权结论。

这里的内生含义是：效果定义成功概率，实际反向分支定义可返回性，两端迹配对定义互易，同一过程的半程接续定义可拆性，更新公式由这些关系共同决定。把所有元放进 $\Omega$ 不会使三个兼容关系自动成立；定理 80.1 恰说明它们各排除了不同的实际自由。三维角可展示整体关系的有限图景，不能代替原全量词。由精确 R 到近似 R 的统一无条件数理论仍未在这些定理中建立。

白话说：让一束光经过有深有浅的滤片，再接一块按原深浅倒过来补偿的滤片；如果所有还能通过的细节都能完整回来，第一块就不能偷偷把信息倒进别处，它只能在留下来的空间里做一个可逆转动。再要求把“送入什么、读出什么”两端交换后关系相同，并且一块滤片与两块相同的半深滤片接起来相同，这个额外转动就被三条关系一起排除了。留下的规则是：每个方向的振幅乘透过率的平方根，概率才乘透过率。两端互易和半程拼接只差一点时，整个更新也只差一个共同的线性预算；这个预算不随方向数量或最暗透过率恶化，但完整返回这条关系仍须精确。

## 追加锚（本行以下为增补区）

## 84. 以统一返回余量代替精确返回

**定义 84.1（互易、半程与归一化输出返回）。** 沿用定义 77.1 的全部有限对象、所选框架、实际成功分支与有限接续供应，仍用通常迹之和 $\tau$。本节只保留精确 S、H，不先假设 R。对非零效果 $E$，写 $P=P_E$、$q=q_E$、$E^\vee=qE^\dagger$、$\mathcal C=P\mathcal AP$。定义

$$
\begin{aligned}
\beta(E,F)&=\sup_{\rho\in\mathcal C,\ \rho\ge0,\ \tau(\rho)=1}
 \bigl\|q^{-1}T_{E^\vee,F}T_{E,F}(\rho)-\rho\bigr\|_1,\\
d(E,F)&=\frac{\|T_{E,F}-\mathcal L_E\|_\diamond}{\|E\|},
\qquad \beta_* =\sup_{E\ne0,F}\beta(E,F),\qquad D=\sup_{E\ne0,F}d(E,F).
\end{aligned}
\tag{84.1}
$$

上确界跨全部已有对象；$\mathcal L_E$ 和未除以二的任意输入 diamond 范数仍按定义 79.1 的公式。$\rho$ 是数学正锥中的归一元，$\beta$ 不含参考系统。它比较原实际分支及原实际补偿分支的完整输出；除以 $q$ 是比较规则，不另外供应一个可执行的放大过程。正锥全称量词也不供应全部实际准备、层析或误差证书。

候选 C109 定义为 S、H 及一个统一关系

$$
\mathrm U:\qquad \exists c\in[0,1)\quad
 \forall E\ne0,F,\qquad \beta(E,F)\le c.
\tag{84.2}
$$

因此 U 是滤波与实际倒数补偿这两个元之间的输出约束，并由同一半程接续关系在不同效果间联结。它不把平方根公式写入定义，也不把每个效果各有一个小于一的界误写成统一的 $c$。

## 85. 互易与半程留下的全部耗散

**定理 85.1（支撑内的对称正收缩与返回计数）。** 在定义 84.1 的供应及 S、H 下，对每个非零效果，存在唯一的完全正映射 $\Phi_{E,F}:\mathcal C_E\to\mathcal C_E$，满足

$$
\begin{gathered}
T_{E,F}=\mathcal L_E\Phi_{E,F},\qquad
\Phi_{E,F}(P_E)=\Phi_{E,F}^*(P_E)=P_E,\qquad
\Phi_{E,F}=\Phi_{E,F}^*,\\
0\le\Phi_{E,F}\le\operatorname{id}\quad\text{在 Hilbert--Schmidt 算子序中},\qquad
\Phi_{E^2,F}=\Phi_{E,F}^{\,2},\\
q_E^{-1}T_{E^\vee,F}T_{E,F}|_{\mathcal C_E}
 =\Phi_{E^\vee,F}\Phi_{E,F}.
\end{gathered}
\tag{85.1}
$$

这里第一行在原代数上由支撑压缩延拓；两个 $\Phi$ 均只是数学分解，不声明为实际过程。原分支不读取支撑外输入，也不向支撑外输出。即使 R 不成立，全部正输入 $\rho\in\mathcal C_E$ 仍有

$$
\tau\bigl(T_{E^\vee,F}T_{E,F}(\rho)\bigr)=q_E\tau(\rho).
\tag{85.2}
$$

证明。省略框架。成功效果给输入支撑；S 又给 $T_E(1)=E$。对正输入 $X$，$\tau((1-P)T_E(X))=\tau(T_E(1-P)X)=0$，故输出也在角内。H 用于效果 $E^2$，给 $T_{E^2}=T_E^2$；取成功效果并用 S，得 $T_E(E)=E^2$。

把各输入、输出简单块的 Kraus 算子填入 $\bigoplus_\alpha\mathbb C^{d_\alpha}$ 上的矩阵 $K_j$。成功效果与 S 分别给 $\sum_jK_j^*K_j=\sum_jK_jK_j^*=E$。因此

$$
\sum_j\|EK_j-K_jE\|_2^2
 =2\tau(E^3)-2\tau\bigl(E T_E(E)\bigr)=0.
\tag{85.3}
$$

每项非负，故 $EK_j=K_jE$；这包括不同中心块之间的 Kraus 算子，只允许相同数值谱的交织，不预设中心块逐一不动。置 $L_j=E^{-1/2}K_j$，逆只在支撑取。则 $\sum_jL_j^*L_j=\sum_jL_jL_j^*=P$，给所需双随机完全正映射 $\Phi_E$。所有 $L_j$ 与 $E$ 对易，故 $\Phi_E$ 与 $\mathcal L_E$ 对易。角内 $\mathcal L_E$ 可逆，S 推出 $\Phi_E=\Phi_E^*$，也给唯一性。

对 $A=\sqrt E$ 做同一分解，H 及函数演算相容性给 $\Phi_E=\Phi_A^2$。所以 $\Phi_E$ 在 Hilbert--Schmidt 空间上半正定；双随机完全正映射由 Schwarz 不等式和迹保持而为 Hilbert--Schmidt 收缩，故其谱在 $[0,1]$。同理得到 $\Phi_{E^2}=\Phi_E^2$。$E^\vee$ 与 $E$ 在支撑内互为正标量倍的逆，其 Kraus 交织也与 $E$ 对易；$\mathcal L_{E^\vee}\mathcal L_E=q\operatorname{id}_{\mathcal C}$，得到 (85.1) 最后一式。两 $\Phi$ 都保迹，故得 (85.2)。∎

## 86. 不带参考的返回误差控制完整参考更新

**定理 86.1（对称耗散的无维数局部界）。** 在定理 85.1 的全部范围内，包括允许中心间转移的有限直和，有

$$
d(E,F)\le\min\{2,10\beta(E,F)\},\qquad
D\le\min\{2,10\beta_*\}.
\tag{86.1}
$$

这里结论的 diamond 范数包含全部数学矩阵参考，前提的 $\beta$ 仍只比较不带参考的正输入；常数不含维数、秩或 $q_E^{-1}$，不宣称常数十最优。

证明。写 $\Phi=\Phi_E$、$\Psi=\Phi_{E^\vee}$、$\delta=\beta(E,F)$。由正、负部分解，$\|\Psi\Phi(X)-X\|_1\le\delta\|X\|_1$ 对全部自伴 $X\in\mathcal C$ 成立。若 $\Phi(X)=\lambda X$、$X=X^*\ne0$，则 $0\le\lambda\le1$，且 $\Psi$ 的迹范数收缩性给

$$
\delta\|X\|_1\ge\|X-\lambda\Psi(X)\|_1
 \ge(1-\lambda)\|X\|_1.
\tag{86.2}
$$

$\Phi$ 保星且自伴，每个特征空间都有自伴实基，所以 $\Phi\ge(1-\delta)\operatorname{id}$ 在 Hilbert--Schmidt 算子序中成立。以下把这个特殊谱下界转成 diamond 界，不使用一般维数相关的范数换算。

把 $\mathcal C=\bigoplus_\alpha M_{r_\alpha}$ 嵌入 $B(H)$，令 $C$ 为中心块 pinching。数学延拓 $\widehat\Phi=\Phi C$ 是双随机、自伴完全正映射。它有 Hermitian Kraus 算子 $h_j$，$\sum_jh_j^2=I_H$：把任意 Kraus 表示与其伴随表示平均，再将每对 $`K,K^*`$ 换成 $`(K+K^*)/2`$ 与 $`(K-K^*)/(2i)`$。这里使用的逐项恒等式是

$$
\operatorname{Re}K\,X\operatorname{Re}K+\operatorname{Im}K\,X\operatorname{Im}K
=\tfrac12(KXK^*+K^*XK).
$$

对任何位于一个中心块的单位向量 $\psi$，记 $p_\psi=|\psi\rangle\langle\psi|$，谱下界给

$$
\sum_j\operatorname{Var}_\psi(h_j)
 =1-\tau\bigl(p_\psi\Phi(p_\psi)\bigr)\le\delta.
\tag{86.3}
$$

在每个中心块任选一个单位向量 $e_\alpha$，置 $c_{j,\alpha}=\langle e_\alpha,h_je_\alpha\rangle$，$c_j=\bigoplus_\alpha c_{j,\alpha}I_\alpha$、$\ell_j=h_j-c_j$。对任意实单位系数向量 $u$，Cauchy--Schwarz 给 $\operatorname{Var}_\psi(\sum_ju_jh_j)\le\delta$，其中心块压缩的方差也不超过此值。测试压缩矩阵最大、最小特征向量的等权叠加，得谱直径至多 $2\sqrt\delta$。于是对同一块中的 $\psi$，对 $u$ 取上确界得到

$$
\sum_j\bigl(\langle\psi,h_j\psi\rangle-c_{j,\alpha}\bigr)^2\le4\delta,
\qquad
\sum_j\|\ell_j\psi\|^2\le5\delta.
\tag{86.4}
$$

因此 $Q=C(\sum_j\ell_j^2)\le5\delta I_H$。在原直和代数上置 $K(X)=C(\sum_j\ell_jX\ell_j)$，它完全正，$K^*(I_H)=Q$。直接展开，得到

$$
\operatorname{id}-\Phi=\tfrac12\{Q,\cdot\}-K.
\tag{86.5}
$$

具体地，记 $A_\alpha=\sum_jc_{j,\alpha}(h_j)_{\alpha\alpha}$、$b_\alpha=\sum_jc_{j,\alpha}^2$，则

$$
Q_\alpha=I_\alpha-2A_\alpha+b_\alpha I_\alpha,\qquad
K(X)_\alpha=\Phi(X)_\alpha-\{A_\alpha,X_\alpha\}+b_\alpha X_\alpha.
$$

同一个交叉项在反对易式中抵消；不同中心块的 $h_j$ 分量仍留在 $K$ 和 $Q$ 中，未将它们删去。完全正范数公式与任意参考上的左右乘法界给 $\|\operatorname{id}-\Phi\|_\diamond\le2\|Q\|\le10\delta$；两个通道的距离又至多二。最后 $T_E-\mathcal L_E=\mathcal L_E(\Phi_E-\operatorname{id})$，而 $\|\mathcal L_E\|_\diamond=\|E\|$，即得 (86.1)。这里复用《AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY》定理 40.1 中的居中 Hermitian Kraus 恒等式和完全正范数工具；新增估计是 (86.3)–(86.4) 的全向量方差控制，取代固定维数的迹上界。∎

## 87. 统一小于一的余量产生精确更新

**定理 87.1（有限平方见证与锐阈值的一侧）。** 在定义 84.1 的范围内，下列条件等价：C109；全部指定更新为 $\mathcal L_E$；$\beta_*=0$。更具体地，若某个 $\Phi_{E,F}\ne\operatorname{id}$，则有自伴特征元 $X\ne0$ 及 $0\le\lambda<1$，使同框架的每个有限层级 $E_n=E^{2^n}$ 满足

$$
\beta(E_n,F)\ge1-\lambda^{2^n}.
\tag{87.1}
$$

对每个 $c<1$，因此存在有限 $n$，并存在 $\mathcal C_E$ 中一个纯态，使该层级的归一化返回误差严格大于 $c$。这里的纯态是一个中心块内的秩一正归一元，不保证为实际可准备态。前述三个等价条件也等价于逐条平方链的较弱形式

$$
\forall E\ne0,F,\qquad
\liminf_{n\to\infty}\beta(E^{2^n},F)<1.
\tag{87.2}
$$

每条链可以各有余量，不要求不同对象、效果或框架共用同一个数。

证明。定理 85.1 给自伴正收缩 $\Phi_E$；非恒等时必有上述特征元。平方链支撑不变，$\Phi_{E_n}=\Phi_E^{2^n}$。其实际补偿分支给 $\Phi_{E_n^\vee}$，它仍为迹范数收缩。把 (86.2) 用于同一 $X$，即得 (87.1)。当 $0\le\lambda<1$ 时，$\lambda^{2^n}\to0$；故对任意 $c<1$，取有限 $n$ 使 $\lambda^{2^n}<1-c$ 即得越界；$\lambda=0$ 时 $n=0$ 已足够。若两个正负部归一态的误差都不超过 $c$，其线性组合会使 $X$ 的误差也不超过 $c\|X\|_1$，矛盾。再把越界正归一元作有限纯态分解，凸性迫使至少一个纯态也越界。故 U 排除所有非恒等 $\Phi_E$，得到全部平方根分支及精确 R。反方向由定理 82.1 的标准公式直接给出。若只给 (87.2)，任何非标准链仍由 (87.1) 得下极限至少一，矛盾；标准族的下极限全为零，证明新增等价形式。对已得到的越界纯态 $\rho$，归一化返回残差自伴且迹为零，取其正谱投影 $B$，还得到有限二元读出见证

$$
\left|\tau\bigl(BT_{E_n^\vee,F}T_{E_n,F}(\rho)\bigr)
-q_E^{2^n}\tau(B\rho)\right|>\tfrac12q_E^{2^n}c.
\tag{87.3}
$$

它不供应实际准备或读出，也不把可能随 $n$ 急剧缩小的原始概率差说成统一可取得的预算。∎

## 88. 阈值、逐点量词与有限检验的完整反模型

**定理 88.1（阈值一可达，逐点小于一仍不足）。** 存在完整通常有限量子菜单上的指定族，满足精确 S、H、$T_1=\operatorname{id}$ 及全部投影分支标准，但 $D=\beta_*=1$。另有这样的非标准族，对每个非零效果均有 $\beta(E,F)<1$，而 $D=\beta_*=1$。任何固定有限个效果及其固定有限平方层级，都可在后一类模型中使返回误差任意小，却仍有 $D=1$。

证明。取定理 80.1 的完整通常有限量子菜单，只改变二维交换对象 $\mathbb C\oplus\mathbb C$ 上的分支；不把它与简单块 $M_2$ 混同。令 $J=\frac12\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)$ 作用于两坐标。对有限参数 $a>0$，在 $0<t<1$ 的标量效果上定义

$$
T_{t1}=t\bigl[J+t^a(\operatorname{id}-J)\bigr],\qquad
T_1=\operatorname{id},\qquad T_0=0.
\tag{88.1}
$$

不等坐标效果一律采用逐坐标标准乘法，其他全部对象和框架采用平方根分支。$J$ 是对称双随机投影，$J+t^a(\operatorname{id}-J)$ 是它与恒等的凸组合，因此完全正且有正确成功效果。$J^2=J$ 给半根分支的平方恰为 (88.1)，S、H 成立。对标量效果，$E^\vee=1$，而在交换两点代数上 $\|J-\operatorname{id}\|_\diamond=1$，可由两列绝对和以及单点输入直接求得。因此

$$
d(t1,F)=\beta(t1,F)=1-t^a;
\tag{88.2}
$$

其他效果的两缺陷为零。每个 $t>0$ 的误差严格小于一，而 $t\downarrow0$ 时趋一，得到逐点反模型。把全部 $0<t<1$ 上的 $t^a$ 直接换成零，仍保留 S、H，但每个此类标量效果的缺陷都恰为一，给阈值可达模型。两构造的投影效果只有坐标投影、零和一，均为标准分支。

对任一固定有限测试表，其中非零误差项只来自有限个 $t_j\in(0,1)$。包含平方层级 $n\le N$ 后，误差是 $1-t_j^{a2^n}$；有限个这样的数随 $a\downarrow0$ 同时趋零。任意 $a>0$ 的全菜单上确界仍为一。这只排除以这些有限指定效果的精确误差代替 U 的做法，不宣称否定所有附加先验下的有限认证。全部指定分支及其互补效果分支属于原全 CP 菜单，标签总映射保迹，故模型完整。∎

## 89. 暗的第三方向为何掩盖返回误差

**定理 89.1（未按成功率归一的误差没有统一更新模量）。** 仅有 S、H 时，即使全部投影分支和 $T_1$ 标准，也存在完整满足族 $M_s$，$s>0$，使

$$
\sup_{E\ne0,F}
\frac{\|T_{E^\vee,F}T_{E,F}|_{\mathcal C_E}-q_E\operatorname{id}_{\mathcal C_E}\|_\diamond}{\|E\|}
\le\frac{4s}{\mathrm e},\qquad D(M_s)=2.
\tag{89.1}
$$

三维简单对象已经能在前项一致趋零时保留趋一的输出误差；达到上确界二的结论允许维数增长。

证明。在每个非零效果的支撑内置 $\kappa(E)=\|E\|/q_E$，令

$$
\mathcal D_E(X)=\bigoplus_\alpha\sum_{\lambda>0}
\frac{\operatorname{Tr}(P_{\alpha,\lambda}X_\alpha)}{\operatorname{rank}P_{\alpha,\lambda}}P_{\alpha,\lambda},
\qquad
T_E^{(s)}=\mathcal L_E\bigl[\kappa(E)^{-s}\operatorname{id}
 +(1-\kappa(E)^{-s})\mathcal D_E\bigr].
\tag{89.2}
$$

支撑外压缩，零效果取零。$\mathcal D_E$ 是支撑角上的保迹、自伴完全正投影，与 $\mathcal L_E$ 对易；逐个原中心块、逐个不同正谱空间平均，不另供实际操作。平方根、正平方和倒数补偿保留这些谱空间；$\kappa(\sqrt E)=\sqrt{\kappa(E)}$、$\kappa(E^\vee)=\kappa(E)$。所以各实际分支有正确成功效果，S、H 精确成立，且

$$
q_E^{-1}T_{E^\vee}^{(s)}T_E^{(s)}
=\kappa^{-2s}\operatorname{id}+(1-\kappa^{-2s})\mathcal D_E.
\tag{89.3}
$$

两个通道的 diamond 距离至多二，故 (89.1) 左端单项至多
$2\kappa^{-1}(1-\kappa^{-2s})\le4s\log(\kappa)/\kappa\le4s/\mathrm e$。

在 $M_3$ 中取 $E=\operatorname{diag}(1,1,q)$，$0<q<1$。任一前二维空间中的纯输入，被 $\mathcal D_E$ 变成 $I_2/2$；实际更新与标准更新的迹范数差为 $1-q^s$。例如沿 $s\downarrow0$ 取 $q=\exp(-1/s^2)$，这个差趋一，同时未归一返回误差仍服从 (89.1)。这是同一三维对象中两个明亮方向的关系，被第三个暗方向决定的全局返回成功率遮蔽，未改变成功效果或成功计数。

在 $M_m\oplus\mathbb C$ 中取 $E=(I_m,q)$，纯输入位于首块，差为 $2(1-q^s)(1-1/m)$。固定 $s>0$ 后依次令 $q\downarrow0$、$m\to\infty$，得到 $D\ge2$；普遍上界二给等号。$\kappa=1$ 时 (89.2) 为标准分支，所以全部标量投影和单位效果均标准。仍取全有限 CP 菜单与互补标签补全，得到完整模型。这个构造不反驳按 $q_E$ 归一的 (86.1)，也不满足 U。∎

## 90. 候选的独立性与量子理论接口

**定理 90.1（C109 的完整满足模型及条件重建）。** C109 有完整通常有限复量子满足模型；三条关系 S、H、U 不能删除任一条而仍保证全部指定更新标准。在任一 C109 模型中，全部已经供应的态、效果和有限指定滤波序列满足 (82.1) 的 Born 成功、Lüders 投影及顺序更新公式。

证明。标准全菜单选择 $T_E=\mathcal L_E$，S、H 成立且 $\beta_*=0$，给非空完整模型。删除 U，定理 88.1 给其余两关系成立的非标准完整族。删除 S 或 H，直接取定理 80.1 的对应完整反模型；它们满足精确 R，所以 $\beta_*=0$，特别满足 U，且仍不是标准更新。无需另造同一反模型。

定理 87.1 把 C109 的指定族精确还原为平方根族，故对已供态 $\rho$、效果 $B$ 有 $p(E\mid\rho)=\tau(\rho E)$、$p(E\text{ 后 }B\mid\rho)=\tau(B\sqrt E\rho\sqrt E)$，成功后态仅在正成功率时按该概率归一。有限序列的 Kraus 乘积仍为 $\sqrt{E_n}\cdots\sqrt{E_1}$。若只保留 S、H 和逐效果返回误差，则 (86.1) 代入 (82.1)–(82.2) 的等迹输出与望远镜证明，给概率、后态和有限路径的相应误差界。

C101–C103 仍承担有限经典／复矩阵直和表示、已供空间边的张量乘法、实际过程的完全正性及共同标尺。全态、一般 POVM 的共同总过程、全部复合与参考、连续可逆群和经验时间单位均须保留各自供应条件；给定连续一参数实际可逆群时才接回原 Hamilton 表示。U 约束既有成功分支，不提供这些额外对象、过程或时间。定理 85.1 的精确成功计数也说明，仅有 Born 成功率和补偿成功率不能替代输出关系。∎

## 91. 正收缩先例与返回约束的白话定义

**定义 91.1（成熟工具与本批关系的范围）。** 定义 83.1 的对称序贯乘积先例仍适用；本批不把 S、H 或精确平方根刻画重新认领为原创。幂次收缩、谱分解和 Hermitian Kraus 居中也是成熟工具。[Mukhamedov，*On dominant contractions and a generalization of the zero-two law*，定理 1.1、1.2](https://arxiv.org/pdf/1004.2103v1) 与 [Ganiev–Mukhamedov–Bekbaev，*On a generalized uniform zero-two law for positive contractions of non-commutative L1-spaces and its vector-valued extension*，定理 1.2、4.1](https://arxiv.org/pdf/1603.07812v1) 给正收缩相邻幂差、支配关系与渐近消失的成熟零二律。那些定理的支配条件及相邻幂差不是本节的实际倒数分支返回条件，不以相同的阈值字面代替参数对应。

这里的承重综合是：由 S、H 在允许中心转移的原有限代数上得到 (85.1)，把不带参考的原实际归一化返回输出误差转为 (86.1) 的无维数完整参考界，再沿同一效果的有限平方链得到 (87.1) 与 U 的精确选择。阈值、逐点量词、有限测试及暗三方向反模型各由定理 88.1、89.1 分开承担；不作穷尽文献或原创优先权结论。相对于 C108，本批放松返回关系而保留精确 S、H，不包含三条关系同时带误差的统一结论。

白话说：把滤片接上倒着补偿的滤片，成功次数对得上还不够，回来时的细节也要对得上。若一块滤片暗中磨掉了一点细节，而整块总能拆成两个相同半块，那么沿同一套拆合关系反复加深，这点损失就会累积，终会在某个有限层级显露到统一门槛之外。因此，只要所有层级归一后的返回误差始终留有同一个小于一的余量，再加上两端互易，就连那一点暗损失也不能存在，平方根更新随之确定；等价地，每条平方链各自反复留有严格余量就已足够，不必让全族共用一个数。第三个很暗的方向说明为什么必须归一：它能把返回成功率压得极低，让原始误差很小，却不能让已经丢掉的细节回来。

## 追加锚（本行以下为增补区）

## 92. 三条实际关系同时允许误差

**定义 92.1（C110：联合容差的互易可拆返回体）。** 保留定义 77.1 的全部有限对象、效果、所选框架、正确成功效果和实际有限接续，不假设 R、S 或 H。仍用通常迹之和、定义 79.1 的任意数学参考 diamond 范数，以及定义 84.1 的归一化实际返回公式；此处不继承定理 85.1 的正常形。对非零效果定义

$$
\begin{aligned}
s(E,F)&=\frac{\|T_{E,F}-T_{E,F}^*\|_\diamond}{\|E\|},&
h(E,F)&=\frac{\|T_{E,F}-T_{\sqrt E,F}^{\,2}\|_\diamond}{\|E\|},\\
b(E,F)&=\sup_{\rho\in\mathcal C_E,\ \rho\ge0,\ \tau(\rho)=1}
\|q_E^{-1}T_{E^\vee,F}T_{E,F}(\rho)-\rho\|_1.
\end{aligned}
\tag{92.1}
$$

写 $S_* =\sup s$、$H_* =\sup h$、$B_* =\sup b$，上确界保留全部原对象、非零效果和框架。$b$ 的输出在原完整代数中比较，不先压回支撑。一般情形不假设它或 $s$ 不超过二。它们分别比较原分支与迹对偶、整程与两个相同半程、滤波与原实际补偿的接续。数学伴随、支撑压缩及除以 $q_E$ 都不另供实际过程。

给 $0\le\varepsilon\le2^{-15}$，C110$(\varepsilon)$ 是满足 $\max(S_*,H_*,B_*)\le\varepsilon$ 的指定族。容差是这些关系缺陷的上界，不在定义中使用平方根更新公式。$\varepsilon=0$ 的精确边界复用 C108；本批研究内容是三条关系同时有误差的统一控制，而非重新认领该精确刻画。数学全态量词仍不等于全部准备已实际供应。

## 93. 原分支与伴随共享一个纯滤波近邻

**定理 93.1（实际返回、中心转移与双向近邻）。** 固定一个非零效果及框架，置 $M=\|E\|$、$\sigma=s(E,F)$、$\delta=b(E,F)\le2^{-15}$，并定义

$$
\begin{aligned}
u&=8\delta,&w&=\frac{8\sqrt{u}}{1-u},&
a&=w\sqrt{1+\delta}+\delta+\sqrt\sigma,\\
e&=2a+(1+\delta)w^2+\sigma,&
e'&=4a+\sigma.
\end{aligned}
\tag{93.1}
$$

存在支撑角 $\mathcal C_E$ 的保星自同构 $\alpha$，允许等阶中心块置换，使数学参照 $A=\mathcal L_E\alpha$ 在原代数上由输入压缩延拓后满足

$$
\|T_E-A\|_\diamond\le Me,\qquad
\|T_E^*-A^*\|_\diamond\le Me',\qquad
AA^*=\mathcal L_{E^2}.
\tag{93.2}
$$

不预设 $\alpha(E)=E$，也不声明 $\alpha$ 为实际过程。所有常数不含维数、秩或 $q_E^{-1}$。

证明。省略框架，写 $P=P_E$、$q=q_E$、$\mathcal C=P\mathcal AP$。正确成功效果使各 Kraus 算子右端含 $P$，故 $T_E$ 不读支撑外输入。令 $D=T_E-T_E^*$；因 $D^*=-D$，迹／算子范数对偶给 $\|D\|_{\rm cb,\infty}=\|D\|_\diamond=\sigma M$。因此

$$
\|T_E(1)-E\|\le\sigma M,\qquad
0\le T_E^*(1-P)=(T_E^*-T_E)(1-P)\le\sigma M I.
\tag{93.3}
$$

后一式把全部输出泄漏的 Kraus 平方和控制在 $\sigma M I$ 内，不只比较一次输出的某个分量。

在支撑上取逆，定义两个数学完全正映射

$$
\Phi(X)=E^{-1/2}PT_E(X)PE^{-1/2},\qquad
\Psi(Y)=q^{-1}T_{E^\vee}(\sqrt E\,Y\sqrt E).
\tag{93.4}
$$

$\Phi:\mathcal C\to\mathcal C$，而 $\Psi:\mathcal C\to\mathcal A$ 保迹：对 $Y\in\mathcal C$，正确成功效果给

$$
\tau\Psi(Y)=q^{-1}\tau\!\left(Y\sqrt E\,E^\vee\sqrt E\right)=\tau Y.
$$

实际补偿也只读 $P$，所以 $\Psi\Phi=q^{-1}T_{E^\vee}T_E|_{\mathcal C}$。令 $G=\Phi^*(P)$。对每个角内归一正 $\rho$，有 $|\tau(\rho G)-1|=|\tau(\Psi\Phi(\rho)-\rho)|\le\delta$；在 $G-P$ 的极值本征态上取值，得到 $\|G-P\|\le\delta$。令 $J=\Phi\mathcal L_{G^{-1}}$，这里 $\mathcal L_{G^{-1}}(X)=G^{-1/2}XG^{-1/2}$。则 $J$ 完全正且保迹，$\Phi=J\mathcal L_G$，并有

$$
\|\Phi-J\|_\diamond
\le(\sqrt{1+\delta}+1)\|\sqrt G-P\|\le3\delta.
\tag{93.5}
$$

固定任一角内态 $\omega$，定义数学映射

$$
\mathscr R(Y)=PYP+\tau((1-P)Y)\omega,\qquad
\widehat\Psi=\mathscr R\Psi.
$$

$\mathscr R:\mathcal A\to\mathcal C$ 完全正且保迹，并在 $\mathcal C$ 上恒等；因此它对自伴输入的迹范数为收缩。$\Psi$ 也完全正且保迹，故 $\|\Psi\|_\diamond=1$。对任一角内归一正输入，(93.5) 给

$$
\begin{aligned}
\|\Psi J(\rho)-\rho\|_1
&\le\|\Psi(J-\Phi)(\rho)\|_1+\|\Psi\Phi(\rho)-\rho\|_1
\le4\delta,\\
\|\widehat\Psi J(\rho)-\rho\|_1
&=\|\mathscr R(\Psi J(\rho)-\rho)\|_1\le4\delta.
\end{aligned}
$$

这里补全丢失迹的系数恰为原输出的角外质量；没有再次归一输入或除以成功率。保留稍宽的 $u=8\delta$，于是

$$
\sup_{\rho\ge0,\ \tau\rho=1}
\|\widehat\Psi J(\rho)-\rho\|_1\le8\delta=u.
\tag{93.6}
$$

以下在这个已取得的同角近左逆内部使用成熟的 Schwarz、Stinespring 与紧群平均工具，给出所需量化。令 $U=J^*$、$V=\widehat\Psi^*$，二者均为同一有限代数 $\mathcal C$ 的幺完全正映射。(93.6) 经迹对偶给 $\|UV-\operatorname{id}\|_{\infty,\mathrm{sa}}\le u<1$。在自伴实 Banach 空间上取 Neumann 逆；有限维且定义域、值域相同，推出 $U,V$ 都可逆，逆的自伴算子范数至多 $(1-u)^{-1}$，并有

$$
\|VU-\operatorname{id}\|_{\infty,\mathrm{sa}}\le\frac{u}{1-u}.
\tag{93.7}
$$

对任意酉元 $v$，分成实、虚自伴部分，得 $\|VU(v)-v\|\le2u/(1-u)$。Schwarz 不等式给 $Z_v=I-U(v)^*U(v)\ge0$，且

$$
0\le V(Z_v)\le I-VU(v)^*VU(v)
\le\frac{4u}{1-u}I,\qquad
\|Z_v\|\le\frac{4u}{(1-u)^2}=t^2.
\tag{93.8}
$$

对 $U$ 的每个输出简单块取 Stinespring 表示 $U_\gamma(x)=V_\gamma^*\pi_\gamma(x)V_\gamma$，其中 $V_\gamma$ 为等距，$Q_\gamma=V_\gamma V_\gamma^*$。将 (93.8) 分别用于 $v,v^*$，得到 $\|[Q_\gamma,\pi_\gamma(v)]\|\le t$。在紧群 $\mathcal U(\mathcal C)$ 上用归一 Haar 平均，置

$$
B_\gamma=\int\pi_\gamma(v)Q_\gamma\pi_\gamma(v)^*\,dv,
\qquad R_\gamma=1_{[1/2,\infty)}(B_\gamma).
\tag{93.9}
$$

$B_\gamma$ 及 $R_\gamma$ 与全部 $\pi_\gamma(x)$ 对易，$\|B_\gamma-Q_\gamma\|\le t$，且 $\|R_\gamma-Q_\gamma\|\le2t<1$。最后一界来自谱包含 $[0,t]\cup[1-t,1]$ 及三角不等式。置
$Z=R_\gamma Q_\gamma+(I-R_\gamma)(I-Q_\gamma)$，其酉极分解因子 $W_\gamma$ 将 $Q_\gamma$ 送到 $R_\gamma$。若 $d=\|R_\gamma-Q_\gamma\|$，则 $Z^*Z=I-(R_\gamma-Q_\gamma)^2$、$\|Z-I\|\le d$，从而

$$
\|W_\gamma-I\|\le d+1-\sqrt{1-d^2}\le2d\le4t=w.
\tag{93.10}
$$

以 $W_\gamma V_\gamma$ 替代 $V_\gamma$，所得映射 $\theta_\gamma$ 是幺保星同态；各块合成 $\theta:\mathcal C\to\mathcal C$，$\|\theta-U\|_{\rm cb,\infty}\le2w=8t$。这里 $u\le1/4096$，故 $8t<1-u$；与 $U$ 的逆界组合说明 $\theta$ 在自伴实空间可逆，因而是原有限代数的保星自同构。其迹伴随 $\alpha=\theta^*$ 也是保星自同构，因为这种自同构只置换等阶简单块并作块内酉共轭，保留通常迹之和。

还需控制同一个原分支及其伴随。以下证明原 Kraus 家族中的分块提升结论，所用见证是 (93.10) 已构造的等距扰动。写
$\mathcal C=\bigoplus_{\gamma\in I}\mathcal B(H_\gamma)$，其中 $H_\gamma=P_\gamma\mathbb C^{d_\gamma}$，$I$ 只保留非零角。必要时补零，取原 $T_E$ 从中心块 $\gamma$ 到 $\beta$ 的矩形 Kraus 家族 $R_{\beta\gamma j}$；它们右端均含 $P_\gamma$。对于 $\beta,\gamma\in I$，令

$$
B_{\beta\gamma j}
=E_\beta^{-1/2}P_\beta R_{\beta\gamma j}|_{H_\gamma}G_\gamma^{-1/2},\qquad
V_\gamma\xi=\bigoplus_{\beta}\sum_j B_{\beta\gamma j}\xi\otimes e_{\beta\gamma j}.
\tag{93.10a}
$$

$J$ 保迹给 $V_\gamma^*V_\gamma=I_\gamma$；这正是上文 $U_\gamma=J^*|_\gamma$ 的一个 Stinespring 表示，表示空间为
$\bigoplus_{\beta\in I}(H_\beta\otimes\mathcal E_{\beta\gamma})$，$\pi_\gamma(x)=\bigoplus_\beta(x_\beta\otimes I)$。整个 Haar 和极分解构造均可从这个原家族表示开始。

置 $\widetilde V_\gamma=W_\gamma V_\gamma$，则 $\|V_\gamma-\widetilde V_\gamma\|\le w$，且其值域投影 $R_\gamma$ 与 $\pi_\gamma$ 对易，故
$\pi_\gamma(x)\widetilde V_\gamma=\widetilde V_\gamma\theta_\gamma(x)$。自同构置换中心极小投影，并在对应矩阵块的矩阵单位之间作酉对应，因此存在双射 $p:I\to I$ 及酉算子 $u_\gamma:H_\gamma\to H_{p(\gamma)}$，使
$\theta_\gamma(x)=u_\gamma^*x_{p(\gamma)}u_\gamma$。

这也直接确定环境重数。将上述交织等式用于各中心投影，$\widetilde V_\gamma$ 在 $\beta\ne p(\gamma)$ 的分量为零；在 $\beta=p(\gamma)$ 的每个环境分量 $F$ 上，全部矩阵 $Y$ 满足 $YFu_\gamma^*=Fu_\gamma^*Y$，所以 $F$ 是 $u_\gamma$ 的标量倍。等距条件使这些标量的平方和为一。于是存在单位向量 $\eta_\gamma\in\mathcal E_{p(\gamma)\gamma}$，使

$$
\widetilde V_\gamma\xi=u_\gamma\xi\otimes\eta_\gamma.
\tag{93.10b}
$$

在该环境空间中把 $\eta_\gamma$ 选为首基向量，并将同一酉基变换用于原 $R_{p(\gamma)\gamma j}$。记所选的 $B$ 分量为 $B_\gamma$，其余所有分量均记为余项；其他中心对的分量也全部属于余项。若 $\mathsf P_\gamma$ 投影到 $H_{p(\gamma)}\otimes\mathbb C\eta_\gamma$，则 $\mathsf P_\gamma\widetilde V_\gamma=\widetilde V_\gamma$，从等距扰动得到

$$
\|B_\gamma-u_\gamma\|\le w,\qquad
\sum_{\mathrm{余项}\ (\beta,j)}B_{\beta\gamma j}^*B_{\beta\gamma j}
=V_\gamma^*(I-\mathsf P_\gamma)V_\gamma\le w^2I_\gamma.
\tag{93.10c}
$$

原家族对应的所选分量记为 $K_\gamma$，保留其在原输出中心 $p(\gamma)$ 内的全部角外行。由 (93.10a) 有
$P_{p(\gamma)}K_\gamma=\sqrt{E_{p(\gamma)}}B_\gamma\sqrt{G_\gamma}$。将 $K_\gamma$ 按双射 $p$ 组装成 $K$，并令 $K_0$ 的相应块为 $\sqrt{E_{p(\gamma)}}u_\gamma$。不同输入中心对应不同输出中心，故 $\operatorname{Ad}_K$ 和 $\operatorname{Ad}_{K_0}$ 都映原代数到自身；后者恰为 $\mathcal L_E\alpha$。由 (93.10c) 及 $\|\sqrt G-P\|\le\delta$，

$$
\begin{aligned}
\|PK-K_0\|&\le\sqrt M\bigl(w\sqrt{1+\delta}+\delta\bigr),\\
\|(1-P)K\|^2&=\|K^*(1-P)K\|
\le\|T_E^*(1-P)\|\le\sigma M.
\end{aligned}
\tag{93.10d}
$$

因此 $\|K-K_0\|\le\sqrt M a$。原矩形 Kraus 家族经过上述环境酉变换后，除所选分量外的全部项定义完全正 $N$，于是 $T_E=\operatorname{Ad}_K+N$。其输入质量可逐块计算：角内余项满足

$$
\begin{aligned}
\sum_{\mathrm{余项}\ (\beta,j)}R_{\beta\gamma j}^*P_\beta R_{\beta\gamma j}
&\le M\sqrt{G_\gamma}
\left(\sum_{\mathrm{余项}\ (\beta,j)}B_{\beta\gamma j}^*B_{\beta\gamma j}\right)\sqrt{G_\gamma}\\
&\le M(1+\delta)w^2 I_\gamma.
\end{aligned}
$$

角外余项的平方和不超过 $T_E^*(1-P)\le\sigma MI$；这也包括 $P_\beta=0$ 的输出中心。因为 $P$ 与 $1-P$ 正交，两个输出部分的输入平方和相加没有交叉项。故取得

$$
T_E=\operatorname{Ad}_K+N,\quad
\|K-K_0\|\le\sqrt M a,\quad
\|N^*(1)\|\le M\bigl((1+\delta)w^2+\sigma\bigr).
\tag{93.11}
$$

这里没有删除任何中心转移或角外分量；分解及环境基变换只是在原实际分支内部使用的数学见证。

正确成功效果给 $\|K\|\le\sqrt M$，而 $K_0K_0^*=E$。因此

$$
\|N(1)\|=\|T_E(1)-KK^*\|
\le M(\sigma+2a).
\tag{93.12}
$$

主纯映射及其伴随距 $\operatorname{Ad}_{K_0}$、$\operatorname{Ad}_{K_0}^*$ 的 diamond 范数都至多 $2Ma$。完全正范数公式分别把余项及其伴随控制为 $\|N^*(1)\|$、$\|N(1)\|$，给出 (93.2) 前两式。最后 $A=\mathcal L_E\alpha$、$A^*=\alpha^{-1}\mathcal L_E$，故 $AA^*=\mathcal L_E^2=\mathcal L_{E^2}$。不需要先证明 $\alpha(E)=E$。∎

## 94. 三边都有误差时的量子更新与有限接续

**定理 94.1（联合稳定及条件量子接口）。** 在定义 92.1 的原完整范围内，对 $A=\sqrt E$，若 $\delta=b(A,F)\le2^{-15}$，将 $\sigma=s(A,F)$ 代入 (93.1)，则

$$
d(E,F)\le\min\{2,\ h(E,F)+\sigma+(1+\sigma)e+e'\}.
\tag{94.1}
$$

特别地，当 $S_*\le1/4$、$B_*\le2^{-15}$ 时，

$$
D\le\min\{2,\ H_*+10\sqrt{S_*}+200\sqrt{B_*}\}.
\tag{94.2}
$$

所以 C110$(\varepsilon)$ 给 $D\le\min\{2,\varepsilon+210\sqrt\varepsilon\}$；三种原关系缺陷同时一致趋零时，全部原指定更新一致趋于平方根族。结论包括全部数学参考，不要求返回前提带参考。

证明。写 $S=T_{A,F}$。定理 93.1 给 $S$ 的参照 $C$，且 $CC^*=\mathcal L_E$。由 $\|S\|_\diamond=\|A\|$、$\|S^*\|_\diamond\le(1+\sigma)\|A\|$ 和 (93.2)，

$$
\|SS^*-\mathcal L_E\|_\diamond
\le\|E\|\bigl((1+\sigma)e+e'\bigr).
\tag{94.3}
$$

同一映射空间中的三个实际关系组成恒等式

$$
T_E-\mathcal L_E
=(T_E-S^2)+S(S-S^*)+(SS^*-\mathcal L_E).
\tag{94.4}
$$

次乘性给 (94.1)；两个完全正映射 $T_E,\mathcal L_E$ 的范数均为 $\|E\|$，另给上界二。若 $\delta\le2^{-15}$，则 $w\le24\sqrt\delta$、$a\le26\sqrt\delta+\sqrt\sigma$、$(1+\delta)w^2\le577\delta$。再用 $1+\sigma\le5/4$、$\sigma\le\sqrt\sigma/2$、$\delta\le\sqrt\delta/128$，有

$$
\begin{aligned}
\sigma+(1+\sigma)e+e'
&\le\tfrac{13}{2}a+\tfrac{2885}{4}\delta+\tfrac{13}{4}\sigma\\
&\le10\sqrt\sigma+200\sqrt\delta.
\end{aligned}
$$

取上确界得 (94.2)，零效果的分支由正确成功效果已为零。

令 $b_i$ 为 (94.1) 或 (94.2) 给第 $i$ 个非零效果的更新界。对任一已经供应的态和有限原指定路径，望远镜恒等式及每段范数 $\|E_i\|$ 给

$$
\|T_{E_n}\cdots T_{E_1}-\mathcal L_{E_n}\cdots\mathcal L_{E_1}\|_\diamond
\le\Bigl(\prod_i\|E_i\|\Bigr)\sum_i b_i.
\tag{94.5}
$$

单次成功率仍精确为 $p=\tau(\rho E)$。实际与标准单次输出同迹，所以任何已有末端效果 $B$ 的联合概率差至多 $\|E\|b_E/2$；若 $p>0$，条件后态迹距离至多 $\|E\|b_E/p$。一般整路径输出不再同迹，概率差使用 (94.5) 的整项；两条路径成功率都正时，按原实际成功率归一的后态误差至多该整项的两倍除以实际成功率。

三维谱角 $Q$ 的压缩更新距 $\operatorname{Ad}_{\sqrt{QEQ}}$ 至多 $\|E\|b_E$；任意一般三维 $Q$ 则比较 $\operatorname{Ad}_{Q\sqrt E Q}$，不把它替换为 $\operatorname{Ad}_{\sqrt{QEQ}}$。这些界来自原完整代数及任意参考的界，经输入、输出压缩的完全收缩性得到，不增加实际角对象或中途压缩操作。全态、空间复合、一般仪器及连续可逆动力学的供应条件仍逐项按定理 90.1 保留；Hamilton 表示仅在连续实际可逆群及时间供应到位时接入。∎

## 95. 全菜单上三种缺陷同时非零的满足族

**定理 95.1（完整扰动族、三维二元见证与删除检验）。** C110$(\varepsilon)$ 有完整通常有限复量子满足模型。对每个 $0<\varepsilon\le2^{-15}$，另有完整非标准族满足 C110$(\varepsilon)$，其中三种关系缺陷均非零，且在同一个三维对象中 $D\ge\varepsilon/12$。不能删除其中任一关系并仍以其余两种缺陷一致趋零保证 $D\to0$。

证明。标准全有限菜单选择全部 $T_E=\mathcal L_E$，给零缺陷模型。对非零扰动，取同一全对象、全态、全 CP 分支及标签仪器菜单。在每个所选细谱框架上选一个对角 $G_F$，$\|G_F\|\le1$，且在 $M_3$ 的指定框架中前三个对角元为 $1,-1,0$；其余框架和对象可统一取交替的 $1,-1$。令 $\Delta_F$ 为逐个原简单块、逐条框架射线的 pinching，$t=\varepsilon/12$，并在每个效果的支撑角上取

$$
\Phi_{E,F}=(1-t)\operatorname{Ad}_{\exp(itG_F)|_{P_E}}+t\Delta_F|_{\mathcal C_E},
\qquad T_{E,F}=\mathcal L_E\Phi_{E,F},\qquad T_{0,F}=0.
\tag{95.1}
$$

所有 $\Phi$ 均双随机且与 $E$ 的左右乘法对易，正确成功效果成立；每个互补标签对的总映射保迹，原全菜单包含它及全部有限接续。这里不要求投影分支或 $T_1$ 在正容差时精确标准。

$\|\Phi_{E,F}-\operatorname{id}\|_\diamond\le2t+2t=4t$，其伴随有同一界。三角不等式及平方差展开分别给 $s\le8t$、$h\le12t$。倒数效果保留同一支撑、框架和 $\Phi$，故归一化实际返回为 $\Phi^2$，$b\le8t$。这给全部原对象上的 C110$(\varepsilon)$，并非仅对一个孤立通道的估计。

在 $M_3$ 中取 $E=\operatorname{diag}(1,1,q)$、$0<q<1$。前两条明亮射线的非对角矩阵元被乘以 $z=(1-t)e^{2it}$；标准更新的系数为一。等权相干纯输入给更新的迹范数差 $|1-z|\ge t$，相应迹零残差的正谱投影给概率差 $|1-z|/2$，因而 $D\ge t$。同一二元关系的互易、半程、返回系数差分别为 $z-\bar z$、$z-z^2$、$1-z^2$，在所取 $t$ 范围均非零。第三方向保持整个三维实际对象，$q$ 可任意暗；界中没有用其倒数。这是有限三维见证，不替代 (93.2)、(94.2) 的全代数量词，也不宣称平方根误差率最优。

删除返回关系，复用定理 80.1 的精确 S、H 非标准族；删除互易或半程关系，复用其中精确 R、H 或 R、S 非标准族，后两者的 $b$ 恒为零。这些完整反模型使保留的两个缺陷已恰为零，更新仍非标准，故否定删除后任何趋零模量。∎

## 96. 近似兼容体的文献对应及未决强版本

**定义 96.1（成熟桥梁、量词边界与白话表述）。** [Choi–Johnston–Kribs，*The multiplicative domain in quantum error correction*，定理 8](https://arxiv.org/pdf/0811.0947) 给幺完全正映射的两个 Schwarz 等号及其乘法域；[McKenney–Vignati，*Ulam stability for some classes of C*-algebras*，定理 1.7](https://arxiv.org/pdf/1601.05445v2) 给有限维 C*-代数上的近保星同态距真同态的统一平方根控制。紧酉群平均、Stinespring 表示、近投影的极分解修正和完全正范数公式均为成熟工具；定理 93.1 在原实际成功效果与返回缺陷中逐步构造其所需前提，并保留对应常数，不把一般 Ulam 稳定性另计为新定理。仓内《ContextualSpacetimeQuantum/330_350_SMALL_BUDGET_AND_CORRECTIONS》第 350 节已使用紧群平均修正的机制；这里不将那里的群表示合同当作当前 CP 分支的已证接口。

本批承重综合是 (93.3)–(93.6) 的原成功效果归一与补全、同角近逆经 (93.8)–(93.11) 回到原矩形 Kraus 家族，以及以正余项两个方向的质量控制同时取得 (93.2)。后一步避免将 diamond 小误差直接取迹伴随的错误，并把最暗方向的逆从联合更新界中消去。(94.4) 的三角组织复用 C108，新增项由三种缺陷都非零的证明承担。不作穷尽文献或原创优先权结论。

C110 给三种缺陷同时趋零的统一理论；它没有证明更强的命题“固定任意 $c<1$ 及 $B_*\le c$，只让 $S_*,H_*\to0$ 就有 $D\to0$”。该固定余量问题仍未决。C109 在 $S_*=H_*=0$ 时的任意严格返回余量结论继续成立；这里的较小返回范围及非最优平方根模量不改写它，也不据此否定强版本。有限数学见证仍不供应实际准备、误差证书或统一取得费用。

白话说：滤片接上倒着补偿的滤片，回来时的细节允许差一点；把整程拆成两个相同半程也允许差一点，交换两端读数同样允许差一点。关键是三种差来自同一套实际分支，不能各挑一个有利实现。本批证明，三边一起变准时，滤片本身也必定一起接近平方根更新，维数再大、第三个方向再暗都不能藏住一块固定的偏差。补偿先找出共同的纯滤波近邻，互易管住泄漏和倒向，半程再把近邻锁到标准更新；这些近邻只是证明中的坐标，不是额外假设出来的实际过程。

## 追加锚（本行以下为增补区）

## 97. 固定返回余量不能有幂次稳定率

**定理 97.1（全菜单上的对数必要尺度）。** 固定 $0<c<1$，置 $a=\sqrt{1-c}$。对所有充分小的 $t>0$，存在定义 92.1 原完整范围内的通常有限量子菜单 $M_t$，满足

$$
\begin{aligned}
S_*(M_t)&=0,&B_*(M_t)&=c,\\
D(M_t)&=\frac{2t}{1+2t}(1+2t)^{-1/(2t)},&
H_*(M_t)&=a^{1+1/(2t)}D(M_t).
\end{aligned}
\tag{97.1}
$$

因此

$$
D(M_t)\sim\frac{2t}{\mathrm e},\qquad
D(M_t)\log\frac1{H_*(M_t)}\longrightarrow
\frac{-\log(1-c)}{2\mathrm e},\qquad
\frac{D(M_t)}{H_*(M_t)^\gamma}\longrightarrow\infty\quad(\gamma>0).
\tag{97.2}
$$

固定余量强版本若有统一趋零模量，就不能是任意正幂次，也不能是 $o(1/\log(1/H_*))$。这里 $D\to0$，故不将它称为该强版本本身的反例；$c=0$ 的精确返回层仍有定理 79.2 的线性界。

证明。取全部通常有限复矩阵直和、全 CP 标签仪器及其有限接续。逐个简单块指定分支：若该块效果恰有两个不同的正谱值 $x>y>0$，令 $r=y/x$，$\Pi_E$ 为这两个正谱空间之间的 pinching，置

$$
f_t(r)=\max\{a,r^t\},\qquad
T_E=\mathcal L_E\bigl[f_t(r)\operatorname{id}+(1-f_t(r))\Pi_E\bigr].
\tag{97.3}
$$

不足两个或多于两个不同正谱值的块一律标准，零效果取零；输入在支撑外压缩。各块并成原直和上的指定分支，对全部框架使用这一相同规则。它完全正且成功效果为 $E$，互补指定分支补成原菜单内的保迹标签总过程。这不是只给若干被测试效果赋值。

$O_E=\operatorname{id}-\Pi_E$ 在该两层角内等于 $(\operatorname{id}-\operatorname{Ad}_{P_x-P_y})/2$，故 $\|O_E\|_\diamond=1$；上界来自两个通道的距离，跨两层的等权纯态给下界。所有系数实数，$S_*=0$。倒数效果保留同一两谱空间和比值 $r$；即使全局 $q_E$ 由别的中心块决定，$\mathcal L_{E^\vee}\mathcal L_E=q_E\operatorname{id}$ 仍成立。因此归一化实际返回为

$$
f_t(r)^2\operatorname{id}+(1-f_t(r)^2)\Pi_E.
\tag{97.4}
$$

其正输入误差为 $1-f_t(r)^2\le c$，在 $r^t\le a$ 时取到 $c$。其他块标准，直和范数取最大，故全菜单 $B_*=c$。

在最高谱值为 $x$ 的两层块，更新及半程差的 diamond 范数分别为

$$
x\sqrt r(1-f_t(r)),\qquad
x\sqrt r\left(f_t(r)-f_t(\sqrt r)^2\right).
\tag{97.5}
$$

因为 $\mathcal L_E O_E=\sqrt{xy}\,O_E$，这些是完整范数等式，而非只在某个矩阵元上的估计。除以原 $\|E\|$ 后至多取 $x=\|E\|$ 的数值，单个 $M_2$ 块已取到。设 $u=r^t$、$p=1/(2t)$，则

$$
\begin{aligned}
D&=\sup_{0<u\le1}u^p(1-\max(a,u)),\\
H_*&=\sup_{0<u\le1}u^p(\max(a,u)-\max(a^2,u)).
\end{aligned}
\tag{97.6}
$$

当 $0<t\le(1-a)/(2a)$ 时，两个最大点分别是 $u_D=(1+2t)^{-1}$、$u_H=a(1+2t)^{-1}$。第一式在 $u\ge a$ 上求导、在 $u\le a$ 上用单调性；第二式在 $a^2\le u\le a$ 上求导，且在 $u\le a^2$ 上单调、$u\ge a$ 时为零，逐段即得这些全局极值。代入得到 (97.1)，再用 $(1+2t)^{-1/(2t)}\to\mathrm e^{-1}$ 及 $t\log(1/t)\to0$ 得 (97.2)。

三维实现可取 $E_r=\operatorname{diag}(1,1,r)$。原分支保留前二维块及第三方向的对角质量，只将连接它们的两组相干乘以 $\sqrt r f_t(r)$；补偿效果为 $\operatorname{diag}(r,r,1)$，归一化返回把同一两组相干乘以 $f_t(r)^2$。更新最大点的 $r_D=(1+2t)^{-1/t}\to\mathrm e^{-2}$，半程最大点却是 $r_H=a^{1/t}(1+2t)^{-1/t}$，指数级变暗。因此小半程缺陷确实发生在原三维完整对象中，并非压缩掉某个不利方向后得到。∎

## 98. 联合容差候选的整体图景

**定义 98.1（共同实现、收敛率与白话定义）。** C110$(\varepsilon)$ 仍由定义 92.1 的同一实际族承担，定理 93.1、94.1 给三种缺陷共同趋零的更新模量，定理 95.1 给三种缺陷都非零的完整满足族。定理 97.1 针对另一个量词范围：固定 $B_*\le c<1$ 时，任何仅依赖 $S_*,H_*$ 的统一模量若存在，都必须允许至少对数级的缓慢收敛。它不与 (94.2) 冲突，因为该反模型族的全菜单 $B_*$ 固定为 $c$，没有趋零；它也没有证明固定余量强版本的充分性。

白话说：三条关系必须属于同一套滤片——回来时细节差多少、交换两端差多少、整程拆成两个相同半程又差多少。三边一起变准，就能把整套更新锁向平方根规则，最暗方向不会出现在统一误差常数里；但若只保证回来还留着一个固定余量，结论即使仍成立，也可能来得很慢。一块滤片可以把半程不一致推到很深、很暗的层级，让这条关系看上去指数级准确，而可见更新只线性改善。三维图景把这种遮蔽留下来了，所以不能用一个漂亮的幂次公式替代真正需要证明的整体关系。

## 追加锚（本行以下为增补区）
