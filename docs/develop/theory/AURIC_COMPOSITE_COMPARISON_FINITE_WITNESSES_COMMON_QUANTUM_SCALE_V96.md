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
