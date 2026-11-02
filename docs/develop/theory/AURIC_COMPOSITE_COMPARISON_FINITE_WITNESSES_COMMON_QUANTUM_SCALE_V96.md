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
