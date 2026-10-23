> **Mathematical scope.** This continuation concerns finite quantum networks, CPTP maps, information geometry, and predictive observation quotients.
> Its mathematical source is commit `a2f195ceb64aaaea7eeb8a6bdea479ca2c3c7430`; individual source attributions and applicability limits accompany the corresponding statements.
> Finite constructions retain their stated hypotheses; physical interpretations, general source compatibility, and RH identifications require the additional bridges specified in the text.
>
> **Navigation.** This volume carries the original sections 27–48, following [the original volume](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE.md).
> The original source heading `后续严格补充` and sections 49–65 continue in [the second continuation](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION_II.md).
> Statements attributed to other sources retain those sources’ explicit hypotheses and limits.

## 27. 有限结构与外部桥接的边界

本节涉及的有限对象与结论为：

1. 有限图概率场 \(\mathcal C_G\)；
2. 节点势与边耦合能量；
3. 场能量的非负分解；
4. 概率场到能量分布的推前；
5. 梯度轨迹的能量耗散；
6. 五态载体的精确维数分解
   \[
   5=2+3;
   \]
7. 无相邻支持的反射 involution；
8. \(|\mathcal W_1|=2\)、\(|\mathcal W_2|=3\)、\(|\mathcal W_3|=5\)；
9. Fibonacci 支持递推；
10. 三位窗口到五态载体的编码；
11. 无限支持场到五态轨迹的局部推前；
12. 局部势产生经验能量分布的定义。

以下对象仍然是显式桥接目标：

1. 素数分类到支持场 \(\mathcal W_\infty\) 的具体编码；
2. 素数权重到局部势 \(\varphi\) 的唯一构造；
3. FIB transfer operator 到 completed \(L\)-function 的谱行列式；
4. 局部反向读取到 \(s\mapsto1-\overline{s}\) 的复反射；
5. Fisher/Dirichlet 正定度量到 Hilbert–Pólya 自伴算子的构造；
6. 无限轨迹空间的连续流形结构；
7. 物理能量、时间、引力或量子 Hamiltonian 的解释。

因此，本节的核心结论是：

\[
\boxed{
\begin{aligned}
&\text{场配置决定局部势和耦合，}\\
&\text{势决定能量分布，}\\
&\text{场上的 shift 或梯度生成元决定轨迹，}\\
&\text{观察映射决定可见流形，}\\
&\text{镜像与 Fibonacci 递推决定局部状态的闭包方式。}
\end{aligned}
}
\]

对当前 Auric FIB ATOM 载体，最严格的数字结构是

\[
\boxed{
\dim(\text{unobserved linear sector})
+
\dim(\text{visible quotient})
=
2+3=5,
}
\]

以及

\[
\boxed{
|\mathcal W_1|=2,\qquad
|\mathcal W_2|=3,\qquad
|\mathcal W_3|=5,
\qquad
|\mathcal W_n|=F_{n+2}.
}
\]

“镜像、三维视角、联合隐藏关系、无限轨迹和 Fibonacci”因此可以放进同一个有限到无限的组合场框架。把它们继续连接到 RH，需要完成算术编码、正定谱度量和完成 \(L\)-函数的 trace/determinant bridge。


---

## 28. 有限量子载体与 CPTP 组合子

本节把量子网络限定为有限维线性代数，所有量子对象均表示为有限复矩阵。这里不把“量子”解释为额外物理本体，只使用正半定性、迹、张量积和线性映射。

### 定义 28.1（有限量子状态）

令 \(H\) 为有限维复 Hilbert 空间，令 \(\mathsf L(H)\) 为其线性算子空间，令

\[
\mathsf D(H)
=
\{\rho\in\mathsf L(H):
\rho=\rho^\ast,\ \rho\succeq0,\ \operatorname{tr}\rho=1\}.
\]

若 \(\rho\in\mathsf D(H)\)，称 \(\rho\) 为量子状态。若 \(\sigma\succeq0\) 且 \(\operatorname{tr}\sigma=1\)，则 \(\sigma\) 也是量子状态。纯状态是秩一投影 \( |\psi\rangle\langle\psi| \)。

### 定义 28.2（量子信道）

有限维量子信道是线性映射

\[
\mathcal E:\mathsf L(H_A)\longrightarrow\mathsf L(H_B)
\]

满足：

1. 完全正性：对每个有限维 \(K\)，
   \[
   \mathcal E\otimes\operatorname{id}_K
   \]
   把正半定算子送到正半定算子；

2. 保迹性：
   \[
   \operatorname{tr}\mathcal E(X)=\operatorname{tr}X.
   \]

记所有这样的映射为 \(\operatorname{CPTP}(H_A,H_B)\)。

### 命题 28.3（Kraus 表示与 Choi 判据）

有限维线性映射 \(\mathcal E\) 是 CPTP，当且仅当存在有限个算子 \(K_i:H_A\to H_B\)，使

\[
\mathcal E(X)=\sum_iK_iXK_i^\ast,
\qquad
\sum_iK_i^\ast K_i=I_{H_A}.
\]

等价地，其 Choi 矩阵

\[
J(\mathcal E)
=
\sum_{i,j}|i\rangle\langle j|
\otimes
\mathcal E(|i\rangle\langle j|)
\]

满足

\[
J(\mathcal E)\succeq0,
\qquad
\operatorname{tr}_{H_B}J(\mathcal E)=I_{H_A}.
\]

#### 证明

Kraus 表示给出完全正性，因为

\[
(\mathcal E\otimes\operatorname{id}_K)(X)
=
\sum_i(K_i\otimes I_K)X(K_i^\ast\otimes I_K)
\]

保持正半定性。且

\[
\operatorname{tr}\mathcal E(X)
=
\operatorname{tr}
\left(
\sum_iK_i^\ast K_iX
\right)
=
\operatorname{tr}X.
\]

反向方向是有限维 Choi 定理。完全正性等价于 \(J(\mathcal E)\succeq0\)，保迹性等价于部分迹条件。证毕。

### 定理 28.4（CPTP 组合子结构）

有限维 Hilbert 空间和 CPTP 映射构成一个带张量积的对称幺半范畴：

\[
\mathbf{QFin}.
\]

具体地：

\[
\operatorname{id}_H\in\operatorname{CPTP}(H,H),
\]

若 \(\mathcal E\in\operatorname{CPTP}(H_A,H_B)\) 且

\[
\mathcal F\in\operatorname{CPTP}(H_B,H_C),
\]

则

\[
\mathcal F\circ\mathcal E
\in\operatorname{CPTP}(H_A,H_C).
\]

若 \(\mathcal E_1,\mathcal E_2\) 是 CPTP，则

\[
\mathcal E_1\otimes\mathcal E_2
\]

也是 CPTP。

#### 证明

恒等映射显然完全正且保迹。复合的完全正性由

\[
(\mathcal F\circ\mathcal E)\otimes\operatorname{id}
=
(\mathcal F\otimes\operatorname{id})
\circ
(\mathcal E\otimes\operatorname{id})
\]

得到，保迹性由迹的逐次保持得到。张量积的 Kraus 算子为

\[
K_i\otimes L_j,
\]

并且

\[
\sum_{i,j}
(K_i\otimes L_j)^\ast(K_i\otimes L_j)
=
\left(\sum_iK_i^\ast K_i\right)
\otimes
\left(\sum_jL_j^\ast L_j\right)
=
I\otimes I.
\]

结合有限维张量积的结合律、单位对象 \(\mathbb C\) 和交换对称子，得到对称幺半范畴结构。证毕。

### 定义 28.5（伴随映射）

相对于 Hilbert--Schmidt 内积

\[
\langle X,Y\rangle_{\mathrm{HS}}
=
\operatorname{tr}(X^\ast Y),
\]

定义 \(\mathcal E^\ast\) 为满足

\[
\operatorname{tr}(Y^\ast\mathcal E(X))
=
\operatorname{tr}((\mathcal E^\ast(Y))^\ast X)
\]

的唯一线性映射。若 \(\mathcal E\) 保迹，则

\[
\mathcal E^\ast(I)=I.
\]

因此 CPTP 映射的伴随是首一完全正映射。量子网络中的“局部观察”应使用 \(\mathcal E^\ast\) 作用在观察量上，而不是把观察量和状态混为同一类型。

### 定义 28.6（POVM 输出映射）

有限输出集 \(A\) 上的 POVM 是一族正半定算子

\[
(M_a)_{a\in A},
\qquad
M_a\succeq0,
\qquad
\sum_{a\in A}M_a=I_H.
\]

它定义概率映射

\[
\operatorname{out}_M:\mathsf D(H)\to\Delta(A),
\qquad
\operatorname{out}_M(\rho)(a)
=
\operatorname{tr}(M_a\rho).
\]

非负性来自 \(M_a,\rho\succeq0\)，归一化来自 \(\sum_aM_a=I_H\)。

---

## 29. FIB 五态概率律作为量子系统的可验证经典扇区

### 定义 29.1（对角嵌入）

令

\[
H_\Sigma=\mathbb C^\Sigma
\]

具有标准基 \((|s\rangle)_{s\in\Sigma}\)。定义

\[
\iota_\Sigma:\Delta(\Sigma)\to\mathsf D(H_\Sigma),
\qquad
\iota_\Sigma(p)
=
\sum_{s\in\Sigma}p_s|s\rangle\langle s|.
\]

该映射把 FIB 概率律嵌入量子状态空间的对角子集。

定义退相干映射

\[
\mathsf{Dec}_\Sigma(X)
=
\sum_{s\in\Sigma}
\langle s|X|s\rangle
|s\rangle\langle s|.
\]

它是 CPTP，并满足

\[
\mathsf{Dec}_\Sigma\circ\iota_\Sigma
=
\iota_\Sigma.
\]

### 定义 29.2（随机核的量子提升）

令 \(W(a\mid s)\) 是从 \(\Sigma\) 到有限集合 \(A\) 的随机核。定义

\[
\mathcal E_W(X)
=
\sum_{a\in A}\sum_{s\in\Sigma}
W(a\mid s)
\langle s|X|s\rangle
|a\rangle\langle a|.
\]

其 Kraus 算子为

\[
K_{a,s}
=
\sqrt{W(a\mid s)}\,|a\rangle\langle s|.
\]

### 定理 29.3（FIB 粗粒化的 CPTP 实现）

\(\mathcal E_W\) 是 CPTP，且对所有 \(p\in\Delta(\Sigma)\) 有

\[
\mathcal E_W(\iota_\Sigma(p))
=
\iota_A(Wp),
\]

其中

\[
(Wp)_a
=
\sum_{s\in\Sigma}W(a\mid s)p_s.
\]

#### 证明

由随机核归一化，

\[
\sum_{a,s}K_{a,s}^\ast K_{a,s}
=
\sum_s
\left(\sum_aW(a\mid s)\right)
|s\rangle\langle s|
=
I_{H_\Sigma}.
\]

所以 \(\mathcal E_W\) 是 CPTP。对角状态代入定义：

\[
\begin{aligned}
\mathcal E_W(\iota_\Sigma(p))
&=
\sum_{a,s}
W(a\mid s)p_s|a\rangle\langle a|\\
&=
\sum_a(Wp)_a|a\rangle\langle a|\\
&=
\iota_A(Wp).
\end{aligned}
\]

证毕。

### 推论 29.4（FIB seam 的量子表示）

令

\[
D=\operatorname{diag}(d_s)_{s\in\Sigma},
\qquad
d=(1,-1,0,-1,1).
\]

则

\[
D=D^\ast,
\qquad
\operatorname{tr}D=0.
\]

若 \(p_\kappa-p_{\kappa'}=(\kappa-\kappa')d\)，则

\[
\iota_\Sigma(p_\kappa)
-
\iota_\Sigma(p_{\kappa'})
=
(\kappa-\kappa')D.
\]

所以 \(\kappa\) 隐藏方向在量子载体中成为一个对角、迹为零的 Hermitian 扰动。它仍然是有限线性代数对象，并不需要把 \(\kappa\) 解释为物理叠加振幅。

### 命题 29.5（经典随机读出的 Fisher 收缩可由 CPTP 读出实现）

令 \(p_\theta\) 是 FIB 概率族，令 \(W\) 为随机核。对角提升满足

\[
\mathcal E_W(\iota_\Sigma(p_\theta))
=
\iota_A(Wp_\theta).
\]

因此输出 Fisher 信息正是前文定理 5.2 的 \(\mathcal I_{\mathrm{out}}\)，并满足

\[
\mathcal I_{\mathrm{out}}\le\mathcal I_{\mathrm{in}}.
\]

证明只使用定理 29.3 和定理 5.2。这里的结论是测量后经典 Fisher 信息的收缩，不等同于尚未定义的量子 Fisher 信息。

---

## 30. 有限 triangle quantum network

### 定义 30.1（三角量子源）

取三个有限维边 Hilbert 空间

\[
H_{AB},\qquad H_{BC},\qquad H_{CA},
\]

以及三个边源状态

\[
\omega_{AB}\in\mathsf D(H_{AB}^{A}\otimes H_{AB}^{B}),
\]

\[
\omega_{BC}\in\mathsf D(H_{BC}^{B}\otimes H_{BC}^{C}),
\]

\[
\omega_{CA}\in\mathsf D(H_{CA}^{C}\otimes H_{CA}^{A}).
\]

三角网络的独立源状态定义为

\[
\Omega
=
\omega_{AB}\otimes\omega_{BC}\otimes\omega_{CA}.
\]

这里“独立”只表示张量积结构。若边源本身是纠缠态，\(\Omega\) 仍是量子网络状态，但它不必具有经典隐变量分解。

### 定义 30.2（局部节点信道）

设

\[
\mathcal A:
\mathsf L(H_{CA}^{A}\otimes H_{AB}^{A})
\to
\mathsf L(K_A),
\]

\[
\mathcal B:
\mathsf L(H_{AB}^{B}\otimes H_{BC}^{B})
\to
\mathsf L(K_B),
\]

\[
\mathcal C:
\mathsf L(H_{BC}^{C}\otimes H_{CA}^{C})
\to
\mathsf L(K_C)
\]

均为 CPTP。网络输出状态为

\[
\rho_{ABC}
=
(\mathcal A\otimes\mathcal B\otimes\mathcal C)(\Omega),
\]

其中输入张量因子按各节点收到的两条边重新排列。

给定 POVM

\[
(M_a^A)_a,\qquad
(M_b^B)_b,\qquad
(M_c^C)_c,
\]

定义输出分布

\[
P(a,b,c)
=
\operatorname{tr}
\left[
(M_a^A\otimes M_b^B\otimes M_c^C)\rho_{ABC}
\right].
\]

### 定理 30.3（有限量子三角分布的归一化）

上式定义合法概率分布：

\[
P(a,b,c)\ge0,
\qquad
\sum_{a,b,c}P(a,b,c)=1.
\]

#### 证明

所有 POVM 元素和输出状态均正半定，所以每个概率非负。对所有输出求和：

\[
\sum_{a,b,c}P(a,b,c)
=
\operatorname{tr}
\left[
(I_{K_A}\otimes I_{K_B}\otimes I_{K_C})\rho_{ABC}
\right]
=
\operatorname{tr}\rho_{ABC}
=
1.
\]

证毕。

### 定理 30.4（经典 triangle-local 是量子网络的对角子类）

假设每个边源都是共享经典寄存器的对角状态，例如

\[
\omega_{AB}
=
\sum_{\alpha}\mu_{AB}(\alpha)
|\alpha\rangle\langle\alpha|_A
\otimes
|\alpha\rangle\langle\alpha|_B,
\]

其余两条边类似。假设节点信道在这些对角输入上先进行经典读取，再输出对角状态。则存在随机核

\[
A(a\mid\beta,\gamma),\quad
B(b\mid\gamma,\alpha),\quad
C(c\mid\alpha,\beta)
\]

使

\[
P(a,b,c)
=
\sum_{\alpha,\beta,\gamma}
\mu_{AB}(\alpha)
\mu_{BC}(\beta)
\mu_{CA}(\gamma)
A(a\mid\gamma,\alpha)
B(b\mid\alpha,\beta)
C(c\mid\beta,\gamma).
\]

#### 证明

把三个对角源状态代入张量积，得到

\[
\Omega
=
\sum_{\alpha,\beta,\gamma}
\mu_{AB}(\alpha)\mu_{BC}(\beta)\mu_{CA}(\gamma)
|\alpha,\beta,\gamma\rangle\langle\alpha,\beta,\gamma|.
\]

对角节点信道在每个输入三元组上给出一个合法输出分布。节点独立作用使输出条件概率分解为三个局部核的乘积。对 \(\alpha,\beta,\gamma\) 求和即可得到公式。证毕。

该定理只证明经典 triangle-local 分布嵌入量子网络的一个对角子类。一般纠缠源的量子三角分布不能由这一定理自动降为经典 triangle-local 分布。

---

## 31. 量子信道的 Dirichlet 单调性

前文的图 Dirichlet 形式使用向量差。量子网络中对应的有限维对象是状态之间的 trace-norm 差。

### 定义 31.1（量子图场）

令 \(G=(V,E,w)\) 为有限无向图，\(w_e\ge0\)。在每个节点 \(v\) 放置

\[
\rho_v\in\mathsf D(H).
\]

定义量子图场的 trace-norm Dirichlet 能量：

\[
\mathcal Q_G^{(1)}(\rho)
=
\sum_{e=(u,v)\in E}
w_e\|\rho_u-\rho_v\|_1^2.
\]

这是一个非负函数。它只测量节点状态之间的可区分性，不假设连续空间或物理距离。

### 定理 31.2（CPTP 分量作用的 Dirichlet 收缩）

设 \(\mathcal E:\mathsf L(H)\to\mathsf L(K)\) 为 CPTP。定义

\[
(\mathcal E_\ast\rho)_v=\mathcal E(\rho_v).
\]

则

\[
\boxed{
\mathcal Q_G^{(1)}(\mathcal E_\ast\rho)
\le
\mathcal Q_G^{(1)}(\rho).
}
\]

#### 证明

对 Hermitian \(X\)，trace norm 的对偶表达为

\[
\|X\|_1
=
\sup_{\|A\|_\infty\le1}
\operatorname{tr}(AX).
\]

由于 \(\mathcal E^\ast\) 是首一正映射，Kadison 不等式给出

\[
\|\mathcal E^\ast(A)\|_\infty
\le
\|A\|_\infty.
\]

因此

\[
\begin{aligned}
\|\mathcal E(X)\|_1
&=
\sup_{\|A\|_\infty\le1}
\operatorname{tr}(A\mathcal E(X))\\
&=
\sup_{\|A\|_\infty\le1}
\operatorname{tr}(\mathcal E^\ast(A)X)\\
&\le
\|X\|_1.
\end{aligned}
\]

每个 \(\rho_u-\rho_v\) 都是 Hermitian，故

\[
\|\mathcal E(\rho_u)-\mathcal E(\rho_v)\|_1
\le
\|\rho_u-\rho_v\|_1.
\]

平方并乘以 \(w_e\)，对所有边求和即得结论。证毕。

### 推论 31.3（与 FIB Dirichlet 形式的相容）

若所有 \(\rho_v\) 都是对角 FIB 状态

\[
\rho_v=\iota_\Sigma(p_v),
\]

则

\[
\|\rho_u-\rho_v\|_1
=
\|p_u-p_v\|_1.
\]

若 \(\mathcal E=\mathcal E_W\) 来自随机核 \(W\)，则

\[
\mathcal Q_G^{(1)}(Wp)
\le
\mathcal Q_G^{(1)}(p).
\]

因此，FIB 概率场的粗粒化是量子 CPTP Dirichlet 收缩定理在对角扇区的限制。

### 定义 31.4（相对熵与量子信息收缩接口）

对 \(\rho,\sigma\in\mathsf D(H)\)，在

\[
\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma
\]

时定义

\[
D(\rho\|\sigma)
=
\operatorname{tr}
\bigl[
\rho(\log\rho-\log\sigma)
\bigr],
\]

否则定义 \(D(\rho\|\sigma)=+\infty\)。

### 定理 31.5（CPTP 相对熵数据处理）

对任意 CPTP 映射 \(\mathcal E\)，有

\[
\boxed{
D(\mathcal E(\rho)\|\mathcal E(\sigma))
\le
D(\rho\|\sigma).
}
\]

这是作为外部有限维结果使用的量子相对熵数据处理定理。其证明依赖 Stinespring 表示将 $\mathcal E$ 分解为等距嵌入后偏迹、偏迹下相对熵单调性及等距共轭下相对熵不变性；这些依赖涉及矩阵对数、支撑条件、偏迹和 Klein 不等式。本节未给出这些中间结果的证明。

该定理的语义边界是明确的：它证明量子信道不能增加相对熵区分度，不直接给出引力、时空或物理热力学定律。

---

## 32. 量子网络的逆极限静态场

### 定义 32.1（量子层载体）

对每个层级 \(j\)，取有限维 Hilbert 空间 \(H_j\)，并取非空紧凸子集

\[
K_j\subseteq\mathsf D(H_j).
\]

令

\[
q_{j+1,j}:K_{j+1}\to K_j
\]

是由 CPTP 映射限制得到的连续仿射映射。

### 定理 32.2（量子 CPTP 逆极限的非空性）

若每个

\[
q_{j+1,j}:K_{j+1}\to K_j
\]

都是满射，则

\[
\mathfrak Q
=
\varprojlim_j(K_j,q_{j+1,j})
\]

是非空紧凸集。

#### 证明

有限维状态空间中的闭有界集合是紧的，连续仿射像保持紧性和凸性。所有 \(K_j\) 的乘积

\[
\prod_jK_j
\]

由 Tychonoff 定理紧。相容条件

\[
q_{j+1,j}(\rho_{j+1})=\rho_j
\]

是闭条件，因此逆极限是紧闭子集。对任意有限层截断，由逐次满射可构造相容有限链。于是这些有限约束集合具有有限交性质。紧性给出全体约束的交非空。坐标逐点凸组合保持相容性，因此逆极限凸。证毕。

这个定理把原来的静态场逆极限扩展到量子载体。它只说明存在一族层间相容的密度矩阵。它不说明存在连续时空，也不说明逆极限具有光滑结构。

### 推论 32.3（量子层与 FIB 层的并行载体）

若

\[
C_j^Q
=
\Phi_j
\times
\Pi_j
\times
N_j
\times
Z_j
\times
K_j
\]

且每一层的 bonding map 在各分量上连续仿射并满射，则

\[
\varprojlim_jC_j^Q
\]

非空紧凸。前四个分量来自 Auric FIB 图场，\(K_j\) 是量子状态分量。这个乘积构造是一个类型化统一载体，不等同于物理统一场方程。

---

## 33. 连接、holonomy 与引力候选几何

若希望把“引力”放入数学骨架，最小的无物理定义是把网络边解释为状态空间之间的可组合传输，并测量闭环传输偏离恒等的程度。

### 定义 33.1（量子连接）

令 \(G=(V,E)\) 为有限有向图。为每条边 \(e:u\to v\) 指定一个 CPTP 映射

\[
\mathcal E_e:\mathsf L(H_u)\to\mathsf L(H_v).
\]

若路径

\[
\gamma=e_n\cdots e_1
\]

首尾 Hilbert 空间相同，则定义路径传输

\[
\mathcal E_\gamma
=
\mathcal E_{e_n}\circ\cdots\circ\mathcal E_{e_1}.
\]

### 定义 33.2（holonomy 与曲率缺陷）

对首尾同为 \(H\) 的闭环 \(\gamma\)，定义

\[
\mathcal H_\gamma=\mathcal E_\gamma,
\qquad
\Omega_\gamma=\mathcal H_\gamma-\operatorname{id}_{\mathsf L(H)}.
\]

称

\[
\Omega_\gamma=0
\]

为该闭环的平坦条件。对 Hermitian 输入使用诱导范数

\[
\|T\|_{1\to1,\mathrm{Herm}}
=
\sup_{X=X^\ast,\ X\ne0}
\frac{\|T(X)\|_1}{\|X\|_1}.
\]

定义曲率缺陷大小为

\[
\|\Omega_\gamma\|_{1\to1,\mathrm{Herm}}.
\]

这是网络传输的代数不一致量。它是候选几何量，不能直接宣称为 Einstein 曲率。

### 定理 33.3（holonomy 缺陷的望远镜界）

若每条 \(\mathcal E_{e_k}\) 都是 CPTP，则

\[
\|\mathcal E_{e_k}\|_{1\to1,\mathrm{Herm}}\le1.
\]

于是

\[
\boxed{
\|\Omega_\gamma\|_{1\to1,\mathrm{Herm}}
\le
\sum_{k=1}^n
\|\mathcal E_{e_k}-\operatorname{id}\|_{1\to1,\mathrm{Herm}}.
}
\]

#### 证明

令

\[
E_k=\mathcal E_{e_k}.
\]

代数恒等式给出

\[
E_n\cdots E_1-I
=
\sum_{k=1}^{n}
E_n\cdots E_{k+1}
(E_k-I)
E_{k-1}\cdots E_1.
\]

CPTP 映射在 Hermitian trace norm 下是收缩，因此每个前后乘积的诱导范数不超过一。对上式取范数并使用三角不等式，得到

\[
\|E_n\cdots E_1-I\|
\le
\sum_{k=1}^n\|E_k-I\|.
\]

证毕。

该定理给出三角网络闭环的严格误差预算。如果每条边都接近恒等传输，则整个闭环的非平坦缺陷至多线性累积。

### 定义 33.4（图电阻度量）

给有限连通无向图 \(G=(V,E,w)\) 赋予正边权 \(w_e>0\)。令 \(B\) 为任意定向边界矩阵，\(W=\operatorname{diag}(w_e)\)，定义

\[
L_w=BWB^{\mathsf T}.
\]

对 \(u,v\in V\)，定义有效电阻

\[
R_w(u,v)
=
(e_u-e_v)^{\mathsf T}
L_w^\dagger
(e_u-e_v),
\]

其中 \(L_w^\dagger\) 是 Moore--Penrose 伪逆。

### 定理 33.5（有效电阻是度量）

\(R_w\) 满足：

\[
R_w(u,v)\ge0,
\qquad
R_w(u,v)=R_w(v,u),
\qquad
R_w(u,v)=0\Longleftrightarrow u=v,
\]

并且

\[
\sqrt{R_w(u,v)}
\]

满足三角不等式。因此 \(R_w\) 是有效电阻平方，\(\sqrt{R_w}\) 是由 Dirichlet 形式诱导的度量。

#### 证明

令

\[
T=L_w^{\dagger/2}.
\]

则

\[
R_w(u,v)
=
\|T(e_u-e_v)\|_2^2.
\]

对称性和非负性直接成立。图连通性说明 \(L_w\) 的核恰为常数向量，因此 \(T(e_u-e_v)=0\) 当且仅当 \(e_u=e_v\)，即 \(u=v\)。最后，\(\sqrt{R_w(u,v)}\) 是 Euclidean 空间中向量 \(T(e_u-e_v)\) 的距离，故满足三角不等式。证毕。

### 推论 33.6（边收缩与几何收缩）

若 \(w'_e\ge w_e\) 对所有边成立，则

\[
R_{w'}(u,v)\le R_w(u,v).
\]

#### 证明

有效电阻具有 Thomson 变分表达：

\[
R_w(u,v)
=
\min_{Bf=e_u-e_v}
\sum_{e\in E}\frac{f_e^2}{w_e}.
\]

增大 \(w_e\) 会逐项减小每个可行流的成本，故最小值不增。证毕。

如果给出一个具体的信道到边权函数

\[
\eta:\operatorname{CPTP}\to(0,\infty),
\qquad
w_e=\eta(\mathcal E_e),
\]

则 \(R_w\) 成为量子连接的候选可见几何。当前理论没有唯一指定 \(\eta\)，所以“信道产生引力度量”仍是桥接接口，而不是已证明的物理结论。

---

## 34. Hamiltonian、静态场与量子能级接口

### 定义 34.1（有限 Hamiltonian 通道）

令 \(H=H^\ast\) 是有限维 Hermitian 矩阵，定义

\[
\mathcal U_t(X)
=
e^{-itH}Xe^{itH}.
\]

则 \(\mathcal U_t\) 是 CPTP，且

\[
\mathcal U_{t+s}
=
\mathcal U_t\circ\mathcal U_s.
\]

### 定理 34.2（静态状态与能量守恒）

若 \(\rho_\ast\in\mathsf D(H)\) 满足

\[
[H,\rho_\ast]=0,
\]

则

\[
\mathcal U_t(\rho_\ast)=\rho_\ast
\]

对所有 \(t\) 成立。并且任意 \(\rho\in\mathsf D(H)\) 的能量期望

\[
E_H(\rho)=\operatorname{tr}(H\rho)
\]

满足

\[
E_H(\mathcal U_t(\rho))=E_H(\rho).
\]

#### 证明

交换关系给出

\[
e^{-itH}\rho_\ast e^{itH}=\rho_\ast.
\]

能量守恒由循环迹：

\[
\begin{aligned}
E_H(\mathcal U_t(\rho))
&=
\operatorname{tr}
\left(
He^{-itH}\rho e^{itH}
\right)\\
&=
\operatorname{tr}
\left(
e^{itH}He^{-itH}\rho
\right)\\
&=
\operatorname{tr}(H\rho).
\end{aligned}
\]

证毕。

### 定义 34.3（能级）

\(H\) 的谱

\[
\operatorname{Spec}(H)
=
\{E_1,\ldots,E_d\}
\]

定义为该有限量子模型的能级集合，按代数重数计数。

如果 \(H\) 由图 Dirichlet 矩阵、量子连接的对称化生成元或某个 FIB 扩张构造，那么这些 \(E_i\) 是该构造的谱值。将它们解释为物理能量，或者进一步解释为 RH 零点虚部，均需要额外的谱识别定理。

当前可严格写出的条件式桥接是：

\[
\begin{aligned}
&\text{若存在自伴 }H\text{，使其正则化谱行列式等于完成的 }\Xi\text{ 函数，}\\
&\text{则 }\Xi\text{ 的非平凡零点由 }H\text{ 的实谱参数化。}
\end{aligned}
\]

FIB、triangle network 和量子连接目前只提供构造候选 \(H\) 所需的有限输入类型，不自动给出该行列式恒等式。

---

## 35. 量子、FIB 与引力桥的保守账本

### Primitive

以下对象属于原始有限数学：

\[
\Sigma,\quad
\Delta(\Sigma),\quad
H,\quad
\mathsf D(H),\quad
\operatorname{CPTP},\quad
\otimes,\quad
\operatorname{tr},\quad
\text{POVM},\quad
G=(V,E,w),\quad
B,\quad
L_w.
\]

### Derived

以下结论由原始对象直接推出：

1. CPTP 映射的复合和张量积闭包；
2. FIB 概率律的对角量子嵌入；
3. 随机核的 measure--dephase--prepare CPTP 提升；
4. 有限 triangle quantum network 输出分布的归一化；
5. 经典 triangle-local 分布作为对角量子网络子类；
6. CPTP 对 trace-norm Dirichlet 能量的收缩；
7. 量子层载体在满射 bonding 下的逆极限非空性；
8. holonomy 缺陷的望远镜界；
9. 有效电阻的度量结构；
10. 有限 Hamiltonian 通道的静态性和能量守恒。

### Bridge

以下对象目前仍需要具体构造：

1. 从 FIB seam \(d\) 到非对角量子相干算子的自然提升；
2. 从有限 quantum triangle network 到完整 triangle-local inflation 证书的映射；
3. 从 CPTP 连接到唯一边权 \(\eta(\mathcal E_e)\)；
4. 从有效电阻或 holonomy 缺陷到 Einstein 曲率、引力势或时空度量；
5. 从 FIB/图 Dirichlet 生成元到自伴 Hamiltonian；
6. 从该 Hamiltonian 的正则化谱行列式到完成的 \(\Xi\) 函数；
7. 从量子能级到 RH 零点的重数保持和谱完备性。

因此当前“量子引力”在 Auric FIB 管线中的严格含义只能是：

\[
\boxed{
\begin{aligned}
&\text{量子层：有限维 CPTP 组合子和密度矩阵；}\\
&\text{网络层：独立源张量积与局部节点信道；}\\
&\text{场层：相容量子状态的逆极限；}\\
&\text{几何层：Dirichlet 形式、holonomy 缺陷和有效电阻；}\\
&\text{能级层：有限自伴算子的谱；}\\
&\text{物理解释：必须由独立桥接定理承担。}
\end{aligned}
}
\]

这套骨架把“引力”和“量子”都降为可检查的数学接口。它不从物理直觉反向定义数学对象，而是先在有限矩阵、凸集、图边界和谱理论中建立可形式化的闭环。



---

## 36. 外部量子网络锚点与证据边界

本节只登记外部结果在管线中的位置，不把外部论文的结论转写成 Auric FIB 的内部定理。

### 锚点 36.1（量子 inflation）

Smith、Wolfe 和 Spekkens 的 *Fully quantum inflation: quantum marginal problem constraints in the service of causal inference*（arXiv:2501.12320）把 inflation 方法推广到量子边缘问题，用量子边缘约束检验给定多方量子态是否兼容指定的量子因果结构，并专门讨论了 triangle scenario。

它支持本卷的类型分离：

\[
\text{经典 triangle-local 分布}
\subsetneq
\text{量子 triangle-network 输出}.
\]

相应的量子 inflation 证书依赖定义 30.1--30.2 的有限源状态、局部 CPTP 映射以及复制网络的量子边缘约束。后者及其证书在此尚未给出，因此不能从有限 CPTP 定义直接推出量子三角兼容性判定。

### 锚点 36.2（三角网络量子非局域性的实验语义）

Wang 等人的 *Experimental genuine quantum nonlocality in the triangle network*（arXiv:2401.15428）报告了三角网络结构中的量子相关实验，并针对 elegant distribution 给出量子非局域性的实验证据。

该结果只能作为以下桥接的实验语义背景：

\[
\text{有限量子源}
\longrightarrow
\text{局部节点测量}
\longrightarrow
\text{三角输出分布}.
\]

它不改变本卷的数学边界：实验相关性不提供 FIB 五态编码，也不证明任意 FIB 概率律具有三个独立量子源分解。

### 锚点 36.3（对本卷的最小影响）

外部量子网络结果对当前理论只增加两个可检验目标：

1. 给定有限 \(\omega_{AB},\omega_{BC},\omega_{CA}\) 和局部 CPTP 映射，生成完整输出态的量子 inflation 复制约束；
2. 给定 FIB 对角输出，判定它是否存在一个满足源独立性、维数上界和局部响应结构的量子 triangle lift。

在这两个目标完成以前，本文使用的关系仍然是：

\[
\text{FIB 对角量子嵌入}
\subseteq
\text{有限量子网络载体},
\]

而不是

\[
\text{任意 FIB 律}
=
\text{量子 triangle-network 律}.
\]



### 锚点 36.4（自旋网络中的纠缠与曲率）

*Curvature from multipartite entanglement in quantum gravity states*（Physical Review D 108, 046010, 2023）研究以图、自旋网络和非平凡 \(SU(2)\) holonomy 表示的量子几何，并分析多体纠缠与有界区域内禀曲率之间的关系。

它与本卷的关系是结构性的：

\[
\text{图连接}
+
\text{边 holonomy}
+
\text{量子态纠缠}
\longrightarrow
\text{曲率候选量}.
\]

本卷目前只使用一般有限 CPTP holonomy 缺陷

\[
\Omega_\gamma=\mathcal E_\gamma-\operatorname{id}
\]

和有效电阻度量。自旋网络论文并不证明这两个量等于其几何曲率；因此它只能支持后续构造的方向，不能升级当前的定理。

### 锚点 36.5（可叠加网络拓扑）

Arrighi、Durbec 和 Wilson 的 *Quantum networks theory*（Quantum 8, 1508, 2024）研究网络连接本身处于量子叠加的过程模型，包括连接、分裂和重连的相干演化。

这提示一个严格的后续扩展：把当前固定图 \(G=(V,E)\) 替换为有限图标签空间

\[
\mathcal G=\{G_1,\ldots,G_m\},
\]

并在

\[
\mathbb C^{\mathcal G}\otimes H_{\mathrm{field}}
\]

上定义 CPTP 映射。上述构造限于固定图和固定层间 bonding，因此不包含量子叠加拓扑。该扩展必须先定义图标签的状态空间、重连信道和逆极限相容性，不能从现有 holonomy 定义直接推导。



## 37. 有限图上的离散曲率证书

本节把“引力”先改写成有限 Dirichlet 载体上的曲率稳定性证书。曲率在这里是由有限矩阵和有限求和定义的函数不等式。它不被解释为 Einstein 曲率，也不自动产生连续时空。

### 定义 37.1（有限可逆图与 Markov 生成元）

令 \(V\) 是有限集合，令 \(\mu_x>0\) 且 \(\sum_{x\in V}\mu_x=1\)。令 \(c_{xy}=c_{yx}\ge0\)，\(c_{xx}=0\)，并假设由 \(c_{xy}>0\) 生成的无向图连通。定义

\[
(Lf)(x)
=
\frac1{\mu_x}
\sum_{y\in V}c_{xy}\bigl(f(y)-f(x)\bigr).
\]

在

\[
\langle f,g\rangle_\mu
=
\sum_{x\in V}\mu_x f(x)g(x)
\]

上，\(L\) 是自伴且非正。记 \(A=-L\)。定义 Dirichlet 双线性型

\[
\mathcal E(f,g)
=
-\langle f,Lg\rangle_\mu
=
\frac12\sum_{x,y\in V}
c_{xy}\bigl(f(x)-f(y)\bigr)\bigl(g(x)-g(y)\bigr).
\]

于是 \(\mathcal E(f)=\mathcal E(f,f)\ge0\)，且连通性给出

\[
\ker A=\operatorname{span}\{\mathbf 1\}.
\]

### 定义 37.2（有限 carré du champ 与二阶型）

对实函数 \(f,g:V\to\mathbb R\)，定义

\[
\Gamma(f,g)
=
\frac12\left(
L(fg)-fLg-gLf
\right),
\qquad
\Gamma(f)=\Gamma(f,f).
\]

直接展开得到

\[
\Gamma(f,g)(x)
=
\frac1{2\mu_x}
\sum_yc_{xy}
\bigl(f(y)-f(x)\bigr)
\bigl(g(y)-g(x)\bigr),
\]

因此

\[
\sum_x\mu_x\Gamma(f)(x)=\mathcal E(f).
\]

定义二阶型

\[
\Gamma_2(f)
=
\frac12L\Gamma(f)-\Gamma(f,Lf).
\]

这里 \(\Gamma_2\) 是有限函数 \(V\to\mathbb R\)。所有量都是有限和与有限矩阵乘法，不需要先给出连续流形。

### 定义 37.3（有限 \(CD_G(K,\infty)\) 证书）

给定 \(K\in\mathbb R\)，称有限图满足 \(CD_G(K,\infty)\)，如果对任意 \(f:V\to\mathbb R\) 和任意 \(x\in V\)，有

\[
\Gamma_2(f)(x)\ge K\Gamma(f)(x).
\]

这一定义是一个可检查的有限二次型不等式。对于固定 \(G,\mu,c\)，最大的允许 \(K\) 是一个有限图证书，可通过有限维半正定条件或广义 Rayleigh 商验证。

### 定理 37.4（离散曲率控制谱隙与 Dirichlet 衰减）

设有限图满足 \(CD_G(K,\infty)\)，且 \(K>0\)。则：

1. 对任意 \(f\)，
   \[
   \sum_x\mu_x\Gamma_2(f)(x)
   =
   \|Lf\|_\mu^2,
   \qquad
   \|Lf\|_\mu^2\ge K\mathcal E(f).
   \]

2. 令 \(\lambda_1>0\) 为 \(A=-L\) 在常数正交子空间上的最小特征值，则
   \[
   \lambda_1\ge K.
   \]

3. 令 \(P_t=e^{tL}\)。则
   \[
   \mathcal E(P_tf)
   \le
   e^{-2Kt}\mathcal E(f).
   \]

#### 证明

由于 \(\sum_x\mu_xLh(x)=0\)，且

\[
\sum_x\mu_x\Gamma(f,Lf)(x)
=
-\langle f,L^2f\rangle_\mu,
\]

有

\[
\begin{aligned}
\sum_x\mu_x\Gamma_2(f)(x)
&=
\frac12\sum_x\mu_xL\Gamma(f)(x)
-
\sum_x\mu_x\Gamma(f,Lf)(x)\\
&=
\langle f,L^2f\rangle_\mu\\
&=
\|Lf\|_\mu^2.
\end{aligned}
\]

积分 \(CD_G(K,\infty)\) 即得第一项的不等式。

若 \(Af=\lambda f\)，且 \(f\perp_\mu\mathbf1\)，则 \(Lf=-\lambda f\)，从而

\[
\|Lf\|_\mu^2
=
\lambda^2\|f\|_\mu^2,
\qquad
\mathcal E(f)
=
\lambda\|f\|_\mu^2.
\]

因此 \(\lambda^2\ge K\lambda\)。对 \(\lambda>0\) 消去一个 \(\lambda\)，得到 \(\lambda\ge K\)。这证明第二项。

令 \(f_t=P_tf\)。由自伴性，

\[
\frac d{dt}\mathcal E(f_t)
=
2\langle Lf_t,-Lf_t\rangle_\mu
=
-2\|Lf_t\|_\mu^2
\le
-2K\mathcal E(f_t).
\]

Gronwall 不等式给出第三项。证毕。

这个定理把“场的稳定性”变成了明确的谱估计：\(K\) 是有限图热流的能量衰减率下界。它没有把 \(K\) 解释成物理引力常数。

### 定理 37.5（曲率证书对有效电阻的控制）

沿用定义 37.1，令

\[
b_{uv}(x)
=
\frac{\mathbf1_{\{x=u\}}}{\mu_u}
-
\frac{\mathbf1_{\{x=v\}}}{\mu_v}.
\]

则 \(b_{uv}\perp_\mu\mathbf1\)，并满足

\[
\langle b_{uv},f\rangle_\mu=f(u)-f(v).
\]

定义加权有效电阻

\[
R_\mu(u,v)
=
\langle b_{uv},A^\dagger b_{uv}\rangle_\mu,
\]

其中 \(A^\dagger\) 表示相对于 \(\langle\cdot,\cdot\rangle_\mu\) 的谱伪逆：它在 \(\mathbf1^\perp_\mu\) 上等于 \(A^{-1}\)，在常数方向上为零。若 \(CD_G(K,\infty)\) 且 \(K>0\)，则

\[
\boxed{
R_\mu(u,v)
\le
\frac{\mu_u^{-1}+\mu_v^{-1}}{K}.
}
\]

#### 证明

定理 37.4 给出 \(A\ge K I\) 在常数正交子空间上的谱序。故

\[
A^\dagger\le K^{-1}I
\]

在该子空间上成立。于是

\[
R_\mu(u,v)
\le
K^{-1}\|b_{uv}\|_\mu^2
=
K^{-1}\left(\frac1{\mu_u}+\frac1{\mu_v}\right).
\]

证毕。

如果令 \(\phi_{uv}=A^\dagger b_{uv}\)，则 \(A\phi_{uv}=b_{uv}\) 且

\[
R_\mu(u,v)
=
\mathcal E(\phi_{uv}).
\]

因此曲率下界控制有限场对点源差分的静态响应幅度。这个响应是离散 Poisson 方程的解。把它称作“引力势”需要额外的物理桥接，数学定理本身只给出有效电阻和 Dirichlet 能量界。

### 定义 37.6（层级曲率数据）

对第 \(j\) 层的 \((V_j,\mu_j,c_j)\)，定义

\[
K_j^{\mathrm{BE}}
=
\sup\{K:\ CD_{G_j}(K,\infty)\text{ 成立}\}.
\]

这给出一个完全由有限层矩阵确定的曲率序列

\[
(K_0^{\mathrm{BE}},K_1^{\mathrm{BE}},\ldots).
\]

若层间 bonding 还满足额外的 \(\Gamma\)-交换和 \(\Gamma_2\)-单调条件，才可以比较 \(K_j^{\mathrm{BE}}\) 与 \(K_{j+1}^{\mathrm{BE}}\)。Dirichlet 能量收缩本身并不自动推出曲率下界单调性。

## 38. 有限量子网络的 detailed-balance Dirichlet 曲率

本节使用有限维矩阵定义量子层。为了避免把经典 \(CD_G\) 不加证明地推广到非交换代数，量子曲率先定义为 detailed-balance 生成元上的二次型谱证书。

### 定义 38.1（有限 detailed-balance 量子半群）

令 \(H\) 是有限维复 Hilbert 空间，令 \(\sigma\in\mathsf D(H)\) 严格正定。对 \(A,B\in\mathsf L(H)\)，定义 GNS 内积

\[
\langle A,B\rangle_\sigma
=
\operatorname{tr}
\left(
\sigma^{1/2}A^\ast\sigma^{1/2}B
\right).
\]

令 \(T_t=e^{t\mathcal L}\) 是有限维 Heisenberg 量子 Markov 半群，其中每个 \(T_t\) 首一完全正，\(\mathcal L(I)=0\)，其 Schrödinger 伴随保持 \(\sigma\)：

\[
\mathcal L^\ast(\sigma)=0.
\]

并假设 \(-\mathcal L\) 在 GNS 内积下非负。进一步要求 GNS detailed balance

\[
\langle A,\mathcal L B\rangle_\sigma
=
\langle\mathcal L A,B\rangle_\sigma.
\]

定义量子 Dirichlet 型

\[
\mathcal E_\sigma(A)
=
\langle A,-\mathcal L A\rangle_\sigma.
\]

在 \(A\) 为常数方向之外，\(\mathcal E_\sigma(A)\ge0\)。

### 定义 38.2（量子二阶型曲率证书）

给定 \(K\in\mathbb R\)，称 \((\mathcal L,\sigma)\) 满足 \(QCD(K)\)，如果对所有满足

\[
\langle I,A\rangle_\sigma=0
\]

的 \(A\) 都有

\[
\langle\mathcal L A,\mathcal L A\rangle_\sigma
\ge
K\mathcal E_\sigma(A).
\]

左侧是生成元的二阶 Hilbert 型，右侧是一阶 Dirichlet 型。这个定义是有限矩阵不等式。它不宣称已经得到一般意义的非交换 Bakry–Émery \(\Gamma_2\)。

### 定理 38.3（量子曲率控制谱隙和衰减）

若 \(QCD(K)\) 且 \(K>0\)，则：

1. \(-\mathcal L\) 在 \(I^\perp\) 上的每个非零特征值 \(\lambda\) 满足 \(\lambda\ge K\)；
2. 对所有 \(A\)，
   \[
   \mathcal E_\sigma(T_tA)
   \le
   e^{-2Kt}\mathcal E_\sigma(A);
   \]
3. 记
   \[
   A_0=A-\langle I,A\rangle_\sigma I,
   \]
   则
   \[
   \|T_tA_0\|_\sigma
   \le
   e^{-Kt}\|A_0\|_\sigma.
   \]

#### 证明

由于 detailed balance，\(-\mathcal L\) 是有限维 GNS Hilbert 空间上的自伴非负算子。若 \(-\mathcal L A=\lambda A\)，且 \(A\perp_\sigma I\)，则

\[
\|\mathcal L A\|_\sigma^2
=
\lambda^2\|A\|_\sigma^2,
\qquad
\mathcal E_\sigma(A)
=
\lambda\|A\|_\sigma^2.
\]

\(QCD(K)\) 给出 \(\lambda^2\ge K\lambda\)，所以 \(\lambda\ge K\)。这证明第一项。

令 \(A_t=T_tA\)。由自伴性，

\[
\frac d{dt}\mathcal E_\sigma(A_t)
=
2\langle\mathcal L A_t,-\mathcal L A_t\rangle_\sigma
=
-2\|\mathcal L A_t\|_\sigma^2
\le
-2K\mathcal E_\sigma(A_t).
\]

Gronwall 不等式给出第二项。

第一项的谱结论还给出 \(-\mathcal L\ge K I\) 在 \(I^\perp\) 上。于是

\[
\frac d{dt}\|T_tA_0\|_\sigma^2
=
-2\mathcal E_\sigma(T_tA_0)
\le
-2K\|T_tA_0\|_\sigma^2.
\]

再次应用 Gronwall 得到第三项。证毕。

### 定理 38.4（独立量子边的张量化）

对有限边指标集 \(E\)，令

\[
H=\bigotimes_{e\in E}H_e,
\qquad
\sigma=\bigotimes_{e\in E}\sigma_e.
\]

每个边生成元 \(\mathcal L_e\) 在 \((H_e,\sigma_e)\) 上满足 \(QCD(K_e)\)。将其提升为

\[
\widehat{\mathcal L}_e
=
I_{\bar e}\otimes\mathcal L_e,
\qquad
\mathcal L_{\mathrm{net}}
=
\sum_{e\in E}\widehat{\mathcal L}_e.
\]

则 \(\mathcal L_{\mathrm{net}}\) 满足

\[
QCD\left(\min_{e\in E}K_e\right).
\]

#### 证明

不同边作用在不同张量因子上，因此 \(\widehat{\mathcal L}_e\) 两两交换，并且在乘积 GNS 内积下自伴。有限维谱定理给出共同特征基。共同特征向量的 \(-\mathcal L_{\mathrm{net}}\) 特征值为

\[
\lambda_{\mathrm{net}}
=
\sum_{e\in E}\lambda_e,
\]

其中每个 \(\lambda_e\) 非负。若共同特征向量不在常数方向，则至少一个 \(\lambda_e>0\)，故

\[
\lambda_{\mathrm{net}}
\ge
\min_{e\in E}K_e.
\]

对共同特征基逐项应用

\[
\lambda_{\mathrm{net}}^2
\ge
\left(\min_eK_e\right)\lambda_{\mathrm{net}}
\]

并线性延拓，得到 \(QCD(\min_eK_e)\)。证毕。

这个张量化结果与 triangle quantum network 的源积结构相容。它只处理独立边生成元的乘积模型。一般节点 CPTP 信道会引入非交换耦合，除非额外证明 detailed balance、共同不变状态和相应二阶型不等式，否则不能使用该定理。

## 39. 离散曲率、量子网络与“引力”之间的桥接账本

当前可严格登记的对象是：

\[
\begin{array}{c|c}
\text{数学层} & \text{可验证对象}\\
\hline
\text{静态场} & (\Phi_j,\Pi_j,N_j,Z_j)\\
\text{经典几何} & \mathcal E_j,\Gamma_j,\Gamma_{2,j},K_j^{\mathrm{BE}}\\
\text{有效距离} & R_{\mu_j}(u,v),\sqrt{R_{\mu_j}(u,v)}\\
\text{量子网络} & (H_j,\sigma_j,\mathcal L_j,T_{j,t})\\
\text{量子几何} & \mathcal E_{\sigma_j},QCD(K_j^Q)\\
\text{逆极限} & \varprojlim_j C_j,\quad \varprojlim_jK_j
\end{array}
\]

由这些定义已经证明：

\[
\begin{aligned}
CD_G(K,\infty)
&\Longrightarrow
\lambda_1(A)\ge K
\Longrightarrow
\mathcal E(P_tf)\le e^{-2Kt}\mathcal E(f),\\
CD_G(K,\infty)
&\Longrightarrow
R_\mu(u,v)\le
(\mu_u^{-1}+\mu_v^{-1})/K,\\
QCD(K)
&\Longrightarrow
\operatorname{Spec}(-\mathcal L|_{I^\perp})\subseteq[K,\infty),\\
QCD(K)
&\Longrightarrow
\mathcal E_\sigma(T_tA)\le e^{-2Kt}\mathcal E_\sigma(A).
\end{aligned}
\]

“场产生引力”的纯数学版本只能先写成：

\[
\text{静态 Dirichlet 场}
\longrightarrow
\text{有限曲率证书}
\longrightarrow
\text{谱隙与响应界}
\longrightarrow
\text{有效网络几何}.
\]

要把这条链升级为物理引力，还需独立证明至少一个具体桥接：

1. 从 \(K_j^{\mathrm{BE}}\) 或 \(K_j^Q\) 到某个度量测度极限的 Ricci 型下界；
2. 从该度量测度极限到光滑黎曼结构的维数、非塌缩、正则性和坐标重构；
3. 从静态 Poisson 响应到一个具有明确单位和变分原理的物理势；
4. 从曲率证书到 Einstein 型场方程，或证明该方程是某个有限能量泛函的 Euler–Lagrange 方程；
5. 从量子网络生成元到同一极限几何中的量子 Hamiltonian 或谱三元组；
6. 从此自伴谱数据到 RH 的完整零点空间和谱行列式恒等式。

因此，当前理论只支持以下条件式陈述：

\[
\boxed{
\begin{aligned}
&\text{若有限层曲率证书在 bonding 下具有统一下界，}\\
&\text{且 Dirichlet 形式满足共同宿主空间中的 Mosco 条件，}\\
&\text{则可以尝试构造带稳定谱隙和有限响应界的度量测度极限。}
\end{aligned}
}
\]

这仍是数学极限问题，不是已经证明的引力理论。尤其不能从 \(CD_G\)、\(QCD\)、有效电阻或 holonomy 单独推出 Ricci 张量、Einstein 张量、时空因果结构或物理能量。

### 外部数学锚点

离散熵曲率与 Markov 链的研究已经给出另一条成熟的几何路线：有限 Markov 链可用熵沿离散运输度量的凸性定义 Ricci 型下界，并证明曲率界的张量化。该路线可作为本节 \(CD_G\) 证书之后的后续桥接，但不能把两种曲率定义视为同一对象。参考 Erbar--Maas, *Ricci curvature of finite Markov chains via convexity of the entropy*, [arXiv:1111.2687](https://arxiv.org/abs/1111.2687)。

因此，当前文件同时保留两条可检验路线：

\[
\begin{aligned}
&\text{有限 }CD_G\text{ 二次型}
\longrightarrow
\text{谱隙、热流衰减、有效电阻界};\\
&\text{离散熵凸性曲率}
\longrightarrow
\text{运输度量、熵梯度流、可能的 metric-measure 极限}.
\end{aligned}
\]

两条路线的共同输入是有限 Markov/Dirichlet 数据。它们的极限识别、相互等价及其与物理引力的关系，都必须另行证明。


## 40. FIB Fisher 结构作为量子 Fisher 几何的精确对角限制

前文已经把五态概率律嵌入对角密度矩阵。本节证明一个可以直接形式化的精确桥接：在可交换的对角扇区，量子 SLD Fisher 信息恰好等于 FIB 的经典 Fisher 信息。因此这里的“量子几何”不是类比，而是同一有限矩阵计算在两个记号系统中的相等。

### 定义 40.1（SLD 与量子 Fisher 型）

令 \(\rho_\theta\) 是有限维严格正定密度矩阵族，令

\[
\dot\rho_\theta
=
\frac{d}{d\theta}\rho_\theta.
\]

定义对称对数导数 \(L_\theta\) 为满足

\[
\dot\rho_\theta
=
\frac12\left(
\rho_\theta L_\theta+L_\theta\rho_\theta
\right)
\]

的 Hermitian 矩阵。定义 SLD 量子 Fisher 信息

\[
F_Q(\rho_\theta)
=
\operatorname{tr}
\left(
\rho_\theta L_\theta^2
\right).
\]

在本节中只处理严格正定有限维状态，避免支撑变化带来的额外伪逆条件。

### 定理 40.2（对角量子 Fisher 等于 FIB Fisher）

令

\[
\rho_\kappa
=
\iota_\Sigma(p_\kappa)
=
\sum_{s\in\Sigma}p_{\kappa,s}|s\rangle\langle s|,
\]

并假设 \(\kappa\) 位于纤维内部，使得 \(p_{\kappa,s}>0\) 对所有 \(s\in\Sigma\)。令

\[
d=(1,-1,0,-1,1),
\qquad
\partial_\kappa p_\kappa=d.
\]

则

\[
L_\kappa
=
\operatorname{diag}
\left(
\frac{d_s}{p_{\kappa,s}}
\right)_{s\in\Sigma},
\]

且

\[
\boxed{
F_Q(\rho_\kappa)
=
\sum_{s\in\Sigma}
\frac{d_s^2}{p_{\kappa,s}}
=
\mathcal I(\kappa).
}
\]

因此 Bures 线元（取标准约定 \(ds_B^2=\tfrac14F_Q\,d\kappa^2\)）满足

\[
\boxed{
ds_B^2
=
\frac14\mathcal I(\kappa)\,d\kappa^2.
}
\]

#### 证明

\(\rho_\kappa\) 和 \(\partial_\kappa\rho_\kappa\) 都是对角矩阵，因此 SLD 方程逐个对角元化为

\[
d_s=p_{\kappa,s}(L_\kappa)_{ss}.
\]

故

\[
(L_\kappa)_{ss}
=
\frac{d_s}{p_{\kappa,s}}.
\]

代入量子 Fisher 定义得到

\[
\begin{aligned}
F_Q(\rho_\kappa)
&=
\sum_s p_{\kappa,s}
\left(\frac{d_s}{p_{\kappa,s}}\right)^2\\
&=
\sum_s\frac{d_s^2}{p_{\kappa,s}}
=
\frac1{p_0}
+\frac1{p_2}
+\frac1{p_5}
+\frac1{p_{25}}
=
\mathcal I(\kappa).
\end{aligned}
\]

Bures 线元的公式直接给出第二项。证毕。

该定理说明：FIB 的隐藏 seam 并不是一个凭空增加的“量子变量”。它在对角量子态流形中对应一个严格定义的 Hermitian 切向扰动。若要研究真正的量子相干，还必须允许非对角密度矩阵并给出额外的非交换动力学。

### 定理 40.3（节点乘积场的 Fisher 可加性）

令 \(V\) 为有限图顶点集。每个顶点有严格正定 FIB 对角态

\[
\rho_{v,\kappa_v}
=
\iota_\Sigma(p_{\kappa_v}),
\]

并定义乘积状态

\[
\rho_{\boldsymbol\kappa}
=
\bigotimes_{v\in V}\rho_{v,\kappa_v}.
\]

令 \(u_v=\partial_{\kappa_v}p_{\kappa_v}=d\)。则对任意向量 \(\dot{\boldsymbol\kappa}=(\dot\kappa_v)_v\)，有

\[
\boxed{
F_Q(\rho_{\boldsymbol\kappa};\dot{\boldsymbol\kappa})
=
\sum_{v\in V}
\dot\kappa_v^{\,2}\mathcal I_v(\kappa_v).
}
\]

#### 证明

乘积状态的导数为

\[
\dot\rho
=
\sum_{v\in V}
\dot\kappa_v
\left(
\bigotimes_{w<v}\rho_w
\right)
\otimes
\dot\rho_v
\otimes
\left(
\bigotimes_{w>v}\rho_w
\right).
\]

每个局部 SLD 为

\[
L_v=\operatorname{diag}(d_s/p_{v,s}),
\qquad
\operatorname{tr}(\rho_vL_v)=\operatorname{tr}(\dot\rho_v)=0.
\]

因此全局 SLD 为

\[
L
=
\sum_{v\in V}
\dot\kappa_v
\,
I\otimes\cdots\otimes L_v\otimes\cdots\otimes I.
\]

计算 \(\operatorname{tr}(\rho L^2)\) 时，交叉项 \(v\ne w\) 含有因子

\[
\operatorname{tr}(\rho_vL_v)
\operatorname{tr}(\rho_wL_w)=0.
\]

剩余对角项为

\[
\sum_v\dot\kappa_v^{\,2}
\operatorname{tr}(\rho_vL_v^2)
=
\sum_v\dot\kappa_v^{\,2}\mathcal I_v(\kappa_v).
\]

证毕。

### 推论 40.4（层级 FIB Fisher 能量的量子解释）

如果第 \(j\) 层场在每个节点使用独立乘积态，并将节点权重吸收到参数速度中，则

\[
\mathcal I_j(p;u)
=
F_Q(\rho_j;\dot{\boldsymbol\kappa})
\]

是该层乘积量子态沿 FIB seam 方向的 SLD Fisher 信息。由前文定理 20.4 的随机粗粒化收缩，

\[
F_Q(\mathcal E_j(\rho_j);\dot{\mathcal E}_j)
\le
F_Q(\rho_j;\dot{\rho}_j)
\]

在对角随机读出层上成立。

因此当前架构可以严格写成：

\[
\text{FIB 隐藏 seam}
\longrightarrow
\text{对角密度矩阵切向量}
\longrightarrow
\text{SLD Fisher 几何}
\longrightarrow
\text{CPTP 粗粒化收缩}.
\]

这条链条仍然只使用有限概率、有限矩阵和 CPTP 映射。它还没有给出引力，也没有把 FIB 的五态载体识别成物理量子系统。


---

## 41. Typed unified-field architecture

The phrase “one unified field” becomes mathematically usable only after the field, its observations, its reference state, and its generator are typed separately. Define a finite or inverse-limit realization

\[
\mathfrak U=
(\mathcal X,\mathcal B,\mathcal K,\mathsf O,\pi,E,S,L,M,B,\mathsf G,\mathsf C),
\]

where:

- \(\mathcal X\) is the state carrier. It may be a finite probability carrier, a finite-dimensional density-matrix state space, a graph field, or a compatible inverse-limit field;
- \(\mathcal B\) is the observable/context family;
- \(\mathcal K\) is the finite incidence, cochain, or graph complex that records locality and boundary;
- \(\mathsf O:\mathcal X\to\mathcal Y\) is a selected observation or readout;
- \(\pi\) is a reference state, such as a Gibbs state, product source law, equilibrium law, or FIB completion;
- \(E\) and \(S\) are energy and entropy functionals;
- \(L\) is the reversible operator and \(M\) is the dissipative operator;
- \(B\) is an external port or source map;
- \(\mathsf G\) is the state generator;
- \(\mathsf C\) is a family of conserved quantities.

The primitive object is this typed architecture, rather than an identification of all physical theories with one untyped variable. A realization is structure-preserving when

\[
L_x^*=-L_x,\qquad
M_x^*=M_x\succeq 0,
\]

and the GENERIC degeneracy conditions hold:

\[
L_x\,dS_x=0,\qquad
M_x\,dE_x=0.
\]

The closed generator is

\[
\dot x
=
\mathsf G(x)
=
L_x\,dE_x+M_x\,dS_x.
\tag{41.1}
\]

For an open port, add \(B(x)u\). The finite-dimensional calculation is exact:

\[
\dot E
=
\langle dE,L\,dE\rangle
+
\langle dE,M\,dS\rangle
=
0,
\]

and

\[
\dot S
=
\langle dS,L\,dE\rangle
+
\langle dS,M\,dS\rangle
=
\langle dS,M\,dS\rangle
\geq 0.
\tag{41.2}
\]

With a port and output \(y=B^*dE\),

\[
\dot E=y^\top u,\qquad
\dot S=\langle dS,M\,dS\rangle.
\tag{41.3}
\]

At inverse temperature \(\beta\), define

\[
F_\beta=E-\beta^{-1}S.
\]

For a purely dissipative isothermal realization written as

\[
\dot x=(L-M)dF_\beta,
\]

one obtains

\[
\dot F_\beta
=
-\langle dF_\beta,M\,dF_\beta\rangle
\leq 0.
\tag{41.4}
\]

Equations (41.1)–(41.4) express the following mathematical decomposition: dynamics is the generator and its trajectory, thermodynamics is a reference-dependent monotone functional, and current or forcing enters through a port. The same algebra supports classical, graph, and finite quantum realizations. It does not by itself identify their physical units or continuum limits.

The GENERIC interpretation of dissipative electromagnetism has been developed explicitly by coarse-graining microscopic Maxwell dynamics and writing macroscopic Maxwell equations in the reversible-irreversible form. This is a useful external anchor for the present typed interface. See Jelić, Hütter, and Öttinger, arXiv:1001.0899.

## 42. Observation closure is the unifying criterion

Given a state observation

\[
\mathsf O:\mathcal X\to\mathcal Y
\]

and a generator \(\mathsf G\), define the closure residual

\[
\mathcal R_{\mathsf O}(x)
=
D\mathsf O_x[\mathsf G(x)]
-
\overline{\mathsf G}(\mathsf O(x)),
\tag{42.1}
\]

whenever a candidate reduced generator \(\overline{\mathsf G}\) has been chosen. Exact autonomous closure is the equation

\[
\mathcal R_{\mathsf O}=0.
\tag{42.2}
\]

For a flow \(\Phi_\tau\), (42.2) is equivalent to the intertwining relation

\[
\mathsf O\circ\Phi_\tau
=
\overline\Phi_\tau\circ\mathsf O.
\tag{42.3}
\]

Thus the same criterion can be instantiated at different layers:

- in the classical predictive setting, \(OA=KO\) is exact finite-dimensional closure;
- for FIB, \(\mathsf O_{\mathrm{FIB}}(p)=(X,Y,Z)\), and closure fails when the projected generator depends on \(\kappa\);
- for quantum observables, closure is invariance of the observable algebra under \(A\mapsto i[H,A]+\mathcal D^\dagger(A)\);
- for electromagnetism, the residual contains unobserved field components, gauge holonomy, and boundary port terms;
- for hidden-memory elimination, the residual is represented by a memory kernel or a conditional prediction defect.

The quantity \(\mathcal R_{\mathsf O}\) is the rigorous version of “information escape” at the dynamical level. A static fiber can be nontrivial even when a statistic is currently constant. A dynamic escape occurs when the generator moves two points in the same observation fiber into distinguishable future observations. Consequently, the correct order is

\[
\text{state carrier}
\longrightarrow
\text{observation quotient}
\longrightarrow
\text{generator}
\longrightarrow
\text{closure residual}.
\]

This also gives a precise distinction between a static field and an autonomous observed field. A field may exist as a compatible inverse-limit state while its current finite readout fails to close under the generator.

## 43. Current as a derived conservation flux

Let \(C^0(\mathcal K)\) be node quantities and \(C^1(\mathcal K)\) oriented edge fluxes. Let

\[
B:C^1(\mathcal K)\to C^0(\mathcal K)
\]

be the signed incidence divergence. A node density \(q\) and edge current \(j\) obey

\[
\dot q=-Bj.
\tag{43.1}
\]

For a closed graph, \(\mathbf 1^\top B=0\), hence

\[
\frac{d}{d\tau}\mathbf 1^\top q=0.
\tag{43.2}
\]

This is the finite form of a continuity equation. Given a constitutive mobility \(K\succeq0\) and a node potential \(\mu(q)\), the gradient-flow current is

\[
j=-K B^\top \mu(q),
\qquad
\dot q=B K B^\top\mu(q).
\tag{43.3}
\]

The sign convention may be reversed by choosing \(B\) as an in-flow rather than out-flow divergence. The invariant statement is that current is an edge flux whose divergence changes the local conserved quantity.

For a general conserved observable \(Q:\mathcal X\to\mathbb R\), the field-generated current is the derived rate

\[
I_Q(x)=dQ_x[\mathsf G(x)].
\tag{43.4}
\]

If \(Q\) is localizable, (43.4) decomposes into boundary fluxes of the form (43.1). Therefore the mathematically correct version of “electric current is a result of the field” is:

\[
\text{current}
=
\text{the conserved flux induced by the coupled field generator},
\]

under an explicit constitutive law, action, or port model. In elementary Maxwell equations \(j^\mu\) may be supplied as an external source. In a coupled matter-gauge theory, it is obtained by varying the matter action with respect to the gauge potential, and local gauge invariance gives its continuity equation. Charge conservation alone determines the Maxwell source equations only after constitutive and boundary assumptions are supplied. See De Zela, arXiv:physics/0506054.

On a finite cochain complex, the gauge realization is

\[
A\in C^1(\mathcal K),\qquad
F=d_1A,\qquad
d_1d_0=0.
\]

The identity \(d_1d_0=0\) is the discrete analogue of \(d^2=0\), hence the homogeneous field constraint is structural. The inhomogeneous equation couples the codifferential of \(F\) to the current \(j\). This is the bridge from the graph incidence carrier to electromagnetic curvature. The field \(A\), curvature \(F\), and current \(j\) occupy different typed slots and should not be collapsed into the same variable.

The triangle network has a related incidence pattern, but its product-source condition is a probability factorization on hidden edge variables. It is not the same object as the divergence of an edge current. The two structures can be placed on one typed carrier only after their maps and constraints are separately defined.

## 44. Thermodynamics is relative to a reference and an observation level

For a reference state \(\pi_\beta\), define the relative free-energy defect

\[
\mathfrak F_\beta(\rho)
=
\beta^{-1}D(\rho\Vert\pi_\beta),
\tag{44.1}
\]

up to an additive reference constant. In a finite Gibbs realization

\[
\pi_\beta
=
\frac{e^{-\beta H}}{\operatorname{tr}(e^{-\beta H})},
\]

this is equivalent to

\[
\mathfrak F_\beta(\rho)
=
\operatorname{tr}(H\rho)-\beta^{-1}S_{\mathrm{vN}}(\rho)
-\text{constant}.
\tag{44.2}
\]

The word “relative” has two independent meanings in the project:

1. the state is compared with a chosen reference equilibrium or product state;
2. the observer sees only a quotient \(\mathsf O(\rho)\), so the measured defect is relative to an observation algebra.

For a coarse-graining \(\mathsf O\) represented by a completely positive trace-preserving map,

\[
D(\rho\Vert\pi_\beta)
\geq
D(\mathsf O\rho\Vert\mathsf O\pi_\beta).
\tag{44.3}
\]

Define the lost relative information

\[
\mathfrak I_{\mathsf O}(\rho\Vert\pi_\beta)
=
D(\rho\Vert\pi_\beta)
-
D(\mathsf O\rho\Vert\mathsf O\pi_\beta)
\geq 0.
\tag{44.4}
\]

This is the observation-level information ledger. It is the mathematically controlled version of local information escape. It depends on \(\mathsf O\) and \(\pi_\beta\); it is not an absolute scalar called “heat”.

For the FIB carrier, \(\mathsf O_{\mathrm{FIB}}(p)=(X,Y,Z)\) forgets \(\kappa\). On the sector \(z=0\), the conditional defect is

\[
(1-Z)
D\!\left(
p_{xy\mid z=0}
\middle\|
p_{x\mid z=0}p_{y\mid z=0}
\right),
\]

which vanishes exactly at

\[
(1-Z)\kappa-XY=0.
\]

The hidden joint mode \(25\) therefore provides a finite exact example of a reference-dependent, observation-dependent thermodynamic defect.

For classical Markov dynamics, the relative free-energy functional decreases under detailed-balance evolution. The entropy-production and free-energy identities separate spontaneous relaxation from externally maintained housekeeping dissipation. See Ge and Qian, arXiv:0911.3984. For quantum Markov semigroups, quantum detailed balance gives the corresponding equilibrium and entropy-production structure through relative entropy of the forward and backward evolution. See Fagnola and Rebolledo, arXiv:1212.1366.

This supports the project's static-field convention: the compatible field state may be static, while \(\tau\) is a bookkeeping parameter for a chosen generator. Physical time is a further realization of \(\tau\), requiring an operational clock and a continuum limit. The mathematical entropy ledger can be established before that physical interpretation.

## 45. Quantum interaction as noncommutative field closure

A finite quantum realization uses a density operator

\[
\rho\in\mathsf D(\mathcal H),
\]

with generator

\[
\dot\rho
=
-i[H,\rho]
+
\mathcal D(\rho).
\tag{45.1}
\]

The commutator is the reversible interaction sector. The completely positive dissipator \(\mathcal D\) is the irreversible or environment-coupled sector. In the Heisenberg picture,

\[
\dot A
=
i[H,A]
+
\mathcal D^\dagger(A).
\tag{45.2}
\]

Let \(\mathcal A_{\mathsf O}\) be the algebra generated by the selected observables. Exact quantum closure means

\[
i[H,\mathcal A_{\mathsf O}]
+
\mathcal D^\dagger(\mathcal A_{\mathsf O})
\subseteq
\mathcal A_{\mathsf O}.
\tag{45.3}
\]

The residual of (45.3) is the noncommutative form of hidden interaction. If \(V\) is the interaction part in

\[
H=H_A\otimes I+I\otimes H_B+V,
\]

then \(V\) changes the future of the selected algebra precisely when its commutator leaves that algebra. This is the quantum version of a memory kernel or a nonzero FIB \(\kappa\)-dependence.

The existing finite quantum interfaces in the theory volume already provide density operators, CPTP maps, quantum triangle sources, trace-norm contraction, quantum relative entropy, and finite Hamiltonian closure tests. The present unified-field statement is therefore:

\[
\text{quantum interaction}
=
\text{noncommutative generator action}
+
\text{possible failure of observable closure}.
\]

A full quantum field theory adds operator-valued fields and locality axioms. Those are a later realization layer. The finite matrix architecture gives a type-correct starting point and does not claim to be a completed QFT.

## 46. Light and sound as normal-mode branches

Let \(\Phi_*\) be a stationary field state:

\[
\mathsf G(\Phi_*)=0.
\]

A fixed point is a state, not a wave. Linearize with

\[
\Phi=\Phi_*+\varepsilon v,
\qquad
\dot v=A_*v+O(\varepsilon),
\qquad
A_*=D\mathsf G_{\Phi_*}.
\tag{46.1}
\]

The spectral branches of \(A_*\) classify the local processes:

\[
\lambda=i\omega
\]

gives a nondissipative oscillatory mode,

\[
\operatorname{Re}\lambda<0
\]

gives a decaying mode, and

\[
\lambda=0
\]

gives a conserved, neutral, or critical direction subject to the nonlinear stability conditions.

Light and sound are candidate normal-mode families of the same field architecture, with different observable ports and constitutive blocks:

- an electromagnetic port uses a gauge connection, field curvature, and Maxwell constitutive map;
- an acoustic port uses density, momentum, pressure, and a medium constitutive map.

A coupled finite linearization can be written

\[
A_*=
\begin{pmatrix}
A_{\mathrm{EM}} & C\\
C^* & A_{\mathrm{mat}}
\end{pmatrix}.
\tag{46.2}
\]

The eigenvectors of this block operator are the actual modes. In a decoupled limit they separate into electromagnetic and acoustic branches. With coupling, hybrid modes can occur. The propagation laws, such as \(\omega\approx c|k|\) or \(\omega\approx c_s|k|\), come from the respective spatial operators and constitutive assumptions. They do not follow from the abstract unified architecture alone.

Thus:

\[
\text{static field}
\longrightarrow
\text{stationary point}
\longrightarrow
\text{linearized generator}
\longrightarrow
\text{normal modes}.
\]

“Light” and “sound” are therefore field excitations or readout branches. They are not generally fixed points themselves. A fixed point is the background around which the modes are defined.

The project's gravitational candidate belongs one level higher. A graph Dirichlet form, Fisher Hessian, effective resistance, or holonomy defect can produce a metric-like structure. To identify it with physical gravity, one still needs a continuum limit, a diffeomorphism-covariant field equation, a stress-energy coupling, and observable predictions. The present finite results define a geometry interface and a closure residual. They do not yet prove an Einstein or Ricci realization.

## 47. Mathematical dependencies and conditional theorem chain

The finite mathematical relationships and their additional assumptions are:

1. a finite StructurePreservingGenerator consists of the state carrier, energy, entropy, skew operator, positive operator, reference state, observation map, and closure residual;
2. (41.2) and (41.4) depend only on skew-symmetry, positivity, and degeneracy;
3. a finite graph current satisfies $\dot q=-Bj$; its charge conservation and relation to the graph Dirichlet energy require the corresponding incidence and constitutive conditions;
4. for $\mathsf O_{\mathrm{FIB}}$, the equality $\mathcal R_{\mathsf O}=0$ is equivalent to generator invariance of the $\kappa$-fibers;
5. the quantum closure residual is related to the commutator-orbit and Hamiltonian-effect theorems under their respective hypotheses;
6. for the electromagnetic cochain $A\mapsto F=dA$, the homogeneous constraint follows from $d^2=0$;
7. light and sound denote labeled spectral subspaces of $D\mathsf G_{\Phi_*}$, with the label carried by the observation port and constitutive block;
8. continuum limits, physical units, and gravitational interpretation require additional assumptions beyond these finite relationships.

The resulting theorem hierarchy is:

\[
\begin{aligned}
&\text{state-flow-conservation}\\
&\Downarrow\\
&\text{observation quotient and closure residual}\\
&\Downarrow\\
&\text{reversible/dissipative split}\\
&\Downarrow\\
&\text{current, entropy defect, quantum commutator, gauge curvature}\\
&\Downarrow\\
&\text{normal modes and geometry interfaces}.
\end{aligned}
\]

This hierarchy specifies the finite mathematical scope of the unified-field relationships. The commonality lies in the typed state, conservation law, generator, observation map, and defect functional. Maxwell theory, stochastic thermodynamics, finite quantum dynamics, FIB geometry, and triangle-source networks are distinct realizations connected by explicit maps. A physical identification requires proving those maps and their limiting laws.

### External anchors for this extension

- Jelić, Hütter, and Öttinger, *Dissipative electromagnetism from a nonequilibrium thermodynamics perspective*, arXiv:1001.0899.
- De Zela, *The way back: from charge conservation to Maxwell equations*, arXiv:physics/0506054.
- Ge and Qian, *The Physical Origins of Entropy Production, Free Energy Dissipation and their Mathematical Representations*, arXiv:0911.3984.
- Fagnola and Rebolledo, *Entropy Production for Quantum Markov Semigroups*, arXiv:1212.1366.
- Onsager, *Reciprocal Relations in Irreversible Processes II*, Physical Review 38 (1931).


## 48. Predictive quotient and dynamic seam observability

The finite FIB quotient is a current observation quotient. For dynamics, the correct quotient is determined by the complete future observation record.

### Definition 48.1 (Future-behavior equivalence)

Let \(X\) be a state set, \(\mathcal A\) a finite action alphabet, \(F_a:X\to X\) an update for each \(a\in\mathcal A\), and \(O:X\to Y\) an observation. For a word \(w=a_1\cdots a_m\), set

\[
F_w=F_{a_m}\circ\cdots\circ F_{a_1},
\qquad
F_\varepsilon=\operatorname{id}_X.
\]

Define the complete future behavior

\[
\mathcal B_O(x)(w)=O(F_wx),
\qquad
w\in\mathcal A^\ast,
\]

and define

\[
x\sim_O y
\quad\Longleftrightarrow\quad
\mathcal B_O(x)=\mathcal B_O(y).
\]

For a relation \(R\subseteq X\times X\), define

\[
\Phi_O(R)
=
\left\{
(x,y):
O(x)=O(y),\
(F_ax,F_ay)\in R\ \forall a\in\mathcal A
\right\}.
\]

### Theorem 48.2 (Minimal exact predictive quotient)

The relation \(\sim_O\) is the greatest fixed point of \(\Phi_O\). The quotient

\[
Q_O=X/{\sim_O}
\]

has uniquely defined updates and observation

\[
\overline F_a([x])=[F_ax],
\qquad
\overline O([x])=O(x),
\]

and the quotient map \(\pi:X\to Q_O\) is an exact predictive representation. If \(r:X\to S\) is any exact representation with updates \(G_a\) and observation \(\overline O_S\),

\[
rF_a=G_ar,
\qquad
O=\overline O_Sr,
\]

then there is a unique surjection \(q:r(X)\to Q_O\) such that

\[
\pi=qr,
\qquad
qG_a=\overline F_aq,
\qquad
\overline O_O\circ q=\overline O_S.
\]

Thus \(Q_O\) is the coarsest state representation that preserves every future observation.

#### Proof

If \(x\sim_O y\), then the empty word gives \(O(x)=O(y)\). For every \(a\in\mathcal A\) and every word \(w\),

\[
O(F_wF_ax)=O(F_wF_ay),
\]

so \(F_ax\sim_OF_ay\). Hence

\[
\sim_O\subseteq\Phi_O(\sim_O).
\]

Conversely, suppose \((x,y)\in\Phi_O(\sim_O)\). The empty word has equal observations. For a nonempty word \(aw\),

\[
O(F_{aw}x)=O(F_wF_ax)=O(F_wF_ay)=O(F_{aw}y),
\]

where the middle equality uses \(F_ax\sim_OF_ay\). Induction on word length gives \(x\sim_Oy\). Therefore

\[
\sim_O=\Phi_O(\sim_O).
\]

If \(R\subseteq\Phi_O(R)\), induction on word length gives \(R\subseteq\sim_O\). Hence \(\sim_O\) is the greatest fixed point.

The definitions of \(\overline F_a\) and \(\overline O\) are well-defined by the fixed-point property. If \(r(x)=r(y)\), exactness gives equal observations after every word, so \(x\sim_Oy\). Therefore \(q(r(x))=[x]\) is well-defined and surjective. The three intertwining identities follow directly from exactness. Uniqueness follows because \(r(X)\) is generated by points \(r(x)\). ∎

### Definition 48.3 (Finite predictive observability of the seam)

Let \(X=\mathbb R^n\), let \(O:X\to\mathbb R^m\) be linear, and let each action have linear difference map \(A_a\). For a word \(w\), write \(A_w=A_{a_m}\cdots A_{a_1}\). The seam direction \(d\) is predictively observable if

\[
O A_wd\ne0
\]

for at least one word \(w\). It is predictively invisible if

\[
O A_wd=0
\qquad
\forall w\in\mathcal A^\ast.
\]

### Theorem 48.4 (Seam observability criterion)

For two states in the same FIB visible fiber,

\[
p_\kappa-p_{\kappa'}=(\kappa-\kappa')d,
\]

the future observations satisfy

\[
O(F_wp_\kappa)-O(F_wp_{\kappa'})
=
(\kappa-\kappa')OA_wd.
\]

Consequently, if the fiber is nondegenerate, \(\kappa\) is distinguished by some finite future experiment if and only if there exists \(w\) with

\[
OA_wd\ne0.
\]

If \(OA_wd=0\) for every word, then the entire \(\kappa\)-fiber collapses in the predictive quotient \(Q_O\).

#### Proof

Affine offsets cancel in the difference of two trajectories. The remaining difference is

\[
A_w(p_\kappa-p_{\kappa'})
=
(\kappa-\kappa')A_wd.
\]

Applying \(O\) gives the displayed formula. If one coefficient is nonzero, the corresponding future observation separates every pair with \(\kappa\ne\kappa'\). If all coefficients vanish, all future observations coincide, so the states are equivalent under Definition 48.1. ∎

### Corollary 48.5 (Finite-dimensional continuous-time test)

For a single linear generator \(A\) and observation \(O\),

\[
Oe^{tA}d\equiv0
\quad\forall t\ge0
\]

if and only if

\[
OA^kd=0,
\qquad
k=0,\ldots,n-1.
\]

#### Proof

The forward implication follows by differentiating at \(t=0\). For the reverse implication, the Cayley–Hamilton theorem expresses every \(A^k\) with \(k\ge n\) as a linear combination of the first \(n\) powers. Therefore every coefficient in

\[
Oe^{tA}d
=
\sum_{k\ge0}\frac{t^k}{k!}OA^kd
\]

vanishes. ∎

### Corollary 48.6 (Current closure versus future closure)

Let \(G(p)=Ap+c\) be an affine generator and let \(O_{\mathrm{FIB}}(p)=(X,Y,Z)\). Exact current closure on every visible FIB fiber is equivalent to

\[
O_{\mathrm{FIB}}Ad=0.
\]

Future closure is stronger. It requires

\[
O_{\mathrm{FIB}}A^kd=0
\qquad
\forall k\ge0,
\]

or, in a finite-dimensional realization, only \(k=0,\ldots,n-1\).

Therefore a seam can be invisible to the instantaneous visible derivative while remaining visible at a later time. This is the precise finite statement of dynamic information escape:

\[
\text{current quotient}
\neq
\text{minimal predictive quotient}.
\]

The result relates the FIB hidden coordinate to predictive sufficiency through the observability family

\[
\{OA_wd:w\in\mathcal A^\ast\},
\]

together with its finite-dimensional Cayley–Hamilton reduction.


---

## 追加锚（本行以下为增补区）
