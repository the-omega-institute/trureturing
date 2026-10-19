# AURIC 集体振子、返回容量与内生记录

## 1. 编码、算符域与时间合同

**定义 1.1（分隔五态单元与二态子码）。** 令

$$
\mathcal H_F=\operatorname{span}\{e_0,e_1,e_2,e_3,e_4\},
\qquad(e_0,e_1,e_2,e_3,e_4)=(000,100,010,001,101).
$$

在每个单元中选 $g=e_0$、$e=e_4$，记 $\mathcal C_1=\operatorname{span}\{g,e\}$。取 $d\geq1$ 个节点，每节点 $N\geq1$ 个单元；二态码空间是 $\mathcal C=(\mathcal C_1)^{\otimes dN}$，它是整个 $\mathcal H_F^{\otimes dN}$ 的真子空间。采用 [静态相容纤维理论，定义 30.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#30-零分隔编码与原生分隔位的回零门) 的分隔零编码，把这些单元等距嵌入长度 $4dN-1$ 的同一合法链：

$$
\iota|x_1\rangle\cdots|x_{dN}\rangle
=|x_1\,0\,x_2\,0\cdots0\,x_{dN}\rangle.
\tag{O.1}
$$

开放合法链 $\mathcal K_n$ 由无相邻 $11$ 的位串张成，故 $\dim\mathcal K_n=F_{n+2}$，其中 $F_1=F_2=1$。此处 $5^{dN}$ 维分隔编码域嵌入 $F_{4dN+1}$ 维合法载体。编码映射的存在不供应输入来源或额外环境。

在二态子码上定义

$$
\sigma^-_{u,j}=|g\rangle_{u,j}\langle e|,
\qquad n_{u,j}=|e\rangle_{u,j}\langle e|,
\qquad a_{u,N}=N^{-1/2}\sum_{j=1}^N\sigma^-_{u,j},
\qquad n_u=\sum_{j=1}^N n_{u,j}.
\tag{O.2}
$$

所有写作 $I-2n_u/N$ 的单位算符均指该二态码上的单位算符。在完整五态空间上，单元对易子实际为 $|g\rangle\langle g|-|e\rangle\langle e|$，不能换成 $I_5-2|e\rangle\langle e|$。

**定义 1.2（对称激发与共同比较空间）。** 节点 $u$ 的归一化 Dicke 向量是

$$
|D_m^{(N)}\rangle=\binom Nm^{-1/2}\sum_{|S|=m}|S\rangle,
\qquad 0\leq m\leq N,
\tag{O.3}
$$

其中 $S$ 标记处于 $e$ 的单元。记 $\mathcal D_N$ 为这些向量的张成空间。对整数 $0\leq M\leq N$，定义有限维空间

$$
\mathcal F_{\leq M}^{(d)}
=\operatorname{span}\{|m_1,\ldots,m_d\rangle:\sum_u m_u\leq M\},
$$

以及等距识别

$$
J_N|m_1,\ldots,m_d\rangle
=\bigotimes_{u=1}^d|D_{m_u}^{(N)}\rangle.
\tag{O.4}
$$

$b_u$ 是玻色 Fock 空间上的标准湮灭算符。下文比较 Hamiltonian 和演化时，先以 $J_N$ 拉回有限模型，再在同一个 $\mathcal F_{\leq M}^{(d)}$ 上作差；不是直接相减两个不同 Hilbert 空间上的算符。

**假设 1.3（目标动力学与可用控制）。** 给定 $B=B^\dagger\in M_d(\mathbb C)$ 和 $\hbar>0$，设

$$
H_N(B)=\hbar\sum_{u,v}B_{uv}a_{u,N}^\dagger a_{v,N},
\qquad H(B)=\hbar\sum_{u,v}B_{uv}b_u^\dagger b_v,
\qquad C_B=\sum_{u,v}|B_{uv}|.
\tag{O.5}
$$

它们是指定的数守恒目标动力学。需要其原生近似时，另外采用静态相容纤维理论的假设 30.2：逐位置独立可寻址受阻驱动、未选项与漂移为零、可重复的固定非实联合相位、初始化为零的分隔位。只引用该卷定理 31.1 的有限字射影近似，不假设任意角相位或每个目标的精确有限综合。参数 $t$ 是目标演化时间；将其换算成实际脉冲持续时间是额外标定。

## 2. 合法链编码中的有限振子网络误差

**定理 2.1（共同低激发空间上的网络逼近）。** 对定义 1.1—1.2 及假设 1.3，$J_N\mathcal F_{\leq M}^{(d)}$ 是 $H_N(B)$ 的不变空间。记

$$
\widetilde H_N(B)=J_N^\dagger H_N(B)J_N\big|_{\mathcal F_{\leq M}^{(d)}}.
$$

对任意实数 $t$，有

$$
\begin{aligned}
\|\widetilde H_N(B)-H(B)|_{\mathcal F_{\leq M}^{(d)}}\|
&\leq\frac{\hbar C_B M(M-1)}{N},\\
\|e^{-it\widetilde H_N(B)/\hbar}
-e^{-itH(B)|_{\mathcal F_{\leq M}^{(d)}}/\hbar}\|
&\leq\frac{|t|C_BM(M-1)}{N}.
\end{aligned}
\tag{O.6}
$$

在假设 1.3 的原生控制下，对任意 $\varepsilon>0$，还存在同一个有限合法字，其编码域逻辑酉记为 $W$，以及 $|z|=1$，满足

$$
\|z^{-1}WJ_N-J_Ne^{-itH(B)|_{\mathcal F_{\leq M}^{(d)}}/\hbar}\|
<\varepsilon+\frac{|t|C_BM(M-1)}{N}.
\tag{O.7}
$$

该字在所有未知输入和有限参考上共同适用；输出态的迹范数误差至多为 (O.7) 右侧的两倍。$N\to\infty$ 的结论固定 $d,M,B,t$，不覆盖任意随 $N$ 增长的激发窗口。

证明。先使用集体自旋的标准计数结构作为中间步骤。不同单元算符交换，而在二态子码上 $[\sigma^-,\sigma^+]=I-2n$，故

$$
[a_{u,N},a_{u,N}^\dagger]=I-\frac{2n_u}{N}.
\tag{O.8}
$$

固定一个含 $m-1$ 个激发的输出集合，它有 $N-m+1$ 个含 $m$ 个激发的父集合。将其数目与 (O.3) 的归一化相乘，得到

$$
\begin{aligned}
a_{u,N}|D_m^{(N)}\rangle
&=\sqrt{m\left(1-\frac{m-1}{N}\right)}|D_{m-1}^{(N)}\rangle,\\
a_{u,N}^\dagger|D_m^{(N)}\rangle
&=\sqrt{(m+1)\left(1-\frac mN\right)}|D_{m+1}^{(N)}\rangle.
\end{aligned}
\tag{O.9}
$$

端点的越界系数为零。这是 Holstein–Primakoff 集体自旋表示的有限占据形式；其一般先例为 T. Holstein 与 H. Primakoff，*Field Dependence of the Intrinsic Domain Magnetization of a Ferromagnet*，Physical Review **58**, 1098，doi:[10.1103/PhysRev.58.1098](https://doi.org/10.1103/PhysRev.58.1098)。这里将它用作 (O.1) 的指定子码与图 Hamiltonian 误差的中间输入，不单独主张新的集体自旋代数。

式 (O.9) 证明节点对称空间及总激发数保持。对角项的拉回系数是 $m_u(1-(m_u-1)/N)$；与 $m_u$ 相差至多 $M(M-1)/N$。非对角项 $u\ne v$ 在 $m_v\geq1$ 时的目标系数是 $\sqrt{(m_u+1)m_v}$，有限系数另乘

$$
\sqrt{(1-m_u/N)(1-(m_v-1)/N)}.
$$

由 $0\leq x,y\leq1$ 时 $1-\sqrt{(1-x)(1-y)}\leq x+y$，系数差至多

$$
\frac{\sqrt{(m_u+1)m_v}(m_u+m_v-1)}N
\leq\frac{M(M-1)}N.
\tag{O.10}
$$

当总激发为零时没有该转移。每个固定有向边把不同占据基向量映到不同输出基向量，故其加权移位的算符范数就是最大系数。对 $B_{uv}$ 加权求和给 (O.6) 第一式。两个有限维自伴生成元的 Duhamel 公式再给第二式。

将 $H_N(B)$ 用 (O.2) 延拓到整个有限五态张量编码域，它仍为自伴且保持选定子码。用静态相容纤维理论的定理 31.1 选一个 $W$ 射影逼近其目标酉，误差小于 $\varepsilon$。将这一界限制到 $J_N\mathcal F_{\leq M}^{(d)}$，再与 (O.6) 作三角估计，得到 (O.7)。通过 $\iota$ 运输即为同一合法物理链上的结论。对共轭通道之差作两项展开，等距嵌入与酉的算符范数均为一，得到任意参考上的两倍迹范数界。

新增对应是分隔合法链、集体对称子码、同一图网络误差与合法字近似的组合。它不重认领一般 Holstein–Primakoff 极限，也不把 [统计定律卷 §199](FIB_ATOM_STATISTICAL_LAWS.md#199-fib-路径上的外加-dicke-超辐射集体自发辐射与光子统计) 已讨论的外加集体辐射当作这里的新增结果。$\square$

**定义 2.2（对易子边界与正频正规模）。** 在单节点 $m\leq M\leq N$ 上，(O.8) 给

$$
\|P_M([a_N,a_N^\dagger]-I)P_M\|=2M/N.
\tag{O.11}
$$

这里先在完整 $\mathcal D_N$ 计算对易子。如果先截断 $A_M=P_Ma_NP_M$，则由 (O.9) 的顶层系数得到

$$
[A_M,A_M^\dagger]
=P_M(I-2n/N)P_M
-(M+1)(1-M/N)|D_M^{(N)}\rangle\langle D_M^{(N)}|.
\tag{O.12}
$$

两式讨论的是不同的算符。有限维对易子的迹为零，因此任何单个有限单元或有限截断都不能精确满足完整 CCR。

如进一步要求稳定的正频弹簧，假设 $B>0$。对 $B=U\operatorname{diag}(\omega_j)U^\dagger$ 定义 $c=U^\dagger b$，则 $\omega_j>0$，且标准玻色正规模公式为

$$
c_j(t)=e^{-i\omega_jt}c_j,\qquad
Q_j=\sqrt{\frac{\hbar}{2\omega_j}}(c_j+c_j^\dagger),\qquad
P_j=-i\sqrt{\frac{\hbar\omega_j}{2}}(c_j-c_j^\dagger),
$$

$$
\hbar\omega_j(c_j^\dagger c_j+1/2)
=\tfrac12(P_j^2+\omega_j^2Q_j^2).
\tag{O.13}
$$

这些是 (O.6) 的目标振子表示；单有 $B=B^\dagger$ 不保证全部频率为正。相空间坐标 $(Q_j,P_j)$ 也不确定物理空间维数。(O.4) 的单节点对称空间只有 $N+1$ 维，二态张量域有 $2^N$ 维；例如 $(|ge\rangle-|eg\rangle)/\sqrt2$ 不在 Dicke 码内。因而此识别没有将任意非对称输入无损压入一个振子。有限图极限还没有规定空间连续极限、局域性或相互作用场。

**定理 2.3（有限单元、交替目标门与采样的共同误差）。** 将 $B=\sum_{\ell=1}^L B_\ell$ 分为自伴矩阵，令 $C_\ell=\sum_{u,v}|(B_\ell)_{uv}|$。在共同低激发空间上定义

$$
V_{N,\tau}=\prod_{\ell=1}^L e^{-i\tau\widetilde H_N(B_\ell)/\hbar},
\qquad k=\lfloor t/\tau\rfloor,
\qquad t\geq0,\quad\tau>0.
$$

则

$$
\begin{aligned}
\|V_{N,\tau}^{\,k}-e^{-itH(B)/\hbar}\|
\leq{}&\frac{tC_BM(M-1)}N\\
&+t\tau M^2\sum_{\ell<j}C_\ell C_j
+\tau M\sum_\ell C_\ell.
\end{aligned}
\tag{O.14}
$$

若将其中有限个目标因子再以合法字作射影近似，其额外误差至多为各因子的算符误差之和。

证明。每个 $a_{u,N}^\dagger a_{v,N}$ 在该不变空间上范数不超过 $M$：对角项不超过 $m_u\leq M$，非对角系数不超过 $\sqrt{(m_u+1)m_v}\leq M$。故 $\|\widetilde H_N(B_\ell)/\hbar\|\leq MC_\ell$。标准一阶酉乘积积分估计给单步误差

$$
\frac{\tau^2}{2}\sum_{\ell<j}
\|[\widetilde H_N(B_\ell)/\hbar,\widetilde H_N(B_j)/\hbar]\|
\leq\tau^2M^2\sum_{\ell<j}C_\ell C_j.
$$

对 $k$ 步望远镜求和，利用 $k\tau\leq t$，得到 (O.14) 第二项。$0\leq t-k\tau<\tau$ 与 $\|\widetilde H_N(B)/\hbar\|\leq M\sum C_\ell$ 给第三项；(O.6) 在时间 $t$ 给第一项。有限个酉因子的误差用同一望远镜展开累加。这里用到的乘积公式为标准中间估计；(O.14) 将它与此合法编码的有限占据误差组合，未把 $\tau$ 认作一次原生调用的实际耗时。$\square$

## 3. Fibonacci 载体中的返回记忆容量

**定义 3.1（固定封闭演化的振幅压缩）。** 在有限维 $\mathcal H$ 中取保留空间 $\mathcal S$，等距嵌入 $J:\mathcal S\to\mathcal H$，$\Pi=JJ^\dagger$，$\mathcal E=(I-\Pi)\mathcal H$。对一个固定幺正 $U$ 定义

$$
K=J^\dagger UJ,\qquad L=(I-\Pi)UJ,\qquad
R_n=J^\dagger U^nJ,\qquad
B_\partial=J^\dagger U|_{\mathcal E},\qquad C=(I-\Pi)U|_{\mathcal E}.
\tag{O.15}
$$

$B_\partial$ 是返回块，和网络矩阵 $B$ 无关。这里每次只在末端压缩；逐步投影、环境重置或按时间另选 $U$ 都是不同合同。块递推给

$$
R_{n+1}=KR_n+\sum_{j=0}^{n-1}B_\partial C^{n-1-j}LR_j,
\qquad R_0=I.
\tag{O.16}
$$

确实，隐藏振幅 $F_n=(I-\Pi)U^nJ$ 满足 $F_{n+1}=LR_n+CF_n$、$F_0=0$；代回保留块递推即得 (O.16)。特别地 $R_2=K^2+B_\partial L$。幺正性还给 $I-K^\dagger K=L^\dagger L$。

**定理 3.2（同一合法链的首次压缩偏离界）。** 设整个封闭载体恰为长度 $n$ 的 $\mathcal K_n$，没有额外辅助空间。令 $p=\dim\mathcal S$、$d_K=\operatorname{rank}(I-K^\dagger K)>0$。则存在首次整数 $m_*\geq2$ 满足 $R_{m_*}\ne K^{m_*}$，而且

$$
m_*\leq\left\lfloor\frac{F_{n+2}-p}{d_K}\right\rfloor+1.
\tag{O.17}
$$

如果对 $0\leq j\leq m$ 均没有偏离，则

$$
\dim\operatorname{span}\{U^jJ\mathcal S:0\leq j\leq m\}
=p+md_K.
\tag{O.18}
$$

证明。使用有限步幺正扩张的缺陷维数原理作为中间步骤；其经典出处为 E. Levy 与 O. M. Shalit，[*Dilation theory in finite dimensions: the possible, the impossible and the unknown*，arXiv:1012.4514v2，Theorem 1.3](https://arxiv.org/html/1012.4514)。该文以 $T$ 表示压缩，以 $N$ 表示要求保持的幂次数，最小维数为 $\dim\mathcal S+N\operatorname{rank}(I-T^\dagger T)$；这里分别代入 $K,m$。对当前同一个 $U$，也可直接看见所占方向：置

$$
E_j=U^jJ-U^{j-1}JK=U^{j-1}L,\qquad1\leq j\leq m.
$$

由幺正性 $\operatorname{rank}E_j=d_K$。对 $0\leq i<j\leq m$，

$$
(U^iJ)^\dagger E_j=R_{j-i}-R_{j-i-1}K=0.
$$

故每个 $\operatorname{ran}E_j$ 都与先前的 $U^iJ\mathcal S$ 正交，且

$$
\operatorname{span}_{j=0}^m U^jJ\mathcal S
=J\mathcal S\oplus\bigoplus_{j=1}^m\operatorname{ran}E_j.
$$

取维数得到 (O.18)。总维数为 $F_{n+2}$，因此 $md_K\leq F_{n+2}-p$。取超过右侧容量的最小整数，便得 (O.17) 与首次偏离的存在。$d_K\leq F_{n+2}-p$ 又由 $L$ 的值域给出，故不与 $R_1=K$ 矛盾。

一般扩张维数不是本卷的新定理；新增应用是同一 FIB 载体、固定幺正和缺陷秩的返回记忆上限。$R_{m_*}\ne K^{m_*}$ 是算符不等，不保证任意指定初态的占据概率在第 $m_*$ 步出现可见复兴峰。$\operatorname{ran}E_j$ 是正交的创新方向，也不是已经被观察者读取的经典档案。$\square$

**定义 3.3（连续自主压缩与非耦合条件）。** 对有限维自伴 $H$，若 $T(t)=J^\dagger e^{-itH/\hbar}J$ 在所有 $t,s\geq0$ 满足 $T(t+s)=T(t)T(s)$，则有限维可微半群的一阶导数规定生成元为 $-iJ^\dagger HJ/\hbar$。二阶导数因而要求

$$
0=J^\dagger H^2J-(J^\dagger HJ)^2
=((I-\Pi)HJ)^\dagger((I-\Pi)HJ).
\tag{O.19}
$$

所以 $(I-\Pi)HJ=0$，保留空间没有外逸。此标准压缩障碍限定 (O.17) 的连续时间读法：有限、固定、自主的封闭振幅演化不能同时具有持续非零外逸和精确压缩半群。它不排除对每个终点时间分别选择不同的有限维扩张。

## 4. 联合占据转移与记录时间的资源差异

**定义 4.1（带新鲜环境的联合扇区仪器）。** 在 $\mathcal H_F$ 上令

$$
A=|e_0\rangle\langle e_4|,\qquad
\Pi_4=|e_4\rangle\langle e_4|,\qquad Q_4=I_5-\Pi_4.
$$

对 $\gamma\geq0$、$\tau\geq0$ 取 $c_\tau=e^{-\gamma\tau/2}$、$s_\tau=\sqrt{1-e^{-\gamma\tau}}$。每一步供应处于 $|0\rangle$ 的新环境二态单元，联合酉在 $\operatorname{span}\{|e_4,0\rangle,|e_0,1\rangle\}$ 上为

$$
|e_4,0\rangle\mapsto c_\tau|e_4,0\rangle+s_\tau|e_0,1\rangle,
\qquad
|e_0,1\rangle\mapsto c_\tau|e_0,1\rangle-s_\tau|e_4,0\rangle,
$$

在正交补上为恒等。读环境得到仪器 $K_0=Q_4+c_\tau\Pi_4$、$K_1=s_\tau A$。离开后的环境不再与系统耦合；此供应和不返回规则是实际假设。该二维环境也可用一个额外五态单元的二态子码承载；若需要原生近似，仍采用假设 1.3，并计入近似误差。

**定理 4.2（隐藏联合占据的转移事件与终点资源）。** 对相同单点占据均值 $X=\langle n_1\rangle$、$Y=\langle n_3\rangle$、$Z=\langle n_2\rangle$，取五态对角输入

$$
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\quad
\max\{0,X+Y+Z-1\}\leq\kappa\leq\min\{X,Y\}.
\tag{O.20}
$$

其中 $X,Y,Z\geq0$，且该区间非空。定义 4.1 的 $m$ 步仪器在 $t=m\tau$ 给

$$
\begin{aligned}
\Pr_\kappa(\text{已转移})&=\kappa(1-e^{-\gamma t}),\\
\Pr_\kappa(\text{无转移})&=1-\kappa+\kappa e^{-\gamma t},\\
X_t&=X-(1-e^{-\gamma t})\kappa,\\
Y_t&=Y-(1-e^{-\gamma t})\kappa,\qquad Z_t=Z.
\end{aligned}
\tag{O.21}
$$

所以两个初始单点均值完全相同的输入 $\kappa,\kappa'$，其已转移事件概率差为 $(1-e^{-\gamma t})(\kappa-\kappa')$。

当 $\gamma\tau>0$、$m\geq1$ 且完整保留“无转移”及每一个首次转移步数时，独立记录寄存器需要至少 $m+1$ 个可完全区分的方向。与此相对，在同一个给定终点 $t>0$，丢弃这些时间标签的系统通道只有 Choi 秩二，最小纯环境维数为二。

证明。先把标准振幅阻尼通道作为计算 (O.21) 的中间步骤。由 $K_0^\dagger K_0+K_1^\dagger K_1=I$，一步通道完全正保迹，且直接展开为

$$
\begin{aligned}
\Phi_t(\rho)={}&Q_4\rho Q_4
+e^{-\gamma t/2}(Q_4\rho\Pi_4+\Pi_4\rho Q_4)\\
&+e^{-\gamma t}\Pi_4\rho\Pi_4
+(1-e^{-\gamma t})A\rho A^\dagger.
\end{aligned}
\tag{O.22}
$$

这些块系数相乘给 $\Phi_{t+s}=\Phi_t\Phi_s$，生成元是 $\gamma(A\rho A^\dagger-\{\Pi_4,\rho\}/2)$。若加入指定的 $H_\omega=\hbar\omega\Pi_4$，其跨块矩阵元 $\rho_{4j}$ 另乘 $e^{-i\omega t}$。一般阻尼和重复相互作用不是新结论；重复新鲜环境及连续缩放的文献接口为 S. Attal 与 Y. Pautrat，[*From repeated to continuous quantum interactions*，arXiv:math-ph/0311002](https://arxiv.org/abs/math-ph/0311002)。这里新增的是五态联合人口与可读事件、完整标签和终点秩的共同对应。

因为 $A^2=0$，从环境全零初态出发至多发生一次转移。无转移历史的系统算符为 $D_t=Q_4+c_\tau^m\Pi_4$，第 $j$ 步首次转移的系统算符为

$$
A_j=s_\tau c_\tau^{j-1}A,\qquad1\leq j\leq m.
\tag{O.23}
$$

故一个保留时间记录的等距嵌入是

$$
V_m\psi=D_t\psi\otimes|\mathrm{vac}\rangle
+\sum_{j=1}^m A_j\psi\otimes|1_j\rangle.
\tag{O.24}
$$

几何级数给 $D_t^\dagger D_t+\sum_jA_j^\dagger A_j=I$。对任意输入 $\rho$，第 $j$ 分支的概率为 $s_\tau^2c_\tau^{2(j-1)}\rho_{44}$，求和得 (O.21) 的两事件概率。$e_4=101$ 每次向 $e_0=000$ 转移同时减少第一和第三位占据，不改变第二位，因此也给该式的三个单点均值。

当 $\gamma\tau>0$ 时，每一个 (O.23) 都非零，无转移分支也非零。若只读独立记录寄存器就要无误识别全部 $m+1$ 个标签，其承载状态必须两两正交，故至少需要 $m+1$ 维。(O.24) 达到这一标签维数；它没有断言新鲜环境乘积空间 $2^m$ 维是最小需求。

然而所有 $A_j$ 都是同一 $A$ 的倍数。丢弃时间标签后可合并为两个 Kraus 算符

$$
D_t=Q_4+e^{-\gamma t/2}\Pi_4,
\qquad F_t=\sqrt{1-e^{-\gamma t}}A.
\tag{O.25}
$$

当 $\gamma t>0$ 时它们非零且线性独立，因而 Choi 矩阵 $|D_t\rangle\!\rangle\langle\!\langle D_t|+|F_t\rangle\!\rangle\langle\!\langle F_t|$ 的秩恰为二。每个纯环境维数 $q$ 的扩张至多提供 $q$ 个 Kraus 算符，所以 $q\geq2$，而定义 4.1 的单个终点环境达到二。$\gamma t=0$ 时通道是恒等，秩为一。

终点通道与有序记录资源不同的区分，与 [最小记录扩张卷 §§5—8](RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md#8-balanced-terminal-channels-and-homogeneous-kraus-word-rank) 的合同一致；这里的具体秩二阻尼例不改变该卷的源特定秩公式。$\square$

**定义 4.3（连续缩放与相位遗忘的区别）。** 对上述碰撞模型，转移角 $\theta_\tau=\arccos e^{-\gamma\tau/2}\sim\sqrt{\gamma\tau}$。若它由持续时间 $\tau$ 的 Hamiltonian 脉冲实现，角速度尺度是 $\theta_\tau/\tau\sim\tau^{-1/2}$。相反，固定耦合强度 $g$、每次角度 $g\tau$ 给 $\cos^{2\lfloor t/\tau\rfloor}(g\tau)\to1$，没有该有限速率阻尼。$\gamma$ 因而来自指定的更新与耦合规则。

[相位增益卷，定理 13.2 与定义 13.3](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#13-recorded-and-discarded-phase-on-the-same-orbit) 的相位遗忘改变跨块相干，不改变对角占据；(O.21) 则是人口转移。这里 $\kappa$ 是输入的联合占据，那个相位圆的 $r$ 是通道相干传递强度。联合占据相关性也不自动意味着纠缠。条件归一化后的状态不能替代 (O.21) 的完整分支权重。

## 5. 内生策略、未来节点与记录合同

**定义 5.1（按已有记录选择的完整仪器树）。** 一个有限深度策略给每个已有历史 $h$ 指定 $a=\pi(h)$，并提供有限仪器 $\{K_{a,y}\}_y$，满足 $\sum_yK_{a,y}^\dagger K_{a,y}=I$。令 $K_\varnothing=I$、$K_{hy}=K_{\pi(h),y}K_h$。标准仪器完备性逐层给 $\sum_{|h|=m}K_h^\dagger K_h=I$，所以

$$
\psi\longmapsto\sum_{|h|=m}K_h\psi\otimes|h\rangle
\tag{O.26}
$$

是等距嵌入，有限维中可补全为更大空间上的酉。它是 (O.24) 的标准仪器树推广，不作为新的 Stinespring 定理。策略程序、时钟记录和全部历史标签可以由同一个联合模型承载；这不供应未知状态依赖的外部选择。

[B0 因果八读恢复](FIB_QUADRATIC_B0_CAUSAL_EIGHT_READ_RECOVERY.md) 给出指定二次读出模型、实际前缀 $JMJMJ$ 及 $\mathsf B_0$ 条件下的记录依赖策略：六次已有 TOTAL 读数之后，第六动作选 $J$，每个可达七读 FULL 子片至多含一个真正二次世界与一个仿射世界；可根据整个子片选择末动作，总计至多八读。其经典代数读出不能直接代入 (O.26) 当作量子仪器。两者共同需要动作由已有历史确定，并用于所有仍相容候选；逐个世界各有可行动作的 $\forall x\exists a_x$ 不提供一个共同动作 $\exists a\forall x$。

**定义 5.2（未来充分节点与时间、价值的参数）。** 只比较具有正概率、可定义条件律的历史。定义 $h\sim h'$ 当且仅当它们允许相同的有限未来实验树，且每种允许策略的所有未来输出串条件概率相同。节点取 $s=[h]_\sim$。该定义沿用 [动态未来商与未来闭合记忆](AURIC_FIB_ATOM_DYNAMIC_FUTURE_QUOTIENT_AND_FUTURE_CLOSED_MEMORY.md) 的未来充分任务；若需定义按边转移的商图，另要求实验菜单与更新尊重该等价。隐藏返回、控制程序或时钟记录若影响未来，就必须保存在节点中。未解决的来源不确定性还需要相容模型集合或另行指定的模型概率律；没有这个选择，不同模型的条件概率不能当作同一个已知概率。单个局部密度矩阵只有在满足这一充分条件时才足够。

记录长度 $|h|$ 可以作指定协议的离散钟。门的拆分会改变记录长度，因此它不是无需协议的物理时间标尺。有限时域价值函数还需另外给定效用 $u$，才有

$$
V_k(s)=\sup_{a\in\mathcal A(s)}
\left[u(s,a)+\sum_y p(y\mid s,a)V_{k-1}(s_{a,y})\right].
\tag{O.27}
$$

此处 Bellman 关系是对已充分节点、合法动作和效用的标准条件递推，不推出时间等于价值。没有形成可区分记录的路径须先叠加振幅；已形成正交输出记录的互斥事件才相加概率。有限历史图可嵌入固定大空间，正交方向的占用增长与本体空间的新增不是同一命题；(O.18) 也不给知识、熵或效用的数值。控制内生化也不保证公布后的自预测具有不动点，参见静态相容纤维理论的命题 33.3；依公布预测位 $p$ 输出 $1-p$ 的合法程序不能被一个总是正确的 Boolean 预测覆盖。

**定义 5.3（模型范围与归属）。** 相位圆与其恢复几何归相位增益卷 §§11—13；(O.6)—(O.7) 的共同编码误差、(O.14) 的三项误差、(O.17) 的 Fibonacci 返回界及 (O.21)—(O.25) 的联合占据与记录资源对应，是采用所引中间结果的 `repo-derived` 综合推导。集体自旋表示、酉扩张维数、阻尼半群、仪器等距扩张和 Bellman 递推为 `literature-attested` 的中间输入，保留其既有文献地位。这里没有把相同术语或相同数值视作物理实现的证明。

从原生机制决定 $B,\gamma,D$、物理时间标度、空间局域性，以及哪些源、环境与记录实际可取得，是独立的模型条件。本文的有限模与记录定理不通过命名替代这些条件，也不把纸面推导表述为已完成 Lean/kernel 核验或经验确认。

## 追加锚（本行以下为增补区）
