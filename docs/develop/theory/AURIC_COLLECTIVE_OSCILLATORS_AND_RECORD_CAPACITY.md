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

当 $\gamma\tau>0$、$m\geq1$ 且完整保留“无转移”及每一个首次转移步数时，独立记录寄存器需要至少 $m+1$ 个可完全区分的方向。与此相对，对固定 $\gamma>0$ 和给定终点 $t>0$，丢弃这些时间标签的系统通道只有 Choi 秩二，最小纯环境维数为二。

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

故一个在标签读出前保留相干时间记录的等距嵌入是

$$
V_m\psi=D_t\psi\otimes|\mathrm{vac}\rangle
+\sum_{j=1}^m A_j\psi\otimes|1_j\rangle.
\tag{O.24}
$$

几何级数给 $D_t^\dagger D_t+\sum_jA_j^\dagger A_j=I$。实际取得经典时间标签时还要在该寄存器上执行规定的标签读出。对任意输入 $\rho$，第 $j$ 分支的概率为 $s_\tau^2c_\tau^{2(j-1)}\rho_{44}$，求和得 (O.21) 的两事件概率。$e_4=101$ 每次向 $e_0=000$ 转移同时减少第一和第三位占据，不改变第二位，因此也给该式的三个单点均值。

当 $\gamma\tau>0$ 时，每一个 (O.23) 都非零，无转移分支也非零。若只读独立记录寄存器就要无误识别全部 $m+1$ 个标签，其承载状态必须两两正交，故至少需要 $m+1$ 维。(O.24) 达到这一标签维数；它没有断言新鲜环境乘积空间 $2^m$ 维是最小需求。

然而所有 $A_j$ 都是同一 $A$ 的倍数。丢弃时间标签后可合并为两个 Kraus 算符

$$
D_t=Q_4+e^{-\gamma t/2}\Pi_4,
\qquad F_t=\sqrt{1-e^{-\gamma t}}A.
\tag{O.25}
$$

当 $\gamma t>0$ 时它们非零且线性独立，因而 Choi 矩阵 $|D_t\rangle\!\rangle\langle\!\langle D_t|+|F_t\rangle\!\rangle\langle\!\langle F_t|$ 的秩恰为二。每个纯环境维数 $q$ 的扩张至多提供 $q$ 个 Kraus 算符，所以 $q\geq2$，而定义 4.1 的单个终点环境达到二。$\gamma t=0$ 时通道是恒等，秩为一。

终点通道与有序记录资源不同的区分，与 [最小记录扩张卷 §§5—8](RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md#8-balanced-terminal-channels-and-homogeneous-kraus-word-rank) 的合同一致；这里的具体秩二阻尼例不改变该卷的源特定秩公式。$\square$

**定义 4.3（连续缩放与相位遗忘的区别）。** 对上述碰撞模型，在固定 $\gamma>0$、$\tau\downarrow0$ 时，转移角 $\theta_\tau=\arccos e^{-\gamma\tau/2}\sim\sqrt{\gamma\tau}$。若它由持续时间 $\tau$ 的 Hamiltonian 脉冲实现，角速度尺度是 $\theta_\tau/\tau\sim\sqrt\gamma\,\tau^{-1/2}$。$\gamma=0$ 时转移角恒为零。相反，固定耦合强度 $g$、每次角度 $g\tau$ 给 $\cos^{2\lfloor t/\tau\rfloor}(g\tau)\to1$，没有该有限速率阻尼。$\gamma$ 因而来自指定的更新与耦合规则。

[相位增益卷，定理 13.2 与定义 13.3](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#13-recorded-and-discarded-phase-on-the-same-orbit) 的相位遗忘改变跨块相干，不改变对角占据；(O.21) 则是人口转移。这里 $\kappa$ 是输入的联合占据，那个相位圆的 $r$ 是通道相干传递强度。联合占据相关性也不自动意味着纠缠。条件归一化后的状态不能替代 (O.21) 的完整分支权重。

## 5. 内生策略、未来节点与记录合同

**定义 5.1（按已有记录选择的完整仪器树）。** 一个有限深度策略给每个已有历史 $h$ 指定 $a=\pi(h)$，并提供有限仪器 $\{K_{a,y}\}_y$，满足 $\sum_yK_{a,y}^\dagger K_{a,y}=I$。令 $K_\varnothing=I$、$K_{hy}=K_{\pi(h),y}K_h$。标准仪器完备性逐层给 $\sum_{|h|=m}K_h^\dagger K_h=I$，所以

$$
\psi\longmapsto\sum_{|h|=m}K_h\psi\otimes|h\rangle
\tag{O.26}
$$

是等距嵌入，有限维中可补全为更大空间上的酉。它是 (O.24) 的标准仪器树推广，不作为新的 Stinespring 定理。策略程序、时钟记录和全部历史标签可以由同一个联合模型承载；这不供应未知状态依赖的外部选择。该表示规定允许实验的概率结构，不为所有互不相容实验同时预设确定结果。

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

## 6. 有限相位记录与集体振子的相干范围

**定义 6.1（相位编码、能级窗口与恢复合同）。** 对单模数算子 $\hat n|j\rangle=j|j\rangle$ 取 $U_\varphi=e^{-i\varphi\hat n}$。未知相位均匀分布于圆周；一个至多 $K\geq1$ 标签的随机编码由可测函数 $q_y(\varphi)\geq0$、$\sum_yq_y(\varphi)=1$ 给出。标签机制与未知量子输入独立，接收者只有量子输出和该经典标签，没有额外的相关相位参考。有限窗口上的通道为

$$
\mathcal E_q(\rho)=\sum_{y=1}^K|y\rangle\langle y|\otimes
\int_0^{2\pi}q_y(\varphi)U_\varphi\rho U_\varphi^\dagger
\frac{d\varphi}{2\pi}.
\tag{O.28}
$$

定义 $\mathcal H_M=\operatorname{span}\{|0\rangle,\ldots,|M\rangle\}$，diamond 范数不除以二。等弧标签记录相位所在的 $K$ 个等长圆弧之一，并按中心作逆相位校正。其剩余误差 $\theta$ 均匀分布于 $[-\alpha,\alpha]$、$\alpha=\pi/K$，通道记为

$$
\mathcal D_K(\rho)=\frac1{2\alpha}\int_{-\alpha}^{\alpha}
 e^{-i\theta\hat n}\rho e^{i\theta\hat n}\,d\theta.
\tag{O.29}
$$

一般相位分布 $\mu$ 的作用由其 Fourier 矩给出：$|j\rangle\langle k|$ 乘以 $\widehat\mu(j-k)=\int e^{-i(j-k)\varphi}\,d\mu(\varphi)$。因此第一阶矩不能决定所有相干；例如 $\tfrac12(\delta_0+\delta_\pi)$ 和均匀圆周分布的第一阶矩同为零，第二阶矩分别为一和零。这是数相位共轭的标准 Fourier 计算，用于区分相位恢复卷中单一跨块相干与这里的多阶任务。

**定理 6.2（等弧记录与有限 AURIC 振子网络的联合误差）。** 定义 6.1 的校正通道满足

$$
\mathcal D_K(|j\rangle\langle k|)
=\operatorname{sinc}\left(\frac{(j-k)\pi}{K}\right)|j\rangle\langle k|,
\qquad \operatorname{sinc}(x)=\frac{\sin x}{x},\quad\operatorname{sinc}(0)=1,
\tag{O.30}
$$

且对整数 $M\geq0$，

$$
1-\operatorname{sinc}\left(\frac{M\pi}{K}\right)
\leq\|\mathcal D_K-\mathrm{id}\|_{\diamond,\mathcal H_M}
\leq\min\left\{2,\frac{\pi^2M^2}{6K^2}\right\}.
\tag{O.31}
$$

固定 $M$ 时，该误差为 $\pi^2M^2/(6K^2)+O(K^{-4})$。对定义 1.1—1.2 的 $d$ 模共同空间 $\mathcal F_{\leq M}^{(d)}$，将 (O.29) 中的数算子改为总激发数，令

$$
V_N(t)=e^{-it\widetilde H_N(B)/\hbar},\qquad
V(t)=e^{-itH(B)|_{\mathcal F_{\leq M}^{(d)}}/\hbar}.
$$

在 $M\leq N$ 时，

$$
\left\|\mathcal D_K\circ\operatorname{Ad}_{V_N(t)}-
\operatorname{Ad}_{V(t)}\right\|_{\diamond,\leq M}
\leq\frac{2|t|C_BM(M-1)}{N}+\frac{\pi^2M^2}{6K^2}.
\tag{O.32}
$$

因此固定 $d,B,t$，$M^2/N\to0$ 与 $M/K\to0$ 是联合误差趋零的一组充分条件。反向地，对一个节点的 Dicke 窗口 $m=0,\ldots,M\leq N$，若任意至多 $K$ 标签的相位编码与联合恢复把误差降至 $0\leq\epsilon<2$，则必要条件为 $K\geq(M+1)(1-\epsilon/2)$。无能量限制的振子极限上，每个有限 $K$ 的统一恢复误差为二；先令窗口或标签数趋无限给出 (O.35) 的不同极限。这里使用集体编码识别后的同一空间；原生门逼近误差、标签获取成本与物理时间标定另计。

证明。积分 $e^{-i(j-k)\theta}$ 得 (O.30)。对 $M\geq1$，输入 $(|0\rangle+|M\rangle)/\sqrt2$ 的输出差只有一对非零特征值，其迹范数为 $1-\operatorname{sinc}(M\pi/K)$。$M=0$ 时通道恒等。

为证上界，将数算子平移为 $A=\hat n-(M/2)I$，不改变共轭通道。对任意辅助空间和迹类 $X$，$\|[A\otimes I,X]\|_1\leq2\|A\|\|X\|_1=M\|X\|_1$。所以 $\|\operatorname{ad}_{\hat n}\|_\diamond\leq M$。幺正通道保持迹范数，用带积分余项的二阶展开得

$$
\left\|\operatorname{Ad}_{e^{-i\theta\hat n}}-\mathrm{id}
+i\theta\operatorname{ad}_{\hat n}\right\|_\diamond
\leq\frac{\theta^2M^2}{2}.
\tag{O.33}
$$

对称平均消去一次项，且 $\mathbb E\theta^2=\alpha^2/3$。两通道的距离至多二，得到 (O.31)。下界的 Taylor 展开与此上界夹住同一个二次领先项。

多模总数在该窗口内的谱也包含于 $[0,M]$，以上上界不受简并度影响。两个网络演化保持这个窗口。由定理 2.1 及任意有限参考上的幺正通道比较，

$$
\|\operatorname{Ad}_{V_N(t)}-\operatorname{Ad}_{V(t)}\|_\diamond
\leq2\|V_N(t)-V(t)\|
\leq\frac{2|t|C_BM(M-1)}N.
$$

应用通道收缩性与三角不等式即得 (O.32)。

必要记录规模使用标准的有限经典侧信息恢复界作为中间步骤。[König、Renner 与 Schaffner，*The operational meaning of min- and max-entropy*，Theorem 2](https://arxiv.org/pdf/0807.1338) 将最优纠缠恢复写成 $2^{-H_{\min}(A|B)}/d_A$；[Tomamichel，*Quantum Information Processing with Finite Resources*，arXiv:1504.00233v5，Lemma 6.18](https://arxiv.org/pdf/1504.00233v5) 给经典 $K$ 值寄存器的条件最小熵损失至多 $\log_2 K$。这两条熵公式采用二进制单位。在完全退相干的 Choi 边缘上 $H_{\min}(A|B)=0$，故两者给纠缠保真度上界 $K/d_0$。下面直接验证当前模型的同一界，作为集体码容量推导的供应者，不另立一般恢复定理。在 $d_0\geq1$ 个连续能级 $0,\ldots,d_0-1$ 上，对定义 6.1 的所有至多 $K$ 标签编码以及所有 CPTP 联合恢复，

$$
\inf_{q,\mathcal R}\|\mathcal R\mathcal E_q-\mathrm{id}_{d_0}\|_\diamond
\geq2\max\left\{0,1-\frac K{d_0}\right\}.
\tag{O.34}
$$

若误差至多为 $0\leq\epsilon<2$，必要条件为 $K\geq d_0(1-\epsilon/2)$。它不是充分条件。若恢复范围是无能量限制的整个单模 Fock 空间，则每个有限 $K$ 编码和每个 CPTP 恢复的 diamond 误差恰为二。特别地，

$$
\begin{aligned}
\lim_{K\to\infty}\lim_{M\to\infty}
\|\mathcal D_K-\mathrm{id}\|_{\diamond,\mathcal H_M}&=2,\\
\lim_{M\to\infty}\lim_{K\to\infty}
\|\mathcal D_K-\mathrm{id}\|_{\diamond,\mathcal H_M}&=0.
\end{aligned}
\tag{O.35}
$$

确实，取归一化 Choi 测试 $|\Omega\rangle=d_0^{-1/2}\sum_{j=0}^{d_0-1}|j,j\rangle$。标签 $y$ 的未归一化 Choi 算子 $J_y$ 满足

$$
0\leq J_y\leq J_*=
\frac1{d_0}\sum_{j=0}^{d_0-1}|j,j\rangle\langle j,j|,
\tag{O.36}
$$

因为 $q_y\leq1$，而均匀相位平均消去不同能级间的交叉项。任意联合恢复在该经典标签上限制为 CPTP 映射 $\mathcal R_y$。完全正性保持 (O.36) 的序关系，因此该标签对恢复后纠缠保真度的贡献至多为

$$
\begin{aligned}
f_y&=\langle\Omega|(\mathrm{id}\otimes\mathcal R_y)(J_y)|\Omega\rangle\\
&\leq\frac1{d_0^2}\sum_{j=0}^{d_0-1}
\langle j|\mathcal R_y(|j\rangle\langle j|)|j\rangle
\leq\frac1{d_0}.
\end{aligned}
$$

故总保真度 $f\leq K/d_0$。以 $|\Omega\rangle\langle\Omega|$ 作二结果测量，恢复输出与理想态的迹距离至少为 $2(1-f)$，给出 (O.34)，并与非负性合并。

对单节点 Dicke 码，定义 1.2 的 $J_N$ 将 $m=0,\ldots,M$ 等距识别为这 $d_0=M+1$ 个不同电荷能级。该识别保持带有限参考的迹范数，因而 (O.34) 给出所述标签必要条件。

对无限空间的任意固定编码与恢复，将输入限制到前 $d_0$ 个能级。恢复输出可用一个 CPTP 压回该窗口的映射作后处理：保留窗口内块，将窗口外概率送入 $|0\rangle$。该后处理在理想窗口输入上是恒等，且不增加迹范数。有限维下界因而仍是原误差的下界。令 $d_0\to\infty$ 得二；通道距离的通用上界也是二。固定 $K$ 时有限窗口误差随 $M$ 非减并趋二；固定 $M$ 时 (O.31) 趋零，得到 (O.35)。$\square$

## 7. 固定返回容量的有限误差稳定性

**定义 7.1（同一幺正的近似幂压缩）。** 沿用定义 3.1 的 $J,U,K,R_n$，以 $D=\dim\mathcal H$、$p=\dim\mathcal S$ 记总维数和保留维数。设

$$
D_K=I-K^\dagger K,\quad s=\operatorname{rank}D_K>0,\quad
\lambda=\lambda_{\min}^{+}(D_K),\quad\kappa=\|K\|\leq1,
\quad\Delta_n=R_n-K^n.
\tag{O.37}
$$

$D_K$ 是正算子，$0<\lambda\leq1$，且 $\Delta_0=\Delta_1=0$。下文的 $D_K$ 是缺陷算子，不是相位校正通道 $\mathcal D_K$。

**定理 7.2（FIB 返回容量界的稳定版本）。** 对整数 $m\geq1$，若

$$
\max_{1\leq n\leq m}\|\Delta_n\|\leq\epsilon,
\qquad (m-1)(1+\kappa)^2\epsilon<\lambda,
\tag{O.38}
$$

则 $D\geq p+ms$。等价地，对 $m\geq2$，

$$
D<p+ms\quad\Longrightarrow\quad
\max_{2\leq n\leq m}\|R_n-K^n\|
\geq\frac{\lambda}{(m-1)(1+\kappa)^2}.
\tag{O.39}
$$

若整个封闭载体恰为长度 $\ell$ 的合法链、没有其他辅助空间，取

$$
m_\ell=\left\lfloor\frac{F_{\ell+2}-p}{s}\right\rfloor+1,
$$

则 $m_\ell\geq2$，且 (O.39) 在 $m=m_\ell$ 成立。这是定理 3.2 的算符误差加强，不指定某一初态的复兴峰高。

证明。把 $F=[J,UJ,\ldots,U^mJ]$ 看作从 $\mathcal S^{\oplus(m+1)}$ 到 $\mathcal H$ 的块列算子，令 $G=F^\dagger F$。其上三角块为 $G_{ij}=R_{j-i}$。定义 Hermitian 参考矩阵 $G_K$，上三角块为 $K^{j-i}$，下三角取伴随。零步和一步误差均为零，所以每个块行至多有 $m-1$ 个非零误差块。由块矩阵的行列和范数界，

$$
\|G-G_K\|\leq(m-1)\epsilon.
\tag{O.40}
$$

令 $B_0$ 为主对角 $I$、上邻对角 $-K$ 的块矩阵。它可写成单位算子减一个范数至多 $\kappa$ 的块移位，故 $\|B_0\|\leq1+\kappa$，而

$$
FB_0=[J,L,UL,\ldots,U^{m-1}L],\qquad L=UJ-JK.
$$

直接乘出参考矩阵得

$$
B_0^\dagger G_KB_0=\operatorname{diag}(I,D_K,\ldots,D_K),
$$

于是

$$
\left\|B_0^\dagger GB_0-
\operatorname{diag}(I,D_K,\ldots,D_K)\right\|
\leq(1+\kappa)^2(m-1)\epsilon.
\tag{O.41}
$$

在 $\mathcal W=\mathcal S\oplus((\ker D_K)^\perp)^{\oplus m}$ 上，参考矩阵的二次型至少为 $\lambda I$，且 $\dim\mathcal W=p+ms$。条件 (O.38) 保证实际 Gram 矩阵的二次型在 $\mathcal W$ 上仍严格为正，因此其秩至少为 $p+ms$。另一方面，$\operatorname{rank}(B_0^\dagger GB_0)\leq\operatorname{rank}F\leq D$。这证明维数界；以实际最大误差作 $\epsilon$ 得反向读法 (O.39)。

合法链维数为 $F_{\ell+2}$，而 $s=\operatorname{rank}L\leq F_{\ell+2}-p$，故 $m_\ell\geq2$。其定义给 $F_{\ell+2}<p+m_\ell s$，代入即可。经典精确扩张的出处沿用定理 3.2；本条在同一固定实现上加入非零谱隙和 Gram 扰动控制。$\square$

## 8. 精确与近似指数返回的不同维数律

**定义 8.1（有限窗口的标量返回实现）。** 固定 $q\in\mathbb C$、$|q|<1$，整数 $m\geq1$，误差 $\epsilon\geq0$。记 $D_{\min}(m,q,\epsilon)$ 为存在单位向量 $v\in\mathbb C^D$ 与同一个 $U\in U(D)$ 满足下式的最小 $D$：

$$
\langle v,Uv\rangle=q,\qquad
\max_{1\leq n\leq m}|\langle v,U^nv\rangle-q^n|\leq\epsilon.
\tag{O.42}
$$

一步压缩在所有误差等级下都要求精确。每个终点只压缩一次；没有中途测量、环境重置或随 $n$ 改变的门。$q=e^{-(\gamma/2+i\omega)\tau}$ 是一个可选参数化，需要另外指定 $\tau>0$、$\gamma>0$、$\omega\in\mathbb R$；$q=0$ 也属于数学模型，但不来自有限的这三个参数。

**定理 8.2（同一固定结构的线性精确容量与对数近似容量）。** 定义 8.1 满足

$$
D_{\min}(m,q,0)=m+1.
\tag{O.43}
$$

对固定 $q$ 和固定 $0<\epsilon<1$，

$$
D_{\min}(m,q,\epsilon)=\Theta_{q,\epsilon}(\log m)
\quad(m\to\infty).
\tag{O.44}
$$

更明确地，$m\geq2$ 时有

$$
D_{\min}(m,q,\epsilon)\leq
\min\left\{m+1,\ 2\left\lceil4\epsilon^{-2}
\log(8(m-1))\right\rceil\right\}.
\tag{O.45}
$$

令 $b_0=(1-\epsilon)/3$，选择任意整数 $n_0\geq1$ 使 $|q|^{n_0}\leq b_0$，并令 $Q_0=\lceil6\pi/(1-\epsilon)\rceil$。每个可行维数都满足

$$
m<n_0Q_0^D,\qquad
D>\frac{\log(m/n_0)}{\log Q_0}.
\tag{O.46}
$$

证明。精确下界是有限步幺正扩张的缺陷维数结论，采用定理 3.2 已归属的 Levy–Shalit Theorem 1.3；也可在定理 7.2 取 $p=s=1$、$\lambda=1-|q|^2$、$\epsilon=0$。为给出当前标量模型的显式上界，取正交基 $e_0,\ldots,e_m$，$a_q=\sqrt{1-|q|^2}$，规定

$$
Ue_0=qe_0+a_qe_1,\qquad
Ue_j=e_{j+1}\ (1\leq j<m),\qquad
Ue_m=a_qe_0-\overline q e_1.
\tag{O.47}
$$

这些列正交归一。令 $v=e_0$，从 $e_0$ 外逸的分量最早在第 $m+1$ 步返回，故前 $m$ 个返回振幅为 $q^n$。第 $m+1$ 步为 $q^{m+1}+1-|q|^2$。这给 (O.43)，也证明最小维数定义总可行。

接着给出保持精确一步压缩的近似构造。其两点谱测度与相位平均有直接文献先例：[Simon，*Orthogonal polynomials with exponentially decaying recursion coefficients*，Theorem 2.2](https://arxiv.org/pdf/math/0603099) 固定前面的 Verblunsky 系数，对末端相位作 Haar 平均，得到 Bernstein–Szegő 测度。取该文 $n=1$、$\alpha_0=\overline q$，每个两点测度保留首矩 $q$，平均为密度 $(1-|q|^2)/|e^{i\theta}-q|^2$ 的 Poisson 测度，其正整数矩为 $q^n$。下面直接验证当前矩阵的对应恒等式，不把固定首矩的相位平均机制作为新发明。对每个 $|\zeta|=1$ 取

$$
U_\zeta=\begin{pmatrix}q&a_q\\\zeta a_q&-\zeta\overline q\end{pmatrix},
\qquad f_n(\zeta)=\langle e_0,U_\zeta^ne_0\rangle.
\tag{O.48}
$$

列的内积为零且范数为一，因此 $U_\zeta$ 幺正。$f_n$ 是 $\zeta$ 的非负次幂多项式，其常数项为 $q^n$：在 $\zeta=0$ 时矩阵的第二行是零。均匀圆周平均消去其全部正次幂，所以

$$
|f_n(\zeta)|\leq1,\qquad f_1(\zeta)=q,\qquad
\mathbb E_\zeta f_n(\zeta)=q^n.
\tag{O.49}
$$

一次性独立取 $d_1$ 个均匀相位，设

$$
U=\bigoplus_{j=1}^{d_1}U_{\zeta_j},\qquad
v=d_1^{-1/2}(e_0\oplus\cdots\oplus e_0).
\tag{O.50}
$$

这时 $D=2d_1$，一步压缩精确为 $q$，而 $R_n=d_1^{-1}\sum_jf_n(\zeta_j)$。

使用 Hoeffding 的独立有界变量不等式作为经典中间步骤，见 [*Probability Inequalities for Sums of Bounded Random Variables*](https://doi.org/10.1080/01621459.1963.10500830)。在这里所需的 $[-1,1]$ 范围，中心化对数矩母函数的二阶导数是指数倾斜分布下的方差，至多为一；其零点处函数值和一阶导数都是零，所以该函数至多为参数平方的一半。独立相乘并用指数 Markov 不等式，得到样本平均的双侧偏差超过 $u>0$ 的概率至多 $2e^{-d_1u^2/2}$。实部和虚部分别满足该条件；复数模超过 $\epsilon$ 意味着其中一者超过 $\epsilon/\sqrt2$。因此

$$
\Pr(|R_n-q^n|>\epsilon)\leq4e^{-d_1\epsilon^2/4},
$$

再对 $n=2,\ldots,m$ 并合得

$$
\Pr\left(\max_{2\leq n\leq m}|R_n-q^n|>\epsilon\right)
\leq4(m-1)e^{-d_1\epsilon^2/4}.
\tag{O.51}
$$

取 $d_1=\lceil4\epsilon^{-2}\log(8(m-1))\rceil$，右侧至多为 $1/2$，故至少存在一组固定相位使全部要求成立。结合 (O.43) 得 (O.45)。随机化只证明这样一组相位存在；选定后，整个 $U,v$ 固定，演化不再注入随机性。这个界不提供给定原生门集上的高效选相或编译算法。

最后证明下界，使用同时相位逼近的经典鸽巢论证。任意 $D$ 维幺正 $V$ 的本征值写成 $e^{2\pi i x_j}$。将 $[0,1)^D$ 分为 $Q_0^D$ 个边长 $1/Q_0$ 的半开方块。$Q_0^D+1$ 个向量 $(kx_1,\ldots,kx_D)\bmod1$ 中必有两个落于同块，所以存在 $1\leq l\leq Q_0^D$ 使

$$
\|V^l-I\|\leq\frac{2\pi}{Q_0}\leq b_0.
\tag{O.52}
$$

应用于 $V=U^{n_0}$，置 $n=n_0l$。于是 $n\leq n_0Q_0^D$，且

$$
|R_n-1|\leq b_0,\qquad |q^n|\leq b_0,\qquad
|R_n-q^n|\geq1-2b_0=\frac{1+2\epsilon}{3}>\epsilon.
$$

该步必在允许窗口以外，故 $m<n_0Q_0^D$，给 (O.46)。固定 $q,\epsilon$ 时 $n_0,Q_0$ 是常数；与 (O.45) 合并即得 (O.44)。$q=0$ 时可取 $n_0=1$，不使用 $\log|q|$。$\square$

**推论 8.3（精度转折、复返与单时刻统计）。** 对 $m\geq2$，

$$
\epsilon<\frac{1-|q|^2}{(m-1)(1+|q|)^2}
\quad\Longrightarrow\quad D_{\min}(m,q,\epsilon)=m+1.
\tag{O.53}
$$

对任意固定有限维 $U$、单位向量 $v$ 和 $|q|<1$，

$$
\limsup_{n\to\infty}|\langle v,U^nv\rangle-q^n|=1.
\tag{O.54}
$$

若窗口内振幅误差至多为 $\epsilon$，则相应单时刻生存概率误差至多为 $2\epsilon$。

证明。将定理 7.2 代入 $p=s=1$、$\lambda=1-|q|^2$、$\kappa=|q|$，再用 (O.43) 的上界，得到 (O.53)。有限本征相位的同时复返给一列 $n_j\to\infty$ 满足 $U^{n_j}\to I$：让 (O.52) 的分割不断变细；若所选正整数有无界子列便得到结论，若它们有有界子列，则某个正整数给精确周期，其倍数给出所需序列。沿该列 $R_{n_j}\to1$、$q^{n_j}\to0$。反之 $|R_n-q^n|\leq1+|q|^n$，所以其上极限恰为一。概率界由

$$
\bigl||R_n|^2-|q|^{2n}\bigr|
\leq|R_n-q^n|(|R_n|+|q|^n)\leq2\epsilon
$$

得到。$\square$

**定义 8.4（静态谱解释与归属范围）。** 谱分解 $U=\sum_j e^{-i\theta_j}\Pi_j$ 给

$$
R_n=\sum_jp_je^{-in\theta_j},\qquad
p_j=\langle v,\Pi_jv\rangle\geq0,\quad\sum_jp_j=1.
\tag{O.55}
$$

定理 8.2 的构造因而是固定 Euler 相位叠加在压缩读出中的有限窗口包络。对数谱点数与指数长度窗口的随机幂和机制已有 [Erdős–Rényi，*A probabilistic approach to problems of Diophantine approximation*，Theorems 1–2，pp.303–305](https://www.renyi.hu/~p_erdos/1957-01.pdf) 的直接先例：他们对零目标的等权幂和使用独立圆周相位、指数尾界与并合界，并以同时 Dirichlet 逼近给出复返障碍。其打印结论没有要求一般首矩精确为 $q$。[Ambainis–Nahimovs，*Improved constructions of quantum automata*，Theorem 2 与 §3.2](https://arxiv.org/pdf/0805.1686) 也使用二维旋转块直和与等幅初态，在有限循环输入问题中实现对数状态数；那是零目标的模素数判别，不能直接替代本卷的一般 $q$ 合同。

精确扩张维数、Simon 的固定首矩平均、Hoeffding 浓缩和有限谱复返均为归属明确的中间原理。本卷的容量陈述是它们在同一压缩合同中的定量综合，不把相位平均、二维块架构或对数容量规律宣称为原创。式 (O.44) 固定 $q$、非零 $\epsilon$ 和采样合同，不声称关于 $q\to1$、$\epsilon\to0$ 或连续时间的统一估计。它控制末端返回振幅，不是完整开放通道、连续测量联合分布或条件轨迹的模拟。

## 9. 内生观察者的可读精度与时钟容量

**定义 9.1（实际接口和任务价值）。** 采用第 5 节的内生策略 $a=\pi(h)$，把允许的门、记录的实际可读字段、读出精度、资源成本纳入未来节点等价。未被安装为操作数的原始时间记录不自动成为策略的输入。在《[原生在线获取与执行](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ONLINE_ACQUISITION_ACTUATION.md)》的 $\omega$ 运行时，Corollary 9.1 给联合结构—时间接口的纤维大小 $2^{r(c)}$；只有原始叶标签的首次分类 Probe 减少 $r(c)$，其他执行行不减少它。Theorem 10.3 和 Corollary 10.4 分别区分原始时间纤维 $\prod_i2^{h_i}C_{h_i-1}$ 与固定形状的联合纤维 $2^{\sum_i h_i}$。这里引用这些精确执行结论，不将它们移植到该卷的 $\iota$ 运行时。

在固定相位任务中，可用《[相位增益与 qutrit 恢复](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md)》定义 15.1 的 $rc_n$ 作为期望恢复价值。它的增量 $r(c_{n+1}-c_n)$ 非负，但独立记录以及该卷命题 15.3 给零增量；执行步数、纤维基数和任务价值不是同一变量。精确实数响应的单射也没有指定有限记录成本。《[V1 整纤维饱和](FIB_V1_ENTIRE_GAIN_PLANE_SATURATION.md)》定理 31.2 与《[C35 整纤维 JM 响应](FIB_C35_ENTIRE_JM_RESPONSE_INJECTIVITY.md)》定理 2.1 分别针对其指定历史证明实际响应单射；本卷的均匀相位容量式没有为这些非均匀实代数纤维提供误差标定或编码器。

**定理 9.2（完全可辨时刻的额外容量）。** 若一个闭合实现中的观察者必须在时刻 $0,1,\ldots,m$ 保存可由同一个无误差读出测量完全区分的时钟态，则时钟承载空间至少为 $m+1$ 维。因此，定理 8.2 的对数返回实现没有给出包含这种完整时钟及全部历史档案的对数总维数保证。

证明。设时钟态为 $\rho_0,\ldots,\rho_m$，测量效应为 $E_0,\ldots,E_m$，$\sum_jE_j=I$ 且 $\operatorname{tr}(E_j\rho_k)=\delta_{jk}$。正性给 $E_k$ 在 $\operatorname{supp}\rho_k$ 上等于一，并在所有 $\operatorname{supp}\rho_j$、$j\ne k$ 上等于零。由于 $E_k$ 自伴，其一与零本征空间正交，所以各状态的非零支撑彼此正交，至少需要 $m+1$ 个方向。对纯经典记录，这正是 $m+1$ 个正交符号的计数。若另行采用独立张量时钟寄存器，其维数应与返回系统维数相乘；若共享空间则仍需证明二者的联合可实现性，不能直接相加或相乘最优值。$\square$

## 追加锚（本行以下为增补区）

## 10. 含记录与程序的静态 AURIC 条件历史

**定义 10.1（有限内生读出的共同载体）。** 固定第 5 节的一棵有限深度仪器树，所有动作菜单和输出字母表有限。准备对象、内部控制程序、既有记录及足够多的空白记录单元，把它们放入同一个有限寄存器 $\mathcal Q$。第 $n+1$ 步动作只由已经生成且实际可读的历史 $h_n$ 决定：$a_{n+1}=\pi(h_n)$。对每个动作供给其完整仪器的有限幺正扩张；控制计算和新记录写入也必须可由联合幺正门实现。将这些门合成 $U_{n+1}$，所有已使用及将使用的辅助空间均计入 $\mathcal Q$。这是假设一个实际有限实现，不是由抽象菜单推出原生可控性。

另供正交时钟 $\mathcal C=\operatorname{span}\{|0\rangle,\ldots,|N\rangle\}$，规定相邻关系和单位初始向量 $\psi_0\in\mathcal Q$。置 $W_0=I$、$W_n=U_n\cdots U_1$，定义

$$
A_n=\langle n+1|\otimes I-\langle n|\otimes U_{n+1},\qquad
H_{\rm prop}=\sum_{n=0}^{N-1}A_n^\dagger A_n.
\tag{O.56}
$$

该时钟是联合描述内部的一个寄存器；其分解、邻接、程序、边界和读出权限都是模型输入。

**定理 10.2（内生仪器的静态条件实现与零残差变化）。** 在定义 10.1 的同一有限实现中，固定联合态

$$
|\Psi\rangle=\frac1{\sqrt{N+1}}\sum_{n=0}^N|n\rangle W_n|\psi_0\rangle
\tag{O.57}
$$

满足 $H_{\rm prop}\Psi=0$。条件于时钟 $n$，联合对象、程序和记录恰为 $W_n\psi_0$；对已写入历史再作条件化，得到第 5 节仪器树相同的分支概率和条件状态。因而有限的 AURIC 记录门、转移仪器或相位探针实现，在其扩张和制备被供应时，都可用一个固定的联合相容态表示，不需再引入一个沿该态运动的外部观察者。

所有零能向量及传播算子的受控换基为

$$
\begin{aligned}
\ker H_{\rm prop}
&=\left\{\sum_{n=0}^N|n\rangle W_n\phi:\phi\in\mathcal Q\right\},\\
\mathcal W&=\sum_{n=0}^N|n\rangle\langle n|\otimes W_n,\qquad
\mathcal W^\dagger H_{\rm prop}\mathcal W=L_{\rm path}\otimes I,
\end{aligned}
\tag{O.58}
$$

其中 $L_{\rm path}=\sum_{n=0}^{N-1}(|n+1\rangle-|n\rangle)(\langle n+1|-\langle n|)$。所以裸传播谱不确定指定读口的动力学，而条件变化也不要求非零传播残差。

证明。使用 Feynman--Kitaev 历史态作为已知中间构造，参数对应为时钟位置 $n$、全部联合寄存器 $\mathcal Q$ 和实际联合门 $U_{n+1}$。参见 Caha--Landau--Nagaj，[*The Feynman-Kitaev computer's clock: bias, gaps, idling and pulse tuning*, §2.2, Eqs. (4)--(5)](https://arxiv.org/abs/1712.07395)；受控去门共轭参见 Bausch--Crosson，[*Analysis and limitations of modified circuit-to-Hamiltonian constructions*, Lemma 2](https://arxiv.org/abs/1609.08571)。这些一般构造不作为本卷新增定理。这里需要核对的是内生读出树的同一实现对应。

每个动作的仪器等距为 $\xi\mapsto\sum_yK_{a,y}\xi\otimes|y\rangle$，完备性保证它可在预分配空间中补全为幺正。以互相正交的已存历史控制动作，就使用 $\pi(h_n)$，而非未知世界标签。归纳后 $W_n\psi_0$ 的各历史分量正是第 5 节的 $K_h\psi_0$ 连同所需工作寄存器，其平方范数是原仪器概率。所有这些分支在同一个 $W_n$ 中产生，未把分别可达的控制拼成共同策略。混合初态可先在 $\mathcal Q$ 中计入纯化寄存器。

对任意 $\Phi=\sum_n|n\rangle\phi_n$，

$$
\langle\Phi,H_{\rm prop}\Phi\rangle
=\sum_{n=0}^{N-1}\|\phi_{n+1}-U_{n+1}\phi_n\|^2.
$$

正项之和为零等价于逐项为零，即 $\phi_n=W_n\phi_0$，证明核公式和 (O.57)。又 $A_n\mathcal W=(\langle n+1|-\langle n|)\otimes W_{n+1}$，取伴随乘积给共轭式。投影时钟 $n$ 的概率是 $1/(N+1)$，归一化条件态是 $W_n\psi_0$，再投影实际历史就得上述仪器统计。

最后，在一个 AURIC 单元的二态子码 $\operatorname{span}\{e_0,e_1\}$ 供交换门 $Xe_0=e_1,Xe_1=e_0$，令 $N=1,\psi_0=e_0$。历史态为 $(|0\rangle e_0+|1\rangle e_1)/\sqrt2$。两个条件态正交，但 $e_1-Xe_0=0$，故传播残差仍为零。这证明相容残差和可读条件差异并非同一量。$\square$

**假设 10.3（静态表示的观察边界）。** 关系时间的历史态背景参见 Page--Wootters，[*Evolution without evolution: Dynamics described by stationary observables*, DOI:10.1103/PhysRevD.27.2885](https://doi.org/10.1103/PhysRevD.27.2885)。定理 10.2 是有限门与仪器的条件表示，不从无结构集合导出唯一时间顺序，不从 $H_{\rm prop}$ 的谱单独恢复原寄存器分解。不同门串可以有相同传播谱。对静态历史态条件化也不自动等同于在该态上连续实施实际时钟测量；后者要另给测量仪器及其回作用。新增正交时钟、空白记录、程序和工作空间均有容量成本，不能借用定理 8.2 的返回维数而免计。

**命题 10.4（同一 AURIC 子码中的读出与撤销边界）。** 在定义 10.1 中，以有限来源标签 $X$、已有可读记录 $H$ 和新增实际读数 $Y$ 定义任务信息。若 $I(X:Y\mid H)>0$，则某个正概率的旧记录上，不同相容来源的新增可读响应分布必有区别。内生控制条件本身既不保证每次读出取得这种信息，也不保证形成永久记录。另一方面，若同一联合幺正精确保留两个非正交纯对象态，且初始记录相同，则不能留下区分它们的记录。

证明。条件互信息为各旧记录上条件响应律与其条件乘积律之相对熵的平均；相对熵非负，且等于零当且仅当两律相同。因此正值要求某个正概率旧记录上的响应依赖来源。若该记录下全部可访问来源条件态 $\sigma_{x,h}$ 相同，任何共同 POVM 都给相同的 $\operatorname{tr}(E_y\sigma_{x,h})$，不能取得上述正值。这是信息确实新增所需的可读区别，不保证其被永久保留。

在两个 AURIC 单元的二态子码上，按定义 10.1 另行供给精确 CNOT。它使 $|x\rangle|0\rangle\mapsto|x\rangle|x\rangle$，对正交标签 $x=0,1$ 保留对象且给出无误记录。假设 1.3 只给原生近似，不替代这里的精确供应；采用近似门时须另计误差。再把已知标签复制到另一空白子码，条件于第一记录，第二记录由它确定，故 $I(X:O_2\mid O_1)=0$。两次作用同一个 CNOT 则在 $|+\rangle|0\rangle$ 上建立后又解除相关性，联合初态复原；有其他保留副本时必须把其纳入总空间，不能只对局部声称全局复原。

非正交边界使用已知的信息获取--扰动原理，参见 Fuchs--Peres，[*Quantum State Disturbance vs. Information Gain*, DOI:10.1103/PhysRevA.53.2038](https://arxiv.org/abs/quant-ph/9512023)。在这里的纯态保留情形，其适用步骤是：若 $U(\psi_b\otimes r)=\psi_b\otimes m_b$，则内积保持给

$$
\langle\psi_0|\psi_1\rangle
=\langle\psi_0|\psi_1\rangle\langle m_0|m_1\rangle.
$$

对象内积非零就得 $\langle m_0|m_1\rangle=1$，两个单位记录相同。若原联合输出纯且对象约化态仍是原纯态，Schmidt 分解保证上述乘积形式，故没有额外的乘积输出限制。这些已知中间事实在同一子码中给出反例与边界；内生性并不替代输入族、可读权限或不撤销假设。$\square$

## 11. 有限 AURIC 载体对永久关系时钟的限制

**定义 11.1（当前记忆量与完整历史的不同任务）。** 取长度 $\ell$ 的合法 FIB 链 $\mathcal K_\ell$，总维数 $D=F_{\ell+2}$。它是整个闭系统的承载空间；若有额外时钟或环境，应先扩大 $D$。给固定 $U\in U(D)$ 和初态 $\rho_0$，以及固定记忆通道 $\mathcal M$，记

$$
\rho_n=U^n\rho_0U^{-n},\qquad \sigma_n=\mathcal M(\rho_n).
\tag{O.59}
$$

$\mathcal M$ 可以是一个已供应张量分解中的部分迹，也可以是已指定的记忆读口。当前记忆价值为状态空间上的连续实函数 $V$。保存历史的另一任务是把 $L$ 个等概历史编码成同一个 $d$ 维可读寄存器中的态 $\sigma_h$，并以同一 POVM $(E_h)$ 解码；编码、寄存器和测量不能依真实未知标签另换。

**定理 11.2（同一有限载体的单调性障碍与可读历史容量）。** 定义 11.1 的固定闭合实现若满足 $V(\sigma_{n+1})\geq V(\sigma_n)$ 对所有 $n\geq0$，则

$$
V(\sigma_n)=V(\sigma_0)\quad\text{对所有 }n\geq0.
\tag{O.60}
$$

对同一定义的历史解码任务，

$$
P_{\rm succ}=\frac1L\sum_h\operatorname{tr}(E_h\sigma_h)\leq\min\{1,d/L\}.
\tag{O.61}
$$

特别地，若在完全计数的载体中供应一个 $d\leq D$ 的历史寄存器，要求等概时刻 $0,\ldots,m$ 的成功率至少为 $1-\varepsilon>0$，则

$$
(m+1)(1-\varepsilon)\leq d\leq F_{\ell+2}.
\tag{O.62}
$$

所以有限窗口返回振幅的对数容量、可无误保存的时刻数，以及全程单调的当前记忆量，是不同的资源要求。

证明。有限幺正谱同时复返是已知中间原理；本卷推论 8.3 的证明已给一列 $n_j\to\infty$ 使 $U^{n_j}\to I$。因而 $\rho_{n_j}\to\rho_0$，固定有限维通道的连续性给 $\sigma_{n_j}\to\sigma_0$。对任意固定 $n$ 和足够大的 $j$，

$$
V(\sigma_0)\leq V(\sigma_n)\leq V(\sigma_{n_j})\longrightarrow V(\sigma_0),
$$

得到 (O.60)。这是复返作用于同一记忆读口的直接应用；不把一般复返--Lyapunov 障碍作为新定理。

维数解码界也是标准中间估计：$0\leq\sigma_h\leq I_d$，所以

$$
\frac1L\sum_h\operatorname{tr}(E_h\sigma_h)
\leq\frac1L\sum_h\operatorname{tr}E_h=\frac dL.
$$

它亦由第 6 节引用的有限量子存储猜测界得到；这里只取其无需旁信息的特例。代入 $L=m+1$ 得 (O.62)。任意先验、连续参数估计、可访问额外寄存器或选择性成功不在这一等概合同内。$\square$

**命题 11.3（关系方向、圈数与当前状态的区别）。** 在固定有限 AURIC 实现的未来状态图中，若存在返回同一完整节点的有向环，则不存在沿环上每条边严格增加的单值节点时间。若实际可读历史按 $h\mapsto(h,y)$ 追加且不撤销，严格前缀关系可给扩展历史节点一个方向；要把周期相位展开为累计钟，必须使圈数或等价档案也进入该节点。这个追加方向不保证相位恢复价值或每条后验路径严格增加。

证明。沿闭环严格增加会给 $\tau(v)<\tau(v)$，矛盾。严格前缀关系具有传递性且不可自反，因此是严格偏序；每次实际追加都增加可读长度。在有限无环图上可用拓扑排序构造递增函数，但这仅是相应节点图上的序，不规定物理秒数。周期相位 $e^{i\varphi}=e^{i(\varphi+2\pi k)}$ 不能区分圈数；扩展为相位与圈数或保存历史后，这些端点才不同。第 9 节的零价值执行以及相位卷命题 15.3 已给“记录增加而目标恢复价值不严格增加”的实例。插入 $I$ 或 $VV^\dagger$ 也会改变门串长度而不改变端点；若实际执行留下中间记录，应计入不同的联合历史，不能仅以端点抹除。$\square$

**假设 11.4（关系时间的接合范围）。** 定理 10.2 供有限相容条件历史；相位卷定理 16.2、17.2 在指定探针和访问权限下供可读长度及其退化条件；命题 11.3 在不撤销的可读追加合同下供历史方向。要把它们解释为同一内生时钟，仍需供应同一实现中的时钟对应、门选择与记录权限，并校准相位相对于该钟的关系 $\varphi=f(\tau)$。定理 11.2 排除固定有限闭空间中的非恒定全程单调连续记忆量；它不排除周期钟、有限时域增长、长衰减窗口或使用扩展历史而非当前记忆的函数。

相位卷定理 17.2 的 $\sum_j-\log c_j$ 是固定二分支的记录强度，不是 (O.61) 中不同历史数的对数；两种界不能互相替代。只有已计入总空间的新张量载体才能支持相应的新鲜记录合同。每个有限阶段不完备也不要求极限误差为正：相位卷定理 15.2 已把极限恢复与目标对极限可读记录的可测性相联系。因此，有限未知、永久盲核和无界记录容量是分别需要条件的陈述。

## 追加锚（本行以下为增补区）
