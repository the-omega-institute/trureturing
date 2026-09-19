# 电磁预测几何：洛伦兹耦合、热响应与可辨识状态

**版本：** v1.0，2026-09-20。

**证明层级：** 本卷给出带前件的纸面推导与可重建算例，尚无配套 Lean 证明项或独立同行核验。最小耦合、磁 Poisson 括号、Maxwell 场论、涨落耗散、Aharonov–Bohm 效应及 Fock–Darwin 谱均属既有理论。本卷将其接到目标相对预测闭包与相关数据证书，不认领全球优先权、新的外部猜想结算或物理统一理论。

本卷承接 [辛预测完成卷](SYMPLECTIC_PREDICTIVE_COMPLETION.md) 第 4–9 节与 [预测可观测性时间窗卷](PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md) 第 8、12–19 节。新增电磁分卷用于容纳规范势、场的闭合约束与磁场控制的观测实例；已有三卷保持原样。

## 0. 对象与范围

固定带符号电荷 e、质量 m>0、位置 r、正则动量 p、动力学动量 π=mv，以及标势 φ、矢势 A。除明确采用归一单位的章节外，使用 SI 形式的洛伦兹力。磁场 B 与生成元矩阵使用不同记号；时间相关矩阵记为 F_c(t)，电磁二形式记为 ℱ。

比较对象有四层：经典轨迹与 Poisson 几何；热平衡分布及耗散；量子观测代数及谱；电磁场与物质耦合。每条迁移保留指定的状态空间、边界、观测、统计律和实验输入。存在共同结构不自动给出任意模型之间的物理等价。

## 1. 从一个作用量得到洛伦兹力与最小耦合

### 命题 1.1（带电粒子的 Hamilton 表示）

设 A(r,t)、φ(r,t)、U(r) 光滑，考虑

$$
L=\frac m2|\dot r|^2+eA(r,t)\cdot\dot r-e\phi(r,t)-U(r).
$$

则

$$
p=m\dot r+eA,\qquad
H(r,p,t)=\frac{|p-eA|^2}{2m}+e\phi+U,
$$

Euler–Lagrange 方程等价于

$$
m\ddot r=-\nabla U+e(E+\dot r\times B),
\quad E=-\nabla\phi-\partial_tA,\quad B=\nabla\times A.
$$

**证明。** 对速度求导得到 p；作 Legendre 变换得到 H。第 i 个 Euler–Lagrange 方程中，矢势项合并为 e(∂iAj−∂jAi) vj−e∂tAi，即磁叉积项与感生电场项。$\square$

规范变换 A↦A+∇χ、φ↦φ−∂tχ 使 L 增加 e dχ/dt，因此在固定端点变分中保留轨迹方程。动力学动量 π 与正则动量 p 必须区分，尤其是在比较热协方差时。[T-Dyn]

### 推论 1.2（磁耦合的瞬时功率）

$$
\dot r\cdot e(\dot r\times B)=0,
\qquad
\frac d{dt}\left(\frac m2|\dot r|^2+U\right)=e\dot r\cdot E.
$$

这是点电荷速度与磁力的正交性。电机、磁性材料和受约束导体的机械能流必须连同电源、感生电场及场能一起记账，不能将这个等式理解成整台电机无法输出机械功。

## 2. 磁场是 Poisson 配对中的曲率

本节先取静态磁场。定义三阶反对称矩阵

$$
\mathcal B_{ij}(r)=\varepsilon_{ijk}B_k(r),
\qquad\mathcal Bv=v\times B,
$$

以及动力学坐标 (r,π) 上的矩阵

$$
J_B=\begin{pmatrix}0&I_3\\-I_3&e\mathcal B\end{pmatrix}.
$$

### 命题 2.1（磁 Poisson 括号与 Jacobi 条件）

令 e≠0。由 J_B 定义的括号满足

$$
\{r_i,r_j\}=0,\quad\{r_i,\pi_j\}=\delta_{ij},
\quad\{\pi_i,\pi_j\}=e\varepsilon_{ijk}B_k.
$$

它满足 Jacobi 恒等式，当且仅当 ∇·B=0。J_B 处处可逆，对应第 0 节辛约定的二形式为

$$
\omega_B=\sum_i dr_i\wedge d\pi_i
-\frac e2\sum_{i,j}\mathcal B_{ij}\,dr_i\wedge dr_j.
$$

**证明。** 所有包含位置坐标的 Jacobi 三元组都为零。三个不同动量的三元组给出

$$
\{\pi_1,\{\pi_2,\pi_3\}\}+\text{cyclic}=-e\nabla\cdot B.
$$

一般函数的 Jacobiator 是坐标 Jacobiator 与其一阶导数的组合，因此这是充分必要条件。块矩阵求逆给出

$$
-J_B^{-1}=\begin{pmatrix}-e\mathcal B&I_3\\-I_3&0\end{pmatrix},
$$

其外微分为 −e(∇·B) dr1∧dr2∧dr3。$\square$

对于 H0=|π|²/(2m)+U，方程 ż=J_B∇H0 给出静态磁场中的洛伦兹运动。非零磁场通过改变变量之间的配对进入动力学，即使 H0 的表达不含 B。只约束一个学习矩阵反对称，足以得到能量守恒项，却不足以保证 Jacobi；磁场模型还须满足上述闭合条件。[T-Dyn, GEMPIC]

### 命题 2.2（时空曲率与齐次 Maxwell 方程）

取一形式 a=A·dr−φdt，定义 ℱ=da。则

$$
\mathcal F=\frac12\sum_{i,j}\mathcal B_{ij}\,dr_i\wedge dr_j
+\sum_i E_i\,dr_i\wedge dt,
$$

$$
d\mathcal F=0
\iff
\nabla\cdot B=0,\qquad\partial_tB+\nabla\times E=0.
$$

**证明。** 展开 da 得到所示各分量；再按三个空间指标与两个空间加一个时间指标分别展开外微分即可。d²a=0 保证条件成立。反向在可缩局部区域由 Poincaré 引理存在势；全局势还取决于拓扑。$\square$

这个等式给出磁 Gauss 律和 Faraday 律的共同几何形式。带电源的另一半 Maxwell 方程还需要场能作用量、时空度量、材料关系及电流，不能单凭 Jacobi 恒等式推出。[T-GR, T-QFT]

## 3. 电磁场本身的 Hamilton 系统与边界功率

以无源真空场为明确实例。在周期边界或足够快衰减的横向规范下，取横向矢势 A_T 与共轭动量 Π=−ε0 E_T，定义

$$
H_{\rm EM}=\int\left(\frac{|\Pi|^2}{2\epsilon_0}
+\frac{|\nabla\times A_T|^2}{2\mu_0}\right)dr.
$$

其变分导数给出

$$
\partial_t A_T=\Pi/\epsilon_0=-E_T,\qquad
\partial_t\Pi=-\mu_0^{-1}\nabla\times B.
$$

因此恢复无源 Maxwell 演化；横向约束保留 Gauss 律。有限域上进行分部积分时必须保留边界项。一般真空带源的能量平衡为

$$
\frac d{dt}\int_\Omega
\left(\frac{\epsilon_0|E|^2}{2}+\frac{|B|^2}{2\mu_0}\right)dr
=-\int_{\partial\Omega}\frac{E\times B}{\mu_0}\cdot n\,dS
-\int_\Omega j\cdot E\,dr.
$$

**推导。** 将 E 点乘 Ampère–Maxwell 方程，将 B/μ0 点乘 Faraday 方程，相加并使用散度公式。$\square$

可见，场是无限维状态，Lorentz 耦合在粒子与场之间传递作用，边界 Poynting 通量给出实际输入输出端口。GEMPIC 已将这一 Hamilton–Poisson 结构用于保持散度与电荷约束的离散化；该基本框架不登记为本卷的新算法。[GEMPIC]

## 4. 量子最小耦合与全局相位信息

### 命题 4.1（同一曲率决定动力学动量交换子）

在共同光滑测试函数域上令

$$
\widehat\pi_i=-i\hbar\partial_i-eA_i,
\qquad
\widehat H=\frac1{2m}\sum_i\widehat\pi_i^2+e\phi+U.
$$

则

$$
[\widehat r_i,\widehat\pi_j]=i\hbar\delta_{ij}I,
\qquad
[\widehat\pi_i,\widehat\pi_j]=i e\hbar\varepsilon_{ijk}B_k.
$$

规范变换与 ψ↦exp(ieχ/ℏ)ψ 相容。

**证明。** 展开微分算子的交换子，二阶导数互消，余项为 ieℏ(∂iAj−∂jAi)。将变换后的势和振幅代入 Schrödinger 方程，空间导数与时间导数的 χ 项分别抵消。$\square$

于是局部磁曲率在经典侧为 Poisson 括号，在量子侧为协变导数的交换子。统一推导必须保留算子域和可观测代数，不能只把所有矩阵都称为同一物理系统。[T-QFT]

### 例 4.2（环上的相同局部场与不同全局谱）

在半径 R 的理想环上，通量 Φ 位于粒子不能进入的内部区域。环上局部 B 为零，但

$$
\exp\left(\frac{ie}{\hbar}\oint A\cdot dr\right)
=\exp(ie\Phi/\hbar)
$$

可以非平凡。周期波函数的能级为

$$
E_n=\frac{\hbar^2}{2mR^2}
\left(n-\frac{e\Phi}{2\pi\hbar}\right)^2,\qquad n\in\mathbb Z.
$$

**推导。** 环切向势可取常数 Φ/(2πR)，对动量算子 −iℏ∂θ/R−eΦ/(2πR) 的 Fourier 本征函数直接求平方。$\square$

这给出一个全局观测不足的成对实例：相同局部 Lorentz 场不必决定相同量子相位与谱；还须保留闭环 holonomy。该现象属于既有 Aharonov–Bohm 理论，不是新猜想解答。[AB59]

## 5. 热力学中的无耗散磁耦合与耗散对称部分

### 命题 5.1（恒温 Kramers 模型的 Gibbs 不变律与熵耗散）

设 U 光滑且 exp(−βU) 可积，B 静态，Γ 为常数对称半正定矩阵，β>0。考虑

$$
dr=\frac\pi mdt,
$$

$$
d\pi=\left[-\nabla U+e\mathcal B(r)\frac\pi m
-\Gamma\frac\pi m\right]dt+\sqrt{2\beta^{-1}\Gamma}\,dW_t.
$$

在确保存在性、可积性及分部积分无边界余项的条件下，Gibbs 密度

$$
g_\beta(r,\pi)=Z^{-1}\exp\left[-\beta\left(\frac{|\pi|^2}{2m}+U(r)\right)\right]
$$

不变。对光滑正密度 ρ，

$$
\frac d{dt}D_{\rm KL}(\rho\Vert g_\beta)
=-\beta^{-1}\int\rho\,
\nabla_\pi\log(\rho/g_\beta)^T\Gamma
\nabla_\pi\log(\rho/g_\beta)\,dr\,d\pi\le0.
$$

**证明。** Hamilton–Lorentz 漂移在 (r,π) 测度下无散，且与 ∇H0 正交，所以保留 gβ，积分时对相对熵无贡献。摩擦与扩散部分为

$$
\beta^{-1}\nabla_\pi\cdot
\left[\Gamma\rho\nabla_\pi\log(\rho/g_\beta)\right].
$$

乘以 log(ρ/gβ) 并分部积分即得耗散式。$\square$

磁场可以改变后续分布及松弛速度；上述结论只表示同一个瞬时密度下，磁项不直接进入这个相对熵耗散式。物理时间反演需要同时翻转动量和磁场，不默认固定 B 的普通详细平衡。空间变温或消去惯性可能引入额外熵项，不能直接套用本命题。[Bir17]

### 命题 5.2（从速度相关斜率分离磁耦合与摩擦）

在命题 5.1 的常数磁场版本中，令 v=π/m，并取平衡初态。定义归一化速度相关

$$
K_v(t)=\beta m\,\mathbb E[v_tv_0^T].
$$

则其右导数满足

$$
K_v'(0+)=\frac em\mathcal B-\frac1m\Gamma,
$$

$$
\operatorname{Skew}K_v'(0+)=\frac em\mathcal B,
\qquad
\operatorname{Sym}K_v'(0+)=-\frac1m\Gamma.
$$

**证明。** 对条件均值用 Langevin 生成元求右导数。Gibbs 初态使位置与速度独立、速度均值为零，因此势能力与 v0 的交叉平均为零；E[v0v0ᵀ]=(βm)⁻¹I。噪声增量与初态交叉期望为零。$\square$

该分解允许非二次 U，但要求本节的常系数和热平衡条件。估计有限延迟斜率及处理传感器噪声仍须另给预算。它明确显示，静态热分布与动态相关读取的是不同对象。

## 6. 同一带电振子的经典、量子与热表示

固定平面各向同性势 U=mω0²(x²+y²)/2，ω0>0，垂直恒定磁场 B0，带符号回旋频率 c=eB0/m。定义能量归一状态

$$
\xi=(\omega_0x,\omega_0y,v_x,v_y)^T.
$$

它满足

$$
\dot\xi=\Omega_c\xi,\qquad
\Omega_c=\begin{pmatrix}
0&0&\omega_0&0\\
0&0&0&\omega_0\\
-\omega_0&0&0&c\\
0&-\omega_0&-c&0
\end{pmatrix},\qquad\Omega_c^T=-\Omega_c.
$$

物质能量为 m|ξ|²/2，在恒定 B0 下守恒。Gibbs 协方差为 (βm)⁻¹I4，与 B0 无关。以正则相空间 Lebesgue 测度积分，经典分区函数为

$$
Z_{\rm cl}=\frac{(2\pi)^2}{\beta^2\omega_0^2},
$$

这里尚未除以相空间量子归一因子。独立于磁场的经典结果是 Bohr–van Leeuwen 机制的这个实例，不包含自旋和材料磁性。[T-Dyn]

### 命题 6.1（两种频率和量子分区函数）

$$
\det(\lambda I-\Omega_c)
=\lambda^4+(2\omega_0^2+c^2)\lambda^2+\omega_0^4,
$$

正模态频率可写为

$$
\omega_\pm=\sqrt{\omega_0^2+c^2/4}\pm c/2,
\quad\omega_+\omega_-=\omega_0^2.
$$

对无自旋量子振子，

$$
E_{n_+,n_-}=\hbar\omega_+(n_++1/2)+\hbar\omega_-(n_-+1/2),
$$

$$
Z_{\rm q}=\left[4\sinh(\beta\hbar\omega_+/2)
\sinh(\beta\hbar\omega_-/2)\right]^{-1}.
$$

**推导。** 特征多项式由块矩阵展开。选对称规范 A=(−B0y/2,B0x/2)，量子 Hamilton 算子等于频率 √(ω0²+c²/4) 的二维各向同性振子减去 cLz/2。用圆偏振升降算子对角化得到两项独立振子能谱，再求两个几何级数得到 Zq。$\square$

这些是既有 Fock–Darwin 结果 [LFO90]。量子 Zq 一般依赖 |B0|，其高温首项为 (β²ℏ²ω0²)⁻¹，与经典相空间积分除以 (2πℏ)² 后一致。

当 c=ω0 时，ω+/ω0=φ、ω−/ω0=φ⁻¹，其中 φ=(1+√5)/2。这是可调频率比的精确实例，由所选择的参数比产生，不能据此认领黄金比是电磁学普遍常数。

## 7. 磁场改变最小预测状态，却不改变静态能量

令当前唯一读数为 y=Cξ，其中 C=(1,0,0,0)，ω0 和 c 已校准。使用归一状态的欧氏范数以及连续时间读数的 L2 范数。

### 定理 7.1（单位置观测的磁激活）

若 c=0，完整四维状态不能由 y 的未来恢复，其最小预测闭包为二维。若 c≠0，单个位置读数在每个 T>0 上对完整四维状态可观测。

**证明。** 导数观测矩阵为

$$
\mathcal O=\begin{pmatrix}
1&0&0&0\\
0&0&\omega_0&0\\
-\omega_0^2&0&0&c\omega_0\\
0&-c\omega_0^2&-\omega_0(c^2+\omega_0^2)&0
\end{pmatrix},
\quad\det\mathcal O=-c^2\omega_0^4.
$$

c=0 时仅张成第一位置与其速度方向。c≠0 时矩阵可逆，具体重建为

$$
\xi_1=y,\quad\xi_3=y'/\omega_0,\quad
\xi_4=\frac{y''+\omega_0^2y}{c\omega_0},
$$

$$
\xi_2=-\frac{y'''+(c^2+\omega_0^2)y'}{c\omega_0^2}.
$$

若某个非零初态在一个正窗上所有读数为零，解析性令四阶导数读数也为零，与矩阵可逆性矛盾。有限维紧性给出正的窗口 Gram 下界。$\square$

### 推论 7.2（固定非零磁场的短窗最优首项）

定义

$$
a_c(T)=\lambda_{\min}\int_0^T e^{t\Omega_c^T}C^TCe^{t\Omega_c}\,dt.
$$

对每个固定 c≠0，

$$
\boxed{a_c(T)\sim\frac{\omega_0^4c^2}{100800}T^7,
\qquad T\downarrow0.}
$$

**证明。** 令 V 的第 j 行为 CΩc^j/j!，j=0,1,2,3。直接求解 Ve3 得

$$
V^{-1}e_3=(0,-6/(c\omega_0^2),0,0)^T.
$$

时间窗卷定理 8.1 的 Hilbert 矩阵常数为 (H3⁻¹)33=2800，代入其首项公式即得结果。$\square$

这一计算复用已有可观测性首项定理，不以新的包装认领其基础定理。新用途是将有物理输入的磁场参数、传感器与噪声代价置于同一显式实例中。首项是固定 c 的极限，不能将 c 同时趋于无穷代入这一局部展开。

### 定理 7.3（固定窗口存在有限非零最佳磁场幅值）

对任意固定 T>0，a_c(T) 在 c 上连续、对 c≠0 为正，并满足

$$
a_0(T)=0,\qquad
0\le a_c(T)\le
\frac{\omega_0^2T}{\omega_0^2+c^2/4}.
$$

因此 c↦a_c(T) 在 c>0 上取得一个有限非零的全局最大值；不主张最大值唯一。

**证明。** 连续性来自矩阵指数积分和最小特征值连续性。取单位初态 ξ(0)=e3，并令 X=ξ1+iξ2、V=ξ3+iξ4，则 X'=ω0V、V'=−ω0X−icV。解得

$$
X(t)=\frac{\omega_0}{i(\omega_++\omega_-)}
\big(e^{i\omega_-t}-e^{-i\omega_+t}\big).
$$

所以 |ξ1(t)|²≤|X(t)|²≤ω0²/(ω0²+c²/4)，积分给出上界。因 a_c(T) 在 c→0 和 c→∞ 时都趋零，而任意一个 c≠0 处为正，可选一个紧区间包含其全局最大值，再由连续性取得。$\square$

这个结论给出实际设计权衡：磁场把隐藏方向耦合到传感器，但过强磁场又使固定窗口的某些读数幅度过小。磁项对点电荷不做功，不代表它对有限时间的信息传输没有影响。

## 8. 已知参数的状态可观测性与未知磁场的可辨识性

采用第 6 节的 Gibbs 初态，归一化到单位协方差。记标量平稳相关

$$
f_c(t)=C e^{t\Omega_c}C^T.
$$

### 定理 8.1（完整单通道平衡路径对磁场方向失明）

对全部实 t，f_c(t)=f_{−c}(t)。更强地，任意有限组时刻的单通道联合分布，在 c 和 −c 下完全相同。因此仅由这种被动平衡单通道数据，无法辨识带符号磁场；对于等先验的两种符号，任何判别器的平均错误率至少为 1/2。

**证明。** 取 R=diag(1,−1,1,−1)。直接计算得

$$
R\Omega_cR=\Omega_{-c},\quad CR=C,\quad RR^T=I.
$$

反射保留 Gibbs 初态分布，并逐条将一个模型的读数路径变为另一模型的相同路径。也可用零均值 Gaussian 路径的所有协方差相同来证明。两个参数的观测分布一致，等先验判别风险下界直接成立。$\square$

这不与定理 7.1 冲突：该定理是在 c 已知时恢复初态；本定理比较 c 未知且允许相容隐藏初态改变的两个实现。受控、已知的初态或附加交叉读数可以打破这个对称性。

### 推论 8.2（磁幅值进入更深的相关层级）

$$
f_c''(0)=-\omega_0^2,\qquad
f_c^{(4)}(0)=\omega_0^2(\omega_0^2+c^2).
$$

因此单读数的首轮闭包缺陷 M=ω0² 与 c 无关，而四阶相关可在精确数据下恢复

$$
|c|^2=f_c^{(4)}(0)/\omega_0^2-\omega_0^2.
$$

导数闭包维数在 c=0 时依次为 1,2,2,2，在 c≠0 时为 1,2,3,4。

**证明。** 计算 CΩc²Cᵀ、CΩc⁴Cᵀ 和逐层导数矩阵的秩。$\square$

首阶缺陷为非零足以证明需要记忆，但其大小不单独决定完整预测维数。有限精度四阶相关估计也必须重新建立偏差和噪声预算。

### 命题 8.3（交叉相关恢复方向）

令 Qp 选择两个位置分量，则

$$
F_{pp,c}^{(3)}(0)=Q_p\Omega_c^3Q_p^T
=-c\omega_0^2J_2.
$$

令 Qv 选择两个速度分量，则

$$
F_{vv,c}'(0)=cJ_2.
$$

所以定向交叉相关能够区分磁场符号；静态位置密度和全部单通道被动平衡路径都不能替代这一信息。该判断属于本模型的可辨识性结论，不是一般量子测量主张。

## 9. 与机器学习、规范商和既有项目接口的关系

一个电磁学习模型可以将待学习对象设为 Uθ、Aθ、φθ，以及耗散与噪声参数，而后由

$$
B_\theta=\nabla\times A_\theta,\qquad
E_\theta=-\nabla\phi_\theta-\partial_tA_\theta
$$

生成场，借此在光滑局部图内严格保持齐次 Maxwell 约束。源方程、材料定律、边界通量和全局 holonomy 必须另行处理。参数化 A 并不保证任意潜变量模型已经等价于 Maxwell 理论。

第 7–8 节为模型评估提供三个不同任务：已知 c 的初态重建；未知 |c| 的谱或相关估计；未知符号 c 的定向辨识。三者使用不同的观测充分性条件。训练损失不能弥补同一数据模型中的完全不可辨识性。

已有辛预测卷与时间窗卷的形式是常数正定线性系统。恒定 B0 可由对称规范下的线性坐标变换回接该形式，因而可以复用能量范数、预测 Gram、Kubo 相关及误差估计。一般空间变化的 B、非二次势、辐射反作用和材料非线性超出本卷线性可观测性定理。

本轮源码检索中的 `GoldenLorentzUpdate` 使用不定二次型的 Lorentz 命名，不能仅凭同名把它当作这里的电磁力证明。实际承接的是本 PR 的辛预测与相关闭包公式。

## 10. 特斯拉的关系与能量来源

tesla（T）是磁通密度 B 的 SI 单位：1 T=1 Wb/m²=1 N/(A·m)。这属于量纲命名。[NIST]

尼古拉·特斯拉的 US381968A 专利描述由相互独立、适当错相的交流线路产生逐步旋转的磁极，并驱动电机。[Tesla1888] 一个理想两相正交模型为

$$
B(t)=B_0\cos(\nu t)e_x+B_0\sin(\nu t)e_y.
$$

其幅值恒定、方向旋转；这是相位、向量叠加、旋转作用和机电耦合的具体实现。电源给出的功率须与机械功、场能变化和损耗平衡。旋转磁场和共振可以改变传能与响应特征，不提供无输入能量产生机制。

## 11. 可重复算例与验证状态

本卷配套本地脚本执行 74 项检查，包括符号 Jacobi 障碍、能量守恒、规范最小耦合坐标变换、观测行列式与恢复式、磁反射对称、Gaussian 相对熵瞬时导数、速度相关分解及有限窗口界。数值部分的短窗 Gram 使用 75 位十进制精度和块矩阵指数；一般命题由正文证明承担。

在 ω0=1 时，固定非零 c 的短窗核验为：

| c | T | a_c(T) | 与首项 c²T⁷/100800 的比值 |
|---:|---:|---:|---:|
| 0.5 | 0.01 | 2.48015873015348486e-20 | 0.9999999999978851 |
| 1 | 0.01 | 9.92065145494414047e-20 | 1.000001666658369 |
| 2 | 0.01 | 3.96828703703159447e-19 | 1.000008333331962 |

同一归一化下，固定 T=1 的观测强度随磁场变化为：

| c | a_c(1) |
|---:|---:|
| 0 | 0（完整四维状态） |
| 1 | 1.0077265589146574e-5 |
| 8 | 约 1.139e-3 |
| 30 | 9.04140252667726e-5 |
| 100 | 8.308302919629494e-6 |

表中样点不用于认领全局最优数值；有限非零最大值的存在由定理 7.3 证明。已完成的是符号与合成数值核验，未进行硬件测量、机器学习 benchmark、Lean 编译或仓库 CI。外部具名时间窗猜想的纸面证明维持同一 PR 的既有验证层级，本轮不增加已解猜想计数。

## 12. 文献与使用范围

[T-Dyn] David Tong. *Classical Dynamics*, §4.1.3、§4.2.1、§4.3.2. https://www.damtp.cam.ac.uk/user/tong/dynamics/dynhtml/S4.html 。用于带电粒子的 Hamilton 函数、动量 Poisson 括号与经典热平衡的背景。

[T-GR] David Tong. *General Relativity*, §2.4.2. https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S2.html 。用于电磁二形式与外微分背景。

[T-QFT] David Tong. *Quantum Field Theory*, §6.1–6.2. https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S6.html 。用于规范结构、场 Hamilton 形式与量子电磁耦合的背景。

[GEMPIC] M. Kraus, K. Kormann, P. J. Morrison, E. Sonnendrücker. *GEMPIC: Geometric ElectroMagnetic Particle-In-Cell Methods*. Journal of Plasma Physics 83, 905830401, 2017. DOI: 10.1017/S002237781700040X. https://arxiv.org/abs/1609.03053 。用于场粒子 Hamilton 离散化、Jacobi 与散度约束的既有路线。

[AB59] Y. Aharonov, D. Bohm. *Significance of Electromagnetic Potentials in the Quantum Theory*. Physical Review 115, 485–491, 1959. DOI: 10.1103/PhysRev.115.485 。用于局部零场与全局相位效应，不作为本卷的新发现。

[LFO90] X. L. Li, G. W. Ford, R. F. O'Connell. *Charged oscillator in a heat bath in the presence of a magnetic field*. Physical Review A 42, 4519–4527, 1990. DOI: 10.1103/PhysRevA.42.4519 。用于带电受限振子、量子热响应和自由能的既有物理背景。本文可观测性常数由明确矩阵另行计算。

[Bir17] Jeremiah Birrell. *Entropy Anomaly in Langevin-Kramers Dynamics with a Temperature Gradient, Matrix Drag, and Magnetic Field*. https://arxiv.org/abs/1709.06981 。用于带磁场、矩阵摩擦和变温情形的范围区分；本卷只证明恒温有惯性模型的相对熵恒等式。

[NIST] NIST. *Guide to the SI*, Chapter 4, Table 3. https://www.nist.gov/pml/special-publication-811/nist-guide-si-chapter-4-two-classes-si-units-and-si-prefixes 。用于 tesla 单位。

[Tesla1888] Nikola Tesla. *Electro-magnetic motor*, US381968A, granted 1888-05-01. https://patents.google.com/patent/US381968A/en 。用于多相交流与旋转磁场的历史装置原文。
