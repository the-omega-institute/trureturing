# 预测可观测性：短时间窗、有限导数深度与辛结构余量

**版本：** v1.0，2026-09-20。

**证明层级：** 本卷给出纸面证明与可重建算例，尚无本卷配套的 Lean 证明项。命题 6.1 对应一个有明确原文来源的猜想的可逆算子版本；独立审阅、可能的更早控制论蕴含与文献优先权仍待核定。本卷不写入猜想机器结算状态，也不将有限数值检查当作一般 Hilbert 空间证明。

本卷承接 [辛预测完成卷](SYMPLECTIC_PREDICTIVE_COMPLETION.md) 第 4–8 节。该卷构造了目标相对的最小预测状态，本卷进一步求出从有限时间观测恢复这一状态的稳定性、短窗噪声代价，以及近似闭包何时仍必须保留辛配对。

## 0. 外部问题与适用对象

### 0.1 具名问题及假设展开

[AHP19, Theorem 5.5] 考虑复 Hilbert 空间上的有界、可逆、自伴算子 $A$ 和可数观测向量族 $\mathcal G$，证明由 $A^t g$ 生成的半连续帧性质不依赖所选有限正时间窗。紧接其后的原文为：

> Conjecture 5.6. Theorem 5.5 remains true if A is a normal reductive operator.

同一问题在 [ACKM26, Conjecture 2] 再次列出。本文保留所引用定理中的**可逆假设**，并展开目标为：对有界可逆正规 $A$、可数 $\mathcal G$，若存在 $T_0>0$ 和 $0<a_0\le b_0<\infty$ 使

$$
a_0\|x\|^2\le
\sum_{g\in\mathcal G}\int_0^{T_0}|\langle x,A^t g\rangle|^2dt
\le b_0\|x\|^2\qquad(\forall x),
$$

则对每个 $T>0$ 都存在相应正的上下帧界。第 6 节证明这一陈述，而且不使用 reductive 条件。此处 reductive 指每个闭不变子空间也对伴随算子不变。若将原猜想解释为还要删除可逆性，本文不将该更广解释登记为已解。

[AHP19, Definition 2.3] 的幂约定为 $z^t=\exp(t(\ln|z|+i\operatorname{Arg}z))$，$\operatorname{Arg}z\in[-\pi,\pi)$。第 6 节严格使用同一分支。

### 0.2 已有结算及本卷归属

[ACKM26] 的猜想 1 已由 [GP26] 给出反例，猜想 3 已由 [KP26] 给出反例；这两项不列为本卷成果。[DMM21] 已建立一般有界生成元的若干连续与离散采样关系，本卷不把这些既有接口计作新发现。本文的组织目标是把具名问题、有限导数下界、短窗恢复代价与辛预测完成接在同一条证明链上。

一般有界生成元的可观测性属于既有控制论范围。以下证明独立写出所需的量化版本，并明确其常数与假设，不声称一般概念或全部结论首次出现于本卷。

## 1. 观测算子与有限导数深度

令 $X,Y$ 为非零实或复 Hilbert 空间，$B\in\mathcal B(X)$、$C\in\mathcal B(X,Y)$。固定

$$
b=\max(1,\|B\|),\qquad c=\|C\|.
$$

定义时间窗观测算子与最佳下界

$$
(\mathcal T_Tx)(t)=Ce^{tB}x,\qquad
\mathcal T_T:X\to L^2((0,T);Y),
$$

$$
a(T)=\inf_{\|x\|=1}\int_0^T\|Ce^{tB}x\|^2dt.
$$

称 $a(T)>0$ 为该窗上的稳定可观测性。上界自动满足

$$
\|\mathcal T_T\|^2\le c^2\int_0^T e^{2bt}dt.
$$

有限导数映射为

$$
\mathcal J_Nx=(Cx,CBx,\ldots,CB^Nx)\in Y^{N+1},
\qquad
\mu_N=\inf_{\|x\|=1}\sum_{k=0}^N\|CB^kx\|^2.
$$

若某个 $\mu_N>0$，定义稳定导数深度

$$
m=\min\{N\ge0:\mu_N>0\}.
$$

这里要求统一正下界。在无限维空间中，仅有 $\bigcap_{k\ge0}\ker(CB^k)=\{0\}$ 不足以替代这一条件。

## 2. 从一个时间窗到有限导数下界

### 引理 2.1（有界生成元的 Taylor 余量）

设

$$
p_N(t;x)=\sum_{k=0}^N\frac{t^k}{k!}CB^kx.
$$

则对 $T>0$，

$$
\|\mathcal T_Tx-p_N(\cdot;x)\|_{L^2}
\le R_N(T)\|x\|,
$$

$$
R_N(T)=
\frac{c e^{bT}b^{N+1}T^{N+3/2}}
{(N+1)!\sqrt{2N+3}}.
$$

**证明。** 算子范数收敛的指数级数及标量指数余项给出

$$
\left\|Ce^{tB}-\sum_{k=0}^N\frac{t^k}{k!}CB^k\right\|
\le \frac{c e^{bt}(bt)^{N+1}}{(N+1)!}.
$$

平方并在 $[0,T]$ 积分，使用 $e^{bt}\le e^{bT}$ 即得结论。$\square$

### 定理 2.2（观测下界强迫有限稳定深度）

若 $a(T_0)\ge a_0>0$，取任意使

$$
R_N(T_0)\le\tfrac12\sqrt{a_0}
$$

成立的整数 $N$，并定义

$$
M_N(T_0)^2=
\sum_{k=0}^N\frac{T_0^{2k+1}}{(2k+1)(k!)^2}.
$$

则

$$
\boxed{\mu_N\ge\frac{a_0}{4M_N(T_0)^2}>0.}
$$

这样的 $N$ 总存在。

**证明。** 对固定 $T_0$，阶乘增长保证 $R_N(T_0)\to0$。三角不等式给出

$$
\|p_N(\cdot;x)\|_{L^2(0,T_0)}
\ge\tfrac12\sqrt{a_0}\|x\|.
$$

另一方面，对有限和应用 Cauchy–Schwarz，再积分得到

$$
\|p_N(\cdot;x)\|_{L^2(0,T_0)}^2
\le M_N(T_0)^2\sum_{k=0}^N\|CB^kx\|^2.
$$

合并两式即得统一下界。$\square$

本证明不使用有限维紧性、谱分解或正规性。

## 3. 从有限导数下界到任意正时间窗

令 $H_N$ 为 $(N+1)$ 阶 Hilbert 矩阵：

$$
(H_N)_{jk}=\frac1{j+k+1},\quad0\le j,k\le N,
\qquad\lambda_N=\lambda_{\min}(H_N)>0.
$$

正定性由 $v^*H_Nv=\int_0^1|\sum_{k=0}^Nv_ks^k|^2ds$ 得到。

### 定理 3.1（显式短时间窗下界）

假设 $\mu_N\ge\mu>0$。定义

$$
d_N=\frac{\sqrt{\lambda_N\mu}}{N!},\qquad
r_N=\frac{c e^b b^{N+1}}{(N+1)!\sqrt{2N+3}},
$$

$$
\tau_N=\min\left(1,\frac{d_N}{2r_N}\right),
\qquad \alpha_N=\frac{\lambda_N\mu}{4(N!)^2}.
$$

则 $c>0$，上述常数有定义，且

$$
\boxed{a(T)\ge\alpha_N T^{2N+1}
\qquad(0<T\le\tau_N).}
$$

对所有 $T>0$ 还可写成

$$
a(T)\ge\alpha_N\min(T,\tau_N)^{2N+1}>0.
$$

**证明。** 令 $t=Ts$，将 $p_N$ 的系数视为 $Y$ 中的向量。有限 Gram 矩阵的下界同样适用于 $Y$ 值多项式：可在系数的有限维线性跨度中取正交基后逐坐标求和。因此

$$
\int_0^T\|p_N(t;x)\|^2dt
\ge T\lambda_N\sum_{k=0}^N
\frac{T^{2k}}{(k!)^2}\|CB^kx\|^2.
$$

当 $T\le1$ 时，$T^{2k}/(k!)^2\ge T^{2N}/(N!)^2$，故右侧至少为 $d_N^2T^{2N+1}\|x\|^2$。引理 2.1 在这一范围给出余量上界 $r_NT^{N+3/2}\|x\|$。当 $T\le\tau_N$ 时，余量不超过多项式下界的一半，故

$$
\|\mathcal T_Tx\|\ge\tfrac12d_NT^{N+1/2}\|x\|.
$$

平方即得结论；较长窗口使用非负积分的单调性。$\square$

### 推论 3.2（有限窗口、有限导数与所有窗口等价）

对有界 $B,C$，下列三项等价：存在一个有限 $T>0$ 使 $a(T)>0$；存在有限 $N$ 使 $\mu_N>0$；对每个 $T>0$ 都有 $a(T)>0$。

**证明。** 定理 2.2、定理 3.1 及直接的逻辑蕴含给出闭环。$\square$

## 4. 最短稳定深度决定噪声指数

### 定理 4.1（最佳下界的匹配幂次）

若稳定导数深度 $m$ 有限，则存在 $T_*,\alpha,\beta>0$ 使

$$
\boxed{\alpha T^{2m+1}\le a(T)\le\beta T^{2m+1}
\qquad(0<T\le T_*).}
$$

其中下界可取定理 3.1 的常数，且在 $T\le1$ 时上界可取

$$
\beta=\frac{c^2 e^{2b}b^{2m}}{(m!)^2(2m+1)}.
$$

**证明。** 下界已证。若 $m\ge1$，最小性给出 $\mu_{m-1}=0$，故存在单位向量 $x_j$ 使 $\sum_{k<m}\|CB^kx_j\|^2\to0$。固定 $T$，其 $(m-1)$ 阶 Taylor 多项式在 $L^2(0,T;Y)$ 中趋零；引理 2.1 给出

$$
\limsup_j\|\mathcal T_Tx_j\|_{L^2}
\le\frac{c e^b b^mT^{m+1/2}}{m!\sqrt{2m+1}}.
$$

对单位向量取下确界，得到所述上界。$m=0$ 时直接使用 $\|Ce^{tB}\|\le ce^b$ 即可。$\square$

### 推论 4.2（任何重建器的最坏噪声代价）

在 $L^2$ 噪声预算 $\|\eta\|\le\delta$ 下，无先验约束的最坏状态重建误差的最优值为

$$
\boxed{\frac{\delta}{\sqrt{a(T)}}
=\Theta\bigl(\delta T^{-m-1/2}\bigr).}
$$

上式前一等号是所有重建器上的 minimax 值，后一式是 $T\downarrow0$ 的阶。

**证明。** $a(T)>0$ 保证 $\mathcal T_T$ 的像闭，Moore–Penrose 左逆的范数为 $1/\sqrt{a(T)}$，最小二乘重建达到上界。反向取单位 $v$ 使 $\|\mathcal T_Tv\|$ 任意接近 $\sqrt{a(T)}$，令 $h=\delta v/\|\mathcal T_Tv\|$。状态 $h$ 与 $-h$ 配上噪声 $-\mathcal T_Th$ 与 $\mathcal T_Th$ 后产生相同的零数据，任意重建器对二者至少有一个误差不小于 $\|h\|$。取极限得到下界。$\square$

结论针对固定观测模型与全部状态。增加状态先验、改变传感器、延长窗口或改变噪声模型，都属于改变问题条件。

### 定理 4.3（积分矩提供可实现的有限测量）

取 $\ell_0,\ldots,\ell_N$ 为 $L^2(0,1)$ 中次数不超过 $N$ 的正交归一多项式。定义向量积分矩

$$
(\mathcal M_Tx)_k=
\frac1{\sqrt T}\int_0^T\ell_k(t/T)Ce^{tB}x\,dt.
$$

在定理 3.1 的条件和时间范围内，

$$
\sum_{k=0}^N\|(\mathcal M_Tx)_k\|^2
\ge\alpha_NT^{2N+1}\|x\|^2.
$$

同一积分矩作用于噪声时，其总平方范数不超过 $\|\eta\|_{L^2}^2$。

**证明。** $T^{-1/2}\ell_k(t/T)$ 是 $L^2(0,T)$ 中多项式子空间的正交基，所示平方和等于 $\|\Pi_N\mathcal T_Tx\|^2$。因为 $\Pi_Np_N=p_N$ 且投影收缩，

$$
\|\Pi_N\mathcal T_Tx\|
\ge\|p_N\|-\|\mathcal T_Tx-p_N\|.
$$

代入定理 3.1 的两个界即得结论；噪声部分由 Bessel 不等式。$\square$

因此导数深度可用来选择有限积分矩阶数，无须对带噪数据直接做高阶数值微分。有限维时可预计算矩阵 $\mathcal M_T$ 并做加权最小二乘；离散求积误差须另行计入噪声预算。

## 5. 初始观测族的 Bessel 性不必额外假设

### 引理 5.1（积分上界推出初始 Bessel 上界）

令 $B\in\mathcal B(X)$，$\mathcal G=(g_j)_{j\in J}$ 为可数向量族。假设

$$
\sum_j\int_0^{T_0}|\langle e^{tB}x,g_j\rangle|^2dt
\le M_0\|x\|^2.
$$

取 $b=\max(1,\|B\|)$、$d=\min(T_0,\log(3/2)/b)$，则

$$
\boxed{\sum_j|\langle x,g_j\rangle|^2
\le\frac{4M_0}{d}\|x\|^2.}
$$

**证明。** 对任意有限 $F\subset J$，令 $C_Fx=(\langle x,g_j\rangle)_{j\in F}$，以及常值轨迹算子 $S_Fx(t)=C_Fx$、动态轨迹算子 $T_Fx(t)=C_Fe^{tB}x$，二者限制于 $[0,d]$。有

$$
\|S_F\|=\sqrt d\|C_F\|,\qquad
\|T_F-S_F\|\le\tfrac12\sqrt d\|C_F\|,
$$

因为 $\|e^{tB}-I\|\le e^{bt}-1\le1/2$。积分上界给出 $\|T_F\|\le\sqrt{M_0}$，因此 $\sqrt d\|C_F\|/2\le\sqrt{M_0}$。对有限集递增取极限得结论。$\square$

此引理避免先把可能无界的分析映射当作有界算子使用。

## 6. 具名猜想的可逆正规算子版本

### 定理 6.1（有限时间窗不变性的强化版本）

设 $A\in\mathcal B(X)$ 正规且有有界逆，$\mathcal G$ 可数；按第 0 节的固定分支定义 $A^t$。则 $\{A^tg:g\in\mathcal G,0\le t\le T_0\}$ 在某个有限正窗上为半连续帧，当且仅当它在每个有限正窗上为半连续帧。

**证明。** 记 $E_A$ 为 $A$ 的投影值谱测度。其谱位于紧环带

$$
\|A^{-1}\|^{-1}\le|z|\le\|A\|.
$$

有界 Borel 函数

$$
q(z)=\ln|z|+i\operatorname{Arg}z
$$

给出有界正规算子 $Q=q(A)$。谱积分的乘法演算与一致收敛的指数级数给出

$$
e^{tQ}=A^t.
$$

此处使用有界 Borel 演算，不要求在整个谱邻域存在连续或全纯对数。

设 $[0,T_0]$ 上的帧上下界为 $a_0,M_0$。对所有 $x,g$，

$$
\langle x,A^tg\rangle=\langle e^{tQ^*}x,g\rangle.
$$

由引理 5.1，$Cx=(\langle x,g\rangle)_{g\in\mathcal G}$ 定义有界映射 $C:X\to\ell^2(\mathcal G)$。以 $B=Q^*$ 应用定理 2.2 和定理 3.1，得到每个 $T>0$ 的正下界；上界由第 1 节得到。反向蕴含直接成立。$\square$

证明没有使用 reductive 条件。它给出 [AHP19, Conjecture 5.6] 与 [ACKM26, Conjecture 2] 在保留所引用定理的可逆前件时的纸面解答。本文不把一般控制论的可能更早蕴含排除在外，也不将文献检索未命中等同于优先权证明。

**分支说明。** 证明只使用 $(e^{tQ})^*=e^{tQ^*}$。在负实谱点，不应自动把 $Q^*$ 换成用同一主值分支计算的 $\log(A^*)$；例如 $A=-I$ 时两者分别是 $i\pi I$ 与 $-i\pi I$。这不会影响上面的分析映射转换。

**未覆盖范围。** 若 $A$ 只有单射性而没有有界逆，$q(A)$ 可能无界，第 2–3 节的算子范数 Taylor 估计不能原样使用。本文没有删除这个前件。

## 7. 从精确辛闭包到可认证的近似辛闭包

沿用辛预测完成卷的有限维记号：$S=S^T\succ0$、$J$ 标准 Poisson 矩阵、$A=JS$，$O$ 满行秩。此处不要求 $OA$ 已在 $O$ 的行空间中闭合。令

$$
P=OS^{-1}O^T,\quad J_r=OJO^T,\quad K=J_rP^{-1},
$$

$$
\epsilon=\|P^{-1/2}(OA-KO)S^{-1/2}\|_2.
$$

再定义能量归一坐标中的矩阵

$$
\Omega=S^{1/2}JS^{1/2},\quad
Q=P^{-1/2}OS^{-1/2},\quad
D=Q\Omega Q^T=P^{-1/2}J_rP^{-1/2},
$$

以及 $\omega_*=\sigma_{\min}(\Omega)>0$。$\Omega$ 实反对称，故 $\omega_*$ 是正定二次系统的最小模态频率。

### 定理 7.1（辛非退化性的定量余量）

如果 $\epsilon<\omega_*$，则

$$
\boxed{\sigma_{\min}(D)\ge\sqrt{\omega_*^2-\epsilon^2}>0.}
$$

因此约化 Poisson 配对非退化，潜状态维数为偶数。对任意奇数维满行秩 $O$，必有

$$
\boxed{\epsilon\ge\omega_*.}
$$

**证明。** $QQ^T=I$，所以 $\Pi=Q^TQ$ 为正交投影。直接计算有

$$
\epsilon=\|Q\Omega-DQ\|_2
=\|Q\Omega(I-\Pi)\|_2
=\|(I-\Pi)\Omega Q^T\|_2,
$$

最后一步使用反对称性。对单位向量 $v$，正交分解给出

$$
\|\Omega Q^Tv\|^2
=\|Dv\|^2+\|(I-\Pi)\Omega Q^Tv\|^2.
$$

左侧至少为 $\omega_*^2$，第二项至多为 $\epsilon^2$，得到所述下界。若行数为奇数，反对称 $D$ 必奇异；取其核中的单位向量，反向得到 $\epsilon\ge\omega_*$。$\square$

### 例 7.2（界的精确达到）

在四维坐标 $(q_1,q_2,p_1,p_2)$ 中取 $S=I_4$，并令

$$
Q=\begin{pmatrix}1&0&0&0\\0&4/5&3/5&0\end{pmatrix}.
$$

则 $QQ^T=I_2$、$\omega_*=1$，且

$$
D^TD=\tfrac9{25}I_2,\qquad
(QJ-DQ)(QJ-DQ)^T=\tfrac{16}{25}I_2.
$$

所以 $\sigma_{\min}(D)=3/5$、$\epsilon=4/5$，定理 7.1 等号成立。只保留 $Q=(1,0,0,0)$ 时，$D=0$、$\epsilon=1$，奇数维下界也达到。

该判据与辛预测完成卷第 8 节共用同一个 $\epsilon$：它既控制预测轨迹误差，也在足够小时认证潜空间没有丢失全部共轭配对。证明不要求学习算法显式采用辛参数化。

## 8. 有限维标量观测的精确短窗首项

### 定理 8.1（满导数矩阵的首项常数）

令 $X=\mathbb C^d$ 或 $\mathbb R^d$、$Y$ 为标量，$m=d-1$，并假设矩阵

$$
V=\begin{pmatrix}
C\\CB\\CB^2/2!\\\vdots\\CB^m/m!
\end{pmatrix}
$$

可逆。则

$$
\boxed{\lim_{T\downarrow0}\frac{a(T)}{T^{2m+1}}
=\frac1{(H_m^{-1})_{mm}\|V^{-1}e_m\|^2}.}
$$

**证明。** 令 $D_T=\operatorname{diag}(1,T,\ldots,T^m)$，定义标量行函数

$$
w_T(s)=Ce^{TsB}V^{-1}D_T^{-1}.
$$

Taylor 展开在 $s\in[0,1]$ 上一致给出 $w_T(s)=(1,s,\ldots,s^m)+O(T)$：余项的第 $k$ 个分量为 $O(T^{m+1-k})$。因此

$$
H(T)=\int_0^1w_T(s)^*w_T(s)ds\longrightarrow H_m\succ0.
$$

观测 Gram 矩阵为

$$
G(T)=\int_0^T e^{tB^*}C^*Ce^{tB}dt
=T V^*D_TH(T)D_TV.
$$

所以

$$
T^{2m+1}G(T)^{-1}
\longrightarrow
(H_m^{-1})_{mm}(V^{-1}e_m)(V^{-1}e_m)^*.
$$

极限右侧只有一个非零特征值。取最大特征值并使用 $a(T)=1/\lambda_{\max}(G(T)^{-1})$，得到结论。$\square$

### 例 8.2（两个振子与传感器数量）

取坐标 $(q_1,p_1,q_2,p_2)$，

$$
B=\operatorname{diag}(J_2,2J_2),\quad
J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

这是正定 Hamilton 函数 $(q_1^2+p_1^2+2q_2^2+2p_2^2)/2$ 的流。

只观测合成位置 $C=(1,0,1,0)$ 时，导数矩阵逐层秩为 $1,2,3,4$，故 $m=3$。直接求逆得到

$$
(H_3^{-1})_{33}=2800,\qquad
V^{-1}e_3=(0,2,0,-1)^T.
$$

因此

$$
a(T)\sim\frac{T^7}{14000},\qquad
\|\mathcal T_T^\dagger\|\sim\sqrt{14000}\,T^{-7/2}.
$$

改为分别观测 $q_1,q_2$，则 $m=1$，两个模态的 Gram 矩阵分块。频率 $\omega$ 的最小特征值为

$$
\frac12\left(T-\frac{|\sin(\omega T)|}{\omega}\right).
$$

取两块的最小值，得到 $a(T)\sim T^3/12$。这是传感器改变恢复幂次的显式实例，而非只改变常数。

**数值核验。** 以 90 位十进制精度计算同一精确 Gram 积分，得到：

| 观测 | $T$ | $a(T)$ | $1/\sqrt{a(T)}$ |
|---|---:|---:|---:|
| 合成位置 | 0.1 | $7.14507890954\times10^{-12}$ | $3.74107560621\times10^5$ |
| 合成位置 | 0.01 | $7.14287936503\times10^{-19}$ | $1.18321411607\times10^9$ |
| 分别测位置 | 0.1 | $8.32916765859\times10^{-5}$ | $1.09571901378\times10^2$ |
| 分别测位置 | 0.01 | $8.33329166677\times10^{-8}$ | $3.46411027540\times10^3$ |

所有读数使用固定的欧氏状态范数、固定传感器增益和 $L^2$ 噪声预算。时间是按给定频率归一化后的数值。改变采样密度、噪声协方差或单位时应重算相应的加权 Gram 矩阵。

该算例以及引理 2.1、定理 3.1 的有限维下界、定理 7.1 的有理等号实例与主值分支伴随转换共通过 12 项局部检查。一般定理由各节证明承担。

## 9. 量子、机器学习与可测系统的共同接口

在辛预测完成卷的最小预测商 $y=Oz$ 上，原始读数具有形式 $b=Dy$、$\dot y=Ky$。本卷应用于 $B=K,C=D$，求得的是目标预测状态的恢复代价；若完整状态中仍有不可见模式，不能对完整状态错误地宣称 $a(T)>0$。

该卷第 7 节的量子线性观测满足相同的 $\partial_t\widehat y=K\widehat y$。对有限一阶矩向量，其时间窗分析使用同一个矩阵 Gram；有限矩阵量子系统也可以在 Hermitian 算子的实 Hilbert 空间上，以交换子作为有界生成元应用本卷。真实测量仍须给出重复制备、噪声协方差及扰动模型；这里不把量子态的完整恢复缩减成一阶矩恢复。

对于学习得到的线性潜动力学，可分别计算稳定导数深度 $m$、窗口下界 $a(T)$ 和闭包误差 $\epsilon$。这三项分别回答：需要多少阶未来信息、在给定噪声下能恢复多准确，以及压缩是否已损坏共轭结构。积分矩定理给出无需数值求导的实现接口，最坏噪声下界则适用于同一数据模型上的所有重建算法。

例 8.2 可以由两个校准后的振荡模态实现，例如机械模态或线性 LC 模态。数学预测是：在固定噪声度量下，分别测量与只测合成输出会呈现不同的短窗指数。本文已有的是可重建的合成算例与证明，尚无硬件实验或机器学习 benchmark 结果。

## 10. 无界生成元的反例与进一步义务

### 反例 10.1（正的最小观测时间）

令 $X=L^2(\mathbb R/2\mathbb Z)$，$U_tf(s)=f(s+t)$，$C$ 为区间 $[0,1]$ 的指示函数乘法。$U_t$ 是强连续酉群，其微分生成元无界。Fubini 换元给出

$$
\int_0^2\|CU_tf\|^2dt=\|f\|^2.
$$

但对 $0<T<1$，取非零 $f$ 支撑于 $(1+T,2)$，则 $CU_tf=0$ 对全部 $t\in[0,T]$ 成立。所以 $a(2)=1$，而 $a(T)=0$ 对 $0<T<1$ 成立。

**证明。** 一个完整周期中，每个点恰被观测区间覆盖长度为 1 的时间，得到第一式；短窗内被扫描的空间集合包含于 $[0,1+T]$，得到第二式。$\square$

因此不能仅凭酉性把有界生成元结论推广到任意场论或输运方程。仍需独立处理的义务包括：不可逆正规 $A$ 的无界对数、非线性预测完成的稳定深度，以及有限样本下从估计矩阵认证 $a(T)$ 和 $\epsilon$ 的联合误差。

## 11. 参考文献

[AHP19] A. Aldroubi, L. X. Huang, A. Petrosyan. *Frames induced by the action of continuous powers of an operator*. Journal of Mathematical Analysis and Applications 478(2), 1059–1084, 2019. DOI: [10.1016/j.jmaa.2019.05.066](https://doi.org/10.1016/j.jmaa.2019.05.066). [arXiv:1801.10103](https://arxiv.org/abs/1801.10103). 使用 Definition 2.3、Theorem 5.5 与 Conjecture 5.6，原 PDF 印刷页 18 的猜想及前件已逐字核对。

[ACKM26] A. Aldroubi, C. Cabrelli, I. Krishtal, U. Molter. *Dynamical Sampling: A Survey*. La Matematica 5, Article 37, 2026. DOI: [10.1007/s44007-026-00215-y](https://doi.org/10.1007/s44007-026-00215-y). [arXiv:2511.10769v3](https://arxiv.org/abs/2511.10769v3). 使用 Theorem 2.13 与 Conjecture 2；该综述的其他猜想需与其后的结算论文分别核对。

[DMM21] R. Díaz Martín, I. Medri, U. Molter. *Continuous and discrete dynamical sampling*. Journal of Mathematical Analysis and Applications 499(2), 125060, 2021. DOI: [10.1016/j.jmaa.2021.125060](https://doi.org/10.1016/j.jmaa.2021.125060). [arXiv:2006.08046](https://arxiv.org/abs/2006.08046). 使用一般有界生成元与连续/离散帧的既有背景；Theorem 3.1 的有限时间离散化和后续无限窗结果不列为本卷成果。

[GP26] E. A. Gallardo-Gutiérrez, J. R. Partington. *Frame constructions associated with operator orbits*. [arXiv:2605.29671](https://arxiv.org/abs/2605.29671), submitted 2026-05-28. 给出 [ACKM26] 中 Carleson 采样猜想的反例。

[KP26] I. A. Krishtal, G. E. Pfander. *The normalized orbit of a bounded normal operator can be a frame*. [arXiv:2606.20848](https://arxiv.org/abs/2606.20848), submitted 2026-06-18. 反驳 [ACKM26, Conjecture 3]。

[KM26] I. A. Krishtal, B. Miller. *Block Diagonal Carleson Frames*. [arXiv:2607.18491v1](https://arxiv.org/abs/2607.18491v1), 2026. §5 进一步区分 Müntz 条件、完备性与稳定帧。本卷没有复用这些已有反例来认领新的外部猜想结算。
