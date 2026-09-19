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

## 12. 平衡相关矩阵给出的可观测闭包证书

**增订范围（2026-09-20）。** 第 12–20 节补上第 10 节的部分数据认证义务：在有限维正定二次系统、线性读数与指定平衡分布下，从相关矩阵及其误差预算认证隐藏耦合、预测下限和额外状态维数。新增内容为纸面证明及合成验证，尚无配套 Lean，不新增外部猜想结算。第 6 节留下的不可逆正规算子义务已由同一 PR 的 [正规连续幂时间窗卷](NORMAL_POWER_FRAME_TIME_INVARIANCE.md) 单独处理，本节不改变其验证层级。

固定 $A=JS$、$S=S^T\succ0$，令 $\vartheta=\beta^{-1}>0$。取随机初态

$$
z_0\sim N(0,\vartheta S^{-1}),\qquad z_t=e^{At}z_0,
\qquad y_t=Oz_t,
$$

其中 $O$ 满行秩、行数为 $r$。这是 Gibbs 初态下的封闭线性 Hamilton 演化；$AS^{-1}+S^{-1}A^T=0$ 保证平稳性。它不要求或推出单条轨迹的遍历性。

设

$$
C(t)=\mathbb E[y_ty_0^T],\qquad
F(t)=C(0)^{-1/2}C(t)C(0)^{-1/2}.
$$

沿用第 7 节的 $P,Q,\Omega,D$，直接得到

$$
C(t)=\vartheta Oe^{At}S^{-1}O^T,\quad
F(t)=Qe^{t\Omega}Q^T,\quad QQ^T=I_r,\quad\Omega^T=-\Omega.
$$

因而 $F(0)=I_r$、$F(-t)=F(t)^T$、$\|F(t)\|_2\le1$。归一化消去了温度尺度；温度与热分布的指定仍是模型假设。

### 定理 12.1（相关曲率等于隐藏耦合 Gram 矩阵）

令 $\Pi=Q^TQ$，则

$$
\boxed{M:=F'(0)^2-F''(0)
=\big((I-\Pi)\Omega Q^T\big)^T
 \big((I-\Pi)\Omega Q^T\big)\succeq0.}
$$

它与第 7 节使用的闭包残差满足 $\epsilon^2=\|M\|_2$。特别地，$M=0$ 当且仅当 $OA=KO$。用未归一化读数也可写成

$$
M=C(0)^{-1/2}
\big[C'(0)C(0)^{-1}C'(0)-C''(0)\big]C(0)^{-1/2}.
$$

**证明。** $F'(0)=D=Q\Omega Q^T$，$F''(0)=Q\Omega^2Q^T$。展开右侧 Gram 矩阵，使用 $\Omega^T=-\Omega$ 得 $D^2-Q\Omega^2Q^T$。其算子范数是隐藏耦合范数的平方；第 7 节已经将该范数等同于 $\epsilon$。Gram 为零等价于 $(I-\Pi)\Omega Q^T=0$，转置即 $Q\Omega=DQ$，转换坐标得到 $OA=KO$。最后一式将归一化矩阵代回。$\square$

这个证书使用相同读数的零、一、二阶相关信息，不需要先辨识完整的 $A,S$。只有下一节的有限延迟偏差界还需要带宽上界。$M\succeq0$ 是模型蕴含的必要条件；估计矩阵出现显著负特征值时，应检查误差预算或模型假设。

## 13. 同一个矩阵同时控制记忆和热涨落

选择 $V$ 使 $\binom QV$ 为正交矩阵。令 $\xi_0=\vartheta^{-1/2}S^{1/2}z_0\sim N(0,I)$，$u=Q\xi$、$v=V\xi$，并记

$$
B_h=V\Omega Q^T,\qquad E_h=V\Omega V^T.
$$

则 $u=C(0)^{-1/2}y$，且

$$
\dot u=Du-B_h^Tv,\qquad \dot v=B_hu+E_hv.
$$

### 定理 13.1（精确记忆方程与相关动力学）

消去 $v$ 得

$$
\dot u(t)=Du(t)-\int_0^t\Lambda(t-s)u(s)\,ds+\eta(t),
$$

$$
\Lambda(t)=B_h^Te^{tE_h}B_h,\qquad
\eta(t)=-B_h^Te^{tE_h}v_0.
$$

初态 $u_0,v_0$ 独立，且

$$
\mathbb E[\eta(t)\eta(s)^T]=\Lambda(t-s),\quad
\Lambda(0)=M,\quad\|\Lambda(t)\|_2\le\|M\|_2.
$$

相关矩阵满足

$$
F'(t)=DF(t)-\int_0^t\Lambda(t-s)F(s)\,ds.
$$

**证明。** 第二个状态方程的变参数公式代入第一个即得记忆式。独立标准高斯初态给出噪声协方差；$E_h$ 反对称，所以其指数正交。由 $V^TV=I-\Pi$，有 $B_h^TB_h=M$。最后将记忆方程右乘 $u_0^T$ 并取期望，独立性令噪声交叉项消失。$\square$

这是 Mori 投影和涨落耗散关系在当前载体上的精确实现 [M65, M65C]。有限封闭系统的 $\Lambda$ 可以振荡且不衰减，此处没有认领不可逆热浴极限。

### 推论 13.2（当前状态条件均值的二阶偏差界）

$$
\boxed{\|F(t)-e^{tD}\|_2\le\tfrac12t^2\|M\|_2,
\qquad t\ge0.}
$$

**证明。** 对相关方程再用变参数公式，使用 $\|e^{tD}\|=1$、$\|F(s)\|\le1$ 和上一节的记忆核界，在三角形 $0\le s\le\tau\le t$ 上积分。$\square$

这个 $O(\epsilon^2t^2)$ 结论针对条件均值。它不替换辛预测完成卷中针对任意隐藏初态的 $O(\epsilon t)$ 轨迹界。

## 14. 所有只读当前状态的预测器共有的误差下限

### 定理 14.1（Gaussian 条件预测及其正交分解）

在第 12 节模型下，对任意固定 $t$，

$$
\mathbb E[u_t\mid u_0]=F(t)u_0,\qquad
\operatorname{Cov}(u_t\mid u_0)=G(t):=I_r-F(t)F(t)^T.
$$

对任意可测且平方可积的预测器 $f:\mathbb R^r\to\mathbb R^r$，

$$
\boxed{\mathbb E\|u_t-f(u_0)\|^2
=\operatorname{tr}G(t)+\mathbb E\|F(t)u_0-f(u_0)\|^2.}
$$

因此全部此类预测器的最小均方误差恰为 $\operatorname{tr}G(t)$。有

$$
G(t)=Qe^{t\Omega}(I-\Pi)e^{-t\Omega}Q^T,
\qquad G(t)=t^2M+O(t^3),
$$

$$
\operatorname{tr}G(t)=t^2\operatorname{tr}M+O(t^4).
$$

**证明。** 分解 $\xi_0=Q^Tu_0+V^Tv_0$，其中两个高斯部分独立。代入 $u_t=Qe^{t\Omega}\xi_0$ 即得条件均值、协方差及其 Gram 表达。预测误差与当前状态的任意平方可积函数正交，展开平方得恒等式。Taylor 展开得矩阵首项。迹等于 $r-\|F(t)\|_F^2$，由 $F(-t)=F(t)^T$ 知其为偶函数，故迹余项从四阶开始。$\square$

定理涵盖只使用当前读数的任意非线性网络；历史、附加传感器或其他关于同一隐藏初态的信息会改变条件化对象。此处是 Gibbs 先验下的 Bayes 下限，与第 4 节无状态先验的最坏噪声下限分别记账。

## 15. 从相关矩阵识别必须补回的状态维数

### 定理 15.1（相关导数 Gram 塔）

定义块矩阵

$$
\mathcal H_m=\big[(-1)^i F^{(i+j)}(0)\big]_{i,j=0}^m.
$$

则

$$
\mathcal H_m=\mathcal K_m^T\mathcal K_m,\qquad
\mathcal K_m=[Q^T,\Omega Q^T,\ldots,\Omega^mQ^T].
$$

其秩等于截至 $m$ 阶的线性预测闭包维数，稳定后的秩等于完整的最小预测维数。特别地，

$$
\boxed{\operatorname{rank}\mathcal H_1=r+\operatorname{rank}M.}
$$

**证明。** 第 $(i,j)$ 个 Gram 块为 $(\Omega^iQ^T)^T\Omega^jQ^T=(-1)^iF^{(i+j)}(0)$。生成向量的跨度与连续预测闭包仅相差可逆能量坐标变换。对

$$
\mathcal H_1=\begin{pmatrix}I_r&D\\-D&-F''(0)\end{pmatrix}
$$

消去首块后，其 Schur 补为 $-F''(0)+D^2=M$，得到秩公式。有限维的稳定性由 Cayley–Hamilton 保证。$\square$

$\operatorname{rank}M$ 给出第一轮至少要补回的独立方向数，它可能小于最终所需数。精确秩结论不直接适用于有限精度数据；后文以特征值余量给出可认证下界。

## 16. 单个有限延迟的证书和最优误差阶

假设已知 $\|\Omega\|_2\le b$，其中 $b>0$。对 $h>0$，定义无需数值求导的双向延迟矩阵

$$
W_h=\frac{2I_r-F(h)F(h)^T-F(h)^TF(h)}{2h^2}.
$$

### 定理 16.1（有限延迟与相关误差的联合预算）

$W_h\succeq0$，且

$$
\|W_h-M\|_2\le\tfrac23b^4h^2.
$$

若 $\|\widehat F_h-F(h)\|_2\le\delta$，将 $\widehat F_h$ 代入同一公式得到 $\widehat W_h$，则

$$
\boxed{\|\widehat W_h-M\|_2\le
\eta(h,\delta):=\tfrac23b^4h^2+\frac{2\delta+\delta^2}{h^2}.}
$$

因此 $\widehat W_h$ 中大于 $\eta$ 的特征值个数，是 $\operatorname{rank}M$ 的可靠下界。

**证明。** $F$ 收缩给出半正定性。令 $P_t=F(t)F(t)^T$。$P''_0=-2M$，并由 $\|F^{(k)}(t)\|\le b^k$ 和 Leibniz 公式得 $\|P^{(4)}_t\|\le16b^4$。双向 Taylor 展开的四阶余项给出 $16b^4h^2/24$。相关误差造成每个乘积至多 $2\delta+\delta^2$ 的扰动，代入定义即得界。最后用对称矩阵特征值扰动界；它也可直接由 Rayleigh 商的最大最小表述证明。$\square$

对固定 $\delta>0$，该上界在

$$
h_*^4=\frac{3(2\delta+\delta^2)}{2b^4}
$$

处最小，最小值为 $2b^2\sqrt{2(2\delta+\delta^2)/3}$。延迟太小会放大误差，延迟太大则增大截断偏差。带宽条件不可省：单振子在 $\omega h=2\pi$ 时有 $F(h)=1$、$W_h=0$，但 $M=\omega^2>0$。

### 定理 16.2（单延迟数据模型中的匹配 minimax 阶）

限制到标量读数、已知 $F(0)=1$、频率位于 $[1,3]$ 的有限正定 Hamilton 系统，数据只包含一个 $d$，且 $|d-F(h)|\le\delta$。对于充分小的固定 $h_0>0$，允许选择一次延迟 $0<h\le h_0$。从这一数据估计 $M=-F''(0)$ 的最优最坏绝对误差满足

$$
\boxed{\inf_{0<h\le h_0}\inf_{\widehat M}
\sup_{F,\ |d-F(h)|\le\delta}|\widehat M(d)-M(F)|
=\Theta(\sqrt\delta),\qquad\delta\downarrow0.}
$$

**证明。** 上界由定理 16.1 取 $b=3$、$h\asymp\delta^{1/4}$ 得到。下界使用两组成对实现。

第一组取 $F_a(t)=\cos(2t)$，以及

$$
F_b(t)=(1-p_h)\cos t+p_h\cos(3t),\qquad
p_h=\frac{\cos h-\cos(2h)}{\cos h-\cos(3h)}.
$$

充分小 $h$ 时 $0<p_h<1$，且 $F_a(h)=F_b(h)$；二者均由正定振子及归一化线性读数实现。其曲率差为

$$
M_b-M_a=1+8p_h-4=\tfrac54h^2+O(h^4).
$$

故即使零噪声，单延迟数据也留下至少 $c_1h^2$ 的最坏误差。第二组在 $0<\delta\le h^2$ 时取

$$
F_x(t)=\cos(\sqrt{x}\,t),\quad x_0=4,\quad x_1=4+4\delta/h^2.
$$

因 $|\partial_x\cos(\sqrt{x}\,h)|\le h^2/2$，两个数据相差至多 $2\delta$，同一个中点数据与二者相容，曲率差为 $4\delta/h^2$。最坏估计误差至少为 $2\delta/h^2$。$\delta>h^2$ 时改取 $x_1=8$，同理得到常数下界 2。结合两个下界，在 $\delta\le h^2$ 时用 $\max(c_1h^2,2\delta/h^2)\ge\sqrt{2c_1\delta}$；另一情形更强。$\square$

这是一个延迟相关值及有界加性误差的信息模型。多延迟、完整轨迹、额外谱先验或其他测量可以改变最优阶；本定理不把 $\sqrt\delta$ 宣称为所有实验设计的共同下限。

## 17. 协方差白化误差与一个有限样本保证

### 定理 17.1（经验白化的正交对齐预算）

设 $C_0=C(0)\succ0$，估计量满足

$$
\|C_0^{-1/2}(\widehat C_0-C_0)C_0^{-1/2}\|\le\rho<1,
\quad
\|C_0^{-1/2}(\widehat C_h-C(h))C_0^{-1/2}\|\le\nu.
$$

则 $\widehat C_0\succ0$，存在正交 $U$，使经验归一化相关矩阵满足

$$
\boxed{\left\|U^T\widehat C_0^{-1/2}\widehat C_h
\widehat C_0^{-1/2}U-F(h)\right\|
\le\frac{\rho+\nu}{1-\rho}.}
$$

**证明。** 写 $E_0=C_0^{-1/2}(\widehat C_0-C_0)C_0^{-1/2}$。对 $L=\widehat C_0^{-1/2}C_0^{1/2}$ 作右极分解 $L=UR$，其中 $R=(I+E_0)^{-1/2}$。对齐后的估计为 $R(F(h)+E_h)R$，$\|E_h\|\le\nu$。谱界给出 $\|R\|\le(1-\rho)^{-1/2}$、$\|R-I\|\le(1-\rho)^{-1/2}-1$。用 $\|F(h)\|\le1$ 展开扰动，得到 $\nu/(1-\rho)+\rho/(1-\rho)$。$\square$

第 16 节的特征值与范数证书对正交变换不变，所以不需要从数据额外恢复 $U$。已知绝对协方差误差及 $\lambda_{\min}(C_0)$ 的正下界时，可直接换算 $\rho,\nu$。

### 推论 17.2（独立 Gibbs 配对样本的保守置信预算）

从 $N$ 次独立初态制备得到配对样本 $(y_0^{(j)},y_h^{(j)})$，均值按已知的零均值处理，以未中心化样本二阶矩估计 $C_0,C_h$。取 $0<\alpha<1$，定义

$$
\kappa=2\sqrt{\frac{r(r+1)}{N\alpha}}.
$$

若 $\kappa<1$，则以至少 $1-\alpha$ 的概率，定理 17.1 同时适用 $\rho=\nu=\kappa$，并可向第 16 节输入

$$
\delta_N=\frac{2\kappa}{1-\kappa}.
$$

**证明。** 真白化后的配对向量具有 Gaussian 协方差

$$
\Gamma=\begin{pmatrix}I_r&F(h)^T\\F(h)&I_r\end{pmatrix},
\quad\|\Gamma\|\le2,\quad\operatorname{tr}\Gamma=2r.
$$

Gaussian 四阶矩展开给出样本协方差 $\widehat\Gamma$ 的恒等式

$$
\mathbb E\|\widehat\Gamma-\Gamma\|_F^2
=\frac{(\operatorname{tr}\Gamma)^2+\operatorname{tr}(\Gamma^2)}N
\le\frac{4r(r+1)}N.
$$

Markov 不等式与 $\|\cdot\|_2\le\|\cdot\|_F$ 给出失败概率至多 $\alpha$；提取各子块得到两个相对误差预算。$\square$

这是保守的充分样本界，不认领最优样本复杂度。固定 $r,\alpha$ 时，它与第 16 节组合给出 $h\asymp N^{-1/8}$、曲率证书半径 $O(N^{-1/4})$。一条封闭振子轨迹上的相邻时刻不构成这里的独立样本；传感器噪声、未知均值或相关采样需要单独的估计预算。

## 18. 从数据证书传播到预测与辛结构

令 $\widehat D_h=(\widehat F_h-\widehat F_h^T)/(2h)$，并取

$$
\gamma=\tfrac16b^3h^2+\delta/h,
\qquad M_+=\max\{0,\lambda_{\max}(\widehat W_h)+\eta(h,\delta)\}.
$$

### 定理 18.1（可计算的模型误差界）

在与真坐标正交对齐后，

$$
\|\widehat D_h-D\|\le\gamma,\quad\|M\|\le M_+,
$$

$$
\boxed{\|F(t)-e^{t\widehat D_h}\|\le\tfrac12M_+t^2+\gamma t.}
$$

其预测均方误差满足

$$
\mathbb E\|u_t-e^{t\widehat D_h}u_0\|^2
\le\operatorname{tr}G(t)
+r\bigl(\tfrac12M_+t^2+\gamma t\bigr)^2.
$$

若 $\sigma_{\min}(\widehat D_h)>\gamma$，则 $D$、进而 $J_r$ 非退化。若另有原系统最低频率下界 $\omega_*>0$ 且 $M_+<\omega_*^2$，第 7 节进一步给出 $\sigma_{\min}(D)\ge\sqrt{\omega_*^2-M_+}$。

**证明。** 中心一阶差分的余项由 $\sup_t\|F'''(t)\|\le b^3$ 控制，给出 $b^3h^2/6$；数据误差贡献至多 $\delta/h$。$D,\widehat D_h$ 都反对称，Duhamel 公式给出两个正交流的差至多 $t\gamma$。与推论 13.2 合并，再用定理 14.1 及 Frobenius 范数至多 $\sqrt r$ 倍算子范数，得到预测界。最后由奇异值扰动及定理 7.1 得结构证书。$\square$

这些结论给出相同实现下的联合链：样本协方差误差、经验白化误差、隐藏耦合余量、预测均值误差和辛非退化性。有限误差证书可以证明非零缺陷或给出上界，不能从近零读数证明精确闭合。

## 19. 量子热响应中保持同一几何的相关量

考虑有限个正则量子模式，$\widehat H=\widehat z^TS\widehat z/2$、$S\succ0$，采用 Weyl 对称排序与通常 Schrödinger 表示。Gibbs 态为 $\rho_\beta$，定义线性读数的 Kubo 相关矩阵

$$
C^K_{ij}(t)=\frac1\beta\int_0^\beta
\operatorname{Tr}\big[\rho_\beta e^{s\widehat H}
\widehat y_i(t)e^{-s\widehat H}\widehat y_j\big]ds.
$$

### 定理 19.1（二次量子 Gibbs 系统的共同相关矩阵）

$$
\boxed{C^K(t)=\beta^{-1}Oe^{At}S^{-1}O^T.}
$$

因此其归一化相关矩阵也是 $Qe^{t\Omega}Q^T$。第 12、15、16 节的矩阵恒等式和确定性误差证书使用同一组对象。

**证明。** 对 $\widehat H_f=\widehat H-f^T\widehat z$ 作 Weyl 位移完成平方，得到

$$
Z(f)=Z(0)\exp\bigl(\tfrac\beta2f^TS^{-1}f\bigr).
$$

Duhamel 微分公式给出 $\partial_{f_i}\partial_{f_j}\log Z(0)=\beta^2 C^K_{z,ij}(0)$，而右式 Hessian 为 $\beta S^{-1}$。这证明静态恒等式。二次算子的 Heisenberg 方程为 $\widehat z(t)=e^{At}\widehat z$，由双线性得到动态式。正定二次 Gibbs 算子的分区函数及这些线性源导数均有限；矩阵元公式可在共同 Schwartz 域计算后由热迹延拓。$\square$

Kubo 变换及线性响应本身为既有理论 [H14]。普通对称协方差通常不同：对 $H=(p^2+\omega^2q^2)/2$，

$$
C^K_{qq}(0)=\frac1{\beta\omega^2},\qquad
\tfrac12\langle\{q,q\}\rangle
=\frac{\hbar}{2\omega}\coth(\beta\hbar\omega/2).
$$

Kubo 相关不等于一次普通量子测量的联合概率协方差；第 14 节的经典条件预测下限和第 17 节的独立 Gaussian 样本保证不能直接移植成量子测量结论。应根据实际的响应或相关测量协议另建误差预算。

## 20. 算例、既有文献与剩余边界

在能量归一坐标中取

$$
\Omega=\operatorname{diag}(J_2,2J_2),\qquad
Q=\begin{pmatrix}1&0&0&0\\0&3/5&4/5&0\end{pmatrix}.
$$

则

$$
D=\tfrac35J_2,\qquad
M=\operatorname{diag}(16/25,64/25),\qquad
\operatorname{rank}\mathcal H_1=4.
$$

因此两维当前读数需要补回两个独立方向。所有只读当前状态的预测器的最小均方误差，在 $t=0.1,0.25,0.5$ 时分别为 $0.0316905865,0.1881986417,0.6264800864$。

取 $b=2$、归一化相关误差预算 $\delta=0.001$，固定种子扰动实验得到：

| $h$ | $\eta$ | $\|\widehat W_h-M\|_2$ | 可认证额外方向数 |
|---|---:|---:|---:|
| 0.01 | 20.0110667 | 14.3335506 | 0 |
| 0.05 | 0.8270667 | 0.5461889 | 2 |
| 0.10 | 0.3067667 | 0.2103546 | 2 |
| 0.20 | 0.4766917 | 0.1010210 | 2 |
| 0.50 | 2.6746707 | 0.6470029 | 0 |

可认证方向数为零表示该实验预算不足以认证，不表示没有隐藏方向。47 项局部检查覆盖有理 Gram 恒等式、记忆协方差、Volterra 方程、预测风险分解、有限延迟扰动、白化误差、单延迟成对反例和单模 Kubo 热迹。数值检验不替代一般证明，也不构成硬件实验或机器学习性能比较。

**文献归属。** 从相关函数恢复记忆核已有成熟方法。Lang–Lu 的 2026 论文给出相关函数误差到记忆核估计误差的控制；其另一篇论文研究记忆核扰动到轨迹误差的传递。这里聚焦同一个正定 Hamilton 系统的可观测缺陷、额外状态秩、单延迟信息下限和证书传播，不把整个 Mori/GLE 路线登记为新方法 [LL26, LL25]。非线性势、真正热浴极限、测量反作用和非平稳数据均需要独立证明；第 12–19 节不直接覆盖这些情形。

[M65] H. Mori. *Transport, Collective Motion, and Brownian Motion*. Progress of Theoretical Physics 33(3), 423–455, 1965. DOI: [10.1143/PTP.33.423](https://doi.org/10.1143/PTP.33.423). 投影、记忆与涨落耗散的既有背景。

[M65C] H. Mori. *A Continued-Fraction Representation of the Time-Correlation Functions*. Progress of Theoretical Physics 34(3), 399–416, 1965. DOI: [10.1143/PTP.34.399](https://doi.org/10.1143/PTP.34.399). 相关矩与记忆层级的既有背景。

[LL26] Q. Lang, J. Lu. *Learning Memory Kernels in Generalized Langevin Equations*. SIAM Journal on Mathematics of Data Science 8(1), 141–166, 2026. DOI: [10.1137/24M1651101](https://doi.org/10.1137/24M1651101).

[LL25] Q. Lang, J. Lu. *Error Analysis of Generalized Langevin Equations with Approximated Memory Kernels*. [arXiv:2512.10256](https://arxiv.org/abs/2512.10256), 2025. 其同步白噪声与衰减假设不同于这里的封闭热初态记忆。

[H14] A. Horikoshi. *External Source Method for Kubo-Transformed Quantum Correlation Functions*. [arXiv:1401.0983](https://arxiv.org/abs/1401.0983), 2014. 使用第 II 节的 Kubo 变换约定和线性源响应公式；本文的多模矩阵恒等式由定理 19.1 明确推导。
