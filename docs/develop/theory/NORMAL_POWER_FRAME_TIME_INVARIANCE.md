# 正规算子连续幂帧的时间窗不变性

**版本：** v1.0，2026-09-20。

**证明层级：** 本卷给出一个具名猜想的完整纸面证明，尚未经过独立同行复核或 Lean 核验，不写入机器冻结或开放问题结算状态。文献优先权仍待独立确认。下述主定理不要求算子可逆、不要求 reductive 性，也不预设初始传感向量族为 Bessel 族。

本卷补全 [预测可观测性时间窗卷](PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md) 第 6、10 节留下的不可逆正规算子义务。该卷的有限导数深度与显式幂次估计继续保留有界生成元前件；本卷使用另一条解析传播证明，不把那些定量界外推到无界对数。

## 0. 原问题与主结论

[AHP19, Theorem 5.5] 证明有界可逆自伴算子的半连续帧性质与有限正时间窗无关；紧随其后的 Conjecture 5.6 提出 normal reductive 推广。[ACKM26, Theorem 2.13 and Conjecture 2] 再次列出这一问题。本卷证明下面的更强版本，所以无论是否在原猜想中保留可逆性，主定理均覆盖其正规算子范围。

### 定理 0.1（任意有界正规算子的有限时间窗不变性）

令 $\mathcal H$ 为非零复 Hilbert 空间，$A\in\mathcal B(\mathcal H)$ 正规，$\mathcal G=(g_j)_{j\in J}$ 为可数向量族。对 $\lambda\ne0$ 固定

$$
\ell(\lambda)=\ln|\lambda|+i\operatorname{Arg}\lambda,
\qquad\operatorname{Arg}\lambda\in[-\pi,\pi),
$$

并以谱演算定义 $A^t$，在零谱点取 $0^t=0$，$t>0$。记

$$
\mathcal E_T(x)=\sum_{j\in J}\int_0^T
|\langle x,A^tg_j\rangle|^2dt.
$$

若存在 $T_0>0$ 和常数 $0<a_0\le M_0<\infty$，使

$$
a_0\|x\|^2\le\mathcal E_{T_0}(x)\le M_0\|x\|^2
\quad(\forall x\in\mathcal H),
$$

则对每个 $T>0$ 都存在 $0<a_T\le M_T<\infty$ 使

$$
\boxed{a_T\|x\|^2\le\mathcal E_T(x)\le M_T\|x\|^2
\quad(\forall x\in\mathcal H).}
$$

因此，一个有限正窗上的半连续帧性质与每个有限正窗上的半连续帧性质等价。

证明分为三个环节：构造与原幂分支相容的解析算子族；由积分上界推出正时间处的局部一致观测界；用标量解析函数的紧性把短窗上的小读数传播到任意紧时间段。第 4 节完成证明。

## 1. 连续幂的解析延拓与虚时间平移

内积约定对第一变量线性。令 $E_A$ 为 $A$ 的投影值谱测度，$r_A=\max(1,\|A\|)$。在右半平面 $\mathbb C_+=\{z:\operatorname{Re}z>0\}$ 定义

$$
R_z=\int_{\sigma(A)\setminus\{0\}}
\exp\bigl(z\overline{\ell(\lambda)}\bigr)\,dE_A(\lambda).
$$

零谱子空间上的乘子为零。另设 $R_0=I$，并对 $v\in\mathbb R$ 定义

$$
V_v=\int_{\sigma(A)\setminus\{0\}}
\exp\bigl(iv\overline{\ell(\lambda)}\bigr)\,dE_A(\lambda)
+E_A(\{0\}).
$$

### 引理 1.1（谱算子的解析性与分解）

$R_z$ 在 $\mathbb C_+$ 上算子范数全纯，并满足

$$
R_t=(A^t)^*,\qquad
\|R_t\|\le r_A^t\quad(t\ge0),
$$

$$
\|V_v\|\le e^{\pi|v|},\qquad
R_{u+iv}=R_uV_v\quad(u>0),
$$

$$
R_{s+u}=R_uR_s\quad(s\ge0,\ u>0).
$$

**证明。** 对非零谱点写 $\lambda=\rho e^{i\theta}$，则

$$
\left|e^{iv\overline{\ell(\lambda)}}\right|=e^{v\theta}
\le e^{\pi|v|}.
$$

各乘法公式逐谱点成立；在零谱子空间上也成立，因为 $u>0$。谱定理给出相应算子等式和范数界。

全纯性可在任意紧集 $K\subset\mathbb C_+$ 上由一致微分核实。若 $\operatorname{Re}z\ge\varepsilon>0$，对每个固定整数 $k\ge0$，乘子的 $k$ 阶导数由

$$
\rho^{\operatorname{Re}z}
\bigl(|\ln\rho|+\pi\bigr)^k e^{\pi|\operatorname{Im}z|}
$$

控制。该量在 $0<\rho\le\|A\|$ 与 $z\in K$ 上有界，并在 $\rho\downarrow0$ 时趋零。以包含 $K$ 的较大紧邻域控制二阶余项，即得差商在谱乘子的上确界范数中收敛，因此可在算子范数中微分。$\square$

无需在零时刻求导，也无需将无界 $\log A$ 当作有界算子。对于负实谱点，证明使用的是 $(A^t)^*$，并没有把它替换成可能具有不同分支的 $(A^*)^t$。

## 2. 积分上界推出正时间处的一致观测界

对有限集 $F\subset J$，定义有界有限行分析映射

$$
C_Fx=(\langle x,g_j\rangle)_{j\in F}.
$$

这里只把有限行映射当作有界算子；不预先假设完整初始分析映射有界。

### 引理 2.1（局部观测平滑界）

只假设定理 0.1 的积分上界。取 $z_0=u_0+iv_0\in\mathbb C_+$，并令

$$
\rho=\min(u_0/2,T_0/4),\qquad
s=\max(0,u_0-T_0/2).
$$

则对任意有限 $F$ 和任意 $x$，

$$
\boxed{
\|C_FR_{z_0}x\|^2
\le \frac{2M_0}{\pi\rho}\,
r_A^{2s}e^{2\pi(|v_0|+\rho)}\|x\|^2.
}
$$

因此对每个紧集 $K\subset\mathbb C_+$，存在 $B_K<\infty$，独立于 $F$，使

$$
\sup_{z\in K}\|C_FR_z\|\le B_K.
$$

**证明。** 有限维向量函数 $z\mapsto C_FR_zx$ 全纯，其范数平方为次调和函数。以 $D(z_0,\rho)$ 为圆盘，面积平均不等式给出

$$
\|C_FR_{z_0}x\|^2
\le\frac1{\pi\rho^2}
\int_{D(z_0,\rho)}\|C_FR_zx\|^2\,d\operatorname{Area}(z).
$$

该圆盘包含于矩形

$$
[s,s+T_0]\times[v_0-\rho,v_0+\rho].
$$

固定虚部 $v$，由引理 1.1 和非负有限和，

$$
\begin{aligned}
\int_s^{s+T_0}\|C_FR_{u+iv}x\|^2du
&=\int_0^{T_0}\|C_FR_tR_sV_vx\|^2dt\\
&\le M_0\|R_sV_vx\|^2\\
&\le M_0r_A^{2s}e^{2\pi|v|}\|x\|^2.
\end{aligned}
$$

端点处的取值不影响积分。再对长度为 $2\rho$ 的虚部区间积分，得到所示常数。$K$ 中实部有正下界、实部和虚部都有上界，所以常数可在 $K$ 上统一选取。$\square$

### 推论 2.2（正时间分析映射的定义）

对 $z\in\mathbb C_+$，系数族

$$
\mathcal C(z)x=(\langle R_zx,g_j\rangle)_{j\in J}
$$

属于 $\ell^2(J)$，且 $\|\mathcal C(z)\|\le B_K$ 对 $z\in K$ 成立。

**证明。** 对有限集 $F$ 的平方和使用引理 2.1，并按可数指标取单调极限。$\square$

这允许初始传感族非 Bessel，甚至允许 $\|\mathcal C(t)\|$ 在 $t\downarrow0$ 时发散。

## 3. 小读数的解析传播

### 引理 3.1（标量解析传播）

设 $f_n$ 为 $\mathbb C_+$ 上的全纯函数，并在每个紧子集上一致有界。若某个实区间 $I=[a,b]\subset(0,\infty)$、$a<b$ 满足

$$
\int_I|f_n(t)|^2dt\longrightarrow0,
$$

则 $f_n\to0$ 在 $\mathbb C_+$ 的每个紧子集上一致成立。

**证明。** 局部一致有界性与 Cauchy 导数估计给出紧子集上的等度连续性。Arzelà–Ascoli 与紧集穷竭的对角选取表明，任意子列都存在在紧子集上一致收敛的子子列，其极限全纯。这是标量 Montel 紧性的标准证明。

该极限在 $I$ 上的平方积分为零，因此由连续性在 $I$ 上为零，再由恒等定理在整个右半平面为零。若原序列未在某个紧集上一致趋零，取一个保持正下界的子列会与上述子子列结论矛盾。$\square$

### 命题 3.2（无限传感族的范数传播）

在引理 2.1 的假设下，令 $\|x_n\|\le1$。若某个 $T>0$ 满足

$$
\int_0^T\|\mathcal C(t)x_n\|_{\ell^2}^2dt\longrightarrow0,
$$

则对每个紧集 $K\subset\mathbb C_+$，

$$
\sup_{z\in K}\|\mathcal C(z)x_n\|_{\ell^2}\longrightarrow0.
$$

**证明。** 反设存在 $\eta>0$、子列及 $z_n\in K$，使完整系数范数大于 $\eta$。选有限 $F_n\subset J$ 使 $\|C_{F_n}R_{z_n}x_n\|>\eta/2$，并选单位向量 $v_n\in\mathbb C^{F_n}$ 满足

$$
|\langle C_{F_n}R_{z_n}x_n,v_n\rangle|>\eta/2.
$$

定义标量全纯函数

$$
f_n(z)=\langle C_{F_n}R_zx_n,v_n\rangle.
$$

引理 2.1 保证这个标量函数族在每个紧集上一致有界，且对 $I=[T/4,T/2]$，

$$
\int_I|f_n(t)|^2dt
\le\int_0^T\|\mathcal C(t)x_n\|_{\ell^2}^2dt\longrightarrow0.
$$

引理 3.1 推出 $\sup_K|f_n|\to0$，与在 $z_n$ 的下界矛盾。$\square$

本证明使用随 $n$ 变化的有限指标集和标量测试向量；没有把有限维 Montel 紧性错误地套用于无限维目标空间。

## 4. 主定理的证明

先说明任意有限窗口上的上界。给定 $T>0$，取整数 $N=\lceil T/T_0\rceil$。由半群乘法与原积分上界，

$$
\begin{aligned}
\mathcal E_T(x)
&\le\sum_{k=0}^{N-1}
\int_{kT_0}^{(k+1)T_0}\|\mathcal C(t)x\|^2dt\\
&\le M_0\sum_{k=0}^{N-1}\|R_{kT_0}x\|^2\\
&\le M_0\sum_{k=0}^{N-1}r_A^{2kT_0}\|x\|^2.
\end{aligned}
$$

因而可取

$$
M_T=M_0\sum_{k=0}^{N-1}r_A^{2kT_0}<\infty.
$$

当 $T\ge T_0$ 时，积分单调性直接给出下界 $a_0$。

现在设 $0<T<T_0$。若不存在正下界，则存在单位向量 $x_n$ 使 $\mathcal E_T(x_n)\to0$。取 $\delta=T/2$，由命题 3.2，

$$
\sup_{t\in[\delta,T_0]}\|\mathcal C(t)x_n\|^2\longrightarrow0.
$$

所以

$$
\begin{aligned}
\mathcal E_{T_0}(x_n)
&=\int_0^\delta\|\mathcal C(t)x_n\|^2dt
+\int_\delta^{T_0}\|\mathcal C(t)x_n\|^2dt\\
&\le\mathcal E_T(x_n)
+(T_0-\delta)\sup_{[\delta,T_0]}\|\mathcal C(t)x_n\|^2
\longrightarrow0.
\end{aligned}
$$

这与 $\mathcal E_{T_0}(x_n)\ge a_0$ 矛盾。故每个 $T>0$ 都有正下界，定理 0.1 得证。$\square$

**零谱说明。** 若 $A$ 有非零核，核内状态在全部正时刻的读数都为零，因此主定理的正下界假设已经排除该情形。证明仍允许 $0\in\sigma(A)$ 为连续谱点，且不要求 $A^{-1}$ 有界。

## 5. 非 Bessel 初始族与零谱聚集的显式实例

在 $\ell^2(\mathbb N)$ 中令

$$
Ae_n=e^{-n}e_n,\qquad g_n=\sqrt{2n}\,e_n.
$$

$A$ 有界、正规且单射，$0\in\sigma(A)$，无有界逆。初始族不是 Bessel，因为 $\|g_n\|^2=2n$ 无界。但是

$$
\mathcal E_T(x)
=\sum_{n\ge1}(1-e^{-2nT})|x_n|^2,
$$

所以最佳帧界为

$$
\boxed{a_T=1-e^{-2T},\qquad M_T=1.}
$$

在正时间处，

$$
\|\mathcal C(t)\|^2
=\sup_{n\ge1}2n e^{-2nt}\le\frac1{et}.
$$

**证明。** 对每个坐标直接积分 $\int_0^T2n e^{-2nt}dt$，并观察所得系数随 $n$ 增大而递增，趋于 1。最后将连续函数 $u\mapsto2u e^{-2ut}$ 在 $u>0$ 上最大化，其极大值为 $1/(et)$。$\square$

这个实例说明：主定理确实覆盖初始分析映射无界、对数生成元无界的范围；正时间处的平滑界是证明中的必要替代接口。

## 6. 与定量预测和辛结构的连接

本卷证明有限正窗之间的稳定性传递，未给出在零谱聚集情形下统一的短窗幂次。若 $A$ 另有有界逆，则有界 Borel 对数存在，[预测可观测性时间窗卷](PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md) 的有限导数定理进一步给出

$$
a(T)=\Theta(T^{2m+1}),\qquad
\|\mathcal T_T^\dagger\|=\Theta(T^{-m-1/2}).
$$

对 [辛预测完成卷](SYMPLECTIC_PREDICTIVE_COMPLETION.md) 的有限维 Hamilton 预测商，其生成元本身有界，因而可以直接使用这些定量结论，并同时计算辛闭包余量。三项结果依次回答：是否能由某个窗口恢复；缩短窗口会付出多大噪声代价；压缩后的变量是否仍保有共轭配对。

一般无界生成元的酉群不自动具有本卷的有界虚时间平移结构。时间窗卷第 10 节的平移群反例仍然成立：有限扫描速度可能产生正的最小观测时间。这与本卷主定理不冲突，因为这里的动力学是具有固定有界辐角分支的正规算子连续幂。

## 7. 结论状态与原始文献

本卷定理 0.1 为 [AHP19, Conjecture 5.6] 与 [ACKM26, Conjecture 2] 给出纸面解答，并加强到全部有界正规算子。原文、幂分支、无限维指标和零谱边界已在正文中逐项处理。仍需独立完成的是证明审阅、相关控制论与算子理论优先权核查，以及机器形式化；这些状态不影响本文已经写出的数学前件与推导范围。

[AHP19] A. Aldroubi, L. X. Huang, A. Petrosyan. *Frames induced by the action of continuous powers of an operator*. Journal of Mathematical Analysis and Applications 478(2), 1059–1084, 2019. DOI: [10.1016/j.jmaa.2019.05.066](https://doi.org/10.1016/j.jmaa.2019.05.066). [arXiv:1801.10103](https://arxiv.org/abs/1801.10103). 使用 Definition 2.3、Theorem 5.5 和 Conjecture 5.6。

[ACKM26] A. Aldroubi, C. Cabrelli, I. Krishtal, U. Molter. *Dynamical Sampling: A Survey*. La Matematica 5, Article 37, 2026. DOI: [10.1007/s44007-026-00215-y](https://doi.org/10.1007/s44007-026-00215-y). [arXiv:2511.10769v3](https://arxiv.org/abs/2511.10769v3). 使用 Theorem 2.13 与 Conjecture 2。

[DMM21] R. Díaz Martín, I. Medri, U. Molter. *Continuous and discrete dynamical sampling*. Journal of Mathematical Analysis and Applications 499(2), 125060, 2021. DOI: [10.1016/j.jmaa.2021.125060](https://doi.org/10.1016/j.jmaa.2021.125060). [arXiv:2006.08046](https://arxiv.org/abs/2006.08046). 提供有界生成元、观测与连续帧的既有研究背景。
