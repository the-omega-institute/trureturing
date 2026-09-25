# 奇偶隐箭头的谱边界层

## 54. 消失宽度的谱边界层与端点不紧性

**定义 54.1（趋零的谱区间左端点）。** 保持[窗口相位卷](PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)第 49–52 章的原序列、
同一完整后验标签、精确中心及全部空间归一化。
记 $`\delta=Q^{-1/2}`$，$`\mathfrak L=\log(1/h)`$，并把定义 51.1 的有限谱公式
按原式定义到 $`u=0`$：

```math
\begin{aligned}
N_M(u)&=\left\lfloor h^{-1}e^{u/\sqrt\delta}\right\rfloor,\qquad u\ge0,\\
\mathcal Z_M(u)&=\sum_{|k|\le N_M(u)}(1+k^2)^{-1/2}
 |\widehat\mu_M(k)|^2-2\mathfrak L Y_M^2-\frac{2u}{\sqrt\delta}V_M,\\
\mathcal J_M&=b_*\mathcal Q_M+
 \sum_{t\ne r}H(x_t,x_r)A_tA_r,\qquad
\mathcal Q_M=\sum_tA_t^2,\qquad
T_M=\frac{\mathcal Q_M-V_M}{\sqrt\delta}.
\end{aligned}
```

式 (54.1)。

这里 $`A_t`$ 为按完整得分组合并的精确中心标签和，
$`H(x,y)=1+2D_{\rm w}-2\log(\omega|x-y|)`$，$`\omega=\pi/2`$。
固定 $`U>0`$；取任意确定性序列 $`a_M\in(0,U)`$，满足

```math
a_M\longrightarrow0,\qquad
\ell_M:=\frac{a_M}{\sqrt\delta}\longrightarrow\infty,
\qquad
\vartheta_M(t)=a_M+\left(1-\frac{a_M}{U}\right)t,\quad 0\le t\le U.
```

式 (54.2)。

**定理 54.2（外部仿射律可逼近端点，但不能包含端点）。** 对定义 54.1 的任意序列，

```math
\sup_{a_M\le u\le U}
 \left|\mathcal Z_M(u)-\mathcal J_M-2uT_M\right|
 \longrightarrow0
```

式 (54.3)。

依联合概率成立；在均匀固定基数支持先验的条件版本中，
相应条件误差概率依数据概率趋零。
于是 $`\mathcal Z_M\circ\vartheta_M`$ 在 $`D[0,U]`$ 的 $`J_1`$ 拓扑中收敛到

```math
t\longmapsto\mathcal J_\infty+2tN_2,\qquad
\mathcal J_\infty=b_*\gamma+I_2(H),
```

式 (54.4)。

并联合保留第 51 章的同一端点、固定紧区间轮廓、桥、偶极子及二次坐标。
条件有界 Lipschitz、无条件固定支持一致性及共同方向事件的范围均保持原义。
这里不要求 $`\ell_M/\log Q\to\infty`$。

另一方面，定义到 $`u=0`$ 的整族 $`\mathcal Z_M|_{[0,U]}`$
在任意固定支持序列的无条件律下都不是 $`J_1`$ 紧的。
更精确地，对任意固定 $`c>0`$，置

```math
D_c=2\int_1^{e^c}(|F(v)|^2-\gamma)\,\frac{dv}{v},\qquad
\sigma_c^2=\mathbb E D_c^2>0.
```

式 (54.5)。

则

```math
\mathcal Z_M(c\sqrt\delta)-\mathcal Z_M(0)\Longrightarrow D_c,
\qquad
\liminf_M\inf_S\mathbb P_S\left\{
 |\mathcal Z_M(c\sqrt\delta)-\mathcal Z_M(0)|>
 \frac{\sigma_c}{\sqrt2}\right\}\ge\frac1{60}.
```

式 (54.6)。

将 $`V_M`$ 换成 $`\gamma`$ 时，这些结论也成立，外部二次坐标同时换成
$`T_M^\circ=(\mathcal Q_M-\gamma)/\sqrt\delta`$。

证明。第 51 章的有限二次型逼近已经给出
$`(\mathcal J_M,T_M)`$ 与所列空间对象的联合极限。
这里需补足趋零左端点上的一致谱估计。
以下辅助二阶矩均在第 51 章固定截断索引集上估计，最后才移除全行截断事件；
不把截断失败概率乘以无界谱量。

先保留有限频率的 $`\mathrm{Ci}`$ 余项。
对 $`0<|\theta|\le1`$，令 $`g_\theta(v)=(\cos(\theta v)-1)/v`$，
$`g_\theta(0)=0`$。逐格积分给出

```math
\begin{aligned}
\left|\sum_{k=1}^Ng_\theta(k)-\int_0^Ng_\theta(v)\,dv\right|
 &\le\int_0^N|g_\theta'(v)|\,dv\\
 &\le C|\theta|\{1+\log_+(N|\theta|)\}.
\end{aligned}
```

式 (54.7)。

第二行在换元 $`z=|\theta|v`$ 后使用
$`|\sin z|/z+|1-\cos z|/z^2`$：零点附近有界，远处积分至多对数增长。
把调和数的 $`\log N+\gamma_{\rm E}+O(N^{-1})`$ 与 Ci 恒等式代入，得

```math
\sum_{k=1}^N\frac{\cos(k\theta)}k
 =-\log|\theta|+\mathrm{Ci}(N|\theta|)
 +O\left(N^{-1}+|\theta|\{1+\log_+(N|\theta|)\}\right).
```

式 (54.8)。

第 51 章的可和权重修正仍为
$`D_{\rm w}+O(\theta^2(1+|\log|\theta||)+N^{-2})`$。
在截断组上 $`\omega h\delta\le|\theta|\le Ch\sqrt\lambda`$，
而 $`s=u/\sqrt\delta\in[0,U/\sqrt\delta]`$。
频率取整满足 $`|\log(Nh/e^s)|\le Che^{-s}`$；
因 Ci 对其对数参数的导数为余弦，替换 Ci 的参数也只产生这一量级的误差。
因此有限谱核在所有这些参数上同时满足

```math
\begin{aligned}
K_{N_M(u)}(0)&=2\mathfrak L+2s+b_*+O(h),\\
K_{N_M(u)}(h(x_t-x_r))
 &=2\mathfrak L+H(x_t,x_r)+K_s^{\rm tail}(x_t,x_r)+O(\epsilon_M),
 \qquad t\ne r,\\
K_s^{\rm tail}(x,y)&=2\mathrm{Ci}(\omega e^s|x-y|),\\
\epsilon_M&=C\left[h+h\sqrt\lambda(1+U/\sqrt\delta+\log\lambda)
 +h^2\lambda(1+\mathfrak L+\log\lambda)\right],\qquad
Q^2\epsilon_M\longrightarrow0.
\end{aligned}
```

式 (54.9)。

最后一个极限使用原序列的 $`\mathfrak L\asymp\lambda=Q^3`$。
所有组的共同端点项精确相消后，组数 $`O(Q^2)`$ 与 Cauchy 不等式给出

```math
\sup_{0\le u\le U}\left|
 \mathcal Z_M(u)-\mathcal J_M-2uT_M
 -\sum_{t\ne r}K_{u/\sqrt\delta}^{\rm tail}(x_t,x_r)A_tA_r
 \right|\le CQ^2\epsilon_M\mathcal Q_M=o_{\mathbb P}(1).
```

式 (54.10)。

余下的尾核不能在最小组距上粗略取最大值。
由 Ci 的对数及倒数包络，对所有 $`s\ge0`$ 有

```math
\delta\sum_{k\ge1}\mathrm{Ci}(\omega e^s k\delta)^2\le Ce^{-s}.
```

式 (54.11)。

为证此式，置 $`z=\omega e^s\delta`$。
当 $`z\le1`$，$`kz\le1`$ 的部分由
$`\sum_{k\le1/z}(1+|\log(kz)|)^2\le C/z`$ 控制，
其余部分由 $`\sum_{k>1/z}(kz)^{-2}\le C/z`$ 控制。
当 $`z>1`$，全部求和至多 $`C/z^2\le C/z`$。
乘以 $`\delta`$ 即得结论。

第 51 章不同组的实际两行占据数界与 Gaussian 包络，
对同一辅助乘积标签向量的条件方差 $`v_t`$ 给出

```math
\begin{aligned}
\mathbb E_S\sum_{t\ne r}
 |K_s^{\rm tail}(x_t,x_r)|^2v_tv_r&\le Ce^{-s}+\eta_M,\\
\mathbb E_S\sum_{t\ne r}
 |\partial_sK_s^{\rm tail}(x_t,x_r)|^2v_tv_r&\le C+\eta_M,
 \qquad s\ge0,\\
0\le\eta_M&\le Q^C(1+\log Q)^Ce^{-c_1\lambda}.
\end{aligned}
```

式 (54.12)。

第一行在规则计数区使用
$`\mathbb E_S(v_tv_r)\le C\delta^2e^{-c_1(x_t^2+x_r^2)}`$，
先固定差 $`k=t-r`$ 求和，其余 Gaussian 格和乘以 $`\delta`$ 有统一界，
再用 (54.11)。低计数区的指数小点界、$`O(Q^2)`$ 个组与
$`\sup_{s\ge0,t\ne r}|K_s^{\rm tail}(x_t,x_r)|\le C(1+\log Q)`$
给出所列 $`\eta_M`$。
第二行使用 $`\partial_sK_s^{\rm tail}=2\cos(\omega e^s|x_t-x_r|)`$。
这些估计只需要不同组对应的不同实际行；不假定实际四行独立。

记辅助中心组和为 $`U_t`$，并置
$`B_M(s)=\sum_{t\ne r}K_s^{\rm tail}(x_t,x_r)U_tU_r`$。
这是有限个光滑函数之和。辅助独立性给出
$`\mathbb E_{\mathsf Q}B_M(s)^2=2\sum_{t\ne r}(K_s^{\rm tail})^2v_tv_r`$，
导数也有同一等式。
对任意长为一的区间 $`I_n=[n,n+1]`$，一维 Sobolev 不等式的直接形式是

```math
\sup_{I_n}|f|^2\le\int_{I_n}|f|^2
 +2\left(\int_{I_n}|f|^2\int_{I_n}|f'|^2\right)^{1/2}.
```

式 (54.13)。

可先选一点使其函数平方不超过积分，再积分 $`(|f|^2)'`$ 并用 Cauchy 不等式。
将 (54.12) 代入，再对数据及辅助律取期望，得到

```math
\mathbb E_S\mathbb E_{\mathsf Q}\sup_{I_n}|B_M(s)|^2
 \le C e^{-n/2}+C\sqrt{\eta_M},\qquad n\ge0.
```

式 (54.14)。

把至多 $`C\delta^{-1/2}`$ 个单位区间相加，得

```math
\mathbb E_S\mathbb E_{\mathsf Q}
\sup_{\ell_M\le s\le U/\sqrt\delta}|B_M(s)|^2
\le Ce^{-\lfloor\ell_M\rfloor/2}+C\delta^{-1/2}\sqrt{\eta_M}\longrightarrow0.
```

式 (54.15)。

这正是任意缓慢发散的 $`\ell_M`$ 所需的统一估计。

最后换回精确后验中心。所有 $`s\ge0`$ 的截断尾核矩阵算子范数
同时至多 $`CQ^2(1+\log Q)`$。
第 43 章的 Hilbert 中心界给出组向量位移
$`\|e\|_2\le C\sqrt{V_M}\,r_M`$，
$`r_M=O_{\mathbb P}(Q^{-5/2}+q^{-1/2})`$。
故统一二次型位移至多
$`CQ^2(1+\log Q)(2\|U\|_2\|e\|_2+\|e\|_2^2)=o_{\mathbb P}(1)`$。
用一次完整后验向量总变差比较转移这些有界事件，移除截断事件，
便由 (54.10)、(54.15) 得到 (54.3)。没有通过总变差转移任何无界矩。
联合系数极限、$`a_M\to0`$ 及 (54.3) 随即证明 (54.4)。

为证明另一端的障碍，令 $`\mathcal R_M`$ 为第 50 章的有限谱曲线。
对每个固定 $`c>0`$，包括取整在内，定义精确给出

```math
\mathcal Z_M(c\sqrt\delta)-\mathcal Z_M(0)
=\mathcal R_M(c)-\mathcal R_M(0)-2cV_M.
```

式 (54.16)。

第 50 章固定区间上的联合收敛和 $`V_M\to\gamma`$ 因而给出 (54.6) 的分布极限。
这是固定参数定理的应用，没有代入变化参数。

实 Gaussian 乘积公式写出
$`D_c=I_2(d_c)`$，其中
$`d_c(x,y)=2\int_1^{e^c}\cos(\omega v(x-y))\,dv/v`$。
该连续有界核在对角线上等于 $`2c`$，在其邻域严格为正，
故 $`\sigma_c^2=2\|d_c\|_{L^2(\rho\otimes\rho)}^2>0`$。
所引[二阶 Wiener 混沌谱表示](../../../Library/Dynamics/iyer2025empirical.md)给出四阶矩界
$`\mathbb E D_c^4\le15\sigma_c^4`$。
Paley–Zygmund 不等式于是给出
$`\mathbb P\{|D_c|>\sigma_c/\sqrt2\}\ge1/60`$。
对这个开集用 Portmanteau 下界及固定支持一致性，即得 (54.6)。

$`J_1`$ 紧集在左端点零处必须一致右连续：否则可取紧集内收敛的路径列
及趋零时间列，时间变换固定零点且一致趋于恒等，
从而与极限路径在零处右连续矛盾。
因此紧性要求任意 $`\varepsilon>0`$ 下，

```math
\lim_{\zeta\downarrow0}\limsup_M
\mathbb P_S\{\sup_{0\le u\le\zeta}|\mathcal Z_M(u)-\mathcal Z_M(0)|
>\varepsilon\}=0.
```

式 (54.17)。

式 (54.6) 在 $`c\sqrt\delta\to0`$ 处给出严格正下界，否定这一必要条件。

第 52 章最后给出

```math
\sup_{0\le u\le U}|\mathcal Z_M^\circ(u)-\mathcal Z_M(u)|
\le\frac{2U}{\sqrt\delta}|V_M-\gamma|\longrightarrow0,
```

式 (54.18)。

故确定中心版本的全部结论随之成立。

## 追加锚（本行以下为增补区）
