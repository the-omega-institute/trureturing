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

## 55. 谱边界层的紧化轮廓与精确分离判据

**定义 55.1（同一谱曲线的边界层余项）。** 保持定义 54.1 的原模型及记号，固定 $`U>0`$，
记 $`S_M=U/\sqrt\delta`$，$`\psi(s)=s/(1+s)`$。定义右连续余项

```math
\mathcal B_M(s)=
\begin{cases}
 \mathcal Z_M(s\sqrt\delta)-\mathcal J_M-2s\sqrt\delta\,T_M,
       &0\le s<S_M,\\
 0,&s\ge S_M,
\end{cases}
\qquad
\widetilde{\mathcal B}_M(x)=
\begin{cases}
 \mathcal B_M\!\left(\dfrac{x}{1-x}\right),&0\le x<1,\\
 0,&x=1.
\end{cases}
```

式 (55.1)。

$`S_M`$ 处采用右侧的零值；允许该处有跳跃。
在第 53 章的同一实 Gaussian 空间上，令

```math
\mathcal E(s)=I_2(K_s^{\rm tail}),\qquad
K_s^{\rm tail}(x,y)=2\mathrm{Ci}(\omega e^s|x-y|),\qquad s\ge0,
\qquad
\widetilde{\mathcal E}(x)=
\begin{cases}
 \mathcal E\!\left(\dfrac{x}{1-x}\right),&0\le x<1,\\
 0,&x=1.
\end{cases}
```

式 (55.2)。

空间核的对角线取值不参与二重 Wiener 积分。

**定理 55.2（原始数组的完整边界层轮廓）。** $`\mathcal E`$ 有一个在
$`[0,\infty)`$ 连续且在无穷远几乎处处趋零的版本。
对该版本，$`\widetilde{\mathcal E}\in C[0,1]`$，且

```math
\left(\widetilde{\mathcal B}_M,\mathcal J_M,T_M\right)
\Longrightarrow
\left(\widetilde{\mathcal E},\mathcal J_\infty,N_2\right)
\quad\text{于 }D[0,1]_{J_1}\times\mathbb R^2.
```

式 (55.3)。

该收敛为 C 紧，并可联合保留第 51 章的同一端点、固定紧区间轮廓、桥和偶极子。
$`\mathcal J_\infty=b_*\gamma+I_2(H)`$ 与整个 $`\widetilde{\mathcal E}`$
由同一个 $`\mathcal W_\rho`$ 产生，$`N_2`$ 独立于整个 $`\mathcal W_\rho`$。
条件有界 Lipschitz 收敛依数据概率成立的先验空间、固定支持的无条件一致性
以及未知方向的共同一致事件，均保持第 54 章的范围。
若同时将谱曲线中的 $`V_M`$ 及二次坐标的中心换成 $`\gamma`$，
余项 $`\mathcal B_M`$ 在每个有限样本上完全不变。

证明。先证明连续对象的尾部和版本。
第 53 章的 Ci 等距式及 Gaussian 卷积包络给出，对 $`s\ge0`$，

```math
\mathbb E|\mathcal E(s)|^2\le Ce^{-s},\qquad
\partial_sK_s^{\rm tail}(x,y)=2\cos(\omega e^s|x-y|),\qquad
\mathbb E|I_2(\partial_sK_s^{\rm tail})|^2\le8\gamma^2.
```

式 (55.4)。

在每个固定区间上，核及其导数均平方可积。
Bochner 积分与二重 Wiener 积分的连续性给出具有该弱导数的随机 $`H^1`$ 版本，
因而有连续版本；可在可数个整端点区间上取相容版本。
对第 54 章的单位区间不等式取期望，得

```math
\mathbb E\sup_{n\le s\le n+1}|\mathcal E(s)|^2\le Ce^{-n/2},
\qquad
\mathbb E\sup_{s\ge R}|\mathcal E(s)|^2\le Ce^{-\lfloor R\rfloor/2},
\qquad R\ge0.
```

式 (55.5)。

第二式把第一式求和。整数 $`R`$ 对应的尾部上确界递减，期望趋零，
故其极限几乎处处为零。这同时给出所需的无穷远版本和紧化连续性。

现回到实际数组。仍在固定截断索引集上用同一个辅助标签向量，令

```math
X_M(s)=\sum_{t\ne r}K_s^{\rm tail}(x_t,x_r)U_tU_r.
```

式 (55.6)。

第 54 章的有限谱分解在 $`0\le s\le S_M`$ 上一致成立，
其余误差及统一精确中心位移依概率趋零。
先考虑任意固定 $`R<\infty`$。
第 54 章的核及导数二阶界给出

```math
\mathbb E_S\mathbb E_{\mathsf Q}
 \|X_M\|_{H^1[0,R]}^2\le C_R.
```

式 (55.7)。

因此在辅助联合律下，路径在 $`C[0,R]`$ 中紧。
此处使用一维 $`H^1`$ 有界集的紧嵌入：
其函数一致有界，增量至多为导数 $`L^2`$ 范数乘距离的平方根。
条件版本先用条件 Markov 不等式，再用数据期望控制坏环境。

还需识别与截距的联合有限维律。
对任意固定 $`s_1,\ldots,s_m\in[0,R]`$，
把核 $`H,K_{s_1}^{\rm tail},\ldots,K_{s_m}^{\rm tail}`$
同时在空间远尾和近对角线外截断。
它们在近对角线均至多为 $`C_R(1+|\log|x-y||)`$，
远处至多为 Gaussian 空间包络可积的对数或有界函数。
第 51 章不同组的实际两行估计因而给出

```math
\begin{aligned}
\sup_{s\in[0,R]}\mathbb E_S
 \sum_{\substack{t\ne r\\|x_t-x_r|\le\varepsilon}}
 |K_s^{\rm tail}(x_t,x_r)|^2v_tv_r
 &\le C_R\varepsilon(1+|\log\varepsilon|^2)+o(1),\\
\sup_{s\in[0,R]}\mathbb E_S
 \sum_{\substack{t\ne r\\|x_t|>A\ \mathrm{or}\ |x_r|>A}}
 |K_s^{\rm tail}(x_t,x_r)|^2v_tv_r
 &\le C_Re^{-c_R A^2}+o(1).
\end{aligned}
```

式 (55.8)。

这些是实际数据环境上的辅助方差界，不是实际后验噪声的矩收敛。
截断后的一组连续核可由同一个有限空间分割上的矩形阶梯核逼近。
对任一阶梯核 $`K=\sum_{i,j}k_{ij}\mathbf1_{I_i}\otimes\mathbf1_{I_j}`$，
同一辅助向量给出精确恒等式

```math
\sum_{t\ne r}K(x_t,x_r)U_tU_r
 =\sum_{i,j}k_{ij}U(I_i)U(I_j)
  -\sum_i k_{ii}\sum_{x_t\in I_i}U_t^2.
```

式 (55.9)。

第 49、51 章的混合联合中心极限定理和块内平方和集中，
同时使这些量收敛到同一 $`\mathcal W_\rho`$ 上的二重积分，
并与二次坐标的极限 $`N_2`$ 独立。
有限核族的逼近误差由 (55.8) 和辅助二次型等距式控制；
连续极限误差由 Wiener 等距式控制。
这证明所需的联合有限维收敛，而非由不同对象的边缘律拼接联合律。
结合 (55.7)、已有空间路径紧性及极限的连续性，即得固定 $`R`$ 的联合路径极限。

统一中心位移、一次完整后验向量总变差比较及截断事件移除，
按第 54 章转移上述有界测试。
各条件误差在数据概率中趋零，因此亦得到固定 $`R`$ 的条件联合结论。
没有把 $`H^1`$ 无界范数的期望经总变差传到实际后验。

接着控制增长区间。
第 54 章的单位区间求和对固定 $`R`$ 也成立，给出

```math
\mathbb E_S\mathbb E_{\mathsf Q}
 \sup_{R\le s\le S_M}|X_M(s)|^2
 \le Ce^{-\lfloor R\rfloor/2}
       +C\delta^{-1/2}\sqrt{\eta_M},\qquad
\delta^{-1/2}\sqrt{\eta_M}\longrightarrow0.
```

式 (55.10)。

统一精确中心、有限谱误差和一次向量比较从而证明，对任意 $`\varepsilon>0`$，

```math
\lim_{R\to\infty}\limsup_M\sup_S
 \mathbb P_S\left\{\sup_{s\ge R}|\mathcal B_M(s)|>\varepsilon\right\}=0.
```

式 (55.11)。

条件尾部误差亦在先取 $`M`$、再取 $`R`$ 的意义下依数据概率趋零。
设 $`\chi_R`$ 在 $`[0,R]`$ 等于一，在 $`[R+1,\infty)`$ 等于零，
并在中间线性连接。
固定区间联合收敛给出 $`\chi_R\mathcal B_M`$ 紧化后的联合极限。
由 (55.5)、(55.11)，去掉 $`\chi_R`$ 的一致范数误差在两端都趋零。
对有界 Lipschitz 测试作三角估计，再令 $`R\to\infty`$，便得到 (55.3)。
同一逼近证明 C 紧性；它也控制移动截断处的跳跃，未把有限谱曲线假定为连续。
具体地，截断处的左极限由原余项在 $`[S_M-1,S_M]`$ 的上确界控制，
该上确界依 (55.10) 和同一转移依概率趋零。
被零延拓舍去的原始端点 $`u=U`$ 也由这个闭区间估计控制，
因而后文对原始闭区间取最大值时不会漏掉端点。

固定支持等价性和共同方向事件作用于整个已构造对象，保持联合结论。
最后精确代入

```math
\mathcal Z_M^\circ(u)-\mathcal Z_M(u)
 =\frac{2u}{\sqrt\delta}(V_M-\gamma),\qquad
T_M^\circ-T_M=\frac{V_M-\gamma}{\sqrt\delta},
```

式 (55.12)。

可见余项中两次中心变化完全相消。

**定理 55.3（外层仿射近似的必要充分条件）。** 对任意确定性序列
$`a_M\in[0,U)`$、$`a_M\to0`$，下列两条件等价：

```math
\sup_{a_M\le u\le U}|\mathcal Z_M(u)-\mathcal J_M-2uT_M|
 \longrightarrow0\quad\text{依概率},
\qquad
\frac{a_M}{\sqrt\delta}\longrightarrow\infty.
```

式 (55.13)。

概率结论可取任意固定支持序列的无条件律；当条件成立时，
第 54 章的固定支持一致性和条件版本同时成立。
将中心同时换成 $`\gamma`$ 不改变这个等价关系。

证明。充分性由定理 54.2 给出。
若比例不趋无穷，则存在子列使 $`a_M/\sqrt\delta\to c<\infty`$。
定理 55.2 的连续极限及确定性移动时刻取值给出

```math
\mathcal Z_M(a_M)-\mathcal J_M-2a_MT_M
 =\mathcal B_M(a_M/\sqrt\delta)
 \Longrightarrow\mathcal E(c).
```

式 (55.14)。

$`K_c^{\rm tail}`$ 在对角线附近有非零对数奇性，
而 $`\rho`$ 处处为正，故
$`\mathbb E\mathcal E(c)^2=2\|K_c^{\rm tail}\|_{L^2(\rho\otimes\rho)}^2>0`$。
因此该非零极限不可能同时依概率趋零，否定 (55.13) 的第一个条件。
这个反证适用于任意固定支持序列，因为整个统计量的固定支持律由置换等变性相同。
(55.12) 的精确相消最后给出确定中心版本。

**推论 55.4（有限比例的最大误差律及一致概率障碍）。** 记
$`r_M=a_M/\sqrt\delta`$。
若 $`r_M\to c<\infty`$，则与定理 55.2 的同一联合对象一起，

```math
\sup_{a_M\le u\le U}|\mathcal Z_M(u)-\mathcal J_M-2uT_M|
 \Longrightarrow \sup_{s\ge c}|\mathcal E(s)|.
```

式 (55.15)。

右侧保留与截距、端点和空间轮廓的共同 Gaussian 来源，并不声称独立。
此外，对固定 $`R<\infty`$，令

```math
\begin{aligned}
g(d)&=\int_{\mathbb R}\rho(x)\rho(x+d)\,dx
      =g(0)e^{-\kappa d^2/4},\\
z_0&=e^{-1-\gamma_{\mathrm E}},\qquad
d_R=\min\{1,z_0/(\omega e^R)\},\qquad v_R=16d_Rg(1)>0.
\end{aligned}
```

式 (55.16)。

在任意满足 $`r_M\le R`$ 的子列上，任意固定支持序列均有

```math
\liminf_M\mathbb P_S\!\left\{
 \sup_{a_M\le u\le U}|\mathcal Z_M(u)-\mathcal J_M-2uT_M|
       >\sqrt{v_R/2}\right\}\ge\frac1{60}.
```

式 (55.17)。

证明。紧化后的下端点 $`\psi(r_M)`$ 趋于 $`\psi(c)`$。
在连续极限处，$`J_1`$ 收敛蕴含一致收敛；极限路径的一致连续性
使移动下端点的尾部上确界成为连续泛函。
定理 55.2 因而给出零延拓余项的 (55.15)。
原始 $`u=U`$ 端点与其零替代值的差依概率趋零，故原闭区间也有同一极限。

为证明定量障碍，使用
$`\mathrm{Ci}(z)=\gamma_{\mathrm E}+\log z+\int_0^z(\cos t-1)\,dt/t`$。
当 $`0<z\le z_0`$ 时，$`\mathrm{Ci}(z)\le-1`$。
将方差积分限制在 $`0<|d|\le d_R`$，由 $`g(d)\ge g(1)`$ 得
$`\inf_{0\le s\le R}\operatorname{Var}\mathcal E(s)\ge v_R`$。
第二混沌的四阶矩不超过方差平方的十五倍，
Paley–Zygmund 不等式遂给出
$`\inf_{0\le s\le R}\mathbb P\{|\mathcal E(s)|>\sqrt{v_R/2}\}\ge1/60`$。
对任意 $`r_M\le R`$ 的子列，再取比例收敛的子列，
以 (55.14) 和开集 Portmanteau 将该下界转移到实际下端点余项，
再用最大误差大于等于该余项的绝对值。
若整个有界比例子列的下极限小于 $`1/60`$，可先取违反该下界的子列，
再取比例收敛子列而得到矛盾，故 (55.17) 成立。
此处始终转移概率，不用实际后验矩的收敛代替概率障碍。

## 追加锚（本行以下为增补区）
