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

## 56. 算术网格以下的实际谱 OU 极限

**定义 56.1（增长频率上的放大余项）。** 保持定义 54.1 的原始模型、
固定幅度、固定 $`\beta\in(1/2,1)`$、$`\lambda=Q^3`$ 及同一组精确中心标签。
记 $`\delta=Q^{-1/2}`$。取确定性序列及固定紧区间

```math
s_M\longrightarrow\infty,\qquad R_M=e^{s_M},\qquad
r_M=R_M\delta\longrightarrow0,\qquad I=[t_0,t_1]\subset\mathbb R.
```

式 (56.1)。

用定义 54.1 的有限截距 $`\mathcal J_M`$，定义

```math
\mathcal U_M(t)=e^{(s_M+t)/2}
 \left\{\mathcal Z_M((s_M+t)\sqrt\delta)
       -\mathcal J_M-2(s_M+t)\sqrt\delta\,T_M\right\},\qquad t\in I.
```

式 (56.2)。

所有充分大的 $`M`$ 都使取值点位于任意预先固定的 $`(0,U)`$ 内。
截距必须是 $`b_*\mathcal Q_M+\sum_{j\ne k}H(x_j,x_k)A_jA_k`$；
若另取只有相同弱极限的有限截距，仍须额外控制它与此截距的差为
$`o_{\mathbb P}(R_M^{-1/2})`$。

**定理 56.2（完整网格分离范围内的联合实际极限）。** 对 (56.1) 的每个序列，
实际平稳独立对实验及实际连续路径实验均有

```math
\left(\mathcal U_M,T_M,\mathcal J_M,Y_M,
       L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip}\right)
\Longrightarrow
\left(\mathcal U,N_2,\mathcal J_\infty,Y,
       L|_{[-A,A]},C|_{[-A,A]},Z\right),\qquad A>0.
```

式 (56.3)。

路径坐标取紧区间 $`J_1`$ 拓扑，且为 C-tight。
$`Z_M^{\rm dip}`$ 表示原空间偶极子，以区别于谱曲线。
新过程 $`\mathcal U`$ 是中心平稳连续 Gaussian 过程，满足

```math
\mathbb E[\mathcal U(t)\mathcal U(v)]
 =16g_0e^{-|t-v|/2},\qquad g_0=\int_{\mathbb R}\rho(x)^2\,dx.
```

式 (56.4)。

在原实 isonormal Gaussian 噪声 $`W_\rho`$ 上，旧坐标仍为
$`Y=W_\rho(1)`$、$`L(x)=W_\rho(1_{(-\infty,x]})`$、
$`C(x)=L(x)-F_0(x)Y`$、$`Z=W_\rho(x)`$ 和
$`\mathcal J_\infty=b_*\gamma+I_2(H)`$。
$`N_2\sim N(0,\nu_2)`$，$`\nu_2=2g_0`$；
联合对象 $`(\mathcal U,N_2)`$ 独立于整个 $`W_\rho`$，且两个新坐标相互独立。
收敛同时具有均匀支持先验下依数据概率成立的条件有界 Lipschitz 版本，
以及无条件固定支持一致版本。
未知方向使用原共同判向事件。将 $`V_M`$ 与 $`T_M`$ 同时改为
$`\gamma`$ 与 $`(\mathcal Q_M-\gamma)/\sqrt\delta`$ 时，
(56.2) 逐样本不变；本结论不涉及实际后验无界矩的收敛。

证明。以下比较都作用于同一个完整标签向量。
第 53 章的连续谱极限只用于识别核，不能在其弱收敛中代入 $`s_M`$。
这里直接控制有限原始统计量的放大误差。

先给出实际数据环境上的增长核心估计。
在第 49–51 章的共同计数截断事件上，完整得分组的标记为 $`x_j=j\delta`$，
组数至多 $`CQ^2`$，$`|x_j|\le C\sqrt\lambda`$。
该事件的补集概率一致趋零。
令 $`C_j`$ 为实际组占用数，$`f_j`$ 为信号 Poisson 点概率，
$`m_j`$ 为信号与背景的混合比较均值。
原始一行、两行点概率与对应独立 Poisson 点概率的相对误差
在固定计数截断上分别为 $`O(\lambda^2/M)`$、$`O(\lambda^3/M)`$。
这些是实际联合行概率估计，不是观测行独立性。
它们及精确去倾斜给出

```math
\begin{aligned}
m_j&=2qf_j(1+O(\eta_M)),\qquad
 \eta_M=O(\lambda\eta+\epsilon\lambda+q/M+q^{-1}),\\
|\mathbb EC_j-m_j|&\le e_Mm_j,\qquad
 \operatorname{Var}(C_j)\le C(m_j+e_Mm_j^2),\qquad
 e_M=C\lambda^3/M.
\end{aligned}
```

式 (56.5)。

此处 $`\eta=\alpha-P/Q`$；$`\eta_M`$ 乘任意固定 $`Q`$ 次幂仍趋零。
这些估计对连续路径实验成立，因其标记生成函数的主特征值是
$`1+A_z+O(M^{-2})`$，在 $`T=2M\lambda`$ 时相对生成函数误差为
$`O(\lambda/M)`$；固定截断上的 Cauchy 系数提取对两行至多损失
$`O(\lambda^2)`$。独立对实验直接用 $`(1+A_z)^T`$。
因此两种实验可共用 (56.5)。

取充分大的固定 $`K`$，令 $`H_Q=\sqrt{K\log Q}`$，
$`\mathcal C_Q=\{j:|j\delta|\le H_Q\}`$。
写 $`\xi=a\lambda-\lfloor a\lambda\rfloor`$，
两个计数偏差是 $`\sqrt\lambda x_j-\xi`$ 和
$`(P/Q)\sqrt\lambda x_j+\xi`$。
在此核心内展开 Poisson 率函数并保留 Stirling 余项，得

```math
f_j=\frac{e^{-\kappa x_j^2/2}}{2\pi\lambda\sqrt{ab}}
 \left[1+O_K\left(\frac{1+H_Q^3}{\sqrt\lambda}
            +\frac{1+H_Q^6}{\lambda}+\eta H_Q^2\right)\right].
```

式 (56.6)。

二次率函数给出 $`-\kappa x_j^2/2`$；取整误差为
$`O((1+|x_j|)/\sqrt\lambda)`$，三次项为
$`O((1+|x_j|^3)/\sqrt\lambda)`$，四次余项和指数展开给出所列平方阶。
核心有 $`O(Q^{1/2}\sqrt{\log Q})`$ 组，且最小 $`m_j`$ 至少为
$`qQ^{-C_K}`$。由 (56.5) 的 Chebyshev 界及有限并集，对每个固定 $`D>0`$，

```math
Q^D\max_{j\in\mathcal C_Q}|C_j/m_j-1|\longrightarrow0
\quad\hbox{依数据概率}.
```

式 (56.7)。

令 $`p_i`$ 为原校准 logistic 参数，$`d_j=\sum_{i\in J_j}p_i(1-p_i)`$，
$`v_j=d_j/B^2`$。校准根为 $`O_{\mathbb P}(q^{-1/2})`$，
而 logistic 方差在零点的一阶导数为零。因此
$`\sup_J|p_i(1-p_i)-1/4|=O_{\mathbb P}(\lambda/q+(q/M)^2+q^{-1})`$。
结合 $`B^2\delta=q/\lambda`$，得到

```math
\max_{j\in\mathcal C_Q}
 \left|\frac{v_j}{\delta\rho(x_j)}-1\right|
 =O_{\mathbb P}\bigl(Q^{-3/2}(1+\log Q)^{3/2}\bigr),
\qquad \min_{j\in\mathcal C_Q}d_j\ge q^{9/10}
```

式 (56.8)。

其中最后一个不等式在概率趋一的环境上成立。
固定截断上的全局 Poisson 包络为：两坐标均大于各自均值一半时，
$`m_j/B^2\le C\delta e^{-c x_j^2}`$；其余位置至多为
$`CQ^{5/2}e^{-c\lambda}`$。
因为 $`v_j\le C_j/(4B^2)`$，增大固定 $`K`$ 即可使

```math
\mathbb E\sum_{|x_j|>H_Q}(1+|x_j|)^m v_j=O(Q^{-100}),
\qquad 0\le m\le4.
```

式 (56.9)。

故这些尾质量在概率趋一的环境上均不超过 $`Q^{-60}`$。
同时 $`V_M=\sum_jv_j\to\gamma`$、$`|J|/B^2\to4\gamma`$，
选中标签总方差 $`d_J=O_{\mathbb P}(B^2)=o_{\mathbb P}(q)`$。

下面保留足以承受放大的精确中心误差。
给定数据，令 $`\mathsf Q_M`$ 是参数为 $`p_i`$ 的独立 Bernoulli 标签律；
条件于标签总数为 $`q`$ 后，它恰为完整支持后验。
Siripraparat–Neammanee 的 Bernoulli 局部极限定理
（文献条件见 [Library 归因](../../../Library/Dynamics/iyer2025empirical.md)）
对总数和补集给出

```math
d_{\rm TV}(\mathsf P_J,\mathsf Q_J)
 \le C(d_J/q+q^{-1/2})=o_{\mathbb P}(1).
```

式 (56.10)。

补集方差至少为 $`cq`$，且因 $`|J|=o_{\mathbb P}(q)`$，涉及的条件计数合法。
更精确地，若 $`\pi_i`$ 是原精确后验边缘，任意数据可测 Hilbert 系数满足

```math
\left\|\sum_{i\in J}f_i(\pi_i-p_i)\right\|
 \le C\left(\sum_{i\in J}p_i(1-p_i)\|f_i\|^2\right)^{1/2}\alpha_M,
\qquad
\alpha_M=\frac{d_J+\sqrt{d_J}}q+q^{-1/2}
 =O_{\mathbb P}(Q^{-5/2}+q^{-1/2}).
```

式 (56.11)。

为验证此加强，局部定理把条件密度比写成
$`\sqrt{d_{\rm all}/d_O}\exp(-(k-\mu_J)^2/(2d_O))+O(q^{-1/2})`$。
设 $`F=\sum f_i(\zeta_i-p_i)`$、$`S=\sum_J(\zeta_i-p_i)`$。
减掉常数项后以 Cauchy–Schwarz 控制
$`q^{-1}\mathsf E(\|F\|S^2)+q^{-1/2}\mathsf E\|F\|`$，
使用 $`\mathsf ES^4\le3d_J^2+d_J`$ 即得 (56.11)。
这也证明向量形式，不只是逐个标量中心的界。

记 $`X_j=B^{-1}\sum_{J_j}(\zeta_i-p_i)`$。
精确组中心与乘积中心之差的 $`\ell^2`$ 范数至多为
$`C\sqrt{V_M}\alpha_M`$。
在整个计数截断上，零对角矩阵

```math
K_{R,t}(j,k)=2\sqrt{Re^t}\,\mathrm{Ci}(\omega Re^t|x_j-x_k|),\qquad j\ne k,
\qquad
\sup_{t\in I}\|K_{R,t}\|_{\rm op}
 \le C_I\sqrt R\,Q^2(1+\log Q)
```

式 (56.12)。

由组数界及 Ci 的小参数对数、大参数倒数包络即得此粗界。
因 $`R\delta\to0`$ 蕴含最终 $`R\le Q^{1/2}`$，
且 $`\mathsf E\|X\|_2^2=V_M`$，改变整个路径中心的条件概率误差趋零，其系数为

```math
\sqrt R\,Q^2(1+\log Q)\alpha_M
 =O_{\mathbb P}\bigl(Q^{-1/4}(1+\log Q)\bigr)+o_{\mathbb P}(1).
```

式 (56.13)。

旧截距和二次坐标分别用 $`Q^2(1+\log Q)\alpha_M`$ 与
$`\delta^{-1/2}\alpha_M`$ 控制。
轮廓所有前缀直接在 (56.11) 取子集指标，偶极子取标记系数。

有限谱恒等式在放大之前使用。
设 $`z=s_M+t`$、$`n=\lfloor e^z/h\rfloor`$，
$`E_M(z)=\sum_{|k|\le n}(1+k^2)^{-1/2}|\widehat\mu_M(k)|^2`$。
由于 $`\mathcal Q_M=V_M+\sqrt\delta T_M`$，花括号内精确等于
$`E_M(z)-2\mathfrak L Y_M^2-2z\mathcal Q_M-\mathcal J_M`$。
应用 (54.8) 及可和权重修正，零距离核为
$`2\mathfrak L+2z+b_*+O_I(h/R)`$，非零距离核为
$`2\mathfrak L+H(x_j,x_k)+2\mathrm{Ci}(\omega e^z|x_j-x_k|)+O_I(\varepsilon_Q)`$，其中

```math
\varepsilon_Q\le C_I\{h\sqrt\lambda(1+\log Q)
          +h^2\lambda(1+\mathfrak L+\log\lambda)+h/R\}.
```

式 (56.14)。

取整改变对数参数至多 $`C_Ih/R`$，而 Ci 对对数参数的导数为余弦，故同一界控制取整。
由 $`(\sum_j|A_j|)^2\le CQ^2\sum_jA_j^2`$，

```math
\sup_{t\in I}\left|\mathcal U_M(t)
          -\sum_{j\ne k}K_{R,t}(j,k)A_jA_k\right|
 \le C_I\sqrt R\,Q^2\varepsilon_Q\|A\|_2^2=o_{\mathbb P}(1).
```

式 (56.15)。

$`h`$ 在 $`Q^3`$ 尺度指数小，故其系数比任意逆多项式更快趋零；
$`\|A\|_2^2`$ 的紧性由辅助矩、(56.11) 及一次 (56.10) 得到。
原有限谱路径虽有取整跳跃，但在此已一致逼近连续的二次型路径。

现在在一个耦合中同时替换所有核心组。
(56.9) 与 (56.12) 先使删去非核心组的全部路径误差趋零；
例如尾向量条件二阶矩至多 $`Q^{-60}`$，整个矩阵范数至多
$`CQ^{9/4}(1+\log Q)`$。
二次坐标的尾绝对期望至多 $`2\delta^{-1/2}\sum_{\rm tail}v_j`$。
线性前缀和偶极子用组数与最大标记的多项式界，亦同时趋零。

对每个核心 Bernoulli 和，局部点概率误差为 $`C/d_j`$。
在标准化坐标 $`[-d_j^{1/6},d_j^{1/6}]`$ 内只有
$`O(d_j^{2/3})`$ 个格点；外面用 Chebyshev，得

```math
\sup_x\left|\mathsf Q_M\{BX_j/\sqrt{d_j}\le x\}-\Phi(x)\right|
 \le C d_j^{-1/3}.
```

式 (56.16)。

取独立均匀变量，以逆分布函数同时生成各标准化组和及标准正态 $`g_j`$。
所有均匀变量落在 $`[q^{-1/16},1-q^{-1/16}]`$ 的补事件概率
至多为 $`2|\mathcal C_Q|q^{-1/16}`$。
在此区间稍作扩张后，逆正态导数至多为 $`Cq^{1/16}`$。
由 $`d_j\ge q^{9/10}`$ 得，最终在该共同事件上

```math
\max_{j\in\mathcal C_Q}|BX_j/\sqrt{d_j}-g_j|\le q^{-1/8},\qquad
\|X-(\sqrt{v_j}g_j)_j\|_2\le q^{-1/8}\sqrt{V_M}.
```

式 (56.17)。

这是离散与连续变量的概率耦合，不是两种分布的总变差趋零。
所有有关系数范数只按 $`Q`$ 多项式增长，故一个向量耦合同时替换
增长频率路径、旧截距、二次坐标及全部旧线性路径。

再令 $`I_j=[(j-1/2)\delta,(j+1/2)\delta)`$、
$`m_j^\circ=\int_{I_j}\rho(x)\,dx`$、$`G_j=\sqrt{m_j^\circ}g_j`$。
格心对称 Taylor 展开及 (56.8) 给出

```math
\max_{j\in\mathcal C_Q}|v_j/m_j^\circ-1|
 =O_{\mathbb P}(Q^{-1}(1+\log Q)).
```

式 (56.18)。

核心矩阵只有 $`O(Q^{1/2}\sqrt{\log Q})`$ 行，
故 (56.12) 在核心改善为 $`O_I(Q^{3/4}(1+\log Q)^{3/2})`$。
与 (56.18) 相乘，改变 Gaussian 方差的整个路径误差为
$`O_{\mathbb P}(Q^{-1/4}(1+\log Q)^{5/2})`$，依概率趋零。
二次坐标在两边分别减去对应方差，其误差系数是
$`\delta^{-1/2}Q^{-1}(1+\log Q)`$，同样趋零。
至此未要求 $`R\delta`$ 以任何指定速率趋零。

在同一个 $`W_\rho`$ 上实现 $`G_j=W_\rho(1_{I_j})`$。
令 $`f_a(z)=2\mathrm{Ci}(a|z|)`$，并采用
$`\widehat f(\xi)=\int e^{-i\xi z}f(z)\,dz`$ 的 Fourier 约定。
先截断频率再取 $`L^2`$ 极限，得到经典恒等式

```math
\widehat f_a(\xi)=-\frac{2\pi}{|\xi|}1_{\{|\xi|\ge a\}},\qquad
\int_{\mathbb R}f_a(z)f_b(z)\,dz=\frac{4\pi}{\max(a,b)}.
```

式 (56.19)。

不需要且不声称 Ci 绝对可积。
记 $`q_{R,t}(x,y)=\sqrt{Re^t}f_{\omega Re^t}(x-y)`$。
在不同核心格 $`I_j\times I_k`$ 上把它取为格心值，
在相同格及核心外置零，所得核记作 $`q^\delta_{R,t}`$。
于是参考过程和参考二次坐标分别是

```math
\mathcal U_Q^G(t)=I_2(q^\delta_{R,t}),\qquad
T_Q^G=\delta^{-1/2}\sum_{j\in\mathcal C_Q}(G_j^2-m_j^\circ).
```

式 (56.20)。

实际网格上的零对角不可忽略而不作估计。
对 $`r=R\delta\to0`$，有

```math
\sup_{t\in I}\|q^\delta_{R,t}-q_{R,t}\|_{L^2(\rho\otimes\rho)}^2
 \le C_I r(1+|\log r|^2)+C_Ie^{-cH_Q^2}.
```

式 (56.21)。

证明此估计时先用 Gaussian 格质量的卷积界
$`\sum_jm_j^\circ m_{j+k}^\circ\le C\delta e^{-c(k\delta)^2}`$。
相同格和邻格的连续核平方积分不超过
$`CR\int_0^{3\delta}(1+|\log(Rz)|^2)\,dz`$，
邻格的采样值用同一格质量界，均受第一项控制。
对相距 $`m\ge2`$ 格的位置，格心距离与真实距离相差至多 $`\delta`$，而

```math
\left|\frac{d}{dz}\{\sqrt{Re^t}f_{\omega Re^t}(z)\}\right|
 \le C_I\sqrt R/|z|.
```

式 (56.22)。

该格的平方误差至多 $`C_IR/m^2`$；求和后为
$`C_IR\delta\sum_{m\ge2}m^{-2}`$。
核心外至少一个坐标绝对值超过 $`H_Q-\delta`$，
从其 Gaussian 密度提取 $`e^{-cH_Q^2}`$ 后，
余下卷积密度有界，(56.19) 使归一化核的平方积分一致有界。
这证明 (56.21)，包括被删除的同格区域。

在 $`L^2(\rho dx)`$ 上记相应核算子为 $`T_q`$。
乘以 $`\sqrt\rho`$ 后，连续算子化为有界权重夹住的 Fourier 乘子。
(56.19) 给出 $`\|T_{q_{R,t}}\|_{\rm op}\le C_IR^{-1/2}`$，于是

```math
\sup_{t\in I}\|T_{q^\delta_{R,t}}\|_{\rm op}
 \le C_I\{R^{-1/2}+\sqrt r(1+|\log r|)+e^{-cH_Q^2/2}\}
 \longrightarrow0.
```

式 (56.23)。

令 $`g(z)=\int\rho(x)\rho(x-z)\,dx=g_0e^{-\kappa z^2/4}`$。
在连续核内积中换元 $`z=y/R`$，以 Ci 乘积的绝对可积性作支配收敛，
再用 (56.19)、$`\omega=\pi/2`$ 及 (56.21)，得

```math
2\langle q^\delta_{R,t},q^\delta_{R,v}\rangle
 \longrightarrow \frac{8\pi g_0}{\omega}e^{-|t-v|/2}
 =16g_0e^{-|t-v|/2}.
```

式 (56.24)。

还须在离散网格上直接证明紧性。
对 $`0\le d\le1`$，积分表达式和一次分部积分分别给出

```math
|\mathrm{Ci}(ze^d)-\mathrm{Ci}(z)|
 \le C\min(d,z^{-1}),\qquad z>0.
```

式 (56.25)。

由格质量卷积界，过程增量的二阶矩至多为常数乘
$`\delta\sum_{k\ne0}|\sqrt{Re^t}f_{\omega Re^t}(k\delta)
-\sqrt{Re^v}f_{\omega Re^v}(k\delta)|^2`$。
设 $`t\le v`$、$`d=v-t`$、$`r_t=Re^t\delta`$。
用 Ci 对数及倒数包络，有
$`r_t\sum_{k\ne0}\mathrm{Ci}(\omega r_t|k|)^2\le C`$，
所以振幅因子变化贡献至多 $`Cd^2`$。
其余项由 (56.25) 及在 $`k=(r_td)^{-1}`$ 处分割求和得到

```math
r_t\sum_{k\ge1}\min\{d^2,(r_tk)^{-2}\}\le Cd,
\qquad
\mathbb E|\mathcal U_Q^G(t)-\mathcal U_Q^G(v)|^4
 \le C_I|t-v|^2.
```

式 (56.26)。

最后一步使用第二混沌四阶矩不超过二阶矩平方的十五倍。
大于一的增量由固定紧区间上的有界方差处理。
连续参考路径因而满足一致 Kolmogorov 紧性判据。
这一步单独证明过程紧性；逐点的 (56.21) 本身不承担该结论。

最后识别联合 Gaussian 极限及与整个旧噪声的独立性。
在正交格基 $`e_j=1_{I_j}/\sqrt{m_j^\circ}`$ 下，
$`T_Q^G=I_2(D_Q)`$，其中

```math
\begin{aligned}
D_Q&=\sum_{j\in\mathcal C_Q}\frac{m_j^\circ}{\sqrt\delta}\,e_j\otimes e_j,\\
\|T_{D_Q}\|_{\rm op}&\le C\sqrt\delta\longrightarrow0,\qquad
2\|D_Q\|_{\rm HS}^2=2\delta^{-1}\sum_{j\in\mathcal C_Q}(m_j^\circ)^2
 \longrightarrow\nu_2,\\
\langle D_Q,q^\delta_{R,t}\rangle&=0.
\end{aligned}
```

式 (56.27)。

最后一个等式是严格的同格对角与异格非对角正交。
对有限个时刻的核与 $`D_Q`$ 的任意固定实线性组合，
算子范数趋零，Hilbert–Schmidt 范数平方有极限。
若其特征值是 $`\lambda_{Q,j}`$，Gaussian 平方的特征函数展开给出

```math
\log\mathbb E e^{iz I_2(K_Q)}
 =-z^2\sum_j\lambda_{Q,j}^2
  +O_z\left(\max_j|\lambda_{Q,j}|\sum_j\lambda_{Q,j}^2\right).
```

式 (56.28)。

有限秩时由独立中心正态平方直接计算，一般情形再取 $`L^2`$ 逼近。
此式与 Cramér–Wold 先证明联合 Gaussian 性，
然后才由 (56.27) 的零协方差推出 $`\mathcal U`$ 与 $`N_2`$ 独立。
退化线性组合由方差趋零处理。

若 $`P`$ 是固定有限秩正交投影，$`P^\perp=1-P`$，则

```math
\|T-P^\perp TP^\perp\|_{\rm HS}
 \le2\sqrt{\operatorname{rank}P}\,\|T\|_{\rm op}.
```

式 (56.29)。

所以从上述每个核中删除所有触及 $`P`$ 的分量只产生趋零的 $`L^2`$ 误差。
剩下的二重积分只依赖正交补噪声，独立于 $`P`$ 中原有 Gaussian 坐标。
令有限秩投影递增到恒等，任意旧噪声的有界可测测试可用其有限柱条件期望
在 $`L^1`$ 中逼近，得到相对于整个 $`\sigma(W_\rho)`$ 的 mixing 收敛。
结合 (56.26) 和有理时刻识别，结论适用于整个紧区间过程。
这里的 mixing 是联合有界测试的因子分解，
不是给定整个 Gaussian 噪声后条件分布趋于非退化常数律。

同一噪声上的旧参考轮廓是 $`W_\rho`$ 作用于连续格并集；
格端点与所需位置相差至多 $`\delta/2`$，原轮廓是连续时间变换 Brownian motion，
故在每个固定紧区间上一致依概率收敛。
端点及分段常数标记的偶极子在 $`L^2`$ 收敛，桥由相同确定投影得到。
旧对数核 $`H`$ 的异格采样满足

```math
\|H_Q^\circ-H\|_{L^2(\rho\otimes\rho)}^2
 \le C\delta(1+|\log\delta|^2)+o(1),\qquad
\sum_{j\in\mathcal C_Q}G_j^2\longrightarrow\gamma\quad\hbox{于 }L^2.
```

式 (56.30)。

第一式重复 (56.21) 的同格、邻格、远格划分而不含增长频率；
远端由 Gaussian 对数包络控制。
第二式的方差为 $`2\sum_j(m_j^\circ)^2=O(\delta)`$。
因此旧截距在同一空间收敛到 $`b_*\gamma+I_2(H)`$，
其与旧线性对象的关系由共同实现保留，且与新联合对象独立。

上述确定 Gaussian 参考律不依赖观测数据。
从任意子列取进一步子列，使环境估计及其条件概率误差几乎处处成立，
逐个环境应用共同耦合与参考极限，便得条件有界 Lipschitz 收敛；
子列原理将它还原为依数据概率的结论。
最后以 (56.10) 对完整选中向量作一次比较。
总变差在映到全部路径和坐标的可测映射下收缩，
故只需转移概率和有界测试，不必转移任何辅助无界矩。
所有固定基数支持在正奇偶类置换作用下属于同一轨道，
两种实际实验及整个统计量均等变，故无条件律等于先验混合律，
得到固定支持一致性。
在原共同方向正确事件上所有坐标逐样本等于对齐版本；
其补集概率 $`O(q^{-1})`$ 只作为有界测试误差。
(56.15)、(56.26) 与上述一致概率逼近同时给出实际路径的 C-tight 性。
这完成 (56.3)。

该证明允许例如 $`R_M\delta=1/\log\log Q`$；
关键平方核误差 $`r(1+|\log r|^2)`$ 仍趋零。
本定理的量词是每个确定性序列和每个固定紧区间，
不包含数据自适应频率、增长的 $`I`$ 或 $`R_M\delta`$ 趋于正数的情形。

## 追加锚（本行以下为增补区）

## 57. 临界谱网格、共振及跨尺度独立性

**定义 57.1（临界网格过程）。** 保持定义 54.1 的原始模型和有限截距，
固定 $`\varrho\in(0,\infty)`$，取确定性序列

```math
s_M\longrightarrow\infty,\qquad
r_M=e^{s_M}\delta\longrightarrow\varrho,
\qquad
\mathcal U_M^{\rm cr}(t)=e^{(s_M+t)/2}
 \{\mathcal Z_M((s_M+t)\sqrt\delta)-\mathcal J_M
                       -2(s_M+t)\sqrt\delta\,T_M\}.
```

式 (57.1)。

参数 $`\varrho`$ 表示网格尺度，与固定信号幅度不同。
在独立于旧 $`(N_2,W_\rho)`$ 的标准正态序列 $`(\xi_k)_{k\ge1}`$ 上定义

```math
G_\varrho(t)=4\sqrt{\varrho g_0}\,e^{t/2}
       \sum_{k\ge1}\mathrm{Ci}(\omega\varrho e^t k)\xi_k,
\qquad g_0=\int\rho^2,\quad\omega=\pi/2.
```

式 (57.2)。

级数先按均方定义，再取下面证明的连续版本。
所有 $`\varrho>0`$ 共用这一个序列。

**定理 57.2（两种实际实验的临界网格律）。** 对每个固定紧时间区间 $`I`$，
两种原始平稳实验都满足

```math
(\mathcal U_M^{\rm cr}|_I,T_M,\mathcal J_M,Y_M,
 L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip})
\Longrightarrow
(G_\varrho|_I,N_2,\mathcal J_\infty,Y,
 L|_{[-A,A]},C|_{[-A,A]},Z),\qquad A>0.
```

式 (57.3)。

路径取紧区间 $`J_1`$ 拓扑且为 C-tight；
旧坐标保持定理 56.2 的共同来源。
新过程独立于整个联合对象 $`(N_2,W_\rho)`$，协方差是

```math
C_\varrho(t,u)=16\varrho g_0e^{(t+u)/2}
 \sum_{k\ge1}\mathrm{Ci}(\omega\varrho e^t k)
                  \mathrm{Ci}(\omega\varrho e^u k).
```

式 (57.4)。

条件先验、无条件固定支持一致性和共同方向事件保持定理 56.2 的范围。
同时改变两个方差中心时放大余项仍逐样本相同。

证明。这里 $`e^{s_M}\le C\delta^{-1}`$，
且谱曲线的取值点最终落在任意固定正外区间内。
第 56 章从实际占用到同一个 Gaussian 格向量的误差估计
(56.5)–(56.18) 只需 $`R\le C\delta^{-1}`$；
其中常数可随此处固定 $`\varrho`$ 和时间紧区间改变。
具体而言，增长核心 $`H_Q=\sqrt{K\log Q}`$ 上的方差相对误差仍为
$`O_{\mathbb P}(Q^{-3/2}(1+\log Q)^{3/2})`$，
最小组方差至少 $`q^{9/10}`$，非核心加权方差质量可取至多 $`Q^{-60}`$。
完整截断上矩阵范数至多 $`CQ^{9/4}(1+\log Q)`$，
故放大后的精确中心误差、共同逆分布耦合误差、有限 Fourier 取整误差
及核心外误差全部趋零。
格质量替换的核心误差仍为 $`O_{\mathbb P}(Q^{-1/4}(1+\log Q)^{5/2})`$。
这些步骤联合保留旧截距、二次坐标和线性路径。

因此只需研究同一格向量 $`G_j=W_\rho(1_{I_j})`$ 的二次型。
记 $`m_j^\circ=\int_{I_j}\rho`$，核心外将此质量置零，并令
$`h_Q(k)=\delta^{-1}\sum_jm_j^\circ m_{j+k}^\circ`$。
Gaussian 密度的格和给出

```math
0\le h_Q(k)\le C\quad(k\in\mathbb Z),\qquad
h_Q(k)\longrightarrow g_0\quad\hbox{对每个固定 }k.
```

式 (57.5)。

前者也由 $`\max_jm_j^\circ\le C\delta`$ 与质量总和有界得到；
后者是固定间距 $`k\delta\to0`$ 下的 Riemann 和，核心外由 Gaussian 尾移除。
在独立标准正态格坐标下，参考矩阵的非对角元为

```math
(A_Q(t))_{jl}=2\sqrt{r_M/\delta}\,e^{t/2}
 \mathrm{Ci}(\omega r_Me^t|j-l|)\sqrt{m_j^\circ m_l^\circ},
\qquad (A_Q(t))_{jj}=0.
```

式 (57.6)。

Wick 恒等式于是给出

```math
2\operatorname{tr}(A_Q(t)A_Q(u))
 =8r_Me^{(t+u)/2}\sum_{k\ne0}
    \mathrm{Ci}(\omega r_Me^t|k|)
    \mathrm{Ci}(\omega r_Me^u|k|)h_Q(k).
```

式 (57.7)。

因为 $`r_M`$ 保持在正的紧区间内，Ci 的倒数包络将每个求和项
一致控制在 $`C_I/k^2`$ 之下。
(57.5) 与支配收敛证明 (57.4)，其中两个距离方向产生额外的因子二。
采样核此时保留离散间距，所以不需要连续核近似。

同一倒数界还给出

```math
|(A_Q(t))_{jl}|\le \frac{C_I\sqrt\delta}{|j-l|},\qquad
\sup_{t\in I}\|A_Q(t)\|_{\rm op}
 \le C_I\sqrt\delta(1+\log|\mathcal C_Q|)\longrightarrow0.
```

式 (57.8)。

这是真正的算子范数控制；仅有逐行方差小不能排除一个存活的大特征值。
二次坐标的格矩阵 $`D_Q`$ 仍满足 (56.27)，
且 $`\operatorname{tr}(A_Q(t)D_Q)=0`$ 严格成立。
对任意有限时刻及 $`D_Q`$ 的混合线性组合应用 (56.28)，
先得联合 Gaussian 极限，再由交叉协方差为零推出与 $`N_2`$ 的独立性。
(56.29) 的有限秩删除论证同时使这个联合对象独立于整个旧 $`W_\rho`$。
(56.30) 又在同一个空间识别 $`\mathcal J_\infty`$，
故旧非 Gaussian 截距不需重新抽取。

紧性直接从整数距离级数获得。
对 $`c`$ 在正的紧集内，置
$`q_{c,k}(t)=e^{t/2}\mathrm{Ci}(\omega ce^t k)`$。
在固定时间紧集上，$`|q_{c,k}|\le C_I/k`$、$`|q'_{c,k}|\le C_I`$，故

```math
|q_{c,k}(t)-q_{c,k}(u)|\le C_I\min\{|t-u|,k^{-1}\},\qquad
\sum_{k\ge1}|q_{c,k}(t)-q_{c,k}(u)|^2\le C_I|t-u|.
```

式 (57.9)。

最后一式在 $`k=|t-u|^{-1}`$ 处分割求和，
对任意小的时间间距都成立，不要求时间格。
(57.5)、二次型等距式与第二混沌四阶界遂给出参考路径的
二阶增量 $`C_I|t-u|`$ 和四阶增量 $`C_I|t-u|^2`$。
Kolmogorov 判据给出连续参考路径的紧性。
同一增量计算应用于 (57.2)，证明该 Gaussian 级数有连续版本。
不能把级数逐项求导后要求导数平方可和，因为余弦项不满足该条件。

共同向量耦合给出整个紧区间的一致概率逼近。
最后以一次完整后验向量比较转移有界测试和紧性事件；
坏环境、计数截断及方向错误只按概率移除。
条件数据子列论证和支持置换等变性与定理 56.2 相同。
由一致逼近可知原始取整路径的跳幅趋零，得到 (57.3) 的 C-tight 性。
上述论证没有转移实际后验无界矩。

**定理 57.3（同一临界过程族的连续极限与共振）。** 以同一正态序列实现的
连续过程可以选为满足

```math
G_\varrho(t+c)=G_{\varrho e^c}(t),\qquad
C_\varrho(t+c,u+c)=C_{\varrho e^c}(t,u).
```

式 (57.10)。

当 $`\varrho\downarrow0`$ 时，$`G_\varrho|_I`$ 在每个 $`C(I)`$ 中趋于
协方差为 (56.4) 的平稳 OU 过程；该收敛相对于
$`\sigma(\xi_1,\xi_2,\ldots)`$ 是 mixing。
每个固定正 $`\varrho`$ 的全实轴过程则非平稳。
置 $`V(z)=C_z(0,0)`$，当 $`z\to\infty`$，令
$`\theta=\omega z\bmod\pi\in[0,\pi)`$，则一致地有

```math
V(z)=\frac{8g_0}{\omega^2z}\theta(\pi-\theta)+O(z^{-2}).
```

式 (57.11)。

在精确共振 $`\omega z\in\pi\mathbb Z`$ 上，更强地有

```math
V(z)=\frac{16g_0\zeta(4)}{\omega^4z^3}+O(z^{-5}).
```

式 (57.12)。

这些 $`z`$ 渐近结论描述已识别的 Gaussian 过程族，不改变实际定理 (57.3)
要求网格比例趋于固定正数的量词。

证明。先在有理参数上由级数逐项核对 (57.10)，
再用 $`G_\varrho(t)=G_1(t+\log\varrho)`$ 选择所有连续版本。
对固定时间紧集，Ci 乘积近零由 $`C(1+|\log|x||)^2`$ 控制，
远处由 $`C/x^2`$ 控制；环带上关于空间与时间一致连续。
删去中心小带和远尾后用一致 Riemann 和，再恢复它们，得

```math
\varrho\sum_{k\ne0}
 \mathrm{Ci}(\omega\varrho e^t|k|)\mathrm{Ci}(\omega\varrho e^u|k|)
 \longrightarrow
 \int_{\mathbb R}\mathrm{Ci}(\omega e^t|x|)
                 \mathrm{Ci}(\omega e^u|x|)\,dx
 =\frac{\pi}{\omega e^{\max(t,u)}}.
```

式 (57.13)。

最后一个恒等式是 (56.19) 的同一 $`L^2`$ Fourier 计算。
因此协方差一致趋于 $`16g_0e^{-|t-u|/2}`$。
紧性不能直接套 (57.9) 中依赖正下界的常数；
改用 (56.25) 及归一化格和
$`r\sum_k\min\{d^2,(rk)^{-2}\}\le Cd`$，
便得对 $`0<\varrho\le1`$ 一致的二阶增量 $`C_I|t-u|`$。
Gaussian 四阶矩和 Kolmogorov 判据补上 $`C(I)`$ 收敛。
对每个固定 $`k`$，(57.2) 的系数是
$`O_I(\sqrt\varrho(1+|\log\varrho|))\to0`$。
因而新路径与任意有限组 $`\xi_k`$ 的交叉协方差趋零，
联合 Gaussian 性先给出与有限柱的独立极限；
对整个序列的有界可测测试作 $`L^1`$ 柱条件期望逼近，得到 mixing。

由 (57.13)，$`V(z)\to16g_0`$ 当 $`z\downarrow0`$；
倒数包络则给出 $`V(z)\le C/z\to0`$ 当 $`z\to\infty`$。
所以 $`C_\varrho(t,t)=V(\varrho e^t)`$ 在全实轴上不恒定。
此结论不要求方差在每个小区间严格单调。

两次分部积分给出
$`\mathrm{Ci}(x)=\sin x/x-\cos x/x^2+O(x^{-3})`$，$`x\ge1`$。
在 (57.4) 的方差级数中逐项平方，余项由可和的 $`k^{-3}`$、$`k^{-4}`$ 控制，得
$`V(z)=16g_0(\omega^2z)^{-1}\sum_{k\ge1}\sin^2(\omega zk)/k^2+O(z^{-2})`$。
经典 Bernoulli 多项式 Fourier 级数给出
$`\sum_{k\ge1}\sin^2(k\theta)/k^2=\theta(\pi-\theta)/2`$，
即 (57.11)，其误差在相位上一致。
在精确共振上正弦项全消；再作两次分部积分，得
$`\mathrm{Ci}(\omega zk)=-\cos(\omega zk)/(\omega zk)^2+O((zk)^{-4})`$。
平方求和即 (57.12)。不能用 (57.11) 的绝对误差在接近共振时直接推出等价式。

**定理 57.4（同一实际数据的两个分离谱尺度）。** 在同一个完整后验标签向量上，
分别取确定性序列

```math
R_M^{\rm lo}\longrightarrow\infty,\quad
r_M^{\rm lo}=R_M^{\rm lo}\delta\longrightarrow0,
\qquad R_M^{\rm cr}\delta\longrightarrow\varrho\in(0,\infty),
```

式 (57.14)。

以 (56.2) 的同一公式构造两个放大余项。
在各自固定紧时间区间上，两个过程与全部旧坐标联合收敛到
$`(\mathcal U,G_\varrho,N_2,W_\rho)`$ 所决定的对象，
其中 $`\mathcal U`$、$`G_\varrho`$、$`N_2`$ 三者相互独立，
且联合独立于整个旧 $`W_\rho`$。
条件先验、无条件支持一致性及方向范围与定理 57.2 相同。

证明。用同一增长核心、同一组均匀变量和同一格 Gaussian 向量，
同时进行第 56 章及定理 57.2 的实际误差替换。
有限个过程的误差仍一致依概率趋零，两个边缘的紧性给出乘积紧性。
剩下的义务是混合协方差，而不是再拼接两个边缘极限。
写 $`r=r_M^{\rm lo}`$。由 (57.5) 和临界 Ci 的倒数包络，
两个 Gaussian 二次型的交叉协方差绝对值至多为

```math
C\sqrt r\sum_{k\ge1}\frac{|\mathrm{Ci}(\omega r e^t k)|}{k}
 \le C\sqrt r(1+|\log r|^2)\longrightarrow0,
```

式 (57.15)。

常数在两个时间紧区间上一致。
对 $`k\le1/r`$ 使用对数包络，调和求和给出 $`O(1+|\log r|^2)`$；
对 $`k>1/r`$ 用倒数包络，余和为 $`O(1)`$。
所有低频与临界矩阵的算子范数分别由 (56.23)、(57.8) 趋零，
混合有限线性组合也如此。
其与 $`D_Q`$ 的内积均为零。
所以 (56.28) 对全部混合组合证明联合 Gaussian 性，
然后 (57.15) 和对角正交给出三者相互独立。
有限秩删除和旧核逼近保留与整个旧噪声的联合独立性。
最后仍只对完整原后验向量作一次总变差比较，得到实际联合结论。

## 追加锚（本行以下为增补区）

## 58. 超临界谱网格的微观 Brownian bridge

**定义 58.1（微观相位曲线）。** 保持定义 54.1 的原始模型、完整得分组、
精确标签中心和有限截距，固定 $`U>0`$。取确定性序列

```math
s_M\longrightarrow\infty,\qquad R_M=e^{s_M},\qquad
\eta_M=R_M\delta\longrightarrow\infty,\qquad
0\le s_M\sqrt\delta\le U/2,
\qquad \omega\eta_M\bmod 2\pi\longrightarrow\phi
```

式 (58.1)。

最后的收敛取圆周拓扑；$`\phi`$ 是给定的确定性子列相位，
不假设这些相位的分布。这里 $`\eta_M`$ 表示谱网格，不是 Liouville 逼近误差。
对固定紧区间 $`I=[\theta_0,\theta_1]`$，令

```math
z_M(\theta)=s_M+\theta/\eta_M,\qquad
u_M(\theta)=z_M(\theta)\sqrt\delta,
\qquad
\mathcal V_M(\theta)=\sqrt{\eta_M}\,e^{z_M(\theta)/2}
 \{\mathcal Z_M(u_M(\theta))-\mathcal J_M-2u_M(\theta)T_M\}.
```

式 (58.2)。

这些取值点最终都在 $`[0,U]`$ 内。
在独立于旧联合对象 $`(N_2,W_\rho)`$ 的标准正态序列 $`(\xi_k)_{k\ge1}`$ 上，
先按均方定义

```math
S(a)=\sum_{k\ge1}\frac{\sin(ka)}k\xi_k,\qquad
\mathcal V(\theta)=\frac{4\sqrt{g_0}}\omega S(\phi+\omega\theta),
\qquad g_0=\int\rho^2,\quad\omega=\pi/2.
```

式 (58.3)。

**定理 58.2（实际微观桥极限）。** 对 (58.1) 的每个序列，
两种原始平稳实验都满足

```math
(\mathcal V_M|_I,T_M,\mathcal J_M,Y_M,
 L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip})
\Longrightarrow
(\mathcal V|_I,N_2,\mathcal J_\infty,Y,
 L|_{[-A,A]},C|_{[-A,A]},Z),\qquad A>0.
```

式 (58.4)。

路径取紧区间 $`J_1`$ 拓扑且为 C-tight。
旧坐标保持定理 56.2 的共同实现；新过程独立于整个 $`(N_2,W_\rho)`$。
可同时附加旧固定频率紧区间上的 Fourier 场
$`F(v)=W_\rho(e^{-i\omega v\cdot})`$，以及旧负 Sobolev 空间中的测度与偶极子逼近。
收敛具有均匀支持先验下依数据概率成立的条件有界 Lipschitz 版本，
以及无条件固定支持一致版本；未知方向使用同一个判向事件。
同时改变 $`V_M`$ 与 $`T_M`$ 的方差中心仍使 (58.2) 逐样本不变。

$`S`$ 有连续、奇对称、$`2\pi`$ 周期的版本，其部分和在
$`L^2(\Omega;C[0,2\pi])`$ 中收敛。对 $`0\le a,b\le\pi`$，

```math
\operatorname{Cov}(S(a),S(b))
 =\frac\pi2\left(\min(a,b)-\frac{ab}\pi\right).
```

式 (58.5)。

因此 $`S`$ 在 $`[0,\pi]`$ 上等于长度为 $`\pi`$ 的实 Brownian bridge
乘以 $`\sqrt{\pi/2}`$；其余区间由同一条桥奇对称、周期延拓。
不同周期和反射区间不引入独立桥。

证明。全部比较保留同一个实际后验标签向量。
本证明从有限谱恒等式开始，不把增长的 $`\eta_M`$ 代入定理 57.2 的弱极限。
第 56 章的环境估计只涉及实际得分组，不依赖本章所选的谱频率，故仍适用。
在共同计数截断事件上，$`x_j=j\delta`$，组数至多 $`CQ^2`$，
$`|x_j|\le C\sqrt\lambda`$，且 $`\mathfrak L=c_hQ^3+O(1)`$，$`c_h>0`$。
共同事件的补集用概率去除。

先将有限 Fourier 误差保留到新的精度。
对 $`0<\vartheta<1`$，有限和满足

```math
\begin{aligned}
\sum_{k=1}^N\frac{\cos(k\vartheta)}k
 &=-\log\vartheta+\mathrm{Ci}(N\vartheta)
   +O\{N^{-1}+\vartheta[1+\log_+(N\vartheta)]\},\\
\sum_{k\le N}\bigl((1+k^2)^{-1/2}-k^{-1}\bigr)\cos(k\vartheta)
 &=D_{\rm w}+O\{\vartheta^2(1+|\log\vartheta|)+N^{-2}\}.
\end{aligned}
```

式 (58.6)。

第一式把 $`(\cos(\vartheta v)-1)/v`$ 的和与积分比较：
在 $`v\le1/\vartheta`$ 上导数至多 $`C\vartheta^2`$，
在其余区间至多 $`\vartheta/v+2/v^2`$，积分即给出所列误差。
再加入调和和的常数与余项。
第二式用权重差 $`O(k^{-3})`$，在 $`k=1/\vartheta`$ 分割即可。
对 $`N(z)=\lfloor e^z/h\rfloor`$、$`0\le z\le U/\sqrt\delta`$，
代入 $`\vartheta=\omega h|x_j-x_l|`$ 后，非对角核为
$`2\mathfrak L+H(x_j,x_l)+2\mathrm{Ci}(\omega e^z|x_j-x_l|)`$，
对角核为 $`2\mathfrak L+2z+b_*`$，一致误差至多

```math
\varepsilon_M=C\{h+h\sqrt\lambda(1+U/\sqrt\delta+\log\lambda)
                 +h^2\lambda(1+\mathfrak L+\log\lambda)\}.
```

式 (58.7)。

取整改变对数参数至多 $`Che^{-z}`$；
$`d\mathrm{Ci}(v)/d\log v=\cos v`$，故同一界控制 Ci 的取整误差。
共同空间平移消失于 Fourier 模平方。
用 $`\mathcal Q_M=V_M+\sqrt\delta T_M`$，
(58.2) 中括号精确抵消 $`2\mathfrak L Y_M^2`$ 和 $`2z\mathcal Q_M`$。
因为 $`(\sum|A_j|)^2\le CQ^2\mathcal Q_M`$、$`\mathcal Q_M=O_{\mathbb P}(1)`$，
且

```math
\sup_{\theta\in I}\sqrt{\eta_M}e^{z_M(\theta)/2}Q^2\varepsilon_M
 \le \exp\{-c_hQ^3+(U/2)Q^{1/4}+C_I\log Q\}\longrightarrow0,
```

式 (58.8)。

原过程一致逼近连续的非对角二次型。这里的紧性由辅助标签矩、
精确中心界和全向量 TV 对有界尾事件的比较得到，不要求实际后验矩收敛。

对非零整数 $`k`$ 定义

```math
q_{\eta,k}(\theta)=\eta e^{\theta/(2\eta)}
       \mathrm{Ci}(\omega\eta e^{\theta/\eta}|k|),\qquad
b_M(\theta,k)=2\delta^{-1/2}q_{\eta_M,k}(\theta).
```

式 (58.9)。

由 $`|\mathrm{Ci}(v)|\le C/v`$ 及直接微分，
对 $`\eta\ge1`$、$`\theta\in I`$ 一致有

```math
|q_{\eta,k}(\theta)|\le C_I/|k|,\qquad
\partial_\theta q_{\eta,k}(\theta)
 =\tfrac12e^{\theta/(2\eta)}\mathrm{Ci}(\omega\eta e^{\theta/\eta}|k|)
  +e^{\theta/(2\eta)}\cos(\omega\eta e^{\theta/\eta}|k|),
\qquad |\partial_\theta q_{\eta,k}(\theta)|\le C_I.
```

式 (58.10)。

增长的 $`\eta`$ 从核包络中消失。
完整截断上 $`\sup_I\|b_M(\theta)\|_{\rm op}\le C_IQ^{9/4}`$。
记 $`X_j`$ 为乘积标签的中心组和，$`A_j=X_j-e_j`$。
由 (56.11) 得

```math
\sup_I|(X-e)^\top b_M(X-e)-X^\top b_MX|
 \le C_IQ^{9/4}(2\|X\|_2\|e\|_2+\|e\|_2^2)
 =O_{\mathbb P}(Q^{-1/4})+o_{\mathbb P}(1).
```

式 (58.11)。

此处 $`\|e\|_2\le C\sqrt{V_M}\alpha_M`$，
$`\alpha_M=O_{\mathbb P}(Q^{-5/2}+q^{-1/2})`$。
这是放大之后的中心界。

继续使用第 56 章的增长核心 $`\mathcal C_Q`$。
在其好环境上，尾向量条件平方范数期望至多 $`Q^{-60}`$。
上述矩阵范数界使删除核心外所有组的路径误差一致趋零；
它控制的是整个向量二次型之差，故不需要逐时并集。
旧截距、二次坐标、前缀和与偶极子的对应矩阵或系数也只有多项式增长，
同一尾估计同时适用。
核心内 (56.8) 和 (56.16)–(56.17) 的共同逆分布耦合将
$`X_j`$ 换成 $`G_j=\sqrt{v_j}\zeta_j`$，$`\zeta_j`$ 为独立标准正态。
所有标准化组误差同时至多 $`q^{-1/8}`$ 的事件概率趋一。
组数及矩阵范数均只有多项式增长，所以耦合误差在本章放大尺度下一致趋零。
这是概率耦合，不是离散律与连续 Gaussian 律之间的 TV 比较。
保留实际环境方差 $`v_j`$，无需再用粗矩阵界替换它。

在核心外设 $`v_j=G_j=0`$。对固定正整数滞后定义

```math
\Lambda_{M,k}=\delta^{-1/2}\sum_jG_jG_{j+k},\qquad
h_M(k)=\delta^{-1}\sum_jv_jv_{j+k}.
```

式 (58.12)。

由核心上的 $`v_j/\delta\rho(j\delta)\to1`$ 和 Gaussian 尾，
对每个固定 $`k`$，$`h_M(k)\to g_0`$；同时
$`0\le h_M(k)\le C`$ 对所有整数一致成立，因
$`\max v_j\le C\delta`$、$`\sum v_j\le C`$。
$`\Lambda_{M,k}=\zeta^\top B_{M,k}\zeta`$，
其中每个无序对的两个矩阵元均为
$`\sqrt{v_jv_{j+k}}/(2\sqrt\delta)`$。因此

```math
\|B_{M,k}\|_{\rm op}\le C\sqrt\delta,\qquad
2\operatorname{tr}(B_{M,k}B_{M,l})=1_{\{k=l\}}h_M(k).
```

式 (58.13)。

每行至多有两个非零元，且不同正滞后没有共同无序对。
旧对角坐标的矩阵为 $`D_M=\operatorname{diag}(v_j/\sqrt\delta)`$，
其算子范数趋零、方差趋于 $`2g_0`$，与每个 $`B_{M,k}`$ 的内积精确为零。
任意固定线性组合 $`B`$ 满足 $`\|B\|_{\rm op}\to0`$、
$`\operatorname{tr}B^2=O(1)`$，Gaussian 特征函数给出

```math
\log\mathbb E e^{i(\zeta^\top B\zeta-\operatorname{tr}B)}
 =-\operatorname{tr}B^2
    +O(\|B\|_{\rm op}\operatorname{tr}B^2).
```

式 (58.14)。

先得到联合 Gaussian 极限，再由交叉迹为零得独立性。
加入任意范数有界的旧线性系数 $`\ell`$ 时，特征函数额外因子是
$`\exp\{-\tfrac12\ell^\top(I-2iB)^{-1}\ell\}`$，
其指数与 $`-\|\ell\|_2^2/2`$ 之差趋零。
旧线性坐标的 Gram 矩阵由方差钟收敛确定；
端点、偶极子和固定频率 Fourier 场用总质量及 $`x^2`$ 尾控制。
把旧 $`H`$ 核按 (51.9)–(51.10) 的有限矩形块逼近，
块平方和趋于相应确定方差，故同一个旧 $`I_2(H)`$ 也被保留。
近对角对数平方界与远端 Gaussian 界使矩形逼近误差趋零。
由可数稠密线性测试及单调类论证，这证明固定滞后向量的极限

```math
(\Lambda_{M,1},\ldots,\Lambda_{M,K},T_M^G)
 \Longrightarrow(\sqrt{g_0}\xi_1,\ldots,\sqrt{g_0}\xi_K,N_2)
```

式 (58.15)。

右侧全部坐标独立，且联合独立于整个旧 $`W_\rho`$。
旧截距没有换成另一份二次噪声。

现在证明无限滞后尾的路径界。
令 $`\mathscr T_{M,K}(\theta)=4\sum_{k>K}q_{\eta_M,k}(\theta)\Lambda_{M,k}`$。
这是有限的中心 Gaussian 二次型，(58.10)–(58.13) 给出

```math
\begin{aligned}
\mathbb E_G|\mathscr T_{M,K}(\theta)|^2&\le C_I/K,\\
\mathbb E_G|\mathscr T_{M,K}(\theta)-\mathscr T_{M,K}(\psi)|^2
 &\le C_I\sum_{k>K}\min(|\theta-\psi|^2,k^{-2})
 \le C_I\min(|\theta-\psi|,K^{-1}).
\end{aligned}
```

式 (58.16)。

求和在 $`k=|\theta-\psi|^{-1}`$ 分割，适用于任意微小增量。
任意中心 Gaussian 二次型 $`Q`$ 满足
$`\mathbb EQ^4\le15(\mathbb EQ^2)^2`$。
将 $`I`$ 分成 $`O_I(K)`$ 个长度至多 $`1/K`$ 的区间，
网格点最大值的平方期望至多
$`(\sum_{\rm grid}\mathbb E_G|\mathscr T_{M,K}|^4)^{1/2}\le C_IK^{-1/2}`$。
逐级二分，第 $`n`$ 层有 $`O_I(K2^n)`$ 个增量，
最大增量的 $`L^4`$ 范数至多 $`C_IK^{-1/4}2^{-n/4}`$。
Minkowski 不等式和连续性遂给出

```math
\mathbb E_G\sup_{\theta\in I}|\mathscr T_{M,K}(\theta)|^2
 \le C_IK^{-1/2}.
```

式 (58.17)。

它对组数及 $`\eta_M\ge1`$ 一致。
全级数亦有第四增量矩至多 $`C_I|\theta-\psi|^2`$，故连续二次型路径为 C-tight。
以上中心、核心删除和耦合误差界在删去任意滞后时仍成立，
因为相应粗矩阵元界不变。
于是 (58.17) 可通过一次全向量后验比较传给实际过程的有界尾事件。
尤其有

```math
\limsup_M\sup_{|S|=q}\mathbb P_S\!\left(
 \sup_{\theta\in I}\left|\mathcal V_M(\theta)
 -4\sum_{k=1}^Kq_{\eta_M,k}(\theta)
       \delta^{-1/2}\sum_jA_jA_{j+k}\right|>\varepsilon\right)
 \le C_I\varepsilon^{-2}K^{-1/2}.
```

式 (58.18)。

滞后和在共同计数截断事件上取原完整得分组，例外事件可任意定义。
这不是把逐点二阶矩界当作上确界的期望界。

最后识别相位极限。
由 $`\mathrm{Ci}(z)=\sin z/z+O(z^{-2})`$，对每个固定 $`k`$，

```math
q_{\eta_M,k}(\theta)
 =\frac{e^{-\theta/(2\eta_M)}}{\omega k}
   \sin(\omega\eta_Me^{\theta/\eta_M}k)+O_I((\eta_Mk^2)^{-1})
 \longrightarrow\frac{\sin(k(\phi+\omega\theta))}{\omega k}
```

式 (58.19)。

收敛在 $`I`$ 上一致。
只在固定滞后使用 Taylor 展开；不要求它对增长的全部滞后一致。
(58.15) 给出有限滞后截断的联合极限，(58.17)–(58.18) 允许随后令 $`K\to\infty`$。
极限 sine 级数的每个有限尾也满足同样的方差、第四矩及二分估计，故

```math
\mathbb E\sup_{a\in[0,2\pi]}
 \left|\sum_{K<k\le L}\frac{\sin(ka)}k\xi_k\right|^2
 \le CK^{-1/2},\qquad L>K.
```

式 (58.20)。

这证明 $`L^2(\Omega;C)`$ 收敛及连续、奇对称、周期版本。
令 $`D(a)=\sum_{k\ge1}\cos(ka)/k^2`$，其连续偶周期版本在
$`|a|\le2\pi`$ 上为 $`\pi^2/6-\pi|a|/2+a^2/4`$。
绝对收敛和积化和差给出

```math
\operatorname{Cov}(S(a),S(b))=\tfrac12[D(a-b)-D(a+b)],
\qquad
\operatorname{Cov}(\mathcal V(\theta),\mathcal V(\psi))
 =\frac{8g_0}{\omega^2}
  [D(\omega(\theta-\psi))-D(2\phi+\omega(\theta+\psi))].
```

式 (58.21)。

这也证明 (58.5)。系数 $`4`$ 来自 Ci 核的 $`2`$ 与正滞后无序对的两次计数。
协方差一般同时依赖时间差与时间和；在 $`\phi+\omega\theta\in\pi\mathbb Z`$ 时
极限为零，允许这种孤立时刻的退化。

上述所有 Gaussian 替换先在实际数据的好环境上进行。
一次 (56.10) 仅用于整个路径及旧元组的有界测试和误差事件。
环境界依数据概率成立；任意子列再取环境几乎处处收敛的子列，
先固定 $`K`$，再由一致尾界令 $`K\to\infty`$，得到所述条件有界 Lipschitz 收敛。
有限谱路径到连续二次型的距离由 (58.8) 一致控制，所以取整跳跃不妨碍 C-tight 性。
旧轮廓由独立整组跳跃的方差钟和消失的四阶矩和保持紧性；
旧 Fourier 场用 $`\sum_j(1+x_j^2)v_j`$ 的条件 $`H^1`$ 界。
负 Sobolev 测度和偶极子的旧共同实现逼近由相同方差尾保留。
支持置换等变性把先验结论传为每个固定支持的相同无条件律；
共同判向事件补集概率一致趋零，故同样保留联合结论。
这里没有用 TV 传递无界矩，也没有条件于已实现的旧标签噪声。

式 (58.21) 说明相位限定有内容；相位相差 $`\pi`$ 给出相同 Gaussian 律，
因此 (58.1) 的 $`2\pi`$ 相位收敛只是充分条件，不声称必要性。
没有相位收敛时，圆周紧性提供子列，以上证明逐条识别其极限，
但不据此宣称全部子列有同一个律。
本定理不包含随机相位分布、增长的 $`\theta`$ 区间、其它幅度、实际后验矩收敛，
也不去掉 (58.1) 的上方频率限制。
Brownian bridge 的 sine 展开、Gaussian 二次型谱公式和二分连续性方法为经典工具；
文献条件与本模型桥接的范围见 [Library 归因](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（本行以下为增补区）

## 59. 精确共振处的 Gaussian 偏移与共同 Brownian 反射

**定义 59.1（共振微观尺度）。** 保持定义 54.1 的原始模型与有限截距。
取确定性序列，满足

```math
\eta_M\longrightarrow\infty,\qquad
\eta_M^2\delta\longrightarrow0,\qquad
\eta_M=2m_M,\quad m_M\in\mathbb N,
\qquad R_M=\eta_M/\delta,\quad s_M=\log R_M.
```

式 (59.1)。

这等价于精确共振 $`\omega\eta_M=\pi m_M`$，$`\omega=\pi/2`$。
不限制 $`m_M`$ 的奇偶性。
对固定紧区间 $`I\subset\mathbb R`$ 定义

```math
z_M(\theta)=s_M+\theta/\eta_M^3,\qquad
\mathcal R_M(\theta)=\eta_M^{3/2}e^{z_M(\theta)/2}
 \{\mathcal Z_M(z_M(\theta)\sqrt\delta)-\mathcal J_M
                      -2z_M(\theta)\sqrt\delta\,T_M\}.
```

式 (59.2)。

由 (59.1)，最终 $`\eta_M\le Q^{1/4}`$、$`R_M\le Q^{3/4}`$，
所以 $`z_M(\theta)\sqrt\delta`$ 一致趋零且最终为正。

**定理 59.2（完整共振分离范围的实际路径律）。** 对 (59.1) 的每个序列，
两种原始平稳实验均有

```math
(\mathcal R_M|_I,T_M,\mathcal J_M,Y_M,
 L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip})
\Longrightarrow
(\mathcal R|_I,N_2,\mathcal J_\infty,Y,
 L|_{[-A,A]},C|_{[-A,A]},Z),\qquad A>0,
```

式 (59.3)。

路径取紧区间 $`J_1`$ 拓扑且为 C-tight。
令 $`B`$ 是 $`[0,\infty)`$ 上一条标准 Brownian motion，
则新过程可以实现为

```math
\mathcal R(\theta)=Z_0+4\sqrt{g_0}\,B_{\rm odd}(\theta),\qquad
B_{\rm odd}(\theta)=
\begin{cases}B(\theta),&\theta\ge0,\\-B(-\theta),&\theta<0,
\end{cases}
\qquad
Z_0\sim N\left(0,\frac{16g_0\zeta(4)}{\omega^4}\right)
       =N(0,128g_0/45).
```

式 (59.4)。

$`Z_0`$、$`B`$、$`N_2`$ 相互独立，并联合独立于整个旧 $`W_\rho`$。
旧坐标仍为定理 56.2 的共同实现，特别是
$`\mathcal J_\infty=b_*\gamma+I_2(H)`$。
条件先验、无条件固定支持一致性及共同方向事件保持该定理的范围。
两侧的 Brownian 部分来自同一条路径；对每个固定 $`A_0>0`$，

```math
\sup_{0\le\theta\le A_0}
 |\mathcal R_M(\theta)+\mathcal R_M(-\theta)-2\mathcal R_M(0)|
 \longrightarrow0\quad\hbox{依概率}.
```

式 (59.5)。

证明。仍在同一个完整标签向量上比较。
为分析联合路径可先把 $`I`$ 扩到包含零的固定对称紧区间。
(58.6) 的有限谱估计及精确恒等式
$`\mathcal Q_M=V_M+\sqrt\delta T_M`$ 使 (59.2) 的括号等于
$`E_M(z)-2\mathfrak L Y_M^2-2z\mathcal Q_M-\mathcal J_M`$。
定义零对角原始系数矩阵

```math
K_{\eta,\theta}(j,l)=\frac{2\eta^2}{\sqrt\delta}
 e^{\theta/(2\eta^3)}\mathrm{Ci}
       (\omega\eta e^{\theta/\eta^3}|j-l|),\qquad j\ne l.
```

式 (59.6)。

完整计数截断上有限谱误差可取 (56.14) 的形式，因 $`z=O_I(\log Q)`$。
它与 $`\eta^2\delta^{-1/2}Q^2\le Q^{11/4}`$ 的乘积趋零，
因为 $`h`$ 在 $`Q^3`$ 尺度指数小。
于是原路径一致依概率逼近 $`A^\top K_{\eta,\theta}A`$。
取整在此有限恒等式内已受控制，未在旧弱极限中代入增长参数。

先估计真实中心和耦合的成本。
写 $`a_\theta=\omega\eta e^{\theta/\eta^3}`$、
$`\beta_\theta=a_\theta-\pi m=\omega\eta(e^{\theta/\eta^3}-1)`$，
则 $`|\beta_\theta|\le C_I/\eta^2`$。
分部积分给出 $`\mathrm{Ci}(y)=\sin y/y-\cos y/y^2+O(y^{-3})`$。
精确共振下 $`\sin(a_\theta k)=(-1)^{mk}\sin(\beta_\theta k)`$，因此

```math
|K_{\eta,\theta}(j,j+k)|\le C_I\delta^{-1/2}
 \{\min(\eta^{-1},\eta/|k|)+|k|^{-2}\},\qquad k\ne0.
```

式 (59.7)。

在完整截断的 $`O(Q^2)`$ 指标直径上，按 $`|k|=\eta^2`$ 分割调和和，得

```math
\sup_I\|K_{\eta,\theta}\|_{\rm op}
 \le C_I\delta^{-1/2}\{\eta(1+\log Q)+1\}
 \le C_IQ^{1/2}(1+\log Q).
```

式 (59.8)。

这里矩阵作用于原始组和，尚未乘入方差权重。
(56.11) 的精确中心向量界乘上 (59.8) 后，给出一致条件概率误差
$`O_{\mathbb P}(Q^{-2}(1+\log Q))+o_{\mathbb P}(1)`$。
增长核心外向量的平方范数条件期望至多 $`Q^{-60}`$，
所以同一矩阵界也同时去除全部核心外路径项。
旧截距、二次坐标、轮廓和偶极子的多项式范数与尾估计保持适用。

在核心内，用 (56.16)–(56.17) 的同一逆分布耦合，
把乘积标签组和替换为 $`\sqrt{v_j}g_j`$。
$`q^{-1/8}`$ 的共同标准化误差压过上述所有多项式成本。
再令 $`I_j=[(j-1/2)\delta,(j+1/2)\delta)`$，
$`m_j^\circ=\int_{I_j}\rho`$，核心外置零，
并用同一 $`g_j`$ 定义 $`G_j=\sqrt{m_j^\circ}g_j`$。
(56.18) 的相对质量误差为 $`O_{\mathbb P}(Q^{-1}(1+\log Q))`$，
其与 (59.8) 的乘积为
$`O_{\mathbb P}(Q^{-1/2}(1+\log Q)^2)\to0`$。
旧截距在核心上的原始矩阵范数只有
$`O(Q^{1/2}(1+\log Q)^{3/2})`$，亦可作同一替换。
对角坐标两侧各减其对应方差；额外的
$`\delta^{-1/2}Q^{-1}(1+\log Q)`$ 仍趋零。
所以实际整个联合对象被同一确定 Gaussian 格模型逼近。

下面直接分析此模型。令

```math
w_\delta(k)=\delta^{-1}\sum_jm_j^\circ m_{j+k}^\circ,\qquad
\bar\rho_\delta=\sum_{j\in\mathcal C_Q}(m_j^\circ/\delta)1_{I_j},
\qquad g(z)=\int\rho(x)\rho(x+z)\,dx=g_0e^{-\kappa z^2/4}.
```

式 (59.9)。

格平均的 Poincaré 界与 Gaussian 尾给出
$`\|\bar\rho_\delta-\rho\|_2\le C\delta+Ce^{-cH_Q^2}`$。
又 $`w_\delta(k)=\int\bar\rho_\delta(x)\bar\rho_\delta(x+k\delta)\,dx`$，
Cauchy–Schwarz 遂得

```math
0\le w_\delta(k)\le C,\qquad
\sup_{k\in\mathbb Z}|w_\delta(k)-g(k\delta)|
 \le C\delta+Ce^{-cH_Q^2}.
```

式 (59.10)。

这在增长的滞后尺度上仍成立。
方差加权算子的矩阵元是
$`K_{\eta,\theta}(j,l)\sqrt{m_j^\circ m_l^\circ}`$。
取 Schur 权 $`\sqrt{m_j^\circ}`$，其算子范数被
$`\sup_j\sum_l|K_{\eta,\theta}(j,l)|m_l^\circ`$ 控制。
写 $`r=\eta^2\delta\to0`$，按
$`1\le|k|\le\eta^2`$、$`\eta^2<|k|\le\delta^{-1}`$ 和
$`|k|>\delta^{-1}`$ 三段分割。
使用 $`m_j^\circ\le C\delta`$ 与 $`\sum m_j^\circ\le\gamma`$，
(59.7) 第一项在乘 $`\delta^{-1/2}`$ 前分别至多为
$`C\delta\eta`$、$`C\delta\eta(1+|\log r|)`$、$`C\eta\delta`$；
倒数平方项的和至多 $`C\delta`$。
所以加权算子 $`T_{\eta,\theta}`$ 满足

```math
\sup_{\theta\in I}\|T_{\eta,\theta}\|_{\rm op}
 \le C_I\{\sqrt r(1+|\log r|)+\sqrt\delta\}\longrightarrow0.
```

式 (59.11)。

最后一段利用 $`1/|k|\le\delta`$ 和总质量，故核心边缘的行也满足同一界。
此处没有附加 $`r`$ 与 $`\log Q`$ 的收敛条件。

记正滞后系数为

```math
b_{\eta,\theta}(k)=\eta^2e^{\theta/(2\eta^3)}\mathrm{Ci}(a_\theta k),
\qquad
\mathcal R_Q^G(\theta)=4\delta^{-1/2}
 \sum_{k\ge1}b_{\eta,\theta}(k)\sum_jG_jG_{j+k}.
```

式 (59.12)。

不同正滞后的无序指标对不同。Gaussian 二次矩公式因而给出

```math
\operatorname{Cov}(\mathcal R_Q^G(\theta),\mathcal R_Q^G(u))
 =16\sum_{k\ge1}b_{\eta,\theta}(k)b_{\eta,u}(k)w_\delta(k).
```

式 (59.13)。

共振展开更精确地写成

```math
b_{\eta,\theta}(k)=(-1)^{mk}\left\{
 \frac{\eta}{\omega}e^{-\theta/(2\eta^3)}
       \frac{\sin(\beta_\theta k)}k
 -\frac1{\omega^2}e^{-3\theta/(2\eta^3)}
       \frac{\cos(\beta_\theta k)}{k^2}\right\}
 +r_{\eta,\theta}(k),\qquad
 |r_{\eta,\theta}(k)|\le\frac{C_I}{\eta k^3}.
```

式 (59.14)。

余项的 $`\ell^2`$ 范数趋零。正弦项的平方和由
$`|\sin(\beta_\theta k)|\le\min(C_Ik/\eta^2,1)`$ 控制而一致有界，
余弦项亦然。结合 (59.10)，所有协方差替换均可用 Cauchy–Schwarz 控制。
余弦项在 $`\ell^2`$ 中可替换为
$`-(-1)^{mk}/(\omega^2k^2)`$，因为
$`|\cos(\beta k)-1|\le|\beta|k`$。
这部分在 (59.13) 除去因子 16 后的极限为
$`g_0\zeta(4)/\omega^4`$，且与时间参数无关。
正弦项与该低滞后项的交叉和至多

```math
C_I\eta\sum_{k\ge1}\frac{|\sin(\beta_\theta k)|}{k^3}
 \le C_I\eta|\beta_\theta|\sum_{k\ge1}k^{-2}
 \le C_I/\eta\longrightarrow0.
```

式 (59.15)。

对两个正弦项，先固定 $`H>0`$。在 $`k\le H\eta^2`$ 上，
(59.10) 和 $`\eta^2\delta\to0`$ 给出
$`\sup|w_\delta(k)-g_0|\to0`$；在其余滞后上，两系数乘积的绝对和至多
$`C_I\eta^2\sum_{k>H\eta^2}k^{-2}\le C_I/H`$。
先取 $`M\to\infty`$ 再取 $`H\to\infty`$，即可将权重统一换为 $`g_0`$。
使用经典 Dirichlet Green 核恒等式

```math
\sum_{k\ge1}\frac{\sin(kx)\sin(ky)}{k^2}
 =\frac\pi2\min(x,y)-\frac{xy}{2},\qquad 0\le x,y\le\pi.
```

式 (59.16)。

其归一化可由 $`\min(x,y)-xy/\pi`$ 在 $`x=y`$ 处大小为负一的导数跳跃，
计算 sine 系数 $`2\sin(ky)/(\pi k^2)`$ 得到；这也是第 58 章所引经典桥协方差。
将 (59.16) 用于 $`|\beta_\theta|,|\beta_u|`$，保留 sine 的符号，
并用 $`\eta^2\beta_\theta\to\omega\theta`$ 和 $`\pi/(2\omega)=1`$，得

```math
\lim\operatorname{Cov}(\mathcal R_Q^G(\theta),\mathcal R_Q^G(u))
 =\frac{16g_0\zeta(4)}{\omega^4}
  +16g_0\operatorname{sgn}(\theta u)\min(|\theta|,|u|).
```

式 (59.17)。

任一参数为零时第二项取零。所有乘积中的 $`(-1)^{mk}`$ 相消，
(59.11) 也不依赖奇偶性，故无需再取奇偶子列。

为取得路径紧性，令 $`d=|\theta-u|\le1`$。
精确积分与一次分部积分同时给出
$`|\mathrm{Ci}(ye^l)-\mathrm{Ci}(y)|\le C\min(l,y^{-1})`$。
这里 $`l=d/\eta^3`$、$`y\asymp\eta k`$，所以

```math
|b_{\eta,\theta}(k)-b_{\eta,u}(k)|
 \le C_I\left\{\frac d{\eta^3}|b_{\eta,u}(k)|
                     +\min(d/\eta,\eta/k)\right\},
\qquad
\sum_{k\ge1}|b_{\eta,\theta}(k)-b_{\eta,u}(k)|^2\le C_Id.
```

式 (59.18)。

最后一步在 $`k=\eta^2/d`$ 处分割；即使它超过所有实际滞后，
仍可扩展到整个正整数和，故对任意小的 $`d`$ 成立。
第二 Gaussian 混沌的谱公式给出
$`\mathbb EX^4=3(\mathbb EX^2)^2+48\operatorname{tr}(T_X^4)
\le15(\mathbb EX^2)^2`$。由 (59.10)、(59.13)、(59.18)，

```math
\mathbb E|\mathcal R_Q^G(\theta)-\mathcal R_Q^G(u)|^2\le C_I|\theta-u|,
\qquad
\mathbb E|\mathcal R_Q^G(\theta)-\mathcal R_Q^G(u)|^4\le C_I|\theta-u|^2.
```

式 (59.19)。

有限 Gaussian 路径连续，起点方差有界，因此 Kolmogorov 判据给出 $`C(I)`$ 紧性。
这里未对无限余弦级数逐项求导后取平方和。

同一 Gaussian 实现上的对角坐标是
$`\delta^{-1/2}\sum_j(G_j^2-m_j^\circ)`$。
其算子 $`D_Q`$ 的范数至多 $`C\sqrt\delta`$，方差趋于 $`2g_0=\nu_2`$，
与每个零对角核的 Hilbert–Schmidt 内积恒为零。
将它与有限多个 $`T_{\eta,\theta}`$ 作任意固定实线性组合。
(59.11)、(59.17) 给出小算子范数、有界 Hilbert–Schmidt 范数和收敛的方差。
若该组合的特征值为 $`\lambda_l`$，则

```math
\log\mathbb E\exp\left(it\sum_l\lambda_l(\xi_l^2-1)\right)
 =-t^2\sum_l\lambda_l^2
  +O_t\left(\max_l|\lambda_l|\sum_l\lambda_l^2\right).
```

式 (59.20)。

误差趋零，退化组合由方差趋零处理。Cramér–Wold 先给出联合 Gaussian 极限，
随后才由 (59.17) 的分解与对角正交性得到 $`Z_0,B,N_2`$ 的相互独立。
极限对称点之和减两倍原点的方差为零，连续性使该等式同时对所有参数成立。
这确定了 (59.4) 中同一条 Brownian 路径的反射关系。

独立于整个旧噪声的论证仍需单独完成。
对 $`L^2(\rho\,dx)`$ 的固定有限秩正交投影 $`P`$，

```math
\|T-(1-P)T(1-P)\|_{\rm HS}
 \le2\sqrt{\operatorname{rank}P}\,\|T\|_{\rm op}.
```

式 (59.21)。

它将每个新核及对角核接触这个有限噪声柱面的部分以趋零 $`L^2`$ 误差去掉。
剩余二重积分独立于该柱面。配合 (59.19) 的紧性，先得路径与有限柱面的联合收敛，
再以柱面条件期望的 $`L^1`$ 逼近处理任意有界 $`\sigma(W_\rho)`$ 可测变量。
所以新过程与 $`N_2`$ 联合相对于整个旧噪声 mixing。
这表示联合有界测试的因子分解；不是给定全部旧噪声后的条件律收敛。

旧 Gaussian 前缀路径在同一噪声上按连续方差时钟一致收敛；端点与偶极子在 $`L^2`$ 中收敛。
截距的核 $`H`$ 也在同一实现中保留。
其异格矩形近似 $`H_Q^\circ`$ 满足
$`\|H_Q^\circ-H\|_{L^2(\rho\otimes\rho)}^2
\le C\delta(1+|\log\delta|^2)+o(1)`$：
同格和邻格用 $`\int_0^{3\delta}(1+|\log x|^2)dx`$，
远格用对数导数和 $`\sum_{k\ge2}\delta/k^2`$，其余用 Gaussian 尾。
又 $`\sum G_j^2\to\gamma`$ 于 $`L^2`$，故旧截距趋于
$`b_*\gamma+I_2(H)`$，没有另抽一个与旧场无关的截距。
旧束的依概率收敛与前述 mixing 一起给出 (59.3) 的全部联合关系。

最后在良好数据环境上合并实际有限谱、精确中心、核心截断和共同耦合误差。
对环境任一子列取使这些条件误差界几乎处处成立的进一步子列，
确定 Gaussian 格结论便给出条件有界 Lipschitz 距离于数据概率中趋零。
仅一次对完整标签向量的后验总变差比较，将事件与有界测试转移到全部实际坐标。
未转移辅助 Gaussian 模型的无界矩。
一致逼近连续路径给出实际取整路径的 C-tight $`J_1`$ 收敛。
支持置换使每个固定支持的无条件律等于先验混合律；
逆方向的配对或整路径反转，以及同一个方向判定一致事件，保留全部坐标的共同实现。
方向事件补集只以其概率进入有界测试，故无需控制该事件上的放大统计量。
(59.5) 随后由连续极限映射得到。

本条的经典 sine 桥、二次谱展开与混沌判据归因见
[文献说明](../../../Library/Dynamics/iyer2025empirical.md)。
新增连接是实际共振数组的放大控制、增长滞后卷积和无额外余量的 (59.11)，
它们共同使局部反射律在原后验实验上成立。

**定理 59.3（反射、截距精度与范围）。** 定理 59.2 的极限不能换成
在正负半线上独立的 Brownian motion 加同一偏移。
将有限截距换成 $`\widetilde{\mathcal J}_M`$ 时，原路径与替换路径之差在
每个非空固定紧区间上一致依概率趋零，当且仅当

```math
\frac{\eta_M^2}{\sqrt\delta}
 (\widetilde{\mathcal J}_M-\mathcal J_M)\longrightarrow0
 \quad\hbox{依概率}.
```

式 (59.22)。

证明。若两半线独立，则在固定 $`\theta>0`$ 处的反射和方差是
$`32g_0\theta>0`$，与 (59.5) 矛盾。
截距替换产生的路径差恰为 (59.22) 左边乘
$`-e^{\theta/(2\eta_M^3)}`$；该乘子的绝对值在固定紧区间上一致趋一，证明充要性。
相同弱极限不提供 (59.22) 的速率。
若只把截距中的 $`b_*\mathcal Q_M`$ 换为 $`b_*V_M`$，
则截距差值为 $`-b_*\sqrt\delta T_M`$，替换路径减原路径包含
$`b_*\eta_M^2e^{\theta/(2\eta_M^3)}T_M`$，也不能由旧弱收敛略去。

本章仅处理精确共振与 $`\eta_M^2\delta\to0`$。
没有声称覆盖失谐、临界或超临界的 $`\eta_M^2\delta`$、
增长参数区间、数据自适应频率、其它 Liouville 幅度或实际后验矩收敛。

## 追加锚（本行以下为增补区）

## 60. 临界共振使旧噪声重现

**定义 60.1（临界共振与双场）。** 保持定义 54.1 的原始实际模型、精确中心与有限截距。
取确定性序列

```math
\eta_M=2m_M\longrightarrow\infty,\qquad
\zeta_M=\eta_M^2\delta\longrightarrow\zeta\in(0,\infty),
\qquad s_M=\log(\eta_M/\delta),\qquad
z_M(\theta)=s_M+\theta/\eta_M^3.
```

式 (60.1)。

定义实际过程

```math
\mathcal R_M(\theta)=\eta_M^{3/2}e^{z_M(\theta)/2}
 \{\mathcal Z_M(z_M(\theta)\sqrt\delta)-\mathcal J_M
                          -2z_M(\theta)\sqrt\delta T_M\}.
```

式 (60.2)。

现在 $`s_M=(3/4)\log Q+O(1)`$，因此任意固定参数紧区间的取值点最终落在原 $`[0,U]`$ 内。
令 $`W_\rho`$ 是旧噪声，$`W_\rho'`$ 是它的独立副本；
在 $`m_M`$ 全为偶数的子列上令 $`W_\sigma=W_\rho`$，
在全为奇数的子列上令 $`W_\sigma=W_\rho'`$。
定义连续对称核

```math
q_{\zeta,\theta}(x,y)=
\begin{cases}
 \displaystyle\frac{2\sqrt\zeta}{\omega}
       \frac{\sin(\omega\theta|x-y|/\zeta)}{|x-y|},&x\ne y,\\[4pt]
 2\theta/\sqrt\zeta,&x=y,
\end{cases}
\qquad \omega=\pi/2.
```

式 (60.3)。

它属于 $`L^2(\rho\otimes\rho)`$；对角值是连续延拓，不改变二重 Wiener 积分。

**定理 60.2（实际临界共振的奇偶联合律）。** 在 (60.1) 的每个固定奇偶子列上，
两种原始平稳实验均有紧区间 C-tight $`J_1`$ 联合收敛

```math
(\mathcal R_M|_I,T_M,\mathcal J_M,Y_M,
 L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip})
\Longrightarrow
(\mathcal R_\zeta^\sigma|_I,N_2,\mathcal J_\infty,Y,
 L|_{[-A,A]},C|_{[-A,A]},Z),
\qquad
\mathcal R_\zeta^\sigma(\theta)=Z_0+I_2(q_{\zeta,\theta};W_\sigma),
```

式 (60.4)。

其中 $`I`$ 固定且紧，$`A>0`$，
$`Z_0\sim N(0,16g_0\zeta_{\rm R}(4)/\omega^4)`$、$`N_2\sim N(0,2g_0)`$，
两者相互独立并联合独立于 $`(W_\rho,W_\rho')`$。
这里 $`\zeta_{\rm R}`$ 表示 Riemann zeta 函数，区别于临界参数 $`\zeta`$。
旧元组仍在同一个 $`W_\rho`$ 上，特别是 $`\mathcal J_\infty=b_*\gamma+I_2(H;W_\rho)`$。
可联合保留旧固定频率紧区间上的 Fourier 场及旧负 Sobolev 测度、偶极子逼近。
先验条件有界 Lipschitz 收敛于数据概率中成立；固定支持版本无条件且一致；
未知方向使用同一个判向一致事件。

令 $`F_\sigma(v)=W_\sigma(e^{-i\omega vx})`$，则同一实现中

```math
I_2(q_{\zeta,\theta};W_\sigma)
 =2\sqrt\zeta\int_0^{\theta/\zeta}(|F_\sigma(v)|^2-\gamma)\,dv.
```

式 (60.5)。

所以偶数支的非 Gaussian 部分由旧 Fourier 场本身生成；奇数支使用独立副本。

证明。整个论证保留一个完整后验标签向量。
(58.6)–(58.8) 的有限谱恒等式先在原数组上应用。
放大因子为 $`\eta^2\delta^{-1/2}e^{\theta/(2\eta^3)}=O_I(Q^{3/4})`$，
故乘上完整截断组数 $`O(Q^2)`$ 后的 Fourier 与取整误差仍趋零。
精确抵消仍用 $`\mathcal Q_M=V_M+\sqrt\delta T_M`$ 和原始截距。
所得原始矩阵正是 (59.6)。

先说明实际比较的估计可延伸到这里的有界 $`\zeta_M`$。
(59.7) 的共振包络及 (59.8) 的原始算子界只用
$`\eta\le C Q^{1/4}`$，没有使用 $`\eta^2\delta\to0`$。
因此精确中心误差仍至多 $`O_{\mathbb P}(Q^{-2}(1+\log Q))+o_{\mathbb P}(1)`$。
第 56 章 $`Q^{-60}`$ 尾质量去掉全部核心外向量，
同一个逆分布耦合再将所有核心组换成独立 Gaussian 组。
用 (56.18) 的相对质量误差和这个原始算子界，
实际环境方差可进一步换成确定格质量
$`m_j^\circ=\int_{I_j}\rho`$，路径误差至多
$`O_{\mathbb P}(Q^{-1/2}(1+\log Q)^2)`$。
旧截距、对角量和线性束在同一耦合中保持第 59 章证明里的界。
这一阶段得到 $`G_j=\sqrt{m_j^\circ}\xi_j`$ 的同一格模型。
下面不会把 (59.11) 的趋零结论用于临界参数。

记 $`a=\theta/\eta^3`$、$`d=(j-l)\delta`$、$`\chi_j=(-1)^{mj}`$，并令

```math
b_M(\theta)=\frac{\omega\eta(e^a-1)}\delta,\qquad
q_{M,\theta}(d)=\frac{2\sqrt{\zeta_M}}\omega e^{-a/2}
                           \frac{\sin(b_M(\theta)d)}d.
```

式 (60.6)。

在 $`d=0`$ 连续延拓。
$`b_M(\theta)\to\omega\theta/\zeta`$ 且
$`b'_M(\theta)=\omega e^a/\zeta_M`$。
对固定 $`I`$，核及其时间导数对所有 $`d`$ 一致有界；
核向 (60.3) 的收敛在固定空间紧区间上一致。
这不要求 $`|\zeta_M-\zeta|\sqrt{\log Q}\to0`$。

两次分部积分并保留共振符号，给出逐个非零整数 $`k=j-l`$ 的精确分解

```math
\frac{2\eta^2}{\sqrt\delta}e^{a/2}\mathrm{Ci}(\omega\eta e^a|k|)
 =\chi_j\chi_l q_{M,\theta}(k\delta)
 -\frac{2\chi_j\chi_l}{\omega^2\sqrt\delta}
           \frac{e^{-3a/2}\cos(b_M(\theta)k\delta)}{k^2}
 +E_M(\theta,k),
```

式 (60.7)。

```math
|E_M(\theta,k)|\le\frac{C_I}{\eta\sqrt\delta|k|^3},\qquad
|\partial_\theta E_M(\theta,k)|
 \le\frac{C_I}{\eta^3\sqrt\delta k^2}.
```

式 (60.8)。

导数界直接来自
$`R_3(v)=\mathrm{Ci}(v)-\sin v/v+\cos v/v^2`$ 的
$`R_3'(v)=-2\cos v/v^3`$，并包括前因子的导数。
(59.10) 的卷积界 $`\sum_jm_j^\circ m_{j+k}^\circ\le C\delta`$
将余项二次型的方差与导数方差分别界为 $`C\eta^{-2}`$、$`C\eta^{-6}`$。
对有限可微函数使用

```math
\sup_I|f|^2\le C_I\left\{\int_I|f|^2+
              \left(\int_I|f|^2\int_I|f'|^2\right)^{1/2}\right\}.
```

式 (60.9)。

取一点使其平方不超过平均值，再积分 $`(|f|^2)'`$ 即可证明。
这使余项在路径范数中趋零。

余弦项可一致换成在零点的随机常数

```math
O_Q=-\frac{2}{\omega^2\sqrt\delta}
       \sum_{j\ne l}\frac{\chi_j\chi_l}{(j-l)^2}G_jG_l.
```

式 (60.10)。

因为前因子与余弦相对一的误差至多
$`C_I\{\eta^{-3}+\min((k\delta)^2,1)\}`$，其导数至多
$`C_I\{\eta^{-3}+|k\delta|\min(|k\delta|,1)\}`$。
用同一卷积界并在 $`k=1/\delta`$ 分割，二次型差及其导数的方差均至多
$`C_I(\eta^{-6}+\delta^3)=O_I(\delta^3)`$。
(60.9) 给出一致依概率趋零。因此格模型为

```math
O_Q+\sum_{j\ne l}q_{M,\theta}(x_j-x_l)(\chi_jG_j)(\chi_lG_l)
                  +o_{\mathbb P}(1)\quad\hbox{于 }C(I).
```

式 (60.11)。

现考察同一 Gaussian 向量上的两个线性场
$`W_Q(f)=\sum G_jf(x_j)`$、$`W_Q^\chi(f)=\sum\chi_jG_jf(x_j)`$。
若 $`m`$ 为偶数，两者逐样本相同。
若 $`m`$ 为奇数，对有界区间阶梯函数 $`f,g`$，其交叉 Gram 为
$`\sum(-1)^jm_j^\circ f(x_j)g(x_j)`$。
相邻格成对，平滑 $`\rho`$ 的质量差与有限区间端点贡献使此和为 $`O(\delta)`$。
各自 Gram 均趋于 $`\int fg\rho`$。
总质量和 $`x^2`$ 尾扩展到端点、偶极子及固定频率 Fourier 测试，故

```math
(W_Q,W_Q^\chi)\Longrightarrow
\begin{cases}(W_\rho,W_\rho),&m\text{ 偶},\\
              (W_\rho,W_\rho'),&m\text{ 奇},
\end{cases}
```

式 (60.12)。

此处先是柱面联合收敛；所需旧路径由同一方差时钟的紧性补全。
奇数支的独立副本由确定符号调制的极限产生，有限实验中没有重抽标签。

偏移 (60.10) 的标准化矩阵 $`C_Q`$ 有算子范数 $`O(\sqrt\delta)`$，
由 $`m_j^\circ\le C\delta`$ 和可和的 $`k^{-2}`$ 行包络得到。
又由逐固定滞后 $`w_\delta(k)\to g_0`$，

```math
2\operatorname{tr}C_Q^2
 =\frac8{\omega^4}\sum_{k\ne0}\frac{w_\delta(k)}{k^4}
 \longrightarrow\frac{16g_0\zeta_{\rm R}(4)}{\omega^4}.
```

式 (60.13)。

对角矩阵 $`D_Q=\operatorname{diag}(m_j^\circ/\sqrt\delta)`$ 也有趋零算子范数，
方差趋于 $`2g_0`$，且 $`\operatorname{tr}(C_QD_Q)=0`$。
对任意固定线性组合 $`A=cC_Q+dD_Q`$，
(59.20) 先给出偏移与对角量的联合 Gaussian 极限。
加入旧场与调制场的任意有限组合系数向量 $`\ell_Q`$ 时，联合特征函数为

```math
e^{-i\operatorname{tr}A}\det(1-2iA)^{-1/2}
 \exp\{-\tfrac12\ell_Q^\top(1-2iA)^{-1}\ell_Q\}.
```

式 (60.14)。

$`\|\ell_Q\|_2`$ 有界，故末项指数与 $`-\|\ell_Q\|_2^2/2`$ 的差趋零。
配合 (60.12) 的全部 Gram 极限，这证明 $`Z_0,N_2`$ 相互独立并独立于两个场。
没有把随规模改变的对角量或调制坐标当作固定旧变量。

对固定空间紧区间上的矩形阶梯核 $`K=\sum k_{ab}1_{I_a}\otimes1_{I_b}`$，
异格二次型恒等于

```math
\sum_{a,b}k_{ab}W_Q^\chi(I_a)W_Q^\chi(I_b)
                    -\sum_a k_{aa}\sum_{x_j\in I_a}G_j^2.
```

式 (60.15)。

块平方和的方差 $`2\sum m_j^{\circ2}`$ 趋零，均值趋于 $`\int_{I_a}\rho`$，
故极限恰为 $`I_2(K;W_\sigma)`$。
将 $`q_{M,\theta}`$ 在固定空间紧区间上统一逼近，再用有界核和 Gaussian 质量尾，
即可得到 (60.11) 在有限多个时间的共同极限。
同时对旧对数核先去掉近对角与远端，再用同一个矩形划分，保留旧 $`I_2(H;W_\rho)`$。
新的确定迹为 $`2\theta\gamma/\sqrt\zeta`$，由异格扣除产生 Wick 中心；
有限对角随机误差只是 $`q_{M,\theta}(0)\sqrt\delta T_Q^G=o_{\mathbb P}(1)`$。

由 $`q_{M,\theta}`$ 的一致有界导数，正弦二次型的增量方差至多
$`C_I|\theta-u|^2(\sum m_j^\circ)^2`$，第四矩至多 $`C_I|\theta-u|^4`$。
因此它在 $`C(I)`$ 中紧，偏移为一个紧的随机常数，(60.8)–(60.10) 的余项已在路径范数中去掉。
旧前缀、Fourier 场及负 Sobolev 坐标的共同逼近仍使用同一总质量与 $`x^2`$ 尾。
任意有界 Gaussian 柱面测试再以 $`L^1`$ 逼近，给出整个场的独立关系。

实际收敛由前述共同耦合和精确中心误差恢复，最后仅一次对完整标签向量应用后验 TV。
它只传递事件和有界测试，不传递无界矩。
良好环境的子列原则给出条件有界 Lipschitz 版本；
支持置换给出固定支持的一致无条件版本。
同一方向事件同时控制所有工作坐标，补集只以概率进入误差。
连续格路径与实际取整路径的一致距离趋零，遂得 C-tight $`J_1`$ 结论。

最后，Gaussian 乘积公式给出
$`|F_\sigma(v)|^2-\gamma=I_2(\cos(\omega v(x-y));W_\sigma)`$。
有限有向频率区间上的 Bochner 积分可由二重积分的等距性交换，
其核积分为 (60.3)，证明 (60.5)。连续版本使等式同时对所有参数成立。

**定理 60.3（同边缘律而不同联合律）。** 两个奇偶分支有相同过程边缘律。
任意 $`\theta\ne0`$ 的边缘分布均非 Gaussian；在零点只有 Gaussian 偏移。
若 $`Y=W_\rho(1)`$，则

```math
\operatorname{Cov}(\mathcal R_\zeta^{\rm even}(\theta),Y^2-\gamma)
 =\frac{4\pi g_0\sqrt\zeta}{\omega}
        \operatorname{erf}\left(\frac{\omega\theta}{\zeta\sqrt\kappa}\right),
\qquad
\operatorname{Cov}(\mathcal R_\zeta^{\rm odd}(\theta),Y^2-\gamma)=0.
```

式 (60.16)。

证明。两场同律且各自独立于同分布偏移，故边缘过程同律。
核算子 $`T_{\zeta,\theta}`$ 的实特征值为 $`(\lambda_n)`$，
二阶混沌的经典谱公式给出第四累积量 $`48\sum\lambda_n^4`$。
当 $`\theta\ne0`$，核在对角附近非零，$`\rho>0`$，
所以自伴 Hilbert–Schmidt 算子非零，至少一个特征值非零。
独立 Gaussian 偏移不改变第四累积量，证明非 Gaussian 性。
偶数支的协方差由二阶等距公式化为
$`(4g_0\sqrt\zeta/\omega)\int e^{-\kappa d^2/4}\sin(\omega\theta d/\zeta)/d\,dd`$。
该积分对频率求导为 $`2\sqrt{\pi/\kappa}e^{-a^2/\kappa}`$，
在零频率取零，积分得 $`\pi\operatorname{erf}(a/\sqrt\kappa)`$。
奇数支由独立性取零。这些是极限变量的矩恒等式，不声称实际矩收敛。

对任一规定奇偶性，选同奇偶整数 $`m_M`$ 最近于
$`\sqrt\zeta/(2\sqrt\delta)`$，误差至多一，便有
$`(2m_M)^2\delta-\zeta=O(\sqrt\delta)`$。
所以两分支都可由合法确定探测尺度实现。
奇偶性不稳定时，新过程本身仍由两子列论证收敛到共同边缘律；
若两种奇偶性均出现无穷次，(60.16) 表明不能宣称一个不分支的旧场联合极限。

**定理 60.4（已识别临界族的低参数边界）。** 在固定的 $`W_\sigma`$ 上构造
$`I_2(q_{\zeta,\theta};W_\sigma)`$。当 $`\zeta\downarrow0`$，
此族在每个固定 $`C(I)`$ 中趋于 $`4\sqrt{g_0}B_{\rm odd}`$，
且相对于整个 $`W_\sigma`$ mixing；可联合附加独立偏移 $`Z_0`$。
这是已识别 Gaussian 混沌族的极限，不通过代入定理 60.2 取得实际数组结论。

证明。角频率 Fourier 变换下，sinc 核的乘子为
$`(2\pi\sqrt\zeta/\omega)\operatorname{sgn}(\theta)
1_{\{|\xi|<\omega|\theta|/\zeta\}}`$。
在 Lebesgue $`L^2`$ 上以 $`\sqrt\rho`$ 共轭，Plancherel 给出
$`\|T_{\zeta,\theta}\|_{\rm op}\le
2\pi\|\rho\|_\infty\sqrt\zeta/\omega`$。
二阶协方差为

```math
\frac{8\zeta}{\omega^2}\int
  \frac{\sin(\omega\theta d/\zeta)\sin(\omega u d/\zeta)}{d^2}g(d)\,dd
 \longrightarrow16g_0\operatorname{sgn}(\theta u)\min(|\theta|,|u|).
```

式 (60.17)。

用 $`d=\zeta v`$、$`g(0)=g_0`$ 和可积的倒数平方尾支配，
再用 $`\int\sin(av)\sin(bv)/v^2\,dv
=\pi\operatorname{sgn}(ab)\min(|a|,|b|)`$ 即得。
有限组合的小算子范数和有界 Hilbert–Schmidt 范数使谱特征函数趋于 Gaussian。
同一积分恒等式给出任意符号时间的增量方差至多 $`C|\theta-u|`$，
第二混沌第四矩至多 $`C|\theta-u|^2`$，故在 $`C(I)`$ 中紧。
最后按 (59.21) 删除固定有限秩柱面，再作 $`L^1`$ 柱面逼近，取得 mixing。
协方差 (60.17) 识别的是同一 Brownian motion 的奇反射。

经典 Gaussian 谱、混沌独立性及 sinc Fourier 工具的适用条件见
[文献说明](../../../Library/Dynamics/iyer2025empirical.md)。
本章不包含失谐、随机奇偶分布、实际矩收敛、增长参数区间、其它幅度或临界参数趋零、无穷时的实际数组定理。

## 追加锚（本行以下为增补区）

## 61. 超临界共振的端点平方与共同实现

**定义 61.1（超临界共振的锚定放大）。** 保持定义 54.1 的实际模型、完整后验向量、精确中心与有限截距。
取确定性序列

```math
\eta=2m\longrightarrow\infty,\qquad r_*=\eta^2\delta\longrightarrow\infty,
\qquad s=\log(\eta/\delta),\qquad s\sqrt\delta\le U/2.
```

式 (61.1)。

对固定参数紧区间令 $`z_\theta=s+\theta/\eta^3`$，定义同一实际标签实现上的两个过程

```math
\mathcal V_M(\theta)=\eta^{3/2}e^{z_\theta/2}
 \{\mathcal Z_M(z_\theta\sqrt\delta)-\mathcal J_M
                         -2z_\theta\sqrt\delta T_M\},\qquad
\mathcal D_M(\theta)=\sqrt{r_*}
             \{\mathcal V_M(\theta)-\mathcal V_M(0)\}.
```

式 (61.2)。

再令 $`\chi_j=(-1)^{mj}`$，$`Y_M^\chi=\sum_j\chi_jA_j`$。
这里 $`A_j`$ 仍是定义 54.1 的精确中心组和；所有和使用完整计数截断。
记旧解析 Fourier 场及固定谱分辨率曲线为

```math
\mathcal F_M(v)=\sum_jA_je^{-i\omega vx_j},\qquad
\mathcal S_M(a)=E_M(a)-2\mathfrak L Y_M^2,
\qquad \mathfrak L=\log(1/h),\quad\omega=\pi/2.
```

式 (61.3)。

**定理 61.2（全超临界范围的实际端点平方律）。** 对 (61.1) 的每个固定奇偶子列，
两种原始平稳实验均有联合收敛

```math
(\mathcal V_M|_I,\mathcal D_M|_I,T_M,\mathcal J_M,Y_M,
 L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip},
 \mathcal F_M|_{[0,A_F]},\mathcal S_M|_{I_S})
\Longrightarrow
(Z_0\mathbf1_I,\,[\theta\mapsto2\theta(Y_\sigma^2-\gamma)],
 N_2,\mathcal J_\infty,Y,L,C,Z,\mathcal F,\mathcal S).
```

式 (61.4)。

其中所有区间固定且紧，$`A,A_F>0`$；新过程对取 $`D(I;\mathbb R^2)`$ 的联合 $`J_1`$ 拓扑，
其余 càdlàg 路径取乘积 $`J_1`$ 拓扑，且均为 C-tight。
Fourier 坐标可以取 $`C^1([0,A_F];\mathbb C)`$ 拓扑。
令 $`W_\rho'`$ 为旧 $`W_\rho`$ 的独立副本；偶数 $`m`$ 支令 $`Y_\sigma=Y=W_\rho(1)`$，
奇数支令 $`Y_\sigma=W_\rho'(1)`$。此外

```math
Z_0\sim N(0,16g_0\zeta_{\rm R}(4)/\omega^4)=N(0,128g_0/45),
\qquad N_2\sim N(0,2g_0),
```

式 (61.5)。

两者相互独立，并联合独立于两个 Gaussian 场。
所有旧坐标仍在同一旧场上；特别是

```math
\mathcal J_\infty=b_*\gamma+I_2(H;W_\rho),\qquad
\mathcal F(v)=W_\rho(e^{-i\omega vx}),\qquad
\mathcal S(a)=(b_*+2a)Y^2+
 2\int_0^{e^a}\frac{|\mathcal F(v)|^2-Y^2}{v}\,dv.
```

式 (61.6)。

条件先验版本是给定数据的有界 Lipschitz 距离于数据概率中趋零；
固定支持版本无条件且对支持位置一致。未知方向的全部坐标使用同一个判向一致事件。
同一实际实现还满足

```math
\sup_{\theta\in I}
 |\mathcal D_M(\theta)-2\theta\{(Y_M^\chi)^2-\mathcal Q_M\}|
 \longrightarrow0\quad\hbox{依概率}.
```

式 (61.7)。

不需要 $`r_*`$ 超过任何附加的对数速率。
不含旧坐标的 $`(\mathcal V_M,\mathcal D_M,T_M)`$ 有不分奇偶的同一边缘极限。

证明。先把 $`I`$ 扩大为包含零的固定紧区间。
精确等式 $`\mathcal Q_M=V_M+\sqrt\delta T_M`$ 使 (61.2) 的括号等于
$`E_M(z_\theta)-2\mathfrak L Y_M^2-2z_\theta\mathcal Q_M-\mathcal J_M`$。
有限谱抵消在所有极限之前完成。
定义零对角系数

```math
b_{\eta,\theta}(k)=\frac{2\eta^2}{\sqrt\delta}
 e^{\theta/(2\eta^3)}\mathrm{Ci}(\omega\eta e^{\theta/\eta^3}|k|),
\qquad
d_{\eta,\theta}(k)=2\eta^3
 \{e^{\theta/(2\eta^3)}\mathrm{Ci}(\omega\eta e^{\theta/\eta^3}|k|)
                        -\mathrm{Ci}(\omega\eta|k|)\},\quad k\ne0.
```

式 (61.8)。

第 58 章有限和积分比较在增长 $`s`$ 下给出

```math
\varepsilon_F\le C_I\{h\sqrt\lambda(1+s+\log\lambda)
       +h^2\lambda(1+\mathfrak L+\log\lambda)+he^{-s}\}.
```

式 (61.9)。

具体地，$`\sum_{n\le N}\cos(n\vartheta)/n`$ 与
$`\mathrm{Ci}(N|\vartheta|)-\log|\vartheta|`$ 的误差至多
$`C\{N^{-1}+|\vartheta|[1+\log(1+N|\vartheta|)]\}`$；
权重差 $`(1+n^2)^{-1/2}-n^{-1}=O(n^{-3})`$ 贡献
$`C\vartheta^2(1+|\log|\vartheta||)+CN^{-2}`$。
取整由 $`d\mathrm{Ci}(e^u)/du=\cos(e^u)`$ 控制。
这些界直接作用于有限谱，不在旧弱极限中代入增长参数。
由 $`\log\eta=O_U(Q^{1/4})`$、$`h=\exp(-c_hQ^3+O(1))`$、$`c_h>0`$，
以及完整截断的 $`O(Q^2)`$ 组数，有

```math
\sup_I\left|\mathcal V_M-\sum_{j\ne l}b_{\eta,\theta}(j-l)A_jA_l\right|
+\sup_I\left|\mathcal D_M-\sum_{j\ne l}d_{\eta,\theta}(j-l)A_jA_l\right|
 \le C_I\eta^3Q^2\varepsilon_F\|A\|_2^2=o_{\mathbb P}(1).
```

式 (61.10)。

这里 $`\eta^2/\sqrt\delta\le\eta^3`$ 最终成立。
估计先在辅助乘积律下成立，最后以有界事件转回实际后验。

在零时刻分部积分得

```math
b_{\eta,0}(k)=-\frac{2(-1)^{mk}}{\omega^2\sqrt\delta k^2}
       +O\left(\frac1{\eta^2\sqrt\delta k^4}\right).
```

式 (61.11)。

其主矩阵原始算子范数为 $`O(\delta^{-1/2})`$，余项范数
$`O(\sqrt\delta/r_*)=o(1)`$，故后者可用紧的组向量范数直接舍去。
对锚定系数作精确微分，而非对渐近展开求导，得

```math
\partial_\theta d_{\eta,\theta}(k)
 =2e^{\theta/(2\eta^3)}\{\tfrac12\mathrm{Ci}(v)+\cos v\},
\qquad v=\omega\eta e^{\theta/\eta^3}|k|.
```

式 (61.12)。

由 $`|\mathrm{Ci}(v)|\le C/v`$，这个导数及 $`d_{\eta,\theta}`$ 在所有非零滞后上一致有界。
因此完整截断矩阵的原始范数至多 $`C_IQ^2`$，与 $`\eta`$ 的增长无关。
第 56 章精确中心向量误差
$`a_M^{\rm ctr}=O_{\mathbb P}(Q^{-5/2}+q^{-1/2})`$，
乘这两个矩阵范数分别给出 $`O_{\mathbb P}(Q^{-9/4})+o(1)`$ 和
$`O_{\mathbb P}(Q^{-1/2})+o(1)`$。
这里用
$`|X^\top KX-(X-e)^\top K(X-e)|\le\|K\|_{\rm op}(2\|X\|\|e\|+\|e\|^2)`$。
增长核心外的平方质量至多 $`Q^{-60}`$，同一原始范数界同时去掉整个尾向量。
原始旧对数矩阵至多 $`CQ^2(1+\log Q)`$，其中心与尾误差也趋零。

归一化前 Bernoulli 核心组和的方差至少 $`q^{9/10}`$；第 56 章由 Bernoulli 局部界构造的同一逆分布耦合，
以趋一概率同时使各组的标准化误差至多 $`q^{-1/8}`$。
它压过上述多项式成本。再用同一标准正态变量把归一化后的核心组方差换成
$`m_j^\circ=\int_{[(j-1/2)\delta,(j+1/2)\delta)}\rho(x)\,dx`$。
相对误差为 $`O_{\mathbb P}(Q^{-1}(1+\log Q))`$，
核心大小为 $`O(Q^{1/2}\sqrt{\log Q})`$。
故锚定矩阵、零时刻矩阵与旧对数矩阵的替换误差分别至多

```math
O_{\mathbb P}(Q^{-1/2}(1+\log Q)^{3/2}),\qquad
O_{\mathbb P}(Q^{-3/4}(1+\log Q)),\qquad
O_{\mathbb P}(Q^{-1/2}(1+\log Q)^{5/2}).
```

式 (61.13)。

对角量的中心和平方范数替换成本为相对误差乘 $`\delta^{-1/2}`$，也趋零。
因此得到同一确定 Gaussian 格模型 $`G_j=W_\rho(1_{I_j})`$。
所有矩估计都在辅助律内先转换为概率误差。

记其零时刻主二次型为 $`O_Q`$，对角量为
$`T_Q^\circ=\delta^{-1/2}\sum_j(G_j^2-m_j^\circ)`$。
在标准化格基底中，两者的算子范数均至多 $`C\sqrt\delta`$。
令 $`w_\delta(k)=\delta^{-1}\sum_jm_j^\circ m_{j+k}^\circ`$，则
$`w_\delta(k)\to g_0`$ 对每个固定 $`k`$ 成立，且 $`w_\delta(k)\le C`$ 一致成立。
二阶混沌等距和可和的 $`k^{-4}`$ 给出

```math
\operatorname{Var}O_Q=\frac{16}{\omega^4}
       \sum_{k\ge1}\frac{w_\delta(k)}{k^4}
       \longrightarrow\frac{16g_0\zeta_{\rm R}(4)}{\omega^4},\qquad
\operatorname{Var}T_Q^\circ\longrightarrow2g_0,
\qquad \operatorname{Cov}(O_Q,T_Q^\circ)=0.
```

式 (61.14)。

最后一个等式来自零对角与对角矩阵的正交，还不能单独推出独立。
对每个实线性组合的特征值 $`\lambda_{l,Q}`$，展开 Gaussian 二次型特征函数得

```math
\log\mathbb E e^{itI_2(K_Q)}
 =-t^2\sum_l\lambda_{l,Q}^2
       +O_t\left(\max_l|\lambda_{l,Q}|\sum_l\lambda_{l,Q}^2\right).
```

式 (61.15)。

误差趋零，故先得到联合 Gaussian 性，再由 (61.14) 得到 $`Z_0,N_2`$ 的独立性。
谱展开是 Nourdin–Poly Proposition 2.1 的经典结构。

锚定部分保留一个非消失的秩一方向。
由精确共振及 $`|1-\cos u|\le u^2/2`$，(61.12) 给出全空间界

```math
|\partial_\theta d_{\eta,\theta}(j-l)-2\chi_j\chi_l|
 \le C_I\{\eta^{-1}+\eta^{-3}+|x_j-x_l|^2/r_*^2\}.
```

式 (61.16)。

它不要求核心的最大位移除以 $`r_*`$ 趋零。
Gaussian 格质量的四阶空间矩一致有界，因此相应二次型与
$`2\theta\{(\sum_j\chi_jG_j)^2-\sum_jG_j^2\}`$ 的差 $`E_Q(\theta)`$ 满足

```math
\sup_I\mathbb E|E_Q'(\theta)|^2
 \le C_I(\eta^{-2}+r_*^{-4}),\qquad
\mathbb E\sup_I|E_Q(\theta)|^2
 \le C_I(\eta^{-2}+r_*^{-4})\longrightarrow0.
```

式 (61.17)。

第二步用 $`E_Q(0)=0`$、微积分基本定理与 Cauchy–Schwarz。
异格和的对角扣除是有限恒等式；$`\sum_jG_j^2\to\gamma`$ 于 $`L^2`$，
因为其方差 $`2\sum_j(m_j^\circ)^2=O(\delta)`$。
(61.12) 还给出任意小参数增量的二阶矩界 $`C_I|\theta-\vartheta|^2`$。
谱展开直接算得二阶混沌 $`\mathbb EX^4\le15(\mathbb EX^2)^2`$，
故四阶增量界为 $`C_I|\theta-\vartheta|^4`$。
这证明路径紧性，并与 (61.17) 一起给出统一锚定逼近。
由 (61.2) 的有限恒等式
$`\mathcal V_M(\theta)=\mathcal V_M(0)+\mathcal D_M(\theta)/\sqrt{r_*}`$，
第一过程于是趋于常路径；第二过程的非平凡极限已由独立估计证明。

现在识别与旧场的联合关系。
在每格上延拓 $`\chi_Q(x)=(-1)^{mj}`$。
偶数支它恒为一；奇数支它是周期 $`2\delta`$ 的交替方波，原函数一致为 $`O(\delta)`$。
对任意 $`f,g\in L^2(\rho)`$，光滑紧支撑逼近与分部积分给出

```math
\int\chi_Qfg\rho\longrightarrow0\quad(m\hbox{ 为奇数}).
```

式 (61.18)。

故旧 $`W_\rho(f_i)`$ 与移动 $`W_\rho(\chi_Qg_l)`$ 的任意有限 Gaussian 向量，
其 Gram 矩阵趋于两个独立场的 Gram 矩阵。
为了同时保留 $`O_Q,T_Q^\circ`$，令 $`P_Q`$ 投影到这些固定与移动方向的共同有限维张成空间。
对上述任一小算子 $`K_Q`$，

```math
\|K_Q-(1-P_Q)K_Q(1-P_Q)\|_{HS}
 \le2\sqrt{\operatorname{rank}P_Q}\,\|K_Q\|_{\rm op}\longrightarrow0.
```

式 (61.19)。

保留二次型与这些线性方向精确独立，且等距保证删除误差趋零。
这证明偏移和对角量联合独立于两个极限场，包含同时移动的符号方向。
有限旧柱面逼近还将参考模型的结论延伸到整个旧场的有界可测测试；
它不声称给定整个 Gaussian 场的条件律收敛。

旧轮廓的格质量时钟逼近连续时钟，Brownian 连续模给出紧空间区间上的统一收敛。
端点与偶极子由 $`L^2(\rho)`$ 逼近，桥由确定投影得到。
旧对数核在同格方块置零、其它核心方块取格心值，其平方误差至多
$`C\delta(1+|\log\delta|^2)+o(1)`$：
先隔离对角宽 $`C\delta`$ 条带，外部用对数差 $`C\delta/|x-y|`$，最后用 Gaussian 尾。
等距于是给出同一旧场上的 $`\mathcal J_\infty`$。
以有限旧方向的核逼近它，再用 (61.19)，保留这个非线性旧坐标的联合关系。

Fourier 系数及其前两阶导数在
$`L^2([0,A_F]\times\mathbb R,dv\rho dx)`$ 中由格心值逼近；
支配函数可取 $`C(1+|x|^4)`$。
因此参考 Fourier 路径于 $`H^2`$ 的均方范数收敛，进而于 $`C^1`$ 收敛。
实际中心的 Hilbert 系数平方范数至多 $`C(1+x_j^4)/B^2`$，
第 56 章四阶加权时钟和同一中心界适用；尾、耦合与质量替换也在此范数趋零。
对 $`\mathcal S_M`$ 可先取更大的 $`A_F>e^{\sup I_S}`$。
函数 $`g_M(v)=(|\mathcal F_M(v)|^2-Y_M^2)/v`$ 在零处连续延拓，且
$`g_M(v)=\int_0^1(|\mathcal F_M|^2)'(tv)\,dt`$。
故 $`C^1`$ 收敛使它统一收敛。有限权重分解得

```math
\mathcal S_M(a)=(b_*+2a)Y_M^2+
       2h\sum_{n\le e^a/h}g_M(nh)+o_{\mathbb P}(1)
```

式 (61.20)。

权重差用 $`\sum n|(1+n^2)^{-1/2}-n^{-1}|<\infty`$，
取整误差在固定 $`I_S`$ 为 $`O(h)(1+Y_M^2)`$。
统一 Riemann 和给出 (61.6)，且没有改变共同噪声。

全部比较至此使用一个共同核心、一个标签向量和一个 Gaussian 耦合。
对每个确定的良好数据环境，耦合概率误差与参考弱极限误差趋零；
环境子列原理将它转成数据概率中的条件有界 Lipschitz 收敛。
最后仅一次使用第 56 章完整选择向量的总变差比较，作用于有界测试及误差事件。
同一耦合把锚定平方逼近转成 (61.7)，不需要对实际无界矩传递。
支持置换等变性给出固定支持的无条件一致结论。
已知逆向先对齐观测；未知方向在原来错误概率 $`O(q^{-1})`$ 的一个判向事件上，
所有组、精确中心及坐标同时与正确对齐实验相同。
事件外的巨大放大量不影响有界测试界。
因此概率范围与定理所述一致。

**定理 61.3（相同边缘律不能决定端点耦合）。** 对非零 $`\theta`$，(61.4) 中的锚定极限 $`X_\theta`$ 满足

```math
\operatorname{cum}_4(X_\theta)=768\theta^4\gamma^4>0,\qquad
\operatorname{Cov}(X_\theta,Y^2-\gamma)=
 \begin{cases}4\theta\gamma^2,&m\hbox{ 为偶数},\\0,&m\hbox{ 为奇数}.\end{cases}
```

式 (61.21)。

当 $`\theta>0`$ 时其支持为 $`[-2\theta\gamma,\infty)`$。
两种奇偶性均无限出现时，包含旧端点的元组没有单一的共同弱极限。

证明。写 $`Y_\sigma=\sqrt\gamma\,g`$，$`g\sim N(0,1)`$，
其中心平方第四累积量为 $`48\gamma^4`$；乘 $`2\theta`$ 得第一式。
偶数支使用同一平方，方差 $`2\gamma^2`$；奇数支独立，由定理 61.2 已证明的联合关系得到第二式。
支持来自 $`g^2\in[0,\infty)`$。
两条子列极限有不同的联合分布，因此整个元组不能收敛到同一个分布。
这里比较的是极限律本身，不声称实际协方差或第四矩收敛。
Nourdin–Peccati 的非中心收敛 Proposition 4.5 与 Remark 4.3 也指出：
二阶混沌的中心 Gamma 边缘极限并不自动独立于旧 Gaussian 方向，仍需相应收缩消失。
本例用 (61.18) 与实际有限谱估计识别了这项额外关系。

## 追加锚（本行以下为增补区）
