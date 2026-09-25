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
