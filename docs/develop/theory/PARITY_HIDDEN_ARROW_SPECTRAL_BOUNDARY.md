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

## 62. 非共振载波中的圆对称能量

**定义 62.1（相位间隔与锚定残差）。** 保持定义 54.1 的实际模型、完整选择窗口、精确中心及有限截距。
取确定性序列

```math
\eta\longrightarrow\infty,\qquad \zeta_M=\eta^2\delta\longrightarrow\zeta\in(0,\infty),
\qquad d_M=\operatorname{dist}(\omega\eta,\pi\mathbb Z),\quad d_M/\delta\longrightarrow\infty,
\qquad s=\log(\eta/\delta),\quad z_\theta=s+\theta/\eta^3.
```

式 (62.1)。

相位本身无需收敛，间隔也可趋零；不要求额外对数余量。
令

```math
\mathcal V_M(\theta)=\eta^{3/2}e^{z_\theta/2}
 \{\mathcal Z_M(z_\theta\sqrt\delta)-\mathcal J_M-2z_\theta\sqrt\delta T_M\},
\qquad \mathcal D_M(\theta)=\mathcal V_M(\theta)-\mathcal V_M(0).
```

式 (62.2)。

这里的锚定不含 (61.2) 的额外因子 $`\sqrt{r_*}`$。
令 $`W_1,W_2`$ 为相互独立、也独立于旧 $`W_\rho`$ 的实 Gaussian 测度，控制测度均为 $`\rho(x)dx`$。
按复线性积分约定定义

```math
C=(W_1+iW_2)/\sqrt2,\qquad F_C(v)=C(e^{i\omega vx}),\qquad
\mathbb E C(f)\overline{C(g)}=\int f\bar g\rho,
\qquad \mathbb EC(f)C(g)=0.
```

式 (62.3)。

后一个等式是伪协方差为零，固定圆对称复 Gaussian 的归一化。

**定理 62.2（实际非共振载波与极限能量的两侧关系）。** 在 (62.1) 下，
两种原始平稳实验的同一完整后验向量满足紧区间 C-tight $`J_1`$ 联合收敛

```math
(\mathcal D_M|_I,T_M,\mathcal J_M,Y_M,L_M|_{[-A,A]},C_M|_{[-A,A]},Z_M^{\rm dip})
\Longrightarrow
(\mathcal D_\zeta|_I,N_2,\mathcal J_\infty,Y,L|_{[-A,A]},C|_{[-A,A]},Z),
\qquad
\mathcal D_\zeta(\theta)=2\sqrt\zeta\int_0^{\theta/\zeta}(|F_C(v)|^2-\gamma)\,dv.
```

式 (62.4)。

积分按方向取值，$`I`$ 固定且紧，$`A>0`$。
式中桥坐标 $`C(x)`$ 与复 Gaussian 测度 $`C(f)`$ 由参数种类区分。
新过程独立于整个旧元组；$`N_2\sim N(0,2g_0)`$ 独立于三个 Gaussian 场。
旧坐标保持同一 $`W_\rho`$，特别是 $`\mathcal J_\infty=b_*\gamma+I_2(H;W_\rho)`$。
可联合保留任意固定频率紧区间的旧 Fourier 场（统一拓扑）与旧负 Sobolev 测度、偶极子逼近。
条件先验版本于数据概率中以有界 Lipschitz 距离收敛；固定支持版本无条件且一致；
未知方向使用整个元组的一个共同判向一致事件。
不声称未锚定 $`\mathcal V_M`$ 的紧性。

识别出的 $`\mathcal D_\zeta`$ 有平稳增量，非零时间边缘非 Gaussian。
其协方差为

```math
\operatorname{Cov}(\mathcal D_\zeta(\theta),\mathcal D_\zeta(u))
 =4\zeta\int_0^{\theta/\zeta}\int_0^{u/\zeta}c(v-w)\,dw\,dv,
\qquad c(v)=\gamma^2e^{-\omega^2v^2/\kappa},\qquad \int_{\mathbb R}c=4g_0.
```

式 (62.5)。

在同一个固定复场上，这个已识别族有如下两个边界：

```math
\mathcal D_\zeta\Longrightarrow4\sqrt{g_0}B_{\rm two}
       \quad\hbox{于 }C(I),\quad\zeta\downarrow0,
\qquad
\sqrt\zeta\,\mathcal D_\zeta(\theta)
 \longrightarrow2\theta(|C(1)|^2-\gamma)
       \quad\hbox{于 }L^2(C(I)),\quad\zeta\to\infty.
```

式 (62.6)。

这里 $`B_{\rm two}`$ 的正负半轴为独立标准 Brownian motion，零点连续拼接；
第一收敛与整个固定 $`C`$ 所生成的 sigma 域混合。
第二式中 $`|C(1)|^2`$ 是均值 $`\gamma`$ 的指数变量。
这两个族边界不把 (62.4) 升级为同时改变实际 $`\zeta_M`$ 的定理。
单侧族极限由连续 Breuer–Major 定理覆盖；下述共同谱表示还识别两侧关系与整个场的混合性。

证明。首先在同一有限标签向量上作精确抵消，(62.2) 中括号等于
$`E_M(z)-2\mathfrak L Y_M^2-2z\mathcal Q_M-\mathcal J_M`$。
因为 $`s=(3/4)\log Q+O(1)`$，第 58 章的有限 Fourier 与取整估计乘上
$`\eta^2\delta^{-1/2}Q^2=O(Q^{11/4})`$ 后仍趋零。
其误差含 $`h=\exp(-c_hQ^3+O(1))`$；取整用 $`d\mathrm{Ci}(e^u)/du=\cos(e^u)`$，
不产生额外高频因子。于是 $`\mathcal V_M`$ 统一逼近零对角 Ci 二次型，其系数为

```math
K_M(\theta,k)=\frac{2\eta^2}{\sqrt\delta}e^{\theta/(2\eta^3)}
                  \mathrm{Ci}(\omega\eta e^{\theta/\eta^3}|k|),\quad k\ne0,
\qquad
\partial_\theta K_M(\theta,k)
 =\frac2{\eta\sqrt\delta}e^{\theta/(2\eta^3)}
       \{\tfrac12\mathrm{Ci}(\omega\eta e^{\theta/\eta^3}|k|)
                      +\cos(\omega\eta e^{\theta/\eta^3}k)\}.
```

式 (62.7)。

对原始有限取整路径不求导，只对这个光滑有限核求导。
$`\eta\sqrt\delta=\sqrt{\zeta_M}`$ 有正下界，故导数在全部滞后与固定参数紧区间上一致有界。
锚定原始矩阵 $`K_M(\theta)-K_M(0)`$ 的范数因此至多 $`C_IQ^2`$。
第 56 章 Hilbert 中心界 $`O_{\mathbb P}(Q^{-5/2}+q^{-1/2})`$
与紧的辅助组向量范数给出锚定精确中心误差 $`O_{\mathbb P}(Q^{-1/2})+o(1)`$。
这一步使用锚定后的矩阵，未放大旧的未定速误差。

在辅助乘积标签律下写中心组和为 $`U_j`$，方差为 $`v_j`$。
记 cutoff 占据比较质量 $`a_j=m_j/B^2`$；实际一行、两行相对点估计给出
$`\mathbb E_Sv_jv_l\le Ca_ja_l`$（$`j\ne l`$），且
$`a_j\le C\delta e^{-c(j\delta)^2}`$，低计数部分另有多项式乘 $`e^{-c\lambda}`$ 的总界。
这些是实际数据环境的读数估计，不是假设观测行独立。
辅助独立组的零对角二次型等距遂给出

```math
\mathbb E_S\mathbb E_{\mathsf Q}
 \left|\sum_{j\ne l}\mathrm{Ci}(\omega\eta e^{t/\eta^3}|j-l|)U_jU_l\right|^2
 \le C\delta/\eta^2+Q^Ce^{-c\lambda}.
```

式 (62.8)。

这里用 $`|\mathrm{Ci}(y)|\le C/y`$ 并求和 $`k^{-2}`$。
对包含 $`I`$ 的 $`[-T,T]`$，不等式
$`\sup_\theta|\int_0^\theta f(t)dt|^2\le T\int_{-T}^T|f(t)|^2dt`$
使 (62.7) 的 Ci 项在锚定积分中统一消失，平方误差为 $`O(\delta^2)+Q^Ce^{-c\lambda}`$。

令 $`\varphi_M=\omega\eta`$，并定义

```math
r_M(t)=\frac2{\sqrt{\zeta_M}}e^{t/(2\eta^3)},\qquad
v_M(t)=\frac{\eta(e^{t/\eta^3}-1)}\delta,
\qquad r_M\to2/\sqrt\zeta,\quad v_M(t)\to t/\zeta.
```

式 (62.9)。

两项在固定紧区间上一致收敛。
尚未转回后验之前，锚定量已在同一组向量上统一逼近

```math
\int_0^\theta r_M(t)\sum_{j\ne l}
  \cos\{\varphi_M(j-l)+\omega v_M(t)(x_j-x_l)\}U_jU_l\,dt.
```

式 (62.10)。

取核心 $`|j\delta|\le H_Q=\sqrt{D\log Q}`$，$`D`$ 固定且充分大。
实际占据浓缩与局部 Stirling 展开使核心内
$`v_j=\delta\rho(j\delta)(1+o(1))`$ 一致成立，且归一化前 Bernoulli 组和的最小方差至少 $`e^{c\lambda}`$。
有界导数核、上述两组质量界与积分不等式，使去除核心外至少一个指标的
平方统一误差至多 $`C_Te^{-c'H_Q^2}+Q^Ce^{-c\lambda}`$。
旧对数核使用可积的对角对数平方界，旧对角量使用平方方差时钟；
端点、轮廓、偶极子和紧频率场使用总质量与二阶空间矩的尾界。

所有核心组使用同一逆分布耦合。
独立 Bernoulli 和的局部误差 $`C/d`$ 给出标准化分布函数误差 $`Cd^{-1/3}`$；
其四阶矩一致有界。若分布函数误差为 $`\varepsilon`$，单调耦合下
$`\mathbb E|X-g|\le2T\varepsilon+C/T^3`$。
取 $`T=\varepsilon^{-1/4}`$，再插值一阶与四阶矩，得到

```math
\mathbb E|X-g|^2\le Cd^{-1/6},\qquad
G_j=\sqrt{v_j}g_j,\qquad
\mathbb E\sum_{\rm core}|U_j-G_j|^2\le Ce^{-c\lambda}.
```

式 (62.11)。

组间独立地在分布函数跳跃内随机化即可实现同一有限组和与这些正态坐标的耦合。
它是概率耦合，不是离散律向连续律的总变差收敛。
锚定矩阵、旧对数矩阵和对角量的原始范数分别至多
$`CQ^2`$、$`CQ^2(1+\log Q)`$、$`\delta^{-1/2}`$；
所以这个指数小向量误差同时处理整个新旧元组。
这里保留环境方差 $`v_j`$，不另作确定格质量替换。

在这一实 Gaussian 向量上定义旧场与载波场

```math
W_M(f)=\sum_jG_jf(x_j),\qquad
C_M^{\rm car}(f)=\sum_je^{i\varphi_Mj}G_jf(x_j).
```

式 (62.12)。

先固定空间区间 $`[-R,R]`$ 及有限个区间简单函数或光滑测试函数。
其 Hermitian 协方差趋于 $`\int f\bar g\rho`$。
载波伪协方差与旧场交叉项分别含 $`e^{2i\varphi_Mj}`$ 和 $`e^{i\varphi_Mj}`$。
对 $`h=1,2`$，几何部分和至多 $`2/|1-e^{ih\varphi_M}|`$，且
$`|1-e^{2i\varphi_M}|\ge4d_M/\pi`$、$`|1-e^{i\varphi_M}|\ge2d_M/\pi`$。
对固定紧支撑有界变差权重 $`w`$，离散分部求和给出

```math
\left|\delta\sum_je^{ih\varphi_Mj}w(j\delta)\right|
 \le\frac{C\delta}{|1-e^{ih\varphi_M}|}
       (\|w\|_\infty+\operatorname{Var}w).
```

式 (62.13)。

先按绝对质量分离环境误差：若固定区间上
$`\varepsilon_M(R)=\sup|v_j/(\delta\rho(j\delta))-1|`$，
则测试函数乘积的振荡 Gram 至多
$`C_{R,f,g}\{\delta/d_M+\varepsilon_M(R)\}`$，于数据概率中趋零。
环境误差未乘 $`1/d_M`$。
先固定空间截断、测试与旧核分区，取数组极限，再用 Gaussian 尾移除截断；
增长核心仅用于共同耦合，不进入有界变差常数。
因此没有 $`(\delta/d_M)\log Q\to0`$ 或其它隐藏余量。
在这些固定测试上先得到完整实部、虚部、旧场的 Gaussian Gram 极限；
再以 $`L^2(\rho)`$ 等距延拓极限场，并用尾界处理所需旧坐标。
不对任意 $`L^2`$ 等价类直接作逐点格采样。
无需先取相位收敛子列；伪协方差不能从 Hermitian 协方差推定。
有效窗口尺度的频率分离是经典 Fourier 机制；这里还需上述实际环境与共同后验比较。

同时保留移动的旧对角量。
其标准化矩阵 $`D_Q=\operatorname{diag}(v_j/\sqrt\delta)`$
满足 $`\|D_Q\|_{\rm op}=O(\sqrt\delta)`$、$`2\operatorname{tr}D_Q^2\to2g_0`$。
对任意上述移动实线性坐标向量 $`\ell_Q`$，Gaussian 积分恒等式为

```math
\mathbb E e^{i(g^\top Ag-\operatorname{tr}A)+i\ell_Q^\top g}
 =e^{-i\operatorname{tr}A}\det(1-2iA)^{-1/2}
       \exp\{-\tfrac12\ell_Q^\top(1-2iA)^{-1}\ell_Q\},\qquad A=tD_Q.
```

式 (62.14)。

行列式对数余项至多 $`C\|A\|_{\rm op}\operatorname{tr}A^2`$，
最后二次项与 $`\|\ell_Q\|^2`$ 的差至多 $`C\|A\|_{\rm op}\|\ell_Q\|^2`$。
故先得到联合 Gaussian 极限，再推出 $`N_2`$ 独立于两个场。
旧截距以同一旧场的有限矩形核逼近，块平方和趋于对应质量，
对角条带的 $`H^2`$ 积分至多 $`C\varepsilon(1+|\log\varepsilon|^2)`$，远处为 Gaussian 尾。
二阶等距传递逼近，保留 $`I_2(H;W_\rho)`$ 的共同实现。

令 $`F_{C,M}(v)=C_M^{\rm car}(e^{i\omega vx})`$。
任意固定频率区间上
$`\mathbb E_G\|F_{C,M}\|_{H^1}^2\le C\sum_j(1+x_j^2)v_j\le C`$。
一维 Sobolev 界给出统一范数与 $`1/2`$ Hölder 模的紧性；
结合 Gram 极限，载波 Fourier 场于紧区间 $`C`$ 拓扑收敛。
有限恒等式

```math
\sum_{j\ne l}\cos\{\varphi_M(j-l)+\omega v(x_j-x_l)\}G_jG_l
 =|F_{C,M}(v)|^2-\sum_jG_j^2
```

式 (62.15)。

给出必须保留的 Wick 扣除，$`\sum_jG_j^2\to\gamma`$ 于条件概率中成立。
(62.9)、(62.15) 和连续映射将 (62.10) 送到 (62.4)。
积分路径的 Lipschitz 常数被紧变量
$`C_T(\|F_{C,M}\|_\infty^2+\sum_jG_j^2)`$ 控制，故包含任意小时间增量的路径紧性。
有限谱路径统一逼近这些连续路径，因而确为 C-tight $`J_1`$ 收敛。

旧轮廓的辅助独立组方差时钟收敛且最大跳跃趋零；
旧 Fourier 场使用相同 $`H^1`$ 界，桥为确定投影，偶极子使用二阶空间矩。
负 Sobolev 测度与一阶偶极子分别用点质量平移在 $`H^{-\nu}`$
（$`\nu>1/2`$）的连续性、在 $`\nu>3/2`$ 的可微性及同一加权尾界。
至此始终是同一组向量。
条件近似误差的数据期望趋零给出数据概率中的条件误差控制，
环境子列原理得到条件有界 Lipschitz 收敛。
最后一次完整选择向量的后验总变差比较只转移有界测试与路径模事件。
支持置换等变性给出无条件固定支持一致版本；
原来错误概率 $`O(q^{-1})`$ 的共同方向事件同时对齐每个坐标。
没有使用实际无界矩收敛。

下面在已识别复场上辨认 (62.5)–(62.6)。
圆对称性给出
$`\mathbb EF_C(v)\overline{F_C(w)}=\gamma e^{-\omega^2(v-w)^2/(2\kappa)}`$，
伪协方差为零，所以整个复 Gaussian 场平稳。
配对公式使 $`|F_C(v)|^2-\gamma`$ 的协方差正是 (62.5) 的 $`c(v-w)`$；
其积分为 $`2\pi g_0/\omega=4g_0`$，由此得到能量协方差与平稳增量。
固定 $`\zeta`$ 时异号时间的协方差一般非零，不主张独立增量。

在 $`L^2(\rho;\mathbb C)`$ 上对应 Hermitian 核为

```math
K_{\zeta,\theta}(x,y)=2\sqrt\zeta\int_0^{\theta/\zeta}e^{i\omega v(x-y)}\,dv
 =\frac{2\sqrt\zeta}{\omega}
   \frac{\sin(A(x-y))+i[1-\cos(A(x-y))]}{x-y},
\qquad A=\omega\theta/\zeta.
```

式 (62.16)。

对角按连续延拓，核的迹为 $`2\theta\gamma/\sqrt\zeta`$。
在复线性积分约定下，Wick 积分 $`\iint K(x,y)C(dx)\overline{C(dy)}`$
是能量本身；有限坐标的标准 Hermitian 矩阵可取 $`K^\top`$，谱与迹不变。
不能丢掉核的虚部。
经典谱分解给出独立标准圆对称 $`Z_n`$ 下的
$`\sum_n\lambda_n(|Z_n|^2-1)`$；
由于 $`|Z_n|^2`$ 为单位指数变量，方差为 $`\sum\lambda_n^2`$，
第四累积量为 $`6\sum\lambda_n^4`$，第四矩至多方差平方的九倍。
非零时间核在对角邻域非零，故第四累积量严格正。
此处使用经典 Hermitian Gaussian 二次型结构，并未将实混沌的因子 $`48`$ 直接搬入。

对小 $`\zeta`$，令 $`h_\theta`$ 为从零到 $`\theta`$ 的有向区间示性函数。
将 (62.5) 改写成
$`4\iint h_\theta(x)h_u(y)\zeta^{-1}c((x-y)/\zeta)\,dx\,dy`$。
近似恒等核的质量为 $`4g_0`$，故极限为
$`16g_0\min(|\theta|,|u|)`$（同号），异号为零。
同一谱核的 Lebesgue Fourier 乘子是有向单侧频带
$`(4\pi\sqrt\zeta/\omega)1_{(0,\omega\theta/\zeta)}`$，负时间取负的反向区间。
经 $`\sqrt\rho`$ 共轭及 Plancherel，

```math
\|K_{\zeta,\theta}\|_{\rm op}
 \le(4\pi/\omega)\|\rho\|_\infty\sqrt\zeta.
```

式 (62.17)。

任意有限实线性组合也满足此界。
中心复二次型的特征函数对数为
$`-\tfrac12\operatorname{tr}K^2+O(\|K\|_{\rm op}\operatorname{tr}K^2)`$，
所以得到联合 Gaussian 极限。删去包含任意固定复线性方向的有限秩子空间，
Hilbert–Schmidt 误差至多 $`2\sqrt{\operatorname{rank}P}\|K\|_{\rm op}`$；
由等距与 Gaussian 正交性，极限独立于这些方向。
又增量方差至多 $`16g_0|\theta-u|`$，第四矩至多 $`C|\theta-u|^2`$，
故紧区间路径紧性成立。有限柱面有界测试的 $`L^1`$ 逼近，
把独立性延伸到整个固定复场生成的 sigma 域，得到 (62.6) 的混合版本。
这是联合测试的因式分解，不是给定整个场的条件律收敛。
单侧普通弱极限也可直接将连续 Breuer–Major 定理用于
$`\sqrt{2/\gamma}\operatorname{Re}F_C`$、$`\sqrt{2/\gamma}\operatorname{Im}F_C`$
两个独立平稳实场的 $`H_2(x)=x^2-1`$；平方相关可积且所有所需 Gaussian 矩有限。
上述谱论证额外钉住两侧的共同频带与整个场的混合关系。

最后写 $`X(v)=|F_C(v)|^2-\gamma`$。
$`\mathbb E|X(v)-X(0)|^2=2\gamma^2(1-e^{-\omega^2v^2/\kappa})\le Cv^2`$，
故

```math
\mathbb E\sup_{|\theta|\le T}
 \left|\sqrt\zeta\mathcal D_\zeta(\theta)-2\theta X(0)\right|^2
 \le4T\int_{-T}^T\mathbb E|X(t/\zeta)-X(0)|^2dt
 \le C_T\zeta^{-2}.
```

式 (62.18)。

这给出大参数的统一均方极限。
$`C(1)=\sqrt{\gamma/2}(g_1+ig_2)`$，所以其模平方为均值 $`\gamma`$ 的指数变量。
极限在时间 $`\theta`$ 的方差为 $`4\theta^2\gamma^2`$，第四累积量为 $`96\theta^4\gamma^4`$；
正时间的支持为 $`[-2\theta\gamma,\infty)`$。
实共振场还有 $`\mathbb EF(v)F(w)`$ 对应的第二个配对项，而这里该项为零。
这解释了反射 Brownian 与两侧独立 Brownian 的区别，也说明不能不加条件地删掉 (62.1) 的相位限制。

**定理 62.3（Gaussian 方差轮廓下标量载波的精确边界）。** 保持实际模型与
$`\eta^2\delta\to\zeta\in(0,\infty)`$，暂不施加相位间隔。
用原模型的精确中心组和 $`A_j`$ 定义
$`\mathcal C_M^{\rm act}=\sum_j e^{i\varphi_Mj}A_j`$；在共同全行事件外沿用截断定义。
该标量趋于 Hermitian 方差为 $`\gamma`$ 的圆对称复 Gaussian 律，
当且仅当 $`d_M/\delta\to\infty`$。
结论分别按定理 62.2 的条件后验与无条件固定支持口径成立。
此充要条件只针对标量载波，不声称是非线性能量过程的充要条件。

证明。上述相位无关的精确中心比较、共同耦合及总方差尾界，
将实际载波的有界测试联合转移到 (62.12) 的 Gaussian 载波；
这些步骤只使用调制系数模为一。充分性由 (62.13) 的两个谐波控制得到。
若条件失败，可取子列及最近整数 $`m_M`$，使
$`b_M=(\varphi_M-\pi m_M)/\delta\to b\in\mathbb R`$。
Gaussian 载波的 Hermitian 方差仍趋于 $`\gamma`$，伪协方差则为

```math
\sum_j e^{2i\varphi_Mj}v_j
 =\sum_j e^{2ib_Mx_j}v_j
 \longrightarrow\int e^{2ibx}\rho(x)\,dx
 =\gamma e^{-2b^2/\kappa}>0.
```

式 (62.19)。

固定空间截断上的一致相位收敛与环境相对误差给出 Riemann 极限，总方差尾界移除截断。
因为 $`\rho`$ 为偶函数，实虚部极限独立，方差分别为
$`\gamma(1+e^{-2b^2/\kappa})/2`$ 与 $`\gamma(1-e^{-2b^2/\kappa})/2`$。
非零参数的实部特征函数这一有界测试将其与圆对称律区分。
转回实际后验只转移该有界测试，没有从总变差比较推断实际无界矩收敛。
$`m_M`$ 为偶数时旧场交叉 Gram 保留调制 $`e^{ibx}`$，为奇数时交叉 Gram 因交替符号消失；
两种奇偶的伪协方差均为 (62.19)。因此旧新场独立不等于新场圆对称。

此边界依赖本模型 Gaussian 轮廓的 Fourier 变换处处严格为正。
经典矩形窗口可有精确消零：若 $`n\ge3`$、$`\xi_j`$ 独立标准实 Gaussian，
$`Z_n=n^{-1/2}\sum_{j=0}^{n-1}\xi_je^{2\pi ij/n}`$ 已经圆对称，
并独立于 $`n^{-1/2}\sum_j\xi_j`$，因为两个相应几何和都为零；
但对 $`\delta_n=1/n`$，相位间隔除以网格趋于 $`2\pi`$。
这不属于本实际模型，也不支持普遍 Fourier 必要性。
另一方面，取任意 $`\ell_M\to\infty`$ 且 $`\delta\ell_M\to0`$，
令 $`m_M`$ 为 $`\sqrt\zeta/(2\sqrt\delta)`$ 的最近整数，
$`\eta=2m_M+\delta\ell_M/\omega`$，则 $`\eta^2\delta\to\zeta`$、
$`d_M=\delta\ell_M\to0`$ 且 $`d_M/\delta=\ell_M\to\infty`$。
故 (62.1) 包含任意缓慢分离的合法实际谱参数。

## 追加锚（本行以下为增补区）

## 63. 有限多载波的共同别名簇与后验能量联合律

**定义 63.1（临界窗口与相位关系）。** 沿用第 62 章的原实验、精确组电荷、有限截距及旧联合坐标，固定正整数 $p$。对 $1\le a\le p$ 取确定性序列

$$
\eta_{a,M}\to\infty,\qquad
r_{a,M}=\eta_{a,M}^2\delta_M\to\zeta_a\in(0,\infty),\qquad
\phi_{a,M}=\omega\eta_{a,M},\qquad \omega=\pi/2.
$$

记 $\langle t\rangle$ 为 $t$ 模 $2\pi$ 在 $(-\pi,\pi]$ 内的代表。假定下列有限组实序列各自收敛到一个有限实数，或其绝对值趋于无穷：

$$
\delta_M^{-1}\langle\phi_{a,M}\rangle,\quad
\delta_M^{-1}\langle\phi_{a,M}-\pi\rangle,\quad
\delta_M^{-1}\langle\phi_{a,M}-\phi_{b,M}\rangle,\quad
\delta_M^{-1}\langle\phi_{a,M}+\phi_{b,M}\rangle.
\tag{63.1}
$$

这里 $a=b$ 也包括在内。有限极限分别记作 $b_a^0,b_a^\pi,d_{ab}^-,d_{ab}^+$；不存在有限极限的项记作 $\infty$，不赋予无穷项符号。若 $d_{ab}^-$ 或 $d_{ab}^+$ 有限，则称 $a,b$ 属于同一别名簇。

各窗口都使用同一后验标签向量。令

$$
s_{a,M}=\log(\eta_{a,M}/\delta_M),\qquad
z_{a,M}(\theta)=s_{a,M}+\theta/\eta_{a,M}^3,
$$

$$
V_{a,M}(\theta)=\eta_{a,M}^{3/2}e^{z_{a,M}(\theta)/2}
\left[\mathcal Z_M(z_{a,M}(\theta)\sqrt{\delta_M})
-J_M-2z_{a,M}(\theta)\sqrt{\delta_M}T_M\right],\qquad
D_{a,M}(\theta)=V_{a,M}(\theta)-V_{a,M}(0).
\tag{63.2}
$$

**定理 63.2（共同高斯载波及非高斯能量的联合分类）。** 条件 (63.1) 下，别名关系是等价关系。其每个等价类具有以下一种表示。

零相位类由所有 $b_a^0$ 有限的指标组成，取原实高斯测度 $W_0=W_\rho$，并令

$$
\mathcal C_a(f)=W_0(e^{ib_a^0x}f(x)).
\tag{63.3}
$$

$\pi$ 相位类由所有 $b_a^\pi$ 有限的指标组成，取与旧场独立的一份实高斯测度 $W_\pi$，令

$$
\mathcal C_a(f)=W_\pi(e^{ib_a^\pi x}f(x)).
\tag{63.4}
$$

其他每一类 $L$ 可选一个代表 $a_L$、符号 $\epsilon_a\in\{-1,1\}$ 和实数 $b_a$，使

$$
\delta_M^{-1}\langle\phi_{a,M}-\epsilon_a\phi_{a_L,M}\rangle\to b_a.
\tag{63.5}
$$

这一类取一份 proper 复高斯测度 $\mathcal C_L=(W_{L,1}+iW_{L,2})/\sqrt2$。各类的测度与 $W_0,W_\pi$ 相互独立，并定义

$$
\mathcal C_a(f)=
\begin{cases}
\mathcal C_L(e^{ib_ax}f(x)),&\epsilon_a=1,\\
\overline{\mathcal C_L(e^{-ib_ax}\overline{f(x)})},&\epsilon_a=-1.
\end{cases}
\tag{63.6}
$$

实测度对复函数按实部与虚部延拓，所有控制测度都是 $\rho(x)dx$。在原先的两个实际实验及概率范围内，有限向量 $(D_{a,M})_{a=1}^p$ 与完整旧联合坐标共同收敛，各固定紧区间上的路径是 C-tight 的。其极限为

$$
D_a(\theta)=2\sqrt{\zeta_a}\int_0^{\theta/\zeta_a}
\left(|\mathcal C_a(e^{i\omega vx})|^2-\gamma\right)dv.
\tag{63.7}
$$

$N_2$ 与整个载波测度族独立。所有旧坐标仍在 $W_0$ 上，特别是 $J_\infty=b_\star\gamma+I_2(H)$。原先的先验条件 BL 收敛、固定支持下的一致无条件收敛及共同方向事件均保持。

等价地，这个共同复高斯族满足

$$
\mathbb E\mathcal C_a(f)\overline{\mathcal C_b(g)}=
\begin{cases}
\int e^{id_{ab}^-x}f\overline g\,\rho\,dx,&d_{ab}^-\in\mathbb R,\\
0,&d_{ab}^-=\infty,
\end{cases}
$$

$$
\mathbb E\mathcal C_a(f)\mathcal C_b(g)=
\begin{cases}
\int e^{id_{ab}^+x}fg\,\rho\,dx,&d_{ab}^+\in\mathbb R,\\
0,&d_{ab}^+=\infty.
\end{cases}
\tag{63.8}
$$

这些极限数来自同一组实际相位，不能独立指定为任意矩阵元素。

证明。先核对相位关系。有限差关系与有限和关系分别写成 $\phi_a=\phi_b+\delta d+o(\delta)$ 和 $\phi_a=-\phi_b+\delta d+o(\delta)$，等式均模 $2\pi$。组合两式仍是其中一种，所以关系传递。若一个闭合关系链改变了代表的符号，则 $2\phi_{a_L}=O(\delta)$ 模 $2\pi$。由 (63.1)，该类必落在零相位或 $\pi$ 相位类。非例外类因此可以一致选择符号，并沿关系链得到 (63.5)；两条同符号链所得偏移之差趋于零，异符号链将导致刚排除的情况。例外类的偏移则直接由相对 $0$ 或 $\pi$ 的唯一小提升决定。特别地，非例外代表满足

$$
\operatorname{dist}(\phi_{a_L,M},\pi\mathbb Z)/\delta_M\to\infty.
\tag{63.9}
$$

下面先在同一个高斯参考向量上计算载波，随后才作平方映射。取独立标准实正态 $g_j$，保留实际环境方差 $v_j$，并令

$$
F_{a,M}(v)=\sum_j e^{i\phi_{a,M}j}\sqrt{v_j}g_j e^{i\omega vx_j},
\qquad x_j=j\delta_M.
\tag{63.10}
$$

对任一固定紧支撑光滑函数 $h$，离散分部求和给出

$$
\left|\sum_j\delta_M h(j\delta_M)e^{it_Mj}\right|
\le C_h\frac{\delta_M}{|1-e^{it_M}|}
\tag{63.11}
$$

只要分母不为零。若 $|\langle t_M\rangle|/\delta_M\to\infty$，右侧趋零；若 $\langle t_M\rangle/\delta_M\to d\in\mathbb R$，同一和是趋向 $\int h(x)e^{idx}dx$ 的黎曼和。先对固定光滑或区间简单测试作上述计算，再以等距延拓极限场到 $L^2(\rho)$；不对任意等价类直接逐点采样。以固定紧支撑逼近和高斯尾控制将结论扩展到所需 Fourier 测试函数的乘积。环境方差的替换误差按绝对值由总质量乘以其相对误差控制；它不再乘以 (63.11) 的分母。因此这里没有对数余量条件。

在 (63.10) 的两种交叉 Gram 矩阵中分别取 $t_M=\phi_{a,M}-\phi_{b,M}$ 和 $t_M=\phi_{a,M}+\phi_{b,M}$，得到 (63.8)。与旧实线性测试的交叉项取 $t_M=\phi_{a,M}$，只在零相位类留下原场关联。在 $\pi$ 相位类，乘子 $(-1)^j$ 的自乘恒为一而旧场交叉项消失，所以该类是一份共同实副本。非例外类的自身伪协方差消失，故 proper；(63.5) 则确定共享或共轭的关系。不同类的两种交叉项都消失。实、虚部分的联合高斯性把这些 Gram 极限转成联合独立性，并直接验证 (63.3)—(63.6) 构造了同一个极限族。

相位乘子模长恒为一，故在好环境子列的每个固定频率区间 $K$ 上

$$
\sup_M\mathbb E_G\|F_{a,M}\|_{H^1(K)}^2
\le C_K\sum_j(1+x_j^2)v_j=O(1).
\tag{63.12}
$$

$H^1(K)$ 的有界集在 $C(K)$ 中相对紧，故给出整个有限族的联合紧性。有限维 Gram 极限因此提升为共同的连续路径极限。

回到实际电荷之前，对每个 $a$ 从有限 Fourier 恒等式直接提取锚定系数

$$
a_{a,M,\theta}(k)=\frac{2\eta_{a,M}^2}{\sqrt{\delta_M}}
\left[e^{\theta/(2\eta_{a,M}^3)}\operatorname{Ci}
(\omega\eta_{a,M}e^{\theta/\eta_{a,M}^3}|k|)
-\operatorname{Ci}(\omega\eta_{a,M}|k|)\right],\quad k\ne0.
\tag{63.13}
$$

其导数是

$$
\partial_\theta a_{a,M,\theta}(k)
=\frac{2e^{\theta/(2\eta_{a,M}^3)}}{\sqrt{r_{a,M}}}
\left[\tfrac12\operatorname{Ci}(u)+\cos u\right],
\qquad u=\omega\eta_{a,M}e^{\theta/\eta_{a,M}^3}|k|.
\tag{63.14}
$$

相位的精确整数部分保留在 $e^{i\phi_{a,M}j}$ 中。对 $t$ 在固定紧区间内，余相位与 $\omega t(x_j-x_k)/r_{a,M}$ 的差至多为 $C\eta_{a,M}^{-3}|x_j-x_k|$。Ci 项为 $O(\eta_{a,M}^{-1})$。利用独立参考组的零对角二次型等距式，并对导数积分，可得同一实现上的一致近似

$$
D_{a,M}(\theta)
-\frac2{\sqrt{r_{a,M}}}\int_0^\theta
\left(|F_{a,M}(t/r_{a,M})|^2-\sum_jv_jg_j^2\right)dt
\longrightarrow0
\tag{63.15}
$$

在条件概率中成立，其全部 $a$ 的联合版本由有限性得到。

这里通向实际后验的误差须在新放大尺度上计算。临界条件给 $\eta_{a,M}=O(Q^{1/4})$；有限 Fourier 和 floor 误差乘以 $O(Q^{11/4})$ 仍由 $e^{-cQ^3}$ 吸收。全截止域的锚定矩阵及其导数原始范数为 $O(Q^2)$，故 Hilbert 精确中心误差至多为 $O_P(Q^{-1/2})+o_P(1)$。已有 $Q^{-60}$ 加权尾方差可同时删除全部窗口的尾向量。一份核心逆分布函数耦合把每组标准化误差控制为 $q^{-1/8}$，消去所有这些多项式损失；这里的核心未归一化 Bernoulli 方差下界是 $q^{9/10}$。同一个正态向量保留旧截距与所有旧线性坐标，不为窗口另取样。核心相对方差估计与尾界保证 (63.11)—(63.12) 的条件确定性环境极限。

高斯参考的对角统计具有算子范数 $O(\sqrt\delta)$ 和方差极限 $2g_0$。对有限个旧场及全部载波的实、虚测试方向作共同有限秩投影，删除这些方向的 Hilbert–Schmidt 代价至多为投影秩平方根乘以该算子范数。剩余二次型与投影向量精确独立，谱特征函数给出正态极限 $N_2$。再以有限秩逼近旧对数核 $H$、以路径紧性保留旧过程，得到 $N_2$ 与整个载波族和旧联合坐标的独立关系。

最后 $\sum_jv_jg_j^2\to\gamma$，因为其方差 $2\sum_jv_j^2=O(\delta)$。对共同连续场极限施加积分平方连续映射即得 (63.7)。参考二次型导数的二阶矩一致有界，第四增量矩至多为 $C|\theta-\psi|^4$，适用于任意小增量。实际 floor 路径由一致概率误差转为 C-tight 的 $J_1$ 路径。一次完整选择标签向量的后验 TV 比较只转移有界测试和概率事件；环境子序列论证给先验条件 BL 收敛，支持置换等变性给一致无条件结论，共同方向事件同时保留所有窗口。这些步骤不推出实际无界矩收敛。

**定理 63.3（能量依赖恰由别名簇区分）。** 在定理 63.2 下，取任意 $\theta_a,\theta_b\ne0$。每个非零时间边缘都非 Gaussian；两个极限能量 $D_a(\theta_a),D_b(\theta_b)$ 独立，当且仅当 $a,b$ 属于不同别名簇。不同簇的整个过程族也相互独立。若 $a$ 在零相位类，则 $D_a(\theta)$ 与旧端点平方 $Y^2-\gamma$ 对每个 $\theta>0$ 的协方差严格为正；其余类别的整个过程与旧场独立。

证明。记 $H_{ab}(v,w)=\mathbb EF_a(v)\overline{F_b(w)}$、$P_{ab}(v,w)=\mathbb EF_a(v)F_b(w)$，其中 $F_a(v)=\mathcal C_a(e^{i\omega vx})$。实高斯 Wick 公式给

$$
\operatorname{Cov}(D_a(\theta),D_b(\psi))
=4\sqrt{\zeta_a\zeta_b}
\int_0^{\theta/\zeta_a}\int_0^{\psi/\zeta_b}
\left(|H_{ab}(v,w)|^2+|P_{ab}(v,w)|^2\right)dv\,dw.
\tag{63.16}
$$

若 $d_{ab}^-$ 有限，第一项是 $|\widehat\rho(d_{ab}^-+\omega(v-w))|^2$；若 $d_{ab}^+$ 有限，第二项是 $|\widehat\rho(d_{ab}^++\omega(v+w))|^2$；相应无穷项为零。原高斯密度满足 $\widehat\rho(t)=\gamma e^{-t^2/(2\kappa)}>0$。同簇至少有一项处处为正；将两个积分改写成正向积分后，其协方差非零且符号为 $\operatorname{sgn}(\theta\psi)$，排除独立。异簇的独立来自整个高斯测度的联合独立，强于二次型零协方差。
正时间还有 $D_a(\theta)\ge-2\gamma\theta/\sqrt{\zeta_a}$，而上述自协方差严格为正；
非退化且有单侧界的变量不可能 Gaussian。负时间改用相应上界。
例如同一 proper 类的两个成员取相同 $\zeta$、零偏移与相反符号，则
$F_-(v)=\overline{F_+(-v)}$，在同一实现上 $D_-(\theta)=-D_+(-\theta)$。
其 Hermitian 交叉项为零，伪交叉项却为 $\widehat\rho(\omega(v+w))$；
分别重抽两个场会破坏这条路径关系。

零相位类同理满足

$$
\operatorname{Cov}(D_a(\theta),Y^2-\gamma)
=4\sqrt{\zeta_a}\int_0^{\theta/\zeta_a}
|\widehat\rho(b_a^0+\omega v)|^2dv>0.
\tag{63.17}
$$

其余类别使用与 $W_0$ 独立的测度，所以整个路径都与旧场独立。这是极限律的关系；没有断言有限后验能量独立或其协方差已收敛。

**定理 63.4（别名结构的实际可实现性与失谐压缩）。** 任给有限个正数 $\zeta_a$、至多一个零相位类、至多一个 $\pi$ 相位类及有限多个 proper 类，任给类内有限偏移和 proper 类内符号，均可由原 $\delta_M$ 序列上的确定性临界载波实现。有限失谐的单窗口结论则是第 60 章临界过程的确定性时间平移。

证明。为各 proper 类选取模符号彼此分离且不等于 $0,\pi$ 的固定相位 $\alpha_L$。在零类、$\pi$ 类和 proper 类分别设置相位目标 $\delta_Mb_a$、$\pi+\delta_Mb_a$ 和 $\epsilon_a\alpha_L+\delta_Mb_a$。选择整数 $n_{a,M}$ 使

$$
\eta_{a,M}=\frac{2\pi n_{a,M}+\text{相位目标}}\omega
=\sqrt{\zeta_a/\delta_M}+O(1).
\tag{63.18}
$$

最近整数选择即可做到，且最终 $\eta_{a,M}>0$。于是 $\eta_{a,M}^2\delta_M\to\zeta_a$，同时完整实现指定关系。整数整周部分调节临界宽度，模 $2\pi$ 部分调节载波关系，两者并不冲突。

若 $\omega\eta_M=\pi m_M+\delta_Mb_M$ 且 $b_M\to b$，在 $m_M$ 奇偶性固定的子列上令 $\eta_{0,M}=2m_M$ 及

$$
t_M(\theta)=\eta_{0,M}^3\log(\eta_M/\eta_{0,M})
+(\eta_{0,M}/\eta_M)^3\theta.
$$

在同一有限谱分辨率处有精确恒等式

$$
D_{\eta_M}(\theta)=
(\eta_M/\eta_{0,M})^{3/2}
\left[V_{\eta_{0,M}}(t_M(\theta))-V_{\eta_{0,M}}(t_M(0))\right].
\tag{63.19}
$$

$t_M(0)\to\zeta b/\omega$，且 $t_M(\theta)-t_M(0)\to\theta$ 在紧区间上一致。第 60 章的相应奇偶共同连续过程极限可以直接代入；随机常数项抵消，留下 (63.7) 中相应实类的移频积分。这个等式解释有限失谐边缘律的复用，但不能决定不同 proper 类之间的联合关系；后者由 (63.8) 的两套 Gram 极限给出。

## 追加锚（本行以下为增补区）

## 64. 亚临界载波的共同白噪声与观察区间的可识别性

**定义 64.1（可比载波与细相位关系）。** 保留第 63 章的实际实验、有限截距和同一后验标签向量，固定载波数 $p$。取确定性参考量 $\eta_{*,M}\to\infty$，令

$$
L_M=\eta_{*,M}^2,\qquad L_M\delta_M\to0,\qquad
\eta_{a,M}^2/L_M\to c_a\in(0,\infty),\qquad
\phi_{a,M}=\omega\eta_{a,M},\qquad\omega=\pi/2.
\tag{64.1}
$$

每个 $D_{a,M}$ 仍由 (63.2) 定义，先放大再在零点锚定。以 $\langle t\rangle\in(-\pi,\pi]$ 表示模 $2\pi$ 的代表，假定

$$
\frac{L_M}{\omega}\langle\phi_{a,M}\rangle,\quad
\frac{L_M}{\omega}\langle\phi_{a,M}-\pi\rangle,\quad
\frac{L_M}{\omega}\langle\phi_{a,M}-\phi_{b,M}\rangle,\quad
\frac{L_M}{\omega}\langle\phi_{a,M}+\phi_{b,M}\rangle
\tag{64.2}
$$

各自具有有限实极限或绝对值趋于无穷，包括 $a=b$。后两类有限极限记为 $d^-_{ab},d^+_{ab}$。有限差或有限和关系确定共同别名簇。零类与 $\pi$ 类的偏移分别是前两类有限极限 $b_a$；其余每类选代表相位 $q_{C,M}$，取相容符号 $\sigma_a\in\{-1,1\}$ 与偏移

$$
\frac{L_M}{\omega}
\langle\phi_{a,M}-\sigma_a q_{C,M}\rangle\longrightarrow b_a.
\tag{64.3}
$$

相位关系的相容性与第 63 章相同，分辨率改为 $\omega/L_M$。特别是一般类满足
$L_M\operatorname{dist}(q_{C,M},\pi\mathbb Z)\to\infty$。
参考量 $\eta_{*,M}$ 仅规定尺度，不要求它本身是某个预先固定相位的载波。

**定理 64.2（实际亚临界联合过程）。** 对每个零类或 $\pi$ 类取一份标准 Brownian motion，并令
$B_{C,\mathrm{odd}}(t)=\operatorname{sgn}(t)B_C(|t|)$。
对每个其余的簇取一份标准两侧 Brownian motion $B_{C,\mathrm{two}}$，其正负两半独立。
不同簇的噪声相互独立。则各固定紧区间上的实际有限过程族联合 C-tight 收敛，其极限为

$$
D_a(\theta)=4\sqrt{g_0c_a}
\left[B_{C,\mathrm{odd}}(b_a+\theta/c_a)-B_{C,\mathrm{odd}}(b_a)\right]
\tag{64.4}
$$

于实类，以及

$$
D_a(\theta)=4\sigma_a\sqrt{g_0c_a}
\left[B_{C,\mathrm{two}}(\sigma_a(b_a+\theta/c_a))
-B_{C,\mathrm{two}}(\sigma_a b_a)\right]
\tag{64.5}
$$

于一般类。整个 Brownian 族、$N_2$ 与旧实高斯测度 $W_\rho$ 相互独立，包括零类。旧联合坐标保持在同一 $W_\rho$ 上，特别是
$J_\infty=b_\star\gamma+I_2(H;W_\rho)$。
原先的先验条件 BL 收敛、固定支持下的一致无条件收敛及共同方向事件保持；实际路径取紧区间 $J_1$ 拓扑。

任意有限个正比率 $c_a$、相容簇、偏移与符号均可在原合法算术序列上实现。无需对数余量，也无需一般类代表相位有通常意义的极限。

证明。第 63 章的有符号关系组合证明同样适用。反向闭链迫使代表接近 $0$ 或 $\pi$；(64.2) 排除在两者之间交替的例外类，其他类可以一致定向。实现性可直接取相位目标 $\psi_{a,M}=q_C+\omega b_a/L_M$ 或
$\psi_{a,M}=\sigma_aq_{C,M}+\omega b_a/L_M$，并选最近整数

$$
n_{a,M}=\operatorname{round}
\frac{\omega\sqrt{c_aL_M}-\psi_{a,M}}{2\pi},\qquad
\eta_{a,M}=\frac{2\pi n_{a,M}+\psi_{a,M}}{\omega}.
\tag{64.6}
$$

于是 $\eta_{a,M}=\sqrt{c_aL_M}+O(1)$，相位目标精确实现。

先作实际有限谱比较。记 $\eta=\eta_{a,M}$，固定紧区间 $I$。有限 Fourier 恒等式与精确中心取消给出零对角系数

$$
K_{a,\theta}(k)=2\delta^{-1/2}b_{a,\theta}(|k|),\qquad
b_{a,\theta}(k)=\eta^2
\left[e^{\theta/(2\eta^3)}
\operatorname{Ci}(\omega\eta e^{\theta/\eta^3}k)
-\operatorname{Ci}(\omega\eta k)\right].
\tag{64.7}
$$

全部 Fourier、权重和 floor 误差乘以至多 $O(Q^{11/4})$，仍被 $e^{-cQ^3}$ 吸收。
这里 $\eta_a=O(Q^{1/4})$，而 $z_{a,M}(\theta)\sqrt\delta\to0$，所以原频率区间最终包含全部固定紧区间。
对 $y\ge1$ 与有界小量 $l$，Ci 尾积分及其一次分部积分给出

$$
|\operatorname{Ci}(ye^l)-\operatorname{Ci}(y)|
\le C\min(|l|,y^{-1}),\qquad
|\operatorname{Ci}(y)|\le C/y.
\tag{64.8}
$$

拆开放大因子的变化可得

$$
|b_{a,\theta}(k)|
\le C_I\left[\min(\eta^{-1},\eta/k)+\frac1{\eta^2k}\right]
\le C_I\min(\eta^{-1},\eta/k).
\tag{64.9}
$$

全计数截止域上的原始矩阵范数因此至多
$C_I\delta^{-1/2}\eta(1+\log Q)\le C_IQ^{1/2}(1+\log Q)$。
与第 56 章的 Hilbert 精确中心界组合，新的中心误差为
$O_P(Q^{-2}(1+\log Q))+o_P(1)$。
同一 $Q^{-60}$ 尾向量与核心 $q^{-1/8}$ 逆分布耦合同时控制全部有限载波和旧坐标。
此处核心 Bernoulli 方差下界 $q^{9/10}$ 是未归一化方差。
在同一标准正态向量上改用 Gaussian 单元质量 $m_j^\circ$，相对误差
$O_P(Q^{-1}(1+\log Q))$ 产生路径误差
$O_P(Q^{-1/2}(1+\log Q)^2)$。
这些是新放大尺度上的界；没有再放大旧的未量化误差。

令 $G_j=\sqrt{m_j^\circ}g_j$。在共同核心上，实际向量由连续参考二次型
$D^G_{a,M}(\theta)=\sum_{j\ne k}K_{a,\theta}(j-k)G_jG_k$
一致概率逼近。定义

$$
w_\delta(k)=\delta^{-1}\sum_jm_j^\circ m_{j+k}^\circ,\qquad
g(x)=\int\rho(y)\rho(y+x)\,dy.
$$

Gaussian 密度的单元平均在 $L^2$ 中逼近原密度，Cauchy–Schwarz 与平移等距给出

$$
\sup_k|w_\delta(k)-g(k\delta)|\le C\delta+Ce^{-cH_Q^2},
\qquad 0\le w_\delta(k)\le C.
\tag{64.10}
$$

这个估计覆盖增长的滞后。Ci 的两次分部积分还给出

$$
\ell_{a,\theta}(k)=\frac{\eta_a}{\omega k}
\left[\sin\left((\phi_a+\omega\theta/\eta_a^2)k\right)
-\sin(\phi_ak)\right],
\quad
\sup_{\theta\in I}\sum_{k\ge1}|b_{a,\theta}(k)-\ell_{a,\theta}(k)|^2\to0.
\tag{64.11}
$$

具体地，Ci 三阶余项的 $\ell^2$ 范数为 $O(\eta_a^{-1})$，
锚定余弦项与正弦振幅误差各为 $O(\eta_a^{-2})$。
相位线性化误差为 $O_I(\eta_a^{-5})$；由
$\sum_{k\ge1}\min(k|u|,2)^2/k^2\le C|u|$，
它的系数平方和为 $O(\eta_a^{-3})$。
同时 $\sup_{\theta\in I}\sum_k|\ell_{a,\theta}(k)|^2\le C_I$。
这些估计先用于协方差；路径紧性另由精确系数证明。

两种滞后方向和 Gaussian 配对式给出

$$
\operatorname{Cov}(D^G_{a,M}(\theta),D^G_{b,M}(\psi))
=16\sum_{k\ge1}w_\delta(k)b_{a,\theta}(k)b_{b,\psi}(k).
\tag{64.12}
$$

对固定 $A$，在 $k\le AL_M$ 上有 $k\delta\to0$，故 (64.10) 的权重一致趋于 $g_0$。
剩余系数积的绝对和至多 $CL_M\sum_{k>AL_M}k^{-2}\le C/A$。
先令 $M\to\infty$ 再令 $A\to\infty$，可以把 (64.12) 化为
$16g_0\sum_k\ell_{a,\theta}(k)\ell_{b,\psi}(k)$，无相位间距分母。

使用经典余弦级数
$C(t)=\sum_{k\ge1}\cos(kt)/k^2
=\pi^2/6-\pi|\langle t\rangle|/2+\langle t\rangle^2/4$。
其唯一尖点位于 $2\pi\mathbb Z$，在代表边界 $\pi$ 处光滑。
积化和差后，有限相位差与相位和分别留下

$$
\begin{aligned}
\Delta_-(d;A,B)&=|d+A-B|-|d+A|-|d-B|+|d|,\\
\Delta_+(d;A,B)&=|d+A+B|-|d+A|-|d+B|+|d|.
\end{aligned}
$$

因此极限协方差是

$$
8g_0\sqrt{c_ac_b}
\left[
-1_{\{d^-_{ab}\ {\rm 有限}\}}
\Delta_-(d^-_{ab};\theta/c_a,\psi/c_b)
+1_{\{d^+_{ab}\ {\rm 有限}\}}
\Delta_+(d^+_{ab};\theta/c_a,\psi/c_b)
\right].
\tag{64.13}
$$

若某项的相位距离乘以 $L_M$ 逃逸，四个相位最终处于余弦和的同一光滑二次分支。
其混合差分只有 $O(L_M^{-2})$，乘以 $\eta_a\eta_b=O(L_M)$ 后趋零。
有限相位项则由尖点的绝对值给出 (64.13)。
分别代入奇延拓与两侧 Brownian 协方差，即得 (64.4)—(64.5) 的共同协方差，包括共轭方向外侧的 $\sigma_a$。

还须证明联合 Gaussian 性。把参考矩阵作用在标准正态向量上，以 $\sqrt{m_j^\circ}$ 作 Schur 权重。
令 $r_a=\eta_a^2\delta$，由 (64.9)，滞后区间 $[1,\eta_a^2]$、
$(\eta_a^2,\delta^{-1}]$ 和 $(\delta^{-1},\infty)$ 分别给出
$C\sqrt{r_a}$、$C\sqrt{r_a}(1+|\log r_a|)$ 和 $C\sqrt{r_a}$。
最后一段只需 $|k|^{-1}\le\delta$ 与总质量有界，故对边缘行同样成立。于是

$$
\sup_{\theta\in I}\|\mathcal K_{a,\theta}\|_{\rm op}
\le C_I\sqrt{r_a}(1+|\log r_a|)\longrightarrow0.
\tag{64.14}
$$

对角坐标的算子范数为 $O(\sqrt\delta)$，方差趋于 $2g_0$；
它与全部新零对角矩阵的 Hilbert–Schmidt 内积精确为零。
任何固定线性组合仍有有界 Hilbert–Schmidt 范数与趋零的算子范数。
对其特征值展开
$\sum_j[-it\lambda_j-\frac12\log(1-2it\lambda_j)]$
证明联合 Gaussian 极限，随后才由零交叉协方差得到与 $N_2$ 的独立性。
对包含有限旧线性方向的投影 $P$，删除这些方向的误差至多
$2\sqrt{\operatorname{rank}P}\|\mathcal K\|_{\rm op}$。
剩余二次型与这些方向精确独立。先作有限圆柱逼近，再保留旧 $H$ 的共同矩形逼近和旧路径紧性，得到与整个旧场的联合独立性。
零类也适用这一步；决定性条件是新算子范数趋零。

最后证明任意小时间增量的紧性。直接在 (64.7) 使用 (64.8)，对 $d=|\theta-\psi|\le1$ 得

$$
|b_{a,\theta}(k)-b_{a,\psi}(k)|
\le C_I\left[\min(d/\eta_a,\eta_a/k)+\frac{d}{\eta_a^2k}\right],
\qquad
\sum_{k\ge1}|b_{a,\theta}(k)-b_{a,\psi}(k)|^2\le C_Id.
\tag{64.15}
$$

第二个式子在 $k=\eta_a^2/d$ 处分割；该分点超过实际截止也不影响上界。
Gaussian 配对与第二混沌的第四矩界因此给出
$\mathbb E|D^G_{a,M}(\theta)-D^G_{a,M}(\psi)|^4\le C_I|\theta-\psi|^2$。
参考路径从零出发且连续，Kolmogorov 判据给出有限向量的联合紧性。
统一概率逼近使实际 floor 路径 C-tight。
旧 $J$、对角和线性坐标始终使用同一耦合；其质量尾、方差时钟及固定频率路径界沿用原证明。
一次完整标签向量的 TV 比较只转移有界测试和概率事件。
好环境子序列给出条件 BL 收敛，支持置换等变性给出一致无条件结论，共同方向事件同时保留整个向量。
这不转移实际无界矩。

**定理 64.3（指定增量的独立性由区间交叠决定）。** 记 $I_{u,v}$ 为有向区间指示函数：
$u<v$ 时为 $1_{(u,v]}$，$u>v$ 时为 $-1_{(v,u]}$，相等时为零。
对极限增量 $D_a(v)-D_a(u)$，在一般类定义

$$
f_{a;u,v}(y)=\sigma_a
I_{\sigma_a(b_a+u/c_a),\,\sigma_a(b_a+v/c_a)}(y),\qquad y\in\mathbb R,
\tag{64.16}
$$

在实类定义

$$
f_{a;u,v}(y)=
I_{b_a+u/c_a,\,b_a+v/c_a}(y)
+I_{b_a+u/c_a,\,b_a+v/c_a}(-y),\qquad y>0.
\tag{64.17}
$$

同类两个增量的协方差为

$$
16g_0\sqrt{c_ac_b}\int f_{a;u,v}(y)f_{b;u',v'}(y)\,dy,
\tag{64.18}
$$

不同类的协方差为零。任意有限组增量相互独立，当且仅当对应 Gram 矩阵的所有非对角元为零。
两个非零单增量在同类中独立，当且仅当有效区间交集的 Lebesgue 测度为零：
一般类使用 (64.16) 的区间，实类使用原区间在绝对值映射下的像。
实类的折叠重数影响协方差大小，不改变零交叠判据。

对有限线性读数，先在每类把函数改为
$\sum_a\alpha_a\sqrt{c_a}f_{a;u_a,v_a}$；
独立性等价于这些直和空间向量正交，此时可以出现带符号的抵消。
整个限制过程的独立性则要求全部时间读数所张成的闭子空间正交。

证明。把一般类的两侧 Brownian 增量写成实白噪声作用于有向指示函数，即得 (64.16)。
奇延拓满足
$B_{\rm odd}(t)=\mathcal W(\operatorname{sgn}(t)1_{(0,|t|]})$，
故跨过零点时两侧贡献相加，得到 (64.17) 的正折叠。
每个单增量的函数符号恒为 $\operatorname{sgn}(v-u)$；折叠后可以取重数二，但不能变号。
因此两个单增量的内积在正测度交叠上不可能抵消。
Gaussian 联合律把零内积变成独立性，并给出有限向量与闭子空间的判据。

这些区别都可由 (64.6) 实现。例如取 $c_1=c_2=1$。
在同向一般类中，$b_1=0,b_2=2$ 的正时间一读数使用区间 $[0,1]$ 和 $[2,3]$，相互独立；
把过程观察区间增至 $[0,3]$ 后，部分读数的区间开始交叠。
在实类中，$b_1=1,b_2=-2$ 的正时间一读数使用 $[1,2]$ 和 $[-2,-1]$，原区间不交但折叠相同，两个读数相等。
取两个不交且等长的正径向区间，其独立等方差读数 $X_1,X_2$ 满足
$X_1+X_2$ 与 $X_1-X_2$ 独立；这里才发生有符号抵消。
同一一般类、零偏移、相同比率且相反方向还满足
$D_-(\theta)=-D_+(-\theta)$：
其两个正半轴限制相互独立，整个双向过程仍共享同一噪声。
这些是极限律的关系，不宣称有限后验独立或其协方差收敛。

**定理 64.4（单窗口的局部不可辨与全局失谐分类）。** 对单载波仅假定
$\eta_M\to\infty$、$\eta_M^2\delta_M\to0$，无需固定奇偶性。令

$$
a_M=\frac{\eta_M^2}{\omega}
\operatorname{principal}_{\pi}(\omega\eta_M),
\qquad \operatorname{principal}_{\pi}\in(-\pi/2,\pi/2].
\tag{64.19}
$$

若 $a_M\to a\in\mathbb R$，则实际锚定过程趋于
$4\sqrt{g_0}X_a(\theta)$，其中
$X_a(\theta)=B_{\rm odd}(a+\theta)-B_{\rm odd}(a)$。
若 $|a_M|\to\infty$，则极限为 $4\sqrt{g_0}B_{\rm two}$。
两者都与完整旧场及 $N_2$ 联合独立。
实际过程在所有固定紧区间上具有一个连续的联合极限，当且仅当 $a_M$ 在实直线的一点紧化中收敛；无穷点表示绝对值逃逸。

对固定 $S,T>0$，参考过程 $X_a$ 在 $[-S,T]$ 上具有标准两侧 Brownian 律，当且仅当

$$
a\in(-\infty,-T]\cup[S,\infty).
\tag{64.20}
$$

因此实际过程在这个固定区间上趋于 $4\sqrt{g_0}B_{\rm two}$ 的充要条件是
$\operatorname{dist}(a_M,(-\infty,-T]\cup[S,\infty))\to0$；
在所有紧区间上同时如此的充要条件才是 $|a_M|\to\infty$。

证明。单载波的自协方差中整数奇偶因子自乘消失，所以 (64.12)—(64.15) 的论证无需 (64.2) 中例外类的奇偶稳定。
余弦和的自差分给出

$$
\begin{aligned}
2\operatorname{Cov}(X_a(\theta),X_a(\psi))
={}&|\theta|+|\psi|-|\theta-\psi|\\
&+|2a+\theta+\psi|-|2a+\theta|-|2a+\psi|+|2a|.
\end{aligned}
\tag{64.21}
$$

有限 $a_M$ 直接趋于此式；绝对值逃逸时第二行在每个固定区间最终恒为零。
前述小算子与紧性证明分别识别这两种实际联合极限。

若 $a>0$，有
$\operatorname{Var}X_a(\theta)-|\theta|
=2\min\{(-a-\theta)_+,a\}$。
因此只在 $\theta\ge-a$ 的范围内具有两侧 Brownian 的全部限制律；
该范围内原 Brownian 时间与锚点 $a$ 均非负，独立增量给出充分性。
负 $a$ 由时间反射得到。$a=0$ 时每个单点方差虽仍为 $|\theta|$，
异号时间协方差为 $-\min(|\theta|,|\psi|)$，与两侧独立律不同。
这证明 (64.20)，含边界点。
任意不含零点的观察区间还必须核对锚点：
例如 $a=1$、区间 $[-3,-2]$ 不经过反射中心 $-1$，
但 $X_1(-2)=-2B(1)$ 的方差为四，不能具有方差为二的两侧 Brownian 读数。

全部有向时间上的过程律识别有限的带符号参数 $a$。
正 $a$ 的方差偏离集合是 $(-\infty,-a)$，负 $a$ 的偏离集合是 $(-a,\infty)$；
$a=0$ 与无穷点则由异号协方差区分。
有限参数下还有同一实现上的关系
$X_a(\theta)+X_a(-2a-\theta)=X_a(-2a)$。
把 $a$ 改为 $-a$ 对应时间反射，不是在保留时间方向时得到相同的律。

这一族在一点紧化上连续：有限处由共同 Brownian 连续路径的平移得到，
无穷处在任意固定紧区间最终已具有两侧 Brownian 律；
统一界
$\operatorname{Var}(X_a(\theta)-X_a(\psi))\le2|\theta-\psi|$
给出共同紧性。实际过程的紧性也对相位一致。
对子列取一点紧化中的聚点，实际极限定理与过程律的单射性给出全局收敛的充要条件。
在固定 $[-S,T]$ 上同理使用 (64.20)，得到距离条件。
这些都是路径律与有界测试的推论，没有利用实际矩收敛。

最后，固定 $A>\max(S,T)$，取 $m_M=\lfloor Q^{1/8}\rfloor$，
令 $b_M$ 在 $A,-A$ 间交替，设
$\eta_M=2m_M+b_M/(4m_M^2)$。
则 $\eta_M^2\delta_M\to0$，$a_M=b_M+o(1)$。
该实际序列在指定有限区间上有同一个两侧 Brownian 极限，全局却有两个不同的子列极限。
这在原实验内实现了局部读数不足以识别全局失谐的区别。

## 追加锚（本行以下为增补区）

## 65. 未锚定谱的失谐紧性与三种常数分量

**定义 65.1（未锚定残差和统一失谐幅度）。** 保留原实际实验、固定幅度与 beta、完整固定总量后验、精确中心及定义 54.1 的有限截距。对确定性 $\eta_M\to\infty$，令

$$
r_M=\eta_M^2\delta_M,\quad s_M=\log(\eta_M/\delta_M),\quad
s_M\sqrt{\delta_M}\le U/2,\quad
z_M(\theta)=s_M+\theta/\eta_M^3.
\tag{65.1}
$$

记 $\omega=\pi/2$，唯一选取
$d_M\in(-\pi/2,\pi/2]$ 与整数 $m_M$ 使
$\omega\eta_M=\pi m_M+d_M$。本章使用未在零点锚定的过程

$$
\begin{aligned}
\mathcal V_M(\theta)
&=\eta_M^{3/2}e^{z_M(\theta)/2}
\left[\mathcal Z_M(z_M(\theta)\sqrt\delta)-J_M
-2z_M(\theta)\sqrt\delta\,T_M\right],\\
\mathcal D_M(\theta)&=\mathcal V_M(\theta)-\mathcal V_M(0),\qquad
\mathcal A_M^2=\frac{\eta_M^2d_M^2}{\delta_M+|d_M|}.
\end{aligned}
\tag{65.2}
$$

所有时间与旧坐标均使用同一个后验标签向量。$r_M$ 表示网格尺度比，不表示原模型的固定信号幅度。

**定理 65.2（实际未锚定过程的紧性充要条件）。** 在每个包含零的固定紧区间 $I$ 上，实际 $\mathcal V_M$ 的紧 $J_1$ 路径律紧，当且仅当 $\limsup_M\mathcal A_M<\infty$。条件成立时极限支撑于连续路径；加入旧联合坐标和 $T_M$ 不改变该判据。$\mathcal D_M$ 对所有满足 (65.1) 的序列均 C-tight，无需 $\mathcal A_M$ 有界。

紧性同时具有两种原实验意义：每个固定支持下的一致无条件紧性，以及先验数据概率中的后验紧性。后者意为对任意 $\varepsilon,\alpha>0$，存在紧集 $K\subset D(I)$ 满足

$$
\limsup_M\Pr_{\rm data}\{\Pi_M(K^c)>\varepsilon\}\le\alpha.
\tag{65.3}
$$

若沿某子列 $\mathcal A_M\to\infty$，则对每个有限 $R$，

$$
\Pr_{\rm data}\left\{
\Pi_M(|\mathcal V_M(0)|>R)>1/240
\right\}\longrightarrow1.
\tag{65.4}
$$

这里的必要性是实际概率结论，不由实际方差发散推断。单点区间 $I=\{0\}$ 按标量结论理解。

证明。先在最终放大尺度作有限恒等式比较。第 54 章的 Fourier 权重、调和项与 Ci 展开在完整计数截止域上给出

$$
\mathcal V_M(\theta)=\sum_{j\ne l}K_M(\theta,j-l)A_jA_l+o_P(1),\quad
K_M(\theta,k)=\frac{2\eta^2}{\sqrt\delta}e^{\theta/(2\eta^3)}
\operatorname{Ci}(\omega\eta e^{\theta/\eta^3}|k|).
\tag{65.5}
$$

误差在固定时间紧区间一致。该比较使用精确的
$\mathcal Q_M=V_M+\sqrt\delta T_M$ 和原 $J_M$，所以大项在放大前恰好取消。
原 Fourier 误差记为 $\varepsilon_M$；其界为 $e^{-cQ^3}$ 乘以固定次幂因子。
由 (65.1) 有 $\log\eta=O(Q^{1/4})$，故

$$
Q^2\eta^2\delta^{-1/2}\varepsilon_M\to0,
\qquad Q^2\eta^3\varepsilon_M\to0.
\tag{65.6}
$$

第二项预先保留给 $\sqrt r\mathcal D_M$。floor 改变 Ci 自变量的对数至多 $O(he^{-z})$，而 $d\operatorname{Ci}(v)/d\log v=\cos v$，因此这个误差也受控。上述论证允许 $\eta$ 达到 $\exp(O(Q^{1/4}))$。

零点分解为正弦、余弦与余项：

$$
\begin{aligned}
S_M(\theta,k)&=\frac{2\eta}{\omega\sqrt\delta}
\frac{\sin[(\omega\eta+\omega\theta/\eta^2)k]}{k},\\
C_M(k)&=-\frac{2\cos(\omega\eta k)}{\omega^2\sqrt\delta k^2},\\
K_M(0,k)&=S_M(0,k)+C_M(k)+E_M(k),\qquad
|E_M(k)|\le\frac{C}{\eta\sqrt\delta |k|^3}.
\end{aligned}
\tag{65.7}
$$

对 $h_M=1+\mathcal A_M$，先将静态矩阵除以 $h_M$。令 $D=|d_M|$。
当 $D\le\delta$ 时，$|S_M(0,k)|/h_M\le C$；当 $D\ge\delta$ 时，

$$
\frac{|S_M(0,k)|}{h_M}
\le\frac{C}{\sqrt{\delta D}}\min(D,|k|^{-1}).
\tag{65.8}
$$

全截止域有至多 $CQ^2$ 个组，所以相应原始矩阵范数分别至多
$CQ^2$ 与 $C\delta^{-1}(1+\log Q)$。余弦、余项的范数至多
$C\delta^{-1/2}$ 与 $C/(\eta\sqrt\delta)$。
另一方面精确微分给出

$$
\partial_\theta K_M(\theta,k)=
\frac{2e^{\theta/(2\eta^3)}}{\eta\sqrt\delta}
\left[\cos(\omega\eta e^{\theta/\eta^3}k)
+\tfrac12\operatorname{Ci}(\omega\eta e^{\theta/\eta^3}|k|)\right].
\tag{65.9}
$$

其绝对值至多 $C_I/\sqrt r$，乘以 $\sqrt r$ 后至多 $C_I$。
故锚定矩阵范数至多 $C_IQ^2/\sqrt r$，缩放锚定矩阵范数至多 $C_IQ^2$。
第 56 章 Hilbert 精确中心位移
$\|e\|_2=O_P(Q^{-5/2}+q^{-1/2})$ 因此在归一化静态量上消失；
锚定量上的误差为 $O_P(Q^{-1/2}/\sqrt r)+o_P(1)
=O_P(Q^{-1/4}/\eta)+o_P(1)$，缩放锚定量上的误差为 $O_P(Q^{-1/2})+o_P(1)$。
这一步没有把任意大 $\eta$ 的未归一化原始矩阵误当成多项式有界。

在同一核心 $|j\delta|\le R_c=\sqrt{D_*\log Q}$ 上保留环境方差
$v_j=d_j/B^2$，不另换确定性质量。原实际一行、两行比较与 Stirling 界给出共同好环境：

$$
v_j=\delta\rho(j\delta)(1+o(1))\text{ 一致成立},\quad
v_j\le C\delta e^{-c(j\delta)^2},\quad d_j\ge q^{9/10}.
\tag{65.10}
$$

最后的下界针对未归一化 Bernoulli 方差 $d_j$。不同组的环境乘积满足
$E_{\rm data}v_jv_l\le Ca_ja_l$，其中 $a_j$ 是比较组占用均值除以 $B^2$，具有同一 Gaussian 包络和指数小的远计数尾。
归一化静态系数逐项至多 $C\delta^{-1/2}$，锚定导数至多 $C_I/\sqrt r$。
由独立辅助组的二次型等距，含至少一个核心外标记的项，其平均条件方差分别至多

$$
C\delta^{-1}\left[e^{-cR_c^2}+Q^Ce^{-c\lambda}\right],\qquad
C_Ir^{-1}\left[e^{-cR_c^2}+Q^Ce^{-c\lambda}\right].
\tag{65.11}
$$

锚定项先积分导数再取上确界；缩放锚定项的界去掉 $r^{-1}$。
由于 $r^{-1}\le\delta^{-1}$ 最终成立，取一个固定且充分大的 $D_*$ 即使全部尾消失。
旧 $H$ 的对角邻域与空间尾、旧对角量和线性路径也用同一个核心。
上述期望先对每个数据集上定义的截止组计算，再按概率删去坏数据事件，不在无界矩中丢弃事件。

一次核心逆分布耦合产生 $G_j=\sqrt{v_j}\xi_j$，$\xi_j$ 为共同独立标准正态。
核心未归一化方差指数增长，既有耦合误差乘以前述全部多项式矩阵范数仍趋零。
因此在一次最终后验 TV 转移之前，可以同时比较
$\mathcal V_M(0)/(1+\mathcal A_M)$、完整 $\mathcal D_M$、所需的 $\sqrt r\mathcal D_M$ 与旧联合坐标。
这里没有推断发散静态量的未归一化比较。

令 $\Gamma_M(k)=\sum_jv_jv_{j+k}$，求和仅用核心。
(65.10) 的平方配方和固定空间内的下界给出

$$
\Gamma_M(k)\le C\delta e^{-c(k\delta)^2},\qquad
\Gamma_M(k)\ge c_{D_0}\delta\quad(1\le k\le D_0/\delta).
\tag{65.12}
$$

固定滞后时 $\Gamma_M(k)/\delta\to g_0$；若 $r\to0$，则对每个固定 $A$，
该收敛在 $k\le A\eta^2$ 上一致，因为此时 $k\delta\le Ar\to0$。
核心相对误差乘以有界的自相关质量，Gaussian 网格积分误差在有界平移上一致趋零。

记 $P_M(0)=\sum_{j\ne l}S_M(0,j-l)G_jG_l$。
两种滞后方向与 Gaussian 配对给出

$$
\operatorname{Var}_G P_M(0)
=\frac{16\eta^2}{\omega^2\delta}
\sum_{k\ge1}\Gamma_M(k)\frac{\sin^2(d_Mk)}{k^2}
\asymp\eta^2\min(D,D^2/\delta)\asymp\mathcal A_M^2.
\tag{65.13}
$$

常数对相位和 $\eta$ 一致。上界在 $D\le\delta$ 时用 Gaussian 滞后总质量，在 $D\ge\delta$ 时于 $1/D$ 分割。
下界在前一情形取 $1\le k\le\lfloor1/\delta\rfloor$；后一情形取
$1\le k\le\lfloor\pi/(2D)\rfloor$。
这些区间内 $\sin(Dk)\ge2Dk/\pi$，并分别至少含 $c/\delta$ 与 $c/D$ 个整数。
配合 (65.12) 即得下界。这样连 $D$ 离零有固定距离的情况也被覆盖，不用全域连续近似代替离散别名。
余弦项方差一致有界，Ci 余项方差为 $O(\eta^{-2})$。

还要控制任意小时间增量。令
$b_\theta(k)=\eta^2[e^{\theta/(2\eta^3)}\operatorname{Ci}(\omega\eta e^{\theta/\eta^3}k)-\operatorname{Ci}(\omega\eta k)]$。
第 64 章的精确 Ci 增量论证仅使用 $\eta\to\infty$，故此处仍给出，对 $h=|\theta-\psi|\le1$，

$$
|b_\theta(k)-b_\psi(k)|
\le C_I\left[\min(h/\eta,\eta/k)+h/(\eta^2k)\right],\quad
\sum_{k\ge1}|b_\theta(k)-b_\psi(k)|^2\le C_Ih.
\tag{65.14}
$$

(65.12) 与配对式使锚定 Gaussian 二次型的二阶增量至多 $C_Ih$。
中心 Gaussian 二次型满足 $EX^4\le15(EX^2)^2$，于是四阶增量至多 $C_Ih^2$。
Kolmogorov 判据给出锚定参考路径的一致紧性，前述统一比较给出实际 C-tightness。
若 $\mathcal A_M$ 有界，(65.13) 又使零点紧，得到充分性。

若 $\mathcal A_M\to\infty$，则 $P_M(0)/\mathcal A_M$ 的参考方差介于两个正常数之间。
对其平方应用 Paley–Zygmund 和四阶矩界得

$$
\Pr_G\{|P_M(0)|/\mathcal A_M>\sqrt{c/2}\}\ge1/60.
\tag{65.15}
$$

除以 $\mathcal A_M$ 后余弦和 Ci 余项均消失。先前证明的归一化比较和完整标签向量 TV 界，只对这个有界概率事件转移，即给出 (65.4)。
任意 $J_1$ 紧集的上确界范数有界，因为 $J_1$ 收敛的时间变换保持全区间上确界；
因此 (65.4) 足以排除紧性，不需要把内部零点的评价映射误当成处处连续。

最后，(65.3) 与先验平均紧性由 Markov 不等式及
$E\Pi_M(K^c)\le\varepsilon+\Pr\{\Pi_M(K^c)>\varepsilon\}$ 相互推出。
原支持置换等变性使先验平均联合律恰等于每个固定支持的无条件律。
实际 pair/path 环境估计一致，未知方向继续使用一个共同相等事件。
这些步骤不转移实际无界矩，也不声称逐个无限数据实现上的几乎处处后验紧性。

**定理 65.3（三种未锚定极限及同一端点平方）。** 令
$Z_0\sim N(0,128g_0/45)$，$N_2\sim N(0,2g_0)$。
在下列各子列上，过程与旧联合坐标在固定紧区间联合 C-tight 收敛。

当 $r_M\to0$ 且 $a_M=\eta_M^2d_M/\omega\to a\in\mathbb R$ 时，

$$
\mathcal V_M(\theta)\Rightarrow
Z_0+4\sqrt{g_0}B_{\rm odd}(a+\theta).
\tag{65.16}
$$

$B_{\rm odd}$ 是同一标准 Brownian motion 的奇延拓，且 $B,Z_0,N_2$ 与整个旧实场相互独立。此分支无需固定 $m_M$ 奇偶性。

当 $r_M\to\zeta\in(0,\infty)$、$d_M/\delta_M\to b$，且 $m_M$ 奇偶性固定时，

$$
\begin{aligned}
\mathcal V_M(\theta)&\Rightarrow Z_0+I_2(q_{\zeta,b,\theta};W_\sigma),\\
q_{\zeta,b,\theta}(x,y)&=
\frac{2\sqrt\zeta}{\omega}\frac{\sin[(b+\omega\theta/\zeta)(x-y)]}{x-y},\\
I_2(q_{\zeta,b,\theta};W_\sigma)&=
2\sqrt\zeta\int_0^{b/\omega+\theta/\zeta}
\left(|F_\sigma(v)|^2-\gamma\right)dv.
\end{aligned}
\tag{65.17}
$$

核在对角线上连续延拓。偶数 $m_M$ 时 $W_\sigma$ 为旧场，奇数时为其独立实副本。
$Z_0,N_2$ 相互独立，且与两份场联合独立；旧 $J_\infty$ 始终使用旧场。

当 $r_M\to\infty$、$b_M=\eta_Md_M/\sqrt\delta_M\to b$，并固定奇偶子列时，联合有

$$
\left(\mathcal V_M(\theta),\sqrt{r_M}\mathcal D_M(\theta)\right)
\Rightarrow
\left(Z_0+\frac{2b}{\omega}(Y_\sigma^2-\gamma),
2\theta(Y_\sigma^2-\gamma)\right).
\tag{65.18}
$$

$Y_\sigma=W_\sigma(1)$，两处平方是同一个随机量。第一坐标为常数路径，独立性和奇偶约定同 (65.17)。
全部结论保留先验条件 BL 数据概率收敛、一致固定支持无条件收敛及共同方向事件。

证明。三种参数条件都使 $\mathcal A_M$ 有界，因此前一定理提供未归一化共同 Gaussian 比较和路径紧性。又由
$\eta^2|d|^2\le C(\delta+|d|)$ 得 $d\to0$。
令 $\chi_j=(-1)^{m_Mj}$。余弦项的参考 $L^2$ 极限与

$$
O_M^\chi=-\frac2{\omega^2\sqrt\delta}
\sum_{j\ne l}\frac{\chi_j\chi_l}{(j-l)^2}G_jG_l
\tag{65.19}
$$

相同，因为逐个固定滞后的 $\cos(dk)\to1$，且 $k^{-4}$ 可求和。
标准正态矩阵的算子范数为 $O(\sqrt\delta)$，参考方差趋于 $128g_0/45$。
旧移动对角矩阵也有小算子范数，与此零对角矩阵的迹内积为零。
联合二次型—线性型特征函数或同一有限秩删除证明：这两个量先有联合 Gaussian 极限，再与所有旧及移动符号线性方向独立。
这给出所述 $Z_0,N_2$，不能由零协方差单独代替这一步。

对固定有限个时间，(65.7) 的正弦核同样逼近完整 Ci 核扣除静态余弦项。
具体地，Ci 三阶余项的二次均方为 $O(\eta^{-2})$；锚定余弦和正弦振幅的系数平方和为 $O(\eta^{-4})$；
相位线性化用 $\sum k^{-2}\min(k|u|,2)^2\le C|u|$，给出 $O_I(\eta^{-3})$。
这些有限维误差结合 (65.14) 的精确路径紧性即可使用连续极限；无需先将一个粗振幅误差乘以 $r^{-1}$。

亚临界时，正弦系数为
$2\eta\chi_j\chi_l\sin[\omega(a_M+\theta)k/\eta^2]/(\omega\sqrt\delta k)$。
同第 64 章的滞后分割与余弦尖点计算，其协方差趋于
$8g_0(|2a+\theta+\psi|-|\theta-\psi|)$。
标准正态矩阵的算子范数至多 $C_I\sqrt r(1+|\log r|)\to0$。
与 (65.19) 的协方差至多
$C_I\eta\sum k^{-3}\min(k/\eta^2,1)=O_I(\eta^{-1})$，与旧对角量的迹内积恰为零。
对所有这些矩阵的线性组合一起作特征函数展开，得到联合 Gaussian 极限和 (65.16) 的独立性；奇偶符号在新协方差中消失。

临界时，正弦核恰好是 $\chi_j\chi_l q_{M,\theta}(x_j-x_l)$，其中

$$
q_{M,\theta}(y)=\frac{2\sqrt r}{\omega}
\frac{\sin[(d/\delta+\omega\theta/r)y]}{y}.
\tag{65.20}
$$

核及时间导数在固定时间紧区间全空间有界，在固定空间紧集上一致趋于 (65.17)。
相邻单元的交替求和给出旧场与符号场的完整 Gram：偶数时两者相同，奇数时极限独立。
共同矩形逼近同时保留旧 $H$ 和新核，块内平方扣除给出 Wick 常数。
Gaussian 尾控制空间截断，时间紧性已由精确 Ci 获得。
该推导无需 $r-\zeta$ 或 $d/\delta-b$ 的额外速率；积分表达式由 Gaussian 乘积公式直接得到。

超临界时，$d/\delta=b_M/\sqrt r\to0$。在零点，由 $|\sin u-u|\le C|u|^3$，

$$
\left|q_{M,0}(y)-2b_M/\omega\right|\le C y^2/r.
\tag{65.21}
$$

(65.10) 使 $\sum_{j,l}|x_j-x_l|^4v_jv_l\le C$，所以正弦二次型在参考 $L^2$ 中逼近
$(2b_M/\omega)Q_M^\chi$，其中
$Q_M^\chi=(\sum_j\chi_jG_j)^2-\sum_jG_j^2$。
后者趋于同一个 $Y_\sigma^2-\gamma$。

对更细的增量重新使用 (65.9)，不放大前面的未量化误差。
置 $\tau_\eta(\theta)=\eta^3(e^{\theta/\eta^3}-1)$，则余弦中的新增空间频率为
$b_M/\sqrt r+\omega\tau_\eta(\theta)/r=O_I(r^{-1/2})$。
用 $|\cos u-1|\le Cu^2$、同一四阶空间界和 Ci 尾界，得到

$$
E_G\sup_{\theta\in I}
\left|\sqrt r\sum_{j\ne l}[K_M(\theta,j-l)-K_M(0,j-l)]G_jG_l
-2\theta Q_M^\chi\right|^2
\le C_I\left[r^{-2}+\eta^{-6}+\delta/\eta^2\right]\to0.
\tag{65.22}
$$

先对导数使用二次型等距，再从零积分即可取得上确界。
(65.6) 的第二个误差预算、缩放中心界和同一耦合使该比较适用于实际过程。
因此两坐标共享 $Q_M^\chi$，且未缩放增量消失，证明 (65.18)。

最后，旧非线性截距由共同矩形逼近加入；旧路径由质量尾和方差时钟保持。
一次完整后验向量 TV 比较只转移有界测试与误差事件，好环境子序列给出条件 BL 收敛。
这个论证不把新过程的边缘收敛误用为与旧场的联合收敛，也没有断言实际无界矩收敛。

**推论 65.4（完整子列分类与合法分离实例）。** 令 $\alpha_M=\eta_M^2d_M$。恒有

$$
\mathcal A_M^2=\frac{\alpha_M^2}{r_M+|\alpha_M|}.
\tag{65.23}
$$

在紧性条件下，先选 $r_M$ 在 $[0,\infty]$ 中的收敛子列。
若其极限为零，则 $\alpha_M$ 有界；若为正有限值，则 $d_M/\delta_M$ 有界；
若为无穷，则 $\alpha_M/\sqrt{r_M}$ 有界。再抽取相应失谐参数和所需奇偶子列，
定理 65.3 就覆盖全部所得联合极限。这里不假定原序列的参数、奇偶分布或极限律唯一。

这些分支均可在同一原合法算术中实现。取 $m_M\asymp Q^c$：
$0<c<1/4$ 时令 $\eta_M=2m_M+a/(4m_M^2)$；
临界时取指定奇偶的 $m_M$ 最接近 $(\sqrt\zeta/2)Q^{1/4}$，再令 $\eta_M=2m_M+b\delta_M/\omega$；
$c>1/4$ 时令 $\eta_M=2m_M+b\sqrt\delta_M/(2\omega m_M)$。
分别得到三种指定有限参数。另取任意固定 $d_0\in(0,\pi/2)$ 并令 $\eta_M=2m_M+d_0/\omega$，
则每种尺度中均有 $\mathcal A_M\to\infty$，从而实际未锚定谱不紧而锚定谱仍紧。

在超临界分支，$b=0$ 时未缩放极限是独立 Gaussian 常数，细增量仍含端点平方；
$b\ne0$ 时该常数含一个与细增量共享的非 Gaussian 分量。
不同奇偶分支可有相同新过程边缘律，却与旧场有不同联合律。
这些是已识别极限的性质，不能改写为有限后验独立性或实际矩收敛。

## 追加锚（本行以下为增补区）

## 66. 跨尺度共同噪声与只有两维的静态谱分量

**定义 66.1（有限载波族及相对尺度块）。** 保留原固定幅度与 beta、两种实际实验、完整固定总量后验、精确中心及定义 54.1 的截距。对固定有限个确定性载波，沿同一合法样本序列令

$$
\eta_a\to\infty,\quad r_a=\eta_a^2\delta,\quad
s_a=\log(\eta_a/\delta),\quad s_a\sqrt\delta\le U/2,
\quad\omega\eta_a=\pi m_a+d_a,\quad d_a\in(-\pi/2,\pi/2].
\tag{66.1}
$$

这里 $\omega=\pi/2$。先固定每个 $e_a=m_a\bmod2$，并使每个 $r_a$ 分别趋于零、某个 $\zeta_a\in(0,\infty)$ 或无穷。
对全部亚临界载波，另要求每个 $\eta_a/\eta_b$ 在 $[0,\infty]$ 中有极限。
有限正比值定义等价类；称其为尺度块 $\mathfrak b$。为每块选取 $L_{\mathfrak b}$，使

$$
\eta_a^2/L_{\mathfrak b}\to c_a\in(0,\infty),\qquad
L_{\mathfrak b}\to\infty,\qquad L_{\mathfrak b}\delta\to0.
\tag{66.2}
$$

不同块之间的尺度比趋于零或无穷。该条件是联合结论的假设，不能由每个 $r_a\to0$ 推出。
有限载波族总能抽取满足这些条件的子列，但不因此具有全序列极限。
各载波的 $\mathcal V_{a,M},\mathcal D_{a,M}$ 按 (65.2) 定义；超临界还保留 $\mathcal S_{a,M}=\sqrt{r_a}\mathcal D_{a,M}$。
所有坐标使用同一个实际后验标签向量。

定义两个与载波大小无关的实际统计量和两份符号场：

$$
\begin{aligned}
O_{e,M}&=-\frac2{\omega^2\sqrt\delta}
\sum_{j\ne l}\frac{(-1)^{e(j-l)}}{(j-l)^2}A_jA_l,
\qquad e\in\{0,1\},\\
F_{e,M}(v)&=\sum_j(-1)^{ej}A_je^{i\omega vx_j},
\qquad Y_{e,M}=F_{e,M}(0).
\end{aligned}
\tag{66.3}
$$

在共同计数线隔离事件外将它们置零；该修改只发生在概率趋零的事件上。
$F_{0,M}$ 是旧 Fourier 场，$Y_{0,M}$ 是旧端点。

**定理 66.2（实际多尺度共同实现）。** 设 (66.1)–(66.2) 成立，且各分支满足相应有界失谐极限：

$$
\begin{array}{ll}
r_a\to0:& a_a:=\lim\eta_a^2d_a/\omega\in\mathbb R,\\
r_a\to\zeta_a\in(0,\infty):& b_a:=\lim d_a/\delta\in\mathbb R,\\
r_a\to\infty:& u_a:=\lim\eta_ad_a/\sqrt\delta\in\mathbb R.
\end{array}
\tag{66.4}
$$

令 $W_0$ 为旧实 Gaussian 测度，控制测度为 $\rho(x)dx$；$W_1$ 为其一个独立实副本。
写 $F_e(v)=W_e(e^{i\omega vx})$、$Y_e=W_e(1)$。
存在共同中心 Gaussian 对 $(O_0,O_1)$，满足

$$
v_O=\operatorname{Var}O_0=\operatorname{Var}O_1=\frac{128g_0}{45},
\qquad\operatorname{Cov}(O_0,O_1)=-\frac78v_O.
\tag{66.5}
$$

对每个非空块—奇偶对 $(\mathfrak b,e)$，取一个标准 Brownian motion $B_{\mathfrak b,e}$，
并记其奇延拓为 $B_{\mathfrak b,e}^{\rm odd}$。
这些 Brownian motions、Gaussian 对 $(O_0,O_1)$、$N_2\sim N(0,2g_0)$ 和场对 $(W_0,W_1)$ 作为各块相互独立。
在这一共同实现上，全部实际载波联合收敛为

$$
\begin{array}{ll}
r_a\to0,\ a\in\mathfrak b:
&\displaystyle \mathcal V_a(\theta)=O_{e_a}
+4\sqrt{g_0c_a}\,B_{\mathfrak b,e_a}^{\rm odd}((a_a+\theta)/c_a),\\[2mm]
r_a\to\zeta_a:
&\displaystyle \mathcal V_a(\theta)=O_{e_a}
+2\sqrt{\zeta_a}\int_0^{b_a/\omega+\theta/\zeta_a}
(|F_{e_a}(v)|^2-\gamma)\,dv,\\[2mm]
r_a\to\infty:
&\displaystyle \left(\mathcal V_a(\theta),\mathcal S_a(\theta)\right)
=\left(O_{e_a}+\frac{2u_a}{\omega}(Y_{e_a}^2-\gamma),
2\theta(Y_{e_a}^2-\gamma)\right).
\end{array}
\tag{66.6}
$$

最后一行记号表示相应两个预极限坐标的联合极限。
负端点积分按有向积分理解；每份奇延拓的正负两半使用同一个 Brownian motion。
临界与超临界同奇偶载波始终使用同一个 $W_e$；不为每条载波另取独立场。

收敛同时包括 $(O_{0,M},O_{1,M})$、两份符号 Fourier 场、$T_M$ 以及旧端点、profile、bridge、dipole、截距、固定分辨率曲线和既定固定指数 Sobolev 坐标。
旧截距仍为 $b_\star\gamma+I_2(H;W_0)$。
路径结论在固定紧区间为联合 C-tight 的紧 $J_1$ 收敛，Fourier 场在固定频率紧区间取 $C^1$ 拓扑。
先验后验律在数据概率中按条件 BL 收敛；每个固定支持下为一致无条件收敛。
未知方向使用一个共同相等事件。不声称实际无界矩收敛或有限标签独立。

证明。单载波结论不能自行确定 (66.5) 或各场的共用关系；下面同时比较完整向量。
第 65 章的最终尺度 Fourier 恒等式对有限载波取最大误差后仍成立，因为
$\max_a\log\eta_a=O(Q^{1/4})$。有限权重和 floor 误差乘以
$Q^2\max_a(\eta_a^2/\sqrt\delta+\eta_a^3)$ 后仍趋零。
精确的 $\mathcal Q_M=V_M+\sqrt\delta T_M$ 和原 $J_M$ 在放大前取消大项。
这保留了超临界细增量的预算，没有再放大旧的未量化误差。

在共同截止域上，令 $K_{a,\theta}$ 为 (65.5) 的 Ci 核。
精确共振时有

$$
K_{a,0}(k)=-\frac{2(-1)^{e_ak}}{\omega^2\sqrt\delta k^2}
+O\!\left(\frac1{\eta_a^2\sqrt\delta k^4}\right).
\tag{66.7}
$$

静态主项原始矩阵范数为 $O(\delta^{-1/2})$。
亚临界锚定核由精确 Ci 积分给出
$|K_{a,\theta}(k)-K_{a,0}(k)|\le C_I\delta^{-1/2}\min(\eta_a^{-1},\eta_a/|k|)$，
故行和至多 $C_I\delta^{-1/2}\eta_a(1+\log Q)\le C_IQ^{1/2}(1+\log Q)$。
临界锚定核及超临界缩放锚定核的精确导数逐项有界，原始范数至多 $C_IQ^2$。

有界失谐时，零点正弦项为

$$
\frac{2\eta_a}{\omega\sqrt\delta}\,
\frac{(-1)^{e_ak}\sin(d_ak)}k.
\tag{66.8}
$$

亚临界由 $\eta_a^2|d_a|\le C$ 得到同一行和界；临界和超临界分别由
$d_a/\delta$ 与 $\eta_ad_a/\sqrt\delta$ 有界得到逐项有界。
余弦项与三阶 Ci 余项仍有多项式原始范数。因此第 56 章 Hilbert 中心位移
$O_P(Q^{-5/2}+q^{-1/2})$ 对全部坐标同时消失。
亚临界中心误差至多 $O_P(Q^{-2}(1+\log Q))+o_P(1)$；
临界与缩放超临界至多 $O_P(Q^{-1/2})+o_P(1)$。

选一个共同核心 $|x_j|\le R_c=\sqrt{D_*\log Q}$，一次逆分布耦合得到同一组标准正态。
未归一化 Bernoulli 方差下界 $d_j\ge q^{9/10}$ 提供 $q^{-1/8}$ 级核心向量误差；
核心外条件平方范数至多 $Q^{-60}$，可吸收上述多项式原始范数。
这些是同一数据好事件上的辅助比较，随后只转移有界测试和误差事件。

为联合分析不同尺度，现将所有核心方差一并换成
$m_j^\circ=\int_{(j-1/2)\delta}^{(j+1/2)\delta}\rho(x)dx$，继续使用同一组正态，记为 $G_j$。
原局部 Stirling 展开和占用集中给出相对误差 $O_P(Q^{-1}(1+\log Q))$。
它乘以亚临界核心范数、临界或缩放超临界核心范数、静态范数，分别给出

$$
O_P(Q^{-1/2}(1+\log Q)^2),\quad
O_P(Q^{-1/2}(1+\log Q)^{3/2}),\quad
O_P(Q^{-3/4}(1+\log Q)).
\tag{66.9}
$$

旧对数核的对应误差为 $O_P(Q^{-1/2}(1+\log Q)^{5/2})$。
对角量连同其方差中心一起替换。所有误差趋零，因而整个族已由一个确定质量 Gaussian 阵比较。
此处使用的是定量质量替换，不是把第 65 章未量化的环境收敛乘以新增放大因子。

置

$$
w_\delta(k)=\delta^{-1}\sum_{j,j+k\in\mathcal C_Q}m_j^\circ m_{j+k}^\circ,
\qquad g(t)=\int\rho(x)\rho(x-t)dx=g_0e^{-\kappa t^2/4}.
\tag{66.10}
$$

单元平均的 $L^2$ 逼近及 Gaussian 尾给出
$0\le w_\delta(k)\le C$ 与
$\sup_k|w_\delta(k)-g(k\delta)|\le C\delta+Ce^{-cR_c^2}$。
因此两个静态参考二次型的协方差满足

$$
\operatorname{Cov}_G(O_{e,M},O_{f,M})
=\frac{16}{\omega^4}\sum_{k\ge1}\frac{(-1)^{(e+f)k}w_\delta(k)}{k^4}
\longrightarrow\frac{16g_0}{\omega^4}
\sum_{k\ge1}\frac{(-1)^{(e+f)k}}{k^4}.
\tag{66.11}
$$

因子 16 包括两个滞后方向和 Gaussian 二次型配对。
普通四次 zeta 和交替和之比为 $-7/8$，得到 (66.5)。
其标准正态矩阵算子范数均为 $O(\sqrt\delta)$。
(66.7) 的余项参考方差为 $O(\eta_a^{-4})$；即使缓慢增大的 $\eta_a$ 使原始余项范数不趋零，这个方差仍趋零。
有界失谐时，余弦差的方差由
$C\sum_{k\ge1}(1-\cos(d_ak))^2/k^4\to0$ 控制，Ci 余项方差为 $O(\eta_a^{-2})$。
所以静态低余弦部分始终是同一对 $O_e$；初始正弦部分仍须保留。

亚临界正弦系数在 $2/\sqrt\delta$ 的单位下写为

$$
h_{a,\theta}(k)=\frac{\eta_a(-1)^{e_ak}}{\omega k}
\sin\!\left(\frac{\omega(a_{a,M}+\theta)k}{\eta_a^2}\right),
\qquad a_{a,M}=\eta_a^2d_a/\omega.
\tag{66.12}
$$

固定有限维的精确 Ci 比较沿用 (65.7)、(65.14) 的估计；包络为
$|h_{a,\theta}(k)|\le C_I\min(\eta_a^{-1},\eta_a/k)$。
它与任一静态 $k^{-2}$ 核的加权内积为 $O_I(\eta_a^{-1})$。
若 $q_{ab}=\eta_a/\eta_b\le1$，在 $\eta_a^2,\eta_b^2$ 两处分割可得

$$
\sum_{k\ge1}|h_{a,\theta}(k)h_{b,\psi}(k)|
\le C_Iq_{ab}(1+|\log q_{ab}|).
\tag{66.13}
$$

三个滞后区间的上界分别为 $Cq_{ab}$、$2Cq_{ab}\log(1/q_{ab})$ 和 $Cq_{ab}$。
它在任何趋零的尺度比下消失，不要求额外对数分离。
同块时先在 $k\le AL_{\mathfrak b}$ 用 $w_\delta(k)\to g_0$，其余乘积尾至多 $C/A$。
然后使用第 64 章的周期余弦尖点恒等式：同奇偶得到

$$
16g_0\sqrt{c_ac_b}\,
R_{\rm odd}\!\left((a_a+\theta)/c_a,(a_b+\psi)/c_b\right),
\quad R_{\rm odd}(u,v)=\frac{|u+v|-|u-v|}2;
\tag{66.14}
$$

异奇偶则在 $\pi$ 附近使用光滑二次段，协方差趋零。
这决定 Brownian 块的全部交叉协方差。

这些亚临界标准正态矩阵的算子范数至多
$C_I\sqrt{r_a}(1+|\log r_a|)\to0$，由加权 Schur 界在
$\eta_a^2$ 与 $\delta^{-1}$ 处分割得到；Gaussian 尾控制最后一段，界对行位置一致。
精确 Ci 的任意小增量仍满足 (65.14)，故参考四阶增量至多 $C_I|\theta-\psi|^2$。
这给出路径紧性，而不要求一个对所有滞后均成立的二次时间增量界。

把两个静态二次型、所有亚临界有限时间坐标及对角量一起组成向量。
对角算子范数为 $O(\sqrt\delta)$，与全部非对角矩阵的迹内积恰为零。
任意固定线性组合的算子范数趋零、Hilbert–Schmidt 范数有界且方差收敛，特征函数展开为

$$
\log E\exp\!\left(it\sum_\nu\lambda_\nu(\xi_\nu^2-1)\right)
=-t^2\sum_\nu\lambda_\nu^2
+O_t\!\left(\max_\nu|\lambda_\nu|\sum_\nu\lambda_\nu^2\right).
\tag{66.15}
$$

因此整个小算子向量先有联合 Gaussian 极限，再由已算出的零交叉协方差得到块间独立。

还需与保留的非 Gaussian 坐标联合。两份符号场在同一 Gaussian 阵上的 Hermitian 和 pseudo Gram 同时满足

$$
\begin{aligned}
E F_e(v)\overline{F_f(w)}&=1_{e=f}\Gamma(\omega(v-w)),\\
E F_e(v)F_f(w)&=1_{e=f}\Gamma(\omega(v+w)),\qquad
\Gamma(t)=\gamma e^{-t^2/(2\kappa)}.
\end{aligned}
\tag{66.16}
$$

异奇偶的交替单元和对固定光滑测试为 $O(\delta)$，单元投影和等距再扩展到固定 $L^2$ 测试。
四阶空间质量矩给出两场一致 $H^2$ 界及 $C^1$ 紧性。
因此所有临界积分端点可置于一个共同固定频率紧区间，超临界平方使用相应共同端点。

对每个固定有限个旧测试、两场 Fourier 测试和端点，将其共同实线性张成空间的投影记为 $P_M$。
投影随奇偶方向移动、Gram 也可以奇异，但秩一致有界。对上述任意小算子 $K_M$，

$$
\|K_M-(1-P_M)K_M(1-P_M)\|_{\rm HS}
\le2\sqrt{\operatorname{rank}P_M}\|K_M\|_{\rm op}\to0.
\tag{66.17}
$$

删去部分的中心二次型在参考 $L^2$ 中消失；保留部分与全部投影线性坐标严格独立。
先作这个有限维极限，再共同细分临界积分的矩形近似，证明小 Gaussian 块独立于整个临界和超临界非线性族。
旧对数核 $H$ 也先作同一场上的有限张量近似，其对角条带误差为
$O(\delta(1+|\log\delta|^2))$，空间尾由 Gaussian 质量控制。
这一步保留旧截距，且没有把各个边缘收敛拼成联合收敛。
仅用绝对交叉行和会产生未必消失的 $\sqrt r\log Q$；(66.17) 避免了这一额外条件。

临界项的精确余弦导数给出同一场的积分，并保留有限平方扣除 $\sum_jG_j^2\to\gamma$。
失谐初值由 (66.8) 给出积分的起始正弦部分，故完整上限为 (66.6) 所写。
超临界初始正弦核趋于 $2u_a/\omega$ 乘以同一符号秩一核。
细增量直接从最终缩放后的 Ci 导数估计，使用四阶空间矩得到 (65.22) 的误差
$C_I(r_a^{-2}+\eta_a^{-6}+\delta/\eta_a^2)$。
因此初值与细增量共享同一个 $Y_e^2-\gamma$，且整个有限载波族同时成立。

旧 profile、bridge、dipole、固定分辨率曲线与 Sobolev 坐标沿相同耦合保留；
Fourier 的 $C^1$ 紧性处理零频商的连续延拓，旧路径用方差时钟和质量尾。
有限个路径因子各自 C-tight 给出乘积紧性，前面的共同有限维极限确定联合律。
最后一次对完整选中标签向量使用后验 TV 界，只转移有界测试和事件。
数据好事件子列、支持置换等变性和一个共同方向事件分别给出所述三种原实验量词，证明完毕。

**推论 66.3（静态抵消、跨区间依赖与尺度条件的必要边界）。** 精确共振时，任意两条同奇偶载波无论属于哪种尺度，都有

$$
\mathcal V_{a,M}(0)-\mathcal V_{b,M}(0)\longrightarrow_P0.
\tag{66.18}
$$

这是同一实现的抵消，不仅是两个边缘极限相同。
设 $S=(O_0+O_1)/2$、$A=(O_0-O_1)/2$，则

$$
S\perp A,\qquad \operatorname{Var}S=\frac{8g_0}{45},
\qquad\operatorname{Var}A=\frac{8g_0}{3},\qquad O_e=S+(-1)^eA.
\tag{66.19}
$$

在有限核中，$S_M$ 只保留偶滞后，$A_M$ 只保留奇滞后；参考协方差恰为零，联合 Gaussian 极限使两部分独立。
方差的 $1:15$ 分配来自偶滞后四次和占全部的 $1/16$。
对任意固定实权重 $t_a$，载波组合的静态贡献为
$\sum_at_aO_{e_a}$，其方差为

$$
\frac{8g_0}{45}\left(\sum_at_a\right)^2
+\frac{8g_0}{3}\left(\sum_a(-1)^{e_a}t_a\right)^2.
\tag{66.20}
$$

它消失当且仅当两个奇偶类的权重和分别为零。
这个判据仅取消低余弦静态分量；有失谐时，(66.6) 的初始 Brownian、能量或端点平方项还在。

即使两条亚临界载波属于不同尺度块，其未锚定极限仍因共享 $O_e$ 而相关；
锚定后才只留下独立的块噪声。
相同奇偶的临界能量与超临界细增量还满足

$$
\operatorname{Cov}\!\left(
2\sqrt\zeta\int_0^{\theta/\zeta}(|F_e(v)|^2-\gamma)dv,
2\psi(Y_e^2-\gamma)\right)
=8\psi\sqrt\zeta\int_0^{\theta/\zeta}\Gamma(\omega v)^2dv.
\tag{66.21}
$$

当 $\theta,\psi>0$ 时严格为正；异奇偶则场导出的两项独立。
这是已识别极限的协方差，不主张实际矩收敛。

最后，取 $\eta_1=4n_M\asymp Q^{1/8}$，并交替令 $\eta_2=\eta_1$ 或 $2\eta_1$。
二者始终精确共振、同为偶奇偶类且亚临界，各自边缘律相同。
时间一处的动态交叉协方差在两子列分别为 $16g_0$ 与 $8g_0$，静态贡献均为 $v_O$。
定理 66.2 给出的两个联合 Gaussian 子列律不同，故没有全序列联合极限。
这说明相对尺度假设有实质作用；论证比较的是两个极限分布，而不是以实际方差振荡替代分布论证。

所需尺度与奇偶安排均可由 $4\operatorname{round}((t_M-2e)/4)+2e$ 实现，
分别取 $t_M=\sqrt{c_a}Q^{\xi_{\mathfrak b}}$、$\sqrt{\zeta_a}Q^{1/4}$ 或 $Q^\xi$，
其中 $0<\xi_{\mathfrak b}<1/4<\xi$；不同亚临界块还可任意缓慢分离。
三种失谐按第 65 章的小扰动加入，不改原样本算术。
结论限于固定有限载波族、固定紧区间和所列子列；不外推为增长载波族、任意振荡尺度的全序列极限或全球原创性声明。

## 追加锚（本行以下为增补区）

## 67. 任意相位超临界斜率的完整收敛分类

**定义 67.1（不限制相位的精细锚定）。** 保持定义 54.1 的实际模型、精确中心、完整选择窗口及有限截距，令

```math
\eta\to\infty,\qquad r_M=\eta^2\delta\to\infty,\qquad
s=\log(\eta/\delta),\qquad 0\le s\sqrt\delta\le U/2,
\qquad z_\theta=s+\theta/\eta^3,
```

```math
\mathcal V_M(\theta)=\eta^{3/2}e^{z_\theta/2}
 [\mathcal Z_M(z_\theta\sqrt\delta)-\mathcal J_M-2z_\theta\sqrt\delta T_M],
\qquad
\mathcal S_M(\theta)=\sqrt{r_M}[\mathcal V_M(\theta)-\mathcal V_M(0)].
```

式 (67.1)。

取唯一约定

```math
\varphi_M=\omega\eta=\pi m_M+d_M,\qquad
 d_M\in(-\pi/2,\pi/2],\qquad \ell_M=|d_M|/\delta,
\qquad \omega=\pi/2.
```

式 (67.2)。

在共同计数事件上令 $`Z_{\varphi,M}=\sum_j e^{i\varphi_Mj}A_j`$；在任意数据上，按实际分数组标记 $`x_g`$ 将系数定义为 $`e^{i(\varphi_M/\delta)x_g}`$。
两者在该事件上相同。仍记 $`\mathcal Q_M=\sum_gA_g^2`$。
令 $`W_0=W_\rho`$ 为旧实 Gaussian 测度，$`W_1`$ 为独立实副本，
$`F_e(v)=W_e(e^{i\omega vx})`$。
本章旧联合坐标取端点、空间累积场及桥、偶极、固定紧频段 Fourier 场、$`\mathcal J_\infty=b_*\gamma+I_2(H;W_0)`$ 和 $`N_2`$，均保留同一实现。

**定理 67.2（任意相位实际归约与收敛当且仅当）。** 对每个固定紧区间 $`I`$，

```math
\sup_{\theta\in I}
\left|\mathcal S_M(\theta)
 -2\theta\bigl(|Z_{\varphi,M}|^2-\mathcal Q_M\bigr)\right|
 \longrightarrow_P0.
```

式 (67.3)。

不加相位假设，$`\mathcal S_M`$ 已为 C-tight。
若 $`I`$ 含非零时刻，则其完整序列收敛，当且仅当 $`\ell_M`$ 在 $`[0,\infty]`$ 中收敛。
对有限极限 $`\ell`$，极限为 $`2\theta E_\ell`$，其中

```math
E_\ell\overset d=
 \lambda_+(\ell)G_+^2+\lambda_-(\ell)G_-^2-\gamma,
\qquad
\lambda_\pm(\ell)=\frac\gamma2(1\pm e^{-2\ell^2/\kappa}),
```

式 (67.4)。

$`G_+,G_-`$ 独立标准实 Gaussian；在 $`\ell=\infty`$ 时，$`E_\infty`$ 为均值 $`\gamma`$ 的指数变量减去 $`\gamma`$。
与全部旧坐标联合的完整序列收敛，当且仅当下列二者之一成立：

- $`\ell_M\to\infty`$，此时斜率独立于整个旧场和 $`N_2`$；
- $`\ell_M\to\ell<\infty`$ 且 $`m_M`$ 的奇偶性最终固定为 $`e`$，此时斜率为 $`2\theta\{|F_e(\ell/\omega)|^2-\gamma\}`$。

有限极限时，$`d_M`$ 的符号无需稳定。只把 $`T_M`$ 添入边缘过程不改变第一个判据。
若 $`I=\{0\}`$，过程恒零，不存在上述必要相位条件。
结论在均匀支持先验下为条件 BL 收敛、以数据概率成立；(67.3) 的条件超差概率也以数据概率趋零。
对每个固定支持，结论无条件且一致成立；两种平稳实验和共同方向一致事件均保留。

**证明。** 首先在实际有限统计上比较。
第 61、62 章的有限 Fourier、权重及取整余项记为 $`\varepsilon_M`$。
本章总放大因子为 $`\eta^3`$，而 $`\log\eta=O(Q^{1/4})`$、$`h=e^{-c_hQ^3+O(1)}`$，所以
$`Q^2\eta^3\varepsilon_M\to0`$。
$`\mathcal Q_M=O_P(1)`$ 由辅助总方差、精确中心和有界事件比较得到。
有限截距与平方和的抵消仍是精确恒等式；不能用一个未给速率的旧弱极限代替此比较。

对非零滞后 $`k`$，令

```math
K_M(\theta,k)=\frac{2\eta^2}{\sqrt\delta}e^{\theta/(2\eta^3)}
 \operatorname{Ci}(\omega\eta e^{\theta/\eta^3}|k|).
```

式 (67.5)。

实际锚定过程由 $`\sqrt{r_M}[K_M(\theta,k)-K_M(0,k)]`$ 的非对角二次型一致逼近。
只对这个光滑有限核求导，有

```math
\sqrt{r_M}\,\partial_\theta K_M(\theta,k)
 =2e^{\theta/(2\eta^3)}
 \left[\cos(\omega\eta e^{\theta/\eta^3}k)
 +\tfrac12\operatorname{Ci}(\omega\eta e^{\theta/\eta^3}|k|)\right].
```

式 (67.6)。

令 $`y=k\delta`$、$`\tau_\eta(t)=\eta^3(e^{t/\eta^3}-1)`$。
余弦相位相对 $`\varphi_Mk`$ 的变化恰为 $`\omega\tau_\eta(t)y/r_M`$。
由 $`|\cos(u+v)-\cos u|\le|v|`$ 和 $`|\operatorname{Ci}(v)|\le C/v`$，

```math
\sup_{t\in I}\left|
 \sqrt{r_M}\partial_tK_M(t,k)-2\cos(\varphi_Mk)\right|
 \le C_I\left(\eta^{-1}|k|^{-1}+\eta^{-3}+|y|/r_M\right).
```

式 (67.7)。

两边被比较的核还各自一致有界。
取同一辅助独立标签向量的组和 $`U_j`$，其方差为 $`v_j`$。
实际两行读数给出 $`\mathbb E_{\rm data}v_jv_l\le Ca_ja_l`$，$`j\ne l`$，并有
$`\sum a_j+\sum x_j^2a_j\le C`$，低计数区域只留 $`Q^Ce^{-c\lambda}`$。
对时间积分用 Cauchy–Schwarz，对非对角二次型用独立组等距式，遂得

```math
\mathbb E_{\rm data}\mathbb E_{\rm aux}
 \sup_{\theta\in I}\left|
 \int_0^\theta\sum_{j\ne l}
 [\sqrt{r_M}\partial_tK_M(t,j-l)-2\cos(\varphi_M(j-l))]U_jU_l\,dt
 \right|^2
 \le C_I(\eta^{-2}+r_M^{-2})+Q^Ce^{-c\lambda}.
```

式 (67.8)。

这里仅需二阶空间权重，因为
$`\sum_{j,l}(x_j-x_l)^2a_ja_l\le4(\sum a_j)(\sum x_j^2a_j)`$。
完整截断窗口至多 $`CQ^2`$ 组，核一致有界，所以原始矩阵范数至多 $`C_IQ^2`$。
第 56 章的 Hilbert 精确中心误差因此只贡献 $`O_P(Q^{-1/2})+o_P(1)`$，不含 $`\eta`$ 放大，也不含静态正弦核。
最后使用同一实向量的恒等式

```math
\sum_{j\ne l}\cos(\varphi(j-l))A_jA_l
 =\left|\sum_je^{i\varphi j}A_j\right|^2-\sum_jA_j^2.
```

式 (67.9)。

一次完整选择标签向量的 TV 比较只作用于有界事件，移除共同计数坏事件，便得 (67.3)。
上述均方读数属于数据环境和辅助标签，不宣称实际后验矩的收敛。

为识别联合律，在同一个 $`\sqrt{D\log Q}`$ 空间核心上采用第 62 章的单调分位耦合。
非标准化 Bernoulli 方差至少 $`e^{c\lambda}`$，标准化平方耦合误差至多 $`Cd_j^{-1/6}`$；完整组向量的平方误差指数小。
(67.6) 的原始范数 $`CQ^2`$、旧对数核的 $`CQ^2(1+\log Q)`$ 及对角核的 $`\delta^{-1/2}`$ 同时可承受该误差。
保留随机 $`v_j`$；总质量和二阶空间尾控制线性坐标，平方方差钟控制 $`T_M`$，旧对数核按共同矩形和 Wick 减项逼近。
这些比较全用一个向量。

固定空间截断和 BV 测试后，先把环境误差以绝对质量分出，再作 Abel 求和，得到

```math
C_{R,f,g}\left(\varepsilon_{{\rm env},M}(R)
       +\frac{\delta}{|1-e^{i\psi_M}|}\right).
```

式 (67.10)。

此处 $`\psi_M=\varphi_M`$ 管旧场交叉 Gram，$`\psi_M=2\varphi_M`$ 管伪 Gram。
固定测试和截断后先取数组极限，再移除尾部，故无额外对数余量。
若 $`\ell_M\to\infty`$，两项振荡 Gram 均消失，而 Hermitian Gram 保留 $`\rho`$，得到独立于旧场的 proper 复 Gaussian 测度。
若 $`d_M/\delta\to b`$ 且奇偶性为 $`e`$，
$`e^{i\varphi_Mj}=(-1)^{ej}e^{i(d_M/\delta)x_j}`$，极限为 $`f\mapsto W_e(e^{ibx}f)`$。
奇类交叉旧场的第一谐波消失，但自身第二谐波不消失。

同一 Gaussian 向量上，$`T_M`$ 的矩阵为 $`\operatorname{diag}(v_j/\sqrt\delta)`$，算子范数 $`O(\sqrt\delta)`$。
第 62 章的二次型加线性型联合行列式公式对任意有限个移动载波方向仍成立，余项由算子范数乘该方向范数平方控制。
这先证明联合 Gaussian 极限，再给出 $`N_2`$ 与整个场族的独立性。
共同旧矩形逼近保留 $`I_2(H;W_0)`$，不从分别的边缘律拼接。
每个固定频段上的 $`H^1`$ 二阶界由 $`\sum_j(1+x_j^2)v_j`$ 控制，给出紧性及共同 Fourier 路径。
$`\mathcal Q_M\to\gamma`$ 由辅助平方和方差 $`2\sum v_j^2+B^{-2}\sum v_j=o_P(1)`$，再转为概率事件得到。

Gaussian 控制密度的 Fourier 变换给出有限 $`b`$ 时
$`\mathbb E|Z|^2=\gamma`$、$`\mathbb EZ^2=\gamma e^{-2b^2/\kappa}`$。
实虚部独立且方差为 (67.4)，包括 $`b=0`$ 的退化情况。
这些谱公式是经典 Gaussian 二次型事实，出处与适用条件见 [相关文献条目](../../../Library/Dynamics/iyer2025empirical.md)。

载波系数绝对值为一，辅助二阶矩一致紧，故 (67.3) 将任意相位过程一致逼近为紧斜率的连续仿射路径，证明 C-tight。
极限能量的 Laplace 变换为

```math
\mathbb Ee^{-tE_\ell}
 =e^{\gamma t}\left[1+2\gamma t+
   \gamma^2(1-e^{-4\ell^2/\kappa})t^2\right]^{-1/2},\qquad t\ge0.
```

式 (67.11)。

对任何 $`t>0`$，此式区分所有 $`\ell\in[0,\infty]`$。
若 $`\ell_M`$ 收敛，每个子序列再取符号及奇偶性稳定的子序列，(67.4) 给出同一能量边缘律。
若不收敛，紧化区间上两个不同聚点给出不同的非零时刻极限律，完整过程不能收敛。
这是比较已识别的极限分布，不使用实际矩收敛。

对有限 $`\ell`$，实测度满足 $`|F_e(-v)|^2=|F_e(v)|^2`$，所以符号变化连旧联合律也不改变。
奇偶性却由旧端点 $`Y=W_0(1)`$ 区分：

```math
\operatorname{Cov}(|F_0(\ell/\omega)|^2-\gamma,Y^2-\gamma)
 =2\gamma^2e^{-\ell^2/\kappa}>0,
\qquad
\operatorname{Cov}(|F_1(\ell/\omega)|^2-\gamma,Y^2-\gamma)=0.
```

式 (67.12)。

两种奇偶性无限次出现即给出不同联合子序列律；最终固定则足够。
$`\ell=\infty`$ 时所有相位给出同一独立 proper 端点，不再需要奇偶性条件。
条件结论由好环境子序列、条件近似概率和一次向量比较得到；支持置换等变性给出固定支持的一致无条件结论。
共同方向事件同时作用于全部坐标。证毕。

**定理 67.3（跨临界尺度仍可共享一个能量场）。** 取有限个符合原外频范围的确定性载波，每个 $`r_{a,M}=\eta_a^2\delta`$ 或趋于 $`\zeta_a\in(0,\infty)`$，或趋于无穷。
添入 $`\varphi_{0,M}=0`$ 表示旧场。
假定每个实际相位差和相位和的 $`2\pi`$ 主值除以 $`\delta`$，分别收敛到有限 $`\Delta_{ab}`$、$`\Sigma_{ab}`$，或其绝对值趋于无穷；包括自身相位和。
令 $`C_0=W_0`$，场族 $`C_a`$ 由第 63 章相同的兼容 Hermitian 与伪 Gram 确定，$`F_a(v)=C_a(e^{i\omega vx})`$。
则共同旧坐标及 $`T_M`$ 与下列所有极限联合成立：

```math
\mathcal S_{a,M}(\theta)\Longrightarrow
 2\theta(|F_a(0)|^2-\gamma),\qquad r_{a,M}\to\infty,
```

```math
\mathcal V_{a,M}(\theta)-\mathcal V_{a,M}(0)\Longrightarrow
 \frac2{\sqrt{\zeta_a}}\int_0^\theta
 (|F_a(t/\zeta_a)|^2-\gamma)\,dt,
 \qquad r_{a,M}\to\zeta_a\in(0,\infty).
```

式 (67.13)。

$`N_2`$ 独立于整个场族；各载波之间是否独立，由两类 Gram 共同决定。
这些相位条件是本联合场结论的充分条件，不宣称是所有非线性能量元组收敛的必要条件。

**证明。** 固定有限个载波，前一证明的同一核心、精确中心、耦合和旧矩形逼近同时适用。
第 63 章的相位分类仅用实际相位和、差的关系以及 (67.10)，与 $`r_{a,M}`$ 的极限类别无关。
有限极限的 Gram 分别为 $`\int f\bar g e^{i\Delta_{ab}x}\rho dx`$ 和 $`\int fg e^{i\Sigma_{ab}x}\rho dx`$；逃逸者为零。
这些都是同一个实际 Gaussian 向量的实协方差矩阵极限，因此自动相容，不能任意拼一个两两数值表。
每个共轭类共用一个 proper 复测度或一个实测度，反向载波用同一场的共轭，而非另抽副本。

超临界坐标直接用 (67.3)。临界坐标将 (67.6) 除以 $`\sqrt{r_{a,M}}`$：Ci 项的积分均方误差为 $`O(\eta_a^{-2})`$，相位中的频率映射为
$`\eta_a(e^{t/\eta_a^3}-1)/\delta\to t/\zeta_a`$。
同一向量的 (67.9) 及共同 Fourier 紧性给出第二个积分极限。
紧的场上确界控制积分路径的 Lipschitz 常数，有限取整误差一致趋零，遂得 C-tight 紧区间 $`J_1`$ 联合收敛。
有限个原始矩阵范数都至多 $`CQ^2`$ 乘固定常数；一次完整向量比较和同一方向事件同时转移全部坐标。
概率量词与定理 67.2 相同。证毕。

**命题 67.4（频率大小分离不蕴含能量独立）。** 固定 $`\zeta>0`$、$`\psi\in(0,\pi)`$ 及 $`b\in\mathbb R`$。
可取合法临界载波 $`\eta_c\equiv\psi/\omega\pmod4`$，距 $`\sqrt{\zeta/\delta}`$ 至多二；并取合法超临界载波
$`\eta_s=4n_M+\psi/\omega+(b/\omega)\delta`$，其中 $`\log n_M=cQ^{1/4}+o(Q^{1/4})`$，$`0<c<U/2`$。
它们的强度比可指数增长，但极限仍共用一个独立于旧场的 proper 测度 $`C`$，且

```math
\operatorname{Cov}\left(
 2\theta(|C(e^{ibx})|^2-\gamma),
 \frac2{\sqrt\zeta}\int_0^t(|C(e^{i\omega ux/\zeta})|^2-\gamma)\,du
 \right)
 =\frac{4\theta\gamma^2}{\sqrt\zeta}
   \int_0^t e^{-(b-\omega u/\zeta)^2/\kappa}\,du.
```

式 (67.14)。

特别地，$`\theta,t>0`$ 时右侧严格为正。

**证明。** 两相位差除以 $`\delta`$ 等于 $`b`$，自身和交叉相位和都远离 $`2\pi\mathbb Z`$。
定理 67.3 因此给出同一场的两个调制，而非独立场。
外频限制由 $`c<U/2`$ 和 $`\log(1/\delta)\sqrt\delta\to0`$ 满足。
对共同 proper Gaussian 坐标用 Wick 公式
$`\operatorname{Cov}(|Z_1|^2,|Z_2|^2)=|\mathbb EZ_1\overline Z_2|^2`$，再用 Gaussian Fourier 变换及有向积分，即得 (67.14)。
这里只计算极限变量的协方差。证毕。

## 追加锚（67 章后）

## 68. 一个精确二次标量恢复全部后验组电荷

**定义 68.1（实际模型的精确能量增广）。** 保持定义 39.1 的固定振幅、固定 $\beta\in(1/2,1)$、
实际平稳独立对实验和连续路径实验，以及定义 54.1 的完整选择窗口与精确中心。
将十进制指数记为 $d_n$：

```math
d_1=1,\quad d_{n+1}=10^{5d_n},\quad Q_n=10^{d_n},\quad
P_n=\sum_{l\le n}10^{d_n-d_l},\quad
\alpha=\sum_{l\ge1}10^{-d_l}
       =\frac{\log(1+r)}{-\log(1-r)}.
```

式 (68.1)。

省略序列下标，记 $a=(1+r)/2$、$b=(1-r)/2$、
$\phi=a\log(1+r)+b\log(1-r)>0$，以及

```math
\lambda=Q^3,\quad M=2^{\lfloor\phi\lambda/(\beta\log2)\rfloor},
\quad T=2M\lambda,\quad k_0=\lfloor a\lambda\rfloor,
\quad l_0=\lambda-k_0,
```

```math
z_0=k_0\log(1+r)+l_0\log(1-r),\quad q=\lfloor Me^{-z_0}\rfloor,
\quad\tau=\log(M/q),\quad \epsilon=\frac{rq}{M-q},
\quad w=\sqrt{\lambda/q},\quad\delta=Q^{-1/2},\quad B^2=\frac q{Q\sqrt\lambda}.
```

式 (68.2)。

先正确对齐方向。对正类候选行，以原始计数 $k_i,l_i$ 定义

```math
W_i=k_i\log\frac{1+r}{1-\epsilon}
       +l_i\log\frac{1-r}{1+\epsilon},\qquad
J=\{i:\tau-w<W_i\le\tau+w\}.
```

式 (68.3)。

在全行计数截断与格线隔离事件上，$J$ 的完整等分数组对应
$(k_0+jQ,l_0+jP)$，$|j|\le K_M$，其中确定性 $K_M=O(Q^2)$ 覆盖整个截断窗口。
设 $\mathscr X_M$ 为全部原始数据，$\pi_i=\mathbb P(i\in S\mid\mathscr X_M)$ 为均匀大小 $q$ 支持先验的完整后验边缘，令

```math
C_j=|J_j|,\quad R_j=|S\cap J_j|,\quad
\mu_j=\sum_{i\in J_j}\pi_i,\quad A_j=(R_j-\mu_j)/B,
\quad\mathcal I_M=\{j:C_j>0\},\quad D_M=\sum_jj\delta A_j.
```

式 (68.4)。

空组补零至对称范围。取原数据可测方差 $V_M=B^{-2}\sum_{i\in J}p_i(1-p_i)$，
其中 $p_i$ 为原共同校准的辅助 Bernoulli 参数，完整后验中心仍是 $\pi_i$。
定义 54.1 的精确关系为

```math
\mathcal Q_M=\sum_jA_j^2=V_M+\sqrt\delta\,T_M.
```

式 (68.5)。

考察增广观测 $(\mathscr X_M,\mathcal Q_M)$ 或等价的 $(\mathscr X_M,T_M)$。
新增标量来自同一潜在标签实现；它不被声明为原始数据本身可计算的标签统计量。
参数与实数读数精确已知，允许可测的精确相等检验。
截断或隔离失败时附原始数据可见的失败旗并取默认输出。

**定理 68.2（实际后验中心的不同消失阶与单标量恢复）。** 对任意固定充分大的 $D_0>1$，
存在纯数据事件 $H_M$，使原两种实验均满足

```math
\sup_{S:|S|=q,\ \mathcal E\in\{\mathrm{pair},\mathrm{path}\}}
 \mathbb P_S^{\mathcal E}(H_M^c)
 \le CM^{1-D_0}+4e^{-c_*\lambda}=o(1),\qquad
 c_*=\frac9{16}\log(9/8)-\frac1{16}>0.
```

式 (68.6)。

每份 $H_M$ 内数据上，$1$ 与全部占据组的精确中心 $(\mu_j)_{j\in\mathcal I_M}$ 在 $\mathbb Q$ 上线性无关。
因此映射

```math
(R_j)_{j\in\mathcal I_M}\longmapsto
      \sum_{j\in\mathcal I_M}(R_j-\mu_j)^2
```

式 (68.7)。

在整个 $\mathbb Z^{\mathcal I_M}$ 上单射。
同一个可测解码器从 $(\mathscr X_M,T_M)$ 恢复全部所选组计数、组电荷与偶极，
对每个固定支持的无条件错误概率由 (68.6) 控制。
在均匀支持先验下，条件恢复概率于 $H_M$ 上精确为一。
该断言不要求偶部读数，不区分组内同分数站点的个别标签。
已知反向实验先作反向对齐；未知方向的共同判向版本，其无条件错误界只增加原来的 $O(q^{-1})$。

**证明。** 先核对实际固定振幅的算术性质。
十进制尾满足 $0<\eta_n:=\alpha-P_n/Q_n<2\,10^{-Q_n^5}$，且 $P_n<Q_n$、$P_n\equiv1\pmod {10}$。
若 $r$ 代数，则 $1+r$、$1-r$ 是固定的非零、非一正代数数。
Baker–Wüstholz 1993 原文第 20 页主定理，对固定代数数、固定对数支及非零整数线性形式给出
$\log|u\log(1+r)+v\log(1-r)|>-C\log\max(e,|u|,|v|)$。
取实自然对数、$u=Q_n$、$v=P_n$，得到

```math
0<\Lambda_n=Q_n\log(1+r)+P_n\log(1-r)
 =[-\log(1-r)]Q_n\eta_n
 <2[-\log(1-r)]Q_n e^{-(\log10)Q_n^5}.
```

式 (68.8)。

正尾保证形式非零；固定域次数与代数高度满足该定理条件，系数高度至多 $\log Q_n$。
其下界与 (68.8) 矛盾，故实际 $r$ 超越。这是成熟对数线性形式定理的直接应用。

下面给出保留完整后验归一化的有限代数论证。
固定数据、$M,q$ 及实际 $r$ 所选择的组集合，只在代数表达式内引入变量 $t$。
记 $c=q/(M-q)<1$，

```math
L_i(t)=\left(\frac{1+t}{1-ct}\right)^{k_i}
       \left(\frac{1-t}{1+ct}\right)^{l_i},\qquad
\pi_i(t)=\frac{L_i(t)e_{q-1}(L_l(t):l\ne i)}{e_q(L_l(t):l\in C_+)},
\quad \mu_j(t)=\sum_{i\in J_j}\pi_i(t).
```

式 (68.9)。

两种实验的支持似然都是 $\prod_{i\in S}L_i(r)$ 乘支持无关因子；
路径平稳初始分布均匀且支持无关，故没有遗漏依赖支持的路径次序因子。
固定大小的正权重乘积律及其初等对称归一化是经典 rejective law。
因此各 $\mu_j(t)\in\mathbb Q(t)$，在实际 $r$ 的分母严格为正。
这里不随 $t$ 重新取窗口、分组或参数；负 $t$ 仅用于同一有理函数的代数分析。

将所有 $M$ 行的 $k_i$ 按非降次序列成 $k_{(1)},\ldots,k_{(M)}$，
记 $s_h=\sum_{u=1}^h k_{(u)}$、$s_0=0$。
暂设每个所选组的共同计数 $k_j$ 严格大于 $k_{(q)}$，且不同组的 $k_j$ 不同。
令 $y=1+t\downarrow0$。逐行有

```math
L_i(-1+y)=\kappa_i y^{k_i}(1+O_i(y)),\qquad
\kappa_i=\frac{2^{l_i}}{(1+c)^{k_i}(1-c)^{l_i}}>0.
```

式 (68.10)。

有限和的最低次项系数均为正，所以 $e_q(L)$ 的阶精确为 $s_q$。
所选行 $i$ 满足 $k_i>k_{(q)}$，删除它不改变最小 $q-1$ 个计数之和；
于是 $e_{q-1}(L_l:l\ne i)$ 的阶精确为 $s_{q-1}$。
同组求和亦无抵消，得到

```math
\mu_j(-1+y)=a_j y^{k_j-k_{(q)}}(1+O_j(y)),\qquad a_j>0.
```

式 (68.11)。

最低计数可以并列，因其领先系数相加而不相消，论证不受影响；$q=1$ 时用 $e_0=1$。
所有占据组的指数是互异的正整数。
若 $a_0+\sum_j b_j\mu_j(t)=0$ 是实常系数关系，先令 $y\downarrow0$ 得 $a_0=0$；
再选 $b_j\ne0$ 中最小指数，除以对应 $y$ 次幂并取极限，得到 $b_ja_j=0$，矛盾。
故 $1,\mu_j(t)$ 在 $\mathbb R$ 上线性无关。
一个有理仿射关系若在超越数 $r$ 成立，清分母后即为恒零多项式，
与此函数独立性矛盾。于是 $1,\mu_j(r)$ 在 $\mathbb Q$ 上线性无关。
此步在每份有限数据上先完成，不交换增长维数极限与端点极限；不需要维数一致的领先系数下界。

现证明上述计数分离在实际数据中以 (68.6) 的概率成立。
原取整尺度给出
$\log M=\phi\lambda/\beta+O(1)$、
$\log q=\phi(1-\beta)\lambda/\beta+O(1)$、
$\log\epsilon=-\phi\lambda+O(1)$、$\tau-z_0=O(q^{-1})$。
因此最终 $q<M/4$、$c<1$。
原模型的一行生成函数可直接控制实际路径行。
对一个正类标记行，置
$u=(z_++z_-)/2-1$、$v=(z_+-z_-)/2$、
$A_z=(u+b_S(i)v)/(2M)$、$B_z=(v+b_S(i)u)/(2M)$，
其中支持上的 $b_S(i)=r$，正类补集上为 $-\epsilon$。
独立对生成函数为 $(1+A_z)^T$，平稳路径生成函数精确为

```math
e_1^{\mathsf T}
 \begin{pmatrix}1+A_z&B_z\\ A_z&B_z\end{pmatrix}^{T}e_1.
```

式 (68.12)。

这来自原转移核的秩二因式分解与 $\sum_i b_S(i)=0$。
固定复多圆盘上，主特征值是 $1+A_z+O(M^{-2})$，系数是 $1+O(M^{-1})$，
另一特征值贡献至多 $C2^{-T}$；展开主特征值的对数后，
实际生成函数与 Poisson 比较函数之差至多 $C\lambda/M$ 乘对应的实部指数包络。
信号比较均值为 $(a\lambda,b\lambda)$，背景为
$((1-\epsilon)\lambda/2,(1+\epsilon)\lambda/2)$。
特别地，任一固定正标记处实际生成函数最终至多比较函数的两倍，
一致于支持位置和两种实验。这里未假设独立观测行。

取 $z_+=z_-=2$ 得 $\mathbb E2^{k_i+l_i}\le2e^\lambda$。
由 Markov 及全行并集界，选择充分大的固定 $C_0$ 可使

```math
\mathcal C_M=\{\max_{i\in C_+}(k_i+l_i)\le C_0\lambda\},
\qquad \sup_{S,\mathcal E}\mathbb P_S^{\mathcal E}(\mathcal C_M^c)
       \le CM^{1-D_0}.
```

式 (68.13)。

在截断内，去补偿分数差是
$[-\log(1-r)]\{\eta(k-k_0)+[P(k-k_0)-Q(l-l_0)]/Q\}$。
有
$\lambda\eta+\epsilon\lambda+q^{-1}=o(w)$ 与 $w=o(Q^{-1})$；
第一式中的补偿项使用 $\epsilon\lambda/w=\epsilon\sqrt{\lambda q}\to0$，其余由原超小尾及 $q\to\infty$ 得到。
非零整数分子有至少固定常数乘 $Q^{-1}$ 的间隔，故窗口恰选截断内的格线点。
$P,Q$ 互素给出 $(k,l)=(k_0+jQ,l_0+jP)$，其分数严格位于窗口内部，
且精确步长
$[-\log(1-r)]Q\eta+\epsilon(Q-P)+O(\epsilon^2Q)>0$。
所以不同组有不同 $j$，进而有不同 $k_j$。

本振幅还提供一致的低计数储备。
函数 $r\mapsto\log(1+r)/[-\log(1-r)]$ 严格递减，
因为 $(1+r)\log(1+r)+(1-r)\log(1-r)$ 在零处为零、导数为 $\log((1+r)/(1-r))>0$。
十进制构造给 $1/10\le P/Q<\alpha<1/8$，而
$\log(31/16)/\log16>1/8$，于是 $r>15/16$、$a>31/32$、$b<1/32$。
以 $\xi=a\lambda-k_0\in[0,1)$ 记地板误差。
任一非负格线点满足

```math
k_j\ge k_0-\frac{l_0}{P/Q}
 =\lambda\left(a-\frac b{P/Q}\right)-\xi\left(1+\frac1{P/Q}\right)
 >\frac{21}{32}\lambda-11>\frac9{16}\lambda
```

式 (68.14)。

最后一个不等式最终成立，且覆盖整条可行计数线。
对每个背景行取 $z_+=9/8,z_-=1$，其正计数比较均值至多 $\lambda/2$，所以

```math
\mathbb E(9/8)^{k_i}\le2e^{\lambda/16},\qquad
\mathbb P(k_i>9\lambda/16)\le2e^{-c_*\lambda}.
```

式 (68.15)。

$c_*>0$ 由 $\log(9/8)>1/9$ 得出；严格尾保留非整数阈值。
定义纯数据事件
$\mathcal R_M=\{\#\{i\in C_+:k_i\le9\lambda/16\}\ge q\}$。
若该事件失败，至少 $M-2q+1\ge M/2$ 个背景行的计数超过阈值。
这些大计数背景行的期望总数至多 $2Me^{-c_*\lambda}$，再次用 Markov 得
$\sup_{S,\mathcal E}\mathbb P_S^{\mathcal E}(\mathcal R_M^c)\le4e^{-c_*\lambda}$。
概率证明中用背景身份作下界；事件和解码器不需要知道这些身份。
取 $H_M=\mathcal C_M\cap\mathcal R_M$，其上
$k_{(q)}\le9\lambda/16<\min_j k_j$，故 (68.11) 适用，且 (68.6) 成立。

最后，两个整数向量在 (68.7) 下相同会给出

```math
2\sum_j(R_j-R'_j)\mu_j
     =\sum_j(R_j^2-(R'_j)^2).
```

式 (68.16)。

有理独立性迫使每个 $R_j=R'_j$。
乘以已知 $B^2$ 即将相同能量转成该等式，不要求 $B$ 有理。
可测解码器可按固定顺序枚举所有大小 $q$ 支持，选择首个与测得能量匹配者。
每个有限规模的数据空间有限，候选有限，相等事件是 Borel 集，故该解码器可测。
真实支持保证存在匹配；所有匹配的组计数一致，空组自动为零。
(68.5) 用数据已知量把 $T_M$ 与能量相互转换。
空的占据组集合只有一个组向量，结论自动成立。
已知反向实验对齐后完全相同；未知方向在原共同判向成功事件上，分组、中心、标量与解码同时一致，
故无条件错误界只增加该事件的 $O(q^{-1})$ 失败概率。错误方向的工作中心不被称为方向混合后验。
此论证未使用后验乘积近似、Gaussian 替代或实际无界矩转移，
也不给精确能量之间规模一致的分离下界、有限位数或抗噪计算保证。证毕。

**推论 68.3（精确可恢复性与 Gaussian 独立极限并存）。** 原始数据与单标量 $T_M$ 在 $H_M$ 上
决定 $D_M$，但原联合弱极限仍有

```math
(T_M,D_M)\Longrightarrow (N_2,W_\rho(x)),\qquad
N_2\ \perp\ W_\rho,
```

式 (68.17)。

并保留第 51–54 章所列旧空间对象及其条件 BL、固定支持无条件一致范围。
若 $S_M=\operatorname{sgn}D_M$、$\operatorname{sgn}0=0$，TV 采用事件上确界约定，则先验数据概率意义下

```math
\left\|\mathcal L((T_M,S_M)\mid\mathscr X_M)
       -\mathcal L((T_M,-S_M)\mid\mathscr X_M)\right\|_{\rm TV}\longrightarrow1.
```

式 (68.18)。

**证明。** (68.17) 是原精确坐标的既有联合极限；本章只改变所讨论的信息问题，未改变这些随机变量。
$N_2$ 与整个旧实 Gaussian 场独立，由第 51 章的共同二次型逼近与有限秩删除证明。
在 $H_M$ 的每份数据上，成功图像与其非零符号反射图像不交，零符号子测度相同，
所以 (68.18) 左边精确等于 $1-\mathbb P(D_M=0\mid\mathscr X_M)$。
原偶极条件 CLT 的极限为非退化连续 Gaussian；先用固定 $[-u,u]$ 上界零原子，再令 $u\downarrow0$，
该原子以数据概率趋零。加上 $\mathbb P(H_M^c)\to0$ 即得结论。
与之对应，极限 $N_2$ 单独不能预测独立的 $\operatorname{sgn}W_\rho(x)$，其条件符号公平。
这里未把增长的整个原始数据宣称为某个固定弱极限对象，也未断言统计实验等价。
有限系统的平移整数格与精确后验中心承担可恢复性；连续 Gaussian 近似不保留该算术分离。
不存在与弱收敛的矛盾。证毕。

**推论 68.4（功率观测及其固定频率压缩）。** 固定任一非空实开区间 $I_0$，置
$F_M(v)=\sum_jA_j e^{i\omega vj\delta}$、$P_M(v)=|F_M(v)|^2$，$\omega=\pi/2$。
在 $H_M$ 上，$(\mathscr X_M,(P_M(v))_{v\in I_0})$ 决定所有所选组电荷。
更存在一个依赖固定模型参数的确定性可数集 $E\subset I_0$，
任一固定 $v_*\in I_0\setminus E$ 都使 $(\mathscr X_M,P_M(v_*))$ 对所有充分大合法规模、
两种实验及其全部 $H_M$ 内数据同时具有该可恢复性。

**证明。** 功率三角多项式的零滞后系数是 $\mathcal Q_M$。
其指标在 $[-2K_M,2K_M]$，故在 $I_0$ 的短子区间取 $4K_M+1$ 个相位互异样本，
乘 $z^{2K_M}$ 后用普通多项式插值就能确定全部系数，继而用定理 68.2。
这只是精确插值，不给条件数或稳定外推界。
对同一好数据下任意两个不同可行计数向量，能量不同使功率差成为非零实解析函数；
其区间零集离散。每个有限规模的数据和候选集合有限，合法规模可数，
对所有碰撞零集取并便得到确定性可数集 $E$。
一次独立的绝对连续频率抽样几乎必然避开 $E$，同时适用于所有这些规模和数据。
这是经典有限候选解析分离的应用，不提供某个具名频率必好的结论。
例如若有两个占据组，固定 $q-1$ 个储备行并分别在两组各添一个标签，
便得到同总组计数的两个可行支持；它们的 $F_M(0)$ 和 $P_M(0)$ 相同，故零频率一般不能使用。
“一个标量”指一个精确实数，不指一个有界位数的信息通道。证毕。

**定理 68.5（完整组计数与精确标量的条件离散熵率）。** 对每份原始数据 $x$，
以完整所选组计数向量 $R$ 在均匀大小 $q$ 支持先验下的有限后验分布定义

```math
h_M(x)=-\sum_r\mathbb P(R=r\mid\mathscr X_M=x)
                    \log_2\mathbb P(R=r\mid\mathscr X_M=x),
\qquad 0\log_20=0.
```

式 (68.19)。

$h_M^T(x)$ 则是精确实值 $T_M$ 在同一数据纤维上的有限原子分布的离散熵。置

```math
c_q=\phi(1-\beta)/\beta,\quad
\mathcal I=\{u:a+u\ge0,\ b+\alpha u\ge0\},\quad
J_c(v)=v\log(v/c)-v+c\quad(v\ge0),
```

```math
I(u)=J_a(a+u)+J_b(b+\alpha u),\qquad
\mathscr H(r,\beta)=\frac1{2\log2}\int_{\mathcal I}(c_q-I(u))_+\,du.
```

式 (68.20)。

这里 $0\log0=0$，率函数使用自然对数，$\mathscr H(r,\beta)$ 有限且严格为正。
原平稳独立对与连续路径实验分别满足

```math
\frac{h_M(\mathscr X_M)}{Q^5}\longrightarrow\mathscr H(r,\beta),
\qquad
\frac{h_M^T(\mathscr X_M)}{Q^5}\longrightarrow\mathscr H(r,\beta)
```

式 (68.21)。

收敛在先验数据概率意义下成立，亦即对每个固定 $e>0$，上述任一偏差超过 $e$ 的概率
在所有大小 $q$ 的确定支持抽样律下之上确界趋零。这里仍评价由均匀先验定义的熵函数，
不改用确定支持的点质量先验。在 $x\in H_M$ 上，$h_M^T(x)=h_M(x)$，
给定 $x,T_M$ 后组计数的离散熵精确为零。结论不涉及 Gaussian 微分熵或期望熵的收敛。

**证明。** 全部占据数先在原实际数据律下定义，不条件于截断成功。
取固定充分大的 $C_0$，使全行计数截断事件 $\mathcal C_M$ 的失败概率至多 $CM^{1-D_0}$。
第 68.2 条的一、二行生成函数比较可在任意固定倍数的 $\lambda$ 计数范围内使用。
具体地，对于 $k=1,2$ 个指定行，在 Cauchy 系数圆上取各半径
$\max(n_\nu,1)/m_\nu$，其中 $m_\nu$ 是该信号或背景 Poisson 坐标的均值。
这些半径有共同常数上界；相对 Poisson 点质量的误差最多引入
$C\prod_\nu\sqrt{n_\nu+1}$。因此对包括零计数在内的指定元组，

```math
\mathbb P_S^{\mathcal E}\{N=\mathbf n\}
 =\mathbb P_{\rm Pois}\{N=\mathbf n\}
       (1+O(\lambda^{k+1}/M)),\qquad k=1,2.
```

式 (68.22)。

路径行仍可相依；此处使用秩二生成函数的系数界。指定点质量的误差是相对误差，
不能换成会淹没稀有组均值的固定加性误差。
设 $\alpha_Q=P/Q$、$\xi=a\lambda-k_0\in[0,1)$。在全行截断内，
整数间隙与 $\lambda(\alpha-\alpha_Q)+\epsilon\lambda+q^{-1}=o(w)$、$w=o(Q^{-1})$
使原窗口恰由下列可行计数线元组组成，且不同元组的精确分数不同：

```math
K_M=\{j:k_j=k_0+jQ\ge0,\ l_j=l_0+jP\ge0,\ k_j+l_j\le C_0\lambda\},
\qquad u_j=j/Q^2,\qquad |K_M|\le CQ^2.
```

式 (68.23)。

令 $C_j$ 是实际全部候选行中具有该计数元组的行数；它在任意原数据上定义。
在 $\mathcal C_M$ 上，这些正占据数给出完整窗口各组，零占据数组可补入计数向量。

先核对端点。固定振幅满足 $r>15/16$，故 $a>31/32$、$b<1/32$、
$b/\alpha\le10b<a$，于是 $\mathcal I=[u_-,\infty)$，其中 $u_-=-b/\alpha$。
在内部

```math
I'(u)=\log((a+u)/a)+\alpha\log((b+\alpha u)/b),\qquad
I''(u)=\frac1{a+u}+\frac{\alpha^2}{b+\alpha u}>0.
```

式 (68.24)。

$I$ 在闭域连续，唯一极小值 $I(0)=0$，且 $I(u)\sim(1+\alpha)u\log u$。
因此 $(c_q-I)_+$ 的支撑紧，且在零附近严格为正。
左端点不能预先删除：令 $d_0=b/\alpha$、
$I_-=(a-d_0)\log(1-d_0/a)+d_0+b$，则

```math
0<I_-<d_0+b\le11b<11/32<225/512<\phi,\qquad
\beta_*=\frac{\phi}{\phi+I_-}\in(1/2,1).
```

式 (68.25)。

最后一个下界来自 $\phi'(r)=\operatorname{atanh}r\ge r$，故 $\phi(r)\ge r^2/2$。
当 $\beta<\beta_*$ 时积分的正区域接触左端点；等号时端点积分值为零，右邻域为正；
当 $\beta>\beta_*$ 时左根位于内部。右根 $u_+>0$ 总是唯一。
增大同一个固定 $C_0$，使 $U_0=(C_0-1)/(1+\alpha)>u_++1$。
这只扩大用于估计的截断，不改变原后验或窗口。

令 $\bar u_j=\max(u_j,u_-)$。网格 $K_M/Q^2$ 的两端距 $u_-,U_0$ 为 $O(Q^{-2})$；
若合法 $u_j<u_-$，其距离实际为 $O(\lambda^{-1}+\alpha-\alpha_Q)$，只影响有界数量的格点。
又有 $k_j/\lambda=a+u_j-\xi/\lambda$、$l_j/\lambda=b+\alpha_Q u_j+\xi/\lambda$。
对 $0\le n\le C_0\lambda$，统一使用
$\log(n!)=n\log n-n+O(\log\lambda)$，包括 $n=0$。
函数 $x\log x$ 在固定非负紧区间上的模连续性为
$C|x-y|(1+|\log|x-y||)$，故信号 Poisson 点质量 $f_j$ 满足

```math
\log f_j=-\lambda I(\bar u_j)+O(\log\lambda)
```

式 (68.26)。

这一步保留零负计数端点，没有把内部 Stirling 前因子延伸到零。
背景点质量与 $f_j$ 的精确似然比为 $e^{W_j}$，两类总行均值同为 $\lambda$。
因此占据数的比较均值

```math
m_j=qf_j\{1+(1-q/M)e^{\tau-W_j}\}=(2+o(1))qf_j,
\quad
\sup_{j\in K_M}|\log m_j-\lambda(c_q-I(\bar u_j))|\le C\log Q.
```

式 (68.27)。

$W_j=\tau+o(w)$ 在整个截断线一致成立，$m_j>0$，但不要求其趋无穷。
由 (68.22) 对同组的一个或两个行指标求和，记 $\varepsilon_M=C\lambda^3/M$，得到

```math
|\mathbb E C_j-m_j|\le\varepsilon_Mm_j,
\qquad \operatorname{Var}C_j\le C(m_j+\varepsilon_Mm_j^2).
```

式 (68.28)。

对任意固定 $A>2$，Markov 给 $1+C_j\le Q^A(1+m_j)$，
对 $m_j\ge Q^A$ 再用 Chebyshev 给 $C_j/m_j\in[1/2,3/2]$，
这些断言同时失败的概率至多 $CQ^{2-A}+CQ^2\varepsilon_M$。
当 $m_j<Q^A$ 时只用 $\log(1+m_j)\le A\log Q+\log2$，不要求相对集中。
由 $|\log(1+m)-(\log m)_+|\le\log2$，同一好事件上

```math
\sup_{j\in K_M}
 \left|\log(1+C_j)-\lambda(c_q-I(\bar u_j))_+\right|\le C_A\log Q.
```

式 (68.29)。

这是全窗口对数占据数估计；空组和过渡区域 $I\approx c_q$ 都在其中。

下一步仅对给定原始数据的校准辅助标签取独立乘积律 $\mathsf Q_x$。
第 35 章的校准根满足
$p_i=\operatorname{logistic}(W_i-\log((M-q)/q)+\theta_M)$，
$\theta_M=O_{\mathbb P}(q^{-1/2})$，总方差 $d_{\rm all}\asymp q$。
这些全窗口估计也可从 (68.22) 核对：在倾斜前，精确改变测度给
混合总成功均值为 $q$，混合总 Bernoulli 方差为 $q\mathbb E_s(1-p^0)$。
信号 Poisson 分数的均值距阈值 $O(1)$、标准差为固定正倍数的 $\sqrt\lambda$，
其普通特征函数 CLT 使 $\mathbb E_s(1-p^0)\to1/2$。
一、二行比较对这些有界非负函数给方差
$C(\mu+\varepsilon_M\mu^2+M^{2-D_0})$，其中 $\mu\asymp q$。
由于 $\varepsilon_Mq\to0$，校准总和误差为 $O_{\mathbb P}(\sqrt q)$；
logistic 方差在位移 $\theta$ 下至少为原值的 $e^{-|\theta|}$ 倍，给出上述根估计。
原窗口内因而有 $p_j\in[1/4,3/4]$，概率趋一。

对任意固定 $p_0>0$，经典二项分布离散熵界在全部 $n\ge0$、
$p\in[p_0,1-p_0]$ 上统一给

```math
\left|H_{\rm disc}(\operatorname{Bin}(n,p))
       -\frac{\log(1+n)}{2\log2}\right|\le C_{p_0}.
```

式 (68.30)。

下界可由 Fourier 反演的最大原子界 $C/\sqrt{n+1}$ 取得；
上界取离散比较律 $r_k=Z^{-1}\exp(-(k-np)^2/(n+1))$，
$Z\le C\sqrt{n+1}$，用相对熵非负性和二项方差至多 $n/4$ 即得。
$n=0$ 单独为零。各完整组在 $\mathsf Q_x$ 下是独立的
$\operatorname{Bin}(C_j,p_j)$；设其联合离散熵为 $\widetilde h_M(x)$，则

```math
\left|\widetilde h_M(x)-\frac1{2\log2}\sum_{j\in K_M}\log(1+C_j)\right|
 \le CQ^2.
```

式 (68.31)。

(68.29) 与网格间距 $Q^{-2}$ 给

```math
\frac{\widetilde h_M(\mathscr X_M)}{Q^5}
 =\frac1{2\log2\,Q^2}\sum_{j\in K_M}(c_q-I(\bar u_j))_++o_{\mathbb P}(1)
 \longrightarrow\mathscr H(r,\beta).
```

式 (68.32)。

率函数正部先增后减、总变差有限，Riemann 和误差为 $O(Q^{-2})$，
即使左端点导数无界也成立。这里 $Q^5=\lambda Q^2$：
每组对数占据数的尺度是 $\lambda$，计数线的宏观网格数是 $Q^2$。

最后在同一有限字母表上传递实际后验熵。
信号线概率满足 $\sum_{j\in K_M}f_j\le C/(Q\sqrt\lambda)$：
两个 Poisson 最大点质量各为 $O(\lambda^{-1/2})$，在中心区域沿正计数间距 $Q$
求 Gaussian 上界和，余下固定比例偏移为指数尾。故实际 $|J|=O_{\mathbb P}(B^2)$，
$d_J=O_{\mathbb P}(B^2)=o_{\mathbb P}(q)$，补集方差 $d_{J^c}\asymp q$。
给定数据后，完整校准乘积律条件于总数 $q$ 就是精确后验，所选向量的密度比为

```math
L(S_J)=\frac{\mathsf Q_x(S_{J^c}=q-S_J)}{\mathsf Q_x(S_{\rm all}=q)}.
```

式 (68.33)。

独立 Bernoulli 和的局部界
$\sup_k|\mathbb P(S=k)-(2\pi d)^{-1/2}e^{-(k-m)^2/(2d)}|\le C/d$
对异质参数统一成立：中心特征函数满足
$|\psi(t)|\le e^{-2d\sin^2(t/2)}$、
$\log\psi(t)=-dt^2/2+O(d|t|^3)$，小区间积分误差为 $O(d^{-1})$，其余为指数尾。
总均值恰为整数 $q$；因此令 $V=S_J-\mathbb E_{\mathsf Q_x}S_J$，有
$L(S_J)=\sqrt{d_{\rm all}/d_{J^c}}e^{-V^2/(2d_{J^c})}+O(q^{-1/2})$。
对 $|L-1|$ 积分并用 $\mathbb E_{\mathsf Q_x}V^2=d_J$，得到一次完整所选向量比较

```math
\Delta_M=d_{\rm TV}(\mathsf P_{x,J},\mathsf Q_{x,J})
 \le C(d_J/q+q^{-1/2})=O_{\mathbb P}(Q^{-5/2}+q^{-1/2}).
```

式 (68.34)。

这里 TV 是半 $\ell^1$ 距离。计数映射收缩 TV；两种计数律都在同一个盒字母表
$\mathcal A_x=\prod_{j\in K_M}\{0,\ldots,C_j\}$ 上，允许其中一些点在实际后验中概率为零。
在全行截断上，$\log_2|\mathcal A_x|\le CQ^2\log_2(M+1)\le CQ^5$。
对于同一 $D$ 点字母表、TV 为 $t$ 的两律，最大耦合及误差指示位的链式法则给
$|H(P)-H(Q)|\le h_2(t)+t\log_2(D-1)$；$D=1$ 时两熵都为零。
因此

```math
\frac{|h_M(x)-\widetilde h_M(x)|}{Q^5}
 \le Q^{-5}+C\Delta_M=o_{\mathbb P}(1).
```

式 (68.35)。

这不是无界熵的一般 TV 连续性断言；完整组计数字母表的对数大小界是必要的一步。
坏数据只付其概率，以证明数据概率收敛，没有用坏事件概率乘未受控的熵。
由 (68.32)、(68.35) 得第一条 (68.21)。定理 68.2 在 $H_M$ 上使组计数与 $T_M$
仅为同一有限原子概率表的重标记，故熵精确相等；$\mathbb P(H_M^c)\to0$ 给第二条。
支持置换保持这些数据可测熵函数，且在所有大小 $q$ 支持上传递，得到所述一致确定支持含义。
共同判向成功事件上所有数据、中心、组及熵函数同时一致，原未知方向结论同样按事件概率转移。
这不提供期望熵极限、二阶熵展开、增长维数 CLT、组内站点恢复、稳定逆或计算效率。证毕。

**定理 68.6（完整组计数的最大后验原子）。** 在定理 68.5 的同一均匀支持先验下，令

```math
p_{\max,M}(x)=\max_n\mathbb P(R=n\mid\mathscr X_M=x),\qquad
h_{\infty,M}(x)=-\log_2p_{\max,M}(x).
```

式 (68.36)。

$h_{\infty,M}$ 是每份原始数据上有限计数律的最小熵。
两种实际实验分别满足

```math
\frac{h_{\infty,M}(\mathscr X_M)}{Q^5}\longrightarrow\mathscr H(r,\beta)
```

式 (68.37)。

收敛在先验数据概率下成立，并一致于确定支持的抽样律；后者仍使用均匀先验定义的函数。
在定理 68.2 的单射事件 $H_M$ 上，精确标量 $T_M$ 的最大原子与 $p_{\max,M}$ 相等。

**证明。** 继续使用 (68.23) 的完整计数线、校准乘积律 $\mathsf Q_x$ 与精确后验
$\mathsf P_x$。在概率趋一的实际数据集上，
$p_j\in[1/4,3/4]$、$d_{\rm all},d_{J^c}\asymp q$、
$d_J=O_{\mathbb P}(B^2)$、$|J|=O_{\mathbb P}(B^2)=o_{\mathbb P}(q)$。
这些估计来自定理 68.5 的实际一、二行比较与校准。
由 (68.33) 的同一条件化，组计数的概率精确满足

```math
\mathsf P_x(R=n)=L\left(\sum_jn_j\right)
                     \prod_j\mathbb P\{\operatorname{Bin}(C_j,p_j)=n_j\}.
```

式 (68.38)。

设 $m_J=\mathbb E_{\mathsf Q_x}S_J$。
同一个 Bernoulli 局部估计在中心分母与任意分子上给

```math
L(k)=\sqrt{d_{\rm all}/d_{J^c}}
         e^{-(k-m_J)^2/(2d_{J^c})}+O(q^{-1/2}),\qquad
\sup_kL(k)\le1+C(d_J/q+q^{-1/2}).
```

式 (68.39)。

误差对全部整数 $k$ 统一；总均值恰为 $q$，所以分母至少为 $c/\sqrt q$。
这是相对最大原子比较所需的密度信息，不能用 (68.34) 的加性 TV 误差替代。

对于 $N\ge0$、$p\in[1/4,3/4]$，记二项最大原子为 $b_{N,p}$。
经典 Fourier 模界给 $b_{N,p}\le C/\sqrt{1+N}$。
另一方面，方差至多 $N/4$，半径 $\sqrt{N+1}$ 内由 Chebyshev 至少容纳 $3/4$ 的质量；
该区间最多有 $3\sqrt{N+1}$ 个整数，故有统一下界。
相邻概率之比为 $(N-k)p/((k+1)(1-p))$，因此可取模态
$n^*=\lfloor(N+1)p\rfloor$，并有 $|n^*-Np|\le1$。
$N=0$ 时单独取 $n^*=0$、$b_{0,p}=1$。于是

```math
\frac c{\sqrt{1+N}}\le b_{N,p}\le\frac C{\sqrt{1+N}},\qquad
\left|\sum_j n_j^*-m_J\right|\le |K_M|\le CQ^2=o(\sqrt q).
```

式 (68.40)。

乘积模态向量在实际后验中可行：好事件上 $|J|<q<M-|J|$，
所以任何所选总数 $0\le k\le|J|$ 都可由补集凑成总数 $q$；所有辅助 Bernoulli 参数严格在零一之间。
将 $k^*=\sum_jn_j^*$ 代入 (68.39)，得到
$L(k^*)=1+O(d_J/q+Q^4/q+q^{-1/2})$。
令 $\widetilde p_{\max,M}=\prod_jb_{C_j,p_j}$，则 (68.38) 直接给

```math
L(k^*)\widetilde p_{\max,M}\le p_{\max,M}
       \le (\sup_kL(k))\widetilde p_{\max,M},\qquad
\left|\log\frac{p_{\max,M}}{\widetilde p_{\max,M}}\right|
 =O_{\mathbb P}(Q^{-5/2}+Q^4/q+q^{-1/2}).
```

式 (68.41)。

所以实际与乘积最大原子的比趋一，即使二者本身都以 $Q^5$ 指数尺度趋零。
(68.40) 又给

```math
-\log_2\widetilde p_{\max,M}
 =\frac1{2\log2}\sum_{j\in K_M}\log(1+C_j)+O(Q^2).
```

式 (68.42)。

由 (68.29) 与同一全域 Riemann 和，右边除以 $Q^5$ 趋于 $\mathscr H(r,\beta)$，
证明 (68.37)。空组、稀有组、率函数过渡区域及零计数左端点均未删去。
坏数据只付其概率；没有平均最小熵或平均最大原子的指数断言。
单射事件上，$T_M$ 与 $R$ 只是同一有限概率表的重标记。
支持置换与共同判向事件按定理 68.5 处理，得到所述一致性。证毕。

**定理 68.7（Shannon 熵与最小熵的次阶差）。** 沿用定理 68.5、68.6 的全部参数、
完整计数向量及概率含义，令

```math
\ell(r,\beta)=\operatorname{Leb}\{u\in\mathcal I:I(u)<c_q\}.
```

式 (68.43)。

该长度有限且严格为正。两种实际实验分别满足

```math
\frac{h_M(\mathscr X_M)-h_{\infty,M}(\mathscr X_M)}{Q^2}
 \longrightarrow\frac{\ell(r,\beta)}{2\log2}.
```

式 (68.44)。

收敛在先验数据概率下成立，亦一致于确定支持的抽样律。
若 $\widetilde h_M,\widetilde h_{\infty,M}$ 是同一数据上校准乘积组计数律的两种熵，则还有绝对比较

```math
h_M-\widetilde h_M=O_{\mathbb P}(Q^{-3/2}),\qquad
h_{\infty,M}-\widetilde h_{\infty,M}=O_{\mathbb P}(Q^{-5/2}).
```

式 (68.45)。

在 $H_M$ 上，精确标量 $T_M$ 的离散 Shannon 熵与最小熵之差等于 (68.44) 的分子，
故它也满足同一极限。这里不分别给出两种熵在 $Q^2$ 阶的展开。

**证明。** 首先加强 (68.34) 的密度比较。下文在给定好数据 $x$ 上以
$\mathsf Q_x$ 表示乘积组计数律，$\mathsf P_x$ 表示精确后验计数律，
$V=S_J-\mathbb E_{\mathsf Q_x}S_J$。
由 (68.39)、$|\sqrt{d_{\rm all}/d_{J^c}}-1|\le Cd_J/q$、
$1-e^{-t}\le t$ 及独立 Bernoulli 和的四阶中心矩，

```math
\mathbb E_{\mathsf Q_x}V^4\le3d_J^2+d_J,\qquad
\chi_x^2:=\mathbb E_{\mathsf Q_x}(L(S_J)-1)^2
 \le C\{(d_J/q)^2+q^{-1}\}.
```

式 (68.46)。

这里 $d_J\le q$，$d_{J^c}\asymp q$。
因此 $\chi_x=O_{\mathbb P}(Q^{-5/2}+q^{-1/2})$。
密度比只依赖组计数之和，所以对计数律仍有
$\mathsf P_x(n)=L(\sum_j n_j)\mathsf Q_x(n)$、
$\mathbb E_{\mathsf Q_x}L=1$；没有另行近似实际各组独立。

所需二项信息量界可直接从全部原子取得。
固定 $p_0\in(0,1/2)$，记 $f_{n,p}$ 为二项概率质量，
$n\ge0$、$p\in[p_0,1-p_0]$。Fourier 模界及带端点的 Stirling 界给

```math
\max_k f_{n,p}(k)\le\frac C{\sqrt{n+1}},\qquad
f_{n,p}(k)\ge\frac c{\sqrt{n+1}}
       \exp\left(-C\frac{(k-np)^2}{n+1}\right),\quad0\le k\le n.
```

式 (68.47)。

具体地，对 $n\ge1$、$z=k/n$，阶乘界给
$\binom nk\ge c\sqrt{(n+1)/((k+1)(n-k+1))}\,e^{n[-z\log z-(1-z)\log(1-z)]}$。
前因子至少为 $c/\sqrt{n+1}$；乘 $p^k(1-p)^{n-k}$ 后的指数为
$-nD(z\Vert p)$。由 $\log t\le t-1$ 有
$D(z\Vert p)\le(z-p)^2/[p(1-p)]$，包括 $z=0,1$ 的连续延拓，得下界。
$n=0$ 的单位原子单独满足两界。

令 $K\sim\operatorname{Bin}(n,p)$、$Z=-\log f_{n,p}(K)$、$\Delta=K-np$。
于是 $-C\le Z-\tfrac12\log(n+1)\le C+C\Delta^2/(n+1)$；
而 $\mathbb E\Delta^4\le C(n+1)^2$，故

```math
\mathbb E\{Z-\tfrac12\log(n+1)\}^2\le C,\qquad
\operatorname{Var}(Z)\le C.
```

式 (68.48)。

这些常数不随占据数增长。完整乘积计数的信息量
$\mathcal S(n)=-\log\mathsf Q_x(n)$ 是这些独立坐标信息量之和，所以
$\operatorname{Var}_{\mathsf Q_x}(\mathcal S)\le C|K_M|\le CQ^2$。
以自然对数计算有限分布的熵 $h$，精确恒等式与相对熵界为

```math
\begin{aligned}
h(\mathsf P_x)-h(\mathsf Q_x)
 &=\mathbb E_{\mathsf Q_x}[(L-1)(\mathcal S-\mathbb E_{\mathsf Q_x}\mathcal S)]
       -D(\mathsf P_x\Vert\mathsf Q_x),\\
0\le D(\mathsf P_x\Vert\mathsf Q_x)
 &\le\mathbb E_{\mathsf Q_x}L(L-1)=\chi_x^2.
\end{aligned}
```

式 (68.49)。

零密度点按 $0\log0=0$ 处理。第二行仍只用 $\log t\le t-1$ 与归一化。
Cauchy–Schwarz 因而给

```math
|h(\mathsf P_x)-h(\mathsf Q_x)|
 \le\chi_x\sqrt{\operatorname{Var}_{\mathsf Q_x}(\mathcal S)}+\chi_x^2
 \le CQ(d_J/q+q^{-1/2})+C\{(d_J/q)^2+q^{-1}\}
 =O_{\mathbb P}(Q^{-3/2}).
```

式 (68.50)。

信息量的 $Q^5$ 阶均值在估计之前已精确消去。
这是由密度的 $L^2$ 范数及乘积信息量方差控制期望，不能仅由 TV 推出。
除以 $\log2$ 得 (68.45) 第一式；第二式由 (68.41) 直接得到。

最后比较同一个二项坐标的两种熵。记自然对数下的差为
$g(n,p)=h(\operatorname{Bin}(n,p))-h_\infty(\operatorname{Bin}(n,p))$。
经典二项熵渐近式与模态 Stirling 估计给

```math
0\le g(n,p)\le C,\qquad g(0,p)=0,\qquad
\sup_{p\in[p_0,1-p_0]}|g(n,p)-1/2|\longrightarrow0.
```

式 (68.51)。

半 nat 常数属于经典二项熵结论，可由 Adell–Lekuona–Yu 的统一熵界与模态估计直接取得。
此处给出适于全部占据数的验证：在模态 $k^*=np+O(1)$ 处，
$-\log f_{n,p}(k^*)=\tfrac12\log(2\pi np(1-p))+O(n^{-1})$。
在 $|\Delta|\le n^{5/8}$ 内，对二项相对熵作 Taylor 展开得到
$-\log f_{n,p}(K)+\log f_{n,p}(k^*)=\Delta^2/[2np(1-p)]+O(n^{-1/8})$，
误差对上述参数区间统一。
补集上，(68.47) 将非负差界为 $C+C\Delta^2/n$；四阶矩给
$\mathbb P(|\Delta|>n^{5/8})\le Cn^{-1/2}$ 及
$\mathbb E[(\Delta^2/n)1_{\{|\Delta|>n^{5/8}\}}]\le Cn^{-1/4}$。
故期望趋于 $\mathbb E\Delta^2/[2np(1-p)]=1/2$。
统一有界性则由 (68.48) 与模态的双边 $(n+1)^{-1/2}$ 界给出，包括小 $n$。

乘积律的熵与最小熵均逐坐标相加，故其差精确等于
$\sum_{j\in K_M}g(C_j,p_j)$。固定 $0<e<c_q$。
在 $I(\bar u_j)\le c_q-e$ 的格点，(68.29) 使全部 $C_j\ge e^{e\lambda/2}$，
所以每项统一趋于 $1/2$。
在 $I(\bar u_j)\ge c_q+e$ 的格点，(68.27)、(68.28) 给
$\mathbb E\sum C_j\le Q^{C}e^{-e\lambda}\to0$，
所以这些组以概率趋一全部为空，贡献精确为零。
剩余条带 $|I(\bar u_j)-c_q|\le e$ 中只用 $0\le g\le C$。

$I$ 的严格凸性及两侧单调性使水平集 $I=c_q$ 至多含两点。
固定条带和子水平集都是有限个区间，网格间距为 $Q^{-2}$，
投影到闭左端点只改变有界个格点。
先令规模趋无穷，再令 $e\downarrow0$，条带长度趋零，得到

```math
\frac1{Q^2}\sum_{j\in K_M}g(C_j,p_j)
       \longrightarrow\frac12\operatorname{Leb}\{I<c_q\}.
```

式 (68.52)。

(68.45) 将其传回实际后验，换算为比特即得 (68.44)。
若正区域接触闭左端点，其整个邻接区间仍被计入。
这里先逐组相减，故不必排除两种熵各自可能存在的更大格点或端点修正。
坏数据只付其概率；支持置换、未知方向的共同成功事件及 $H_M$ 上的原子重标记
均按定理 68.5 传递。没有期望熵、参数趋端点的一致性或有限精度解码结论。证毕。


**定理 68.8（完整后验的信息量波动与概率覆盖）。** 沿用定理 68.7，令

```math
Y_M=-\log_2\mathbb P(R\mid\mathscr X_M),\qquad
v(r,\beta)=\frac{\ell(r,\beta)}{2(\log2)^2}>0.
```

式 (68.53)。

$Y_M$ 在给定数据后仍由同一后验计数向量 $R$ 随机产生。
两种实际实验分别满足

```math
\sup_{z\in\mathbb R}\left|
\mathbb P\!\left\{\frac{Y_M-h_M(x)}Q\le z\,\middle|\,\mathscr X_M=x\right\}
 -\Phi\!\left(\frac z{\sqrt{v(r,\beta)}}\right)\right|
 \longrightarrow0
```

式 (68.54)。

同一概率意义下还有 $Q^{-2}\operatorname{Var}(Y_M\mid\mathscr X_M)\to v(r,\beta)$。
收敛以原始数据概率理解；$\Phi$ 是标准正态分布函数。
固定 $0<\varepsilon<1$，定义

```math
N_{\varepsilon,M}(x)=\min\{|A|:\mathbb P(R\in A\mid\mathscr X_M=x)\ge1-\varepsilon\}.
```

式 (68.55)。

最小值在有限后验支持的子集上取到，且

```math
\log_2N_{\varepsilon,M}(x)
 =h_M(x)+Q\sqrt{v(r,\beta)}\,\Phi^{-1}(1-\varepsilon)+o_{\mathbb P}(Q).
```

式 (68.56)。

这些后验函数仍有对确定支持抽样律一致的含义；在 $H_M$ 上，精确标量 $T_M$ 的原子覆盖数相同。
中心必须是实际纤维熵 $h_M(x)$，不是仅有一阶极限的 $Q^5\mathscr H(r,\beta)$。

**证明。** 先给出二项信息量的统一矩估计。记自然对数下
$Z_{n,p}=-\log f_{n,p}(K)$，$K\sim\operatorname{Bin}(n,p)$、$p\in[1/4,3/4]$。
由 (68.47)，信息量减去模态信息量是非负的，并至多为
$C+C(K-np)^2/(n+1)$。
八阶中心矩 $\mathbb E(K-np)^8\le C(n+1)^4$ 因而给

```math
\sup_{n,p}\mathbb E|Z_{n,p}-\mathbb EZ_{n,p}|^4<\infty,\qquad
\sup_p\left|\operatorname{Var}(Z_{n,p})-\frac12\right|\longrightarrow0
 \quad(n\to\infty).
```

式 (68.57)。

第二个极限可沿 (68.51) 的中心区间证明。
在 $|K-np|\le n^{5/8}$ 内，信息量减模态信息量与
$(K-np)^2/[2np(1-p)]$ 的差一致为 $O(n^{-1/8})$。
补集上的差平方由 $C+C(K-np)^4/n^2$ 控制；八阶矩使该补集期望趋零。
二项 CLT 对紧参数区间统一成立，其标准化四阶矩趋于三，
所以这个二次信息量的方差趋于 $\operatorname{Var}(G^2/2)=1/2$。
$n=0$ 时信息量恒为零；全部小 $n$ 的统一界保留。

在给定好数据的辅助乘积计数律下，各组信息量独立。
令 $s_x^2$ 为自然对数总信息量的方差。
以 (68.52) 的正区域、空区域及固定过渡条带分解，
(68.57) 与 $|K_M|=O(Q^2)$ 给

```math
\frac{s_x^2}{Q^2}\longrightarrow\frac\ell2,\qquad
\frac{\sum_{j\in K_M}\mathbb E_{\mathsf Q_x}
 |Z_{C_j,p_j}-\mathbb E_{\mathsf Q_x}Z_{C_j,p_j}|^4}{s_x^4}
 \le\frac{CQ^2}{s_x^4}\longrightarrow0
```

式 (68.58)。

这里两次收敛均在实际数据概率下；方差系数严格为正。
独立三角阵的 Lyapunov 定理于是给辅助总信息量的条件正态极限。
等价地，统一三阶矩与 Berry–Esseen 界在 $s_x\asymp Q$ 的事件上
给至多 $C/Q$ 的标准化分布误差。
再用 (68.58) 的方差极限，得到以 $Q$ 为尺度、方差为 $\ell/2$ 的极限。
随机环境的陈述可由任意子列再取上述系数几乎处处收敛的子列得到，故不要求环境本身独立。

最后处理精确后验。设 $\mathcal S=-\log\mathsf Q_x(R)$，则
$-\log\mathsf P_x(R)=\mathcal S-\log L(S_J)$，在实际正概率原子上精确成立。
(68.34) 使 $\mathcal S$ 的有界分布测试从乘积律传回实际律。
由 $L\le C$ 及 $\mathsf P_x=L\mathsf Q_x$，对任意固定 $a>0$，

```math
\mathsf P_x\{-\log L>aQ\}\le e^{-aQ},\qquad
\log L\le\log C.
```

式 (68.59)。

所以 $\log L/Q$ 在实际后验中趋零；零密度点没有实际质量。
(68.45) 又使两个精确均值之差为 $o_{\mathbb P}(Q)$。
Slutsky 定理及连续极限分布函数的统一性给 (68.54)，并按 $\log2$ 换算方差。
没有从 TV 直接传递无界信息量的期望。

方差结论需要单独核对。对 $0\le t\le C$，函数
$t(\log t)^2/(t-1)^2$ 在零和一处连续延拓后有界，故
$\mathbb E_{\mathsf P_x}(\log L)^2\le C\chi_x^2$。
独立组的信息量四阶中心矩之和与交叉二阶项给
$\mathbb E_{\mathsf Q_x}(\mathcal S-\mathbb E_{\mathsf Q_x}\mathcal S)^4\le CQ^4$。
以 $L-1$ 加权，再用 Cauchy–Schwarz，实际二阶中心矩与乘积值之差至多为
$C\chi_xQ^2$，实际均值偏移至多为 $C\chi_xQ$。
加入 $-\log L$ 的方差误差至多为 $C(Q\chi_x+\chi_x^2)$，
重新中心化还至多贡献 $C\chi_x^2Q^2$。
除以 $Q^2$ 并用 (68.46)、(68.58)，得所述实际方差极限。

概率覆盖使用经典有限字母表信息谱不等式。
若有限律的比特信息量为 $Y$，则 $A_b=\{Y\le b\}$ 至多有 $2^b$ 个原子；
另一方面，任意至多 $N$ 点的集合 $A$ 和任意 $t>0$ 满足

```math
\mathbb P(A)\le\mathbb P\{Y\le\log_2N+t\}+2^{-t}.
```

式 (68.60)。

因为阈值之外每个原子的概率小于 $2^{-t}/N$。
以 $h_M+Q(\sqrt v\,\Phi^{-1}(1-\varepsilon)+a)$ 截断，
(68.54) 给覆盖概率严格超过 $1-\varepsilon$，概率趋一；这给 (68.56) 的上界。
若 $\log_2N\le h_M+Q(\sqrt v\,\Phi^{-1}(1-\varepsilon)-a)$，
在 (68.60) 中取 $t=aQ/2$，其右边以数据概率趋于严格小于 $1-\varepsilon$ 的数，
给下界。任意 $a>0$ 的夹逼即得结论。
取整至多影响常数位数，因 $h_M/Q^5\to\mathscr H>0$ 而不影响本尺度。

支持置换及未知方向的共同成功事件按定理 68.5 处理；
$H_M$ 上单射仅重标记原子，因此也重标记达到最小覆盖数的集合。
结论不要求实际各组独立，不给 $\varepsilon\to0$ 的一致性、期望覆盖数、
有效枚举算法或带噪解码保证。证毕。


## 追加锚（68 章后）

## 69. 消失的测量噪声保留对角弱极限并抹去符号可恢复性

**定义 69.1（同一组电荷上的隐藏测量噪声）。** 保持定义 68.1 的原实际模型、固定振幅与
固定 $\beta\in(1/2,1)$。所有原始数据、完整窗口、精确后验中心、组电荷 $A_j$、
原对角统计量 $T_M$ 与偶极 $D_M$ 均取同一支持标签实现。记

```math
\rho(x)=c_0e^{-\kappa x^2/2},\quad
c_0=(4\pi\sqrt{ab})^{-1},\quad \kappa=a^{-1}+\alpha^2/b,
\quad\gamma=\int\rho,\quad g_0=\int\rho^2,
\quad c_q=\phi(1-\beta)/\beta.
```

式 (69.1)。

取固定 $D_*=8/\kappa$，定义对称核心与独立测量噪声

```math
R_c=\sqrt{D_*\log Q},\qquad
\mathcal K_M=\{j\in\mathbb Z:|j\delta|\le R_c\},\qquad m_M=|\mathcal K_M|,
\qquad X_j=A_j+\sigma_M\xi_j,
```

```math
\xi_j\overset{\mathrm{iid}}\sim N(0,1),\qquad
\sigma_M=Q^{-2}\quad\text{或}\quad \sigma_M=e^{-c_q\lambda/100}.
```

式 (69.2)。

两种噪声分别给出两个观测实验。噪声独立于原始数据及支持，其实现值不另行提供。
在原全行截断事件上，完整等分数组恰为原计数线的组，标记 $x_j=j\delta$。
在任意数据上，可将核心坐标定义为相应计数元组中属于原窗口的精确中心化标签和，缺组补零；
这样定义在截断成功时与原组电荷一致。原完整 $T_M,D_M$ 在失败数据上仍按原定义取值。
令

```math
T_M^{\mathrm{sm}}=\delta^{-1/2}
       \left(\sum_{j\in\mathcal K_M}X_j^2-V_M\right),\qquad
V_M=B^{-2}\sum_{i\in J}p_i(1-p_i).
```

式 (69.3)。

$V_M$ 是与原对角坐标相同的原始数据可测辅助方差中心；它不被替换为实际后验平方能量期望。
新的标量由带噪核心重新计算。

**定理 69.2（实际对角尺度上的近似与联合弱极限）。** 在上述两个噪声选择下，
原平稳独立对与连续路径实验都满足：对任意固定 $\varepsilon,\eta>0$，

```math
\mathbb P_{\mathrm{data}}
 \left\{\mathbb P\bigl(|T_M^{\mathrm{sm}}-T_M|>\varepsilon
                         \mid\mathscr X_M\bigr)>\eta\right\}\to0,
\qquad
\sup_{|S|=q}\mathbb P_S\{|T_M^{\mathrm{sm}}-T_M|>\varepsilon\}\to0.
```

式 (69.4)。

第一式在均匀大小 $q$ 支持先验下，内层为精确后验及独立测量噪声；
第二式为各确定支持的无条件抽样律。
对第 49、51、54 章已建立的同一旧联合组束 $\mathcal B_M$，
将对角坐标 $T_M$ 换成 $T_M^{\mathrm{sm}}$ 后联合极限不变：

```math
(T_M^{\mathrm{sm}},\mathcal B_M)\Longrightarrow(N_2,\mathcal B),
\qquad N_2\sim N(0,2g_0),\qquad N_2\perp\mathcal W_\rho.
```

式 (69.5)。

其中旧端点、偶极、固定紧区间上的剖面、桥、Fourier 场和定义 54.1 的有限截距保持原范围，
并由同一个旧实 Gaussian 随机测度 $\mathcal W_\rho$ 驱动。
条件 BL 收敛在先验数据概率意义下成立，无条件收敛一致于固定支持。

**证明。** 给出本章需要的实际有限估计及新增的尾部精度。
在全行计数截断内，原一、二行生成函数的系数比较给实际行概率与相应独立 Poisson
比较概率之间相对误差 $O(\lambda^3/M)$；其路径版本来自 (68.12) 的秩二矩阵，未假设实际行独立。
全行截断失败概率可取 $CM^{1-D_0}$，其中 $D_0$ 为任意充分大的固定数。
以 $C_j$ 表示计数线元组的占据数，以 $f_j$ 表示信号 Poisson 点概率，记

```math
\overline C_j=qf_j\{1+(1-q/M)e^{\tau-W_j}\},\quad
u_j=\overline C_j/B^2,\quad d_j=C_jp_j(1-p_j),\quad v_j=d_j/B^2.
```

式 (69.6)。

精确改变测度关系给 $\overline C_j=2qf_j(1+O(\chi_M))$，
其中 $\chi_M=C(q/M+\epsilon\lambda+\lambda(\alpha-P/Q)+q^{-1})$ 指数小。
实际一、二行比较和 $d_j\le C_j/4$ 给

```math
\mathbb E C_j=\overline C_j(1+O(\lambda^3/M)),\quad
\operatorname{Var}C_j\le C(\overline C_j+\lambda^3M^{-1}\overline C_j^2),
```

```math
\mathbb E v_j\le C\nu_j,\qquad
\mathbb E(v_jv_l)\le C\nu_j\nu_l\ (j\ne l),\qquad
\mathbb E v_j^2\le C(\nu_j^2+B^{-2}\nu_j).
```

式 (69.7)。

这些期望是实际数据上的方差时钟读数。
固定标记紧集上的 Stirling 展开与上述集中给
$v_j=\delta\rho(x_j)(1+o_{\mathbb P}(1))$ 一致成立。
在两计数均至少为各自均值一半的范围，$\nu_j\le C\delta e^{-c x_j^2}$；
其余截断线点的总贡献为 $Q^Ce^{-c\lambda}$。
Riemann 和及尾界于是给

```math
V_M\to\gamma,\qquad \delta^{-1}\sum_jv_j^2\to g_0,\qquad
\sum_jx_j^{2p}v_j\to\int x^{2p}\rho(x)\,dx
```

式 (69.8)。

每个 $p$ 在取极限前固定；没有增长次数的一致性。
共同校准还给全体方差 $d_{\mathrm{all}}\sim q/2$、
所选方差 $d_J=O_{\mathbb P}(B^2)=o_{\mathbb P}(q)$、补集方差 $d_{J^c}\sim q/2$。

给定数据，在同一个辅助乘积律 $\mathsf Q$ 中令

```math
U_j=B^{-1}\sum_{i\in J_j}(\zeta_i-p_i),\qquad
 e_j=B^{-1}\sum_{i\in J_j}(\pi_i-p_i),\qquad
 e_M=\frac{\sqrt{3d_J^2+d_J}}q+q^{-1/2}.
```

式 (69.9)。

完整辅助标签总数条件于 $q$ 后恰为原后验 $\mathsf P$。
第 35 章的 Bernoulli 局部极限定理及精确校准给完整所选向量的单次比较

```math
\tau_M:=d_{\mathrm{TV}}(\mathsf P_J,\mathsf Q_J)
 \le C(d_J/q+q^{-1/2}),\qquad
\|e\|_2\le C\sqrt{V_M}e_M,\qquad |e_j|\le C\sqrt{v_j}e_M.
```

式 (69.10)。

TV 按事件上确界定义，$e_M=O_{\mathbb P}(Q^{-5/2}+q^{-1/2})$。
中心估计由条件密度比的常数项抵消及 Cauchy–Schwarz 得到；
对任意一组数据可测 Hilbert 系数 $f_i$，同一论证给
$\|\sum f_i(\pi_i-p_i)\|\le C(\sum p_i(1-p_i)\|f_i\|^2)^{1/2}e_M$。
故上述群组范数界没有逐组并集损失。
所有矩计算留在 $\mathsf Q$ 中，只将误差事件经 (69.10) 转入实际后验。

关键是对角尺度要求被删平方质量为 $o_{\mathbb P}(\sqrt\delta)$。
令地板误差 $\xi_0=\{a\lambda\}$。线点相对 Poisson 均值的位移为
$x_j\sqrt\lambda-\xi_0$ 与 $(P/Q)x_j\sqrt\lambda+\xi_0$。
对 $\mu\asymp\lambda$、$|z|\le\mu/2$，Stirling 给

```math
\log\mathbb P\{\operatorname{Poi}(\mu)=\mu+z\}
=-\tfrac12\log(2\pi\mu)-\frac{z^2}{2\mu}
 +O(\mu^{-1}+|z|/\mu+|z|^3/\mu^2).
```

式 (69.11)。

在 $|x_j|\le\lambda^{1/8}$ 上，两坐标合计余项一致为
$O(\lambda^{-1/2}(1+|x_j|)^3+(\alpha-P/Q)(1+|x_j|)^2)=o(1)$。
因此可取 $\nu_j\le C\delta e^{-\kappa x_j^2/4}$；
更远截断线点之和为 $Q^Ce^{-c\lambda^{1/4}}$。
抽出半个 Gaussian 因子后，整个格点和满足

```math
\delta\sum_{|j\delta|>R_c}e^{-\kappa(j\delta)^2/4}
 \le e^{-\kappa R_c^2/8}\delta\sum_{j\in\mathbb Z}e^{-\kappa(j\delta)^2/8}
 \le C Q^{-\kappa D_*/8}.
```

式 (69.12)。

故 $L_M^{(0)}=\sum_{j\notin\mathcal K_M}v_j$ 在完整确定截断线上满足

```math
\mathbb E_{\mathrm{data}}L_M^{(0)}
 \le C Q^{-\kappa D_*/8}+Q^Ce^{-c\lambda^{1/4}},
\qquad \delta^{-1/2}\mathbb E L_M^{(0)}\to0.
```

式 (69.13)。

任意固定 $D_*>2/\kappa$ 都足够，本章所选值留有余量，不声称最优。
辅助律中被删平方和的期望为
$L_M^{(0)}+\sum_{j\notin\mathcal K_M}e_j^2\le L_M^{(0)}+CV_Me_M^2$。
于是对每个 $h>0$，在好数据上

```math
\mathsf P\left\{\delta^{-1/2}\sum_{j\notin\mathcal K_M}A_j^2>h
                       \mid\mathscr X_M\right\}
 \le\tau_M+h^{-1}\delta^{-1/2}(L_M^{(0)}+CV_Me_M^2)=o_{\mathbb P}(1).
```

式 (69.14)。

这是先用辅助矩界 Markov，再转移有界事件；不把辅助期望当成实际期望。

全行截断成功时有精确同向量恒等式

```math
T_M^{\mathrm{sm}}-T_M
=-\delta^{-1/2}\sum_{j\notin\mathcal K_M}A_j^2
 +2\sigma_M\delta^{-1/2}\sum_{j\in\mathcal K_M}A_j\xi_j
 +\sigma_M^2\delta^{-1/2}\sum_{j\in\mathcal K_M}\xi_j^2.
```

式 (69.15)。

两处同一个 $V_M$ 精确抵消。
原平方总质量 $\mathcal Q_M\to\gamma$ 在实际后验条件概率、先验数据概率意义下成立：
在辅助律中，$\operatorname{Var}\sum_jU_j^2\le2\sum_jv_j^2+B^{-2}V_M=o_{\mathbb P}(1)$，
精确中心位移由 $2\|U\|_2\|e\|_2+\|e\|_2^2$ 控制，再只转移相应事件即可。
给定任意实际电荷，(69.15) 第二项关于独立测量噪声的方差精确为
$4\sigma_M^2\delta^{-1}\sum_{\mathcal K_M}A_j^2$。
在 $\mathcal Q_M\le K$ 的事件上用 Chebyshev，其失败概率至多
$4\sigma_M^2\delta^{-1}K/h^2$；先固定 $K>\gamma+1$，实际定位失败概率趋零。
第三项非负，其噪声期望为

```math
\sigma_M^2\delta^{-1/2}m_M
 \le C\sigma_M^2\delta^{-3/2}(1+R_c).
```

式 (69.16)。

对多项式噪声，第二项方差系数为 $Q^{-7/2}$，第三项期望为
$O(Q^{-13/4}\sqrt{\log Q})$；指数噪声更小。
结合 (69.14)，截断失败只付概率，得到 (69.4) 第一式。
误差概率有界，故也在先验平均下趋零。
保持奇偶类的站点置换在大小 $q$ 支持上可迁，将原数据和标签一起置换保持所有组统计量不变；
使用同一按 $j$ 编号的噪声，误差事件也不变。
它在任意固定支持下的概率精确等于其先验平均，给出第二式。

最后，原旧组束与 $T_M$ 的联合极限先在同一辅助律中由混合线性—二次 CLT 建立，
再经共同有限秩核近似加入旧截距；$N_2$ 与全场的独立性已在这一步证明。
对任意有界单位 Lipschitz 联合测试 $f$，实际同一随机实现上有

```math
\left|\mathbb E[f(T_M^{\mathrm{sm}},\mathcal B_M)-f(T_M,\mathcal B_M)
                    \mid\mathscr X_M]\right|
 \le\varepsilon+2\mathbb P(|T_M^{\mathrm{sm}}-T_M|>\varepsilon\mid\mathscr X_M).
```

式 (69.17)。

先取规模极限再令 $\varepsilon\downarrow0$，得到条件 Slutsky 及 (69.5)。
联合弱极限定理中出现的旧潜在坐标并不自动成为下述解码实验允许观测的坐标。证毕。

**定理 69.3（所有可测解码器的符号风险）。** 令二值符号
$S_M=1$ 当 $D_M\ge0$，$S_M=-1$ 当 $D_M<0$。
在均匀支持先验下，存在原始数据可测 $b_M\in[0,1]$，
使 $b_M\to0$ 于先验数据概率和 $L^1$ 中，且对每个仅观察
$(\mathscr X_M,T_M^{\mathrm{sm}})$ 的可测二值解码器 $d_M$，

```math
\left|\mathbb P\{d_M(\mathscr X_M,T_M^{\mathrm{sm}})=S_M
                         \mid\mathscr X_M\}-\tfrac12\right|\le b_M.
```

式 (69.18)。

解码器可以随规模改变，且可以使用独立随机化；上界与解码器无关。
因此条件 Bayes 错误率与其先验平均都趋于 $1/2$。
更一般地，结论允许观测同一带噪向量 $X$ 的任意可测函数 $f_{\mathscr X_M}(X)$，
只要对每份固定数据，该函数在有限核心反射
$(\mathcal R x)_j=x_{-j}$ 下精确不变。
例如可同时提供带噪偶部、带噪 Fourier 功率曲线和 (69.3) 的标量。
这些观测必须由同一个 $X$ 计算，不能根据弱极限追加未平滑的标签坐标。

**证明。** 先证明增长核心维数下的有限反射 TV 界。
在 $R_c$ 核心内，(69.11) 的精度给

```math
f_j=\frac{e^{-\kappa x_j^2/2}}{2\pi\lambda\sqrt{ab}}
 \left[1+O\{\lambda^{-1/2}(1+R_c)^3+(\alpha-P/Q)(1+R_c)^2\}\right].
```

式 (69.19)。

最小期望占据数至少为 $c(q/\lambda)e^{-CR_c^2}\ge e^{c_q\lambda/2}$，最终成立。
对相对误差阈值 $Q^{-10}$ 使用 (69.7) 及 $m_M=O(\sqrt Q\sqrt{\log Q})$ 次并集界，
其失败概率至多
$CQ^{20}m_M\{(\min_j\overline C_j)^{-1}+\lambda^3/M\}=o(1)$。
共同 logistic 倾斜满足 $|\theta_M|\le1$ 的概率趋一；
$|\log[p_j(1-p_j)]-\log[p_{-j}(1-p_{-j})]|\le|W_j-W_{-j}|$，
所以该共同倾斜不会制造额外反射误差。
在好数据集上可取

```math
\min_{\mathcal K_M}d_j\ge e^{c_q\lambda/3},\quad
\sum_{\mathcal K_M}v_j\le C,\quad
\max_{\mathcal K_M}|v_j/v_{-j}-1|\le C\alpha_M,
```

```math
\alpha_M=\lambda^{-1/2}(1+R_c)^3+Q^{-10}
            +(\alpha-P/Q)(1+R_c)^2+\chi_M,
\qquad m_M\alpha_M^2\to0,\qquad m_Me_M^2\to0.
```

式 (69.20)。

最后两个界分别至多为 $O(Q^{-5/2}(1+\log Q)^{7/2})+o(1)$
与 $O(Q^{-9/2}\sqrt{1+\log Q})+o(1)$。
仅有逐坐标方差比趋一不足以代替它们。

给出所需的定量 Gaussian 耦合。
方差为 $d\ge1$ 的标准化 Bernoulli 和 $Z$ 由局部 CLT 及在 $[-d^{1/6},d^{1/6}]$
上的格点求和得到 Kolmogorov 误差 $Cd^{-1/3}$；区间外用 Chebyshev，且 $\mathbb EZ^4\le4$。
对其单调分位数耦合的标准 Gaussian $G$，若 $\epsilon=Cd^{-1/3}$，
积分分布函数差并用四阶尾界给
$\mathbb E|Z-G|\le2T\epsilon+CT^{-3}$。
取 $T=\epsilon^{-1/4}$，再在 $L^1,L^4$ 间插值得
$\mathbb E|Z-G|^2\le Cd^{-1/6}$。
独立地耦合辅助核心群组，得到同一空间上的独立 $G_j\sim N(0,v_j)$，满足

```math
\mathbb E_{\mathsf Q}\|U-G\|_2^2
 \le C\sum_{\mathcal K_M}v_jd_j^{-1/6}\le Ce^{-c_q\lambda/18},
\qquad \mathbb E_{\mathsf Q}\|U-G\|_2\le Ce^{-c_q\lambda/36}.
```

式 (69.21)。

维数已由总方差和支付。
Gaussian 平移公式和混合凸性给任意有限维耦合 $H,K$ 的经典平滑界

```math
d_{\mathrm{TV}}(\mathcal L(H+\sigma\xi),\mathcal L(K+\sigma\xi))
 \le\frac{\mathbb E\|H-K\|_2}{\sqrt{2\pi}\sigma}.
```

式 (69.22)。

精确中心位移在两端都保留：取 $H=U-e,K=G-e$。
设 $\nu_M=\mathcal L(X\mid\mathscr X_M)$，参考律为

```math
P_M^G=\bigotimes_{j\in\mathcal K_M}N(-e_j,v_j+\sigma_M^2),\qquad
 d_{\mathrm{TV}}(\nu_M,P_M^G)\le\tau_M+\eta_M^{\mathrm{sm}},
\quad \eta_M^{\mathrm{sm}}=C\sigma_M^{-1}e^{-c_q\lambda/36}\to0.
```

式 (69.23)。

指数噪声时，剩余指数为 $1/36-1/100=4/225>0$。
若把精确中心误差直接除以该噪声，则本证明不成立；(69.23) 没有作这种替换。

一维正方差 Gaussian 的亲和度为

```math
\operatorname{Aff}(N(\mu,w),N(\mu',w'))
 =\left(\frac{2\sqrt{ww'}}{w+w'}\right)^{1/2}
          \exp\left[-\frac{(\mu-\mu')^2}{4(w+w')}\right].
```

式 (69.24)。

独立乘积的亲和度相乘。
增加共同噪声方差只减小相对方差差，(69.20) 使反射方差的总负对数亲和度为 $O(m_M\alpha_M^2)$。
精确均值的反射差则满足

```math
\sum_{\mathcal K_M}
 \frac{(e_j-e_{-j})^2}{v_j+v_{-j}+2\sigma_M^2}
 \le C m_M e_M^2.
```

式 (69.25)。

由 $d_{\mathrm{TV}}\le\sqrt{1-\operatorname{Aff}^2}$ 及三角不等式，

```math
\Delta_M:=d_{\mathrm{TV}}(\nu_M,\mathcal R_\#\nu_M)
 \le2\tau_M+2\eta_M^{\mathrm{sm}}
                 +C\sqrt{m_M}(\alpha_M+e_M)\to0.
```

式 (69.26)。

坏数据上只用 $\Delta_M\le1$，所以数据概率与先验平均收敛同时成立。

还须将带噪核心符号接回原完整偶极。
令 $D_X=\sum_{\mathcal K_M}x_jX_j$，
$L_M^{(2)}=\sum_{j\notin\mathcal K_M}x_j^2v_j$ 与
$N_M^{(2)}=\sigma_M^2\sum_{\mathcal K_M}x_j^2$。
实际数据尾界给 $L_M^{(2)}\to0$，而
$N_M^{(2)}\le C\sigma_M^2\delta^{-1}(1+R_c)^3\to0$。
辅助律中的差平方期望由
$H_M^{\mathrm{sgn}}=(1+Ce_M^2)L_M^{(2)}+N_M^{(2)}$ 控制。
只转移 Chebyshev 事件，得到

```math
\mathbb P(|D_M-D_X|>h\mid\mathscr X_M)
 \le\tau_M+H_M^{\mathrm{sgn}}/h^2.
```

式 (69.27)。

参考律下 $D_X$ 是方差趋于 $\int x^2\rho=\gamma/\kappa>0$ 的 Gaussian，
无论其均值如何，在 $[-h,h]$ 的概率均至多 $Ch$。
经 (69.23) 转移并优化 $h$，得到

```math
r_M^{\mathrm{sgn}}:=\mathbb P(\operatorname{sgn}D_M\ne\operatorname{sgn}D_X
                                      \mid\mathscr X_M)
 \le C(H_M^{\mathrm{sgn}})^{1/3}+2\tau_M+\eta_M^{\mathrm{sm}}\to0.
```

式 (69.28)。

此处符号在零点取 $+1$；测量噪声使 $D_X$ 连续，原 $D_M$ 的零原子也由这些界趋零。

给定数据，$f(x)=\delta^{-1/2}(\|x\|_2^2-V_M)$ 精确反射不变，$D_X$ 在反射下变号。
任一确定二值解码器的成功集
$A=\{x:d_M(\mathscr X_M,f(x))=\operatorname{sgn}\sum_jx_jj\delta\}$
被反射变成其补集，除去一个 $\nu_M$ 零测超平面。
于是 $|2\nu_M(A)-1|\le\Delta_M$。
独立随机化可先固定随机种子再积分；任意反射不变可测观测同理。
将目标符号由 $D_X$ 换成 $D_M$，得到 (69.18)，其中好数据上可取
$b_M=\min(1,\Delta_M/2+r_M^{\mathrm{sgn}})$，其余取一。
所有界均不依赖解码器，所以覆盖随规模改变的任意可测规则。
这一步依靠有限 TV 与符号耦合，未从弱收敛推断解码风险。
带噪 Fourier 场反射后成为其共轭，故功率不变；偶部也逐点不变，所列观测都符合假设。证毕。

**推论 69.4（精确信息、平滑风险与确定支持边界）。** 原数据加精确 $T_M$ 在定理 68.2
的好事件上恢复全部组计数，条件离散熵按定理 68.5 以 Q^5 尺度增长。
本章重新计算的 $T_M^{\mathrm{sm}}$ 与 $T_M$ 的差趋零、联合弱极限相同，
但对原偶极符号的均匀先验 Bayes 错误率趋于 $1/2$。
因此该实际模型中，弱极限与同一实现上的依概率接近都不足以保存任意可测解码能力。

定理 69.3 的任意解码器范围不能改写为不受限制的逐确定支持结论。
若限制解码器在保持奇偶类的站点置换下不变，则有合法的无条件扩展

```math
\sup_{d_M\ \mathrm{invariant}}\sup_{|S|=q}
 \left|\mathbb P_S\{d_M(\mathscr X_M,T_M^{\mathrm{sm}})=S_M\}-\tfrac12\right|
 \le\mathbb E_{\mathrm{prior}}b_M\to0.
```

式 (69.29)。

**证明。** 前两句组合定理 68.2、定理 68.5 与本章两定理，保持相同精确中心、窗口、标签及数据。
对任意固定 $S_0$，一个将 $S_0$ 写死在程序内的规则可以从数据计算
$B^{-1}\sum_{i\in J}x_i(1_{i\in S_0}-\pi_i)$ 的符号，
在真实支持 $S_0$ 下总是正确；这排除了不受限制的确定支持风险说法。
对置换不变规则，成功事件在支持置换下不变，而该群在全部大小 $q$ 支持上传递。
每个支持的成功概率因此相同，并等于先验平均；积分 (69.18) 得 (69.29)。
已知反向实验先作原反向对齐。未知方向采用原共同判向事件，失败概率为 $O(q^{-1})$；
在成功事件上，数据、中心、核心、标量和偶极同时一致，噪声也可保持同一实现。
无条件误差和有界风险只增加这个失败概率，条件先验数据概率结论相应转移。
不把错误方向的工作权重解释成一个未指定方向先验的后验。
以上是电荷域测量噪声的结论；下面单独建立直接标量通道的比较。
指数 $1/100$ 和核心常数只是已核验的充分选择。
全部结果仍是原固定参数和原合法序列上的普通数学陈述，不是可行规模实验或形式核验。证毕。

**定理 69.5（原标量的任意固定多项式 Gaussian 噪声）。** 固定 $p,c>0$，
令 $G\sim N(0,1)$ 独立于原数据及支持标签，观察原标量的直接加噪版本

```math
Z_M=T_M+\upsilon_MG,\qquad \upsilon_M=cQ^{-p}.
```

式 (69.30)。

噪声实现值不提供给解码器。两种实际实验中，存在原数据可测 $a_M\in[0,1]$，
在均匀支持先验数据概率及均值意义下趋零，使所有依赖原数据与 $Z_M$ 的可测规则满足

```math
\sup_d\left|\mathbb P\{d(\mathscr X_M,Z_M)=S_M\mid\mathscr X_M\}
                           -\tfrac12\right|\le a_M.
```

式 (69.31)。

允许额外独立随机化。$(Z_M,\mathcal B_M)$ 同时保持 (69.5) 的原联合弱极限。
这对每个固定 $p,c$ 分别成立，不对增长的 $p$ 一致，也不含指数尺度直接标量噪声。
确定支持的无条件风险扩展仍只在置换不变规则类内成立。

**证明。** 先证明密度比较所需的经典有限界。若 $G_0\sim N(0,1)$、
$U\sim\chi^2_{m-1}$ 独立，$m=1$ 时取 $U=0$，则对充分小的 $\varepsilon\ge0$，

```math
d_{\rm TV}(\mathcal L(G_0+\varepsilon(G_0^2+U-m)),N(0,1))
 \le\min\{1,C\varepsilon(1+\sqrt m)\}.
```

式 (69.32)。

仅有随机误差趋零不够推出该 TV 结论：把正态数舍入到趋零网格，耦合误差趋零而 TV 恒为一。
为证明 (69.32)，先取固定光滑截断 $\chi$，在 $[-1,1]$ 为一、在 $[-2,2]$ 外为零。
置 $A=\varepsilon^{-1/2}$、$h(x)=x^2\chi(x/A)$、$F_t(x)=x+t\varepsilon h(x)$。
有 $|h|\le x^2$、$|h'|\le C|x|$；对小 $\varepsilon$，
$1/2\le F_t'\le3/2$ 且 $|x|/2\le|F_t(x)|\le3|x|/2$。
$F_t$ 因而为递增双射。以 $\varphi$ 表示标准正态密度，换元及对 $t$ 积分给

```math
2d_{\rm TV}(\mathcal L(F_1(G_0)),N(0,1))
 =\int|\varphi(x)-\varphi(F_1(x))F_1'(x)|\,dx\le C\varepsilon,
```

式 (69.33)。

因为被积表达式对 $t$ 的导数绝对值至多
$C\varepsilon(|x|^3+|x|)e^{-x^2/8}$。
$F_1(G_0)$ 与 $G_0+\varepsilon G_0^2$ 只在 $|G_0|>A$ 上不同，
该概率至多 $2e^{-1/(2\varepsilon)}$，所以未忽略完整二次映射远端的非单调分支。
再作 $-\varepsilon$ 平移，用正态平移 TV 界，得到
$d_{\rm TV}(G_0+\varepsilon(G_0^2-1),G_0)\le C\varepsilon$。
与同一个独立 $\varepsilon(U-(m-1))$ 卷积收缩 TV；随后混合正态平移界，
代价为 $C\varepsilon\mathbb E|U-(m-1)|\le C\varepsilon\sqrt{2(m-1)}$，得 (69.32)。
这里没有假定 $G_0$ 与 $G_0^2$ 独立。

为比较原通道，重新取固定核心常数与电荷噪声

```math
D_*^{(p)}=\frac{8(p+5/4)}\kappa,\quad
R_c^{(p)}=\sqrt{D_*^{(p)}\log Q},\quad
\sigma_M^{(p)}=\frac{c}{2\sqrt\gamma}Q^{-(p+1/4)},
```

```math
\overline T_M^{(p)}=\delta^{-1/2}
 \left[\sum_{|j\delta|\le R_c^{(p)}}(A_j+\sigma_M^{(p)}\xi_j)^2
             -m_M(\sigma_M^{(p)})^2-V_M\right].
```

式 (69.34)。

本证明以下简写核心、维数和电荷噪声为 $\mathcal K,m,\sigma$。
$\overline T_M^{(p)}$ 是一个辅助比较观测；其已知噪声平方偏差已扣除，原观察量仍是 (69.30)。
定理 69.3 的有限反射论证对该固定 $D_*^{(p)}$ 与 $\sigma$ 仍成立：
$m=O(Q^{1/2}\sqrt{\log Q})$，核心最小组方差保持指数下界，
$m\alpha_M^2\to0$、$me_M^2\to0$，而
$\sigma^{-1}e^{-c_q\lambda/36}\to0$。
有限核心偶极的测量噪声方差至多
$C\sigma^2\delta^{-1}(R_c^{(p)})^3
 =O(Q^{-2p}(\log Q)^{3/2})\to0$；
原偶极的核心尾、精确中心误差与反集中仍按 (69.26)–(69.28) 处理。
扣除确定的 $m\sigma^2$ 不破坏反射不变性。
因此该比较观测已具有 (69.31) 型风险结论。

现在必须把比较连回同一标签的原标量与符号。令实际核心、外部平方质量为

```math
E_c=\sum_{j\in\mathcal K}A_j^2,\qquad
E_o=\sum_{j\notin\mathcal K}A_j^2.
```

式 (69.35)。

本次所需精度是 $E_o=o_{\mathsf P}(\sigma)$，强于单独的 $E_o=o_{\mathsf P}(\sqrt\delta)$。
(69.12)–(69.13) 对新固定核心常数给
$\mathbb E_{\rm data}L_M^{(0)}\le CQ^{-(p+5/4)}+Q^Ce^{-c\lambda^{1/4}}$。
逐组精确中心界还给局部版本
$\sum_{j\notin\mathcal K}e_j^2\le Ce_M^2L_M^{(0)}$。
先在 $e_M\le1$ 的好数据上对辅助平方尾作 Markov，再通过一次所选向量 TV 转移该事件，得到

```math
\mathsf P\{E_o/\sigma>h\mid\mathscr X_M\}
 \le\tau_M+\frac{C L_M^{(0)}}{h\sigma}=o_{\mathbb P}(1)
 \qquad(h>0).
```

式 (69.36)。

其中 $\mathbb E L_M^{(0)}/\sigma=O(Q^{-1})+o(1)$，坏环境只付其概率。
结合原 $\mathcal Q_M\to\gamma$，得到 $E_c\to\gamma$ 的实际条件概率结论。
使用全局中心范数代替局部尾中心界会限制可处理的 $p$，此处不能丢掉局部化。

给定任意实际标签向量与数据、且 $E_c>0$，旋转独立测量正态到核心向量的方向，
其余平方和为独立的 $U\sim\chi^2_{m-1}$。于是该有限测量通道精确满足

```math
\overline T_M^{(p)}
\ \stackrel{d}{=}\ T_M-\delta^{-1/2}E_o
 +2\sigma\delta^{-1/2}\sqrt{E_c}
   \left[G_0+\frac{\sigma}{2\sqrt{E_c}}(G_0^2+U-m)\right].
```

式 (69.37)。

旋转只计算给定电荷的测量噪声律，不把电荷本身假定为 Gaussian。
在 $E_c\in[\gamma/2,2\gamma]$ 上，(69.32) 的误差至多
$C_\gamma\sigma(1+\sqrt m)=O(Q^{-p}(1+\log Q)^{1/4})\to0$。
主正态标准差与 $\upsilon_M$ 之比恰为 $\sqrt{E_c/\gamma}$；
平移量除以 $\upsilon_M$ 为 $E_o/(2\sqrt\gamma\sigma)$。
有限正态亲和度或直接密度积分因而给每个实际标签上的通道误差界

```math
\min\left\{1,C_\gamma
 \left[\sigma(1+\sqrt m)+|E_c/\gamma-1|+E_o/\sigma\right]\right\},
```

式 (69.38)。

在上述能量区间外只用界一。对同一个完整实际后验标签律混合，
由 (69.36) 和 $E_c\to\gamma$，这一有界误差的条件平均 $\epsilon_M(x)$ 趋零。
即使附带完整所选标签向量 $L_J$，仍有

```math
d_{\rm TV}\!\left(
 \mathcal L(Z_M,L_J\mid\mathscr X_M),
 \mathcal L(\overline T_M^{(p)},L_J\mid\mathscr X_M)\right)
 \le\epsilon_M(\mathscr X_M)\longrightarrow0.
```

式 (69.39)。

收敛在先验数据概率及均值意义下成立。两端使用相同后验混合权重，
所以原符号 $S_M$ 可随标签一起保留；单独的标量边缘 TV 不足以完成这一步。
所有解码成功事件现在只相差 $\epsilon_M$，与比较通道的反射风险界合并即得 (69.31)。
未把 TV 误差乘一个无界实际矩，也未从耦合接近直接推断 TV。

直接噪声 $\upsilon_MG$ 本身趋零，条件 Slutsky 保持原完整旧组束的联合弱极限。
对置换不变规则，原群作用仍保持直接标量通道与成功事件，故先验平均等于各确定支持概率；
不受限制的确定支持反例仍如推论 69.4。未知方向只使用同一个判向成功事件。

偏差修正对比较的范围有实质作用。若不扣除 $m\sigma^2$，
其均值除以主正态尺度为 $m\sigma/(2\sqrt\gamma)
 \asymp Q^{1/4-p}\sqrt{\log Q}$，在 $p\le1/4$ 时未趋零。
当 $p=7/4,c=2\sqrt\gamma$ 时，$\sigma=Q^{-2}$、$D_*^{(p)}=24/\kappa$，
该未修正偏差也趋零，故这时可直接与未扣偏差的核心平方和比较。
本定理不作对 $p\to\infty$ 的一致断言，也不把电荷域指定指数噪声的结论移到原标量上。证毕。

**定理 69.6（实际后验矩与直接噪声的信息量）。** 保持完整组计数向量 $R$、
原标量 $T_M$ 及均匀大小 $q$ 支持先验。记
$v_M(x)=\operatorname{Var}(T_M\mid\mathscr X_M=x)$。
对原平稳独立对和连续路径实验，

```math
\mathbb E(T_M^2\mid\mathscr X_M)=O_{\mathbb P}(1),\qquad
v_M(\mathscr X_M)=O_{\mathbb P}(1).
```

式 (69.40)。

令 $\upsilon_M>0$ 为确定数，$G\sim N(0,1)$ 独立于原数据和全部标签，
$Z_M=T_M+\upsilon_MG$，且噪声实现值不另行提供。
每份固定原始数据上，以同一后验计算的互信息满足

```math
I_x(R;Z_M)=I_x(T_M;Z_M)
 \le\frac12\log_2(1+v_M(x)/\upsilon_M^2)
 \le\log_2^+(1/\upsilon_M)+\tfrac12\log_2(1+v_M(x)).
```

式 (69.41)。

特别地，$\upsilon_M=cQ^{-p}$、固定 $p,c>0$ 时，
$I_x(R;Z_M)\le p\log_2Q+O_{\mathbb P}(1)$。
更一般地，只要 $\log^+(1/\upsilon_M)=o(Q^5)$，就有

```math
\frac{H_x(R\mid Z_M)}{Q^5}\longrightarrow\mathscr H(r,\beta),\qquad
\frac{I_x(R;Z_M)}{H_x(R)}\longrightarrow0
```

式 (69.42)。

这里 $H_x(R\mid Z_M)$ 是在固定数据纤维上、对 $Z_M\mid x$ 积分后的剩余离散熵；
不是对每个单独噪声输出逐点断言。分母为零时将比值定义为零。
所有渐近断言在先验数据概率下成立，并一致于确定支持的抽样律，
后者仍评价均匀先验定义的数据函数。
例如 $\upsilon_M=e^{-Q^4}$ 满足 (69.42)，但本定理不对该尺度声称 (69.31) 的符号风险结论。

**证明。** 先在实际数据上取得充分的方差时钟界。
沿 (68.23) 的全部确定截断线，信号 Poisson 点质量 $f_j$ 满足

```math
\max_j f_j\le C/\lambda,\qquad
\sum_j f_j\le C/(Q\sqrt\lambda).
```

式 (69.43)。

第一式由两个均值为固定正倍数 $\lambda$ 的 Poisson 最大原子界相乘得到。
第二式将负计数点质量上界为 $C/\sqrt\lambda$，正计数只落在模 $Q$ 的一个剩余类。
若 $K\sim\operatorname{Pois}(a\lambda)$，有限循环群 Fourier 反演给

```math
\mathbb P(K\equiv k_0\pmod Q)
 \le\frac1Q\sum_{l=0}^{Q-1}
 e^{-a\lambda(1-\cos(2\pi l/Q))}\le C/Q,
```

式 (69.44)。

因为 $1-\cos(2\pi l/Q)\ge c\min(l,Q-l)^2/Q^2$，而 $\lambda/Q^2=Q\to\infty$。
去掉不可行线点只减小此界，所以零计数端点和完整尾部均包含在内。
用 (68.27) 的 $m_j\le Cqf_j$ 与 (68.28) 的实际一、二行比较，有

```math
\sum_jm_j\le CB^2,\qquad
\sum_jm_j^2\le C(q/\lambda)B^2=CB^4\delta,
```

```math
\mathbb E_{\rm data}\sum_j C_j\le CB^2,\qquad
\mathbb E_{\rm data}\sum_j C_j^2\le C(B^2+B^4\delta).
```

式 (69.45)。

这里先对任意数据定义每个截断线占据数，再取实际期望；未条件于截断成功。
全行截断失败只付其概率，且 $d_j\le C_j/4$，因此 Markov 给

```math
V_M=O_{\mathbb P}(1),\qquad
\sum_jv_j^2=O_{\mathbb P}(\delta),\qquad d_J=B^2V_M=o_{\mathbb P}(q).
```

式 (69.46)。

这些较粗界已足够，无须从 Gaussian 弱极限推断实际矩。
原校准仍给 $d_{\rm all}\sim q/2$、$d_{J^c}/d_{\rm all}\to1$。

现在在固定数据上使用同一完整辅助 Bernoulli 乘积律 $\mathsf Q_x$ 与精确后验
$\mathsf P_x$。由 (68.33) 及其 Bernoulli 局部估计，令
$D_J=S_J-\mathbb E_{\mathsf Q_x}S_J$，则在概率趋一的数据集上，统一于所有所选标签，

```math
L(S_J)=a_x e^{-D_J^2/(2d_{J^c})}+\xi_x(S_J),\qquad
 a_x=\sqrt{d_{\rm all}/d_{J^c}},\quad
\sup|\xi_x|\le Cq^{-1/2},\quad 0\le L\le K_0.
```

式 (69.47)。

$K_0$ 为固定常数。分母是总均值恰为整数 $q$ 的中心原子，至少 $c/\sqrt{d_{\rm all}}$；
补集任意原子至多 $C/\sqrt{d_{J^c}}$，故最后一个界对遥远总数同样成立。
由此对任意非负函数 $F$ 有
$\mathbb E_{\mathsf P_x}F\le K_0\mathbb E_{\mathsf Q_x}F$。
这是本证明传递实际矩的依据；TV 接近本身不具有此性质。

沿用 (69.9) 的 $U_j=(n_j-C_jp_j)/B$、$e_j=(\mu_j-C_jp_j)/B$，
所以原电荷精确为 $A=U-e$，且 $e=\mathbb E_{\mathsf P_x}U$。
在 (69.47) 中消去 $\mathbb E_{\mathsf Q_x}U=0$ 的常数项，
由 $1-e^{-t}\le t$、Hilbert 空间 Cauchy–Schwarz 与
$\mathbb E_{\mathsf Q_x}D_J^4\le3d_J^2+d_J$，得到

```math
\|e\|_2
 \le C\sqrt{V_M}\left(\frac{\sqrt{3d_J^2+d_J}}q+q^{-1/2}\right)
 =O_{\mathbb P}(Q^{-5/2}+q^{-1/2}).
```

式 (69.48)。

这估计的是范数，不是范数平方；没有按组数放大中心误差。
各组在辅助律下独立。令 $Y=\sum_jU_j^2-V_M$，Bernoulli 四阶累积量的直接展开给

```math
\mathbb E_{\mathsf Q_x}Y^2\le2\sum_jv_j^2+B^{-2}V_M,\qquad
\mathbb E_{\mathsf Q_x}\langle U,e\rangle^2
   =\sum_jv_je_j^2\le V_M\|e\|_2^2.
```

式 (69.49)。

使用原定义 $T_M=\delta^{-1/2}(Y-2\langle U,e\rangle+\|e\|_2^2)$，
再用 (69.47) 对整个平方作非负密度支配，得到

```math
\mathbb E_{\mathsf P_x}T_M^2
 \le\frac{3K_0}{\delta}
 \left(2\sum_jv_j^2+B^{-2}V_M+4V_M\|e\|_2^2+\|e\|_2^4\right).
```

式 (69.50)。

第一项除以 $\delta$ 有界于数据概率，$B^{-2}/\delta=\lambda/q\to0$，
而 (69.48) 使其余项除以 $\delta$ 后趋零，证明 (69.40)。
坏数据上的有限矩不需要一致期望界，因此本结论不包含无条件二阶矩收敛。

最后固定任一份数据，包括上述坏数据。此时 $T_M=f_x(R)$ 只有有限多个值。
噪声通道条件于 $T_M$ 后与 $R$ 无关，链式法则给 (69.41) 的等号，
无需调用 $R\mapsto T_M$ 的单射性。
设 $m=\mathbb E_xT_M$、$v=v_M(x)$，$f$ 为 $Z_M$ 的有限 Gaussian 混合密度，
$g$ 为均值 $m$、方差 $v+\upsilon_M^2$ 的 Gaussian 密度。
以自然对数定义相对熵，经典混合恒等式为

```math
\sum_t\mathbb P_x(T_M=t)
 D\bigl(N(t,\upsilon_M^2)\Vert g\bigr)
 =I_x(T_M;Z_M)_{\rm nats}+D(f\Vert g)
 =\tfrac12\log(1+v/\upsilon_M^2).
```

式 (69.51)。

有限混合的对数密度有可积二次包络，故分解对数和交换有限求和合法。
非负性给信息上界，且
$1+v/\upsilon_M^2\le\max(1,\upsilon_M^{-2})(1+v)$。
这是成熟 Gaussian 通道不等式在本数据纤维上的应用；新增桥梁是 (69.45)–(69.50)
对原实际后验和精确中心的控制。

由定理 68.5 与有限输入信息恒等式
$H_x(R\mid Z_M)=H_x(R)-I_x(R;Z_M)$，立即得到 (69.42)。
对固定多项式噪声也可直接将 $c$ 保留在
$\tfrac12\log_2(1+v/c^2)$ 余项中。
支持置换保持所有这些均匀先验定义的数据函数，并在大小 $q$ 支持上传递，
故数据概率结论一致于确定支持。未知方向使用同一个判向成功事件。
这里没有把剩余熵等同于任意指定符号的风险，也不声称期望信息极限、
每个噪声输出的熵下界或稳定重构算法。证毕。

**定理 69.7（直接加噪后完整计数恢复的条件指数）。** 对任意确定的 $\upsilon_M>0$，
令 $Z_M=T_M+\upsilon_MG$，独立 Gaussian 噪声的实现值不另行公开。
给定原数据 $x$，记 $p_{{\rm guess},M}(x)$ 为所有可测规则仅观察 $(x,Z_M)$
后正确恢复完整组计数向量 $R$ 的最大条件成功概率；该概率已经对噪声输出与后验标签积分。
若 $\log^+(1/\upsilon_M)=o(Q^5)$，则两种实际实验分别满足

```math
\frac{-\log_2p_{{\rm guess},M}(\mathscr X_M)}{Q^5}
 \longrightarrow\mathscr H(r,\beta)
```

式 (69.52)。

收敛在先验数据概率下成立，且一致于确定支持抽样律下对同一均匀先验函数的评价。
另外，所有均匀先验解码规则的无条件成功概率之上确界趋零；
本定理不给出这个数据平均成功概率的 $Q^5$ 指数。

**证明。** 给定任意原数据，完整可行计数集合 $\mathcal F_x$ 有限。
记其后验概率为 $p_x(n)$、原精确标量值为 $t_x(n)$，$\varphi_\upsilon$ 为方差 $\upsilon^2$
的中心 Gaussian 密度。经典条件 Bayes 公式给

```math
p_{{\rm guess},M}(x)
 =\int_{\mathbb R}\max_{n\in\mathcal F_x}
             p_x(n)\varphi_{\upsilon_M}(z-t_x(n))\,\mathrm dz.
```

式 (69.53)。

有限个连续函数的最大值可测；按计数向量的字典序选择第一个最大者，得到可测最优规则。
固定规模的原数据字母表亦有限，因此各纤维规则可合为一个可测规则。
独立随机化不能改善逐点最大值。本式不要求 $n\mapsto t_x(n)$ 单射。

对任何可行计数，$n_j\ge0$、$\sum_jn_j\le q$，精确中心也满足
$\mu_j\ge0$、$\sum_j\mu_j\le q$。故
$0\le\sum_j(n_j-\mu_j)^2\le(\sum_jn_j+\sum_j\mu_j)^2\le4q^2$。
原 $T_M$ 的全部可能值因此位于一个长度至多

```math
L_M=\frac{4q^2}{B^2\sqrt\delta}=4qQ^{11/4},\qquad
\log L_M=c_qQ^3+\tfrac{11}4\log Q+O(1)
```

式 (69.54)。

的区间中。区间位置为原数据可测量，不需要控制其中心。
若所有均值在 $[a,a+L]$ 内，Gaussian 密度平移族的包络积分精确为
$1+L/(\sqrt{2\pi}\upsilon)$：区间内取密度峰值，区间外的两条尾积分各为 $1/2$。
在 (69.53) 中提出 $p_{\max,M}(x)$，并用忽略观测的模态规则作下界，便有

```math
p_{\max,M}(x)\le p_{{\rm guess},M}(x)
 \le\min\left\{1,p_{\max,M}(x)
               \left(1+\frac{L_M}{\sqrt{2\pi}\upsilon_M}\right)\right\}.
```

式 (69.55)。

这是经典猜测成功率与最大泄漏界在有界均值 Gaussian 通道上的应用。
它对每份数据成立，连截断失败的数据也包含在内；不需要后验矩、
Gaussian 后验近似、最小标量间距或中心误差除以噪声尺度的估计。

(69.54) 与噪声假设使
$\log_2(1+L_M/(\sqrt{2\pi}\upsilon_M))=o(Q^5)$。
对 (69.55) 取负对数，便把恢复指数夹在 $h_{\infty,M}$ 与它减去该确定开销之间；
定理 68.6 给 (69.52)。例如 $\upsilon_M=e^{-Q^4}$ 满足条件，
开销的自然对数至多 $Q^4+c_qQ^3+O(\log Q)$。
正噪声条件实质必要于此计算：固定规模令噪声趋零时包络发散，不能将本界代入零噪声。
这不把所给充分尺度条件判为最优阈值。

取固定 $0<\eta<\mathscr H(r,\beta)$，有

```math
\mathbb E_{\rm prior}p_{{\rm guess},M}
 \le\mathbb P_{\rm prior}\{-\log_2p_{{\rm guess},M}<\eta Q^5\}
                  +2^{-\eta Q^5}\longrightarrow0.
```

式 (69.56)。

可测 Bayes 规则的先验成功概率等于左边，故这是所有规则的统一界。
第一个概率只知趋零，没有 $Q^5$ 指数控制；不能进一步给左边宣称同样指数。
完整向量的恢复困难也不能推出某个符号或单个计数的恢复困难。

保持奇偶类的站点置换同时作用于数据和支持，保持原组计数、精确中心、$T_M$ 及噪声通道。
这些均匀先验函数因而在各大小 $q$ 支持下有相同数据分布，得到 (69.52) 的一致性。
若解码器也置换不变，其无条件成功概率在各支持下相同，并等于先验平均，故同样趋零。
不受限制的确定支持规则可写死 $S_0$ 并从数据直接计数组内 $S_0$ 成员，
在真实支持为 $S_0$ 时成功率为一；因此不作这种无条件风险扩展。
未知方向沿用同一个判向成功事件，数据概率结论按事件一致性转移，
平均风险只增加趋零的判向错误概率，不取得新的指数结论。证毕。

## 追加锚（69 章后）

## 70. 完整后验 Rényi 熵谱与零阶极限的过渡

**定义 70.1（原始数据纤维上的 Rényi 熵）。** 保留第 68 章的模型、完整窗口和计数向量 $R$。
对每份原始数据 $x$，令 $\mathsf P_x$ 是均匀大小 $q$ 支持先验的精确计数后验，
$\mathsf Q_x$ 是同一校准参数下的独立二项计数律。
以 $\nu$ 表示熵的阶数，原计数线斜率 $\alpha$ 不变。定义

```math
H_{\nu,M}(x)=\frac{\log_2\sum_n\mathsf P_x(n)^\nu}{1-\nu}
 \quad(0<\nu\ne1),\qquad
H_{0,M}(x)=\log_2|\operatorname{supp}\mathsf P_x|,
```

```math
H_{1,M}=h_M,\qquad H_{\infty,M}=h_{\infty,M},\qquad
\widetilde H_{\nu,M}=H_\nu(\mathsf Q_x),\qquad
A(u)=(c_q-I(u))_+.
```

式 (70.1)。

$h_M,h_{\infty,M},c_q,I,\mathcal I,\ell,\mathscr H$ 均取第 68 章的定义。
阶数为零时仅数正概率的组计数元组，不数每个元组内部的标签排列。
这些量都在同一数据纤维上先取有限和，再取对数。

**定理 70.2（固定正阶的次阶熵差与完整支持熵）。** 对每个固定
$\nu\in(0,\infty)\setminus\{1\}$，两种实际实验分别满足

```math
H_{\nu,M}-\widetilde H_{\nu,M}=O_{\mathbb P,\nu}(Q^{-5/2}),\qquad
\frac{H_{\nu,M}-H_{\infty,M}}{Q^2}
 \longrightarrow\frac{\ell\log\nu}{2(\nu-1)\log2}.
```

式 (70.2)。

在概率趋一的数据集上，完整实际后验支持精确为
$\prod_{j\in K_M}\{0,\ldots,C_j\}$，故

```math
H_{0,M}=\sum_{j\in K_M}\log_2(C_j+1)=\widetilde H_{0,M},\qquad
\frac{H_{0,M}}{Q^5}\longrightarrow2\mathscr H.
```

式 (70.3)。

收敛在先验数据概率下成立，亦一致于所有大小 $q$ 确定支持的抽样律；
后一表述评价同一均匀先验后验函数，不改用点质量先验。
每个固定正阶的 $Q^5$ 主系数因而都是 $\mathscr H$。
阶数一的差及阶数无穷的主项分别已由定理 68.7、68.6 给出。
常数不要求一致于 $\nu\to1$ 或 $\nu\to\infty$。

**证明。** 使用第 68 章的实际一、二行比较、完整线占据数与全局校准。
记 $N_J=\sum_jC_j$、$d_c=d_{J^c}$。这些估计给

```math
N_J=O_{\mathbb P}(qQ^{-5/2}),\qquad d_{\rm all},d_c\sim q/2,
\qquad d_J=O_{\mathbb P}(qQ^{-5/2}).
```

式 (70.4)。

这里第一式来自实际行数，而不是从后验方差反推。
所以以概率趋一有 $N_J<q<M-N_J$；补集 Bernoulli 参数均严格在零一之间，
每个 $0\le\sum_jn_j\le N_J$ 都能由补集凑成总数 $q$。
这证明完整盒支持。(68.29) 的对数占据数估计及全域 Riemann 和随即证明 (70.3)。

还需要比窗口半宽更精确的参数界。
在全行截断上，完整窗口恰为原有计数线，因而

```math
\sup_{j\in K_M}|W_j-\tau|
 \le C\{\lambda|\alpha-P/Q|+\epsilon\lambda+q^{-1}\}
 =o(q^{-1/2}),\qquad
\eta_x:=\max_{j:C_j>0}|p_j-1/2|=O_{\mathbb P}(q^{-1/2}).
```

式 (70.5)。

第一项的十进制尾是 $10^{-Q^5}$ 阶；第二项乘 $\sqrt q$ 的指数率为
$-\phi+c_q/2<0$；第三项显然满足。
又有 $\tau-\log((M-q)/q)=O(q/M)=o(q^{-1/2})$，
加上 $O_{\mathbb P}(q^{-1/2})$ 的全局校准根即得第二式。
空组单独置 $p_j=1/2$，不改变任何律。

令 $m_J=\sum_jC_jp_j$、$D=k-m_J$。
精确后验与乘积律的密度比仍为

```math
L_x(k)=\frac{\mathsf Q_x(S_{J^c}=q-k)}{\mathsf Q_x(S_{\rm all}=q)},\qquad
\mathsf P_x(n)=L_x\!\left(\sum_jn_j\right)\mathsf Q_x(n).
```

式 (70.6)。

(68.39) 的局部 Bernoulli 界给
$\log L_x(k)\le C(d_J/q+q^{-1/2})$。
远离中心的下界不能取该加性近似的对数，须另作倾斜。
对补集定义 $K(t)=\sum_{i\notin J}\log(1-p_i+p_ie^t)$。
logistic 方差的对数导数绝对值至多为一，所以

```math
e^{-|t|}d_c\le K''(t)\le e^{|t|}d_c.
```

式 (70.7)。

在 $d_c\ge c_1q$ 且 $N_J\le c_1q/(4e)$ 的好数据上，
每个所选总数都对应唯一 $t$，使 $K'(t)=q-k$，且
$|t|\le C|D|/q=o(1)$，一致于完整盒。
这是将 (70.7) 先在 $[-1,1]$ 上积分定位根，再用导数下界所得。
倾斜后的均值恰为目标整数，方差 $d_t=K''(t)\asymp q$，
故同一局部 Bernoulli 估计给中心原子
$(2\pi d_t)^{-1/2}(1+O(q^{-1/2}))$。
撤销倾斜付出 $\exp(-\mathcal I_t)$，其中
$0\le\mathcal I_t=t(q-k)-K(t)\le C D^2/q$。
由于 $d_{\rm all}\ge d_c$ 且 $|\log(d_t/d_c)|\le|t|$，得到

```math
-C\{D^2/q+q^{-1/2}\}\le\log L_x(k)
 \le C\{d_J/q+q^{-1/2}\},\qquad0\le k\le N_J.
```

式 (70.8)。

此式允许极端元组具有很小的密度比；并未给出一致的正常数下界。

现在估计乘积计数律的幂倾斜。
对 $f_{n,p}(k)=\binom nkp^k(1-p)^{n-k}$，令

```math
f_{n,p;\nu}(k)=\frac{f_{n,p}(k)^\nu}{\sum_h f_{n,p}(h)^\nu}
 \propto\binom nk^\nu e^{\nu t k},\qquad t=\operatorname{logit}p.
```

式 (70.9)。

这是经典 COM-binomial 指数族，在 Kadane 的参数化中成功参数为
$\operatorname{logistic}(\nu\operatorname{logit}p)$，而非原 $p$；其计数组合因子也被取幂，
因此不同于先对独立标签取幂再合并为计数。
以下直接证明所需的阶数一致界。
记未归一化权重为 $w_k$、相邻比为 $r_k=w_{k+1}/w_k$。
当 $n\ge2$ 时

```math
\log r_{k+1}-\log r_k
 =\nu\left\{\log\frac{n-k-1}{n-k}+\log\frac{k+1}{k+2}\right\}
 \le-2\nu/n=:-\kappa.
```

式 (70.10)。

取该律的两个独立样本 $X_1,X_2$，条件于和 $h$。
距离 $d=|X_1-h/2|$ 的格为非负整数或正半整数；
除零点一次、其余两次的重数外，权重为 $w_{h/2+d}w_{h/2-d}$。
相邻距离权重比至多为 $e^{-\kappa(2d+1)}$。
所以其对同重数折叠离散 Gaussian $e^{-\kappa d^2}$ 的密度比随距离不增，
递增函数的期望不超过该 Gaussian 的期望。
这一比较由递增函数与递减密度比的协方差非正直接得到。
整数格、半整数格的 Gaussian 和与积分比较给
$\mathbb E d^2\le C(1+\kappa^{-1})$；$\kappa\ge1$ 时先提出最小格点权重即可。
因此
$2\operatorname{Var}X_1=\mathbb E(X_1-X_2)^2=4\mathbb Ed^2\le C(1+n/\nu)$。
$n=1$ 用方差至多 $1/4$，$n=0$ 为零。

在 $t=0$ 处均值为 $n/2$，均值对 $t$ 的导数为 $\nu\operatorname{Var}X_1$。
积分并用 $|\operatorname{logit}p|\le C|p-1/2|$，对 $p\in[1/4,3/4]$ 得

```math
\operatorname{Var}_{n,p;\nu}X_1\le Cn/\nu,\qquad
|\mathbb E_{n,p;\nu}X_1-np|\le Cn|p-1/2|,\quad0<\nu\le1.
```

式 (70.11)。

对每个固定 $\nu>1$，同样的结论以依赖 $\nu$ 的常数成立。
产品律的幂倾斜仍是这些计数幂倾斜的乘积，故

```math
\mathbb E_{\mathsf Q_{x,\nu}}D^2
 \le C\{N_J/\nu+\eta_x^2N_J^2\}\quad(0<\nu\le1).
```

式 (70.12)。

固定 $\nu>1$ 时右边可写成 $C_\nu(N_J+\eta_x^2N_J^2)$。
这已足够，无须另证每个组的幂倾斜均值偏移为 $O_\nu(1)$。

在完整盒支持事件上精确有

```math
(\log2)(H_{\nu,M}-\widetilde H_{\nu,M})
 =\frac{\log\mathbb E_{\mathsf Q_{x,\nu}}L_x^\nu}{1-\nu}.
```

式 (70.13)。

Jensen 不等式、(70.8)、(70.12) 给，在 $0<\nu\le1$ 上一致地

```math
-C\left\{\frac{N_J}q+\frac{\nu\eta_x^2N_J^2}q+\nu q^{-1/2}\right\}
 \le\log\mathbb E_{\mathsf Q_{x,\nu}}L_x^\nu
 \le C\nu(d_J/q+q^{-1/2}).
```

式 (70.14)。

(70.4)、(70.5) 使 $\eta_x^2N_J^2/q=O_{\mathbb P}(Q^{-5})$；
不需要这些数据函数相互独立。
故对固定非一正阶得到 (70.2) 第一式，$\nu>1$ 用同一固定阶矩界。
同时已得到后续所需的更强一致性

```math
\sup_{0<\nu\le1/2}|H_{\nu,M}-\widetilde H_{\nu,M}|
 =O_{\mathbb P}(Q^{-5/2}).
```

式 (70.15)。

分母不靠近零；未将此绝对误差界一致地延伸到 $\nu=1$ 的缩小邻域。

固定阶的单组结论由经典二项局部极限给出。
具体地，紧参数区间上对全部原子都有

```math
\frac c{\sqrt{n+1}}e^{-C(k-np)^2/(n+1)}
 \le f_{n,p}(k)\le
\frac C{\sqrt{n+1}}e^{-c(k-np)^2/(n+1)}.
```

式 (70.16)。

下界已见 (68.47)。上界在 $k/n$ 离端点有固定距离时由 Stirling 与
$D(k/n\Vert p)\ge2(k/n-p)^2$ 得到；在其余区域，
$|k-np|\ge cn$，粗略类型上界 $e^{-nD}$ 的额外指数衰减吸收所需的 $\sqrt{n+1}$ 因子。
于是中心 Stirling 展开、标准化网格的 Riemann 和及 (70.16) 的尾控制给

```math
\sum_{k=0}^n f_{n,p}(k)^\nu
 =(2\pi np(1-p))^{(1-\nu)/2}\nu^{-1/2}(1+o(1)),
```

```math
h_\nu(f_{n,p})-h_\infty(f_{n,p})\longrightarrow
 \frac{\log\nu}{2(\nu-1)},\qquad
0\le h_\nu(f_{n,p})-h_\infty(f_{n,p})\le C_\nu.
```

式 (70.17)。

这里 $h$ 用自然对数，阶数固定且不为一，极限对 $p\in[1/4,3/4]$ 一致；
小 $n$ 包括零由 (70.16) 及双边模态界处理。
其中有界差还可直接使用 Melbourne–Tkocz 对整数对数凹律的经典界
$h_\nu-h_\infty<\log\nu/(\nu-1)$；它不要求质量序列单调，
但不能替代这里的半倍 Gaussian 极限和趋零阶数的一致估计。
这些单组 Gaussian 熵系数是成熟工具，不是新的抽象熵公式。

产品律的两种熵都逐组相加。
在 $I\le c_q-e$ 的固定正区域上占据数指数增长，故每组贡献趋于 (70.17) 的常数；
在 $I\ge c_q+e$ 上实际组以概率趋一全部为空；
过渡条带用 $C_\nu$ 界。
先令规模趋无穷，再令 $e\downarrow0$，第 68 章的完整域网格计数给正区域长度 $\ell$。
由定理 68.6 的最小熵比较及 (70.13) 传回实际律，即得 (70.2) 第二式。
端点邻接区间未删除，也未分别展开两个熵的较大算术修正。
支持置换及共同判向成功事件按第 68 章传递全部结论。证毕。

**定理 70.3（阶数随规模趋零的完整过渡）。** 对任意确定序列 $0<\nu_M\le1$，若
$Q^{-3}\log(1/\nu_M)\to s\in[0,\infty)$，则在定理 70.2 的同一概率意义下

```math
\frac{H_{\nu_M,M}}{Q^5}
 \longrightarrow\frac1{2\log2}
 \int_{\mathcal I}\{A(u)+\min(A(u),s)\}\,du.
```

式 (70.18)。

$s=0$ 时极限为 $\mathscr H$；$s\ge c_q=\max A$ 时为 $2\mathscr H$。
若 $Q^{-3}\log(1/\nu_M)\to\infty$，仍得到 $2\mathscr H$。

**证明。** 不能把移动阶数代入 (70.17) 的固定阶展开。
对 $0<\nu\le1/2$，将 (70.16) 取幂后求和，直接有一致双边估计

```math
\sum_k f_{n,p}(k)^\nu\asymp(n+1)^{-\nu/2}
 \min\left\{n+1,\sqrt{\frac{n+1}{\nu}}\right\}.
```

式 (70.19)。

上界同时使用全格 Gaussian 和及项数；下界在距均值不超过较小宽度的固定倍数内取格点。
由于 $p\in[1/4,3/4]$，该区域至少含常数倍相应宽度的可行整数，指数项统一有正下界。
小 $n$ 和零占据数单独满足同一常数界。
置 $t=\log(n+1)$、$b_\nu=\log(1/\nu)$；对 (70.19) 取对数并除以 $1-\nu$，得

```math
\left|h_\nu(f_{n,p})-\frac12\{t+\min(t,b_\nu)\}\right|\le C.
```

式 (70.20)。

额外项至多为 $\nu\log(1/\nu)/(2(1-\nu))$，在这个阶数范围一致有界。
此估计包括 $\nu n$ 约为一的交界，无须另设空隙。

将 (70.20) 沿完整计数线相加并用 (70.15)，
再由 (68.29) 将 $\log(1+C_j)$ 换成 $Q^3A(\bar u_j)$。
最小值对每个参数都是 Lipschitz，故在归一化 $Q^5$ 下，
占据数替换误差为 $O_{\mathbb P}(\log Q/Q^3)$，单组有界误差之和为 $O(Q^{-3})$。
剩下的 Riemann 和为

```math
\frac1{2\log2\,Q^2}\sum_{j\in K_M}
 \{A(\bar u_j)+\min(A(\bar u_j),Q^{-3}\log(1/\nu_M))\}.
```

式 (70.21)。

$A$ 在完整闭域连续且支撑紧；有限 $s$ 下由一致连续性及最小值的 Lipschitz 性得到 (70.18)。
$s=\infty$ 时第二个参数最终超过 $\max A$，给两倍积分。

$s>0$ 或 $s=\infty$ 时阶数最终小于 $1/2$。
$s=0$ 时，对阶数大于 $1/2$ 的其余指标用
$H_{1,M}\le H_{\nu_M,M}\le H_{1/2,M}$；
两端的归一化极限都是 $\mathscr H$，与小阶子列一起完成夹逼。
这一步允许阶数趋近一甚至等于一，没有除以趋零的 $1-\nu_M$。

极端元组的条件化代价可达 $N_J^2/q$，本身无需趋零。
真正进入幂和的是 (70.12) 的期望乘阶数：
$\nu\mathbb E_{\mathsf Q_{x,\nu}}D^2/q
\le C\{N_J/q+\nu\eta_x^2N_J^2/q\}=O_{\mathbb P}(Q^{-5/2})$。
所以本模型的固定总数约束不另添一条相变条件。
先固定正阶取规模极限、再令阶数趋零，得到 $\mathscr H$；
先在每个有限规模令阶数趋零得到支持熵，再取规模极限，则是 $2\mathscr H$。
(70.18) 给出这两个顺序之间的过渡。
所有结论仍为数据概率极限，不涉及期望熵、变化的 $\beta$、负阶、
随规模增长的阶数或噪声解码风险。证毕。

## 追加锚（70 章后）

## 71. 直接标量噪声下的信息谱与列表恢复

**定义 71.1（带噪输出与有限列表）。** 保留第 68–69 章的原实验、完整窗口、
均匀大小 $q$ 支持先验和精确中心。给定原始数据 $x$，记完整组计数后验为
$\mathsf P_x$，正支撑为有限集 $\mathcal F_x$，并写

```math
\imath_x(n)=-\log_2\mathsf P_x(n),\qquad
h_x=\mathbb E_x\imath_x(R),\qquad
v_*=\frac{\ell}{2(\log2)^2}.
```

式 (71.1)。

$h_x$ 是定理 68.8 的精确纤维熵。令 $t_x(n)$ 为定义 54.1 的原 $T_M$ 在计数元组 $n$ 上的值，
仍使用全固定基数后验均值及原校准方差中心。观察

```math
Y=T_M+\sigma_M G,\qquad G\sim N(0,1),\qquad
\sigma_M>0\text{ 为确定序列},\qquad
\log^+(1/\sigma_M)=o(Q),
```

式 (71.2)。

$G$ 独立于原始数据和完整标签。给定 $x$，以下概率包含 $R$ 与 $G$ 的同一联合律。
其输出密度和输出后验为

```math
w_n(y)=\varphi_{\sigma_M}(y-t_x(n)),\qquad
f_x(y)=\sum_{n\in\mathcal F_x}\mathsf P_x(n)w_n(y)>0,\qquad
\mathsf P_x^y(n)=\frac{\mathsf P_x(n)w_n(y)}{f_x(y)}.
```

式 (71.3)。

对整数 $K\ge0$，定义

```math
\Psi_x(K)=\sup_{\mathcal L:\,|\mathcal L_x(y)|\le K}
 \mathbb P_x\{R\in\mathcal L_x(Y)\},\qquad
C_x^0(K)=\max_{A\subseteq\mathcal F_x,\ |A|\le K}\mathsf P_x(A).
```

式 (71.4)。

列表可随 $x,y$ 改变，其大小预算对所有输出相同。
允许列表使用独立于原始数据、标签及 $G$ 的辅助随机性，大小约束对每次随机化都成立；
成功率同时对该随机性平均。确定列表是其中的特例。
称随机列表置换不变，是指保持奇偶类的站点置换作用于数据和计数目标时，
其输出列表的条件分布按同一作用变换，即策略核等变。
$\Psi_x$ 是对噪声输出平均的最优成功率；$C_x^0$ 是不使用新增输出的最优成功率。
$K=0$ 时两者为零，$K\ge|\mathcal F_x|$ 时为一。
这里没有假定标量映射 $t_x$ 单射，亦不需要第 68 章的超越性论证。

**定理 71.2（信息谱稳定与列表大小的次阶极限）。** 在 (71.2) 下，两种原实际实验分别满足

```math
\sup_z\left|\mathbb P_x\left\{
 \frac{-\log_2\mathsf P_x^Y(R)-h_x}{Q}\le z\right\}
 -\Phi\left(\frac z{\sqrt{v_*}}\right)\right|
 \longrightarrow0
```

式 (71.5)。

收敛在原始数据概率下成立，且一致于所有大小 $q$ 的确定支持；
该表述始终评价同一均匀先验定义的联合纤维律，未将其换成点质量先验。
对每个固定 $z\in\mathbb R$，令 $K_x(z)=\lfloor2^{h_x+Qz}\rfloor$，则

```math
C_x^0(K_x(z))\longrightarrow\Phi(z/\sqrt{v_*}),\qquad
\Psi_x(K_x(z))\longrightarrow\Phi(z/\sqrt{v_*}).
```

式 (71.6)。

对固定 $0<\varepsilon<1$，令

```math
K_{\varepsilon,M}^{\rm noisy}(x)
 =\min\{K\in\{0,\ldots,|\mathcal F_x|\}:\Psi_x(K)\ge1-\varepsilon\}.
```

式 (71.7)。

在同一概率意义下，

```math
\log_2K_{\varepsilon,M}^{\rm noisy}(x)
 =h_x+Q\sqrt{v_*}\Phi^{-1}(1-\varepsilon)+o_{\mathbb P}(Q).
```

式 (71.8)。

这是输出平均的共同列表预算。(71.5) 也在联合纤维律中积分了 $Y$，
不声称每个输出后验各自具有同一正态信息谱。
固定参数与精确中心均保留，不将 $h_x$ 换成其 $Q^5$ 主项。

**证明。** 所需实际模型输入是定理 68.8 的原信息谱及定理 69.6 的实际矩界

```math
\sup_z\left|\mathsf P_x\{(\imath_x-h_x)/Q\le z\}
 -\Phi(z/\sqrt{v_*})\right|\longrightarrow0,\qquad
m_{2,x}:=\mathbb E_xT_M^2=O_{\mathbb P}(1).
```

式 (71.9)。

第二式并不来自弱收敛。为明确它与当前标量的对应，沿用 69.6 的单一校准乘积律，
置 $U_j=(R_j-C_jp_j)/B$、$e_j=(\mu_j-C_jp_j)/B$、$v_j=C_jp_j(1-p_j)/B^2$，
$V=\sum_jv_j$、$L=d\mathsf P_x/d\mathsf Q_x$、$a_x=\|L-1\|_2$。
其实际行数估计与精确密度计算给出

```math
V=O_{\mathbb P}(1),\qquad \sum_jv_j^2=O_{\mathbb P}(\delta),\qquad
0\le L\le C,\qquad a_x=O_{\mathbb P}(Q^{-5/2}),\qquad
\|e\|\le a_x\sqrt V,
```

```math
T_M=\delta^{-1/2}\left\{\sum_j(U_j^2-v_j)-2e\cdot U+\|e\|^2\right\},
```

```math
m_{2,x}\le\frac C\delta
 \left\{2\sum_jv_j^2+B^{-2}V+4a_x^2V^2+a_x^4V^2\right\}
 =O_{\mathbb P}(1).
```

式 (71.10)。

其中 $B^{-2}/\delta=Q^3/q\to0$。这是对同一完整计数向量的非负平方使用密度支配，
保留了 $\|e\|^2$ 截距；并未将 TV 接近当作矩传递。
坏环境只进入外层数据概率，未乘以一个无界统计量。

固定一个有限纤维。每个 $w_n$ 严格正且连续，故按
$\mathsf P_x(n)w_n(y)$ 降序、以按得分排列的计数元组字典序破同分，
取前 $K\wedge|\mathcal F_x|$ 个，得到 Borel 可测的最优列表。
它逐点最大化有限和，因此积分后恰取得 (71.4) 的上确界；随机列表也不能超过它。
每个 $M$ 的原始数据字母表有限，所以校准根、后验中心、预算和此选择器对 $x$ 都可测。
同理，(71.7) 的有限最小值可测且存在。

首先用信息密度连接 (71.9) 与新增输出。
自然对数单位下的纤维互信息由定理 69.6 的经典 Gaussian 通道界控制：

```math
I_x(R;Y)=I_x(T_M;T_M+\sigma_M G)
 \le\frac12\log\left(1+\frac{m_{2,x}}{\sigma_M^2}\right)
 =o_{\mathbb P}(Q).
```

式 (71.11)。

末式也适用于噪声增大：上界至多为
$\tfrac12\log(1+m_{2,x})+\log^+(1/\sigma_M)$。
全部熵积分在有限 Gaussian 混合上有定义。
令 $i_x(n,y)=\log(w_n(y)/f_x(y))$。严格正性给精确恒等式

```math
\mathbb E_xe^{-i_x(R,Y)}
 =\sum_n\mathsf P_x(n)\int w_n(y)\frac{f_x(y)}{w_n(y)}\,dy=1.
```

式 (71.12)。

所以 $\mathbb P_x(i_x<-t)\le e^{-t}$，积分尾界得 $\mathbb E_x(i_x)_-\le1$，进而

```math
\mathbb E_x|i_x|=I_x+2\mathbb E_x(i_x)_-\le I_x+2,
\qquad
\mathbb P_x\{|i_x|>bQ\}\le\frac{I_x+2}{bQ}=o_{\mathbb P}(1)
\quad(b>0).
```

式 (71.13)。

这是把平均信息变成谱扰动控制所需的一步。
仅凭一个熵数不能确定原谱；此处已另有 (71.9) 的实际条件 CLT。
Bayes 公式又给

```math
-\log_2\mathsf P_x^Y(R)=\imath_x(R)-\frac{i_x(R,Y)}{\log2}.
```

式 (71.14)。

对任意固定 $b>0$，(71.13) 及阈值两侧移动 $b/\log2$ 将 (71.5) 的误差界为
原 Kolmogorov 误差、一个 $o_{\mathbb P}(1)$ 和正态分布在此宽度内的最大质量之和。
先取规模极限，再令 $b\downarrow0$，即证 (71.5)。
不需要 $T_M$ 与原信息谱独立，亦未声称信息密度对每个输出都小。

对任意有限律 $p$，记其 $K$ 个最大原子的质量为 $C_p(K)$，
其惊奇量 $-\log_2p$ 的分布函数为 $F_p$。
直接数原子可得对任意 $K\ge1,b>0$

```math
F_p(\log_2K-b)\le C_p(K)
 \le F_p(\log_2K+b)+2^{-b}.
```

式 (71.15)。

左侧集合中每个原子的质量至少为 $2^b/K$，所以它至多有 $K$ 个元素；
右侧则将最优 $K$ 集合中质量小于 $2^{-b}/K$ 的部分单独估计。
这是经典一次信息谱计数界。
对每个输出的有限后验 $\mathsf P_x^y$ 使用此式，再对 $y$ 积分，得到

```math
\mathbb P_x\{-\log_2\mathsf P_x^Y(R)\le\log_2K-b\}
 \le\Psi_x(K)
 \le\mathbb P_x\{-\log_2\mathsf P_x^Y(R)\le\log_2K+b\}+2^{-b}.
```

式 (71.16)。

因为 $h_x/Q^5\to\mathscr H>0$，对固定 $z$，以概率趋一有
$K_x(z)\ge1$ 且 $\log_2K_x(z)=h_x+Qz+o(1)$。
取 $b=\sqrt Q$，由 (71.5)、(71.16) 得 (71.6) 第二式；
用原律版本的 (71.9)、(71.15) 得第一式。

再置 $z_\varepsilon=\sqrt{v_*}\Phi^{-1}(1-\varepsilon)$。
对任意固定 $a>0$，正态值在 $z_\varepsilon-a,z_\varepsilon+a$ 处严格夹住 $1-\varepsilon$。
(71.6) 与 $\Psi_x$ 对 $K$ 的单调性使 (71.7) 以概率趋一夹在
$\lfloor2^{h_x+Q(z_\varepsilon-a)}\rfloor$ 与
$\lfloor2^{h_x+Q(z_\varepsilon+a)}\rfloor$ 之间。
取对数再令 $a\downarrow0$ 即得 (71.8)，无需改变误差水平或假定数据收敛速率。

还有一条直接保留原信息谱的有限上界。
对任意半径 $R_0>0$、松弛 $t>0$，按
$|T_M|>R_0$、$\imath_x\le\log_2K+t$ 和剩余原子分拆任意列表的成功事件，得到

```math
C_x^0(K)\le\Psi_x(K)
 \le\mathsf P_x\{\imath_x\le\log_2K+t\}
 +\frac{m_{2,x}}{R_0^2}
 +2^{-t}\left(1+\frac{2R_0}{\sqrt{2\pi}\sigma_M}\right).
```

式 (71.17)。

剩余原子各至多为 $2^{-t}/K$，而列表最多有 $K$ 个；
其通道密度积分由区间 Gaussian 包络
$\int\sup_{|u|\le R_0}\varphi_\sigma(y-u)\,dy
=1+2R_0/(\sqrt{2\pi}\sigma)$ 控制。
区间内取峰值、外面取最近端点，两侧尾积分相加为一，证明该公式。
取 $R_0=Q^a$、固定 $a>0$，再取
$t=\log_2(1+2Q^a/(\sqrt{2\pi}\sigma_M))+\sqrt Q=o(Q)$，
(71.17) 也给出相同的成功率上界。
这里截断的是上界证明中的输入集合，没有剪裁实际观测或更换 $T_M$。
整个确定标量范围的对数为 $O(Q^3)$，不能代替这一步所需的 $o(Q)$ 通道代价。

最后说明固定支持下的风险范围。
保持奇偶类的站点置换把支持 $S$ 的原对／路径实验映到支持 $\pi S$，
并保持按得分排列的计数坐标、完整先验后验、校准根、精确中心及 $t_x$。
预算 $K_x(z)$ 置换不变；字典序仅用于给出一个可测最优列表，
不要求这个确定的破平局规则本身等变。
记有限置换群为 $\mathcal G_M$，取与一切观测、标签及 $G$ 独立的均匀群元 $U$。
将上述确定最优列表记为 $\mathcal L^*$，定义
$\widetilde{\mathcal L}_x(y;U)=U^{-1}\mathcal L^*_{Ux}(y)$，
其中群对列表的作用来自它对计数目标的双射。
后验质量和通道密度在该双射下保持，所以每个 $U$ 给出的拉回列表
仍逐纤维取得最优值，且每次大小不超过 $K_x(z)$。
对任意 $\pi\in\mathcal G_M$，以均匀群元 $U\pi$ 换元可得
$\widetilde{\mathcal L}_{\pi x}(y;U)$ 与
$\pi\widetilde{\mathcal L}_x(y;U)$ 同分布。
这就在允许标量碰撞时给出等变最优策略核。
使用同一 $G$，群在大小 $q$ 支持上传递，故任意这种策略核的积分成功率对支持相同。
平均此恒等值等于其先验 Bayes 成功率；对称化最优策略逐纤维取得上界，因而

```math
\sup_{\substack{\mathcal L\ {\rm 置换不变的随机策略核}\\
 |\mathcal L_x(y;U)|\le K_x(z)}}
 \Pr_{S,G,U}\{R(S,\mathscr X)\in\mathcal L_{\mathscr X}(Y;U)\}
 =\mathbb E_{\rm prior\ data}\Psi_{\mathscr X}(K_{\mathscr X}(z))
 \longrightarrow\Phi(z/\sqrt{v_*}).
```

式 (71.18)。

成功率有界，故数据概率收敛足以给这里的期望收敛。
这里 $S$ 固定，概率对原实验、Gaussian 噪声及独立策略随机性平均；
式中的 $U$ 对一般策略表示其辅助随机性，对上述最优构造则是均匀群元。
这不提供熵或对数列表大小的期望展开。
不限制策略的逐支持结论会被写死该支持的单元素列表推翻；(71.18) 的策略类不能删除。
反向实验先作原整体反转；未知方向使用已有共同判向事件并耦合同一噪声，
使全部数据函数及成功事件同时一致，误差由该事件的失败概率控制。

结论包含如 $\sigma_M=e^{-\sqrt Q}$ 的噪声，未分类
$\log(1/\sigma_M)\sim cQ$ 或更小噪声。
(71.17) 在那个尺度留下的代价只是上界余量，不是可达增益或锐利相变。
不涉及逐输出保证、变化的 $\varepsilon$、特定符号风险、有限精度效率或实验等价。证毕。

## 追加锚（71 章后）

## 72. 熵的确定中心与格点边缘的剩余随机性

**定义 72.1（实际平均占据数中心）。** 保持第 68 章的原幅度、固定
$\beta\in(1/2,1)$、合法规模和完整窗口。以 $\mathcal E$ 区分原平稳对与连续路径实验。
对每个规模，枚举所有非负整数对 $k+l\le2M\lambda$ 在原窗口内产生的得分，
得到有限确定集合 $\mathcal G_M$。每个得分只保留一份，允许相同得分来自不同计数对。
令 $C_g$ 为该完整得分组的实际行数，定义

```math
\bar c_g^{\mathcal E}=\mathbb E_S^{\mathcal E}C_g,\qquad
b_{ent}(n)=H(\operatorname{Bin}(n,1/2)),\quad b_{ent}(0)=0,
\qquad d_M^{\mathcal E}=\sum_{g\in\mathcal G_M}
 b_{ent}(\lfloor\bar c_g^{\mathcal E}\rfloor).
```

式 (72.1)。

熵以 bits 计。保持奇偶类的站点置换把任意大小 $q$ 支持映到另一个支持，
共轭原核并保持均匀平稳初始律，也保持完整得分组的行数。
所以 $\bar c_g^{\mathcal E}$ 精确地不依赖支持的选择。
它是原始数据行数的期望，不是原后验标签中心 $\mu_j$；后者未改动。
两种实验的精确中心暂不识别为相同。
反向实验在交换每对的两个端点或整体反转路径后，恰有同一正确定向的定义。

**定理 72.2（确定熵中心与至多两个过渡组）。** 记 $h_M(x)$ 为原完整组计数的精确后验 Shannon 熵。
对每个固定合法 $\beta$，两种实际实验分别有

```math
h_M(\mathscr X)-d_M^{\mathcal E}=O_{\mathbb P}(1)=o_{\mathbb P}(Q).
```

式 (72.2)。

收敛与紧性在先验数据律下成立，也一致于所有大小 $q$ 确定支持的抽样律，
后者评价同一均匀先验定义的熵函数。
取足够大的固定行数截断 $k+l\le C_0\lambda$，其窗口计数线索引仍记为 $K_M$。
将该线的完整得分组均值写成 $\bar c_j^{\mathcal E}$，令

```math
\mathcal B_M^{\mathcal E}
 =\{j\in K_M:Q^{-8}\le\bar c_j^{\mathcal E}\le Q^8\}.
```

式 (72.3)。

则最终 $|\mathcal B_M^{\mathcal E}|\le2$，而且

```math
h_M-d_M^{\mathcal E}
 =\sum_{j\in\mathcal B_M^{\mathcal E}}
 \{b_{ent}(C_j)-b_{ent}(\lfloor\bar c_j^{\mathcal E}\rfloor)\}
 +o_{\mathbb P}(1).
```

式 (72.4)。

阈值 $Q^{\pm8}$ 和截断只用于证明，不更改原观察窗口。

**证明。** 先处理完整得分组与截断计数线的关系。
原行 PGF 在两个标记均为 2 时给
$\mathbb E2^{k_i+l_i}\le2e^\lambda$。
固定 $C_0$ 足够大，可使超出截断的总行数 $T_{\rm tail}$ 满足

```math
\mathbb E T_{\rm tail}\le CM^{-10}=:\rho_M,\qquad
\Pr(T_{\rm tail}>0)\le\rho_M.
```

式 (72.5)。

截断内的所有所选计数恰为 $(k_j,l_j)=(k_0+jQ,l_0+jP)$，
不同 $j$ 有严格不同的补偿得分，且 $|K_M|=O(Q^2)$。
令 $\widehat C_j$ 只计精确计数对 $(k_j,l_j)$，均值为 $\nu_j^{\mathcal E}$。
远处计数对即使与该得分相撞，也仅来自 (72.5)，所以

```math
0\le\bar c_j^{\mathcal E}-\nu_j^{\mathcal E},\qquad
\sum_{j\in K_M}(\bar c_j^{\mathcal E}-\nu_j^{\mathcal E})\le\rho_M.
```

式 (72.6)。

截断得分以外的每组均值均小于 $\rho_M<1$，在 (72.1) 中贡献精确为零。
在 $T_{\rm tail}=0$ 上，所有 $C_j=\widehat C_j$ 同时成立。

沿用第 68 章的信号与背景 Poisson 点概率

```math
f_j=e^{-\lambda}\frac{(a\lambda)^{k_j}(b\lambda)^{l_j}}{k_j!l_j!},\qquad
f_j^0=e^{-\lambda}\frac{((1-\epsilon)\lambda/2)^{k_j}
 ((1+\epsilon)\lambda/2)^{l_j}}{k_j!l_j!},\qquad
m_j=qf_j+(M-q)f_j^0.
```

式 (72.7)。

这里 $a=(1+r)/2,b=(1-r)/2$，$b_{ent}$ 与模型参数 $b$ 区分。
原实际一、二行比较给，以 $\varepsilon_M=C\lambda^3/M$ 记其统一相对误差，

```math
|\nu_j^{\mathcal E}-m_j|\le\varepsilon_Mm_j,\qquad
\operatorname{Var}(\widehat C_j)\le C(m_j+\varepsilon_Mm_j^2).
```

式 (72.8)。

未把实际路径行数换成独立 Poisson 行。
(70.4)、(70.5) 的全线行数与近半校准，以及 (68.45) 的熵比较，给

```math
N_J=O_{\mathbb P}(qQ^{-5/2}),\qquad
\eta_x:=\max_{j:C_j>0}|p_j-1/2|=O_{\mathbb P}(q^{-1/2}),
```

```math
h_M-\sum_jH(\operatorname{Bin}(C_j,p_j))=O_{\mathbb P}(Q^{-3/2}).
```

式 (72.9)。

近半率用原计数线得分误差与全局校准根，不能只用宽度较大的得分窗口。
熵比较先将乘积惊奇量中心化，再使用精确密度的 $L^2$ 范数，未由 TV 传递无界熵。

暂用自然对数，记 $g(n,p)=H_{\rm nats}(\operatorname{Bin}(n,p))$。
第 68 章的全部原子下界与 Bernoulli 四阶矩给
$\sup_{n\in\mathbb Z_{\ge0},\ p\in[1/4,3/4]}\operatorname{Var}[-\log f_{n,p}(R)]\le C$。
对有限熵和求导，以二项得分函数作协方差，再用 Cauchy–Schwarz，得到

```math
|\partial_p g(n,p)|
 =\left|\operatorname{Cov}\left(-\log f_{n,p}(R),
 \frac{R-np}{p(1-p)}\right)\right|\le C\sqrt n.
```

式 (72.10)。

因此全部参数替换的误差至多
$C\eta_x\sum_j\sqrt{C_j}\le C\eta_x\sqrt{|K_M|N_J}
=O_{\mathbb P}(Q^{-1/4})=o_{\mathbb P}(1)$。
与 (72.5)、(72.9) 合并得

```math
h_M=\sum_{j\in K_M}b_{ent}(\widehat C_j)+o_{\mathbb P}(1).
```

式 (72.11)。

再看过渡组的几何。第 68 章的 $I$ 在内部严格凸，以零为唯一极小点，
$I(u)=c_q>0$ 的内部根至多两个且导数非零。
若左端点恰为根，其右导数趋于负无穷；在一侧邻域仍可取固定负导数上界。
故对每个固定 $\beta$ 和足够小的 $v>0$，集合 $|I-c_q|\le v$
由至多两个长度不超过 $Cv$ 的区间组成，包含端点情形。
由全部整数的 Stirling 界与 (72.7)，

```math
\sup_{j\in K_M}|\log m_j-\lambda(c_q-I(\bar u_j))|\le C\log Q,
\qquad u_j=j/Q^2,
```

式 (72.12)。

$\bar u_j$ 只将越过合法左端点 $O(\lambda^{-1})$ 的可行格点投回该端点。
对 (72.3) 中的组，(72.6)、(72.8) 给 $m_j/\bar c_j^{\mathcal E}\to1$，
故 $|I(\bar u_j)-c_q|\le C\log Q/Q^3$。
这两个可能区间的长度及端点修正均为 $o(Q^{-2})$，小于原格距，
所以各至多含一个原格点。这证明 (72.3) 的基数界。
同样，按 $m_j$ 定义的过渡集也至多有两个元素。

最后需要比每组有界误差更精确的熵增量。置 $g(n)=(\log2)b_{ent}(n)$。
令 $S\sim\operatorname{Bin}(n,1/2)$ 与独立公平位 $B$ 相加，$K=S+B$。
由交换性，$\Pr(B=1\mid K)=K/(n+1)$；链式法则和二元 KL 的卡方上界给

```math
0<g(n+1)-g(n)=I(B;K)
 =\mathbb E D(\operatorname{Bern}(K/(n+1))\Vert\operatorname{Bern}(1/2))
 \le4\operatorname{Var}(K/(n+1))=\frac1{n+1}.
```

式 (72.13)。

于是对整数 $c,N\ge0$，
$|g(c)-g(N)|\le|c-N|/(\min(c,N)+1)$，
且 $g(N)\le C\log(N+1)$、$g(N)\le N\log2$。
以 $\mu=\bar c_j^{\mathcal E}\ge2$ 记一组均值，
在 $\widehat C_j\ge\mu/2$ 上用上述增量界，在补事件上用熵的对数上界和 (72.8) 的 Chebyshev 界，得

```math
\mathbb E|g(\widehat C_j)-g(\lfloor\mu\rfloor)|
 \le C\left\{\mu^{-1/2}+\sqrt{\varepsilon_M}
 +\frac{1+\rho_M}\mu
 +(\mu^{-1}+\varepsilon_M)\log(\mu+1)\right\}.
```

式 (72.14)。

(72.6) 控制均值偏移；此处期望取实际点计数，未由高概率一致推出矩界。
$0\le\mu\le2$ 时期望误差统一有界，$\mu<1$ 时确定项为零且期望至多 $\mu\log2$。

在 $\mu<Q^{-8}$ 的全部组上，期望误差和至多 $CQ^{-6}$。
在 $\mu>Q^8$ 上将 (72.14) 求和，使用 $\mu\le M$、$|K_M|=O(Q^2)$，所得上界为

```math
C\{Q^{-2}+Q^{-6}\log Q+Q^2\sqrt{\varepsilon_M}
 +Q^2\varepsilon_M\lambda+\rho_MQ^{-6}\}=o(1).
```

式 (72.15)。

只剩至多两个过渡组，每组期望绝对误差统一有界。
由 (72.11) 得 (72.2)，保留这些组即得 (72.4)。
这里界住的是截断点计数的熵误差期望，不能据此宣称完整后验熵在坏数据上也一致可积。证毕。

**定理 72.3（显式中心与 Poisson 剩余项）。** 令 $m_j$ 精确取 (72.7)，并定义

```math
\widetilde d_M=
 \frac1{2\log2}\sum_{j\in K_M:m_j>Q^8}\log(\pi e m_j/2)
 +\sum_{j\in K_M:Q^{-8}\le m_j\le Q^8}
 b_{ent}(\lfloor m_j\rfloor).
```

式 (72.16)。

则 $d_M^{\mathcal E}-\widetilde d_M=O(1)$，故
$h_M-\widetilde d_M=O_{\mathbb P}(1)=o_{\mathbb P}(Q)$。
该显式中心同时适用于两种实验，完整保留 $k_0,l_0,P,Q,M,q,\epsilon$ 的原值及阶乘。

更精细地，任意子序列都能继续抽取，使至多两个过渡组的均值各趋于 $[0,\infty]$ 中一点。
保留其中正有限极限 $\theta_1,\ldots,\theta_t$，并继续抽取使相应
$\lfloor\bar c_j^{\mathcal E}\rfloor=k_v$ 固定，则

```math
h_M-d_M^{\mathcal E}\ \Longrightarrow\
 \sum_{v=1}^t\{b_{ent}(P_{\theta_v})-b_{ent}(k_v)\},\qquad
P_{\theta_v}\text{ 相互独立},\quad P_{\theta_v}\sim\operatorname{Pois}(\theta_v),
\quad 0\le t\le2.
```

式 (72.17)。

若 $\theta_v$ 非整数，则 $k_v=\lfloor\theta_v\rfloor$；若它是正整数，
$k_v$ 可以是该整数或小一的整数，不能省去这一侧向取整信息。
特别地，$h_M-d_M^{\mathcal E}=o_{\mathbb P}(1)$ 当且仅当过渡组均值没有趋于正有限值的子序列。
原幅度不变时，存在一个固定合法 $\beta$ 及合法规模子序列，使

```math
h_M-d_M^{\mathcal E}\ \Longrightarrow\ b_{ent}(P_\theta),
\qquad \theta\in[1/4,1/2],
```

式 (72.18)。

该非退化结论分别对两种实际实验成立，排除了对所有合法参数统一声称 $o_{\mathbb P}(1)$。

**证明。** 先比较确定中心。
$m_j>Q^8$ 时，(72.6)、(72.8)、(72.13) 给逐组误差
$C(\varepsilon_M+(1+\rho_M)/m_j)$，总和趋零。
$m_j<Q^{-8}$ 时两种均值的下取整最终均为零。
中间至多两组满足 $|\bar c_j^{\mathcal E}-m_j|\le\varepsilon_MQ^8+\rho_M\to0$，
其下取整最多差一，每组成本至多一 bit。因此

```math
\left|d_M^{\mathcal E}-\sum_{j\in K_M}b_{ent}(\lfloor m_j\rfloor)\right|
 \le2+o(1).
```

式 (72.19)。

经典公平二项熵展开
$b_{ent}(n)=\log(\pi e n/2)/(2\log2)+O(n^{-1})$
在高占据组上总共只损失 $O(Q^{-6})$，证明 (72.16) 的精度。
有限均值处的整数跨越使 (72.19) 不能自动加强为 $o(1)$。
充分大固定截断之外 $m_j<1$，不改变最终确定求和。
未将每项 $\log m_j$ 换成误差为 $O(\log Q)$ 的粗率函数，避免在 $Q^2$ 项上累加丢失所需精度。

为证明实际 Poisson 极限，将原标记行 PGF 推到任意固定数目 $h$ 的不同候选行。
置 $u_i=(z_{i,+}+z_{i,-})/2-1$、$v_i=(z_{i,+}-z_{i,-})/2$，
未标记行取零，并令 $A=\mathbb E(u+b_Sv)$、$B_1=\mathbb E(v+b_Su)$，
其中平均在全部 $2M$ 个状态上取。原平稳路径的精确 PGF 仍为

```math
e_1^{\mathsf T}\begin{pmatrix}1+A&B_1\\A&B_1\end{pmatrix}^{2M\lambda}e_1;
```

式 (72.20)。

独立对的版本为 $(1+A)^{2M\lambda}$。
在固定标记多圆盘上，主特征值为 $1+A+O_h(M^{-2})$，其系数 $1+O_h(M^{-1})$，
另一项可忽略。Cauchy 系数半径取 $\max(k,1)$ 除以对应 Poisson 均值，
相对系数成本为 $O_h(\lambda^h)$，所以截断内每个指定计数事件满足

```math
\Pr(\text{指定 }h\text{ 行计数})
 =\Pr_{\rm Pois}(\text{同一计数})
 \{1+O_h(\lambda^{h+1}/M)\}.
```

式 (72.21)。

对均值趋于 $\theta_v\in(0,\infty)$ 的有限个不同移动格点，
$m_j\to\theta_v$，信号和背景贡献各趋于 $\theta_v/2$，最大单行点概率为 $O(1/q)$。
展开其任意固定混合下降阶乘矩，(72.21) 控制不同实际行的概率；
去除重复行指派只产生 $o(1)$，于是

```math
\mathbb E\prod_{v=1}^t(\widehat C_{j_v})_{r_v}
 \longrightarrow\prod_{v=1}^t\theta_v^{r_v}
\quad\text{对每个固定非负整数向量 }(r_1,\ldots,r_t).
```

式 (72.22)。

所有更高固定阶矩亦有界，提供子序列极限传矩所需的一致可积；
独立 Poisson 向量的矩母函数在零附近有限，唯一确定其律。
故这些实际计数联合趋于相互独立的 Poisson 变量，(72.5) 再移回完整得分组。
原始路径行之间的依赖一直保留在 (72.20) 中。

过渡均值趋零时，由 $\mathbb E b_{ent}(\widehat C_j)\le\bar c_j^{\mathcal E}$ 去掉该项；
趋无穷时由 (72.14) 去掉其中心化误差。
剩余项用计数的离散弱极限和 (72.4)，得到 (72.17)，无需原熵期望收敛。
$b_{ent}$ 严格递增，每个正均值 Poisson 项都非退化，其独立和亦非退化。
对至多两个过渡均值作扩充实轴的子序列紧性论证，即得所述 $o_{\mathbb P}(1)$ 充要条件。

最后构造 (72.18)。取任意正长度紧区间 $J_0\subset(1/2,\beta_*)$，
其中 $\beta_*$ 为第 68 章的端点阈值。此时正率区域接触左端点，只有一个正侧根。
在对应的正 $u$ 紧区间上，令
$F(u)=\phi/(\phi+I(u))$；它严格递减且导数非零。
$f_j,z_0$ 只依赖合法 $Q,j$ 和原幅度，不依赖 $\beta$。定义

```math
\chi_{Q,j}=2e^{-z_0}f_j,\qquad
L_{Q,j}=\left\lceil\log_2\frac{1/4}{\chi_{Q,j}}\right\rceil,
\qquad 1/4\le2^{L_{Q,j}}\chi_{Q,j}<1/2.
```

式 (72.23)。

使原 $M$ 精确等于 $2^{L_{Q,j}}$ 的参数区间为

```math
\mathcal J_{Q,j}=
 \left(\frac{\phi\lambda}{(L_{Q,j}+1)\log2},
       \frac{\phi\lambda}{L_{Q,j}\log2}\right].
```

式 (72.24)。

其宽度与 $\lambda^{-1}$ 同阶，且由紧内部 Stirling 展开，
$L_{Q,j}\log2=\lambda(\phi+I(j/Q^2))+O(\log Q)$，
所以该区间距 $F(j/Q^2)$ 为 $O(\log Q/Q^3)$。
给定 $J_0$ 内任意开子区间，先选内部目标参数，再将其 $F^{-1}$ 值乘 $Q^2$ 取最近整数。
误差 $O(Q^{-2})$ 趋零，故足够大的合法 $Q$ 使整个 (72.24) 落入该子区间。

逐次选原合法序列中更大的 $Q_h$，以及内含于上一步区间和某个
$\mathcal J_{Q_h,j_h}$ 内部的非空闭区间，令其长度趋零。
嵌套紧区间给一个固定 $\beta_\infty\in J_0$。
在选定规模上，原 $M=2^{L_{Q_h,j_h}}$；$q,\epsilon$ 均仍按原定义取得。
统一于此紧参数区间，

```math
m_{j_h}=(2+o(1))qf_{j_h}
 =(1+o(1))2^{L_{Q_h,j_h}}\chi_{Q_h,j_h}.
```

式 (72.25)。

继续抽取使右侧确定主值趋于 $\theta\in[1/4,1/2]$。
(72.6)、(72.8) 使两种实验的该组实际均值都趋于 $\theta$，其下取整最终为零。
因为这里只存在一个根邻域，该组是唯一的多项式过渡组。
(72.17) 遂给 (72.18)，且 Poisson 在零、一处的正质量证明非退化。
构造只选择了一次固定 $\beta$，没有让参数随规模移动，也没有声称任意预先指定 $\beta$ 都有此子序列。

所有结论均为数据概率或分布结论。未知方向仍由原共同判向事件传递，
不引入方向先验；不推出 $h_M-\mathbb E h_M$、期望熵或坏数据上的一致可积。
在第 68、71 章已证的 $Q$ 尺度结论中，可以用 (72.16) 的确定中心替换 $h_M$，
因为差为 $o_{\mathbb P}(Q)$；不能因此省去阶乘、原取整和可能的端点修正。证毕。

## 追加锚（72 章后）

## 73. 典型噪声输出的条件信息谱

**定义 73.1（逐输出的条件分布距离）。** 保持第 68、69、71 章的原实际模型，
记一个完整原始数据纤维为 $x$，完整组计数律为 $P_x$，其精确熵为 $h_x$。
令 $R$ 为同一组计数向量，$T=t_x(R)$ 为定义 54.1 的精确标量，
并观测 $Y=T+\sigma_MG$，其中 $\sigma_M>0$ 确定，$G$ 独立标准正态且不另行揭示。
沿用 $v=\ell/(2(\log2)^2)>0$，置 $\Phi_v(z)=\Phi(z/\sqrt v)$、

```math
Z_x(R)=\frac{-\log_2P_x(R)-h_x}{Q},\qquad
p_x(n\mid y)=\frac{P_x(n)\varphi_{\sigma_M}(y-t_x(n))}{f_x(y)},
```

```math
f_x(y)=\sum_nP_x(n)\varphi_{\sigma_M}(y-t_x(n)),\qquad
J_x(n,y)=-\log_2p_x(n\mid y).
```

式 (73.1)。

严格正的有限 Gaussian 混合使这些条件权重对每个实数 $y$ 都有定义。
定义两个有界距离

```math
D_M^A(x,y)=\sup_{z\in\mathbb Q}
 |P_x(Z_x\le z\mid y)-\Phi_v(z)|,
```

```math
D_M^B(x,y)=\sup_{z\in\mathbb Q}
 \left|P_x\left(\frac{J_x(R,y)-h_x}{Q}\le z\,\middle|\,y\right)
       -\Phi_v(z)\right|,
\qquad \overline D_M^a(x)=\int D_M^a(x,y)f_x(y)\,dy\quad(a=A,B).
```

式 (73.2)。

有理阈值上确界可测，并由 CDF 右连续性与正态 CDF 连续性等于实阈值上确界。
$A$ 度量原惊奇量在给定输出后的分布，$B$ 度量输出后验自身的惊奇量；二者不混同。
内层条件律和 $f_x$ 均由均匀大小 $q$ 先验定义。

**定理 73.2（空间分离与典型输出定理）。** 对每个固定合法原幅度与
$\beta\in(1/2,1)$，两种实际实验分别满足：

```math
\log^+(1/\sigma_M)=o(Q^3)
\quad\Longrightarrow\quad
\overline D_M^A(\mathscr X)\longrightarrow0,
```

```math
\log^+(1/\sigma_M)=o(Q)
\quad\Longrightarrow\quad
\overline D_M^B(\mathscr X)\longrightarrow0.
```

式 (73.3)。

两条收敛均为原始数据概率收敛，既在先验数据律下成立，也一致于所有大小 $q$ 的确定支持，
后者仍评价同一先验定义的数据函数。
对每个固定 $t>0$，相应的条件输出坏集概率满足

```math
P_{Y\mid x}\{D_M^a(x,Y)>t\}\le\overline D_M^a(x)/t.
```

式 (73.4)。

故这是典型输出的条件 CDF 结论。第二条未扩展到第一条的全部噪声范围。

**证明。** 先固定共同好数据事件，保留完整窗口、校准根及精确后验中心。
以 $\mathsf Q_x=\prod_j\operatorname{Bin}(C_j,p_j)$ 记原单个校准乘积计数律，
$L_x=dP_x/d\mathsf Q_x$，$a_x=\|L_x-1\|_2$。
第 68 章的实际比较及信息谱证明给

```math
0\le L_x\le C,\qquad a_x=O_{\mathbb P}(Q^{-5/2}),\qquad
|h_x-\widetilde h_x|\le C(Qa_x+a_x^2),\qquad
\mathbb E_{P_x}(\log L_x)^2\le Ca_x^2.
```

式 (73.5)。

这里 $\widetilde h_x$ 是乘积计数熵，以 bits 计，常数吸收单位转换。
密度仍为补集 Bernoulli 和在所需整数处的概率除以全体和在 $q$ 处的概率；
未按组重新抽取实际标签。
第 68 章还给 $p_j\in[1/4,3/4]$ 上统一的二项惊奇量方差界与乘积惊奇量的 $Q$ 尺度 CLT。
由原一、二行 PGF 得到的全部窗口行数与第 69 章矩界同样适用，
这些前提不要求实际路径行独立。

写 $h_M^{noise}=\log^+(1/\sigma_M)$，$\lambda=Q^3$，取确定半径

```math
H_M=h_M^{noise}+\log Q+1,\qquad R_M^2=\sqrt{\lambda H_M}.
```

式 (73.6)。

在第一条噪声条件下，$R_M\to\infty$、$R_M^2=o(\lambda)$，且
$R_M^2/H_M\to\infty$。
只为估计取足够大固定原行数截断 $k+l\le C_0\lambda$，其计数线索引为 $K_M$。
在该线内分为

```math
\mathcal C_M=\{j:|j\delta|\le R_M\},\qquad
\mathcal O_M=K_M\setminus\mathcal C_M,
\qquad n_M^{core}=|\mathcal C_M|\le1+2R_M/\delta=o(Q^2).
```

式 (73.7)。

截断事件的坏概率一致趋零，所有目标仍是原完整窗口。
下述行数期望先在全部原始数据上对确定计数对取得，再在共同截断事件上识别为完整得分组。

令 $m_j$ 为 (72.7) 的原 Poisson 混合平均占据数，
$v_j=C_jp_j(1-p_j)/B^2$、$V_{\mathcal O}=\sum_{\mathcal O_M}v_j$。
若两个计数均不少于对应 Poisson 均值的一半，固定截断上的率函数 Hessian 有正下界，
保留有界原取整后，Stirling 前因子与严格凸性给

```math
\frac{m_j}{B^2}\le C\delta e^{-c(j\delta)^2}.
```

式 (73.8)。

这在整个上述区域统一成立，不限于固定空间区间或固定对数半径。
其余点至少有一个 Poisson 计数低于均值的一半，故
$m_j/B^2\le Q^Ce^{-c\lambda}$，无需在零计数端点使用 Gaussian 前因子。
原实际一行比较、$p_j(1-p_j)\le1/4$ 以及 Gaussian 格点尾和给

```math
\sup_S\mathbb E_S V_{\mathcal O}
 \le Ce^{-cR_M^2}+Q^Ce^{-c\lambda}.
```

式 (73.9)。

例如尾和用
$\delta\sum_{|j\delta|>R}e^{-c(j\delta)^2}
\le e^{-cR^2/2}\delta\sum_je^{-c(j\delta)^2/2}$ 即得。
原行数依赖仍保留在实际期望中。

在同一乘积计数向量上置

```math
U_j=(R_j-C_jp_j)/B,\qquad e_j=(\mu_j-C_jp_j)/B,
\qquad \mathbb E_{\mathsf Q_x}U_j=0,\quad
\mathbb E_{\mathsf Q_x}U_j^2=v_j.
```

式 (73.10)。

精确后验中心给 $e=\mathbb E_{\mathsf Q_x}[(L_x-1)U]$，故
$\|e_{\mathcal O}\|_2\le a_x\sqrt{V_{\mathcal O}}$。
定义仅在证明中使用的核心标量

```math
T^{core}=\delta^{-1/2}
 \left\{\sum_{j\in\mathcal C_M}(U_j-e_j)^2
         -V_{\mathcal C}+\|e_{\mathcal O}\|_2^2\right\}.
```

式 (73.11)。

每个中心与方差在给定原始数据后都是确定量；
因此它只随机依赖核心的乘积后验计数。
尾部确定项完整保留，不能因其趋零就在任意小噪声比较中删去。
由原标量的精确展开直接相减，

```math
T-T^{core}=\delta^{-1/2}
 \sum_{j\in\mathcal O_M}(U_j^2-v_j-2e_jU_j),\qquad
\mathbb E_{\mathsf Q_x}|T-T^{core}|
 \le C\delta^{-1/2}V_{\mathcal O}.
```

式 (73.12)。

后一界用 $\mathbb E|U_j^2-v_j|\le2v_j$ 及
$\mathbb E|e_{\mathcal O}\cdot U_{\mathcal O}|
\le\|e_{\mathcal O}\|\sqrt{V_{\mathcal O}}$，
共同好事件上 $L_x\le C$ 已保证 $a_x$ 有界。

同方差 Gaussian 平移的 TV 距离至多
$\min(1,|t-t'|/(\sqrt{2\pi}\sigma_M))$。
把整个计数向量保留在联合律中，比较同一乘积向量的原通道与核心通道，得到

```math
\tau_M(x):=d_{TV}\bigl(\mathsf Q_x(dn)\varphi_{\sigma_M}(y-t_x(n))dy,
 \mathsf Q_x(dn)\varphi_{\sigma_M}(y-t_x^{core}(n))dy\bigr)
 \le\min\left(1,\frac{C\delta^{-1/2}V_{\mathcal O}}{\sigma_M}\right).
```

式 (73.13)。

对好事件上的右侧取实际原始数据期望，(73.9) 给上界

```math
CQ^{1/4}e^{h_M^{noise}}
 \{e^{-cR_M^2}+Q^Ce^{-c\lambda}\}\longrightarrow0.
```

式 (73.14)。

因此已在真实 $1/\sigma_M$ 精度支付尾部代价。
再对同一原通道使用一次完整后验向量比较，联合律满足

```math
\epsilon_M(x):=d_{TV}(P_x^{R,Y},\mathsf Q_x^{R,Y^{core}})
 \le a_x/2+\tau_M(x)=o_{\mathbb P}(1).
```

式 (73.15)。

坏数据事件只付其外层概率，未以 TV 传递无界矩。

以自然对数写各乘积二项惊奇量 $S_j$ 及其均值 $H_j$，置

```math
Z^{out}=\frac{\sum_{j\in\mathcal O_M}(S_j-H_j)}{Q\log2},\qquad
Z^{core}=\frac{\sum_{j\in\mathcal C_M}(S_j-H_j)}{Q\log2}.
```

式 (73.16)。

在 $\mathsf Q_x^{R,Y^{core}}$ 下，$Z^{out}$ 与 $Y^{core}$ 精确独立。
二项 varentropy 的统一界给
$\mathbb E_{\mathsf Q_x}(Z^{core})^2\le Cn_M^{core}/Q^2=o(1)$。
故乘积全惊奇量的 CLT 及阈值夹逼给

```math
\kappa_M(x):=\sup_z|\mathsf Q_x(Z^{out}\le z)-\Phi_v(z)|
 \longrightarrow0
```

式 (73.17)。

这删除的是独立和中方差可忽略的一部分，没有把增长半径代入固定半径的极限定理。
原惊奇量的精确密度恒等式为

```math
Z_x=Z^{out}+Z^{core}
 -\frac{\log L_x+(\log2)(h_x-\widetilde h_x)}{Q\log2}.
```

式 (73.18)。

用 $L_x\le C$ 直接控制非负平方，再用 (73.5)，得

```math
\mathbb E_{P_x}|Z_x-Z^{out}|^2
 \le C\{n_M^{core}/Q^2+a_x^2\}.
```

式 (73.19)。

此矩界来自密度与精确中心，未由 (73.15) 推出。

现在用一个有限核事实。若 $(X_0,Y)$ 的联合律与 $\nu\otimes\eta$ 的 TV 距离至多 $e$，
则边缘收缩与三角不等式给该联合律距 $\nu\otimes P_Y$ 至多 $2e$。
对有限输入逐原子积分绝对差，恰有

```math
\int d_{TV}(P_{X_0\mid y},\nu)P_Y(dy)\le2e.
```

式 (73.20)。

无需对输出密度设逐点下界。将 (73.15) 推前到 $(Z^{out},Y)$，
结合 (73.17) 得其条件 CDF 距离的输出平均至多 $2\epsilon_M+\kappa_M$。
再以 (73.19) 作同一实现上的小位移夹逼。对任意固定 $b>0$，

```math
\overline D_M^A(x)\le2\epsilon_M(x)+\kappa_M(x)+\omega_v(b)
 +\frac{C}{b^2}\{n_M^{core}/Q^2+a_x^2\},\qquad
\omega_v(b)=\sup_z|\Phi_v(z+b)-\Phi_v(z)|.
```

式 (73.21)。

先令规模趋无穷，再令 $b\downarrow0$，即得 (73.3) 第一条。
所用 TV 始终比较有限输入与平滑输出的联合律、或两个离散核；
没有声称离散惊奇量与连续正态在 TV 中趋近。

对第二条，第 71 章的原通道信息密度记为 $i_x(R,Y)$，以自然对数计。
实际矩界与严格正通道恒等式给

```math
I_x(R;Y)\le\tfrac12\log(1+m_{2,M}(x)/\sigma_M^2)=o_{\mathbb P}(Q),
\qquad \mathbb E_x|i_x|\le I_x+2,
```

```math
\frac{J_x(R,Y)-h_x}{Q}=Z_x-\frac{i_x(R,Y)}{Q\log2}.
```

式 (73.22)。

其中 $m_{2,M}(x)=\mathbb E_{P_x}T^2=O_{\mathbb P}(1)$；
绝对信息界来自 $\mathbb E_xe^{-i_x}=1$ 和负尾积分，不假定 $T$ 与惊奇量独立。
逐输出使用同一小位移夹逼后积分，

```math
\overline D_M^B(x)\le\overline D_M^A(x)+\omega_v(b)
 +\frac{I_x+2}{bQ\log2}.
```

式 (73.23)。

先取规模极限再取 $b\downarrow0$ 即得第二条。
第一条较宽范围只控制原惊奇量的条件律，不保证 $i_x/Q$ 可忽略，故不推出第二条。
所有输入界一致于固定支持，逐数据纤维的确定推导保留该一致性。证毕。

**定理 73.3（逐输出列表曲线与最小覆盖大小）。** 在
$\log^+(1/\sigma_M)=o(Q)$ 下，记 $C_{x,y}(K)$ 为输出后验最大的 $K$ 个原子的总质量。
对每个固定实数 $z$，取 $K_x(z)=\lfloor2^{h_x+Qz}\rfloor$，则

```math
\int|C_{x,y}(K_x(z))-\Phi_v(z)|f_x(y)\,dy\longrightarrow0
```

式 (73.24)。

对固定 $\varepsilon\in(0,1)$，令 $N_{\varepsilon,M}(x,y)$ 为覆盖输出后验质量
$1-\varepsilon$ 所需的最少原子数，$z_\varepsilon=\sqrt v\Phi^{-1}(1-\varepsilon)$。
每个固定 $e>0$ 都满足

```math
\int\mathbf1\left\{
 \left|\frac{\log_2N_{\varepsilon,M}(x,y)-h_x}{Q}-z_\varepsilon\right|>e
 \right\}f_x(y)\,dy\longrightarrow0.
```

式 (73.25)。

收敛具有定理 73.2 的两种原始数据概率意义。
此外，$D_M^A,D_M^B$、(73.24) 的被积绝对差及 (73.25) 的指示函数，
在各自噪声范围内都趋零于实际确定支持的联合数据／输出概率，且一致于支持。
该联合输出由真实支持的计数生成，结论所评价的条件权重仍为原均匀先验的权重。

**证明。** 按输出后验原子质量降序排列，平局按得分排序后的计数元组字典序决定，
得到可测且达到最优值的列表。原始数据字母表在每个规模有限，
各联合原子权重连续依赖 $y$，故有限比较与确定平局规则给 Borel 选择器。
累计质量首次达到 $1-\varepsilon$ 的整数同样可测且有限。

任意有限质量函数 $p$ 的最大 $K$ 原子质量与惊奇量 CDF $F^p$ 满足

```math
F^p(\log_2K-b)\le C^p(K)
 \le F^p(\log_2K+b)+2^{-b}\qquad(K\ge1,b>0).
```

式 (73.26)。

这是第 71 章已证的有限计数界，现在逐输出使用，随后才积分。
$h_x/Q^5\to\mathscr H>0$ 保证好数据上 $K_x(z)\ge1$，
$\log_2K_x(z)=h_x+Qz+o(1)$。取 $b=\sqrt Q$，正态密度有界给

```math
|C_{x,y}(K_x(z))-\Phi_v(z)|
 \le D_M^B(x,y)+CQ^{-1/2}+o(Q^{-1})+2^{-\sqrt Q}.
```

式 (73.27)。

好事件外左侧有界，故 (73.24) 成立。
对逆问题，$\Phi_v(z_\varepsilon-e/2)$ 与 $\Phi_v(z_\varepsilon+e/2)$
分别严格小于、大于 $1-\varepsilon$，差距有固定正下界。
在 $D_M^B$ 小于该差距一半时，(73.27) 使最小覆盖数夹在对应两个预算之间。
单调性、可达性和对数取整误差给 (73.25)，坏输出概率由 (73.4) 控制。
此处预算可以在看到 $y$ 后选择；第 71 章的共同输出预算是在看到 $y$ 前选择，两者并非同一定义。

最后证明实际输出的范围。保持奇偶类的站点置换 $\pi$ 将支持 $S$ 映到 $\pi S$，
共轭原核并保持原始观测似然。按得分排序后，组大小、精确后验、校准、中心、熵及
$t_x(n)$ 都在对应下相同，而且 $R(\pi S,\pi x)=R(S,x)$。
使用同一个 $G$ 则输出 $Y$ 相同。因此对任意有界置换不变函数 $g_M(x,y)$，

```math
\mathbb E_{S,G}g_M(\mathscr X,t_{\mathscr X}(R(S,\mathscr X))+\sigma_MG)
 =\mathbb E_{\rm prior}g_M(\mathscr X,Y),
```

式 (73.28)。

右侧先验混合与任意固定支持左侧相等，来自群对大小 $q$ 支持的传递性。
将已证有界距离／指示函数先在先验下平均，再用此恒等式，得到实际确定支持的联合概率结论。
这不宣称给定 $x$ 的先验混合密度 $f_x$ 等于固定真实支持下的单个 Gaussian 输出密度，
也不把先验后验解释成点质量支持先验。
这里用于实际成功率的规范策略取第 71 章 (71.18) 构造的随机对称化最优策略核。
其辅助均匀群元独立于数据、标签和测量噪声，策略核等变，故对该辅助随机性平均的
Bayes 风险有相应固定支持解释。字典序选择器只用于取得可测最优值，本身无需等变；
标量最优质量 $C_{x,y}(K)$ 与最小覆盖数 $N_{\varepsilon,M}(x,y)$ 不依赖破平局方式。
不受限规则可以写死支持，不能借本定理宣称所有此类规则的固定支持不可能性。
未知方向只用原共同判向事件及同一个 $G$ 传递所有有界结论，不引入方向先验。

第 72 章给 $h_x-\widetilde d_M=o_{\mathbb P}(Q)$，
故本章所有 $Q$ 尺度中心可改为 (72.16) 的同一个确定中心。
这是两个已经量化的误差的组合，不将 $Q^5$ 主项单独当作该中心。证毕。

**注记 73.4（小信息与条件极限的区别）。** 独立 Bernoulli$(p)$ 源在固定
$p\ne1/2$ 时，其标准化惊奇量有普通 CLT。
若只揭示该中心化惊奇量是否为正的一位，信息代价至多 $\log2$，
但在阈值零，其给定输出的 CDF 为零或一，与正态 CDF 的差均为 $1/2$。
因此原 CLT 加小平均信息可以支持第 71 章的联合边缘结论，
却不能独自证明本章的典型输出条件 CDF 结论；(73.15) 的联合比较补上了这一步。
这个例子检验的是通用推理，不反驳本章的原 Gaussian 通道。

本章给充分噪声条件，未证明 $Q^3$ 或 $Q$ 是必要／锐利阈值。
当 $\log(1/\sigma_M)$ 与 $Q^3$ 同阶时，当前核心可占 $Q^2$ 组，
可忽略方差删除法失去其前提；方法在此停止不等于命题反例。
没有每个输出保证、变化误差水平、期望对数覆盖展开、效率或零噪声结论。

## 追加锚（73 章后）

## 74. 熵集中例外集的零测度、稠密类别与局部维数

**定义 74.1（固定参数的集中例外）。** 保持第 72 章的实际均值中心
$d_M^{\mathcal E}$，其中 $\mathcal E$ 为原平稳对或连续路径实验。
每个 $\beta\in(1/2,1)$ 都使用原固定幅度、原合法规模、全部取整、补偿和完整窗口。
定义

$$
E_{\mathcal E}=\{\beta:h_M(\mathscr X)-d_M^{\mathcal E}
\text{ 不依数据概率收敛于零}\}.
\tag{74.1}
$$

概率可以取任意大小 $q$ 的确定支持的实际抽样律；被评价的后验熵仍由均匀支持先验定义。
原支持置换使这个熵函数的分布精确地不依赖支持，所以也等价于先验数据律与支持上一致的概率表述。
本章的 Lebesgue 测度、类别与 Hausdorff 维数均取在参数区间上，不给 $\beta$ 新增先验。

记原 Liouville 斜率为 $\vartheta$，有限逼近为 $P/Q$。
合法序列满足

$$
Q_{n+1}=10^{Q_n^5},\qquad \lambda=Q^3,\qquad
L_0(\beta)=\left\lfloor\frac{\phi Q^3}{\beta\log2}\right\rfloor,
\quad M=2^{L_0(\beta)},\quad q=\lfloor Me^{-z_0}\rfloor.
\tag{74.2}
$$

这里 $\phi,z_0,k_0,l_0$ 均为原定义。对固定紧区间
$J\Subset(1/2,1)$，取一个统一足够大的证明截断 $k+l\le C_0\lambda$。
其窗口计数线为 $(k_j,l_j)=(k_0+jQ,l_0+jP)$，索引集 $K_Q$ 与 $\beta$ 无关，且 $|K_Q|=O_J(Q^2)$。
截断不改变观测或完整得分组。

**引理 74.2（原 floor 区间与两种实际实验的共同判据）。** 令
$f_j,f_j^0,m_j=qf_j+(M-q)f_j^0$ 精确取 (72.7)，并设

$$
\chi_{Q,j}=2e^{-z_0}f_j.
\tag{74.3}
$$

$\chi_{Q,j}$ 只依赖原幅度、$Q,j$，不依赖 $\beta$。
统一于每个固定 $J$ 与全部 $j\in K_Q$，有

$$
m_j(\beta)=2^{L_0(\beta)}\chi_{Q,j}(1+o_J(1)).
\tag{74.4}
$$

若相应实际完整得分组均值 $\bar c_j^{\mathcal E}$ 位于 $[Q^{-8},Q^8]$，
则 $\bar c_j^{\mathcal E}/m_j\to1$ 亦统一成立。
两种例外集相同，记为 $E$，且局部有精确的 Borel 表述

$$
E\cap J=J\cap\bigcup_{v=2}^{\infty}\limsup_{n\to\infty}
\bigcup_{j\in K_{Q_n}}
\{\beta:1/v\le m_{Q_n,j}(\beta)\le v\}.
\tag{74.5}
$$

证明。在紧参数区间上，原规模满足
$\log q=\phi(1-\beta)Q^3/\beta+O(1)$，故 $q$ 统一指数增长。
原一、二行 PGF 比较、尾界与计数线隔离中的常数可统一选择：
$\log M/Q^3$ 有正的有限上下界，幅度固定，而 $C_0$ 固定后所有标记提取半径有统一界。
因此 (72.5)、(72.6)、(72.8) 在这里分别给

$$
\rho_M\le C_JM^{-10},\qquad
|\bar c_j^{\mathcal E}-m_j|
\le\varepsilon_Mm_j+\rho_M,\qquad
\varepsilon_M\le C_J\lambda^3/M.
\tag{74.6}
$$

该式包括完整组的远处同分计数，未假定得分映射在截断外单射。

截断线上 $f_j/f_j^0=e^{W_j}$，而
$W_j-z_0=O_J(\epsilon\lambda+\lambda(\vartheta-P/Q))=o_J(1)$。
又 $q/(Me^{-z_0})=1+O_J(q^{-1})$，所以

$$
\frac{m_j}{Me^{-z_0}f_j}
=\frac{q}{Me^{-z_0}}+(1-q/M)e^{z_0-W_j}=2+o_J(1).
\tag{74.7}
$$

这是相对误差比较，即使 $f_j$ 很小仍成立；补偿与 $q$ 的取整未删去。
由 (74.6) 得所述多项式区间上的实际均值比较。

定理 72.3 给出的充要条件是：存在原合法规模子序列及移动组，使实际均值趋于正有限值。
若平稳对中出现这样的组，(74.6) 使 $m_j$ 与路径中的实际均值有同一极限；反向论证相同。
因此 $E_{\rm pair}=E_{\rm path}$。
这个共同判据与紧正区间的子序列紧性恰给 (74.5)。
不要求两种精确中心相差 $o(1)$：接近正整数的两种均值仍可有不同下取整。

对固定 $Q$，全部实际参数及抽样律在原区间

$$
\mathcal J_{Q,L}
=\left(\frac{\phi Q^3}{(L+1)\log2},
        \frac{\phi Q^3}{L\log2}\right],\qquad L\ge1,
\tag{74.8}
$$

上保持不变，$q$ 与补偿也随之固定。左端点的 floor 为 $L+1$，右端点为 $L$。
在与 $J$ 相交的区间上，$L\asymp_JQ^3$，且
$|\mathcal J_{Q,L}|\asymp_JQ^{-3}$。
故 (74.5) 的每个有限层事件是有限个半开区间的并。
紧区间的可数穷尽证明 $E$ 是 Borel 集。证毕。

**定理 74.3（参数几乎处处集中与维数上界）。** 例外集 $E$ 的 Lebesgue 测度为零，
且 $\dim_HE\le2/3$。
更强地，对几乎处处的固定 $\beta$，两种实际实验的 (72.3) 过渡组集合最终都为空，因此

$$
\sup_{S:|S|=q}\Pr_S^{\mathcal E}
\{|h_M-d_M^{\mathcal E}|>\varepsilon\}\longrightarrow0
\quad(\varepsilon>0).
\tag{74.9}
$$

证明。若一个实际均值在 $[Q^{-8},Q^8]$ 中，(74.4)、(74.6) 迫使

$$
-8\log Q-C_J\le L_0(\beta)\log2+\log\chi_{Q,j}
\le8\log Q+C_J.
\tag{74.10}
$$

对每个 $j$ 只有 $O_J(\log Q)$ 个连续整数 $L$ 可以满足此式。
共有 $O_J(Q^2)$ 个索引，每个原 floor 区间宽 $O_J(Q^{-3})$，
所以两种实验的过渡事件都有一个参数空间中的共同覆盖 $A_Q(J)$，满足

$$
|A_Q(J)|\le C_J\frac{\log Q}{Q}.
\tag{74.11}
$$

由原序列的增长率，$\sum_n\log Q_n/Q_n<\infty$。
在参数 Lebesgue 测度上用第一 Borel–Cantelli 引理，得到过渡事件几乎处处仅发生有限次。
(72.4) 遂给 (74.9)，再可数穷尽紧区间。
这里没有对分段常值均值求导，也没有要求不同规模的数据独立。

为估计维数，固定 (74.5) 中的整数 $v$。
把 (74.10) 的两端换成依赖 $v$ 的常数后，每个 $j$ 仅需 $O_{J,v}(1)$ 个 floor 区间。
其第 $n$ 层由 $O_{J,v}(Q_n^2)$ 个长度 $O_J(Q_n^{-3})$ 的区间覆盖。
对每个 $s>2/3$，

$$
\sum_nQ_n^{2-3s}<\infty.
\tag{74.12}
$$

从任意足够晚的层开始覆盖 limsup，其最大直径及总 $s$ 内容均趋零。
因此该 limsup 的 $s$ 维 Hausdorff 测度为零；对 $v$ 与紧区间取可数并即得上界。证毕。

**引理 74.4（整个参数区间的实际正根网格）。** 令 $I$ 为第 68 章的原行率函数，
$c(\beta)=\phi(1-\beta)/\beta$，并在正 $u$ 轴上设

$$
F(u)=\frac{\phi}{\phi+I(u)},\qquad
L_{Q,j}=\left\lceil\log_2\frac{1/4}{\chi_{Q,j}}\right\rceil.
\tag{74.13}
$$

对每个紧参数区间，可选择覆盖其正根的 $j$，使原区间
$\mathcal J_{Q,j}:=\mathcal J_{Q,L_{Q,j}}$ 满足

$$
\frac14\le2^{L_{Q,j}}\chi_{Q,j}<\frac12,\qquad
\bar c_j^{\mathcal E}
=2^{L_{Q,j}}\chi_{Q,j}(1+o_J(1))
\quad\text{在整个 }\mathcal J_{Q,j}\text{ 上}.
\tag{74.14}
$$

设其中点为 $x_{Q,j}$，则

$$
x_{Q,j}=F(j/Q^2)+O_J(\log Q/Q^3),\qquad
|\mathcal J_{Q,j}|\asymp_JQ^{-3},\qquad
|x_{Q,j+1}-x_{Q,j}|\asymp_JQ^{-2}.
\tag{74.15}
$$

在稍大的紧邻域中取网格后，对内部任意区间 $A$，中点数至多
$C_J(1+|A|Q^2)$；当 $|A|Q^2$ 足够大时，完全包含于 $A$ 的目标区间数至少 $c_J|A|Q^2$。

证明。每个 $0<c<\phi$ 都有唯一正根；在紧参数区间的逆像上，
$F$ 光滑、严格递减，且导数绝对值有正的有限上下界。
该性质在跨越 $\beta_*$ 时不变，因这里只用正根。
取整定义直接给 (74.14) 的第一个不等式，(74.4)、(74.6) 给第二式。
紧内部 Stirling 展开给

$$
L_{Q,j}\log2=z_0-\log f_j+O(1)
=Q^3\{\phi+I(j/Q^2)\}+O_J(\log Q).
\tag{74.16}
$$

所以中点位置满足 (74.15)。相邻 $F$ 值之差为 $Q^{-2}$ 阶，
而两点位置误差之和为 $o(Q^{-2})$，故实际中点随 $j$ 递减，间隔上下界均成立。
由最大间隔求下计数界、最小间隔求上计数界；完全包含的区间只需删去端点旁固定多个。
这不借助等分布假设。
正根在 $0<c\le\phi$ 的范围有界，因此一个固定截断可包含全部正根及余量。
每层保留落在 $(1/2,1)$ 内的相应区间，就得到全区间上的同一列有限网格。证毕。

**定理 74.5（零测度例外集的稠密类别与局部维数）。** 对每个非空开区间
$J_0\subset(1/2,1)$，

$$
\dim_H(E\cap J_0)=\frac23.
\tag{74.17}
$$

此外，$E$ 包含全参数区间中的稠密 $G_\delta$ 集，所以是余贫集；
其补集同时具有全 Lebesgue 测度与第一纲类别。

证明。令 $U_n$ 为第 $Q_n$ 层所有正根目标区间的开放中三分之一的并。
每个非空开区间在所有充分大的层都包含一个完整目标区间，故

$$
G=\bigcap_{N\ge1}\bigcup_{n\ge N}U_n
\tag{74.18}
$$

是稠密 $G_\delta$。
若 $\beta\in G$，固定其紧邻域，在无穷多次命中中继续抽取，
使 (74.14) 的两种实际均值同时趋于某个 $\theta\in[1/4,1/2]$。
引理 74.2 的实际判据给 $G\subset E$。
即使负根组也留下正有限均值，定理 72.3 的两个 Poisson 极限相互独立；
其熵函数的非退化性不能相互抵消。
因此这一类别结论覆盖 $\beta_*$ 两侧，不限于单根区间。

下面给出包括所有中间尺度的维数下界。
取非退化闭区间 $K\subset J_0$，在稍大紧邻域中固定引理 74.4 的常数。
选择足够小的 $\kappa_0>0$，使以目标中点为中心、长度

$$
\ell_n=\kappa_0Q_n^{-3}
\tag{74.19}
$$

的闭区间都严格包含在各自的开放中三分之一中。
从充分晚的一层开始，每层保留完全内含于上一层父区间的所有这些闭区间。
中心间距与 $\Delta_n=Q_n^{-2}$ 同阶，而每个父区间的子区间数满足

$$
c\ell_{n-1}Q_n^2\le N_n(\text{父区间})
\le C\ell_{n-1}Q_n^2.
\tag{74.20}
$$

原超稀疏规模保证 $\ell_{n-1}Q_n^2\to\infty$，吸收固定端点损失。
首层以 $|K|$ 替换 $\ell_{n-1}$。嵌套交集 $\mathcal C$ 是非空紧集，且
$\mathcal C\subset G\cap J_0$。

把每个父区间的质量等分给子区间，得到支撑于 $\mathcal C$ 的概率测度 $\nu$。
记最大层质量为 $M_n$，$t_n=\log Q_n$，则

$$
\log M_n\le-2t_n+\sum_{i<n}t_i+O(n)+O_K(1),\qquad
\frac{\sum_{i<n}t_i+n}{t_n}\longrightarrow0.
\tag{74.21}
$$

故对每个 $0<s<2/3$，$M_n\le C_{K,s}\ell_n^s$。
仅这个柱集质量估计还不够；需控制任意短区间 $A$。
设其长度为 $r$，选择 $\ell_n\le r<\ell_{n-1}$。
若 $r<\Delta_n$，最小间距使 $A$ 只交固定多个第 $n$ 层区间，故
$\nu(A)\le CM_n\le C_{K,s}r^s$。
若 $r\ge\Delta_n$，因上一层中心间距远大于 $\ell_{n-1}$，
$A$ 至多交两个父区间，每个内至多交 $CrQ_n^2$ 个子区间。
因此

$$
\nu(A)\le C\frac{rM_{n-1}}{\ell_{n-1}}
\le C_{K,s}r\ell_{n-1}^{s-1}\le C_{K,s}r^s.
\tag{74.22}
$$

最后一步用 $s<1$ 与 $r\le\ell_{n-1}$。
这个质量界覆盖子区间宽度与中心间距之间的所有尺度。
任意充分细区间覆盖满足 $1\le\sum_i\nu(A_i)\le C_{K,s}\sum_i|A_i|^s$，
故 $\dim_H\mathcal C\ge s$。令 $s\uparrow2/3$，结合定理 74.3 即得 (74.17)。
由于 $E\supset G$，其补集包含于贫集 $G^c$，类别结论也成立。证毕。

**命题 74.6（临界左端点不产生正有限均值障碍）。** 在指定参数
$\beta=\beta_*$，负侧端点组不能沿子序列具有正有限实际均值。
该指定参数是否属于 $E$，仍由其正根算术判据决定，本章不作判定。

证明。设负端点为 $u_-=-b/\vartheta$，并置
$x_-=a-b/\vartheta>0$、$d_0=k_0-a\lambda\in(-1,0]$。
若端点组有正有限均值，则 (72.12) 的单侧率带迫使其未缩放第二计数
$L=l_j$ 满足 $0\le L=O(\log Q)$。
原计数线及 $\lambda|\vartheta-P/Q|=o(1)$ 给

$$
k_j=x_-\lambda+L/\vartheta+(1+1/\vartheta)d_0+o(1).
\tag{74.23}
$$

仅对正的一侧用 Stirling，另一侧保留精确 $L!$。
由 $\log q=I(u_-)\lambda+O(1)$，主率取消，得到

$$
\log m_j=(L-\tfrac12)\log\lambda-\log(L!)+O(L+1).
\tag{74.24}
$$

正计数展开余项为 $O((L+1)^2/\lambda)$；原 floor、补偿与背景因子已包含在误差内。
$L=0$ 时此式趋负无穷；$1\le L=O(\log Q)$ 时，
$\log(L!)\le L\log L$ 与 $\log L=o(\log\lambda)$ 使它统一趋正无穷。
两者均与正有限均值矛盾。(74.6) 移回实际完整组，证毕。

这里的“几乎处处”先固定参数，再取实际数据概率极限；
不意味着对全部参数一致的收敛速度，也不意味着把参数随机化后的新实验。
例外集的相同性不识别两种实验的精确 floor 中心。
所有统计结论仍经原共同方向相等事件移到未知方向版本。
不推出期望熵、$h_M-\mathbb Eh_M$、无界矩、有限精度恢复或计算效率结论。
Borel–Cantelli、Baire、质量分布与维数理论是经典工具；
本章新增推导在于把它们接到原实际模型的完整均值、原 floor 网格和共同例外判据上。

## 追加锚（74 章后）

## 75. 低噪声的实际信息增益与平移后的条件信息谱

**定义 75.1（噪声对数与精确中心）。** 保持第 73 章的两种实际实验、原固定幅度、
固定 $\beta\in(1/2,1)$、完整窗口和均匀大小 $q$ 支持先验。
给定完整原始数据 $x$，以 $P_x$ 表示原完整组计数律，以 $h_x$ 表示其精确熵，单位为 bits。
本章仍只观测定义 54.1 的精确标量加独立 Gaussian 噪声：

$$
T=t_x(R)=\frac{\sum_j((R_j-\mu_j)/B)^2-V}{\sqrt\delta},\qquad
Y=T+\sigma_MG,
\quad \mu_j=\mathbb E_{P_x}R_j,
\quad V=B^{-2}\sum_jC_jp_j(1-p_j).
\tag{75.1}
$$

这里 $B^2=q/Q^{5/2}$、$\delta=Q^{-1/2}$、$\lambda=Q^3$，
$p_j$ 为原单个校准乘积律的参数；$V$ 不替换成实际平方和的后验期望。
$G$ 独立于原数据与全部标签，且不单独揭示。
取确定正噪声满足

$$
L_M:=\ln(1/\sigma_M)\longrightarrow\infty,
\qquad L_M=o(Q^3),
\qquad c_M(x)=h_x-\frac{L_M}{\ln2}.
\tag{75.2}
$$

以 $\ln$ 表示自然对数。沿用 (73.1) 的严格正密度 $f_x$、输出后验 $p_x(n\mid y)$、
输出后惊奇量 $J_x(n,y)$，并定义自然单位的信息密度

$$
i_x(n,y)=\ln\frac{\varphi_{\sigma_M}(y-t_x(n))}{f_x(y)},\qquad
b_{M,\varepsilon}(x)=P_x^{R,Y}\{|i_x(R,Y)-L_M|>\varepsilon Q\}.
\tag{75.3}
$$

$v>0$ 与 $\Phi_v(z)=\Phi(z/\sqrt v)$ 仍取第 73 章的完整窗口信息谱方差。
噪声对数 $L_M$ 与决定 $v$ 的正率区间长度是不同量。

**定理 75.2（实际信息密度的低噪声增益）。** 在 (75.2) 的整个范围内，
对每个 $\varepsilon,t>0$，两种实际实验分别满足

$$
\sup_{S:|S|=q}\Pr_S^{\mathscr X}
 \{b_{M,\varepsilon}(\mathscr X)>t\}\longrightarrow0.
\tag{75.4}
$$

内层概率使用给定 $x$ 的原先验纤维和测量噪声，外层可以是任意确定支持的实际数据律。
若 $b_{M,\varepsilon}(x,y)$ 是同一事件给定 $Y=y$ 后的概率，则

$$
\int b_{M,\varepsilon}(x,y)f_x(y)\,dy=b_{M,\varepsilon}(x),\qquad
P_{Y\mid x}\{b_{M,\varepsilon}(x,Y)>t\}
 \le b_{M,\varepsilon}(x)/t.
\tag{75.5}
$$

所以信息密度误差也在典型输出的条件概率意义下为 $o(Q)$。
这不声称信息密度期望的展开。

证明。第 73 章的实际比较给单个完整乘积计数律
$\mathsf Q_x=\prod_j\operatorname{Bin}(C_j,p_j)$ 及

$$
0\le L_x:=\frac{dP_x}{d\mathsf Q_x}\le C,
\quad a_x:=\|L_x-1\|_2=O_{\mathbb P}(Q^{-5/2}),
\quad V=O_{\mathbb P}(1),
\quad m_{2,M}(x):=\mathbb E_{P_x}T^2=O_{\mathbb P}(1).
\tag{75.6}
$$

$L_x$ 是选定计数律的密度，不是 (75.2) 的噪声对数。
最后的实际矩界由第 69、71 章对精确密度和中心的直接计算得到，未由 TV 或弱收敛传递。
以下每个好数据事件的概率都一致于确定支持；原一、二行比较分别适用于平稳对与连续路径。

第一步是在真实噪声精度建立共同计数向量的比较。
取第 73 章的确定核心

$$
R_M^2=\sqrt{\lambda(L_M+\ln Q+1)},\qquad
\mathcal C_M=\{j\in K_M:|j\delta|\le R_M\},
\quad \mathcal O_M=K_M\setminus\mathcal C_M.
\tag{75.7}
$$

$K_M$ 是同一固定原行截断内的计数线；它只用于估计，目标仍为全部完整得分组。
$R_M^2=o(\lambda)$ 且 $|\mathcal C_M|=o(Q^2)$。
这里需要新增一个在整个移动核心上的下占据界。
设 $c_q=\phi(1-\beta)/\beta>0$，原规模给 $\ln q=c_q\lambda+O(1)$。
核心内 $j/Q^2=o(1)$，故两个 Poisson 计数都最终不少于对应均值的一半。
原率函数在其最小点邻域的 Hessian 有有限上界，线性项为零；保留有界取整，Stirling 给

$$
c\lambda^{-1}e^{-C(j\delta)^2}
 \le f_j\le C\lambda^{-1}e^{-c(j\delta)^2},\qquad
\min_{j\in\mathcal C_M}m_j
 \ge c(q/\lambda)e^{-CR_M^2}
 =\exp\{c_q\lambda-O(R_M^2+\ln Q)\}.
\tag{75.8}
$$

$m_j$ 精确取 (72.7) 的混合占据均值，其信号／背景比例在核心统一有正的有限上下界。
这是由原率函数取得的移动半径估计，不把固定对数核心的极限外推到此处。
原一、二行 PGF 比较给

$$
\Pr_S\{|C_j/m_j-1|>1/2\}
 \le C(m_j^{-1}+e_{\rm row}).
\tag{75.9}
$$

对至多 $CQ^2$ 组取并，坏概率由
$CQ^2\{\exp[-c_q\lambda+O(R_M^2+\ln Q)]+e_{\rm row}\}$ 控制并趋零。
交原校准好事件后，$p_j\in[1/4,3/4]$，未归一化二项方差与中心小核心分别满足

$$
d_{\min}:=\min_{j\in\mathcal C_M}C_jp_j(1-p_j)
 \ge e^{c_q\lambda/2},
\qquad
c\delta\le v_j:=\frac{C_jp_j(1-p_j)}{B^2}\le C\delta
\quad(|j\delta|\le1).
\tag{75.10}
$$

后一个核心有 $n_0\asymp\delta^{-1}$ 组。小 $v_j$ 与指数大的原二项方差不能混同。

使用第 67 章的有限单调耦合估计：对 $d=np(1-p)\ge1$，
标准化二项变量 $X$ 与标准正态 $Z$ 可耦合使

$$
\mathbb E(X-Z)^2\le Cd^{-1/6}.
\tag{75.11}
$$

该粗速率也可由原方差型局部 Bernoulli 界直接核对：局部质量误差 $C/d$ 在
$[-A,A]$ 内求和，加方差尾界，给 Kolmogorov 误差
$C(A/\sqrt d+A^{-2}+d^{-1/2})$；取 $A=d^{1/6}$ 得 $\eta\le Cd^{-1/3}$。
二项标准化四阶矩至多 $4$。
单调耦合的层饼恒等式给
$\mathbb E|X-Z|=\int|F_X-\Phi|\le2T\eta+CT^{-3}$；
取 $T=\eta^{-1/4}$，再用 $L^1$ 与 $L^4$ 插值得 (75.11)。
这没有离散变量与连续变量的 TV 收敛主张。

在给定同一个好数据纤维后，核心各组独立进行这些耦合，保持外部乘积计数独立。
置 $U_j=(R_j-C_jp_j)/B$、$e_j=(\mu_j-C_jp_j)/B$、
$G_j=\sqrt{v_j}Z_j$。完整二项侧计数向量仍记为 $R$，并始终附在通道上。
精确中心给 $\|e\|\le a_x\sqrt V$。
定义 Gaussian 参考标量

$$
T^{\rm G}=\delta^{-1/2}
 \left\{\sum_{j\in\mathcal C_M}(G_j-e_j)^2
             -V_{\mathcal C}+\|e_{\mathcal O}\|^2\right\}.
\tag{75.12}
$$

其全部非中心项和尾部确定截距均保留，与 (73.11) 完全同形。
平方范数差的 Cauchy–Schwarz 界及 (75.11) 给

$$
\mathbb E\|U_{\mathcal C}-G_{\mathcal C}\|^2
 \le Cd_{\min}^{-1/6}V_{\mathcal C},\qquad
\mathbb E|T^{core}-T^{\rm G}|
 \le C\delta^{-1/2}(1+a_x)Vd_{\min}^{-1/12}
 \le CQ^{1/4}Ve^{-c_q\lambda/24}.
\tag{75.13}
$$

Gaussian 平移核的 TV 距离至多标量位移除以 $\sqrt{2\pi}\sigma_M$。
在 $V\le Q$ 的高概率事件上，保留 $R$ 的核心通道比较误差至多

$$
\upsilon_M(x)\le CQ^{5/4}\exp\{L_M-c_q\lambda/24\}\longrightarrow0.
\tag{75.14}
$$

这里正是 $L_M=o(\lambda)$ 支付了最终噪声精度。
第 73 章已用 (73.12)–(73.14) 在相同精度支付了尾部误差 $\tau_M=o_{\mathbb P}(1)$。
因此，对保留完整二项计数和输出 $T^{\rm G}+\sigma_MG_0$ 的参考联合律 $\mathsf R_x$，

$$
d_{TV}(P_x^{R,Y},\mathsf R_x^{R,Y})
 \le a_x/2+\tau_M(x)+\upsilon_M(x)=:\Delta_M(x)=o_{\mathbb P}(1).
\tag{75.15}
$$

$G_0$ 是额外独立的测量正态。第一项由同一完整后验向量的核收缩得到，
不除以 $\sigma_M$；只有已定量控制的标量位移付出该因子。
参考输出可以与其所附二项计数相关，这不改变其 Gaussian 核心的边缘分布。

第二步只对参考输出建立有界密度。
除去一个确定平移，(75.12) 为
$\sum_{\mathcal C_M}w_j(Z_j-c_j)^2$，其中
$w_j=v_j/\sqrt\delta>0$、$c_j=e_j/\sqrt{v_j}$。
非中心正态平方的特征函数满足

$$
\left|\mathbb E e^{itw(Z-c)^2}\right|
 =(1+4t^2w^2)^{-1/4}
 \exp\left\{-\frac{2t^2w^2c^2}{1+4t^2w^2}\right\}
 \le(1+4t^2w^2)^{-1/4}.
\tag{75.16}
$$

仅取 (75.10) 的 $n_0\asymp\delta^{-1}$ 个中心组，其 $w_j\asymp\sqrt\delta$，
便有 $|\psi_x(t)|\le(1+c\delta t^2)^{-n_0/4}$。
在 $|t|\le\delta^{-1/2}$ 上以 $e^{-c't^2}$ 控制；其余部分换元
$u=\sqrt\delta|t|$，再以
$C\delta^{-1/2}(1+c)^{-n_0/8}\int_1^\infty(1+cu^2)^{-1}du$ 控制。
故 $\|\psi_x\|_1\le C$，Fourier 反演给参考标量的密度上界 $C$。
独立测量噪声的卷积保持该上界，记参考输出密度为 $g_x$。
这也是经典 Gaussian 二次型密度定理的直接适用步骤；任意精确非中心项均允许。

(75.15) 的边缘收缩给 $d_{TV}(f_xdy,g_xdy)\le\Delta_M(x)$。
对任意固定 $b>0$，实际高密度集合 $H_b(x)=\{y:f_x(y)>e^{bQ}\}$ 的长度至多 $e^{-bQ}$，所以

$$
P_{Y\mid x}\{f_x(Y)>e^{bQ}\}\le\Delta_M(x)+Ce^{-bQ}.
\tag{75.17}
$$

集合由实际密度定义也合法，因为 TV 控制每个可测集合。
没有由此推出实际密度的逐点上界或密度差的上确界估计。
另一方面，在 $|y|\le Q^d$ 上对 $\{f_x<e^{-bQ}\}$ 直接积分，
再用实际二阶矩控制补集。对任意固定 $d>0$，由
$\mathbb E_xY^2=m_{2,M}(x)+\sigma_M^2$ 得

$$
P_{Y\mid x}\{|\ln f_x(Y)|>bQ\}
 \le\Delta_M(x)+(C+2Q^d)e^{-bQ}
       +\frac{m_{2,M}(x)+1}{Q^{2d}}=o_{\mathbb P}(1).
\tag{75.18}
$$

$\sigma_M\le1$ 最终成立。这里截断的是概率估计，实际观测没有被裁剪。

最后，原通道在同一实际纤维实现上的精确恒等式为

$$
i_x(R,Y)=L_M-\tfrac12\ln(2\pi)-\tfrac12G^2-\ln f_x(Y).
\tag{75.19}
$$

测量 $G$ 在给定原始数据后仍为标准正态。结合 (75.18) 与其二阶矩，
对足够大规模得到

$$
b_{M,\varepsilon}(x)
 \le\Delta_M(x)+(C+2Q^d)e^{-\varepsilon Q/3}
       +\frac{m_{2,M}(x)+1}{Q^{2d}}+\frac{3}{2\varepsilon Q}.
\tag{75.20}
$$

好事件外只计其概率，故 (75.4) 成立。(75.5) 是条件概率的积分与 Markov 界。
给定输出后的残差 $(y-t_x(R))/\sigma_M$ 未被假定为条件标准正态。证毕。

**定理 75.3（平移后的典型输出信息谱）。** 定义

$$
D_M^{\rm shift}(x,y)=\sup_{z\in\mathbb Q}
 \left|P_x\left(\frac{J_x(R,y)-c_M(x)}Q\le z\,\middle|\,y\right)
             -\Phi_v(z)\right|.
\tag{75.21}
$$

在 (75.2) 下，$\int D_M^{\rm shift}(x,y)f_x(y)dy\to0$，
收敛为原数据概率收敛并一致于确定支持；因而也成立于典型先验预测输出。

证明。令 $Z_x=(-\log_2P_x(R)-h_x)/Q$。有限 Bayes 恒等式给

$$
\frac{J_x(R,Y)-c_M(x)}Q
 =Z_x-\frac{i_x(R,Y)-L_M}{Q\ln2}.
\tag{75.22}
$$

对每个固定 $b>0$，在给定输出的同一实现上夹逼阈值，然后积分，得

$$
\int D_M^{\rm shift}(x,y)f_x(y)dy
 \le\overline D_M^A(x)+\omega_v(b)+b_{M,b\ln2}(x).
\tag{75.23}
$$

第 73 章第一条条件 CDF 定理适用于整个 $L_M=o(Q^3)$ 范围，
故首项趋零；定理 75.2 给末项趋零。
先取规模极限再令 $b\downarrow0$ 即得结论。
这里使用原惊奇量给定输出的分布结论，不能只用其边缘 CLT。证毕。

**定理 75.4（可达列表曲线与临界噪声收益）。** 记 $C_{x,y}(K)$ 为输出后验最大
$K$ 个原子的总质量，$N_{\varepsilon,M}(x,y)$ 为覆盖质量 $1-\varepsilon$ 的最小原子数。
对固定 $z\in\mathbb R$、$\varepsilon\in(0,1)$ 和 $e>0$，有

$$
\int\left|C_{x,y}\!\left(\left\lfloor2^{c_M(x)+Qz}\right\rfloor\right)
                -\Phi_v(z)\right|f_x(y)dy\longrightarrow0,
\tag{75.24}
$$

$$
\int\mathbf1\left\{
 \left|\frac{\log_2N_{\varepsilon,M}(x,y)-c_M(x)}Q
          -\sqrt v\Phi^{-1}(1-\varepsilon)\right|>e\right\}f_x(y)dy
 \longrightarrow0.
\tag{75.25}
$$

两式具有定理 75.3 的原数据概率量词。按质量降序、以固定计数元组顺序打破平局，
给出可测且达到这些后验最优值的列表。
特别地，若 $L_M=a_{noise}Q+o(Q)$，固定 $a_{noise}>0$，则旧预算的曲线平移为

$$
\int\left|C_{x,y}(\lfloor2^{h_x+Qz}\rfloor)
 -\Phi\left(\frac{z+a_{noise}/\ln2}{\sqrt v}\right)\right|f_x(y)dy\to0,
\tag{75.26}
$$

最小覆盖大小等价地满足
$\log_2N_{\varepsilon,M}
=h_x+Q[\sqrt v\Phi^{-1}(1-\varepsilon)-a_{noise}/\ln2]+o_{\mathbb P}(Q)$，
误差按 (75.25) 解释。因此 $Q$ 尺度上的对数基数收益精确为 $a_{noise}/\ln2$。
若 $L_M/Q\to\infty$ 但仍为 $o(Q^3)$，同一旧预算的成功质量趋于一。

证明。逐输出使用 (73.26) 的有限信息阈值界，取松弛量 $\sqrt Q$。
原 $h_x/Q^5\to\mathscr H>0$ 与 $L_M=o(Q^3)$ 保证预算最终为正，且其对数取整误差为 $o(1)$。
因此 (75.24) 的绝对差至多
$D_M^{\rm shift}+CQ^{-1/2}+o(Q^{-1})+2^{-\sqrt Q}$。
在 $\sqrt v\Phi^{-1}(1-\varepsilon)$ 两侧各取固定小距离，
正态 CDF 的严格单调性和两侧列表误差把最小覆盖数夹在相应两个整数预算之间，得到 (75.25)。
有限后验排序达到最优；随机化不增加任何给定基数的最大质量。

旧预算在新中心下的标准化阈值为 $z+L_M/(Q\ln2)$。
(75.21) 是所有阈值上的一致距离，故允许这个移动阈值，得到 (75.26) 及趋正无穷时的结论。
其可达性是后验列表意义的可达性，不附计算效率主张。证毕。

所有有界信息误差事件、条件 CDF 距离、列表质量误差与覆盖失败指示函数均对原支持置换不变。
按 (73.28)，先在均匀先验下积分，再用传递置换对称，便得到实际确定支持的联合数据／输出概率结论，
且一致于支持；对信息事件同时保留真实计数 $R(S,\mathscr X)$。
这里不把先验预测混合 $f_x$ 等同于固定真实支持给定 $x$ 后的单个 Gaussian 密度。
规范列表的实际积分成功率具有同一极限；不对能写死支持的不受限解码器宣称不可能性。
未知方向仍只用原共同判向相等事件及同一个测量 $G$。

第 72 章的 $h_x-\widetilde d_M=o_{\mathbb P}(Q)$ 允许将本章中心统一改为
$\widetilde d_M-L_M/\ln2$；不能只用 $Q^5$ 主项替代该精度的中心。
本章未推出平均互信息或输出后验 Shannon 熵的展开，也未推出期望对数覆盖、每个输出保证、
实际密度上确界、零噪声或 $L_M\asymp Q^3$ 的锐利阈值。
新增连接在于移动核心的实际下占据率、保留精确非中心项的指数精度通道比较，
以及将参考密度界转为实际对数密度事件；经典耦合、二次型密度与列表阈值原理各保留其归属。

## 追加锚（75 章后）

## 76. 熵例外集的临界测度与双根同步约束

**定义 76.1（规范函数与同步例外集）。** 沿用第 74 章的共同 Borel 例外集 $E$，
保持原固定幅度、原合法 $Q_n$、全部 floor、补偿和完整得分组。
称 $f$ 为本章允许的规范函数，若它在零的邻域连续、正、递增且趋零，并满足

$$
f(t)/t\text{ 随 }t\text{ 非增},\qquad
\lim_{t\downarrow0}f(t)/t=\infty.
\tag{76.1}
$$

只在该邻域规定 $f$ 即可，其余部分取任意相容延拓。
在两根区间 $(\beta_*,1)$，定义 $E_2$ 为如下固定参数的集合：
存在同一个原合法规模子序列，以及各在正、负率根附近的两个移动完整组，
其实际均值同时趋于两个正有限值。
这里要求同一参数和同一子序列；分别沿两个子序列出现有限均值不够。

**定理 76.2（完整例外集的规范测度零／无穷律）。** 对每个非空开区间
$J\subset(1/2,1)$ 及每个满足 (76.1) 的 $f$，有

$$
\mathcal H^f(E\cap J)=
\begin{cases}
0,&\displaystyle\sum_nQ_n^2f(Q_n^{-3})<\infty,\\
\infty,&\displaystyle\sum_nQ_n^2f(Q_n^{-3})=\infty.
\end{cases}
\tag{76.2}
$$

特别地，$\mathcal H^{2/3}(E\cap J)=\infty$。
若 $f_a(t)=t^{2/3}/(\ln(1/t))^a$，则测度在每个 $a>0$ 时为零，
在 $a\le0$ 时为无穷。

证明。由 (76.1)，对每个固定 $c>0$ 有 $f(ct)\asymp_c f(t)$：
$c\ge1$ 时 $f(t)\le f(ct)\le cf(t)$，$c<1$ 时反向缩放即可。
第 74 章对每个紧参数区间和固定正均值范围，给第 $n$ 层至多 $CQ_n^2$ 个、
直径至多 $CQ_n^{-3}$ 的原 floor 区间覆盖。
当级数收敛时，尾覆盖的总 $f$ 代价趋零。
对正均值范围及紧参数区间取可数穷尽，得到完整 $E$ 的零测度结论。

发散侧使用 Beresnevich–Dickinson–Velani 的经典局部 ubiquity Hausdorff 定理。
在 $J$ 内选非退化紧区间 $\Omega$，取相对 Euclidean 度量和归一化 Lebesgue 测度。
小球测度与半径统一可比，包括端点球，所以其条件 (M2) 的指数为 $d=1$。
以引理 74.4 的正根目标区间中点为点共振，权重为 $Q_n$；
有界权重内只有有限多个点，点共振的交叠指数为 $\gamma=0$。
取块下、上端点 $l_n=Q_{n-1}$、$u_n=Q_n$，并令

$$
\rho(t)=At^{-2},\qquad \psi(t)=\kappa_0t^{-3}.
\tag{76.3}
$$

在稍大紧邻域中使用原网格，再保留 $\Omega$ 中点。
$A$ 足够大时，最大间隙界使每个充分晚块的 $\rho$ 邻域覆盖整个 $\Omega$，
从而给每个相对球中的局部 ubiquity。
$\kappa_0$ 足够小时，每个 $\psi$ 小球包含于对应原 floor 区间的开放中三分之一，
其 limsup $\Lambda$ 因 (74.14) 的实际均值比较而包含于 $E\cap J$。
端点相对球的裁剪不破坏该包含。

该原定理令

$$
g(t)=f(\psi(t))\psi(t)^{-\gamma}\rho(t)^{\gamma-d},
\qquad G=\limsup_ng(u_n).
\tag{76.4}
$$

其条件为 $t^{-d}f(t)$ 递减且在零处趋无穷，$t^{-\gamma}f(t)$ 递增。
在 $G>0$ 时结论为 $\mathcal H^f(\Lambda)=\infty$；
在 $G=0$ 时，若 $\rho(u_{n+1})\le c\rho(u_n)$ 最终成立于某个 $c<1$，
且 $\sum_ng(u_n)=\infty$，同样得到该结论。
本章 (76.1) 恰满足其函数条件，而

$$
g(Q_n)=A^{-1}Q_n^2f(\kappa_0Q_n^{-3})\asymp Q_n^2f(Q_n^{-3}),
\qquad \rho(Q_{n+1})/\rho(Q_n)=(Q_n/Q_{n+1})^2\longrightarrow0.
\tag{76.5}
$$

因此发散时分别由上述两个分支得到无穷测度，不要求 $g(Q_n)$ 单调。
在临界幂 $f(t)=t^{2/3}$ 下，$g(Q_n)=\kappa_0^{2/3}/A>0$。
对数规范的级数项为 $(3\ln Q_n)^{-a}$；
原 $Q_{n+1}=10^{Q_n^5}$ 使其对每个 $a>0$ 都可求和，$a\le0$ 时发散。
该计算不把稀疏层序列替换成连续分母。证毕。

**定理 76.3（局部 packing 维数）。** 每个非空开 $J\subset(1/2,1)$ 满足
$\dim_P(E\cap J)=1$。

证明。第 74 章给 $E$ 内的稠密 $G_\delta$ 集。
以 $\mathcal P^s_\delta(A)$ 表示半径至多 $\delta$、中心在 $A$ 的互不相交球的
$(2r)^s$ 总和上确界，置 $\mathcal P^s_0=\lim_{\delta\downarrow0}\mathcal P^s_\delta$，
并以可数覆盖正则化得到 packing 外测度

$$
\mathcal P^s(A)=\inf_{A\subset\bigcup_iA_i}\sum_i\mathcal P^s_0(A_i).
\tag{76.6}
$$

若 $0<s<1$ 且 $A$ 在某个区间稠密，可在较短区间中放置至少 $c/r$ 个
中心在 $A$ 的不交半径 $r$ 球；总量至少 $cr^{s-1}\to\infty$。
故 $\mathcal P^s_0(A)<\infty$ 迫使 $A$ 无处稠密。
若 $\dim_P(E\cap J)<1$，选介于它与 $1$ 之间的 $s$，
$\mathcal P^s(E\cap J)=0$ 便给一列有限前测度集的覆盖，使 $E\cap J$ 成为贫集，
与它包含相对稠密 $G_\delta$ 矛盾。直线给反向上界 $1$。证毕。

稠密性本身不足以作此推论：可数稠密集的 packing 维数为零。
这里用到了第 74 章的类别结论，而非仅用网格稠密。

**命题 76.4（共享原 floor 的精确同步判据）。** $E_2$ 对平稳对与连续路径实验相同，
且是 Borel 集。固定紧区间 $J\Subset(\beta_*,1)$，沿用
$\chi_{Q,j}=2e^{-z_0}f_j$，对 $H>0$、$j>0$、$k<0$ 定义

$$
\mathcal L_{Q,j,k}(H)=\{L\in\mathbb Z:
 |L\ln2+\ln\chi_{Q,j}|\le H,
 |L\ln2+\ln\chi_{Q,k}|\le H\}.
\tag{76.7}
$$

只保留原区间 $\mathcal J_{Q,L}$ 与 $J$ 相交的 $L$。
令 $A^{(2)}_{Q,H}(J)$ 为所有这些原区间与 $J$ 的交之并，则

$$
E_2\cap J=\bigcup_{H\in\mathbb N}\limsup_n A^{(2)}_{Q_n,H}(J).
\tag{76.8}
$$

证明。第 74 章统一相对比较使两种实际均值与同一个 $2^L\chi_{Q,j}$ 相同到 $1+o(1)$。
同步正有限极限使 (76.7) 两项最终落在一个固定范围内。
反过来，无穷多次满足同一 $H$ 使两个实际均值同时处于同一个正紧区间，
抽取共同子序列即可取得两个正有限极限。
这也证明两种实验的集合相同；不要求其整数 floor 中心完全相同。
有限层为半开区间有限并，可数操作给 Borel 性。证毕。

共享整数条件在未限制参数位置前等价于

$$
\left\lceil\max\left\{\frac{-H-\ln\chi_{Q,j}}{\ln2},
                         \frac{-H-\ln\chi_{Q,k}}{\ln2}\right\}\right\rceil
\le
\left\lfloor\min\left\{\frac{H-\ln\chi_{Q,j}}{\ln2},
                         \frac{H-\ln\chi_{Q,k}}{\ln2}\right\}\right\rfloor.
\tag{76.9}
$$

只核对 $|\ln\chi_{Q,j}-\ln\chi_{Q,k}|\le2H$ 不能替代整数交集与参数位置条件。
其比值还有精确阶乘表达式

$$
\frac{\chi_{Q,j}}{\chi_{Q,k}}
 =(a\lambda)^{Q(j-k)}(b\lambda)^{P(j-k)}
       \frac{k_k!\,l_k!}{k_j!\,l_j!},
\tag{76.10}
$$

其中 $a,b$、$k_j,l_j$ 仍取原固定幅度与原计数线。
该式保留共同实现中的算术关系，不将两个边缘命中率相乘。

**定理 76.5（双根同步集的维数上界）。** 有 $\dim_HE_2\le4/9$。
该上界不证明 $E_2$ 非空，也不声称是锐利值。

证明。令 $I$ 为原率函数，$u_*>0$ 满足 $I(u_*)=I(u_-)$。
在 $0<u<u_*$ 上定义负根曲线 $\Psi(u)\in(u_-,0)$，使 $I(\Psi(u))=I(u)$。
因负侧导数不为零，$\Psi$ 实解析，且

$$
\Psi'(u)=\frac{I'(u)}{I'(\Psi(u))},\qquad
\Psi''(u)=\frac{I''(u)-I''(\Psi(u))\Psi'(u)^2}{I'(\Psi(u))}.
\tag{76.11}
$$

先把同步条件化成固定分母的曲线邻域条件。
设 $N=Q^2$、$d_{0,Q}=k_0-a\lambda\in(-1,0]$，
在两坐标为正的固定紧区间上，原 Stirling 展开为

$$
\ln f_j=-\lambda I(u)-\ln\lambda+A_Q(u)+o(1),
\quad u=j/N,
\tag{76.12}
$$

$$
A_Q(u)=-\ln(2\pi)-\tfrac12\ln[(a+u)(b+\vartheta u)]
 +d_{0,Q}\left[\ln\frac{b+\vartheta u}{b}-\ln\frac{a+u}{a}\right].
\tag{76.13}
$$

$A_Q$ 及固定阶数的导数统一有界。
两计数的 floor 位移分别为 $d_{0,Q}$ 和
$-d_{0,Q}+\lambda u(P/Q-\vartheta)$；末项超指数小，余项统一为 $o(1)$。
在两个根之间，$-\ln\lambda$ 抵消，不能粗略地再留下 $O(\ln Q)$ 误差。
(76.7) 因而蕴含

$$
|I(j/N)-I(k/N)|\le C_{J,H}N^{-3/2},\qquad
|k-N\Psi(j/N)|\le C_{J,H}N^{-1/2}.
\tag{76.14}
$$

个别均值条件先使两点落入相应紧根邻域，再由负侧导数的正绝对下界得第二式。
每个 $j$ 最终至多对应一个 $k$。

还须核对曲率，不假定它处处非零。
原率函数在零处写成

$$
I(u)=\tfrac12Au^2+\tfrac16Bu^3+O(u^4),\quad
A=1/a+\vartheta^2/b>0,\quad B=-1/a^2-\vartheta^3/b^2<0.
\tag{76.15}
$$

用 $I(u)=u^2h(u)$ 和 $u\sqrt{h(u)}$ 的解析逆可将根交换延拓过零，系数比较给
$\Psi(u)=-u-Bu^2/(3A)+O(u^3)$。
所以 $\Psi''(0)=-2B/(3A)>0$，$\Psi''$ 不恒为零；它的内部零点孤立、至多可数。
除去其可数参数像，其余参数可由可数个紧邻域覆盖，每个上有
$0<c\le|\Psi''|\le C$。

固定其中一个 $u$ 区间 $U$。经典二阶导数和估计给

$$
S_h=\sum_{j:j/N\in U}e^{2\pi ihN\Psi(j/N)},\qquad
|S_h|\le C\{\sqrt{hN}+\sqrt{N/h}\}
\quad(1\le h\le\lfloor N^{1/3}\rfloor).
\tag{76.16}
$$

为明确所用范围，若相位 $F$ 在长度 $O(N)$ 的区间上满足
$\eta\le|F''|\le C\eta$、$0<\eta\le1/16$，则
$|\sum e^{2\pi iF(j)}|\le C'(N\sqrt\eta+\eta^{-1/2})$。
其直接证明是删去 $F'$ 距整数不足 $\sqrt\eta$ 的部分：
单调导数只有 $O(N\eta+1)$ 个整数交叉，每段贡献至多 $O(\eta^{-1/2})$ 个格点。
余下每段的相邻相位差单调且离整数至少 $\sqrt\eta$，
用 $(1-e^{2\pi it})^{-1}=1/2+(i/2)\cot(\pi t)$ 作望远镜求和，
端点与总变差都为 $O(\eta^{-1/2})$。
汇总即得该界；取 $F(x)=hN\Psi(x/N)$、$\eta\asymp h/N$ 得 (76.16)。

置 $H_N=\lfloor N^{1/3}\rfloor$，用非负 Fejér 核

$$
K_{H_N}(t)=\frac1{H_N}\left(\frac{\sin(\pi H_Nt)}{\sin(\pi t)}\right)^2
 =\sum_{|h|<H_N}(1-|h|/H_N)e^{2\pi iht}.
\tag{76.17}
$$

在 $\|t\|\le1/(2H_N)$ 上它至少为 $cH_N$。
(76.14) 的整数距离窗 $C_{J,H}N^{-1/2}$ 最终包含于此范围，故其命中数 $Z_N$ 满足

$$
Z_N\le\frac C{H_N}\sum_jK_{H_N}(N\Psi(j/N))
 \le C\left\{\frac N{H_N}+\sqrt{NH_N}+\sqrt{N/H_N}\right\}
 =O(N^{2/3})=O(Q^{4/3}).
\tag{76.18}
$$

每对索引只允许 $O_H(1)$ 个原 floor 区间，每段长度 $O_J(Q^{-3})$。
因此对每个 $s>4/9$，相应覆盖的尾代价由
$C_{J,H}\sum_nQ_n^{4/3-3s}<\infty$ 控制。
对 $H$、曲率邻域取可数并，再加入可数拐点参数，得到所述上界。证毕。

**推论 76.6（两根区域内仍有大量单 Poisson 极限）。**
每个非空开 $J\subset(\beta_*,1)$ 都有一个 $\mathcal H^{2/3}$ 测度为无穷的固定参数集合，
其中每个参数沿某个原合法子序列、对两种实验分别满足

$$
h_M-d_M^{\mathcal E}\ \Rightarrow\ b(P_\theta),
\qquad \theta\in[1/4,1/2],\quad
P_\theta\sim\operatorname{Pois}(\theta),\quad
b(k)=H(\operatorname{Bin}(k,1/2)).
\tag{76.19}
$$

证明。定理 76.2 使用的正根目标 limsup $\Lambda$ 已有无穷临界测度，
而定理 76.5 给 $\mathcal H^{2/3}(E_2)=0$。
对 $\beta\in\Lambda\setminus E_2$，先抽取正根均值趋于 $\theta\in[1/4,1/2]$ 的子序列，
其 floor 最终为零。负根不能在同一子序列上有正紧区间内的均值子极限，
否则参数属于 $E_2$；进一步抽取后，该项趋零、趋无穷或没有过渡组。
第 72 章的实际残差定理将这些情形均移除，只留下 (76.19)。
两种实际均值与共同 proxy 相对相等，故可用相同均值极限，不需要把两个实验耦合为同一样本。证毕。

真正的双 Poisson 可达性仍未解决。
足够的后续条件是：在某个非退化紧参数区间中，存在一个固定 $H$，
使每个开子区间在任意晚的原合法层都能找到某一更晚层的完整同步 floor 区间。
严格内含的嵌套闭区间即可固定一个参数，并抽取两个正有限均值；
逐次让 $H$ 无界增长不能履行这个条件。
(76.18) 只有上计数界，不能推出任何下计数或存在性。

此外，若写 $k=N\Psi(u)+\xi$，$\xi=O(Q^{-1})$，原精细展开给

$$
\ln(\chi_{Q,j}/\chi_{Q,k})
 =QI'(\Psi(u))\xi+A_Q(u)-A_Q(\Psi(u))+o(1).
\tag{76.20}
$$

前因子造成的 $Q^{-1}$ 阶整数位置平移与目标宽度同阶，
取得实际命中时不能丢弃，之后还须满足 (76.9)。
对所有分母累计的有理点定理，或两个边缘 limsup 的交集，均不能直接履行这个固定分母同步条件。
本章不证明 $E_2$ 非空、不声称维数为 $1/3$，也不判定指定 $\beta_*$ 的正根算术。
参数上的测度与类别结论不引入新统计先验；实际概率量词与共同方向事件保持第 74 章的范围。
不包含期望熵、无界矩转移、数值起效、有限精度或效率保证。

## 追加锚（76 章后）

## 77. 实际输出密度与低噪声平均信息的常数项

**定义 77.1（纤维内平均信息）。** 保持第 75 章的原实验、完整计数目标和精确标量
$T=t_x(R)$；$Y=T+\sigma_MG$，其中 $G$ 是独立标准正态，
$L_M=\ln(1/\sigma_M)\to\infty$ 且 $L_M=o(Q^3)$。
$p_x(n\mid y)$、$f_x(y)$、$h_x=H_2(P_x)$ 均保持原定义。
记 $w_n(y)=\varphi_{\sigma_M}(y-t_x(n))$，定义

$$
\begin{aligned}
\mathsf h_M(x)&=-\int f_x(y)\ln f_x(y)\,dy,\\
I_M(x)&=\sum_nP_x(n)\int w_n(y)\ln\frac{w_n(y)}{f_x(y)}\,dy,\\
\overline H_M(x)&=\int H_2(p_x(\cdot\mid y))f_x(y)\,dy.
\end{aligned}
\tag{77.1}
$$

前两项使用自然单位，第三项使用 bits。这些都是指定均匀大小 $q$ 支持先验下的纤维量。
它们可以作为数据函数在确定支持的原始数据律下求概率；定义本身不改为点质量先验。
令原空间剖面与方差常数为

$$
\rho(t)=\frac{e^{-\kappa t^2/2}}{4\pi\sqrt{ab}},\qquad
\kappa=a^{-1}+\alpha^2/b,\qquad
 g_0=\int_{\mathbb R}\rho(t)^2dt
 =\frac1{16\pi^2ab}\sqrt{\frac\pi\kappa},\qquad \nu=2g_0>0.
\tag{77.2}
$$

$a=(1+r)/2$、$b=(1-r)/2$ 和 $\alpha$ 均为原固定参数。
以 $\varphi_\nu$ 表示方差为 $\nu$ 的中心正态密度，区别于按标准差标记的测量核。

**定理 77.2（真实噪声精度的密度控制）。** 对每个上述确定噪声序列，在两种实际实验中，

$$
\|f_{\mathscr X}\|_\infty=O_{\mathbb P}(1),\qquad
\|f_{\mathscr X}-\varphi_\nu\|_1\longrightarrow0,\qquad
\mathbb E_{P_{\mathscr X}}T^2=O_{\mathbb P}(1).
\tag{77.3}
$$

收敛与紧性均一致于确定真实支持。例如第二式的量词是对每个 $\varepsilon>0$，
$\sup_{S:|S|=q}\Pr_S^{\mathscr X}
\{\|f_{\mathscr X}-\varphi_\nu\|_1>\varepsilon\}\to0$。
不是对所有尚未指定收敛速度的噪声序列同时取上确界。

证明。以下全部环境估计来自原一、二行比较，平稳路径中不假定观测行独立。
沿用第 75 章的单个完整乘积计数律 $\mathsf Q_x$、
密度 $L_x=dP_x/d\mathsf Q_x$、$a_x=\|L_x-1\|_2$、
$v_j=C_jp_j(1-p_j)/B^2$、$V=\sum_jv_j$、
$U_j=(R_j-C_jp_j)/B$ 和 $e_j=(\mu_j-C_jp_j)/B$。
噪声对数 $L_M$ 与密度 $L_x$ 不混用。

先把完整密度的上界保留到一阶精度。令 $d_A,d_C,d_J$ 分别为校准 Bernoulli
总和、窗口补集和窗口内的方差，$m_J$ 为窗口总和均值。
第 68 章的精确条件化式与方差型局部 Bernoulli 估计给

$$
L_x(k)=\sqrt{d_A/d_C}\,
 e^{-(k-m_J)^2/(2d_C)}+O(q^{-1/2}),\qquad
0\le L_x\le1+\eta_x,\quad
\eta_x\le C(d_J/q+q^{-1/2})=O_{\mathbb P}(Q^{-5/2}).
\tag{77.4}
$$

误差在所有整数 $k$ 上一致；分母是均值恰为整数 $q$ 的总和中心质量。
这里 $d_A,d_C\asymp q$，$d_J=O_{\mathbb P}(B^2)$。
这些关系与 $a_x=O_{\mathbb P}(Q^{-5/2})$ 在同一好事件成立。
由密度恒等式与 Hilbert 空间 Cauchy–Schwarz，任意指标集 $D$ 满足

$$
 e_D=\mathbb E_{\mathsf Q_x}[(L_x-1)U_D],\qquad
 \|e_D\|\le a_x\sqrt{V_D}.
\tag{77.5}
$$

实际二阶矩可直接重新核对。精确展开为
$T=\delta^{-1/2}\{\sum_j(U_j^2-v_j)-2e\cdot U+\|e\|^2\}$。
乘积律下二项四阶矩给
$\mathbb E(\sum_j(U_j^2-v_j))^2\le2\sum_jv_j^2+B^{-2}V$。
利用 (77.4) 的非负密度上界，得到

$$
\mathbb E_{P_x}T^2\le\frac C\delta
 \left[2\sum_jv_j^2+B^{-2}V+4a_x^2V^2+a_x^4V^2\right]
 =O_{\mathbb P}(1).
\tag{77.6}
$$

此处 $V=O_{\mathbb P}(1)$、$\sum_jv_j^2=O_{\mathbb P}(\delta)$、
$B^{-2}/\delta=Q^3/q\to0$。这是实际纤维内的矩估计，不通过 TV 搬运无界函数。

还需识别平方质量的常数。固定 $H<\infty$，原 Poisson 率与 Stirling 展开在
$|j\delta|\le H$ 上给

$$
f_j=\frac{e^{-\kappa(j\delta)^2/2}}{2\pi\lambda\sqrt{ab}}(1+o(1)),\qquad
\sup_{|j\delta|\le H}\left|\frac{v_j}{\delta\rho(j\delta)}-1\right|
 \longrightarrow0.
\tag{77.7}
$$

第二式使用实际占据均值 $m_j\sim2qf_j$、校准 $p_j\to1/2$，
以及原一、二行方差界在这个固定核心内的一致相对集中。
例如取相对容差 $Q^{-1}$，对 $O_H(\delta^{-1})$ 组取并的失败概率至多
$C_HQ^2\delta^{-1}\{\exp[-c_q\lambda+O_H(1)+O(\ln Q)]+e_{row}\}\to0$。
若 $a_j^{occ}=m_j/B^2$，原实际二阶占据界给
$\mathbb E_Sv_j^2\le C[(a_j^{occ})^2+B^{-2}a_j^{occ}]$。
率函数的 Gaussian 尾和非正规端点的指数界因而给

$$
\sup_S\mathbb E_S\left[\delta^{-1}
 \sum_{|j\delta|>H}v_j^2\right]
 \le Ce^{-cH^2}+CB^{-2}/\delta+Q^Ce^{-c\lambda}.
\tag{77.8}
$$

这在确定截断计数线上先计算，只有移除原全行截断失败事件后才与完整窗口认同。
紧核心的 Riemann 和、(77.8) 的 Markov 界及 $H\to\infty$ 证明
$\delta^{-1}\sum_jv_j^2\to g_0$。
累积方差钟的收敛本身不替代这个逐组平方质量计算。

现在取第 75 章的移动核心
$R_M^2=\sqrt{\lambda(L_M+\ln Q+1)}$，及其 $\mathcal C_M,\mathcal O_M$。
保留 (75.12) 的全部精确非中心项和外部中心截距，令该参考量仍为 $T^{\rm G}$。
在同一完整乘积向量与独立分位耦合上，设
$D_M(x)=\mathbb E|T-T^{\rm G}|$。
原实际一阶占据尾界及 (75.13) 给

$$
\begin{aligned}
\sup_S\mathbb E_S V_{\mathcal O}&\le Ce^{-cR_M^2}+Q^Ce^{-c\lambda},\\
D_M(x)&\le CQ^{1/4}
 \{V_{\mathcal O}+(1+a_x)V e^{-c_q\lambda/24}\}.
\end{aligned}
\tag{77.9}
$$

第一式仍在确定计数线上使用。第二式的尾差精确为
$\delta^{-1/2}\sum_{\mathcal O}(U_j^2-v_j-2e_jU_j)$；
(77.5) 使其绝对均值至多 $C\delta^{-1/2}V_{\mathcal O}$。
没有把尾部 $\|e_{\mathcal O}\|^2$ 删去后再付出噪声放大。
相较于第 75 章，这里需要支付更强的 $\sigma_M^{-2}$。
由于 $R_M^2/(L_M+\ln Q+1)\to\infty$，有

$$
\begin{aligned}
 Q^{1/4}e^{2L_M}(e^{-cR_M^2}+Q^Ce^{-c\lambda})&\to0,\\
 Q^{5/4}e^{2L_M-c_q\lambda/24}&\to0,\\
 \sigma_M^{-2}D_M(\mathscr X)&\longrightarrow0.
\end{aligned}
\tag{77.10}
$$

最后一式使用实际尾部期望的 Markov 界及高概率事件 $V\le Q$。
所有精确 $e_j$ 和随机 $v_j$ 先保留在参考量内；空间剖面近似误差不乘 $\sigma_M^{-2}$。

参考密度需要强于弱极限的结论。令核心内 $w_j=v_j/\sqrt\delta$。
移动核心的实际相对占据上界与 (77.7)–(77.8) 给
$\max w_j\le C\sqrt\delta\to0$、$\sum w_j^2\to g_0$。
参考量精确展开为

$$
T^{\rm G}=\sum_{\mathcal C}w_j(Z_j^2-1)
 -2\delta^{-1/2}\sum_{\mathcal C}e_j\sqrt{v_j}Z_j
 +\delta^{-1/2}\|e\|^2.
\tag{77.11}
$$

最后一项是 $o_{\mathbb P}(1)$，线性项的条件方差至多
$4\delta^{-1}(\max v_j)\|e\|^2=o_{\mathbb P}(1)$。
它不必与二次项独立。对固定 $t$，中心二次项的对数特征函数为
$-t^2\sum w_j^2+O_t((\max w_j)\sum w_j^2)\to-g_0t^2$。
故参考极限的方差恰为 $2g_0$。

(75.16) 的非中心特征函数估计保留了任意 $e_j$。
中心小核心有 $n_0\asymp\delta^{-1}$ 个 $w_j\asymp\sqrt\delta$，因而完整特征函数满足
$|\psi_x(t)|\le(1+c\delta t^2)^{-n_0/4}$。
在 $|t|\le\delta^{-1/2}$ 上它由固定 Gaussian 函数控制；外部积分至多
$C\delta^{-1/2}(1+c)^{-n_0/8}\int_1^\infty(1+cu^2)^{-1}du\to0$。
所以特征函数的 $L^1$ 尾一致消失。
固定 $t$ 极限与 Fourier 反演给无噪声参考密度 $g_x^0$ 满足
$\|g_x^0-\varphi_\nu\|_\infty\to0$，且 $\|g_x^0\|_\infty\le C$。
两密度积分均为一，对 $\min(g_x^0,\varphi_\nu)$ 用支配收敛得到
$\|g_x^0-\varphi_\nu\|_1\to0$。
这些论证先对任意满足上述参数极限的确定环境序列成立，
再由各环境误差的一致概率界推出一致原数据概率版本。
令 $g_x=g_x^0*\varphi_{\sigma_M}$，卷积收缩与 Gaussian 方差
$\nu+\sigma_M^2\to\nu$ 给

$$
 \|g_x\|_\infty\le C,\qquad \|g_x-\varphi_\nu\|_1\to0.
\tag{77.12}
$$

最后回到实际输出。乘积标量密度
$f_x^{prod}(y)=\mathbb E_{\mathsf Q_x}\varphi_{\sigma_M}(y-T)$ 使用同一精确中心。
(77.4) 直接给逐点正密度支配
$f_x(y)\le(1+\eta_x)f_x^{prod}(y)$。
Gaussian 核的导数范数为
$\|\varphi_\sigma'\|_\infty=e^{-1/2}/(\sqrt{2\pi}\sigma^2)$、
$\|\varphi_\sigma'\|_1=\sqrt{2/\pi}/\sigma$。
对 (77.9) 的同一标量耦合应用平移界，再对完整后验向量使用一次核收缩，得

$$
\begin{aligned}
\|f_x\|_\infty
 &\le(1+\eta_x)\left[C+\frac{e^{-1/2}}{\sqrt{2\pi}}
                  \sigma_M^{-2}D_M(x)\right],\\
\|f_x-\varphi_\nu\|_1
 &\le a_x+\sqrt{2/\pi}\,\sigma_M^{-1}D_M(x)
               +\|g_x-\varphi_\nu\|_1.
\end{aligned}
\tag{77.13}
$$

(77.10)–(77.12) 证明所需两个密度结论。
完整密度误差 $a_x$ 从未除以噪声；上确界控制依靠正密度支配及指数精度标量耦合。
这里未声称实际密度在上确界范数收敛到 Gaussian。证毕。

**定理 77.3（平均信息与平均输出后验熵）。** 在定义 77.1 的整个范围内，
各有限纤维的积分均存在，并有精确恒等式

$$
 I_M(x)=L_M-\tfrac12\ln(2\pi e)+\mathsf h_M(x),\qquad
 \overline H_M(x)=h_x-I_M(x)/\ln2.
\tag{77.14}
$$

进而，在定理 77.2 的同一一致原数据概率意义下，

$$
\begin{aligned}
\mathsf h_M(\mathscr X)&\longrightarrow\tfrac12\ln(2\pi e\nu),\\
I_M(\mathscr X)&=L_M+\tfrac12\ln\nu+o_{\mathbb P}(1),\\
\overline H_M(\mathscr X)&=h_{\mathscr X}
 -\frac{L_M}{\ln2}-\frac{\ln\nu}{2\ln2}+o_{\mathbb P}(1).
\end{aligned}
\tag{77.15}
$$

证明。先明确所需经典熵连续性条件。若概率密度 $f$ 满足
$\|f\|_\infty\le B\ge1$ 和 $\int y^2f(y)dy\le K$，则对 $R>0$，

$$
\int_{|y|>R}|f\ln f|\,dy
 \le\frac{K\ln B}{R^2}+\frac{2e^{-R}}e+\frac KR.
\tag{77.16}
$$

在 $f>1$ 上用 $f\ln f\le f\ln B$；在 $f\le1$ 上置
$q_0(y)=e^{-|y|}$，由 $u\ln(1/u)\le1/e$ 得
$f\ln(1/f)\le q_0/e+|y|f$，再积分即得该式。
需要的是二阶矩有界给出的一阶矩尾控制，不要求二阶矩本身一致可积。

对共同满足这些界的 $f,g$，置 $d=\|f-g\|_1$，
$M_B=\sup_{[0,B]}|t\ln t|$，$\omega_B(u)$ 为 $t\ln t$ 在该区间的连续模。
紧区间按 $|f-g|\le u$ 分开，补集长度至多 $d/u$，从而

$$
|\mathsf h(f)-\mathsf h(g)|
 \le2\left[\frac{K\ln B}{R^2}+\frac{2e^{-R}}e+\frac KR\right]
      +2R\omega_B(u)+2M_Bd/u.
\tag{77.17}
$$

先取 $R$ 大，再取 $u$ 小，最后取 $d$ 小，给出该密度／矩类上的 $L^1$ 熵连续性。
这是经典结果的本章所需一维证明。
有限纤维中 $f_x\le1/(\sqrt{2\pi}\sigma_M)$、$\mathbb E_xY^2<\infty$，
故 (77.16) 先保证每个纤维的 $\int|f_x\ln f_x|<\infty$。

在渐近分析中，$\mathbb E_xY^2=\mathbb E_{P_x}T^2+\sigma_M^2=O_{\mathbb P}(1)$。
给定任意外层失败容差，定理 77.2 允许选确定 $B,K$，
使实际密度及 Gaussian 极限共同满足两界，除去的原数据概率不超过该容差。
在余下事件使用 (77.17) 和 (77.3) 的 $L^1$ 收敛，最后令外层容差趋零，
即得 (77.15) 第一式。弱收敛和密度有界本身不足以排除细密度振荡，
而单独 $L^1$ 收敛不足以控制熵尾；本证明分别给出两部分。

有限 Gaussian 通道上，实际同一实现满足
$\ln w_R(Y)=L_M-\tfrac12\ln(2\pi)-G^2/2$。
给定原始数据的 $G$ 仍为标准正态，积分得
$\mathbb E_x\ln w_R(Y)=L_M-\tfrac12\ln(2\pi e)$。
对每个正先验原子 $n$，$f_x\ge P_x(n)w_n$，
而 $\ln^+f_x$ 有有限上界，所以各 $w_n|\ln f_x|$ 的积分有限。
由有限求和可交换积分，信息密度的期望即给 (77.14) 第一式。
有限字母 Bayes 恒等式
$-\log_2p_x(n\mid y)=-\log_2P_x(n)-\ln(w_n(y)/f_x(y))/\ln2$
再给第二式；输出后验熵本身介于零和有限 $\log_2|\mathcal F_x|$ 之间。
代入已证微分熵极限即得全部展开。证毕。

本章新增了第 75 章未承担的期望结论，凭据是新的实际密度支配、
$\sigma^{-2}$ 精度耦合、平方质量极限和熵尾控制，未从概率信息密度结论直接取期望。
当 $L_M=a_{noise}Q+o(Q)$ 时，(77.15) 给该精确噪声对数之上的常数修正；
若只知道 $L_M=a_{noise}Q+o(Q)$，不能把其中的 $o(Q)$ 擅自降为 $o(1)$。
本章精确熵中心 $h_x$ 不由其 $Q^5$ 主项或只有 $o_{\mathbb P}(Q)$ 精度的中心替代。

原支持置换保持全部数据函数不变，未知方向仍只使用原共同判向相等事件，
其失败概率 $O(q^{-1})$ 只进入概率结论。所有输出积分使用先验预测混合 $f_x$；
它不等于固定支持给定数据后的单个 Gaussian 密度。
本章没有全原始数据平均的信息／熵展开，也没有逐输出后验 Shannon 熵集中、
期望对数覆盖、任意解码器不可能性或计算效率结论。
$L_M\asymp Q^3$ 时当前半径及耦合预算不再给出上述推导；这不是该尺度的反例或必要阈值。
零噪声、其他幅度、向量／适应性通道均未纳入。
Gaussian 平移界、二次型密度、熵连续性与有限 Bayes 链式公式保留经典归属；
新增连接是原实际后验在整个所述低噪声范围内满足这些定理的联合条件。

## 追加锚（77 章后）

## 78. 一个固定参数实现全部正 Poisson 均值

**定义 78.1（正根均值的通用子序列集）。** 保持第 72、74 章的原幅度、合法规模、
全部取整和补偿、完整得分组及两种实际实验。
以 $\bar c_{Q,j}^{\mathcal E}(\beta)$ 表示包含原计数线点
$(k_0+jQ,l_0+jP)$ 的完整组之实际占据均值；它不是后验标签中心。
仍用 $\vartheta$ 表示原 Liouville 斜率，$\theta$ 专指目标 Poisson 均值。
定义 $\mathcal U$ 为满足以下性质的固定 $\beta\in(1/2,1)$ 的集合：
对每个实数 $\theta>0$，存在原合法层的严格递增子序列及正根侧索引 $j_n$，使

$$
\bar c_{Q_n,j_n}^{pair}(\beta)\longrightarrow\theta,
\qquad
\bar c_{Q_n,j_n}^{path}(\beta)\longrightarrow\theta.
\tag{78.1}
$$

同一个参数、子序列和索引用于两种确定均值；这不把两种不同数据实验耦合为一次观测。
由 (74.6)，只用其中任一种实验定义的集合也等于 $\mathcal U$。
本章将构造一个明确的稠密 $G_\delta$ 子集 $\mathcal U_0\subset\mathcal U$。

**引理 78.2（精确阶乘相位的区间下计数）。** 使用 (74.3) 的
$\chi_{Q,j}=2e^{-z_0}f_j$。固定稍大的紧参数区间 $K\Subset(1/2,1)$，
只取其正根所对应的紧 $u=j/Q^2$ 区间。
把 $\log_2\chi_{Q,j}$ 延伸为实变量函数

$$
\Phi_Q(t)=\frac1{\ln2}\left[
\ln2-z_0-\lambda+(k_0+Qt)\ln(a\lambda)+(l_0+Pt)\ln(b\lambda)
 -\ln\Gamma(k_0+Qt+1)-\ln\Gamma(l_0+Pt+1)\right].
\tag{78.2}
$$

在任意 $N$ 个连续可用索引上，对每个固定正整数 $h$，有

$$
\left|\sum_j e^{2\pi ih\Phi_Q(j)}\right|
 \le C_K\{N\sqrt{h/Q}+\sqrt{Q/h}\}.
\tag{78.3}
$$

对圆周上每个固定非空开弧 $A$，存在 $p_A>0,C_{K,A}<\infty$ 使

$$
\#\{j:\{\Phi_Q(j)\}\in A\}
 \ge p_AN-C_{K,A}(N/\sqrt Q+\sqrt Q).
\tag{78.4}
$$

证明。Euler 乘积的二阶对数导数为
$\psi_1(x)=\sum_{m\ge0}(x+m)^{-2}$，且
$x^{-1}\le\psi_1(x)\le x^{-1}+x^{-2}$。
导数级数在正半轴紧集上一致收敛，积分比较给两界。
因此原精确相位满足

$$
\Phi_Q''(t)=-\frac{Q^2\psi_1(k_0+Qt+1)+P^2\psi_1(l_0+Pt+1)}{\ln2},
\qquad c_K/Q\le-\Phi_Q''(t)\le C_K/Q.
\tag{78.5}
$$

两个 Gamma 参数与 $Q^3$ 同阶，$P/Q$ 有正的有限界。
这里保留了精确 $k_0,l_0,P$，没有对一个未控制导数的 Stirling 余项求导。

经典二阶导数检验给：若 $\eta\le|f''|\le C\eta$、$0<\eta\le1/16$，
则长 $N$ 的整数区间上指数和至多 $C'(N\sqrt\eta+\eta^{-1/2})$。
其所需一致性可直接看出：$f'$ 单调，删去距整数不足 $\sqrt\eta$ 的部分，
其 $O(N\eta+1)$ 个分量共包含 $O(N\sqrt\eta+\eta^{-1/2})$ 个整数。
余下每段的相邻相位差单调、距整数至少 $\sqrt\eta$，
利用 $(1-e^{2\pi it})^{-1}=1/2+(i/2)\cot(\pi t)$ 的望远镜分解，
端点与总变差给每段 $O(\eta^{-1/2})$；段数同阶，得到所述界。
边界整数只增加相同量级。对 $h\Phi_Q$ 应用即得 (78.3)。

为得到真正的下界，选 $0\le g\le1$ 为支撑于 $A$ 的连续圆周函数，且 $\int g>0$。
它的一个固定足够高阶 Fejér 均值 $P$ 满足
$\|P-g\|_\infty<\epsilon<\frac12\int g$。
于是 $P-\epsilon\le\mathbf1_A$ 且积分为正。
对这个有限三角多项式各非零频率用 (78.3)，便得 (78.4)。
固定弧后，若 $N$ 大于弧相关常数乘 $\sqrt Q$，且 $Q$ 足够大，下界至少为 $p_AN/2$。
这也是经典有限序列 discrepancy 不等式的直接后果。
这里只在每个合法 $Q$ 上横跨索引作计数，未证明一个固定参数沿层数等分布。证毕。

**引理 78.3（任意窄均值带的原 floor 区间）。** 固定
$B=(A,B')\Subset(0,\infty)$，且 $\log_2(B'/A)<1$。
在 $B$ 内依次固定有正宽度的嵌套内带，最内带为 $(A_2,B_2)$。
筛选满足存在整数 $L=L(j)$ 使

$$
 A_2<2^{L+\Phi_Q(j)}<B_2
\tag{78.6}
$$

的正根索引。$L$ 唯一；相位条件是一条固定正长度圆弧，跨零时可再取非空子弧。
以 $x_{Q,j}$ 表示原 floor 区间 $\mathcal J_{Q,L(j)}$ 的中点。
在每个紧参数区间中，这些中点最小间距至少 $c_KQ^{-2}$，区间宽度与 $Q^{-3}$ 同阶。
任意长 $r$ 的区间内中点数至多 $C_K(1+rQ^2)$。
对一个已经固定的父区间，所有充分大合法 $Q$ 都有至少

$$
 a_{K,B}\,rQ^2\quad(a_{K,B}>0)
\tag{78.7}
$$

个完整选中区间内含于其中央部分。两种实际均值在每个这样的整个原区间上均属于 $B$。

证明。引理 74.2 的全部原 floor 与补偿估计给
$m_j=2^{L_0(\beta)}\chi_{Q,j}(1+o_K(1))$ 及
$|\bar c_j^{\mathcal E}-m_j|\le\varepsilon_Mm_j+\rho_M$。
有界正均值带上这是两种实际均值的统一相对近似；内带余量保证落入外带。
每个原 $M$-floor 区间上 $M,q$、补偿、实际分布与均值均不变。

正根紧区间上的精确阶乘 Stirling 展开为

$$
\ln\chi_{Q,j}=-Q^3[\phi+I(j/Q^2)]-\ln(Q^3)+O_K(1).
\tag{78.8}
$$

$z_0$ 和两个计数取整的有界影响包含在末项。
故对 $F(u)=\phi/(\phi+I(u))$，
$x_{Q,j}=F(j/Q^2)+O_{K,B}(\ln Q/Q^3)$。
$|F'|$ 在此紧区间有正的有限上下界，误差为 $o(Q^{-2})$，
从而不同索引不落入同一个 floor 区间，并给最小间距及上计数界。

父区间中央部分的 $F$ 逆像含 $N\asymp_KrQ^2$ 个连续整数索引。
(78.4) 在 $rQ^2$ 超过带相关常数乘 $\sqrt Q$ 时给正比例下计数。
再令位置误差与区间宽度相对 $r$ 足够小，便得 (78.7)。
这里只得到父区间内的正比例计数，没有得到筛选网格的 $O(Q^{-2})$ 最大空隙界。证毕。

**定理 78.4（一个固定参数的全部均值与局部维数）。** 存在稠密 $G_\delta$ 集
$\mathcal U_0\subset\mathcal U\subset E$，使每个非空开区间 $J\subset(1/2,1)$ 满足

$$
\dim_H(\mathcal U_0\cap J)=\dim_H(\mathcal U\cap J)=\frac23.
\tag{78.9}
$$

两集合均为 Lebesgue 零测度的余贫集，局部 packing 维数为一。
对 $\beta\in\mathcal U_0$，(78.1) 在任意正整数目标处还可分别指定从下侧或上侧趋近，
且两种实际均值具有同一指定侧。

证明。取正半轴上端点有理、端点比小于二的可数开区间基 $\mathscr B$。
对每个带固定引理 78.3 的内带。
令 $U_{n,B}$ 为该层全部选中原区间的开放中三分之一之并，
每层只取可行正索引且区间落在 $(1/2,1)$ 中。
引理 78.3 使 $\bigcup_{n\ge N}U_{n,B}$ 对每个 $B,N$ 都稠密，故

$$
\mathcal U_0=\bigcap_{B\in\mathscr B}\bigcap_{N\ge1}
                   \bigcup_{n\ge N}U_{n,B}
\tag{78.10}
$$

是稠密 $G_\delta$。
固定其中一个 $\beta$ 和任意实 $\theta>0$，取直径趋零、逼近 $\theta$ 的基区间。
逐次选择严格更晚的命中层，并超过该固定带的实际／代理误差阈值，
即可让两种实际均值同时趋于 $\theta$。
整数目标可把每个带都置于其严格下侧或上侧。
这是先固定一次 $\beta$ 后的对角选取，不只覆盖有理均值，也不让 $\beta$ 随层变化。
完整集合 $\mathcal U$ 也可用每个有理基带中无穷多次实际命中表述，因而是 Borel 集。
(74.6) 给两种实验定义相同，定理 72.3 给 $\mathcal U\subset E$。
若负根也保留有限项，两个独立非退化 Poisson 熵项不能相互抵消。

维数下界需要重新控制任意尺度，不能给筛选网格借用未证的最大空隙性质。
固定非退化闭区间 $K_0\Subset J$ 及稍大紧邻域 $K$。
事先排列均值带 $B_s$，使每个基带出现无穷多次，并固定相应下计数常数
$a_s\in(0,1]$，记 $A_s=-\ln a_s$。这些常数可以随 $s$ 任意趋零。
取只依赖 $K$ 的小常数 $\kappa_0>0$，递归选择原合法层的子序列
$R_s=Q_{n_s}$，置 $\ell_s=\kappa_0R_s^{-3}$、$t_s=\ln R_s$。
在每个父区间中央部分保留以 $B_s$-选中原区间中点为中心、长度 $\ell_s$ 的闭区间，
使它严格位于相应开放中三分之一中。引理 78.3 允许要求每个父区间的子数满足

$$
 a_s\ell_{s-1}R_s^2\le N_s(P)\le C_K\ell_{s-1}R_s^2,
 \qquad a_s\ell_{s-1}R_s^2\ge2,
\tag{78.11}
$$

首层用 $\ell_0=|K_0|$。每阶段还要求

$$
t_s\ge s^2\left[\sum_{i<s}t_i+\sum_{i\le s+1}A_i
 +C(s+1)+C|\ln\ell_0|+C|\ln\kappa_0|\right].
\tag{78.12}
$$

下一带的 $a_{s+1}$ 在选择 $R_s$ 前已经确定，故这是合法的前瞻条件。
原合法序列无界，可同时满足所有有限阈值、各父区间下计数与实际带内条件。
这只是抽取原层，不修改任何 $M,q$ 或模型。

嵌套交集 $\mathcal K$ 是非空紧集，且 $\mathcal K\subset\mathcal U_0\cap J$。
将每个父区间质量等分给其子区间，所得概率测度记为 $\nu_0$。
若 $M_s$ 为最大第 $s$ 层质量，则 (78.11) 给

$$
\ln M_s\le-2t_s+\sum_{i<s}t_i+\sum_{i\le s}A_i
                 +O(s+|\ln\ell_0|).
\tag{78.13}
$$

固定 $0<d<2/3$，由 (78.12) 可同时得到

$$
 M_s\le C_d\ell_s^d,
 \qquad M_{s-1}\le C_d(a_s\ell_{s-1})^d.
\tag{78.14}
$$

第一式的对数差含主项 $-(2-3d)t_s$；第二式在第 $s-1$ 层多付 $dA_s$，
由该层的前瞻项吸收。有限初始层只改变 $C_d$。
第二式是控制筛选密度损失的必要额外步骤。

设任意短区间 $A$ 的长度为 $r$，取 $\ell_s\le r<\ell_{s-1}$。
上一层间距远大于其宽度，故 $A$ 只交固定多个父区间。
若 $r<R_s^{-2}$，子中点最小间距使其只交固定多个子区间，
于是 $\nu_0(A)\le CM_s\le C_dr^d$。
若 $r\ge R_s^{-2}$，上计数界与 (78.11) 给

$$
\nu_0(A)\le C_KM_{s-1}
       \min\{1,r/(a_s\ell_{s-1})\}.
\tag{78.15}
$$

置 $r_0=a_s\ell_{s-1}$，以 (78.14) 第二式替换父质量。
$r\ge r_0$ 时界为 $C_dr_0^d\le C_dr^d$；
$r<r_0$ 时界为 $C_dr_0^d(r/r_0)
=C_dr^d(r/r_0)^{1-d}\le C_dr^d$。
所以任意足够细区间覆盖都满足
$1\le C_d\sum|A_i|^d$，得到 $\dim_H\mathcal K\ge d$。
同一构造对每个固定 $d<2/3$ 成立，故下界为 $2/3$。
上界与零测度来自 $\mathcal U\subset E$ 和第 74 章。
两集包含稠密 $G_\delta$，故余贫；第 76 章的 Baire／packing 论证逐区间给 packing 维数一。
它使用第一纲闭包覆盖的矛盾，不由稠密性单独推得。证毕。

**推论 78.5（一个参数的整族单 Poisson 熵极限）。** 对每个
$\beta\in\mathcal U_0\cap(1/2,\beta_*)$，以及每个
$\beta\in\mathcal U_0\setminus E_2$ 且 $\beta>\beta_*$，
实际后验熵残差在每个非整数 $\theta>0$ 都有合法子序列极限

$$
h_M-d_M^{\mathcal E}\ \Rightarrow\
 b(P_\theta)-b(\lfloor\theta\rfloor),
 \qquad b(k)=H_2(\operatorname{Bin}(k,1/2)),\quad P_\theta\sim\operatorname{Poi}(\theta).
\tag{78.16}
$$

在每个正整数 $m$，分别有子序列达到

$$
 b(P_m)-b(m-1),\qquad b(P_m)-b(m).
\tag{78.17}
$$

两种实验各使用自己的精确确定中心 $d_M^{\mathcal E}$。
此外，每个非空开 $J\subset(\beta_*,1)$ 满足

$$
\dim_H((\mathcal U_0\setminus E_2)\cap J)=\frac23.
\tag{78.18}
$$

证明。定理 72.3 的实际熵表示只保留最多两个过渡根的
$b(C_j)-b(\lfloor\bar c_j^{\mathcal E}\rfloor)$，误差为 $o_{\mathbb P}(1)$。
正有限均值的实际占据极限由原固定阶多行 PGF 给 Poisson 律；
若两根同时存在，其极限独立。
在单根区间，将定理 78.4 的同一固定参数子序列代入即可。
非整数目标使 floor 最终固定；整数目标从下／上侧分别选带，
让两种实际均值同时有 floor $m-1$／$m$，不是假定代理与实际的 floor 自动相同。

在两根区间，对 $\beta\notin E_2$ 的一个右根均值子序列，
左根不可能再有正有限紧子极限，否则正是 $E_2$ 的定义。
进一步抽取后，左侧趋零、趋无穷或无过渡组，其贡献由第 72 章实际熵增量估计趋零。
正根极限及指定侧保留，得到相同单项律。
在指定 $\beta_*$，引理 74.6 排除了负端点正有限均值，
故若该指定参数属于 $\mathcal U_0$，结论亦成立；本章没有判定其成员身份。

定理 76.5 给 $\dim_HE_2\le4/9<2/3$。
若 (78.18) 的差集维数更小，则将其与 $\mathcal U_0\cap E_2$ 作有限并，
会使 $\mathcal U_0\cap J$ 维数小于 $2/3$，与 (78.9) 矛盾。证毕。

这里没有给 $\mathcal U_0\setminus E_2$ 余贫性结论：小 Hausdorff 维数不蕴含贫性。
在整个 $\mathcal U_0$ 上已证明所有正根均值的通用性，但未排除某些子序列附带左侧 Poisson 项。
$E_2$ 的非空性、锐利维数及指定同步均值仍未解决。

(78.14) 只对 $d<2/3$ 有效；临界时负主项消失。
因此本章未确定 $\mathcal H^{2/3}(\mathcal U_0\cap J)$ 或
$\mathcal H^{2/3}(\mathcal U\cap J)$。
第 76 章对更大集合 $E$ 的临界无穷测度不能经包含关系传给这里；
其收敛规范的零测度结论可以传递。
也未把可数个均值带 limsup 的维数或测度直接当作其交集的结论。

全部统计结论先固定参数，再在原实际数据律下取概率或弱极限，
由原支持对称性一致于确定支持，未知方向只付一次共同相等事件的失败概率。
没有参数随机化、独立 Poisson 替代实验、全数据期望或无界矩转移。
经典二阶导数检验、Fourier 小函数逼近、Baire 和质量分布各保留归属；
新增连接是精确阶乘相位、任意窄带的原 floor 区间下计数，以及同时守住所有尺度的通用参数构造。

## 追加锚（78 章后）

## 79. 实际信息增益的乘积正态波动与典型输出条件律

**定义 79.1（同一测量实现的信息波动）。** 保持第 75、77 章的原模型、
完整计数向量 $R$、精确标量 $T=t_x(R)$ 与实际先验纤维律 $P_x$。
对每个确定正噪声序列，令

$$
Y=T+\sigma_MG,\qquad L_M=\ln(1/\sigma_M)\to\infty,\qquad L_M=o(Q^3),
\tag{79.1}
$$

其中 $G$ 独立于完整原实验，服从标准正态。沿用第 77 章的
$\nu=2g_0>0$、方差参数密度 $\varphi_\nu$ 和实际输出密度 $f_x$，置

$$
\begin{aligned}
i_x(n,y)&=\ln\frac{\varphi_{\sigma_M}(y-t_x(n))}{f_x(y)},\\
H_M&=i_x(R,Y)-L_M,\qquad c=\tfrac12\ln\nu,\\
\Lambda_x(y)&=\ln\frac{f_x(y)}{\varphi_\nu(y)}.
\end{aligned}
\tag{79.2}
$$

测量核 $\varphi_{\sigma_M}$ 仍按标准差标记。$H_M$ 是自然单位的信息波动，
不是 Shannon 熵。$\mathbb E_x$ 积分同一个先验计数向量及其独立测量噪声。
下文所有随机环境结论均对每个上述噪声序列、两种实际平稳实验成立，
且一致于确定真实支持的原始数据概率；不对所有噪声序列同时取上确界。

**定理 79.2（实际联合波动律）。** 给定原始数据的条件律满足

$$
\mathcal L_x(T,Y,G,H_M)
 \Longrightarrow
 \mathcal L\left(\sqrt\nu Z,\sqrt\nu Z,G_\infty,
               c+\frac{Z^2-G_\infty^2}{2}\right),
\qquad Z\perp G_\infty,\quad Z,G_\infty\sim N(0,1).
\tag{79.3}
$$

精确含义是 $\mathbb R^4$ 上的有界 Lipschitz 距离在上述原数据概率中趋零。
标量 $H_M$ 的条件 Kolmogorov 距离也趋零。

证明。任意概率密度 $f$、严格正密度 $p$ 与 $u>0$ 满足有限不等式

$$
 \int_{\{|\ln(f/p)|>u\}}f(y)dy
 \le\frac{\|f-p\|_1}{1-e^{-u}}.
\tag{79.4}
$$

在 $f>e^up$ 上，$|f-p|\ge(1-e^{-u})f$；在不相交的
$f<e^{-u}p$ 上，$|f-p|\ge(e^u-1)f$。相加积分即得，零密度点不贡献质量。
定理 77.2 因而给

$$
\Pr_x\{|\Lambda_x(Y)|>u\}
 \le\frac{\|f_x-\varphi_\nu\|_1}{1-e^{-u}}\longrightarrow0.
\tag{79.5}
$$

这是实际输出质量加权的对数密度替换，不要求逐点相对误差一致趋零。
Gaussian 通道的精确恒等式为

$$
H_M=-\tfrac12\ln(2\pi)-\tfrac12G^2-\ln f_x(Y)
   =c+\frac{Y^2}{2\nu}-\frac{G^2}{2}-\Lambda_x(Y).
\tag{79.6}
$$

第 77 章给 $Y$ 的律在 TV 中趋于 $N(0,\nu)$，而
$|\mathbb E_xh(T)-\mathbb E_xh(Y)|\le\sigma_M\mathbb E|G|$
对每个一阶 Lipschitz 测试函数成立。因此 $T$ 条件弱收敛到同一正态。
每个有限纤维中 $T$ 与 $G$ 独立；它们的联合律就是该实际 $T$ 边缘与标准正态的乘积。
紧性、紧集上的有限乘积测试函数逼近给其联合弱极限。
再用 $Y-T=\sigma_MG\to0$、(79.5) 和 (79.6) 的连续映射，得到 (79.3)。
此处极限中出现的 $G_\infty$ 正是同一测量残差的极限，不能用一个独立拷贝替代。

上述证明适用于误差读数趋零的任意确定好环境序列。
各读数的一致原数据概率控制，再以反证选取失败环境序列，给所述随机环境结论。
没有把无界测试函数在异常数据上的值乘以其概率。
令 $U=(Z+G_\infty)/\sqrt2$、$V_*=(Z-G_\infty)/\sqrt2$，则
$U,V_*$ 是独立标准正态，且 $(Z^2-G_\infty^2)/2=UV_*$。
条件于非零的一个因子可知乘积无原子，故极限 CDF 连续。
在两尾和有限内部网格上用 CDF 单调性，弱收敛升级为标量 Kolmogorov 收敛。证毕。

**定理 79.3（信息矩、方差与同一残差的相关性）。** 对每个固定 $p>0$ 和整数 $k\ge0$，

$$
\begin{aligned}
\mathbb E_x|H_M|^p&\longrightarrow\mathbb E|c+\Xi|^p,\\
\mathbb E_xH_M^k&\longrightarrow\mathbb E(c+\Xi)^k,
\qquad\Xi=(Z^2-G_\infty^2)/2.
\end{aligned}
\tag{79.7}
$$

任意固定的 $(G,H_M)$ 混合多项式矩也收敛。以实际纤维均值中心化后，

$$
\begin{aligned}
\mathbb E_x(H_M-\mathbb E_xH_M)^{2m}&\longrightarrow[(2m-1)!!]^2,\\
\mathbb E_x(H_M-\mathbb E_xH_M)^{2m+1}&\longrightarrow0,\qquad m\ge1,\\
\mathbb E_x|H_M-\mathbb E_xH_M|^p
 &\longrightarrow\frac{2^p\Gamma((p+1)/2)^2}{\pi}.
\end{aligned}
\tag{79.8}
$$

特别地，$\operatorname{Var}_x i_x(R,Y)\to1$，四阶中心矩趋于 $9$，
$\operatorname{Cov}_x(H_M,G^2)\to-1$。

证明。必须另证一致可积，不能对 (79.3) 直接取矩。
固定确定 $B\ge1,K<\infty$，限制在
$\|f_x\|_\infty\le B$、$\mathbb E_xY^2\le K$ 的环境类。
对任意 $r,R>0$，

$$
\Pr_x\{-\ln f_x(Y)>r\}\le2Re^{-r}+K/R^2.
\tag{79.9}
$$

第一项是区间 $[-R,R]$ 内密度小于 $e^{-r}$ 部分的积分上界，第二项是二阶矩尾界。
取 $R=e^{r/3}$，得到

$$
\Pr_x\{(-\ln f_x(Y))_+>r\}\le(2+K)e^{-2r/3},\qquad
(\ln f_x(Y))_+\le\ln B.
\tag{79.10}
$$

对任意固定 $s>0$ 分层积分，
$\mathbb E_x[(-\ln f_x(Y))_+]^s\le(2+K)\Gamma(s+1)(3/2)^s$。
由 (79.6) 第一种表达及 $G$ 的精确 Gaussian 矩，便得

$$
\mathbb E_x|\ln f_x(Y)|^s\le C_{s,B,K},\qquad
\mathbb E_x|H_M|^s\le C'_{s,B,K}.
\tag{79.11}
$$

不要求 $G$ 与 $f_x(Y)$ 独立，也不要求 $Y$ 的任意高阶矩。
每个有限纤维的密度上确界和二阶矩均有限，因此全部信息绝对矩在每个纤维上存在。
这不证明其全原数据期望一致可积。

固定 $s>p$，(79.11) 给
$\mathbb E_x[|H_M|^p\mathbf1_{|H_M|>A}]\le C'_{s,B,K}A^{p-s}$。
对连续截断使用 (79.3)，再令 $A\to\infty$，得到固定环境类上的矩转移。
定理 77.2 与 $\mathbb E_xY^2=\mathbb E_xT^2+\sigma_M^2$
使这类环境的补集原数据概率任意小；最后令该失败容差趋零，证明 (79.7)。
对混合矩用 Hölder，把所需更高阶 $|G^jH_M^k|$ 矩分成精确 Gaussian 矩
与 (79.11)，同样得到一致可积。

经典正态旋转给 $\Xi=UV_*$，所以

$$
\mathbb Ee^{it\Xi}=(1+t^2)^{-1/2},\qquad
\mathbb E\Xi^{2m}=[(2m-1)!!]^2,\qquad
\mathbb E\Xi^{2m+1}=0,\qquad
\mathbb E|\Xi|^p=\frac{2^p\Gamma((p+1)/2)^2}{\pi}.
\tag{79.12}
$$

第一式可由条件于 $U$ 后积分 $e^{-t^2U^2/2}$ 直接得到。
均值收敛给 $\mathbb E_xH_M\to c$；展开整数中心矩并对绝对中心矩再用截断，证明 (79.8)。
同一联合极限中
$\operatorname{Cov}(c+(Z^2-G_\infty^2)/2,G_\infty^2)=-1$。
标量乘积表示识别的是分布，未把信息波动与测量残差变成独立变量。证毕。

**定理 79.4（典型输出的残差与信息条件 CDF）。** 令 $N$ 为用于描述目标核的标准正态，
$a_0(y)=c+y^2/(2\nu)$，并定义可测距离

$$
\begin{aligned}
D_M^G(x,y)&=\sup_{z\in\mathbb Q}
 \left|\Pr_x(G\le z\mid Y=y)-\Phi(z)\right|,\\
D_M^H(x,y)&=\sup_{z\in\mathbb Q}
 \left|\Pr_x(H_M\le z\mid Y=y)
            -\Pr\{a_0(y)-N^2/2\le z\}\right|.
\end{aligned}
\tag{79.13}
$$

则在相同一致原数据概率意义下，

$$
\int D_M^G(x,y)f_x(y)dy\longrightarrow0,\qquad
\int D_M^H(x,y)f_x(y)dy\longrightarrow0.
\tag{79.14}
$$

证明。输出边缘密度收敛不足以证明此式，需要保留计数向量与参考标量的联合关系。
取第 77 章同一分位耦合中的完整乘积向量 $R$、精确非中心 Gaussian 标量
$T^{\rm G}$ 和独立测量正态 $G_0$。设 $\mathsf B_x$ 是
$(R,Y_g)$ 的联合律，其中 $Y_g=T^{\rm G}+\sigma_MG_0$。
$T^{\rm G}$ 依赖构造该 $R$ 的分位随机数，不能另行独立抽取。
记第 77 章的 $D_M(x)=\mathbb E|T-T^{\rm G}|$、
$a_x=\|L_x-1\|_{L^2(\mathsf Q_x)}$，则完整向量变换及 Gaussian 平移界给

$$
\epsilon_x:=d_{\rm TV}(\mathcal L_x(R,Y),\mathsf B_x)
 \le\tfrac12a_x+\frac{D_M(x)}{\sqrt{2\pi}\sigma_M}\longrightarrow0.
\tag{79.15}
$$

TV 采用半 $L^1$ 约定。第一项仅改变完整计数律而保持精确通道，
第二项条件于同一耦合后改变平滑标量。
在两种联合律上使用相同可测映射 $h_x(n,y)=(y-t_x(n))/\sigma_M$。
实际律下它恰为 $G$；参考律下为 $G_0+\Delta_x$，其中

$$
\Delta_x=(T^{\rm G}-t_x(R))/\sigma_M,\qquad
\mathbb E_{\mathsf B_x}|\Delta_x|\le D_M(x)/\sigma_M.
\tag{79.16}
$$

令 $g_x^0$ 为第 77 章的无噪声参考密度、$g_x=g_x^0*\varphi_{\sigma_M}$。
参考 $(G_0,Y_g)$ 的密度为 $\varphi_1(u)g_x^0(y-\sigma_Mu)$。
由于 $\varphi_\nu'\in L^1$，有

$$
\begin{aligned}
\beta_x&:=d_{\rm TV}(\mathcal L_{\mathsf B_x}(G_0,Y_g),
                         N(0,1)\otimes N(0,\nu))\\
 &\le\tfrac12\|g_x^0-\varphi_\nu\|_1
       +\tfrac12\sigma_M\mathbb E|G_0|\,\|\varphi_\nu'\|_1\longrightarrow0,\\
\int g_x(y)d_{\rm TV}(\mathcal L_{\mathsf B_x}(G_0\mid Y_g=y),N(0,1))dy
 &\le2\beta_x.
\end{aligned}
\tag{79.17}
$$

最后一式把联合律与其实际参考输出边缘的乘积作比较，边缘收缩再付一次 $\beta_x$。
它尚未断言实际残差给定输出后正态。

为明确条件核转移，记实际与参考有限计数／输出联合密度为 $p_n(y),b_n(y)$，
边缘为严格正的 $f_x,g_x$。积分
$|p_n-f_xb_n/g_x|\le|p_n-b_n|+|1-f_x/g_x|b_n$ 并求和得到

$$
\int f_x(y)d_{\rm TV}(P_x(R\in\cdot\mid y),
                   \mathsf B_x(R\in\cdot\mid y))dy\le2\epsilon_x.
\tag{79.18}
$$

逐输出经映射 $h_x$ 推前不增 TV；把 $[0,1]$ 值参考距离的输出积分从 $g_x$
换到 $f_x$ 再至多付出 $\epsilon_x$。在 $|\Delta_x|\le b$ 上，
残差 CDF 夹在 $G_0$ 的两个平移 CDF 之间；补集的平均概率至多 $D_M/(b\sigma_M)$。
所以对每个固定 $b>0$，

$$
\int D_M^G(x,y)f_x(y)dy
 \le3\epsilon_x+2\beta_x+\frac b{\sqrt{2\pi}}
                         +\frac{D_M(x)}{b\sigma_M}.
\tag{79.19}
$$

第 77 章已证 $D_M/\sigma_M^2\to0$，足以支付这里的位移项。
先取原序列极限，再令 $b\downarrow0$，得 (79.14) 第一式。
多项式后验密度误差没有除以噪声。

精确恒等式 (79.6) 还给
$H_M=a_x^{shift}(Y)-G^2/2$，其中
$a_x^{shift}(y)=-\tfrac12\ln(2\pi)-\ln f_x(y)$，
$a_x^{shift}(y)-a_0(y)=-\Lambda_x(y)$。
若一个实随机变量的 CDF 距离 $\Phi$ 至多 $d$，其负半平方的 CDF 距离
$-N^2/2$ 的 CDF 至多 $2d$：用对称区间的两个端点；有原子时取左极限。
后者的统一连续模满足

$$
\omega_-(b)\le\min\{1,2\sqrt{b/\pi}\}.
\tag{79.20}
$$

因为 $N^2/2$ 的一个长度 $b$ 区间的原像总长度至多 $2\sqrt{2b}$，
再乘标准正态密度上界即可。故 (79.5) 给有限界

$$
\int D_M^H(x,y)f_x(y)dy
 \le2\int D_M^G(x,y)f_x(y)dy
    +\omega_-(b)+\frac{\|f_x-\varphi_\nu\|_1}{1-e^{-b}}.
\tag{79.21}
$$

依次令 $M\to\infty$、$b\downarrow0$ 证明第二式。
有限计数 Gaussian 混合核与有理 CDF 上确界保证可测性；右连续性使有理上确界等于实数上确界。
给定数据后再用 Markov，得到先验预测输出中坏 CDF 距离的质量趋零。证毕。

每个有限纤维、固定输出 $y$ 的实际残差只取有限个值
$\{(y-t_x(n))/\sigma_M:n\in\mathcal F_x\}$。
因此它与连续标准正态的 TV 距离恰为 $1$，与 (79.14) 的 CDF 结论并不矛盾。
参考连续残差的 TV 比较和实际有限残差的 CDF 比较承担不同作用。

本章信息矩结论均是纤维内积分作为原数据函数的收敛；未增加全原数据无界期望、
实际指数矩收敛、任意 $T,Y$ 高阶混合矩或大偏差结论。
输出条件结论使用 $f_x$，不等于已知固定真实支持下给定数据的单个 Gaussian 通道。
对有界联合测试或典型输出失败事件，原支持置换的传递作用保持计数、标量与信息不变，
可先在均匀先验上平均，再转为每个固定支持的无条件联合实验结论。
这不把其给定数据条件律改为先验条件律。

有限 Bayes 公式仍给第 77 章的
$\int H_2(p_x(\cdot\mid y))f_x(y)dy=h_x-\mathbb E_xi_x/\ln2$。
(79.7) 恢复平均信息的常数项，但典型输出的信息条件 CDF
不自动给逐输出后验 Shannon 熵集中；后者还涉及原先验惊奇度给定输出的条件均值。
精确 $h_x$ 不由其 $Q^5$ 主项代替。
已知反向按原方式对齐；未知方向只在原共同判向相等事件上转移，失败概率只进入概率界。
没有零噪声、$L_M\asymp Q^3$ 边界分类、计算效率或任意旧场的新增联合极限定理。

乘积正态分布及 Gaussian 信息密度的这种表示是经典结果。
本章新增连接是第 77 章的实际密度控制与同向量耦合如何同时支持
原模型的信息联合律、全部固定信息矩及典型输出条件 CDF；
不是一种新分布、通用连续性原则或全球原创性声明。

## 追加锚（79 章后）

## 80. 通用均值参数集的临界 Hausdorff 测度

**约定 80.1（固定原通用集合）。** 本章保持 (78.10) 的
$\mathcal U_0$ 及定义 78.1 的 $\mathcal U$ 完全不变：
可数均值带基 $\mathscr B$、各带预先选定的内带、原 floor 区间的开放中三分之一，
以及原合法 $Q_n$ 都不另选定义。
$E$ 与同步双根集 $E_2$ 仍取第 76 章的集合。
本章解决第 78 章尚未确定的临界测度，不把单带 limsup 的测度直接传给可数交集。

**定理 80.2（通用参数的局部临界无穷测度）。** 每个非空开区间
$J\subset(1/2,1)$ 满足

$$
\mathcal H^{2/3}(\mathcal U_0\cap J)
 =\mathcal H^{2/3}(\mathcal U\cap J)=\infty.
\tag{80.1}
$$

证明。固定非退化闭区间 $P_0\Subset J$，置于稍大的紧参数区间
$K\Subset(1/2,1)$ 中，记 $s=2/3$。
引理 78.3 对每个固定均值带 $B$ 提供：选中原区间中点间距至少 $c_KQ^{-2}$；
任意长 $t$ 的区间中点数至多 $C_K(1+tQ^2)$；
每个已经固定的非空区间 $V\subset K$，在所有充分晚的原合法层有至少
$a_B|V|Q^2$ 个选中中点，$a_B>0$，且其完整原区间可要求内含于 $V$。
起效层可以依赖 $B,V$，不要求对任意小区间一致。

选一个只依赖 $K$ 的小常数 $\kappa_0>0$，使以选中原区间中点为中心、长度

$$
\ell(Q)=\kappa_0Q^{-3}
\tag{80.2}
$$

的闭区间 $I(Q,j)$，严格内含于该原区间的开放中三分之一。
固定 $B$ 后，晚层的两种实际均值在整个选中原区间内都属于 $B$。
这些子区间不改变 $\mathcal U_0$ 的定义，只用于构造其中的紧子集。

先证明一个父区间可容纳任意有限多层。给定长度 $r$ 的闭父区间 $P\subset K$、
一个带 $B$ 和任意有限整数 $m$，可以从原合法层选择
$R_1<\cdots<R_m$，$R_{i+1}\ge2R_i$，并在每层取有限多个子区间，使

$$
\begin{aligned}
&\text{所有子区间的三倍同心区间 }3I\text{ 两两不交且内含于 }P,\\
&I\subset U_{n_i,B},\qquad |I|=\kappa_0R_i^{-3}<r/10,\\
&\eta_Br\le\sum_{I\text{ 属于第 }i\text{ 层}}|I|^s\le C_1r,\\
&\sum_{I\text{ 属于第 }i\text{ 层}}|I|\le C_2r/R_i,
\end{aligned}
\tag{80.3}
$$

其中 $\eta_B\in(0,1]$ 可以依赖带，$C_1,C_2$ 只依赖 $K,\kappa_0$。
各层均可要求至少两个子区间，且选用层晚于任意预先给定的有限层集。

具体构造如下。上计数界在 $rR_i^2\ge1$ 时使候选数至多 $CrR_i^2$，
故自动给 (80.3) 两个上界。
把首层取得足够晚，保证
$5C_2\sum_{i\ge1}R_i^{-1}\le10C_2/R_1<1/8$，
同时可再要求 $C_2\sum R_i^{-1}<1/40$；这不依赖有限 $m$ 的大小。
选第 $i$ 层前，从 $P$ 的开放中央一半删去前面所有闭区间 $5I$。
余下开放集 $V_i$ 是有限个区间之并，总长度大于 $3r/8$。
在其中选有限多个相互分离的闭核心，使其内部总长度至少 $r/4$。
它们与已删区间及父边界的距离均为正，并在选择下一合法层前固定。

对这些有限核心的稍小内部应用引理 78.3，取有限个起效阈值的最大值，
即可在所有充分晚合法层取得至少 $c_BrR_i^2$ 个中点。
再把该层取得足够晚，使其 $3I$ 全落在余下区域，并满足所有此前阈值。
同层中点间距 $c_KR_i^{-2}$ 大于三倍子长度，故三倍区间不交；
跨层不交由删去的 $5I$ 保证。
将下计数乘以 $\ell(R_i)^s=\kappa_0^sR_i^{-2}$，得 (80.3) 的下界。
此过程逐层只使用一个已固定有限开集上的下计数，不假定跨层相位独立。

设 $\mathcal C(P)$ 为这 $m$ 层的全部子区间，令

$$
T(P)=\sum_{I\in\mathcal C(P)}|I|^s.
\qquad
\eta_Bmr\le T(P)\le C_1mr,\qquad
\sum_{I\in\mathcal C(P)}|I|<r/40.
\tag{80.4}
$$

因此普通长度总和保持小，而临界内容可随有限层数任意增加。
这是每父区间只用一层时缺少的累积量。

现在事先排列 $B_1,B_2,\ldots$，使每个原基带出现无穷多次，
置 $\eta_k=\eta_{B_k}$。不假定这些正常数有共同正下界。
固定任意 $\varepsilon>0$，从 $\mu(P_0)=1$ 开始。
对第 $k-1$ 深度每个父区间 $P$，选择有限层数 $m(P)\ge2$ 满足

$$
\eta_km(P)|P|\ge\frac{\mu(P)}{\varepsilon\eta_{k+1}}.
\tag{80.5}
$$

下一带的密度常数已知，所以此要求在当前分割前可确定。
应用 (80.3) 构造 $B_k$ 子区间；本深度只有有限父区间，每个使用有限层，
所有层均可取得晚于此前深度的全部层。
把父质量按临界内容分给子区间：

$$
\mu(I)=\mu(P)\frac{|I|^s}{T(P)}.
\tag{80.6}
$$

由 (80.4)–(80.5)，

$$
\frac{\mu(P)}{T(P)}\le\varepsilon\eta_{k+1},\qquad
\mu(I)\le\varepsilon\eta_{k+1}|I|^s.
\tag{80.7}
$$

特别地，第 $k-1$ 深度的每个非根父区间满足
$\mu(P)\le\varepsilon\eta_k|P|^s$。
这个下一阶段密度因子不能删去，否则后面的中间尺度估计会留下 $1/\eta_k$。

子区间有限并形成非空嵌套紧集，令交集为 $K_\varepsilon$。
相容质量可先定义在有限分支路径空间，再经嵌套区间的唯一交点推前；
每深度长度缩小至少十倍，故给支撑于 $K_\varepsilon$ 的 Borel 概率测度。
三倍兄弟区间不交保证柱集相互分离，(80.7) 使单点质量为零。
每条分支的层号严格增加，每个基带被无穷多次访问，因此

$$
K_\varepsilon\subset\mathcal U_0\cap J.
\tag{80.8}
$$

每条分支确定一个固定参数；不同参数可用不同子序列，符合原集合定义。
该测度仅用来计算参数集大小，不是新增统计先验。

还须控制任意区间，不能只验柱集。若长 $t$ 的测试区间 $A$ 与同一父区间的
两个子区间相交，三倍区间不交给
$\operatorname{dist}(I,I')\ge|I|+|I'|$，
故每个被触及子区间的长度不超过 $t$。
在层 $R_i$，这些子中点位于长至多 $2t$ 的区间内；上计数界于是给其临界内容至多
$C\ell_i^s+C\kappa_0^st$。
相邻 $R_i$ 至少加倍，使 $\ell_i^s$ 至少缩小四倍；对全部 $\ell_i\le t$ 的层求和得

$$
\sum_{\substack{I\in\mathcal C(P)\\I\cap A\ne\varnothing, |I|\le t}}|I|^s
 \le C_3\{t^s+m(P)t\}.
\tag{80.9}
$$

常数不依赖层数、带、父区间或 $\varepsilon$。
该估计同时覆盖子长度、同层间距以及不同层之间的尺度，不需要筛选网格最大空隙界。

任取区间 $A$。若它与极限集至多交一个点，则 $\mu(A)=0$。
否则取 $A\cap K_\varepsilon$ 第一次落入两个子区间的树深度；
此前所有相交点位于唯一父区间 $P$。记 $r=|P|$，该分割使用第 $k$ 个带。
由 (80.6)、(80.9)，

$$
\mu(A)\le C_3\frac{\mu(P)}{T(P)}\{t^s+m(P)t\}.
\tag{80.10}
$$

若 $P$ 非根且 $t\ge r$，直接用
$\mu(A)\le\mu(P)\le\varepsilon\eta_kr^s\le\varepsilon t^s$。
若 $P$ 非根且 $t<r$，第一项由 (80.7) 至多为 $C_3\varepsilon t^s$；第二项满足

$$
\frac{\mu(P)m(P)t}{T(P)}
 \le\frac{\mu(P)t}{\eta_kr}
 \le\varepsilon r^{-1/3}t
 \le\varepsilon t^{2/3}.
\tag{80.11}
$$

最后一步使用 $t<r$，下一带的密度损失正好消去。
根区间 $P_0$ 的第一项仍由 (80.7) 控制；第二项至多为
$C_3t/(\eta_1|P_0|)$。
取

$$
t_0=\min\{|P_0|/2, (\varepsilon\eta_1|P_0|)^3\}>0,
\tag{80.12}
$$

则对所有长 $t<t_0$ 的区间都有

$$
\mu(A)\le C_J\varepsilon |A|^{2/3},
\tag{80.13}
$$

其中 $C_J$ 与 $\varepsilon$ 无关，阈值 $t_0$ 可依赖它。
任意直径小于 $t_0$ 的可数覆盖以闭区间包络替代，直径不变，单点质量为零，故
$1\le C_J\varepsilon\sum_i\operatorname{diam}(A_i)^{2/3}$。
取覆盖下确界并令覆盖尺度趋零，得到
$\mathcal H^{2/3}(K_\varepsilon)\ge(C_J\varepsilon)^{-1}$。
对每个 $\varepsilon>0$ 都在同一个 $\mathcal U_0\cap J$ 内作此构造，
令 $\varepsilon\downarrow0$，证明其临界测度无穷。
$\mathcal U_0\subset\mathcal U$ 给另一等式。证毕。

该证明使用经典质量传递原理的多层子构造：普通长度衰减而临界内容累积，
然后用任意小的 Frostman 常数证明无穷测度。
本章另承担预先固定的可数均值带、逐阶段变化的密度常数及原 floor 层的共同约束。
并未声称第 78 章原先的单层 Cantor 子集已具有正临界测度。

**推论 80.3（对数规范与排除同步双根）。** 对
$f_a(t)=t^{2/3}/(\ln(1/t))^a$ 的近零规范及任意非空开
$J\subset(1/2,1)$，

$$
\mathcal H^{f_a}(\mathcal U_0\cap J)
 =\mathcal H^{f_a}(\mathcal U\cap J)
 =\begin{cases}0,&a>0,\\\infty,&a\le0.
 \end{cases}
\tag{80.14}
$$

每个非空开 $J\subset(\beta_*,1)$ 还满足

$$
\mathcal H^{2/3}((\mathcal U_0\setminus E_2)\cap J)=\infty.
\tag{80.15}
$$

证明。$a>0$ 时，第 76 章的原合法层覆盖代价由
$\sum_n(\ln Q_n)^{-a}<\infty$ 控制，给 $\mathcal H^{f_a}(E)=0$；
包含关系把零测度传给两通用集合。
$a=0$ 用定理 80.2，$a<0$ 用近零 $f_a(t)\ge t^{2/3}$。
定理 76.5 给 $\dim_HE_2\le4/9$，从而 $\mathcal H^{2/3}(E_2)=0$。
从 (80.1) 删去该零测度部分不能留下有限测度，得 (80.15)。证毕。

(80.15) 加强了第 78 章整族单 Poisson 熵子序列律所适用参数集的大小。
每个这样的固定参数仍实现所有正实均值，整数目标仍可选两侧，
两种实验保持各自精确熵中心及共同确定均值子序列。
单根区间的相应通用参数集也有无穷临界测度。
没有新增统计近似、期望熵或无界矩转移。
$E_2$ 的非空性、锐利维数与指定同步均值继续未决；
小 Hausdorff 维数没有被用来推断 $E_2$ 贫性或差集余贫性。

本章只对所显示的对数规范族新增通用集合的完整零／无穷律，
没有把第 76 章任意规范的发散结论自动推广到 $\mathcal U_0$ 或 $\mathcal U$。
一般 large-intersection 类在严格次临界指数或严格更大规范上的交集性质，
也不直接承担这里等号处的临界测度。
所有对象保留原幅度、合法分母、完整组、floor、精确实际均值和固定参数的量词。

## 追加锚（80 章后）

## 81. 双根曲率、逐层同步单元与固定参数的算术障碍

**定义 81.1（原双根与精确等系数曲线）。** 保持第 72、74、76、78 章的原固定幅度、
原合法序列 $Q=Q_n$、$P=P_n$、$\lambda=Q^3$、全部取整、完整得分组和实际均值
$\bar c_{Q,j}^{\mathcal E}(\beta)$，$\mathcal E\in\{pair,path\}$。
令 $N=Q^2$，$I$ 为原率函数，$u_-=-b/\vartheta$，
$u_*>0$ 满足 $I(u_*)=I(u_-)$。
对 $0<u<u_*$，仍以 $\Psi(u)\in(u_-,0)$ 表示 $I(\Psi(u))=I(u)$ 的负根，
并记 $F(u)=\phi/(\phi+I(u))$。
定义自然对数相位 $\ell_Q=(\ln2)\Phi_Q$，其中 $\Phi_Q$ 是 (78.2) 的精确 Gamma 延伸：

$$
\ell_Q(x)=\ln2-z_0-\lambda
 +(k_0+Qx)\ln(a\lambda)+(l_0+Px)\ln(b\lambda)
 -\ln\Gamma(k_0+Qx+1)-\ln\Gamma(l_0+Px+1).
\tag{81.1}
$$

整数点有 $\ell_Q(j)=\ln\chi_{Q,j}$。本章的双根同步集仍是定义 76.1 的 $E_2$。
在参数 $\beta\in(\beta_*,1)$，两根记为 $u=u(\beta)>0$、$v=v(\beta)<0$。
原规模单元为

$$
\mathcal J_{Q,L}=
 \left(\frac{\phi Q^3}{(L+1)\ln2},\frac{\phi Q^3}{L\ln2}\right],
\qquad L\in\mathbb N.
\tag{81.2}
$$

在一个单元内，$M=2^L$、$q$、补偿和实际均值均不变；
任何两根的比较都使用同一个 $L$。

**定理 81.2（两条原等系数曲线的严格凸性）。** 原负根映射满足

$$
\Psi''(u)>0\quad(0<u<u_*),\qquad
\Psi':(0,u_*)\longrightarrow(-1,0)
\text{ 为严格递增双射}.
\tag{81.3}
$$

在任意固定 $U\Subset(0,u_*)$，充分大的原合法 $Q$ 下存在精确映射
$G_Q$，使 $\ell_Q(G_Q(x))=\ell_Q(x)$，$x/N\in U$，且 $G_Q(x)$ 位于负根邻域。
它严格凸，并满足

$$
\left\|N^{-1}G_Q(N\,\cdot)-\Psi\right\|_{C^2(U)}=O_U(Q^{-3}).
\tag{81.4}
$$

特别地，第 76 章局部曲率论证中不再需要排除内部拐点。

证明。原率函数具有

$$
I''(x)=\frac1{a+x}+\frac{\vartheta^2}{b+\vartheta x}>0,
\qquad
I'''(x)=-\frac1{(a+x)^2}-\frac{\vartheta^3}{(b+\vartheta x)^2}<0.
\tag{81.5}
$$

令 $K(x)=I'(x)^2-2I(x)I''(x)$。
有 $K(0)=0$、$K'(x)=-2I(x)I'''(x)>0$，$x\ne0$。
因此若 $I(u)=I(v)=t>0$、$u>0>v$，则

$$
\frac{I''(u)}{I'(u)^2}<\frac1{2t}
 <\frac{I''(v)}{I'(v)^2}.
\tag{81.6}
$$

隐式求导给

$$
\Psi''(u)=\frac{I'(u)^2}{I'(v)}
 \left[\frac{I''(u)}{I'(u)^2}-\frac{I''(v)}{I'(v)^2}\right]>0.
\tag{81.7}
$$

其中 $I'(v)<0$，括号也为负。零点附近写 $I(x)=x^2h(x)$，$h$ 为正解析函数，
用 $x\sqrt{h(x)}$ 的解析逆可延拓根交换，得 $\Psi'(0)=-1$。
当 $u\uparrow u_*$，$v\downarrow u_-$，$I'(v)\to-\infty$，
而 $I'(u)$ 有正的有限极限，故 $\Psi'(u)\to0$，得到 (81.3)。

再令 $V_Q=-\ell_Q$。经典 polygamma 级数给

$$
\begin{aligned}
V_Q''(x)&=Q^2\psi_1(k_0+Qx+1)+P^2\psi_1(l_0+Px+1)>0,\\
V_Q'''(x)&=Q^3\psi_2(k_0+Qx+1)+P^3\psi_2(l_0+Px+1)<0,\\
\psi_1(z)&=\sum_{m\ge0}(z+m)^{-2},\qquad
\psi_2(z)=-2\sum_{m\ge0}(z+m)^{-3}.
\end{aligned}
\tag{81.8}
$$

在零附近 $V_Q'(0)=O(Q^{-2})$，$V_Q''\asymp Q^{-1}$，
所以唯一极小点 $x_Q=O(Q^{-1})$。
对 $V_Q-V_Q(x_Q)$ 重复 (81.6)–(81.7)，得到其等值负支 $G_Q$ 的严格凸性。
固定紧根邻域内，两支存在性由率函数严格单调性及内部等值范围保证。

还需控制精确曲线与极限曲线的导数，而非对概率余项求导。
取 (76.13) 的 $A_Q$ 和 $d_{0,Q}=k_0-a\lambda$。
在稍大的正、负紧根邻域，删去与 $t$ 无关的项后，

$$
Q^{-3}V_Q(Nt)=I(t)-Q^{-3}A_Q(t)+O(Q^{-6}),
\tag{81.9}
$$

余项及其前三阶导数都有相同阶数界；$A_Q$ 的这些导数统一有界。
这一平滑 Stirling 界可由经典 Binet 余项直接核对。
在 $\ln\Gamma(z+1)$ 的 Stirling 公式中，余项为

$$
R(z)=\int_0^\infty e^{-zt}
 \left(\frac12-\frac1t+\frac1{e^t-1}\right)\frac{dt}{t}.
\tag{81.10}
$$

括号除以 $t$ 在正半轴有界，在零处奇异项抵消，
故积分求导给 $|R^{(m)}(z)|\le C_mz^{-1-m}$，$z\ge1$。
代入原计数 $k_0+QNt$、$l_0+PNt$ 后得到 (81.9)；
$P/Q-\vartheta$ 的贡献小于任何所需固定逆幂。
负支 $I'$ 在紧邻域与零分离，等值方程及两次隐式求导给 (81.4)。

严格递减的 $I''$ 还给 $I(-x)>I(x)$，只要 $x>0$ 且两点都在定义域，
因为两者分别为 $\int_0^x(x-t)I''(\mp t)\,dt$。
所以 $\Psi(x)>-x$；在固定内部根区间，$k=-j+O(1)$ 不能替代正确负根配对。
其率差与零分离，原系数比的对数为非零的 $Q^3$ 阶。证毕。

**定理 81.3（每个晚期合法尺度都存在实际双根同步单元）。**
对每个非空开区间 $J\Subset(\beta_*,1)$，存在 $H_J<\infty$，使每个充分大的原合法
$Q$ 都有整数 $j>0$、$k<0$、$L$，原单元 $\mathcal J_{Q,L}\subset J$，并且

$$
e^{-H_J}\le \bar c_{Q,j}^{\mathcal E}(\beta),
                \bar c_{Q,k}^{\mathcal E}(\beta)\le e^{H_J}
\quad(\beta\in\mathcal J_{Q,L},\ \mathcal E\in\{pair,path\}).
\tag{81.11}
$$

该单元长度与 $Q^{-3}$ 同阶。
正根代理均值可同时置于 $[2^{-1/2},2^{1/2}]$，实际均值与它相差相对 $o(1)$。
两索引均对应原完整窗口中的组。
量词是 $\forall J\ \exists H_J\ \forall Q\text{ 充分大}$；
本结论不交换前两个量词，也不由此断言 $E_2$ 非空。

证明。取紧正根区间 $U\Subset(0,u_*)$，使 $F(U)\subset J$。
由 (81.3)，选内部点 $u_0$ 和互素整数 $p,d$，使
$\Psi'(u_0)=p/d$、$d\ge1$、$-d<p<0$。
(81.4) 及正曲率保证唯一邻近点 $t_Q$ 满足

$$
G_Q'(t_Q)=p/d,
\qquad t_Q=Nu_0+O(Q^{-1}),
\qquad c/N\le G_Q''\le C/N
\tag{81.12}
$$

于 $t_Q$ 周围一个长度与 $N$ 同阶的固定相对邻域。
令 $h_Q(x)=G_Q(x)-(p/d)x$，于是 $h_Q'(t_Q)=0$。
选固定 $0<A<B$，使 $c(B^2-A^2)/2>4$。
在 $[t_Q+AQ,t_Q+BQ]$ 上，$h_Q$ 增加至少 $4$，而
$0<h_Q'\le CB/Q$。
仅取 $d$ 的整数倍 $j$；删去两个端点损失的函数值为 $O(d/Q)$，
相邻采样差满足

$$
0<h_Q(j+d)-h_Q(j)\le C_Bd/Q.
\tag{81.13}
$$

因此采样值最终跨过长度大于 $2$ 的区间。
选一个严格位于首尾值之间的整数 $m$，在跨过它的两个相邻采样点中取一个，得到
$|h_Q(j)-m|\le C_Bd/Q$。
因为 $pj/d$ 为整数，令 $k=pj/d+m$，便有

$$
j=Nu_0+O(Q),\qquad k<0,
\qquad |G_Q(j)-k|\le C_Bd/Q.
\tag{81.14}
$$

在负根紧邻域，$|\ell_Q'|\le C'Q$。
用精确等值方程及中值定理，得

$$
|\ln\chi_{Q,j}-\ln\chi_{Q,k}|\le C''d.
\tag{81.15}
$$

这是有理切线及格点同余类的经典构造在原精确系数曲线上的应用；
不需要固定分母的等分布断言。
取 $L$ 为 $-\log_2\chi_{Q,j}$ 的最近整数，则

$$
|L\ln2+\ln\chi_{Q,j}|\le\tfrac12\ln2,
\qquad
|L\ln2+\ln\chi_{Q,k}|\le C''d+\tfrac12\ln2.
\tag{81.16}
$$

两根在此确实使用同一个整数 $L$。
原 Stirling 式给

$$
L\ln2=Q^3[\phi+I(j/N)]+3\ln Q+O(1),
\qquad
\beta_{Q,L}=F(u_0)+O(Q^{-1}),
\tag{81.17}
$$

其中 $\beta_{Q,L}$ 是原单元中点；于是全单元最终包含于 $J$。
第 74 章的实际相对均值桥在该紧区间统一成立：

$$
\bar c_{Q,s}^{\mathcal E}(\beta)
 =2^L\chi_{Q,s}(1+o(1))+O(M^{-10}),\qquad s\in\{j,k\}.
\tag{81.18}
$$

因此 (81.16) 给出 (81.11)，稍增常数即可同时容纳两种实验及小余项。
原桥来自各实际实验的一、二标记行系数及全组尾界；
它没有将连续路径的行当成独立样本。
紧根邻域的线点均在原完整窗口内，单元内所有取整保持相同。

任何固定有限个不同有理切线可同时作此构造，得到极限位置不同的同步单元，
并对该有限集合使用一个有限上界。
这些切线中心稠密，但 (81.15) 的界含分母 $d$；
稠密性并未证明一个固定 $H$ 所允许的同步单元也稠密。
尤其取这些单元中点的极限，不能保证极限点属于宽度仅 $Q^{-3}$ 的单元。证毕。

**定理 81.4（固定参数的双相位判据与有理根排除）。** 固定
$\beta\in(\beta_*,1)$，设

$$
\rho_Q=\left\{\frac{\phi Q^3}{\beta\ln2}\right\},\qquad
\eta=\ln\frac{1+r}{1-r},\qquad
C_Q(x;\beta)=(1-\rho_Q)\ln2-d_{0,Q}\eta+A_Q(x),
\tag{81.19}
$$

其中 $A_Q$ 精确取 (76.13)。定义

$$
X_{Q,x}=Nx-\frac{3\ln Q}{QI'(x)}+\frac{C_Q(x;\beta)}{QI'(x)},
\qquad x\in\{u,v\}.
\tag{81.20}
$$

则 $\beta\in E_2$ 当且仅当存在一个有限常数 $C$，使无穷多个原合法层同时满足

$$
\|X_{Q,u}\|_{\mathbb R/\mathbb Z}\le C/Q,
\qquad
\|X_{Q,v}\|_{\mathbb R/\mathbb Z}\le C/Q.
\tag{81.21}
$$

若任一根为有理数，参数不属于 $E_2$。
因此以下两个可数稠密参数集都与 $E_2$ 不交：

$$
\{F(x):x\in\mathbb Q\cap(0,u_*)\},\qquad
\{\phi/(\phi+I(x)):x\in\mathbb Q\cap(u_-,0)\}.
\tag{81.22}
$$

证明。保留 $z_0=\phi Q^3+d_{0,Q}\eta$ 和原规模 floor，
在固定根邻域，(81.18) 与 Stirling 式给

$$
\ln\bar c_{Q,j}^{\mathcal E}(\beta)
 =Q^3[c(\beta)-I(j/N)]-3\ln Q+C_Q(j/N;\beta)+o(1)
\tag{81.23}
$$

于紧正均值范围；$c(\beta)=\phi(1-\beta)/\beta$。
反过来，若右端有界，则代理均值在固定正有限区间，(81.18) 也保证实际均值如此。
根处 $I'$ 非零；紧正均值首先迫使 $j-Nx=O(\ln Q/Q)$。
Taylor 二次项乘 $Q^3$ 后仅为 $O((\ln Q)^2/Q^3)$，故等价条件为

$$
QI'(x)(j-Nx)+3\ln Q-C_Q(x;\beta)=O(1).
\tag{81.24}
$$

这正是 (81.21) 的一个坐标。两根使用同一 $\rho_Q$ 和 $d_{0,Q}$；
一组统一界给两均值在同一紧正区间，再以共同子序列抽取极限，得到 $E_2$ 的定义。
若要求具体极限 $\theta_x>0$，相应的
$QI'(x)(X_{Q,x}-j)$ 必须趋于 $\ln\theta_x$，仅有有界性不够。

若 $x=A/B$ 为有理数，非零的 $|Nx-j|$ 至少为 $1/B$。
由 (81.24)，任何拟议紧正均值子序列最终只能满足 $Nx=j\in\mathbb Z$。
这时 (81.24) 退化为 $3\ln Q-C_Q(x;\beta)=O(1)$，
与 $C_Q$ 的有界性矛盾。
每侧率根到参数的映射连续且严格单调，故 (81.22) 各自可数稠密。
这没有排除另一根单独的均值复现，也不判定 $E_2$ 的类别或非空性。证毕。

**命题 81.5（有理切线处的截距约束与共同均值比）。** 固定参数如上，若
$\Psi'(u)=p/d$、$p,d$ 互素、$d>0$，令 $\zeta=dv-pu$。
若某原合法子序列同时实现实际均值极限 $\theta_+,\theta_->0$，对应整数索引为 $j,k$，则

$$
Q[dk-pj-N\zeta]
 =\frac d{I'(v)}
 \left[A_Q(v)-A_Q(u)+\ln\frac{\theta_+}{\theta_-}\right]+o(1).
\tag{81.25}
$$

特别地 $\|Q^2\zeta\|_{\mathbb R/\mathbb Z}=O(Q^{-1})$ 是必要条件。
若进一步 $d_{0,Q}\to d_\infty$、左端趋于 $D$，则

$$
\ln\frac{\theta_+}{\theta_-}
 =\frac{I'(v)}dD-A_{d_\infty}(v)+A_{d_\infty}(u),
\tag{81.26}
$$

$A_{d_\infty}$ 表示 (76.13) 将 $d_{0,Q}$ 替换为 $d_\infty$ 后的函数。

证明。由 (81.23)–(81.24)，两索引分别为

$$
\begin{aligned}
j&=Nu-\frac{3\ln Q}{QI'(u)}
 +\frac{C_Q(u;\beta)-\ln\theta_+}{QI'(u)}+o(Q^{-1}),\\
k&=Nv-\frac{3\ln Q}{QI'(v)}
 +\frac{C_Q(v;\beta)-\ln\theta_-}{QI'(v)}+o(Q^{-1}).
\end{aligned}
\tag{81.27}
$$

因为 $p/I'(u)=d/I'(v)$，组合 $dk-pj$ 时，$3\ln Q$ 项和共同规模 floor 项精确抵消，
仅留下 (81.25)。右端有界，$dk-pj$ 是整数，故必要条件成立；
再取极限即得 (81.26)。原计数 floor 在 $A_Q$ 中的贡献仍然保留。
这既未构造截距相位的适当子序列，也未补足 (81.21) 的另一个相位条件。

一个足以推出非空性的条件是：在某个固定紧内部参数范围内，存在一个共同 $H$，
使每个非空子开区间都在任意晚的原合法层含有满足 (76.7) 的双根单元。
在这些单元内部逐次选择闭子区间并令直径趋零，紧性给一个固定参数，
共同 $H$ 保证两均值在同一紧正区间，从而共同抽取正有限极限。
单条这样的无限嵌套分支已经足够。
定理 81.3 的 $H_J$ 没有提供这个共同界；原尺度再稀疏也不消去 (81.15) 的 $d$。
因此 $E_2$ 非空性、锐利维数及指定双均值的可实现性仍未决。证毕。

## 追加锚（本行以下为增补区）

## 82. 典型输出后验熵的首个随机响应

**定义 82.1（同一计数实现的逐输出后验熵）。** 保持第 75、77、79 章的两种原实际实验、
完整窗口计数向量 $R$、均匀大小 $q$ 支持先验下的精确纤维律 $P_x$、
精确中心标量 $T=t_x(R)$ 及同一个独立标准正态 $G$。
仍令 $Y=T+\sigma_MG$，$L_M=\ln(1/\sigma_M)\to\infty$、$L_M=o(Q^3)$。
沿用 $f_x$、$H_M=i_x(R,Y)-L_M$、$\nu=2g_0$、$c=\tfrac12\ln\nu$，并置

$$
\gamma=\int_{\mathbb R}\rho(t)\,dt,
\qquad S_x(n)=-\ln P_x(n),\qquad
h_x^{\rm nat}=\mathbb E_{P_x}S_x(R),
\qquad
\mathsf H_{{\rm post},x}(y)=-\sum_n p_x(n\mid y)\ln p_x(n\mid y).
\tag{82.1}
$$

本章熵均用自然单位，$\rho$ 精确取 (77.2)，$\delta=Q^{-1/2}$。
条件积分始终使用同一个先验计数向量及其测量噪声。
所有环境收敛均按第 77 章的量词，在两种原实验中分别一致于确定真实支持的数据概率。

**定理 82.2（实际后验熵的输出积分回归）。** 对每个上述确定噪声序列，有

$$
\int_{\mathbb R} f_x(y)
 \left|\sqrt\delta\,[\mathsf H_{{\rm post},x}(y)-h_x^{\rm nat}+L_M]
             -\frac\gamma\nu y\right|dy\longrightarrow0.
\tag{82.2}
$$

更强的中间结论是：若

$$
r_x(y)=\sqrt\delta\,\mathbb E_{P_x}
 [(S_x(R)-h_x^{\rm nat})\varphi_{\sigma_M}(y-T)],
\tag{82.3}
$$

则 $\|r_x+\gamma\varphi_\nu'\|_1\to0$。
首个非零随机修正的尺度为 $\delta^{-1/2}=Q^{1/4}$；
精确中心 $h_x^{\rm nat}$ 不得替换为仅知一阶等价的熵表达式。

证明。首先处理实际后验与乘积律之间的带权误差。
沿用第 77 章 $\mathsf Q_x,L_x,a_x,v_j,V,U_j,e_j$，
令 $\mathcal S=-\ln\mathsf Q_x(R)$、$\widetilde h=\mathbb E_{\mathsf Q_x}\mathcal S$、
$s=\mathcal S-\widetilde h$。
第 68 章全占据范围的二项信息矩估计与独立乘积结构给

$$
\mathbb E_{\mathsf Q_x}s^2\le CQ^2,\qquad
\mathbb E_{\mathsf Q_x}s^4\le CQ^4.
\tag{82.4}
$$

这些界包括空组及所有端点组。
具体地，紧参数范围的全点二项界使单组信息量减去
$\tfrac12\ln(n+1)$ 介于 $-C$ 与 $C+C(K-np)^2/(n+1)$ 之间；
Bernoulli 四阶、八阶中心矩分别控制它的二阶、四阶中心矩。
展开至多 $CQ^2$ 个独立中心变量的四次和即得 (82.4)。

实际正概率原子上 $S_x=\mathcal S-\ln L_x$，且

$$
\begin{aligned}
h_x^{\rm nat}-\widetilde h
 &=\mathbb E_{\mathsf Q_x}[(L_x-1)s]-D(P_x\Vert\mathsf Q_x),\\
0\le D(P_x\Vert\mathsf Q_x)&\le a_x^2,\qquad
\mathbb E_{P_x}(\ln L_x)^2\le Ca_x^2,\\
|h_x^{\rm nat}-\widetilde h|&\le CQa_x+a_x^2.
\end{aligned}
\tag{82.5}
$$

第二行用 $\ln t\le t-1$ 及 $0\le L_x\le C$；
$t(\ln t)^2/(t-1)^2$ 在零、一处连续延拓后有界。
零密度点没有实际质量。
定义 $r_x^{\rm prod}(y)=\sqrt\delta\,\mathbb E_{\mathsf Q_x}
[s\varphi_{\sigma_M}(y-T)]$，每个测量核的积分等于一，故

$$
\|r_x-r_x^{\rm prod}\|_1
 \le C\sqrt\delta(Qa_x+a_x+a_x^2)
 =O_{\mathbb P}(Q^{-7/4})\to0.
\tag{82.6}
$$

这里先消去 $Q^5$ 阶平均信息，才估计其 $O(Q)$ 波动。
这是整个计数向量的带权比较，未把实际后验的外部组当成独立变量。

接着使用第 77 章原量化耦合，核心半径为
$R_M^2=\sqrt{\lambda(L_M+\ln Q+1)}$，核心、外部指标分别记为 $\mathcal C,\mathcal O$。
保留同一组量化均匀变量、独立核心正态 $Z_j$、精确中心及外部中心截距，
使参考标量为

$$
T^{\rm G}=\delta^{-1/2}
 \left[\sum_{\mathcal C}(\sqrt{v_j}Z_j-e_j)^2
       -V_{\mathcal C}+\|e_{\mathcal O}\|^2\right].
\tag{82.7}
$$

对任意固定 $A\ge0,b>0$，(77.9) 实际还给

$$
Q^A\sigma_M^{-b}D_M(x)\to0,
\qquad D_M(x)=\mathbb E|T-T^{\rm G}|.
\tag{82.8}
$$

因为外部项的实际数据期望至多为
$CQ^{A+1/4}e^{bL_M}(e^{-cR_M^2}+Q^Ce^{-c\lambda})$，
核心项在 $V\le Q$ 上至多为 $CQ^{A+5/4}e^{bL_M-c_q\lambda/24}$。
两项均趋零，坏环境仅付其概率。
同一假设 $L_M=o(\lambda)$ 足够，未加入额外对数间隔。

两个平移 Gaussian 核的 $L^1$ 距离 $k$ 满足
$k\le\min(2,\sqrt{2/\pi}|T-T^{\rm G}|/\sigma_M)$，
故 $\mathbb Ek^2\le CD_M/\sigma_M$。
由 (82.4)，在保留完整计数向量的耦合上，

$$
\left\|r_x^{\rm prod}
 -\sqrt\delta\,\mathbb E[s\varphi_{\sigma_M}(\,\cdot-T^{\rm G})]\right\|_1
 \le C\sqrt\delta Q\sqrt{D_M/\sigma_M}\to0.
\tag{82.9}
$$

在乘积参考中，中心化的外部信息 $s_{\mathcal O}$ 与核心量化变量独立，
而精确中心与截距只是数据的函数，因此
$\mathbb E[s_{\mathcal O}\varphi_{\sigma_M}(y-T^{\rm G})]=0$。
这个精确抵消发生在 (82.6) 已支付实际总数依赖之后。

同一个量化耦合还给单组信息量的带权替换。
若 $X=(K-np)/\sqrt{np(1-p)}$、$Z$ 为其量化耦合正态、$d=np(1-p)$，则

$$
\mathbb E\left|[-\ln f_{n,p}(K)-\mathbb E(-\ln f_{n,p}(K))]
                         -\tfrac12(Z^2-1)\right|\le Cd^{-1/12}.
\tag{82.10}
$$

在 $|K-np|\le n^{5/8}$ 内，Stirling 与二项相对熵 Taylor 展开使信息量等于
$\tfrac12\ln(2\pi d)+X^2/2+O(n^{-1/8})$。
补集以全点界及四阶中心矩控制，绝对余项期望仍为 $O(n^{-1/8})$。
中心化至多使此误差加倍；第 75 章量化界
$\mathbb E|X-Z|^2\le Cd^{-1/6}$ 再给 $\mathbb E|X^2-Z^2|\le Cd^{-1/12}$。
核心最小 $d$ 至少为 $e^{c_q\lambda/2}$，组数至多 $CQ^2$，所以令

$$
F_M=\frac{\sqrt\delta}{2}\sum_{\mathcal C}(Z_j^2-1),\qquad
r_x^{\rm G}(y)=\mathbb E[F_M\varphi_{\sigma_M}(y-T^{\rm G})],
\tag{82.11}
$$

便有 $\|r_x-r_x^{\rm G}\|_1\to0$。
此处核心信息的替换没有逆噪声代价，因为测量核积分为一。
$F_M$ 的方差可能随移动核心半径增长，下一步不以其方差控制尾部。

令 $w_j=v_j/\sqrt\delta$、$c_j=e_j/\sqrt{v_j}$。
固定中心区 $|j\delta|\le1$ 的每个模四同余类都有至少 $c/\delta$ 个组，
且 $c\sqrt\delta\le w_j\le C\sqrt\delta$。
将核心按这四类分为独立和 $T_0,T_1,T_2,T_3$，外部截距并入 $T_0$。
在任意固定高概率环境类上，各 $\mathbb E|T_l|\le C$，并且其特征函数满足

$$
|\psi_l(t)|\le m_\delta(t):=(1+c\delta t^2)^{-c'/\delta}.
\tag{82.12}
$$

这由非中心平方正态因子的模长界直接得到，不要求每个 $c_j$ 小。
各类方差为 $2\sum w_j^2+4\sum w_j^2c_j^2\le C$，
均值绝对值至多 $\delta^{-1/2}\|e\|^2=o(1)$。
任意固定次多项式乘 $m_\delta$ 的积分统一有界、尾积分统一趋零：
在 $|t|\le\delta^{-1/2}$ 用 $e^{-c''t^2}$ 控制，
外部令 $z=\sqrt\delta|t|\ge1$，将幂指数分成两份，
一份产生 $e^{-c'''/\delta}$，另一份支付任意固定 $z$ 幂次。

全和及两个半和 $T_A=T_0+T_2$、$T_B=T_1+T_3$ 都可再分成两独立部分。
对特征函数求导，利用一部分的第一绝对矩、另一部分的衰减，得
$|\psi'(t)|\le Cm_\delta(t)$。
对各自密度 $g$，Fourier 反演与 Plancherel 因而给

$$
\int(1+y^2)|g'(y)|^2dy\le C,
\qquad \|g'\|_1\le C,
\qquad \int_{|y|>H}|g'(y)|dy\le CH^{-1/2}.
\tag{82.13}
$$

第二个加权平方积分来自 $\psi+t\psi'$ 的 $L^2$ 范数，
可先在弱 Fourier 导数意义理解，再由上述可积界识别为普通函数。
第 77 章的平方质量极限与精确中心估计使全和特征函数趋于 $e^{-\nu t^2/2}$。
用 (82.12) 支配 $|t|$ 加权 Fourier 积分，先得密度导数一致收敛；
再用 (82.13) 的尾界得到

$$
\|(g_x^0)'-\varphi_\nu'\|_1\to0,
\qquad \|g_x'-\varphi_\nu'\|_1\to0,
\quad g_x=g_x^0*\varphi_{\sigma_M}.
\tag{82.14}
$$

最后一步用卷积的 $L^1$ 收缩及 $\varphi_\nu'$ 的平移连续性。
一般有限 Wiener chaos 下的这一导数极限由 Herry–Malicet–Poly 的
Corollary 10(a) 直接覆盖；此处的经典 Fourier 推导还给出了两个独立半和所需的统一界。

经典 Gaussian 分部积分
$\mathbb E[(Z_j^2-1)h]=\mathbb E[Z_j\partial_jh]$ 给精确恒等式

$$
r_x^{\rm G}(y)=-\mathbb E[K_M\varphi_{\sigma_M}'(y-T^{\rm G})],
\qquad K_M=\sum_{\mathcal C}v_jZ_j(Z_j-c_j).
\tag{82.15}
$$

导数前系数是 $\sqrt\delta w_j=v_j$，决定了响应的正号及常数。
写 $K_M=V_{\mathcal C}+J_A+J_B$，其中两个 $J$ 是相应半核心上的中心贡献。
它们分别与对方半和独立，并满足

$$
\mathbb EJ_l=0,
\qquad \mathbb EJ_l^2=2\sum_{j\in l}v_j^2+\sum_{j\in l}v_je_j^2\le C\delta.
\tag{82.16}
$$

若 $h_B$ 为 $T_B$ 的密度，Fubini 与独立性把含 $J_A$ 的导数项写成
$\mathbb E[J_A(h_B'*\varphi_{\sigma_M})(y-T_A)]$，
其 $L^1$ 范数至多为 $\mathbb E|J_A|\|h_B'\|_1\le C\sqrt\delta$。
另一项相同。因此

$$
\|r_x^{\rm G}+V_{\mathcal C}g_x'\|_1\le C\sqrt\delta,
\qquad
\|r_x+\gamma\varphi_\nu'\|_1\to0.
\tag{82.17}
$$

第二式还用 $V_{\mathcal C}\to\gamma$，由原局部剖面和外部第一质量尾界成立。
这里将导数交给独立核心块的密度，未单独支付测量核的 $\sigma_M^{-1}$ 导数范数。

最后回到实际熵。第 77 章的 $L^1$ 密度收敛与实际输出二阶矩紧性给
$\|y(f_x-\varphi_\nu)\|_1\to0$：
在 $\mathbb E_xY^2\le K$ 上，分割 $|y|\le H$ 后误差至多为
$H\|f_x-\varphi_\nu\|_1+(K+\nu)/H$，依次取极限。
于是 (82.17) 及 $-\gamma\varphi_\nu'=(\gamma/\nu)y\varphi_\nu$ 给

$$
\int f_x(y)\left|\sqrt\delta\,\mathbb E_x[S_x-h_x^{\rm nat}\mid Y=y]
                              -\frac\gamma\nu y\right|dy\to0.
\tag{82.18}
$$

有限 Bayes 恒等式为

$$
\mathsf H_{{\rm post},x}(y)-h_x^{\rm nat}+L_M
 =\mathbb E_x[S_x-h_x^{\rm nat}\mid y]-\mathbb E_x[H_M\mid y].
\tag{82.19}
$$

第 79 章已证 $\mathbb E_x|H_M|=O_{\mathbb P}(1)$，
因此第二项乘 $\sqrt\delta$ 后的输出积分绝对值趋零，得到 (82.2)。
所有推导在高概率好环境进行，环境外只付概率；
未将无界熵乘以坏环境概率来声称期望收敛。证毕。

**推论 82.3（随机熵响应与平均熵的不同尺度）。** 在同一实际条件实现上，

$$
\mathcal L_x\!\left(T,Y,G,H_M,
 \sqrt\delta[\mathsf H_{{\rm post},x}(Y)-h_x^{\rm nat}+L_M]\right)
\Longrightarrow
\mathcal L\!\left(\sqrt\nu Z,\sqrt\nu Z,G_\infty,
 c+\tfrac12(Z^2-G_\infty^2),\frac\gamma{\sqrt\nu}Z\right),
\tag{82.20}
$$

其中 $Z,G_\infty$ 为独立标准正态；条件有界 Lipschitz 距离按定义 82.1 趋零。
因此尺度化熵响应有非退化 $N(0,\gamma^2/\nu)$ 极限，而

$$
\int f_x(y)\mathsf H_{{\rm post},x}(y)dy
 =h_x^{\rm nat}-L_M-c+o_{\mathbb P}(1).
\tag{82.21}
$$

证明。(82.2) 给第五坐标在实际输出下的条件 $L^1$ 替换；
将其与定理 79.2 的同一联合向量组合，连续映射即得 (82.20)。
(82.21) 是第 77 章平均信息式与有限 Bayes 恒等式。
平均修正为常数阶，不蕴含每个典型输出的熵在常数尺度集中。
在 bits 单位，(82.2) 的括号改为
$\mathsf H_{{\rm post},x}^{bits}-h_x^{bits}+L_M/\ln2$，系数改为 $\gamma/(\nu\ln2)$。
本推论未从 $L^1$ 或弱极限推出熵响应的方差收敛。证毕。

**定理 82.4（典型输出条件信息矩）。** 对每个固定整数 $k\ge1$，令
$H_*(y,N_0)=c+y^2/(2\nu)-N_0^2/2$，其中 $N_0$ 为描述目标核的标准正态，则

$$
\int f_x(y)\left|\mathbb E_x[H_M^k\mid y]
                       -\mathbb E_{N_0}H_*(y,N_0)^k\right|dy\to0.
\tag{82.22}
$$

任意固定 $p>0$ 的绝对 $p$ 阶矩也有同样结论。特别地

$$
\begin{aligned}
\int f_x\left|\mathbb E_x[H_M\mid y]-c-\frac{y^2}{2\nu}+\frac12\right|dy&\to0,\\
\int f_x\left|\operatorname{Var}_x(H_M\mid y)-\frac12\right|dy&\to0.
\end{aligned}
\tag{82.23}
$$

证明。这里需要新的实际高阶矩界，不能只用第 77 章二阶矩。
在乘积律下，中心 Bernoulli 单项展开中每个非零指标至少重复两次，故

$$
\mathbb E_{\mathsf Q_x}|U_j|^{2m}
 \le C_m\sum_{l=1}^m v_j^lB^{-2(m-l)}
 \le C_m(v_j^m+B^{2-2m}v_j).
\tag{82.24}
$$

令 $W_j=\delta^{-1/2}(U_j^2-v_j)$，则对固定整数 $k\ge2$，

$$
\sum_j\mathbb E_{\mathsf Q_x}|W_j|^k
 \le C_k\left[(\delta^{-1}\sum_jv_j^2)^{k/2}
              +\delta^{-k/2}B^{2-2k}V\right]=O_{\mathbb P}(1).
\tag{82.25}
$$

展开独立中心和的固定 $2m$ 阶矩，仅剩各指标至少出现两次的有限种分拆；
将不同指标的求和放大为不受限乘积，(82.25) 控制每种分拆，故
$\mathbb E_{\mathsf Q_x}|\sum_jW_j|^{2m}=O_{\mathbb P}(1)$。
Minkowski 与 (82.24) 还给

$$
(\mathbb E_{\mathsf Q_x}\|U\|^{2m})^{1/m}
 \le C_m[V+B^{-2+2/m}(CQ^2)^{1-1/m}V^{1/m}]=O_{\mathbb P}(1).
\tag{82.26}
$$

由 $\|e\|\le a_x\sqrt V$，精确中心线性项乘 $\delta^{-1/2}$ 后的固定阶矩趋零，
截距也趋零。对原精确展开使用非负密度上界 $L_x\le C$，得到

$$
\mathbb E_{P_x}|T|^{2m}=O_{\mathbb P}(1),\qquad
\mathbb E_x|Y|^{2m}=O_{\mathbb P}(1)
\quad\text{对每个固定 }m.
\tag{82.27}
$$

这通过密度支配证明，无 TV 搬运无界矩。
第 79 章对数密度尾界已给 $\mathbb E_x|H_M|^q=O_{\mathbb P}(1)$，任意固定 $q>0$。
(82.27) 同时使目标核满足
$\int f_x\mathbb E|H_*(y,N_0)|^qdy\le C_q(1+\mathbb E_x|Y|^{2q})=O_{\mathbb P}(1)$。
记 (79.14) 的输出积分条件 CDF 误差为 $\overline D_H(x)\to0$。
对固定 $q>p>0$，截断函数 $\min(|t|^p,A^p)$ 的总变差至多 $2A^p$，从而

$$
\begin{aligned}
&\int f_x\left|\mathbb E_x[|H_M|^p\mid y]-\mathbb E|H_*|^p\right|dy\\
&\quad\le2A^p\overline D_H(x)
 +A^{p-q}\left[\mathbb E_x|H_M|^q+\int f_x\mathbb E|H_*|^qdy\right].
\end{aligned}
\tag{82.28}
$$

在固定高概率矩界事件上先选大 $A$，再取规模极限，最后扩大事件，即得绝对矩结论；
带符号整数次幂的截断总变差也受相同阶数控制。
对条件方差，还须比较条件均值的平方。
两条件均值之差 $d(y)$ 的输出积分绝对值趋零，四阶矩积分紧，
所以 $\int f_xd^2\le A\int f_x|d|+A^{-2}\int f_x|d|^4\to0$。
Cauchy–Schwarz 控制均值平方之差，再用二阶矩结论与
$\operatorname{Var}(N_0^2/2)=1/2$，得到 (82.23)。

条件 Markov 不等式将这些积分结论转为典型输出结论。
所有后验仍是先验定义的纤维核，未改为确定支持的点质量后验。
有界失败概率经先验平均，再由保持两奇偶类的支持置换不变性，
传为确定支持的无条件联合实验结论；不据此平均无界数据误差。
已知反向按原方式对齐，未知方向在单个共同一致事件上传递全部坐标与同一个 $G$，
仅付该事件失败概率。
有限纤维中 $G\mid Y=y$ 仍为离散律，其对连续正态的 TV 距离为一。
本章不声称每个输出成立、增长阶矩一致、全局数据期望收敛，
也未确定去除 $Q^{1/4}$ 项后的后验熵常数项。证毕。

## 追加锚（本行以下为增补区）

## 83. 全剩余类同步界与 Liouville 多项式根的排除

**定义 83.1（精确切线的单侧相位）。** 沿用第 81 章的原模型、完整得分组、
实际均值 $\bar c_{Q,j}^{\mathcal E}(\beta)$、$N=Q^2$、等系数曲线 $G_Q$、
自然对数系数 $\ell_Q$、负根映射 $\Psi$ 和同一规模单元 $\mathcal J_{Q,L}$。
固定紧参数区间 $K\Subset(\beta_*,1)$，并一次选定稍大的内部根邻域。
对该邻域斜率范围中的既约有理数 $s=p/d$，$d\ge1$、$-d<p<0$，定义

$$
\Psi'(u)=s,\qquad G_Q'(t)=s,\qquad
h_Q(x)=G_Q(x)-sx,\qquad
\omega_{Q,p,d}=\lceil dh_Q(t)\rceil-dh_Q(t)\in[0,1).
\tag{83.1}
$$

这里 $t=Nu+O_K(Q^{-1})$。$h_Q$ 在 $t$ 达到严格极小值；
因此需要从上方接近整数的相位，不能以无向距离 $\|dh_Q(t)\|$ 替代 $\omega$。
切线分母 $d$ 是辅助整数，原计数分母始终为 $N$。

**定理 83.2（保留全部剩余类的实际同步界）。** 存在只依赖 $K$ 的常数 $C$，
使充分大的原合法 $Q$ 下，任意上述斜率且 $d\le Q^{2/3}$，都可找到原整数
$j>0$、$k<0$ 和一个共同规模整数 $L$，使该原单元位于选定参数邻域，并且

$$
\max_{\mathcal E\in\{pair,path\}}
\max_{i\in\{j,k\}}\left|\ln\bar c_{Q,i}^{\mathcal E}(\beta)\right|
\le C\left(1+\sqrt{d\omega_{Q,p,d}}+\frac{d^2}{Q}\right)
\quad(\beta\in\mathcal J_{Q,L}).
\tag{83.2}
$$

正根代理均值 $2^L\chi_{Q,j}$ 同时位于 $[2^{-1/2},2^{1/2}]$。
单元中点 $\beta_{Q,L}$ 满足

$$
|\beta_{Q,L}-F(u)|
\le C\left(\frac{\sqrt{\omega_{Q,p,d}/d}}Q
             +\frac d{Q^2}+\frac{\ln Q}{Q^3}\right).
\tag{83.3}
$$

特别地，最坏相位下的对数均值界是 $C(1+\sqrt d)$。
这改进定理 81.3 证明中的 $d$ 阶界；它仍不是固定参数的无限层复现。

证明。由定理 81.2，在固定的放大根邻域内
$c/N\le G_Q''\le C/N$。令 $m=\lceil dh_Q(t)\rceil$。
由于 $p,d$ 互素，恰有一个剩余类 $r\pmod d$ 满足

$$
pr+m\equiv0\pmod d.
\tag{83.4}
$$

这使 $m/d$ 成为该剩余类上的合法整数配对截距。
严格凸性给 $x_*\ge t$，使 $h_Q(x_*)=m/d$，并且积分曲率界给

$$
0\le x_*-t\le CQ\sqrt{\omega_{Q,p,d}/d}.
\tag{83.5}
$$

$\omega=0$ 时取 $x_*=t$。选取 $j\equiv r\pmod d$ 且 $|j-x_*|\le d/2$，
再令 $k=(pj+m)/d\in\mathbb Z$。两点仍在固定内部根邻域中，因而 $j>0>k$。
利用 $h_Q'(t)=0$ 和积分导数界，得到

$$
\begin{aligned}
|G_Q(j)-k|
 &=|h_Q(j)-m/d|\\
 &\le \frac C N\bigl(|x_*-t|+d\bigr)d
 \le C\left(\frac{\sqrt{d\omega_{Q,p,d}}}{Q}+\frac{d^2}{Q^2}\right),\\
|j-Nu|&\le C\left(Q\sqrt{\omega_{Q,p,d}/d}+d+Q^{-1}\right).
\end{aligned}
\tag{83.6}
$$

精确等值关系 $\ell_Q(G_Q(j))=\ell_Q(j)$ 及 $|\ell_Q'|\le CQ$ 因此给

$$
|\ln\chi_{Q,j}-\ln\chi_{Q,k}|
\le C\left(\sqrt{d\omega_{Q,p,d}}+d^2/Q\right).
\tag{83.7}
$$

取 $L$ 为 $-\ell_Q(j)/\ln2$ 的最近整数，即得正根代理均值界。
原 Stirling 公式给 $\beta_{Q,L}=F(j/N)+O_K(\ln Q/Q^3)$，从而得到 (83.3)。
这里对两根只选一次 $L$，其原 $q$、补偿和全部取整随该同一单元确定。

还须将代理均值接回实际依赖行。第 72、74 章的实际标记行系数估计与全组尾界给

$$
\bar c_{Q,i}^{\mathcal E}(\beta)
 =2^{L_0(\beta)}\chi_{Q,i}(1+o(1))+O(M^{-10}),
\tag{83.8}
$$

误差在选定截断、紧参数区间及两个实验上统一。
在本构造中代理均值位于 $\exp(\pm C Q^{1/3})$ 内，
而 $M=\exp(\Theta_K(Q^3))$，所以加性尾误差也可相对化。
这证明 (83.2)，没有以独立 Poisson 行替代实际路径。
最后 $\omega<1$ 且 $d^2/Q\le\sqrt d$，给最坏相位界。证毕。

上述证明直接积分精确曲率，没有丢弃自然 $O(Q)$ 指标窗口中的三阶项。
该项在 $G_Q$ 中为 $O(Q^{-1})$，乘回 $|\ell_Q'|=O(Q)$ 后可留下常数误差；
仅解一个未计余项的二次同余式不足以给指定均值比。

**推论 83.3（随区间长度变化的逐层界）。** 对固定 $K$ 中任意非空开子区间 $J$，
记其长度为 $\ell\le1$。存在只依赖 $K$ 的 $C,Q_0$，使每个原合法

$$
Q\ge\max(Q_0,C\ell^{-3/2})
\tag{83.9}
$$

都有一个原共同单元 $\mathcal J_{Q,L}\subset J$，其两根实际均值的对数绝对值
不超过 $C(1+\ell^{-1/2})$，对 pair/path 同时成立。

证明。$F$ 和 $\Psi'$ 在固定紧区间上有非零导数，
故 $J$ 的中部对应一个长度与 $\ell$ 同阶的斜率区间。
用分母 $\lceil C_1/\ell\rceil$ 的网格在该区间中部选有理数，再约分，
得 $d\le C_0/\ell$。条件 (83.9) 保证 $d\le Q^{2/3}$。
(83.3) 的位移和单元长度 $O(Q^{-3})$ 之和小于到 $J$ 边界的固定比例距离，
而 (83.2) 至多为 $C(1+\sqrt d)$，得到结论。
即使 $J$ 随 $Q$ 变化，只要满足 (83.9)，相对误差仍在上述
$\exp(\pm C Q^{1/3})$ 范围内统一成立。证毕。

**命题 83.4（可变分母的充分相位条件与精确对偶修正）。** 若一个固定 $A<\infty$ 满足

$$
d\le\sqrt Q,\qquad d\omega_{Q,p,d}\le A,
\tag{83.10}
$$

则定理 83.2 的对数均值界可统一取为 $C_K(1+\sqrt A)$，允许 $d$ 随层增长。
若能在一个固定紧参数区间内、每个父区间的固定内部子区间中，于任意晚期合法层找到
满足 (83.10) 的切线，则可构造一个 $E_2$ 中的固定参数。
这一相位复现前提尚未证明；仅一个保持同一有限界的嵌套分支也已足够。

更精确地，令 $g_Q(x)=N^{-1}G_Q(Nx)$，并定义

$$
\begin{aligned}
R_Q(x)&=\frac{A_Q(\Psi(x))-A_Q(x)}{I'(\Psi(x))},\\
\mathcal L(s)&=\Psi(u)-su,\qquad \Psi'(u)=s,\\
\mathcal L_Q(s)&=g_Q(u_Q)-su_Q,\qquad g_Q'(u_Q)=s.
\end{aligned}
\tag{83.11}
$$

$A_Q$ 精确取 (76.13)。则在固定紧斜率区间上统一有

$$
dh_Q(t)=Nd\mathcal L(p/d)+\frac dQ R_Q(u)+O_K(d/Q^4).
\tag{83.12}
$$

证明。代入 (83.2) 即得统一均值界；(83.3) 的位移至多为
$C_K(1+\sqrt A)(1/(Qd)+d/Q^2+\ln Q/Q^3)$，趋于零。
若所述相位前提成立，可逐次在父区间内部选共同单元，再取其内部闭子区间嵌套。
交点是同一个 $\beta$；两均值在同一紧正区间，抽取共同子序列即给正有限联合极限。
pair/path 的相对比较 (83.8) 保证同一极限对，全部规模取整仍共同。

为证对偶展开，在 (81.9) 中使用 Binet 余项的各固定阶导数界，
对精确等值方程隐式展开，得到

$$
g_Q=\Psi+Q^{-3}R_Q+O_K(Q^{-6})
\quad\text{于每个所需固定有限阶 }C^k\text{ 范数中}.
\tag{83.13}
$$

这里 $I'$ 在负根邻域与零分离；$P/Q-\vartheta$ 的误差小于任何所需固定逆幂。
因此 $u_Q=u-Q^{-3}R_Q'(u)/\Psi''(u)+O_K(Q^{-6})$。
在 $g_Q(u_Q)-su_Q$ 中，关于 $u_Q-u$ 的一阶项因 $\Psi'(u)=s$ 抵消，
故 $\mathcal L_Q(s)=\mathcal L(s)+Q^{-3}R_Q(u)+O_K(Q^{-6})$。
乘以 $Nd$ 即得 (83.12)。证毕。

当 $d\asymp\sqrt Q$ 时，(83.12) 的 $d/Q$ 修正与目标宽度 $A/d$ 同阶。
因此原率曲线的截距不能无条件替代精确 Gamma 截距。
推论 83.3 仅给随父区间缩小而增长的界，尚未建立 (83.10)，也不能据此交换量词证明 $E_2$ 非空。

**定理 83.5（所有有理多项式像的原率根排除）。** 令 $\Pi\in\mathbb Q[X]$ 为固定多项式。
若 $x=\Pi(\vartheta)\ne0$ 是某个固定允许参数的内部率根，则该根沿原合法序列
没有正有限实际均值子序列。特别地，在 $\beta\in(\beta_*,1)$ 时，若任一根如此表示，
则 $\beta\notin E_2$。这同时适用于原 pair/path 实验。

证明。定理 81.4 的实际均值局部化说明，正有限均值要求存在整数 $j$，使

$$
QI'(x)(j-Nx)+3\ln Q-C_Q(x;\beta)=O(1),
\tag{83.14}
$$

其中 $C_Q$ 精确取 (81.19)，在该固定内部根上一致有界。
特别地 $\|Nx\|=O(\ln Q/Q)$。若 $Nx$ 反而距离某个整数 $o(Q^{-1})$，
该整数留下的 $3\ln Q$ 漂移也无法由有界 $C_Q$ 消去。

记 $\vartheta_{n-1}=P_{n-1}/Q_{n-1}$。原十进制序列有

$$
\vartheta=\vartheta_{n-1}+Q_n^{-1}+\epsilon_n,
\qquad 0<\epsilon_n<2\,10^{-Q_n^5}.
\tag{83.15}
$$

取正整数 $D$ 清除 $\Pi$ 的全部系数分母。若 $m=\deg\Pi$，则充分大时

$$
A_n=D\left[Q_n^2\Pi(\vartheta_{n-1})
                  +Q_n\Pi'(\vartheta_{n-1})\right]\in\mathbb Z.
\tag{83.16}
$$

这是因为 $Q_n=10^{e_n}$、$e_n/e_{n-1}\to\infty$，
故每个 $Q_{n-1}^i$，$i\le m$，最终整除 $Q_n^2$，
而 $i\le m-1$ 时最终整除 $Q_n$。仅对固定多项式使用这条整除关系。
在 $\vartheta$ 处展开，并保留来自前一截断的导数项，得到

$$
Q_n^2\Pi(\vartheta)
 =\frac{A_n}{D}+\frac12\Pi''(\vartheta)
       -\frac{\Pi'''(\vartheta)}{3Q_n}+O_\Pi(Q_n^{-2}).
\tag{83.17}
$$

具体地，令 $h=\vartheta-\vartheta_{n-1}$，则
$\Pi(\vartheta)-\Pi(\vartheta-h)-h\Pi'(\vartheta-h)
=\Pi''(\vartheta)h^2/2-\Pi'''(\vartheta)h^3/3+O_\Pi(h^4)$；
以 $Q_n$ 替换 $Q_n^2h$ 的误差由 (83.15) 吸收。

原 $\vartheta$ 为超越数：若非零整数多项式 $R$ 在其上为零，
则充分大的不同有理逼近 $P_n/Q_n$ 不是 $R$ 的根，因而
$|R(P_n/Q_n)|\ge Q_n^{-\deg R}$；
均值定理及原尾界却给 $|R(P_n/Q_n)|\le C_R10^{-Q_n^5}$，矛盾。
若 $m\ge3$，$\Pi''(\vartheta)/2$ 因此无理，并且

$$
\Delta_\Pi=\operatorname{dist}(\Pi''(\vartheta)/2,D^{-1}\mathbb Z)>0.
\tag{83.18}
$$

由 $\mathbb Z\subset D^{-1}\mathbb Z$ 和 (83.17)，
$\|Q_n^2\Pi(\vartheta)\|\ge\Delta_\Pi/2$ 最终成立，与 (83.14) 矛盾。

若 $m\le2$，$\Pi''/2$ 为分母整除 $D$ 的有理数，其余高阶项消失。
(83.15) 更给

$$
Q_n^2\Pi(\vartheta)\in D^{-1}\mathbb Z+o(Q_n^{-B})
\quad\text{对每个固定 }B>0.
\tag{83.19}
$$

若 (83.14) 成立，离整数至少 $1/D$ 的非整数格点首先被排除，
所以相应 $D^{-1}\mathbb Z$ 格点必须就是整数，且 $j-Nx=o(Q^{-1})$。
(83.14) 遂变成 $3\ln Q-C_Q(x;\beta)=O(1)$，再次矛盾。证毕。

低次无理根的障碍是对格点过度精确的对齐不能补偿对数前因子；
次数至少三时，二阶导数留下与整数分离的固定相位。
这两种机制均使用原合法分母，而非以稀疏性猜测等分布。
排除集可数，包含第 81 章的稠密有理根参数族；它不穷尽允许参数。
有理函数在有理逼近处的分母未必整除十的幂，故本定理未扩展到任意有理函数或解析函数。

**例 83.6（两个明确的允许无理根参数）。** 令

$$
x_1=\vartheta/100,\qquad x_3=\vartheta^3/100,\qquad
\beta_i=\frac\phi{\phi+I(x_i)},\quad i\in\{1,3\}.
\tag{83.20}
$$

两者均严格位于 $(\beta_*,1)$，具有无理正根，并且均不属于 $E_2$。
为核对参数合法性，原级数给 $1/10<\vartheta<11/100$。
$f(r)=\ln(1+r)/[-\ln(1-r)]$ 严格递减，
而 $f(1-2^{-11})<1/11<\vartheta$，所以 $b>2^{-12}$。
由 $121\cdot4096<10^6$ 得 $\vartheta^2/100<b$，于是

$$
0<x_3<x_1<b/\vartheta<u_*.
\tag{83.21}
$$

最后一个严格不等式来自 $I(-t)>I(t)$ 及端点连续性，
在 $t=b/\vartheta$ 处给 $I(t)<I(u_-)$。

在 $\beta_1$，原 $Q_n$ 最终被 $100$ 整除，
$j_n=Q_nP_n/100$ 为整数，且 $Nx_1-j_n$ 小于每个固定逆幂。
精确均值展开给

$$
\bar c_{Q_n,j_n}^{\mathcal E}(\beta_1)
 =Q_n^{-3}\exp(C_{Q_n}(x_1;\beta_1)+o(1))\longrightarrow0.
\tag{83.22}
$$

它被两个固定正常数乘 $Q_n^{-3}$ 夹住；相邻格点的对数均值则相差 $Q_n$ 阶。
在 $\beta_3$，令 $t=\vartheta_{n-1}$，原整除关系给

$$
\{N x_3\}=\frac{3t}{100}+\frac1{100Q_n}+o(Q_n^{-B})
 \longrightarrow c_3:=3\vartheta/100\in(0,1).
\tag{83.23}
$$

充分大时没有模一回绕。令 $j_0=\lfloor Nx_3\rfloor$，则

$$
\begin{aligned}
\ln\bar c_{Q,j_0}^{\mathcal E}(\beta_3)&=QI'(x_3)c_3+o(Q)\to+\infty,\\
\ln\bar c_{Q,j_0+1}^{\mathcal E}(\beta_3)&=-QI'(x_3)(1-c_3)+o(Q)\to-\infty.
\end{aligned}
\tag{83.24}
$$

(83.8) 在这里仍可相对使用，因为这些均值为 $\exp(O(Q))$，远高于 $M^{-10}$ 尾误差。
两个例子的负根是否单独复现未由此判定，因而不能从正根排除推出整个熵残差趋于零。

本章保留原支持置换下的固定支持一致范围、原后验和方向对齐，
没有改变实际路径观测、完整得分组或共用规模取整。
先前的单根结果与 $E_2$ 维数上界保持原范围。
$E_2$ 的非空性、空性、锐利维数以及指定双均值的共同实现仍未解决。

## 追加锚（本行以下为增补区）

## 84. 噪声衰减校正后的后验熵常数项

**定义 84.1（同一输出上的精确熵余量）。** 沿用定义 82.1 的原计数向量、
精确后验中心标量 $T$、同一个测量噪声 $G$、$Y=T+\sigma_MG$、
先验预测密度 $f_x$ 及自然单位熵 $h_x^{\rm nat},\mathsf H_{{\rm post},x}$。
仍假定 $L_M=\ln(1/\sigma_M)\to\infty$、$L_M=o(Q^3)$，且
$\delta=Q^{-1/2}$、$\nu=2g_0$、$c=\tfrac12\ln\nu$。令

$$
\begin{aligned}
g_3&=\int_{\mathbb R}\rho(t)^3dt,
&A_M^\sigma&=\frac\gamma{\sqrt\delta(\nu+\sigma_M^2)},\\
C_*&=\nu-\frac{4\gamma g_3}{\nu},
&b_{\rm sur}&=\frac{C_*}{\nu^2},\qquad
b_{\rm ent}=b_{\rm sur}-\frac1{2\nu},\\
\mathcal H(y)&=b_{\rm ent}(y^2-\nu)-c,
&R_M^\sigma(y)&=\mathsf H_{{\rm post},x}(y)-h_x^{\rm nat}+L_M-A_M^\sigma y.
\end{aligned}
\tag{84.1}
$$

所有数据函数的收敛仍指：对每个 $\varepsilon>0$，在两种原实际实验中分别有
$\sup_{S:|S|=q}\Pr_S^{\mathscr X}(|F_M(\mathscr X)|>\varepsilon)\to0$。
条件期望始终使用均匀支持先验定义的纤维核，输出积分使用 $f_x(y)dy$。
本章精化第 82 章的首阶响应；其精确熵中心不换成 $Q^5$ 阶等价式。

**定理 84.2（带噪声方差的常数阶熵展开）。** 对定义 84.1 的每个噪声序列，

$$
\int f_x(y)|R_M^\sigma(y)-\mathcal H(y)|dy\longrightarrow0.
\tag{84.2}
$$

更强的中间结论为

$$
\int f_x(y)\left|
 \mathbb E_x[S_x(R)-h_x^{\rm nat}\mid Y=y]
 -A_M^\sigma y-b_{\rm sur}(y^2-\nu)\right|dy\longrightarrow0.
\tag{84.3}
$$

原 Gaussian 空间剖面 $\rho(t)=c_0e^{-\kappa t^2/2}$ 给

$$
\frac{\gamma g_3}{g_0^2}=\frac2{\sqrt3},\qquad
b_{\rm sur}=\frac{1-2/\sqrt3}{\nu},\qquad
\mathcal H(y)=\left(\frac12-\frac2{\sqrt3}\right)
                  \frac{y^2-\nu}{\nu}-\frac12\ln\nu.
\tag{84.4}
$$

特别地，常数阶中心化二次响应的系数为负。
分母中的 $\sigma_M^2$ 保留了测量对首阶回归的衰减；
仅有 $\sigma_M\to0$ 并不足以在常数精度删除它。

证明。先加强实际方差剖面的精度。
使用第 82 章同一个移动核心 $\mathcal C$、外部集 $\mathcal O$ 及 $v_j,e_j,a_x$，有

$$
V_{\mathcal C}=\sum_{\mathcal C}v_j=\gamma+O_{\mathbb P}(\delta),\qquad
\nu_M=2\delta^{-1}\sum_{\mathcal C}v_j^2=\nu+O_{\mathbb P}(\delta),\qquad
\delta^{-2}\sum_{\mathcal C}v_j^3\longrightarrow g_3.
\tag{84.5}
$$

为取得前两式的速率，取固定足够大的 $K$，令 $H_Q=\sqrt{K\ln Q}$。
由于原核心半径满足 $R_M^2/(L_M+\ln Q+1)\to\infty$，这个较小核心最终包含于 $\mathcal C$。
在 $|j\delta|\le H_Q$ 上，原信号 tuple 的 Stirling 展开给

$$
f_j^{\rm sig}
 =\frac{e^{-\kappa(j\delta)^2/2}}{2\pi\lambda\sqrt{ab}}
 \left[1+O\left(\frac{1+H_Q^3}{\sqrt\lambda}\right)\right].
\tag{84.6}
$$

两种 tuple 坐标仍是其均值的固定正比例，三阶率函数余项、取整误差及
Liouville 斜率误差都被右侧控制。精确混合均值满足
$m_j/(2qf_j^{\rm sig})=1+O(w+q/M)$，校准参数还满足
$\sup_{i\in J}|p_i-1/2|=O_{\mathbb P}(w+q^{-1/2}+q/M)$。
对实际一行、两行精度使用相对阈值 $Q^{-2}$ 的并合 Chebyshev，失败概率至多为

$$
CQ^4(1+H_Q/\delta)
 [e^{-c_q\lambda+O(H_Q^2+\ln Q)}+e_{\rm row}]\longrightarrow0.
\tag{84.7}
$$

路径行之间的依赖仍由原 $e_{\rm row}$ 项支付。在所得事件上

$$
\sup_{|j\delta|\le H_Q}
 \left|\frac{v_j}{\delta\rho(j\delta)}-1\right|
 \le O\left(Q^{-2}+\frac{1+H_Q^3}{\sqrt\lambda}\right)
      +O_{\mathbb P}(w+q^{-1/2}+q/M)=o_{\mathbb P}(\delta).
\tag{84.8}
$$

对 $\rho,\rho^2,\rho^3$，逐格积分导数给全直线 Riemann 和误差
不超过 $\delta\|g'\|_1=O(\delta)$。
选择足够大的 $K$，原第一、第二质量尾界使实际尾部
$\sum_{|j\delta|>H_Q}v_j$ 及 $\delta^{-1}\sum_{|j\delta|>H_Q}v_j^2$
均为 $o_{\mathbb P}(\delta^2)$：先对确定 tuple 占据数作期望界，再用 Markov；
不在坏环境上平均无界量。三次尾和则用核心内 $\max v_j\le C\delta$，
有 $\delta^{-2}\sum_{\mathcal C,|j\delta|>H_Q}v_j^3\le C\sum_{|j\delta|>H_Q}v_j$。
这证明 (84.5)，无需三行独立性或第三占据矩。

接着保留第 82 章比较中的未尺度化误差。定义带符号密度

$$
q_x(y)=\mathbb E_{P_x}[(S_x-h_x^{\rm nat})\varphi_{\sigma_M}(y-T)],\qquad
q_G(y)=\mathbb E[S_G\varphi_{\sigma_M}(y-T^{\rm G})],\qquad
S_G=\frac12\sum_{\mathcal C}(Z_j^2-1).
\tag{84.9}
$$

这里 $T^{\rm G}$ 正是 (82.7)，精确中心和外部中心截距均保留。
(82.4)—(82.10) 在乘 $\sqrt\delta$ 之前分别给

$$
\begin{aligned}
\|q_x-q_x^{\rm prod}\|_1
 &\le C(Qa_x+a_x+a_x^2)=O_{\mathbb P}(Q^{-3/2}),\\
\|q_x^{\rm prod}-\mathbb E[s\varphi_{\sigma_M}(\,\cdot-T^{\rm G})]\|_1
 &\le CQ\sqrt{D_M/\sigma_M}\longrightarrow0,\\
\|q_x-q_G\|_1&\longrightarrow0.
\end{aligned}
\tag{84.10}
$$

第二行的额外 $Q$ 因子由 (82.8) 支付；
第三行还使用乘积律下外部中心信息的精确抵消，以及核心量化信息误差的指数小界。
这是整个实际后验的中心信息比较，不是由无权 TV 推出无界信息量的收敛。

令 $g_x$ 为 $T^{\rm G}+\sigma_MG_0$ 的辅助密度。
同一耦合还给 $\epsilon_x:=\|f_x-g_x\|_1\le a_x+CD_M/\sigma_M$。
实际与参考输出的二阶矩有界于固定高概率环境类，故 Cauchy–Schwarz 给

$$
\|y(f_x-g_x)\|_1
 \le [\mathbb E_xY^2+\mathbb E(T^{\rm G}+\sigma_MG_0)^2]^{1/2}\epsilon_x^{1/2},
\qquad
\delta^{-1/2}\|y(f_x-g_x)\|_1\longrightarrow0.
\tag{84.11}
$$

最后一式用 $\delta^{-1}a_x=O_{\mathbb P}(Q^{-2})$ 及 (82.8)。
因此从参考密度返回实际密度时，大小为 $\delta^{-1/2}$ 的线性系数也已付清。

现在建立二阶密度导数的统一界。仍按第 82 章模四分块，令
$T_A=T_0+T_2$、$T_B=T_1+T_3$。
对全和及这两个半和的特征函数，(82.12) 及独立分块给
$|\psi(t)|\le m_\delta(t)$、$|\psi'(t)|\le Cm_\delta(t)$。
于是对各自密度 $h$ 和 $k=1,2$，Plancherel 给

$$
\begin{aligned}
\|h^{(k)}\|_2^2+\|yh^{(k)}\|_2^2
 &\le C_k\int\big[|t|^{2k}|\psi(t)|^2
       +|kt^{k-1}\psi(t)+t^k\psi'(t)|^2\big]dt\le C_k,\\
\|h^{(k)}\|_1&\le C_k,\qquad
\int_{|y|>H}|h^{(k)}(y)|dy\le C_kH^{-1/2}.
\end{aligned}
\tag{84.12}
$$

Fourier 反演将弱导数识别为连续导数。
全和的特征函数趋于 $e^{-\nu t^2/2}$；多项式加权的 $m_\delta$ 支配、
(84.12) 的空间尾界及卷积收缩共同给

$$
\|g_x^{(k)}-\varphi_\nu^{(k)}\|_1\longrightarrow0,
\qquad \|g_x^{(k)}\|_1\le C_k,\qquad k=1,2.
\tag{84.13}
$$

一般导数极限仍由 Herry–Malicet–Poly 的既有理论覆盖；
显式半块界用于下一步，没有 $\sigma_M^{-2}$ 代价。

令 $w_j=v_j/\sqrt\delta$、$c_j=e_j/\sqrt{v_j}$，并置

$$
\begin{aligned}
a_0&=\sum_{\mathcal C}w_j=V_{\mathcal C}/\sqrt\delta,\\
\mu_G&=\mathbb ET^{\rm G}=\delta^{-1/2}\|e\|^2,\\
v_G&=\operatorname{Var}(T^{\rm G})
 =2\sum_{\mathcal C}w_j^2+4\sum_{\mathcal C}w_j^2c_j^2,\\
\Lambda_G&=v_G+\sigma_M^2,\qquad A_G=a_0/\Lambda_G.
\end{aligned}
\tag{84.14}
$$

逐项非中心量 $c_j$ 不要求小；需要的是
$\max w_j\le C\sqrt\delta$、$\sum w_j^2\le C$ 及
$\sum w_j^2c_j^2=\delta^{-1}\sum v_je_j^2\le C\|e\|^2=O_{\mathbb P}(a_x^2)$。
好环境上 $\Lambda_G$ 一致远离零。

第一次 Gaussian 分部积分给

$$
\begin{aligned}
q_G(y)&=-\mathbb E[\mathcal A\varphi_{\sigma_M}'(y-T^{\rm G})],\\
\mathcal A&=\sum_{\mathcal C}w_jZ_j(Z_j-c_j),\qquad
\mathcal A_c=\mathcal A-a_0
 =\sum_{\mathcal C}[w_j(Z_j^2-1)-w_jc_jZ_j].
\end{aligned}
\tag{84.15}
$$

另一方面，对任意适当光滑测试函数 $h$，逐坐标分部积分给
$\mathbb E[(T^{\rm G}-\mu_G)h(T^{\rm G})]=\mathbb E[\mathcal B h'(T^{\rm G})]$，其中

$$
\mathcal B=2\sum_{\mathcal C}w_j^2(Z_j-c_j)(Z_j-2c_j),\qquad
\mathcal B_c=\mathcal B-v_G
 =\sum_{\mathcal C}[2w_j^2(Z_j^2-1)-6w_j^2c_jZ_j].
\tag{84.16}
$$

取 $h(t)=\varphi_{\sigma_M}(y-t)$，并用
$(y-t)\varphi_{\sigma_M}(y-t)=-\sigma_M^2\varphi_{\sigma_M}'(y-t)$，得到精确含噪声恒等式

$$
(y-\mu_G)g_x(y)=-\Lambda_Gg_x'(y)
 -\mathbb E[\mathcal B_c\varphi_{\sigma_M}'(y-T^{\rm G})].
\tag{84.17}
$$

消去 (84.15) 中的 $g_x'$，有
$q_G-A_G(y-\mu_G)g_x=-\mathbb E[(\mathcal A_c-A_G\mathcal B_c)\varphi_{\sigma_M}']$。
写

$$
\mathcal A_c-A_G\mathcal B_c
 =\sum_{\mathcal C}[h_j(Z_j^2-1)+k_jZ_j],\qquad
h_j=w_j-2A_Gw_j^2,\quad k_j=-w_jc_j+6A_Gw_j^2c_j.
\tag{84.18}
$$

第二次分部积分给

$$
\begin{aligned}
q_G(y)-A_G(y-\mu_G)g_x(y)
 &=\mathbb E[\mathcal C_M\varphi_{\sigma_M}''(y-T^{\rm G})],\\
\mathcal C_M&=\sum_{\mathcal C}
 [2h_jw_jZ_j(Z_j-c_j)+2k_jw_j(Z_j-c_j)].
\end{aligned}
\tag{84.19}
$$

固定 $\sigma_M>0$ 时这些核导数有界，Gaussian 多项式可积，故两次操作均合法。
其均值和中心部分分别为

$$
\begin{aligned}
C_M=\mathbb E\mathcal C_M
 &=2\sum w_j^2-4A_G\sum w_j^3
       +2\sum w_j^2c_j^2-12A_G\sum w_j^3c_j^2,\\
\mathcal C_M-C_M
 &=\sum [d_j(Z_j^2-1)+l_jZ_j],\\
d_j&=2w_j^2-4A_Gw_j^3,\qquad
l_j=-4w_j^2c_j+16A_Gw_j^3c_j.
\end{aligned}
\tag{84.20}
$$

此处 $d_j$ 只表示多项式系数。
因为 $A_G=O(\delta^{-1/2})$，两个半核心上相应中心贡献 $J_A,J_B$ 均满足

$$
\mathbb EJ_l^2
 \le C\sum(w_j^4+w_j^4c_j^2)
 \le C\delta\left(\sum w_j^2+\sum w_j^2c_j^2\right)\le C\delta.
\tag{84.21}
$$

条件于 $A$ 半块后，将二阶导数交给独立的 $B$ 半块密度 $h_B$。
Fubini、(84.12) 与卷积收缩使相应 $L^1$ 范数至多为
$\mathbb E|J_A|\|h_B''\|_1\le C\sqrt\delta$；另一项相同。因此

$$
\|q_G-A_G(y-\mu_G)g_x-C_Mg_x''\|_1\le C\sqrt\delta.
\tag{84.22}
$$

这一步不使用 $S_G$ 随核心增长的方差，也不支付测量核的逆噪声导数范数。
由 (84.5)，非中心修正为 $O_{\mathbb P}(a_x^2)$，且

$$
4A_G\sum w_j^3
 =\frac{4V_{\mathcal C}}{\Lambda_G}\delta^{-2}\sum v_j^3,
\qquad C_M\longrightarrow C_*.
\tag{84.23}
$$

此外 (84.5) 给 $v_G=\nu+O_{\mathbb P}(\delta)+O_{\mathbb P}(a_x^2)$，从而

$$
|A_G-A_M^\sigma|
 =O_{\mathbb P}(\sqrt\delta+\delta^{-1/2}a_x^2)\longrightarrow0,
\qquad |A_G\mu_G|=O_{\mathbb P}(\delta^{-1}a_x^2)\longrightarrow0.
\tag{84.24}
$$

现在用 (84.10)—(84.13)、(84.22)—(84.24) 回到实际密度，得到

$$
\|q_x-A_M^\sigma y f_x-C_*\varphi_\nu''\|_1\longrightarrow0.
\tag{84.25}
$$

每项误差均已单独支付：带权后验比较、参考回归余项、确定系数替换、
精确中心截距，以及 (84.11) 中被大系数放大的密度差。
实际四阶输出矩由 (82.27) 给出，结合 $\|f_x-\varphi_\nu\|_1\to0$，分割 $|y|\le H$ 后得到
$\|(1+y^2)(f_x-\varphi_\nu)\|_1\to0$。
又 $\varphi_\nu''=(y^2-\nu)\varphi_\nu/\nu^2$，所以 (84.25) 等价于 (84.3)。
只在已带 $f_x$ 权的积分内除以严格正密度，没有断言低密度输出上的逐点回归。

最后由 (82.23) 的实际条件信息均值，

$$
\int f_x(y)\left|\mathbb E_x[H_M\mid y]
                         -c-\frac{y^2-\nu}{2\nu}\right|dy\longrightarrow0.
\tag{84.26}
$$

将其从 (84.3) 减去，再使用精确 Bayes 恒等式 (82.19)，即得 (84.2)。
积分 $\rho,\rho^2,\rho^3$ 得到 (84.4)。全程保留同一实际向量、观测和方向一致事件。
未知方向仅传递有界失败概率，不将无界熵乘以方向失败概率。证毕。

**命题 84.3（删除噪声校正的精确边界与实际反例）。** 令

$$
R_M^0(y)=\mathsf H_{{\rm post},x}(y)-h_x^{\rm nat}+L_M
                      -\frac\gamma{\nu\sqrt\delta}y,\qquad
 d_M=\frac{\sigma_M^2}{\sqrt\delta},\qquad
 k_M=\frac{\gamma d_M}{\nu(\nu+\sigma_M^2)}.
\tag{84.27}
$$

则对原完整噪声范围始终有

$$
\int f_x(y)|R_M^0(y)+k_My-\mathcal H(y)|dy\longrightarrow0.
\tag{84.28}
$$

$R_M^0$ 本身具有 (84.2) 的同一二次剖面，当且仅当 $\sigma_M^2=o(\sqrt\delta)$。
若 $d_M\to d<\infty$，其剖面为 $\mathcal H(y)-\gamma d y/\nu^2$。
若 $d_M\to\infty$，则对每个固定 $K<\infty$，

$$
\Pr_x(|R_M^0(Y)|\le K)\longrightarrow0.
\tag{84.29}
$$

例如合法噪声 $\sigma_M=Q^{-1/16}$ 满足 $L_M=(\ln Q)/16=o(Q^3)$，
而 $d_M=Q^{1/8}\to\infty$；它是原实际模型中常数阶余量不紧的反例。

证明。精确系数差为
$A_M^\sigma-\gamma/(\nu\sqrt\delta)=-k_M$，直接给 (84.28)。
记其积分误差为 $E_M(x)\to0$，两次三角不等式给

$$
\left|\int f_x|R_M^0-\mathcal H|-k_M\mathbb E_x|Y|\right|\le E_M(x).
\tag{84.30}
$$

实际加权密度收敛给 $\mathbb E_x|Y|\to\sqrt{2\nu/\pi}>0$，
而 $k_M\to0$ 恰等价于 $d_M\to0$，于是得充要条件及有限比率情形。
若 $k_M\to\infty$，由实际二阶矩紧性，

$$
\mathbb E_x|R_M^0(Y)/k_M+Y|
 \le\frac{\mathbb E_x|\mathcal H(Y)|+E_M(x)}{k_M}\longrightarrow0.
\tag{84.31}
$$

所以对 $\eta>0$，

$$
\Pr_x(|R_M^0(Y)|\le K)
 \le\Pr_x(|Y|\le\eta+K/k_M)
    +\eta^{-1}\mathbb E_x|R_M^0(Y)/k_M+Y|.
\tag{84.32}
$$

先取规模极限，再令 $\eta\downarrow0$；极限 Gaussian 在零点无原子，得到 (84.29)。
这是实际条件概率的逃逸结论，没有从参考方差发散推断不紧。
噪声比率振荡时仍适用 (84.28)，可分别取有限比率或发散比率子列。
完整分母覆盖任意慢的噪声衰减；固定阶 Taylor 截断不具有这一保证。证毕。

**推论 84.4（同一实现上的二次极限与纤维平均）。** 条件有界 Lipschitz 距离按定义 84.1 趋零地，

$$
\mathcal L_x\!\left(T,Y,G,H_M,R_M^\sigma(Y)\right)
\Longrightarrow
\mathcal L\!\left(\sqrt\nu Z,\sqrt\nu Z,N,
 c+\frac{Z^2-N^2}{2},
 \left(\frac12-\frac2{\sqrt3}\right)(Z^2-1)-c\right),
\tag{84.33}
$$

其中 $Z,N$ 独立标准正态。并且
$\mathbb E_xR_M^\sigma(Y)\to-c$；即使命题 84.3 的未校正余量逃逸，
仍有 $\mathbb E_xR_M^0(Y)\to-c$。

证明。(84.2) 提供同一联合向量最后坐标的条件 $L^1$ 替换，
与第 79 章的信息联合极限组合即得 (84.33)。实际矩界给
$\mathbb E_xY^2\to\nu$，所以 $\mathbb E_x\mathcal H(Y)\to-c$。
未校正情形只差 $-k_M\mathbb E_xY$。精确中心展开与选中密度比较给

$$
\mathbb E_xY=\mathbb E_{P_x}T
 =O_{\mathbb P}(a_x+\delta^{-1/2}a_x^2),\qquad k_M\le C\delta^{-1/2},
\tag{84.34}
$$

故该差仍趋零。稳定的纤维平均与输出余量不紧可以同时成立。
本章只证明余量的输出积分 $L^1$，未证明其方差或更高矩收敛。
有界误差事件可先验平均，再以奇偶类内支持置换不变性传为
确定支持的无条件联合结论；这不把确定支持条件输出律等同于先验预测律。
所有熵换为 bits 时，将熵、$L_M$、线性系数及二次剖面同时除以 $\ln2$。
未断言每个输出、无界数据平均、$L_M$ 与 $Q^3$ 同阶的噪声、零噪声、
有限精度解码效率或实验等价性。证毕。

## 追加锚（本行以下为增补区）

## 85. 有理函数根的实际熵正则性与对偶计数的格约束

**定义 85.1（前一有理截断上的二阶预测量）。** 保持第 81、83 章的
原 $\vartheta$、合法 $Q=Q_n$、$N=Q^2$、完整得分组及实际均值
$\bar c_{Q,j}^{\mathcal E}(\beta)$。固定 $F\in\mathbb Q(X)$，在 $\vartheta$ 无极点，
且 $x=F(\vartheta)\ne0$ 是固定允许参数 $\beta$ 的一个简单内部率根。
记 $R=Q_{n-1}$、$t=P_{n-1}/R$，并定义

$$
J_n^F=Q^2F(t)+QF'(t)+\frac12F''(t),\qquad
\kappa_F=\frac{F'''(\vartheta)}6.
\tag{85.1}
$$

本章的 $R$ 是前一层分母，不是计数向量。函数、参数和根均一次固定；
结论不统一于增长的次数或系数高度。

**定理 85.2（有理函数根的精确过渡带二择一）。** 在根 $x$ 的一个固定充分小邻域内，
充分大的原合法层上，实际过渡带
$Q^{-8}\le\bar c_{Q,j}^{\mathcal E}\le Q^8$ 有如下完整描述：
若 $J_n^F\notin\mathbb Z$，带内没有整数指标；若 $J_n^F\in\mathbb Z$，
带内恰有 $j=J_n^F$，并且

$$
\bar c_{Q,J_n^F}^{\mathcal E}(\beta)
 =Q^{-3}\exp\{C_Q(x;\beta)+I'(x)\kappa_F+o(1)\}.
\tag{85.2}
$$

这里 $C_Q$ 取 (81.19)，保留原 $M$ 取整和计数取整，且一致有界。
结论同时适用于 pair/path；特别地该根没有正有限实际均值子序列。
在两根区间 $(\beta_*,1)$，任一根属于 $\mathbb Q(\vartheta)$ 即排除 $\beta\in E_2$。

证明。原序列给

$$
\vartheta=t+Q^{-1}+\epsilon_n,\qquad
0<\epsilon_n<2\,10^{-Q^5},\qquad Q=10^{R^5}.
\tag{85.3}
$$

写 $F=A/B$，其中 $A,B\in\mathbb Z[X]$，并置
$m=\max(1,\deg A,\deg B)$。
在 $\vartheta$ 的固定邻域上，$B$ 与零分离，$F$ 的前四阶导数有界。
令 $A_0=A$、$A_{i+1}=A_i'B-(i+1)A_iB'$，则
$F^{(i)}=A_i/B^{i+1}$，且 $\deg A_i\le(i+1)m-i$。
对 $i=0,1,2$，有整数

$$
B_h=R^mB(t)\ne0,\qquad
A_{i,h}=R^{(i+1)m-i}A_i(t),\qquad
F^{(i)}(t)=\frac{R^iA_{i,h}}{B_h^{i+1}}.
\tag{85.4}
$$

因此 $J_n^F$ 的一个公分母为 $2B_h^3$。
若其正既约分母为 $b_n$，则

$$
b_n\le C_FR^{3m},\qquad \frac{b_n\ln Q}{Q}\longrightarrow0.
\tag{85.5}
$$

这只使用 $Q=10^{R^5}$；没有假设 $B_h$ 或 $b_n$ 整除 $Q$。
在 $t$ 处 Taylor 展开并保留三次项，得到

$$
Q^2F(\vartheta)
 =J_n^F+\frac{F'''(t)}{6Q}+O_F(Q^{-2})+O_F(Q^2\epsilon_n)
 =J_n^F+\frac{\kappa_F}{Q}+O_F(Q^{-2}).
\tag{85.6}
$$

若实际均值位于所述过渡带，原 Stirling 展开与简单根局部化首先给

$$
|j-Nx|\le C\ln Q/Q,\qquad
\ln\bar c_{Q,j}^{\mathcal E}
 =-QI'(x)(j-Nx)-3\ln Q+C_Q(x;\beta)+o(1).
\tag{85.7}
$$

这由 (83.8) 在多项式均值范围的相对比较得到，
路径依赖仍由原一行、两行系数估计支付；$M^{-10}$ 尾部不可能制造过渡均值。
(85.6) 使 $|j-J_n^F|\le C_F\ln Q/Q$。
若 $J_n^F$ 不是整数，其到每个整数的距离至少为 $1/b_n$，与 (85.5) 矛盾。
若它是整数，则必有 $j=J_n^F$，此时
$j-Nx=-\kappa_F/Q+O_F(Q^{-2})$。
代回 (85.7) 得 (85.2)，注意常数项符号为正的 $I'(x)\kappa_F$。

反之，当 $J_n^F$ 为整数时，它距内部根指标 $Nx$ 仅 $O(Q^{-1})$，
所以 tuple 可行、位于原完整窗口，原得分隔离及固定截断均适用。
由实际均值展开，其均值被固定正倍数的 $Q^{-3}$ 夹住，最终确实在过渡带中。
这证明二择一的充分性。正有限均值最终必须落入该过渡带，
而带内唯一可能均值趋零，故不存在该类复现。证毕。

这一证明扩展了第 83 章的多项式排除：需要的是前一层预测量分母相对 $Q/\ln Q$ 小，
不需要它整除十的幂。一般解析函数或具有代数无理 Taylor 系数的函数并未由此覆盖；
证明中到整数的 $1/b_n$ 分离不可删除。

**命题 85.3（两个明确的非多项式参数与空过渡带）。** 令

$$
x_{\rm rec}=\frac1{1000+\vartheta},\qquad
\beta_{{\rm rec},\pm}=\frac\phi{\phi+I(\pm x_{\rm rec})}.
\tag{85.8}
$$

它们是两个不同的 $(\beta_*,1)$ 参数，且均不属于 $E_2$。
在 $\beta_{{\rm rec},+}$ 的正根及 $\beta_{{\rm rec},-}$ 的负根附近，
原实际多项式过渡带最终为空。

证明。对 $F_+(z)=1/(1000+z)$，令 $P=P_{n-1}$、$H=1000R+P$，则

$$
J_n^{F_+}=\frac{Q^2RH^2-QR^2H+R^3}{H^3}.
\tag{85.9}
$$

$\gcd(H,R)=1$，分子模 $H$ 等于 $R^3$，故既约分母恰为 $H^3>1$。
$F_-=-F_+$ 的预测量也不是整数，定理 85.2 因而给空带。
没有关于 $Q$ 模 $H$ 的等分布假设。

参数合法性由第 83 章的 $1/10<\vartheta<11/100$、$b>2^{-12}$ 及
$\vartheta^2/100<b$ 给出：

$$
0<x_{\rm rec}<\vartheta/100<b/\vartheta,
\qquad 0<I(x_{\rm rec})<I(-x_{\rm rec})<I(u_-).
\tag{85.10}
$$

中间严格率函数比较用 $I''$ 严格递减作两次积分，负端点以连续性处理。
因此 $\beta_*<\beta_{{\rm rec},-}<\beta_{{\rm rec},+}<1$。
$x_{\rm rec}$ 无理；若它是某个有理多项式 $\Pi(\vartheta)$，
$\vartheta$ 的超越性会使 $(1000+X)\Pi(X)=1$ 成为多项式恒等式，矛盾。

还能量化相邻均值间隙。由 (85.6)、(85.9) 和 $Q^{-1}=o(H^{-3})$，
$\|Q^2x_{\rm rec}\|\ge1/(2H^3)$ 最终成立。
令 $j_0=\lfloor Q^2x_{\rm rec}\rfloor$，则某个固定 $c_1>0$ 使

$$
\ln\bar c_{Q,j_0}^{\mathcal E}(\beta_{{\rm rec},+})\ge c_1Q/H^3,
\qquad
\ln\bar c_{Q,j_0+1}^{\mathcal E}(\beta_{{\rm rec},+})\le-c_1Q/H^3.
\tag{85.11}
$$

因为 $Q/H^3\gg\ln Q$，均值展开中的 $-3\ln Q$ 及有界项均被吸收。
负根的增长、衰减侧反向。这些均值为 $\exp(O(Q))$，原实际比较仍可相对化。
两个参数各自的另一根未被分类；这里没有一个两根均已处理的参数。证毕。

**推论 85.4（指定根的熵余项消失）。** 沿用原完整后验熵 $h_M(\mathscr X)$、
实际均值确定中心 $d_M^{\mathcal E}$ 和
$\mathcal B(v)=H(\operatorname{Bin}(v,1/2))$，熵单位为 bits。
既有过渡带表示为

$$
h_M(\mathscr X)-d_M^{\mathcal E}
 =\sum_{j:Q^{-8}\le\bar c_{Q,j}^{\mathcal E}\le Q^8}
 [\mathcal B(C_j)-\mathcal B(\lfloor\bar c_{Q,j}^{\mathcal E}\rfloor)]
 +o_{\mathbb P}(1).
\tag{85.12}
$$

定理 85.2 指定根的这部分和，非零概率至多为 $C_{F,\beta}Q^{-3}$，
一致于确定真实支持并对两个实际实验分别成立。
所以两根情形的全余项只剩另一根的项加 $o_{\mathbb P}(1)$；
合法单根区间中若唯一根属于 $\mathbb Q(\vartheta)$，则全余项趋零。

证明。带内无指标时根项恒为零；有指标时其均值为 $O(Q^{-3})<1$，
确定中心项为零，随机项仅为 $\mathcal B(C_{J_n^F})$。
$\mathcal B(v)>0$ 恰在整数 $v\ge1$，因此实际均值及 Markov 给

$$
\sup_{S:|S|=q}\Pr_S^{\mathcal E}
 (\text{该根的过渡带项非零})
 \le\mathbb E_S^{\mathcal E}C_{J_n^F}\le C_{F,\beta}Q^{-3}.
\tag{85.13}
$$

原支持置换不变性给一致性；这是事件概率界，没有推出无界熵的期望收敛。
倒数例中指标集最终为空，指定根项直接恒零。
临界参数 $\beta_*$ 的边界根有不同前因子，不在本结论内。证毕。

**命题 85.5（固定原层上的对偶计数与归一化后的格条件）。** 令
$\mathscr F_Q(s)=N\mathcal L_Q(s)$，$\mathcal L_Q$ 取 (83.11)，
固定内部紧斜率区间 $\Sigma$，并令 $D=\lfloor\sqrt Q\rfloor$。
能够用于 (83.10) 的一个计数是

$$
\mathcal K_Q(A,\Sigma,D)=\#\left\{(p,d,m):
 \frac D2<d\le D,\ \gcd(p,d)=1,\ p/d\in\Sigma,
 \ 0\le m-d\mathscr F_Q(p/d)\le A/d\right\}.
\tag{85.14}
$$

这里对辅助 $d$ 求和，原 $N=Q^2$ 始终固定。
较窄单侧条件 $0<m-d\mathscr F_Q(p/d)<A/D$ 恰可写为

$$
\|d\mathscr F_Q(p/d)-\theta_2\|<\delta_D,
\qquad \theta_2=-A/(2D),\quad\delta_D=A/(2D).
\tag{85.15}
$$

允许对平移统一的曲线定理可以容纳这个随 $Q$ 变化的 $\theta_2$，
但不能据此省略曲线常数或 $\gcd(p,d)=1$。

具体地，Beresnevich–Vaughan–Velani 的 0903.2817v1 固定曲线覆盖证明采用
$0<c_1\le|f''|\le c_2$、$c_0<1/6$ 及充分校准

$$
C_1=\frac{3c_2}{c_1c_0^8},\qquad k_1^3>c_2C_1^2,\qquad
\delta\ge k_1/R_0.
\tag{85.16}
$$

对 $f=\mathscr F_Q$，有 $|f''|\asymp N$，故该特定校准迫使
$k_1\ge cN^{1/3}$；取 $R_0=D/2$ 和 (85.15) 后需 $A\ge cN^{1/3}$。
它不提供一个固定 $A$ 的充分界。

证明。对偶函数的精确微分给
$\mathscr F_Q''(s)=-N/g_Q''(u_Q)\asymp-N$，
$\mathscr F_Q'''(s)=O(N)$，所以 $c_2\ge cN$，$c_2/c_1\ge1$。
(85.16) 的 $C_1\ge3\cdot6^8$，直接给所述增长；
而 $\delta_DR_0=A/4$。该原文最后 Taylor 界中的分母上限有一个固定二倍因子，
补上只改变充分常数，不改变这里的 $N^{1/3}$ 次数。
本结论只否定这套指定充分校准的统一性，不是所有可能计数定理的下界或不可能性证明。

此外，无原始基分数条件的计数也不够。
若 $p=gp'$、$d=gd'$，同余式 $pr+m\equiv0\pmod d$ 需要 $g\mid m$；
只要求三元组 $\gcd(p,m,d)=1$ 并不能保证它。
因此平面有理点的原始三元组与原始基分数在本问题中不是同一个限制。

即便归一化曲率，也必须保留格。
选 $s_0=a_0/b_0\in\Sigma$，使固定 $b_0$ 最终整除 $Q$，令
$z=Q(s-s_0)$、$\widetilde f_Q(z)=\mathscr F_Q(s_0+z/Q)$。
其二阶导数上下有界，三阶导数也有界；但 $s=p/d$ 对应

$$
z=\frac{v}{d},\qquad v=Qp-(Qa_0/b_0)d,\qquad
v+(Qa_0/b_0)d\equiv0\pmod Q.
\tag{85.17}
$$

这是整数对 $(v,d)$ 中指数 $Q$ 的子格，
原始性还要求 $\gcd((v+(Qa_0/b_0)d)/Q,d)=1$。
不带该同余式的有理点定理计数了更大的集合。
固定 $z$ 区间对应长度 $O(Q^{-1})$ 的 $s$ 区间；保持固定父斜率区间则会使
归一化后的区间长度增长。曲率归一化并未同时解决常数、区间和格限制。证毕。

计数 (85.14) 若能以同一有限 $A$ 支持一个无限嵌套分支，仍可按第 83 章构造 $E_2$ 参数。
本章没有给出这样的正计数或分支；$E_2$ 的非空性、空性、锐利维数和指定双均值实现仍为开放问题。
有理函数根的排除与局部熵结论不决定两个倒数参数的另一根，也不决定其全熵余项。
所有结论使用原完整后验、实际依赖路径和共同方向一致事件，未引入新参数先验或替代分母实验。

## 追加锚（本行以下为增补区）

## 86. 固定凸体薄壳与双根同步维数的严格改进

**定义 86.1（原尺度同步条带）。** 沿用第 76、81、83、85 章的原固定幅度、
合法 $Q=Q_n$、$N=Q^2$、两内部率根映射 $\Psi$、精确 Gamma 等系数曲线
$G_Q$、自然对数系数 $\ell_Q$ 和双根集合 $E_2$。
固定紧参数区间 $J\Subset(\beta_*,1)$，在其正根范围外稍作固定扩大，
得到 $K=[\kappa_0,\kappa_1]\Subset(0,u_*)$。
对固定 $H<\infty$，考虑同一原 $N$ 上的全部整数对

$$
\mathscr P_{Q,H}(K)=
 \{(j,k)\in\mathbb Z^2:j/N\in K,
                    \ |k-G_Q(j)|\le H/Q\}.
\tag{86.1}
$$

本章不改变 $E_2$：两个相反率根对应的完整组必须沿同一原合法子序列，
在同一个固定 $\beta$、同一个 $M,q$ 及补偿下，具有正有限的实际均值极限。
平稳对与连续路径集合的相同性仍由实际相对均值桥保证。

**定理 86.2（固定原层的严格改进计数）。** 对上述每个固定 $K,H$，
每个充分大的原合法层分别满足

$$
\#\mathscr P_{Q,H}(K)
 =O_{K,H}(N^{19/29})=O_{K,H}(Q^{38/29}).
\tag{86.2}
$$

该结论没有对分母、尺度、旋转或平移取平均。

证明。原率函数满足 $I''>0$、$I'''<0$，第 81 章给 $\Psi''>0$。
解析延拓给 $\Psi(0)=0$、$\Psi'(0)=-1$，故

$$
\frac d{du}[\Psi(u)-u\Psi'(u)]=-u\Psi''(u)<0,
\qquad \Psi(u)-u\Psi'(u)<0\quad(u>0).
\tag{86.3}
$$

先把所需弧精确嵌入一个固定闭凸体。选
$0<A<\kappa_0<\kappa_1<B<u_*$，记 $L_A=\Psi(A)-A\Psi'(A)<0$。
取正光滑函数 $W$，在 $[A,B]$ 等于 $\Psi''$，在一个更大有界区间之外等于
某个正小常数，并使

$$
\int_0^A tW(t)dt<-L_A/2.
\tag{86.4}
$$

具体可在 $[A-h,A]$ 以平滑截断从该小常数过渡到 $\Psi''$，
先令 $h$ 小，再令常数小；右端独立平滑接回同一常数。
令 $F''=W$，在 $A$ 匹配 $\Psi$ 的值与一阶导数，则

$$
F|_{[A,B]}=\Psi,\qquad
F(0)=L_A+\int_0^A tW(t)dt<0.
\tag{86.5}
$$

$F$ 严格凸且向两端二次增长。另选 $Y_0>0$ 和光滑函数 $\chi$，
在 $t\le0$ 为零，在 $t>0$ 为正，在 $t\ge1$ 等于 $2$。
定义

$$
\varphi_0(y)=
\begin{cases}
-y,&y\le Y_0,\\
-y+\displaystyle\int_{Y_0}^y(y-t)\chi(t-Y_0)dt,&y>Y_0,
\end{cases}
\qquad
\Omega=\{(x,y):F(x)+\varphi_0(y)\le0\}.
\tag{86.6}
$$

这里 $\varphi_0$ 与模型常数 $\phi$ 不同。它凸且两端趋正无穷，
唯一极小点位于 $Y_0$ 之上，那里 $\varphi_0''>0$。
因此 $\Omega$ 是含原点为内点的紧凸体。
$F+\varphi_0$ 的唯一临界点是严格负值的极小点，零水平集正则；其曲率为

$$
\frac{F''\varphi_0'^2+\varphi_0''F'^2}
 {(F'^2+\varphi_0'^2)^{3/2}}>0.
\tag{86.7}
$$

若 $\varphi_0'\ne0$，第一项为正；否则 $\varphi_0''>0$，
而正则性给 $F'\ne0$。紧性给正曲率下界。
由于 $\Psi<0<Y_0$，$\{(u,\Psi(u)):u\in[A,B]\}$ 精确包含在
$\partial\Omega$ 中。$K$ 两端位于该弧内部；没有切出竖边或引入角点。
这个 $C^\infty$ 正曲率凸体只依赖固定 $K$ 和原幅度。

所用经典格点输入是 Guo 的 arXiv:1010.4923v2，Remarks 6.5(1) 的
正曲率特例及其第 6 节逐方向证明：对每个这样的固定凸体 $\Omega$，

$$
A_\Omega(t):=\#(t\Omega\cap\mathbb Z^2)
 =|\Omega|t^2+O_\Omega(t^{19/29})
\quad(t\longrightarrow\infty).
\tag{86.8}
$$

这里采用固定原方向、所有充分大的实数 $t$。该文主定理中有限型曲线的
“几乎处处旋转”量词不用于本式。为明确适用条件，取低于最小曲率的固定截断；
原文坏锥集合 $D_2$ 为空。Lemma 3.4 在切／法方向给支持函数导数行列式
$-m!^2\kappa^{-2}$，并以整数方向及其有限指数格陪集保留整个整数格。
令差分阶 $m=3$，原文 Proposition 5.2 和 (6.10)–(6.11) 在频率块
$D_0\le D\le c t^{4/5}$ 给加权和界

$$
C_\Omega(1+D\eta)^{-m_0}
\left[t^{1/22}D^{7/22}+D^{1/4}
+t^{-15/88}D^{15/22}
+t^{-1/22}D^{19/44}(\ln D)^{1/8}\right].
\tag{86.9}
$$

$D_0$ 和充分大的 $m_0$ 固定，$\eta$ 是卷积平滑宽度。
原文尺度条件 $T\ge C M_*^{9/4}$ 在 $T=tD,M_*\asymp D$ 下恰给
$D\le c t^{4/5}$。支持分离、导数界和行列式下界的常数在固定凸体上均固定。
乘 $t^{1/2}$ 并按二进块求和，四项分别受控于

$$
C_\Omega\left[
 t^{6/11}\eta^{-7/22}+t^{1/2}\eta^{-1/4}
 +t^{29/88}\eta^{-15/22}
 +t^{5/11}\eta^{-19/44}\ln t\right].
\tag{86.10}
$$

Corollary 4.3 的 Fourier 余项为 $O(\ln(2/\eta))$；低频块贡献
$O_\Omega(t^{1/2})$，高频块贡献
$O_\Omega(t^{9/10-4m_0/5}\eta^{-m_0})$。
原文 Lemma 6.2 证明中的卷积夹逼以面积误差 $O_\Omega(t\eta)$
接回闭域的未平滑计数。取 $\eta=t^{-10/29}$，首项与面积项均为
$t^{19/29}$；其余三项的幂分别为 $17/29$、$1441/2552$、$385/638$，
均更小，且高频衰减阶可固定取得充分大。因此得到 (86.8)，不带额外对数损失。
这使用原文的成熟偏差估计，不把它作为本模型新创的一般格点定理。

接着保留精确曲线的尺度修正。第 83 章的原 Gamma 展开是

$$
G_Q(j)=N\Psi(j/N)+Q^{-1}R_Q(j/N)+O_K(Q^{-4}),
\qquad \sup_Q\|R_Q\|_{C^0(K)}<\infty.
\tag{86.11}
$$

原 $k_0$ 的 floor 仍在 $R_Q$ 中。该修正与条带宽度同阶；
本证明把它计入上包络，不把它从相位等式中删除。
于是 (86.1) 中每点到 $N\partial\Omega$ 的距离至多
$w_N=C_{K,H}N^{-1/2}$。
选 $r_0>0$ 使闭球 $B(0,r_0)\subset\Omega$。
Minkowski 泛函 $p_\Omega$ 次可加且
$p_\Omega(z)\le|z|/r_0$，故

$$
|p_\Omega(z)-p_\Omega(z')|\le |z-z'|/r_0.
\tag{86.12}
$$

这不要求 $\Omega$ 关于原点对称。
令 $s_N=2w_N/r_0$，便有严格的闭内域排除关系

$$
\mathscr P_{Q,H}(K)
 \subset (N+s_N)\Omega\setminus(N-s_N)\Omega,
\tag{86.13}
$$

因为每个所数点满足 $p_\Omega\ge N-w_N/r_0>N-s_N$。
两尺度相减无需额外处理边界格点。由 (86.8)，

$$
\begin{aligned}
\#\mathscr P_{Q,H}(K)
 &\le A_\Omega(N+s_N)-A_\Omega(N-s_N)\\
 &\le4|\Omega|Ns_N+O_K(N^{19/29})\\
 &=O_{K,H}(N^{1/2}+N^{19/29}).
\end{aligned}
\tag{86.14}
$$

这给 (86.2)。整个移动曲线族只通过 (86.11) 的零阶误差进入同一个固定凸体；
没有假定任意移动域上的偏差常数统一。证毕。

**定理 86.3（同步集合的改进维数与临界对数规范）。** 原双根同步集合满足

$$
\dim_H E_2\le\frac{38}{87}<\frac49.
\tag{86.15}
$$

对每个 $\gamma_0>0$，令
$f_{\gamma_0}(t)=t^{38/87}/[\ln(e/t)]^{\gamma_0}$ 于充分小的 $t$，则

$$
\mathcal H^{f_{\gamma_0}}(E_2)=0.
\tag{86.16}
$$

特别地，$\mathcal H^{4/9}(E_2)=0$。本结论不判定临界
$\mathcal H^{38/87}(E_2)$。

证明。沿用原共同单元

$$
\mathcal J_{Q,L}=
\left(\frac{\phi Q^3}{(L+1)\ln2},
      \frac{\phi Q^3}{L\ln2}\right],
\qquad |\mathcal J_{Q,L}|\asymp_J Q^{-3}.
\tag{86.17}
$$

在 $J$ 中，两个均值同时有界正的原单元必须满足某个固定 $H$ 下的

$$
|L\ln2+\ell_Q(j)|\le H,\qquad
|L\ln2+\ell_Q(k)|\le H.
\tag{86.18}
$$

这是同一个整数 $L$。原实际均值桥
$\bar c_{Q,i}^{\mathcal E}=2^L\chi_{Q,i}(1+o(1))+O(M^{-10})$
在此统一成立；反过来，(86.18) 在无穷多层成立便把两实际均值留在同一紧正区间，
可抽取共同的收敛子序列。因而第 76 章的共同单元 limsup 表达仍精确有效，
最后对整数 $H$ 取并；这不声称有限 $Q$ 下代理阈值与实际阈值逐字相等。

均值局部化把两索引置于固定放大的根邻域，其中
$|\ell_Q'|\ge c_JQ$。由精确等值关系和 (86.18)，
$|k-G_Q(j)|\le C_{J,H}/Q$。
定理 86.2 给 $O_{J,H}(Q^{38/29})$ 对候选整数。
每对由第一条约束至多允许 $\lfloor2H/\ln2\rfloor+1$ 个整数 $L$，
故每层以 $O_{J,H}(Q^{38/29})$ 个直径 $O_J(Q^{-3})$ 的原共同单元覆盖。
对 $s>38/87$，覆盖尾代价

$$
C_{J,H,s}\sum_{n\ge n_0}Q_n^{38/29-3s}\longrightarrow0.
\tag{86.19}
$$

对 $f_{\gamma_0}$，幂恰消去，尾代价则受控于
$C\sum_{n\ge n_0}(\ln Q_n)^{-\gamma_0}\to0$。
两者均由原 $Q_{n+1}=10^{Q_n^5}$ 的超稀疏增长得到。
先对 $H$，再对 $(\beta_*,1)$ 的紧区间穷尽取可数并，得到两式。
若 $\gamma_0=0$，当前覆盖代价不趋零，故不添加临界测度结论。证毕。

更一般地，同一覆盖对任意 doubling 维数函数 $f$ 给充分条件
$\sum_nQ_n^{38/29}f(Q_n^{-3})<\infty\Rightarrow\mathcal H^f(E_2)=0$。
它不是完整的零／无穷律。若日后有经原文核对的固定凸体偏差
$O(t^a(\ln t)^b)$，$a>1/2$，本章的固定凸体桥即给维数上界 $2a/3$；
$a=1/2$ 时还须保留薄壳面积项。未核对完整条件的更强指数不在本章结论内。

$E_2$ 的非空性、空性、锐利维数、保持同一有限 $H$ 的无限嵌套分支，
以及同时指定两个正均值的可达性仍为 **open**。
薄壳的上界不能提供下界、共同单元存在或无限分支。
本章保留全部原 floor、补偿、完整组及两种实际实验，不把连续路径的行视为独立；
这里也没有新的噪声解码、期望熵或方向判别结论。
固定凸体构造、实际 Gamma 包络与共同规模单元之间的连接是本章新增的模型推导；
格点偏差、卷积夹逼与 Hausdorff 覆盖原理保留经典归属，参见 Library 对应说明。

## 追加锚（86 章后）

## 87. 同一带噪能量观测造成的首个条件信息方差损失

**定义 87.1（纤维内的信息方差）。** 保持第 77、82、84 章的固定幅度、固定
$\beta\in(1/2,1)$、原合法规模、全部得分组、均匀支持先验后验 $P_x$、精确中心及
同一个 $Y=T+\sigma_MG$。仍令

$$
L_M=\ln(1/\sigma_M)\longrightarrow\infty,\qquad
L_M=o(Q^3),\qquad \delta=Q^{-1/2},\qquad \nu=2g_0.
\tag{87.1}
$$

$G$ 在给定原始数据 $x$ 后独立标准正态，未另行提供给观察者。
$\varphi_\sigma$ 表示标准差为 $\sigma$ 的正态密度；$\varphi_\nu$ 则沿用前文，
表示方差为 $\nu$ 的中心正态密度。对同一个原计数向量 $R$，定义自然单位变量

$$
\begin{aligned}
S&=-\ln P_x(R),& h&=\mathbb E_xS=h_x^{\rm nat},\\
J&=-\ln p_x(R\mid Y),& H_x(y)&=\mathbb E_x[J\mid Y=y],\\
\mathcal V_{{\rm prior},x}&=\operatorname{Var}_x S,&
\mathcal V_{{\rm post},x}(y)&=\operatorname{Var}_x(J\mid Y=y).
\end{aligned}
\tag{87.2}
$$

这里的方差不含跨输出的 $H_x(Y)$ 波动。每个有限纤维的计数字母表有限，
预测密度 $f_x(y)>0$；这些对象在每个实输出处均有定义。
以下仍分别对原平稳对与连续路径实验，在确定真实支持的数据概率下一致收敛。
不把均匀先验核换成已知真实支持的点质量核。

**定理 87.2（输出积分的首阶 varentropy 损失）。** 对 (87.1) 中每个确定噪声序列，
有

$$
\int_{\mathbb R}f_x(y)
 \left|\delta\{\mathcal V_{{\rm post},x}(y)-\mathcal V_{{\rm prior},x}\}
                 +\frac{\gamma^2}{\nu+\sigma_M^2}\right|dy
 \longrightarrow0.
\tag{87.3}
$$

量词为：对每个 $\varepsilon>0$，上述积分超过 $\varepsilon$ 的数据概率，
在各原实验内对合法真实支持 $S_0\subset C_+$、$|S_0|=q$ 取上确界后趋零。
等价地可将 (87.3) 的常数写成

$$
\frac{\gamma^2}{\nu}=\sqrt{\frac\pi\kappa}>0.
\tag{87.4}
$$

因此首个已识别的损失为负，阶为 $Q^{1/2}$，低于原 $Q^2$ 阶信息方差。
保留 $\nu+\sigma_M^2$ 只表示相差 $O(\sigma_M^2)=o(1)$ 的等价写法，
不声称余项比 $\sigma_M^2$ 小，也不提供收敛速率。

证明。以下所有辅助量均取给定数据后的原定义。
沿用 $\mathsf Q_x,L_x=dP_x/d\mathsf Q_x,a_x=\|L_x-1\|_{2,\mathsf Q_x}$，
以及第 82 章的同一移动核心 $\mathcal C$、外部集 $\mathcal O$ 和参考标量
$T^{\rm G}$。(82.7) 中的精确 $e_j$ 和外部中心截距保持不动。

**二阶权重先通过实际总数条件化。** 令
$\mathcal S=-\ln\mathsf Q_x(R)$、$\widetilde h=\mathbb E_{\mathsf Q_x}\mathcal S$、
$s=\mathcal S-\widetilde h$、$V_Q=\mathbb E_{\mathsf Q_x}s^2$。
(82.4)—(82.5) 已给整个原窗口上的

$$
\mathbb E_{\mathsf Q_x}s^4\le CQ^4,\quad V_Q\le CQ^2,\quad
0\le L_x\le C,\quad a_x=O_{\mathbb P}(Q^{-5/2}),\quad
\|S-h-s\|_{2,P_x}\le C(Qa_x+a_x^2).
\tag{87.5}
$$

这些矩界包括空组和过渡组；对单组二项信息量减去
$\tfrac12\ln(n+1)$ 使用全点上下界及 Bernoulli 八阶中心矩，再展开独立中心和即可。
原 $Q^5$ 阶平均信息已经消去，路径行独立性没有被引入。
记 $b_x=S-h-s$。Cauchy–Schwarz 给

$$
\begin{aligned}
\mathbb E_{\mathsf Q_x}|(L_x-1)(s^2-V_Q)|&\le Ca_xQ^2,\\
\mathbb E_{P_x}|2sb_x+b_x^2|
 &\le C\{Q^2(a_x+a_x^2)+a_x^4\},\\
|\mathcal V_{{\rm prior},x}-V_Q|
 &\le C\{Q^2(a_x+a_x^2)+a_x^4\}=o_{\mathbb P}(1).
\end{aligned}
\tag{87.6}
$$

这是未归一化的实际矩比较，不是由 TV 传递平方信息量。
定义带符号输出密度

$$
\begin{aligned}
q_x(y)&=\mathbb E_{P_x}[(S-h)\varphi_{\sigma_M}(y-T)],\\
c_x(y)&=\mathbb E_{P_x}[\{(S-h)^2-\mathcal V_{{\rm prior},x}\}
                                      \varphi_{\sigma_M}(y-T)].
\end{aligned}
\tag{87.7}
$$

每个正测量核的积分等于一，故 (87.6) 将 $c_x$ 与
$\mathbb E_{\mathsf Q_x}[(s^2-V_Q)\varphi_{\sigma_M}(\,\cdot-T)]$
的 $L^1$ 误差控制为 $o_{\mathbb P}(1)$，没有除以噪声。

**同一量化耦合控制平方信息。** (82.8) 给每个固定 $A\ge0,b>0$

$$
Q^A\sigma_M^{-b}D_M(x)\to0,\qquad
D_M=\mathbb E|T-T^{\rm G}|.
\tag{87.8}
$$

对两个平移正态核，令其 $L^1$ 距离为 $k$，则
$k\le\min(2,C|T-T^{\rm G}|/\sigma_M)$，
$\mathbb Ek^2\le CD_M/\sigma_M$。由 (87.5)，更换标量通道的平方权重误差至多为
$CQ^2\sqrt{D_M/\sigma_M}=o_{\mathbb P}(1)$。
至此才在乘积参考下写 $s=s_{\mathcal C}+s_{\mathcal O}$；
外部计数与核心量化变量独立，
$s_{\mathcal O}^2-\mathbb Es_{\mathcal O}^2$ 和
$2s_{\mathcal C}s_{\mathcal O}$ 在条件核积分中精确抵消。

还须将 (82.10) 的单组 $L^1$ 信息近似加强到 $L^2$。
若 $X=(K-np)/\sqrt{d}$、$d=np(1-p)$、$p\in[1/4,3/4]$，
同一单调量化耦合满足 $\|X-Z\|_2\le Cd^{-1/12}$，而八阶矩一致有界。
插值及 Hölder 给

$$
\|X-Z\|_4\le Cd^{-1/36},\qquad
\|X^2-Z^2\|_2\le Cd^{-1/36}.
\tag{87.9}
$$

在 $|K-np|\le n^{5/8}$ 内，Stirling 余项为 $O(n^{-1/8})$。
补集上全点界以 $C(1+X^2)$ 控制余项，而

$$
\mathbb E[(1+X^2)^2\mathbf1_{|X|>cn^{1/8}}]
 \le Cn^{-1/2}\mathbb E(1+|X|^8)\le Cn^{-1/2}.
$$

因此单组中心信息 $s_j$ 满足
$\|s_j-(Z_j^2-1)/2\|_2\le Cd_j^{-1/36}$。
令 $m=|\mathcal C|$、$S_G=\tfrac12\sum_{\mathcal C}(Z_j^2-1)$、
$k_M=\|s_{\mathcal C}-S_G\|_2$，则

$$
\begin{aligned}
k_M&\le Cm d_{\min}^{-1/36},\qquad \mathbb ES_G^2=m/2,\\
\mathbb E|s_{\mathcal C}^2-S_G^2|
 +|\mathbb Es_{\mathcal C}^2-m/2|
 &\le Ck_M(\sqrt m+k_M)=o_{\mathbb P}(1).
\end{aligned}
\tag{87.10}
$$

核心的指数占据下界胜过 $m\le CQ^2$。
令 $g_x$ 为 $T^{\rm G}+\sigma_MG_0$ 的辅助密度，并记

$$
q_G(y)=\mathbb E[S_G\varphi_{\sigma_M}(y-T^{\rm G})],\qquad
c_G(y)=\mathbb E[(S_G^2-m/2)\varphi_{\sigma_M}(y-T^{\rm G})].
$$

前述比较证明了未尺度化的

$$
\|c_x-c_G\|_1\to0,\qquad \|q_x-q_G\|_1\to0.
\tag{87.11}
$$

第二式本身不能用来平方条件均值，后面另证所需的 $L^2$ 比较。

**四个独立块给导数尾界。** 置 $w_j=v_j/\sqrt\delta$、$c_j=e_j/\sqrt{v_j}$，则

$$
T^{\rm G}=\sum_{\mathcal C}w_j[(Z_j-c_j)^2-1]
                      +\delta^{-1/2}\|e_{\mathcal O}\|^2.
\tag{87.12}
$$

第 77、84 章的实际剖面与中心界给

$$
\max_jw_j\le C\sqrt\delta,\quad \sum_jw_j^2\to g_0,\quad
\sum_jw_j^2c_j^2\le C\|e\|^2=O_{\mathbb P}(a_x^2),\quad
\mathbb ET^{\rm G}=\delta^{-1/2}\|e\|^2=o_{\mathbb P}(1).
\tag{87.13}
$$

不要求所有 $c_j$ 一致小。沿用按 $j\bmod4$ 的四块分拆，将外部截距放入一块。
每块在 $|j\delta|\le1$ 都有至少 $c/\delta$ 个权重位于
$[c\sqrt\delta,C\sqrt\delta]$ 的坐标。
每块的固定阶矩有界：其中心二次项的矩母函数对固定小 $|t|$ 的对数至多
$Ct^2\sum w_j^2$，线性项为方差有界的正态，均值由 (87.13) 控制。
其特征函数模至多为

$$
m_\delta(t)=(1+c_1\delta t^2)^{-c_2/\delta}.
\tag{87.14}
$$

每个固定多项式权重乘 $m_\delta$ 的积分一致有界且尾部一致消失：
$|t|\le\delta^{-1/2}$ 时用 $e^{-ct^2}$，补集先取一半幂得到指数小因子。
对至少两块之和的特征函数 $\psi$，一阶求导后仍有一个未求导的独立衰减因子，
故 $|\psi|+|\psi'|\le Cm_\delta$。
若 $h_B$ 为这种和的密度，Plancherel 对 $k=1,2$ 给

$$
\|h_B^{(k)}\|_2^2+\|y h_B^{(k)}\|_2^2\le C_k,
\quad \|h_B^{(k)}\|_1\le C_k,
\quad\int_{|y|>H}|h_B^{(k)}(y)|dy\le C_kH^{-1/2}.
\tag{87.15}
$$

最后两式用权重 $(1+y^2)^{-1}$ 的 Cauchy–Schwarz。
对完整和，原特征函数收敛及 (87.14) 先给前两阶密度导数的一致收敛，
再由 (87.15) 升为 $L^1$；正态卷积是 $L^1$ 收缩，因此

$$
\|g_x^{(k)}-\varphi_\nu^{(k)}\|_1\to0,\qquad k=0,1,2.
\tag{87.16}
$$

这些界不含逆噪声因子。若多项式权重依赖至多两个块，
可将一阶或二阶输出导数放到另两个独立块的密度上。

**半核心的对数密度导数有更高矩。** 令 $F$ 为任一半核心和，含其确定截距，置

$$
\begin{aligned}
D_F&=\|\nabla F\|^2=4\sum_{j\in B}w_j^2(Z_j-c_j)^2,\\
M_B&=2\sum_{j\in B}w_j(Z_j^2-1-c_jZ_j),\\
H_B&=\frac{M_B}{D_F}
 +\frac{16\sum_{j\in B}w_j^3(Z_j-c_j)^2}{D_F^2}.
\end{aligned}
\tag{87.17}
$$

对向量场 $\nabla F/D_F$ 作有限维 Gaussian 分部积分，得到
$\mathbb E h'(F)=\mathbb E[H_Bh(F)]$。
除法先以 $D_F+\epsilon$ 正则化。在至少 $n\ge c/\delta$ 个中心坐标上，
$D_F\ge c\delta\sum_{i=1}^n(Z_i-c_i)^2$；
非中心卡方的 Laplace 变换不大于中心卡方的变换。
负矩的 Mellin 积分因此给每个固定 $k$、充分大的 $n$

$$
\mathbb E D_F^{-k}\le(c\delta)^{-k}2^{-k}
 \frac{\Gamma(n/2-k)}{\Gamma(n/2)}\le C_k.
\tag{87.18}
$$

整数 $k$ 可直接用 Gamma 比值的乘积表示；所需实数阶由更大整数阶控制。
$M_B$ 是固定次数的中心多项式，固定阶矩有界；
(87.17) 第二项至多为 $4\max_jw_j/D_F$。
Hölder 给 $\mathbb E|H_B|^p\le C_p$，也正当化正则化极限。
于是半核心密度及其正态卷积 $h_{B,\sigma}$ 满足

$$
\frac{h_B'}{h_B}(y)=-\mathbb E[H_B\mid F=y],
\qquad
\int\left|\frac{h_{B,\sigma}'}{h_{B,\sigma}}\right|^p
               h_{B,\sigma}\le C_p.
\tag{87.19}
$$

零密度处任取零值；卷积后的密度处处正。第二式由条件 Jensen 得到，
不是 $\sigma^{-p}$ 的粗界。负号与对数密度导数的定义一致。
这里使用的是经典密度分部积分机制，并已核对本移动非中心二次型的统一负矩条件。

**两次精确方差倾斜给二阶带符号密度。** 对核心 Gaussian 律乘
$e^{\theta S_G}/\mathbb Ee^{\theta S_G}$。
倾斜后的 $Z$ 精确等分布于 $(1-\theta)^{-1/2}Z$；
保持 $c_j$ 和外部截距固定，所得标量记为 $T_\theta$。
在零处的两阶导数为

$$
\begin{aligned}
\mathcal A&=\sum_jw_j(Z_j^2-c_jZ_j),
& a_0&=\mathbb E\mathcal A=\frac{V_{\mathcal C}}{\sqrt\delta},\\
\mathcal B&=\sum_jw_j(2Z_j^2-\tfrac32c_jZ_j),
& \mathbb E\mathcal B&=2a_0.
\end{aligned}
\tag{87.20}
$$

归一化倾斜密度的二阶导数恰为 $S_G^2-m/2$，所以有限精确恒等式是

$$
q_G=-\mathbb E[\mathcal A\varphi_{\sigma_M}'(\,\cdot-T^{\rm G})],
\quad
c_G=\mathbb E[\mathcal A^2\varphi_{\sigma_M}''(\,\cdot-T^{\rm G})
                 -\mathcal B\varphi_{\sigma_M}'(\,\cdot-T^{\rm G})].
\tag{87.21}
$$

每个有限 $\sigma_M>0$ 下，正态导数有界而多项式局部指数矩有限，故可求导。
$\mathcal A-a_0,\mathcal B-2a_0$ 的固定阶矩由 (87.13) 有界；
前者平方展开的每一项只依赖至多两个块。
将输出导数放到未使用的独立块，应用 (87.15)，得到

$$
\|q_G+a_0g_x'\|_1\le C,\qquad
\|c_G-a_0^2g_x''\|_1\le C(1+a_0).
\tag{87.22}
$$

例如两块权重 $W$ 的二阶项的 $L^1$ 范数至多为
$\mathbb E|W|\,\|h_{\rm unused}''*\varphi_{\sigma_M}\|_1\le C\mathbb E|W|$。
这控制整条实线的输出，而非仅紧集。
$V_{\mathcal C}\to\gamma$，故 (87.11)、(87.16)、(87.22) 给

$$
\|\sqrt\delta\,q_G+\gamma\varphi_\nu'\|_1\to0,\qquad
\|\delta c_x-\gamma^2\varphi_\nu''\|_1\to0.
\tag{87.23}
$$

**平方根密度加权的条件均值比较。** 需要下述有限概率事实。
若两个联合律满足 $P=LQ_0$、$0\le L\le C$、$\mathbb E_{Q_0}L=1$，
$a=\|L-1\|_{2,Q_0}$，输出密度为 $f,g$，共同权重为 $W$，
则

$$
\|\sqrt f\,\mathbb E_P[W\mid y]
       -\sqrt g\,\mathbb E_{Q_0}[W\mid y]\|_2^2
 \le C'a(\mathbb E_{Q_0}W^4)^{1/2}.
\tag{87.24}
$$

证明这一事实时，条件于 $Q_0$ 的输出，置
$l=\mathbb E[L\mid Y]$、$A=\mathbb E[LW\mid Y]$、
$B=\mathbb E[W\mid Y]$。
左边等于 $\mathbb E_{Q_{0,Y}}|A/\sqrt l-B|^2$。
在 $l\ge1/2$ 上，写成
$\mathbb E[(L-1)W\mid Y]/\sqrt l+B(1/\sqrt l-1)$，
用 Cauchy–Schwarz、Jensen、
$\mathbb E(L-1)^4\le Ca^2$ 和 $|1/\sqrt l-1|\le C|l-1|$ 得右侧界。
在 $l<1/2$ 上，事件概率至多 $4a^2$，且
$A^2/l\le\mathbb E[LW^2\mid Y]$、$B^2\le\mathbb E[W^2\mid Y]$，
再用有界 $L$ 及四阶矩得到同一界；$l=0$ 处实际质量为零。

若两联合律的 TV 距离为 $\epsilon$，分别与其平均律比较，
密度比均至多为二、与一的 $L^2$ 距离至多为 $\sqrt\epsilon$，因而还有

$$
\|\sqrt f\,\mathbb E_P[W\mid y]
       -\sqrt g\,\mathbb E_{Q_0}[W\mid y]\|_2^2
 \le C\sqrt\epsilon(\mathbb E_PW^4+\mathbb E_{Q_0}W^4)^{1/2}.
\tag{87.25}
$$

实际后验的多项式误差使用较强的 (87.24)；
(87.25) 只用于指数精细的通道耦合。

先以共同 $s$ 比较实际／乘积联合律，再用 (87.5) 改变权重到 $S-h$。
接着在同一个计数与量化均匀变量空间比较 $T+\sigma_MG$ 和
$T^{\rm G}+\sigma_MG$，其联合 TV 至多 $CD_M/\sigma_M$。
这里已将测量正态积分进输出核；不声称在另行保留 $G$ 的图支撑上也有此 TV。
最后由条件 $L^2$ 收缩将核心信息换为 $S_G$，外部中心信息精确消失。
得到

$$
\left\|\sqrt\delta\,\frac{q_x}{\sqrt{f_x}}
 -\sqrt\delta\,\frac{q_G}{\sqrt{g_x}}\right\|_2^2
 \le C\delta\left[a_xQ^2+(Qa_x+a_x^2)^2
                 +Q^2\sqrt{D_M/\sigma_M}+k_M^2\right]\to0.
\tag{87.26}
$$

首项为 $O_{\mathbb P}(Q^{-1})$；其它项由 (87.8)、(87.10) 支付。
并未要求实际似然对数的四阶矩，改变该权重只用其已证二阶矩。

**参考条件均值可平方。** 将四块合成独立两半 $A,B$，
$\mathcal A_A,\mathcal A_B$ 为 (87.20) 的对应贡献。
由 (87.21)

$$
q_G(y)=-\mathbb E[\mathcal A_Ah_{B,\sigma_M}'(y-T_A)]
        -\mathbb E[\mathcal A_Bh_{A,\sigma_M}'(y-T_B)].
\tag{87.27}
$$

除以 $g_x$ 后为两个条件期望。
$\mathcal A_A$ 与 $T_B+\sigma_MG$ 独立，另一项同理。
条件 Jensen、(87.19) 及
$\mathbb E|\mathcal A_A|^4+\mathbb E|\mathcal A_B|^4\le C(1+a_0^4)$ 给

$$
\int g_x(y)\left|\sqrt\delta\,\frac{q_G(y)}{g_x(y)}\right|^4dy\le C.
\tag{87.28}
$$

这是条件均值的统一四阶界，不用可能过大的 $\operatorname{Var}S_G=m/2$。
由 (87.23)、$g_x\to\varphi_\nu$ 的 $L^1$ 收敛及参考输出的一致四阶矩，
先得到 $\sqrt\delta q_G/g_x-\gamma y/\nu$ 的 $L^1(g_xdy)$ 收敛，
再以 (87.28) 插值为 $L^2$。
同时截断尾部给 $\int y^2|g_x-\varphi_\nu|dy\to0$。
于是 (87.26) 推出

$$
\sqrt\delta\,\frac{q_x}{\sqrt{f_x}}
 \longrightarrow \frac{\gamma y}{\nu}\sqrt{\varphi_\nu(y)}
 \quad\hbox{于 }L^2(dy),
\qquad
\left\|\delta\,\frac{q_x^2}{f_x}
 -\frac{\gamma^2y^2}{\nu^2}\varphi_\nu\right\|_1\to0.
\tag{87.29}
$$

第二式使用 $\|u^2-v^2\|_1\le\|u-v\|_2(\|u\|_2+\|v\|_2)$。
这一步不能由第 82、84 章的 $L^1$ 回归直接得出。

现在应用每个有限纤维的精确恒等式

$$
f_x(y)\{\operatorname{Var}_x(S\mid Y=y)-\mathcal V_{{\rm prior},x}\}
       =c_x(y)-q_x(y)^2/f_x(y).
\tag{87.30}
$$

(87.23) 与 (87.29) 的极限相减，输出二次项精确消去：

$$
\gamma^2\varphi_\nu''(y)
 -\frac{\gamma^2y^2}{\nu^2}\varphi_\nu(y)
 =-\frac{\gamma^2}{\nu}\varphi_\nu(y).
$$

结合 $f_x\to\varphi_\nu$ 的 $L^1$ 收敛，得到

$$
\int f_x(y)\left|\delta\{\operatorname{Var}_x(S\mid y)
 -\mathcal V_{{\rm prior},x}\}+\gamma^2/\nu\right|dy\to0.
\tag{87.31}
$$

**后验信息中的测量余量不改变此阶。** 同一个实际 $R,G,Y$ 满足

$$
J=S-L_M+\tfrac12\ln(2\pi)+G^2/2+\ln f_x(Y),
$$

从而

$$
\mathcal V_{{\rm post},x}(Y)
 =\operatorname{Var}_x(S\mid Y)
  +\tfrac14\operatorname{Var}_x(G^2\mid Y)
  +\operatorname{Cov}_x(S,G^2\mid Y).
\tag{87.32}
$$

输出内确定项已经消去；没有假定给定 $Y$ 后 $G$ 仍独立正态。
给定原数据、尚未观测 $Y$ 时 $\mathbb EG^4=3$，所以
$\int f_x\operatorname{Var}_x(G^2\mid y)dy\le3$。
粗略的 $O_{\mathbb P}(Q)$ 协方差界不够，需要另估混合核。令

$$
\psi_\sigma(t)=(t/\sigma)^2\varphi_\sigma(t),\quad
u_x(y)=\mathbb E_{P_x}[(S-h)\psi_{\sigma_M}(y-T)].
\tag{87.33}
$$

$\psi_\sigma$ 非负、积分为一，且 $\|\psi_\sigma'\|_1\le C/\sigma$。
因此前面的单次权重比较仍有效，将 $u_x$ 换为
$u_G=\mathbb E[S_G\psi_{\sigma_M}(\,\cdot-T^{\rm G})]$ 的误差为
$C(Qa_x+a_x+a_x^2)+CQ\sqrt{D_M/\sigma_M}+k_M=o_{\mathbb P}(1)$。
一次倾斜给 $u_G=-\mathbb E[\mathcal A\psi_{\sigma_M}'(\,\cdot-T^{\rm G})]$。
将常数部分与中心块部分的导数移到独立密度，再用 (87.15) 和正核卷积收缩，得
$\|u_x\|_1=O_{\mathbb P}(1+a_0)=O_{\mathbb P}(\delta^{-1/2})$。

令 $m_x=\mathbb E_x[S-h\mid Y]$、$r_x=\mathbb E_x[G^2\mid Y]$。
(87.29) 给 $\mathbb E_{f_x}m_x^2=O_{\mathbb P}(\delta^{-1})$，
条件 Jensen 给 $\mathbb E_{f_x}r_x^2\le3$。
又 $u_x=f_x\mathbb E_x[(S-h)G^2\mid Y]$，所以

$$
\int f_x|\operatorname{Cov}_x(S,G^2\mid y)|dy
 \le\|u_x\|_1+(\mathbb E_{f_x}m_x^2)^{1/2}
                    (\mathbb E_{f_x}r_x^2)^{1/2}
 =O_{\mathbb P}(\delta^{-1/2}).
\tag{87.34}
$$

乘以 $\delta$ 后，(87.32) 的后两项均消失。
由 (87.31) 得 (87.3)；(87.4) 来自原 Gaussian 空间剖面的两个积分。
所有估计都在原数据好环境上给出，坏环境只支付其概率。
实际一行／两行界和支持置换维持了两种原实验的一致量词，证毕。

**推论 87.3（被观测解释的信息方差）。** 同一数据概率范围内，

$$
\delta\,\operatorname{Var}_{Y\mid x}(\mathbb E_x[S\mid Y])
 \longrightarrow\gamma^2/\nu,\qquad
\delta\{\mathbb E_{Y\mid x}\mathcal V_{{\rm post},x}(Y)
                  -\mathcal V_{{\rm prior},x}\}
 \longrightarrow-\gamma^2/\nu.
\tag{87.35}
$$

第一式由 (87.29) 积分及 $\mathbb E_x(S-h)=0$ 得到；第二式由 (87.3) 得到。
这些期望只在有限原数据纤维内，不对原始数据平均无界方差。

(87.3) 还给联合先验数据／输出概率中的相同损失：
用积分除以阈值控制条件失败概率，再把该概率截于一后平均即可。
这也一致适用于确定真实支持的实际联合观测律。
理由是保持奇偶类的站点置换同时映射原数据、真实支持、完整组和原标量，
保留同一 $G$ 后也保留 $Y$；上述先验定义函数及失败事件在此作用下不变，
各合法支持的无条件失败概率相同并等于先验平均。
不能将已知支持后的一条正态输出密度，条件于数据后直接替换成先验混合 $f_x$。
未知方向只使用原共同判向成功事件，仍保留同一测量噪声；不转移坏事件上的无界期望。

本章的结论不来自一般的“侧信息降低 varentropy”原则。
均匀两点先验的先验信息为常数、方差为零；
若两个点给不同标量均值并加入正 Gaussian 噪声，除一个输出点外，
后验两点概率不等而均为正，纤维内 varentropy 严格为正。
本章负损失依赖已经证明的实际模型关系。

在 bits 单位中，两方差及损失常数须同时除以 $(\ln2)^2$。
没有逐输出有限规模单调性、常数阶剩余方差展开、更高条件矩定理、零噪声结论、
$L_M\asymp Q^3$ 相变、期望方差收敛或有效解码算法。
第 84 章熵常数项中的精确噪声分母仍必须保留；
那里删除 $\sigma_M^2$ 会受到 $\delta^{-1/2}$ 放大，本章等价替换仅付 $O(\sigma_M^2)$。
二次型密度、指数族倾斜和条件方差恒等式均保留经典归属；
新增内容是实际完整后验的平方权重与平方条件均值比较，以及由此得到的首个损失尺度。

## 追加锚（87 章后）

## 88. 两根各自通用仍不产生同层同步

**定义 88.1（带符号的原单元通用集）。** 保持第 76、78、80、86 章的
原幅度、合法 $Q=Q_n$、$P=P_n$、$M=2^{L_0(\beta)}$、$q$、补偿、
精确 Gamma 系数 $\chi_{Q,j}$ 及两种实际实验。
沿用 $\vartheta$ 表示原 Liouville 斜率。令 $D=(\beta_*,1)$，
其中 $\beta_*=\phi/\{\phi+I(-b/\vartheta)\}$ 是原双内根阈值；
对 $\beta\in D$，$u_-(\beta)<0<u_+(\beta)$ 是
$I(u)=\phi(1-\beta)/\beta$ 的两个内根。
记 $\mu^{\mathcal E}_{Q,j}(\beta)$ 为第 78 章完整得分组的精确实际占据均值，
其中 $\mathcal E$ 表示平稳对或连续路径实验；它不是后验标签中心。
取第 78 章的可数正均值带基 $\mathscr B$，带宽之比小于二，
以及每带已经固定的嵌套内带
$(A_2,B_2)\Subset(A_1,B_1)\Subset B$。
原 floor 单元为

$$
C_{Q,L}=\left(\frac{\phi Q^3}{(L+1)\ln2},
                   \frac{\phi Q^3}{L\ln2}\right].
\tag{88.1}
$$

对符号 $\sigma\in\{-,+\}$，选择所有满足
$\sigma j>0$、$k_0+jQ\ge0$、$l_0+jP\ge0$，
且存在整数 $L$ 使

$$
A_2<2^L\chi_{Q,j}<B_2,\qquad C_{Q,L}\subset D
\tag{88.2}
$$

的完整原单元。这里 $\sigma j>0$ 分别表示 $j<0$ 或 $j>0$。
$U_{n,\sigma,B}$ 是这些单元的开放中三分之一之并。
令

$$
\mathcal V_0=
 \bigcap_{\sigma\in\{-,+\}}\ \bigcap_{B\in\mathscr B}\
 \bigcap_{n_0\ge1}\ \bigcup_{n\ge n_0}U_{n,\sigma,B}.
\tag{88.3}
$$

此定义使用全部可行整数指标，证明用的截断不进入定义。
令 $\mathcal V$ 为这样的全部固定参数组成的集合：对每个符号、每个
$\theta>0$，存在原合法子序列和该符号根旁的完整组，使其精确实际均值
在平稳对与连续路径实验中沿同一子序列均趋于 $\theta$。
两个符号可选不同子序列。$E_2$ 仍为第 76、86 章要求同层两根共同出现的集合。

**定理 88.2（两根边缘通用集与非同步族）。** $\mathcal V_0$ 是 $D$ 中的稠密
$G_\delta$，$\mathcal V_0\subset\mathcal V$；两集合均为 Lebesgue 零测集。
每个非空开区间 $J\subset D$ 满足

$$
\begin{aligned}
\mathcal H^{2/3}(\mathcal V_0\cap J)
 &=\mathcal H^{2/3}(\mathcal V\cap J)=\infty,\\
\dim_H(\mathcal V_0\cap J)
 &=\dim_H(\mathcal V\cap J)=2/3.
\end{aligned}
\tag{88.4}
$$

而 $\mathcal D_0=\mathcal V_0\setminus E_2$ 仍满足

$$
\mathcal H^{2/3}(\mathcal D_0\cap J)=\infty,\qquad
\dim_H(\mathcal D_0\cap J)=2/3.
\tag{88.5}
$$

每个 $\beta\in\mathcal D_0$、每个有限 $H>0$，在所有充分晚原合法层，
不存在两个相反根旁的完整组，其两个精确实际均值同时位于
$[e^{-H},e^H]$。这也适用于一个均值取平稳对实验、另一个取路径实验。
同时，每个这样的 $\beta$ 在每一根分别实现所有正实均值；
整数目标可以从两侧分别逼近。

证明。须补充负根的实际原单元估计，再将两种符号放进第 80 章已有的
多层质量构造。仅取两个已有临界无穷测度集合的交集不足以证明 (88.4)。

固定 $K\Subset D$ 及稍大的紧参数区间。
在两根各自的扩大紧弧上，两计数坐标 $a+u,b+\vartheta u$ 均有正下界，
$I'$ 不为零。记

$$
F(u)=\frac{\phi}{\phi+I(u)},\qquad
\Phi_Q(z)=\frac{\ln\chi_{Q,z}}{\ln2},
\tag{88.6}
$$

其中非整数指标的系数取第 86 章的精确 Gamma 延拓。
$F$ 在负弧严格递增、在正弧严格递减，两弧上 $|F'|$ 都上下有正界。
令 $\psi_1$ 为 trigamma 函数。直接求导精确系数，得到

$$
\Phi_Q''(z)=-
 \frac{Q^2\psi_1(k_0+Qz+1)+P^2\psi_1(l_0+Pz+1)}{\ln2},
\qquad
\frac{c_K}{Q}\le-\Phi_Q''(z)\le\frac{C_K}{Q}.
\tag{88.7}
$$

这里保留了 $k_0,l_0,P$ 的原精确值。由
$\psi_1(x)=\sum_{m\ge0}(x+m)^{-2}$ 及
$x^{-1}\le\psi_1(x)\le x^{-1}+x^{-2}$ 即得两侧界；
全部 Gamma 参数在所用弧上与 $Q^3$ 同阶。
负指标不改变此计算，因紧弧严格避开可行域左端点。
没有对只知逐点阶数的 Stirling 余项求导。

对固定正整数 $h$ 及弧内任意 $m$ 个连续整数，
第 78 章采用的经典二阶导数估计由 (88.7) 给

$$
\left|\sum_j e^{2\pi i h\Phi_Q(j)}\right|
 \le C_K\{m\sqrt{h/Q}+\sqrt{Q/h}\}.
\tag{88.8}
$$

指标为负不改变该估计的假设。
对固定非空圆弧 $A$，取支撑于其中的非负连续函数 $g\le1$、积分为正。
以固定阶 Fejér 多项式 $P_A$ 一致逼近 $g$，误差为 $\eta$，使
$2\eta<\int g$；则 $P_A-\eta\le\mathbf1_A$ 且积分为正。
对有限个非零 Fourier 模应用 (88.8)，得到真正的下计数

$$
\#\{j:\{\Phi_Q(j)\}\in A\}
 \ge p_A m-C_{K,A}(m/\sqrt Q+\sqrt Q),\qquad p_A>0.
\tag{88.9}
$$

这是每个固定层内随指标变化的结论，未断言固定参数沿原 $Q_n$ 的相位均匀分布。

内带对数宽度小于一，故 (88.2) 的 $L$ 唯一，
其允许相位中含一条固定正长度圆弧。
精确系数在任一根弧上的统一 Stirling 展开为

$$
\ln\chi_{Q,j}=-Q^3\{\phi+I(j/Q^2)\}-3\ln Q+O_K(1).
\tag{88.10}
$$

原 floor 与 $P/Q-\vartheta$ 均留在有界余项内。
若 $x_{Q,j}$ 是选中原单元的中点，则

$$
x_{Q,j}=F(j/Q^2)+O_{K,B}(\ln Q/Q^3),\qquad
|C_{Q,L}|\asymp_K Q^{-3}.
\tag{88.11}
$$

两个不同选中指标的主位置相距至少 $c_K|j-j'|Q^{-2}$，
而两个误差之和为 $o(Q^{-2})$。所以在任一固定符号下，中点间距至少
$c_KQ^{-2}$，任意长 $t$ 区间内的中点数至多 $C_K(1+tQ^2)$。
尤其不会由同一符号的不同指标选出相同单元。

对已经固定的非空开区间 $V\Subset K$，其符号弧逆像长度与 $|V|$ 同阶。
在该逆像的中部应用 (88.9)，再剔除边界，可得每个充分晚原合法层都有至少

$$
a_{K,\sigma,B}|V|Q^2,\qquad a_{K,\sigma,B}>0
\tag{88.12}
$$

个选中完整单元内含于 $V$。起效层可依赖 $V,\sigma,B$，
不要求对任意小区间统一。有限个已固定区间之并也适用。

第 78 章的实际均值比较在两弧均适用：它以正的计数坐标紧区间为条件，
不要求 $j>0$。具体为

$$
\mu^{\mathcal E}_{Q,j}(\beta)
 =2^{L_0(\beta)}\chi_{Q,j}(1+o(1))+O(M^{-10}),
\qquad \mathcal E\in\{\mathrm{pair},\mathrm{path}\},
\tag{88.13}
$$

在所用有界正代理均值带上一致。
路径结论使用原行转移矩阵的系数估计；观测行没有被当作独立。
由预定内带的正裕量，每个选中完整原单元上的两种实际均值最终都在外带 $B$。
该层使用同一个原 $L_0,M,q$ 和补偿，未把 floor 换成连续大小。
(88.10) 又将紧参数区间内的选中指标定位到相应根旁，
所以定义中不设截断仍可应用此完整组估计。

由 (88.12)，每个 $\bigcup_{n\ge n_0}U_{n,\sigma,B}$ 在 $D$ 稠密且开放。
Baire 定理给 $\mathcal V_0$ 稠密 $G_\delta$。
对其中固定 $\beta$、固定符号及任意实 $\theta>0$，选择直径趋零且靠近
$\theta$ 的有理基带，逐次选取严格增加、晚于该带实际比较阈值的命中层。
(88.13) 给两种实验沿该同一子序列趋于 $\theta$。
若 $\theta$ 为正整数，基带可全部位于它的下方或上方。
这先固定一个 $\beta$，再处理所有目标；不是对不同目标重选参数。

临界测度使用定理 80.2 证明中的构造，其输入已经由
(88.11)—(88.12) 对每一符号验证。
具体将该证明的带序列替换成预先排列的
$\rho_k=(\sigma_k,B_k)$，每一对出现无穷多次。
取一个依赖 $K$ 的共同小 $\kappa_0>0$，
使长度 $\kappa_0Q^{-3}$ 的中点闭区间内含于每个选中原单元的开放中三分之一。
两个符号只有有限种，故相同的上计数、长度与分离常数可以共同选取；
下密度 $\eta_k\in(0,1]$ 则允许随 $\rho_k$ 变小。

第 80 章父区间内删去既有 $5I$、在余下固定有限开集选择晚层的构造，
此时仍由 (88.12) 给每子层临界内容至少 $\eta_k|P|$。
令 $s=2/3$，对于任意 $\varepsilon>0$，在质量为 $\mu(P)$ 的父区间取有限
子层数 $m(P)$，满足

$$
\eta_km(P)|P|\ge\frac{\mu(P)}{\varepsilon\eta_{k+1}},
\qquad
\mu(I)=\mu(P)\frac{|I|^s}{\sum_{I'\in\mathcal C(P)}|I'|^s}.
\tag{88.14}
$$

下一阶段密度因子保留，因此每个非根父区间有
$\mu(P)\le\varepsilon\eta_k|P|^s$。
同层中点上计数及子层至少倍增给第 80 章完全相同的任意区间估计：
长 $t$ 的区间首次穿过两个子区间时，其所遇临界内容至多
$C(t^{2/3}+m(P)t)$。
其中线性项由
$\mu(P)t/(\eta_k|P|)\le\varepsilon t^{2/3}$（$t<|P|$）控制，
根的线性项由足够小的测试尺度控制。
于是所得概率测度在所有足够小区间满足
$\mu(A)\le C_J\varepsilon |A|^{2/3}$，且 $C_J$ 与 $\varepsilon$ 无关。
每条嵌套分支按有符号日程命中所有要求，其紧支撑包含于
$\mathcal V_0\cap J$。质量分布原理给
$\mathcal H^{2/3}(\mathcal V_0\cap J)\ge(C_J\varepsilon)^{-1}$；
令 $\varepsilon\downarrow0$ 得无穷。
这里复用的是已经证明的任意尺度估计；没有从单带测度直接推断交集测度。

对上界，$\beta\in\mathcal V$ 在正根有无穷多实际均值落入例如 $[1,2]$。
在每个固定参数紧区间上，(88.13) 将相应代理均值最终限制于 $[1/2,4]$。
每层只有 $O_K(Q^2)$ 个可能根指标，每指标允许 $O(1)$ 个整数 $L$，
单元长 $O_K(Q^{-3})$。对每个 $t>2/3$，
$\sum_n Q_n^{2-3t}<\infty$，尾覆盖给维数至多 $2/3$；
$t=1$ 给 Lebesgue 零测度。可数紧区间穷尽 $D$ 后得到 (88.4) 及零测结论。

定理 86.3 给 $\dim_HE_2\le38/87<2/3$，
所以 $\mathcal H^{2/3}(E_2)=0$。从 (88.4) 的无穷测度集合删去这部分，
得到 (88.5)。最后若某个 $\beta\notin E_2$、某个固定 $H$ 在无穷多原层
仍有两根的实际均值同时位于 $[e^{-H},e^H]$，
则由 (88.13) 两种实验的均值之比趋一，
并由紧性抽出同一层子序列上的两个正有限极限，
恰使 $\beta\in E_2$，矛盾。这也处理混合实验的选择，证毕。

该结论给出原模型内的严格区分：两根各自拥有全部正均值的子序列簇集，
仍不保证任何固定正有限带中的同层双根命中。
对 $\mathcal D_0$ 的 Baire 类别没有结论；
小 Hausdorff 维数不推出 $E_2$ 为贫集。
$E_2$ 的非空性、空性、锐利维数与指定同步均值继续未决。
本章局限于两根都在内部的 $D$，不包含 $\beta=\beta_*$。
第 72、78 章的单 Poisson 熵子序列结论可分别沿任一根应用，
保留各实验精确熵中心及整数目标两侧的区别；未产生同层双 Poisson 极限，
也未引入参数随机化、期望熵收敛或新的统计近似。

## 追加锚（88 章后）

## 89. 双根边缘通用集的一般规范零／无穷律

**约定 89.1（固定集合与近零规范）。** 保持定义 88.1 的
$\mathcal V_0,\mathcal V,E_2,D=(\beta_*,1)$ 完全不变：
原有符号均值带、预定内带、完整原 floor 单元的开放中三分之一，
以及合法 $Q_n$ 均不随规范函数改变。
设 $f$ 在零的某个右邻域连续、正、非减，趋于零，且

$$
\frac{f(t)}t\ \text{随 }t\text{ 非增},\qquad
\frac{f(t)}t\longrightarrow\infty\quad(t\downarrow0).
\tag{89.1}
$$

只需在该邻域规定 $f$；以下级数忽略有限个尚未进入定义域的项。
置

$$
\Sigma(f)=\sum_n Q_n^2f(Q_n^{-3}).
\tag{89.2}
$$

**定理 89.2（完整规范律及删除同步集合）。** 对每个满足 (89.1) 的 $f$、
每个非空开区间 $J\subset D$，以及

$$
A\in\{\mathcal V_0,\mathcal V,
             \mathcal V_0\setminus E_2,\mathcal V\setminus E_2\},
$$

有

$$
\mathcal H^f(A\cap J)=
\begin{cases}
0,&\Sigma(f)<\infty,\\
\infty,&\Sigma(f)=\infty.
\end{cases}
\tag{89.3}
$$

不要求级数项单调、正则变化或有正的上极限；
发散而趋零且振荡的项也在结论内。

证明。发散部分使用 Beresnevich–Dickinson–Velani 的局部 ubiquity 推论，
再使用 Durand 的大交集类定理；以下核对原单元与这些经典定理的全部接口。
其中 Durand 的严格规范顺序约定为
$f\prec g$ 表示 $f(t)/g(t)$ 随 $t\downarrow0$ 单调趋于无穷，
即这里 $f$ 是数值较大的规范。
其大交集类 $\mathcal G^g(O)$ 对可数交封闭，
并对每个 $f\prec g$ 给局部 $\mathcal H^f$ 无穷测度；
不能将这个结论直接用于 $f=g$。

先由 (89.1) 得固定缩放常数 $c>0$ 的比较

$$
\min(1,c)f(t)\le f(ct)\le\max(1,c)f(t)
\tag{89.4}
$$

（两参数均在定义域内）。
所以半径与直径、原单元宽度中的固定因子不改变级数收敛分类。

固定非退化闭区间 $\Omega\Subset J$，令 $O=\operatorname{int}\Omega$，
并在稍大的 $K\Subset D$ 内工作。
对一个固定有符号均值带，第 88 章给选中单元中点 $x_{n,j}$ 的分离
$c_KQ_n^{-2}$、任意长 $t$ 区间的上计数 $C_K(1+tQ_n^2)$，
以及每个已经固定的区间 $B\subset K$ 在所有充分晚层的下计数
$a_{\sigma,\mathrm{band}}|B|Q_n^2$。
后者的阈值可依赖 $B$，下密度不要求对所有带统一。

在 $\Omega$ 上取归一化 Lebesgue 测度 $m$；
其相对度量球的测度与半径同阶，包括端点附近的球。
将该固定带在 $\Omega$ 内的中点作为点状 resonant sets，权重取 $Q_n$。
每个有界权重范围只有有限标签；取上端序列 $u_n=Q_n$，
下端 $l_n$ 位于 $Q_{n-1}$ 与 $Q_n$ 之间，每块恰含该原层。
选择

$$
\rho(t)=c_0t^{-2},\qquad 0<c_0<c_K/4.
\tag{89.5}
$$

对每个固定相对球 $B\subset\Omega$，先在内部选长与 $m(B)|\Omega|$ 同阶的
区间核心，再取充分晚的原层。下计数及中点分离使半径 $\rho(Q_n)$ 的球
两两不交且位于 $B$，并给

$$
m\!\left(B\cap\bigcup_{j\text{ 属于第 }n\text{ 层}}
                     B(x_{n,j},\rho(Q_n))\right)
 \ge c_{\sigma,\mathrm{band}}m(B).
\tag{89.6}
$$

常数不依赖测试球，起效层可以依赖它。
这验证了局部 $m$-ubiquity；测度条件 M2 的指数为一，
点状共振的交叠指数为零，交叠条件由区间长度直接满足。
又
$\rho(Q_{n+1})/\rho(Q_n)=(Q_n/Q_{n+1})^2\le1/4$ 最终成立，
故 $\rho$ 对原上端序列满足经典定理要求的几何衰减。
这不是级数项的正则性假设。

Beresnevich–Dickinson–Velani 原推论因此给：对递减趋零的逼近函数 $\psi$，
若

$$
\sum_nQ_n^2\psi(Q_n)=\infty,
\tag{89.7}
$$

则 $\limsup_{n,j}B(x_{n,j},\psi(Q_n))$ 在 $O$ 有全 Lebesgue 测度。
原推论允许由 $\rho$ 的几何衰减控制其双重和，
不要求 $\psi(Q_n)/\rho(Q_n)$ 单调。
局部正比例覆盖是 (89.6)；全测度是此经典推论的结论，两者没有混同。

设现在 $\Sigma(f)=\infty$。需要一个严格较小而仍保留发散的规范。
令 $r_n=Q_n^{-3}$、$a_n=Q_n^2f(r_n)$、
$D_f(t)=f(t)/t$、$y_n=D_f(r_n)\uparrow\infty$。
选阈值 $T_{k+1}\ge4T_k$，使

$$
\sum_{\{n:T_k\le y_n<T_{k+1}\}}a_n\ge k+1.
\tag{89.8}
$$

每个固定阈值下只有有限项，正项级数的任一尾部仍发散，
故可逐次选择这样的阈值。
规定 $\Theta(T_k)=k$，在相邻阈值间按 $\log y,\log\Theta$ 线性插值，
在 $T_1$ 以下取一。各段对数斜率位于 $(0,1/2]$。
因此 $\Theta$ 连续非减、趋于无穷，
$y/\Theta(y)$ 非减且趋于无穷。
定义

$$
g(t)=\frac{f(t)}{\Theta(D_f(t))}.
\tag{89.9}
$$

$g$ 正、连续、非减且趋零：当 $t$ 增大时，
$f(t)$ 与 $1/\Theta(D_f(t))$ 都非减。
其比值 $g(t)/t=D_f(t)/\Theta(D_f(t))$ 随 $t$ 非增并在零处趋无穷。
同时 $f/g=\Theta(D_f)$ 单调趋无穷，即 $f\prec g$。
在 (89.8) 的第 $k$ 块，$\Theta(y_n)\le k+1$，所以

$$
\sum_nQ_n^2g(Q_n^{-3})=\infty.
\tag{89.10}
$$

这是经典辅助规范削薄步骤的具体实现，同一个 $g$ 用于全部有符号带。
它也满足 (89.4)，不要求 $a_n$ 单调。

取共同小 $\kappa_0>0$，使
$B(x_{n,j},\kappa_0Q_n^{-3})$ 内含于选中原单元的开放中三分之一；
第 88 章的宽度界使该常数可对所有带共同选定，各带仍可有自己的起效层。
为兼容严格递减的逼近函数约定，取充分大 $t$ 上

$$
\psi(t)=\left(\frac12+\frac1{2(1+t)}\right)g(\kappa_0t^{-3}).
\tag{89.11}
$$

它严格递减、趋零，位于 $g(\kappa_0t^{-3})$ 的一半与一倍之间。
由 (89.4)、(89.10) 满足 (89.7)，故每个固定带的放大球 limsup 在 $O$ 全测。
每层中点有限，球半径趋零，所以在有界区域中，
半径超过任意正阈值的标签只有有限个，满足 Durand 的逼近族条件。

令 $g_*^{-1}(u)=\inf\{t:g(t)\ge u\}$，在近零区域之外作非减延拓。
Durand 的 Theorem 2 将上述全测度球族缩为半径
$g_*^{-1}(\psi(Q_n))$ 的 limsup，并断言所得集合属于 $\mathcal G^g(O)$。
连续非减的 $g$ 不必严格递增，因为

$$
g_*^{-1}(\psi(Q_n))
 \le g_*^{-1}(g(\kappa_0Q_n^{-3}))
 \le\kappa_0Q_n^{-3}.
\tag{89.12}
$$

故缩球 limsup 包含于原来的
$\limsup_n U_{n,\sigma,B}$。
后者为 $G_\delta$；原 Proposition 1(e) 的向上封闭性给它也属于
$\mathcal G^g(O)$。所有有符号带使用同一个 $g,O$，
Theorem 1(a) 的可数交封闭性遂给 $\mathcal V_0\in\mathcal G^g(O)$。
这里按局部类的约定在 $O$ 内理解该集合。
由 $f\prec g$，Theorem 1(c) 及局部限制性质给
$\mathcal H^f(\mathcal V_0\cap O)=\infty$。
包含关系证明 $\mathcal V_0,\mathcal V$ 的发散结论。
原开放中三分之一及均值要求均未改变，规范只决定其中用于证明测度的子集。

若 $\Sigma(f)<\infty$，固定 $K\Subset D$。
$\mathcal V$ 中的参数有无穷多正根均值落入 $[1,2]$；
实际相对均值桥将其代理值最终限制于 $[1/2,4]$。
每原层只有 $O_K(Q_n^2)$ 个根指标，每指标只有 $O(1)$ 个可能 $L$，
对应单元直径为 $O_K(Q_n^{-3})$。尾覆盖的 $f$-代价由

$$
C_K\sum_{n\ge n_0}Q_n^2f(C_KQ_n^{-3})
 \le C'_K\sum_{n\ge n_0}Q_n^2f(Q_n^{-3})
\tag{89.13}
$$

控制并趋零。可数紧区间穷尽 $D$，给两集合零测度。

最后处理删去 $E_2$。收敛时结论自动传给子集。
发散时取

$$
h(t)=\min\{f(t),\sqrt t\}.
\tag{89.14}
$$

它仍满足 (89.1)，因为
$h(t)/t=\min\{f(t)/t,t^{-1/2}\}$ 保持所需单调性与无穷极限。
其级数项为
$\min\{Q_n^2f(Q_n^{-3}),Q_n^{1/2}\}$，
仍发散：若第一项在无穷多指标超过第二项，截断后各该项趋于无穷；
否则截断仅改变有限项。
已证规范律给 $\mathcal H^h(\mathcal V_0\cap J)=\infty$。
第 86 章 $\dim_HE_2\le38/87<1/2$ 给
$\mathcal H^{1/2}(E_2)=0$，而 $h\le\sqrt t$，
故 $\mathcal H^h(E_2)=0$。
删去该零测部分后仍有无穷 $h$-测度，再由 $h\le f$ 得 (89.3)。
这不声称任意发散规范都使 $\mathcal H^f(E_2)=0$。证毕。

**命题 89.3（振荡且趋零的层代价）。** 令
$a_n=1/n$（偶数 $n$）、$a_n=1/n^2$（奇数 $n$）。
存在满足 (89.1) 的规范，使每个充分晚 $n$ 都有
$Q_n^2f(Q_n^{-3})=a_n$。
因此 (89.3) 的无穷测度结论覆盖层代价趋零、相邻比值无界振荡的情形。

证明。在 $r_n=Q_n^{-3}$ 上规定 $f(r_n)=a_nQ_n^{-2}$，
相邻结点之间作幂函数插值，其指数为

$$
s_n=\frac{2\ln(Q_{n+1}/Q_n)+\ln(a_n/a_{n+1})}
                  {3\ln(Q_{n+1}/Q_n)}\in(0,1)
\tag{89.15}
$$

（充分晚时）。后者因第二项为 $O(\ln n)$ 而原层对数比远大于它。
插值连续递增，$f(t)/t$ 在各段及接点保持非增；
结点上的 $f(r_n)/r_n=a_nQ_n\to\infty$，$f(r_n)\to0$。
故满足 (89.1)。偶数项子级数发散，应用定理 89.2 即得结论。
若所有 $a_n$ 均改为 $1/n^2$，同一构造给收敛且零测度的规范。证毕。

$E_2$ 的存在性与空性仍未解决，参数集的测度不充当统计先验，
两个根的子序列不被改为同一原层。

## 追加锚（89 章后）

## 90. 带噪能量观测后的第三阶后验覆盖

**定义 90.1（精确熵中心与最小覆盖数）。** 保持定义 87.1 的原固定幅度、
固定 $\beta\in(1/2,1)$、全部取整、完整得分组、均匀支持先验后验及同一个
$Y=T+\sigma_MG$，仍假定
$L_M=\ln(1/\sigma_M)\to\infty$、$L_M=o(Q^3)$。
沿用第 68 章的完整率域 $\mathcal I$、率函数 $I$、$c_q=\phi(1-\beta)/\beta$，
并置

$$
\ell_*=\operatorname{Leb}\{u\in\mathcal I:I(u)<c_q\},
\qquad v=\ell_*/2>0.
\tag{90.1}
$$

$v$ 是自然单位信息方差的首阶系数，与能量极限方差 $\nu=2g_0$ 不同。
对每个有限数据纤维，写

$$
\begin{aligned}
f_x(y)&=\sum_rP_x(r)\varphi_{\sigma_M}(y-t_x(r)),\\
p_x(r\mid y)&=\frac{P_x(r)\varphi_{\sigma_M}(y-t_x(r))}{f_x(y)},\\
J_y(r)&=-\ln p_x(r\mid y),\qquad
H_x(y)=\sum_rp_x(r\mid y)J_y(r),\\
N_\varepsilon(x,y)&=
\min\{|A|:\sum_{r\in A}p_x(r\mid y)\ge1-\varepsilon\}.
\end{aligned}
\tag{90.2}
$$

以下 $\varepsilon\in(0,1)$ 固定，$z=\Phi^{-1}(1-\varepsilon)$，
$\varphi$ 是标准正态密度。所有信息量使用自然对数。
$H_x(y)$ 始终是同一输出处的精确条件熵。

**定理 90.2（常数精度的固定误差覆盖）。** 定义

$$
C_\varepsilon=\frac{z^2-1}{3}+\ln\varphi(z)-\frac12\ln v.
\tag{90.3}
$$

对任意 $\eta>0$，有

$$
\int f_x(y)\,
\mathbf1_{\left\{
\left|\ln N_\varepsilon(x,y)-H_x(y)-Q\sqrt v\,z
                  +\ln Q-C_\varepsilon\right|>\eta\right\}}dy
\longrightarrow0
\tag{90.4}
$$

在两种原实际实验内分别对固定真实支持的数据概率一致成立。
即对该积分超过任意 $\tau>0$ 的数据事件，对 $|S_0|=q$ 取概率上确界后趋零。
特别地，在此输出积分概率意义下，

$$
\ln N_\varepsilon(x,Y)
=H_x(Y)+Q\sqrt v\,z-\ln Q
 +\frac{z^2-1}{3}+\ln\varphi(z)-\frac12\ln v+o_{\mathbb P}(1).
\tag{90.5}
$$

不将结论加强为每个输出成立或未界定的对数余项期望收敛。

证明。需要局部信息谱精度，以下先证明一个带速率尺度的条件 Gamma 比较。
仍用 $\mathsf Q_x$ 表示校准的独立二项组参考，
$L_x=dP_x/d\mathsf Q_x$、$a_x=\|L_x-1\|_{2,\mathsf Q_x}$，
$d_j=C_jp_j(1-p_j)$、$B^2=q/Q^{5/2}$、$v_j=d_j/B^2$、
$U_j=(R_j-C_jp_j)/B$ 和 $e_j=(\mu_j-C_jp_j)/B$。
第 82、87 章给
$0<L_x\le C$、$a_x=O_{\mathbb P}(Q^{-5/2})$、
$\|e_D\|\le a_x\sqrt{V_D}$，其中 $V_D=\sum_Dv_j$。
这些是完整计数向量的条件化控制，不是路径观测行的独立性。

**过渡组的有界数目。** 在共同良好数据事件上取固定 $A_0=3600$，令

$$
\mathcal B_x=\{j:d_j\ge Q^{A_0}\},\qquad N_x=|\mathcal B_x|.
\tag{90.6}
$$

有

$$
N_x=\ell_*Q^2+O(1),\qquad
|\{j\notin\mathcal B_x:C_j>0\}|=O(1).
\tag{90.7}
$$

为证明这一精度，原一行／两行比较及完整域 Stirling 界给

$$
\ln m_j=Q^3\{c_q-I(\bar u_j)\}+O(\ln Q),
\quad u_j=j/Q^2,\quad \bar u_j=\max(u_j,-b/\vartheta),
\tag{90.8}
$$

其中 $m_j$ 是原混合 Poisson 行均值，$\vartheta$ 是原固定斜率。
这包括零计数端点：$t\ln t$ 的模连续性和
$\ln(n!)=n\ln n-n+O(\ln Q)$ 在计数范围内给同一误差。
可行格点低于左端点的偏差为 $O(Q^{-3}+|\vartheta-P/Q|)$，只涉及有界个点。
$I$ 严格凸，正根导数非零，内部负根导数也非零；
若 $I(-b/\vartheta)=c_q$，其右导数趋于负无穷，绝对值仍局部有正下界。
因此小 $t$ 下 $\{|I-c_q|\le t\}$ 至多有两个分支，总长度为 $O(t)$。

由原实际均值方差界，所有 $m_j<Q^{-10}$ 的组同时为空，
其失败概率至多 $CQ^{-8}$；所有 $m_j>Q^{A_0+10}$ 的组同时满足
$C_j\ge m_j/2$，其失败概率至多
$CQ^{2-A_0-10}+CQ^2e_{\rm row}$。
良好事件上 $p_j\in[1/4,3/4]$，故这些大组都进入 $\mathcal B_x$。
其余可能有非零占据的过渡点位于宽 $O(\ln Q/Q^3)$ 的率带，
格距为 $Q^{-2}$，点数至多 $C(1+\ln Q/Q)=O(1)$。
在正率区间计数格点即得 (90.7)。固定证明截断取在正根以外，
截断失败仍仅以其数据概率删除，不改原完整窗口。

令 $\mathcal S=-\ln\mathsf Q_x(R)$、$\widetilde h=\mathbb E_{\mathsf Q_x}\mathcal S$，
$s=\mathcal S-\widetilde h=\sum_js_j$。
单组二项全点界和中心 Bernoulli 矩展开给每个固定阶的 $s_j$ 中心矩一致有界；
特别地 $\mathbb Es^2\le CQ^2$、$\mathbb Es^4\le CQ^4$、$\mathbb E|s|^6\le CQ^6$。
用第 87 章同一单调量化耦合，在 $\mathcal B_x$ 上取独立标准正态 $Z_j$。
(87.9) 及其 Stirling 余项给

$$
\left\|s_j-\frac{Z_j^2-1}{2}\right\|_2\le Cd_j^{-1/36}.
\tag{90.9}
$$

定义 $S_B=\frac12\sum_{\mathcal B_x}(Z_j^2-1)$，
$s_b=\sum_{j\notin\mathcal B_x}s_j$。保留外部原乘积计数，则 $S_B,s_b$ 独立，
$s_b$ 中心且每个固定阶矩有界，并有

$$
\varepsilon_s:=\|s-S_B-s_b\|_2\le CQ^{2-A_0/36}=CQ^{-98}.
\tag{90.10}
$$

此信息权重误差不除以测量噪声。

**在原噪声尺度上的平方标量误差。** 取第 82 章移动核心
$\mathcal C_R=\{|j\delta|\le R_M\}$，
$R_M^2=\sqrt{Q^3(L_M+\ln Q+1)}$。
其组数 $o(Q^2)$，且在良好事件上
$d_{\min}\ge\exp(c_qQ^3/2)$，因而最终包含于 $\mathcal B_x$。
记保持全部精确 $e_j,v_j$ 和外部中心截距的参考为 $T_R^{\rm G}$。
在同一计数／正态耦合下令
$D_1=\mathbb E|T-T_R^{\rm G}|$、$D_2=\mathbb E|T-T_R^{\rm G}|^2$。
对所有固定 $a\ge0,b>0$，

$$
Q^a\sigma_M^{-b}(D_1+\sqrt{D_2})\longrightarrow0.
\tag{90.11}
$$

这里需补足平方版本。由 (90.9) 使用的四阶范数量化界，核心误差的 $L^2$ 范数至多
$C\delta^{-1/2}d_{\min}^{-1/36}(1+a_x)V$。
在 $\mathcal O=K_M\setminus\mathcal C_R$ 上，精确中心展开给

$$
\|T-T^{\rm core}\|_2
\le\delta^{-1/2}
\left[\left(2\sum_{\mathcal O}v_j^2+B^{-2}V_{\mathcal O}\right)^{1/2}
                       +2a_xV_{\mathcal O}\right].
\tag{90.12}
$$

常数截距精确抵消。原实际行界使尾部一阶、平方方差质量的期望
分别受 $Ce^{-cR_M^2}$、$C\delta e^{-cR_M^2}+CB^{-2}$ 及
$Q^Ce^{-cQ^3}$ 型项控制。
在 Markov 界中平方所需阈值后，
$R_M^2/(L_M+\ln Q+1)\to\infty$、
$L_M=o(Q^3)$ 和 $B^{-2}=Q^{5/2}/q$ 支付每个固定
$Q^a\sigma_M^{-b}$。
核心可再限制 $V\le Q$，其失败概率趋零；指数 $d_{\min}$ 支付剩余因子。
得 (90.11)。实际后验密度误差 $a_x$ 与任何多项式中心误差均未除以噪声。

**中心化后的条件分布比较。** 精确 Bayes 恒等式为

$$
J=S-L_M+\tfrac12\ln(2\pi)+G^2/2+\ln f_x(Y),
\qquad S=-\ln P_x(R).
\tag{90.13}
$$

故令 $K_1=S-\widetilde h+G^2/2$ 后，
$J-H_x(Y)=K_1-\mathbb E[K_1\mid Y]$；
全部只依赖输出的项精确消去。

所用有限比较如下。设两个潜变量／输出联合律为 $\mu,\zeta$，
输出密度 $f,g$，联合 TV 距离至多 $e$。
同一坐标空间上的 $U_1,U_2$ 满足
$\mathbb E_\mu|U_1-U_2|\le\epsilon$，
各自二阶矩之和至多 $CQ^2$。
若 $\zeta$ 下 $U_2$ 的每个条件密度至多 $C/Q$，
两个非归一化一阶矩输出密度的 $L^1$ 距离至多 $w$，则任意 $\eta>0$ 下

$$
\int f\,d_K\!\left(
\mathcal L_\mu(U_1-\mathbb E_\mu[U_1\mid y]\mid y),
\mathcal L_\zeta(U_2-\mathbb E_\zeta[U_2\mid y]\mid y)\right)
\le C\left(e+\frac\epsilon\eta+\frac\eta Q+\frac wQ+\sqrt e\right).
\tag{90.14}
$$

若比较的是同一 $(U,y)$ 坐标联合律，可去掉含 $\epsilon,\eta$ 的两项。
证明此界只需条件 TV 积分、Markov 和密度的区间界。
对条件均值，用公共输出子测度 $h_0=\min(f,g)$；
若 $A_1,A_2$ 是两个非归一化矩密度，则

$$
h_0|A_1/f-A_2/g|
\le |A_1-A_2|+(f-h_0)|A_1/f|+(g-h_0)|A_2/g|.
$$

后两项积分由各自的条件 Jensen 与 Cauchy–Schwarz 控制为 $CQ\sqrt e$。
均值平移再乘条件密度上界 $C/Q$；公共子测度外只支付 $O(e)$。
这证明 (90.14)，没有把无界条件均值按 TV 直接转移。

在完整扩展量化空间上比较

$$
d\mu_1=L_x(R)d\mathsf Q_x^{\rm ext}\,
               \varphi_\sigma(y-T)\,dy,\qquad
d\mu_2=d\mathsf Q_x^{\rm ext}\,
               \varphi_\sigma(y-T_R^{\rm G})\,dy.
\tag{90.15}
$$

令 $g_1=(y-T)/\sigma$、$g_2=(y-T_R^{\rm G})/\sigma$，
并分别取
$K_1=S-\widetilde h+g_1^2/2$、
$K_2=S_B+s_b+g_2^2/2$。
噪声变量未作为同一坐标追加到 (90.15)，因为残差图随参考标量改变。
有限误差满足

$$
\begin{aligned}
e_1&\le C(a_x+D_1/\sigma),\\
\epsilon_1:=\mathbb E_{\mu_1}|K_1-K_2|
&\le C(a_x+\varepsilon_s+\sqrt{D_2}/\sigma+D_2/\sigma^2),\\
w_1&\le C(Qa_x+a_x+Q\sqrt{D_1/\sigma}
                         +\varepsilon_s+D_1/\sigma).
\end{aligned}
\tag{90.16}
$$

第一式是完整向量密度与正态平移界。
第二式使用 $P_x$ 下 $\mathbb E|\ln L_x|\le Ca_x$ 和
$|g_1^2-g_2^2|\le2|g_1||T-T_R^{\rm G}|/\sigma
                         +|T-T_R^{\rm G}|^2/\sigma^2$。
第三式先中心化 $s$，使换密度的代价为 $CQa_x$；
正态核的 $L^1$ 差 $k$ 满足
$k\le\min(2,C|T-T_R^{\rm G}|/\sigma)$，故信息权重的平移代价
至多 $CQ\sqrt{D_1/\sigma}$。
对残差平方使用正核
$\psi_\sigma(t)=(t/\sigma)^2\varphi_\sigma(t)$，
其积分为一、导数 $L^1$ 范数为 $C/\sigma$。
这给剩余的 $Ca_x+CD_1/\sigma$，并保留同一个测量变量。
两侧各自的 $K$ 二阶矩至多 $CQ^2$。

$\mu_2$ 下 $\mathcal B_x\setminus\mathcal C_R$ 的正态信息和
独立于输出、核心和 $s_b$，是形状
$(N_x-|\mathcal C_R|)/2\sim vQ^2$ 的中心 Gamma。
其密度至多 $C/Q$，故 $K_2$ 的每个条件密度也有此界。
在 (90.14) 取 $\eta=Q^{-1/2}$，由
$a_x=O_{\mathbb P}(Q^{-5/2})$、(90.10)—(90.11)，得到

$$
\int f_x\,d_K\!\left(
\mathcal L(J-H_x(y)\mid y),
\mathcal L_{\mu_2}(K_2-\mathbb E_{\mu_2}[K_2\mid y]\mid y)\right)dy
=o_{\mathbb P}(Q^{-1}).
\tag{90.17}
$$

**二维正态密度使能量核心缩小。** 取固定足够大 $D$，
$H_M^2=D\ln Q$、$\mathcal H=\{|j\delta|\le H_M\}$，
$m_H=|\mathcal H|=O(Q^{1/2}\sqrt{\ln Q})=o(Q)$。
它最终包含于 $\mathcal C_R$。保留全部中心截距，定义

$$
T_H^{\rm G}
=\delta^{-1/2}
\left[\sum_{\mathcal H}(\sqrt{v_j}Z_j-e_j)^2
-V_{\mathcal H}+\|e_{K_M\setminus\mathcal H}\|^2\right],
\qquad S_H=\frac12\sum_{\mathcal H}(Z_j^2-1).
\tag{90.18}
$$

则 $(S_H,T_H^{\rm G})$ 的联合密度 $p_H$ 满足

$$
\|\partial_t p_H(s,t)\|_{L^1(\mathbb R^2)}\le C\delta^{-1/2}.
\tag{90.19}
$$

以下核对这一步的有限维非退化性。取 128 个不同核心指标组成 64 个互不相交的对，
每对一端的空间坐标趋于零，另一端趋于一。
$b_j=v_j/\delta$ 落在有界正区间内，两个区间因 $\rho(0)>\rho(1)$ 而分离；
$c_j=e_j/\sqrt{v_j}$ 在这些指标上一致趋零，可限制 $|c_j|\le1$。
在此固定块上置
$F_1=\frac12\sum(Z_j^2-1)$、
$F_2=\sum b_j((Z_j-c_j)^2-1)$。
梯度 Gram 矩阵 $\Gamma$ 的行列式由 Cauchy–Binet 给

$$
\det\Gamma\ge4\sum_{\text{64 对 }(i,j)}P_{ij}^2,\qquad
P_{ij}=(b_j-b_i)Z_iZ_j+b_ic_iZ_j-b_jc_jZ_i.
\tag{90.20}
$$

条件于 $Z_j$，多项式关于 $Z_i$ 的斜率小于 $\eta$ 的概率至多 $C\eta$；
在其补集上，$|P_{ij}|\le u$ 的概率至多 $Cu/\eta$。
取 $\eta=\sqrt u$ 得 $\Pr(|P_{ij}|\le u)\le C\sqrt u$。
各对独立，因此

$$
\Pr(\det\Gamma\le t)\le Ct^{16}\quad(0<t\le1),
\qquad \mathbb E(\det\Gamma)^{-r}\le C_r\quad(r<16).
\tag{90.21}
$$

令 $\mathfrak u=\sum_b(\Gamma^{-1})_{2b}\nabla F_b$。
它对 $F_1,F_2$ 的方向导数分别为零、一；
正态散度 $\mathfrak h=Z\cdot\mathfrak u-\operatorname{div}\mathfrak u$
由多项式除以 $\det\Gamma$ 或其平方组成。
固定维正态矩与 (90.21) 给 $\mathbb E|\mathfrak h|\le C$。
先在行列式远离零处光滑截断，再用逆矩界去掉截断，正态分部积分给
$\mathbb E[\partial_2\zeta(F)]=\mathbb E[\zeta(F)\mathfrak h]$。
梯度几乎处处秩二；在非零二列 Jacobian 子式的可数局部坐标覆盖内，
变元公式与 Fubini 给 $(F_1,F_2)$ 的密度 $p$。
其弱导数为
$\partial_2p=-p\,\mathbb E[\mathfrak h\mid F]$，故 $L^1$ 范数至多 $C$。
第二坐标乘 $\sqrt\delta$，再卷积其余独立核心项和常数平移，即得 (90.19)。
这是经典逆梯度／散度方法的具体二维条件验证。

在同一正态空间保留 $K=S_B+s_b+G^2/2$，取
$Y_R=T_R^{\rm G}+\sigma G$、$Y_H=T_H^{\rm G}+\sigma G$。
二标量之差为

$$
T_R^{\rm G}-T_H^{\rm G}
=\sum_{\mathcal C_R\setminus\mathcal H}
  [w_j(Z_j^2-1)-2w_jc_jZ_j],\qquad w_j=v_j/\sqrt\delta.
\tag{90.22}
$$

它独立于 $\mathcal H$ 内的正态变量。
条件于核心外全部变量及同一个 $G$，比较只平移联合密度的第二坐标。
由 (90.19)，

$$
e_H:=d_{\rm TV}(\mathcal L(K,Y_R),\mathcal L(K,Y_H))
\le C\delta^{-1/2}\mathbb E|T_R^{\rm G}-T_H^{\rm G}|
\le C\delta^{-1}(1+a_x)V_{\mathcal C_R\setminus\mathcal H}.
\tag{90.23}
$$

这里没有逆噪声因子。原行尾界为
$\sup_{S_0}\mathbb E_{S_0}V_{|j\delta|>H_M}
\le Ce^{-c_{\rm tail}H_M^2}+Q^Ce^{-cQ^3}$，
其中 $c_{\rm tail}>0$ 由正 Hessian 下界取得。
固定 $D>200/c_{\rm tail}$ 后，Markov 给 $e_H=o_{\mathbb P}(Q^{-40})$。
两个 $(K,Y)$ 联合律的一阶矩密度差至多 $CQ\sqrt{e_H}$：
对被两联合律之和支配的差测度用 Cauchy–Schwarz 即可。
各自条件密度仍由独立外部 Gamma 以 $C/Q$ 控制。
用 (90.14) 的同一坐标版本，中心条件律之输出积分距离为 $o_{\mathbb P}(1/Q)$。

**小核心的精确中心化。** 对 $\mathcal H$ 通道，令

$$
A_k=\frac12\sum_{\mathcal B_x\setminus\mathcal H}(Z_j^2-1),
\quad k_x=(N_x-m_H)/2,
\quad B_y=S_H+s_b+G^2/2-\mathbb E[S_H+s_b+G^2/2\mid Y_H=y].
\tag{90.24}
$$

$A_k$ 服从 $\operatorname{Gamma}(k_x,1)-k_x$，
独立于 $(Y_H,B_{Y_H})$；$\mathbb E[B_y\mid Y_H=y]=0$。
全方差公式给

$$
\int f_H(y)\mathbb E[B_y^2\mid y]dy\le C(m_H+1),\qquad
k_x=vQ^2+o(Q),\quad \sqrt{k_x}=Q\sqrt v+o(1).
\tag{90.25}
$$

设中心 Gamma 密度及 CDF 为 $p_k,F_k$。
特征函数模为 $(1+t^2)^{-k/2}$；Fourier 积分给
$\|p_k\|_\infty\le C/Q$、$\|p_k'\|_\infty\le C/Q^2$。
密度及导数在支撑左端也连续归零，故全实线 Taylor 界成立。
条件中心化消去一次项，从而

$$
\sup_t|\mathbb E[F_k(t-B_y)\mid y]-F_k(t)|
\le (C/Q^2)\mathbb E[B_y^2\mid y].
\tag{90.26}
$$

其输出积分为 $O(m_H/Q^2)=o(1/Q)$。
组合 (90.17)、(90.23)—(90.26)，并只对有界 CDF 距离更换输出测度，得到

$$
Q\int f_x(y)\sup_{t\in\mathbb R}
\left|\Pr_x(J_Y(R)-H_x(y)\le t\mid Y=y)-F_{k_x}(t)\right|dy
\longrightarrow0.
\tag{90.27}
$$

这一步同时保留全组信息、原标量及精确条件熵；
未直接删除可能接近 $Q^2$ 个组的大核心信息。

**边界计数与并列项。** 对中心 Gamma，
Stirling 展开及积分给，在固定紧 $z$ 区间一致地

$$
\begin{aligned}
\sqrt k\,p_k(\sqrt k\,z)
&=\varphi(z)\left[1+\frac{z^3-3z}{3\sqrt k}+O(k^{-1})\right],\\
F_k(\sqrt k\,z)
&=\Phi(z)+\frac{1-z^2}{3\sqrt k}\varphi(z)+O(k^{-1}).
\end{aligned}
\tag{90.28}
$$

积分余项可在 $|z|\le\sqrt{C\ln k}$ 内以正态密度乘固定多项式控制，
其外由 Gamma 母函数的 Chernoff 界取为 $O(k^{-2})$。
这是所用平滑 Gamma 家族的经典 Edgeworth 计算，
不对任意格点分布套用连续余项。
其 $1-\varepsilon$ 分位数满足

$$
t_k=Q\sqrt v\,z+\frac{z^2-1}{3}+o(1).
\tag{90.29}
$$

令 $d_y$ 为 (90.27) 内的 CDF 距离，$t_y$ 为实际中心信息的广义分位数。
$Qd_Y\to0$；Gamma 在 $t_k$ 附近的密度下界为 $c/Q$，
故任意固定 $\eta>0$ 下两个阈值 $t_k\pm\eta$ 的 CDF 间隔至少为 $c\eta/Q$，
推出 $t_y-t_k=o_{\mathbb P}(1)$。

使用有界、总变差为二的函数 $u\mapsto e^{u-t}\mathbf1_{u\le t}$，置

$$
\Lambda_{x,y}(t)=
\mathbb E[e^{J-H_x(y)-t}\mathbf1_{J-H_x(y)\le t}\mid y],
\qquad
\Lambda_k(t)=\int_0^\infty e^{-s}p_k(t-s)\,ds.
\tag{90.30}
$$

Stieltjes 分部积分给 $|\Lambda_{x,y}(t)-\Lambda_k(t)|\le2d_y$；
又 $|\Lambda_k(t)-p_k(t)|\le\|p_k'\|_\infty\le C/Q^2$。
因此

$$
Q\Lambda_{x,Y}(t_Y)\to\frac{\varphi(z)}{\sqrt v},\qquad
\ln\Lambda_{x,Y}(t_Y)
=-\ln Q+\ln\varphi(z)-\tfrac12\ln v+o_{\mathbb P}(1).
\tag{90.31}
$$

有限计数恒等式为

$$
N_{\rm all}(t)=
\#\{r:J_y(r)\le H_x(y)+t\}
=e^{H_x(y)+t}\Lambda_{x,y}(t).
\tag{90.32}
$$

最小覆盖按概率递减排列，取全体严格超过边界概率的点，
再取边界并列组中足够的点。由于 $F_k$ 连续，
实际 CDF 任一跳跃、特别是边界并列组总概率 $b_y$，至多为 $2d_y$。
故

$$
0\le\frac{N_{\rm all}(t_y)-N_\varepsilon(x,y)}{N_{\rm all}(t_y)}
\le\frac{b_y}{\Lambda_{x,y}(t_y)}=o_{\mathbb P}(1).
\tag{90.33}
$$

此式包括选取部分并列组时的整数舍入。
将 (90.29)、(90.31) 代入 (90.32)—(90.33)，得 (90.4)—(90.5)。证毕。

每个有限纤维只有有限个计数向量，正态核处处为正，
故上述条件熵、CDF、覆盖数和输出积分可测；
CDF 上确界可取有理阈值，最优覆盖可按固定字典序打破并列。
两种原实验的全部环境界对真实支持一致，例外数据只支付概率，
不将无界信息量乘以例外概率。
对联合数据／输出中的有界失败事件，原支持置换等变性把均匀先验平均
转为任意固定真实支持的同一概率；这不认定给定数据和已知支持时的单一正态输出律
等于先验混合 $f_x$。
未知方向仍经原共同对齐事件传递同一组、精确中心、标量和测量噪声。
若改用比特，(90.5) 全式除以 $\ln2$，不再加密度 Jacobian 常数。
结论不统一于趋近零或一的 $\varepsilon$，不涵盖零噪声或 $L_M$ 与 $Q^3$ 同阶，
也不给高效编码算法。第 84 章熵响应若另行代入，
其 $\nu+\sigma_M^2$ 分母仍须保留；本章没有用近似熵替换精确 $H_x(y)$。

## 追加锚（90 章后）

## 91. 固定切线构造的逃离与单侧复现刚性

**定义 91.1（固定切线与原共同单元）。** 保持第 81、83 章的固定幅度、
原合法 $Q=Q_n$、$N=Q^2$、完整得分组及两个实际实验。
沿用 $I,\Psi,F(u)=\phi/(\phi+I(u))$、精确 Gamma 曲线 $G_Q$、
$\ell_Q(j)=\ln\chi_{Q,j}$ 和共同规模单元

$$
\mathcal J_{Q,L}=
\left(\frac{\phi Q^3}{(L+1)\ln2},\frac{\phi Q^3}{L\ln2}\right].
\tag{91.1}
$$

固定紧参数区间 $K\Subset(\beta_*,1)$，所有根及切点留在稍大的固定内部弧。
记 $d_{0,Q}=k_0-aQ^3\in(-1,0]$、$\eta=\ln((1+r)/(1-r))$。
对一个固定既约斜率 $s=p/d\in(-1,0)$，令

$$
\Psi'(u_s)=s,\quad \beta_s=F(u_s),\quad
G_Q'(t_{Q,s})=s,\quad h_{Q,s}(x)=G_Q(x)-sx.
\tag{91.2}
$$

第 81 章的严格凸性保证唯一性；$F'<0$ 在这些紧弧上与零分离。
本章的复现始终指同一个参数属于无穷多个原单元。
第 83 章已给每层可取新参数的局部构造，二者量词不同。

**引理 91.2（精确修正的符号与整单元位置）。** 令 $A_Q$ 如 (76.13)，
$R_Q(u)=[A_Q(\Psi(u))-A_Q(u)]/I'(\Psi(u))$。则统一有

$$
-C_K\le R_Q(u)\le-c_K<0.
\tag{91.3}
$$

若 $L$ 是 $-\ell_Q(j)/\ln2$ 的任一最近整数，
则对整个 $\mathcal J_{Q,L}$ 中的参数统一有

$$
\beta=F(j/N)-\frac{3F(j/N)^2}{\phi}\frac{\ln Q}{Q^3}
                    +O_K(Q^{-3}).
\tag{91.4}
$$

这里 $j/N$ 位于所选正根紧弧，最近整数的并列选择均允许。

证明。原幅度恒等式给
$\vartheta a-b=\phi/[-\ln(1-r)]>0$。
直接对含原 count floor 的 $A_Q$ 求导，得到

$$
A_Q'(x)=-\frac12\left(\frac1{a+x}+\frac{\vartheta}{b+\vartheta x}\right)
 +d_{0,Q}\frac{\vartheta a-b}{(a+x)(b+\vartheta x)}<0.
\tag{91.5}
$$

两个项均非正，第一项严格为负。
因此 $A_Q(\Psi(u))-A_Q(u)$ 在紧弧上有统一正上下界；
负根导数 $I'(\Psi(u))<0$ 与零分离，给 (91.3)。
原精确 Stirling 展开为

$$
\ell_Q(j)=-Q^3[\phi+I(j/N)]-3\ln Q
       +\ln2-d_{0,Q}\eta+A_Q(j/N)+O_K(Q^{-3}).
\tag{91.6}
$$

最近整数误差与单元内部的规模相位均有界。
将此式代入 $\beta=\phi Q^3/(L\ln2+\rho\ln2)$，$0\le\rho<1$，
展开倒数即得 (91.4)。它保留原半开单元的全部点，
不要求穿过规模跳点时可微。证毕。

**定理 91.3（有限固定切点的环形窗口没有复现）。** 固定有限个上述斜率，
对每个斜率固定 $0<A_s<B_s<\infty$。
在每个原合法层，取任意满足

$$
j\in t_{Q,s}+[A_sQ,B_sQ]
\quad\text{或}\quad
j\in t_{Q,s}-[A_sQ,B_sQ]
\tag{91.7}
$$

的整数 $j$，按引理 91.2 选择规模整数并取整个原单元。
令 $\mathcal A_n$ 为这些单元的任意子族之并；可以仅保留已成功配对的单元。
则

$$
\limsup_{n\to\infty}\mathcal A_n=\varnothing.
\tag{91.8}
$$

证明。由 (83.13) 及隐函数展开，

$$
t_{Q,s}=Nu_s-Q^{-1}\frac{R_Q'(u_s)}{\Psi''(u_s)}+O_K(Q^{-4}).
\tag{91.9}
$$

在右窗口中 $j/N-u_s\in[A_s/Q,B_s/Q]+O_K(Q^{-3})$。
$F'$ 的严格负性和 (91.4) 给正数 $c_s,C_s$，使整个生成单元满足

$$
c_s/Q\le\beta_s-\beta\le C_s/Q.
\tag{91.10}
$$

左窗口相应为 $c_s/Q\le\beta-\beta_s\le C_s/Q$。
$O(\ln Q/Q^3)$ 的规模修正与 $O(Q^{-3})$ 单元宽度均不能跨过该间隔。
固定参数若不同于有限个 $\beta_s$，它与此有限集有正距离，最终不属于任何单元；
若等于其中一个，自己的窗口排除它，其他切点的窗口最终也排除它。
故每点只命中有限次，得到 (91.8)。证毕。

适当的固定 $A_s,B_s$ 确实仍能在每个晚期层产生配对单元：
第 81 章的 $c/Q^2\le h''\le C/Q^2$ 使窗口内相位上升超过常数，
在 $d\mathbb Z$ 上相邻值差为 $O(d/Q)$，跨过整数后给
$|\ell_Q(j)-\ell_Q(k)|\le C_Kd$。
这就是已有局部定理，均值界对固定切点有限。
定理 91.3 说明此特定族虽逐层有单元，却不能通过嵌套得到固定参数。
它不排除变化的切点、增长的分母或更靠近切点的交点，也不判定 $E_2$ 为空。

**定理 91.4（首个上方交点的固定参数刚性）。** 对一个固定 $p/d$，
精确使用第 83 章的如下规则：

$$
\begin{aligned}
m_Q&=\lceil d h_{Q,s}(t_{Q,s})\rceil,\qquad
\omega_Q=m_Q-dh_{Q,s}(t_{Q,s}),\\
h_{Q,s}(x_*)&=m_Q/d,\qquad x_*\ge t_{Q,s},\\
pj+m_Q&\equiv0\pmod d,\qquad |j-x_*|\le d/2,\qquad
k=(pj+m_Q)/d.
\end{aligned}
\tag{91.11}
$$

取该剩余类中距 $x_*$ 最近的整数 $j$，再取 $-\ell_Q(j)/\ln2$ 的最近整数 $L$；
并列时包含全部选择。记所得单元之并为 $\mathcal B_{n,s}$。
则

$$
\limsup_n\mathcal B_{n,s}\subseteq\{\beta_s\}.
\tag{91.12}
$$

若 $\beta_s$ 沿某子序列属于这些单元，则沿该子序列

$$
\begin{aligned}
j-t_{Q,s}&=-\frac{3\ln Q}{QI'(u_s)}+O_{K,d}(Q^{-1})<0,\\
0\le\omega_Q&\le C_Kd^3/Q^2,\\
\frac{\bar c_{Q,j}^{\mathcal E}(\beta_s)}
     {\bar c_{Q,k}^{\mathcal E}(\beta_s)}&\longrightarrow1
\quad(\mathcal E=pair,path).
\end{aligned}
\tag{91.13}
$$

任何由此规则产生的联合正极限均为 $(\theta,\theta)$，
其中 $2^{-1/2}\le\theta\le2^{1/2}$。

证明。(83.3) 在固定 $d$ 时趋零，且单元宽度也趋零，给 (91.12)。
设固定参数发生命中。原实际均值比较 (83.8) 和最近规模整数规则使正根均值有统一正上下界。
令

$$
\rho_Q(\beta)=\left\{\frac{\phi Q^3}{\beta\ln2}\right\},\qquad
C_Q(x;\beta)=(1-\rho_Q(\beta))\ln2-d_{0,Q}\eta+A_Q(x).
\tag{91.14}
$$

原 Stirling 公式与实际行桥给

$$
\ln\bar c_{Q,j}^{\mathcal E}(\beta)
=Q^3[c(\beta)-I(j/N)]-3\ln Q+C_Q(j/N;\beta)+o(1).
\tag{91.15}
$$

在 $\beta_s$ 的简单正根先得到 $j-Nu_s=O(\ln Q/Q)$，再展开得
$j-Nu_s=-3\ln Q/[QI'(u_s)]+O(Q^{-1})$。
二次项在对数均值中仅为 $O((\ln Q)^2/Q^3)$；结合 (91.9) 得首式。
由于 $x_*\ge t_{Q,s}$ 而 $j<t_{Q,s}$，最近剩余类取整给

$$
0\le x_*-t_{Q,s}\le d/2+j-t_{Q,s}<d/2.
\tag{91.16}
$$

积分 $h''\le C_K/Q^2$，得到 $\omega_Q\le C_Kd^3/Q^2$。
同一曲率界又给

$$
|G_Q(j)-k|\le C_K\left(\frac{d^2}{Q^2}
                    +\frac{(\ln Q)^2}{Q^4}\right).
\tag{91.17}
$$

乘以 $|\ell_Q'|\le C_KQ$，固定 $d$ 下的对数系数差趋零。
(83.8) 把它转为两种实际均值之比趋一，最近规模整数给所述极限范围。证毕。

此规则还有可逐层核对的精确判据。令 $J_Q$ 是 $Nu_s$ 的最近整数，
并列采用任一固定约定；充分大 $Q$ 下，$\beta_s\in\mathcal B_{n,s}$ 当且仅当

$$
\begin{gathered}
L_0(\beta_s)\in\operatorname{Nint}(-\ell_Q(J_Q)/\ln2),\qquad
pJ_Q+m_Q\equiv0\pmod d,\\
J_Q+d/2\ge t_{Q,s},\qquad
0\le\omega_Q\le
 d[h_{Q,s}(J_Q+d/2)-h_{Q,s}(t_{Q,s})].
\end{gathered}
\tag{91.18}
$$

第一项给有界正根代理均值，因而 (91.13) 对该整数成立，最终最近根整数唯一，
且 $J_Q-d/2<t_{Q,s}$。严格递增的右支上，最后两项恰好等价于
$x_*\le J_Q+d/2$；中间同余给合法剩余类与原整数 $k$。
这些正是取整规则，故两个方向均成立。判据的无穷次可满足性尚未证明。

**推论 91.5（有符号截距条件与等均值排除）。** 置
$\zeta_s=d\Psi(u_s)-pu_s$。
定理 91.4 的复现必使

$$
N\zeta_s-m_Q=-\frac dQ R_Q(u_s)+O_{K,d}(Q^{-2}).
\tag{91.19}
$$

因此最终 $m_Q=\lfloor N\zeta_s\rfloor$，且小数部分在正的 $d/Q$ 阶区间内。
若 $\zeta_s$ 为有理数，该固定切点规则的无穷次命中集为空。
更一般地，$\|N\zeta_s\|=o(Q^{-1})$ 的子序列不能成为该规则的复现子序列。

证明。(83.12) 保留驻点的一阶抵消，给
$dh_{Q,s}(t_{Q,s})=N\zeta_s+dR_Q(u_s)/Q+O_K(d/Q^4)$。
结合 $m_Q-dh_{Q,s}(t_{Q,s})=O_{K,d}(Q^{-2})$ 得 (91.19)，
负修正的统一符号给余下结论。
对有理截距，$N\zeta_s$ 若非整数，其到整数的距离有固定正下界；
若是整数，(91.19) 的严格正 $Q^{-1}$ 阶右端同样不可能。证毕。

等均值的限制还可脱离这一具体取整规则。若在同一个有理斜率切点参数处，
任意原同步子序列的两实际均值趋于 $\theta_+,\theta_->0$，
令 $u=u_s,v=\Psi(u_s)$、$m=dk-pj\in\mathbb Z$，则

$$
Q(m-N\zeta_s)=\frac d{I'(v)}
\left[A_Q(v)-A_Q(u)+\ln(\theta_+/\theta_-)\right]+o(1).
\tag{91.20}
$$

事实上，分别由 (91.15) 解出两根指标，得到

$$
\begin{aligned}
j&=Nu-\frac{3\ln Q}{QI'(u)}
       +\frac{C_Q(u;\beta_s)-\ln\theta_+}{QI'(u)}+o(Q^{-1}),\\
k&=Nv-\frac{3\ln Q}{QI'(v)}
       +\frac{C_Q(v;\beta_s)-\ln\theta_-}{QI'(v)}+o(Q^{-1}).
\end{aligned}
\tag{91.21}
$$

关系 $p/I'(u)=d/I'(v)$ 使共同规模相位与 $3\ln Q$ 项精确抵消，
给 (91.20)；原 $d_{0,Q}$ 的取整项仍保留在 $A_Q$ 内。
若两极限相等，必有

$$
N\zeta_s-m=-dR_Q(u)/Q+o(Q^{-1})>c_Kd/Q.
\tag{91.22}
$$

因此等正均值同步不能出现在 $\|N\zeta_s\|=o(Q^{-1})$ 的子序列，
特别不能发生在有理截距切点。
本章没有证明原曲线上存在同时具有有理斜率和有理截距的切点。
即使有理截距切点存在，也不能据此排除不等均值的 $E_2$ 子序列：
那时 (91.20) 仅迫使 $N\zeta_s=m$ 最终成立，并在抽取
$d_{0,Q}\to d_\infty$ 后要求

$$
\ln(\theta_+/\theta_-)=-[A_{d_\infty}(v)-A_{d_\infty}(u)]<0.
\tag{91.23}
$$

该必要关系的可实现性仍未解决。
所有均值均是原完整组在实际 pair/path 实验中的期望，原支持置换保证固定支持的一致含义；
两实验的均值桥不认定其数据律相同。
增长分母的充分条件仍为 (83.10)，本章没有证明它沿一条嵌套分支成立。
第 86 章的 $E_2$ 上维数界以及第 88、89 章的边缘通用性均保持原范围，
原 $E_2$ 的非空性与空性仍是开放问题。

## 追加锚（91 章后）

## 92. 指数分辨率下的第三阶后验覆盖

**定义 92.1（保留精确观测的扩展噪声范围）。** 沿用定义 90.1 的完整计数后验、
精确中心、方差中心、有限截距和同一个 $Y=T+\sigma_MG$。
固定原幅度和 $\beta\in(1/2,1)$，保持全部原取整与两种原实际实验，改取

$$
L_M=\ln(1/\sigma_M)\longrightarrow\infty,
\qquad \limsup_M\frac{L_M}{Q^3}<\frac{c_q}{2},
\qquad c_q=\frac{\phi(1-\beta)}{\beta}.
\tag{92.1}
$$

这是一个充分范围，不宣称 $c_q/2$ 是必要阈值。
仍以自然对数定义 $J_y,H_x(y),N_\varepsilon(x,y)$，并用
$v=\ell_*/2$、$z=\Phi^{-1}(1-\varepsilon)$，其中 $\varepsilon\in(0,1)$ 固定。
比较过程中出现的混合标量不替换实际观测，也不作为额外输出交给观察者。

**定理 92.2（指数分辨率的常数阶覆盖公式）。** 在 (92.1) 下，第 90 章的公式仍成立：

$$
\ln N_\varepsilon(x,Y)
=H_x(Y)+Q\sqrt v\,z-\ln Q
 +\frac{z^2-1}{3}+\ln\varphi(z)-\frac12\ln v+o_{\mathbb P}(1).
\tag{92.2}
$$

准确量词为：对任意 $\eta,\tau>0$，将余项绝对值超过 $\eta$ 的指标
对原纤维预测密度 $f_x(y)$ 积分，该积分超过 $\tau$ 的实际数据概率趋零；
对规定大小的固定真实支持一致，原 pair/path 实验分别成立。
更强地，在下文共同良好数据事件上有 $k_x=vQ^2+o(Q)$，使

$$
Q\int f_x(y)\sup_{t\in\mathbb R}
\left|\Pr_x\{J_y-H_x(y)\le t\mid Y=y\}-F_{k_x}(t)\right|dy
\longrightarrow0
\tag{92.3}
$$

在同一实际数据概率意义下成立；$F_k$ 是 $\operatorname{Gamma}(k,1)-k$ 的 CDF。
本结论不把输出积分收敛升级为每个输出或无界余项期望收敛。

证明。第 90 章中不依赖噪声的完整向量密度比较、过渡组计数和中心信息矩继续适用。
其移动大核心的任意逆噪声估计 (90.11) 只在原范围内使用，不能直接外推到 (92.1)。
这里改用对数大小的能量核心、经典的精确阶二项量化耦合，以及先联合比较再中心化的顺序。

**紧参数二项量化的精确阶。** Bonis 的有限 Wasserstein 中心极限定理
给出：若 $K\sim\operatorname{Bin}(n,p)$、$p\in[1/4,3/4]$，
$d=np(1-p)$，则同一单调量化耦合
$K=F_{n,p}^{-1}(U)$、$Z=\Phi^{-1}(U)$ 满足，对每个固定 $m\ge2$，

$$
\left\|\frac{K-np}{\sqrt d}-Z\right\|_m\le C_m d^{-1/2}.
\tag{92.4}
$$

适用性直接核对如下：将标准化 Bernoulli 和代入原 Theorem 1、式 (9)，
其均值为零、方差为一，所需四阶及 $(m+2)$ 阶矩在此 $p$ 区间一致有界，
原常数只依赖 $m$。一维单调量化最小化每个凸代价 $|u-v|^m$，
故同一个耦合可同时实现这些界；不同组使用独立均匀变量。
这引用的是成熟的有限定理，不是新增的一般耦合结果。
取 $m=4$，结合一致四阶矩得

$$
\|X^2-Z^2\|_2\le\|X-Z\|_4\|X+Z\|_4\le Cd^{-1/2},
\qquad X=(K-np)/\sqrt d.
\tag{92.5}
$$

**仅对能量的对数核心作正态替换。** 记 $\delta=Q^{-1/2}$、$B^2=q/Q^{5/2}$，
并沿用 $U_j=(R_j-C_jp_j)/B$、$v_j=C_jp_j(1-p_j)/B^2$、
$e_j=(\mu_j-C_jp_j)/B$、$V_D=\sum_Dv_j$、$V=V_{K_M}$。
设 $L_x=dP_x/d\mathsf Q_x$，$a_x=\|L_x-1\|_2$。
已证有限界为 $0<L_x\le C$、$a_x=O_{\mathbb P}(Q^{-5/2})$、
$\|e_D\|\le a_x\sqrt{V_D}$、$V=O_{\mathbb P}(1)$。
在良好事件上 $a_x$ 另有固定上界。

选足够大的固定 $D$，令

$$
H_M^2=D\ln Q,\qquad
\mathcal H=\{j:|j\delta|\le H_M\},\qquad
m_H=|\mathcal H|=O(Q^{1/2}\sqrt{\ln Q})=o(Q).
\tag{92.6}
$$

原 Poisson 率在均值附近有正定 Hessian，故核心内
$f_j\ge c\lambda^{-1}e^{-C(j\delta)^2}$。
原 $\ln q=c_qQ^3+O(1)$ 与实际一行／两行方差界给

$$
\min_{j\in\mathcal H}m_j\ge e^{c_qQ^3}Q^{-C_D},
\qquad
d_{\min,\mathcal H}:=\min_{j\in\mathcal H}C_jp_j(1-p_j)
\ge e^{c_qQ^3}Q^{-C_D}
\tag{92.7}
$$

在共同良好事件成立。具体地，$C_j/m_j\in[1/2,3/2]$ 在核心同时成立的失败概率
至多 $CQ^2(Q^{C_D}e^{-c_qQ^3}+e_{\rm row})\to0$；
再交校准事件 $p_j\in[1/4,3/4]$。
此处保留完整指数 $c_q$，没有将其降成一个固定分数。

在同一扩充乘积空间上只替换核心能量，外部仍使用原二项计数：

$$
T^{\rm mix}=\delta^{-1/2}
\left\{\sum_{\mathcal H}(\sqrt{v_j}Z_j-e_j)^2
       +\sum_{\mathcal H^c}(U_j-e_j)^2-V\right\}.
\tag{92.8}
$$

由 (92.5) 及 $\sum_{\mathcal H}|e_j|\sqrt{v_j}\le a_xV_{\mathcal H}$，
三角不等式给

$$
\begin{aligned}
b_x:=\|T-T^{\rm mix}\|_{2,\mathsf Q_x^{\rm ext}}
&\le C\delta^{-1/2}(1+a_x)V_{\mathcal H}d_{\min,\mathcal H}^{-1/2}\\
&\le Q^{C_D'}(1+a_x)V e^{-c_qQ^3/2}.
\end{aligned}
\tag{92.9}
$$

因此，令 $\theta_x=b_x/\sigma_M$，对每个固定 $A\ge0$ 都有
$Q^A\theta_x\to0$，一致地在实际数据概率下成立。
理由是 (92.1) 给固定 $\eta_0>0$ 使
$L_M\le(c_q/2-\eta_0)Q^3$；限制 $V\le Q$ 的代价趋零后，
余下上界为多项式乘 $e^{-\eta_0Q^3}$。
以下只支付 $b_x/\sigma_M$ 及其平方，不支付 $b_x/\sigma_M^2$。

最终核心参考保留外部精确中心的截距：

$$
\begin{aligned}
T_H^{\rm G}
&=\delta^{-1/2}\left\{
\sum_{\mathcal H}(\sqrt{v_j}Z_j-e_j)^2-V_{\mathcal H}
                 +\|e_{\mathcal H^c}\|^2\right\},\\
E_O:=T^{\rm mix}-T_H^{\rm G}
&=\delta^{-1/2}\sum_{\mathcal H^c}(U_j^2-v_j-2e_jU_j).
\end{aligned}
\tag{92.10}
$$

故 $\mathbb E_{\mathsf Q_x}|E_O|
\le C\delta^{-1/2}(1+a_x)V_O$，$O=\mathcal H^c$。
原实际行界在确定性计数线上给

$$
\sup_{S_0}\mathbb E_{S_0}V_O
\le Ce^{-c_{\rm tail}H_M^2}+Q^Ce^{-cQ^3}.
\tag{92.11}
$$

窗口与计数线只在共同截断事件上识别，坏事件仍仅以概率删除。
取 $D>200/c_{\rm tail}$ 即足以支付后续多项式误差；尾部不除以噪声。

**联合比较保留外部信息与能量的相关。** 取 (90.6) 的大组集 $\mathcal B_x$。
仍有 $N_x=\ell_*Q^2+O(1)$、核心包含于大组集，以及

$$
\mathcal S=-\ln\mathsf Q_x(R),\quad
\widetilde h=\mathbb E\mathcal S,\quad s=\mathcal S-\widetilde h,
\quad S_B=\frac12\sum_{\mathcal B_x}(Z_j^2-1),
\quad s_b=\sum_{\mathcal B_x^c}s_j,
\qquad \|s-S_B-s_b\|_2\le CQ^{-98}=:\varepsilon_s.
\tag{92.12}
$$

每个外部大组的原计数仍是同一量化均匀变量的像；它没有被独立重抽。
非大组仅有 $O(1)$ 个非空组，故 $s_b$ 的中心二阶、四阶矩有界；
$\mathbb Es^2\le CQ^2$、$\mathbb Es^4\le CQ^4$。

第 90 章已证明，对核心的
$S_H=\frac12\sum_{\mathcal H}(Z_j^2-1)$，
$(S_H,T_H^{\rm G})$ 的联合密度 $p_H$ 满足

$$
\|\partial_t p_H\|_{L^1(ds\,dt)}\le C\delta^{-1/2}.
\tag{92.13}
$$

所需统一非退化性仅使用趋向两个不同空间位置的 64 对正态坐标，
其 $v_j/\delta$ 分居两个正的分离区间，而 $e_j/\sqrt{v_j}\to0$。
对应梯度 Gram 行列式的小值概率至多 $Ct^{16}$，
足够的逆矩给二维分部积分；余下独立坐标卷积不增导数 $L^1$ 范数。
这个有限维条件与噪声无关，在当前核心仍成立。

使用同一个独立测量正态 $G$，记

$$
K=S_B+s_b+G^2/2,\qquad
Y_m=T^{\rm mix}+\sigma_MG,\qquad Y_H=T_H^{\rm G}+\sigma_MG.
\tag{92.14}
$$

条件于所有外部计数、量化变量和 $G$ 后，
从 $(K,Y_H)$ 到 $(K,Y_m)$ 仅将第二坐标平移 $E_O$。
这保留了 $E_O$ 与外部信息量之间的相关，因而 (92.13) 给

$$
e_H:=d_{\rm TV}(\mathcal L(K,Y_m),\mathcal L(K,Y_H))
\le C\delta^{-1}(1+a_x)V_O=o_{\mathbb P}(Q^{-40}).
\tag{92.15}
$$

两律各自的 $K$ 二阶矩均至多 $CQ^2$。
用差测度被两律之和支配及 Cauchy–Schwarz，
它们的未归一化一阶矩输出密度之差的 $L^1$ 范数至多 $CQ\sqrt{e_H}$。
中间输出 $Y_m$ 一般仍依赖外部信息量，不能在它处使用独立 Gamma 密度界。

**先合成联合比较，再作条件中心化。** 在共同潜变量／输出空间定义

$$
d\mu_A=L_x(R)d\mathsf Q_x^{\rm ext}\varphi_{\sigma_M}(y-T)dy,
\qquad
d\mu_m=d\mathsf Q_x^{\rm ext}\varphi_{\sigma_M}(y-T^{\rm mix})dy.
\tag{92.16}
$$

若 $D_1=\mathbb E|T-T^{\rm mix}|\le b_x$，则
$d_{\rm TV}(\mu_A,\mu_m)\le C(a_x+D_1/\sigma_M)=:e_1$。
在此共同空间上置

$$
g_A=(y-T)/\sigma_M,\quad g_m=(y-T^{\rm mix})/\sigma_M,
\quad K_A=-\ln P_x(R)-\widetilde h+g_A^2/2,
\quad \bar K=S_B+s_b+g_m^2/2.
\tag{92.17}
$$

精确 Bayes 恒等式使
$J_y-H_x(y)=K_A-\mathbb E_{\mu_A}[K_A\mid y]$。
由 $P_x=L_x\mathsf Q_x$、$L_x\le C$ 和
$\mathbb E_{P_x}(\ln L_x)^2\le Ca_x^2$，

$$
\epsilon_1:=\mathbb E_{\mu_A}|K_A-\bar K|
\le C(a_x+\varepsilon_s+\theta_x+\theta_x^2).
\tag{92.18}
$$

残差项用 $|g_A^2-g_m^2|\le
2|g_A||T-T^{\rm mix}|/\sigma_M+|T-T^{\rm mix}|^2/\sigma_M^2$。
这是直接的权重误差界，没有把不同残差的图像任意附加到 TV 比较。
将 (92.16) 经同一 $(\bar K,y)$ 映射，再接 (92.15)，得到

$$
d_{\rm TV}(\mathcal L_{\mu_A}(\bar K,Y),\mathcal L(K,Y_H))
\le e:=e_1+e_H.
\tag{92.19}
$$

设 $A_A,A_H$ 是 $K_A,K$ 各自在自己联合律下的未归一化一阶矩输出密度。
对中心信息量换律付 $C(Qa_x+a_x)$；平移核付
$CQ\sqrt{D_1/\sigma_M}$，因为核的 $L^1$ 距离至多
$\min(2,C|T-T^{\rm mix}|/\sigma_M)$，其平方期望至多 $CD_1/\sigma_M$。
对残差平方，使用
$\psi_\sigma(t)=(t/\sigma)^2\varphi_\sigma(t)$，
$\int\psi_\sigma=1$、$\|\psi_\sigma'\|_1\le C/\sigma$。
结合 (92.12)、(92.15)，得

$$
w:=\|A_A-A_H\|_1
\le C\left[Qa_x+a_x+Q\sqrt{D_1/\sigma_M}
 +\varepsilon_s+D_1/\sigma_M+Q\sqrt{e_H}\right].
\tag{92.20}
$$

两个自己律下的二阶矩 $\mathbb E_{\mu_A}K_A^2+\mathbb EK^2\le CQ^2$
由中心信息矩和正态四阶矩直接推出。整个比较没有出现 $Q^5$ 的未中心化熵因子。

现用如下有限条件比较。若律 $A$ 有 $(U,\bar U,Y)$，律 $B$ 有 $(W,Y')$，
$(\bar U,Y)$ 与 $(W,Y')$ 的 TV 至多 $e$，
$\mathbb E_A|U-\bar U|\le\epsilon$，各自二阶矩之和至多 $CQ^2$，
一阶矩输出密度之差的 $L^1$ 范数至多 $w$，且最终 $W\mid Y'=y$ 的密度至多 $C/Q$，则

$$
\int f_A(y)d_K\left(
\mathcal L_A(U-\mathbb E_A[U\mid y]\mid y),
\mathcal L_B(W-\mathbb E_B[W\mid y]\mid y)\right)dy
\le C\left[e+\epsilon/t_0+t_0/Q+w/Q+\sqrt e\right]
\tag{92.21}
$$

对每个 $t_0>0$ 成立。证明为：积分条件 TV 至多 $Ce$，
$|U-\bar U|>t_0$ 的积分概率至多 $\epsilon/t_0$，
余下阈值平移经最终密度支付 $Ct_0/Q$。
比较均值时取 $h_0=\min(f_A,f_B)$，有

$$
h_0\left|\frac{A_A}{f_A}-\frac{A_B}{f_B}\right|
\le|A_A-A_B|+(f_A-h_0)\left|\frac{A_A}{f_A}\right|
 +(f_B-h_0)\left|\frac{A_B}{f_B}\right|.
\tag{92.22}
$$

后两项各以自己律下的二阶矩及输出 TV 界支付 $CQ\sqrt e$；
再用最终密度平移中心即得 (92.21)。这是合成联合比较后才适用的中心化步骤。

在最终 $Y_H$ 处，核心以外的大组正态信息
$\frac12\sum_{\mathcal B_x\setminus\mathcal H}(Z_j^2-1)$
独立于 $Y_H$、核心、非大组计数和 $G$，是中心 Gamma，形状

$$
k_x=(N_x-m_H)/2=vQ^2+o(Q).
\tag{92.23}
$$

其密度至多 $C/Q$，与余下条件变量卷积仍保此界。
故将 (92.18)–(92.20) 代入 (92.21)，取 $t_0=Q^{-1/2}$，
每一项都是 $o_{\mathbb P}(1/Q)$。
例如最慢的 $\sqrt e=O_{\mathbb P}(Q^{-5/4})$
以及 $t_0/Q=Q^{-3/2}$ 均满足这一要求。

最终剩余的中心化条件变量为
$S_H+s_b+G^2/2-\mathbb E[S_H+s_b+G^2/2\mid Y_H]$，
其条件方差积分至多 $C(m_H+1)$。
Gamma 密度导数上界为 $C/Q^2$；条件中心化消去一次 Taylor 项，
故它对 CDF 的积分影响至多 $C(m_H+1)/Q^2=o(1/Q)$。
这证明 (92.3)。第 90 章的 Gamma 分位数展开、有界变差计数核和并列组界
只需要这个精度及 $\sqrt{k_x}=Q\sqrt v+o(1)$，因此直接给出 (92.2)。
特别地，计数核总变差为二，将 CDF 误差转成 $o(1/Q)$ 的计数边界误差；
最大并列质量也至多该连续比较误差的两倍，没有遗漏整数覆盖修正。证毕。

**注记 92.3（范围与归属）。** 本章扩展的是精确熵中心下的覆盖与条件 Gamma 比较。
旧信息增益、熵响应、密度上确界或方差损失结论并未因此自动扩展到 (92.1)：
例如付 $D_1/\sigma_M^2$ 的核密度估计尚未由本章支付。
同样没有宣称零噪声、阈值锐性、所有输出、误差水平趋端点或有效解码。
固定支持的实际联合输出评价仍只通过第 90 章的精确置换不变性转移；
给定数据和已知固定支持的单一正态输出律不等于 $f_x$。
未知方向沿用同一事件上的整个纤维与观测一致性，不新造方向后验。

经典量化、密度分部积分及第三阶源编码各归其原文。
新增推导在于只正态替换对数能量核心、保留外部真实计数关系，
并在最终参考处统一处理信息量、输出与精确条件中心。
当前是普通数学推导，未声称 Lean 核验。

## 追加锚（本行以下为增补区）

## 93. 原分母的素因子限制、超越根与傅里叶障碍

**定义 93.1（原根坐标中的有限均值复现）。** 沿用第 81、85、88 章的
原固定幅度、原取整、两种实际实验和双根区间
$D=(\beta_*,1)$。写 $N_n=Q_n^2$，正、负内部率根为
$x_+(\beta),x_-(\beta)$，满足 $I(x_\sigma)=c(\beta)$。
令 $\mathcal R_\sigma$ 为那些根值 $x_\sigma(\beta)$ 的集合：
在某条原合法子序列上，该根附近的一个完整得分组的实际均值
$\mu^{\mathcal E}_{Q,j}(\beta)$ 收敛到正的有限值。
原相对均值比较使 pair/path 的这两个参数集合相同；不宣称有限数据律相同。
以下 $\|t\|$ 表示到最近整数的距离。

复现要求一个固定 $\beta$、原 $Q_n$ 和原 $M,q$ 历史。
两根各自属于 $\mathcal R_\sigma$ 仍允许不同子序列，不等于同步集合 $E_2$。

**定理 93.2（代数无理根的空过渡带）。** 固定 $\beta\in D$，
设其一个内部非零率根 $x$ 是代数无理数。则对每个固定 $B>0$，
在 $x$ 的一个固定充分小邻域内，原多项式均值带

$$
\{j:Q^{-B}\le\mu^{\mathcal E}_{Q,j}(\beta)\le Q^B\}
\tag{93.1}
$$

在所有充分晚的合法层为空，两种实际实验均成立。
更强地，对每个 $0<\epsilon<1$，正根的相邻格点满足

$$
\ln\mu^{\mathcal E}_{Q,\lfloor Nx\rfloor}\ge cQ^{1-\epsilon},
\qquad
\ln\mu^{\mathcal E}_{Q,\lceil Nx\rceil}\le-cQ^{1-\epsilon},
\tag{93.2}
$$

其中 $c>0$ 及起始层依赖固定 $x,\beta,\epsilon$。
负根处两个不等式的方向相反。
结合第 81 章的有理根排除，$\mathcal R_+$ 与 $\mathcal R_-$ 中的每个数都超越，
因而 $E_2$ 的每个参数必须有两个超越率根。

证明。先直接应用成熟的 $p$-进子空间定理。
所用明确版本为 Adamczewski–Bugeaud 原文 Section 4 的 Theorem E：
数域 $K$、包含所有无穷赋值的有限集合 $S$、每处 $m$ 个线性无关且允许系数
在 $K$ 之外的代数线性形式满足

$$
\prod_{w\in S}\prod_{i=1}^m
\frac{|L_{i,w}(z)|_w}{|z|_w}\le H(z)^{-m-\epsilon_0}
\tag{93.3}
$$

的 $z\in K^m$ 落在有限个真 $K$-线性子空间，$0<\epsilon_0<1$。
无穷处使用原文欧氏范数，有限处用最大坐标范数。

对固定代数无理数 $\xi$、既约 $p/q$、$q>0$ 且素因子只有 $2,5$，
取 $K=\mathbb Q$、$m=2$、$S=\{\infty,2,5\}$、$z=(p,q)$，以及

$$
(L_{1,\infty},L_{2,\infty})=(Y,\xi Y-X),\qquad
(L_{1,\ell},L_{2,\ell})=(X,Y)\quad(\ell=2,5).
\tag{93.4}
$$

每对形式线性无关；本原性给所有有限处 $|z|_\ell=1$，
$H(z)=\sqrt{p^2+q^2}$，并有

$$
q|\xi q-p|\prod_{\ell=2,5}|pq|_\ell\le|\xi q-p|.
\tag{93.5}
$$

若 $|\xi-p/q|<q^{-1-\gamma}$，$0<\gamma<1$，则
$|\xi q-p|<q^{-\gamma}$，而 $H(z)\asymp_\xi q$。
取 $\epsilon_0=\gamma/2$ 后，所有充分大解满足 (93.3)。
每条真有理直线至多含一个 $q>0$ 的本原整数对，故解只有有限个。
吸收这些非零误差与远离 $\xi$ 的分数，得

$$
|\xi-p/q|\ge c_{\xi,\gamma}q^{-1-\gamma}.
\tag{93.6}
$$

这就是此处需要的经典受限素因子逼近结论，不作为新的一般数论定理。
将 $j/N$ 约分为 $p/q$ 后，$q\mid N=10^{2e_n}$，仍只有素因子 $2,5$，且 $q\le N$。
所以对任意 $0<\epsilon<1$，取 $\gamma=\epsilon/2$，有

$$
\|Q_n^2\xi\|\ge c_{\xi,\epsilon}Q_n^{-\epsilon}.
\tag{93.7}
$$

未要求 $j,N$ 互素，也未把其他分母舍入到原合法分母。

另一方面，第 81 章保留原楼层相位的实际均值展开为

$$
\ln\mu^{\mathcal E}_{Q,j}(\beta)
=Q^3\{c(\beta)-I(j/N)\}-3\ln Q+C_Q(j/N;\beta)+o(1),
\tag{93.8}
$$

在固定内部根邻域内 $C_Q$ 及所需导数一致有界，两个原取整没有被删去。
简单根附近的 (93.1) 因此要求
$|j-Nx|\le C_{x,\beta,B}\ln Q/Q$，与 (93.7) 矛盾。
对相邻格点 $|j-Nx|\le1$，Taylor 展开进一步给

$$
\ln\mu^{\mathcal E}_{Q,j}
=-QI'(x)(j-Nx)-3\ln Q+C_Q(x;\beta)+O(Q^{-1})+o(1).
\tag{93.9}
$$

此处实际均值与原 Poisson 参考之间仍是相对比较：
相邻均值为 $e^{O(Q)}$，其最小尺度 $e^{-CQ}$ 大于尾部 $e^{-cQ^3}$ 的加性误差。
(93.7) 使主项至少为 $cQ^{1-\epsilon}$，支配其余项，即得 (93.2)。

有理根另按第 81 章处理：$Nx$ 的分母整除固定整数，
正有限复现所需的 $O(\ln Q/Q)$ 距离最终必须为零，
但此时 (93.8) 仍给 $-3\ln Q+O(1)\to-\infty$。
这只排除有理根的正有限复现；它不排除 $Q^{-3}$ 量级的多项式带。
两类合起来才给所有复现根超越。证毕。

**命题 93.3（两个固定原参数及其熵贡献）。** 令

$$
x_0=\frac{\sqrt2}{10000},\qquad
\beta_{\rm alg,+}=\frac{\phi}{\phi+I(x_0)},\qquad
\beta_{\rm alg,-}=\frac{\phi}{\phi+I(-x_0)}.
\tag{93.10}
$$

则 $\beta_*<\beta_{\rm alg,-}<\beta_{\rm alg,+}<1$，二者均不在 $E_2$。
各参数处指定的代数无理根都满足定理 93.2；没有断言其另一根的算术类型。

证明。原 $1/10<\vartheta<11/100$，
$r\mapsto\ln(1+r)/[-\ln(1-r)]$ 在 $(0,1)$ 严格下降。
在 $r_0=1-2^{-11}$ 处该比值小于 $1/11<\vartheta$，故
$r<r_0$、$b>1/4096$。
由 $121\cdot4096<10^6$ 得 $\vartheta^2/100<b$，于是

$$
0<x_0<1/5000<1/1000<\vartheta/100<b/\vartheta.
\tag{93.11}
$$

第 81 章的 $I'''<0$ 给 $I(-t)>I(t)$ 于 $0<t\le b/\vartheta$，
且 $I$ 在负侧严格下降到零。因此 $I(\pm x_0)$ 严格位于
$(0,I(-b/\vartheta))$，给出两参数次序及其合法性。
指定根代数无理，应用定理 93.2 即可。证毕。

第 72 章精确确定性熵中心的残差仅来自至多两个
$Q^{-8}\le\mu_{Q,j}^{\mathcal E}\le Q^8$ 的过渡组。
上述每个参数处，指定根的该求和指标集在充分晚的层确定为空，
所以残差只剩另一根的贡献与原 $o_{\mathbb P}(1)$ 项。
这不证明整个熵残差趋零，也不推出熵期望收敛。
第 85 章对 $\mathbb Q(\vartheta)$ 根的排除仍独立保留；
$\mathbb Q(\vartheta)$ 的代数元素恰为 $\mathbb Q$，故两条障碍并不重复。

**命题 93.4（固定代数无理切线截距的排除）。** 若实际参数处
$\psi'(u)=p/d$ 是既约有理数，$v=\psi(u)$，且固定
$\zeta=dv-pu$ 是代数无理数，则该参数不在 $E_2$。

证明。假设沿原共同子序列两实际均值趋于 $\theta_+,\theta_->0$。
第 81、91 章的有符号截距消去公式给原整数 $m=dk-pj$ 满足

$$
Q(m-N\zeta)=\frac d{I'(v)}
\left[A_Q(v)-A_Q(u)+\ln\frac{\theta_+}{\theta_-}\right]+o(1).
\tag{93.12}
$$

右侧有界，故 $\|N\zeta\|=O(Q^{-1})$，与 (93.7) 矛盾。证毕。
这是条件参数类的排除，没有断言实际曲线上存在这种代数截距。
它不涵盖有理截距，也不能对随 $d,Q$ 变化且无统一高度的截距使用同一个常数。

**定理 93.5（根复现集合的傅里叶障碍）。** 若实线上概率测度 $\nu$
集中于 $\mathcal R_\sigma$，则

$$
\sum_n\sup_{k\in\mathbb Z\setminus\{0\}}
|\widehat\nu(kN_n)|=\infty.
\tag{93.13}
$$

因此不存在任何 $A>0$ 使
$|\widehat\nu(t)|=O((\ln(2+|t|))^{-A})$。
两根复现集及 $E_2$ 的两个根投影的傅里叶维数均为零。
第 88、89 章非空边缘通用集 $\mathcal V$ 在任意非空开区间
$J\Subset D$ 上的两个根像则都有 Hausdorff 维数 $2/3$、傅里叶维数零。

证明。(93.8) 的简单根必要条件给

$$
\mathcal R_\sigma\subset
\bigcup_{C=1}^{\infty}
\left\{x:\|N_nx\|\le C\frac{\ln Q_n}{Q_n}
\text{ 于无穷多个 }n\right\}.
\tag{93.14}
$$

这只是必要的包含关系，没有将 $-3\ln Q$ 位移或取整相位忽略为充分条件。
直接用 Pollington–Velani–Zafeiropoulos–Zorin 原文的收敛定理：
对 $[0,1]$ 上概率测度、正整数序列 $q_n$ 和正函数 $\psi$，
若 $\sum_n\sup_{k\ne0}|\widehat\nu(kq_n)|<\infty$ 且
$\sum_n\psi(q_n)<\infty$，则
$\|q_nx\|\le\psi(q_n)$ 的上极限集测度为零。
原 Lemma 2 的有限界为
$\nu\{\|qx\|\le\psi(q)\}\le3\psi(q)+3\sup_{k\ne0}|\widehat\nu(kq)|$，
$q\ge4$；接第一 Borel–Cantelli 引理即是该结论。

对实线测度先模一推前，其整数频率傅里叶系数和 (93.14) 的事件均不变。
取 $q_n=N_n\ge100$，$\psi(N_n)=\min(1/4,C\ln Q_n/Q_n)$。
原增长 $Q_{n+1}=10^{Q_n^5}$ 使

$$
\sum_n\frac{\ln Q_n}{Q_n}<\infty,\qquad
\sum_n(\ln N_n)^{-A}<\infty\quad\text{对每个 }A>0.
\tag{93.15}
$$

若 (93.13) 不成立，成熟收敛定理使 (93.14) 中每个上极限集为零测，
从而 $\nu(\mathcal R_\sigma)=0$，矛盾。
任何正的对数衰减率都会使 (93.13) 的级数收敛，故也被排除。
正傅里叶维数要求某个非零有限测度具有正幂次衰减，归一化后亦不可能。
最后，$\mathcal V$ 的两个根像属于相应 $\mathcal R_\sigma$；
原根映射在紧内部区间是双 Lipschitz，保留已证 Hausdorff 维数 $2/3$。
傅里叶结论则从 (93.14) 单独推出。证毕。

**注记 93.6（障碍与坐标范围）。** 傅里叶维数不由非线性换坐标自动保留，
故不把定理 93.5 改写成 $\beta$ 坐标的傅里叶维数零。
这里的测度用于分类确定性参数集，不是新增参数、幅度或支持先验。
这一障碍排除了“先在根复现集上取得正对数傅里叶衰减，再用所引测度下界”的路线，
没有排除不具这种衰减的异常嵌套构造。

代数逼近界的常数和起始层依赖固定代数数；没有给有效起始层或增长高度的一致性。
可变分母的精确单侧相位、共同剩余类和有界均值的嵌套分支仍未构造，
$E_2$ 非空或为空仍为 OPEN。
成熟数论与傅里叶收敛定理直接归属原文；新增内容是它们与原素因子受限分母、
实际均值尺度和原熵残差的对应。本文未声称形式核验或全球原创性。

## 追加锚（93 章后）

## 94. 指数分辨率下紧输出区间的一致覆盖

**定义 94.1（紧输出区间与精确条件中心）。** 沿用定义 92.1 的原实验、
完整组计数后验 $P_x$、精确标量 $T$ 及同一个 $Y=T+\sigma_MG$，仍要求

$$
L_M=\ln(1/\sigma_M)\longrightarrow\infty,
\qquad \limsup_M L_M/Q^3<c_q/2.
\tag{94.1}
$$

所有信息量均用自然对数。保持 $J_y=-\ln P_x(R\mid y)$、
$H_x(y)=\mathbb E_x[J_y\mid y]$、最小覆盖大小 $N_\varepsilon(x,y)$，
以及 $v=\ell_*/2>0$、$z=\Phi^{-1}(1-\varepsilon)$。
这里 $\varepsilon\in(0,1)$ 与输出半径 $K<\infty$ 固定，$K\ge0$。
对固定真实支持取数据概率时，这些仍是同一均匀支持先验定义的纤维函数。

**定理 94.2（紧区间上一致的三阶覆盖与局部信息谱）。** 在 (94.1) 下，

$$
\sup_{|y|\le K}\left|
\ln N_\varepsilon(x,y)-H_x(y)-Q\sqrt v\,z+\ln Q
-\frac{z^2-1}{3}-\ln\varphi(z)+\frac12\ln v
\right|\longrightarrow0
\tag{94.2}
$$

一致地在原固定支持的实际数据概率下成立，pair/path 两种实验分别成立。
更强地，可以取与输出无关的 $k_x=vQ^2+o(Q)$，使

$$
Q\sup_{|y|\le K}\sup_{t\in\mathbb R}
\left|\Pr_x\{J_y-H_x(y)\le t\mid y\}-F_{k_x}(t)\right|
\longrightarrow0,
\tag{94.3}
$$

其中 $F_k$ 是 $\operatorname{Gamma}(k,1)-k$ 的 CDF。
原输出混合密度还满足

$$
\|f_x-\varphi_\nu\|_\infty\longrightarrow0,
\qquad
\inf_{|y|\le K}f_x(y)\ge\frac12\min_{|y|\le K}\varphi_\nu(y)>0
\tag{94.4}
$$

于概率趋一的事件上成立；$\nu=2\int\rho^2$ 取原空间轮廓的值，
$\varphi_\nu$ 表示方差为 $\nu$ 的中心正态密度。
式 (94.2) 的精确量词是：对每个固定 $K,\varepsilon,\eta>0$，
其左侧超过 $\eta$ 的数据概率对全部规定大小的真实支持取上确界后趋零。
这不要求给定固定支持后的实际输出密度等于先验混合密度 $f_x$。

证明。采用第 92 章的同一量化空间和精确中心。
本证明需要逐输出的带权密度控制，以下直接建立这种控制。

**共同良好环境与分块平滑。** 保持 $U_j,v_j,e_j,V_D,L_x,a_x$ 的原定义。
将 (92.6) 的固定常数 $D$ 增大，令 $H_M^2=D\ln Q$，
$\mathcal H=\{j:|j\delta|\le H_M\}$、$O=\mathcal H^c$、
$m_H=|\mathcal H|=O(\sqrt{Q\ln Q})=o(Q)$。
实际行估计、校准和 (92.11) 允许在失败概率一致趋零的环境上同时取

$$
\begin{gathered}
V\le C,\quad a_x\le CQ^{-5/2},\quad
\|e_A\|\le a_x\sqrt{V_A},\quad d_A,d_C\asymp q,\quad V_O\le Q^{-200},\\
\min_{j\in\mathcal H}d_j\ge e^{c_qQ^3}Q^{-C_D},\qquad
\frac{v_j}{\delta\rho(j\delta)}\longrightarrow1
\quad\text{在每个固定空间紧区间上一致},\qquad
\delta^{-1}\sum_jv_j^2\longrightarrow\nu/2.
\end{gathered}
\tag{94.5}
$$

此处下标 $A$ 在 $e_A,V_A$ 中可指任意组集；$d_A$ 仍指全部 Bernoulli 总和方差。
例如取 $D>1000/c_{\rm tail}$ 后，以 (92.11) 及 Markov 不等式取得尾界。
$V\to\int\rho$，故 $V\le C$ 可用固定足够大的 $C$。
显式界 $a_x\le C(d_J/q+q^{-1/2})$ 与 $d_J=B^2V$ 再给确定的
$CQ^{-5/2}$ 上界，未将任意紧随机乘子当作固定常数。
以下先对满足这些条件的确定环境证明估计，再恢复实际数据概率。

将核心按整数指标的模三剩余类分成三个部分 $\mathcal H_l$。
每一部分在固定正长度空间区间内都有至少 $c/\delta$ 个坐标。
对其正态能量块，置 $w_j=v_j/\sqrt\delta$、$c_j=e_j/\sqrt{v_j}$。
一维非中心平方的特征函数模不大于中心平方的模，故每个块满足

$$
\left|\mathbb E\exp\left(it\sum_{j\in\mathcal H_l}
w_j(Z_j-c_j)^2\right)\right|
\le(1+c\delta t^2)^{-c'/\delta}.
\tag{94.6}
$$

截距不影响此式。右侧及其乘每个固定 $|t|^r$ 的积分一致有界，且积分尾部
一致趋零：在 $|t|\le\delta^{-1/2}$ 用 $e^{-c''t^2}$，在其外换元
$s=\sqrt\delta t$，得到随 $1/\delta$ 指数衰减的界。
因此每个块的能量密度上确界至多固定 $C$。
删除固定数目的坐标或添加独立变量仍保留此界。

保持 (92.8) 的 $T^{\rm mix}$，记

$$
W=\sum_jU_j,\quad s=-\ln\mathsf Q_x(R)-\widetilde h,
\quad B_s=S_B+s_b,\quad r_s=s-B_s.
\tag{94.7}
$$

对每个固定 $p\ge2$，Bernoulli 中心矩展开及二项中心信息矩给
$\|W\|_p\le C_p$、$\|s\|_p+\|B_s\|_p\le C_pQ$。
具体地，$BW$ 是方差 $B^2V$ 的独立 Bernoulli 中心和，
其 $2m$ 阶矩至多 $C_m((B^2V)^m+B^2V)$；
每组中心信息量的固定阶矩一致有界，独立和中消去单次指标后给 $C_mQ^{2m}$。
这些独立性只在校准乘积空间中使用。

若权重 $F_l$ 仅依赖三个核心部分及其外部这四部分之一，
条件于它和所有其它变量，保留另一个独立核心块平滑输出，便有

$$
\sup_y\mathbb E\bigl[|F_l|^p\varphi_{s_0}(y-T^{\rm mix})\bigr]
\le C\mathbb E|F_l|^p,\qquad s_0>0.
\tag{94.8}
$$

以四部分分解和 $|\sum_lF_l|^p\le4^{p-1}\sum_l|F_l|^p$ 得

$$
\begin{aligned}
\sup_y\mathbb E[(1+|W|^p)\varphi_{s_0}(y-T^{\rm mix})]&\le C_p,\\
\sup_y\mathbb E[(|s|^p+|B_s|^p)\varphi_{s_0}(y-T^{\rm mix})]&\le C_pQ^p.
\end{aligned}
\tag{94.9}
$$

固定阶残差多项式可用 $|u|^b\varphi(u)\le C_b\varphi_2(u)$ 插入；
权重乘积由带权测度下的 Hölder 不等式控制。
对各组量化／Stirling 误差分别应用 (94.8)，再用带权 Minkowski 不等式及
(92.12) 的逐组误差和，得到

$$
\sup_y\mathbb E[|r_s|\varphi_{s_0}(y-T^{\rm mix})]\le CQ^{-98},
\qquad
\sup_y\mathbb E[r_s^2\varphi_{s_0}(y-T^{\rm mix})]\le CQ^{-196}.
\tag{94.10}
$$

每个误差即使属于核心，也可由另一个核心块平滑。
式 (94.8)–(94.10) 对删除外部能量后的 $T_H^{\rm G}$ 同样成立；
特别地，核心中心信息量 $S_H=\frac12\sum_{\mathcal H}(Z_j^2-1)$ 满足
$\sup_y\mathbb E[S_H^2\varphi_{s_0}(y-T_H^{\rm G})]\le Cm_H$。

**局部核替换支付完整半指数范围。** Bonis 的有限定理给 (92.4) 的每个固定阶。
取 $2m$ 阶后用 Hölder 及三角不等式，即将 (92.9) 加强为

$$
\|\Delta T\|_m\le C_mQ^{C_D}e^{-c_qQ^3/2},
\qquad
\|\Delta T/\sigma_M\|_m\le C_mQ^{C_D}e^{-\eta_0Q^3},
\quad \Delta T=T-T^{\rm mix},
\tag{94.11}
$$

其中固定 $\eta_0>0$ 来自 (94.1)，而 $m$ 可以依赖这个间隙，但不随 $M$ 增长。
取 $h_Q=Q^{-100}$，将空间分为
$E_{\rm bad}=\{|\Delta T|>h_Q\sigma_M\}$ 及其补集。
对任意所需固定 $A$，足够大的固定 $m$ 使

$$
\sigma_M^{-1}Q^C\Pr(E_{\rm bad})^{1/2}=o(Q^{-A}).
\tag{94.12}
$$

事实上概率至多 $C_mQ^{m(C_D+100)}e^{-m\eta_0Q^3}$，
而 $\sigma_M^{-1}\le e^{(c_q/2-\eta_0)Q^3}$。
所需额外固定次幂 $|\Delta T/\sigma_M|$ 亦由更高固定矩及 Hölder 支付。
普通二阶范数至多多项式的中心权重可同时插入。

对 $|d|\le h\sigma$、$h\le1/2$，正态核的微分给

$$
|\varphi_\sigma(t-d)-\varphi_\sigma(t)|
\le Ch\varphi_{2\sigma}(t),\qquad
\varphi_\sigma(t-d)\le C\varphi_{2\sigma}(t).
\tag{94.13}
$$

对固定整数 $b\ge0$，将核换成 $(t/\sigma)^b\varphi_\sigma(t)$
也有同式的差界，必要时再固定倍数放宽正态方差。
另有
$|(t-d)^2-t^2|\varphi_\sigma(t-d)/\sigma^2\le Ch\varphi_{2\sigma}(t)$。
这些式子由中值定理及多项式乘宽正态包络的一致界直接成立。
坏事件上使用核及残差多项式核的上确界 $C_b/\sigma$，由 (94.12) 支付。
与 (94.9) 结合，逐输出地得到

$$
\begin{aligned}
\sup_y\mathbb E|\varphi_\sigma(y-T)-\varphi_\sigma(y-T^{\rm mix})|
&\le Ch_Q+o(Q^{-90}),\\
\sup_y\mathbb E|s|\,|\varphi_\sigma(y-T)-\varphi_\sigma(y-T^{\rm mix})|
&\le CQh_Q+o(Q^{-90}).
\end{aligned}
\tag{94.14}
$$

$W^2,B_s$、所需乘积及至多四阶残差多项式亦满足对应估计。
小位移以噪声为单位测量，宽核由正态核心的有界能量密度积分；
坏事件的 $\sigma^{-1}$ 由高固定矩吸收。
由此没有使用在当前范围未获保证的 $\mathbb E|\Delta T|/\sigma^2$ 界。

**实际后验的逐输出带权比较。** 原完整向量选中密度的方差型局部估计为

$$
L_x(k)=\sqrt{d_A/d_C}\,e^{-(k-m_J)^2/(2d_C)}+O(q^{-1/2})
\tag{94.15}
$$

对全部整数总计数 $k$ 一致成立。它的分母是整数校准均值处的中心概率，
故绝对局部误差在相除后为所示 $O(q^{-1/2})$。
用 $1-e^{-u}\le u$、$k-m_J=BW$、$B^2/q=Q^{-5/2}$，得到全局界

$$
|L_x-1|\le C[Q^{-5/2}(V+W^2)+q^{-1/2}],\qquad 0<L_x\le C.
\tag{94.16}
$$

于是 (94.9)、(94.14) 给

$$
\begin{aligned}
\sup_y\mathbb E[|L_x-1|\varphi_\sigma(y-T)]&\le CQ^{-5/2},\\
\sup_y\mathbb E[|L_x-1||s|\varphi_\sigma(y-T)]&\le CQ^{-3/2},\\
\sup_y\mathbb E[L_x(|\ln L_x|+|\ln L_x|^2)\varphi_\sigma(y-T)]&\le CQ^{-5/2}.
\end{aligned}
\tag{94.17}
$$

末式使用 $t|\ln t|+t(\ln t)^2\le C'|t-1|$ 于 $0\le t\le C$。
所需残差多项式亦可插入。这里未将无界信息量通过 TV 传递。

使用 (92.16)–(92.17) 的共同潜变量／输出律 $\mu_A,\mu_m$，
以及各自正确的残差 $g_A,g_m$ 和可观测量 $K_A,\bar K$。
在固定输出 $y$ 的未归一化测度上，(94.10)、(94.14)、(94.17) 依次给

$$
\begin{gathered}
\sup_y\|\mu_A(\bar K\in\cdot,dy)/dy-\mu_m(\bar K\in\cdot,dy)/dy\|_{\rm TV}
\le e_1=O(Q^{-5/2}),\\
\sup_y\int|K_A-\bar K|\,d\mu_A(\cdot,y)/dy
\le\epsilon_1=O(Q^{-5/2}),\\
\sup_y|A_A(y)-A_m(y)|\le w_1=O(Q^{-3/2}).
\end{gathered}
\tag{94.18}
$$

$A_A,A_m$ 为这两个可观测量各自的一阶矩输出密度；此处 TV 取绝对质量范数。
第一式经同一个 $\bar K$ 映射；第二式分别支付 $-\ln L_x$、$r_s$ 和残差平方差。
第三式对中心信息量换律付 $CQ^{-5/2}Q$、平移付 $CQh_Q$，
对残差平方使用残差多项式核，信息近似再付 $CQ^{-98}$。
因而不存在一个未中心化的 $Q^5$ 因子。

**联合密度的切片导数移除相关外部能量。** 需要加强 (92.13) 的范数。
设 $(S_H,T_H^{\rm G})$ 的联合密度为 $p_H(s,t)$，则

$$
\sup_t\int|\partial_t p_H(s,t)|ds\le C\delta^{-1/2},
\qquad
\sup_t\int |s|\,|\partial_t p_H(s,t)|ds
\le C\delta^{-1/2}(1+\sqrt{m_H}).
\tag{94.19}
$$

以下给出所需二维非退化性及切片论证。保留 64 对不交核心坐标，
每对一端空间位置趋零、另一端趋一。
$b_j=v_j/\delta$ 的两个范围正且分离，$|c_j|=|e_j|/\sqrt{v_j}=O(Q^{-9/4})$。
该固定块上令
$F_1=\frac12\sum(Z_j^2-1)$、$F_2=\sum b_j((Z_j-c_j)^2-1)$。
梯度 Gram 矩阵 $\Gamma$ 的 Cauchy–Binet 公式给

$$
\det\Gamma\ge4\sum_{64\text{ 对 }(i,j)}P_{ij}^2,
\qquad
P_{ij}=(b_j-b_i)Z_iZ_j+b_ic_iZ_j-b_jc_jZ_i.
\tag{94.20}
$$

条件于 $Z_j$，$Z_i$ 的系数是方差有正下界的仿射正态。
其绝对值不超过 $a$ 的概率至多 $Ca$；在补集上
$\Pr(|P_{ij}|\le u\mid Z_j)\le Cu/a$。取 $a=\sqrt u$，
由 64 对独立性得到
$\Pr(\det\Gamma\le t)\le Ct^{16}$，$0<t<1$。
因此低于 16 阶的逆矩一致有界。

令 $u=\sum_b(\Gamma^{-1})_{2b}\nabla F_b$，则
$u\cdot\nabla F_1=0$、$u\cdot\nabla F_2=1$。
正态散度 $D_u=Z\cdot u-\operatorname{div}u$ 的分母至多为
$(\det\Gamma)^2$，分子为固定维多项式。
Hölder 与上述逆矩给 $\mathbb E[(1+|F_1|)|D_u|]\le C$。
先在行列式远离零处局部化、再以更高逆矩移除截断，正态分部积分给
$(F_1,\sqrt\delta F_2)$ 的密度 $p_A$ 满足

$$
\iint(1+|s|)|\partial_t p_A(s,t)|dsdt\le C\delta^{-1/2}.
\tag{94.21}
$$

几乎处处秩为二通过局部变量变换保证绝对连续性；分部积分给密度导数的散度表示。
这是经典密度演算在所列逆矩已核对后的应用。
余下核心的能量边缘密度上界为 $C$，且
$\sup_t\int|s|p_B(s,t)ds\le C\sqrt{m_H}$：
再分两个独立宏观块，以一个块的能量平滑另一个块的中心信息量即可。
在 $p_H=p_A*p_B$ 中用 Fubini 及 $|s_A+s_B|\le|s_A|+|s_B|$，即得 (94.19)。
余下独立块的可积 Fourier 导数给连续版本；再保留一个这样的卷积块，
上述切片界可在每个实数 $t$ 处成立。

保持 (92.10) 的真实外部能量差 $E_O=T^{\rm mix}-T_H^{\rm G}$。
二项四阶矩及中心和独立性给

$$
\|E_O\|_2\le C\delta^{-1/2}[(1+a_x)V_O+B^{-1}\sqrt{V_O}],
\qquad \mathbb E|E_O|\le C\delta^{-1/2}(1+a_x)V_O.
\tag{94.22}
$$

例如平方和的方差至多 $2\sum_Ov_j^2+V_O/B^2$，
线性部分的二阶范数至多 $2\sqrt{\max_Ov_j}\|e_O\|\le2a_xV_O$。
条件于全部外部计数、量化变量和同一个 $G$，
令 $K_0=S_B+s_b+G^2/2$、$Y_m=T^{\rm mix}+\sigma G$、$Y_H=T_H^{\rm G}+\sigma G$。
两对 $(K_0,Y_m),(K_0,Y_H)$ 仅将 $p_H$ 的第二坐标平移 $E_O$，
第一坐标同时保留外部信息量和 $G^2/2$。
因此其逐输出未归一化测度的 TV 及一阶矩密度差分别至多

$$
\begin{aligned}
e_2&\le C\delta^{-1}(1+a_x)V_O,\\
w_2&\le C\delta^{-1/2}[(1+\sqrt{m_H})\mathbb E|E_O|+Q\|E_O\|_2]\\
&\le CQ\delta^{-1}[(1+a_x)V_O+B^{-1}\sqrt{V_O}].
\end{aligned}
\tag{94.23}
$$

第二式对外部信息量用其 $CQ$ 二阶范数，对 $G^2$ 用独立的固定均值。
由 (94.5)，两误差均为 $o(Q^{-90})$。
这一联合平移保留了外部信息量与外部实际能量的相关，且不收取逆噪声因子。

**正密度、精确中心与条件 CDF。** $T_H^{\rm G}$ 的均值是
$\delta^{-1/2}\|e\|^2=o(1)$。
其中心二次部分的方差 $2\sum_{\mathcal H}w_j^2\to\nu$，最大系数趋零：
固定空间紧区间由轮廓控制，区间之外由平方质量尾界控制。
线性部分二阶范数趋零，故独立正态平方的累积量界给 $T_H^{\rm G}\Rightarrow N(0,\nu)$。
式 (94.6) 的统一可积 Fourier 包络将其加强为输出密度
$\|f_H-\varphi_\nu\|_\infty\to0$，加同一个消失正态噪声仍成立。
这也落在 Herry–Malicet–Poly 的有限 Wiener chaos 密度超收敛定理范围内：
最高二阶投影归一化后趋标准正态，低阶余项在 $L^2$ 中趋零。
这里的显式 Fourier 证明同时提供了前述独立块估计。

合成 (94.18)、(94.23)，令 $e=e_1+e_2=O(Q^{-5/2})$、
$w=w_1+w_2=O(Q^{-3/2})$。质量比较给
$\sup_y|f_x(y)-f_H(y)|\le e$，从而证明 (94.4)。
在固定紧区间两个密度均至少为确定的 $c_K>0$。
设 $A_H$ 是最终 $K_0$ 的一阶矩密度；带权比较给
$\sup_y|A_A-A_H|\le w$。
最终参考的条件二阶矩至多 $C_KQ^2$，故归一化均值满足

$$
\sup_{|y|\le K}|m_A(y)-m_H(y)|\le C_K(w+Qe)=O(Q^{-3/2}).
\tag{94.24}
$$

此式直接由
$m_A-m_H=(A_A-A_H)/f_x+m_H(f_H-f_x)/f_x$ 推出。
这里 $m_H(y)$ 表示均值函数，核心坐标数仍记 $m_H$；两者以是否带自变量区分。
Bayes 恒等式精确给
$J_y-H_x(y)=K_A-m_A(y)$，其中噪声对数和输出密度在中心化时完全相消。

现在，且仅在最终参考处，
$A_k=\frac12\sum_{\mathcal B_x\setminus\mathcal H}(Z_j^2-1)$
独立于 $(Y_H,S_H,s_b,G)$；其形状
$k=(N_x-m_H)/2=vQ^2+o(Q)$。
因此 $K_0\mid Y_H=y$ 的密度至多 $C/Q$。
由 (94.18) 的可观测量位移界、合成测度 TV、此密度界及 (94.24)，对每个 $t_0>0$，

$$
\sup_{|y|\le K}d_K\bigl(
\mathcal L(K_A-m_A(y)\mid y),\mathcal L(K_0-m_H(y)\mid Y_H=y)\bigr)
\le C_K[e+\epsilon_1/t_0+t_0/Q+w/Q].
\tag{94.25}
$$

具体地，大于 $t_0$ 的位移由 Markov 支付 $C_K\epsilon_1/t_0$；
余下阈值移动付 $Ct_0/Q$，归一化及移动精确均值再付 $C_K(e+w/Q)$。
先在联合可观测量上合成比较，再于有正下界的输出密度上归一化。

最终 $K_0-m_H(y)=A_k+B_y$，$B_y$ 条件中心化且与 $A_k$ 独立。
分块带权矩给 $\mathbb E[B_y^2\mid y]\le C_K(m_H+1)$；
$s_b$ 有界二阶矩，$G^4$ 用核心密度上界积分后除以 $c_K$。
这里不声称给定输出后 $G$ 仍为独立标准正态。
Gamma 密度满足 $\|p_k'\|_\infty\le C/Q^2$，
Taylor 展开中一次项由条件中心化消失，因此

$$
d_x(K):=\sup_{|y|\le K}d_K(\mathcal L(J_y-H_x(y)\mid y),F_k)
\le C_K[e+\epsilon_1/t_0+t_0/Q+w/Q+(m_H+1)/Q^2].
\tag{94.26}
$$

取 $t_0=Q^{-1/2}$，得到 $Qd_x(K)\to0$。
所有环境估计来自对固定支持一致的实际行概率界；取良好环境子列或直接删除其坏事件，
即恢复定理所述实际数据概率，证明 (94.3)。

**计数边界与并列。** Gamma 的 Stirling 展开给固定误差分位数
$t_k=Q\sqrt v\,z+(z^2-1)/3+o(1)$。
由于 $\sqrt k=Q\sqrt v+o(1)$、该处密度至少为 $c/Q$，
(94.3) 将实际分位数 $t_y$ 一致夹在 $t_k\pm o(1)$ 之间。
精确计数恒等式为

$$
C_y(t)=\#\{n:J_y(n)-H_x(y)\le t\}
=e^{H_x(y)+t}\mathbb E[e^{J_y-H_x(y)-t}
\mathbf1_{\{J_y-H_x(y)\le t\}}\mid y].
\tag{94.27}
$$

括号中的核总变差为二，故其期望与 Gamma 参考之差至多 $2d_x(K)=o(1/Q)$。
在 $t=t_y$ 处，参考积分为
$\int_0^\infty e^{-u}p_k(t_y-u)du
=\varphi(z)/(Q\sqrt v)+o(1/Q)$，一致于紧输出区间。
实际中心信息分布的任何原子质量至多 $2d_x(K)$，故截止处全部并列计数
至多 $e^{H_x(y)+t_y}2d_x(K)=o(C_y(t_y))$。
最优覆盖包含截止前的所有点与所需的截止并列点；取整误差亦包含在这个精确界中。
取对数便得 (94.2)，不需实际信息量的非格点性或单射性。

每个有限 $M$ 的原数据空间有限，故上述输出上确界作为数据函数可测。
逐输出后验概率为正且连续，覆盖大小由有限子集质量测试的最小值定义；
按概率排序并以计数组词典序处理并列给可测选择。
证明覆盖紧区间每个实输出，包括孤立并列点，未用几乎处处结论代替上确界。证毕。

**注记 94.3（条件化范围）。** 常数可依赖固定 $K$ 的正密度下界；
本章未给全实线或增长区间的一致式、误差水平趋端点、零噪声或阈值锐性。
精确条件熵仍保留在覆盖公式中，不能自动代入未在当前噪声范围证明的熵响应、
条件方差或无界期望展开。
若将余项在实际固定支持输出处评价且要求 $|Y|\le K$，
其失败事件包含于 (94.2) 的坏数据事件，因而相同概率界直接适用；
这不将已知支持下的单正态输出律识别为先验混合律，也不约束任意硬编码支持的解码器。
未知方向仍经原共同一致事件、同一标量和同一测量 $G$ 处理。

经典的高阶量化、正态密度演算和局部源计数承担各自原有结论。
本章新增的是原固定总数后验在指数测量分辨率下的逐输出带权桥梁及紧区间一致覆盖。

## 追加锚（本行以下为增补区）

## 95. 可计算的双根边缘通用参数与有符号数位障碍

**约定 95.1（原模型与有效输入）。** 保持定义 88.1 的
$D=(\beta_*,1)$、实际边缘通用集 $\mathcal V$ 和同步集合 $E_2$ 不变。
保持原固定幅度 $r$、$a=(1+r)/2$、$b=(1-r)/2$、$\phi$，以及

$$
e_1=1,\quad e_{n+1}=10^{5e_n},\quad Q_n=10^{e_n},\quad
P_n=\sum_{h\le n}10^{e_n-e_h},\quad
\vartheta=\sum_{h\ge1}10^{-e_h},\quad
\frac{\ln(1+r)}{-\ln(1-r)}=\vartheta.
\tag{95.1}
$$

所有实数运算以下均指带有理误差界的运算；可计算实数由任意精度的有理闭区间表示。
算法输入为有理端点、正长度紧区间 $J=[c,d]\Subset D$。
两种实验的 $\mu^{\mathcal E}_{Q,j}$ 都是原完整得分组的实际占据均值，
不是组内截断均值，也不是后验中心。
固定支持可任选，其均值由正侧状态置换对称性保持不变。

**定理 95.2（边缘通用集的有效稠密性）。** 存在一个全算法，
对每个上述 $J$ 输出一个固定的可计算数 $\Beta(J)\in\operatorname{int}J\cap\mathcal V$。
具体而言，输入精度 $m$ 后算法在有限时间内返回长度至多 $2^{-m}$、
包含同一个 $\Beta(J)$ 的有理闭区间。算法同时输出可计算的原合法层日程：

- 对每个正有理目标 $t_i$ 和每个符号 $\sigma$，有可计算的严格递增原层子序列，
  其完整组 pair/path 实际均值均趋于 $t_i$，并附规定的有理误差界。
- 对每个正实目标，两符号各有原层子序列实现该目标；若提供目标的可计算 Cauchy 名，
  相应子序列及其误差界可由该名字计算。
- 所构造参数避开所有原 $M$ 取整边界，故在每个给定的原合法层，
  包括未选中的层，其原 $M,q$ 及其余有限整数参数均可计算。

这里对不同符号允许不同子序列。结论不判定 $\Beta(J)$ 是否属于 $E_2$，
也不宣称实际求值具有可行的时间或空间复杂度。

证明。实质输入是严格有限证书的可枚举性；逐项建立它，再证明搜索必停。

**常数与取整。** 原十进制尾满足

$$
0<\vartheta-P_n/Q_n<2\,10^{-Q_n^5}.
\tag{95.2}
$$

因此逐个计算有限整数递推便可给出 $\vartheta$ 的任意精度包围。
正有理数的对数可用范围缩减及
$\ln y=2\sum_{h\ge0}z^{2h+1}/(2h+1)$、$z=(y-1)/(y+1)$ 计算；
截到 $h=m-1$ 后的余项绝对值至多
$2|z|^{2m+1}/((2m+1)(1-z^2))$。
对正的可计算输入，先取得远离零的包围再使用同一过程。

函数 $f(t)=\ln(1+t)/[-\ln(1-t)]$ 在 $(0,1)$ 连续严格下降，
两端极限为一、零。枚举宽度小于所需误差的有理 $l<u$，
并以区间运算证成 $f(l)>\vartheta>f(u)$，即得 $r\in(l,u)$。
每次限制在前次包围内；严格单调和连续性保证每一精度都能找到这样的包围。
该程序不调用实数等号判定或未知的逆函数模。
由此 $a,b,\phi,\beta_*$ 和原单元端点均可计算。
$I(-b/\vartheta)$ 中消失的计数项按 $0\ln0=0$ 直接取零，不求 $\ln0$。
输入承诺 $\beta_*<c<d<1$ 也可以通过严格包围证实。

第 68 章式 (68.8) 已由固定代数对数的非零线性形式界证明实际 $r$ 超越。
该结论在这里排除若干有限代数等号；不需要计算其数论下界常数。
写 $Q=Q_n$、$P=P_n$、$\lambda=Q^3$，则

$$
k_0=\lfloor aQ^3\rfloor,\quad l_0=Q^3-k_0,\quad
z_0=k_0\ln(1+r)+l_0\ln(1-r).
\tag{95.3}
$$

若 $aQ^3$ 为整数，$r$ 为有理数，矛盾；故区间细化在有限时间内确定 $k_0$。
对任一候选整数 $L\ge1$，令 $M=2^L$。原支持大小为

$$
q=\left\lfloor T_{n,L}(r)\right\rfloor,\qquad
T_{n,L}(r)=\frac{2^L}{(1+r)^{k_0}(1-r)^{l_0}}.
\tag{95.4}
$$

若 $T_{n,L}(r)=z\in\mathbb Z_{>0}$，则
$z(1+r)^{k_0}(1-r)^{l_0}-2^L=0$。
这是次数 $Q^3>0$、最高次系数非零的有理多项式，超越性排除该等号；
$T_{n,L}>0$ 也排除零。因此 $q$ 可由细化包围确定。
丢弃 $q=0$、$q\ge M$ 或不能给出合法转移概率的候选。
对合法候选置 $\kappa=q/(M-q)$、$\epsilon=\kappa r$、$n_{\rm obs}=2MQ^3$。
这些整数虽然很大，每一个都是有限对象。

原 $L_0(\beta)=\lfloor\phi Q^3/(\beta\ln2)\rfloor$ 等于 $L$ 的整个单元为

$$
\mathcal C_{n,L}=
\left(\frac{\phi Q_n^3}{(L+1)\ln2},
      \frac{\phi Q_n^3}{L\ln2}\right].
\tag{95.5}
$$

在一个这样的单元上，原 $M,q,\epsilon,n_{\rm obs}$、得分和两种实际均值均恒定。
算法只用其开放中三分之一安放后继闭区间，不改原单元及其边界约定。

**完整得分组的等号判定。** 对候选线指标
$(k_j,l_j)=(k_0+Qj,l_0+Pj)$，先验证非负且 $k_j+l_j\le n_{\rm obs}$。
在有理函数域中定义

$$
R_{k,l}(T)=
\left(\frac{1+T}{1-\kappa T}\right)^k
\left(\frac{1-T}{1+\kappa T}\right)^l\in\mathbb Q(T).
\tag{95.6}
$$

在实际 $r$ 处各因子正；原得分是 $\ln R_{k,l}(r)$。
两个得分相等，当且仅当 $R_{k,l}-R_{k',l'}$ 清分母后的有理多项式恒为零：
若非零，超越 $r$ 不能是其根；若恒为零，等号当然成立。
多项式系数等号可以有限精确判定。
故枚举所有 $k,l\ge0$、$k+l\le n_{\rm obs}$ 并作此判定，
得到原完整得分组 $G_{n,L,j}$。没有丢弃任何远端碰撞，也未假设得分单射。

令 $W_j=\ln R_{k_j,l_j}(r)$、$\tau=\ln(M/q)$、$w=\sqrt{Q^3/q}$。
条件

$$
|W_j-\tau|<w/2
\tag{95.7}
$$

在成立时有有限有理区间证书；它是进入原 $\tau-w<W\le\tau+w$ 窗的充分证书，
不是换用新窗口。若某候选恰在检验边界，单项严格搜索可以不停止，
下面的交错搜索不会让它阻塞其余候选。

**两种实际实验的有限均值。** 对幅度为 $t$ 的一行，pair 实验的精确概率为

$$
p_{\rm pair}(k,l;t)=
\frac{n_{\rm obs}!}{k!l!(n_{\rm obs}-k-l)!}
\left(\frac{1+t}{4M}\right)^k
\left(\frac{1-t}{4M}\right)^l
\left(1-\frac1{2M}\right)^{n_{\rm obs}-k-l}.
\tag{95.8}
$$

一对独立平稳观测分别提供这三类概率，故

$$
F_{\rm pair}(T)=
\sum_{(k,l)\in G_{n,L,j}}
\{q\,p_{\rm pair}(k,l;T)
 +(M-q)p_{\rm pair}(k,l;-\kappa T)\}\in\mathbb Q[T]
\tag{95.9}
$$

在 $T=r$ 的值正是完整组实际均值。这里只对期望求和，不假设各行计数独立。

path 实验保留完整转移关系。任取一个规范的大小为 $q$ 的正侧支持 $S$，
令 $b_S(u;T)$ 在支持上为 $T$，其余正侧为 $-\kappa T$，负侧为零。
原 $2M\times2M$ 矩阵为

$$
P_S(T)_{uv}=\frac{1+b_S(u;T)\operatorname{par}(v)}{2M}.
\tag{95.10}
$$

因 $qT-(M-q)\kappa T=0$，均匀初始行向量 $\pi$ 是平稳分布。
对每个正侧行 $i$，引入两个形式变量，置

$$
\begin{aligned}
A_i(T;X,Y)_{uv}
 &=P_S(T)_{uv}
 X^{\mathbf1_{\{u=i,\operatorname{par}(v)=+1\}}}
 Y^{\mathbf1_{\{u=i,\operatorname{par}(v)=-1\}}},\\
Z_i(T;X,Y)&=\pi A_i(T;X,Y)^{n_{\rm obs}}\mathbf1,\\
F_{\rm path}(T)
 &=\sum_{i\in C_+}\sum_{(k,l)\in G_{n,L,j}}
 [X^kY^l]Z_i(T;X,Y)\in\mathbb Q[T].
\end{aligned}
\tag{95.11}
$$

展开有限矩阵幂，$Z_i$ 就是该行出边标记的精确 PGF，
故 $F_{\rm path}(r)$ 是实际平稳路径的完整组均值。
正侧状态置换说明任选规范支持不改变此值。
有限多项式矩阵乘法给出一个终止的算法，无需把路径改成独立行模型。

因此，对有理正带 $(A,B)$，严格条件

$$
A<F_{\rm pair}(r)<B,\qquad A<F_{\rm path}(r)<B
\tag{95.12}
$$

在成立时总有有限精度证书。事实上，与有理端点的比较也可先检查差多项式
是否恒为零，非零时再由超越性保证细化终止；构造只需严格条件的半判定性。
有限概率求值不使用任何未知的渐近起始层或收敛速度。

**固定日程及嵌套算法。** 将正有理数 $t_i$ 按既约分数分子分母之和、
再按分子排序。第 $k$ 轮依次访问 $i=1,\ldots,k$ 和符号 $+,-$，使用

$$
\eta_{i,k}=\min(t_i/4,2^{-k}),\qquad
B_{i,k}=(t_i-\eta_{i,k},t_i+\eta_{i,k}).
\tag{95.13}
$$

两端之比至多 $5/3<2$；两符号对应阶段
$s=k(k-1)+2i-1$ 和 $s=k(k-1)+2i$。
另以固定配对次序枚举所有可计算的原取整边界

$$
d_{n,L}=\frac{\phi Q_n^3}{L\ln2},\qquad n,L\ge1.
\tag{95.14}
$$

允许重复。先在 $\operatorname{int}J$ 中选一个正长度有理闭区间 $I_0$，置 $n_0=0$。
由简单根的单调有理包围，计算两个有理紧弧 $K_-,K_+$，
使其分别严格处于负、正计数内部域，且包含 $J$ 上全部相应率根于内部。
这只需用 $I$ 和 $c(\beta)$ 的严格端点比较；紧内部输入保证这样的弧存在。

阶段 $s$ 已有固定有理闭父区间 $I_{s-1}$ 及前一原层 $n_{s-1}$。
同时交错搜索整数三元组 $(n,L,j)$ 及其有理精度证书，要求：

1. $n>n_{s-1}$、$L\ge1$、$j/Q_n^2\in K_\sigma$，上述全部整数与概率合法；
   整个 $\mathcal C_{n,L}$ 的两端严格处于 $\operatorname{int}I_{s-1}$。
2. 式 (95.7) 和对当前 $B_{i,k}$ 的两个实际均值条件 (95.12) 都被严格证成。
3. 找到这样的三元组后，在该同一单元的开放中三分之一内寻找正长度有理闭区间
   $I_s$，长度至多 $2^{-s}$，并以严格分离证书排除 (95.14) 枚举的前 $s$ 点。

整数、有理数、多项式和证书均用固定自然数编码；例如使用 Cantor 配对、
带符号整数编码及既约分数编码。交错搜索在时刻 $h$ 给前 $h$ 个候选各模拟
$h$ 个额外基本步骤，以固定编码打破同时成功的并列。
因此每个有限成功证书最终都会被检出；一个等号或不成功的候选不阻塞其它候选。
这是单一确定算法的调度说明。

**终止性。** 在任一阶段，父区间及正带已经固定。
第 88 章式 (88.10)–(88.13) 给出任意充分晚的原层内、整个包含于该父区间的
原 floor 单元，带有所需符号的指标，两个实际完整组均值均严格位于当前带。
可先取有理内带，再用其到外带的正裕量。
原得分比较还给 $W_j=\tau+o(w)$，故这些晚层满足 (95.7)。
指标处于所选 $K_\sigma$，且参数合法。
从而至少一个候选具有全部有限严格证书，交错搜索必定找到。

所得开放中三分之一有正长度，删除有限个点后仍含正长度开区间。
其中有任意小的正长度有理闭区间，与这些点之间的严格间隔都可由细化包围证成。
故第三步也终止。此论证不要求计算 (88.12) 的起效层：
存在定理保证成功证书存在，算法实际检验的始终是有限精确条件。

现有 $I_s\Subset\operatorname{int}I_{s-1}$ 且 $|I_s|\le2^{-s}$，
故交集含唯一 $\Beta(J)$。运行前 $m$ 阶段并返回 $I_m$ 即计算同一个数。
每个选中原单元都含该数于内部，故记录的层、$L,M,q,j$ 是该固定参数的
原模型历史，(95.12)–(95.13) 给出其实际误差界。
对固定 $i,\sigma$，取轮数 $k\ge i$ 就得到可计算的原层子序列及误差 $2^{-k}$。

每个边界 $d_{n,L}$ 最终被永久排除，所以任一给定层的
$\phi Q_n^3/(\Beta(J)\ln2)$ 不为整数。
细化该可计算实数的包围便能确定原 $L_0$，再由 (95.4) 计算 $q$。
这是对构造所得参数的结论；没有断言任意可计算实数的取整都可统一计算。

对任意实 $\theta>0$，选正有理 $t_{i_h}$ 满足
$|t_{i_h}-\theta|<2^{-h-2}$，再取严格递增且满足
$k_h\ge i_h$、$k_h>h+2$ 的轮数。
相应有符号阶段的两个实际均值与 $\theta$ 的距离都小于 $2^{-h}$。
若给出 $\theta$ 的可计算 Cauchy 名，以上选择均可有效完成；一般实目标只用存在性。
这恰是同一个参数属于原 $\mathcal V$ 的要求，证毕。

**注记 95.3（经典有效 Baire 输入与同步边界）。** 嵌套选择属于经典有效 Baire 方法。
Brattka–Hendtlass–Kreuzer 的 $\mathrm{BCT}_0$ 在可计算 Polish 空间中，
对以负信息表示的无处稠密闭集序列，给出可计算的共同补集点。
这里对每个有理带、符号和下限层，枚举严格通过 (95.7)、(95.12) 的单元内部
所含有理开区间，便得到一致可枚举的稠密开集；其补集恰有该定理要求的负信息。
可计算边界点的补集也可如此枚举。
定理 95.2 给出该经典工具在本模型中的具体证书，并额外保留原层和均值日程。
它不要求此前任意预选内弧具有有效描述，也未重新定义 $\mathcal V_0$ 或 $\mathcal V$。

单凭稠密剩余性不能推出存在可计算点；所需区别在于这里能枚举严格有限证书。
另一方面，一个固定序列只有可数多个可计算子序列，每个收敛子序列只有一个极限，
故不能要求所有正实目标都无输入地拥有可计算实现子序列。
小 Hausdorff 维数也不能保证避开全部可计算点；
定理 88.2 的非有效 $\mathcal V\setminus E_2$ 结论并未因此有效化。
$E_2$ 的非空性、空性以及所构造参数与它的关系仍为 OPEN。

**命题 95.4（复现根的有符号数位块）。** 对任意固定 $\beta\in D$，
若根 $x=x_\sigma(\beta)$ 的实际完整组均值沿原合法子序列趋于正有限值，
则 $y=\{x\}$ 的十进制展开在位置 $2e_n+1$ 开始具有长度
$e_n-\log_{10}e_n+O(1)$ 的连续相同数位块：正根为零块，负根为九块。
相应数位在前缀中的频率上极限至少为 $1/3$；
因而该根不是十进制简单正规数，数位频率最大偏差的上极限至少为 $7/30$。

证明。正有限实际复现结合 (93.8) 先给
$d_Q=j-Q^2x=O(\ln Q/Q)$。
在简单根处展开并保留有界 floor 项，得

$$
\ln\mu^{\mathcal E}_{Q,j}
 =-QI'(x)d_Q-3\ln Q+C_Q(x;\beta)+o(1),\qquad
d_Q=-\frac{3\ln Q}{QI'(x)}+O(Q^{-1}).
\tag{95.15}
$$

二次余项为 $d_Q^2/Q=o(1)$。因为 $I'(x)$ 与 $x$ 同号，充分晚时

$$
\begin{cases}
j=\lfloor Q^2x\rfloor,\quad
\{Q^2x\}=3\ln Q/(QI'(x))+O(Q^{-1}),&x>0,\\
j=\lceil Q^2x\rceil,\quad
1-\{Q^2x\}=3\ln Q/(Q|I'(x)|)+O(Q^{-1}),&x<0.
\end{cases}
\tag{95.16}
$$

有符号偏移来自原 $-3\ln Q$ 前因子；无符号的近整数上界不足以区分两种数位。
由于 $Q=10^e$，相应正距离为

$$
\delta_n=\frac{3\ln10}{|I'(x)|}\,e_n10^{-e_n}+O(10^{-e_n}).
\tag{95.17}
$$

取一个固定足够大的整数 $C$，则沿该子序列最终有
$0<\delta_n<10^{-m_n}$，其中
$m_n=e_n-\lceil\log_{10}e_n\rceil-C>0$。
乘 $10^{2e_n}$ 将数位移到位置 $2e_n+1$，(95.16) 遂分别强制前 $m_n$ 位
全零或全九。式 (95.17) 的同阶下界也将这段连续块的最大长度限制为
$e_n-\log_{10}e_n+O(1)$。
定理 93.2 已给复现根超越，不存在终止展开与无限九尾的歧义；
也可统一采用不最终为九的标准展开。

令 $A_d(T)$ 为 $y$ 的前 $T$ 位中数位 $d$ 的次数，$T_n=2e_n+m_n$。
正根取 $d=0$，负根取 $d=9$，则

$$
\frac{A_d(T_n)}{T_n}\ge\frac{m_n}{2e_n+m_n}\longrightarrow\frac13,
\qquad
\limsup_{T\to\infty}\max_{0\le d\le9}
\left|\frac{A_d(T)}T-\frac1{10}\right|\ge\frac7{30}.
\tag{95.18}
$$

这与简单正规性要求的各频率 $1/10$ 矛盾，证毕。
论证使用块占整个前缀的正比例；仅有任意长块不能排除正规性。

定理 95.2 构造的两个根可以通过简单根单调包围计算，
又都具有正有限复现，因此都是可计算、超越且十进制非正规的实数。
没有把根的数位结论通过非线性映射转移给 $\Beta(J)$。
本章没有新增参数先验、期望熵极限、同层双根极限或有效解码结论；
已知反向只沿原坐标对齐，不为数据依赖判向规则补作期望转移。
一般有效 Baire 与正规数定义归属既有文献；这里新增的是原完整模型证书、
取整可计算性及有符号前缀障碍的对应。它们是普通数学推导，未宣称 Lean 核验。

## 追加锚（95 章后）

## 96. 紧输出区间上显式的常数阶熵响应

**定义 96.1（同一后验的中心信息与局部矩）。** 保持定义 94.1 的原完整组计数后验、
精确标量 $T$、测量 $Y=T+\sigma_MG$ 和全部原取整，要求

$$
L_M=\ln(1/\sigma_M)\longrightarrow\infty,
\qquad \limsup_M L_M/Q^3<c_q/2.
\tag{96.1}
$$

信息量均用自然对数。记 $S_x(n)=-\ln P_x(n)$、$h_x=\mathbb E_xS_x(R)$，
$H_x(y)$ 为精确输出后验熵；它们不是主项近似。
使用原轮廓 $\rho(t)=c_0e^{-\kappa t^2/2}$，其中
$c_0=(4\pi\sqrt{ab})^{-1}$、$\kappa=1/a+\alpha^2/b$，置

$$
\gamma=\int\rho,\quad g_0=\int\rho^2,\quad g_3=\int\rho^3,\quad
\nu=2g_0,\qquad
A_M^\sigma=\frac{\gamma}{\sqrt\delta(\nu+\sigma_M^2)},
\quad b_S=\frac{1-2/\sqrt3}{\nu},
\quad b_H=\frac{1/2-2/\sqrt3}{\nu}.
\tag{96.2}
$$

此处 $b_S$ 仅为熵响应系数，不是站点漂移函数。
以下条件期望由正的有限 Gaussian 混合后验定义于每个实输出。

**定理 96.2（完整噪声区间内的局部熵响应）。** 对每个固定 $K<\infty$、$K\ge0$，

$$
\sup_{|y|\le K}
\left|\mathbb E_x[S_x-h_x\mid y]
-A_M^\sigma y-b_S(y^2-\nu)\right|\longrightarrow0,
\tag{96.3}
$$

$$
\sup_{|y|\le K}
\left|H_x(y)-h_x+L_M-A_M^\sigma y
-b_H(y^2-\nu)+\tfrac12\ln\nu\right|\longrightarrow0.
\tag{96.4}
$$

收敛为原实际数据概率收敛，且对所有规定大小的固定真实支持一致；
pair/path 两种原实验分别成立。精确地，对任意固定 $\eta>0$，
左侧超过 $\eta$ 的数据概率对这些支持和两种实验取上确界后趋零。
这些是同一均匀支持先验定义的纤维函数在固定支持数据律下的评价，
不把已知真实支持后的输出律当作先验混合密度。

证明。先建立实际局部矩的传递，再在正密度紧区间归一化。
沿用第 94 章的共同量化空间、核心 $\mathcal H$、外部 $O$，
以及 $U_j,v_j,e_j,L_x,a_x$。核心半径为 $H_M=\sqrt{D\ln Q}$，
固定 $D$ 可增大，使 $V_O\le Q^{-200}$ 于一致良好数据事件上成立。
所有中间替换仅用于估计同一个实际 $T$，保持精确后验中心与有限截距。

**分离中心信息密度与噪声残差密度。** 记

$$
\begin{aligned}
f_x(y)&=\mathbb E_x\varphi_\sigma(y-T),\\
q_x(y)&=\mathbb E_x[(S_x-h_x)\varphi_\sigma(y-T)],\\
u_x(y)&=\mathbb E_x[((y-T)/\sigma)^2\varphi_\sigma(y-T)],\\
g(y)&=\mathbb E\varphi_\sigma(y-T_H^{\rm G}),\\
q_G(y)&=\mathbb E[S_H\varphi_\sigma(y-T_H^{\rm G})],
\qquad S_H=\tfrac12\sum_{j\in\mathcal H}(Z_j^2-1),\\
u_G(y)&=\mathbb E[((y-T_H^{\rm G})/\sigma)^2
                              \varphi_\sigma(y-T_H^{\rm G})].
\end{aligned}
\tag{96.5}
$$

比值 $u_x/f_x$ 等于
$\mathbb E_x[G^2\mid Y=y]$。所有参考期望都在第 94 章的同一辅助乘积空间。
式 (94.18)、(94.23) 的质量部分直接给

$$
\|f_x-g\|_\infty=O(Q^{-5/2}).
\tag{96.6}
$$

为分离 (94.18) 的信息量与残差平方，设
$\psi_\sigma(t)=(t/\sigma)^2\varphi_\sigma(t)$。
将 (94.14)、(94.16)–(94.17) 的核换成此正多项式核，
宽 Gaussian 包络及独立核心块平滑给

$$
\|u_x-u_m\|_\infty\le CQ^{-5/2}+Ch_Q+o(Q^{-90}),
\qquad u_m(y)=\mathbb E\psi_\sigma(y-T^{\rm mix}).
\tag{96.7}
$$

具体地，换律成本是 $CQ^{-5/2}$ 乘 $V+W^2$ 与残差平方的带权密度，
由 (94.9) 的固定阶矩及 Hölder 一致控制。
小位移成本由 (94.13) 的多项式核版本支付 $Ch_Q$；
坏事件上的 $\sigma^{-1}$ 由 (94.12) 的高固定矩支付。
没有把无界残差通过 TV 传递，也没有将多项式换律误差除以 $\sigma$。

核心输入密度 $h_H$ 的一阶导数上确界由 (94.6) 的加权 Fourier 积分控制。
外部能量差 $E_O=T^{\rm mix}-T_H^{\rm G}$ 独立于核心及同一个 $G$，故

$$
u_m(y)=\mathbb E[G^2h_H(y-\sigma G-E_O)],\qquad
u_G(y)=\mathbb E[G^2h_H(y-\sigma G)],\qquad
\|u_m-u_G\|_\infty\le C\mathbb E|E_O|=o(Q^{-90}).
\tag{96.8}
$$

此处未出现外部信息量，故只需边缘导数；其与外部能量的相关性
已经在 (94.19)–(94.23) 的联合密度比较中支付。
有限 Gaussian 核恒等式又给

$$
u_G=g+\sigma^2g'',\qquad \|u_x-u_G\|_\infty=O(Q^{-5/2}).
\tag{96.9}
$$

令 $A_A,A_H$ 为 (94.18)、(94.23) 的实际及最终参考一阶矩密度。
最终参考中，核心外的中心信息量独立于 $(T_H^{\rm G},G)$ 且均值为零，
所以 $A_H=q_G+u_G/2$。实际恒等式为
$q_x=A_A-u_x/2-(h_x-\widetilde h)f_x$。
原选中密度的精确熵比较给
$|h_x-\widetilde h|\le CQa_x+a_x^2=O(Q^{-3/2})$。
由 (94.18)、(94.23) 的 $O(Q^{-3/2})$ 一阶矩密度界，得到

$$
\|q_x-q_G\|_\infty=O(Q^{-3/2}),\qquad
\delta^{-1/2}\|f_x-g\|_\infty=O(Q^{-9/4}).
\tag{96.10}
$$

中心化后才估计信息量，使其矩成本为 $Q$ 而非 $Q^5$。
全固定总数的依赖在 $L_x$ 中处理完毕后，才使用参考外部信息量的独立性。

**实际方差轮廓的定量精度。** 常数阶中心需要比单纯轮廓收敛更强的速率。
在同一对数核心上，原 Poisson 率的三阶 Taylor 余项及 Stirling 公式给

$$
f_j^{\rm sig}
=\frac{e^{-\kappa(j\delta)^2/2}}{2\pi Q^3\sqrt{ab}}
 \left[1+O\left(\frac{1+H_M^3}{Q^{3/2}}\right)\right].
\tag{96.11}
$$

原有界 floor 误差贡献 $O((1+H_M)/Q^{3/2})$，包含于上式；
原固定斜率的算术逼近余项在此范围内更小。
混合行均值与 $2qf_j^{\rm sig}$ 的比为 $1+O(w+q/M)$，而校准给
$\sup_j|p_j-1/2|=O_{\mathbb P}(w+q^{-1/2}+q/M)$。
这些校准项指数小于任何所需固定幂。
实际一／二行估计以相对容差 $Q^{-2}$ 对核心并合，失败概率至多

$$
CQ^4(1+H_M/\delta)
 [e^{-c_qQ^3+O(H_M^2+\ln Q)}+e_{\rm row}]\longrightarrow0.
\tag{96.12}
$$

故对精确观测方差，
$\sup_{j\in\mathcal H}|v_j/(\delta\rho(j\delta))-1|=o_{\mathbb P}(\delta)$。
可积可微函数的网格界
$|\delta\sum_jF(j\delta)-\int F|\le\delta\int|F'|$
由逐格积分中值差得到。将它用于 $\rho,\rho^2,\rho^3$，
再用增大固定 $D$ 后的 Gaussian 尾界，即得

$$
V_H:=\sum_{\mathcal H}v_j=\gamma+O_{\mathbb P}(\delta),\qquad
\nu_H:=2\delta^{-1}\sum_{\mathcal H}v_j^2
       =\nu+O_{\mathbb P}(\delta),\qquad
\delta^{-2}\sum_{\mathcal H}v_j^3\longrightarrow g_3.
\tag{96.13}
$$

这没有假设实际路径各行独立。精确中心还满足
$\|e\|^2\le a_x^2V=O_{\mathbb P}(Q^{-5})$ 及
$\sum_{\mathcal H}v_je_j^2/\delta\le C\|e\|^2$。
不需要每个远端核心的 $e_j/\sqrt{v_j}$ 都一致趋零。

**独立块控制二阶密度导数。** 写

$$
T_H^{\rm G}=\sum_{\mathcal H}w_j[(Z_j-c_j)^2-1]
             +\delta^{-1/2}\|e_O\|^2,\qquad
w_j=v_j/\sqrt\delta,\quad c_j=e_j/\sqrt{v_j},
\tag{96.14}
$$

$$
\mu_G=\delta^{-1/2}\|e\|^2,\qquad
v_G=2\sum w_j^2+4\sum w_j^2c_j^2,\qquad
\max w_j\le C\sqrt\delta,\quad
\sum w_j^2c_j^2=O_{\mathbb P}(a_x^2).
\tag{96.15}
$$

将核心按指标模四分块，每块都含 $c/\delta$ 个
$w_j\asymp\sqrt\delta$ 的中心坐标。
每一块及由两块组成的半核心的特征函数模均不超过
$(1+c_1\delta t^2)^{-c_2/\delta}$。
对每个固定 $r$，其乘 $|t|^r$ 的积分及尾积分如 (94.6) 所证一致受控。
因此两个独立半核心输入密度 $h_A,h_B$ 满足

$$
\|h_A''\|_\infty+\|h_B''\|_\infty\le C,\qquad
\|g-\varphi_\nu\|_\infty+\|g''-\varphi_\nu''\|_\infty\longrightarrow0.
\tag{96.16}
$$

第二式由中心二次和的累积量收敛、(96.15) 的低阶余项及加权 Fourier 支配得到；
卷积消失的正态噪声仍满足该支配。它不是对弱收敛形式求导。
这也属于 Herry–Malicet–Poly 的有限 Wiener chaos 密度超收敛范围；
这里显式分块给出与噪声无关的有限导数界。

**两次精确 Gaussian 分部积分。** 令
$a_0=\sum w_j=V_H/\sqrt\delta$、$\Lambda_G=v_G+\sigma^2$、$A_G=a_0/\Lambda_G$。
以下求和均在核心。
对有限正噪声直接逐坐标分部积分，得到

$$
q_G=-a_0g'-\mathbb E[\mathcal A_c\varphi_\sigma'(y-T_H^{\rm G})],\qquad
\mathcal A_c=\sum[w_j(Z_j^2-1)-w_jc_jZ_j],
\tag{96.17}
$$

$$
(y-\mu_G)g=-\Lambda_Gg'
-\mathbb E[\mathcal B_c\varphi_\sigma'(y-T_H^{\rm G})],\qquad
\mathcal B_c=\sum[2w_j^2(Z_j^2-1)-6w_j^2c_jZ_j].
\tag{96.18}
$$

第一式使用 $\mathbb E[(Z^2-1)F]=\mathbb E[Z\partial_ZF]$；
第二式使用
$\mathbb E[(T_H^{\rm G}-\mu_G)F(T_H^{\rm G})]
=\mathbb E[\mathcal BF'(T_H^{\rm G})]$，其中
$\mathcal B=2\sum w_j^2(Z_j-c_j)(Z_j-2c_j)$、$\mathbb E\mathcal B=v_G$，
再结合 $(y-t)\varphi_\sigma(y-t)=-\sigma^2\varphi_\sigma'(y-t)$。
因此 (96.18) 的分母必须包含实际 $\sigma^2$。

消去 $g'$，置 $h_j=w_j-2A_Gw_j^2$、$k_j=-w_jc_j+6A_Gw_j^2c_j$。
第二次分部积分给

$$
q_G-A_G(y-\mu_G)g
=\mathbb E[\mathcal C\varphi_\sigma''(y-T_H^{\rm G})],\quad
\mathcal C=\sum[2h_jw_jZ_j(Z_j-c_j)+2k_jw_j(Z_j-c_j)].
\tag{96.19}
$$

它的均值及中心部分精确为

$$
\begin{aligned}
C_M&=2\sum w_j^2-4A_G\sum w_j^3
       +2\sum w_j^2c_j^2-12A_G\sum w_j^3c_j^2,\\
\mathcal C-C_M&=\sum[d_j(Z_j^2-1)+l_jZ_j],\\
d_j&=2w_j^2-4A_Gw_j^3,\qquad
l_j=-4w_j^2c_j+16A_Gw_j^3c_j.
\end{aligned}
\tag{96.20}
$$

此处 $d_j$ 仅为多项式系数。
因 $A_G=O(\delta^{-1/2})$、$\max w_j=O(\sqrt\delta)$，
每个独立半核心的中心贡献 $J_A,J_B$ 均满足

$$
\mathbb EJ_A^2+\mathbb EJ_B^2
\le C\sum(w_j^4+w_j^4c_j^2)
\le C\delta[\sum w_j^2+\sum w_j^2c_j^2]\le C\delta.
\tag{96.21}
$$

条件于 $A$ 半核心，以独立 $B$ 半核心平滑二阶导数，(96.16) 给
$\sup_y|\mathbb E[J_A\varphi_\sigma''(y-T_H^{\rm G})]|
\le\mathbb E|J_A|\|h_B''*\varphi_\sigma\|_\infty\le C\sqrt\delta$；
另一半相同。精确截距分配到任意一半不影响导数范数。因此

$$
\|q_G-A_G(y-\mu_G)g-C_Mg''\|_\infty\le C\sqrt\delta.
\tag{96.22}
$$

这是带符号的一阶矩密度的局部展开，独立块承担增长维数的中心余项，
没有收取 $\sigma^{-3}$ 等测量核导数成本。

式 (96.13)、(96.15) 进一步给

$$
\begin{gathered}
C_M\longrightarrow C_*:=\nu-4\gamma g_3/\nu,\qquad
v_G=\nu+O_{\mathbb P}(\delta)+O_{\mathbb P}(a_x^2),\\
|A_G-A_M^\sigma|
\le C\delta^{-1/2}(|V_H-\gamma|+|v_G-\nu|)=o_{\mathbb P}(1),\qquad
|A_G\mu_G|\le C\delta^{-1}\|e\|^2=o_{\mathbb P}(1).
\end{gathered}
\tag{96.23}
$$

$C_M$ 中非中心项为 $O_{\mathbb P}(a_x^2)$，且
$A_G\sum w_j^3=(V_H/\Lambda_G)\delta^{-2}\sum v_j^3$。
常数项的极限可令 $\sigma^2\to0$；线性项的两个分母都保留 $\sigma^2$，
其 $\delta^{-1/2}$ 放大由实际轮廓的 $O_{\mathbb P}(\delta)$ 速率支付。

**归一化与精确熵恒等式。** 对 $|y|\le K$，精确分拆

$$
\begin{aligned}
q_x-A_M^\sigma yf_x-C_*\varphi_\nu''
={}&(q_x-q_G)+(q_G-A_G(y-\mu_G)g-C_Mg'')\\
&+(A_G-A_M^\sigma)yg-A_G\mu_Gg\\
&+A_M^\sigma y(g-f_x)+(C_Mg''-C_*\varphi_\nu'').
\end{aligned}
\tag{96.24}
$$

前两项由 (96.10)、(96.22) 趋零，中间两项由 (96.23) 趋零。
被放大的密度差仍由 (96.10) 的显式速率趋零，最后一项由 (96.16)、(96.23) 趋零。
紧区间上 $f_x,g$ 均有确定正下界，且 $f_x\to\varphi_\nu$ 一致。
除以 $f_x$，用 $\varphi_\nu''/\varphi_\nu=(y^2-\nu)/\nu^2$，得到
$\mathbb E_x[S_x-h_x\mid y]=A_M^\sigma y+(C_*/\nu^2)(y^2-\nu)+o_{\mathbb P}(1)$。

同时 (96.9)、(96.16) 给 $u_x/f_x\to1$ 在紧区间上一致。
信息密度 $i_x=\ln(\varphi_\sigma(Y-T)/f_x(Y))$ 精确满足

$$
i_x-L_M=-\tfrac12\ln(2\pi)-G^2/2-\ln f_x(Y).
\tag{96.25}
$$

故

$$
\sup_{|y|\le K}\left|
\mathbb E_x[i_x-L_M\mid y]
-\left[\tfrac12\ln\nu+\frac{y^2-\nu}{2\nu}\right]\right|
\longrightarrow0.
\tag{96.26}
$$

这一步控制了实际条件残差矩，没有假设观察 $Y$ 后 $G$ 仍独立。
$\ln f_x(y)$ 在固定输出处是确定数，紧区间正下界保证对数的一致收敛。
最后 Bayes 恒等式
$H_x(y)-h_x+L_M=\mathbb E_x[S_x-h_x\mid y]-\mathbb E_x[i_x-L_M\mid y]$
给 (96.4)。直接积分 Gaussian 轮廓得
$\gamma g_3/g_0^2=2/\sqrt3$，所以 $C_*/\nu^2=b_S$、
$b_S-1/(2\nu)=b_H$，证明了所列显式常数。

全部估计先在确定良好环境上成立；实际行估计、核心占据、校准及尾界的
失败概率对固定支持一致趋零，遂恢复所述数据概率量词。
有限纤维的正混合后验及熵函数连续，紧区间上确界可由可数稠密集取得，因而可测。
没有对外层数据作无界期望交换。证毕。

**推论 96.3（以原精确熵为中心的显式覆盖）。** 保持固定
$\varepsilon\in(0,1)$、$z=\Phi^{-1}(1-\varepsilon)$ 和 $v=\ell_*/2$，则
在定理 96.2 的同一紧区间与概率量词下，

$$
\begin{aligned}
\ln N_\varepsilon(x,y)
={}&h_x-L_M+A_M^\sigma y+b_H(y^2-\nu)-\tfrac12\ln\nu\\
&+Q\sqrt v\,z-\ln Q+\frac{z^2-1}{3}
+\ln\varphi(z)-\tfrac12\ln v+o_{\mathbb P}(1).
\end{aligned}
\tag{96.27}
$$

证明。将 (96.4) 代入 (94.2)；两个余项对同一个后验、标量和输出成立，
其紧区间上确界可相加。此处没有组合分别可达而不共同实现的近似。证毕。

式 (96.4) 的噪声方差项一般不能删去。事实上

$$
A_M^\sigma-\frac{\gamma}{\nu\sqrt\delta}
=-\frac{\gamma\sigma_M^2}{\sqrt\delta\,\nu(\nu+\sigma_M^2)}.
\tag{96.28}
$$

合法序列 $\sigma_M=Q^{-1/16}$ 使右端绝对值按 $Q^{1/8}$ 增长。
因此对任何固定 $K>0$，无噪声线性系数不能在此范围提供 $o(1)$ 一致余项。
这不改变此前已明确较强噪声条件的结论。

本章不提供全实线或增长输出区间的一致展开、变化误差水平、零噪声、
半指数端点或阈值锐性、全数据期望熵、期望对数覆盖大小以及高效解码。
若把误差在实际固定支持的 $Y$ 处评价并要求 $|Y|\le K$，坏事件包含于上述坏数据事件；
这仍未识别已知支持下的输出律与先验混合律。
未知方向沿原共同一致事件并保持同一测量噪声处理。
Gaussian 分部积分、超收敛和经典局部计数各归既有来源；
本章新增的是原固定总数模型的独立局部矩传递、精确有限噪声回接及显式常数阶响应。

## 追加锚（96 章后）

## 97. 可计算的边缘通用参数与全晚层同步排除

**定义 97.1（原同步集合与必要算术包络）。** 保持第 88、95 章的
$D=(\beta_*,1)$、原边缘通用集 $\mathcal V$、同步集合 $E_2$、
固定幅度及原合法 $Q_n$、$M,q$ 和完整得分组。
输入为正长度有理闭区间 $J\Subset D$。记两个简单率根为
$x_+(\beta)>0>x_-(\beta)$，定义
$T_{n,m}^{\mathcal E}(\beta)$ 为：同一原层 $n$、同一个 $M,q$ 下，
两根处各有一个完整组，其实际均值均在 $[1/m,m]$ 内，
其中 $m\ge2$、$\mathcal E\in\{pair,path\}$。置

$$
S_n=\left\{\beta\in J:
 \|Q_n^2x_+(\beta)\|\le Q_n^{-3/4},\
 \|Q_n^2x_-(\beta)\|\le Q_n^{-3/4}\right\}.
\tag{97.1}
$$

这里 $\|t\|$ 表示到最近整数的距离，$S_n$ 只是必要条件的放宽包络。

**定理 97.2（有效的非同步边缘通用性）。** 存在全算法，由上述有理端点构造
同一个可计算实数

$$
\Beta(J)\in\operatorname{int}J\cap(\mathcal V\setminus E_2).
\tag{97.2}
$$

算法在输入精度 $m$ 时返回含该数、长度不超过 $2^{-m}$ 的有理闭区间，
并可计算一个 $n_0$，使

$$
\Beta(J)\notin S_n\qquad(n\ge n_0).
\tag{97.3}
$$

对每个正有理目标和每个符号，算法保留原层子序列与有限严格证书，
使 pair/path 两种实际完整组均值同时逼近该目标。
对给有可计算名的正实目标，子序列相对于该名可计算；
所有正实目标的存在性仍属于同一个 $\mathcal V$。
构造点避开全部原 $M$ 的取整边界，因而每个单独原层的有限模型都可计算。
这里不声称已给出任意实际均值带 $[1/m,m]$ 的数值排除起点，也不声称效率。

证明。关键是先独立构造承载原边缘复现的可计算测度，
再以全部未来同步包络的有效尾和定义可计算的剩余测度。

**实际同步的量词与包络方向。** 原同步定义精确等价于

$$
E_2^{\mathcal E}
=\bigcup_{m\ge2}\limsup_n\{\beta:T_{n,m}^{\mathcal E}(\beta)\}.
\tag{97.4}
$$

两个正有限极限最终落在某个紧正方形内；反之，同一紧正方形内的无限命中
有均值对收敛的子序列。原实际 pair/path 相对均值桥使两集合相同。
这不要求两实验数据律相同。

式 (93.8)、(95.15) 的原完整组展开保留所有 floor 项，并给固定
$\beta,m$ 下的晚期紧正均值指标

$$
j-Q^2x_\sigma(\beta)
=-\frac{3\ln Q}{QI'(x_\sigma(\beta))}+O_{\beta,m}(Q^{-1}).
\tag{97.5}
$$

简单根导数与零分离，且 $\ln Q/Q=o(Q^{-3/4})$，所以每个固定
$\beta,m$ 的充分晚同步命中属于 $S_n$。因此

$$
E_2\cap J\subseteq\limsup_n S_n.
\tag{97.6}
$$

以下算法只使用可计算的 $S_n$ 上覆盖。
此蕴含允许无数值起点的实际渐近证明，但算法不把该未知起点当作输入；
放宽包络只能用于排除，不能认证一次实际同步命中。

**可计算紧弧与精确证书。** 第 95 章的严格包围计算
$r,a,b,\phi$、两个简单根及原有限模型。取含 $J$ 根像且留有正缓冲的
有理紧弧 $K_+,K_-$，均远离零及计数域端点。
令 $F(u)=\phi/(\phi+I(u))$，并在正弧上以 $I(\Psi(u))=I(u)$ 定义负根映射。
已有曲率符号也可直接核对：

$$
I''(x)>0,\quad I'''(x)<0,\quad
\frac{d}{dx}[I'(x)^2-2I(x)I''(x)]=-2I(x)I'''(x)>0\quad(x\ne0).
\tag{97.7}
$$

该括号在零处为零。对 $v=\Psi(u)<0<u$，由 $I(u)=I(v)>0$ 得

$$
\frac{I''(u)}{I'(u)^2}<\frac1{2I(u)}
 <\frac{I''(v)}{I'(v)^2},\qquad
\Psi''(u)=\frac{I'(u)^2}{I'(v)}
 \left[\frac{I''(u)}{I'(u)^2}-\frac{I''(v)}{I'(v)^2}\right]>0.
\tag{97.8}
$$

有理区间细分、隐式根单调包围及连续性给可计算有理常数

$$
0<c\le1,\quad C\ge1,\quad c\le\Psi''\le C,\quad
|\Psi'|\le B,\qquad 0<b_F\le|F'|\le B_F,\quad B_F\ge1.
\tag{97.9}
$$

严格正性保证有限细分最终认证这些界；并未查询不可计算的极小值。

每个候选原单元
$C_{n,L}=(\phi Q_n^3/((L+1)\ln2),\phi Q_n^3/(L\ln2)]$
上，$M,q$、补偿、得分与两种均值完全不变。
第 95 章的有限算法枚举 $k+l\le n_{\rm obs}$ 的全部标记，
由有理函数恒等式判断精确得分碰撞，用实际多项式概率与标记路径矩阵
计算整个组的 pair/path 均值。
因此对正有理开带 $(A,B')$，条件

$$
|W_j-\tau|<w/2,\qquad
A<\mu_{n,j}^{pair}<B',\qquad A<\mu_{n,j}^{path}<B'
\tag{97.10}
$$

均有半可判定的有限严格证书。这里较强得分裕量仅认证原完整窗口成员。
单元及有理子区间的严格包含也半可判定。
对所有候选作公平交错搜索，避免某个等号候选阻塞其它成功证书。

**全部同步包络的有效粗覆盖。** 写 $N=Q^2$、
$\epsilon_Q=Q^{-3/4}$、$\delta_Q=Q^{-11/4}$。
对 $n\ge2$，$e_n$ 被四整除，所以这些幂及 $\sqrt Q$ 都是精确有理数。
取正弧 $K=K_+$，有理 $T\ge|K|+2$、$T\ge2$。
当原层足够大且缓冲已由有理不等式认证时，
$\beta\in S_n$ 蕴含某个 $j/N\in K$ 满足

$$
\|N\Psi(j/N)\|\le(1+B)\epsilon_Q,\qquad
|\beta-F(j/N)|\le B_F\delta_Q.
\tag{97.11}
$$

对每个 $j/N\in K$ 计算有理 $z_j$，误差不超过 $\epsilon_Q/16$；
保留 $\|z_j\|\le(B+3/2)\epsilon_Q$ 的指标。
此比较可判定，必保留 (97.11) 的全部指标，
且每个保留指标满足 $\|N\Psi(j/N)\|<(B+2)\epsilon_Q$。
再以误差 $\delta_Q$ 计算 $F(j/N)$ 的有理近似 $y_j$。
令 $R=B_F+3$，以 $y_j$ 为中心、$R\delta_Q$ 为半径的开有理区间之并记为 $B_n$。
它严格覆盖 $S_n$，且只需有限枚举。

为给有效个数界，对 $1\le h\le N^{1/4}$ 置 $f_h(t)=hN\Psi(t/N)$，
于是 $hc/N\le f_h''\le hC/N$。
取 $\eta=\sqrt{h/N}$，在导数值域内删除各整数的 $\eta$ 邻域。
至多 $hCT+5$ 个邻域或剩余块相关；
删除的整数项及端点项数至多
$(hCT+5)(2\eta N/(hc)+4)$。
剩余各块的导数单调且距整数至少 $\eta$，
分部求和给指数和至多 $8/\eta$：
对 $a_j=e^{2\pi if_h(j)}$、单调的
$\Delta_j=f_h(j+1)-f_h(j)$，使用
$a_j=(a_{j+1}-a_j)/(e^{2\pi i\Delta_j}-1)$，
而分母倒数的虚部 $-\frac12\cot(\pi t)$ 单调，
端点与总变差均为 $O(1/\eta)$。
取

$$
A_*=1000(T+1)(C+1)(1+1/c)
\tag{97.12}
$$

即可在可计算的充分大 $N$ 下得到

$$
\left|\sum_{j\in NK\cap\mathbb Z}e^{2\pi ihN\Psi(j/N)}\right|
\le A_*\sqrt{Nh}.
\tag{97.13}
$$

用 $H=N^{1/4}=\sqrt Q$ 的 Fejér 核。
当 $\|t\|\le1/(2H)$ 时核至少 $4H/\pi^2$。
认证 $Q>(2(B+2))^4$ 后，全部保留相位都在该区间。
核的有限 Fourier 展开与 (97.13) 给

$$
\#\{j\text{ 被保留}\}
\le3TN/H+6A_*\sqrt{NH}
\le C_*Q^{3/2},\qquad C_*=3T+6A_*.
\tag{97.14}
$$

所有阈值均由已给有理常数、缓冲和原 $Q_n$ 计算。
得到一个 $n_{\rm geom}$，使每个 $n\ge n_{\rm geom}$ 的 $B_n$
是至多 $C_*Q_n^{3/2}$ 个、直径 $2RQ_n^{-11/4}$ 的开有理区间之并。
这里有意使用足够的粗估计，无须查询更强几何定理的未知常数。

**承载精确边缘复现的可计算测度。** 按第 95 章枚举正有理 $t_i$；
第 $k$ 轮对 $i\le k$ 依次访问正、负符号，目标带半径为
$\eta_{i,k}=\min(t_i/4,2^{-k})$。
每阶段 $s$ 在该带内取两个严格嵌套有理内带，
再取相位圆上一段有理子弧，长度 $\rho_s>0$，严格位于最内带对应的相位弧。
对数的严格包围可计算这一步；跨零时取较小连通分支。

所需晚层下密度来自原精确相位

$$
\Phi_Q(j)=\log_2(2e^{-z_0}s_j),\qquad
s_j=e^{-Q^3}\frac{(aQ^3)^{k_0+Qj}(bQ^3)^{l_0+Pj}}
 {(k_0+Qj)!(l_0+Pj)!},
\tag{97.15}
$$

其二阶导数为

$$
\Phi_Q''(z)=-
\frac{Q^2\psi_1(k_0+Qz+1)+P^2\psi_1(l_0+Pz+1)}{\ln2}
\asymp-Q^{-1}
\tag{97.16}
$$

于两个固定紧弧上一致。第 88 章的有限相位计数论证
对每个固定正长度子弧给比例趋 $\rho_s$，因而最终至少 $\rho_s/2$。
这在单个原层对指标计数，不是沿 $n$ 对某个固定参数假设随机相位。
原单元中点还满足
$F(j/Q^2)+O_s(\ln Q/Q^3)$，实际完整组桥与内带正裕量最终保证 (97.10)。

对长度 $\ell$ 的固定父区间，其中间四分之一的根原像长度至少 $\ell/(4B_F)$。
所以晚层有至少 $\rho_s\ell Q^2/(16B_F)$ 个合格单元，位于父区间中间部分。
选可计算密度与分离常数

$$
a_s=\min(1/100,\rho_s/(256B_F)),\qquad
0<d\le\min(1,b_F/10).
\tag{97.17}
$$

由 $|F'|\ge b_F$ 及中点误差，相邻合格单元中点最终分离至少
$(b_F/2)Q^{-2}$，可保留有理子区间中心分离 $dQ^{-2}$。
原单元长度精确为
$\beta_{\rm hi}\beta_{\rm lo}\ln2/(\phi Q^3)$。
由固定正参数紧区间计算有理 $\kappa_0>0$，足够小，
使每个相关单元的开放中三分之一能严格容纳长度 $\kappa_0Q^{-3}$ 的有理闭区间。

取有理根区间 $P_0\Subset\operatorname{int}J$，长度 $\ell_0<1$，质量 $M_0=1$。
构造一个独立于任何同步排除选择的有限分支有理树。
所有深度 $s$ 的区间长度相同为 $\ell_s=\kappa_0Q_{n_s}^{-3}$，
每个父区间有恰好

$$
T_s=\lceil a_s\ell_{s-1}Q_{n_s}^2\rceil
\tag{97.18}
$$

个子区间，每个子区间质量为 $M_s=M_{s-1}/T_s$。
公平搜索严格递增的原层 $n_s$、各父区间的有限候选族及证书，
要求每个子区间位于父区间内部及其对应原单元的开放中三分之一，
单元闭包也在父区间内部，具备 (97.10)、规定符号、可行标记及紧弧条件。
全部中心分离大于 $dQ_{n_s}^{-2}$，子区间间隙至少 $2\ell_s$，
并认证有理条件

$$
T_s\ge2,\quad
\ell_s\le\min(2^{-s},\ell_{s-1}/100),\qquad
M_s^5<(a_{s+1}\ell_s)^3.
\tag{97.19}
$$

$a_{s+1}$ 已由固定目标日程计算。
搜索全部有限族而非不可撤回的逐个贪心选择。
每阶段终止：父区间只有有限个，晚层下密度留有至少八倍裕量；
拟合与分离条件最终成立，而 $M_s=O_s(Q^{-2})$、
$(a_{s+1}\ell_s)^{3/5}\asymp_sQ^{-9/5}$，故最后的严格不等式最终成立。
未知渐近起点只证明成功证书存在，算法实际查询的都是有限证书。

令 $K_0$ 为这些逐层闭区间并的交，按每层子区间等分质量定义概率测度 $\nu_0$。
每条分支都有整个精确有符号复现日程，所以 $K_0\subset\mathcal V$。
取有理常数

$$
C_0\ge\max(1,(a_1\ell_0)^{-1}),\qquad
C_\nu=10C_0(1+2/d).
\tag{97.20}
$$

式 (97.19) 的前瞻条件给
$M_s\le\ell_s^{3/5}$ 与
$M_{s-1}\le C_0(a_s\ell_{s-1})^{3/5}$。
对任意长度 $r$ 的实区间 $A$，取 $\ell_s\le r<\ell_{s-1}$。
它至多遇到两个父区间，每个父区间内至多遇到
$1+2rQ_{n_s}^2/d$ 个子区间。
若 $r<Q_{n_s}^{-2}$，直接用 $M_s$ 界；
否则由父质量及 (97.18) 得

$$
\nu_0(A)\le2(1+2/d)M_{s-1}
 \min\{1,r/(a_s\ell_{s-1})\}.
\tag{97.21}
$$

令 $r_0=a_s\ell_{s-1}$，分别在 $r\ge r_0$ 和 $r<r_0$ 用
$r_0^{3/5}\le r^{3/5}$ 或
$r_0^{3/5}(r/r_0)\le r^{3/5}$。
大尺度用总质量一，便得到全尺度可计算界

$$
\nu_0(A)\le C_\nu|A|^{3/5}.
\tag{97.22}
$$

前瞻条件支付任意小的带密度，没有假设最大空隙为 $O(Q^{-2})$。

测度也可有效计算：对一个有理区间，以完全包含的深度 $s$ 柱质量之和为下界，
相交柱之和为上界。仅两个端点处的柱不确定，差至多 $4M_s$。
对 $h$ 个有理区间之并，差至多 $4hM_s$，而 $M_s\le2^{-s}$。
所以有限有理并、交、差的测度一致可计算；(97.22) 保证端点质量为零。
每次查询仅生成有限树层，其终止已经证明。

**未来全部层的有效尾预算。** 由 (97.14)、(97.22)，计算有理 $D_*\ge1$，
足够大使每个 $n\ge n_{\rm geom}$ 都有

$$
\nu_0(B_n)\le D_*Q_n^{3/2-(11/4)(3/5)}
           =D_*Q_n^{-3/20}.
\tag{97.23}
$$

可用有理 $\max(1,2R)$ 上界 $(2R)^{3/5}$。
原层满足 $Q_{n+1}\ge Q_n^4$，认证 $Q_n^{-9/20}\le1/2$ 后，

$$
\sum_{n\ge N}\nu_0(B_n)\le2D_*Q_N^{-3/20}.
\tag{97.24}
$$

通过有理整数幂不等式 $(16D_*)^{20}<Q_{n_0}^3$，
计算 $n_0\ge n_{\rm geom}$，使此全部未来尾和小于 $1/8$。

再按固定顺序枚举全部可计算取整边界
$d_{n,L}=\phi Q_n^3/(L\ln2)$。
以包含第 $i$ 个边界的开有理区间 $D_i$ 覆盖它，
选直径足够小，使 $C_\nu|D_i|^{3/5}<2^{-i-8}$；
用有理五次幂比较及中心的严格包围即可做到。
这些孔有可计算几何尾和。令

$$
U=\bigcup_{n\ge n_0}B_n\ \cup\ \bigcup_{i\ge1}D_i,\qquad
F_0=K_0\setminus U,\qquad
\lambda_0(A)=\nu_0(A\setminus U).
\tag{97.25}
$$

$F_0$ 为非空紧集，$\lambda_0(P_0)>3/4$。
正测度有效闭集本身不保证有可计算点；这里还可计算剩余柱质量：
给定有限有理并 $A$ 和精度，取有限孔并 $U_T$，使两类剩余尾和小于该精度的一部分，
再计算 $\nu_0(A)-\nu_0(A\cap U_T)$。
总误差由有限计算误差与 (97.24) 的已知尾界控制。
不需要孔之间独立、互不相交或跨层相位均匀分布。

基树、$C_\nu$ 和全部覆盖均先于剩余分支选择定义，彼此没有循环依赖。
剩余质量查询可以生成更深的基树，但任何有限请求均终止。

**正剩余质量的分支选择。** 从 $P_0$ 开始，若当前父柱 $P$ 有
$\lambda_0(P)>0$，生成其有限个复现子柱。
对每个子柱公平计算质量包围，找到任一严格正有理下界就选择它。
子柱的剩余质量之和等于父质量，至少一个严格为正，所以该搜索终止。
这里不必判断哪个子柱是按字典序第一个正质量者。

返回前 $m$ 步选择的柱 $P_m$。这些柱嵌套、直径至多 $2^{-m}$，
且每个都与闭集 $F_0$ 相交，所以唯一共同点 $\Beta(J)$ 属于 $F_0$。
它因而避开全部 $n\ge n_0$ 的 $S_n$，由 (97.4)、(97.6) 属于
$\mathcal V\setminus E_2$，控制的是全部晚原层，而非仅选中的复现层。

每个子柱在其原单元内部，故记录的 $n_s,L_s,j_s$、完整组和均值证书
均属于同一个最终参数的原有限历史。
固定有理目标及符号的第 $k$ 轮误差小于 $2^{-k}$；
按给定正实名选择有理近似及足够晚轮数，给第 95 章同样的全实目标对角论证。
一般正实目标只得存在性；给有可计算名时选择才相对可计算。

最终参数也避开每个取整边界。对任一未选中原层，
细化 $\phi Q_n^3/(\Beta(J)\ln2)$ 的包围必能确定非整数的取整；
第 95 章再计算其余有限模型。实际均值的支持一致性来自原置换，
没有新增参数先验或数据实验。证毕。

**注记 97.3（有效性与同步问题的剩余范围）。** 上述有限分支算法
是经典可计算测度与构造性 Borel–Cantelli 方法在原复现单元上的应用。
Galatolo–Hoyrup–Rojas 的定理要求完备可计算度量空间、可计算概率测度、
一致有效开的好集及其补集测度的有效可求和性。
若直接调用它，须把 (97.11) 的覆盖换成仍覆盖 $S_n$ 的稍小闭有理区间，
使好集为开集；不能把开坏集的闭补集冒充有效开集。
本章用稍大开坏集和显式可计算剩余柱质量，直接保留了原单元证书与一个可计算算术起点。
Hoyrup–Rojas 的测度表示定理只提供开集测度的下半可计算性，
不替代这里限制测度所需的有效尾预算。

本章没有构造同步点，没有判定 $E_2$ 非空或为空，也没有给其锐维数或同层指定均值。
它加强了第 95 章所留构造点与 $E_2$ 的关系，但不追认第 95 章算法的那个点
自动具备当前排除性质：这里重新选择了有正剩余质量的分支。
辅助 $\nu_0,\lambda_0$ 仅用于参数空间证明，不是统计参数先验。
原可计算、超越且非正规复现根的结论仍按各自条件适用；
没有将数位结论转移到参数本身，没有效率或新期望熵结论。

## 追加锚（97 章后）

## 98. 紧输出区间上的首个信息方差响应

**定义 98.1（精确先验与输出信息方差）。** 保持定义 96.1 的完整计数后验、
原精确标量 $T$、同一测量 $Y=T+\sigma_MG$、固定幅度及全部原取整。
仍要求

$$
L_M=\ln(1/\sigma_M)\longrightarrow\infty,\qquad
\limsup_M L_M/Q^3<c_q/2.
\tag{98.1}
$$

用自然对数记

$$
S_x(n)=-\ln P_x(n),\qquad h_x=\mathbb E_xS_x(R),\qquad
V_{{\rm prior},x}=\operatorname{Var}_xS_x(R),
$$

$$
J_{x,y}(n)=-\ln P_x(n\mid Y=y),\qquad
V_{{\rm post},x}(y)=\operatorname{Var}_x(J_{x,y}(R)\mid Y=y).
\tag{98.2}
$$

这些都是精确有限纤维量。沿用 (96.2) 的 $\gamma,g_0,g_3,\nu=2g_0$，
置

$$
c_V=\frac{2\gamma}{\nu}\left(\frac2{\sqrt3}-1\right)>0.
\tag{98.3}
$$

**定理 98.2（首个输出相关的信息方差修正）。** 对每个固定 $0\le K<\infty$，

$$
\sup_{|y|\le K}
\left|
\sqrt\delta\left[
V_{{\rm post},x}(y)-V_{{\rm prior},x}
+\frac{\gamma^2}{\delta(\nu+\sigma_M^2)}
\right]-c_Vy
\right|\longrightarrow0.
\tag{98.4}
$$

收敛为原实际数据概率收敛，对所有规定大小的固定真实支持一致；
pair/path 两种原实验分别成立。即对每个固定 $\eta>0$，左侧超过 $\eta$
的概率对上述支持及实验取上确界后趋零。
这里评价的是同一均匀支持先验定义的后验函数，不把固定支持条件输出律
识别为先验混合输出律。

证明。第 96 章的一阶局部矩不足以控制方差。本章先在同一良好数据环境
上建立中心二阶矩和混合残差矩的局部传递，再计算有限 Gaussian 参考。
所有常数可依赖固定模型、$K$ 和 (98.1) 的严格裕量。
沿用第 94、96 章同一量化空间、对数核心 $\mathcal H$、$m=|\mathcal H|$、
外部 $O$、$v_j,e_j,U_j,L_x$，增大固定核心常数使 $V_O\le Q^{-200}$。

**先中心化完整信息量，再换律。** 记校准乘积后验为 $\mathsf Q_x$，
$\mathcal S=-\ln\mathsf Q_x(R)$、$\widetilde h=\mathbb E_{\mathsf Q}\mathcal S$、
$s=\mathcal S-\widetilde h$、$\mathcal V_Q=\mathbb E_{\mathsf Q}s^2$、
$d_h=h_x-\widetilde h$、$a_x=\|L_x-1\|_2\le CQ^{-5/2}$。精确关系为

$$
s_P:=S_x-h_x=s-\ln L_x-d_h,\qquad
\|s\|_{p,\mathsf Q}\le C_pQ,\qquad
|d_h|\le CQa_x+a_x^2.
\tag{98.5}
$$

每个固定阶的矩界来自独立中心 binomial 信息量的偶数矩展开：
单次出现的指标项均为零，一组的每个固定矩由原质量下界控制。
因此 $\mathcal V_Q\le CQ^2$，各部分和也有相应矩界。
在 $0\le t\le C$ 上，$t(\ln t)^2\le C'(t-1)^2$，故

$$
\mathbb E_x(\ln L_x)^2\le Ca_x^2,\qquad
|\mathcal V_P-\mathcal V_Q|\le CQ^2a_x=O(Q^{-1/2}),
\quad \mathcal V_P=V_{{\rm prior},x}.
\tag{98.6}
$$

第二式先以 Cauchy–Schwarz 控制
$\mathbb E_{\mathsf Q}|(L_x-1)(s^2-\mathcal V_Q)|\le CQ^2a_x$，
再展开 (98.5)；$L_x\le C$ 给 $\|s\|_{2,P}\le CQ$，
$\|\ln L_x+d_h\|_{2,P}\le CQa_x$。没有由 TV 推出无界矩。

令正多项式核
$K_{\sigma,b}(z)=(z/\sigma)^b\varphi_\sigma(z)$，$b=0,2,4$。
第 94 章独立核心块平滑及固定阶矩给

$$
\sup_y\mathbb E_{\mathsf Q}[|s|^pK_{\sigma,b}(y-T^{\rm mix})]
\le C_{p,b}Q^p,\qquad
\sup_y\mathbb E_{\mathsf Q}[|W|^pK_{\sigma,b}(y-T^{\rm mix})]
\le C_{p,b},\quad W=\sum_jU_j.
\tag{98.7}
$$

固定残差幂由稍宽 Gaussian 核吸收；乘积权重在此正核测度下用 Hölder。
将 $T^{\rm mix}$ 换回同一个实际 $T$ 时，
在 $|T-T^{\rm mix}|\le h_Q\sigma$、$h_Q=Q^{-100}$ 上，
多项式核平移界成本至多 $CQ^ph_Q$。
补集上以核上确界 $C_b/\sigma$、Hölder 和 (94.12) 的高固定阶矩控制；
(98.1) 的严格裕量允许选足够高但不随 $M$ 增长的阶数，
使全部有限种权重的错误小于任意预定固定幂。
这适用于 $s^2,s^4,W^4$ 及残差四次幂。

点态选中密度界及其平方版本遂给

$$
\sup_y\mathbb E_{\mathsf Q}
[|L_x-1||s|^jK_{\sigma,b}(y-T)]
\le CQ^{j-5/2}\quad(j=0,1,2),
$$

$$
(L_x-1)^2\le C[Q^{-5}(V+W^2)^2+q^{-1}],\qquad
\sup_y\mathbb E_{\mathsf Q}
[L_x(\ln L_x)^2K_{\sigma,b}(y-T)]\le CQ^{-5}.
\tag{98.8}
$$

带权 Cauchy–Schwarz 同时控制 $L_x|s\ln L_x|$ 的局部密度为 $CQ^{-3/2}$。
这里固定总数的依赖已由精确 $L_x$ 支付。

定义实际局部密度

$$
\begin{aligned}
f(y)&=\mathbb E_xK_{\sigma,0}(y-T),&
q_1(y)&=\mathbb E_x[s_PK_{\sigma,0}(y-T)],\\
c(y)&=\mathbb E_x[(s_P^2-\mathcal V_P)K_{\sigma,0}(y-T)],&
u_b(y)&=\mathbb E_xK_{\sigma,b}(y-T)\quad(b=2,4),\\
m_2(y)&=\mathbb E_x[s_PK_{\sigma,2}(y-T)].
\end{aligned}
\tag{98.9}
$$

$m_2/f$ 是同一个残差 $G$ 的条件混合矩。
将 $c$ 换为
$\mathbb E_{\mathsf Q}[(s^2-\mathcal V_Q)\varphi_\sigma(y-T)]$ 的差精确为

$$
\begin{aligned}
&\mathbb E_{\mathsf Q}[(L_x-1)(s^2-\mathcal V_Q)\varphi_\sigma]\\
&\quad+\mathbb E_{\mathsf Q}L_x
\left[-2s(\ln L_x+d_h)+(\ln L_x+d_h)^2
-(\mathcal V_P-\mathcal V_Q)\right]\varphi_\sigma .
\end{aligned}
\tag{98.10}
$$

所有核自变量为 $y-T$。(98.5)–(98.8) 逐项给 $CQ^{-1/2}$：
中心二阶权重成本为 $Q^2$，$d_hs$ 也至多 $CQ^2a_x$，
常数方差差乘有界密度。相应的一阶及混合一阶密度成本为 $CQ^{-3/2}$，
质量及纯残差密度成本为 $CQ^{-5/2}$。随后平移到 $T^{\rm mix}$
的成本被 $Q^2h_Q$ 吸收。

**平方权重下移除相关外部能量。** 令
$S_H=\frac12\sum_{\mathcal H}(Z_j^2-1)$，
$p_H(s,t)$ 为 $(S_H,T_H^{\rm G})$ 的联合密度，保留原非中心项及截距。
第 94 章固定 128 坐标正则化可加强为

$$
\sup_t\int |s|^k|\partial_tp_H(s,t)|\,ds
\le C\delta^{-1/2}(1+m^{k/2})\qquad(k=0,1,2).
\tag{98.11}
$$

补充平方权重的证明如下。正则块满足
$\Pr(\det\Gamma\le t)\le Ct^{16}$；
其 Gaussian 散度是多项式分子除以 $\det\Gamma$ 或其平方。
Hölder 与小于 16 阶的充分高逆矩给
$\mathbb E[(1+F_1^2)|D_u|]\le C$，
局部化分部积分给正则块的 $1+s^2$ 加权导数积分界。
与其余独立核心卷积时，将剩余中心信息量分成独立大块，
平方及交叉项各用一个未承载权重的块平滑；
普通二阶矩为 $O(m)$，且 $(s_A+s_B)^2\le2s_A^2+2s_B^2$。
结合 (94.19)–(94.22) 的尺度变换与连续密度版本，得到 (98.11)。

同一量化耦合上的近似中心信息量写成 $B_s=S_H+O_s$，
其中 $O_s$ 含外部 Gaussian 化与未 Gaussian 化的信息量，
$\mathbb E O_s=0$、$\|O_s\|_p\le C_pQ$。
它独立于核心，但尚未独立于外部能量 $E_O$。
原信息量耦合的普通及局部加权 $L^2$ 误差为 $CQ^{-98}$，
故

$$
\sup_y\mathbb E_{\mathsf Q}
[|s^2-B_s^2|K_{\sigma,b}(y-T^{\rm mix})]\le CQ^{-97},\qquad
|\mathcal V_Q-\mathcal V_B|\le CQ^{-97},
$$

$$
\mathcal V_B=m/2+\mathbb EO_s^2.
\tag{98.12}
$$

这是 $|s^2-B_s^2|\le|s-B_s||s+B_s|$ 的带权 Cauchy–Schwarz 应用。
条件于所有外部变量及同一个 $G$，由 (98.11) 平移能量坐标的成本至多

$$
C\delta^{-1/2}\mathbb E
\left[|E_O|\{1+m+(1+\sqrt m)|O_s|+O_s^2+\mathcal V_B\}\right]
\le CQ^2\delta^{-1}
[(1+a_x)V_O+B^{-1}\sqrt{V_O}]
=o(Q^{-90}).
\tag{98.13}
$$

其中 $O_s^2$ 项使用 $\|E_O\|_2\|O_s\|_4^2$，没有假设二者独立。
残差 $G^b$ 仅收取其固定矩，因为它独立于外部变量。
只有支付这次联合平移后，才有精确消去

$$
\mathbb E[(B_s^2-\mathcal V_B)\varphi_\sigma(y-T_H^{\rm G})]
=\mathbb E[(S_H^2-m/2)\varphi_\sigma(y-T_H^{\rm G})].
\tag{98.14}
$$

外部的大方差在此相消；一阶及混合一阶量中的 $O_s$ 同样因均值零消去。
于是实际六种密度与非中心核心版本的误差阶分别为
$Q^{-5/2}$、$Q^{-3/2}$、$Q^{-1/2}$。

**局部支付精确非中心项。** 为计算系数，进一步定义中心参考

$$
w_j=v_j/\sqrt\delta,\quad c_j=e_j/\sqrt{v_j},\quad
T_0=\sum_{\mathcal H}w_j(Z_j^2-1),\quad Y_0=T_0+\sigma G,
$$

$$
T_H^{\rm G}=T_0+D,\qquad
D=-2\sum_{\mathcal H}w_jc_jZ_j+\mu_G,\qquad
\mu_G=\delta^{-1/2}\|e\|^2.
\tag{98.15}
$$

截距包含外部的 $e_j^2$。由 (96.13)–(96.15)，每个固定 $p$ 均有
$\|D-\mu_G\|_p\le C_pa_x$，故
$d_e:=a_x+\delta^{-1/2}a_x^2=O(Q^{-5/2})$。
不需要每个远端 $c_j$ 都小。

将核心分成两个大半块，每半块再交错分成至少三个大子块。
由 (96.16) 的 Fourier 包络，每个未承载权重的子块都提供
任意所需固定阶的有界密度导数。部分保留线性非中心系数时，
配方后的特征函数模只会减小，界仍相同。
展开 $S_H^k=(S_A+S_B)^k$、$k\le2$；
$B$ 半块每个至多二次的权重项只占其三个子块中的至多两个，
导数交给余下独立子块。因此其加权密度一阶导数至多
$C(1+m^{(k-j)/2})$。
条件于 $A,G$，先移除 $D_A$，成本至多

$$
C(1+m^{(k-j)/2})\mathbb E[|D_A||S_A|^j]
\le C(1+m^{k/2})d_e.
\tag{98.16}
$$

再移除另一半。卷积同一个 $\sigma G$ 不增导数范数；
带上 $G^b$ 只乘 $\mathbb E|G|^b$。
中心二阶量还需减去 $m/2$ 倍质量密度，成本至多 $Cmd_e$。
由于 $m=O(\sqrt{Q\ln Q})<CQ$，这些均落在此前误差阶以内。

以 $g,q_0,c_0,u_{b,0},m_{2,0}$ 表示中心参考的对应密度，其中
$q_0=\mathbb E[S_H\varphi_\sigma(y-T_0)]$、
$c_0=\mathbb E[(S_H^2-m/2)\varphi_\sigma(y-T_0)]$。综上，

$$
\begin{aligned}
\|f-g\|_\infty+\sum_{b=2,4}\|u_b-u_{b,0}\|_\infty&\le CQ^{-5/2},\\
\|q_1-q_0\|_\infty+\|m_2-m_{2,0}\|_\infty&\le CQ^{-3/2},\\
\|c-c_0\|_\infty&\le CQ^{-1/2}.
\end{aligned}
\tag{98.17}
$$

$c$ 始终减去原精确完整先验方差；$c_0$ 中的 $m/2$
来自 (98.14) 的正确消去。实际观察量从未被重新定义。

**精确 Gaussian 方差倾斜与消去。** 记

$$
A_0=\sum_{\mathcal H}w_j=\frac{V_H}{\sqrt\delta},\qquad
\nu_0=2\sum_{\mathcal H}w_j^2,\qquad
\kappa_3=8\sum_{\mathcal H}w_j^3,\qquad
\Lambda=\nu_0+\sigma^2.
\tag{98.18}
$$

用 $\exp(\theta S_H)$ 倾斜并归一化有限 Gaussian 向量，$|\theta|<1$；
倾斜后向量精确为 $Z/\sqrt{1-\theta}$，其能量为

$$
T_\theta=\frac{T_0+A_0}{1-\theta}-A_0.
$$

归一化密度在零处的一、二阶导数分别为 $S_H$、$S_H^2-m/2$。
在固定正 $\sigma$ 下对有限 Gaussian 积分求导，给

$$
q_0=-\mathbb E[(T_0+A_0)\varphi_\sigma'(y-T_0)],\qquad
c_0=\mathbb E[(T_0+A_0)^2\varphi_\sigma''(y-T_0)
-2(T_0+A_0)\varphi_\sigma'(y-T_0)].
\tag{98.19}
$$

局部 $\theta$ 上有可积的多项式乘 Gaussian 指数包络，故求导合法。
有限 Gaussian 测量恒等式为

$$
\mathbb E[(T_0+A_0)\varphi_\sigma(y-T_0)]
=(y+A_0)g+\sigma^2g',
$$

$$
\mathbb E[(T_0+A_0)^2\varphi_\sigma(y-T_0)]
=(y+A_0)^2g+2\sigma^2(y+A_0)g'+\sigma^2g+\sigma^4g''.
\tag{98.20}
$$

按 (98.19) 求导后，

$$
\begin{aligned}
q_0&=-(y+A_0)g'-g-\sigma^2g'',\\
c_0&=(y+A_0)^2g''+2(y+A_0)g'
+2\sigma^2(y+A_0)g'''+3\sigma^2g''+\sigma^4g''''.
\end{aligned}
\tag{98.21}
$$

置 $R_j=g^{(j)}/g$、$\ell_g=\ln g$、$B_y=yR_1+1+\sigma^2R_2$。
直接保留条件均值平方的消去，得到

$$
\frac{c_0}{g}-\left(\frac{q_0}{g}\right)^2
=A_0^2\ell_g''
+2A_0\{y\ell_g''+\sigma^2R_2'\}+\mathcal R(y),
$$

$$
\mathcal R(y)=y^2R_2+2yR_1+2\sigma^2yR_3
+3\sigma^2R_2+\sigma^4R_4-B_y^2.
\tag{98.22}
$$

左侧是 $\operatorname{Var}(S_H\mid Y_0=y)-m/2$。
下文将给紧区间上四个导数比值的一致界，故 $\mathcal R=O_K(1)$。
此处的核心是 $R_2-R_1^2=\ell_g''$；
分别只求二阶矩和均值平方的相对 $o(1)$ 近似，会丢失目标修正。

同一个噪声残差还精确满足

$$
u_{2,0}=g+\sigma^2g'',\qquad
u_{4,0}=3g+6\sigma^2g''+\sigma^4g'''',\qquad
m_{2,0}=q_0+\sigma^2q_0'',
$$

$$
\operatorname{Cov}(S_H,G^2\mid Y_0=y)
=\sigma^2\left(\frac{q_0''}{g}-\frac{q_0g''}{g^2}\right).
\tag{98.23}
$$

这些是核恒等式，不假设条件于输出后 $G$ 仍独立。

**带精确噪声的导数级 Edgeworth 界。** 由 (96.13)，
$\max w_j=O(\sqrt\delta)$、$\sum w_j^2=O(1)$、
$\sum w_j^4\le(\max w_j^2)\sum w_j^2=O(\delta)$。
展开有限乘积特征函数，

$$
\log\mathbb Ee^{itT_0}
=\sum_j[-itw_j-\tfrac12\log(1-2itw_j)]
=-\nu_0t^2/2+\kappa_3(it)^3/6+O(\delta|t|^4)
\tag{98.24}
$$

当 $\max_j|w_jt|$ 足够小时成立。乘
$e^{-\sigma^2t^2/2}$ 后，主项方差精确为 $\Lambda$。
在 $|t|\le\delta^{-1/12}$，指数展开余项至多
$C\delta(|t|^4+|t|^6)e^{-ct^2}$。
此区间外，原独立块包络
$(1+c_1\delta t^2)^{-c_2/\delta}$ 乘任意固定 $|t|$ 幂的积分
超多项式小：直到 $\delta^{-1/2}$ 有 Gaussian 界，
再外侧在变量 $u=\sqrt\delta t$ 下有指数于 $1/\delta$ 的尾界。
Gaussian 三次近似也满足相同结论。因此对每个固定导数阶 $j$，
特别是 $j=0,\ldots,4$，Fourier 反演给

$$
\left\|g^{(j)}
-\left(p_\Lambda-\frac{\kappa_3}{6}p_\Lambda'''\right)^{(j)}
\right\|_\infty\le C_j\delta,\qquad
p_\Lambda(y)=\frac{e^{-y^2/(2\Lambda)}}{\sqrt{2\pi\Lambda}}.
\tag{98.25}
$$

常数对 $0<\sigma\le1$ 一致。正则性由 Gaussian 参考核心提供，
没有对弱 CLT 求导，也没有收取逆噪声。

固定紧区间上 $p_\Lambda$ 有确定正下界，且
$-p_\Lambda'''/p_\Lambda=y^3/\Lambda^3-3y/\Lambda^2$。
用 $\kappa_3=O(\sqrt\delta)$、$\kappa_3^2=O(\delta)$ 对商及对数求导，得到

$$
\ell_g''=-\frac1\Lambda+\frac{\kappa_3y}{\Lambda^3}+O_K(\delta),
\qquad
R_2'=\frac{2y}{\Lambda^2}+O_K(\sqrt\delta).
\tag{98.26}
$$

四个导数比值均有界。曲率误差 $O(\delta)$ 乘
$A_0^2=O(\delta^{-1})$ 仍仅为 $O(1)$。
代入 (98.22)，将 $A_0\kappa_3=O(1)$ 项包含于有界余项，得

$$
\operatorname{Var}(S_H\mid Y_0=y)-m/2
=-\frac{A_0^2}{\Lambda}
+\left(\frac{A_0^2\kappa_3}{\Lambda^3}
-\frac{2A_0}{\Lambda}
+\frac{4A_0\sigma^2}{\Lambda^2}\right)y+O_K(1).
\tag{98.27}
$$

由 (98.21)，$q_0=-A_0g'+b_0$，$b_0$ 及其前两阶导数
在紧区间上有界。因此 (98.23) 给

$$
\operatorname{Cov}(S_H,G^2\mid Y_0=y)
=-A_0\sigma^2R_2'+O_K(\sigma^2)
=-\frac{2A_0\sigma^2y}{\Lambda^2}+O_K(1).
\tag{98.28}
$$

残差条件方差由 (98.23) 有界。参考后验信息量在固定输出处
相差一个输出函数后等于 $S_H+G^2/2$，故

$$
\operatorname{Var}(S_H+G^2/2\mid Y_0=y)-m/2
=-\frac{A_0^2}{\Lambda}
+\left(\frac{A_0^2\kappa_3}{\Lambda^3}
-\frac{2A_0\nu_0}{\Lambda^2}\right)y+O_K(1).
\tag{98.29}
$$

它是有界余项的有限系数界，并未识别常数阶极限。

**归一化误差与实际方差回接。** 由 (98.17)、(98.25)，紧区间上
$f,g$ 同有确定正下界，且
$|q_0|+|m_{2,0}|\le C_K(1+A_0)$、
$|c_0|\le C_K(1+A_0^2)$，$u_{2,0},u_{4,0}$ 有界。
精确地，

$$
\operatorname{Var}_x(S_x\mid y)-\mathcal V_P
=\frac{c(y)}{f(y)}-\left(\frac{q_1(y)}{f(y)}\right)^2.
\tag{98.30}
$$

其第一项与 $c_0/g$ 的差至多
$C_K[Q^{-1/2}+(1+A_0^2)Q^{-5/2}]$；
第二项与 $(q_0/g)^2$ 的差至多

$$
C_K(1+A_0)[Q^{-3/2}+(1+A_0)Q^{-5/2}]
+C_K[Q^{-3/2}+(1+A_0)Q^{-5/2}]^2.
\tag{98.31}
$$

$A_0=O(Q^{1/4})$ 使两者均为 $O_K(Q^{-1/2})$。
这逐项支付了大二阶矩及均值平方放大的密度误差。
Bayes 的精确关系为

$$
J_{x,y}(R)=S_x(R)+G^2/2+\tfrac12\ln(2\pi)-L_M+\ln f(y),
$$

$$
V_{{\rm post},x}(y)
=\operatorname{Var}_x(S_x\mid y)
+\operatorname{Cov}_x(s_P,G^2\mid y)
+\tfrac14\operatorname{Var}_x(G^2\mid y).
\tag{98.32}
$$

后两项分别等于
$m_2/f-q_1u_2/f^2$ 和 $\frac14[u_4/f-(u_2/f)^2]$；
与参考量的差由 (98.17) 至多为
$C_K[Q^{-3/2}+(1+A_0)Q^{-5/2}]$ 及 $C_KQ^{-5/2}$。
结合 (98.29)–(98.32)，得到原精确后验的有限系数展开

$$
V_{{\rm post},x}(y)-V_{{\rm prior},x}
=-\frac{A_0^2}{\Lambda}
+\left(\frac{A_0^2\kappa_3}{\Lambda^3}
-\frac{2A_0\nu_0}{\Lambda^2}\right)y+O_{\mathbb P}(1),
\tag{98.33}
$$

余项在每个固定紧区间上一致有界于数据概率。

最后由原实际占据及 Stirling 推出的 (96.13)，
$V_H=\gamma+O_{\mathbb P}(\delta)$、
$\nu_0=\nu+O_{\mathbb P}(\delta)$、
$G_{3,H}:=\delta^{-2}\sum_{\mathcal H}v_j^3\to g_3$。
两个分母均保留同一个实际 $\sigma^2$，故

$$
\sqrt\delta\left|
\frac{A_0^2}{\nu_0+\sigma^2}
-\frac{\gamma^2}{\delta(\nu+\sigma^2)}
\right|
\le C\delta^{-1/2}(|V_H-\gamma|+|\nu_0-\nu|)
=O_{\mathbb P}(\sqrt\delta)\longrightarrow0.
\tag{98.34}
$$

因 $\kappa_3=8\sqrt\delta G_{3,H}$，输出系数满足

$$
\sqrt\delta\left(
\frac{A_0^2\kappa_3}{\Lambda^3}
-\frac{2A_0\nu_0}{\Lambda^2}\right)
=\frac{8V_H^2G_{3,H}}{(\nu_0+\sigma^2)^3}
-\frac{2V_H\nu_0}{(\nu_0+\sigma^2)^2}
\longrightarrow\frac{8\gamma^2g_3}{\nu^3}-\frac{2\gamma}{\nu}
=c_V.
\tag{98.35}
$$

末式使用 Gaussian 轮廓的精确积分
$\gamma g_3/g_0^2=2/\sqrt3$、$\nu=2g_0$。
将 (98.33) 的有界余项乘 $\sqrt\delta$，即得 (98.4)。
所有估计先在同一确定良好环境上证明；占据、校准和尾部事件的
失败概率对真实支持一致趋零，故恢复所述量词。
不在坏数据事件上对无界实际矩作概率乘积估计。
有限正混合使全部条件矩函数连续，紧区间上确界可由可数稠密集取得，
因而可测。证毕。

**注记 98.3（精确噪声、单位与范围）。** 在放大的主损失中
将 $\nu+\sigma_M^2$ 换成 $\nu$，会改变 (98.4) 的中心量

$$
\frac{\gamma^2\sigma_M^2}
{\sqrt\delta\,\nu(\nu+\sigma_M^2)}.
\tag{98.36}
$$

合法序列 $\sigma_M=Q^{-1/16}$ 使它按正倍数 $Q^{1/8}$ 发散，
即使 $y=0$ 也如此。因此完整噪声区间不能删去有限噪声方差，
也未偷偷添加 $\sigma_M^2=o(\sqrt\delta)$。
若信息量改用 bit，两个方差及所有修正系数均除以 $(\ln2)^2$，
与熵均值的单位换算不同。

定理保持原精确先验方差，没有用其 $Q^2$ 主项替换。
它不识别 (98.33) 的常数阶极限，不声称全实线或增长紧区间的一致性、
零噪声、半指数端点、阈值锐性、全数据期望方差、一般条件化方差单调性
或新的覆盖定理。若只在实际输出 $|Y|\le K$ 处评价误差，
该坏事件包含于定理的坏数据事件；这不需要将已知支持条件律换成先验混合律。
未知方向仍用原共同一致事件及同一个测量噪声，不加入方向先验。
两个原实验分别满足论证，不由此主张实验等价。

Gaussian 指数族求导、核恒等式及 Edgeworth 方法均为经典工具。
本章连接的是实际固定总数后验的局部中心二阶矩传递、
带平方权重的相关外部能量移除、精确非中心项支付，
以及完整严格噪声区间上的显式 $Q^{1/4}$ 输出响应。

## 追加锚（98 章后）

## 99. 双根同步的联合算术障碍与实际均值分离

**定义 99.1（共同层的根与均值）。** 沿用第 81、85、93、97 章的原幅度、
原合法序列、原 $M,q$ 取整、完整得分组及两种实际实验。固定
$\beta\in D=(\beta_*,1)$，写

$$
N=Q^2,\quad u=x_+(\beta)>0>v=x_-(\beta),\quad
I(u)=I(v)=c(\beta),\quad A=I'(u)>0,\quad B=-I'(v)>0.
\tag{99.1}
$$

$\mu_+=\mu^{\mathcal E}_{Q,j}(\beta)$、$\mu_-=\mu^{\mathcal E}_{Q,k}(\beta)$
指同一参数、原层和实验下两侧完整得分组的实际占用均值，不是后验中心。
$E_2$ 等价于：存在一个有限 $H$，无限多个原层上两侧均有均值落在
$[e^{-H},e^H]$。紧性抽取共同子序列即给两个正有限极限。
原相对均值比较使 pair/path 的集合及正有限极限对相同，不把有限数据律等同。

本章只给新的同步排除条件；$E_2$ 非空与否仍未解决。
常数可依赖固定参数、内部根邻域和所指定的固定代数对象。

**引理 99.2（共同整数关系）。** 有 $B>A$。对固定整数 $h,l$，
不同时为零，置

$$
T=hu+lv,\qquad D_{h,l}=h/A-l/B,\qquad J=hj+lk\in\mathbb Z.
\tag{99.2}
$$

在共同有界正均值带上，

$$
\begin{aligned}
J-NT={}&-\frac{3D_{h,l}\ln Q}{Q}\\
&+\frac1Q\left[
\frac hA\{C_Q(u;\beta)-\ln\mu_+\}
-\frac lB\{C_Q(v;\beta)-\ln\mu_-\}\right]+o(Q^{-1}).
\end{aligned}
\tag{99.3}
$$

$C_Q$ 保留两个原取整相位且一致有界。
两均值同处任一固定多项式带 $[Q^{-K},Q^K]$ 时，仍有
$\|NT\|=O_K(\ln Q/Q)$。

证明。原实际均值展开为

$$
\ln\mu^{\mathcal E}_{Q,j}(\beta)
=Q^3\{c(\beta)-I(j/N)\}-3\ln Q+C_Q(j/N;\beta)+o(1).
\tag{99.4}
$$

具体地，令 $\Delta_Q=\lfloor aQ^3\rfloor-aQ^3$、
$\rho_Q=\{\phi Q^3/(\beta\ln2)\}$、$\eta=\ln((1+r)/(1-r))$，则

$$
\begin{aligned}
A_Q(x)={}&-\ln(2\pi)-\tfrac12\ln[(a+x)(b+\vartheta x)]\\
&+\Delta_Q\left[\ln\frac{b+\vartheta x}{b}-\ln\frac{a+x}{a}\right],\\
C_Q(x;\beta)={}&(1-\rho_Q)\ln2-\Delta_Q\eta+A_Q(x).
\end{aligned}
\tag{99.5}
$$

内部紧集上这些函数及所需导数一致有界；原 $P/Q-\vartheta$ 误差小于
这里任一保留阶。多项式均值带和简单根定位给
$d_+=j-Nu,\ d_-=k-Nv=O_K(\ln Q/Q)$，因此

$$
\begin{aligned}
\ln\mu_+&=-QA\,d_+-3\ln Q+C_Q(u;\beta)+o(1),\\
\ln\mu_-&= QB\,d_--3\ln Q+C_Q(v;\beta)+o(1).
\end{aligned}
\tag{99.6}
$$

Taylor 余项为 $O((d_+^2+d_-^2)/Q)=o(1)$。解出两个位移并取线性组合，
得到 (99.3)。共同 $N$ 和整数 $J$ 不能由两个无关的边缘子序列替代。

再核对严格斜率。$I''>0,I'''<0$；令
$H(x)=I'(x)^2-2I(x)I''(x)$，有 $H(0)=0$、
$H'=-2II'''>0$（$x\ne0$）。等率两点满足

$$
\frac{I''(u)}{I'(u)^2}<\frac1{2I(u)}
<\frac{I''(v)}{I'(v)^2}.
$$

反根映射 $v=\psi(u)$ 经隐函数微分得 $\psi''>0$；
零点延拓 $\psi'(0)=-1$，故 $-1<\psi'=-A/B<0$，即 $B>A$。证毕。

**定理 99.3（联合根组合的排除）。** 若 $\beta\in E_2$，则：

1. 任意固定非零有理线性组合 $hu+lv$ 不得为代数无理数。
2. 对整系数 $h,l$，若 $T=hu+lv\in\mathbb Q$，必有
   $T\in\mathbb Z[1/10]$ 且 $D_{h,l}=0$。
3. 对整系数 $h,l$，若 $T=F(\vartheta)$，$F\in\mathbb Q(X)$
   在 $\vartheta$ 有限，必有 $D_{h,l}=0$，且 (99.8) 的预测量
   在同一复现子序列上最终为整数。

特别地，令 $\overline{\mathbb Q}$ 在此表示实代数数，则

$$
\beta\in E_2\ \Longrightarrow\
u+v,\ u-v\notin\overline{\mathbb Q}\cup\mathbb Q(\vartheta).
\tag{99.7}
$$

若 $\psi'(u)$ 无理，每个非零有理线性组合都在这两个类之外。
有理切线斜率处保留至多一个未排除的有理方向，不判定该方向是否可达。

证明。第 93 章从 Adamczewski–Bugeaud 原文 Theorem E 推出：
固定代数无理数 $\xi$ 满足
$\|Q_n^2\xi\|\ge c_{\xi,\epsilon}Q_n^{-\epsilon}$，
$0<\epsilon<1$。将 $J/N$ 约分后分母仍只含素因子 $2,5$，
所以该成熟子空间定理适用于固定 $\xi=hu+lv$，与 (99.3) 矛盾。
有理系数先清固定公分母；同一论证也排除共同固定多项式均值带。

若 $T=p/q$ 既约，其 $\|NT\|$ 为零或至少 $1/q$。
晚层复现迫使 $NT$ 为整数，故 $q$ 只含素因子 $2,5$；
此时 $q$ 最终整除 $N$，且 (99.3) 迫使 $J=NT$。
乘 $Q$ 再除以 $\ln Q$ 得 $D_{h,l}=0$。
有限小数结论针对整系数组合，未省略有理系数清分母的影响。

对第三项，置 $R=Q_{n-1}$、$t=P_{n-1}/R$，原递推给
$\vartheta=t+Q^{-1}+O(10^{-Q^5})$。定义

$$
Z_n^F=Q^2F(t)+QF'(t)+\tfrac12F''(t),\qquad
\kappa_F=F'''(\vartheta)/6.
\tag{99.8}
$$

第 85 章的有理函数预测用于这个共同标量，给

$$
NT=Z_n^F+\kappa_F/Q+O_F(Q^{-2}),\qquad
\operatorname{den}(Z_n^F)\le C_FR^{3m}.
\tag{99.9}
$$

$m$ 是清分母后分子、分母次数与 $1$ 的最大值。
写 $F=A_0/B_0$ 为整系数多项式之比，前三个导数项在 $t=P/R$
可用固定有理倍数的 $(R^mB_0(t))^3$ 作公共分母，大小为 $O_F(R^{3m})$。
此分母可能含 $2,5$ 之外的素因子，并未假定它整除 $Q$。
三阶 Taylor 及有界四阶导数给第一式。

因 $R^{3m}\ln Q/Q\to0$，非整数 $Z_n^F$ 到整数的距离大于
(99.3)、(99.9) 允许的误差。晚层复现必须满足
$Z_n^F\in\mathbb Z$、$J=Z_n^F$。
于是 $Q(J-NT)=-\kappa_F+o(1)$ 有界，迫使 $D_{h,l}=0$。
最后 $D_{1,1}=1/A-1/B>0$、$D_{1,-1}=1/A+1/B>0$，得到 (99.7)。
非零整数对满足 $D_{h,l}=0$ 时同号且 $h/l=A/B=-\psi'(u)$，
无理斜率不允许这种关系。固定对象的论证不排除随层变动的切线分母。证毕。

**定理 99.4（实际均值的对数分离）。** 若固定 $\beta\in D$ 满足
$u+v\in\mathbb Q(\vartheta)$，令 $c_\beta=3(B-A)/(B+A)\in(0,3)$。
对两根固定充分小邻域内任意原索引 $j,k$，充分晚层有

$$
\max\{|\ln\mu^{\mathcal E}_{Q,j}|,|\ln\mu^{\mathcal E}_{Q,k}|\}
\ge c_\beta\ln Q-C_\beta
\tag{99.10}
$$

且 $C_\beta<\infty$。零均值的对数绝对值视为无穷。
两种实际实验分别成立。若根和为代数无理数，则任意固定
$[Q^{-K},Q^K]$ 的共同均值带最终为空。

证明。记左侧为 $H_Q$。$H_Q>4\ln Q$ 时直接成立；
否则 (99.6) 适用。根和的非整数预测量与该多项式带矛盾；
整数情形 $j+k=Z_n^F$，所以 $Q(d_++d_-)=-\kappa_F+o(1)$。
将 (99.6) 分别除以 $A,B$ 后相减：

$$
\frac{\ln\mu_+}{A}-\frac{\ln\mu_-}{B}
=\kappa_F-3(1/A-1/B)\ln Q
+\frac{C_Q(u;\beta)}A-\frac{C_Q(v;\beta)}B+o(1).
\tag{99.11}
$$

左侧绝对值至多 $(1/A+1/B)H_Q$，非对数项有界，即得结论。
没有证明该下界常数可达。代数无理根和直接用定理 99.3 的多项式带反证。证毕。

**推论 99.5（有限小数根和的同层反射律）。** 若
$u+v=\rho\in\mathbb Z[1/10]$，且某原子序列上正根索引 $j$
的实际均值趋于正有限值，令 $k=N\rho-j$、$\Lambda=B/A>1$，则

$$
\ln\mu^{\mathcal E}_{Q,k}
=\Lambda\ln\mu^{\mathcal E}_{Q,j}+3(\Lambda-1)\ln Q
+C_Q(v;\beta)-\Lambda C_Q(u;\beta)+o(1).
\tag{99.12}
$$

负根反射均值因此为 $Q^{3(\Lambda-1)}$ 的正固定倍数量级并趋于无穷。
反向若负根反射均值正有限，正根均值为
$Q^{-3(1-1/\Lambda)}$ 的正固定倍数量级并趋于零。

证明。$N\rho$ 最终为整数，$d_-=-d_+=O(\ln Q/Q)$，
反射索引在同一原可行内部根弧和完整得分窗口内。
代入 (99.6) 得式。取整相位有界但不必收敛，不给固定乘法系数极限。
这里以实际边缘复现为条件，没有在下述参数处先行构造这种复现。证毕。

**命题 99.6（由根和指定的可计算稠密排除族）。** 每个正长度有理紧区间
$J\subset D$ 的内部都含一个可计算固定参数 $\beta_\rho\notin E_2$，
其根和为有限小数；也可使根和为 $\mathbb Q(\vartheta)$ 中
一个非多项式有理函数的超越值。

证明。$S(u)=u+\psi(u)$ 满足 $S'>0$，连续端点值为
$0$ 与 $u_*+u_->0$，其中 $I(u_*)=I(u_-)$。
故 $S$ 双射到 $(0,u_*+u_-)$。给定该区间内有限小数 $\rho$，
唯一根 $S(u_\rho)=\rho$ 定义

$$
\beta_\rho=\frac{\phi}{\phi+I(u_\rho)}.
\tag{99.13}
$$

有限小数稠密且定理 99.3 排除它们。
数位尾界计算 $\vartheta$，单调幅度方程有理夹逼计算 $r$；
内部弧的单调夹逼计算 $\psi,S$。从 $J$ 的像中选有严格余量的有限小数，
再夹逼唯一根，算法终止。未用浮点根读数，也未声称复杂度界。

在同一像中选有理 $\rho$ 和足够小的正有理 $\epsilon$，
使 $t=\rho+\epsilon/(1000+\vartheta)$ 严格落入其中。
若 $t$ 代数，$\vartheta=\epsilon/(t-\rho)-1000$ 也代数，矛盾。
用 $S(u)=t$ 定义参数，再由定理 99.3 排除。
未判定其单个根是否属于该有理函数域，也未声称与全部旧排除类分离。
稠密排除族不能证明 $E_2$ 为空。证毕。

**命题 99.7（原分母集合的密度障碍）。** 令
$\mathcal A=\{N_n=10^{2e_n}\}$。不存在 $\delta>0,C<\infty$，
使每个充分大 $q$ 和每个与之互素的 $p$ 都满足

$$
\min_{\substack{w\in\mathcal A\\w\le q}}\|wp/q\|\le Cq^{-\delta}.
\tag{99.14}
$$

证明。取 $q_n=N_{n+1}-3$、$p_n=(q_n-1)/3$。
$N_i\equiv1\pmod3$，所以 $p_n$ 为整数；
$q_n=3p_n+1$ 给互素性。晚层 $N_n<q_n<N_{n+1}$ 且
$q_n\ge4N_n$。任意 $w=N_i\le q_n$ 写为 $3m+1$，有

$$
\frac{wp_n}{q_n}=m+\frac13-\frac{w}{3q_n}.
$$

小数部分在 $[1/4,1/3)$，故左侧至少 $1/4$，右侧趋零，矛盾。
测试分数只检验一个全称密度定义，没有替换原分母或构造固定参数。证毕。

此密度为 Sanford 受限分母文章中的假设之一，命题仅排除该路线。
自由平面乘积逼近、线性同标量逼近、有限相邻指数比的均匀逼近、
素数分母直线上的几乎处处结论，均未给出原反根曲线的共同薄带命中。
来源条件见 [Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。
仍缺一个固定 $\beta$、一个有限带宽和无限个共同原层；没有同步点、
同步集合下维数、类别判定或指定联合均值的结论。

## 追加锚（第 99 章后续增补区）

## 100. 精确有限系数扣除后的常数阶信息方差剖面

**定义 100.1（有限系数与同一残差）。** 保持定义 98.1 的完整计数先验后验、
原精确标量 $T$、同一观测 $Y=T+\sigma_MG$ 及全部原取整，并仍要求

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q/2.
\tag{100.1}
$$

信息量用自然对数，方差为 nats 的平方。沿用第 96、98 章的
$v_j,\delta=Q^{-1/2},\rho,\gamma,g_0,g_3,\nu=2g_0$，另置
$g_4=\int_{\mathbb R}\rho(t)^4\,dt$。
取一个满足原共同截断要求的固定整数 $C_0\ge2$，定义

$$
c_*=\frac1{64(C_0+1)},\quad D_*=1+\frac{2000}{c_*},\quad
\mathcal H=\{j\in K_M:|j\delta|\le\sqrt{D_*\ln Q}\}.
\tag{100.2}
$$

这只是证明核心，不改变原窗口或完整计数向量。对实际观测数据定义有限和

$$
\begin{gathered}
w_j=v_j/\sqrt\delta,\qquad A=\sum_{\mathcal H}w_j,\qquad
\nu_0=2\sum_{\mathcal H}w_j^2,\\
\kappa_3=8\sum_{\mathcal H}w_j^3,\quad
\kappa_4=48\sum_{\mathcal H}w_j^4,\quad
s=\sigma_M^2,\quad\Lambda=\nu_0+s,\\
C_x=\frac{A^2\kappa_3}{\Lambda^3}-\frac{2A\nu_0}{\Lambda^2}.
\end{gathered}
\tag{100.3}
$$

这里保留观测到的有限系数及有限噪声，不以极限常数替代发散的扣除项。

**定理 100.2（常数阶剖面）。** 令

$$
R(y)=\frac{29}{6}-3\sqrt2+
\left(3\sqrt2+\frac8{\sqrt3}-9\right)\frac{y^2}{\nu}.
\tag{100.4}
$$

则对每个固定 $0\le K<\infty$，

$$
\sup_{|y|\le K}\left|
V_{{\rm post},x}(y)-V_{{\rm prior},x}
+\frac{A^2}{\Lambda}-C_xy-R(y)\right|\longrightarrow0.
\tag{100.5}
$$

收敛为原实际数据概率收敛，对规定大小的固定真实支持一致，
pair/path 两种原实验分别成立。即对每个 $\eta>0$，超出 $\eta$ 的概率
对支持及两种实验取上确界后趋零。这里评价同一均匀支持先验定义的有限后验函数，
不把固定支持条件输出律识别为先验混合输出律。

证明分为实际二阶矩传递、同一 Gaussian 残差的精确倾斜及二阶导数展开。
第 98 章的最终 $O_{\mathbb P}(1)$ 余项本身不推出这个常数极限。

**核心及四阶剖面。** 对 $J_a(z)=z\ln(z/a)-z+a$，
$0\le z\le C_0$ 上凸性积分给
$J_a(z)\ge(z-a)^2/[2(C_0+1)]$，端点由连续性解释；$b$ 项同理。
在 $k_j\ge aQ^3/2,l_j\ge bQ^3/2$ 的区域，Stirling 前因子为 $O(Q^{-3})$，
而 $k_j-aQ^3=jQ+O(1)$，故信号行质量满足

$$
f_j^{\rm sig}\le CQ^{-3}
\exp\{- (j\delta)^2/[4(C_0+1)]\}.
\tag{100.6}
$$

非正则区域至少一个率函数有固定正下界，全部贡献至多
$Q^Ce^{-cQ^3}$。原混合行均值至多 $Cqf_j^{\rm sig}$，
实际行比较只乘有界因子，且总有 $p_j(1-p_j)\le1/4$。
以确定性计数线占用先求实际期望，再比较 Gaussian 网格尾积分，得

$$
\sup_{S,\mathcal E}\mathbb E_S V_O
\le Ce^{-c_*D_*\ln Q}+Q^Ce^{-cQ^3},
\qquad V_O=\sum_{K_M\setminus\mathcal H}v_j.
\tag{100.7}
$$

因此在一致高概率数据事件上 $V_O\le Q^{-200}$。
这不把截断外坏事件上的完整后验无界矩当作已控制。
固定增大核心只改变多项式因子，核心占用的指数仍为 $c_q$，
所以第 98 章足够高的固定阶耦合矩仍覆盖整个 (100.1)。

同一良好环境上 $v_j=\delta\rho(j\delta)(1+\epsilon_j)$，
$\sup_{\mathcal H}|\epsilon_j|=o_{\mathbb P}(\delta)$。
令 $G_{r,H}=\delta^{1-r}\sum_{\mathcal H}v_j^r$。
对 $r=4$，

$$
\left|G_{4,H}-\delta\sum_{\mathcal H}\rho(j\delta)^4\right|
\le C\sup_{\mathcal H}|\epsilon_j|\,
\delta\sum_{\mathcal H}\rho(j\delta)^4=o_{\mathbb P}(1).
$$

导数可积的网格积分误差与确定性 Gaussian 尾给
$V_H\to\gamma,\nu_0\to\nu,G_{3,H}\to g_3,G_{4,H}\to g_4$。
因此

$$
A=O(\delta^{-1/2}),\quad \max w_j=O(\sqrt\delta),\quad
\kappa_3=O(\sqrt\delta),\quad\kappa_4=O(\delta),\quad
\sum|w_j|^5=O(\delta^{3/2}).
\tag{100.8}
$$

还有至少 $c/\delta$ 个中央系数介于 $c\sqrt\delta$ 与 $C\sqrt\delta$，
可提供不依赖噪声的 Fourier 平滑。

**实际二阶矩已具有常数精度。** 在第 98 章同一个辅助耦合上，置

$$
m=|\mathcal H|,\quad S_H=\tfrac12\sum_{\mathcal H}(Z_j^2-1),\quad
T_0=\sum_{\mathcal H}w_j(Z_j^2-1),\quad Y_0=T_0+\sigma_MG,\quad
U=S_H+G^2/2.
$$

第 98 章实际局部密度的质量、一阶／混合一阶、中心二阶误差依次是
$O(Q^{-5/2}),O(Q^{-3/2}),O(Q^{-1/2})$。
参考密度在固定紧区间有正下界，一阶有符号密度为 $O(1+A)$，
中心二阶为 $O(1+A^2)$。归一化二阶矩成本至多
$C_K[Q^{-1/2}+(1+A^2)Q^{-5/2}]$；
条件均值平方的成本至多

$$
C_K(1+A)[Q^{-3/2}+(1+A)Q^{-5/2}]
+C_K[Q^{-3/2}+(1+A)Q^{-5/2}]^2=o(1).
$$

同一个残差的二次、四次局部矩及与中心信息量的混合矩均已有相应界。
Bayes 恒等式
$J_{x,y}=S_x+G^2/2+\frac12\ln(2\pi)-L_M+\ln f_x(y)$
说明其条件方差恰由这些矩决定。第 98 章已先联合消去相关的外部能量／信息量，
再支付精确非中心偏移，没有把多项式误差除以 $\sigma_M$。
由此在同一良好数据事件上直接复用其更强中间估计：

$$
\sup_{|y|\le K}\left|
[V_{{\rm post},x}(y)-V_{{\rm prior},x}]
-[\operatorname{Var}(U\mid Y_0=y)-m/2]\right|
\le C_KQ^{-1/2}.
\tag{100.9}
$$

这是中心平方信息量的局部传递，不是用 TV 传递无界二阶矩。

**包含残差的精确倾斜。** 令 $g_s$ 为 $T_0+\sqrt sG$ 的密度，
$\ell_s=\ln g_s$、$R_j=g_s^{(j)}/g_s$，撇号表示 $y$ 导数。
有有限数组恒等式

$$
\operatorname{Var}(U\mid Y_0=y)-m/2
=(A+y)^2\ell_s''+s(A+y)R_2'
+\frac{s^2}{4}(R_4-R_2^2)-\frac12.
\tag{100.10}
$$

为证明它，取完整中心 Gaussian 半径
$F=\frac12(\sum Z_j^2+G^2-(m+1))=U-\frac12$，
以 $e^{\theta F}$ 归一化倾斜所有 $m+1$ 个坐标，$\theta<1$ 近零。
倾斜后每个坐标等于原坐标除以 $\sqrt{1-\theta}$，
因此倾斜输出密度恰为

$$
f_\theta(y)=(1-\theta)
g_{s(1-\theta)}\bigl(y-\theta(A+y)\bigr).
\tag{100.11}
$$

另一方面，
$\ln f_\theta-\ln g_s=\ln\mathbb E[e^{\theta F}\mid Y_0=y]
-\ln\mathbb E e^{\theta F}$。
在零点二次微分，右侧为
$\operatorname{Var}(F\mid Y_0=y)-(m+1)/2$。
固定有限数组和正 $s$ 的 Gaussian 指数可积性保证微分。
左侧微分给

$$
-1+(A+y)^2\partial_y^2\ell_s
+2s(A+y)\partial_y\partial_s\ell_s+s^2\partial_s^2\ell_s.
$$

热方程给 $\partial_s\ell_s=R_2/2$、
$\partial_y\partial_s\ell_s=R_2'/2$、
$\partial_s^2\ell_s=(R_4-R_2^2)/4$，得到 (100.10)。
常数 $-1/2$ 来自 Jacobian 与额外噪声坐标，不能只倾斜 $Z$ 后丢弃它。
这里没有假设 $G$ 在给定输出后仍独立。

**二阶导数展开。** 令 $p_\Lambda$ 为方差 $\Lambda$ 的中心 Gaussian 密度。
对每个固定导数阶 $j$，特别是 $0\le j\le4$，有

$$
\left\|g_s^{(j)}-
\left[p_\Lambda-\frac{\kappa_3}{6}p_\Lambda'''
+\frac{\kappa_4}{24}p_\Lambda^{(4)}
+\frac{\kappa_3^2}{72}p_\Lambda^{(6)}\right]^{(j)}
\right\|_\infty\le C_j\delta^{3/2},
\quad 0<s\le1.
\tag{100.12}
$$

证明用精确特征函数
$\widehat g_s(t)=e^{-st^2/2}\prod e^{-itw_j}(1-2itw_j)^{-1/2}$。
在 $|t|\le\delta^{-1/20}$，其对数为

$$
-\Lambda t^2/2+\kappa_3(it)^3/6+\kappa_4(it)^4/24
+O(\delta^{3/2}|t|^5).
$$

指数展开保留三次项的平方，余项由
$C\delta^{3/2}P_{12}(|t|)e^{-ct^2}$ 控制。
其余频率利用中央系数得到

$$
|\widehat g_s(t)|\le(1+c_1\delta t^2)^{-c_2/\delta}.
\tag{100.13}
$$

直到 $\delta^{-1/2}$ 它被 $e^{-ct^2}$ 控制；
更外侧令 $z=\sqrt\delta|t|$，一半幂给 $e^{-c/\delta}$，
另一半幂支配任意固定阶可积多项式。
带 $|t|^j$ 的尾积分小于任意固定 $\delta$ 幂，Fourier 反演证明 (100.12)。
这是观测系数数组的导数上确界估计，不从带符号 TV 展开或弱收敛中求导。

固定紧区间内 $p_\Lambda$ 有正下界，故取对数并两次求导合法。
令
$P_3=y^3/\Lambda^3-3y/\Lambda^2$，
$P_4=y^4/\Lambda^4-6y^2/\Lambda^3+3/\Lambda^2$，
$P_6=y^6/\Lambda^6-15y^4/\Lambda^5+45y^2/\Lambda^4-15/\Lambda^3$。
$C^2$ 展开为
$\ell_s=\ln p_\Lambda+\kappa_3P_3/6+\kappa_4P_4/24+
\kappa_3^2(P_6-P_3^2)/72+O_K(\delta^{3/2})$，所以

$$
\begin{aligned}
\ell_s''={}&-\Lambda^{-1}+\kappa_3y/\Lambda^3\\
&+\frac{\kappa_4}{2}(y^2/\Lambda^4-\Lambda^{-3})
+\kappa_3^2(\Lambda^{-4}-3y^2/(2\Lambda^5))
+O_K(\delta^{3/2}).
\end{aligned}
\tag{100.14}
$$

同一展开给 $R_2'=2y/\Lambda^2+O_K(\sqrt\delta)$、
$|R_j|\le C_K$（$0\le j\le4$）。

**有限噪声抵消与常数。** 将上式代入 (100.10)。
可能发散的有限噪声线性项精确合并为

$$
-2Ay/\Lambda+2sAy/\Lambda^2=-2A\nu_0y/\Lambda^2.
\tag{100.15}
$$

没有丢弃 $sA$。定义有界的观测多项式

$$
\begin{aligned}
\mathcal R_x(y)={}&-\tfrac12-y^2/\Lambda
+2A\kappa_3y^2/\Lambda^3\\
&+\tfrac12A^2\kappa_4(y^2/\Lambda^4-\Lambda^{-3})\\
&+A^2\kappa_3^2(\Lambda^{-4}-3y^2/(2\Lambda^5)).
\end{aligned}
\tag{100.16}
$$

对 $D_x(y)=V_{{\rm post},x}(y)-V_{{\rm prior},x}+A^2/\Lambda-C_xy$，
(100.9)–(100.15) 给出实际有限估计

$$
\sup_{|y|\le K}|D_x(y)-\mathcal R_x(y)|
\le C_K[Q^{-1/2}+\sqrt\delta+\sigma_M^2].
\tag{100.17}
$$

逐项余项如下：$A^2O(\delta^{3/2})=O(\sqrt\delta)$；
四次／三次平方曲率的 $2Ay,y^2$ 交叉项至多 $O(\sqrt\delta)$；
剩余三次项为 $O(\sqrt\delta)$；
$s(A+y)R_2'$ 的误差是 $O(s)$，其有界 Gaussian 剩项也为 $O(s)$；
$s^2(R_4-R_2^2)$ 为 $O(s^2)$。没有额外要求 $s=o(\sqrt\delta)$。

现在只在有界乘积中取极限：

$$
A\kappa_3\to8\gamma g_3,\qquad
A^2\kappa_4\to48\gamma^2g_4,\qquad
A^2\kappa_3^2\to64\gamma^2g_3^2,\qquad\Lambda\to\nu.
$$

因此极限为

$$
\begin{aligned}
-\tfrac12-\frac{y^2}{\nu}
+\frac{16\gamma g_3y^2}{\nu^3}
+24\gamma^2g_4\left(\frac{y^2}{\nu^4}-\frac1{\nu^3}\right)
+64\gamma^2g_3^2\left(\frac1{\nu^4}-\frac{3y^2}{2\nu^5}\right).
\end{aligned}
\tag{100.18}
$$

对原 $\rho(t)=c_\rho e^{-\kappa t^2/2}$，
令 $d_\rho=\sqrt{2\pi/\kappa}$，Gaussian 积分给
$\gamma=c_\rho d_\rho,g_0=c_\rho^2d_\rho/\sqrt2,
g_3=c_\rho^3d_\rho/\sqrt3,g_4=c_\rho^4d_\rho/2$。
故

$$
\frac{\gamma g_3}{\nu^2}=\frac1{2\sqrt3},\quad
\frac{\gamma^2g_4}{\nu^3}=\frac{\sqrt2}{8},\quad
\frac{\gamma^2g_3^2}{\nu^4}=\frac1{12}.
$$

(100.18) 正是 (100.4)。良好数据事件概率对固定支持和实验一致，
紧的随机常数先限制再放大，得到 (100.5)。有限 Gaussian 混合处处正，
有限后验矩连续，所以紧区间上确界可用可数稠密集表示，包含 $K=0$。证毕。

**命题 100.3（允许核心内的常数阶不变性）。** 可将 (100.2) 换为任意固定
对数核心，只要它保留核心占用指数 $c_q$、上述局部剖面，并在一致良好事件上
$V_O\le Q^{-200}$；例如每个固定 $D'>1000/c_*$ 均满足。
该类中有限系数扣除改变 $o_{\mathbb P}(1)$，故极限 $R$ 不变。

证明。两个对称对数核心嵌套，差集的方差质量 $t\le Q^{-200}$。
非负性给
$|\Delta A|\le\delta^{-1/2}t$、
$|\Delta\nu_0|\le2\delta^{-1}t^2$、
$|\Delta\kappa_3|\le8\delta^{-3/2}t^3$。
两个 $\Lambda$ 使用同一 $s$ 且有正下界，均值定理给

$$
\left|\Delta\frac{A^2}{\Lambda}\right|
\le C(\delta^{-1}t+\delta^{-2}t^2)=o(1),
$$

$$
|\Delta C_x|
\le C(\delta^{-1/2}t+\delta^{-3/2}t^2+\delta^{-5/2}t^3)=o(1).
\tag{100.19}
$$

乘固定有界 $y$ 不改变结论。原实际先验／后验方差本来不依赖证明核心。
没有声称任意小的对数截断均满足常数阶要求。证毕。

可用的 $V_H-\gamma,\nu_0-\nu=O_{\mathbb P}(\delta)$
在发散项 $A^2/\Lambda$ 中仍允许常数量级变化，因此不能把 (100.3)
替换为其极限等价式。合法慢噪声 $\sigma_M=Q^{-1/16}$ 下，
删除分母中的 $\sigma_M^2$ 会产生 $\sigma_M^2/\delta$ 量级的发散差异。
本章不包含零噪声、严格区间端点、增长输出区间、输出尾积分、
实际数据期望或噪声阈值的必要性结论。换用 bits 时所有信息方差及
$R$ 除以 $(\ln2)^2$，能量坐标 $y$ 不变。
成熟倾斜、热方程和 Edgeworth 工具的来源范围见
[Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 100 章后续增补区）

## 101. 全输出加权收敛与平均后验信息方差

**定义 101.1（先验信道内的平均）。** 保持定义 98.1、100.1 的完整计数向量、
精确先验后验 $\mathsf P_x$、原标量 $T$、所有取整及同一观测
$Y=T+\sigma_MG$。继续要求

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q/2.
\tag{101.1}
$$

采用 (100.2) 的固定核心及 (100.3) 的观测系数
$A,\nu_0,\kappa_3,\Lambda=\nu_0+\sigma_M^2,C_x$。
记 $f_x$ 为精确先验信道的 Gaussian 混合输出密度，
$m_x=\mathbb E_xY$，并置

$$
D_x(y)=V_{{\rm post},x}(y)-V_{{\rm prior},x}
+A^2/\Lambda-C_xy,
\qquad
R_*(y)=\frac{29}{6}-3\sqrt2+
\left(3\sqrt2+\frac8{\sqrt3}-9\right)\frac{y^2}{\nu}.
\tag{101.2}
$$

星号区分此确定性多项式与计数向量。本章信息量为自然对数，信息方差为
nats 的平方。以下积分在给定数据 $x$ 的同一个先验信道内进行；
它不是对罕见原始数据环境取无界量的期望。

**定理 101.2（全输出加权极限）。** 在 (101.1) 的完整严格噪声区间内，

$$
\int_{\mathbb R}|D_x(y)-R_*(y)|f_x(y)\,dy\longrightarrow0,
\tag{101.3}
$$

从而

$$
\int_{\mathbb R}V_{{\rm post},x}(y)f_x(y)\,dy
-V_{{\rm prior},x}+\frac{A^2}{\Lambda}-C_xm_x
\longrightarrow\frac8{\sqrt3}-\frac{25}{6}.
\tag{101.4}
$$

两式均为原实际数据概率收敛，对规定大小的固定支持一致，pair/path
两种原实验分别成立：每个固定 $\eta>0$ 下，误差超过 $\eta$ 的概率
对支持及实验取上确界后趋零。此外，

$$
m_x=O_{\mathbb P}(Q^{-5/2}),\qquad C_xm_x=o_{\mathbb P}(1).
\tag{101.5}
$$

所以 (101.4) 的精确均值项可在证明此速率后删除。
有限观测系数 $A^2/\Lambda$ 仍须保留。

证明不能直接积分 (100.5)：固定紧区间外的小概率仍可能乘上发散的中心。
下面先构造全实线的中心方差密度比较，再单独控制参考信道的尾部。

**精确平均恒等式。** 置 $S_x=-\ln\mathsf P_x(R)$、$W=S_x+G^2/2$。
Bayes 恒等式说明给定 $Y=y$ 后的后验信息量与 $W$ 只差输出常数。
观测之前 $S_x,G$ 独立，且 $\operatorname{Var}(G^2)=2$，故全方差公式给出

$$
\int V_{{\rm post},x}(y)f_x(y)\,dy
=V_{{\rm prior},x}+\frac12
-\operatorname{Var}_x\bigl(\mathbb E_x[W\mid Y]\bigr).
\tag{101.6}
$$

有限后验与 Gaussian 矩保证各项有限。本式不假设给定输出后残差仍独立。

**三个全局比较界。** 对 $(U,Y)$ 的联合律 $\mu$ 及其输出密度 $f$，记
$\mathcal V_{\mu,U}(y)=f(y)\operatorname{Var}_\mu(U\mid Y=y)$。
全变差范数中的固定因子并入常数。下列界不要求输出密度有正下界。

首先，在同一概率空间、同一观测下，条件中心化是 $L^2$ 正交投影的补算子，故

$$
\|\mathcal V_U-\mathcal V_V\|_1
\le(\|U\|_2+\|V\|_2)\|U-V\|_2.
\tag{101.7}
$$

证明是条件中心化后平方差分解及 Cauchy–Schwarz；两目标均可先减去任意全局常数。
其次，若两种 $(U,Y)$ 联合律的变差距离为 $\epsilon$，
且两边 $\|U\|_4\le M_4$，则任意 $b>0$ 下

$$
\|\mathcal V_{\mu,U}-\mathcal V_{\mu',U}\|_1
\le C\{b^2\epsilon+M_4^3/b\}.
\tag{101.8}
$$

将 $U$ 截在 $[-b,b]$，被截部分的 $L^2$ 范数至多 $M_4^2/b$，
由 (101.7) 支付两次截断。对有界目标，写
$q=f\mathbb E[U\mid Y]$、
$\mathcal V=f\mathbb E[U^2\mid Y]-q^2/f$。
在凸锥 $|q|\le bf$ 上，$q^2/f$ 两偏导绝对值不超过 $2b,b^2$；
在 $(0,0)$ 连续延拓，沿两对 $(q,f)$ 间线段积分。
结合 $\|q-q'\|_1\le b\epsilon$ 及二阶矩密度的
$b^2\epsilon$ 界，即得 (101.8)，也容许联合律本身奇异。

最后，设在同一联合空间上 $P=LQ$、$0\le L\le C$、
$\mathbb E_QL=1$、$a=\|L-1\|_{2,Q}$、$\|U\|_{4,Q}\le M_4$。
则

$$
\|\mathcal V_{P,U}-\mathcal V_{Q,U}\|_1\le C'aM_4^2.
\tag{101.9}
$$

确实，令 $\bar L=\mathbb E_Q[L\mid Y]$、$m=\mathbb E_Q[U\mid Y]$、
$u=\mathbb E_Q[(L-1)(U-m)\mid Y]$。条件方差直接展开为

$$
\mathcal V_{P,U}-\mathcal V_{Q,U}
=f_Q\mathbb E_Q[(L-1)(U-m)^2\mid Y]-f_Qu^2/\bar L,
\tag{101.10}
$$

在 $\bar L=0$ 时末项取零。首项积分至多 $4aM_4^2$。
在 $\bar L\ge1/2$ 上，Jensen 及 $L$ 有界给
$\int f_Qu^2/\bar L\le2\mathbb E_Q[(L-1)^2(U-m)^2]
\le CaM_4^2$，这里 $\|L-1\|_4^2\le Ca$。
在 $\bar L<1/2$ 上，条件加权 Cauchy–Schwarz 给
$u^2/\bar L\le\mathbb E_Q[L(U-m)^2\mid Y]$，
而该输出事件概率至多 $4a^2$；再次 Cauchy–Schwarz 即付出 $CaM_4^2$。
这一步支付了低密度比输出上的条件均值平方项。

**实际矩与选中律。** 在原一致良好数据事件上，沿用校准乘积律
$\mathsf Q_x$，置 $s_Q=-\ln\mathsf Q_x(R)-\mathbb E_Q[-\ln\mathsf Q_x(R)]$。
(68.47) 的逐组中心四阶矩和独立中心和的展开给

$$
\|s_Q\|_{4,Q}\le CQ,\quad V_Q\le CQ^2,\quad
0\le L_x\le C,\quad a_x=\|L_x-1\|_2\le CQ^{-5/2}.
\tag{101.11}
$$

这与 (98.5)–(98.6) 使用相同完整向量密度。
由于 $t(\ln t)^2/(t-1)^2$ 在 $[0,C]$ 连续延拓后有界，
$\mathbb E_P(\ln L_x)^2\le Ca_x^2$。
能量矩另行核对：对 $U_j=(R_j-C_jp_j)/B$，中心 Bernoulli 八阶展开中
每个非零划分块至少含两个指标，含 $k$ 个指标的块至多贡献方差乘 $B^{-(k-2)}$，故

$$
\mathbb E_QU_j^8\le C(v_j^4+B^{-2}v_j^3+B^{-4}v_j^2+B^{-6}v_j).
\tag{101.12}
$$

利用 $\sum v_j^2=O(\delta)$、$V=O(1)$、$B$ 指数增长，独立中心和给
$\mathbb E_Q[\delta^{-1/2}\sum(U_j^2-v_j)]^4\le C$。
精确中心差 $e_j=(\mu_j-C_jp_j)/B$ 满足 $\|e\|\le a_x\sqrt V$；
线性项四阶矩至多
$C\delta^{-2}[(\sum e_j^2v_j)^2+B^{-2}\sum e_j^4v_j]=o(1)$，
截距仍为 $\delta^{-1/2}\|e\|^2$。因此

$$
\mathbb E_QT^4\le C,\qquad \mathbb E_PT^4\le C,\qquad
\mathbb E_PY^4\le C\quad(\sigma_M\le1).
\tag{101.13}
$$

实际矩来自非负密度支配，未通过 TV 或弱收敛传矩。
同样的高阶耦合与系数界给后续混合、中心和非中心 Gaussian 输出的四阶矩界。
精确均值满足

$$
|m_x|\le\delta^{-1/2}a_x^2V+a_x\|T\|_{2,Q}=O(a_x).
\tag{101.14}
$$

因 $C_x=O(\delta^{-1/2})=O(Q^{1/4})$，其均值乘积为 $O(Q^{-9/4})$，
得到 (101.5)。对 $s_Q+G^2/2$ 用 (101.9)，
再以 (101.7) 支付 $-\ln L_x$ 的目标变化。
先验方差之差也由中心四阶矩给 $|V_{{\rm prior},x}-V_Q|\le Ca_xQ^2$。
于是全局中心方差密度之差为

$$
\bigl\|[\mathcal V_{P,S_x+G^2/2}-V_{{\rm prior},x}f_P]
-[\mathcal V_{Q,s_Q+G^2/2}-V_Qf_Q]\bigr\|_1
\le Ca_xQ^2=o(1).
\tag{101.15}
$$

此外条件 Jensen 与 Cauchy–Schwarz 给

$$
\int|A^2/\Lambda-C_xy|\,|f_P-f_Q|\,dy
\le Ca_x(\delta^{-1}+\delta^{-1/2}\|Y\|_{2,Q})=o(1).
\tag{101.16}
$$

巨大信息均值已在估计前消去，且没有把多项式误差除以噪声。

**同一元组、同一残差的全局传递。** 在第 98 章的同一个量化耦合上，
令 $B_s=S_H+O_s$，其中 $S_H=\frac12\sum_H(Z_j^2-1)$，
$O_s$ 包含所有外部中心信息量，满足
$\|s_Q-B_s\|_2\le CQ^{-98}$、$\|B_s\|_4+\|O_s\|_4\le CQ$。
先仅替换核心能量为 $T_m$，仍保留精确中心和截距。
(98.7) 的完整严格噪声区间耦合给，对任意固定 $p,N$，

$$
d=(T-T_m)/\sigma_M,\qquad \|d\|_p=o(Q^{-N}).
\tag{101.17}
$$

在共同潜变量／输出空间上，两律
$Q(d\xi)\varphi_\sigma(y-T(\xi))dy$ 与
$Q(d\xi)\varphi_\sigma(y-T_m(\xi))dy$ 的 TV 至多 $C\mathbb E|d|$。
还必须支付残差目标变化：在 $y=T_m+\sigma G$ 上，

$$
\frac{(y-T)^2-(y-T_m)^2}{2\sigma^2}=-Gd+d^2/2.
\tag{101.18}
$$

其 $L^2$ 范数由 (101.17) 小于任意固定负幂，交叉律上的目标四阶范数为 $O(Q)$。
先对固定的第一个目标用 (101.8)，取 $b=Q^{10}$，再用 (101.7)
支付 (101.18)，成本为 $O(Q^{-7})$ 加超多项式小量。
随后以 $B_s$ 替换 $s_Q$，条件方差及先验方差均只支付 $O(Q^{-97})$。

移除外部能量必须保留其与 $O_s$ 的相关性。
第 94、98 章的 128 坐标正则化给核心 $(S_H,T_H^G)$ 联合密度

$$
\iint|\partial_t p_H(z,t)|\,dz\,dt\le C\delta^{-1/2}.
\tag{101.19}
$$

每个交错大半块也保留此界：各自选取靠近空间位置 $0,1$ 的 128 个坐标，
沿用相同逆行列式矩及散度界，再卷积其余坐标。
条件于所有外部变量及同一个 $G$，
$(B_s+G^2/2,Y_m)$ 与 $(B_s+G^2/2,Y_H)$ 只平移同一核心密度的能量坐标，
第一坐标包含相关的 $O_s$。因此其 TV 至多

$$
\epsilon_O\le C\delta^{-1/2}\mathbb E|E_O|
\le C\delta^{-1}(1+a_x)V_O=O(Q^{-199.5}).
\tag{101.20}
$$

再次用 (101.8)、$b=Q^{10}$，以及乘 $O(Q^2)$ 的输出质量误差，成本均为 $o(1)$。
只有到此时外部信息量才独立于核心与输出，故精确消去

$$
\operatorname{Var}(B_s+G^2/2\mid Y_H=y)-\operatorname{Var}(B_s)
=\operatorname{Var}(S_H+G^2/2\mid Y_H=y)-|H|/2.
\tag{101.21}
$$

最后写 $T_H^G=T_0+D$，其中 $T_0=\sum_Hw_j(Z_j^2-1)$，
$\|D\|_p=O(Q^{-5/2})$。将核心分成两个交错大半块，
条件于一个半块与 $G$，用另一半块的 (101.19) 支付前者的能量扰动；
然后交换。目标信息量坐标不变，得到

$$
d_{\rm TV}\bigl((S_H+G^2/2,Y_H),(S_H+G^2/2,Y_0)\bigr)
\le C\delta^{-1/2}Q^{-5/2}=O(Q^{-9/4}),
\quad Y_0=T_0+\sigma G.
\tag{101.22}
$$

此时外部大方差已经消去，目标四阶范数仅为 $C\sqrt{|H|}$，
$|H|=O(Q^{1/2}\sqrt{\ln Q})$。取 (101.8) 中 $b=Q$，成本为

$$
C\{Q^2Q^{-9/4}+|H|^{3/2}/Q\}
=O(Q^{-1/4}[1+(\ln Q)^{3/4}])=o(1).
\tag{101.23}
$$

先验核心方差乘输出质量误差也趋零。这解释了不能提前带着完整 $Q$ 阶信息量
执行最后一次 TV 比较。
两输出密度变差为 $\epsilon$ 且二阶矩有界时，
$\int |y||f-g|\le C\sqrt\epsilon$；
所以加入有限残余系数的成本至多
$C(\delta^{-1}\epsilon+\delta^{-1/2}\sqrt\epsilon)$，在 (101.22) 及此前各步都趋零。
令 $g$ 为 $Y_0$ 密度，并置

$$
D_0(y)=\operatorname{Var}(S_H+G^2/2\mid Y_0=y)-|H|/2
+A^2/\Lambda-C_xy.
$$

上述步骤证明

$$
\|f_xD_x-gD_0\|_1\to0,
\qquad \int(1+y^2)|f_x-g|\,dy\to0.
\tag{101.24}
$$

第二式的平方权重由 (101.13) 的四阶矩及
$|f_x-g|\le f_x+g$ 下的 Cauchy–Schwarz 得到。

**参考尾部及相对展开。** 精确 Gaussian 二次型矩母函数、
$\max w_j\le C\sqrt\delta$ 给

$$
\ln\mathbb Ee^{tY_0}\le Ct^2\quad(|t|\le c/\sqrt\delta),
\qquad
\mathbb P(|Y_0|>h)\le2e^{-c'h^2}\quad(1\le h\le c''/\sqrt\delta).
\tag{101.25}
$$

前式展开 $-tw-\frac12\ln(1-2tw)$ 并求和，另加 $\sigma^2t^2/2$；
后式取 Chernoff 参数。它也给每个固定阶输出绝对矩的一致界。
固定足够大的 $D$，取 $h_\delta=\sqrt{D\ln(1/\delta)}$，
使尾概率至多 $C\delta^{20}$。对 $U=S_H+G^2/2$，

$$
\int_{|y|>h_\delta}g(y)\operatorname{Var}(U\mid Y_0=y)\,dy
\le\|U\|_4^2\mathbb P(|Y_0|>h_\delta)^{1/2}\to0.
$$

这里 $\|U\|_4^2\le C|H|=O(\delta^{-1}\sqrt{\ln(1/\delta)})$。
其他项 $|H|/2,A^2/\Lambda,C_xy,R_*(y)$ 由相同尾界及固定矩逐项支付，故

$$
\int_{|y|>h_\delta}g(y)(|D_0(y)|+|R_*(y)|)\,dy\to0.
\tag{101.26}
$$

中间区间则须将 (100.12) 提升到任意高但固定的 Fourier 阶数。
对每个固定 $r\ge3$，精确累积量为

$$
\kappa_r=2^{r-1}(r-1)!\sum_Hw_j^r=O_r(\delta^{r/2-1}).
\tag{101.27}
$$

对数特征函数及其指数保留所有 $\delta$ 阶数小于固定 $N$ 的单项式。
在 $|t|\le\delta^{-\eta_N}$、$\eta_N>0$ 足够小的区域，
Taylor 余项由 $C_N\delta^NP_N(|t|)e^{-ct^2}$ 控制。
其余频率由 (100.13) 的相同块主控支付，带任意固定导数权重仍超多项式小。
所以对 $0\le j\le4$，

$$
\left\|g^{(j)}-
\left[p_\Lambda\left(1+\frac{\kappa_3P_3}{6}
+\frac{\kappa_4P_4}{24}+\frac{\kappa_3^2P_6}{72}
+E_{\delta,N}\right)\right]^{(j)}\right\|_\infty
\le C_{N,j}\delta^N.
\tag{101.28}
$$

$P_3,P_4,P_6$ 是第 100 章多项式；$E_{\delta,N}$ 次数固定，
全部系数为 $O_N(\delta^{3/2})$，因为其余累积量单项式阶数至少为 $3/2$。
在 $|y|\le h_\delta$ 上 $p_\Lambda(y)\ge c\delta^{B_D}$，
其中 $B_D$ 固定。选择固定 $N>B_D+5$，则 $g/p_\Lambda$ 在此有正下界，
(100.14) 的对数导数展开在这个区间成立，余项加强为

$$
O\bigl(\delta^{3/2}(1+|y|^{d_N})\bigr)
+O\bigl(\delta^{N-B_D}(1+h_\delta^{d_N})\bigr).
\tag{101.29}
$$

同理 $R_2'=2y/\Lambda^2+O(\sqrt\delta(1+|y|^{d_N}))$
加相同高阶误差，$R_j$（$j\le4$）有固定多项式界。
这些相对导数估计由四阶导数反演而来，不从 TV 展开求导。

代回包含同一残差的精确倾斜式 (100.10)，有限噪声抵消 (100.15)
仍精确成立。相对于 (100.16) 的观测多项式 $\mathcal R_x$，误差至多

$$
C(\sqrt\delta+\sigma_M^2)(1+|y|^{d'_N})+o(1)
\quad(|y|\le h_\delta),
\tag{101.30}
$$

末项在该区间一致，次数固定。
现在对多项式误差用 (101.25) 的一致矩积分，而非取区间上的最大值，
故无需额外的 $\sigma_M^2(\ln Q)^C\to0$ 条件。
有界系数乘积的极限仍由第 100 章给出，且 $\mathbb E_gY_0^2=\Lambda$，
结合 (101.26) 得

$$
\int g(y)|D_0(y)-R_*(y)|\,dy\to0.
\tag{101.31}
$$

**实际回接与平均常数。** 由三角不等式，(101.24)、(101.31) 及
$|R_*(y)|\le C(1+y^2)$ 得 (101.3)。同时
$\mathbb E_xY^2-\Lambda\to0$，而 $\Lambda\to\nu$，所以

$$
\int f_xR_*\to
\frac{29}{6}-3\sqrt2+3\sqrt2+\frac8{\sqrt3}-9
=\frac8{\sqrt3}-\frac{25}{6}.
$$

积分 $D_x$ 的定义恰为 (101.4) 左侧，证明完成。
全程先在一致良好环境上估计，紧的随机常数先限制再释放；
未以坏数据事件的概率乘未受控的无界矩。

**推论 101.3（回归方差与核心不变性）。** 在同样范围内，(101.6) 等价给出

$$
\operatorname{Var}_x\bigl(\mathbb E_x[S_x+G^2/2\mid Y]\bigr)
=\frac{A^2}{\Lambda}-C_xm_x+\frac{14}{3}-\frac8{\sqrt3}
+o_{\mathbb P}(1).
\tag{101.32}
$$

这不是另加的 Gaussian 回归假设。对命题 100.3 允许的其他固定核心，
(100.19) 及 $\mathbb E_x|Y|=O_{\mathbb P}(1)$ 给

$$
\left|\Delta\frac{A^2}{\Lambda}\right|
+|\Delta C_x|\,\mathbb E_x|Y|=o_{\mathbb P}(1),
$$

故全输出加权极限与平均常数不变；任意更小核心不在该断言范围内。

本章评价同一先验定义的函数在实际固定支持数据下的概率。
没有把固定支持条件输出律换成 $f_x$，没有无界原始数据期望结论，
没有每个实输出的一致近似或增长实际输出区间的上确界结论。
参考中间区间只是已付出尾界的证明工具。
零噪声、严格区间端点及阈值必要性仍不在结论中。
换成 bits 时所有信息方差、有限方差扣除、极限常数及加权残余均除以
$(\ln2)^2$，能量坐标不变。全方差、截断、Gaussian 倾斜与 Edgeworth
方法是成熟工具；本章新增内容是原离散选中信道上的全局传递和可积尾部闭合，
文献范围见 [Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 101 章后续增补区）

## 102. 离散二次平滑与完整占据指数内的平均信息方差

**定理 102.1（扩大严格噪声区间）。** 保持第 101 章的完整原计数向量、
精确先验后验 $\mathsf P_x$、中心 $\mu_j$、标量 $T$、全部原取整及
同一测量 $Y=T+\sigma_MG$。将噪声条件扩大为

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q.
\tag{102.1}
$$

仍取 (100.2) 的固定核心及原观测系数
$A,\nu_0,\kappa_3,\Lambda=\nu_0+\sigma_M^2,C_x$，
令 $D_x,R_*,f_x,m_x$ 精确保持 (101.2) 的定义。则

$$
\int_{\mathbb R}|D_x(y)-R_*(y)|f_x(y)\,dy\longrightarrow0,
\tag{102.2}
$$

$$
\int V_{{\rm post},x}(y)f_x(y)\,dy-V_{{\rm prior},x}
+\frac{A^2}{\Lambda}-C_xm_x
\longrightarrow\frac8{\sqrt3}-\frac{25}{6}.
\tag{102.3}
$$

收敛仍在原实际数据概率下、对规定大小的确定支持一致，pair/path 两种实验分别成立。
积分使用同一个先验预测信道密度；它不替换为已知支持下的条件输出律。
精确均值仍满足 $m_x=O_{\mathbb P}(Q^{-5/2})$、$C_xm_x=o_{\mathbb P}(1)$。
信息方差以 nats 的平方计。严格端点、阈值必要性和零噪声不在结论中。

第 101 章将逐坐标耦合误差除以 $\sigma_M$，只得到半个占据指数。
本章用实际离散二次相位的多个 Fourier 因子共同平滑，替换那一步。
标量密度逼近本身不足够；下面同时比较中心信息量的一、二阶输出矩密度。

**引理 102.2（对实中心一致的二项二次相位界）。** 若
$K\sim\operatorname{Bin}(n,p)$、$p\in[1/4,3/4]$、$d=np(1-p)\ge1$，则
对任意实数 $\mu$ 和 $0<|a|\le1$，

$$
\left|\mathbb E e^{ia(K-\mu)^2}\right|
\le\min\{1,C[\sqrt{|a|}+(d|a|)^{-1/2}]\}.
\tag{102.4}
$$

**证明。** 经典 van der Corput 二阶导数估计对任意长度不超过 $N$ 的整数区间给

$$
\left|\sum e^{ia(k-\mu)^2}\right|
\le C(N\sqrt{|a|}+|a|^{-1/2}).
\tag{102.5}
$$

二阶导数不依赖实中心；负 $a$ 用共轭处理，$2\pi$ 归入常数。
将二项质量 $b(k)$ 在整数轴补零，分成长度 $N=\lceil\sqrt d\rceil$ 的块。
其质量比随 $k$ 递减，故单峰；最大质量至多 $C/\sqrt d$，
总变差至多最大质量的两倍。记各块最大值为 $M_I$，则

$$
M_I\le N^{-1}\sum_Ib(k)+\operatorname{Var}_I(b),\qquad
\sum_IM_I\le N^{-1}+2\max b\le C/\sqrt d.
$$

Abel 求和将每块加权和界为 (102.5) 乘端点质量与块内变差之和，
该和至多 $3M_I$。对全部块求和即得 (102.4)。
这里未丢弃二项尾部，也没有待乘逆噪声的小概率余项。证毕。

**实际尺度与共同实现。** 仍记
$\lambda=Q^3,\delta=Q^{-1/2},B^2=q/Q^{5/2}$，置

$$
\mathcal B=B^2\sqrt\delta=q/Q^{11/4},\qquad
\ln\mathcal B=c_q\lambda+O(\ln Q),\qquad
T=\mathcal B^{-1}\sum_j(R_j-\mu_j)^2-V/\sqrt\delta.
\tag{102.6}
$$

这只是原二次整数相位的精确系数，未断言存在共同格距。
在原一致良好数据事件上，校准乘积律给独立
$R_j\sim\operatorname{Bin}(C_j,p_j)$。写

$$
d_j=C_jp_j(1-p_j),\quad v_j=d_j/B^2,\quad
e_j=(\mu_j-C_jp_j)/B,\quad w_j=v_j/\sqrt\delta.
$$

第 98、101 章使用的同一固定对数核心 $H$ 满足

$$
|H|=O(Q^{1/2}\sqrt{\ln Q}),\quad
\min_Hd_j\ge e^{c_q\lambda}Q^{-C_D},\quad
V_O\le Q^{-200},\quad \|e\|\le a_x\sqrt V,
\quad a_x=O_{\mathbb P}(Q^{-5/2}).
\tag{102.7}
$$

其中 $C_D$ 固定。原紧区域的正 Gaussian 剖面还给至少 $c/\delta$ 个中心坐标满足
$c\delta\le v_j\le C\delta$。
这些条件由实际一、二行 PGF、统一占据方差及紧区域 Stirling 剖面得到，
与噪声选择无关；没有增加新的系数假设或假定实际路径行独立。

在第 98 章的同一个单调分位数耦合上，以独立 $Z_j$ 替换核心标准化计数，
外部计数仍保留原实现。令

$$
s_j=-\ln b_j(R_j)-\mathbb E_Q[-\ln b_j(R_j)],\quad
s_Q=\sum_js_j,\quad s_O=\sum_{H^c}s_j,\quad
S_H=\tfrac12\sum_H(Z_j^2-1),
$$

$$
U=s_Q+G^2/2,\quad U'=S_H+s_O+G^2/2,
$$

$$
T'=\delta^{-1/2}\left[
\sum_H(\sqrt{v_j}Z_j-e_j)^2+
\sum_{H^c}((R_j-C_jp_j)/B-e_j)^2-V\right],\quad Y'=T'+\sigma_MG.
\tag{102.8}
$$

两边使用同一个 $G$，外部信息量与外部能量的相关性完整保留。
紧参数二项量化耦合有任意固定阶 $L^p$ 误差 $C_pd_j^{-1/2}$。
中心信息量的 Stirling 估计给
$\|\sum_Hs_j-S_H\|_2\le C|H|(\min_Hd_j)^{-1/36}$：
在 $|K-np|\le n^{5/8}$ 用带余项 Stirling，补事件用高阶 Bernoulli 矩与
二次信息量界，中心化后得到这一较弱但足够的指数。
因式分解平方差并保留实中心修正，得

$$
\|U-U'\|_2+\|Y-Y'\|_2
\le Q^{C_D'}e^{-c_q\lambda/36}=:\eta_Q,
\quad \|U\|_4+\|U'\|_4\le CQ,
\quad \mathbb E|Y|^4+\mathbb E|Y'|^4\le C.
\tag{102.9}
$$

矩界由同一独立和的展开及原中心界直接得到，未从 TV 传递无界矩。

**命题 102.3（前两阶信息矩的全输出密度比较）。** 在 (102.1) 下，定义有限有符号密度

$$
q_k(y)\,dy=\mathbb E_Q[U^k;Y\in dy],\qquad
q'_k(y)\,dy=\mathbb E_Q[(U')^k;Y'\in dy],\quad k=0,1,2.
$$

则对每个固定 $N>0$，在上述良好环境上最终有

$$
\max_{0\le k\le2}\{
\|q_k-q'_k\|_\infty+\|q_k-q'_k\|_1\}\le C_NQ^{-N}.
\tag{102.10}
$$

**证明。** Fourier 变换分别为 $\mathbb E[U^ke^{itY}]$ 和
$\mathbb E[(U')^ke^{itY'}]$。由 (102.9) 及 Cauchy–Schwarz，

$$
|\widehat q_k(t)-\widehat q'_k(t)|\le CQ^2\eta_Q(1+|t|).
\tag{102.11}
$$

$k=2$ 时分别估计平方差与
$\mathbb E[(U')^2|Y-Y'|]\le\|U'\|_4^2\|Y-Y'\|_2$。
该界在任意固定多项式频段上的积分超多项式小，无需除以噪声。

高频则展开 $s_Q^k$。每个单项至多标记两个坐标，
其绝对矩一致有界；其余未标记坐标的 Fourier 因子相乘。
非空组数为 $O(Q^2)$，故展开成本至多 $CQ^4$。
对每个单项，从中心坐标中选取任意固定数 $n$ 个未标记者。
由 (102.4)、(102.6)，其因子至多

$$
\min\{1,C[(|t|/\mathcal B)^{1/2}+\delta^{-1/4}|t|^{-1/2}]\},
\qquad 0<|t|\le\mathcal B.
\tag{102.12}
$$

Gaussian 核心的精确非中心二次积分则给

$$
|\mathbb E e^{itw_j(Z_j-a_j)^2}|
=(1+4t^2w_j^2)^{-1/4}
\exp\left\{-\frac{2t^2w_j^2a_j^2}{1+4t^2w_j^2}\right\}
\le\min\{1,C\delta^{-1/4}|t|^{-1/2}\}.
$$

不要求远处核心坐标的个别标准化平移小。
同一测量残差的因子必须精确保留：

$$
\mathbb E e^{it\sigma G}=e^{-\sigma^2t^2/2},\quad
\mathbb E[G^2e^{it\sigma G}]=(1-\sigma^2t^2)e^{-\sigma^2t^2/2},
$$

$$
\mathbb E[G^4e^{it\sigma G}]
=(3-6\sigma^2t^2+\sigma^4t^4)e^{-\sigma^2t^2/2}.
\tag{102.13}
$$

由 $U^2=s_Q^2+s_QG^2+G^4/4$、独立乘积及
$(u+v)^n\le2^{n-1}(u^n+v^n)$，两种加权变换均满足

$$
|\widehat q_k(t)|+|\widehat q'_k(t)|
\le C_nQ^4[(|t|/\mathcal B)^{n/2}+\delta^{-n/4}|t|^{-n/2}],
\quad1\le|t|\le\mathcal B,
\tag{102.14}
$$

以及对全部实频率的界

$$
|\widehat q_k(t)|+|\widehat q'_k(t)|
\le CQ^4[1+(\sigma|t|)^4]e^{-\sigma^2t^2/2}.
\tag{102.15}
$$

固定 $0<b_0<b_1<c_q$ 使最终 $L_M\le b_0\lambda$，取
$F_M=e^{b_1\lambda}$，再固定
$n>\max\{4,2b_1/(c_q-b_1)\}$。
令 $T_M=Q^b$，其中固定 $b$ 随要求的精度选择。
(102.14) 在 $[T_M,F_M]$ 上的积分至多

$$
C_nQ^4[\mathcal B^{-n/2}F_M^{1+n/2}
+\delta^{-n/4}T_M^{1-n/2}].
\tag{102.16}
$$

首项的指数为 $[b_1-(n/2)(c_q-b_1)]\lambda$ 加 $O_n(\ln Q)$，严格为负；
第二项为 $C_nQ^{4+n/8+b(1-n/2)}$，选 $b$ 即可达到任意固定精度。
$F_M/\mathcal B\to0$，故全部应用都在 (102.12) 的范围内。
在 $|t|>F_M$ 用 (102.15)，积分至多

$$
CQ^4\sigma^{-1}[1+(\sigma F_M)^5]e^{-(\sigma F_M)^2/4}.
\tag{102.17}
$$

因 $\sigma F_M\ge e^{(b_1-b_0)\lambda}$，Gaussian 双指数尾支付了逆噪声。
低频用 (102.11)。对每个正噪声，加权变换可积，Fourier 反演给
(102.10) 的上确界范数部分。

由 (102.9)，$R\ge1$ 时

$$
\int_{|y|>R}|q_k(y)|\,dy
\le\mathbb E[|U|^k;|Y|>R]\le CQ^2R^{-2},
\tag{102.18}
$$

另一密度相同。$k=2$ 时用四阶矩和输出四阶尾界；其余更弱。
在足够大的固定 $Q$ 次幂处截断，内部提高上确界精度，外部用 (102.18)，
得到 $L^1$ 部分。全程未声称离散与连续潜在信息量的联合 TV 趋零。证毕。

**条件均值平方的非线性步骤。** 对任意 $(U,Y)$ 及其前三个输出矩密度，写
$f=q_0$、$\mathcal V_U=q_2-q_1^2/f$。令

$$
F_b(f,q)=\sup_{|t|\le b}(2tq-t^2f).
$$

则 $|F_b(f,q)-F_b(f',q')|\le2b|q-q'|+b^2|f-f'|$，且
$q^2/f-F_b(f,q)=f(|q/f|-b)_+^2$，零密度处取零。
条件 Jensen 给该非负余项的积分至多 $\mathbb E|U|^4/b^2$。
所以记 $\epsilon_k=\|q_k-q'_k\|_1$，有

$$
\|\mathcal V_U-\mathcal V_{U'}\|_1
\le\epsilon_2+2b\epsilon_1+b^2\epsilon_0
+\frac{\mathbb E|U|^4+\mathbb E|U'|^4}{b^2}.
\tag{102.19}
$$

取 $b=Q^3$，(102.9)、(102.10) 使右侧为 $O(Q^{-2})+o(1)$。
不需要输出密度下界。耦合又给
$|V_Q-V'_Q|\le CQ\eta_Q$，其中
$V'_Q=|H|/2+\operatorname{Var}(s_O)$；减去各自先验方差后，
质量误差乘 $O(Q^2)$ 也由 (102.10) 支付。
有界输出二阶矩给
$\int|y||f-f'|\le C\|f-f'\|_1^{1/2}$，
故有限修正密度 $A^2f/\Lambda-C_xyf$ 的差也趋零。

**返回原选中信道。** 实际比较仍先支付 (101.15) 的完整选中密度误差
$Ca_xQ^2=o_{\mathbb P}(1)$，以及 (101.16) 的有限系数密度误差。
它们对同一信道成立且不含逆噪声。Bayes 恒等式把实际后验信息方差
精确识别为 $S_x+G^2/2$ 的条件方差。
随后应用本章 (102.10)、(102.19)，替换第 101 章受半指数限制的
(101.17)–(101.18) 那一段。

此时外部信息量仍与其能量相关。沿用核心联合密度的
$\iint|\partial_t p_H|\le C\delta^{-1/2}$，条件于全部外部变量及同一 $G$，
平移能量坐标支付 $C\delta^{-1}(1+a_x)V_O=O(Q^{-199.5})$ 的联合变差。
(101.8) 以截断 $b=Q^{10}$ 将其传递到方差密度，之后才精确消去外部先验方差。
再以两个交错大半核心互相平滑去掉原非中心线性项及截距，
联合变差为 $O_{\mathbb P}(Q^{-9/4})$；此时目标四阶范数只为 $C\sqrt{|H|}$，
取 $b=Q$ 支付 $O_{\mathbb P}(Q^{-1/4}[1+(\ln Q)^{3/4}])$。
这些是 (101.19)–(101.23) 已逐项证明的不含逆噪声的界，其假设 (102.7) 未变。

以 $g,D_0$ 记第 101 章相同的中心 Gaussian 核心输出及残余，遂得

$$
\|f_xD_x-gD_0\|_1\to0,\qquad
\int(1+y^2)|f_x-g|\,dy\to0.
\tag{102.20}
$$

平方权重由各中间输出的直接四阶矩支付。
最后，(101.25)–(101.31) 的参考展开和可积尾界仅要求 $\sigma_M\to0$：
核心 Fourier 高频界在零噪声下仍成立，所有固定累积量和 Chernoff 估计
对 $0<\sigma_M\le1$ 一致；有限噪声抵消始终精确，没有使用半指数条件。
因此仍有 $\int g|D_0-R_*|\to0$。
与 (102.20) 及 $|R_*(y)|\le C(1+y^2)$ 合并，证明 (102.2)。
$\mathbb E_xY^2\to\nu$ 后积分同一多项式，给 (102.3)。
均值速率仍由 (101.14) 得到，与噪声无关。证毕。

**边界与归属。** 新区间依赖 $b_1<c_q$：在端点，(102.16) 的指数预算
对任意固定 $n$ 都不能按此法闭合。这是本证明的边界，未证明实际共振或定理失效。
中心可为任意实数，未添加有理性或无共振假设。
任意慢的噪声趋零仍包括在内，放大的 $A^2/\Lambda$ 与 $C_x$ 中有限
$\sigma_M^2$ 不能删去。第 101 章允许的固定核心变更仍只造成 $o_{\mathbb P}(1)$
积分误差，任意更小核心不包含在该断言中。

本章未自动扩大逐输出熵、覆盖或信息谱的适用范围，没有全实线上确界或
无界原始数据期望结论。未知方向只使用原共同判向事件。
换成 bits 时各信息方差、有限方差修正、残余多项式和极限常数统一除以
$(\ln2)^2$，能量坐标不变。
van der Corput、Abel 求和、Fourier 反演及凸截断都是成熟工具；
新增连接是原完整计数信道上的加权离散平滑及其绝对条件方差传递。
原始文献和适用条件见 [Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 102 章后续增补区）

## 103. 固定阶后验 Rényi 熵与稀有能量鞍点

**定义 103.1（逐输出的计数 Rényi 熵）。** 保持第 68–71 章的原幅度、固定
$\beta\in(1/2,1)$、合法规模、全部取整、完整计数向量及其均匀大小 $q$ 支持先验。
记 $\mathsf P_x$ 为原精确计数后验，$\mathsf P_x^y$ 为同一标量
$Y=t_x(R)+\sigma_MG$ 在输出 $y$ 后的精确后验。
本章固定 $\alpha>0$、$\alpha\ne1$，采用自然对数，定义

$$
H_\alpha(P)=\frac{\ln\sum_nP(n)^\alpha}{1-\alpha}.
\tag{103.1}
$$

这是每个输出对应的一份有限分布的熵，不是输出平均，也不是 Arimoto 或 Sibson 条件熵。
幂作用于计数概率，包括其中的组合因子；对象不是标签微观态。

为避免与熵阶混淆，将原计数线斜率记为
$\vartheta=\ln(1+r)/[-\ln(1-r)]$。令

$$
a=(1+r)/2,\quad b=(1-r)/2,\quad
\kappa=a^{-1}+\vartheta^2/b,\quad
\rho(s)=\frac{e^{-\kappa s^2/2}}{4\pi\sqrt{ab}},\quad
\gamma=\int_{\mathbb R}\rho(s)\,ds,
$$

$$
K(t)=-\frac12\int_{\mathbb R}\ln(1-2t\rho(s))\,ds,
\quad -\infty<t<t_c:=\frac1{2\rho(0)}.
\tag{103.2}
$$

记 $t_\alpha$ 为 $K'(t_\alpha)=\alpha\gamma$ 的唯一解，并置
$J_\alpha=\alpha\gamma t_\alpha-K(t_\alpha)$。
下文证明全部固定正阶均有这个内部鞍点。

**定理 103.2（固定阶的后验熵响应）。** 若

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q/2,
\tag{103.3}
$$

则对每个固定有限 $R$，

$$
\sup_{|y|\le R}\left|
\delta[H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x)+L_M]
-\frac{J_\alpha}{\alpha-1}\right|\longrightarrow0,
\qquad\delta=Q^{-1/2}.
\tag{103.4}
$$

收敛在原实际数据概率下、对所有规定大小的确定支持一致，pair/path 两种原实验分别成立。
确定支持数据仍评价同一个均匀先验定义的后验函数。
$J_\alpha>0$，故修正项在 $0<\alpha<1$ 时为负，在 $\alpha>1$ 时为正。
本结论不对趋近零、一或无穷的阶数一致，不给期望后验熵或增长输出区间上的结论。

**精确模型与最大权重。** 在原共同良好数据事件上，完整非空组位于确定截断计数线，
组数 $m\le CQ^2$。保留

$$
B^2=q/Q^{5/2},\quad
d_j=C_jp_j(1-p_j),\quad v_j=d_j/B^2,\quad V=\sum_jv_j,
\quad e_j=(\mu_j-C_jp_j)/B,
$$

$$
A_j(n)=(n_j-\mu_j)/B,\quad E(n)=\sum_jA_j(n)^2,
\quad t_x(n)=\delta^{-1/2}(E(n)-V).
\tag{103.5}
$$

原精确中心 $\mu_j$ 和完整校准 $V$ 都未替换。
第 69、70 章的实际占据数与校准界给
$N_J=\sum C_j=O_{\mathbb P}(B^2)$、$V\to\gamma$、
$\eta_x=\max|p_j-1/2|=O_{\mathbb P}(q^{-1/2})$、
$\|e\|_2=O_{\mathbb P}(Q^{-5/2}+q^{-1/2})$。
空组可补零。以 $\bar C_j$ 记两总体 Poisson 比较均值，原一、二行 PGF 给

$$
\mathbb EC_j=\bar C_j(1+O(\lambda^3/M)),\quad
\operatorname{Var}C_j\le C(\bar C_j+\lambda^3\bar C_j^2/M),
\quad\sum_j\bar C_j\le CB^2,\quad
\sum_j\bar C_j^2\le CB^4\delta.
\tag{103.6}
$$

因此对固定 $\zeta>0$，Chebyshev 联合界给

$$
\Pr\{\max_j|C_j-\mathbb EC_j|>\zeta B^2\delta\}
\le C_\zeta\left[(B^2\delta^2)^{-1}
+\lambda^3/(M\delta)\right]\to0.
\tag{103.7}
$$

在固定空间紧区间上，原 Stirling 剖面给
$\bar C_j/(4B^2\delta)\to\rho(j\delta)$ 一致成立；其外先用 Gaussian 包络，
再用远端指数小的总均值。结合 (103.7) 及校准，得到

$$
\max_jv_j/\delta\to\rho(0).
\tag{103.8}
$$

原点组给下界。正倾斜需要这项最大值控制，单有累积时钟极限不够。
同理，对包含权重范围的固定区间上的 $C^1$ 函数 $F$，若 $F(0)=0$，则

$$
\delta\sum_jF(v_j/\delta)\to\int F(\rho(s))\,ds.
\tag{103.9}
$$

紧区间上用 Riemann 和，外部用 $|F(u)|\le C_Fu$ 及实际尾质量的 Markov 界。
对紧的一致 Lipschitz 参数族用有限网，得到参数一致版本。
这些仍是实际数据概率结论，没有假定路径行独立。

**精确 escort 恒等式。** 对计数律 $P$ 置 $P_\alpha=P^\alpha/\sum P^\alpha$，
以 $f_{P,s}$ 记对原同一 $t_x$ 加标准差 $s$ 的 Gaussian 输出密度。
Gaussian 核的幂满足

$$
\varphi_\sigma(z)^\alpha
=(2\pi)^{(1-\alpha)/2}\sigma^{1-\alpha}\alpha^{-1/2}
\varphi_{\sigma/\sqrt\alpha}(z).
$$

有限求和及 Bayes 公式于是给精确等式

$$
H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x)
=-L_M+\tfrac12\ln(2\pi)-\frac{\ln\alpha}{2(1-\alpha)}
+\frac{\ln f_{\mathsf P_\alpha,\sigma/\sqrt\alpha}(y)
-\alpha\ln f_{\mathsf P,\sigma}(y)}{1-\alpha}.
\tag{103.10}
$$

在计数 escort 下，紧输出对应稀有能量；普通中心极限定理不能计算这里的密度。

**固定总数修正的稀有输出比较。** 校准乘积计数律
$\mathsf Q_x=\bigotimes_j\operatorname{Bin}(C_j,p_j)$ 与实际计数律满足
$\mathsf P_x(n)=\mathcal L_x(k)\mathsf Q_x(n)$，其中
$k=\sum_jn_j$、$D=k-\sum C_jp_j$。
在完整盒支持事件上，第 70 章全局界为

$$
-C(D^2/q+q^{-1/2})\le\ln\mathcal L_x(k)
\le C(d_J/q+q^{-1/2}),\quad d_J=B^2V.
\tag{103.11}
$$

其完整计数 escort 仍是独立乘积，每个组合因子都取 $\alpha$ 次幂。
已证界给
$\operatorname{Var}_\alpha n_j\le C_\alpha C_j$、
$|\mathbb E_\alpha n_j-C_jp_j|\le C_\alpha C_j\eta_x$，以及
$\ln\mathbb E_\alpha\mathcal L_x^\alpha=O_{\mathbb P,\alpha}(Q^{-5/2})$。
精确能量满足

$$
D^2/q\le2mB^2q^{-1}(E+\|e\|^2)
\le C\delta(E+\|e\|^2),\qquad
\mathbb E_\alpha E=O_{\mathbb P,\alpha}(1).
\tag{103.12}
$$

后式来自 $N_J/B^2$、$\eta_x^2N_J^2/B^2$ 及 $\|e\|^2$ 的界。

需要控制同一稀有输出权重下的能量，而非除以输出密度。
若非负变量 $E$ 满足 $\mathbb EE\le A$、$A\ge1$，按
$\exp[-(E-h)^2/(2w^2)]$ 重加权，其中 $|h|\le H$、$0<w\le1$，
则新均值只依赖 $A,H$ 有界。确实，$\Pr(E\le2A)\ge1/2$，故分母至少
$\frac12e^{-(2A+H)^2/(2w^2)}$。选固定 $R_0$ 使 $u\ge R_0$ 时
$(u-h)^2-(2A+H)^2\ge u^2/4$，尾部均值比至多
$2\sup_{u\ge R_0}u e^{-u^2/(8w^2)}$，统一有界；内部至多 $R_0$。

取 $h=V+\sqrt\delta y$、$w=\sqrt\delta\sigma/\sqrt\alpha$，
用 $\mathbb E_{\alpha,y}$ 表示这个 Gaussian 加权的原计数 escort，则

$$
\frac{f_{\mathsf P_\alpha,\sigma/\sqrt\alpha}(y)}
{f_{\mathsf Q_\alpha,\sigma/\sqrt\alpha}(y)}
=\frac{\mathbb E_{\alpha,y}\mathcal L_x^\alpha}
{\mathbb E_\alpha\mathcal L_x^\alpha}.
$$

由 Jensen、(103.11)–(103.12) 及刚证明的条件均值界，

$$
\sup_{|y|\le R}\left|
\ln\frac{f_{\mathsf P_\alpha,\sigma/\sqrt\alpha}(y)}
{f_{\mathsf Q_\alpha,\sigma/\sqrt\alpha}(y)}\right|
=O_{\mathbb P,\alpha,R}(\delta).
\tag{103.13}
$$

此步对任意趋零正噪声成立，也包含 $\alpha=1$。
极端元组的 $\mathcal L_x$ 可很小；没有声称全盒上的正下界。

**计数幂律与取整 Gaussian 的相对比较。** 对紧参数二项分布，记
$d=np(1-p)$，$z=(k-np)/\sqrt d$。带余项 Stirling 给

$$
\ln b_{n,p}(k)=-\tfrac12\ln(2\pi d)-z^2/2
+O((1+|z|^3)/\sqrt n).
\tag{103.14}
$$

在 $|z|\le n^{1/12}$ 归一化 $\alpha$ 次幂；全局 Gaussian 原子包络控制补集。
Riemann 和得到

$$
\sum_kb_{n,p}(k)^\alpha
=(2\pi d)^{(1-\alpha)/2}\alpha^{-1/2}(1+O_\alpha(n^{-1/4})).
\tag{103.15}
$$

若 $Z^{\rm round}$ 是 $N(np,d/\alpha)$ 的最近整数取整，
则在 $|z|\le R_n=o(n^{1/6})$、右侧误差趋零的范围内，归一化幂质量 $h$ 满足

$$
\frac{h_{n,p;\alpha}(k)}{\Pr(Z^{\rm round}=k)}
=1+O_\alpha\left[n^{-1/4}+(1+R_n^3)/\sqrt n\right].
\tag{103.16}
$$

单位格内积分与中心密度的相对误差为 $O_\alpha((1+|z|)/\sqrt n)$。
同一包络给所用范围内的尾界 $C_\alpha e^{-c_\alpha R^2}$。

固定 $l<c_q/2$ 使最终 $L_M\le lQ^3$，选 $\epsilon>0$ 满足
$2\epsilon<c_q-l$。只为证明分组：令 $H=\{j:C_j\ge e^{\epsilon Q^3}\}$。
其余所有计数配置均满足

$$
0\le E_{H^c}\le CQ^2e^{2\epsilon Q^3}/B^2.
\tag{103.17}
$$

这是由 $0\le\mu_j,n_j\le C_j$ 得到的整个范围界。
在 $H$ 上引入独立标准正态并保持精确中心，令

$$
T_G=\delta^{-1/2}\left[
\sum_{j\in H}(\sqrt{v_j/\alpha}Z_j-e_j)^2-V\right].
\tag{103.18}
$$

整数盒 $|n_j-C_jp_j|/\sqrt{d_j}\le Q^2$ 上，(103.16) 的至多 $CQ^2$ 项
相乘得到 $1+o(1)$ 的一致质量比；两律盒外概率至多
$CQ^2e^{-c_\alpha Q^4}$。
在盒的连续 Gaussian 原像上，电荷范数至多 $CQ^2$，
取整造成的电荷向量误差至多 $\sqrt m/(2B)$。
结合 (103.17) 及平方差分解，对所有低计数组配置一致有

$$
|t_x(n)-T_G|\le\Delta_Q
\le\operatorname{poly}(Q)[B^{-1}+B^{-2}e^{2\epsilon Q^3}],
\qquad\Delta_Q/\sigma\to0.
\tag{103.19}
$$

多项式阶固定，来自 $m\le CQ^2$、$\delta^{-1/2}$ 和盒半径。
原两次下取整已包含在 $\ln q=c_qQ^3+O(1)$ 内。

为避免额外损失一个逆噪声，直接夹住 Gaussian 核。
若 $|d|\le\Delta$、$h=\Delta/s\in(0,1)$，则对全部实 $z$，

$$
\varphi_s(z+d)\ge(1+h)^{-1/2}e^{-(h+h^2)/2}
\varphi_{s/\sqrt{1+h}}(z),
$$

$$
\varphi_s(z+d)\le(1-h)^{-1/2}e^{h/2}
\varphi_{s/\sqrt{1-h}}(z).
\tag{103.20}
$$

它们由 $(z+d)^2$ 的两侧二次不等式直接得到，$\Delta=0$ 时取等式。
取 $s=\sigma/\sqrt\alpha$，在整个中央盒上积分，再积分全部低计数组。
所得原乘积 escort 密度夹在 $(1+o(1))$ 倍的两种 (103.18) Gaussian 输出密度之间，
噪声宽度分别为 $s/\sqrt{1\pm h}$，加性误差至多

$$
C_\alpha\sigma^{-1}Q^2e^{-c_\alpha Q^4}.
\tag{103.21}
$$

下一步的相对密度下界会支付此误差，不能用多项式加性误差代替。

**倾斜数组的局部密度。** 每个固定空间紧区间最终都包含在 $H$ 中，
而删除低计数组对 $\sum v_j$ 的影响指数小。
故 (103.8)–(103.9) 仍成立。容许 $\sigma'/\sigma\to1$，包括 (103.20) 的两种宽度扰动。
定义

$$
W=\sum_{j\in H}(\sqrt{v_j}Z_j-\sqrt\alpha e_j)^2
+\sqrt{\alpha\delta}\,\sigma'G,\qquad
z_y=\alpha(V+\sqrt\delta y).
$$

其精确缩放累积量函数为

$$
F_x(t)=\delta\ln\mathbb E e^{tW/\delta}
=-\frac\delta2\sum_H\ln(1-2tv_j/\delta)
+\alpha t\sum_H\frac{e_j^2}{1-2tv_j/\delta}
+\frac{\alpha t^2(\sigma')^2}{2}.
\tag{103.22}
$$

由最大权重界，在 $t<t_c$ 的任意紧子区间上有共同正分母余量；
(103.9) 给 $F_x^{(k)}\to K^{(k)}$ 对 $k=0,1,2,3,4$ 局部一致。
非中心项及其固定阶导数至多 $C\|e\|^2=o_{\mathbb P}(1)$。

直接微分积分得

$$
K'(t)=\int\frac{\rho(s)}{1-2t\rho(s)}\,ds,\qquad
K''(t)=2\int\frac{\rho(s)^2}{(1-2t\rho(s))^2}\,ds>0.
$$

$K'(0)=\gamma$，$t\to-\infty$ 时导数趋零；$t\uparrow t_c$ 时，
原点附近分母与 $1-2t\rho(0)+s^2$ 可比，故导数趋无穷。
因此每个固定正阶的 $t_\alpha$ 唯一且内部。
严格凸性给 $J_\alpha>0$，除非 $\alpha=1$。
在 $t_\alpha$ 两侧选紧的导数夹点，得到唯一精确鞍点

$$
F_x'(t_x(y))=z_y,\qquad t_x(y)\to t_\alpha
\quad\text{对 }|y|\le R\text{ 一致}.
\tag{103.23}
$$

按 $e^{tW/\delta-F_x(t)/\delta}$ 倾斜，取 $t=t_x(y)$。
平方前的 Gaussian 坐标均值与方差变为

$$
-\frac{\sqrt\alpha e_j}{1-2tv_j/\delta},\qquad
\widetilde v_j=\frac{v_j}{1-2tv_j/\delta}.
$$

附加 Gaussian 方差仍为 $\alpha\delta(\sigma')^2$，均值变为
$\alpha t(\sigma')^2$。倾斜后的 $W$ 均值恰为 $z_y$，方差为 $\delta F_x''(t)$。
固定空间核心提供至少 $c/\delta$ 个 $v_j\in[c\delta,C\delta]$ 的坐标。
因此倾斜后标准化变量的特征函数满足

$$
|\psi_{x,t}(u)|\le(1+c\delta u^2)^{-c'/\delta}.
\tag{103.24}
$$

非中心因子只减小模。$|u|\le\delta^{-1/2}$ 时由 $e^{-c_1u^2}$ 主控；
更高频令 $v=\sqrt\delta|u|\ge1$，用
$\ln(1+cv^2)\ge\ln(1+c)+[2c/(1+c)]\ln v$，尾积分指数小。
在固定频段，对 (103.22) 作复参数展开给

$$
\ln\psi_{x,t}(u)=-\tfrac12F_x''(t)u^2
+O(\sqrt\delta|u|^3).
$$

共同分母余量控制复导数余项；Fourier 反演与一致可积主控遂给倾斜标准化密度在零处为
$[2\pi F_x''(t)]^{-1/2}+o(1)$，对固定输出紧区间及两种噪声扰动一致。
解除倾斜，并用 $dz_y/dy=\alpha\sqrt\delta$，得到相对估计

$$
f_{G,\alpha,\sigma'/\sqrt\alpha}(y)
=\frac{\alpha[1+o(1)]}{\sqrt{2\pi F_x''(t_x(y))}}
\exp\left[-\frac{t_x(y)z_y-F_x(t_x(y))}{\delta}\right].
\tag{103.25}
$$

其前因子有正的上下界，指数率一致趋于 $J_\alpha$，所以

$$
\sup_{|y|\le R}|\delta\ln f_{G,\alpha,\sigma'/\sqrt\alpha}(y)+J_\alpha|\to0,
\qquad f_{G,\alpha,\sigma'/\sqrt\alpha}(y)\ge e^{-C_{\alpha,R}/\delta}.
\tag{103.26}
$$

上述结论可先限制紧随机量，再释放限制，得到实际数据概率收敛；
未断言所有原历史上的几乎处处收敛。

**实际回接。** (103.21) 相对 (103.26) 下界的对数至多
$-c_\alpha Q^4+L_M+C_{\alpha,R}\sqrt Q+O(\ln Q)\to-\infty$。
因此核夹逼给原完整乘积 escort 的同一缩放对数密度极限。
再用 (103.13) 回到实际固定总数后验，得到

$$
\sup_{|y|\le R}|\delta\ln f_{\mathsf P_\alpha,\sigma/\sqrt\alpha}(y)+J_\alpha|\to0,
\qquad
\sup_{|y|\le R}|\delta\ln f_{\mathsf P,\sigma}(y)|\to0.
\tag{103.27}
$$

第二式用同一密度证明的 $\alpha=1$ 情形，此时 $t_1=J_1=0$，不是由 Shannon 熵推得。
代回 (103.10)，分子留下 $-J_\alpha$；除以 $1-\alpha$ 得 (103.4) 的符号与系数。
固定常数乘 $\delta$ 后消失。
全部原输入界分别覆盖 pair/path 且对支持一致；保持奇偶的置换也保持
组计数、中心、标量及输出上确界。未知方向只增加原共同判向事件的失败概率。证毕。

该证明没有从稀有密度上除掉多项式 TV 误差，没有将精确中心误差提前除以噪声，
也没有改动完整观察向量。独立性只用于校准乘积律和显式构造的 Gaussian 比较。
第 102 章的平均信息方差区间不能据此自动推广到本章。
变化阶数、增长输出紧区间、噪声端点与期望熵仍不在结论中。
指数倾斜、Stirling 与 Fourier 局部极限为成熟方法；新增连接是原选中计数模型下的
稀有输出条件矩控制与相对密度回接，归属见 [Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 103 章后续增补区）

## 104. 宏观占据数组的高频作用与线性噪声余量

**定理 104.1（显式线性余量）。** 保持第 102 章的原实验、全部取整、
完整选中计数律、实际中心、二次标量及同一测量残差。以下各信息方差以 nats 的平方计。
令 $a=(1+r)/2$、$b=(1-r)/2$，为避免与第 103 章 Rényi 阶数混淆，
本章以 $\vartheta=\ln(1+r)/[-\ln(1-r)]$ 表示原计数线斜率。置

$$
K_*=\frac1a+\frac{\vartheta^2}{b},\qquad
u_* =\min\left\{1,\sqrt{\frac{c_q}{16K_*}}\right\},\qquad
C_{r,\beta}=\frac{8c_q}{u_*},\qquad
\mathcal B=\frac q{Q^{11/4}}.
\tag{104.1}
$$

这里 $c_q=\phi(1-\beta)/\beta>0$，所有常数只依赖原固定参数。
若确定正噪声序列满足

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\Delta_M=\ln\mathcal B-L_M\ge C_{r,\beta}Q
\quad\text{最终成立},
\tag{104.2}
$$

则第 102 章的完整加权结论仍成立：

$$
\int_{\mathbb R}|D_x(y)-R_*(y)|f_x(y)\,dy\longrightarrow0,
\tag{104.3}
$$

$$
\int V_{{\rm post},x}(y)f_x(y)\,dy-V_{{\rm prior},x}
+\frac{A^2}{\Lambda}-C_xm_x
\longrightarrow\frac8{\sqrt3}-\frac{25}{6}.
\tag{104.4}
$$

其中 $D_x,R_*,f_x,m_x,A,\Lambda,C_x$ 精确保持第 101、102 章的定义；特别是

$$
\Lambda=\nu_0+\sigma_M^2,\quad
C_x=\frac{A^2\kappa_3}{\Lambda^3}-\frac{2A\nu_0}{\Lambda^2},\quad
D_x=V_{{\rm post},x}-V_{{\rm prior},x}+A^2/\Lambda-C_xy,
$$

$$
R_*(y)=\frac{29}{6}-3\sqrt2+
\left(3\sqrt2+\frac8{\sqrt3}-9\right)\frac{y^2}{\nu}.
\tag{104.5}
$$

对每个正容差，上述偏差事件的实际数据概率在全部规定大小的确定支持上取上确界后趋零，
原平稳 pair/path 实验分别成立。积分始终使用先验定义的信道预测密度；
没有把它替换为已知支持下的条件输出律，也没有取无界的原始数据平均。

条件 $\Delta_M/Q\to\infty$ 是 (104.2) 的充分条件。
例如 $\sigma_M=e^{C_{r,\beta}Q}/\mathcal B$ 满足 (104.2)，且
$L_M/Q^3\to c_q$，已超出第 102 章的固定严格指数区间。
$C_{r,\beta}$ 只是一个显式充分常数，未声称最优。

**原率函数提供的坐标。** 以 $\vartheta_Q=P/Q$ 记原 Liouville 有理逼近。
第 68 章在全行截断成功事件上识别完整分数组为

$$
K_M=\{j:k_0+jQ\ge0,\ l_0+jP\ge0,\ k_0+l_0+j(Q+P)\le C_0\lambda\},
\quad u_j=j/Q^2,\quad \lambda=Q^3.
\tag{104.6}
$$

截断只用于估计；在其补事件原后验仍然定义。
已有固定 $C_0$ 满足 $(C_0-1)/(1+\vartheta)>u_++1$，
其中 $u_+>0$ 是 $I(u_+)=c_q$ 的唯一正根。
原率函数为

$$
I(u)=J_a(a+u)+J_b(b+\vartheta u),\qquad
J_c(v)=v\ln(v/c)-v+c,
$$

$$
I(0)=I'(0)=0,\qquad
I''(u)=\frac1{a+u}+\frac{\vartheta^2}{b+\vartheta u}\le K_*
\quad(u\ge0).
\tag{104.7}
$$

所以 $I(u)\le K_*u^2/2$，由 (104.1) 得

$$
\sup_{u\in[u_*,2u_*]}I(u)\le2K_*u_*^2\le c_q/8.
\tag{104.8}
$$

当 $u_*=1$ 时也成立，因为此时 $c_q\ge16K_*$。
严格凸性给 $2u_*<u_+$。因此确定指标集

$$
\mathcal A_M=\{j\in\mathbb Z:u_*\le j/Q^2\le2u_*\},\qquad
|\mathcal A_M|=u_*Q^2+O(1),
\tag{104.9}
$$

最终包含在原完整计数线内，并与固定对数核心 $H$ 不交。
核心指标只有 $O(Q^{1/2}\sqrt{\ln Q})$ 的大小，
而这些指标至少为 $u_*Q^2$。
它们在 (102.8) 的原乘积数组和混合数组中都保留二项分布。

**引理 104.2（实际共同占据事件）。** 在原两种实验中，
对全部确定支持一致地，以趋于一的概率，$\mathcal A_M$ 中每个组同时满足

$$
d_j=C_jp_j(1-p_j)\ge Q^{-C_1}e^{7c_q\lambda/8},\qquad
w_j=d_j/\mathcal B\ge Q^{-C_2}e^{-c_q\lambda/8}.
\tag{104.10}
$$

**证明。** 在全部原数据上定义计数元组的占据数 $C_j$，
不先条件于截断成功。记 (68.27) 的 Poisson 比较均值为 $m_j$。
原全窗口阶乘估计及 (104.8) 给

$$
|\ln m_j-\lambda(c_q-I(u_j))|\le C\ln Q,\qquad
\min_{\mathcal A_M}m_j\ge Q^{-C}e^{7c_q\lambda/8}.
\tag{104.11}
$$

该估计仍保留 $k_0,l_0,M,q$ 的全部取整：若 $\xi=a\lambda-k_0\in[0,1)$，
则 $k_j/\lambda=a+u_j-\xi/\lambda$、
$l_j/\lambda=b+\vartheta_Qu_j+\xi/\lambda$。
在这个固定紧区间，Liouville 误差乘 $\lambda$ 仍可忽略，阶乘余项为 $O(\ln Q)$。
这些只用于估计，没有替换真实计数或中心。

令 $\varepsilon_{\rm row}=C\lambda^3/M$。实际一、二行系数比较给

$$
|\mathbb E_{S_0}C_j-m_j|\le\varepsilon_{\rm row}m_j,\qquad
\operatorname{Var}_{S_0}C_j\le C(m_j+\varepsilon_{\rm row}m_j^2).
\tag{104.12}
$$

path 情形使用原秩二 PGF 的相对系数界，没有假定各行独立。
当 $\varepsilon_{\rm row}<1/4$ 时，Chebyshev 与确定指标集上的并集界给

$$
\sup_{S_0}\mathbb P_{S_0}
\{\exists j\in\mathcal A_M:C_j<m_j/2\}
\le CQ^{C+2}e^{-7c_q\lambda/8}+CQ^2\varepsilon_{\rm row}\to0.
\tag{104.13}
$$

再交原校准及截断事件，$p_j\in[1/4,3/4]$，由
$\ln\mathcal B=c_qQ^3-\tfrac{11}4\ln Q+O(1)$ 得 (104.10)。证毕。

这些远处组的低阶能量总量很小，但高频相位仍能快速变化。
它们的实际占据事件和信息量—能量相关性是同一实现的一部分。
后面的 Fourier 分解只在已支付选中密度误差后的校准乘积律下使用独立性。

**命题 104.3（增长乘积的完整频率预算）。** 以 (102.8) 的同一
$U,U',Y,Y'$ 定义矩密度 $q_k,q'_k$，$k=0,1,2$。
在 (104.2) 及上述共同良好环境下，对每个固定 $N>0$，

$$
\max_{0\le k\le2}
\{\|q_k-q'_k\|_\infty+\|q_k-q'_k\|_1\}\le C_NQ^{-N}
\quad\text{最终成立}.
\tag{104.14}
$$

**证明。** (102.4) 中有一个固定常数 $C_v$，对所有计数参数和实中心一致，
与之后相乘的坐标数无关。第 102 章的分块单峰质量与 Abel 证明正给出这个一致性。
信息量的二次展开每项至多标记两个坐标，单个标记矩一致有界，
项数至多 $CQ^4$。令

$$
n_M=\lfloor u_*Q^2\rfloor-4.
\tag{104.15}
$$

即使删除任意两个标记坐标，$\mathcal A_M$ 仍包含 $n_M$ 个可用二项坐标，
且最终 $u_*Q^2/2\le n_M\le u_*Q^2$。
两个数组均保留它们；不将这些外部信息量视为与输出独立。
同一 $G$ 的零、二、四阶 Fourier 因子仍精确取 (102.13)，
多项式乘 Gaussian 的上界与 $Q$ 无关。

置

$$
H_0=e^{c_q\lambda/4},\qquad
F=\max\{H_0,Q^2/\sigma_M\},\qquad
g=\Delta_M-2\ln Q.
\tag{104.16}
$$

由 (104.2)，最终 $g>0$、$H_0<\mathcal B$，且
$(Q^2/\sigma_M)/\mathcal B=e^{-g}<1$，故 $F<\mathcal B$。
取固定大数 $b_0$，以 $T_Q=Q^{b_0}$ 分开低频。
这里 $b_0$ 只随要求的多项式精度选择，不随 $Q$ 增长。

在 $|t|\le T_Q$，(102.11) 给积分误差
$CQ^2\eta_Q(T_Q+T_Q^2)$，小于任意固定负幂。
在 $T_Q<|t|\le H_0$，预留八个中心坐标，标记后使用六个；
(102.14) 及其 Gaussian 对应界给

$$
\int_{T_Q<|t|\le H_0}(|\widehat q_k|+|\widehat q'_k|)\,dt
\le CQ^4[\mathcal B^{-3}H_0^4+\delta^{-3/2}T_Q^{-2}]
\le Q^Ce^{-2c_q\lambda}+CQ^{19/4-2b_0}.
\tag{104.17}
$$

提高固定 $b_0$ 即可支付这段。

若 $F=H_0$，下一段为空。否则 $F=Q^2/\sigma_M$。
在 $H_0<|t|\le F$，对所有储备坐标，由 (104.10)，

$$
(w_j|t|)^{-1/2}\le Q^Ce^{-c_q\lambda/16}
\le e^{-c_q\lambda/32},\qquad
(|t|/\mathcal B)^{1/2}\le e^{-g/2}.
\tag{104.18}
$$

所以两种矩变换都满足

$$
|\widehat q_k(t)|+|\widehat q'_k(t)|
\le CQ^4[C_v(e^{-g/2}+e^{-c_q\lambda/32})]^{n_M}.
\tag{104.19}
$$

常数的全部增长为显式的 $C_v^{n_M}$，没有把它藏进固定常数。
标记坐标仍取联合相位和信息量的矩，只以绝对矩控制。
由 (104.2)，$g/2\ge4c_qQ/u_*-\ln Q$；
而 $c_q\lambda/32$ 最终也大于这个右侧。因此

$$
n_M\min\{g/2,c_q\lambda/32\}
\ge2c_qQ^3-\tfrac{u_*}2Q^2\ln Q.
\tag{104.20}
$$

区间长度至多 $\mathcal B$，其对数为 $c_qQ^3+O(\ln Q)$；
因子常数只增加 $n_M\ln(2C_v)=O(Q^2)$。于是

$$
\int_{H_0<|t|\le F}(|\widehat q_k|+|\widehat q'_k|)\,dt
\le\exp[-c_qQ^3+O(Q^2\ln Q)]
\le e^{-c_qQ^3/2}
\quad\text{最终成立}.
\tag{104.21}
$$

这里的严格余量使 (104.2) 可以取等号。
$C_v$ 的数值只影响起效位置，不进入显式的 $C_{r,\beta}$；未给出有效起效尺度。

在 $|t|>F$，(102.15) 给尾积分至多

$$
CQ^4\sigma_M^{-1}[1+(\sigma_MF)^5]e^{-(\sigma_MF)^2/4}
\le CQ^4\mathcal B e^{-Q^4/8}
\le\exp[-Q^4/8+c_qQ^3+O(\ln Q)].
\tag{104.22}
$$

使用了 $\sigma_MF\ge Q^2$ 与 $\sigma_M^{-1}\le\mathcal B$。
完整逆噪声由 Gaussian 尾支付，没有乘在选中密度或耦合误差上。
四段覆盖全部频率，亦包含 $F=H_0$ 及任意慢的噪声趋零。

有限正噪声下矩变换可积，Fourier 反演得到 (104.14) 的上确界部分。
(102.9) 的四阶矩不变，因此对 $R\ge1$，

$$
\int_{|y|>R}|q_k(y)|\,dy+
\int_{|y|>R}|q'_k(y)|\,dy\le CQ^2R^{-2}.
\tag{104.23}
$$

在足够大的固定 $Q$ 次幂处截断，内部提高上确界精度，得到 $L^1$ 部分。
所需矩阶保持固定，增长的只是未标记 Fourier 因子的数量。证毕。

**由矩密度回到原信息方差。** 新命题替换第 102 章的固定指数高频预算，
其余接口的适用条件不变。具体地，(102.19) 对条件均值平方作凸截断，
取截断高度 $Q^3$，用 (104.14) 和 $\|U\|_4+\|U'\|_4\le CQ$
支付 $O(Q^{-2})+o(1)$。不要求任何输出密度下界。
原先验方差与混合先验方差相差至多 $CQ\eta_Q$；
质量误差乘 $O(Q^2)$、以及有限系数 $A^2/\Lambda-C_xy$ 的密度变化，
也由任意固定幂精度和直接输出矩界支付。

实际完整选中律先由 (101.15)–(101.16) 支付 $Ca_xQ^2=o_{\mathbb P}(1)$，
Bayes 恒等式将后验信息方差识别为同一 $S_x+G^2/2$ 的条件方差。
这些界不含逆噪声，因此可以在新的余量条件下先作这一步，再使用乘积独立性。

命题 104.3 完成后，外部组仍保留其信息量—能量相关性。
核心联合密度的能量导数积分界 $C\delta^{-1/2}$
把外部能量平移的联合变差界为 $C\delta^{-1}(1+a_x)V_O$。
按 (101.19)–(101.23) 的截断方差传递，先支付这项，之后才精确消去外部先验方差。
两个交错大半核心再相互平滑原非中心线性项与截距。
相应联合变差为 $O_{\mathbb P}(Q^{-9/4})$，
此时目标四阶范数只为 $C\sqrt{|H|}$，故绝对方差误差趋零。
新占据事件没有改变这些核心假设。

因而仍得到 (102.20) 的完整桥梁

$$
\|f_xD_x-g_xD_0\|_1\to0,\qquad
\int(1+y^2)|f_x-g_x|\,dy\to0.
\tag{104.24}
$$

第 101 章参考结论对所有 $0<\sigma_M\le1$、$\sigma_M\to0$ 一致：
其 Gaussian 核心 Fourier 尾在零噪声下仍可积，固定累积量与 Chernoff 界
不使用 $L_M/Q^3$ 的严格上界。因此 $\int g_x|D_0-R_*|\to0$。
与 (104.24) 合并得到 (104.3)。二阶输出矩趋于 $\nu$，
积分 (104.5) 得到 (104.4)。精确均值仍有
$m_x=O_{\mathbb P}(Q^{-5/2})$、$C_xm_x=o_{\mathbb P}(1)$。证毕。

**范围与未解处。** 新增内容是实际宏观占据区间、共同高概率事件及其增长乘积预算。
其充分条件覆盖每个旧固定严格指数序列，也覆盖部分 $L_M/Q^3\to c_q$ 的序列。
它没有证明 $\Delta_M=0$、更小阶余量、最优线性系数或任何必要阈值。
当上述预算不能支付频率区间时，只表示该估计不足，不能推出实际共振或定理为假。
真实经验中心未替换为整数中心，完整选中约束未删去，也未假定公共格距。

所有原参数固定；结论不对变化的 $r,\beta$ 取一致上确界。
良好数据补事件只通过其一致趋零概率处理，未据此控制其上的无界期望。
第 101 章允许的固定核心变更仍只产生 $o_{\mathbb P}(1)$ 积分误差，
不含任意更小核心。有限 $\sigma_M^2$ 继续保留在被放大的系数中。
本章没有自动推广逐输出熵、Rényi 响应、覆盖数或信息谱，也没有零噪声断言。
换成 bits 时，所有信息方差及其修正、极限统一除以 $(\ln2)^2$。
van der Corput、Abel 求和、Fourier 反演和凸截断的文献归属见
[Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 104 章后续增补区）

## 105. 精确噪声鞍点与逐输出 Rényi 熵的二阶响应

**定义 105.1（全数组的有限鞍点）。** 保持第 103 章的原实验、固定幅度、
$\beta\in(1/2,1)$、合法规模与全部取整，沿用其 $\rho,K,\gamma,t_\alpha$ 和
精确 $C_j,p_j,\mu_j,v_j,e_j,V$。原计数后验仍由均匀大小 $q$ 支持先验定义，
输出仍为 $Y=t_x(n)+\sigma_MG$，其中
$t_x(n)=\delta^{-1/2}[\sum_j((n_j-\mu_j)/B)^2-V]$、$\delta=Q^{-1/2}$。
所有熵均以自然对数计。令 $\nu=K''(0)=2\int\rho^2$。

对正阶 $c$ 和方差参数 $u\ge0$，定义使用全部原组的函数

$$
\mathcal F_{c,u}(t)
=-\frac\delta2\sum_j\ln(1-2tv_j/\delta)
+c t\sum_j\frac{e_j^2}{1-2tv_j/\delta}+\frac{cu t^2}{2},
\qquad t<\frac\delta{2\max_jv_j}.
\tag{105.1}
$$

全零数组的右端点取 $+\infty$。置 $u=\sigma_M^2>0$，用

$$
\mathcal F_{c,u}'(\tau_{c,x})=cV,\qquad
s_{c,x}=\mathcal F_{c,u}''(\tau_{c,x})
\tag{105.2}
$$

定义零输出处的精确鞍点及曲率。第二导数严格正；左端导数因噪声项趋负无穷，
右端导数趋正无穷，因此有限数据中该鞍点唯一。
这只是分析量的定义，不把小组计数替换成 Gaussian，也不改变原标量中心。

**定理 105.2（常数阶的输出响应）。** 假设

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q/2.
\tag{105.3}
$$

对每个固定 $\alpha>0$、$\alpha\ne1$ 及有限 $R$，有

$$
\sup_{|y|\le R}\left|
H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
-\frac{\alpha\tau_{\alpha,x}}{\alpha-1}\frac{y}{\sqrt\delta}
-\mathcal B(\alpha)y^2\right|\longrightarrow0,
\tag{105.4}
$$

$$
\mathcal B(\alpha)=
\frac{\alpha^2/K''(t_\alpha)-\alpha/\nu}{2(\alpha-1)}.
\tag{105.5}
$$

收敛在原实际数据概率下，对所有规定大小的确定支持一致，pair/path 分别成立。
固定支持只规定数据采样律，仍评价同一个先验定义的后验。
输出 $y$ 没有平均。特别地，

$$
\sqrt\delta\,[H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)]
\longrightarrow\frac{\alpha t_\alpha}{\alpha-1}y
\tag{105.6}
$$

在同一输出紧区间和概率口径下一致成立。
(105.4) 的放大线性项必须保留有限噪声与经验数据，不能仅由
$\tau_{\alpha,x}\to t_\alpha$ 换成极限常数。

**证明：共同数组界与截断回接。** 以下常数先在紧的正阶区间
$A=[c_-,c_+]\subset(0,\infty)$ 和固定输出紧区间上一致选取。
第 103 章实际占据数、校准与精确中心界给

$$
V\to\gamma,\quad \|e\|_2=O_{\mathbb P}(Q^{-5/2}+q^{-1/2}),
\quad\max_jv_j/\delta\to\rho(0),\quad
\delta\sum_jF(v_j/\delta)\to\int F(\rho(s))\,ds.
\tag{105.7}
$$

末式适用于这里使用的紧的一致 Lipschitz 函数族，且 $F(0)=0$。
固定空间核心含至少 $b_0/\delta$ 个权重在 $[b_1\delta,b_2\delta]$ 的组。
由 $K'$ 严格递增且值域为 $(0,\infty)$，全部阶数的鞍点以高概率位于
固定的内部紧区间，$\tau_{c,x}\to t_c$ 对 $c\in A$ 一致。
这里 $t_c$ 表示阶数 $c$ 的解，不是矩母函数域的右端点。
在该紧区间，$\mathcal F''$ 上下有正常数界，三、四阶导数有界。

为使用第 103 章的实际取整比较，选 $l<c_q/2$ 使最终 $L_M\le lQ^3$，
并选 $\epsilon>0$ 满足 $2\epsilon<c_q-l$。
令 $H=\{j:C_j\ge e^{\epsilon Q^3}\}$，以 $F^H_{c,u}$ 表示 (105.1)
只在两项和中保留 $H$ 的函数；其鞍点目标仍为完整 $cV$。
因为 $0\le\mu_j,C_jp_j\le C_j$ 且组数至多 $CQ^2$，

$$
\sum_{H^c}v_j\le CQ^2e^{\epsilon Q^3}/B^2,\qquad
\sum_{H^c}e_j^2\le CQ^2e^{2\epsilon Q^3}/B^2.
$$

共同分母余量遂给

$$
\|\mathcal F_{c,u}-F^H_{c,u}\|_{C^4}\le d_Q,
\quad d_Q=\operatorname{poly}(Q)e^{-(c_q-2\epsilon)Q^3},
\quad |\tau_{c,x}-\tau^H_{c,x}|\le Cd_Q.
\tag{105.8}
$$

固定多项式阶由至多 $CQ^2$ 组和 $\delta$ 的固定幂产生。
因此任何满足上述条件的固定截断，其放大线性中心都与全数组中心等价。
这不把原观察向量删成 $H$。

**绝对对数精度的倾斜密度。** 对全数组或上述高计数子数组，引入独立标准正态，令

$$
W_{c,u}=\sum_j(\sqrt{v_j}Z_j-\sqrt c\,e_j)^2+\sqrt{c\delta u}\,G,
\qquad z_{c,y}=c(V+\sqrt\delta y).
\tag{105.9}
$$

其缩放累积量函数 $F_{c,u}(t)=\delta\ln\mathbb E e^{tW_{c,u}/\delta}$
恰为相应的 (105.1)。令 $t=t_{c,u}(y)$ 解 $F_{c,u}'(t)=z_{c,y}$，并记
$I_{c,u}(z)=zt-F_{c,u}(t)$。
按 $\exp[tW/\delta-F(t)/\delta]$ 倾斜后，
$(W-F'(t))/\sqrt\delta$ 的特征函数 $\psi_t$ 满足

$$
|\psi_t(\xi)|\le(1+b\delta\xi^2)^{-b'/\delta}.
\tag{105.10}
$$

这是固定核心的平方正态变换乘积；非中心项和附加 Gaussian 因子的模至多一。
取固定小 $b_3>0$，在 $|\xi|\le b_3/\sqrt\delta$ 上，该函数及对应中心
Gaussian 特征函数均由 $e^{-b_4\xi^2}$ 主控。
共同分母余量中的复 Taylor 展开给一个连续解析对数

$$
A_t(\xi):=\ln\psi_t(\xi)
=-\tfrac12F''(t)\xi^2+R_t(\xi),\qquad
|R_t(\xi)|\le C\sqrt\delta|\xi|^3.
$$

写 $B_t=-F''(t)\xi^2/2$。两者实部均不超过 $-b_4\xi^2$，故

$$
|e^{A_t}-e^{B_t}|
\le |A_t-B_t|\int_0^1e^{\operatorname{Re}[(1-s)B_t+sA_t]}\,ds
\le C\sqrt\delta|\xi|^3e^{-b_4\xi^2}.
\tag{105.11}
$$

此界不要求频段边缘的余项绝对值小。
外频段令 $v=\sqrt\delta|\xi|$，利用 (105.10) 的固定正阈值后对数增长界，
积分为 $e^{-b_5/\delta}$ 乘固定多项式。
因此两特征函数的 $L^1$ 距离为 $O(\sqrt\delta)$。
Fourier 反演给倾斜标准化密度在零点等于
$[2\pi F''(t)]^{-1/2}+O(\sqrt\delta)$；首项有正下界，故也是相对误差。
解除倾斜并乘 $dz_{c,y}/dy=c\sqrt\delta$，Gaussian 比较输出密度满足

$$
\ln g_{c,u}(y)
=-I_{c,u}(z_{c,y})/\delta+\ln c
-\tfrac12\ln[2\pi F_{c,u}''(t_{c,u}(y))]
+O_{\mathbb P}(\sqrt\delta).
\tag{105.12}
$$

该误差是未缩放对数的误差。所有界对 $c,y$ 及 $u$ 的小邻域一致；
先约束紧随机量再释放约束，得到所写实际数据概率口径。

**噪声宽度的定量稳定性。** 同一目标 $z$ 下，精确函数差为
$F_{c,u'}(t)-F_{c,u}(t)=c(u'-u)t^2/2$。
曲率下界与鞍点有界给 $|t_{c,u'}-t_{c,u}|\le C|u'-u|$。
在彼此的极值点计算两个 Legendre 上确界，得
$|I_{c,u'}(z)-I_{c,u}(z)|\le C|u'-u|$。
再用三阶导数界控制曲率前因子，(105.12) 给

$$
\sup_{c\in A,|y|\le R}|\ln g_{c,u'}(y)-\ln g_{c,u}(y)|
\le C|u'-u|/\delta+C|u'-u|+O_{\mathbb P}(\sqrt\delta).
\tag{105.13}
$$

第 103 章的整数盒取整及全部小组能量界给
$\Delta_Q\le\operatorname{poly}(Q)[B^{-1}+B^{-2}e^{2\epsilon Q^3}]$。
原核夹逼使用 $s=\sigma/\sqrt c$ 和 $h_c=\Delta_Q\sqrt c/\sigma$，
两宽度为 $s/\sqrt{1\pm h_c}$。由 (105.3) 及上述严格指数余量，

$$
h_c\le\operatorname{poly}(Q)e^{-bQ^3},\qquad
u'_{\pm}=u/(1\pm h_c),\qquad
|u'_{\pm}-u|\le C\sigma^2h_c.
\tag{105.14}
$$

故 $|u'_{\pm}-u|/\delta$ 指数趋零，即使原噪声下降极慢仍成立。
只知道宽度之比趋一不足以支付 (105.12) 中的 $1/\delta$。

**从同一实际计数律返回。** 对 $c\in A$，第 103 章的幂二项 Stirling 估计，
在 $H$ 上的共同盒 $|n_j-C_jp_j|/\sqrt{d_j}\le Q^2$ 内，给计数 escort
与取整正态数组的联合质量比
$1+O(\operatorname{poly}(Q)e^{-\epsilon Q^3/4})$。
两律盒外概率至多 $CQ^2e^{-bQ^4}$；常数对紧正阶区间一致。
核夹逼及 (105.13)–(105.14) 因而控制盒内的绝对对数差。
盒外平滑密度至多 $C\sigma^{-1}Q^2e^{-bQ^4}$，
而 (105.12) 给比较密度下界 $e^{-C/\delta}$。
前者除以后者仍指数趋零；未把多项式 TV 误差除以稀有密度。

实际固定总数修正也保持定量精度。以 $\mathsf Q_x$ 记原校准乘积计数律，
第 103 章的同一稀有输出重加权能量界给

$$
\sup_{c\in A,|y|\le R}
\left|\ln\frac{f_{\mathsf P_{x,c},\sigma/\sqrt c}(y)}
{f_{\mathsf Q_{x,c},\sigma/\sqrt c}(y)}\right|=O_{\mathbb P}(\delta).
\tag{105.15}
$$

其一致性来自幂计数律曲率至少 $2c/C_j$，以及相应方差、均值偏移和
重加权能量均值界在 $A$ 上的一致常数；仍是在实际稀有权重下使用 Jensen。
结合 (105.8) 的鞍点、Legendre 和曲率稳定性，将高数组换为全数组只增加
$Cd_Q/\delta+O_{\mathbb P}(\sqrt\delta)$。最终得到

$$
\sup_{c\in A,|y|\le R}
|\ln f_{\mathsf P_{x,c},\sigma/\sqrt c}(y)-\ln g_{c,\sigma^2}(y)|
=O_{\mathbb P}(\sqrt\delta).
\tag{105.16}
$$

路径行或条件计数向量没有被宣布独立；它们的依赖由原实际输入界和 (105.15) 承担。

**先展开有限 Legendre 函数。** 固定原 $u=\sigma^2$。
精确恒等式 $I'=t$、$I''=1/F''(t)$、$I'''=-F'''(t)/F''(t)^3$ 给

$$
I(cV+c\sqrt\delta y)-I(cV)
=c\tau_c\sqrt\delta y+\frac{c^2\delta y^2}{2s_c}
+O(\delta^{3/2}).
$$

前因子的对数差为 $O(\sqrt\delta)$。
用 (105.12)、(105.16)，得到实际相对密度的未缩放展开

$$
\ell_c(y):=\ln\frac{f_{\mathsf P_{x,c},\sigma/\sqrt c}(y)}
{f_{\mathsf P_{x,c},\sigma/\sqrt c}(0)}
=-\frac{c\tau_c y}{\sqrt\delta}-\frac{c^2y^2}{2s_c}
+O_{\mathbb P}(\sqrt\delta).
\tag{105.17}
$$

这是对有限函数先 Taylor，未对一个已经取极限的率函数误差再除以 $\delta$。
阶数一处 $F_{1,u}'(0)=V+\|e\|^2$，故

$$
\tau_1=O_{\mathbb P}(Q^{-5}),\qquad s_1\to\nu,
\qquad\sup_{|y|\le R}|\ell_1(y)+y^2/(2\nu)|\to0.
\tag{105.18}
$$

第 103 章有限 escort 恒等式在 $y$ 与零处相减，精确给

$$
H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
=\frac{\ell_\alpha(y)-\alpha\ell_1(y)}{1-\alpha}
=\frac{\alpha(\tau_\alpha-\tau_1)}{\alpha-1}\frac{y}{\sqrt\delta}
+\frac{\alpha^2/s_\alpha-\alpha/s_1}{2(\alpha-1)}y^2
+O_{\mathbb P}\!\left(\frac{\sqrt\delta}{|\alpha-1|}\right).
\tag{105.19}
$$

固定阶下，(105.18) 消去普通鞍点的放大项，曲率极限给 (105.4)；
再乘 $\sqrt\delta$ 得 (105.6)。全部输入对原支持一致且 pair/path 分别适用，证毕。

**定理 105.3（趋一阶数的穿孔窗口）。** 设固定正紧区间 $A$ 的内部包含一，
$\eta_Q\downarrow0$ 且 $\sqrt\delta/\eta_Q\to0$。
则 (105.4) 还对 $\alpha\in A$、$|\alpha-1|\ge\eta_Q$ 一致成立，
仍保留该阶数的精确有限噪声鞍点。

证明不能只把曲率的一致收敛除以 $\alpha-1$。
写 $F_{c,u}(t)=C_x(t)+cD_x(t)$，其中

$$
D_x(t)=t\sum_j\frac{e_j^2}{1-2tv_j/\delta}+\tfrac12ut^2.
$$

在共同紧域上 $C_x\to K$、$D_x\to0$ 于 $C^4$ 范数成立。
对精确有限鞍点方程微分得

$$
\partial_c\tau_c=\frac{V-D_x'(\tau_c)}{s_c},\qquad
\partial_cs_c=D_x''(\tau_c)+F_{c,u}'''(\tau_c)\partial_c\tau_c.
\tag{105.20}
$$

因此 $N_x(c)=c^2/s_c-c/s_1$ 于 $C^1(A)$ 收敛到
$N(c)=c^2/K''(t_c)-c/\nu$，且两者在一处严格等于零。
恒等式

$$
\frac{N_x(c)}{c-1}=\int_0^1N_x'(1+s(c-1))\,ds
\tag{105.21}
$$

给相应差商的一致收敛，无需经验环境的收敛速率。
(105.19) 的余项除以 $\eta_Q$ 后趋零，
普通鞍点遗漏项至多 $O_{\mathbb P}(Q^{-5}/(\eta_Q\sqrt\delta))\to0$，证毕。
连续延拓的二次系数为

$$
\mathcal B(1)=\frac1{2\nu}-\frac{\gamma K'''(0)}{2\nu^3}.
\tag{105.22}
$$

例如 $\eta_Q=\delta^{1/4}$ 可用。该窗口不含阶数一，也不含
$|\alpha-1|=O(\sqrt\delta)$ 的全部序列。
有限纤维上 Shannon 响应需要
$H_1(\mathsf P_x^y)-H_1(\mathsf P_x^0)=\ell_1(y)-\partial_c\ell_c(y)|_{c=1}$。
(105.16) 的一致函数值误差不控制其阶数导数；显式 Gaussian 累积量函数可微
也不补出实际比较误差的导数界。本章不据此声称 Shannon 响应定理。

**命题 105.4（删除有限噪声的实际反例）。** 固定 $\alpha\ne1$，以
$\tau_\alpha(u)$ 记 (105.2) 在方差 $u$ 处的解。
在共同内部紧域，隐函数微分和有界高阶导数给

$$
\frac{d\tau_\alpha(u)}{du}
=-\frac{\alpha\tau_\alpha(u)}{F_{\alpha,u}''(\tau_\alpha(u))},
\qquad
\frac{\tau_\alpha(u)-\tau_\alpha(0)}u
\longrightarrow-\frac{\alpha t_\alpha}{K''(t_\alpha)}.
\tag{105.23}
$$

有限无噪声鞍点在这些概率趋一的事件上存在，右侧非零。
取原模型允许的 $\sigma_M=\delta^{1/8}$，即 $u=\delta^{1/4}$；
它满足 (105.3)，但 $u/\sqrt\delta=\delta^{-1/4}\to\infty$。
若在 (105.4) 中把中心换为 $\tau_\alpha(0)$，所得残差对固定 $y\ne0$ 满足

$$
\delta^{1/4}\left[
H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
-\frac{\alpha\tau_\alpha(0)}{\alpha-1}\frac y{\sqrt\delta}
-\mathcal B(\alpha)y^2\right]
\longrightarrow-\frac{\alpha^2t_\alpha y}{(\alpha-1)K''(t_\alpha)}\ne0.
\tag{105.24}
$$

这是原实际计数信道的结论，直接由 (105.4) 和 (105.23) 得到，非仅 Gaussian 代理的反例。
它排除删除噪声项的简化，不否定保留精确中心的定理。

本章不提供无穷阶端点、增长输出区间、期望熵、全局原始数据平均或噪声端点结论。
指数倾斜、相对鞍点方法和 Legendre 演算是经典工具；新增连接是原完整计数模型中的
绝对对数误差、噪声宽度支付、精确有限中心及穿孔阶数窗口。
文献的适用条件与未接通的 Shannon 导数义务见
[Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 105 章后续增补区）

## 106. 二次共振的积分宽度与双重对数噪声余量

**定理 106.1（积分平滑后的完整信息方差）。** 保持第 101、102、104 章的
原实际 pair/path 实验、固定参数、全部取整、完整计数后验、精确中心及同一测量残差。
置

$$
\mathcal B=q/Q^{11/4}=B^2\sqrt\delta,\quad
L_M=\ln(1/\sigma_M),\quad\Delta_M=\ln\mathcal B-L_M,
\qquad\delta=Q^{-1/2}.
$$

若确定正噪声满足

$$
L_M\to\infty,\qquad e^{2\Delta_M}/\ln Q\to\infty,
\tag{106.1}
$$

则仍有完整的原信道加权结论

$$
\int|D_x(y)-R_*(y)|f_x(y)\,dy\to0,
\tag{106.2}
$$

$$
\int V_{{\rm post},x}(y)f_x(y)\,dy-V_{{\rm prior},x}
+A^2/\Lambda-C_xm_x\to\frac8{\sqrt3}-\frac{25}{6}.
\tag{106.3}
$$

这里精确保持 (104.5) 的 $D_x,R_*$、原 $m_x=\mathbb E_xY$ 及有限系数

$$
A=V_H/\sqrt\delta,\quad\nu_0=2\sum_Hw_j^2,\quad
\kappa_3=8\sum_Hw_j^3,\quad\Lambda=\nu_0+\sigma_M^2,\quad
C_x=A^2\kappa_3/\Lambda^3-2A\nu_0/\Lambda^2.
\tag{106.4}
$$

核心 $H$ 仍是 (100.2) 的固定容许对数核心，$w_j=d_j/\mathcal B$。
信息方差以 nats 的平方计。收敛在原实际数据概率下，对所有规定大小的确定支持一致，
两种实验分别成立。积分始终使用同一先验定义的预测密度，不替换为已知支持的条件输出律。

(106.1) 等价于 $\Delta_M-\tfrac12\ln\ln Q\to\infty$。
例如 $\Delta_M=\ln\ln Q$ 满足它，却不满足任何固定正 $C$ 的
$\Delta_M\ge CQ$。本定理扩大第 104 章的充分区间，未声称任意
$\Delta_M\to\infty$ 均可用，也未声称这个新阈值必要。

**证明：同一实际数组上的接口。** 沿用第 102 章校准乘积律 $\mathsf Q_x$、
选中密度 $\mathsf P_x=\mathscr L_x\mathsf Q_x$、同一量化扩展和同一 $G$。
已有完整选中比较为

$$
0\le\mathscr L_x\le C,\quad
\varepsilon_x:=\|\mathscr L_x-1\|_{2,\mathsf Q}=O_{\mathbb P}(Q^{-5/2}),
\quad \mathbb E_{\mathsf P}(\ln\mathscr L_x)^2\le C\varepsilon_x^2.
\tag{106.5}
$$

固定核心外的实际方差尾满足 $V_O\le Q^{-200}$。
其较小中心区间 $|j\delta|\le1$ 同时含至少 $c/\delta$ 个原坐标，满足

$$
c\delta\le v_j\le C\delta,\qquad
c\mathcal D\le d_j\le C\mathcal D,
\qquad\mathcal D:=\mathcal B\sqrt\delta.
\tag{106.6}
$$

这是 (102.7) 后原中心剖面与共同占据事件的直接应用：原一、二行相对 PGF 系数，
结合多项式个坐标的并集界给同时事件，path 行无需独立。
该事件足以选择 $\lceil\ln Q\rceil+22$ 个坐标；未另加经验中心的算术假设。

以 $s_{\mathsf Q}$ 表示乘积律的中心信息量，保持 (102.8) 的

$$
U=s_{\mathsf Q}+G^2/2,\quad
U'=\tfrac12\sum_H(Z_j^2-1)+\sum_{H^c}s_j+G^2/2,
\quad Y=T+\sigma G,\quad Y'=T'+\sigma G.
$$

其中 $T'$ 仅在同一耦合中将核心电荷替换为 Gaussian，外部计数、外部信息量及其相关性全部保留。
记 $q_k(y)dy=\mathbb E_{\mathsf Q}[U^k;Y\in dy]$，$q'_k$ 相应定义，$k=0,1,2$。
(102.9)、(102.11) 的噪声无关低频和矩界为

$$
|\widehat q_k(t)-\widehat q'_k(t)|
\le CQ^2\eta_Q(1+|t|),\quad
\eta_Q=Q^{C_*}e^{-c_qQ^3/36},
$$

$$
\|U\|_4+\|U'\|_4\le CQ,\qquad
\mathbb E Y^4+\mathbb E(Y')^4\le C.
\tag{106.7}
$$

下面只更换高频积分估计，不改原参考信息方差。

**任意实线性项的离散 Gaussian 包络。** 对 $K\sim\operatorname{Bin}(n,p)$、
$p\in[1/4,3/4]$，令 $d=np(1-p)$、$m=np$，并在 $\mathbb Z$ 上定义归一化质量
$g_{m,d}(k)\propto e^{-(k-m)^2/(2d)}$。
经典一致 Stirling 估计在 $|k-m|\le d^{5/8}$ 内给对数相对误差 $O(d^{-1/8})$：
立方余项为 $O(|k-m|^3/n^2)$，对数前因子余项更小。
两侧尾质量均为 $O(e^{-cd^{1/4}})$，Poisson 求和给归一化常数
$\sqrt{2\pi d}[1+O(e^{-2\pi^2d})]$，对任意实 $m$ 一致。因此

$$
\sum_{k\in\mathbb Z}|\Pr(K=k)-g_{m,d}(k)|\le Cd^{-1/8}.
\tag{106.8}
$$

这只用于逐因子特征函数，误差没有直接乘逆噪声。

写 $\theta=p_0/k+\tau$，$(p_0,k)=1$。经典有限二次 Fourier 分解为

$$
e^{2\pi i p_0\ell^2/k}=\sum_{h=0}^{k-1}c_he^{2\pi ih\ell/k},
\qquad |c_h|\le\sqrt{2/k}.
$$

确实，分子 Gauss 和的模平方中令 $u=v-w$，内层求和只在 $k\mid2u$ 时非零，
至多两个余数，每项模至多 $k$。这也覆盖偶分母。
对每个 Gaussian 项 Poisson 求和并完成平方，再对间距 $1/k$ 的对偶网格求和，得到

$$
\left|\sum_\ell g_{m,d}(\ell)e^{2\pi i\theta\ell^2+ib\ell}\right|
\le C\left[k^{-1/2}(1+d^2\tau^2)^{-1/4}
+k^{1/2}d^{-1/2}(1+d^2\tau^2)^{1/4}\right].
\tag{106.9}
$$

所用网格界为
$\sum_{\ell\in\mathbb Z}e^{-cd(\ell/k-\zeta)^2/(1+d^2\tau^2)}
\le C[1+k\sqrt{1+d^2\tau^2}/\sqrt d]$，对全部实 $\zeta$ 一致。
故 (106.9) 对 $m,b$ 任意取实数都一致；原 $(K-\mu)^2$ 的中心只给
$b=-4\pi\theta\mu$，不要求 $\mu$ 有理。

取 $J=\lfloor\sqrt{\mathcal D}\rfloor$。
Dirichlet 抽屉逼近给每个 $\theta$ 一个既约 $p_0/k$，使
$k\le J$、$|\tau|\le1/(kJ)$。
对 (106.6) 的所有组，(106.9) 第二项至多 $C\mathcal D^{-1/4}$，于是

$$
|\mathbb E e^{2\pi i\theta(K-\mu)^2}|
\le C_0[k^{-1/2}(1+\mathcal D^2\tau^2)^{-1/4}
+\mathcal D^{-1/8}].
\tag{106.10}
$$

$C_0$ 固定，不依赖频率、经验中心或之后的因子个数。

**积分有理峰的宽度。** 对 $n$ 个原中心坐标，使用同一个 $\theta$ 及同一个逼近。
由 $(x+y)^n\le2^{n-1}(x^n+y^n)$，其模乘积由下列一周期函数主控：

$$
P_{\mathcal D,n}(\theta)=C_1^n\left[\mathcal D^{-n/8}
+\sum_{k\le J}\ \sum_{\substack{p_0\in\mathbb Z,\ (p_0,k)=1\\
|\theta-p_0/k|\le1/(kJ)}}
k^{-n/2}[1+\mathcal D^2(\theta-p_0/k)^2]^{-n/4}\right].
\tag{106.11}
$$

原实中心的特征函数模未必周期；只有这个对实线性项一致的上包络周期。
对所有整数 $n\ge8$，逐峰在整条实轴积分给

$$
\int_0^1P_{\mathcal D,n}(\theta)d\theta
\le C_2^n(\mathcal D^{-1}+\mathcal D^{-n/8}).
\tag{106.12}
$$

因为每峰积分至多 $C\mathcal D^{-1}k^{-n/2}$，每周期分子数至多 $Ck$，
而 $\sum_{k\ge1}k^{1-n/2}$ 一致有界。所有固定常数均可吸收入 $C_2^n$。
特别地，16 个未标记因子的每周期积分至多 $C/\mathcal D$。

若 $0<h<a_0<1/8$、$\mathcal D h\ge1$，则还可分别估计原点峰和非零分子峰：

$$
\int_h^{a_0}P_{\mathcal D,n}(\theta)d\theta
\le C_3^n\left[a_0\mathcal D^{-n/8}
+\mathcal D^{-1}\{(\mathcal D h)^{1-n/2}+a_0^{n/2-2}\}\right].
\tag{106.13}
$$

原点峰只有 $p_0=0,k=1$，从 $h$ 起积分幂尾。
任何触及 $[h,a_0]$ 的非零峰有正分子，且
$p_0/k\le a_0+1/(kJ)$，故 $k\ge1/(2a_0)$。
把相应整峰积分求和即得第二项；重叠只造成正的上界。
负频率用反射处理。

**最多两个信息矩标记。** 展开 $U^k$ 时每项至多标记两个计数坐标，
总项数至多 $CQ^4$。各标记联合变换以对应绝对中心信息矩控制；
只对未标记坐标用 (106.11)。同一 $G$ 的三个因子精确为

$$
e^{-\sigma^2t^2/2},\quad
(1-\sigma^2t^2)e^{-\sigma^2t^2/2},\quad
(3-6\sigma^2t^2+\sigma^4t^4)e^{-\sigma^2t^2/2}.
$$

因此

$$
|\widehat q_k(t)|\le CQ^4P_{\mathcal D,n}(t/(2\pi\mathcal B))
[1+(\sigma t)^4]e^{-\sigma^2t^2/2},\qquad k\le2.
\tag{106.14}
$$

这里没有把测量残差在后验下重新抽样或假定它仍独立。

**三个频段的共同预算。** 令

$$
g_Q=\Delta_M-\tfrac12\ln\ln Q\to\infty,\quad
r_Q=\min(g_Q,\sqrt{\ln Q}),\quad a_0=e^{-r_Q/2},
\quad n_Q=\lceil\ln Q\rceil+20,
$$

$$
T_Q=Q^2,\quad h_Q=T_Q/(2\pi\mathcal B),\quad
\mathcal D h_Q=Q^{7/4}/(2\pi),\quad\mathcal B/\mathcal D=Q^{1/4}.
\tag{106.15}
$$

原中心坐标的同时界供应 $n_Q+2$ 个坐标，删除任意两个标记后仍够。
低频 $|t|\le T_Q$ 用 (106.7)，变换差积分指数小。
中频 $T_Q<|t|\le2\pi\mathcal B a_0$ 用 (106.13)–(106.14)，积分至多

$$
CQ^4C_3^{n_Q}\left[\mathcal B a_0\mathcal D^{-n_Q/8}
+Q^{1/4}\{(Q^{7/4}/(2\pi))^{1-n_Q/2}+a_0^{n_Q/2-2}\}\right].
\tag{106.16}
$$

三项对数分别不超过 $-cQ^3\ln Q$、
$-\tfrac78(\ln Q)^2+O(\ln Q)$ 和
$-\tfrac14r_Q\ln Q+O(\ln Q+r_Q)$，故均小于任意固定负幂。
这显式支付了增长乘积的 $C_3^{n_Q}$。

全部远频 $|t|>2\pi\mathcal B a_0$ 改用固定 16 个未标记因子。
令 $s=2\pi\sigma\mathcal B=2\pi e^{\Delta_M}$，将 $\theta$ 轴逐单位区间分解。
每段包络积分至多 $C/\mathcal D$，而 Gaussian 权重的段上确界之和至多
$C e^{-cs^2a_0^2}$。首段从 $a_0$ 起，随后段的 Gaussian 和有一致常数界。
故

$$
\int_{|t|>2\pi\mathcal B a_0}|\widehat q_k(t)|dt
\le CQ^{17/4}e^{-c e^{2\Delta_M}a_0^2}.
\tag{106.17}
$$

变量替换产生的 $\mathcal B$ 被每周期成本 $1/\mathcal D$ 抵消，只剩 $Q^{1/4}$。
并且 $e^{2\Delta_M}a_0^2=(\ln Q)e^{2g_Q-r_Q}\ge(\ln Q)e^{g_Q}$，
所以此界也小于任意固定负幂。
它覆盖所有整数与有理共振及 $|t|>\mathcal B$，未要求 $Q^2/\sigma<\mathcal B$。

混合数组的未标记核心 Gaussian 因子满足
$|\mathbb E e^{itw_j(Z_j-e_j/\sqrt{v_j})^2}|
\le(1+4t^2w_j^2)^{-1/4}\le C\delta^{-1/4}|t|^{-1/2}$。
同取 $n_Q$ 个因子，$|t|>T_Q$ 上的矩变换积分至多

$$
CQ^4 C^{n_Q}\delta^{-n_Q/4}
\frac{T_Q^{1-n_Q/2}}{n_Q/2-1},
$$

其对数为 $-\tfrac78(\ln Q)^2+O(\ln Q)$。外部因子保留相关性，只用模至多一。
综上，对每个固定 $N$，

$$
\max_{k\le2}\int_{\mathbb R}|\widehat q_k-\widehat q'_k|dt
\le C_NQ^{-N}.
\tag{106.18}
$$

**从有限有符号密度到实际方差。** 每个有限正噪声下变换均可积，Fourier 反演给
$q_k-q'_k$ 的同阶一致界。由 (106.7) 和 Cauchy–Schwarz，

$$
\int_{|y|>R}(|q_k|+|q'_k|)dy\le CQ^2R^{-2}.
$$

令 $R$ 为足够高的固定 $Q$ 次幂，再在 (106.18) 选择足够高的固定 $N$，得到
对任意固定 $N$ 都有
$\max_{k\le2}(\|q_k-q'_k\|_1+\|q_k-q'_k\|_\infty)\le C_NQ^{-N}$。

条件方差密度是 $\mathcal V_U=q_2-q_1^2/q_0$。
(102.19) 的凸截断不等式在所有输出上给

$$
\|\mathcal V_U-\mathcal V_{U'}\|_1
\le\epsilon_2+2b\epsilon_1+b^2\epsilon_0
+(\mathbb E|U|^4+\mathbb E|U'|^4)/b^2,
\quad\epsilon_k=\|q_k-q'_k\|_1.
\tag{106.19}
$$

取 $b=Q^3$ 后误差趋零，包括任意小密度输出。
先验方差先中心化再比较，量化耦合给
$|V_{\mathsf Q}-V'_{\mathsf Q}|\le CQ\eta_Q$；
$V_{\mathsf Q}=O(Q^2)$ 乘密度误差也趋零。
$A^2/\Lambda=O(\delta^{-1})$、$C_x=O(\delta^{-1/2})$，
利用直接二阶输出矩和上述任意幂 $L^1$ 界，有限系数项同样可传递。

剩余回接严格使用第 101、102 章不含逆噪声的界。
完整选中律及实际信息量的改变成本为 $C\varepsilon_xQ^2=o_{\mathbb P}(1)$。
对外部计数及同一 $G$ 条件化，核心二维密度的能量导数范数至多 $C\delta^{-1/2}$，
实际外部能量的一阶矩至多 $C\delta^{-1/2}(1+\varepsilon_x)V_O$，
故联合变差成本为 $O(Q^{-199.5})$；外部信息量与能量的相关性在这一步保留。
用 (101.9) 的联合变差截断，取截断值 $Q^{10}$、四阶范数 $O(Q)$，误差趋零。
此后外部信息方差才与原先验中心项精确抵消。

原非中心电荷及截距的联合变差成本至多
$C\delta^{-1/2}\varepsilon_x=O_{\mathbb P}(Q^{-9/4})$。
外部已抵消，剩余四阶范数为 $O(\sqrt{|H|})$；取截断值 $Q$，
所得方差成本为 $O_{\mathbb P}(Q^{-1/4}[1+(\ln Q)^{3/4}])=o_{\mathbb P}(1)$。
这些中心和截距误差都未除以 $\sigma$。
同一 128 坐标联合平滑储备保持原假设；高频选择只是对同一数组的另一估计，不消耗坐标。

因此，以 $g_x,D_0$ 记原中心 Gaussian 核心参考量，得到

$$
\|f_xD_x-g_xD_0\|_1\to0,\qquad
\int(1+y^2)|f_x-g_x|dy\to0.
\tag{106.20}
$$

第二式还用直接四阶输出矩，未从 TV 单独转移无界矩。
(101.31) 的全局参考结论对所有趋零 $\sigma\in(0,1]$ 一致：
其已证幂和、核心块、Fourier 导数和 Chernoff 尾界没有逆噪声条件。
于是 $\int g_x|D_0-R_*|\to0$。
三角不等式结合 $R_*$ 为固定二次式，给 (106.2)；
$\mathbb E_{g_x}Y^2=\Lambda\to\nu$ 再给 (106.3)。证毕。

**剩余的小余量问题。** 本证明在 $e^{2\Delta_M}/\ln Q$ 有界时没有支付
(106.17) 中的多项式前因子。增长因子数控制大分母峰，但固定小分母峰的两个矩标记
仍以绝对值处理。对真实经验中心证明额外算术衰减，或在
$q_2-q_1^2/q_0-V_{\mathsf Q}q_0$ 中证明共同别名项抵消，均是尚缺的义务。
$\Delta_M=\tfrac14\ln\ln Q$ 是未覆盖的合法序列，不是实际模型反例。
整数中心的玩具数组也不能替代原数据概率下的反例。
本章不给阈值必要性、零噪声、全局原始数据期望或其他后验泛函的自动推广。
经典 theta、Gauss 和及有理峰积分的归属见
[Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 106 章后续增补区）

## 107. 最大后验原子的能量成本与无穷阶熵

**定义 107.1（逐输出的最小熵）。** 保持第 103、105 章原幅度、
固定 $\beta\in(1/2,1)$、全部合法规模与取整，使用原完整计数后验
$\mathsf P_x$ 及同一输出 $Y=T+\sigma_MG$ 后的 $\mathsf P_x^y$。
对有限计数律定义 $H_\infty(P)=-\ln\max_nP(n)$，单位为 nats。
这是一份指定输出下的分布的熵，不是对输出平均最佳猜测概率后取负对数。
仍记

$$
E(n)=\sum_j[(n_j-\mu_j)/B]^2,\quad
T(n)=\delta^{-1/2}[E(n)-V],\quad
v_* =\max_jv_j,\quad\rho_0=\rho(0),\quad
c_\infty=\frac{\gamma}{2\rho_0}=\sqrt{\frac\pi{2\kappa}}.
\tag{107.1}
$$

全部 $\mu_j,V,v_j,\rho,\gamma,\kappa$ 保持 (103.2)、(103.5) 的精确定义。

**定理 107.2（实际最小熵端点）。** 若

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q/2,
\tag{107.2}
$$

则对每个固定有限 $R$，

$$
\sup_{|y|\le R}\left|
\delta[H_\infty(\mathsf P_x^y)-H_\infty(\mathsf P_x)+L_M]
-c_\infty\right|\to0.
\tag{107.3}
$$

收敛在原实际数据概率下，对全部规定大小的确定支持一致，原 pair/path 分别成立。
固定支持采样仍评价原均匀支持先验定义的后验，输出没有平均。
本定理直接计算最大原子，不从固定阶结果交换 $\alpha\to\infty$ 与规模极限。

**证明：有限约束极小值。** 写 $P_* =\max_n\mathsf P_x(n)$、
$S_P(n)=\ln[P_*/\mathsf P_x(n)]\ge0$、$h_y=V+\sqrt\delta y$、$u=\sigma^2$。
在原全盒支持事件上，定义完整可行计数元组上的极小值

$$
A_x(y)=\min_n\left[S_P(n)+\frac{(E(n)-h_y)^2}{2\delta u}\right].
\tag{107.4}
$$

精确 Bayes 公式给

$$
H_\infty(\mathsf P_x^y)-H_\infty(\mathsf P_x)+L_M
=A_x(y)+\tfrac12\ln(2\pi)+\ln f_{\mathsf P_x,\sigma}(y).
\tag{107.5}
$$

第 103 章的普通阶密度结论 (103.27) 已给
$\sup_{|y|\le R}|\delta\ln f_{\mathsf P_x,\sigma}(y)|\to0$，
所以只需证明 $\delta A_x(y)\to c_\infty$ 一致成立。
大基准计数熵在 (107.5) 中严格抵消，无需另估先验最小熵。

**对所有元组成立的离散曲率。** 对二项质量 $b_N(k)$，取任一众数 $k^\circ$。
当 $N\ge2$，相邻对数比

$$
a_k=\ln\frac{b_N(k)}{b_N(k+1)}
=\ln\frac{k+1}{N-k}-\ln\frac p{1-p}
$$

满足

$$
a_{k+1}-a_k
\ge\frac1{k+2}+\frac1{N-k}\ge\frac4{N+2}.
$$

首个不等式用 $\ln(1+x)\ge x/(1+x)$。
在众数两侧累加，从众数处相应符号的起始增量得到

$$
\ln\frac{b_N(k^\circ)}{b_N(k)}
\ge\frac2{N+2}\ell(\ell-1),\qquad\ell=|k-k^\circ|.
\tag{107.6}
$$

$N=0,1$ 直接成立，也覆盖众数并列。
对原乘积计数律 $\mathsf Q_x$，令 $k^\circ=(k_j^\circ)$ 为众数向量，
$Q_* =\mathsf Q_x(k^\circ)$，组数为 $m\le CQ^2$，$C_{\max}=\max C_j$。
每个众数信息量非负，故 (107.6) 与 Cauchy–Schwarz 给全盒上的界

$$
S_Q(n):=\ln\frac{Q_*}{\mathsf Q_x(n)}
\ge\frac2{C_{\max}+2}(\|n-k^\circ\|_2-\sqrt m)_+^2.
\tag{107.7}
$$

当范数不小于 $\sqrt m$，使用
$r^2-\sqrt m r\ge(r-\sqrt m)^2$；较小时只用非负性。
这保留了向量误差，没有减掉会淹没目标尺度的 $O(m)$ 常数。
众数满足 $|k_j^\circ-C_jp_j|\le1$，因此

$$
\delta S_Q(n)\ge a_x(\sqrt{E(n)}-b_x)_+^2,\quad
 a_x=\frac{2B^2\delta}{C_{\max}+2},\quad
 b_x=\|e\|_2+2\sqrt m/B.
\tag{107.8}
$$

原校准近半及 (103.8) 的最大权重界给

$$
C_{\max}/(B^2\delta)\to4\rho_0,\qquad
 a_x\to(2\rho_0)^{-1},\qquad b_x\to0.
\tag{107.9}
$$

这里使用的是原实际数据的最大值估计，非仅一个标量中心极限定理。

**原先验最大值的双向比较。** 写原选择修正
$\mathsf P_x(n)=\mathcal L_x(\sum n_j)\mathsf Q_x(n)$，
$D(n)=\sum_j(n_j-C_jp_j)$。沿用 (103.11) 的两侧界。
在众数向量有 $|D(k^\circ)|\le m$，故令

$$
\ell_Q=C(m^2/q+q^{-1/2}),\quad
u_Q=C(B^2V/q+q^{-1/2}),
$$

即得 $-\ell_Q\le\ln(P_*/Q_*)\le u_Q$，两者都趋零。
因此对全部原元组，

$$
S_P(n)\ge S_Q(n)-\ell_Q-u_Q,
\tag{107.10}
$$

而指定元组可用上界

$$
S_P(n)\le S_Q(n)+u_Q+C(D(n)^2/q+q^{-1/2}).
\tag{107.11}
$$

并未把 $\mathcal L_x$ 在极远元组上的下界错当成统一正常数。

**达到成本的可行整数构造。** 按固定规则选 $j_*$ 使 $v_{j_*}=v_*$，
其余坐标保持众数。精确背景能量

$$
E_0=\sum_{j\ne j_*}(k_j^\circ-\mu_j)^2/B^2
\le(\|e\|_2+\sqrt m/B)^2=o_{\mathbb P}(1).
$$

在概率趋一的共同事件上，所有紧输出均有 $h_y-E_0$ 正且远离零。
令 $n_{j_*}$ 为 $\mu_{j_*}+B\sqrt{h_y-E_0}$ 的最近整数，其他坐标为 $k_j^\circ$。
由 $C_{j_*}\asymp B^2\delta$、$p_{j_*}\to1/2$、$\|e\|_2\to0$，
改动为 $O(B)$ 而 $C_{j_*}/B\asymp B\delta\to\infty$，故该整数严格位于计数范围内。
原全盒支持保证它属于同一大小 $q$ 先验的可行元组。
取整误差满足

$$
|E(n(y))-h_y|\le C/B,\qquad
|T(n(y))-y|\le C/(B\sqrt\delta),\qquad
(B\sqrt\delta\sigma)^{-1}\to0.
\tag{107.12}
$$

最后一式由 (107.2) 的严格半指数余量成立，故原 Gaussian 惩罚本身趋零。

只有最大权重坐标支付乘积众数信息量。在该坐标，标准化偏移
$z=(n_{j_*}-C_{j_*}p_{j_*})/\sqrt{d_{j_*}}=O_{\mathbb P}(\delta^{-1/2})$
只有多项式大小，而 $C_{j_*}$ 指数大。
第 103 章一致 Stirling 余项 $O((1+|z|^3)/\sqrt{C_{j_*}})$ 因而趋零，给

$$
\delta S_Q(n(y))
=\frac{[\sqrt{h_y-E_0}+e_{j_*}+O(B^{-1})]^2}{2(v_*/\delta)}
+o_{\mathbb P}(1)\to c_\infty
\tag{107.13}
$$

一致成立。该元组的 $|D(n(y))|\le CB+m$，从而
$D(n(y))^2/q\le C Q^{-5/2}+Cm^2/q=o(1)$。
用 (107.11)–(107.13)，得到 $\sup_{|y|\le R}\delta A_x(y)\le c_\infty+o_{\mathbb P}(1)$。

**所有极小元组的下界。** 对 (107.4) 的任一极小元组 $n_y$，
$S_P\ge0$ 及刚证明的上界给
$(E(n_y)-h_y)^2/(2u)\le C$，故
$|E(n_y)-h_y|\le C'\sigma$。
因此 $E(n_y)\to\gamma$，对紧输出及所有极小元组一致。
现在才舍去非负惩罚，并用 (107.8)–(107.10)，得到

$$
\delta A_x(y)\ge a_x(\sqrt{E(n_y)}-b_x)_+^2-o_{\mathbb P}(1)
=c_\infty-o_{\mathbb P}(1).
\tag{107.14}
$$

这覆盖任意合法慢降噪序列，未在定位极小能量之前删除有限噪声。
结合上界与 (107.5) 即证 (107.3)。所有共同事件保留原支持一致及 pair/path 范围。证毕。

**定理 107.3（受控增长阶数）。** 在 (107.2) 下，对每个确定序列
$a_Q\to\infty$、$a_Q\le\ln Q$，有

$$
\sup_{\substack{a_Q\le\alpha\le\ln Q\\|y|\le R}}
\left|\delta[H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x)+L_M]
-c_\infty\right|\to0
\tag{107.15}
$$

于同一实际数据概率和支持口径成立。上限 $\ln Q$ 是充分范围，不声称最优。

**证明：不用边界鞍点的密度界。** 选 $l<c_q/2$ 使最终 $L_M\le lQ^3$，
选 $\epsilon>0$ 满足 $2\epsilon<c_q-l$，只为证明划分
$H=\{j:C_j\ge e^{\epsilon Q^3}\}$，保留完整 $V$。
这里的 $H$ 是本证明的高计数组，不是第 106 章对数核心。
以 $g_{\alpha,\sigma'}$ 表示

$$
\delta^{-1/2}\left[\sum_H(\sqrt{v_j/\alpha}Z_j-e_j)^2-V\right]
+\frac{\sigma'}{\sqrt\alpha}G
\tag{107.16}
$$

的密度，$\sigma'$ 允许核夹逼所需的邻近宽度。
其能量乘 $\alpha$ 后的缩放累积量函数是

$$
F_{\alpha,x}(t)=C_x^{G}(t)+\alpha D_{x,\sigma'}^{G}(t),
\quad C_x^{G}(t)=-\frac\delta2\sum_H\ln(1-2tv_j/\delta),
$$

$$
D_{x,\sigma'}^{G}(t)=t\sum_H\frac{e_j^2}{1-2tv_j/\delta}
+\tfrac12(\sigma')^2t^2.
\tag{107.17}
$$

上标仅避免与信息方差系数 $C_x$ 混淆。
任取固定 $0<t<t_c=1/(2\rho_0)$，共同分母余量给
$C_x^{G}(t)=O_{\mathbb P}(1)$、$D_{x,\sigma'}^{G}(t)\to0$。
倾斜后标准化能量的特征函数模由
$(1+b\delta\xi^2)^{-b'/\delta}$ 主控，常数不依赖 $\alpha$：
非中心因子即使带 $\sqrt\alpha e_j$，其模仍至多一。
该包络积分一致有界，故倾斜标准化密度处处有界。
在目标能量 $\alpha h_y$ 处解除倾斜，得到

$$
g_{\alpha,\sigma'}(y)
\le C\alpha\exp\left[-\frac{\alpha h_y t-C_x^{G}(t)
-\alpha D_{x,\sigma'}^{G}(t)}\delta\right].
\tag{107.18}
$$

乘对数以 $\delta/\alpha$，先用 $\alpha\ge a_Q\to\infty$，再令固定 $t\uparrow t_c$，
给极限上界 $-\gamma t_c$。这里没有假定随 $\alpha$ 增长的鞍点保持内部紧性。

反向界单独取最大权重坐标。其余平方能量 $R_\alpha$ 的期望至多
$V/\alpha+\|e\|^2$，故以至少 $1/2$ 概率不超过
$\epsilon_x=2(V/a_Q+\|e\|^2)\to0$。
独立能量尺度噪声的标准差为 $s_E=\sqrt\delta\sigma'/\sqrt\alpha$，
其绝对值不超过 $s_E$ 的概率为固定正常数。
最大坐标平方 $X=(\sqrt{v_*/\alpha}Z-e_*)^2$ 的精确密度为

$$
p_X(z)=\frac{\sqrt{\alpha/(2\pi v_*)}}{2\sqrt z}
\left[e^{-\alpha(\sqrt z+e_*)^2/(2v_*)}
+e^{-\alpha(\sqrt z-e_*)^2/(2v_*)}\right],\qquad z>0.
$$

在上述两个事件上，$z=h_y-R_\alpha-\mathrm{noise}$ 位于固定正紧区间。
积分并乘能量到输出的 Jacobian $\sqrt\delta$，得到

$$
g_{\alpha,\sigma'}(y)\ge c\sqrt{\alpha\delta/v_*}
\exp\left[-\frac\alpha{2v_*}(\sqrt{h_y+s_E}+|e_*|)^2\right].
\tag{107.19}
$$

结合 (103.8) 和精确中心界，(107.18)–(107.19) 给

$$
\sup_{a_Q\le\alpha\le\ln Q,|y|\le R}
\left|\frac\delta\alpha\ln g_{\alpha,\sigma'}(y)+c_\infty\right|\to0.
\tag{107.20}
$$

这一步本身不需要阶数上限；上限用于下列实际计数回接。

**显式支付增长阶数。** 对 $1\le\alpha\le\ln Q$、$N\ge e^{\epsilon Q^3}$，
将二项 Stirling 展开的对数误差乘 $\alpha$。
在 $|z|\le N^{1/12}$ 内误差至多 $C\alpha N^{-1/4}$；
幂质量的外部 Gaussian 原子包络相对中央归一化至多
$e^{C\alpha}\operatorname{poly}(\alpha)e^{-c\alpha N^{1/6}}$，仍一致可忽略。
因此幂二项归一化为

$$
\sum_kb_{N,p}(k)^\alpha
=(2\pi d)^{(1-\alpha)/2}\alpha^{-1/2}(1+o(1)),
\tag{107.21}
$$

相对误差至多 $\operatorname{poly}(Q)e^{-\epsilon Q^3/4}$。
单位取整格积分的对数误差至多
$C\alpha(1+|z|)/\sqrt N+C\alpha/N$。
故在共同盒 $|n_j-C_jp_j|/\sqrt{d_j}\le Q^2$ 上，
完整高组 escort 与独立取整 $N(C_jp_j,d_j/\alpha)$ 的质量比为
$1+O(\operatorname{poly}(Q)e^{-\epsilon Q^3/4})$，
两律盒外概率至多 $\operatorname{poly}(Q)e^{-cQ^4}$。

全部低组配置能量至多 $CQ^2e^{2\epsilon Q^3}/B^2$，原标量取整误差仍为
$\Delta_Q\le\operatorname{poly}(Q)[B^{-1}+B^{-2}e^{2\epsilon Q^3}]$。
对 $s=\sigma/\sqrt\alpha$ 用 (103.20)，
$h=\sqrt\alpha\Delta_Q/\sigma\le\operatorname{poly}(Q)e^{-bQ^3}$，
对应 $\sigma'=\sigma/\sqrt{1\pm h}$，(107.20) 对两宽度都成立。
盒外加性密度至多 $\operatorname{poly}(Q)\sigma^{-1}e^{-cQ^4}$，
而 (107.19) 给比较密度下界 $e^{-C\alpha/\delta}$。
由于 $\alpha\le\ln Q$、$L_M=O(Q^3)$，加性误差相对下界仍指数小。
于是 (107.20) 传给原乘积计数 escort 的稀有输出密度。

同一质量比较给 $\sup_{1\le\alpha\le\ln Q}\mathbb E_{\mathsf Q_\alpha}E=O_{\mathbb P}(1)$。
盒内用 Gaussian 能量均值与小组全范围界；盒外使用确定界
$E\le N_J^2/B^2=O_{\mathbb P}(B^2)$ 乘 $e^{-cQ^4}$，而 $\ln B^2=O(Q^3)$。
Gaussian 尾能量用其直接尾矩控制。
第 103 章非负能量的稀有 Gaussian 重加权均值界遂对这些阶数一致。
用 $D^2/q\le C\delta(E+\|e\|^2)$、Jensen 及 (103.11)，精确比值

$$
\frac{f_{\mathsf P_\alpha,\sigma/\sqrt\alpha}(y)}
{f_{\mathsf Q_\alpha,\sigma/\sqrt\alpha}(y)}
=\frac{\mathbb E_{\mathsf Q_\alpha,y}\mathcal L_x^\alpha}
{\mathbb E_{\mathsf Q_\alpha}\mathcal L_x^\alpha}
$$

的对数绝对值至多 $O_{\mathbb P}(\alpha\delta)$。
乘 $\delta/\alpha$ 后趋零，得到实际版本的 (107.20)。
最后代入精确 (103.10)：$\alpha/(\alpha-1)\to1$ 一致，
普通密度项由 (103.27) 消失，其余常数乘 $\delta$ 也消失，即得 (107.15)。证毕。

作为一致性核对，固定阶系数中的 $t_\alpha\uparrow t_c$，
而 $K(t_c-)$ 有限：原点附近只出现可积的 $\ln|s|$ 奇性。
因此 $J_\alpha/(\alpha-1)\to\gamma t_c$，与本章一致。
此核对不是上述任一证明中的极限交换步骤。

本章未给常数阶输出响应、超过受控窗口的增长阶数、Shannon 延拓或输出平均熵。
离散众数比、凸性、Stirling 和指数倾斜为成熟方法；原模型中的全元组下界、可行整数构造、
实际完整选择修正和增长阶数的稀有密度回接构成本章连接。
归属和经典最大猜测概率、Gaussian 二次型大偏差的对象差别见
[Library 说明](../../../Library/Dynamics/iyer2025empirical.md)。

## 追加锚（第 107 章后续增补区）

## 108. 最大原子成本的绝对精度与输出差中的噪声抵消

**定义 108.1（保留经验系数的极小值包络）。** 保持第 107 章原实际计数律、
原固定总数先验、全部取整、精确中心及同一输出 $Y=T+\sigma G$。
熵仍以 nats 计。记 $u=\sigma^2$、$h_y=V+\sqrt\delta y$，并使用
(107.4) 的 $A_x(y)$、完整数组的 $v_* =\max_jv_j$。令

$$
c_* =\frac1{2v_*},\qquad
\Phi_x(h)=\min_{E\ge0}\left[c_*E+\frac{(E-h)^2}{2\delta u}\right],
\qquad e^\circ(h)=(h-\delta u c_*)_+.
\tag{108.1}
$$

有限层级 $v_* =0$ 的数据计作失败事件；下述比值只在 $v_* >0$ 处评价。
由 $v_*/\delta\to\rho_0>0$，其失败概率对原确定支持一致趋零。
也可在该事件任意作可测延拓，不改变概率收敛。

**定理 108.2（绝对成本与常数精度的最小熵响应）。** 在原半指数条件

$$
L_M=\ln(1/\sigma_M)\to\infty,\qquad
\limsup_M L_M/Q^3<c_q/2
\tag{108.2}
$$

下，对每个固定有限 $R$，在原实际数据概率下、对全部规定大小的确定支持一致，
原 stationary pair 与连续 path 实验分别有

$$
\sup_{|y|\le R}
\left|A_x(y)-\frac{V+\sqrt\delta y}{2v_*}
                 +\frac{\delta\sigma^2}{8v_*^2}\right|\to0,
\tag{108.3}
$$

以及

$$
\sup_{|y|\le R}\left|
H_\infty(\mathsf P_x^y)-H_\infty(\mathsf P_x^0)
-\frac{\sqrt\delta}{2v_*}y+\frac{y^2}{2\nu}\right|\to0.
\tag{108.4}
$$

更完整的绝对展开是

$$
H_\infty(\mathsf P_x^y)-H_\infty(\mathsf P_x)+L_M
=\frac{V+\sqrt\delta y}{2v_*}
 -\frac{\delta\sigma^2}{8v_*^2}
 -\frac12\ln\nu-\frac{y^2}{2\nu}+o_{\mathbb P}(1),
\tag{108.5}
$$

其中余项对上述紧输出一致。保留的 $V,v_*$ 是同一实际数据纤维的精确量。
本章不假定最大权重唯一、与次大权重分离，或实际最小化元组只有一个非众数坐标。

**证明：精确经验系数的全元组下界。** 仍取二项计数乘积律 $\mathsf Q_x$，
众数向量 $k^\circ$、标量组数 $m\le CQ^2$、$C_{\max}=\max_jC_j$。
第 103、107 章的实际输入界给

$$
\epsilon_p:=\max_j|p_j-1/2|=O_{\mathbb P}(q^{-1/2}),\qquad
\epsilon_e:=\|e\|_2=O_{\mathbb P}(Q^{-5/2}+q^{-1/2}),
\quad v_*/\delta\to\rho_0,
\quad V\to\gamma.
\tag{108.6}
$$

使用 (107.7)–(107.8) 的未缩放形式，设

$$
c_Q=\frac{2B^2}{C_{\max}+2},\qquad
b_Q=\epsilon_e+\frac{2\sqrt m}{B}.
$$

则全盒上精确有

$$
S_Q(n)\ge c_Q(\sqrt{E(n)}-b_Q)_+^2.
\tag{108.7}
$$

这里使用众数比的离散曲率与向量 Cauchy–Schwarz，没有损失 $O(m)$ 常数。
校准精度直接比较两个有限经验系数：

$$
(1-4\epsilon_p^2)C_{\max}\le4B^2v_*\le C_{\max},\qquad
0\le c_*-c_Q
\le c_*\left(4\epsilon_p^2+\frac2{C_{\max}+2}\right).
\tag{108.8}
$$

对每个固定 $K>0$，由 $(a-b)_+^2\ge a^2-2ab$，在全部 $E(n)\le K$ 的元组上

$$
S_Q(n)\ge c_*E(n)-r_Q(K),\quad
r_Q(K)=c_*\left[
\left(4\epsilon_p^2+\frac2{C_{\max}+2}\right)K+2b_Q\sqrt K\right]
\to0.
\tag{108.9}
$$

确实 $C_{\max}\asymp_{\mathbb P}B^2\delta$、$c_*\asymp_{\mathbb P}\delta^{-1}$，
故中心误差 $\epsilon_e/v_* =O_{\mathbb P}(Q^{-2})$，
组数众数舍入误差 $\sqrt m/(Bv_*)$ 及其余项均为指数小量乘固定多项式。
不需要 $v_*/\delta-\rho_0$ 的收敛速率；提前把系数换成其极限会丢失这一绝对精度。

完整固定总数修正仍是
$\mathsf P_x(n)=\mathcal L_x(\sum_jn_j)\mathsf Q_x(n)$。
令 $D(n)=\sum_j(n_j-C_jp_j)$、$d_J=B^2V$，沿用全局两个方向的界

$$
-C[D(n)^2/q+q^{-1/2}]\le\ln\mathcal L_x
\le C[d_J/q+q^{-1/2}].
\tag{108.10}
$$

因 $|D(k^\circ)|\le m$，记
$\ell_Q=C(m^2/q+q^{-1/2})$、$u_Q=C(d_J/q+q^{-1/2})$，有

$$
-\ell_Q\le\ln(P_*/Q_*)\le u_Q,\qquad
S_P(n)\ge S_Q(n)-\ell_Q-u_Q.
\tag{108.11}
$$

两误差均趋零，$u_Q=O_{\mathbb P}(Q^{-5/2})$ 加指数小量。因此

$$
S_P(n)\ge c_*E(n)-r_x(K),\qquad
r_x(K):=r_Q(K)+\ell_Q+u_Q\to0
\quad\text{对所有 }E(n)\le K.
\tag{108.12}
$$

这里只在众数处使用修正的下界；没有假定它在远元组上一致远离零。

**小组与实际背景能量。** 上述全元组界直接保留所有组。
也可选固定 $0<\epsilon<c_q/2$，把 $C_j<e^{\epsilon Q^3}$ 作为低组。
因 $0\le n_j,\mu_j\le C_j$，它们对每个元组的能量满足

$$
E_{\rm low}(n)\le\frac{m e^{2\epsilon Q^3}}{B^2}
=\operatorname{poly}(Q)e^{-(c_q-2\epsilon)Q^3}.
\tag{108.13}
$$

低组众数信息量非负，故丢掉该非负信息量并在能量项支付
$c_*E_{\rm low}$ 仍给 (108.12) 的趋零误差。
这是下界的证明分组，不更改完整标量。以下可行上界保留低组的精确众数能量，
从未要求把该能量除以指数小的噪声后仍可忽略。

**同一原模型中的整数上界。** 对固定 $0<k<K<\infty$，
选任一达到 $v_*$ 的组 $j_*$，以确定规则处理并列。
其余坐标保持在二项众数，保留

$$
E_0=\sum_{j\ne j_*}(k_j^\circ-\mu_j)^2/B^2
\le(\epsilon_e+\sqrt m/B)^2.
\tag{108.14}
$$

对每个所需能量 $e\in[k,K]$，令

$$
n_*(e)=\operatorname{nearestInteger}
 [\mu_*+B\sqrt{e-E_0}],\qquad
n_j(e)=k_j^\circ\ (j\ne j_*),\qquad E_e=E(n(e)).
\tag{108.15}
$$

在概率一致趋一的事件上，所有这些元组同时可行且

$$
|E_e-e|\le C_K/B.
\tag{108.16}
$$

可行性来自 $C_*\asymp_{\mathbb P}B^2\delta$、$p_*\to1/2$、
$|\mu_*-C_*p_*|\le B\epsilon_e$ 和 $B\delta\to\infty$；
$O(B)$ 位移严格留在 $[0,C_*]$ 内。原全盒支持事件保证它属于同一固定总数后验。
特别地，最大方差组是高组，无须对低组作 Gaussian 原子近似。

写 $a_e=(n_*(e)-\mu_*)/B$。只有一个坐标离开众数，
第 103、107 章的含众数归一化 Stirling 估计给

$$
S_Q(n(e))
=\frac{(n_*(e)-C_*p_*)^2}{2C_*p_*(1-p_*)}+o_{\mathbb P}(1)
=c_*(a_e+e_*)^2+o_{\mathbb P}(1)
\tag{108.17}
$$

一致于 $e\in[k,K]$。标准位移仅为 $O_{\mathbb P}(\delta^{-1/2})$，
而 $C_*$ 指数增长，所以误差
$O((1+|z|^3)/\sqrt{C_*})$ 是指数小量乘多项式。
因 $E_e=a_e^2+E_0$，

$$
|S_Q(n(e))-c_*E_e|
\le c_*[2|a_e e_*|+e_*^2+E_0]+o_{\mathbb P}(1)=o_{\mathbb P}(1).
\tag{108.18}
$$

$|D(n(e))|\le C_KB+m$ 还给 $D(n(e))^2/q=O_{\mathbb P}(Q^{-5/2})+o(1)$。
按 (108.10)–(108.11) 的正确方向使用修正，得到实际可行证据

$$
S_P(n(e))\le c_*E_e+\widetilde r_x(k,K),\qquad
\widetilde r_x(k,K)\to0,
\tag{108.19}
$$

对整段 $e$ 一致。它只是一个上界构造，不宣告实际最优元组的坐标结构。

**包络极小值与全部实际极小元。** (108.1) 是实直线上仿射函数加半直线示性函数的
经典 Moreau 包络。配方给极小能量 $e^\circ(h)$。
因 $h_y\to\gamma>0$ 且 $\delta u c_*\to0$，
对紧输出其极小能量同时位于某固定 $[k,K]\subset(0,\infty)$。
此时

$$
\Phi_x(h_y)=c_*h_y-\frac{\delta u c_*^2}{2},\qquad
c_*E+\frac{(E-h_y)^2}{2\delta u}
=\Phi_x(h_y)+\frac{(E-e^\circ(h_y))^2}{2\delta u}.
\tag{108.20}
$$

将 (108.15) 应用于 $e=e^\circ(h_y)$，得到

$$
A_x(y)\le\Phi_x(h_y)+\frac{C_K}{B^2\delta\sigma^2}
                         +\widetilde r_x(k,K).
\tag{108.21}
$$

线性舍入项在配方中严格抵消，不用一个随噪声爆炸的粗导数界。
选 $l<c_q/2$ 使最终 $L_M\le lQ^3$，则原取整给

$$
\frac1{B^2\delta\sigma^2}
=\frac{Q^3e^{2L_M}}q
\le C Q^3e^{-(c_q-2l)Q^3}\to0.
\tag{108.22}
$$

上界为 $O_{\mathbb P}(\delta^{-1})$，而 $S_P\ge0$，
故每一个实际最小化元组 $n_y$ 都满足

$$
|E(n_y)-h_y|\le C\sigma
\tag{108.23}
$$

在紧事件上一致成立。于是它们的能量同时留在固定有界区间。
对全部这些元组用 (108.12)，得到

$$
A_x(y)\ge c_*E(n_y)+\frac{(E(n_y)-h_y)^2}{2\delta u}-r_x(K')
\ge\Phi_x(h_y)-r_x(K').
\tag{108.24}
$$

(108.21)–(108.24) 证明 $\sup_{|y|\le R}|A_x(y)-\Phi_x(h_y)|\to0$，
即 (108.3)。远能量由实际非负信息量与原 Gaussian 罚项排除，
不是从假设最优配置为单坐标推出。

**普通密度的绝对极限。** 为得到 (108.5)，需要比 (103.27) 更强的普通密度归一化。
它已由第 105 章的相对比较导出：在 $c=1$ 处，
$F_{1,u}'(0)=V+\|e\|^2$，(105.12) 的有限 Legendre 成本在目标 $V$ 处为
$O_{\mathbb P}(\|e\|^4)$，除以 $\delta$ 仍趋零；曲率趋于 $\nu$。
故 $g_{1,u}(0)\to(2\pi\nu)^{-1/2}$，再由 (105.16)、(105.18)，

$$
\sup_{|y|\le R}|f_{\mathsf P_x,\sigma}(y)-\varphi_\nu(y)|\to0,
\qquad
\sup_{|y|\le R}\left|
\ln\frac{f_{\mathsf P_x,\sigma}(y)}{f_{\mathsf P_x,\sigma}(0)}
+\frac{y^2}{2\nu}\right|\to0.
\tag{108.25}
$$

紧区间上极限密度为正，允许上述对数运算。
这是实际相对密度桥的推论，不从弱中心极限定理推导密度收敛。
将 (108.3)、(108.25) 代入精确式 (107.5) 得 (108.5)。
对 $y$ 与零相减，

$$
\Phi_x(V+\sqrt\delta y)-\Phi_x(V)=\frac{\sqrt\delta}{2v_*}y,
\tag{108.26}
$$

有限噪声修正先严格抵消，再取极限，给 (108.4)。
全部输入均保留原支持一致性、pair/path 各自的实际概率律，证毕。

**推论 108.3（所有最优能量的细定位）。** 同一条件下，不要求最小化元组唯一，
仍有

$$
\sup_{\substack{|y|\le R\\n_y\in\operatorname{argmin}_n
\{S_P(n)+(E(n)-h_y)^2/(2\delta\sigma^2)\}}}
\frac{|E(n_y)-h_y+\delta\sigma^2/(2v_*)|}{\sigma\sqrt\delta}\to0.
\tag{108.27}
$$

证明是把 (108.12)、(108.20) 与实际可行上界合并，
该比值的平方不超过两个非负趋零误差之和的两倍。
这定位能量，不识别坐标分配，也不宣称后验典型质量集中在某个最大权重坐标。

**命题 108.4（逐输出噪声项可以发散）。** 合法噪声 $\sigma=\delta^{1/8}$ 满足
(108.2)，但 (108.3) 给

$$
\sup_{|y|\le R}\left|
\delta^{3/4}\left[A_x(y)-\frac{h_y}{2v_*}\right]
+\frac1{8\rho_0^2}\right|\to0.
\tag{108.28}
$$

因此在每份输出成本中删除噪声项，会丢掉 $\delta^{-3/4}$ 阶的量。
该项与输出无关，所以不反驳 (108.4)。这是原模型的解析序列，非代理数值实验。

**注记 108.5（归属与结论边界）。** 半直线上的仿射近端公式直接属于 Moreau 的
经典结果，二项众数比、Stirling 与配方也不是本章新工具。
这里新增的模型内桥梁是：用指数精确校准比较两个有限经验曲率，
在完整固定总数后验上取得绝对 $o(1)$ 的全元组下界与可行上界，
再于原半指数噪声精度支付整数误差。
最大权重坐标仅提供存在证据；Gaussian 场的条件质量凝聚定理不自动适用于它。
本章不将经验 $v_*$ 换成极限系数，不扩张输出紧区间或噪声范围，
不导出任意增长 Rényi 阶、Shannon 阶、期望熵或全局原创结论。

## 追加锚（本行以下为增补区）

## 109. 半整数共振的定位、全余量标量平滑与中心方差的剩余接口

**定义 109.1（同一数组的标记密度）。** 保持第 106 章全部原模型与有限系数，记

$$
\mathcal B=q/Q^{11/4}=B^2\sqrt\delta,\qquad
\mathcal D=\mathcal B\sqrt\delta=q/Q^3,\qquad
L=\ln(1/\sigma),\qquad\Delta=\ln\mathcal B-L.
\tag{109.1}
$$

信息量以 nats 计，$s_j=-\ln\mathsf Q_{x,j}(R_j)-\mathbb E[-\ln\mathsf Q_{x,j}(R_j)]$，
$s_{\mathsf Q}=\sum_js_j$。仍用完整校准乘积律 $\mathsf Q_x$、原精确中心 $\mu_j$、原完整 $V$ 和

$$
T=\mathcal B^{-1}\sum_j(R_j-\mu_j)^2-V/\sqrt\delta,\qquad
U=s_{\mathsf Q}+G^2/2,\qquad Y=T+\sigma G.
\tag{109.2}
$$

以 $T',U',Y'$ 表示 (102.8)、第 106 章的同一核心 Gaussian 耦合：
外部计数及其信息量保持原联合关系，测量变量仍是同一个 $G$。
定义 $q_k(y)dy=\mathbb E_{\mathsf Q}[U^k;Y\in dy]$，
$q'_k(y)dy=\mathbb E_{\mathsf Q}[(U')^k;Y'\in dy]$，$k=0,1,2$。
记 $f_{\mathsf Q}=q_0$、$f'=q'_0$，$f_x$ 是原选中律的输出密度，
$g_x$ 是第 106 章相同观测权重、相同噪声的中心 Gaussian 核心参考密度。

**定理 109.2（任意发散余量下的标量桥与标记定位）。** 若确定噪声满足

$$
L\to\infty,\qquad\Delta\to\infty,
\tag{109.3}
$$

则在原实际数据概率下，对原规定大小的确定支持一致，pair/path 分别成立

$$
\|f_{\mathsf Q}-f'\|_\infty\to0,
\qquad
\int(1+y^2)|f_x(y)-g_x(y)|\,dy\to0.
\tag{109.4}
$$

第一式明确只对校准乘积比较律，不由它宣称原选中密度的逐点极限。
此外，存在固定 $R_0>0$，使全部三个原标记变换在半整数带

$$
\left|t-\pi\ell\mathcal B\right|
\le2\pi R_0\mathcal B/\mathcal D,\qquad\ell\in\mathbb Z
\tag{109.5}
$$

之外的绝对积分至多 $CQ^{17/4}e^{-c\sqrt Q}$。
下文给非零带的精确同数组表示及余项界。
本定理没有把第 106 章的完整信息方差结论扩张到所有 (109.3)；
带标记的中心抵消及输出尾部仍是缺口。

**证明：小分母的精确收缩。** 在 (106.6) 的共同事件上，
中心区域有至少 $c_0/\delta$ 个原坐标，$c\mathcal D\le d_j\le C\mathcal D$。
对其中一个 $K\sim\operatorname{Bin}(n,p)$，写 $m=np$、$d=np(1-p)$。
(106.8) 的离散 Gaussian 总变差误差为 $C\mathcal D^{-1/8}$。
对既约 $p_0/k$，有限 Gauss 分解的系数模至多 $\sqrt{2/k}$。
当 $k=1,2$ 时，整数平方模二等于整数本身，所以二次相位恰是一项模为一的线性相位。

写 $\theta=p_0/k+\tau$。Poisson 求和中的单个 Gaussian 积分有模前因子

$$
F_d(\tau)=(1+16\pi^2d^2\tau^2)^{-1/4}
\tag{109.6}
$$

及间距 $1/k$ 的对偶 Gaussian 网格。
对固定 $k_0,R_0$，当 $k\le k_0$、$|\mathcal D\tau|\le2R_0$ 时，
对任意实移位 $\xi$ 都有

$$
\sum_{v\in\mathbb Z}
\exp\left[-\frac{2\pi^2d}{1+16\pi^2d^2\tau^2}(v/k-\xi)^2\right]
\le1+C_{R_0,k_0}e^{-c_{R_0,k_0}\mathcal D}.
\tag{109.7}
$$

取最近网格点，其项至多一，其余距离至少 $(j-1/2)/k$；
若最近点并列，它们自身已指数小，仍给同一界。
归一化常数也仅相差 $1+O(e^{-c\mathcal D})$。
因此对 $3\le k\le k_0$，任意原实中心 $\mu$，

$$
|\mathbb E e^{2\pi i\theta(K-\mu)^2}|
\le\sqrt{2/k}[1+Ce^{-c\mathcal D}]+C\mathcal D^{-1/8}.
\tag{109.8}
$$

对 $k=1,2$，保留单模前因子则有

$$
|\mathbb E e^{2\pi i(\ell/2+\tau)(K-\mu)^2}|
\le(1+C_{R_0}\mathcal D^{-1/8})
 (1+c_1\mathcal D^2\tau^2)^{-1/4},
\qquad |\mathcal D\tau|\le2R_0.
\tag{109.9}
$$

这里 $F_d$ 在指定带内有正下界，才把加性二项误差转成乘性误差。
它是 $1+o(1)$，不能换成逐坐标的任意固定常数。

对所有分母使用 (106.10) 的粗界

$$
|\mathbb E e^{2\pi i\theta(K-\mu)^2}|
\le C_0[k^{-1/2}(1+\mathcal D^2\tau^2)^{-1/4}+\mathcal D^{-1/8}],
\quad k\le\lfloor\sqrt{\mathcal D}\rfloor,
\quad |\tau|\le[k\lfloor\sqrt{\mathcal D}\rfloor]^{-1}.
\tag{109.10}
$$

先选固定 $k_0$ 使 $C_0/\sqrt{k_0}<1/4$，再选固定 $R_0$ 使
$C_0(1+R_0^2)^{-1/4}<1/4$。Dirichlet 逼近与 (109.8) 处理剩余有限分母，
得到某个固定 $\rho<1$，一致于全部原中心和中心坐标：

$$
\operatorname{dist}(\theta,\tfrac12\mathbb Z)>R_0/\mathcal D
\quad\Longrightarrow\quad
|\mathbb E e^{2\pi i\theta(K-\mu)^2}|\le\rho.
\tag{109.11}
$$

未要求经验中心有理，也未宣称实际特征函数周期化。

**保留全部中央储备并先积分。** 取 $n_Q=\lfloor c_0/(2\delta)\rfloor$ 个收缩因子，
另留十六个用于 (106.12)–(106.13) 的周期非负包络 $P_{\mathcal D,16}$。
在至多两个信息标记之后，原共同事件仍供应这些不相交因子；
所有剩余未标记因子的模至多一。包络满足

$$
\int_0^1P_{\mathcal D,16}(\theta)\,d\theta\le C/\mathcal D.
\tag{109.12}
$$

展开前两阶中心信息量标记至多产生 $CQ^4$ 项，各标记坐标矩有一致界。
同一测量变量精确给

$$
h_0(t)=e^{-\sigma^2t^2/2},\quad
h_2(t)=(1-\sigma^2t^2)e^{-\sigma^2t^2/2},\quad
h_4(t)=(3-6\sigma^2t^2+\sigma^4t^4)e^{-\sigma^2t^2/2}.
\tag{109.13}
$$

令 $\theta=t/(2\pi\mathcal B)$。带外变换由
$CQ^4\rho^{n_Q}P_{\mathcal D,16}(\theta)[1+(\sigma t)^4]e^{-\sigma^2t^2/2}$ 控制。
令 $s=2\pi\sigma\mathcal B=2\pi e^\Delta\ge1$，按整周期划分实线。
$e^{-s^2\theta^2/4}$ 在这些单位区间的上确界之和一致有界，
且标记多项式可吸收入该较弱 Gaussian 指数。因此

$$
\int_{\rm 带外}|\widehat q_k(t)|dt
\le CQ^4\rho^{n_Q}\mathcal B/\mathcal D
\le CQ^{17/4}e^{-c\sqrt Q},\qquad k\le2.
\tag{109.14}
$$

该积分覆盖整个无界频轴，而非先乘一个指数长频率区间。
混合律的中心 Gaussian 因子有模
$(1+4t^2w_j^2)^{-1/4}$，原非中心移位只降低该模。
保留 $\lceil\ln Q\rceil+20$ 个因子即由第 106 章同样计算得

$$
\forall N<\infty:\qquad
\max_{k\le2}\int_{|t|>Q^2}|\widehat q'_k(t)|dt\le C_NQ^{-N}.
\tag{109.15}
$$

低频 $|t|\le Q^2$ 只用 (106.7) 的中心量化耦合，从未将其误差除以噪声。

**非零共振的精确分离。** 取固定偶的光滑函数 $0\le\chi\le1$，在 $[-1,1]$ 为一，
在 $[-2,2]$ 外为零。写

$$
t_\ell=\pi\ell\mathcal B,\quad W_Q=2\pi R_0\mathcal B/\mathcal D,\qquad
\widehat a_k(t)=\sum_{\ell\ne0}\chi((t-t_\ell)/W_Q)\widehat q_k(t),
\quad a_k=\mathcal F^{-1}\widehat a_k.
\tag{109.16}
$$

这些带最终互不相交，零带完全包含在 $|t|\le Q^2$ 内。
每个有限正噪声下所有变换可积。$a_k$ 是有符号振荡函数，不是密度或独立信道。
结合低频耦合、(109.14)–(109.15)，得到

$$
q_k-q'_k=a_k+e_k,\qquad
\forall N<\infty:\quad\max_{k\le2}\|e_k\|_\infty\le C_NQ^{-N}.
\tag{109.17}
$$

没有从该上确界界自动推出全局 $L^1$ 或加权尾界；光滑分割也不能替代那一义务。

**无标记共振的物理宽度。** 对 (109.9) 使用 $n_Q$ 个原因子，
因 $n_Q\mathcal D^{-1/8}\to0$，其乘积至多
$2(1+c_1\mathcal D^2\tau^2)^{-n_Q/4}$。
Beta 积分给每一带内、在物理频率单位下

$$
\int_{\text{带 }\ell}|\text{未标记计数乘积}|dt
\le\frac{C\mathcal B}{\mathcal D\sqrt{n_Q}}\le C.
\tag{109.18}
$$

这里利用 $n_Q\delta$ 有正下界，消除了固定十六因子界的 $Q^{1/4}$ 损失。
对 $\ell\ne0$，带内 $|t|\ge c|\ell|\mathcal B$，故

$$
\sum_{\ell\ne0}\int_{\text{带 }\ell}|\widehat q_0(t)|dt
\le Ce^{-c e^{2\Delta}}.
\tag{109.19}
$$

没有多项式 $Q$ 前因子。于是

$$
\|\widehat q_0-\widehat q'_0\|_1\le\varepsilon_Q,
\quad\varepsilon_Q=Ce^{-c e^{2\Delta}}+\zeta_Q,
\qquad\forall N:\ \zeta_Q\le C_NQ^{-N}.
\tag{109.20}
$$

任意慢的发散余量都使它趋零，但不能把它称为关于 $Q$ 的任意幂小量。
Fourier 反演给 (109.4) 第一式。直接四阶输出矩还给，对 $R\ge1$，

$$
\int(1+y^2)|f_{\mathsf Q}-f'|dy
\le C(R+R^3)\varepsilon_Q+C(R^{-4}+R^{-2}).
\tag{109.21}
$$

取 $R=\varepsilon_Q^{-1/5}$ 得上界 $C\varepsilon_Q^{2/5}$。
回到原选中律时，先在同一计数与同一 $G$ 上条件化，再用 Cauchy–Schwarz：

$$
\int(1+y^2)|f_x-f_{\mathsf Q}|dy
\le\mathbb E_{\mathsf Q}[|\mathscr L_x-1|(1+Y^2)]
\le C\varepsilon_x\to0.
\tag{109.22}
$$

无逆噪声。最后用第 101、102、106 章噪声前的二维核心正则器，
对原外部计数和同一 $G$ 条件化后平移能量坐标，支付 $V_O\le Q^{-200}$；
再用分块比较移去精确非中心和截距，联合变差成本为 $O_{\mathbb P}(Q^{-9/4})$。
外部信息量与外部能量的相关性保留到合法平移完成。
直接四阶输出矩把这些联合变差转成加权 $L^1$ 收敛，给 (109.4) 第二式，证毕。
这一步只回接标量密度，没有传递放大的先验信息方差。

**推论 109.3（乘积比较的紧区间分母）。** 对每个固定 $K$，
在相同概率范围内，$f_{\mathsf Q},f'$ 在 $[-K,K]$ 上均最终以概率趋一有正下界。
确实，中央 Gaussian 因子给每个固定 $a\ge0$

$$
\int |t|^a|\widehat f'(t)|dt
\le\int |t|^a(1+c\delta t^2)^{-n_Q/4}dt\le C_a.
\tag{109.23}
$$

由 $n_Q\delta\asymp1$ 的 Beta 积分得到最后一步。
已有弱极限与 $a=1$ 的一致 Fourier 尾界给 $\|f'-\varphi_\nu\|_\infty\to0$；
再用 (109.20) 即得。没有用 TV 将此逐点正下界转移给原选中密度。

**命题 109.4（同一经验数组的精确扭曲向量）。** 因整数 $a$ 满足 $a^2-a\in2\mathbb Z$，
在 $t_\ell$ 处原标量的相位精确等于

$$
e^{it_\ell T}=\omega_\ell e^{i\sum_jb_{\ell j}R_j},\quad
b_{\ell j}=\pi\ell(1-2\mu_j),\quad
\omega_\ell=e^{i\pi\ell(\sum_j\mu_j^2-B^2V)}.
\tag{109.24}
$$

令 $F_r^{(\ell)}(s)=\mathbb E_{\mathsf Q}[s_{\mathsf Q}^r
 e^{isT+i\sum_jb_{\ell j}R_j}]$。对 $t=t_\ell+s$，同一残差的精确展开是

$$
\begin{aligned}
\widehat q_0(t)&=\omega_\ell h_0(t)F_0^{(\ell)}(s),\\
\widehat q_1(t)&=\omega_\ell[h_0(t)F_1^{(\ell)}(s)+\tfrac12h_2(t)F_0^{(\ell)}(s)],\\
\widehat q_2(t)&=\omega_\ell[h_0(t)F_2^{(\ell)}(s)+h_2(t)F_1^{(\ell)}(s)
 +\tfrac14h_4(t)F_0^{(\ell)}(s)].
\end{aligned}
\tag{109.25}
$$

这里全部坐标、精确中心与截距都保留，不能换成任意整数中心数组。
为避免扭曲因子的零点，置
$A_j=\mathbb E e^{is(R_j-\mu_j)^2/\mathcal B+ib_{\ell j}R_j}$，
$B_j=\mathbb E[s_j e^{is(R_j-\mu_j)^2/\mathcal B+ib_{\ell j}R_j}]$，
$E_j=\mathbb E[s_j^2 e^{is(R_j-\mu_j)^2/\mathcal B+ib_{\ell j}R_j}]$，
$z(s)=e^{-isV/\sqrt\delta}$、$V_{\mathsf Q}=\sum_j\mathbb E s_j^2$。则

$$
F_0=z\prod_jA_j,\qquad F_1=z\sum_jB_j\prod_{i\ne j}A_i,
$$

$$
F_2-V_{\mathsf Q}F_0
=z\left[\sum_j(E_j-\mathbb E s_j^2A_j)\prod_{i\ne j}A_i
 +2\sum_{i<j}B_iB_j\prod_{h\ne i,j}A_h\right].
\tag{109.26}
$$

这在取界前减掉 $O(Q^2)$ 的先验方差，且没有除以任何 $A_j$。
精确共振处还直接有

$$
|\mathbb E e^{ibR_j}|\le e^{-2d_j\sin^2(b/2)}.
\tag{109.27}
$$

原中心的有理独立性排除精确等式，却不提供此处所需的
$d_j^{-1/2}$ 级联合模距离界，也不覆盖整个 $s$ 带。
本章未把这种量化算术界当作已证前提。

**命题 109.5（先抵消共同调制的方差接口）。** 令 $f=q_0$、
$m(y)=q'_1(y)/f'(y)$、$v(y)=q'_2(y)/f'(y)-m(y)^2$，
$d_k=q_k-q'_k$。直接展开条件均值平方给

$$
f[\operatorname{Var}(U\mid Y=y)-v]
=d_2-2md_1+(m^2-v)d_0-\frac{(d_1-md_0)^2}{f}.
\tag{109.28}
$$

若三个密度仅同乘一个正函数，右侧严格为零；
分别对每个 $d_k$ 取绝对值会掩盖这一抵消。
最后的商项必须保留，正密度本身不支付它的积分。
令 $D_{\mathsf Q},D'_{\mathsf Q}$ 使用第 106 章同一有限系数但各自精确先验方差，
则 (109.28) 右侧再减 $(V_{\mathsf Q}-V'_{\mathsf Q})f$，
即为 $f(D_{\mathsf Q}-D'_{\mathsf Q})$；放大的有限系数先逐点抵消。

(109.17)、推论 109.3 与保留 Gaussian 中央平滑后的多项式上确界给，
对任意固定 $K,N$，

$$
f(D_{\mathsf Q}-D'_{\mathsf Q})
=a_2-2ma_1+(m^2-v)a_0-\frac{(a_1-ma_0)^2}{f}+o(Q^{-N}),
\qquad |y|\le K.
\tag{109.29}
$$

先验方差差由原中心耦合为指数小量乘多项式，已纳入余项。
这是把障碍定位到 (109.24)–(109.26) 的同数组标记向量，尚未证明右侧趋零。
小密度的支付也可写为经典变分恒等式

$$
\int\eta^2/f
=\sup_{b\text{ 有界可测}}\left[2\int b\eta-\int b^2f\right],
\tag{109.30}
$$

以配方及 $\eta/f$ 的有界截断证明，允许扩展非负值。
未加权 $L^1$ 小量不能替代它。

**命题 109.6（固定原标量的精确信息倾斜）。** 对任一有限先验计数律 $P$，
令 $s=-\ln P-\mathbb E_P[-\ln P]$、$M_P(u)=\mathbb E_Pe^{us}$，
$P_u=e^{us}P/M_P(u)$。求导时固定原 $T$、全部中心和模型参数；
令 $f_{P,u}$ 是 $P_u$ 下、噪声方差 $\sigma^2/(1-u)$ 的输出密度。
同一残差 $G=(y-T)/\sigma$ 给，在零附近精确有

$$
Z_P(u,y):=\mathbb E_P[e^{u(s+G^2/2)};Y\in dy]/dy
=M_P(u)(1-u)^{-1/2}f_{P,u}(y).
\tag{109.31}
$$

有限计数和及 Gaussian 矩允许两次求导，于是

$$
V_{{\rm post},P}(y)-V_{{\rm prior},P}
=\tfrac12+\left.\partial_u^2\ln f_{P,u}(y)\right|_{u=0}.
\tag{109.32}
$$

其中 $1/2$ 来自 $-\tfrac12\ln(1-u)$，不是另加独立测量残差。
对混合目标的中心 Gaussian 二次信息量，矩母函数在零的固定邻域有限；
外部计数仍是有限和，因而同样允许两次求导。乘积与混合比较相减后，精确得到
$D_{\mathsf Q}-D'_{\mathsf Q}=\partial_u^2\ln(f_{\mathsf Q,u}/g_u)|_{u=0}$，
这里 $g_u$ 是混合目标的同样倾斜预测密度，不是重新校准后的信道。
与 $u$ 无关的共同调制在该式中消失。
若用复分析控制二阶导数，必须另证固定复邻域无零点及一致相对误差；
零处标量平滑或形式可微均不提供这一结论。

**剩余问题 109.7（完整信息方差仍未闭合）。** 对全部 (109.3)，
第 106 章目标 $\int f_x|D_x-R_*|\to0$ 仍未由本章证明，也没有原实际模型反例。
足以回接它的具体剩余义务是

$$
\int f_{\mathsf Q}|D_{\mathsf Q}-D'_{\mathsf Q}|dy\to0,
\qquad
\int|f_{\mathsf Q}-f'|\,|D'_{\mathsf Q}-R_*|dy\to0.
\tag{109.33}
$$

第一式需要中心标记抵消及小密度输出控制；第二式只支付参考残差，
而非再次乘整个 $Q^2$ 先验方差，但它仍需要尾部一致可积性。
已有参考定理与三角不等式随后给乘积结论，
原选中律回接成本 $C\varepsilon_xQ^2=o_{\mathbb P}(1)$ 不含逆噪声。

若仍对标记仅使用绝对矩，非零带给
$Q^{O(1)}e^{-c e^{2\Delta}}$，任意慢发散余量不足以使该界趋零。
这是充分估计未闭合，不是实际命题反例。
外部信息量的相关性、$h_2,h_4$ 与 $h_0$ 的差别、以及 (109.28) 的商项
都不能借标量结论删除。经典 Gauss/Poisson、theta 矩公式与指数族求导
分别归属成熟理论；本章新连接是原增长中央块的标记定位与无多项式损失的标量回接。
不据有限文献检索宣称全局原创，不推导零噪声或其他后验泛函。

## 追加锚（第 109 章后续增补区）

## 110. 高阶 Rényi 输出响应的统一边界与有限阶修正

**定理 110.1（从增长阶数到无穷阶的同纤维一致响应）。** 保持第 103、105、107、108 章的原实际模型、全部取整、完整计数后验、精确中心及同一 Gaussian 标量观测。信息量以 nats 计。令

$$
L=\ln(1/\sigma),\qquad L\to\infty,\qquad
\limsup L/Q^3<c_q/2,
\qquad b_x=\frac{\sqrt\delta}{2v_*},\quad v_*=\max_jv_j.
\tag{110.1}
$$

这里 $v_j=C_jp_j(1-p_j)/B^2$、$\delta=Q^{-1/2}$；$v_*$ 是原完整数组的经验最大值。
记 $\mathsf P_x^y$ 为原均匀大小 $q$ 支持先验下，给定数据及输出 $y$ 的完整计数后验，
$\nu=2\int\rho(s)^2ds$。对每个固定 $c>0,K<\infty$，

$$
\sup_{\substack{\alpha\in[c/\sqrt\delta,\infty]\\|y|\le K}}
\left|H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
-\frac\alpha{\alpha-1}\left(b_xy-\frac{y^2}{2\nu}\right)\right|
\longrightarrow0.
\tag{110.2}
$$

无穷阶的因子约定为一。收敛是在原实际数据概率下，对所有规定大小的确定支持一致，
pair/path 分别成立；整个双重上确界取在同一数据纤维 $x$ 上。
该结论不把不同阶数的最优实现当作共同实现，也不排列两个输出熵之差。

因此，对任意确定 $a_Q\sqrt\delta\to\infty$，

$$
\sup_{\substack{\alpha\in[a_Q,\infty]\\|y|\le K}}
\left|H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)-b_xy+\frac{y^2}{2\nu}\right|
\longrightarrow0.
\tag{110.3}
$$

若 $\alpha_Q\sqrt\delta\to c\in(0,\infty)$，则在同样范围内

$$
H_{\alpha_Q}(\mathsf P_x^y)-H_{\alpha_Q}(\mathsf P_x^0)-b_xy+\frac{y^2}{2\nu}
\longrightarrow\frac{y}{2c\rho_0}
\tag{110.4}
$$

一致于紧输出区间。有限阶因子在这一尺度留下真实常数项，不能直接删掉。
本章未分类更慢增长的阶数、无界输出或 Shannon 端点。

**证明：从原剖面取得缩小的谱隙。** 保持第 56 章

$$
a=(1+r)/2,\quad b=(1-r)/2,\quad
\theta=\frac{\ln(1+r)}{-\ln(1-r)},\quad
\kappa=1/a+\theta^2/b,
$$

$$
\rho(s)=\rho_0e^{-\kappa s^2/2},\quad
\rho_0=(4\pi\sqrt{ab})^{-1},\quad\gamma=\int\rho(s)ds.
\tag{110.5}
$$

在同一个实际好事件上，原完整 $V\to\gamma>0$，组数 $m_Q\le CQ^2$，
$\ln q=c_qQ^3+O(1)$，$\ln M=O(Q^3)$，以及

$$
e_j=(\mu_j-C_jp_j)/B,\qquad
\|e\|_2=O_{\mathbb P}(Q^{-5/2}),\qquad
\max_j|p_j-1/2|=O_{\mathbb P}(q^{-1/2}),\qquad
\sum_jC_j=O_{\mathbb P}(B^2).
\tag{110.6}
$$

取充分大固定 $K_0$，$R_Q=\sqrt{K_0\ln Q}$。第 56 章 (56.5)–(56.9) 的原有界取整与
第 69 章 (69.6) 的精确补偿给

$$
\max_{|j\delta|\le R_Q}
\left|\frac{v_j}{\delta\rho(j\delta)}-1\right|
=O_{\mathbb P}(Q^{-3/2}(1+\ln Q)^{3/2})=o_{\mathbb P}(\delta^2),
\qquad
\sum_{|j\delta|>R_Q}v_j\le Q^{-60}.
\tag{110.7}
$$

这里比较均值是原信号双 Poisson 点质量的 $2q$ 倍；原一、二行方差界给增长核心内的相对集中。
两个计数偏差仍分别为 $\sqrt\lambda j\delta-\xi$ 和
$(P/Q)\sqrt\lambda j\delta+\xi$，$\xi\in[0,1)$ 为原取整误差。
保留这两项的 Stirling 展开给 (110.7)，未更换幅度或计数线，path 行也未被设为独立。

对核心内非零 $j$，
$1-e^{-\kappa j^2\delta^2/2}\ge c\min(j^2\delta^2,1)$。
由于 (110.7) 的相对误差是 $o_{\mathbb P}(\delta^2)$，尾部又比 $v_0\asymp\delta$ 小，得到

$$
v_*=v_0\ \text{且唯一},\qquad
1-v_j/v_0\ge c_1\min(j^2\delta^2,1)\quad(j\ne0),
\qquad
1-v_{\pm1}/v_0\sim\kappa\delta^2/2.
\tag{110.8}
$$

这是从实际环境推出的缩小谱隙，不是新增正的固定谱隙假设。

选 $\ell<c_q/2$ 使 $L\le\ell Q^3$ 最终成立，再选固定 $\epsilon>0$ 使
$2\epsilon<c_q-\ell$。仅为证明分成
$\mathcal H=\{j:C_j\ge e^{\epsilon Q^3}\}$ 与其补集；$0,\pm1$ 及上述增长核心最终属于 $\mathcal H$。
对 $j\in\mathcal H\setminus\{0\}$ 置

$$
d_j^\circ=1-v_j/v_0,\qquad
w_j=\frac{v_j}{\alpha d_j^\circ},\qquad
m_j^\circ=-\frac{e_j}{d_j^\circ}.
\tag{110.9}
$$

$d_j^\circ$ 表示谱亏损，不是二项方差。按 $|j|$ 递增排列非零指标，以 $i$ 为秩。
核心内使用 $e^{-cx^2}/\min(x^2,1)\le C/x^2$，尾部使用 $v_j\le Q^{-60}$、$i\le CQ^2$，得

$$
w_i\le\frac{C}{\alpha\delta i^2},\qquad
w_1,w_2\asymp(\alpha\delta)^{-1},\qquad
\sum_{j\ne0}(m_j^\circ)^2\le C\delta^{-4}\|e\|_2^2=O_{\mathbb P}(Q^{-3}).
\tag{110.10}
$$

删除不在 $\mathcal H$ 的指标只减小它们的秩，故该上界仍适用。

**精确幂后验与临界能量分解。** 对有限 $\alpha>1$，令
$\mathsf P_{x,\alpha}(n)=\mathsf P_x(n)^\alpha/\sum\mathsf P_x^\alpha$。
在同一原标量 $T$ 上记其噪声 $\sigma/\sqrt\alpha$ 的预测密度为 $f_{\alpha}$。
有限 Gaussian 似然求和给经典恒等式

$$
H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
=\frac{-\ln[f_\alpha(y)/f_\alpha(0)]
+\alpha\ln[f_x(y)/f_x(0)]}{\alpha-1}.
\tag{110.11}
$$

先验的大熵项在此精确消去。第 105、108 章已给原普通输出密度

$$
\sup_{|y|\le K}\left|\ln\frac{f_x(y)}{f_x(0)}+\frac{y^2}{2\nu}\right|\to0.
\tag{110.12}
$$

现先在 $c/\sqrt\delta\le\alpha\le Q^6$ 上分析高组 Gaussian 比较。
令

$$
E_\alpha^G=\sum_{j\in\mathcal H}(\sqrt{v_j/\alpha}Z_j-e_j)^2,
\qquad c_*=1/(2v_0),\qquad h_y=V+\sqrt\delta y.
\tag{110.13}
$$

$Z_j$ 是辅助独立标准 Gaussian；完整 $V$ 和精确中心保留。
对每个非最大坐标的平方作 $e^{\alpha c_*X_j^2}$ 倾斜，因 $v_j<v_0$ 可积，
新 Gaussian 的均值和方差恰为 (110.9)。写

$$
R_\alpha=\sum_{j\in\mathcal H\setminus\{0\}}(\sqrt{w_j}Z_j+m_j^\circ)^2,
\qquad F_\alpha(h)=\Pr(R_\alpha\le h).
$$

最大坐标的平方密度保留为未归一化核，从而有限维精确分解为

$$
p_{E_\alpha^G}(h)=C_{x,\alpha}e^{-\alpha c_*h}r_\alpha(h),\qquad
r_\alpha(h)=\mathbb E\!\left[
\frac{\cosh(\alpha e_0\sqrt{h-R_\alpha}/v_0)}{\sqrt{h-R_\alpha}}
\mathbf1_{R_\alpha<h}\right],\quad h>0.
\tag{110.14}
$$

常数 $C_{x,\alpha}>0$ 与输出、噪声无关，未对它作近似。
本式没有把最大坐标在不可积临界点归一化，也没有延拓内部鞍点定理。

**有限数组的小球下界和对数凹性。** 置 $A=1/(\alpha\delta)$。
对每个固定 $h_0>0$，(110.10) 给

$$
F_\alpha(h_0)\ge e^{-C_{h_0}(1+A)}.
\tag{110.15}
$$

具体取 $N=\lceil K_1(1+A)\rceil$。在当前阶数范围内 $N=O(\delta^{-1/2})$，
比可用核心坐标数小；必要时缺失坐标补零。
尾部中心平方范数的均值至多 $CA/N$，由 Markov 至少以概率 $1/2$ 小于 $h_0/16$。
前 $N$ 个独立标准坐标限制为 $|Z_i|\le\eta i/N$，其能量至多 $CA\eta^2/N$，
而概率至少 $(c\eta)^NN!/N^N\ge e^{-CN}$。
取 $K_1$ 大、$\eta$ 小，再用原非中心均值范数趋零及三角不等式，得到 (110.15)。

$F_\alpha$ 关于正 $h$ 对数凹。确实，Gaussian 密度乘
凸集合 $\{(h,z):\|z\|^2\le h\}$ 的指标是联合对数凹函数，经典 Prékopa 边缘定理适用。
若采用光滑正函数版本，先用

$$
\varphi(z)\exp\{-n^{-1}\ln(1+e^{n^2(\|z\|^2-h)})\}
\tag{110.16}
$$

逼近；它正、光滑、联合对数凹且被可积 Gaussian 主控。
球面为 Gaussian 零测集，支配收敛及对数凹不等式的点态极限给所需指标版本。
非中心、非等方差均不改变此论证；未声称平方和密度本身对数凹。

$F_\alpha$ 在正能量区间光滑、递增。对数凹性和 $h/2$ 处的小球下界给，
在任一固定正能量紧区间上

$$
0\le(\ln F_\alpha)'(h)\le\frac{2[-\ln F_\alpha(h/2)]}{h}
\le D_\alpha:=C(1+1/(\alpha\delta)).
\tag{110.17}
$$

从 $r_\alpha$ 中去掉 cosh 得 $r_\alpha^0$。分 $R_\alpha\le h/2$ 与其余部分，
后者用 $F_\alpha'(t)\le D_\alpha F_\alpha(h)$ 积分平方根奇点，得到

$$
C^{-1}F_\alpha(h)\le r_\alpha^0(h)\le C(1+D_\alpha)F_\alpha(h),
\qquad
\alpha^{-1}\left|\ln\frac{r_\alpha(h)}{r_\alpha^0(h)}\right|
\le C|e_0|/v_0=O_{\mathbb P}(Q^{-2}).
\tag{110.18}
$$

这是每阶自由能的界，允许 $\alpha|e_0|/v_0$ 本身增大。
对全局卷积尾部，指标 $\pm1$ 的二维 Gaussian 密度至多 $C\alpha\delta$；
极坐标积分使这两个平方的和具有相同阶的密度上界，卷积其余非负平方不增大它。因此

$$
F_\alpha'(h)\le C\alpha\delta,\qquad
r_\alpha(h)\le C\alpha\delta\sqrt h\,e^{\alpha|e_0|\sqrt h/v_0},\quad h>0.
\tag{110.19}
$$

**噪声平方完成与输出差。** 对稍后所需的相邻噪声宽度 $\sigma'$，令
$u'=(\sigma')^2$、$s^2=\delta u'/\alpha$、
$z_y=h_y-\delta u'c_*$，以及 $\Phi_{u'}(h)=c_*h-\delta u'c_*^2/2$。
将 $r_\alpha$ 在负能量处延拓为零。能量尺度上的 Gaussian 卷积精确给

$$
g_{\alpha,\sigma'}(y)=C_{x,\alpha}\sqrt\delta\,
 e^{-\alpha\Phi_{u'}(h_y)}(r_\alpha*\varphi_s)(z_y).
\tag{110.20}
$$

其中 $g$ 是 $(E_\alpha^G-V)/\sqrt\delta+(\sigma'/\sqrt\alpha)G$ 的密度。
$V\to\gamma$、$\delta c_*$ 有界、$\sigma'\to0$，使紧输出的所有 $z_y$ 落在固定正能量紧区间。
由 (110.17)–(110.19)，在此区间

$$
\left|\ln\frac{(r_\alpha*\varphi_s)(z)}{F_\alpha(z)}\right|
\le C\{1+\ln(2+D_\alpha)+D_\alpha s+D_\alpha^2s^2
 +\alpha|e_0|/v_0\}+o(1).
\tag{110.21}
$$

证明是在稍大的正紧区间使用
$e^{-D_\alpha|E-z|}\le F_\alpha(E)/F_\alpha(z)\le e^{D_\alpha|E-z|}$。
上界用 $\mathbb E e^{D_\alpha s|G|}\le2e^{D_\alpha^2s^2/2}$，
下界只积分 $|G|\le1$。
区间外用 (110.19)，将 $\alpha|e_0|\sqrt E/v_0$ 吸收入 Gaussian 指数的固定比例：
$\sqrt E/(E-z)^2$ 在那里有界，且 $(|e_0|/v_0)\delta u'\to0$。
剩余尾部为多项式乘 $e^{-c/s^2}$，除以
$F_\alpha(z)\ge e^{-C(1+1/(\alpha\delta))}$ 仍趋零，
因为 $\alpha/(\delta u')$ 在整个指定阶数范围内压过该损失及多项式对数。

现在 $z_y-z_0=\sqrt\delta y$，故

$$
\frac1\alpha\left|\ln
\frac{(r_\alpha*\varphi_s)(z_y)}{(r_\alpha*\varphi_s)(z_0)}\right|
\le\frac C\alpha\{D_\alpha\sqrt\delta K+1+\ln(2+D_\alpha)
 +D_\alpha s+D_\alpha^2s^2\}+C|e_0|/v_0+o(1)\to0.
\tag{110.22}
$$

例如 $\sqrt\delta D_\alpha/\alpha\le
C(\sqrt\delta/\alpha+1/(\alpha^2\sqrt\delta))=O(\sqrt\delta)$，
$\ln(2+D_\alpha)/\alpha=O(\sqrt\delta\ln Q)$，且 $D_\alpha s\to0$ 一致成立。
(110.20) 在两个输出相减后归一化常数与有限噪声截距同时消失，得到

$$
-\alpha^{-1}\ln[g_{\alpha,\sigma'}(y)/g_{\alpha,\sigma'}(0)]
=b_xy+o_{\mathbb P}(1).
\tag{110.23}
$$

为支付整数舍入，还需噪声宽度的绝对比较。
若 $|u'/u-1|\le h_Q$ 且 $h_Q$ 指数小，(110.20) 的同一个 $C_{x,\alpha}$ 精确消去。
$\Phi$ 的变化至多 $C|u'-u|/\delta$，$z$ 的变化至多 $C|u'-u|$。
再用 (110.17)、(110.21)，给

$$
\alpha^{-1}|\ln g_{\alpha,\sigma'}(y)-\ln g_{\alpha,\sigma}(y)|
\le C|u'-u|/\delta+CD_\alpha|u'-u|/\alpha+o_{\mathbb P}(1)=o_{\mathbb P}(1).
\tag{110.24}
$$

这里分别在两点使用的 (110.21) 除以 $\alpha$ 后趋零，未隐藏噪声前因子。

**至 $Q^6$ 的原计数回接。** 对高组 $N=C_j$、$d=Np(1-p)$、
$z=(n-Np)/\sqrt d$，Stirling 给

$$
\ln\Pr\{\operatorname{Bin}(N,p)=n\}
=-\tfrac12\ln(2\pi d)-z^2/2+O((1+|z|^3)/\sqrt N).
\tag{110.25}
$$

在 $|z|\le N^{1/12}$ 内乘 $\alpha\le Q^6$ 后误差至多 $CQ^6N^{-1/4}$。
归一化 Gaussian 格点标准差 $\sqrt{d/\alpha}$ 仍为指数大；
区域外的全局二项 Gaussian 原子包络除以中央归一化量，给
$e^{C\alpha}\operatorname{poly}(\alpha)e^{-c\alpha N^{1/6}}$ 的尾界。
在更小的联合高组盒 $|z_j|\le Q^2$，累计至多 $CQ^2$ 个对数余项和单元积分误差，
归一化乘积幂律 $\mathsf Q_{x,\alpha}$ 与舍入 Gaussian $N(C_jp_j,d_j/\alpha)$ 满足

$$
\left|\frac{\mathsf Q_{x,\alpha}^{\mathcal H}(n)}
 {\Pr\{\operatorname{round}N(C_jp_j,d_j/\alpha)=n_j,\ j\in\mathcal H\}}-1\right|
\le\operatorname{poly}(Q)e^{-\epsilon Q^3/4}.
\tag{110.26}
$$

两侧删去的概率至多

$$
\operatorname{poly}(Q)e^{-c\alpha Q^4+C\alpha}.
\tag{110.27}
$$

保留尾指数中的 $\alpha$ 才能覆盖增长阶数：将统一原子包络升至 $\alpha$ 次方，
除以 $\sqrt{N/\alpha}$ 级中央归一化，再求 Gaussian 格点尾和，便得此式。

每个低组原元组的能量至多 $CQ^2e^{2\epsilon Q^3}/B^2$。
高组盒的 Gaussian 原像上，舍入使电荷范数改变至多 $\sqrt{m_Q}/(2B)$，
未舍入范数至多 $CQ^2$。于是对所有低组配置一致，原完整标量与比较标量相差至多

$$
\Delta_Q\le\operatorname{poly}(Q)(B^{-1}+B^{-2}e^{2\epsilon Q^3}),
\qquad h_Q=\frac{\Delta_Q}{\sigma/\sqrt\alpha}
\le\operatorname{poly}(Q)e^{-b_0Q^3}\to0.
\tag{110.28}
$$

这里 $\ln B=c_qQ^3/2+O(\ln Q)$，$\ell<c_q/2$、$c_q-2\epsilon>\ell$；
原半指数噪声条件正好支付此项。
令 $s_{out}=\sigma/\sqrt\alpha$。对 $|d|\le\Delta_Q$ 的精确核夹逼为

$$
(1+h_Q)^{-1/2}e^{-(h_Q+h_Q^2)/2}
\varphi_{s_{out}/\sqrt{1+h_Q}}(z)
\le\varphi_{s_{out}}(z+d)
\le(1-h_Q)^{-1/2}e^{h_Q/2}
\varphi_{s_{out}/\sqrt{1-h_Q}}(z).
\tag{110.29}
$$

对盒内原像和全部低组积分，(110.26)–(110.29) 给相邻宽度下 Gaussian 密度的相对夹逼。
尾部必须在稀有输出密度尺度支付：紧输出下
$g_{\alpha,\sigma'}(y)\ge e^{-C\alpha/\delta}$。
可直接留最大平方不积分；其余未倾斜平方的均值为 $O(1/\alpha)+o(1)$，
至少以概率 $1/2$ 处于固定小能量内。能量噪声在一个标准差内也有固定正概率，
剩余正紧能量处的最大平方密度由精确公式给所需下界。
故尾密度与此下界之比至多多项式乘
$\sigma^{-1}e^{-c\alpha Q^4+C\alpha+C\alpha/\delta}\to0$，
其中 $L=O(Q^3)$。结合 (110.24)，

$$
\sup_{\substack{c/\sqrt\delta\le\alpha\le Q^6\\|y|\le K}}
\alpha^{-1}\left|\ln f_{\mathsf Q_{x,\alpha},\sigma/\sqrt\alpha}(y)
-\ln g_{\alpha,\sigma}(y)\right|\to0.
\tag{110.30}
$$

没有把加性多项式误差除以稀有密度，完整 $V$ 也没有被截断。

**同一稀有输出下的固定总数修正。** 原精确选中律仍为
$\mathsf P_x(n)=\mathscr L_x(\sum n_j)\mathsf Q_x(n)$，完整盒在原好事件上可行。沿用第 107、108 章的全局对数界

$$
-C(D(n)^2/q+q^{-1/2})\le\ln\mathscr L_x(n)
\le C(B^2V/q+q^{-1/2}),\qquad D(n)=\sum_j(n_j-C_jp_j).
\tag{110.31}
$$

(110.26)–(110.27) 同时给
$\sup_{1\le\alpha\le Q^6}\mathbb E_{\mathsf Q_{x,\alpha}}E=O_{\mathbb P}(1)$。
盒外用 $E\le O_{\mathbb P}(B^2)$ 乘 (110.27)，$Q^4$ 指数压过 $\ln B^2=O(Q^3)$；
Gaussian 侧用直接尾矩。因此不沿用未核实的固定阶数矩常数。

需要的稀有加权矩事实是：若 $E\ge0$、$\mathbb EE\le A$，以
$e^{-(E-h)^2/(2w^2)}$ 重加权，$|h|\le H$、$0<w\le1$，则新均值仍由只依赖 $A,H$ 的常数控制。
因 $\Pr(E\le2A)\ge1/2$，归一化分母至少为
$\tfrac12e^{-(2A+H)^2/(2w^2)}$；在充分大固定 $R$ 之外，
尾均值之比由 $2\sup_{u\ge R}u e^{-u^2/(8w^2)}$ 控制。
该论证允许任意稀有的能量壳。

原向量上的 Cauchy–Schwarz 给
$D(n)^2/q\le C\delta(E(n)+\|e\|^2)$。
相应幂后验的预测密度比精确为

$$
\frac{f_{\mathsf P_{x,\alpha},\sigma/\sqrt\alpha}(y)}
 {f_{\mathsf Q_{x,\alpha},\sigma/\sqrt\alpha}(y)}
=\frac{\mathbb E_{\mathsf Q_{x,\alpha},y}\mathscr L_x^\alpha}
 {\mathbb E_{\mathsf Q_{x,\alpha}}\mathscr L_x^\alpha}.
\tag{110.32}
$$

分子就是同一原 Gaussian 输出权重下的期望。
由 (110.31)、上述矩界及 Jensen，两个期望的对数下界为 $-C\alpha\delta$，
上界为 $C\alpha(B^2V/q+q^{-1/2})$。所以

$$
\sup_{\substack{c/\sqrt\delta\le\alpha\le Q^6\\|y|\le K}}
\alpha^{-1}\left|\ln\frac{f_{\mathsf P_{x,\alpha},\sigma/\sqrt\alpha}(y)}
 {f_{\mathsf Q_{x,\alpha},\sigma/\sqrt\alpha}(y)}\right|=O_{\mathbb P}(\delta)\to0.
\tag{110.33}
$$

(110.23)、(110.30)、(110.33) 合起来证明
$-\alpha^{-1}\ln[f_\alpha(y)/f_\alpha(0)]=b_xy+o_{\mathbb P}(1)$，
一致于当前整个多项式阶数区间。这一步保留了原固定总数选择，未把实际后验设为乘积律。

**与无穷阶的真正重叠。** 对任意 $N$ 原子概率向量和 $\alpha>1$，

$$
0\le H_\alpha-H_\infty\le\frac{H_\infty}{\alpha-1}
\le\frac{\ln N}{\alpha-1}.
\tag{110.34}
$$

它由 $p_{\max}^\alpha\le\sum p_i^\alpha\le p_{\max}^{\alpha-1}$ 直接推出。
原计数后验的原子数至多 $(M+1)^{m_Q}$，故 $\ln N\le CQ^5$。
分别在 $y$ 和零输出应用此界，再作三角不等式，得

$$
\sup_{\alpha\ge Q^6,\,y}
\left|[H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)]
-[H_\infty(\mathsf P_x^y)-H_\infty(\mathsf P_x^0)]\right|\le CQ^{-1}.
\tag{110.35}
$$

这不使用输出熵差关于阶数的单调性。
计数／Gaussian 证明到达 $Q^6$，此界从 $Q^6$ 延伸到无穷阶；
超多项式阶数不再要求有效噪声大于整数网格。

将多项式区间的结论和 (110.12) 代入 (110.11)，得 (110.2) 的有限区间。
对余下阶数用 (110.35) 与第 108 章已证端点响应，
把一改为 $\alpha/(\alpha-1)$ 的代价至多 $C(1+|b_x|)/Q^6=o_{\mathbb P}(1)$。
所以 (110.2) 覆盖整个区间。
若 $a_Q\sqrt\delta\to\infty$，被删有限阶因子的贡献一致趋零，得到 (110.3)。
若 $\alpha_Q\sqrt\delta\to c$，只在有界剩余系数中使用 $v_*/\delta\to\rho_0$，即
$b_x/(\alpha_Q-1)\to1/(2c\rho_0)$，得到 (110.4)。
从未把 $v_*$ 在放大的主中心中替换成极限。

最后，噪声平方完成中的 $-\delta\sigma^2/(8v_*^2)$ 可以发散，
但在两个输出之差中精确取消，其余影响已由 (110.21)–(110.24) 支付。
所有估计位于同一实际数据好事件，原一、二行概率界对支持一致且对 pair/path 分别成立；
穷尽紧常数即给声明的概率范围，证毕。

经典 Gibbs/Rényi 恒等式、Prékopa 定理、Stirling 估计及有限支持熵界各归成熟理论。
本章的模型内连接是实际缩小谱隙、非最大模的有限小球控制、稀有输出下的原计数回接和无穷阶重叠。
没有典型单模凝聚、期望熵、全阶 Shannon 延拓、零噪声或全局原创结论。

## 追加锚（第 110 章后续增补区）

## 111. 保持整数坐标的方差归约与无维数损失的补偿混叠

**定理 111.1（原完整方差熵问题的格点大组归约）。** 保持第 101、106、109 章的原实际模型、固定幅度与 $\beta$、全部取整、经验中心和共同 Gaussian 观测。令

$$
\delta=Q^{-1/2},\quad B^2=q/Q^{5/2},\quad
\mathcal B=B^2\sqrt\delta=q/Q^{11/4},\quad
L=\ln(1/\sigma)\to\infty,\quad
\Delta=\ln\mathcal B-L\to\infty.
\tag{111.1}
$$

原标量仍为

$$
T=\mathcal B^{-1}\sum_j(R_j-\mu_j)^2-V/\sqrt\delta,\qquad Y=T+\sigma G.
\tag{111.2}
$$

记原选中律为 $\mathsf P_x$、精确先验惊异为 $S=-\ln\mathsf P_x(R)$。
保持此前固定的对数核心 $H$ 及其原有限系数

$$
A=V_H/\sqrt\delta,\quad \nu_0=2\sum_Hw_j^2,\quad
\kappa_3=8\sum_Hw_j^3,\quad\Lambda=\nu_0+\sigma^2,
\quad C_x=A^2\kappa_3/\Lambda^3-2A\nu_0/\Lambda^2,
$$

$$
D_x(y)=V_{\mathrm{post},x}(y)-V_{\mathrm{prior},x}+A^2/\Lambda-C_xy,
\qquad
R_*(y)=\frac{29}{6}-3\sqrt2+
\left(3\sqrt2+\frac8{\sqrt3}-9\right)y^2/\nu.
\tag{111.3}
$$

其中 $V_{\mathrm{prior},x}=\operatorname{Var}_{\mathsf P_x}S$ 精确保留，$\nu=2g_0$。
下述明确的辅助格点律 $\mathsf Q_x^{\mathrm{lat}}$，使用同一个整数坐标上的能量函数、原中心及同一个 $G$，满足

$$
\|f_xD_x-f_{\mathrm{lat}}D_{\mathrm{lat}}\|_{L^1}\to0,
\qquad \int(1+y^2)|f_x(y)-f_{\mathrm{lat}}(y)|dy\to0.
\tag{111.4}
$$

收敛是在原实际数据概率下，对所有规定大小的确定支持一致，pair/path 分别成立。
所以

$$
\int f_x|D_x-R_*|\to0
\quad\Longleftrightarrow\quad
\int f_{\mathrm{lat}}|D_{\mathrm{lat}}-R_*|\to0.
\tag{111.5}
$$

这是常数方差尺度的归约。两侧极限本身在任意慢发散 $\Delta$ 下仍未解决；
第 106 章较强余量下的结论与第 109 章标量平滑结论均保留。

**辅助律与原好事件。** 原校准乘积律为
$\mathsf Q_x=\prod_j\operatorname{Bin}(C_j,p_j)$，置

$$
m_j=C_jp_j,\quad d_j=C_jp_j(1-p_j),\quad
v_j=d_j/B^2,\quad w_j=d_j/\mathcal B,\quad e_j=(\mu_j-m_j)/B.
$$

第 101、106 章的原选择比较给

$$
\mathsf P_x=\mathscr L_x\mathsf Q_x,\quad0\le\mathscr L_x\le C,
\quad a_x=\|\mathscr L_x-1\|_{2,\mathsf Q}=O_{\mathbb P}(Q^{-5/2}),
\quad\mathbb E_{\mathsf P}(\ln\mathscr L_x)^2\le Ca_x^2,
\quad\|e\|^2\le a_x^2V.
\tag{111.6}
$$

这里没有将原选中律或实际 path 行设为独立。
第 90 章的过渡组计数取固定阈值 $3600$，得到

$$
\mathcal J_x=\{j:d_j\ge Q^{3600}\},\quad
N_x=|\mathcal J_x|=O(Q^2),\quad
|\{j\notin\mathcal J_x:C_j>0\}|=O(1),\quad H\subset\mathcal J_x.
\tag{111.7}
$$

原率剖面的网格为 $Q^{-2}$，对数期望为 $Q^3(c_q-I(u))+O(\ln Q)$，
正率边界的斜率非零；过渡带宽 $O(\ln Q/Q^3)$ 只含有界个网格点。
极低均值组为空，高均值组由原一、二行比较集中。这是原模型已有的占用结论。
同一好事件还有 $p_j\in[1/4,3/4]$、$V=O(1)$、
$\sum_jw_j^2=O(1)$、$\max_jv_j\le C\delta$，
以及原中心区间中的至少 $c/\delta$ 个因子满足
$cq/Q^3\le d_j\le Cq/Q^3$。

对每个 $j\in\mathcal J_x$，用整数上的归一化离散 Gaussian

$$
g_j(k)=Z_{m_j,d_j}^{-1}e^{-(k-m_j)^2/(2d_j)},\qquad k\in\mathbb Z
\tag{111.8}
$$

替换该二项质量，其余因子完整保留。大组辅助支持是 $\mathbb Z$，不再是原有限计数盒；
这明示为比较概率律，不改变原模型。其惊异以自己的精确期望中心化，记为 $s_{\mathrm{lat}}$，
$V_{\mathrm{lat}}=\operatorname{Var}s_{\mathrm{lat}}$。
在原函数 (111.2) 中代入辅助整数元组 $K$，定义
$Y^{\mathrm{lat}}=T(K)+\sigma G$、$U^{\mathrm{lat}}=s_{\mathrm{lat}}+G^2/2$，并令

$$
D_{\mathrm{lat}}(y)=\operatorname{Var}(U^{\mathrm{lat}}\mid Y^{\mathrm{lat}}=y)
-V_{\mathrm{lat}}+A^2/\Lambda-C_xy.
\tag{111.9}
$$

$A,\Lambda,C_x$ 仍取原观测值，没有重新校准；未在负辅助计数上定义原选择权重。

**单因子的带惊异有符号质量界。** 若 $b=\operatorname{Bin}(n,p)$、$m=np$、$d=np(1-p)$，
令 $q(k)=(k-m)^2/(2d)$、$c_g=\mathbb E_gq$，
$s_b=-\ln b-\mathbb E_b(-\ln b)$、$s_g=q-c_g$。
在原支持外将二项有符号质量延拓为零。对固定整数 $0\le h\le4$，

$$
\sum_{k\in\mathbb Z}|b(k)s_b(k)^h-g(k)s_g(k)^h|\le C_hd^{-1/8}.
\tag{111.10}
$$

确实，在 $|k-m|\le d^{5/8}$ 上，统一 Stirling 余项给

$$
-\ln b(k)=\tfrac12\ln(2\pi d)+q(k)+O(d^{-1/8}),\qquad b(k)/g(k)=1+O(d^{-1/8}).
\tag{111.11}
$$

三次率函数余项为 $O(|k-m|^3/d^2)$。两侧尾质量至多 $Ce^{-cd^{1/4}}$；
原支持上 $-\ln b\le n\ln4$、$q\le Cn$，故固定次多项式加权尾仍可支付。
$\mathbb E_bq=1/2$ 精确成立，而实 Gaussian 正规化的 Poisson 求和给

$$
c_g=1/2+O(de^{-cd}),\qquad \sup_{m,d\ge d_0}\mathbb E_g|s_g|^h<\infty.
\tag{111.12}
$$

因此中央 $|s_b-s_g|\le Cd^{-1/8}$。用幂差不等式与有界中心矩，再加两侧尾界，得 (111.10)。
正规化求导由绝对 Gaussian 收敛保证，不除以复 theta 函数。
特别地，精确中心方差差也至多 $Cd^{-1/8}$。

**共同核的直接收缩。** 在完整整数元组空间上定义
$\eta_h(k)=\mathsf Q_x(k)s_{\mathsf Q}(k)^h$ 与
$\eta_h^{\mathrm{lat}}(k)=\mathsf Q_x^{\mathrm{lat}}(k)s_{\mathrm{lat}}(k)^h$。
$h\le2$ 的展开至多有 $O(Q^4)$ 个积，每积至多两个因子带惊异标记。
逐一替换 $O(Q^2)$ 个大组，(111.10) 的误差为 $CQ^{-450}$，其余带标记因子具有有界全变差。
所以全绝对质量范数满足

$$
\max_{h\le2}\|\eta_h-\eta_h^{\mathrm{lat}}\|_{\mathrm{TV}}\le CQ^{-444}.
\tag{111.13}
$$

这里 TV 不附 $1/2$；精确中心惊异已按坐标展开，未留下巨大的熵均值误差。
对同一个能量函数，核

$$
K_r(k,y)=\left(\frac{y-T(k)}\sigma\right)^{2r}\varphi_\sigma(y-T(k))
\quad\text{满足}\quad\int K_r(k,y)dy=\mathbb EG^{2r}.
\tag{111.14}
$$

它对有符号输入的 $L^1$ 算子范数与 $\sigma$ 无关。
若 $q_h(y)dy=\mathbb E[(s_{\mathsf Q}+G^2/2)^h;Y\in dy]$，辅助侧类似，则

$$
q_h-q_h^{\mathrm{lat}}
=\sum_{r=0}^h{h\choose r}2^{-r}K_r(\eta_{h-r}-\eta_{h-r}^{\mathrm{lat}}),
\qquad\max_{h\le2}\|q_h-q_h^{\mathrm{lat}}\|_1\le CQ^{-444}.
\tag{111.15}
$$

该步对每个正 $\sigma$ 成立；不发生能量位移、Fourier 截断或小密度除法。
若换成移动坐标的连续耦合，此共同核收缩不能原样使用。

两侧中心惊异的四阶范数为 $O(Q)$，输出四阶矩有界。
后者由 $\sum w_j^2=O(1)$、$\max w_j=O(\sqrt\delta)$ 的中心二次和给出；
线性非中心项的平方系数和为
$4\delta^{-1}\sum v_je_j^2\le C\|e\|^2$。
离散 Gaussian 的标准化矩与连续 Gaussian 相差多项式乘 $e^{-cd_j}$，
在 $d_j\ge Q^{3600}$ 上累计仍小于任意 $Q$ 的负幂；外部原二项坐标保留。

**条件均值平方和原选择的支付。** 对 $f=q_0$，未归一化条件方差为
$\mathcal V=q_2-q_1^2/f$。
令 $\epsilon_h$ 是两侧 $q_h$ 的 $L^1$ 差。将条件均值截到 $[-b,b]$，利用
$q_1^2/f=\sup_z(2zq_1-z^2f)$ 与条件 Jensen，得到

$$
\|\mathcal V-\mathcal V^{\mathrm{lat}}\|_1
\le\epsilon_2+2b\epsilon_1+b^2\epsilon_0+
\frac{\mathbb E|U|^4+\mathbb E|U^{\mathrm{lat}}|^4}{b^2}.
\tag{111.16}
$$

取 $b=Q^{10}$，用 (111.15) 与四阶矩界得 $O(Q^{-16})$。
精确先验方差差至多 $CN_xQ^{-450}=CQ^{-448}$；
质量差乘 $V_{\mathsf Q}=O(Q^2)$ 亦可支付。
输出四阶矩还给
$\int y^2|f_{\mathsf Q}-f_{\mathrm{lat}}|\le C\|f_{\mathsf Q}-f_{\mathrm{lat}}\|_1^{1/2}$。
因此乘原 $A^2/\Lambda=O(\delta^{-1})$、$C_x=O(\delta^{-1/2})$ 的费用仍趋零。

第 101 章同一通道的选中密度比较，在 (111.6) 下给

$$
\|[\mathcal V_{\mathsf P,S+G^2/2}-V_{\mathrm{prior},x}f_x]
-[\mathcal V_{\mathsf Q,s_{\mathsf Q}+G^2/2}-V_{\mathsf Q}f_{\mathsf Q}]\|_1
\le Ca_xQ^2=o_{\mathbb P}(1).
\tag{111.17}
$$

它先控制 $\ln\mathscr L_x$ 带来的惊异改变，再按条件密度比是否低于 $1/2$ 分割，
以 Cauchy–Schwarz 支付；不要求输出密度下界。
另有 $\int(1+y^2)|f_x-f_{\mathsf Q}|\le Ca_x$。
有限系数项费用至多 $Ca_x(\delta^{-1}+\delta^{-1/2}\|Y\|_2)=o_{\mathbb P}(1)$。
原 Bayes 恒等式将 $\operatorname{Var}(S+G^2/2\mid Y=y)$ 识别为实际后验方差熵；
条件输出密度和噪声正规化常数在条件方差中精确消去。
于是 (111.4) 成立。用固定二次多项式 $R_*$ 和三角不等式得 (111.5)，证毕。
该比较甚至不需 $\sigma\mathcal B\ge1$；本章的混叠结论仍在 (111.1) 下使用。

**定理 111.2（完整补偿的混叠界没有多项式维数费用）。** 对上述同一个辅助数组，
在第 109 章非零半整数条带上，将质量、一阶和二阶惊异变换按下面的复频率系数补偿，
其绝对积分和至多

$$
Ce^{-c e^{2\Delta}}.
\tag{111.18}
$$

原校准二项乘积律使用相同补偿系数时，上界为
$Ce^{-c e^{2\Delta}}+O(Q^{-400})$。
该结论对全部实际经验扭转成立，且不要求它们具有定量算术分离。

**证明：有限 Gaussian 积分。** 对大组辅助连续标准 Gaussian $Z_j$，置

$$
X=\tfrac12\sum_{\mathcal J_x}(Z_j^2-1),\quad
T_a=\sum_{\mathcal J_x}w_j(Z_j-a_j)^2-c,\quad a_j=(\mu_j-m_j)/\sqrt{d_j},
$$

$$
z_j=1-2isw_j,\quad r_{0j}=-2sw_ja_j,\quad r_j=r_{0j}+\xi_j,
\quad
P(s)=e^{is(\sum w_ja_j^2-c)}\prod_jz_j^{-1/2}.
\tag{111.19}
$$

平方根从 $s=0$ 连续选取。Gaussian 平方完成给

$$
F(s,\xi)=\mathbb Ee^{isT_a+i\xi\cdot Z}
=P(s)\exp\left(-\tfrac12\sum_jr_j^2/z_j\right).
\tag{111.20}
$$

基准复均值、方差和扭转差为

$$
\mu_0=\tfrac12\sum_j(z_j^{-1}-1)-\tfrac12\sum_jr_{0j}^2z_j^{-2},
\quad v_0^G=\tfrac12\sum_jz_j^{-2}-\sum_jr_{0j}^2z_j^{-3},
$$

$$
K_1=\sum_j(r_j^2-r_{0j}^2)z_j^{-2},\qquad
K_2=\sum_j(r_j^2-r_{0j}^2)z_j^{-3}.
\tag{111.21}
$$

令 $M_h=\mathbb E[X^he^{isT_a+i\xi\cdot Z}]$。在 $|u|<1/2$ 内对
Gaussian 可积的 $e^{uX}$ 积分求两次导数，精确得到

$$
M_1-\mu_0M_0=-K_1F/2,
\qquad M_2-2\mu_0M_1+(\mu_0^2-v_0^G)M_0=F(K_1^2/4-K_2).
\tag{111.22}
$$

这属于经典 Gaussian 二次型积分。关键的维数一致估计如下：
若 $E=\sum r_j^2$、$E_0=\sum r_{0j}^2$、$B_s=1+4s^2w_{\max}^2$，则

$$
|F|\le|P(s)|e^{-E/(2B_s)},\qquad |K_1|+|K_2|\le2(E+E_0).
\tag{111.23}
$$

$B_s,E_0$ 有界时，聚合扭转能量的多项式被其自身 Gaussian 衰减吸收，
所以三个补偿量之和至多 $C|P(s)|$，与维数和任意实向量 $\xi$ 无关。
在整个 $|s|\le C/\sqrt\delta$ 条带偏移上，原数组确实满足

$$
B_s\le C,\qquad
E_0=4s^2\delta^{-1}\sum_jv_je_j^2\le Cs^2a_x^2
=O_{\mathbb P}(a_x^2/\delta)=o_{\mathbb P}(1).
\tag{111.24}
$$

**全部 Poisson 模之和。** 对整数线性扭转 $b_j$，第 $k_j\in\mathbb Z$ 个模的实扭转为

$$
\xi_j(k_j)=\sqrt{d_j}(b_j-2\pi k_j),\qquad
r_j(k_j)=r_{0j}+\sqrt{d_j}(b_j-2\pi k_j).
\tag{111.25}
$$

同时保留相位 $e^{i\sum_j(b_j-2\pi k_j)m_j}$ 和原截距相位，二者模为一。
总正规化乘数为
$\prod_j\sqrt{2\pi d_j}/Z_{m_j,d_j}=1+O(N_xe^{-cQ^{3600}})$。
格点惊异的精确中心比 $X$ 多常数
$\epsilon_c=\sum_j(1/2-c_{g_j})$；将 $\mu_0$ 同时改为 $\mu_0+\epsilon_c$，(111.22) 不变。

固定 $B_*$ 下，对每个平移都有

$$
\sum_{k\in\mathbb Z}
 e^{-[r_0+\sqrt d(b-2\pi k)]^2/(4B_*)}\le1+Ce^{-cd}.
\tag{111.26}
$$

留一个最近点，其项至多一；其余点距零至少 $\pi\sqrt d$，逐项求和。
最近点并列时该界仍成立。先把聚合多项式吸收到较弱指数，再逐坐标乘积，得到

$$
\sum_{k\in\mathbb Z^{N_x}}(1+E(k)^2+E_0^2)e^{-E(k)/(2B_s)}
\le C\prod_j(1+Ce^{-cd_j})\le C.
\tag{111.27}
$$

最后一个常数由 $N_x=O(Q^2)$、$d_j\ge Q^{3600}$ 保证，没有隐藏 $C^{N_x}$。
非大组中仅 $O(1)$ 个被占用，保留其共同惊异—能量变换
$A_E,B_E,C_E$，分别为零、一、二阶标记；固定中心矩给
$|A_E|\le1$、$|B_E|\le C$、$|C_E-V_EA_E|\le C$。
此处只用比较乘积律中的大组／其余组独立，不分离单组惊异与自己的能量。

令 $M_h(s,b)$ 现在表示完整格点大组与原其余组的计数变换，置
$m_0(s)=\mu_0(s)+\epsilon_c$、$v_0(s)=v_0^G(s)+V_E$、
$\Pi(s)=\prod_{\mathcal J_x}|1-2isw_j|^{-1/2}$。
二阶补偿展开为大组二阶补偿乘 $A_E$、两倍大组一阶补偿乘 $B_E$，
以及大组质量乘 $C_E-V_EA_E$。由上述各界，

$$
|M_0|+|M_1-m_0M_0|+
|M_2-2m_0M_1+(m_0^2-v_0)M_0|\le C\Pi(s).
\tag{111.28}
$$

若 $k_0=v_0-V_{\mathrm{lat}}$，末项精确等于
$(M_2-V_{\mathrm{lat}}M_0)-2m_0M_1+(m_0^2-k_0)M_0$；
没有将先验方差换成主阶近似。

**原条带与同一噪声。** 在 $t_\ell=\pi\ell\mathcal B$、$t=t_\ell+s$ 上，
整数平方的奇偶恒等式给原经验扭转
$b_{\ell,j}=\pi\ell(1-2\mu_j)$ 和单位相位
$\omega_\ell=e^{i\pi\ell(\sum\mu_j^2-B^2V)}$。
对含同一 $G$ 的格点矩密度，定义

$$
\mathcal C_0=\widehat q_0^{\mathrm{lat}},\quad
\mathcal C_1=\widehat q_1^{\mathrm{lat}}-m_0(s)\widehat q_0^{\mathrm{lat}},\quad
\mathcal C_2=\widehat q_2^{\mathrm{lat}}-2m_0(s)\widehat q_1^{\mathrm{lat}}
 +(m_0(s)^2-v_0(s))\widehat q_0^{\mathrm{lat}}.
\tag{111.29}
$$

噪声矩变换恰为
$h_0=e^{-\sigma^2t^2/2}$、
$h_2=(1-\sigma^2t^2)e^{-\sigma^2t^2/2}$、
$h_4=(3-6\sigma^2t^2+\sigma^4t^4)e^{-\sigma^2t^2/2}$。
除单位相位外，三项分别是
$h_0M_0$，$h_0(M_1-m_0M_0)+h_2M_0/2$，以及

$$
h_0[M_2-2m_0M_1+(m_0^2-v_0)M_0]
+h_2(M_1-m_0M_0)+h_4M_0/4.
\tag{111.30}
$$

原中心区有 $c/\delta$ 个 $w_j^2\ge c\delta$，beta 积分给
$\int\Pi(s)ds\le C$。
第 109 章条带的偏移宽度为 $O(\mathcal B/(q/Q^3))=O(\delta^{-1/2})$；
非零条带上 $|t|\ge c|\ell|\mathcal B$。
吸收 $h_2,h_4$ 的多项式到较弱 Gaussian 指数，遂得

$$
\sum_{\ell\ne0}\int_{\text{条带 }\ell}\sum_{h=0}^2|\mathcal C_h(t)|dt
\le C\sum_{\ell\ne0}e^{-c\ell^2e^{2\Delta}}
\le Ce^{-c'e^{2\Delta}}.
\tag{111.31}
$$

原二项乘积律的回接需要 Fourier 的 $L^1$ 界，不能仅引用 (111.15)。
对带标记积逐项替换时，除差因子和至多两个标记外，保留十六个原中央因子；
它们可以是二项或离散 Gaussian，第 106 章同一个周期 Gauss 包络仍适用。
该包络一个周期的积分为 $O((q/Q^3)^{-1})$。
$\sigma\mathcal B\ge1$ 时，用 Gaussian 加权的周期上确界求和，得到总积分 $O(Q^{1/4})$。
所以

$$
\max_{h\le2}\|\widehat q_h-\widehat q_h^{\mathrm{lat}}\|_1
\le CQ^4Q^2Q^{-450}Q^{1/4}\le CQ^{-440}.
\tag{111.32}
$$

各条带互不相交，其上 $|m_0|\le CQ^{1/2}$、$|v_0|\le CQ^2$。
乘这些系数的总费用小于 $CQ^{-400}$，证明原乘积律版本。
返回原选中律仍使用 (111.17) 的全输出方差比较，不宣称额外的逐频选中界，证毕。

**命题 111.3（只减先验方差的任意扭转估计存在增长项）。** 在原渐近权重剖面下，
取固定非零偏移 $s$，选一个原中央坐标 $j_*$，并在辅助 Gaussian 公式中取
$\xi_j=\mathbf1_{j=j_*}$。置 $A_{\mathrm{bulk}}=\sum_{\mathcal J_x}w_j$、
$V_G=N_x/2$、$\alpha_0=F(s,\xi)/F(s,0)$。连续 Gaussian 的分母由 (111.20) 显式非零。
从 (111.21)–(111.22) 精确得到

$$
[M_2(s,\xi)-V_GF(s,\xi)]
-\alpha_0[M_2(s,0)-V_GF(s,0)]
=F(s,\xi)(-\mu_0K_1+K_1^2/4-K_2).
\tag{111.33}
$$

原剖面给 $A_{\mathrm{bulk}}\sim\gamma/\sqrt\delta$、
$2\sum w_j^2\to\nu$、$\max w_j\to0$、$\sum r_{0j}^2=o_{\mathbb P}(1)$。
对固定 $s$ 展开 $z_j^{-1}$，得 $\mu_0/A_{\mathrm{bulk}}\to is$；
$K_1,K_2\to1$，且 $|F(s,\xi)|\to e^{-\nu s^2/2-1/2}$。
于是 (111.33) 左边的绝对值除以 $A_{\mathrm{bulk}}$ 趋于

$$
|s|e^{-\nu s^2/2-1/2}>0.
\tag{111.34}
$$

这反驳“任意实扭转下，只减精确先验方差及共同质量调制就获得有界二阶标记”的参考估计。
它没有证明所选扭转等于某个实际经验混叠，也没有反驳原方差熵目标。

**剩余接口：频率补偿不等于输出条件化。** 令 $f,q_1,q_2$ 为格点律矩密度，
$g,r_1,r_2$ 为第 109 章保留的混合 Gaussian 参考；各自取精确中心惊异和先验方差。
置 $m=r_1/g$、$v=r_2/g-m^2$、$d_h=q_h-r_h$，其中 $r_0=g$，
$\Delta V=V_{\mathrm{lat}}-V_{\mathrm{ref}}=o_{\mathbb P}(1)$。
同一原有限校正系数消去后，逐输出精确恒等式为

$$
f(D_{\mathrm{lat}}-D_{\mathrm{ref}})
=d_2-2md_1+(m^2-v)d_0
-\frac{(d_1-md_0)^2}{f}-\Delta V f.
\tag{111.35}
$$

$m_0(s),v_0(s)$ 是复频率函数；它们的逆 Fourier 作用是乘子，
不等于乘上这里的实条件均值 $m(y)$、条件方差 $v(y)$。
将这些乘子分别取绝对值拆开，可以重新引入增长的 $A,A^2$；
任意慢发散 $\Delta$ 不能支付这样的费用。
尚缺的是 (111.35) 完整非线性表达式的全输出估计与尾部控制，
或等价的归一化惊异倾斜二阶导数控制。
逐项绝对收敛只是充分条件；若有共同的有符号抵消，不应把它误当必要条件。
一个充分的尾部判据是：对每个正容差 $\eta$，先取输出截断 $K\to\infty$，再取原规模上极限，
所有固定支持中事件
$\int_{|y|>K}f|D_{\mathrm{lat}}-D_{\mathrm{ref}}|>\eta$ 的最大概率趋零，pair/path 分别结算。
已有 $\|s\|_4=O(Q)$ 不能单独支付减去增长方差后的尾部。
本章的归约与无维数损失混叠界缩小了缺口，未宣布该接口闭合。

## 追加锚（第 111 章后续增补区）

## 112. 逆平方谱端的小球导数与 Rényi 输出的临界修正

**定理 112.1（原经验有限数组的谱端修正）。** 保持第 110 章的原完整计数后验、固定参数、取整、精确中心及同一带噪标量，信息量以 nats 计。仍假设

$$
L=\ln(1/\sigma)\to\infty,\qquad \limsup L/Q^3<c_q/2.
\tag{112.1}
$$

保留 $v_j=C_jp_j(1-p_j)/B^2$、$v_*=\max_jv_j$、$b_x=\sqrt\delta/(2v_*)$。
用 (110.5) 的原剖面参数定义两个不同的常数

$$
C_0=\frac{\pi^2\rho_0}{\kappa},\qquad C_{\mathrm{edge}}=\frac{C_0}{\gamma^2}.
\tag{112.2}
$$

对每个固定 $c>0,K<\infty$，有

$$
\sup_{\substack{\alpha\in[c\delta^{-1/4},\infty]\\|y|\le K}}
\left|H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
-\frac\alpha{\alpha-1}
\left[b_xy-\frac{y^2}{2\nu}-\frac{C_{\mathrm{edge}}y}{\alpha^2\sqrt\delta}\right]\right|
\longrightarrow0.
\tag{112.3}
$$

在无穷阶约定因子为一、$\alpha^{-2}=0$。收敛仍在原实际数据概率下，对全部大小 $q$ 的确定支持一致，
pair/path 分别成立；双重上确界中的全部函数来自同一个数据纤维。
原噪声可以任意慢地趋零，没有新增下界速率。

特别地，若 $\alpha_Q\delta^{1/4}\to c\in(0,\infty)$，则一致于紧输出区间，

$$
H_{\alpha_Q}(\mathsf P_x^y)-H_{\alpha_Q}(\mathsf P_x^0)
-\frac{\alpha_Q}{\alpha_Q-1}\left[b_xy-\frac{y^2}{2\nu}\right]
\longrightarrow-\frac{C_{\mathrm{edge}}}{c^2}y.
\tag{112.4}
$$

若确定 $a_Q\delta^{1/4}\to\infty$，则 (112.3) 在 $\alpha\ge a_Q$ 上删去谱端项后仍成立，
但保留有限阶因子。第 110 章的 $\alpha_Q\sqrt\delta\to c$ 修正保持不变：在那个尺度谱端项趋零。
在本章较低阶数尺度直接删去 $\alpha/(\alpha-1)$，则会留下 $\delta^{-1/4}$ 量级的项。

**证明：更长的实际谱端窗口。** 在第 110 章同一个好事件上，$v_*=v_0$ 唯一，
$d_j^\circ=1-v_j/v_0\ge c_1\min(j^2\delta^2,1)$。
取原高计数组集合 $\mathcal H=\{j:C_j\ge e^{\epsilon Q^3}\}$，
令

$$
A_\alpha=\frac1{\alpha\delta},\qquad
w_j=\frac{v_j}{\alpha d_j^\circ},\qquad m_j^\circ=-\frac{e_j}{d_j^\circ}
\quad(j\in\mathcal H\setminus\{0\}).
\tag{112.5}
$$

这里 $A_\alpha$ 是本章的小球尺度，不是第 111 章的原方差校正系数。
按原整数指标直接有

$$
w_j\le\frac{CA_\alpha}{j^2},\quad w_{\pm1}\asymp A_\alpha,
\quad \sum_j(m_j^\circ)^2\le C\delta^{-4}\|e\|^2=O_{\mathbb P}(\delta^6).
\tag{112.6}
$$

中央用剖面和谱亏损；中央外 $v_j\le Q^{-60}$、$|j|\le CQ^2$ 给相同的指标界。
只为写和式可在不存在的指标补零，不新增实际计数组。

先取区间

$$
\mathcal A_Q=[c\delta^{-1/4},\delta^{-1/3}].
\tag{112.7}
$$

其中 $A_\alpha\to\infty$ 且 $A_\alpha\delta=1/\alpha\to0$ 一致成立。
对每个固定 $B_0$，第 110 章的实际相对剖面误差
$\eta_Q=O_{\mathbb P}(Q^{-3/2}(1+\ln Q)^{3/2})=o_{\mathbb P}(\delta^2)$ 给

$$
\sup_{\substack{\alpha\in\mathcal A_Q\\1\le|j|\le B_0A_\alpha}}
\left|\frac{w_j}{\zeta A_\alpha/j^2}-1\right|\to0,
\qquad \zeta=2\rho_0/\kappa.
\tag{112.8}
$$

确实，此处 $|j|\delta\le B_0/\alpha\to0$，所有这些实际指标均属高计数核心。
Taylor 展开给

$$
d_j^\circ=\frac\kappa2j^2\delta^2
\left[1+O((j\delta)^2)+O\left(\frac{\eta_Q}{j^2\delta^2}\right)\right].
\tag{112.9}
$$

两个相对误差分别由 $CB_0^2/\alpha_{\min}^2$ 与 $C\eta_Q/\delta^2$ 控制。
同时 $v_j=\delta\rho_0(1+o_{\mathbb P}(1))$，得到 (112.8)。
两侧整数分支和原所有取整都已包括，未假设一条固定无限谱。

**有限数组的统一小球对数极限。** 先将辅助临界 Gaussian 的均值设为零，置
$R_\alpha^0=\sum_jw_jZ_j^2$、$F_\alpha^0(h)=\Pr(R_\alpha^0\le h)$。
其有限 Laplace 变换精确给

$$
T_{Q,\alpha}(z):=-A_\alpha^{-1}\ln\mathbb Ee^{-A_\alpha zR_\alpha^0}
=\frac1{2A_\alpha}\sum_j\ln(1+2A_\alpha zw_j).
\tag{112.10}
$$

一致于 $\alpha\in\mathcal A_Q$ 和每个正的紧 $z$ 区间，

$$
T_{Q,\alpha}(z)\longrightarrow d\sqrt z,
\qquad d=2\pi\sqrt{\rho_0/\kappa}.
\tag{112.11}
$$

为核对移动数组的统一性，先限 $\eta A_\alpha\le|j|\le B_0A_\alpha$。
(112.8) 与网格 $1/A_\alpha$ 将和式化为

$$
\frac12\int_{\mathbb R}\ln(1+2\zeta z/t^2)dt
=\pi\sqrt{2\zeta z}=d\sqrt z.
\tag{112.12}
$$

外尾 $|j|>B_0A_\alpha$ 由 $\ln(1+x)\le x$ 和 (112.6) 控为 $C/B_0$。
内段 $0<|j|<\eta A_\alpha$ 由阶乘或积分比较控为
$C\eta(1+|\ln\eta|)+C\ln A_\alpha/A_\alpha$。
先取原规模极限，再令 $\eta\downarrow0$、$B_0\uparrow\infty$。
积分通过分部积分和 $\int_0^\infty\ln(1+b^2/t^2)dt=\pi b$ 得到；
Gaussian 对数变换的 $1/2$ 与正负两个分支均已计入。

对任意正紧能量区间 $I$，进一步有

$$
\sup_{\alpha\in\mathcal A_Q,\,h\in I}
\left|A_\alpha^{-1}\ln F_\alpha^0(h)+C_0/h\right|\to0.
\tag{112.13}
$$

上界用指数 Markov，取 $z=C_0/h^2$：
$F_\alpha^0(h)\le\exp\{A_\alpha(zh-T_{Q,\alpha}(z))\}$。
下界在同一个有限数组上以 $e^{-A_\alpha zR_\alpha^0}$ 倾斜。
倾斜后的均值和方差是

$$
\mathbb E_zR_\alpha^0=\sum_j\frac{w_j}{1+2A_\alpha zw_j},\qquad
\operatorname{Var}_zR_\alpha^0
=2\sum_j\left(\frac{w_j}{1+2A_\alpha zw_j}\right)^2\le C/A_\alpha.
\tag{112.14}
$$

方差界逐项用 $\min(CA_\alpha/j^2,(2A_\alpha z)^{-1})$，在 $|j|\asymp A_\alpha$ 处分和。
均值一致趋于 $d/(2\sqrt z)$：可用同一 Riemann 和，
也可用 $T_{Q,\alpha}$ 的凹性，将其导数夹在固定步长的前后割线间，
先取 (112.11) 的一致极限，再令步长趋零。

固定小 $t>0$，取 $h'=h-2t$、$z=C_0/(h')^2$。
倾斜均值趋于 $h'$，方差趋零，故区间 $[h-3t,h-t]$ 的倾斜概率一致趋一。
撤去同一个倾斜，得到

$$
F_\alpha^0(h)\ge e^{-A_\alpha T_{Q,\alpha}(z)+A_\alpha z(h-3t)}
\Pr_z\{h-3t\le R_\alpha^0\le h-t\}.
\tag{112.15}
$$

其归一化对数下界为 $-C_0/(h-2t)-zt+o_{\mathbb P}(1)$。
最后 $t\downarrow0$，证明 (112.13)。这支付了有限随机数组的均值、方差和统一误差，
不直接套用固定无限序列的小半径渐近式。

**精确非中心均值与导数。** 还原
$R_\alpha=\sum_j(\sqrt{w_j}Z_j+m_j^\circ)^2$、$F_\alpha(h)=\Pr(R_\alpha\le h)$。
若 $b=\|m^\circ\|=O_{\mathbb P}(\delta^3)$，同一 Gaussian 向量上的三角不等式给

$$
F_\alpha^0((\sqrt h-b)_+^2)\le F_\alpha(h)
\le F_\alpha^0((\sqrt h+b)^2).
\tag{112.16}
$$

所以 $A_\alpha^{-1}\ln F_\alpha(h)\to f(h):=-C_0/h$ 在稍扩大正紧区间上一致成立。
第 110 章核对的 Prékopa 边缘定理使 $F_\alpha$ 关于 $h$ 对数凹；
非中心与不等方差均不破坏凸球上图集论证。
正能量上这些有限数组的 CDF 光滑。
对固定小步长 $t>0$，凹函数 $f_{Q,\alpha}=A_\alpha^{-1}\ln F_\alpha$ 满足

$$
\frac{f_{Q,\alpha}(h+t)-f_{Q,\alpha}(h)}t
\le f_{Q,\alpha}'(h)
\le\frac{f_{Q,\alpha}(h)-f_{Q,\alpha}(h-t)}t.
\tag{112.17}
$$

若扩大区间上的一致误差为 $\epsilon_Q$，两侧离 $f'(h)$ 的误差至多
$2\epsilon_Q/t$ 加 $f'$ 在尺度 $t$ 的连续模。
先固定 $t$ 取规模极限，再令 $t\downarrow0$，得到

$$
\sup_{\alpha\in\mathcal A_Q,\,h\in I}
\left|\frac{(\ln F_\alpha)'(h)}{A_\alpha}-\frac{C_0}{h^2}\right|\to0.
\tag{112.18}
$$

这里补上了从对数渐近式到导数的实质条件；未直接微分未控制的渐近误差。

**原噪声在较低阶数下的费用。** 现在核对整个区间
$c\delta^{-1/4}\le\alpha\le Q^6$。
第 110 章的精确临界分解仍为

$$
g_{\alpha,\sigma'}(y)=C_{x,\alpha}\sqrt\delta\,
 e^{-\alpha[c_*h_y-\delta u'c_*^2/2]}(r_\alpha*\varphi_s)(z_y),
\tag{112.19}
$$

其中 $c_*=1/(2v_*)$、$h_y=V+\sqrt\delta y$、$u'=(\sigma')^2$、
$s^2=\delta u'/\alpha$、$z_y=h_y-\delta u'c_*$，而

$$
r_\alpha(h)=\mathbb E\left[(h-R_\alpha)^{-1/2}
\cosh\!\left(\frac{\alpha e_0\sqrt{h-R_\alpha}}{v_0}\right)
\mathbf1_{R_\alpha<h}\right].
\tag{112.20}
$$

临界倾斜只用于非最大坐标，最大平方仍保留为未归一化核。
所有紧输出的 $z_y$ 在固定正紧区间内，且

$$
z_0=V-\frac{\delta(\sigma')^2}{2v_*}\to\gamma.
\tag{112.21}
$$

这里仅需 $\sigma'\to0$，没有要求环境收敛或噪声收敛的附加速率。

第 110 章的小球下界仍适用：其构造所需坐标数
$N=\lceil C(1+A_\alpha)\rceil=O(\delta^{-3/4})$，小于可用核心的 $\delta^{-1}$ 阶数量。
前 $N$ 个标准坐标的限制概率至少 $e^{-CN}$，尾平方和的均值至多 $CA_\alpha/N$，
小非中心均值由三角不等式支付。因此 $F_\alpha(h)\ge e^{-C(1+A_\alpha)}$，
对数凹性给 $0\le(\ln F_\alpha)'\le D_\alpha:=C(1+A_\alpha)$。
平方根核的局部积分界与 $j=\pm1$ 的二维密度界同样给

$$
F_\alpha'(h)\le C\alpha\delta,\qquad
r_\alpha(h)\le C\alpha\delta\sqrt h\,e^{\alpha|e_0|\sqrt h/v_0}.
\tag{112.22}
$$

在局部用 CDF 的对数 Lipschitz 界，区间外吸收非中心指数到 Gaussian 卷积的固定比例，得到

$$
\left|\ln\frac{(r_\alpha*\varphi_s)(z)}{F_\alpha(z)}\right|
\le C\{1+\ln(2+D_\alpha)+D_\alpha s+D_\alpha^2s^2+\alpha|e_0|/v_0\}+o(1).
\tag{112.23}
$$

外尾相对小球概率仍可忽略，因为 $(1/s^2)/A_\alpha=\alpha^2/u'\to\infty$，
且 $1/s^2$ 一致压过各多项式对数。
新的阶数范围内不能沿用 $D_\alpha s\to0$；正确的归一化费用是

$$
\frac{1+\ln(2+D_\alpha)}\alpha\le C\delta^{1/4}(1+|\ln\delta|),\qquad
\frac{D_\alpha s}\alpha\le C\sigma'\delta^{1/8},
$$

$$
\frac{D_\alpha^2s^2}\alpha
\le C(\sigma')^2\left(\frac\delta{\alpha^2}+\frac1{\alpha^3}
+\frac1{\alpha^4\delta}\right)\le C(\sigma')^2,
\qquad |e_0|/v_0=O_{\mathbb P}(\delta^4).
\tag{112.24}
$$

全部趋零，故 (112.23) 除以 $\alpha$ 的误差一致趋零。

**缩小输出差的积分。** 对 $\alpha\in\mathcal A_Q$，将 (112.18) 沿
$[z_0,z_0+\sqrt\delta y]$ 有向积分。整个区间一致趋近 $\gamma$，故

$$
\frac{\ln F_\alpha(z_y)-\ln F_\alpha(z_0)}\alpha
=\frac{A_\alpha\sqrt\delta}{\alpha}
\left(\frac{C_0y}{\gamma^2}+o_{\mathbb P}(1)\right)
=\frac{C_{\mathrm{edge}}y}{\alpha^2\sqrt\delta}+o_{\mathbb P}(1).
\tag{112.25}
$$

误差可一致支付，因为 $1/(\alpha^2\sqrt\delta)\le1/c^2$。
对 $\delta^{-1/3}\le\alpha\le Q^6$，用粗导数界已经有

$$
\alpha^{-1}|\ln F_\alpha(z_y)-\ln F_\alpha(z_0)|
\le C_K(\sqrt\delta/\alpha+1/(\alpha^2\sqrt\delta))=O(\delta^{1/6});
\tag{112.26}
$$

显式谱端项本身也为 $O(\delta^{1/6})$。
因此 (112.19)、(112.23)–(112.26) 在整个多项式阶数区间给

$$
-\alpha^{-1}\ln\frac{g_{\alpha,\sigma'}(y)}{g_{\alpha,\sigma'}(0)}
=b_xy-\frac{C_{\mathrm{edge}}y}{\alpha^2\sqrt\delta}+o_{\mathbb P}(1).
\tag{112.27}
$$

有限噪声截距先在两个输出相减时精确消去。
若 $|u'/u-1|\le h_Q$ 且 $h_Q$ 指数小，同一个 $C_{x,\alpha}$ 也使相邻宽度的绝对比较成立：

$$
\alpha^{-1}|\ln g_{\alpha,\sigma'}(y)-\ln g_{\alpha,\sigma}(y)|
\le C|u'-u|/\delta+C(D_\alpha/\alpha)|u'-u|+o_{\mathbb P}(1)=o_{\mathbb P}(1).
\tag{112.28}
$$

**实际计数、选择与无穷阶的回接。** (110.25)–(110.29) 的有限估计实际上对
$1\le\alpha\le Q^6$ 成立：高计数组中央联合质量比误差为
$\operatorname{poly}(Q)e^{-\epsilon Q^3/4}$，删去尾概率为
$\operatorname{poly}(Q)e^{-c\alpha Q^4+C\alpha}$，
原标量与舍入 Gaussian 的偏移满足

$$
\Delta_Q\le\operatorname{poly}(Q)(B^{-1}+B^{-2}e^{2\epsilon Q^3}),\qquad
\frac{\Delta_Q}{\sigma/\sqrt\alpha}\le\operatorname{poly}(Q)e^{-b_0Q^3}.
\tag{112.29}
$$

这些界未用第 110 章最终定理的更高阶数下界；高计数条件、原半指数噪声与 $\alpha\le Q^6$ 已足够。
较低区间的稀有密度下界也可直接核验：除最大平方外，其余未倾斜平方均值至多
$V/\alpha+\|e\|^2=o(1)$，至少以概率 $1/2$ 留在固定小能量内。
将能量噪声限制在一个标准差内，剩余正紧能量处的最大平方密度给
$g_{\alpha,\sigma'}(y)\ge e^{-C\alpha/\delta}$。
所以删去尾密度相对此下界的费用至多
$\operatorname{poly}(Q)\sigma^{-1}e^{-c\alpha Q^4+C\alpha+C\alpha/\delta}\to0$。
用核宽夹逼和 (112.28)，将 (112.27) 移到原乘积计数幂律，误差除以 $\alpha$ 一致趋零。

原选择回接仍是 (110.32) 的同一稀有输出期望比。
全区间 $1\le\alpha\le Q^6$ 的能量期望有界；
以 $e^{-(E-h)^2/(2w^2)}$ 重加权后亦有界，因其分母可由固定有界能量事件下界，
远尾由 Gaussian 指数压过。
再用原 $D(n)^2/q\le C\delta(E+\|e\|^2)$、精确选择对数界及 Jensen，
得到幂后验的对数预测密度比除以 $\alpha$ 为 $O_{\mathbb P}(\delta)$。
这保留实际固定总数选择与原 path 依赖。

将实际幂预测密度的 (112.27) 代入精确恒等式 (110.11)，
普通预测密度差仍为 $-y^2/(2\nu)+o_{\mathbb P}(1)$，便得 (112.3) 至 $Q^6$。
更高阶数使用原有限计数支持的 $\ln N\le CQ^5$ 和
$0\le H_\alpha-H_\infty\le\ln N/(\alpha-1)$，
分别在两个输出应用，误差为 $O(Q^{-1})$；第 108 章端点响应完成真正的重叠。
此时有限阶因子与谱端项的费用分别至多 $C(1+|b_x|)/Q^6$ 和
$C_K/(Q^{12}\sqrt\delta)$，都趋零。
因此不必在超多项式阶数要求有效噪声仍大于整数网格。

全部估计在同一个原好事件上完成，原概率界对支持一致且对 pair/path 分别成立。
放开紧的环境常数即给完整概率范围。(112.4) 和更快阶数结论由 (112.3) 直接推出，证毕。
本章没有无界输出、期望熵、Shannon 延拓、典型单模凝聚、噪声阈值等号或全局原创结论。
经典负指数倾斜、小球方法、Gaussian 二次型和凹函数割线各归成熟理论；
新增连接是实际移动有限谱的一致导数，以及它在原完整后验输出响应中的常数阶作用。

## 追加锚（第 112 章后续增补区）

## 113. 归一化温度导数的混叠消去与任意发散间隙

**定理 113.1（原后验信息方差的完整发散间隙）。** 保持第 101、106、109、111 章的原实际模型、固定幅度与参数、全部取整、完整计数元组、经验中心及同一观测。令

$$
\mathcal B=q/Q^{11/4},\qquad \delta=Q^{-1/2},\qquad
L=\ln(1/\sigma)\to\infty,\qquad \Delta=\ln\mathcal B-L\to\infty.
\tag{113.1}
$$

仍用同一个原可准入对数核心 $H$，保留其有限数据系数

$$
A=V_H/\sqrt\delta,\quad \nu_0=2\sum_Hw_j^2,\quad
\kappa_3=8\sum_Hw_j^3,\quad \Lambda=\nu_0+\sigma^2,
\quad C_x=\frac{A^2\kappa_3}{\Lambda^3}-\frac{2A\nu_0}{\Lambda^2}.
\tag{113.2}
$$

记 $V_{\rm prior,x}$ 为精确有限选择先验的惊异方差，$V_{\rm post,x}(y)$ 为原输出后验的惊异方差，均以 nats 计。置

$$
D_x(y)=V_{\rm post,x}(y)-V_{\rm prior,x}+A^2/\Lambda-C_xy,
$$

$$
R_*(y)=29/6-3\sqrt2+(3\sqrt2+8/\sqrt3-9)y^2/\nu,
\qquad \nu=2g_0.
\tag{113.3}
$$

则对于每条满足 (113.1) 的确定序列，

$$
\int_{\mathbb R}f_x(y)|D_x(y)-R_*(y)|\,dy\longrightarrow0
\tag{113.4}
$$

在原实际数据概率下对全部大小 $q$ 的确定支持一致，pair/path 分别成立。
即对每个正容差，超过容差的原数据概率对支持取上确界仍趋零。
没有对稀有数据环境取无界期望，也没有逐个无界输出的断言。
有限 $\sigma^2$ 始终保留在 (113.2)，容许噪声任意慢地趋零。
若用 bits 表示方差，整体除以 $(\ln2)^2$。

**原格点归约与噪声分支。** 记校准乘积律为 $Q_x$，原选择律为 $P_x=\mathscr L_xQ_x$，并沿用

$$
m_j=C_jp_j,\quad d_j=C_jp_j(1-p_j),\quad
B^2=q/Q^{5/2},\quad v_j=d_j/B^2,\quad w_j=d_j/\mathcal B,
\quad e_j=(\mu_j-m_j)/B.
$$

第 111 章给出同一好环境上的

$$
0\le\mathscr L_x\le C,\quad
a_x=\|\mathscr L_x-1\|_{2,Q}=O_{\mathbb P}(Q^{-5/2}),\quad
\|e\|^2\le a_x^2V.
\tag{113.5}
$$

取 $J=\{j:d_j\ge Q^{3600}\}$、$E=\{j\notin J:C_j>0\}$。
原完整组计数给 $N=|J|=O(Q^2)$、$|E|=O(1)$、$H\subset J$。
仅将 $J$ 中的质量换成整个整数轴上的归一化离散 Gaussian
$g_j(k)=Z_{m_j,d_j}^{-1}\exp(-(k-m_j)^2/(2d_j))$，保留 $E$ 的原二项计数、每个能量坐标及同一个 $G$，所得律记为 $Q^{\rm lat}$。
其精确中心化先验惊异为 $s_{\rm lat}$；比较空间可数，原选择权重不延伸到负计数。
第 111 章的有符号矩质量比较及条件均值平方裁剪，已经证明

$$
\|f_xD_x-f_{\rm lat}D_{\rm lat}\|_1=o_{\mathbb P}(1),\qquad
\int(1+y^2)|f_x-f_{\rm lat}|\,dy=o_{\mathbb P}(1),
\tag{113.6}
$$

其中 $D_{\rm lat}$ 使用 $\operatorname{Var}(s_{\rm lat}+G^2/2\mid Y^{\rm lat}=y)$、精确先验方差和原 (113.2) 的系数。
这一步费用为 $Ca_xQ^2=o_{\mathbb P}(1)$，没有逆噪声因子。

将序列分为 $\Delta\ge\ln Q$ 与 $\Delta<\ln Q$。
前者满足第 106 章的 $\Delta-\tfrac12\ln\ln Q\to\infty$，已有结论适用。
后者则必有

$$
\sigma\le Q/\mathcal B=\exp[-c_qQ^3+O(\ln Q)],\qquad
\sigma\mathcal B=e^\Delta\to\infty.
\tag{113.7}
$$

以下只处理这个新分支。两分支穷尽原序列，允许它们交替出现。
不以新分支的指数小噪声替代整个定理的假设。

置 $\epsilon=\max_Jw_j$、$A_b=\sum_Jw_j$、$a_j=(\mu_j-m_j)/\sqrt{d_j}$。
同一实际剖面给

$$
\epsilon\asymp Q^{-1/4},\quad \nu_b=2\sum_Jw_j^2\to\nu>0,
\quad A_b=O(\epsilon^{-1}),\quad A_b\epsilon\le C.
\tag{113.8}
$$

至少 $c\epsilon^{-2}$ 个原中央坐标满足 $c\epsilon\le w_j\le\epsilon$，而

$$
\|wa\|_2\le Ca_x,\qquad
\sum_Jw_ja_j^2\le a_x^2V/\sqrt\delta,\qquad
V/\sqrt\delta-A_b=\sum_Ew_j\le CQ^{3600}/\mathcal B.
\tag{113.9}
$$

每个 $E$ 坐标的中心化惊异有一致有界的任意固定阶矩。
这些是原模型的占据与选择估计，不是关于小数中心的独立性假设。

**精确温度输运。** 先考虑连续辅助向量 $Z$ 及同一个独立标准 Gaussian $G$。
固定 $w,a,c,\sigma$，令

$$
Y_{a,\sigma}=\sum_Jw_j(Z_j-a_j)^2-c+\sigma G,
\qquad X=(\|Z\|^2-N)/2,\qquad U=X+G^2/2.
$$

记输出密度为 $p_{a,\sigma}$，带因子 $e^{i\xi\cdot Z+i\eta G}$ 的振荡质量密度为 $b$，并写 $r=b/p$。
以 $e^{uU}$ 作归一化实倾斜，$\tau=1-u$ 时 $Z,G$ 的方差都变为 $1/\tau$。
换元直接给

$$
\frac{b_u(y)}{p_u(y)}=
r\left(\xi/\sqrt\tau,\eta/\sqrt\tau,a\sqrt\tau,
\sigma\sqrt\tau,\tau(y+c)-c\right).
\tag{113.10}
$$

共同 Jacobian 消去，$\eta\sigma$ 不变；$y$ 在求导时是原物理输出。
令 $R_\xi=\xi\cdot\partial_\xi$，其余径向算子同理，置

$$
\mathcal D=\tfrac12(R_\xi+R_\eta-R_a-R_\sigma)-(y+c)\partial_y.
$$

对 (113.10) 的路径求两次导数得

$$
(b_u/p_u)'_0=\mathcal Dr,\qquad
(b_u/p_u)''_0=(\mathcal D^2+\mathcal D)r.
\tag{113.11}
$$

例如 $\xi''(0)=3\xi/4$、$a''(0)=-a/4$、$y''(0)=0$。
中央零噪声情形 $c=A_b$ 中，若 $R=R_\xi$，后一式为

$$
(\mathcal D^2+\mathcal D)r
=(R^2/4+R/2)r-(y+A_b)Rr_y+(y+A_b)^2r_{yy}.
\tag{113.12}
$$

单独含一阶输出导数的项消去。
因此需证明 $r_y$ 带 $\epsilon$、$r_{yy}$ 带 $\epsilon^2$，以支付增长的 $A_b$。
有限维实积分在 $|u|<u_0<1$ 有 Gaussian 指数控制，故此处求导合法。
连续零噪声密度随后由可积 Fourier 导数处理，未令离散观测的噪声等于零。

**适中输出区间上的相对模展开。** 对 $T_0=\sum_Jw_j(Z_j^2-1)$ 记密度 $p$、特征函数

$$
P(s)=\prod_Je^{-isw_j}(1-2isw_j)^{-1/2},\qquad
h_Q=\sqrt{100\nu\ln Q}.
$$

中央坐标块给

$$
|P(s)|\le(1+c\epsilon^2s^2)^{-c'/\epsilon^2},\qquad
\kappa_r=2^{r-1}(r-1)!\sum_Jw_j^r=O_r(\epsilon^{r-2})\quad(r\ge3).
\tag{113.13}
$$

前一式对任意固定 $|s|$ 幂可积，$|s|>c_0/\epsilon$ 的相应积分至多
$\operatorname{poly}(\epsilon^{-1})e^{-c_1/\epsilon^2}$。
在 $|s|\le\epsilon^{-\eta_J}$ 展开 $\log P$ 至任意预先固定阶，再展开指数，余项为 $C_J\epsilon^J$ 的可积 Gaussian 加权多项式；固定阶选小 $\eta_J$，互补区域用 (113.13)。
同法处理所需 Fourier 导数权重，得到任意固定阶密度导数展开。
这只是第 101 章连续参考计算的延伸，不把它当作原格点律的 Edgeworth 定理。

当需要除以密度时，取展开阶至少 $1200$；在 $|y|\le h_Q$ 上有

$$
p(y)\ge Q^{-60},\qquad p(y)/\varphi_{\nu_b}(y)=1+o(1),
$$

$$
|\partial_y^k(p^{(r)}/p)|\le C_{r,k}(1+|y|^{d_{r,k}})\quad(k\le2),
\qquad |(\log p)'''(y)|\le C\epsilon(1+|y|^d)+Q^{-100}.
\tag{113.14}
$$

确实 $\nu_b\in[0.99\nu,1.01\nu]$ 时 $\varphi_{\nu_b}(h_Q)>Q^{-51}$，有限 Edgeworth 因子在该区间为 $1+o(1)$，而绝对余项可小于 $Q^{-250}$。
Gaussian 的三阶对数导数为零，第一个非 Gaussian 系数带 $\epsilon$。
所有次数固定，不随 $Q,y$ 或扭转向量改变。

沿用第 109 章的固定光滑条带截断 $\chi(s/W_Q)$，$W_Q\asymp\epsilon^{-1}$。
令 $E_\xi=\|\xi\|^2$、$B_1=\sum_Jw_j\xi_j^2$，并定义

$$
a_\xi(y)=\frac1{2\pi}\int e^{-isy}\chi(s/W_Q)P(s)
\exp\left[-\frac12\sum_J\frac{\xi_j^2}{1-2isw_j}\right]ds,
\qquad r_\xi=a_\xi/p.
\tag{113.15}
$$

则对于所需的每个固定径向导数阶 $l$ 及 $k\le2$，

$$
r_\xi=e^{-E_\xi/2}\{1+B_1(\log p)'\}+\mathcal E_\xi,
$$

$$
|\partial_y^kR_\xi^l\mathcal E_\xi|
\le C\epsilon^2(1+|y|^d)(1+E_\xi)^de^{-cE_\xi}+Q^{-100}e^{-cE_\xi}.
\tag{113.16}
$$

为证明对任意大扭转的一致性，只在分母中插入 $\lambda$，保持 $P$ 不变。
条带上 $\operatorname{Re}(1-2is\lambda w_j)^{-1}$ 有正下界。
扭转指数的 $J$ 阶 $\lambda$ 导数至多
$C_J(\epsilon|s|)^J(1+E_\xi)^Je^{-cE_\xi}$；径向求导只增添固定多项式。
在零点 Taylor 后，第 $r$ 项系数为 $e^{-E_\xi/2}c_r(is)^r$，
$c_0=1,c_1=-B_1$，且 $|R_\xi^lc_r|\le C\epsilon^r(1+E_\xi)^d$。
逆变换的 $(is)^r$ 给 $(-1)^rp^{(r)}$。
高阶余项及截断误差先作绝对 $C^k$ 界，再用 (113.14) 支付密度除法；取足够固定 $J$ 后余项为 $Q^{-100}e^{-cE_\xi}$。
其余 $r\ge2$ 项由相对导数比界收束，得到 (113.16)。

于是

$$
|R_\xi^lr_\xi|\le C(1+|y|^d)(1+E_\xi)^de^{-cE_\xi},
$$

$$
|R_\xi^l(r_\xi)_y|\le C\epsilon(1+|y|^d)(1+E_\xi)^de^{-cE_\xi}+Q^{-100}e^{-cE_\xi},
$$

$$
|R_\xi^l(r_\xi)_{yy}|\le C\epsilon^2(1+|y|^d)(1+E_\xi)^de^{-cE_\xi}+Q^{-100}e^{-cE_\xi}.
\tag{113.17}
$$

最后一行的主项是 $B_1(\log p)'''$，不是 $B_1p'''/p$。
这正好给两次温度导数需要的 $\epsilon^2$。
质量本身还满足整个适中区间上一致的更强界

$$
|r_\xi(y)|\le e^{-E_\xi/2}+o(1)(1+E_\xi)^de^{-cE_\xi},
\tag{113.18}
$$

因为 $\epsilon h_Q^d\to0$；该 $o(1)$ 也对 $\xi$ 一致。

**原中心、非大组和共同残差。** 记 $g_u$ 为把 $J$ 换成连续 Gaussian、保留 $E$ 原二项惊异的归一化温度倾斜输出密度；仍保留原 $\mu,V$ 和 $E$ 的能量，且同一 $G$ 的方差为 $1/(1-u)$。其未倾斜密度为 $g$。
在第 $\ell$ 条半整数弧 $t_\ell=\pi\ell\mathcal B$ 上，噪声扭转为

$$
\eta_\ell=\sigma t_\ell=\pi\ell e^\Delta.
\tag{113.19}
$$

物理空间相位 $e^{-it_\ell y}$ 在温度求导时固定。
噪声因子的前两阶导数仍来自
$\exp[-(\eta_\ell+\sigma s)^2/(2\tau)]$，完整保留第 109、111 章的二阶和四阶残差标记。

置

$$
\rho_x=\|wa\|_2+\sum_Jw_ja_j^2+|V/\sqrt\delta-A_b|
+\sigma+Q^{7202}/\mathcal B.
$$

(113.5)、(113.7)、(113.9) 给 $\rho_x=O_{\mathbb P}(Q^{-5/2})$，且

$$
(1+A_b)^2\rho_x=o_{\mathbb P}(1).
\tag{113.20}
$$

最后一项覆盖 $E$ 的整个能量范围；其坐标数有界且 $C_j\le CQ^{3600}$。
精确体块与噪声变换相对中央 $P(s)$ 的因子为

$$
\exp\left\{is\kappa-\frac12\sum_J\frac{(\xi_j-2sw_ja_j)^2}{1-2isw_j}
-\frac12(\eta+\sigma s)^2\right\},\qquad
\kappa=\sum_Jw_ja_j^2-V/\sqrt\delta+A_b.
\tag{113.21}
$$

与中央零噪声指数的差是

$$
is\kappa+\sum_J\frac{2sw_ja_j\xi_j-2s^2w_j^2a_j^2}{1-2isw_j}
-\eta\sigma s-\sigma^2s^2/2.
\tag{113.22}
$$

条带上配方后，Taylor 路径上的指数均由 $Ce^{-c(E_\xi+\eta^2)}$ 控制，因为
$\|wa\|/\epsilon$ 与 $\sigma/\epsilon$ 趋零。
每个固定径向、中心或噪声导数只引入 $E_\xi,\eta,|s|$ 的固定多项式。
按 (113.16) 的办法作足够高固定阶展开；每个非恒定扰动系数至少带一个 $\kappa,wa,\sigma$，其总线性扭转系数由 $\|wa\|\sqrt{E_\xi}$ 控制。
逆变换后使用 (113.14)，包括两次 $y$ 导数及 (113.11) 所需全部参数导数，得到相对误差

$$
C\rho_x(1+|y|^d)(1+E_\xi+\eta^2)^de^{-c(E_\xi+\eta^2)}
+Q^{-100}e^{-c(E_\xi+\eta^2)}.
\tag{113.23}
$$

分母用零扭转的同一展开，先得 $g/p=1+O(\rho_x(1+|y|^d))+O(Q^{-100})$，在适中区间远离零，再作商的求导。
参数的径向导数遵守同界，固定截距不随参数变化。
温度算子作用两次最多付 $(1+A_b)^2$；(113.20) 支付扰动部分。
中央主项对 $\eta$ 的依赖为 $e^{-\eta^2/2}$，径向导数只添多项式。
由 (113.12)、(113.17)，归一化模的温度导数遂满足

$$
|\partial_u^j(b_u/g_u)(y)|_{u=0}
\le C(1+|y|^d)(1+E_\xi+\eta^2)^de^{-c(E_\xi+\eta^2)}
+Q^{-90}e^{-c(E_\xi+\eta^2)},\quad j=0,1,2.
\tag{113.24}
$$

$j=0$ 仍保留 (113.18) 的主项 $e^{-(E_\xi+\eta^2)/2}$ 加统一小误差。

对 $E$ 不先作独立化，而保留精确因子
$\mathbb E[e^{us_E+ib_E\cdot R_E+isT_E}]/M_E(u)$。
Taylor 展开 $e^{isT_E}$，其零、一、二阶温度导数由固定惊异矩乘确定能量界控制。
同一相对 Fourier 展开支付的费用至多
$C(1+A_b)^2Q^{7202}/\mathcal B$ 乘固定输出和扭转多项式，趋零。
此后才能把该因子换成仅含 $s_E$ 的归一化扭转特征函数；其前两阶导数一致有界。

条带截断也随温度换元：$\chi(s/W_Q)$ 变成 $\chi(\tau s/W_Q)$。
前两阶截断导数只支撑在 $|s|\asymp\epsilon^{-1}$，(113.13) 给指数小量；全部标记和输运导数仅付固定多项式。
故这些交换误差小于任意固定 $Q$ 负幂，不能把移动截断默认为常量。

**对同一实际模求和，并保留完整条件商。** 原经验中心给

$$
b_{\ell j}=\pi\ell(1-2\mu_j),\qquad
\xi_{\ell,k,j}=\sqrt{d_j}(b_{\ell j}-2\pi k_j),\quad k\in\mathbb Z^N.
\tag{113.25}
$$

这些相位可以任意相关。对每个固定 $c>0,d_*>0$，第 111 章逐坐标最近格点界给

$$
\sum_{k\in\mathbb Z^N}(1+\|\xi_{\ell,k}\|^2)^{d_*}
e^{-c\|\xi_{\ell,k}\|^2}\le C.
\tag{113.26}
$$

先把多项式吸收进半个指数，再用
$\sum_k e^{-cd_j(b_j-2\pi k)^2/2}\le1+Ce^{-c'd_j}$ 并相乘。
$N=O(Q^2)$、$d_{\min}\ge Q^{3600}$ 使乘积有界，没有 $C^N$。
离散归一化因子

$$
c_d(u)=\prod_J\frac{\sqrt{2\pi d_j/(1-u)}}{Z_{m_j,d_j/(1-u)}}
\tag{113.27}
$$

在零点的值离一、前两阶导数离零均小于任意固定负幂。
这是对正实 Gaussian 格点归一化和求导，误差由
$C\sum_j(1+d_j)^Ce^{-cd_j}$ 支付，不要求复 theta 函数无零点。

记 $q_h^{\rm lat}(y)dy=\mathbb E[(s_{\rm lat}+G^2/2)^h;Y^{\rm lat}\in dy]$，$h\le2$。
第 109 章两标记条带外界与第 111 章 Fourier 质量比较给条带外余项 $O(Q^{-430})$。
零条带的零 Poisson 模恰为上述连续大组参考；其余双格模有 $E_\xi\ge cQ^{3600}$。
参考律条带外界由 (113.13) 给出，仍保留标记和 $E$ 坐标。
所以三个矩密度都等于参考项、非零半整数混叠模与统一 $O(Q^{-430})$ 余项之和。

精确中心化使 $M'_{\rm lat}(0)=0$、$M''_{\rm lat}(0)=V_{\rm lat}$；共同 $G$ 的矩母函数为 $(1-u)^{-1/2}$。
因此

$$
(f_{{\rm lat},u})'_0=q_1^{\rm lat}-q_0^{\rm lat}/2,
\qquad
(f_{{\rm lat},u})''_0=q_2^{\rm lat}-q_1^{\rm lat}-(V_{\rm lat}+1/4)q_0^{\rm lat}.
\tag{113.28}
$$

参考项也有同式。局部化余项只另付已知 $O(Q^2)$ 方差；这里没有从 $C^0$ 误差推出 $C^2$ 误差。
在适中区间 $g\ge cp\ge cQ^{-60}$，参考一、二阶条件矩至多为
$C(1+A_b)(1+|y|^d)$ 与 $C(N+A_b^2)(1+|y|^d)$。
故全部余项经过除法和两次商求导后仍为 $O(Q^{-100})$。

对真正正的实密度定义 $\mathcal A(u,y)=f_{{\rm lat},u}(y)/g_u(y)$。
将 (113.24) 先按 (113.26) 求和，再用 (113.19) 对 $\ell\ne0$ 求和，得

$$
|\mathcal A(0,y)-1|\le Ce^{-ce^{2\Delta}}+o(1),\qquad |y|\le h_Q,
\tag{113.29}
$$

$$
|\partial_u^j\mathcal A(0,y)|\le C(1+|y|^d)e^{-ce^{2\Delta}}+Q^{-80},
\qquad j=1,2.
\tag{113.30}
$$

质量界先用 (113.18) 的强形式，避免把输出多项式的上确界记到任意慢增长的间隙上。
其余 $o(1)$ 是中心、截断和局部化的多项式小量乘固定对数幂。
导数界中的 (113.20) 系数有界，$\eta$ 多项式被 Gaussian 衰减吸收。

故最终 $\mathcal A(0,y)\ge1/2$，对实正比值求对数导数合法，且

$$
|\partial_u^2\log\mathcal A(0,y)|
\le C(1+|y|^{2d})e^{-ce^{2\Delta}}+Q^{-70}.
\tag{113.31}
$$

平方项 $(\mathcal A'/\mathcal A)^2$ 已包括。
一般同通道恒等式为

$$
\operatorname{Var}(s+G^2/2\mid Y=y)-\operatorname{Var}s
=\tfrac12+\partial_u^2\log f_u(y)|_0.
$$

Bayes 使原律的左端等于后验减先验信息方差；辅助律则给已定义的比较泛函。
两边保持相同有限系数，于是

$$
D_{\rm lat}(y)-D_g(y)=\partial_u^2\log\mathcal A(0,y).
\tag{113.32}
$$

这是第 111 章留下的完整非线性条件商，包括先验方差和条件均值平方。
没有分别将 $A$ 或 $A^2$ 项乘一个标量混叠误差。

**同一律的全输出尾部。** 对格点 Gaussian 能量作正实配方，其矩母函数与连续参考只差正实格点归一化和之比。
当 $|t|\le C\sqrt{\ln Q}$，有效方差 $d_j/(1-2tw_j)\ge d_j/2$，有效均值可以任意。
实 Poisson 归一化界对均值一致，积的对数误差为 $CN e^{-cQ^{3600}}$。
连续参考的精确积分为

$$
\log\mathbb Ee^{tY}=-ct-\tfrac12\sum_J\ln(1-2tw_j)
+\sum_J\frac{tw_ja_j^2}{1-2tw_j}+\sigma^2t^2/2+\log\mathbb E_Ee^{tT_E}.
\tag{113.33}
$$

仍取 $c=V/\sqrt\delta$，保留原截距。
非大组项由 $|t|CQ^{7202}/\mathcal B$ 支付。
按 (113.8)、(113.9) 展开前两阶，格点律满足

$$
\log\mathbb E_{\rm lat}e^{tY^{\rm lat}}
=tm_{\rm lat}+\nu_bt^2/2
+O(\epsilon|t|^3+a_x^2t^2+\sigma^2t^2)
+O(|t|Q^{7202}/\mathcal B)+o(Q^{-100}),
\tag{113.34}
$$

其中 $|m_{\rm lat}|\le Ca_x^2/\sqrt\delta+CQ^{7202}/\mathcal B+o(Q^{-100})$；也可在此精确保留非大组均值。
连续参考有同界。取 $t=\pm h_Q/(1.1\nu)$ 的 Chernoff 界，其主指数超过 $45\ln Q$，可留出余量得到

$$
\Pr_{\rm lat}(|Y^{\rm lat}|>h_Q)+\Pr_g(|Y|>h_Q)\le CQ^{-40}.
\tag{113.35}
$$

固定正负 $t$ 又给任意固定阶输出矩的一致有界性。
精确中心惊异满足 $\|s_{\rm lat}+G^2/2\|_4\le CQ$，参考也相同。
所以

$$
\int_{|y|>h_Q}f_{\rm lat}(y)\operatorname{Var}(s_{\rm lat}+G^2/2\mid y)dy
\le CQ^2\Pr_{\rm lat}(|Y^{\rm lat}|>h_Q)^{1/2}=O(Q^{-18}).
\tag{113.36}
$$

先验方差为 $O(Q^2)$，$A^2/\Lambda=O(Q^{1/2})$，$C_x=O(Q^{1/4})$；其尾部均由 (113.35) 及 Cauchy–Schwarz 支付。
$R_*$ 的二次项由一致第四输出矩支付，故格点律与参考律各自都有

$$
\int_{|y|>h_Q}f(y)(|D(y)|+|R_*(y)|)dy\to0.
\tag{113.37}
$$

此处不对极小输出密度求导或取下界，也不将弱极限当成矩收敛。

**参考映射与原模型回接。** 第 101 章连续中央核心参考的全输出结论保持精确 $A,\nu_0,\kappa_3,\sigma$，对所有 $\sigma\to0$ 有效；此前噪声指数限制属于实际计数的旧耦合，不属于这条参考结论。
现将 $g$ 中的外部能量与其惊异一同移除。原 $V_{\rm out}\le Q^{-200}$ 给
$\mathbb E|T_{\rm out}^{\rm centered}|\le CV_{\rm out}/\sqrt\delta$，并保留非中心项和非大组坐标。
(101.19) 是未加权联合密度界
$\iint|\partial_tp_H(z,t)|dzdt\le C\delta^{-1/2}$。
条件于同一外部元组和 $G$ 后，第一坐标包含相关的外部惊异，第二坐标平移同一外部能量。
因此联合律变差至多

$$
\varepsilon_{\rm out}\le C\delta^{-1/2}\mathbb E|T_{\rm out}^{\rm centered}|
\le C\delta^{-1}V_{\rm out}=O(Q^{-199.5}).
\tag{113.38}
$$

不直接用 TV 传递无界方差。两目标的第四范数为 $CQ$，按 (101.8) 裁剪到 $b=Q^{10}$，方差密度费用为
$C(b^2\varepsilon_{\rm out}+Q^3/b)=o(1)$。
先验方差的输出质量费用 $O(Q^2\varepsilon_{\rm out})$、有限系数的费用
$C(\delta^{-1}\varepsilon_{\rm out}+\delta^{-1/2}\sqrt{\varepsilon_{\rm out}})$ 也趋零。
输出第四矩再给二次权重的输出律比较。

支付这些联合比较以后，外部中心惊异才与核心输出独立，其先验方差在 $D_g$ 中精确消去。
核心非中心与截距再用 (101.22) 的 $O(Q^{-9/4})$ 联合变差界。
此时目标第四范数降为 $O(\sqrt{|H|})$，$|H|=O(Q^{1/2}\sqrt{\ln Q})$；取裁剪 $b=Q$，(101.23) 费用为
$O(Q^{-1/4}[1+(\ln Q)^{3/4}])=o(1)$。
该 Gaussian 核心比较没有逆噪声因子。
至此第 101 章参考结论给

$$
\int g(y)|D_g(y)-R_*(y)|dy\to0.
\tag{113.39}
$$

在适中区间，按同一格点输出律积分 (113.31)、(113.32)，使用固定阶输出矩，而不取增长区间上多项式的上确界，得到

$$
\int_{|y|\le h_Q}f_{\rm lat}|D_{\rm lat}-D_g|
\le Ce^{-ce^{2\Delta}}+o(1)\to0.
\tag{113.40}
$$

(113.29) 还给 $f_{\rm lat}\le2g$，参考贡献遂由两倍 (113.39) 控制。
加上 (113.37)，即得格点律的完整加权收敛。
最后由 (113.6) 和 $R_*$ 为固定二次多项式，

$$
\int f_x|D_x-R_*|
\le\|f_xD_x-f_{\rm lat}D_{\rm lat}\|_1
+\int f_{\rm lat}|D_{\rm lat}-R_*|
+\int|f_x-f_{\rm lat}||R_*|\to0.
\tag{113.41}
$$

结合最初两个噪声分支，证明 (113.4)。全部估计在同一个支持一致好环境上完成，先限制紧常数再放开；原 path 只用其原行比较律，没有被改成独立样本。

**推论 113.2（平均后验信息方差）。** 保留精确 $m_x=\mathbb E_xY$，同样有

$$
\int f_xV_{\rm post,x}-V_{\rm prior,x}+A^2/\Lambda-C_xm_x
\longrightarrow8/\sqrt3-25/6.
\tag{113.42}
$$

证明：上述二次权重比较给 $\mathbb E_xY^2\to\nu$，对 (113.3)、(113.4) 积分即可。
本结论不需要先删去 $m_x$，也不对原数据再取无界期望。

本章补上第 111 章的输出条件化与尾部接口，保留该章关于较弱补偿的反例及以前所有结论的范围。
Gaussian 缩放、Poisson 求和、条件累积量和 Edgeworth 方法均属成熟理论；这里证明的是它们在同一实际有限数组、原计数选择与完整非线性条件商之间的连接。
固定或更小间隙、必要性、阈值等号、无界输出逐点断言以及熵和覆盖推广仍不在本章结论内。

## 追加锚（第 113 章后续增补区）

## 114. 一个精确经验鞍点统一所有发散的 Rényi 阶数

**定理 114.1（任意发散下截点的统一输出响应）。** 保持第 110、112 章的原完整计数后验、固定参数、全部取整、实际经验中心及同一带噪标量。仍假设

$$
\delta=Q^{-1/2},\qquad L=\ln(1/\sigma)\to\infty,
\qquad \limsup L/Q^3<c_q/2.
\tag{114.1}
$$

在原完整组窗口上定义

$$
v_j=C_jp_j(1-p_j)/B^2,\quad V=\sum_jv_j,\quad
e_j=(\mu_j-C_jp_j)/B,\quad v_*=\max_jv_j,
\qquad B^2=q/Q^{5/2}.
$$

原能量与输出仍是 $E(n)=\sum_j((n_j-\mu_j)/B)^2$、
$T_x(n)=(E(n)-V)/\sqrt\delta$ 和 $Y=T_x+\sigma G$。
对有限 $\alpha>1$，令

$$
K_{x,\alpha,\sigma}(t)=
-\frac12\sum_j\ln(1-2tv_j/\alpha)
+\sum_j\frac{te_j^2}{1-2tv_j/\alpha}
+\frac{\delta\sigma^2t^2}{2\alpha},
\qquad t<\frac\alpha{2v_*}.
\tag{114.2}
$$

在概率趋一的共同实际好事件上，对每个有限 $\alpha\ge2$，方程

$$
K_{x,\alpha,\sigma}'(t_\alpha)=V
\tag{114.3}
$$

有唯一正根。定义

$$
b_{x,\alpha,\sigma}=\frac{\sqrt\delta\,t_\alpha}\alpha,
\qquad b_{x,\infty,\sigma}=\frac{\sqrt\delta}{2v_*}.
\tag{114.4}
$$

好事件外可任意定义，不影响下面的概率收敛。
空组 $C_j=\mu_j=v_j=e_j=0$；一般零方差坐标在 (114.2) 中直接作为确定项处理。

对每条确定的 $a_Q\to\infty$ 和每个固定 $R<\infty$，

$$
\sup_{\substack{\alpha\in[a_Q,\infty]\\ |y|\le R}}
\left|H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
-\frac\alpha{\alpha-1}\left[b_{x,\alpha,\sigma}y-\frac{y^2}{2\nu}\right]\right|
\longrightarrow0.
\tag{114.5}
$$

在无穷阶取因子为一。收敛在原实际数据概率下对全部大小 $q$ 的确定支持一致，pair/path 分别成立；同一上确界中的量来自同一个数据纤维。
下截点不必单调，增长可以任意慢。噪声也可任意慢地趋零。
有限阶因子与精确有限经验根均保留，不能在增长的线性项中无条件换成连续谱极限。
本章不包含有界阶数或向 Shannon 阶数一的统一延拓。

**精确累积量与原输入。** 辅助连续能量

$$
S_\alpha=\sum_j(\sqrt{v_j/\alpha}Z_j-e_j)^2
+\sqrt{\delta\sigma^2/\alpha}\,G
\tag{114.6}
$$

的累积量母函数恰为 (114.2)。逐坐标配方给中心行列式因子及非中心指数，独立能量噪声给最后的二次项。
记 $D_j(t)=1-2tv_j/\alpha$，则

$$
K'(t)=\sum_j\frac{v_j}{\alpha D_j(t)}
+\sum_j\frac{e_j^2}{D_j(t)^2}+\frac{\delta\sigma^2t}\alpha,
$$

$$
K''(t)=2\sum_j\frac{v_j^2}{\alpha^2D_j(t)^2}
+4\sum_j\frac{v_je_j^2}{\alpha D_j(t)^3}
+\frac{\delta\sigma^2}\alpha>0.
\tag{114.7}
$$

沿用第 110 章共同实际好事件：
$V\to\gamma>0$、$v_*/\delta\to\rho_0>0$、$\|e\|_2=O_{\mathbb P}(\delta^5)$，
完整组数 $m_Q\le CQ^2$、$\ln M=O(Q^3)$、$N_J=\sum C_j=O_{\mathbb P}(B^2)$。
于是 $K'(0)=V/\alpha+\|e\|^2<V$ 同时对 $\alpha\ge2$ 成立；靠近右极点时最大中心平方项发散。
连续性和严格单调性给 (114.3)。

原剖面仍为 $\rho(s)=\rho_0e^{-\kappa s^2/2}$，$\nu=2\int\rho^2$、$\gamma=\int\rho$。
第 110 章精确数组估计给

$$
\eta_Q=\max_{|j\delta|\le\sqrt{K_0\ln Q}}
\left|\frac{v_j}{\delta\rho(j\delta)}-1\right|
=O_{\mathbb P}(Q^{-3/2}(1+\ln Q)^{3/2})=o_{\mathbb P}(\delta^2),
$$

$$
\sum_{|j\delta|>\sqrt{K_0\ln Q}}v_j\le Q^{-60}.
\tag{114.8}
$$

因此同一事件上 $v_*=v_0$ 唯一，$q_j^\circ=1-v_j/v_*$ 满足

$$
q_j^\circ\ge c\min(j^2\delta^2,1)\quad(j\ne0),\qquad q_0^\circ=0,
\tag{114.9}
$$

小中央弧上还有相应上界 $Cj^2\delta^2$。这是收缩的谱亏损，不是正的极限谱隙。
以下先把各紧随机常数限制在任意固定界内，且把 $V,v_*/\delta$ 限于正紧区间，最后放开这些界。

**较低阶数的共同鞍点几何。** 先处理可能为空的区间

$$
\mathcal I_Q=[a_Q,\delta^{-1/3}].
\tag{114.10}
$$

写 $s_\alpha=2v_*t_\alpha/\alpha$、$d_\alpha=1-s_\alpha$。
在根处 $D_j=d_\alpha+(1-d_\alpha)q_j^\circ$。
由原剖面和谱亏损，当 $0<d\le1/2$ 时

$$
S(d):=\sum_j\frac{v_j}{d+(1-d)q_j^\circ}
\le C\left(\frac\delta d+\frac1{\sqrt d}\right).
\tag{114.11}
$$

最大项由 $C\delta/d$ 控制；$0<|j\delta|\le1$ 的和与
$\sum C\delta/(d+cj^2\delta^2)$ 比较，积分给 $C/\sqrt d$；其余分母远离零，总方差有界。
若 $d=k/\alpha^2$，$k>0$ 固定，$\alpha\in\mathcal I_Q$，则
$d\to0$、$\sqrt d/\delta\to\infty$ 一致成立。
$|j|\le c\sqrt d/\delta$ 的原指标有 $v_j\asymp\delta$、$q_j^\circ\le Cd$，故也有 $S(d)\ge c/\sqrt d$。
于是 $S(d)/\alpha$ 的上界为 $C/\sqrt k+C\alpha\delta/k$，下界为 $c/\sqrt k$。

在测试点 $t=\alpha(1-d)/(2v_*)$，其余两项为

$$
\sum_j\frac{e_j^2}{D_j^2}\le C\delta^{10}\alpha^4/k^2=o(1),
\qquad 0\le\delta\sigma^2t/\alpha\le C\sigma^2=o(1).
\tag{114.12}
$$

先取足够小的 $k$ 使 $K'>V$，再取足够大的 $k$ 使 $K'<V$；
$\alpha\delta\le\delta^{2/3}$ 使最大项修正同时趋零。
根的单调性遂给

$$
c/\alpha^2\le d_\alpha\le C/\alpha^2
\quad(\alpha\in\mathcal I_Q).
\tag{114.13}
$$

没有要求噪声在放大以后也可以删去，它已进入实际根。
根处倾斜的坐标均值与方差为

$$
w_j=\frac{v_j}{\alpha D_j},\qquad m_j=-e_j/D_j,
\qquad A_\alpha=1/(\alpha\delta).
\tag{114.14}
$$

有至少 $cA_\alpha$ 个实际高计数指标 $|j|\le cA_\alpha$，含正负两侧，满足
$c/A_\alpha\le w_j\le C/A_\alpha$。
同时

$$
\max_jw_j\le C/A_\alpha,\qquad \sum_jw_j\le V,
\qquad \sum_jm_j^2\le C\delta^{10}\alpha^4=o(1).
\tag{114.15}
$$

中间一式直接来自完整根方程中三项均非负。
$A_\alpha\ge\delta^{-2/3}$，故有效倾斜坐标数一致发散。

**在完整根处倾斜高计数组。** 取 $l<c_q/2$ 使 $L\le lQ^3$，再取
$\varepsilon>0$ 使 $2\varepsilon<c_q-l$，置 $H=\{j:C_j\ge e^{\varepsilon Q^3}\}$。
整个增长核心及上面的比较坐标块均在 $H$ 中。
令 $K_H$ 只限制 (114.2) 的坐标和，仍保留相同噪声项以及输出能量中的完整 $V$。
由 $0\le\mu_j\le C_j$、组数 $O(Q^2)$，

$$
\ell_v=\sum_{j\notin H}v_j\le\operatorname{poly}(Q)e^{-(c_q-\varepsilon)Q^3},
\qquad
\ell_e=\sum_{j\notin H}e_j^2\le\operatorname{poly}(Q)e^{-(c_q-2\varepsilon)Q^3}.
\tag{114.16}
$$

低组的 $v_j/v_*$ 指数小，所以 $D_j(t_\alpha)\ge1/2$。在完整根而非另一个高组根处，

$$
K_H'(t_\alpha)=V-\varepsilon_{\rm low},\qquad
0\le\varepsilon_{\rm low}\le C(\ell_v/\alpha+\ell_e).
\tag{114.17}
$$

这支付了指数小的均值差，未换掉放大的经验系数。
高组倾斜方差为

$$
W_H=K_H''(t_\alpha)
=2\sum_Hw_j^2+4\sum_Hw_jm_j^2+\delta\sigma^2/\alpha
\asymp A_\alpha^{-1}=\alpha\delta.
\tag{114.18}
$$

比较坐标块给下界，(114.15) 给上界；噪声方差与 $\alpha\delta$ 之比是 $\sigma^2/\alpha^2$。
因此 $\max w_j/\sqrt{W_H}\le CA_\alpha^{-1/2}\to0$ 一致成立。

**相对倾斜密度估计。** 令 $q_{Q,\alpha}$ 是高组倾斜能量减其精确均值、再除以 $\sqrt{W_H}$ 后的密度，包含已倾斜噪声均值。
证明

$$
\sup_{\alpha\in\mathcal I_Q}\sup_{z\in\mathbb R}
|q_{Q,\alpha}(z)-\varphi(z)|\to0.
\tag{114.19}
$$

对 $X=\sqrt wZ+m$，精确特征函数为

$$
\mathbb Ee^{iuX^2}=(1-2iuw)^{-1/2}
\exp\{ium^2/(1-2iuw)\}.
\tag{114.20}
$$

中心化并标准化整个和，在每个固定频率紧区间上展开得

$$
\ln\psi_{Q,\alpha}(\xi)
=-\xi^2/2+
O\left(|\xi|^3\frac{\sum w_j^3+\sum w_j^2m_j^2}{W_H^{3/2}}\right)
=-\xi^2/2+O(|\xi|^3A_\alpha^{-1/2}).
\tag{114.21}
$$

分子各和由 $\max w_j$ 乘 $W_H$ 控制；Gaussian 噪声只有精确二次项。
非中心指数的模为
$\exp[-2u^2wm^2/(1+4u^2w^2)]\le1$，噪声模也至多一。
原比较坐标块给全频率界

$$
|\psi_{Q,\alpha}(\xi)|\le(1+c\xi^2/A_\alpha)^{-c'A_\alpha}.
\tag{114.22}
$$

$|\xi|\le\sqrt{A_\alpha}$ 时由 $e^{-c''\xi^2}$ 控制。
互补范围令 $\xi=\sqrt{A_\alpha}z$，分出半个指数在 $|z|\ge1$ 上取得
$e^{-c'''A_\alpha}$，剩余至少二次的幂可积，尾积分至多
$C\sqrt{A_\alpha}e^{-c'''A_\alpha}$。
先处理固定频率紧区间，再处理两段尾，得到特征函数的一致 $L^1$ 收敛。
Fourier 反演证明 (114.19)，不仅是分布收敛。

在物理能量 $h_y=V+\sqrt\delta y$ 与 $h_0=V$，标准化位置是

$$
z_y=\frac{\sqrt\delta y+\varepsilon_{\rm low}}{\sqrt{W_H}},\qquad
z_0=\frac{\varepsilon_{\rm low}}{\sqrt{W_H}}.
\tag{114.23}
$$

它们在 $\alpha\in\mathcal I_Q$、$|y|\le R$ 上一致趋零，因
$|z_y|\le C_R/\sqrt\alpha+o(1)$，低组误差由 (114.17) 支付。
(114.19) 在密度远离零的位置给
$\ln(q_{Q,\alpha}(z_y)/q_{Q,\alpha}(z_0))\to0$ 一致成立。
撤去同一个倾斜，高组 Gaussian 标量加 $\sigma G/\sqrt\alpha$ 的密度恰为

$$
g_{\alpha,\sigma}(y)=\frac{\sqrt\delta}{\sqrt{W_H}}
e^{K_H(t_\alpha)-t_\alpha h_y}q_{Q,\alpha}(z_y).
\tag{114.24}
$$

两输出的 $K_H,W_H$ 相同，故得到更强的比较式

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\left|\ln\frac{g_{\alpha,\sigma}(y)}{g_{\alpha,\sigma}(0)}
+t_\alpha\sqrt\delta y\right|\to0.
\tag{114.25}
$$

此处用倾斜以后中心密度的相对比，不把原稀有密度上的加性误差直接相除。

**相邻噪声宽度与稀有输出下界。** 令 $u=\sigma^2$，$|u'/u-1|\le h_Q$，其中 $h_Q$ 指数小。
固定原宽度的根 $t=t_\alpha(u)$，两宽度的高组累积量只差

$$
K_{H,u'}(t)-K_{H,u}(t)=\frac{\delta(u'-u)t^2}{2\alpha}.
\tag{114.26}
$$

倾斜均值差为 $\delta(u'-u)t/\alpha=O(|u'-u|)$，方差差为 $\delta(u'-u)/\alpha$。
用 $t\le C\alpha/\delta$、$W_H\asymp\alpha\delta$，其相对方差变化为
$O(|u'-u|/\alpha^2)$，标准化均值差指数小。
相同坐标块使两宽度都满足 (114.21)、(114.22)，在物理输出处的标准化密度均趋于 $\varphi(0)$。
将这些代入 (114.24)，包括指数、方差前因子和中心密度，得

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\frac1\alpha|\ln g_{\alpha,\sqrt{u'}}(y)-\ln g_{\alpha,\sqrt u}(y)|
\le C|u'-u|/\delta+o(1)/a_Q=o(1).
\tag{114.27}
$$

相对宽度扰动指数小，故没有要求 $\sigma$ 本身更快趋零。
此外 (114.24) 中 $K_H(t)\ge0$、$h_y$ 位于固定正紧区间、$q(z_y)\ge c$，
而 $\sqrt{\delta/W_H}\asymp\alpha^{-1/2}$，所以两相邻宽度均有

$$
g_{\alpha,\sigma'}(y)\ge e^{-C\alpha/\delta}.
\tag{114.28}
$$

先建立此下界，再删去任何加性误差。

**原整数计数与同一稀有输出上的选择。** 第 110 章有限 Stirling 比较的推导适用于整个
$1\le\alpha\le Q^6$：先对完整二项计数质量连同二项系数取幂，再归一化。
在高组联合中央盒 $|z_j|\le Q^2$，原乘积计数幂律与舍入 Gaussian 的联合质量比为
$1+O(\operatorname{poly}(Q)e^{-\varepsilon Q^3/4})$。
两者删去的尾概率至多

$$
\operatorname{poly}(Q)e^{-c\alpha Q^4+C\alpha}.
\tag{114.29}
$$

每个低计数元组都满足 $E_{\rm low}\le CQ^2e^{2\varepsilon Q^3}/B^2$；高组舍入与低组完整范围给

$$
|T(n)-T_G|\le\Delta_Q,\qquad
\Delta_Q\le\operatorname{poly}(Q)(B^{-1}+B^{-2}e^{2\varepsilon Q^3}),
\qquad \frac{\sqrt\alpha\Delta_Q}\sigma\le\operatorname{poly}(Q)e^{-b_0Q^3}.
\tag{114.30}
$$

全程保留精确 $\mu,V$。原 Gaussian 核的移位不等式将位移核夹在宽度
$(\sigma/\sqrt\alpha)/\sqrt{1\pm h_Q}$ 的核之间，并只付 $1+O(h_Q)$。
对高组中央盒与全部低组计数积分。
尾密度最多为 $\operatorname{poly}(Q)\sigma^{-1}e^{-c\alpha Q^4+C\alpha}$；
相对于 (114.28) 趋零，因为 $L=O(Q^3)$，$\alpha Q^4$ 压过 $Q^3$ 与 $\alpha/\delta$。
再由 (114.27)，对原乘积计数幂律 $Q_\alpha$ 有

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\alpha^{-1}|\ln f_{Q_\alpha,\sigma/\sqrt\alpha}(y)-\ln g_{\alpha,\sigma}(y)|\to0.
\tag{114.31}
$$

原完整选择关系仍是

$$
P_x(n)=\mathcal L_x\Bigl(\sum n_j\Bigr)Q_x(n),\qquad
-C(D(n)^2/q+q^{-1/2})\le\ln\mathcal L_x\le C(B^2V/q+q^{-1/2}).
\tag{114.32}
$$

有限计数估计还给 $\sup_{1\le\alpha\le Q^6}\mathbb E_{Q_\alpha}E=O_{\mathbb P}(1)$：
中央盒用 Gaussian 能量均值，互补盒用 $E\le CN_J^2/B^2=O_{\mathbb P}(B^2)$ 乘 (114.29)，因 $\ln B^2=O(Q^3)$。
对于一般 $U\ge0$、$\mathbb EU\le A_0$，用
$e^{-(U-h)^2/(2w^2)}$ 重加权，$|h|\le H_0$、$0<w\le1$ 时，均值仍一致有界。
证明是分母至少为 $\tfrac12e^{-(2A_0+H_0)^2/(2w^2)}$；足够大的固定 $R_0$ 外，归一化尾分子由
$2\sup_{u\ge R_0}u e^{-u^2/(8w^2)}$ 控制，内部均值至多 $R_0$。
这里不要求稀有壳层有不消失的概率。

同一完整元组的 Cauchy–Schwarz 给
$D(n)^2/q\le C\delta(E(n)+\|e\|^2)$。
令 $P_\alpha=P_x^\alpha/\sum P_x^\alpha$，精确恒等式为

$$
\frac{f_{P_\alpha,\sigma/\sqrt\alpha}(y)}{f_{Q_\alpha,\sigma/\sqrt\alpha}(y)}
=\frac{\mathbb E_{Q_\alpha,y}\mathcal L_x^\alpha}{\mathbb E_{Q_\alpha}\mathcal L_x^\alpha}.
\tag{114.33}
$$

分子使用的正是 $h=V+\sqrt\delta y$、$w=\sqrt\delta\sigma/\sqrt\alpha$ 的同一输出权重。
上述矩界、(114.32) 与 Jensen 把两个对数期望分别夹在
$-C\alpha\delta$ 和 $C\alpha(B^2V/q+q^{-1/2})$ 之间。
故 (114.33) 的对数除以 $\alpha$ 为 $O_{\mathbb P}(\delta)$，一致于当前阶数和紧输出。
结合 (114.25)、(114.31)，得到原后验的桥梁

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\left|-\alpha^{-1}\ln\frac{f_{P_\alpha,\sigma/\sqrt\alpha}(y)}
{f_{P_\alpha,\sigma/\sqrt\alpha}(0)}-b_{x,\alpha,\sigma}y\right|\to0.
\tag{114.34}
$$

乘积独立性仅属于比较律，实际 path 和选择后的计数并未独立化。

**所有更高有限阶数的根到极点界。** 对整个无界范围 $\alpha\ge\delta^{-1/3}$，有

$$
0<d_\alpha\le C(\alpha^{-2}+\delta/\alpha+\|e\|).
\tag{114.35}
$$

先在半极点 $t=\alpha/(4v_*)$ 用 $D_j\ge1/2$，得
$K'(t)\le2V/\alpha+4\|e\|^2+C\sigma^2<V$，所以实际根满足 $d_\alpha<1/2$。
在根处，(114.7)、(114.11) 给

$$
V\le C\left(\frac\delta{\alpha d_\alpha}
+\frac1{\alpha\sqrt{d_\alpha}}+\frac{\|e\|^2}{d_\alpha^2}+\sigma^2\right).
\tag{114.36}
$$

若 $d_\alpha\ge K(\alpha^{-2}+\delta/\alpha+\|e\|)$，前三项依次至多
$C/K,C/\sqrt K,C/K^2$；取足够大的固定 $K$，再用 $\sigma^2\to0$，与 $V$ 的正下界矛盾。
若该测试阈值已超过 $1/2$，(114.35) 自动成立。
于是

$$
0\le b_{x,\infty,\sigma}-b_{x,\alpha,\sigma}
\le C\left(\frac1{\alpha^2\sqrt\delta}+\frac{\sqrt\delta}\alpha
+\frac{\|e\|}{\sqrt\delta}\right)=o_{\mathbb P}(1)
\tag{114.37}
$$

一致于这个无界阶数区间。
此式不声称固定有限 $Q$、$e_0\ne0$ 时 $\alpha\to\infty$ 的根必到达极点；
非中心项可以使那个有限规模极限低于极点。
这里需要且证明的是 $Q$ 增长时的统一渐近比较。

第 112 章在 $\alpha\ge\delta^{-1/3}$ 的显式谱端项至多 $C_R\delta^{1/6}$，
所以其原实际响应可以换成 (114.37) 的有限根系数。
该章还通过真实有限计数支持连接无穷阶：支持原子数 $N\le(M+1)^{m_Q}$，
$\ln N\le CQ^5$，故在 $\alpha\ge Q^6$，分别对两个输出使用
$0\le H_\alpha-H_\infty\le\ln N/(\alpha-1)$，总误差为 $O(Q^{-1})$。
第 108 章端点结论完成重叠，无需在超多项式阶数把有效噪声当作仍大于整数网格。

**完成熵响应。** 对有限 $\alpha>1$，Gaussian 似然的有限和恒等式为

$$
H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
=\frac\alpha{\alpha-1}\left[
-\frac1\alpha\ln\frac{f_{P_\alpha,\sigma/\sqrt\alpha}(y)}{f_{P_\alpha,\sigma/\sqrt\alpha}(0)}
+\ln\frac{f_x(y)}{f_x(0)}\right].
\tag{114.38}
$$

先验熵精确相消。第 105 章在相同原噪声条件下给普通输出的绝对对数比
$\ln f_x(y)-\ln f_x(0)=-y^2/(2\nu)+o_{\mathbb P}(1)$，紧输出上一致。
用 (114.34) 即得较低区间的 (114.5)；(114.37) 与第 112 章给互补范围，包括无穷阶。
若较低区间为空，只需后一个论证。

所有估计在同一个实际好事件上确定地一致成立，再放开紧常数给支持一致概率结论。
pair/path 分别用原一、二行比较，辅助 Gaussian 独立性不替代实际行关系。
有限阶根由 $K''>0$ 连续依赖参数，有限原子熵连续依赖 $\alpha,y$，
所以这些上确界可由可数稠密集及单列的无穷阶端点表示，可测性没有额外缺口。
第 110 章有限因子修正、第 112 章谱端展开均保持原范围；
本章用一个精确有限系数统一其后的发散阶数，而没有把连续极限中的误差放入放大的中心。

经典正指数倾斜、Gaussian 二次型变换、Fourier 局部极限与有限 Gibbs／Rényi 恒等式各按原条件使用。
本章不声称新的一般局部极限定理、单模最优化、全局原创、输出平均熵、无界输出或 Shannon 延拓。

## 追加锚（第 114 章后续增补区）

## 115. 经验鞍点的曲率把统一响应延伸到所有远离一的阶数

**定理 115.1（固定 Shannon 间隔上的完整经验响应）。** 保持第 114 章的原完整计数后验、固定参数、全部取整、实际经验中心、同一带噪标量，以及

$$
\delta=Q^{-1/2},\qquad L=\ln(1/\sigma)\to\infty,
\qquad \limsup L/Q^3<c_q/2.
\tag{115.1}
$$

对每个固定 $\epsilon>0$，在概率趋一的共同实际好事件上，第 114 章完整累积量

$$
K_{\alpha,\sigma}(t)=
-\frac12\sum_j\ln(1-2tv_j/\alpha)
+\sum_j\frac{te_j^2}{1-2tv_j/\alpha}
+\frac{\delta\sigma^2t^2}{2\alpha}
\tag{115.2}
$$

对每个有限 $\alpha\ge1+\epsilon$ 都有唯一正根 $K'(t_\alpha)=V$。
这里仍是完整原窗口上的
$v_j=C_jp_j(1-p_j)/B^2$、$e_j=(\mu_j-C_jp_j)/B$、$V=\sum_jv_j$、$v_*=\max_jv_j$，
$B^2=q/Q^{5/2}$，零方差项按确定项解释。定义精确有限量

$$
W_\alpha=K''(t_\alpha),\qquad b_\alpha=\sqrt\delta\,t_\alpha/\alpha.
\tag{115.3}
$$

对每个固定 $R<\infty$，

$$
\sup_{\substack{\alpha\in[1+\epsilon,\infty]\\ |y|\le R}}
\left|H_\alpha(\mathsf P_x^y)-H_\alpha(\mathsf P_x^0)
-\frac\alpha{\alpha-1}\left[
b_\alpha y+\left(\frac\delta{2\alpha W_\alpha}-\frac1{2\nu}\right)y^2
\right]\right|\longrightarrow0.
\tag{115.4}
$$

无穷阶取因子为一、$b_\infty=\sqrt\delta/(2v_*)$ 和 $\delta/(\alpha W_\alpha)=0$。
收敛在原实际数据概率下对全部大小 $q$ 的确定支持一致，pair/path 分别成立。
所有阶数、系数和输出均使用同一个实际数据纤维。
$\epsilon$ 固定，常数和好事件阈值可以依赖它；本章不包含移动的 $\epsilon_Q\downarrow0$ 或 Shannon 端点。
噪声可以任意慢地趋零，放大的线性系数和曲率都不换成连续谱极限。

**共同正根及低阶几何。** 第 114 章的实际估计仍给
$V\to\gamma>0$、$v_*/\delta\to\rho_0>0$、$\|e\|=O_{\mathbb P}(\delta^5)$，
以及完整数组的剖面和谱亏损 (114.8)、(114.9)。
由 (114.7)，在同一事件 $\|e\|^2<V\epsilon/(1+\epsilon)$ 上，

$$
K'(0)\le V/(1+\epsilon)+\|e\|^2<V,
\qquad K''(t)>0.
\tag{115.5}
$$

最大中心平方项在右极点发散，故对全部有限 $\alpha\ge1+\epsilon$ 同时有唯一正根。
以下先限制紧随机常数，再放开限制。令

$$
\mathcal I_Q=[1+\epsilon,\delta^{-1/3}],\quad
A=(\alpha\delta)^{-1},\quad
s_\alpha=2v_*t_\alpha/\alpha,\quad d_\alpha=1-s_\alpha,
$$

$$
q_j^\circ=1-v_j/v_*,\qquad
D_j=1-2t_\alpha v_j/\alpha=d_\alpha+(1-d_\alpha)q_j^\circ.
\tag{115.6}
$$

需要在有界阶数也证明

$$
c/\alpha^2\le d_\alpha\le C/\alpha^2
\quad(\alpha\in\mathcal I_Q).
\tag{115.7}
$$

第 114 章的确定和式估计
$S(d)=\sum_jv_j/[d+(1-d)q_j^\circ]\le C(\delta/d+d^{-1/2})$
在 $0<d\le1/2$ 成立。
对充分小的固定 $d_0$，只要 $d\le d_0$ 且 $\sqrt d/\delta\to\infty$ 一致成立，
中央块 $|j|\le c\sqrt d/\delta$ 就给 $S(d)\ge c/\sqrt d$；这个下界不要求 $d\to0$。

先取充分小的固定 $k>0$，在 $d=k/\alpha^2$ 有
$d\le d_0$、$\sqrt d/\delta\ge\sqrt k\delta^{-2/3}$，所以
$S(d)/\alpha\ge c/\sqrt k>V$。其余根方程项非负，单调性给下界。
再取充分大的固定 $K$。对 $\alpha\ge\sqrt{2K}$，在 $d=K/\alpha^2\le1/2$，

$$
S(d)/\alpha\le C/\sqrt K+C\alpha\delta/K,\qquad
\sum_j e_j^2/D_j^2\le C\delta^{10}\alpha^4/K^2=o(1),
\qquad \delta\sigma^2t/\alpha\le C\sigma^2=o(1).
\tag{115.8}
$$

因 $\alpha\delta\le\delta^{2/3}$，取 $K$ 大使测试点的 $K'<V$，得到上界。
剩余 $\alpha<\sqrt{2K}$ 用 $d_\alpha<1\le2K/\alpha^2$。
这补上有界阶数，不直接借用第 114 章的发散下截点。

在根处，倾斜 Gaussian 坐标的精确方差和均值为
$w_j=v_j/(\alpha D_j)$、$m_j=-e_j/D_j$。
原中央块中有 $N\asymp A$ 个高计数坐标满足

$$
c/A\le w_j\le C/A,
\qquad \max_jw_j\le C/A,
\qquad \sum_jw_j\le V,
\qquad \sum_jm_j^2\le C\delta^{10}\alpha^4=o(1).
\tag{115.9}
$$

确切地，取 $|j|\le cA$，则 $|j\delta|\le c/\alpha$ 位于固定小弧，
$v_j\asymp\delta$，$D_j\asymp\alpha^{-2}$；最后两式也由完整根方程及 (115.7) 得到。
$A\ge\delta^{-2/3}$ 一致发散。

**完整根处的高组方差。** 取 $l<c_q/2$ 使 $L\le lQ^3$，再取 $\zeta>0$ 使
$2\zeta<c_q-l$，置 $H=\{j:C_j\ge e^{\zeta Q^3}\}$。
全部比较坐标都在 $H$。令 $K_H$ 仅限制坐标和，保留完整噪声项及输出中的完整 $V$。
原低组范围给

$$
\ell_v=\sum_{j\notin H}v_j\le\operatorname{poly}(Q)e^{-(c_q-\zeta)Q^3},\qquad
\ell_e=\sum_{j\notin H}e_j^2\le\operatorname{poly}(Q)e^{-(c_q-2\zeta)Q^3}.
\tag{115.10}
$$

低组 $D_j\ge1/2$。在同一个完整根处，记

$$
K_H'(t_\alpha)=V-\varepsilon_{\rm low},\quad
0\le\varepsilon_{\rm low}\le C(\ell_v/\alpha+\ell_e),\quad
W_H=K_H''(t_\alpha)\asymp A^{-1}=\alpha\delta.
\tag{115.11}
$$

方差下界由比较块给出，上界用 (115.9) 和噪声方差 $\delta\sigma^2/\alpha$。
完整方差差明确满足

$$
0\le W_\alpha-W_H
\le C(\ell_v^2/\alpha^2+\ell_v\ell_e/\alpha),
$$

$$
\sup_{\alpha\in\mathcal I_Q}\frac\delta\alpha
\left|W_H^{-1}-W_\alpha^{-1}\right|\to0,
\qquad
\sup_{\alpha\in\mathcal I_Q}\varepsilon_{\rm low}/\sqrt{\alpha\delta}\to0.
\tag{115.12}
$$

第一式从低坐标在 (114.7) 中的两项逐项求和；第二式除以
$W_HW_\alpha\ge c\alpha^2\delta^2$ 即得。

**直接应用 Gaussian 泛函的经典密度定理。** 令 $F$ 是高组完整倾斜能量，
包括倾斜后的独立噪声，减去精确均值后除以 $\sqrt{W_H}$。
它作为标准正态坐标的函数恰为

$$
F=\sum_H a_j(Z_j^2-1)+\sum_H\beta_jZ_j+\beta_GG,
\quad a_j=w_j/\sqrt{W_H},\quad
\beta_j=2m_j\sqrt{w_j}/\sqrt{W_H},\quad
\beta_G=\sqrt{\delta\sigma^2/\alpha}/\sqrt{W_H}.
\tag{115.13}
$$

精确归一化给 $2\sum a_j^2+\sum\beta_j^2+\beta_G^2=1$。
Hu–Lu–Nualart 的 arXiv:1302.6962v2，Theorem 6.5，条件 (6.10)，要求
$F_n\in\mathbb D^{2,s}$、收敛于非退化正态，以及

$$
\sup_n\bigl(\|F_n\|_{2,s}+\|F_n\|_{2p}
+\|\|DF_n\|^{-2}\|_r\bigr)<\infty,
\qquad p,r,s>1,\quad 1/p+1/r+1/s=1.
\tag{115.14}
$$

其结论为连续密度的一致收敛。本章直接取 $p=2,r=4,s=4$。
方差一的至多二次 Gaussian 多项式的四阶矩由系数平方和控制。
梯度分量是 $2a_jZ_j+\beta_j$ 和 $\beta_G$，Hessian 是对角常数 $2a_j$，
其 Hilbert–Schmidt 范数平方 $4\sum a_j^2\le2$。
所以 $\|F\|_{2,4}$ 和 $\|F\|_4$ 一致有界，不依赖维数。

逆梯度矩也由同一比较块验证：其中 $a_j^2\ge c/A$，故

$$
\|DF\|^2\ge\frac cA\sum_{j\in\mathcal B}(Z_j+\beta_j/(2a_j))^2,
\qquad |\mathcal B|=N\asymp A.
\tag{115.15}
$$

对任意位移 $c_j$ 和 $u\ge0$，

$$
\mathbb E e^{-u\sum_{j=1}^N(Z_j+c_j)^2}
=(1+2u)^{-N/2}\exp\left[-\frac{u\sum c_j^2}{1+2u}\right]
\le(1+2u)^{-N/2}.
$$

乘 $u^3/6$ 积分，得到移位平方范数的四阶逆矩不超过
$[(N-2)(N-4)(N-6)(N-8)]^{-1}$。于是

$$
\mathbb E\|DF\|^{-8}\le
\frac{CA^4}{(N-2)(N-4)(N-6)(N-8)}\le C.
\tag{115.16}
$$

噪声梯度只增大左侧逆幂前的平方范数。非中心项没有被删去。
精确特征函数 (114.20) 在固定频率紧区间展开给

$$
\ln\mathbb Ee^{i\xi F}
=-\xi^2/2+
O\left(|\xi|^3\frac{\sum w_j^3+\sum w_j^2m_j^2}{W_H^{3/2}}\right)
=-\xi^2/2+O(|\xi|^3A^{-1/2}).
\tag{115.17}
$$

因此沿任意允许数组和阶数序列都有正态分布收敛。
若密度一致性在整个参数族失败，就选出固定正误差的数组序列，
嵌入同一个可数等距 Gaussian 空间；(115.14)–(115.17) 对它仍一致成立，
经典定理产生矛盾。所以标准化密度 $q_{Q,\alpha}$ 满足

$$
\sup_{\alpha\in\mathcal I_Q}\sup_{z\in\mathbb R}
|q_{Q,\alpha}(z)-\varphi(z)|\to0.
\tag{115.18}
$$

这是对一般 Gaussian 泛函定理的直接应用。完整变量含一、二阶混沌，
不把第 114 章引用的单一混沌条件误套于它。

**有界标准化输出留下的曲率。** 物理能量 $h_y=V+\sqrt\delta y$ 的标准化位置为

$$
z_y=(\sqrt\delta y+\varepsilon_{\rm low})/\sqrt{W_H},
\qquad z_0=\varepsilon_{\rm low}/\sqrt{W_H}.
\tag{115.19}
$$

它们在当前范围只保证位于共同紧区间；有界 $\alpha$ 时不能断言 $z_y\to0$。
该紧区间上 $\varphi$ 有正下界，故 (115.18) 给

$$
\ln\frac{q_{Q,\alpha}(z_y)}{q_{Q,\alpha}(z_0)}
=-\frac{\delta y^2}{2W_H}
-\frac{\sqrt\delta y\varepsilon_{\rm low}}{W_H}+o(1).
\tag{115.20}
$$

交叉项由 (115.10)、(115.11) 一致趋零。
对原高组 Gaussian 标量加 $\sigma G/\sqrt\alpha$ 的密度 $g_{\alpha,\sigma}$，
精确撤倾斜公式 (114.24) 仍用同一 $K_H,t_\alpha,W_H$，所以

$$
-\frac1\alpha\ln\frac{g_{\alpha,\sigma}(y)}{g_{\alpha,\sigma}(0)}
=b_\alpha y+\frac\delta{2\alpha W_\alpha}y^2+o(1).
\tag{115.21}
$$

完整方差替换由 (115.12) 支付。正曲率来自对负的正态对数密度曲率乘 $-1/\alpha$，
没有对第 114 章的 $C^0$ 渐近式求导。

**相邻噪声与原计数回接。** 舍入比较需要 $u=\sigma^2$ 与
$|u'/u-1|\le h_Q$，其中 $h_Q$ 对 $Q^3$ 指数小。
固定原完整根 $t=t_\alpha(u)$，有精确变化

$$
K_{H,u'}(t)-K_{H,u}(t)=\delta(u'-u)t^2/(2\alpha),
$$

$$
K'_{H,u'}(t)-K'_{H,u}(t)=\delta(u'-u)t/\alpha,
\qquad W_{H,u'}-W_{H,u}=\delta(u'-u)/\alpha.
\tag{115.22}
$$

$t\le C\alpha/\delta$，所以均值变化为 $O(|u'-u|)$，相对方差变化为
$O(|u'-u|/\alpha^2)$。标准化位置变化至多
$C_R|u'-u|/\sqrt{\alpha\delta}+C_R|u'-u|/\alpha^2=o(1)$。
同一比较块验证两宽度下的 (115.14)–(115.18)，密度在各自有界位置相对比较。
包括指数项及前因子后，

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\alpha^{-1}|\ln g_{\alpha,\sqrt{u'}}(y)-\ln g_{\alpha,\sqrt u}(y)|
\le C|u'-u|/\delta+o(1)=o(1).
\tag{115.23}
$$

这不要求 $\sigma$ 更快趋零，也不把两中心密度都替成 $\varphi(0)$。
先由撤倾斜公式、$K_H(t)\ge0$、$q(z_y)\ge c_R$ 和
$\sqrt{\delta/W_H}\asymp\alpha^{-1/2}$ 得到两宽度共同的稀有密度下界

$$
g_{\alpha,\sigma'}(y)\ge e^{-C_R\alpha/\delta}.
\tag{115.24}
$$

第 110、114 章有限幂二项比较原本在 $1\le\alpha\le Q^6$ 有效：
先对含二项系数的完整计数质量取幂，再归一化。
高组联合盒 $|z_j|\le Q^2$ 内，乘 $\alpha$ 的 Stirling 余项和格点 Gaussian 归一化给
$1+O(\operatorname{poly}(Q)e^{-\zeta Q^3/4})$ 的质量比，
删去的两边尾概率均为
$\operatorname{poly}(Q)e^{-c\alpha Q^4+C\alpha}$。
全部低元组和高组舍入给

$$
|T(n)-T_G|\le\Delta_Q\le
\operatorname{poly}(Q)(B^{-1}+B^{-2}e^{2\zeta Q^3}),
\qquad \sqrt\alpha\Delta_Q/\sigma\le\operatorname{poly}(Q)e^{-b_0Q^3}.
\tag{115.25}
$$

完整 $\mu,V$ 保留。Gaussian 核移位不等式把该位移夹于相邻宽度之间。
尾密度除以 (115.24) 趋零，因为 $\alpha\ge1+\epsilon$、$L=O(Q^3)$，
$\alpha Q^4$ 压过 $Q^3$ 和 $\alpha/\delta$。
结合 (115.23)，原乘积计数幂律 $Q_\alpha$ 满足

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\alpha^{-1}|\ln f_{Q_\alpha,\sigma/\sqrt\alpha}(y)-\ln g_{\alpha,\sigma}(y)|\to0.
\tag{115.26}
$$

原完整选择仍使用 (114.32)、(114.33)。
其能量矩界 $\sup_{1\le\alpha\le Q^6}\mathbb E_{Q_\alpha}E=O_{\mathbb P}(1)$
也含当前有界阶数：盒内用 Gaussian 均值，盒外用
$E\le CN_J^2/B^2=O_{\mathbb P}(B^2)$ 乘上述尾界。
第 114 章的稀有壳层重加权矩论证对每个 $0<w\le1$ 成立，
此处用同一物理壳层 $h=V+\sqrt\delta y$、$w=\sqrt\delta\sigma/\sqrt\alpha$。
因此 Jensen 和 $D(n)^2/q\le C\delta(E+\|e\|^2)$ 给

$$
\sup_{\alpha\in\mathcal I_Q,\ |y|\le R}
\alpha^{-1}\left|\ln\frac{f_{P_\alpha,\sigma/\sqrt\alpha}(y)}
{f_{Q_\alpha,\sigma/\sqrt\alpha}(y)}\right|=O_{\mathbb P}(\delta).
\tag{115.27}
$$

乘积独立性仅属于比较律。完整选择和实际 path 行依赖没有被删除。
(115.21)、(115.26)、(115.27) 将曲率比回接到原 $P_\alpha$。

**命题 115.2（完整鞍点的有限方差下界）。** 对任意有限阶数的正根和任意
$0<\eta<1$，若

$$
B_\eta=V-\frac V{\alpha\eta}-\frac{\|e\|^2}{\eta^2}
-\frac{\delta\sigma^2}{2v_*}>0,
\tag{115.28}
$$

则

$$
W_\alpha\ge\frac{2(1-\eta)v_*}{\alpha\eta}B_\eta,
\qquad
\frac\delta{\alpha W_\alpha}\le
\frac{\delta\eta}{2(1-\eta)v_*B_\eta}.
\tag{115.29}
$$

证明在同一个根方程中分组。$D_j\ge\eta$ 的坐标均值贡献至多
$V/(\alpha\eta)+\|e\|^2/\eta^2$，正噪声均值至多 $\delta\sigma^2/(2v_*)$。
所以 $D_j<\eta$ 的两种坐标均值之和至少 $B_\eta$。
因 $D_j=1-s_\alpha v_j/v_*$、$0<s_\alpha<1$，这些坐标满足
$v_j\ge(1-\eta)v_*$，其方差贡献逐项有

$$
\frac{2v_j}{\alpha D_j}\frac{v_j}{\alpha D_j}
+\frac{4v_j}{\alpha D_j}\frac{e_j^2}{D_j^2}
\ge\frac{2(1-\eta)v_*}{\alpha\eta}
\left(\frac{v_j}{\alpha D_j}+\frac{e_j^2}{D_j^2}\right).
$$

求和并保留其余非负方差项即证。零方差确定坐标在 $D_j=1$ 一组，
非中心项与噪声都已支付；不需要谱隙，也不组合分别可达的最大值。

对任意确定 $A_Q\to\infty$，取 $h=\|e\|$、$\eta=\alpha^{-1/2}+\sqrt h$。
在所有有限 $\alpha\ge A_Q$ 上，$\eta<1/2$ 最终一致成立，且
$V/(\alpha\eta)\le V/\sqrt\alpha$、$h^2/\eta^2\le h$。
所以 $B_\eta\ge V/2$，(115.29) 给

$$
\sup_{A_Q\le\alpha<\infty}\frac\delta{\alpha W_\alpha}
\le C(A_Q^{-1/2}+\sqrt{\|e\|})
=O_{\mathbb P}(A_Q^{-1/2}+\delta^{5/2})\to0.
\tag{115.30}
$$

它包括超多项式阶数，并允许有限 $Q$ 的非中心根不趋于极点。

**完成全部阶数。** 对 $\mathcal I_Q$，把原幂律密度比代入精确有限和恒等式
(114.38)，再用第 105 章普通输出的紧集对数比
$\ln f_x(y)-\ln f_x(0)=-y^2/(2\nu)+o_{\mathbb P}(1)$。
因 $\alpha/(\alpha-1)\le(1+\epsilon)/\epsilon$，得到 (115.4)。
对 $\alpha\ge\delta^{-1/3}$，第 114 章以发散下截点给同一精确斜率的响应，
(115.30) 使新增曲率项一致趋零，于是也得到 (115.4)。
无穷阶保持第 114 章的真实有限支持重叠：
$\ln N\le m_Q\ln(M+1)\le CQ^5$，
$0\le H_\alpha-H_\infty\le\ln N/(\alpha-1)$ 在 $\alpha\ge Q^6$ 给两输出总误差 $O(Q^{-1})$。
无需在无界阶数用仍大于整数网格的有效噪声，也不对熵差使用单调性。

所有估计在同一个实际好事件上一致成立，放开紧常数给原支持一致概率结论。
有限根由 $K''>0$ 连续依赖参数，有限原子熵连续依赖阶数和输出，
可数稠密集与单列的无穷阶端点给可测上确界。
本章新增的是有界阶数保留的曲率比及全阶数有限方差比较；
经典密度定理、Gaussian 变换和 Rényi 恒等式各按原条件使用。
不声称移动 Shannon 间隔、无界输出、输出平均熵、半指数边界等号或全局原创。

## 追加锚（第 115 章后续增补区）

## 116. 固定噪声间隙的相位修正与实际经验中心的算术接口

**定理 116.1（固定正带宽下的完整相位修正）。** 保持第 101、111、113 章的原实际模型、固定幅度与参数、全部取整、完整计数元组、经验中心和同一 Gaussian 观测。令

$$
\delta=Q^{-1/2},\quad B^2=q/Q^{5/2},\quad
\mathcal B=B^2\sqrt\delta=q/Q^{11/4},\quad
T=\mathcal B^{-1}\sum_j(R_j-\mu_j)^2-V/\sqrt\delta,
\qquad Y=T+\sigma G.
\tag{116.1}
$$

仍用原精确先验惊讶 $S=-\ln P_x(R)$、先验方差 $V_x^{\rm prior}$、后验方差熵 $V_x^{\rm post}(y)$。
对第 113 章同一个固定合法对数核心 $H$，保留其有限系数

$$
A=V_H/\sqrt\delta,\quad\nu_0=2\sum_Hw_j^2,\quad
\kappa_3=8\sum_Hw_j^3,\quad\Lambda=\nu_0+\sigma^2,
\quad C_x=A^2\kappa_3/\Lambda^3-2A\nu_0/\Lambda^2,
$$

$$
D_x(y)=V_x^{\rm post}(y)-V_x^{\rm prior}+A^2/\Lambda-C_xy,
\qquad
R_*(y)=\frac{29}{6}-3\sqrt2+
\left(3\sqrt2+\frac8{\sqrt3}-9\right)\frac{y^2}{\nu}.
\tag{116.2}
$$

这些量不在比较后重新计算。精确输出均值也保持 $m_x=\mathbb E_xY$。
对任意固定 $D\in\mathbb R$，沿任意原合法确定序列

$$
\Delta_Q=\ln\mathcal B-\ln(1/\sigma)\to D,
\qquad a_Q=\sigma\mathcal B\to e^D>0,
\tag{116.3}
$$

下面显式构造实值 $2\pi$ 周期函数 $M_0,M_1,M_2$，满足

$$
0<c_D\le M_0(\theta)\le C_D,
\qquad |M_1(\theta)|+|M_2(\theta)|\le C_D.
\tag{116.4}
$$

常数在限制原紧随机常数的好事件上独立于 $Q$、支持和经验扭转。
置

$$
\mathcal K_x(\theta)=\frac{M_2(\theta)}{M_0(\theta)}
-\left(\frac{M_1(\theta)}{M_0(\theta)}\right)^2,
\qquad K_x(y)=\mathcal K_x(\pi\mathcal B y).
\tag{116.5}
$$

则在原实际数据概率下、对大小 $q$ 的固定支持一致，pair/path 分别有

$$
\int f_x(y)|D_x(y)-R_*(y)-K_x(y)|\,dy\longrightarrow0.
\tag{116.6}
$$

进一步，

$$
\int f_x|D_x-R_*|=\mathfrak J_x+o_{\mathbb P}(1),
\qquad
\mathfrak J_x=\frac1{2\pi}\int_0^{2\pi}
\left|M_2-\frac{M_1^2}{M_0}\right|d\theta.
\tag{116.7}
$$

所以无修正的固定间隙结论等价于同一实际经验泛函 $\mathfrak J_x\to0$。
本章不证明它消失，也不给出使它不消失的实际正概率事件；该原问题仍未解决。
第 113 章 $\Delta_Q\to\infty$ 的结论保持原范围。
这里给出的是显式相位修正、受控的全输出余项和等价边界判据，不声称新的实际逐输出结论或环境上的无界期望收敛。

**同一完整经验数组的显式系数。** 原乘积比较律 $Q_x$ 的坐标为
$R_j\sim\operatorname{Bin}(C_j,p_j)$，记 $m_j=C_jp_j$、$d_j=C_jp_j(1-p_j)$、$w_j=d_j/\mathcal B$。
按第 111 章取
$J=\{j:d_j\ge Q^{3600}\}$、$E=\{j\notin J:C_j>0\}$。
原好事件给 $|J|=O(Q^2)$、$|E|=O(1)$、$H\subset J$。
辅助格点概率律仅把 $J$ 坐标替为

$$
g_j(k)=Z_j^{-1}e^{-(k-m_j)^2/(2d_j)},\quad k\in\mathbb Z,
\qquad Z_j=\sum_{k\in\mathbb Z}e^{-(k-m_j)^2/(2d_j)},
\tag{116.8}
$$

$E$ 保留原二项律。选中权重不施加到负格点计数上。
定义仅供相位系数使用的完整大组量

$$
c_{\rm lat}=\prod_{j\in J}\frac{\sqrt{2\pi d_j}}{Z_j},\quad
A_b=\sum_Jw_j,\quad\nu_b=2\sum_Jw_j^2,\quad
k_b=8\sum_Jw_j^3,\quad\varepsilon=\max_Jw_j.
$$

$$
\varepsilon\asymp Q^{-1/4},\quad A_b\varepsilon\le C,
\quad\nu_b\to\nu>0,\quad k_b=O(\varepsilon).
\tag{116.9}
$$

它们不替换 (116.2) 的核心系数。至少 $c\varepsilon^{-2}$ 个原中央坐标的权重位于
$[c\varepsilon,\varepsilon]$。这些是原实际占据和剖面的共同好事件，path 仍用其原行关系。

令 $s_E$ 是保留的联合 $E$ 二项律的精确中心惊讶，$V_E=\mathbb E_Es_E^2$。
对每个整数 $\ell$，记 $b_{\ell j}=\pi\ell(1-2\mu_j)$ 及

$$
\chi_{\ell,0}=\mathbb E_Ee^{i\sum_E b_{\ell j}R_j},\quad
\chi_{\ell,1}=\mathbb E_E[s_Ee^{i\sum_E b_{\ell j}R_j}],\quad
\chi_{\ell,2}=\mathbb E_E[(s_E^2-V_E)e^{i\sum_E b_{\ell j}R_j}].
\tag{116.10}
$$

$E$ 为空时取 $1,0,0$。它们是归一化实倾斜
$\mathbb E_Ee^{us_E+i b_\ell\cdot R_E}/\mathbb E_Ee^{us_E}$ 在零处的前两阶导数，
模一致有界。暂时不删除 $E$ 的相关能量；下面先支付联合删除的误差。
对 $\ell\in\mathbb Z$、$k\in\mathbb Z^J$ 定义

$$
\xi_{\ell k,j}=\sqrt{d_j}(b_{\ell j}-2\pi k_j),\quad
E_{\ell k}=\sum_J\xi_{\ell k,j}^2,\quad
B_{1,\ell k}=\sum_Jw_j\xi_{\ell k,j}^2,\quad
B_{2,\ell k}=\sum_Jw_j^2\xi_{\ell k,j}^2,
$$

$$
\eta_\ell=\pi\ell a_Q,\quad h_{\ell k}=E_{\ell k}+\eta_\ell^2,
\quad\omega_\ell=e^{i\pi\ell(\sum_j\mu_j^2-B^2V)},\quad
z_{\ell k}=\omega_\ell e^{i\sum_J(b_{\ell j}-2\pi k_j)m_j}.
\tag{116.11}
$$

$\omega_\ell$ 中包含全部原组，完整截距和 $1-2\mu_j$ 的符号均保留。
不作独立相位或任意整数中心替换。
令

$$
P_{1,\ell k}=-h_{\ell k}/2+A_bB_{1,\ell k}/\nu_b,
$$

$$
\begin{aligned}
P_{2,\ell k}={}&h_{\ell k}^2/4-h_{\ell k}
+(2-h_{\ell k})A_bB_{1,\ell k}/\nu_b\\
&+A_b^2k_bB_{1,\ell k}/\nu_b^3
+A_b^2(B_{1,\ell k}^2-4B_{2,\ell k})/\nu_b^2.
\end{aligned}
\tag{116.12}
$$

所有 $h$ 都含同一残差噪声的 $\eta_\ell$；$\sigma\to0$ 不使固定 $\ell$ 的 $\eta_\ell$ 趋零。
显式周期函数为

$$
M_0(\theta)=c_{\rm lat}\sum_{\ell,k}
e^{-i\ell\theta}z_{\ell k}e^{-h_{\ell k}/2}\chi_{\ell,0},
$$

$$
M_1(\theta)=c_{\rm lat}\sum_{\ell,k}
e^{-i\ell\theta}z_{\ell k}e^{-h_{\ell k}/2}
(P_{1,\ell k}\chi_{\ell,0}+\chi_{\ell,1}),
$$

$$
M_2(\theta)=c_{\rm lat}\sum_{\ell,k}
e^{-i\ell\theta}z_{\ell k}e^{-h_{\ell k}/2}
(P_{2,\ell k}\chi_{\ell,0}+2P_{1,\ell k}\chi_{\ell,1}+\chi_{\ell,2}).
\tag{116.13}
$$

包括 $\ell=0$ 的非零对偶 $k$，虽然后者可忽略，保留它们使下面的质量正性恒等式精确。
这些级数绝对收敛、实值且光滑，每个固定阶 $\theta$ 导数有一致界。
它们只用原有限经验数组、原 $E$ 二项因子与显式 Gaussian 格点和；不含未知条件期望或待证的 $\ln(f/g)$。
不声称有效计算复杂度。

**固定正带宽仍允许原格点归约。** 第 111 章格点归约证明使用噪声间隙的地方是
Gaussian 加权的周期上确界和。若 $0<a_-\le\sigma\mathcal B\le a_+<\infty$，则

$$
\sum_{n\in\mathbb Z}\sup_{\theta\in[n,n+1]}
e^{-\pi^2a_-^2\theta^2}\le C_{a_-}<\infty.
\tag{116.14}
$$

前两阶噪声标记的多项式可吸收进半个 Gaussian 指数。
在同一原数组中逐组替换，每步保留十六个未标记原中央因子的周期积分界 $C/d_c$，
第 111 章中心带符号质量至四阶的比较给

$$
\max_{h\le2}\|\widehat q_h^{Q}-\widehat q_h^{\rm lat}\|_1\le C_DQ^{-440}.
\tag{116.15}
$$

Fourier 反演先给上确界误差；在 $|y|\le Q^{100}$ 积分并以四阶矩处理补集，
带符号密度的 $L^1$ 误差为 $O(Q^{-198})$。
用截断水平 $Q^{10}$ 的条件均值平方不等式 (111.16)，四阶目标矩 $O(Q^4)$ 给 $O(Q^{-16})$，
精确先验方差比较误差 $O(Q^{-448})$ 也可支付。
完整选择先按同一通道返回：原 $\mathcal L_x=dP_x/dQ_x$ 满足
$0\le\mathcal L_x\le C$、$a_x=\|\mathcal L_x-1\|_2=O_{\mathbb P}(Q^{-5/2})$，
原中心方差密度比较费用为 $Ca_xQ^2=o_{\mathbb P}(1)$，包括 $\ln\mathcal L_x$。
有限系数的质量和矩付款仍由相同输出矩控制。
所以原目标及格点目标满足

$$
\|f_xD_x-f_{\rm lat}D_{\rm lat}\|_1=o_{\mathbb P}(1),\qquad
\int(1+y^2)|f_x-f_{\rm lat}|dy=o_{\mathbb P}(1).
\tag{116.16}
$$

这里 $D_{\rm lat}$ 使用格点律的精确先验方差、同一 $G$ 和原 (116.2) 系数。
比较不除以 $\sigma$ 或选中密度。path 行没有独立化。
同样的周期和将第 109 章半整数条带外双标记界改为
$C_DQ^{17/4}e^{-c\sqrt Q}$；整个频率线仍被覆盖。
由此完整格点通道分解为连续大组参考项和原半整数 Poisson 模，
零、一、二阶矩密度的定位误差均可取 $O(Q^{-430})$。

**归一化标记的显式计算。** 对连续中央大组参考量

$$
T_0=\sum_Jw_j(Z_j^2-1),\qquad
P(t)=\prod_Je^{-itw_j}(1-2itw_j)^{-1/2},
\tag{116.17}
$$

令其密度为 $p$。原中央储备给
$|P(t)|\le(1+c\varepsilon^2t^2)^{-c'/\varepsilon^2}$，
每个固定多项式 Fourier 矩一致有界。
各高阶累积量满足 $k_r=2^{r-1}(r-1)!\sum_Jw_j^r=O_r(\varepsilon^{r-2})$。
取 $h_Q=\sqrt{100\nu\ln Q}$。第 113 章的直接固定高阶导数展开，在当前有限
$\nu_b,k_b$ 下给出所需的明确首项：记 $l=\ln p$、$H_2=p''/p$，则在 $|y|\le h_Q$，

$$
p\ge Q^{-60},\quad
l''=-1/\nu_b+O(\varepsilon(1+|y|^d)),
$$

$$
l'''=k_b/\nu_b^3+O(\varepsilon^2(1+|y|^d))+O(Q^{-100}),
\quad H_2''=2/\nu_b^2+O(\varepsilon(1+|y|^d))+O(Q^{-100}).
\tag{116.18}
$$

这里及下文 $d$ 是充分大的固定多项式次数，可以随所需有限阶导数增加。
具体地，先在 Fourier 侧展开 $\ln P$ 和其指数至足够高的固定阶，例如 1200 阶，
余项对 $e^{-ct^2}$ 的多项式可积；补频率用中央储备指数界。
得到所有所需固定导数的展开，其中

$$
p(y)=\varphi_{\nu_b}(y)
\left[1+\frac{k_b}{6\nu_b^3}(y^3-3\nu_b y)
+O(\varepsilon^2(1+|y|^d))\right].
\tag{116.19}
$$

$\varphi_{\nu_b}(h_Q)>Q^{-51}$ 最终成立，绝对余项可取小于 $Q^{-250}$。
先支付密度除法再对展开比求导，即得 (116.18)，尤其 $l'''$ 的首项为正。
这不是弱 Edgeworth 收敛或对无导数控制的渐近式求导。

对任意实向量 $\xi$，记 $E=\|\xi\|^2$、$B_1=\sum w_j\xi_j^2$、$B_2=\sum w_j^2\xi_j^2$。
用第 113 章相同光滑条带截断 $\chi(t/W_Q)$，$W_Q\asymp\varepsilon^{-1}$，定义

$$
r_\xi(y)=\frac1{2\pi p(y)}\int e^{-ity}\chi(t/W_Q)P(t)
\exp\left[-\frac12\sum_J\frac{\xi_j^2}{1-2itw_j}\right]dt.
\tag{116.20}
$$

在两次 $y$ 导数及每个所需固定径向导数 $R_\xi=\xi\cdot\partial_\xi$ 下，

$$
r_\xi=e^{-E/2}[1+B_1l'+(B_1^2/2-2B_2)H_2]+\mathcal R_\xi,
$$

$$
|\partial_y^jR_\xi^a\mathcal R_\xi|
\le C\varepsilon^3(1+|y|^d)(1+E)^d e^{-cE}
+Q^{-100}(1+E)^d e^{-cE},\qquad j\le2.
\tag{116.21}
$$

为验证任意 $E$ 上的一致性，在扭转分母中插入 $1-2itzw_j$，保持 $P$ 不变。
初始系数为
$e^{-E/2}[1-B_1(it)+(B_1^2/2-2B_2)(it)^2+\cdots]$。
逆变换 $(it)^rP$ 为 $(-1)^rp^{(r)}$，故 $B_1l'$ 是正号。
条带内实倒数有统一正下界，第 $J$ 个 $z$ 导数受
$C_J(\varepsilon|t|)^J(1+E)^Je^{-cE}$ 控制，径向导数只加固定多项式。
先作足够高固定阶 Taylor 展开，再用 (116.18) 支付密度除法；
保留的 $r\ge3$ 项为 $\varepsilon^3$ 乘固定导数比，多余余项及截断尾给第二个小量。

现在保留同一噪声扭转 $\eta$，令 $r=e^{-\eta^2/2}r_\xi$。
对于归一化实倾斜 $e^{u(X+G^2/2)}$，其中 $X=(\|Z\|^2-|J|)/2$，
第 113 章精确温度输运在固定物理输出处给

$$
Dr=\mathcal Lr-(y+A_b)r_y,
$$

$$
(D^2+D)r=(\mathcal L^2+\mathcal L)r
-2(y+A_b)\mathcal Lr_y+(y+A_b)^2r_{yy},
\qquad \mathcal L=(R_\xi+R_\eta)/2.
\tag{116.22}
$$

完整变换用 $\tau=1-u$，把 $\xi,\eta$ 除以 $\sqrt\tau$，
把中心偏移向量和 $\sigma$ 乘 $\sqrt\tau$，输出坐标变为
$\tau(y+c)-c$，$c=V/\sqrt\delta$。
这是在固定物理 $y$ 求导时的积分变量变换，$\eta\sigma$ 不变。
二阶导数包含 $[-\ln(1-u)]''_{u=0}=1$，故不能遗漏 $D^2+D$ 中的后项。

写 $h=E+\eta^2$，(116.18)–(116.21) 得

$$
r=e^{-h/2}+O(\varepsilon),\quad
r_y=-e^{-h/2}B_1/\nu_b+O(\varepsilon^2),
$$

$$
r_{yy}=e^{-h/2}\left[B_1k_b/\nu_b^3
+(B_1^2-4B_2)/\nu_b^2\right]+O(\varepsilon^3).
\tag{116.23}
$$

各余项带固定 $y,E,\eta$ 多项式及 $e^{-c(E+\eta^2)}$，另有超多项式小量。
关键密度除法抵消发生在 $l'''$，不能以 $p'''/p$ 替代。
$B_1\le\varepsilon E$、$B_2\le\varepsilon^2E$、$A_b\varepsilon\le C$，
所以两次输运之后余项只剩 $O(\varepsilon)$ 乘上述权重。
保留项中用 $A_b$ 代替 $y+A_b$ 的误差也是 $O(\varepsilon(1+|y|^d))$。
最后用

$$
\mathcal Le^{-h/2}=-\tfrac h2e^{-h/2},\quad
(\mathcal L^2+\mathcal L)e^{-h/2}=(h^2/4-h)e^{-h/2},
\quad\mathcal L(B_1e^{-h/2})=(1-h/2)B_1e^{-h/2},
$$

就逐项得到 (116.12) 的 $P_1,P_2$，包括 $4B_2$、$k_b$ 及完整噪声标记。

**经验中心、外围标记和归一化定位。** 记中心偏移
$a_j=(\mu_j-m_j)/\sqrt{d_j}$。原实际选择估计给

$$
\|wa\|_2\le Ca_x,\quad
\sum_Jw_ja_j^2\le a_x^2V/\sqrt\delta,\quad
V/\sqrt\delta-A_b=\sum_Ew_j,\qquad a_x=O_{\mathbb P}(Q^{-5/2}).
\tag{116.24}
$$

小标准化误差不代表模一误差小；$b_{\ell j}$ 始终使用实际 $\mu_j$。
令 $g_u$ 是大组连续 Gaussian、外围原二项律、原中心与原能量映射在精确中心惊讶倾斜下的归一化输出密度，
噪声方差变为 $\sigma^2/(1-u)$；$g=g_0$。
格点密度 $f_{{\rm lat},u}$ 用自己的精确中心惊讶作同一人工倾斜。
原参数不在倾斜后重新校准。

一个大组模相对中央 $P(t)$ 的精确变换为

$$
\exp\left[it\kappa-\frac12\sum_J
\frac{(\xi_j-2tw_ja_j)^2}{1-2itw_j}
-\frac12(\eta+\sigma t)^2\right],
\qquad\kappa=\sum_Jw_ja_j^2-V/\sqrt\delta+A_b.
\tag{116.25}
$$

单位相位 $z_{\ell k}$ 和物理调制 $e^{-i\pi\ell\mathcal B y}$ 不依赖 $u$。
同一残差出现在 $\eta+\sigma t$，两次实倾斜导数保留原二、四阶噪声标记。
此处 $\sigma\le C_D/\mathcal B$，外围计数 $C_j\le CQ^{3600}$，
外围能量范围至多 $CQ^{7202}/\mathcal B$。
置

$$
\rho_x=\|wa\|_2+\sum_Jw_ja_j^2+|V/\sqrt\delta-A_b|
+\sigma+Q^{7202}/\mathcal B.
\tag{116.26}
$$

则 $\rho_x=O_{\mathbb P}(Q^{-5/2})$，$(1+A_b)^2\rho_x=o_{\mathbb P}(1)$。
在条带 $|t|\le C/\varepsilon$ 对 (116.25) 和中央版本的指数差作实平方配方，
中间指数均受 $Ce^{-c(E+\eta^2)}$ 控制；每个非恒定系数带 $\rho_x$，
线性扭转用 $\|wa\|\sqrt E$ 控制。
同样先作固定高阶展开、再除以 $p\ge Q^{-60}$，包括两次 $y$ 导数和所需径向导数，得到

$$
C\rho_x\operatorname{poly}(y,E,\eta)e^{-c(E+\eta^2)}
+Q^{-100}e^{-c(E+\eta^2)}.
\tag{116.27}
$$

绝对余项取小于 $Q^{-250}$，分母及其导数也使用零扭转展开。
完整温度算子最多付 $(1+A_b)^2$，故前两阶归一化导数误差趋零；不是微分 $C^0$ 误差。

外围先保留联合因子
$\mathbb E_Ee^{us_E+i b_\ell\cdot R_E+itT_E}/\mathbb E_Ee^{us_E}$。
它的前两阶 $u$ 导数有界，只有支付 $CQ^{7202}/\mathcal B$ 的能量误差后，
才把它换成 (116.10) 的三个因子，不能先切断外围惊讶与能量关系。
移动截断的导数支撑在 $|t|\asymp\varepsilon^{-1}$，中央储备给
$e^{-c/\varepsilon^2}$，付清固定多项式输运费用。
实格点归一化 $c_{\rm lat}=1+o(Q^{-N})$ 及其前两阶温度导数误差也对每个固定 $N$ 成立，
因为每项是 $d_j$ 的多项式乘 $e^{-cd_j}$，$d_j\ge Q^{3600}$。
不需要复杂域中的 theta 非零邻域。

若 $U_{\rm lat}=s_{\rm lat}+G^2/2$，$q_h(y)dy=\mathbb E[U_{\rm lat}^h;Y^{\rm lat}\in dy]$，
归一化密度导数精确为

$$
(f_{{\rm lat},u})'_0=q_1-q_0/2,\qquad
(f_{{\rm lat},u})''_0=q_2-q_1-(V_{\rm lat}+1/4)q_0.
\tag{116.28}
$$

归一化矩母函数的一、二阶导数是 $1/2,V_{\rm lat}+3/4$。
所以前述 $O(Q^{-430})$ 定位误差只付多项式费用，除以 $g\ge cQ^{-60}$ 以后仍足够小。
令 $F(u,y)=f_{{\rm lat},u}(y)/g_u(y)$，综合得

$$
\partial_u^jF(0,y)=M_j(\pi\mathcal B y)+e_j(y),\quad j=0,1,2,
$$

$$
|e_j(y)|\le r_Q(1+|y|^d),\quad |y|\le h_Q,
\qquad r_Q=O_{\mathbb P}(\varepsilon+(1+A_b)^2\rho_x)+O(Q^{-50})\to0.
\tag{116.29}
$$

$r_Q$ 乘每个固定 $h_Q$ 幂仍趋零。接下来证明所用的绝对模求和及正分母，而不假设混叠很小。

**正的有限带宽质量与完整商式。** 对固定 $c>0$、整数 $d\ge0$，最近格点估计给

$$
\sum_{k\in\mathbb Z^J}(1+E_{\ell k})^de^{-cE_{\ell k}}\le C.
\tag{116.30}
$$

先把多项式吸收进半个指数，每个坐标 Gaussian 和至多
$1+Ce^{-c'd_j}$；最近格点并列时，两项本身都指数小。
乘积在 $|J|=O(Q^2)$、$d_{\min}\ge Q^{3600}$ 下仍有一致界，不产生 $C^{|J|}$。
(116.9) 使 $P_1,P_2$ 都被固定 $E+\eta^2$ 多项式控制，
例如 $A_bB_1\le CE$、$A_b^2k_bB_1\le CE$。
由 $\eta_\ell^2\ge c_D\ell^2$ 对 $\ell$ 求和，即得级数及任意固定阶周期导数的上界。
$(\ell,k)\mapsto(-\ell,-k)$ 的共轭关系给实值性。

为证严格正下界，对同一个格点元组 $K$ 定义圆周相位

$$
\Theta(K)=\pi\left[\sum_j(1-2\mu_j)K_j+\sum_j\mu_j^2-B^2V\right]
\pmod{2\pi}.
\tag{116.31}
$$

因整数 $K_j^2\equiv K_j\pmod2$，它恰为 $\pi\mathcal BT^{\rm lat}$ 模 $2\pi$。
逐坐标 Poisson 求和给精确恒等式

$$
\mathbb E_{\rm lat}e^{i\ell\Theta}
=c_{\rm lat}\sum_kz_{\ell k}e^{-E_{\ell k}/2}\chi_{\ell,0}.
\tag{116.32}
$$

令 $s_Q=\pi a_Q$，经典 wrapped Gaussian 核为

$$
W_{s_Q}(\theta)=\sum_{\ell\in\mathbb Z}e^{-s_Q^2\ell^2/2}e^{-i\ell\theta}
=\frac{\sqrt{2\pi}}{s_Q}\sum_{n\in\mathbb Z}
e^{-(\theta-2\pi n)^2/(2s_Q^2)}.
\tag{116.33}
$$

其圆周平均为一。选一个距离至多 $\pi$ 的最近 $2\pi n$，得

$$
W_{s_Q}(\theta)\ge\frac{\sqrt{2\pi}}{s_Q}e^{-\pi^2/(2s_Q^2)}>0.
$$

$s_Q$ 留在固定正紧区间，正下界与 Fourier 级数上界均一致。
由 (116.13)、(116.32)，

$$
M_0(\theta)=\mathbb E_{\rm lat}W_{s_Q}(\theta-\Theta(K)).
\tag{116.34}
$$

这证明任意共同经验中心下的 (116.4)。它不声称能量落在一个共同格点上，也不声称相位均匀。
外围组仍属于相位，其他标记级数也保留外围惊讶。

由 (116.29)，$F(0,y)\ge c_D/2$ 在 $|y|\le h_Q$ 最终成立。
用精确商式
$\partial_u^2\ln F=F''/F-(F'/F)^2$，得到

$$
\sup_{|y|\le h_Q}|\partial_u^2\ln F(0,y)-K_x(y)|\to0,
\tag{116.35}
$$

并有误差界 $C_Dr_Q(1+|y|^d)$。这里保留完整条件均值平方，不能逐个删除混叠模。

任意先验的精确中心惊讶 $s$ 与同一个独立 $G$ 满足如下归一化实倾斜恒等式：
用 $e^{u(s+G^2/2)}$ 倾斜原联合律，输出密度为 $f_u$，则

$$
\operatorname{Var}(s+G^2/2\mid Y=y)-\operatorname{Var}s
=1/2+\left.\partial_u^2\ln f_u(y)\right|_{u=0}.
\tag{116.36}
$$

这是归一化联合矩积分的二阶导数，右侧减去的无条件方差是
$\operatorname{Var}s+1/2$。原先验下 Bayes 公式把条件方差识别为后验方差熵，
因为后验惊讶与 $S+G^2/2$ 只差依赖输出的常数。
对格点律与连续大组参考律相减，精确先验方差已由归一化支付，原有限系数点态相消，故

$$
D_{\rm lat}(y)-D_g(y)=\partial_u^2\ln F(0,y).
\tag{116.37}
$$

这将完整非线性差变为 (116.13) 的显式级数及受控余项，而没有用未知密度比定义答案。

**同一输出律下的尾部与实际加权返回。** 适中区间之外必须支付完整 $O(Q^2)$ 惊讶方差。
第 113 章同一格点律的实矩母函数证明在固定 $D$ 仍有效：对
$|t|\le C\sqrt{\ln Q}$，$|2tw_j|=o(1)$；每个格点实平方配方仅改变连续矩母函数一个
$1+O(e^{-cd_j})$ 的归一化比，均值可任意移动。
乘积费用为 $O(|J|e^{-cQ^{3600}})$。
连续指数精确为

$$
-ct-\frac12\sum_J\ln(1-2tw_j)
+\sum_J\frac{tw_ja_j^2}{1-2tw_j}
+\sigma^2t^2/2+\ln\mathbb E_Ee^{tT_E},\qquad c=V/\sqrt\delta.
\tag{116.38}
$$

其线性均值为 $O(a_x^2/\sqrt\delta)+O(Q^{7202}/\mathcal B)$，
二次项为 $\nu_bt^2/2$，余项受
$O(\varepsilon|t|^3+a_x^2t^2+\sigma^2t^2+|t|Q^{7202}/\mathcal B)$ 控制。
非中心方差由 $C\|wa\|^2$ 控制。
在 $t=\pm h_Q/(1.1\nu)$ 作 Chernoff 估计，得

$$
\mathbb P_{\rm lat}(|Y|>h_Q)+\mathbb P_g(|Y|>h_Q)\le CQ^{-40}.
\tag{116.39}
$$

固定 $t$ 同时给所有固定阶输出矩的一致界，这不依赖经验相位衰减。
完整中心目标有 $\|s_{\rm lat}+G^2/2\|_4+\|U_g\|_4\le CQ$，所以

$$
\int_{|y|>h_Q}f_{\rm lat}\operatorname{Var}(U_{\rm lat}\mid y)dy
\le\mathbb E[U_{\rm lat}^2\mathbf1_{\{|Y|>h_Q\}}]
\le CQ^2\mathbb P_{\rm lat}(|Y|>h_Q)^{1/2}=O(Q^{-18}).
\tag{116.40}
$$

参考律同理。先验方差 $O(Q^2)$、$A^2/\Lambda=O(Q^{1/2})$、$C_x=O(Q^{1/4})$ 的尾款，
以及二次 $R_*$，均由 (116.39) 和输出矩支付。
$K_x$ 全局有界，其尾款直接趋零。没有在尾部除以很小的密度。

连续大组参考仍满足

$$
\int g(y)|D_g(y)-R_*(y)|dy\to0.
\tag{116.41}
$$

具体映射保持第 113 章已支付的范围：第 101 章 Gaussian 参考结论没有噪声下界，
旧指数限制属于实际量化耦合，此处不用那个耦合。
先在同一外围元组和 $G$ 下删除相关外围能量，用 (101.19) 的未加权联合核心密度导数界
$\int|\partial_t p_H|\le C\delta^{-1/2}$ 及 $V_{\rm out}\le Q^{-200}$，给联合变差 $O(Q^{-199.5})$。
再用 (101.8) 的四阶截断不等式、完整目标范数 $CQ$ 和截断水平 $Q^{10}$ 支付无界方差密度差。
之后外围惊讶才与核心输出独立，其先验方差才相消。
接着 (101.22)、(101.23) 的非中心核心比较费用
$O(Q^{-1/4}[1+(\ln Q)^{3/4}])=o(1)$。
完整截距直到比较付款后才处理，原 $A,\Lambda,C_x$ 的费用仍保留。

适中区间上，(116.4)、(116.29) 给 $f_{\rm lat}\le C_Dg$。
结合 (116.35)、(116.37)、(116.41) 和已付尾部，

$$
\int f_{\rm lat}|D_{\rm lat}-R_*-K_x|\to0.
\tag{116.42}
$$

不需要 $f_{\rm lat}/g\to1$。最后用 (116.16)、$R_*$ 二次且 $K_x$ 有界，

$$
\begin{aligned}
\int f_x|D_x-R_*-K_x|
\le{}&\|f_xD_x-f_{\rm lat}D_{\rm lat}\|_1
+\int f_{\rm lat}|D_{\rm lat}-R_*-K_x|\\
&+\int|f_x-f_{\rm lat}|(|R_*|+|K_x|)\longrightarrow0.
\end{aligned}
\tag{116.43}
$$

这证明 (116.6)。所有估计在同一实际好环境上成立，先限制紧常数再放开，得到原支持一致的 pair/path 概率结论。

**周期平均给出必要充分边界。** 由 (116.6)，无修正误差与 $\int f_x|K_x|$ 之差趋零。
$K_x$ 有界，(116.16) 可将此积分换到格点律；再用质量展开 (116.29) 和尾界，

$$
\int f_{\rm lat}|K_x|
=\int g(y)F_x(\pi\mathcal B y)dy+o_{\mathbb P}(1),
\qquad
F_x(\theta)=M_0(\theta)|\mathcal K_x(\theta)|
=\left|M_2(\theta)-\frac{M_1(\theta)^2}{M_0(\theta)}\right|.
\tag{116.44}
$$

周期函数 $F_x$ 随数据和 $Q$ 变化，但仍一致有界。
参考密度有 $\|g'\|_1\le C$：中央变换 $P$ 的对数导数为 $O(|t|)$，
因为中心化消去了 $\sum w_j$，而 $\sum w_j^2$ 有界。
中央储备界使 $tP$ 和 $(tP)'$ 一致平方可积，Plancherel 再配
$(1+y^2)^{-1}$ 的 Cauchy–Schwarz 给 $\|p'\|_1\le C$。
完整非中心指数及其导数用 $\|wa\|$、$\sum wa^2$ 得到同样的界，
外围特征函数及其导数只加已控制的能量范围，Gaussian 噪声不恶化衰减，
完整截距保留，故此界也适用于 $g$。没有使用逆噪声的导数估计。

任意有界 $2\pi$ 周期函数 $F$ 的均值为 $\bar F$。
$F-\bar F$ 有周期原函数 $H$，满足 $\|H\|_\infty\le4\pi\|F\|_\infty$。
对绝对连续密度 $g$ 分部积分得

$$
\left|\int g(y)F(\pi\mathcal B y)dy-\bar F\right|
\le\frac{\|g'\|_1\|H\|_\infty}{\pi\mathcal B}.
\tag{116.45}
$$

可积的 $W^{1,1}$ 密度在两端趋零，边界项消失。
该界对当前数据依赖的 $F_x$ 一致，代入 (116.44) 证明 (116.7)。
只是积分误差化成周期平均，物理输出上的快速振荡没有被声称点态趋于常数。

还有一个单向反驳判据。$M_2$ 的零阶 Fourier 系数对每个固定 $N$ 为 $o(Q^{-N})$：
$\ell=0$ 时 $\chi_{0,1}=\chi_{0,2}=0$，$k=0$ 时 $P_2=0$，其余 $k$ 具有指数大的对偶能量。
所以由实值性和正分母，

$$
\mathfrak J_x\ge\frac1{2\pi}\int_0^{2\pi}\frac{M_1(\theta)^2}{M_0(\theta)}d\theta-o(1).
\tag{116.46}
$$

若能在实际数据的非消失概率事件上证明右积分有正下界，就能反驳固定间隙原目标。
本章没有建立这样的事件，不用人为整数中心实例冒充实际反例。

**命题 116.2（实际经验数组上的充分算术条件）。** 如果对每个固定非零整数 $\ell$，

$$
E^{\min}_{\ell,x}:=\min_kE_{\ell k}
=4\pi^2\sum_{j\in J}d_j\operatorname{dist}
\bigl(\ell(1/2-\mu_j),\mathbb Z\bigr)^2\longrightarrow\infty
\tag{116.47}
$$

在原支持一致实际数据概率下成立，那么 $\mathfrak J_x\to0$，从而原无修正的固定间隙加权极限成立。
证明对固定多项式标记有

$$
\sum_k(1+E_{\ell k})^de^{-cE_{\ell k}}
\le C_de^{-c'E^{\min}_{\ell,x}}.
\tag{116.48}
$$

用 $E_{\ell k}\ge E^{\min}_{\ell,x}$ 提出半个指数，余下按 (116.30) 求和即可。
条件 (116.47) 使每个固定非零谐波及前两阶标记趋零；
$\eta_\ell^2\ge c_D\ell^2$ 给统一可和的剩余谐波尾。
先截断 $\ell$、对有限多个实际概率界作并集，再放开截断，得到
$M_0\to1$、$M_1,M_2\to0$ 一致于 $\theta$，代入 (116.7) 即证。

这是实际模型内的条件蕴含，尚未证明其前提。
它是充分条件，不必是完整商式抵消的必要条件；必要充分条件仍为 (116.7)。
一个坐标接近整数不足以决定共同加权能量，边缘扭转均值也不替代同一环境的 (116.47)。

**未解决的共同经验中心问题。** 原第 68 章的完整选择中心有精确表达式，
对固定观测和 $c=q/(M-q)$，

$$
L_i(t)=\left(\frac{1+t}{1-ct}\right)^{k_i}
\left(\frac{1-t}{1+ct}\right)^{l_i},
\qquad
\pi_i(t)=\frac{L_i(t)e_{q-1}(L_l(t):l\ne i)}{e_q(L_l(t):l\in C_+)},
\qquad \mu_j(t)=\sum_{i\in J_j}\pi_i(t).
\tag{116.49}
$$

全部坐标共享初等对称多项式分母。pair/path 在原对齐后都使用这个似然，
平稳 path 的初始律与支持无关。
这里的人工 $t$ 与前述温度 $u$ 不同，二者都没有改变实际观测或组定义。

第 68 章利用固定超越幅度 $r$ 及各有理函数在 $t=-1$ 的不同正消失阶，
证明实际好事件上 $1$ 和所有占据组 $\mu_j(r)$ 有理独立。
该证明不需要维数一致的首项系数界，因此只排除有限规模的精确对偶等式，
不控制 $d_j^{-1/2}$ 尺度上的近似距离。
每个 $E^{\min}_{\ell,x}>0$ 不推出它发散。

原一、二行相对 Poisson 关系给同时占据好事件和方差剖面，但不是后验中心的独立性。
(116.49) 通过共同分母依赖完整环境。
选择比较也不允许在扭转中把 $\mu_j$ 换成 $m_j$：
$|\mu_j-m_j|\le a_x\sqrt{d_j}$ 在模一单位上可以很大，而对偶坐标还要再乘 $\sqrt{d_j}$。
仍需证明实际 $\mathfrak J_x\to0$，或给出非消失概率的反例；
(116.47) 提供一条充分路线，完整商式也可能以更弱条件抵消。
本章把正分母、完整惊讶与噪声标记、全输出尾部和周期判据具体化，不冒领剩余算术概率结论。

Poisson 求和、实 Gaussian 归一化、wrapped 热核和条件累积量恒等式均属经典。
本章不声称噪声阈值尖锐、无条件相位均匀、一般模一反集中定理、形式核验或全局原创。

## 追加锚（第 116 章后续增补区）

## 117. 在一阶处锚定差商，把经验响应闭合到 Shannon 端点

**定理 117.1（闭区间上的完整经验响应）。** 保持第 114、115 章的原完整计数模型、
固定合法参数、所有取整、实际经验中心和同一带噪标量。令

$$
\delta=Q^{-1/2},\qquad L=\log(1/\sigma)\longrightarrow\infty,
\qquad \limsup\frac{L}{Q^3}<\frac{c_q}{2},
\qquad c_q=\frac{\phi(1-\beta)}{\beta}.
\tag{117.1}
$$

在同一个实际数据纤维 $x$ 上，精确定义

$$
\mathcal B^2=\frac q{Q^{5/2}},\quad
v_j=\frac{C_jp_j(1-p_j)}{\mathcal B^2},\quad
V=\sum_jv_j,\quad v_* =\max_jv_j,\quad
e_j=\frac{\mu_j-C_jp_j}{\mathcal B},
$$

$$
E(n)=\sum_j\left(\frac{n_j-\mu_j}{\mathcal B}\right)^2,
\qquad T_x(n)=\frac{E(n)-V}{\sqrt\delta}.
\tag{117.2}
$$

全部求和仍取原完整组窗；空组的 $v_j=e_j=0$。
以下系数在下述概率趋一的共同好事件上使用，补集上的任意固定可测延拓不影响概率结论。
$P_x$ 是加入标量前的原计数后验，$P_x^y$ 是观察 $T_x+\sigma G=y$ 后的精确后验。
对有限 $\alpha\ge1$，令

$$
K_\alpha(t)=-\frac12\sum_j\log\left(1-\frac{2tv_j}{\alpha}\right)
 +\sum_j\frac{te_j^2}{1-2tv_j/\alpha}
 +\frac{\delta\sigma^2t^2}{2\alpha},
\qquad t<\frac{\alpha}{2v_*}.
\tag{117.3}
$$

以唯一的实根 $K'_\alpha(t_\alpha)=V$ 定义

$$
W_\alpha=K''_\alpha(t_\alpha),\qquad
b_\alpha=\frac{\sqrt\delta\,t_\alpha}{\alpha},\qquad
c_\alpha=\frac{\delta}{2\alpha W_\alpha}.
\tag{117.4}
$$

此处允许 $t_1\le0$。在无穷阶取
$b_\infty=\sqrt\delta/(2v_*)$、$c_\infty=0$，并令

$$
\begin{aligned}
\mathcal R_\alpha(y)
 &=\frac{\alpha}{\alpha-1}
       \bigl[(b_\alpha-b_1)y+(c_\alpha-c_1)y^2\bigr],
       &&1<\alpha<\infty,\\
\mathcal R_1(y)&=b'_1y+c'_1y^2,\\
\mathcal R_\infty(y)&=(b_\infty-b_1)y-c_1y^2.
\end{aligned}
\tag{117.5}
$$

撇号在固定实际数据、$\mu,V,\sigma$、所有计数与组集合后对 $\alpha$ 求导。
对每个固定 $R<\infty$，分别在原 pair、path 实验下，

$$
\sup_{\alpha\in[1,\infty],\ |y|\le R}
 \left|H_\alpha(P_x^y)-H_\alpha(P_x^0)-\mathcal R_\alpha(y)\right|
 \xrightarrow{\mathbb P}0.
\tag{117.6}
$$

熵单位为 nats，$H_1$ 为 Shannon 熵，$H_\infty$ 为最大原子质量的负对数。
概率结论对每个确定大小为 $q$ 的支撑一致：对任意 $\eta>0$，取所有该类支撑的
实际数据概率上确界，式 (117.6) 左侧超过 $\eta$ 的概率趋于零。
所有阶数和输出共享同一数据纤维。

**实际输入与选择修正。** 第 69、70、114、115 章在共同实际好事件上给出

$$
m_Q:=\#\{j:C_j>0\}\le CQ^2=C\delta^{-4},\quad
\log q=c_qQ^3+O(1),\quad N_J:=\sum_jC_j\le C\mathcal B^2,
$$

$$
V\to\gamma>0,\qquad \frac{v_*}{\delta}\to\rho_0>0,
\qquad \frac1\delta\sum_jv_j^2\to\frac\nu2,
\qquad \max_j|p_j-1/2|=O_{\mathbb P}(q^{-1/2}).
\tag{117.7}
$$

存在含 $c/\delta$ 个坐标的原核心块，其上 $v_j\asymp\delta$。
沿用原 Gaussian 轮廓 $\rho(s)=\rho_0e^{-\kappa s^2/2}$、
$\gamma=\int\rho$、$\nu=2\int\rho^2$。还须使用第 69 章的逐坐标中心界，不能只用总范数：

$$
\|e\|_2\le C\sqrt V\,e_M,\qquad
|e_j|\le C\sqrt{v_j}\,e_M,\qquad
e_M=O_{\mathbb P}(\delta^5+q^{-1/2}).
\tag{117.8}
$$

记 $Q_x=\bigotimes_j\operatorname{Bin}(C_j,p_j)$。原完整固定 $q$ 后验在整个可行计数盒上满足

$$
P_x(n)=e^{\ell(n)}Q_x(n),\qquad
-C\left(\frac{D(n)^2}{q}+q^{-1/2}\right)
 \le\ell(n)\le C\left(\frac{\mathcal B^2V}{q}+q^{-1/2}\right),
$$

$$
D(n)=\sum_j(n_j-C_jp_j),\qquad \mathcal D(n)=D(n)/\mathcal B.
\tag{117.9}
$$

因 $\mathcal B^2/q=\delta^5$，在固定紧性常数的好事件上，

$$
|\ell(n)|\le C\delta^5(1+\mathcal D(n)^2),
\qquad \ell(n)\le C\delta^5.
\tag{117.10}
$$

保留同一个标量总偏差 $\mathcal D$，是后面求导仍能支付维数成本的关键。
所有以下确定性界在上述共同事件上一致；最后穷尽紧性常数恢复实际概率量词。
辅助乘积坐标不改变实际 path 行的依赖关系。

**实根与一阶锚。** 写 $D_j(t)=1-2tv_j/\alpha$，则

$$
\begin{aligned}
K'_\alpha(t)&=\sum_j\frac{v_j}{\alpha D_j}
 +\sum_j\frac{e_j^2}{D_j^2}+\frac{\delta\sigma^2t}{\alpha},\\
K''_\alpha(t)&=2\sum_j\frac{v_j^2}{\alpha^2D_j^2}
 +4\sum_j\frac{v_je_j^2}{\alpha D_j^3}
 +\frac{\delta\sigma^2}{\alpha}>0.
\end{aligned}
\tag{117.11}
$$

由于每个有限规模的 $\sigma>0$，$K'$ 在左端趋于负无穷，在最大方差的右极点趋于正无穷，
故实根存在且唯一。这个变换精确对应
$\sum_j(\sqrt{v_j/\alpha}Z_j-e_j)^2+\sqrt{\delta\sigma^2/\alpha}G$。
在 $\alpha=1$，$K'_1(0)=V+\|e\|^2$；在一个固定小负区间内 $K''_1\ge c\delta$，
从而根的夹逼给

$$
|t_1|\le C\frac{\|e\|^2}{\delta}=O_{\mathbb P}(\delta^9),\quad
b_1=O_{\mathbb P}(\delta^{19/2}),\quad
W_1=2\sum_jv_j^2+\delta\sigma^2+O_{\mathbb P}(\delta^{11}),\quad
c_1\to\frac1{2\nu}.
\tag{117.12}
$$

若 $e=0$，则 $t_1=0$ 精确成立。隐函数定理给有限系数的光滑性。
为明确式 (117.5) 中的导数，以下偏导均在 $(\alpha,t_\alpha)$ 处取值：

$$
t'_\alpha=-\frac{K_{t\alpha}}{W_\alpha},\qquad
W'_\alpha=K_{tt\alpha}+K_{ttt}t'_\alpha,
$$

$$
b'_1=\sqrt\delta(t'_1-t_1),\qquad
c'_1=-\frac{\delta}{2W_1}
-\frac{\delta}{2W_1^2}(K_{tt\alpha}+K_{ttt}t'_1)\big|_{\alpha=1}.
\tag{117.13}
$$

其中有限和可直接求导为

$$
\begin{aligned}
K_{t\alpha}&=-\sum_j\frac{v_j}{\alpha^2D_j^2}
-4t\sum_j\frac{v_je_j^2}{\alpha^2D_j^3}
-\frac{\delta\sigma^2t}{\alpha^2},\\
K_{ttt}&=8\sum_j\frac{v_j^3}{\alpha^3D_j^3}
+24\sum_j\frac{v_j^2e_j^2}{\alpha^2D_j^4},\\
K_{tt\alpha}&=-4\sum_j\frac{v_j^2}{\alpha^3D_j^3}
-4\sum_j\frac{v_je_j^2}{\alpha^2D_j^3}
-24t\sum_j\frac{v_j^2e_j^2}{\alpha^3D_j^4}
-\frac{\delta\sigma^2}{\alpha^2}.
\end{aligned}
\tag{117.14}
$$

不在可能发散的线性项中以连续轮廓极限替代这些有限系数。

**包含负根的紧阶数几何。** 暂取 $\alpha\in[1,2]$，令
$s_\alpha=2v_*t_\alpha/\alpha$、$r_j=v_j/v_*$。根方程变为

$$
\frac{F(s_\alpha)}\alpha+C(s_\alpha)
+\frac{\delta\sigma^2s_\alpha}{2v_*}=V,
\quad F(s)=\sum_j\frac{v_j}{1-sr_j},\quad
C(s)=\sum_j\frac{e_j^2}{(1-sr_j)^2}.
\tag{117.15}
$$

原核心轮廓在 $s\uparrow1$ 时给 $F(s)\ge c/\sqrt{1-s}$。
故存在固定 $s_+<1$，使所有根满足
$-C\|e\|^2\le s_\alpha\le s_+$，因而 $c\le D_j\le C$。
直接求导得到

$$
s'_\alpha=
\frac{F(s_\alpha)/\alpha^2}
{F'(s_\alpha)/\alpha+C'(s_\alpha)+\delta\sigma^2/(2v_*)}>0.
\tag{117.16}
$$

分母由 $\sum v_j^2/v_*$ 一致下界控制，所需固定阶导数一致有界。
完整倾斜坐标的方差与均值为
$w_j=v_j/(\alpha D_j)$、$m_j=-e_j/D_j$，满足
$w_j\asymp v_j$、$|w'_j|\le Cw_j$、$|m'_j|\le C|m_j|$，
且 $W_\alpha\asymp\delta$、$|W'_\alpha|\le C\delta$。
这些界不要求 $\sigma$ 的额外下界或衰减速度。

取 $l<c_q/2$ 使最终 $L\le lQ^3$，再取
$0<\zeta$ 使 $2\zeta<c_q-l$，以 $H=\{j:C_j\ge e^{\zeta Q^3}\}$ 作为证明分组。
低组满足

$$
\sum_{j\notin H}v_j\le\operatorname{poly}(Q)e^{-(c_q-\zeta)Q^3},\qquad
\sum_{j\notin H}e_j^2\le\operatorname{poly}(Q)e^{-(c_q-2\zeta)Q^3}.
\tag{117.17}
$$

令 $K_H$ 只删除低组坐标项，保留完整噪声项。仍在完整根 $t_\alpha$ 处取
$\varepsilon_H=V-K'_H(t_\alpha)$、$W_H=K''_H(t_\alpha)$。
它们与完整均值、方差的差及其全 $\alpha$ 导数均为多项式乘指数小量：
由 $|t'_\alpha|\le C/\delta$、$D_j\ge c$ 逐项求导，每个删除项仍带
$v_j$ 或 $e_j^2$。所以 $W_H\asymp\delta$、$|W'_H|\le C\delta$。
完整有限系数 (117.3)–(117.4) 从未删组。

**引理 117.2（倾斜密度比的阶数导数）。** 将高组倾斜能量加原倾斜噪声中心化、方差标准化，得

$$
Z_\alpha=\sum_{j\in H}a_j(Z_j^2-1)
+\sum_{j\in H}\beta_jZ_j+\beta_GG,
\quad a_j=\frac{w_j}{\sqrt{W_H}},\quad
\beta_j=\frac{2m_j\sqrt{w_j}}{\sqrt{W_H}},\quad
\beta_G=\frac{\sqrt{\delta\sigma^2/\alpha}}{\sqrt{W_H}}.
\tag{117.18}
$$

其方差精确为一，$\max a_j\le C\sqrt\delta$，
$|a'_j|\le Ca_j$、$|\beta'_j|\le C|\beta_j|$、$|\beta'_G|\le C|\beta_G|$。
零系数处相应导数也为零；核心块有 $N\asymp1/\delta$ 项满足 $a_j^2\asymp\delta$。
精确特征函数为

$$
\psi_\alpha(\xi)=e^{-\beta_G^2\xi^2/2}
\prod_{j\in H}e^{-i\xi a_j}(1-2i\xi a_j)^{-1/2}
\exp\left(-\frac{\beta_j^2\xi^2}{2(1-2i\xi a_j)}\right).
\tag{117.19}
$$

非中心及噪声因子的模不超过一，故

$$
|\psi_\alpha(\xi)|\le(1+c\delta\xi^2)^{-c'/\delta},\qquad
|\partial_\alpha\psi_\alpha(\xi)|\le C\xi^2|\psi_\alpha(\xi)|.
\tag{117.20}
$$

第二式来自实际求导：中心因子的对数导数至多为 $2\xi^2|a_ja'_j|$；
非中心因子利用 $|1-2i\xi a_j|\ge1$ 和
$|\xi a_j|/|1-2i\xi a_j|\le1/2$，至多贡献 $C\xi^2\beta_j^2$。
将平方系数求和即得该界。
第一式乘任意固定次 $|\xi|$ 的积分一致有界且尾部一致消失：
在 $|\xi|\le\delta^{-1/2}$ 用 $e^{-c''\xi^2}$，在外侧令
$u=\sqrt\delta|\xi|$ 后积分高次幂。

在每个固定频率紧集上直接展开并求导式 (117.19)，

$$
\log\psi_\alpha(\xi)=-\xi^2/2+O(\sqrt\delta|\xi|^3),\qquad
\partial_\alpha\log\psi_\alpha(\xi)=O(\sqrt\delta|\xi|^3).
\tag{117.21}
$$

二次项导数为零源于每个 $\alpha$ 的精确方差标准化。
Fourier 反演与 (117.20) 给密度 $q_\alpha$ 的联合结论

$$
\sup_{\alpha\in[1,2],\ z\in\mathbb R}
\left(|q_\alpha(z)-\varphi(z)|
+|\partial_zq_\alpha(z)-\varphi'(z)|
+|\partial_\alpha q_\alpha(z)|\right)\longrightarrow0.
\tag{117.22}
$$

物理输出的位置 $z_y=(\sqrt\delta y+\varepsilon_H)/\sqrt{W_H}$
及其 $\alpha$ 导数在 $|y|\le R$ 上一致有界。
在该紧集上正态密度有正下界，因此链式法则给
$\log[q_\alpha(z_y)/q_\alpha(z_0)]=-(z_y^2-z_0^2)/2+o(1)$，
且余项的 $\alpha$ 导数也为 $o(1)$。
高组 Gaussian 标量密度 $g_\alpha$ 的精确反倾斜公式是

$$
g_\alpha(y)=\frac{\sqrt\delta}{\sqrt{W_H}}
e^{K_H(t_\alpha)-t_\alpha(V+\sqrt\delta y)}q_\alpha(z_y).
$$

在 $y$ 与零处相除，公共前因子与速率项抵消，得到

$$
D^G_\alpha(y):=-\frac1\alpha\log\frac{g_\alpha(y)}{g_\alpha(0)}
=b_\alpha y+c_\alpha y^2+r^G_\alpha(y),\qquad
\sup_{\alpha\in[1,2],|y|\le R}
(|r^G_\alpha|+|\partial_\alpha r^G_\alpha|)\to0.
\tag{117.23}
$$

式 (117.17) 支付高组与完整系数及其导数之差；没有丢弃前因子或高阶累积量的导数。

**同一稀有输出下的联合矩。** 令倾斜前
$X_j=\sqrt{v_j/\alpha}Z_j-e_j$，并定义

$$
\mathcal D_G=\sum_{j\in H}(X_j+e_j),\quad
S_G=\frac12\sum_{j\in H}\frac{(X_j+e_j)^2}{v_j},\quad
U_y=\frac{\sum_{j\in H}X_j^2-V-\sqrt\delta y}{\sqrt\delta\,\sigma}.
$$

对权重 $e^{-\alpha U_y^2/2}$ 条件化后的同一律，每个固定正整数 $k$ 满足

$$
\mathbb E_{\alpha,y}|\mathcal D_G|^{2k}\le C_k,\qquad
\mathbb E_{\alpha,y}S_G^k\le C_k(1+m_Q)^k,\qquad
\mathbb E_{\alpha,y}|U_y|^{2k}\le C_k\delta^{-k}.
\tag{117.24}
$$

证明把条件事件写成高组能量加独立能量噪声等于 $V+\sqrt\delta y$。
在完整鞍点做指数倾斜不改变该条件律，其密度分母由 (117.22) 下界为 $c/\sqrt{W_H}$。
在 Fourier 积分中插入所需多项式；频率 $\xi/\sqrt{W_H}$ 下每个坐标的复协方差、复均值分别为
$w_j/(1-2i\xi w_j/\sqrt{W_H})$、$m_j/(1-2i\xi w_j/\sqrt{W_H})$。
它们的模不超过 $w_j,|m_j|$。总偏差的协方差和有界，而复均值之和至多
$C\sqrt{m_Q}\|e\|=O(\delta^3)$。
Gaussian 多项式矩公式遂将总偏差插入界为常数乘 (117.20) 的包络。

对 $S_G$，由逐坐标的 $w_j/v_j\le C$ 与 $e_j^2/v_j\le Ce_M^2$，
展开固定次幂并用同一矩公式得到 $C_k(1+m_Q)^k$ 倍包络，覆盖很小的正方差组。
倾斜能量噪声的均值为 $t_\alpha\delta\sigma^2/\alpha$，方差为 $\delta\sigma^2/\alpha$。
除以 $\sqrt\delta\sigma$ 后，复均值模至多
$C(\sigma/\sqrt\delta+|\xi|\sigma)$，复方差模为 $1/\alpha$。
其插入至多为 $C_k\delta^{-k}(1+|\xi|^{2k})$ 倍包络。
积分再除以上述分母即证 (117.24)；混合矩用较高固定阶矩与 Cauchy–Schwarz。
这一步保留了慢衰减噪声的均值位移。

若 $\sigma'^2/\sigma^2=1+u$ 且 $|u|$ 为多项式乘指数小量，在同一个 $t_\alpha$ 处，
$K_H,K'_H,K''_H$ 的变化分别为
$\delta(\sigma'^2-\sigma^2)t_\alpha^2/(2\alpha)$、
$\delta(\sigma'^2-\sigma^2)t_\alpha/\alpha$、
$\delta(\sigma'^2-\sigma^2)/\alpha$。
它们均为多项式乘 $|u|$，故标准化位置仍在紧集，矩界仍成立，
且相邻噪声密度比有固定正的上下界。以下利用这一带插入的比较，不对噪声夹逼直接求导。

**引理 117.3（原计数与完整选择的可微回接）。** 对二项计数质量 $q_j(n)$ 取非负模态惊讶

$$
S_j(n)=-\log\frac{q_j(n)}{\max_kq_j(k)},\qquad S_Q=\sum_jS_j.
\tag{117.25}
$$

这里包含二项系数。若 $p\in[1/4,3/4]$、$N\ge1$，
$z=(n-Np)/\sqrt{Np(1-p)}$，则
$cz^2-C\le S_j(n)\le C(1+z^2)$。
在 $n/N\in[1/8,7/8]$ 内，Stirling 双边界和二元相对熵的二次界给该结论，模态前因子比有界；
在外侧 $z^2\ge cN$，熵成本与对数前因子可一并控制，有限小 $N$ 吸入常数。
由此，$\sum_ne^{-\alpha S_j(n)}\asymp\sqrt{N+1}$，且

$$
\mathbb E_{Q_{\alpha,j}}S_j^k\le C_k,\qquad
\mathbb E_{Q_{\alpha,\mathrm{low}}}S_{\mathrm{low}}^k\le C_k(1+m_Q)^k,
\qquad 1\le\alpha\le2.
\tag{117.26}
$$

下界只需模态附近 $\sqrt N$ 个格点；空组贡献零。低组无须 Gaussian 化。
在高组中心盒 $|n_j-C_jp_j|/\sqrt{C_jp_j(1-p_j)}\le Q^2$ 上，
Stirling 的三次余项与模态减除给

$$
|S_{\mathrm{high}}(n)-S_G(X)|\le\operatorname{poly}(Q)e^{-\zeta Q^3/2},
\qquad X_j=(n_j-\mu_j)/\mathcal B.
\tag{117.27}
$$

逐项余量为 $C(1+Q^6)/\sqrt{C_j}$；对 $m_Q\le CQ^2$ 项求和即可。
模态距 $C_jp_j$ 有界，其势能常数及格元内的势能变化也服从该指数界。
把高组 Gaussian 坐标舍入，并接上任意原低组元组，物理标量变化至多

$$
\Delta_Q\le\operatorname{poly}(Q)
 [\mathcal B^{-1}+\mathcal B^{-2}e^{2\zeta Q^3}],\qquad
\eta_Q:=\Delta_Q/\sigma\le\operatorname{poly}(Q)e^{-bQ^3}
\tag{117.28}
$$

其中 $b>0$，来自 (117.1) 与 $2\zeta<c_q-l$。
令 $\lambda_y(n)=(T_x(n)-y)^2/(2\sigma^2)$、
$u=(T_G-y)/\sigma$、$d=(T_x-T_G)/\sigma$，则

$$
|\lambda_y-u^2/2|\le\eta_Q|u|+\eta_Q^2/2,
\qquad
\left|e^{-\alpha[(u+d)^2-u^2]/2}-1\right|
\le C\eta_Q(1+|u|)e^{C\eta_Q|u|}.
\tag{117.29}
$$

由 $C\eta_Q|u|\le\eta_Qu^2+C^2\eta_Q/4$，额外指数由刚证明的相邻噪声比较支付。
考虑未归一化配分函数

$$
J_Q(\alpha,y)=\sum_ne^{-\alpha(S_Q(n)+\lambda_y(n))},\quad
J_G(\alpha,y)=\int e^{-\alpha(S_G(X)+(T_G(X)-y)^2/(2\sigma^2))}\,dX,
$$

$$
Z_{\mathrm{low}}(\alpha)=\sum_{n_{\mathrm{low}}}e^{-\alpha S_{\mathrm{low}}}.
\tag{117.30}
$$

式 (117.24)、(117.26)–(117.29) 比较 $J_Q$ 与
$\mathcal B^{|H|}Z_{\mathrm{low}}J_G$。
误差及插入一次 $S_Q+\lambda_y$ 或 $S_G+u^2/2$ 后的误差，都不超过后者乘
$\operatorname{poly}(Q)e^{-b'Q^3}$：高组势能误差用 (117.27)，核误差及其势能插入用 (117.29)，
混合多项式用同一条件律的矩界。低组归一化因子的导数由其惊讶矩支付。
这是对实际导数求和项的估计。

中心盒之外的幂律二项尾部及 Gaussian 尾部至多为
$\operatorname{poly}(Q)e^{-cQ^4}$。原计数盒上
$S_Q\le CN_J$、$|\mathcal D|\le C\mathcal B$，最大似然惊讶至多为
$e^{CQ^3+2L}$；固定次插入仍只有 $Q^3+L$ 级指数成本。
Gaussian 尾部的固定次似然插入至多另付 $\sigma^{-2k}$。
由精确反倾斜和紧集正密度下界，归一化后的 Gaussian 核积分至少为
$c\sigma e^{-C/\delta}$。除以稀有输出分母仍不抵消 $Q^4$ 尾指数。
所以整个配分函数满足

$$
A_Q(\alpha,y):=\log\frac{J_Q(\alpha,y)}
{\mathcal B^{|H|}Z_{\mathrm{low}}(\alpha)J_G(\alpha,y)},\qquad
\sup_{\alpha\in[1,2],|y|\le R}
(|A_Q|+|\partial_\alpha A_Q|)\to0.
\tag{117.31}
$$

在 $y$ 与零相除时，模态常数、格体积、低组及 Gaussian 归一化、噪声前因子精确抵消。
因此，定义幂律 $Q_\alpha(n)\propto Q_x(n)^\alpha$ 后，

$$
D^Q_\alpha(y):=-\frac1\alpha
\log\frac{f_{Q_\alpha,\sigma/\sqrt\alpha}(y)}{f_{Q_\alpha,\sigma/\sqrt\alpha}(0)}
=D^G_\alpha(y)+r^{QG}_\alpha(y),\qquad
\|r^{QG}\|_{C^1_\alpha,\infty}\to0.
\tag{117.32}
$$

同一格元比较也可插入总偏差和惊讶，得到原乘积计数幂律在同一输出下的矩界

$$
\mathbb E_{Q_\alpha,y}|\mathcal D|^{2k}\le C_k,\quad
\mathbb E_{Q_\alpha,y}S_Q^k\le C_k(1+m_Q)^k,\quad
\mathbb E_{Q_\alpha,y}\lambda_y^k\le C_k\delta^{-k}.
\tag{117.33}
$$

总偏差的舍入与低组误差至多为
$m_Q/(2\mathcal B)+m_Qe^{\zeta Q^3}/\mathcal B$，指数小；
其余插入分别用 (117.27)、(117.26)、(117.29) 和已支付的尾部。

最后回到原 $P_x$。在同一个 $Q_\alpha$ 输出条件律下令
$Z(\alpha,y)=\mathbb E_{Q_\alpha,y}e^{\alpha\ell}$、$A_y=-(S_Q+\lambda_y)$。
精确有限和求导给

$$
\partial_\alpha\log Z
=\frac{\mathbb E(\ell e^{\alpha\ell})
+\operatorname{Cov}(e^{\alpha\ell},A_y)}{\mathbb E e^{\alpha\ell}}.
\tag{117.34}
$$

由 (117.10)，$|e^{\alpha\ell}-1|+|\ell|e^{\alpha\ell}
\le C\delta^5(1+\mathcal D^2)$，分母最终至少为 $1/2$。
用 (117.33) 的同一条件矩与 Cauchy–Schwarz，

$$
\mathbb E[(1+\mathcal D^2)(S_Q+\lambda_y)]
\le C(1+m_Q+\delta^{-1}),
$$

$$
|\log Z|\le C\delta^5,\qquad
|\partial_\alpha\log Z|
\le C\delta^5(1+m_Q+\delta^{-1})=O(\delta).
\tag{117.35}
$$

协方差第一变量可减去一，故该估计确实支付选择惊讶与似然惊讶的联合项。
对 $P_\alpha\propto P_x^\alpha$，两个输出密度比之比精确为
$Z(\alpha,y)/Z(\alpha,0)$，未条件化的幂律归一化相消。
结合 (117.23)、(117.32)、(117.35)，得到实际模型的可微桥梁

$$
D^P_\alpha(y):=-\frac1\alpha
\log\frac{f_{P_\alpha,\sigma/\sqrt\alpha}(y)}{f_{P_\alpha,\sigma/\sqrt\alpha}(0)}
=b_\alpha y+c_\alpha y^2+r_\alpha(y),\qquad
\sup_{\alpha\in[1,2],|y|\le R}(|r_\alpha|+|\partial_\alpha r_\alpha|)\to0.
\tag{117.36}
$$

**完成闭区间。** 对任意有限正计数律，Gaussian 似然的有限和代数给

$$
H_\alpha(P_x^y)-H_\alpha(P_x^0)
=\frac{\alpha}{\alpha-1}[D^P_\alpha(y)-D^P_1(y)],\quad\alpha>1,
$$

$$
H_1(P_x^y)-H_1(P_x^0)=\partial_\alpha D^P_\alpha(y)\big|_{\alpha=1}.
\tag{117.37}
$$

先消去原幂律归一化与原熵，再近似；$\alpha=1$ 的恒等式只涉及有限和求导。
把 (117.36) 代入，对于 $1<\alpha\le2$，余项为

$$
\frac{\alpha}{\alpha-1}[r_\alpha(y)-r_1(y)]
=\frac{\alpha}{\alpha-1}\int_1^\alpha r'_u(y)\,du,
$$

其模至多为 $2\sup|r'_u|\to0$。在一阶直接用 (117.37)，
从而覆盖以任意速度趋近一的阶数序列。
对 $\alpha\ge2$，第 115 章取固定间隔 $\epsilon=1$；其结论与 (117.5) 的差至多
$2R|b_1|+2R^2|c_1-1/(2\nu)|\to0$。
无穷阶的同一界取前因子一。第 115 章的大阶数连接仍使用原计数有限支撑：
平滑比较只到 $Q^6$，再由 $\log\#\operatorname{supp}P_x\le CQ^5$ 与
$0\le H_\alpha-H_\infty\le\log\#\operatorname{supp}P_x/(\alpha-1)$ 接上，
不把 Gaussian 比较延伸到任意小的 $\sigma/\sqrt\alpha$。

共同好事件、原支撑置换等变性及实际行估计恢复 (117.6) 的一致概率量词。
有限阶数及输出连续、实根光滑、Shannon 的有限和延拓和无穷阶极限，
允许用可数稠密参数集表示上确界，故可测性也保留。
这里的新增桥梁是 (117.36) 的原模型一阶导数控制。
第 115 章的零阶密度近似本身不能除以 $\alpha-1$ 得到本章结论。

有限幂律代数、指数倾斜、Gaussian 多项式矩、Stirling、Fourier 反演和均值定理均为经典工具。
Goodman 的可微鞍点误差提供方法来源，其固定 iid 条件不直接覆盖本章数组；
对应关系及适用边界见 Library 的本章条目。
结论限于 $\alpha\ge1$、紧物理输出、严格半指数范围和完整计数熵；
不声称一阶以下、无界输出、有限规模零噪声、半指数等号、输出平均熵或 Arimoto/Sibson 条件熵。
未作 Lean 核验或全局原创性认证。

## 追加锚（第 117 章后续增补区）
