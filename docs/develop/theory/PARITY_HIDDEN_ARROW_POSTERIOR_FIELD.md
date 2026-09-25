# 隐藏箭头的后验阈值过程

## 36. 阈值尾过程与分离边界的共同原点

**定义 36.1（同一后验上的阈值场）。** 取[波动卷定义 35.1](PARITY_HIDDEN_ARROW_FLUCTUATIONS.md)的非格点情形，固定
$`I=[s_0,s_1]`$、$`s_0\lt s_1`$。所有阈值与容量使用同一数据、同一补偿得分、
同一组连续优先级，以及同一组精确后验概率 $`\pi_i`$。对 $`s\in I`$ 定义

```math
A_M(s)=\{i:W_i\gt\tau+s\},\quad
N_M(s)=|A_M(s)|,\quad C_M(s)=|S\cap A_M(s)|,\quad
\overline C_M(s)=\sum_{i\in A_M(s)}\pi_i,\quad
U_M(s)=-\frac{C_M(s)-\overline C_M(s)}{b_M^\circ},
\qquad b_M^\circ=\sqrt{q/\sqrt\lambda}.
```

式 (36.1)。

该阈值过程在得分等于阈值时同时移除整个得分组，取右连续版本。
固定互异内点 $`s_0\lt c_j\lt s_1`$、$`1\le j\le d`$，以及 $`A\gt0`$，置

```math
\nu_{M,j}=\mathbb E_S N_M(c_j),\qquad
X_{M,j}=-\frac{N_M(c_j)-\nu_{M,j}}{\sqrt q},\qquad
m_{M,j}(a)=\lfloor\nu_{M,j}+a\sqrt q\rfloor\quad(|a|\le A).
```

式 (36.2)。

每个均值按实际实验与正确对齐方向计算，包含背景贡献。
令 $`T_{M,j}(a)`$ 为共同排序的前 $`m_{M,j}(a)`$ 个位置，
$`I_{M,j}(a)=A_M(c_j)\triangle T_{M,j}(a)`$，
$`e_{M,j}(a)=\mathrm{sgn}(N_M(c_j)-m_{M,j}(a))`$，定义

```math
R_{M,j}(a)=q^{-1/4}e_{M,j}(a)
 \left(|I_{M,j}(a)\cap S|-\sum_{i\in I_{M,j}(a)}\pi_i\right),\qquad
\mathcal P_{M,j}(a)=\frac{|S\setminus T_{M,j}(a)|-q+
 \sum_{i\in T_{M,j}(a)}\pi_i}{b_M^\circ}.
```

式 (36.3)。

未知方向时，阈值场与全部容量曲线共同使用定义 35.1 的一次方向判决和工作权重。
置

```math
\Gamma(s)=d_*\log(1+e^{-s}),\qquad
p_j=\frac1{1+e^{-c_j}},\quad v_j=p_j(1-p_j),\qquad
H(s)=B^\circ(\Gamma(s)).
```

式 (36.4)。

这里 $`B^\circ`$ 为标准 Brownian 运动。另取标准 Brownian 运动 $`B_{j,+},B_{j,-}`$，并定义

```math
K_j(t)=\begin{cases}
\sqrt{v_j}\,B_{j,+}(-t),&t\le0,\\[0pt]
-\sqrt{v_j}\,B_{j,-}(t),&t\ge0.
\end{cases}
```

式 (36.5)。

所有上述 Brownian 运动相互独立，并独立于
$`G\sim N(0,\sigma^2)`$、$`\sigma^2=p_*(1-p_*)`$。

**定理 36.2（连续阈值场与有限个独立边界的联合极限）。** 两个实际平稳实验、
两种方向信息情形均对支持一致地满足

```math
\left((X_{M,j})_{j=1}^d,U_M(\cdot),(R_{M,j}(\cdot))_{j=1}^d\right)
\Longrightarrow
\left((G)_{j=1}^d,H(\cdot),(K_j(G+\cdot))_{j=1}^d\right)
```

式 (36.6)。

空间为 $`\mathbb R^d\times D(I)\times D[-A,A]^d`$，各路径空间取
$`J_1`$ 拓扑，全部极限路径连续。此收敛还可同时加入
$`(\mathcal P_{M,j}(\cdot))_{j=1}^d`$，其极限为
$`(a\mapsto H(c_j))_{j=1}^d`$。阈值场独立于粗尺度原点和全部细尺度曲线，且

```math
\mathrm{Cov}(H(s),H(t))=\Gamma(\max(s,t)).
```

式 (36.7)。

不同细尺度曲线给定 $`G`$ 时独立，其绝对值曲线一般不无条件独立：
对 $`j\ne k`$，极限变量满足

```math
\mathrm{Cov}(K_j(G),K_k(G))=0,\qquad
\mathrm{Cov}(K_j(G)^2,K_k(G)^2)
=v_jv_k\sigma^2(1-2/\pi)\gt0.
```

式 (36.8)。

另一方面，过程族 $`(K_j(G+a)-K_j(G))_{|a|\le A}`$ 在不同 $`j`$ 间相互独立，
并共同独立于 $`G,H`$。这些矩等式只涉及极限变量。

证明。先取正确方向与先验联合空间。用第 35 章的同一校准参数定义 $`p_i`$；
它们不随阈值改变。记
$`d_M(s)=\sum_{i\in A_M(s)}p_i(1-p_i)`$。
对每个固定 $`s`$，(35.9) 给出
$`d_M(s)/(b_M^\circ)^2\to\Gamma(s)`$ 依概率。
左端随 $`s`$ 单调递减，右端连续；在有限确定网格上取这些收敛，
再以单调性夹住网格间的值，最后令网格宽度趋零，得到

```math
\epsilon_M:=\sup_{s\in I}
 \left|\frac{d_M(s)}{(b_M^\circ)^2}-\Gamma(s)\right|
\longrightarrow0\quad\text{依概率}.
```

式 (36.9)。

非格点分布仍可有原子。对得分恰等于 $`w`$ 的整个组
$`E_w=\{i:W_i=w\}`$，记 $`d_w=\sum_{i\in E_w}p_i(1-p_i)`$。
在 $`\tau+s_0\lt w\le\tau+s_1`$ 内，$`d_w/(b_M^\circ)^2`$
就是左端方差时钟的一次跳跃。由于 $`\Gamma`$ 连续，其最大值至多 $`2\epsilon_M`$。
所以整组方差的最大归一化跳跃趋零，而不只是单个标签的方差趋零。

固定排名半径 $`H_0\gt0`$，对每个 $`c_j`$ 取阈值两侧各前
$`\lceil H_0\sqrt q\rceil`$ 个位置，记为 $`B_{j,H_0}^\pm`$。
用一次并集
$`J=A_M(s_0)\cup\bigcup_j(B_{j,H_0}^+\cup B_{j,H_0}^-)`$。
有限多个固定阈值的定位估计给出

```math
|J|/q\longrightarrow1-p_*\in(0,1),\qquad
d_J=\frac q{\sqrt\lambda}
 \bigl(\Gamma(s_0)+o_{\mathbb P}(1)\bigr),\qquad d_O\ge cq/2
```

式 (36.10)。

均在概率趋一的事件上成立，第一式取依概率收敛。
增加的有限排名块总方差为 $`O_{d,H_0}(\sqrt q)=o(q/\sqrt\lambda)`$。
所有阈值集合 $`A_M(s)`$ 均包含于 $`J`$。
由 (35.11)、(35.12)，该完整向量的后验律与乘积律总变差趋零，且

```math
\sup_{s\in I}\frac1{b_M^\circ}
 \left|\sum_{i\in A_M(s)}(\pi_i-p_i)\right|\longrightarrow0,
\qquad
\max_{j,\pm}\sup_{B\text{ 为 }B_{j,H_0}^\pm\text{ 的前缀}}
 q^{-1/4}\left|\sum_{i\in B}(\pi_i-p_i)\right|\longrightarrow0
```

式 (36.11)。

两式均为依概率收敛。第一式在统一加权界中用 $`d_B\le d_J`$；
第二式用 $`d_B\le\lceil H_0\sqrt q\rceil/4`$。
因此不需要对连续多个阈值逐一作总变差比较。

先在独立 Bernoulli 乘积律下处理阈值场。不要把反射后的阶梯过程当作右连续鞅，
而应取递增阈值方向的条带过程

```math
D_M(s)=\frac1{b_M^\circ}
 \sum_{\tau+s_0\lt W_i\le\tau+s}(\zeta_i-p_i),\qquad
T_M=-\frac1{b_M^\circ}\sum_{i\in A_M(s_1)}(\zeta_i-p_i),\qquad
U_M^{\mathsf Q}(s)=T_M-D_M(s_1)+D_M(s).
```

式 (36.12)。

严格尾集与非严格条带端点使最后一个等式在所有原子处都精确成立。
$`D_M`$ 按得分组依次揭示，为右连续独立增量鞅；$`T_M`$ 与整个条带过程独立。
其可预测方差时钟为
$`(d_M(s_0)-d_M(s))/(b_M^\circ)^2`$，由 (36.9) 一致趋于
$`V(s)=\Gamma(s_0)-\Gamma(s)`$。该确定时钟连续且严格递增。

成组跳跃需另外核验。乘积律下同组标签仍相互独立，故其中心化和的四阶矩
至多 $`3d_w^2+d_w`$。令 $`\Delta_w D_M`$ 表示整个组的一次跳跃，则

```math
\sum_w\mathbb E_{\mathsf Q_M}|\Delta_wD_M|^4
\le3\left(\max_w\frac{d_w}{(b_M^\circ)^2}\right)
       \frac{\sum_w d_w}{(b_M^\circ)^2}
 +\frac1{(b_M^\circ)^2}\frac{\sum_w d_w}{(b_M^\circ)^2}
\longrightarrow0.
```

式 (36.13)。

这里与下文的乘积律极限先在满足时钟收敛的确定数据环境序列上解释。
因此最大跳幅平方的期望趋零，最大方差时钟跳跃也趋零。
以 $`V^{-1}`$ 作确定时间变换后，可预测方差时钟趋于恒等时钟。
[Whitt 定理 2.1(ii)](../../../Library/Dynamics/whitt2007martingale.md)
遂给出 $`D_M(s)\Rightarrow B(V(s))`$，其中 $`B`$ 为标准 Brownian 运动。
尾部标量由有界独立数组的 Lindeberg 定理趋于方差 $`\Gamma(s_1)`$ 的正态变量，
并保持与条带过程独立。由 (36.12)，极限是连续 Gaussian 过程，协方差恰为
$`\Gamma(\max(s,t))`$，即与 $`H`$ 同律。这同时给出阈值场的路径紧性。

再将有限多个细尺度过程放入同一联合极限。因 $`c_j`$ 互异，可先在它们周围取
互不相交的固定得分窗口。第 33、34 章的固定宽度定位使每个排名块落在自身窗口内
的概率趋一，因而不同 $`j`$ 的整个排名块不交。在乘积律下，各块的两侧前缀
遂给出相互独立的细尺度 Brownian 原过程 $`K_j`$。

这还不能单独推出它们与阈值场独立。对任意有限个阈值场时刻与排名时刻，
将全部坐标写成 $`J`$ 上独立中心化行向量的和。
任一固定线性组合的最大单行系数至多
$`C((b_M^\circ)^{-1}+q^{-1/4})=o(1)`$，满足 Lindeberg 条件。
阈值场与任一边界前缀的归一化交叉协方差，绝对值至多

```math
\frac{C_{d,H_0}\sqrt q}{b_M^\circ q^{1/4}}
=C_{d,H_0}(\lambda/q)^{1/4}\longrightarrow0.
```

式 (36.14)。

该界容许边界块与阈值尾集实际重叠；不同边界块之间的协方差则为零。
有限维极限先由多维 Lindeberg 定理确认为联合 Gaussian，继而由交叉协方差
为零得到独立性。第 34 章的连续排名插值紧性与阈值场紧性合并，
给出乘积路径空间中的联合极限。

将同一完整向量的总变差比较以及 (36.11) 用于该联合随机元，
便转移到精确后验。对子序列抽取使所有方差时钟、定位与校准条件几乎处处成立
的进一步子序列，逐个固定环境应用上述推导。于是精确后验条件律在

```math
D(I)\times\prod_{j=1}^d C[-H_0,H_0]
```

式 (36.15)。

上的有界 Lipschitz 距离，依概率且在 $`L^1`$ 中趋于
$`\mathcal L(H,(K_j|_{[-H_0,H_0]})_{j=1}^d)`$。
该极限核确定，且所有原过程相互独立。这里没有对任意有界可测路径测试
断言条件期望收敛。

还须证明不同阈值使用同一个粗尺度原点。对任意两个固定 $`c_j,c_k`$，
$`N_M(c_j)-N_M(c_k)`$ 除符号外，是固定得分区间中的实际混合行计数。
固定宽度局部界与背景换测度使其比较均值为 $`O(q/\sqrt\lambda)`$。
(35.8) 因而给出

```math
\mathrm{Var}_S\bigl(N_M(c_j)-N_M(c_k)\bigr)
\le C\left(\frac q{\sqrt\lambda}
 +\frac{\delta_M q^2}{\lambda}+M^{2-D}\right)=o(q),\qquad
\mathbb E_S|X_{M,j}-X_{M,k}|^2\longrightarrow0.
```

式 (36.16)。

其中 $`\delta_M=(\log M)^3/n`$，$`D`$ 取充分大。
各坐标减去的是自身的精确均值，因此上述方差直接控制原点之差。
任一原点已由 (34.8) 趋于 $`G`$，于是整个有限向量趋于 $`(G)_{j=1}^d`$。
这一步不需要关于连续所有阈值的粗尺度经验过程结论。

原点向量是数据函数。与第 35 章相同，取有界连续的原点向量测试函数，
以及 (36.15) 上的有界 Lipschitz 测试函数，先条件于数据再使用
确定条件核的 $`L^1`$ 收敛。联合紧性确定乘积极限，因此
$`G`$ 独立于阈值场和全部边界原过程。

对于每个 $`j`$，精确排名参数满足
$`(m_{M,j}(a)-N_M(c_j))/\sqrt q=X_{M,j}+a+O(q^{-1/2})`$，
其中余项对所有 $`|a|\le A`$ 一致。
先将有限原点截断于 $`[-L,L]`$，取 $`H_0\gt L+A+2`$。
每条连续排名插值的斜率至多 $`q^{1/4}`$，故舍入引起的一致误差
至多 $`q^{-1/4}`$。连续路径上的有限组平移映射给出共同起点为 $`G`$ 的曲线；
各原点的统一二阶矩界再以 $`C_d/L^2`$ 去掉截断。
遂证明 (36.6)。由每个 $`c_j`$ 处的精确恒等式

```math
\mathcal P_{M,j}(a)=U_M(c_j)+(\lambda/q)^{1/4}R_{M,j}(a)
```

式 (36.17)。

及有限组细尺度曲线的一致紧性，即可同时加入所述中间尺度曲线。

阈值场、各容量曲线和所有后验中心，在支持、行数据与优先级的共同置换下不变。
因此先验混合的无条件联合分布等于每个固定支持下的无条件联合分布。
未知方向时同一次判决在正确事件上使整个阈值场和所有曲线同时相等，
补集概率 $`O(q^{-1})`$ 转移联合弱极限。条件后验解释仍限定于均匀先验空间。

最后，给定 $`G=g`$，各 $`K_j(g)`$ 是独立中心正态变量，
方差为 $`v_j|g|`$。先作条件期望，再用
$`\mathrm{Var}|G|=\sigma^2(1-2/\pi)`$，即得 (36.8)。
每个非格点边界的两侧方差相等，故它是方差率 $`v_j`$ 的双侧 Brownian 过程。
对任意确定 $`g`$，增量过程 $`a\mapsto K_j(g+a)-K_j(g)`$ 的分布
不依赖 $`g`$。给定 $`G`$ 时不同 $`j`$ 的这些过程仍独立，
其乘积条件律也不依赖 $`G`$，故它们共同独立于 $`G`$ 且相互独立；
与 $`H`$ 的独立性由原过程独立性保持。这不声称单个增量过程独立于
其自身的绝对起点值，后者仍有推论 34.3 的负协方差。∎

## 追加锚（本行以下为增补区）

## 37. 微观得分窗口的后验噪声逃逸

**定义 37.1（中心计数原子与收缩窗口）。** 沿用[波动卷定义 27.1、33.1](PARITY_HIDDEN_ARROW_FLUCTUATIONS.md)的两个实际平稳实验，固定
$`r=1/2`$、$`\beta\in(1/2,1)`$。记信号漂移为
$`\phi=\tfrac34\log(3/2)-\tfrac14\log2\gt0`$，沿允许的
$`M=2^{d-1}\to\infty`$ 取

```math
\lambda_M=4\left\lfloor\frac{\beta\log M}{4\phi}\right\rfloor,
\qquad q_M=\left\lfloor M e^{-\lambda_M\phi}\right\rfloor,
\qquad \mathsf T_M=2M\lambda_M,\qquad
\tau_M=\log(M/q_M),\qquad w_M=\sqrt{\lambda_M/q_M}.
```

式 (37.1)。

下文略去 $`q,\lambda,\tau,w`$ 的下标。所有标签使用同一真实支持
$`S`$，$`\pi_i`$ 为正确对齐数据下、均匀基数先验的精确后验边缘概率。
令

```math
J_M=\{i:\tau-w\lt W_i\le\tau+w\},\qquad
V_M=q^{-1/4}\sum_{i\in J_M}(\mathbf1_{\{i\in S\}}-\pi_i),
\qquad
F_M(u)=q^{-1/4}\sum_{\tau-w\lt W_i\le\tau+uw}
              (\mathbf1_{\{i\in S\}}-\pi_i),\quad -1\le u\le1.
```

式 (37.2)。

路径取右连续版本，同分位置同时进入。于是 $`F_M(-1)=0`$、
$`F_M(1)=V_M`$。未知方向时，按定义 35.1 的同一次方向判决计算工作得分与工作概率，
得到相应的工作统计量；错误方向上的这些概率不被解释为未知方向模型的精确后验。

**定理 37.2（实际后验中心化噪声在微观窗口内不紧）。** 序列 (37.1) 满足非格点临界条件，
内在偏移极限为零。对两个实际实验，正确对齐的均匀先验联合空间中，对每个固定
$`0\le K\lt\infty`$，有

```math
\mathbb P\{|V_M|\le K\mid\mathscr D_M\}
\longrightarrow0\quad\text{依概率}.
```

式 (37.3)。

对每个固定真实支持及两种方向信息情形，相应统计量还满足

```math
\sup_{S:\,|S|=q}\mathbb P_S\{|V_M|\le K\}\longrightarrow0.
```

式 (37.4)。

因此 $`F_M`$ 的分布族在 $`D[-1,1]`$ 的 $`J_1`$ 拓扑下不紧。
此结论使用得分窗口 $`w_M`$，不改变按容量或排序位置索引的细尺度极限。

证明。非格点性及中心原子的构造见[波动卷命题 33.3](PARITY_HIDDEN_ARROW_FLUCTUATIONS.md)。
这里具体地，$`\log(3/2)/(-\log2)`$ 为无理数，否则会使三的非零整数次幂等于二的整数次幂。
取整给出

```math
\lambda\sim\frac\beta\phi\log M,\qquad
q=M^{1-\beta+o(1)},\qquad
\tau-\lambda\phi=O(q^{-1}),\qquad
z_M\longrightarrow0.
```

式 (37.5)。

特别地 $`q`$ 比 $`\lambda`$ 的每个固定幂增长更快。
令 $`B_M`$ 为实际计数对恰等于
$`(3\lambda/4,\lambda/4)`$ 的全部位置，包含信号与背景位置。
这些计数是整数，且所有这些位置的补偿得分相同。记
$`a_M=rq/(M-q)`$，该得分为

```math
W_c=\frac{3\lambda}{4}\log\frac{3/2}{1-a_M}
       +\frac\lambda4\log\frac{1/2}{1+a_M},\qquad
|W_c-\tau|\le C(a_M\lambda+q^{-1})=o(w).
```

式 (37.6)。

最后一个等式由
$`a_M\lambda/w=O(q^{3/2}\sqrt\lambda/M)\to0`$
及 $`1/(qw)=1/\sqrt{\lambda q}\to0`$ 得到。
因此 $`B_M\subseteq J_M`$ 对充分大的 $`M`$ 恒成立。

在信号 Poisson 行比较律 $`Q_r`$ 下，经典 Stirling 公式给出中心计数对的概率
$`h_\lambda\sim2/(\pi\sqrt3\lambda)`$。
补偿背景比较律记为 $`Q_{-a_M}`$，精确换测度关系为
$`dQ_r=e^W dQ_{-a_M}`$。故全部位置的比较期望为

```math
\mu_B=qh_\lambda+(M-q)e^{-W_c}h_\lambda
=qh_\lambda\left(1+\frac{M-q}{q}e^{-W_c}\right)
\sim\frac{4q}{\pi\sqrt3\lambda}.
```

式 (37.7)。

这是同一实际对象中的混合计数；背景项与信号项具有相同主阶。
对中心计数对的确定指示函数应用波动卷 (35.8)，令
$`\delta_M=(\log M)^3/(2M)`$，有

```math
|\mathbb E_S|B_M|-\mu_B|\le C\delta_M\mu_B+CM^{1-D},\qquad
\mathrm{Var}_S(|B_M|)
\le C(\mu_B+\delta_M\mu_B^2+M^{2-D}),\qquad
\frac{|B_M|}{q/\lambda}\longrightarrow\frac4{\pi\sqrt3}
\quad\text{依概率}.
```

式 (37.8)。

这里 $`D`$ 可取任意充分大的固定数。除以相应主阶后，均值误差趋零，相对方差由
$`C(\lambda/q+\delta_M+M^{2-D}\lambda^2/q^2)`$ 控制并趋零。
实际一、二行比较同时适用于独立对与路径实验，不要求实际行相互独立。

现在在同一校准独立 Bernoulli 表示中工作：
$`p_i=\mathrm{logistic}(W_i-\log((M-q)/q)+\theta_M)`$，
$`\sum_i p_i=q`$，乘积律记为 $`\mathsf Q_M`$。
波动卷第 35 章给出
$`\theta_M=O_{\mathbb P}(q^{-1/2})`$ 及
$`cq\le d_{\mathrm{tot}}:=\sum_i p_i(1-p_i)\le q`$
在概率趋一的事件上成立。
因为 $`w\to0`$、$`\log((M-q)/q)-\tau=o(1)`$，所以
$`\max_{i\in J_M}|p_i-1/2|\to0`$ 依概率，空集时该最大值置零。
由 (37.8)，中心组的辅助方差满足

```math
\frac{\sum_{i\in B_M}p_i(1-p_i)}{q/\lambda}
\longrightarrow\frac1{\pi\sqrt3},\qquad
 d_J:=\sum_{i\in J_M}p_i(1-p_i)\ge c_1q/\lambda
\quad\text{以趋一概率成立}.
```

式 (37.9)。

为了控制其上界，只须把收缩窗口包含在固定区间
$`\{\tau-1\lt W\le\tau+1\}`$。
固定宽度局部界使该区间的信号概率为 $`O(\lambda^{-1/2})`$。
在该区间内 $`e^{-W}\le e q/M`$，换测度后整个混合比较期望为
$`O(q/\sqrt\lambda)`$。再用 (35.8) 的一阶矩界和 Markov 不等式，得到

```math
|J_M|/q\longrightarrow0,\qquad d_J/q\longrightarrow0,
\qquad d_O:=d_{\mathrm{tot}}-d_J\ge cq/2
\quad\text{以趋一概率成立}.
```

式 (37.10)。

同时可令 $`|J_M|\lt q`$、$`M-|J_M|\gt q`$。
这里没有在收缩窗口上使用相对密度近似，也没有求整个窗口方差的精确主项。

给定这样的数据，在乘积律下写
$`S_J=\sum_{i\in J_M}\zeta_i`$、$`\mu_J=\sum_{i\in J_M}p_i`$，
并以 $`S_O`$ 表示补集和。条件于全体和为 $`q`$ 就是精确固定基数后验。
由 [Siripraparat–Neammanee 定理 2](../../../Library/Dynamics/siripraparat2021local.md)
对全体和及补集和的一致局部概率界，完整向量的条件密度比满足

```math
\frac{\mathsf Q_M(S_O=q-k)}{\mathsf Q_M(S_J+S_O=q)}
=\sqrt{\frac{d_{\mathrm{tot}}}{d_O}}
  \exp\left(-\frac{(k-\mu_J)^2}{2d_O}\right)+O(q^{-1/2}),
\qquad 0\le k\le|J_M|.
```

式 (37.11)。

分母的均值正好是整数 $`q`$；上述基数界使所有补集取值合法。
与波动卷 (35.11) 同样积分，精确后验完整边缘律 $`\mathsf P_J`$ 满足

```math
d_{\mathrm{TV}}(\mathsf P_J,\mathsf Q_J)
\le C(d_J/q+q^{-1/2})\longrightarrow0
\quad\text{依概率}.
```

式 (37.12)。

此处移除条件化所需的是消失的方差比例，窗口可以含远多于 $`\sqrt q`$ 个位置。

最后把同一局部定理用于 $`S_J`$ 本身。由 $`d_J\to\infty`$，一致地对整数 $`k`$，
$`\mathsf Q_M(S_J=k)\le C/\sqrt{d_J}`$。
任何半径为 $`L`$ 的实区间至多包含 $`2L+2`$ 个整数。因此对任意实数中心
$`x`$，包括任意给定数据后的中心，均有

```math
\mathsf Q_M\{|S_J-x|\le Kq^{1/4}\}
\le\frac{C(Kq^{1/4}+1)}{\sqrt{d_J}}
\le C_K\left(\frac{\sqrt\lambda}{q^{1/4}}
                   +\sqrt{\frac\lambda q}\right)\longrightarrow0.
```

式 (37.13)。

取 $`x=\sum_{i\in J_M}\pi_i`$，再加上 (37.12) 的误差，便得到 (37.3)。
反集中估计对中心一致，因而不需要把无界均值经总变差转移，
也不需要将辅助中心替换为精确中心的更高阶展开。
条件概率被一控制，其期望也趋零。事件及统计量在共同置换支持和数据时不变，
所以先验联合概率等于每个固定支持下的概率，给出正确方向的 (37.4)。
未知方向的工作统计量在同一次方向判决正确时与正确对齐统计量逐项相等；
补事件概率为 $`O(q^{-1})`$，故相等耦合转移 (37.4)。

最后，$`J_1`$ 时间变换固定区间端点，因此端点评价
$`f\mapsto f(1)`$ 连续。若 $`F_M`$ 的分布族紧，则
$`F_M(1)=V_M`$ 的分布族也紧，与 (37.4) 矛盾。∎

## 追加锚（本行以下为增补区）

## 38. 算术隔离与第三尺度上的单跳极限

**定义 38.1（中心原子的噪声尺度）。** 取定义 37.1 的同一序列、同一数据与精确后验。
记

```math
B_M=\{i:(N_{i,+},N_{i,-})=(3\lambda/4,\lambda/4)\},\qquad
b_M^\bullet=\sqrt{q/\lambda},\qquad
\gamma_*=\frac1{\pi\sqrt3},\qquad
Y_M=\frac1{b_M^\bullet}\sum_{i\in J_M}(\mathbf1_{\{i\in S\}}-\pi_i).
```

式 (38.1)。

在同一收缩窗口内定义右连续过程

```math
\mathcal A_M(u)=\frac1{b_M^\bullet}
 \sum_{\tau-w\lt W_i\le\tau+uw}(\mathbf1_{\{i\in S\}}-\pi_i),
\qquad -1\le u\le1,\qquad
u_M=\frac{W_c-\tau}{w}.
```

式 (38.2)。

这里 $`W_c`$ 是 (37.6) 的确定得分，$`u_M\to0`$。
未知方向时仍按定义 37.1 的同一次判决使用工作得分与工作权重。

**定理 38.2（算术原子的独立高斯跳跃）。** 两个实际平稳实验均对支持一致地满足

```math
\mathbb P_S(J_M=B_M)\longrightarrow1,\qquad
\frac1{q/\lambda}\sum_{i\in J_M}p_i(1-p_i)
\longrightarrow\gamma_*\quad\text{依概率},\qquad
\mathcal A_M\Longrightarrow
\bigl(u\mapsto\sqrt{\gamma_*}\,Z\mathbf1_{[0,1]}(u)\bigr)
\quad\text{于 }D[-1,1],\ J_1.
```

式 (38.3)。

第一、二项使用正确对齐数据及第 35 章的校准参数 $`p_i`$；
第三项同时适用于两种方向信息情形，$`Z`$ 为标准正态变量。
它还与定理 36.2 的全部坐标联合成立，且新变量 $`Z`$ 独立于
$`G,H,K_1,\ldots,K_d`$：

```math
\left((X_{M,j})_{j=1}^d,U_M,(R_{M,j})_{j=1}^d,\mathcal A_M\right)
\Longrightarrow
\left((G)_{j=1}^d,H,(K_j(G+\cdot))_{j=1}^d,
       u\mapsto\sqrt{\gamma_*}\,Z\mathbf1_{[0,1]}(u)\right).
```

式 (38.4)。

空间为 $`\mathbb R^d\times D(I)\times D[-A,A]^d\times D[-1,1]`$，
各路径空间取 $`J_1`$ 拓扑；定义 36.1 中的固定区间和互异内点任取。
新尺度严格位于已有两种噪声尺度之间：

```math
\frac{q^{1/4}}{b_M^\bullet}=\frac{\sqrt\lambda}{q^{1/4}}\longrightarrow0,
\qquad
\frac{b_M^\bullet}{b_M^\circ}=\lambda^{-1/4}\longrightarrow0.
```

式 (38.5)。

证明。先证明窗口的算术隔离。在任意固定计数截断
$`k+l\le C\log M`$ 内，置
$`k_0=3\lambda/4`$、$`l_0=\lambda/4`$。未补偿得分满足

```math
Z(k,l)-\lambda\phi
=(k-k_0)\log3-(k+l-\lambda)\log2.
```

式 (38.6)。

右端为零当且仅当 $`k=k_0,l=l_0`$，因为二与三乘法独立。
[Matveev 推论 2.3](../../../Library/Dynamics/matveev2000logarithms.md)
用于数域 $`\mathbb Q`$、代数数 $`2,3`$、实对数以及固定高度参数
$`\log2,\log3`$，给出常数 $`C_0\gt0`$，使对任意不全为零的整数
$`m,n`$，令 $`H=\max(2,|m|,|n|)`$，都有

```math
|m\log3-n\log2|\ge H^{-C_0}.
```

式 (38.7)。

这里将原定理的固定乘法常数吸收到幂指数中；一个系数为零时同样适用。
此下界来自固定代数数的对数，不能仅由两个跳幅之比无理推出。
由截断内的系数为 $`O(\log M)`$，存在固定 $`C_1\gt0`$，使每个非中心计数对满足
$`|Z(k,l)-\lambda\phi|\ge(\log M)^{-C_1}`$，对充分大的 $`M`$ 成立。

同一截断内补偿扰动一致满足
$`|W(k,l)-Z(k,l)|\le C_2a_M\log M`$，而
$`|\tau-\lambda\phi|\le q^{-1}`$。
由于 $`q=M^{1-\beta+o(1)}`$，
$`a_M\log M`$、$`q^{-1}`$ 和 $`w=\sqrt{\lambda/q}`$
都比任意固定的 $`\log M`$ 负幂更快趋零。因此截断内

```math
(k,l)\ne(k_0,l_0)\quad\Longrightarrow\quad
|W(k,l)-\tau|\ge\tfrac12(\log M)^{-C_1}\gt w.
```

式 (38.8)。

已有实际一行计数尾界允许任取固定的多项式指数，再增大固定截断常数。
选指数大于二并对全部 $`M`$ 行取并集，得到
$`\mathbb P_S\{\max_i(N_{i,+}+N_{i,-})\gt C\log M\}\to0`$，
两个实验均支持一致。结合 (37.6) 的 $`B_M\subseteq J_M`$，得到
$`J_M=B_M`$ 以趋一概率成立。这个并集界不要求实际行独立。

由 (37.8)、(37.9)，在同一实际数据下有下式；空组的最大偏差记为零：

```math
\frac{|B_M|}{q/\lambda}\longrightarrow\frac4{\pi\sqrt3},\qquad
\max_{i\in B_M}|p_i-1/2|\longrightarrow0,\qquad
\frac{d_B}{(b_M^\bullet)^2}\longrightarrow\gamma_*,\quad
 d_B:=\sum_{i\in B_M}p_i(1-p_i).
```

式 (38.9)。

依概率收敛在先验混合空间中也成立。这里混合组的基数包括信号与背景，
不能只保留信号的半个主项。

先固定好数据。在校准乘积律 $`\mathsf Q_M`$ 下，独立中心化标签均被一控制，
$`b_M^\bullet\to\infty`$，且 (38.9) 给出归一化方差。
Lindeberg 中心极限定理遂给出
$`(b_M^\bullet)^{-1}\sum_{i\in B_M}(\zeta_i-p_i)`$
趋于 $`N(0,\gamma_*)`$。其条件律的有界 Lipschitz 距离依概率趋零。
补集保留 $`q`$ 量级的方差，而 $`d_B/q=O_{\mathbb P}(\lambda^{-1})`$，
故 (35.11) 的完整向量比较移除基数条件化。

精确中心另用 (35.12)，将其中完整集合及子集均取为 $`B_M`$，得到

```math
\frac1{b_M^\bullet}
 \left|\sum_{i\in B_M}(\pi_i-p_i)\right|
\le\frac{C\sqrt{d_B}}{b_M^\bullet}
 \left(\frac{d_B}{q}+\frac{\sqrt{d_B}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (38.10)。

这不是将总变差乘以组的基数。于是精确后验中心化的组和也有同一条件极限。
再用 $`J_M=B_M`$ 的趋一事件，得到 $`Y_M\Longrightarrow\sqrt{\gamma_*}Z`$。

在该事件上，整个路径恰好为

```math
\mathcal A_M(u)=Y_M\mathbf1_{[u_M,1]}(u).
```

式 (38.11)。

对充分大的 $`M`$，$`u_M\in(-1,1)`$。取严格递增、分段线性的时间变换
$`\rho_M`$，使其固定端点并满足 $`\rho_M(0)=u_M`$；则
$`\sup_u|\rho_M(u)-u|\le|u_M|\to0`$，且
$`\mathbf1_{[u_M,1]}(\rho_M(u))=\mathbf1_{[0,1]}(u)`$。
由幅度到固定跳跃路径的映射在一致范数下连续，得到 (38.3) 的路径极限。
这里不要求 $`u_M`$ 始终位于零的同一侧，也不由 $`J_1`$ 收敛推断跳点零处的逐点收敛。

还须验证联合独立性。对定理 36.2 的固定有限阈值族，先将各细边界截在
$`H_0\sqrt q`$ 个排序位置内。把 $`B_M`$ 加入第 36 章使用的同一次完整并集，
记所得集合为 $`\mathcal J_M`$。由 $`|B_M|=O_{\mathbb P}(q/\lambda)=o_{\mathbb P}(q)`$，
原并集的基数极限不变；并集方差仍为
$`d_{\mathcal J}=O_{\mathbb P}(q/\sqrt\lambda)=o_{\mathbb P}(q)`$，
补集仍有 $`q`$ 量级方差。故可以对所有坐标使用一次完整向量总变差比较。
在 (35.12) 中令子集为 $`B_M`$，并集为 $`\mathcal J_M`$，
除以 $`b_M^\bullet`$ 后的上界为

```math
\frac{C\sqrt{d_B}}{b_M^\bullet}
 \left(\frac{d_{\mathcal J}}q+
       \frac{\sqrt{d_{\mathcal J}}}q+q^{-1/2}\right)
=O_{\mathbb P}(\lambda^{-1/2})+o_{\mathbb P}(1).
```

式 (38.12)。

因此共同转移时新坐标的精确中心仍受控制，旧坐标的两种中心界也仍成立。

在乘积律下，把中心组和加入第 36 章的任意有限维线性组合。
最大的单标签归一化系数仍趋零，联合 Lindeberg 条件成立。
组和与任一阈值尾的协方差绝对值至多为 $`d_B`$；
与任一截断细前缀的协方差绝对值至多为 $`C_{H_0}\sqrt q`$。
归一化后分别为

```math
\frac{d_B}{b_M^\bullet b_M^\circ}
=O_{\mathbb P}(\lambda^{-1/4})\longrightarrow0,
\qquad
\frac{C_{H_0}\sqrt q}{b_M^\bullet q^{1/4}}
=O_{H_0}\left(\frac{\sqrt\lambda}{q^{1/4}}\right)\longrightarrow0.
```

式 (38.13)。

中心组与细前缀允许重叠；这里并未将它们当作有限样本独立块。
联合高斯极限加上这些消失的协方差，才给出新高斯变量与旧原始过程的独立性。
原路径族的紧性与新标量的紧性建立乘积空间紧性。
完整向量比较及 (38.12) 转移整个联合条件律，其确定有界 Lipschitz 极限
使新变量和旧原始过程共同独立于数据可测的粗尺度原点。
随后按第 36 章先加入有限个共同原点，再作随机平移、控制取整并去掉 $`H_0`$ 截断。
最后使用 (38.11) 的确定跳点对齐，即得 (38.4)。

所有集合、中心及联合对象都对共同支持置换等变，故先验联合分布等于每个固定支持下的分布。
未知方向的全部坐标在同一个正确判决事件上逐项相等，补事件概率为 $`O(q^{-1})`$。
这分别转移固定支持联合律与工作方向版本，完成证明。∎

## 追加锚（本行以下为增补区）

## 39. 近算术聚簇的高斯端点与路径不紧性

**定义 39.1（一个固定非格点幅度与聚簇序列）。** 令

```math
A_1=1,\quad A_{j+1}=10^{5A_j},\quad
Q_j=10^{A_j},\quad P_j=\sum_{h=1}^j10^{A_j-A_h},\quad
\alpha=\sum_{h=1}^{\infty}10^{-A_h}.
```

式 (39.1)。

固定一个满足 $`\log(1+r)/[-\log(1-r)]=\alpha`$ 的 $`r\in(0,1)`$，并记

```math
a=\frac{1+r}{2},\quad b=\frac{1-r}{2},\quad
h=-\log(1-r),\quad \phi=a\log(1+r)+b\log(1-r),\quad
D=b+a\alpha^2,\quad \kappa=\frac1a+\frac{\alpha^2}{b}.
```

式 (39.2)。

固定 $`\beta\in(1/2,1)`$。以下省略序列下标 $`j`$，取

```math
\lambda=Q^3,\quad N=\left\lfloor\frac{\phi\lambda}{\beta\log2}\right\rfloor,
\quad M=2^N,\quad
k_0=\lfloor a\lambda\rfloor,\quad l_0=\lambda-k_0,\quad
z_0=k_0\log(1+r)+l_0\log(1-r),
\quad q=\lfloor M e^{-z_0}\rfloor,\quad
\tau=\log(M/q),\quad \mathsf T=2M\lambda.
```

式 (39.3)。

使用定义 27.1 的两个实际平稳实验、完整数据和优先级，以及均匀固定基数先验。
补偿参数记为 $`\epsilon=rq/(M-q)`$，避免与 (39.2) 的 $`a`$ 混淆。
正确对齐的一行得分、微观窗口和计数直线为

```math
W(k,l)=k\log\frac{1+r}{1-\epsilon}
       +l\log\frac{1-r}{1+\epsilon},\qquad
w=\sqrt{\lambda/q},\qquad J=\{i:\tau-w\lt W_i\le\tau+w\},
\qquad
\mathcal L=\{(k_0+tQ,l_0+tP):t\in\mathbb Z,\ k_0+tQ\ge0,\ l_0+tP\ge0\}.
```

式 (39.4)。

$`\pi_i`$ 为精确后验包含概率，$`p_i`$ 为第 35 章的校准独立参数。
定义新的噪声归一化和右连续过程

```math
B=\sqrt{\frac{q}{Q\sqrt\lambda}},\qquad
\gamma=\frac1{2\sqrt{2\pi}\sqrt D},\qquad
Y=\frac1B\sum_{i\in J}(\mathbf1_{\{i\in S\}}-\pi_i),\qquad
F(u)=\frac1B\sum_{\tau-w\lt W_i\le\tau+uw}
                 (\mathbf1_{\{i\in S\}}-\pi_i),\quad -1\le u\le1.
```

式 (39.5)。

未知方向时，仍先作同一次方向判决，再在工作正向数据上计算得分与正向模型权重。

**定理 39.2（聚簇改变尺度，端点极限不保证路径极限）。** 定义 39.1 的幅度存在且非格点，
参数最终合法。两个实际实验均对支持一致地满足

```math
\mathbb P_S\{J=\{i:(N_{i,+},N_{i,-})\in\mathcal L\}\}\longrightarrow1,
\qquad
\frac{Q\sqrt\lambda}{q}|J|\longrightarrow
\frac2{\sqrt{2\pi}\sqrt D},\qquad
\frac1{B^2}\sum_{i\in J}p_i(1-p_i)\longrightarrow\gamma
\quad\text{依概率}.
```

式 (39.6)。

这些式子使用正确对齐数据。两种方向信息情形均有

```math
Y=F(1)\Longrightarrow N(0,\gamma),\qquad
\mathbb P_S\left\{
\left|\frac1{\sqrt{q/\lambda}}
\sum_{i\in J}(\mathbf1_{\{i\in S\}}-\pi_i)\right|\le K\right\}
\longrightarrow0\qquad(K\lt\infty).
```

式 (39.7)。

然而，$`(F)_j`$ 在 $`D[-1,1]`$ 的 $`J_1`$ 拓扑下不紧。
因此第 38 章的原子尺度及单跳路径结论不能只凭非格点条件推广到所有固定幅度。

证明。$`P_j`$ 的十进制末位是一，故 $`\gcd(P_j,Q_j)=1`$。
正的尾和满足

```math
0\lt\alpha-P_j/Q_j\lt e^{-Q_j^4}
```

式 (39.8)。

此式对充分大的 $`j`$ 成立。若 $`\alpha=u/v`$ 为有理数，
它与不同的 $`P_j/Q_j`$ 的距离至少为 $`1/(vQ_j)`$，矛盾。
函数 $`r\mapsto\log(1+r)/[-\log(1-r)]`$ 连续，在零和一处的单侧极限分别为一和零，
所以所需 $`r`$ 存在。其跳幅之比为无理数，且 $`\phi\gt0`$。
由取整直接得到

```math
z_0=\lambda\phi+O(1),\qquad
\log M=\lambda\phi/\beta+O(1),\qquad
q=M^{1-\beta+o(1)},\qquad
\tau=z_0+O(q^{-1}).
```

式 (39.9)。

故 $`1\le q\lt M`$、$`\epsilon\lt1`$ 最终成立，样本量为整数，
$`M`$ 属于允许的超立方体大小。该序列也满足第 27 章内在偏移为零的临界条件。

先在固定截断 $`k+l\le C\lambda`$ 上分析窗口。
令 $`Z(k,l)=k\log(1+r)+l\log(1-r)`$，则

```math
Z(k,l)-z_0
=h\left[\frac{P(k-k_0)-Q(l-l_0)}Q
      +(\alpha-P/Q)(k-k_0)\right].
```

式 (39.10)。

分子为非零整数时，右端绝对值至少为 $`h/(2Q)`$，对充分大的 $`j`$ 一致成立。
分子为零时，互素性恰好给出 $`(k,l)\in\mathcal L`$。
后一情形的未补偿差至多为 $`C'\lambda e^{-Q^4}`$。
截断内补偿差至多为 $`C''\epsilon\lambda`$，并且

```math
\frac{\lambda e^{-Q^4}}w\longrightarrow0,\qquad
\frac{\epsilon\lambda}w
=O\left(\frac{q^{3/2}\sqrt\lambda}{M}\right)\longrightarrow0,
\qquad \frac1{qw}\longrightarrow0,
\qquad Qw\longrightarrow0.
```

式 (39.11)。

因此截断内的计数对落入窗口当且仅当属于 $`\mathcal L`$。
实际一行尾界允许任取充分大的多项式指数，再增大固定 $`C`$；
对全部 $`M`$ 行取并集，即得 (39.6) 的第一式。
这一步不要求实际观测行独立。

下面直接求比较 Poisson 律的直线概率，不向增长系数的线性组合套用固定格距定理。
在信号比较律 $`Q_r`$ 下，两计数独立，均值为 $`a\lambda,b\lambda`$。
令 $`x=tQ/\sqrt\lambda`$。对每个固定 $`R\lt\infty`$，Stirling 公式一致给出

```math
Q_r\{(N_+,N_-)=(k_0+tQ,l_0+tP)\}
=\frac{1+o(1)}{2\pi\lambda\sqrt{ab}}
 \exp(-\kappa x^2/2),\qquad |x|\le R.
```

式 (39.12)。

取整造成的均值偏差有界，而 $`P/Q\to\alpha`$。
网格步长 $`Q/\sqrt\lambda=Q^{-1/2}`$ 趋零，所以任意固定有限端点区间 $`E`$ 满足

```math
Q\sqrt\lambda\,
Q_r\{(N_+,N_-)\in\mathcal L,\ tQ/\sqrt\lambda\in E\}
\longrightarrow
\frac1{2\pi\sqrt{ab}}\int_E e^{-\kappa x^2/2}\,dx.
```

式 (39.13)。

开闭端点不改变此极限，因为单个点的归一化质量为 $`O(Q/\sqrt\lambda)=o(1)`$。

为把 (39.13) 扩展到整条直线，先在
$`|N_+-a\lambda|\le c\lambda`$ 上用 Poisson 点概率界
$`C\lambda^{-1/2}\exp[-c'(N_+-a\lambda)^2/\lambda]`$，
另一计数的最大点概率以 $`C\lambda^{-1/2}`$ 控制。
直线尾和在乘以 $`Q\sqrt\lambda`$ 后，至多为高斯积分尾乘以固定常数及趋零误差。
剩余区域由单个 Poisson 计数的指数尾界控制，归一化后仍趋零。
先令 $`j\to\infty`$，再令 $`R\to\infty`$，得到

```math
Q_r\{(N_+,N_-)\in\mathcal L\}
\sim\frac1{Q\sqrt{2\pi\lambda}\sqrt D}.
```

式 (39.14)。

在公共截断的直线上，$`W=\tau+o(1)`$ 一致成立。
精确换测度 $`dQ_r=e^W dQ_{-\epsilon}`$ 使背景的混合贡献
$`(M-q)Q_{-\epsilon}(\mathcal L)`$ 渐近等于 $`qQ_r(\mathcal L)`$；
截断外余项可取为任意多项式小量。
实际一行、两行比较随后给出同一计数及每个固定 $`E`$ 子块的均值与方差界。
其均值为 $`q/(Q\sqrt\lambda)`$ 的固定正比例，方差至多为
均值乘以常数、$`\delta_M`$ 乘以均值平方，以及可任意提高指数的余项之和，
其中 $`\delta_M=(\log M)^3/n\to0`$。
所以这些实际占据数集中，证明 (39.6) 的基数结论。

校准公式还给出 $`\max_{i\in J}|p_i-1/2|\to0`$ 依概率，空集时最大值置零。
由此，整窗归一化方差趋于 $`\gamma`$，每个固定 $`E`$ 子块的归一化方差趋于

```math
\nu(E)=\frac1{4\pi\sqrt{ab}}\int_E e^{-\kappa x^2/2}\,dx,
\qquad \nu(\mathbb R)=\gamma.
```

式 (39.15)。

特别地，$`d_J:=\sum_{i\in J}p_i(1-p_i)\asymp B^2=o(q)`$ 依概率，
补集仍保留 $`q`$ 量级方差。

在同一校准乘积律下，任意有限个互不相交的固定 $`E`$ 子块满足联合有界数组中心极限定理，
其极限协方差为以 $`\nu(E)`$ 为对角元的对角阵。
整窗亦有方差 $`\gamma`$ 的极限。
第 35 章的完整向量比较对同一个并集 $`J`$ 使总变差趋零；
各子块 $`J_E`$ 的精确中心同时满足

```math
\frac1B\left|\sum_{i\in J_E}(\pi_i-p_i)\right|
\le\frac{C\sqrt{d_{J_E}}}{B}
  \left(\frac{d_J}{q}+\frac{\sqrt{d_J}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (39.16)。

整窗也取相同的中心界。因此在均匀支持先验下，联合条件律的有界 Lipschitz 距离
依概率趋于对应的确定高斯律。取期望即可得到 $`Y\Longrightarrow N(0,\gamma)`$。
又因为

```math
\frac{B}{\sqrt{q/\lambda}}=\frac{\lambda^{1/4}}{\sqrt Q}=Q^{1/4}\longrightarrow\infty,
```

式 (39.17)。

归一化 $`Y`$ 的缩小区间概率可先用任意固定小区间控制，再由正态极限令该区间宽度趋零。
这证明 (39.7) 的逃逸结论，不使用实际统计量的矩收敛。

最后验证路径不紧性。直线上的相邻得分差为

```math
\Delta
=Q\log\frac{1+r}{1-\epsilon}+P\log\frac{1-r}{1+\epsilon}
=hQ(\alpha-P/Q)+\epsilon(Q-P)+O(\epsilon^2Q)\gt0
```

式 (39.18)。

对充分大的 $`j`$，第一项为正，且 $`1-P/Q`$ 有固定正下界，故最后的不等式成立。
固定任意 $`R\gt0`$，置 $`m=\lfloor R\sqrt\lambda/Q\rfloor`$，并定义确定时点

```math
u_- =\frac{W(k_0-mQ,l_0-mP)-\tau}{w},\quad
u_0 =\frac{W(k_0,l_0)-\tau}{w},\quad
u_+ =\frac{W(k_0+mQ,l_0+mP)-\tau}{w}.
```

式 (39.19)。

三点严格递增且都趋于零，所用计数最终为非负。
在公共截断事件上，两个相邻过程增量恰好对应直线上参数范围
$`(-m,0]`$ 与 $`(0,m]`$ 的标签块。
由 (39.13)–(39.16)，

```math
\bigl(F(u_0)-F(u_-),F(u_+)-F(u_0)\bigr)
\Longrightarrow (Z_-,Z_+),\qquad
Z_-,Z_+\text{ 独立},\qquad
Z_\pm\sim N(0,\nu((0,R])).
```

式 (39.20)。

该方差严格为正。
取固定 $`\eta\gt0`$，两增量绝对值同时大于 $`2\eta`$ 的概率趋于严格正数。
对任意固定小 $`\delta\gt0`$，上述三点最终位于区间内部，且跨度小于 $`\delta`$。
任意内部段长度大于 $`\delta`$ 的分割，至多在这三点之间放一个分割点，
故至少一对相邻时点属于同一个半开分割区间。
若分割点恰为中间时点，则后两个时点属于同一段。
于是经典 $`J_1`$ 分割振荡模量至少为两相邻增量绝对值的较小者。
由 [Whitt 的经典紧性判据，定理 3.2](../../../Library/Dynamics/whitt2007martingale.md)，
$`J_1`$ 紧性所必需的模量条件失败。
这里使用两个完整计数块的增量，而不是把单标签小跳误当作整个同分组的小跳。

上述条件计算均在均匀支持先验下。
所有集合、精确中心及整个路径都对共同支持置换等变，所以其无条件分布等于任意固定支持下的分布。
一行、两行界的支持一致性也保留了所述一致结论。
未知方向的全部对象在同一个正确判决事件上与正确对齐版本逐项相等，
补事件概率为 $`O(q^{-1})`$，故端点极限、逃逸及振荡下界一并转移。
这既不把固定支持下的标签重新解释为随机后验标签，也不声称其他路径拓扑下的结论。∎

## 追加锚（本行以下为增补区）

## 40. 补偿尺度上的聚簇轮廓与后验桥

**定义 40.1（按精确中心展开聚簇）。** 沿用定义 39.1 的固定幅度、固定 $`\beta\in(1/2,1)`$
及其序列，保留同一实际数据、优先级与精确后验标签。置

```math
W_c=W(k_0,l_0),\qquad
\Delta=Q\log\frac{1+r}{1-\epsilon}
       +P\log\frac{1-r}{1+\epsilon},\qquad
v=\frac{\sqrt\lambda}{Q}\Delta,\qquad
F_0(x)=\Phi(\sqrt\kappa\,x),\qquad V(x)=\gamma F_0(x),
```

式 (40.1)。

其中 $`\Phi`$ 是标准正态分布函数。以下仅取使 $`\Delta\gt0`$ 的充分大下标。
对 $`x\in\mathbb R`$ 定义右连续的轮廓与桥

```math
J_x=\{i\in J:W_i\le W_c+xv\},\qquad
L_M(x)=\frac1B\sum_{i\in J_x}(\mathbf1_{\{i\in S\}}-\pi_i),\qquad
\mathcal C_M(x)=L_M(x)-F_0(x)Y.
```

式 (40.2)。

这里 $`J,B,Y,\gamma,\kappa`$ 均取第 39 章定义。
未知方向版本共同使用一次方向判决及其工作正向得分、后验权重；$`W_c,v`$ 仍由上述确定参数计算。

**定理 40.2（聚簇展开的联合过程极限）。** 对任意固定 $`R\gt0`$，
两个实际实验、两种方向信息情形均对支持一致地满足

```math
\bigl(Y,L_M(\cdot),\mathcal C_M(\cdot)\bigr)
\Longrightarrow
\bigl(\mathcal W(\gamma),\mathcal W(V(\cdot)),
       \mathcal W(V(\cdot))-F_0(\cdot)\mathcal W(\gamma)\bigr)
```

式 (40.3)。

空间为 $`\mathbb R\times D[-R,R]^2`$，路径空间取 $`J_1`$ 拓扑，
$`\mathcal W`$ 是标准 Brownian 运动。末坐标与首坐标独立，
其分布为 $`\sqrt\gamma\,\mathcal B(F_0(\cdot))`$，其中 $`\mathcal B`$ 是标准 Brownian 桥。

此收敛可与定义 36.1 的任意固定紧阈值区间、有限个互异内点和固定紧容量区间同时成立：

```math
\left((X_{M,j})_{j=1}^d,U_M(\cdot),(R_{M,j}(\cdot))_{j=1}^d,
             Y,L_M(\cdot),\mathcal C_M(\cdot)\right)
\Longrightarrow
\left((G)_{j=1}^d,H(\cdot),(K_j(G+\cdot))_{j=1}^d,
 \mathcal W(\gamma),\mathcal W(V(\cdot)),
 \mathcal W(V(\cdot))-F_0(\cdot)\mathcal W(\gamma)\right).
```

式 (40.4)。

所有路径空间仍取乘积 $`J_1`$ 拓扑，$`\mathcal W`$ 独立于 $`G,H,K_1,\ldots,K_d`$。
第 36 章的 $`\mathcal P_{M,j}`$ 也可同时加入，并保留其原极限。
证明中的条件后验计算在均匀支持先验空间上解释；固定支持结论为整个对象的无条件分布收敛。
此外，展开尺度与中心满足

```math
v\sim\epsilon(1-\alpha)\sqrt\lambda,\qquad
\frac vw\longrightarrow0,\qquad
\frac{W_c-z_0}{v\sqrt\lambda}\longrightarrow\frac r{1-\alpha}\gt0.
```

式 (40.5)。

证明。由 (39.8)、(39.9)，$`\log(1/\epsilon)=O(Q^3)`$，故
$`(\alpha-P/Q)/\epsilon\to0`$。在 (39.18) 中除以 $`\epsilon Q`$ 得到
$`\Delta/(\epsilon Q)\to1-\alpha`$，证明 (40.5) 的第一式。
又有

```math
\frac vw\sim(1-\alpha)\epsilon\sqrt q\longrightarrow0,\qquad
W_c-z_0=\epsilon(k_0-l_0)+O(\epsilon^2\lambda),\qquad
k_0-l_0=r\lambda+O(1).
```

式 (40.6)。

这里 $`\epsilon\sqrt q=O(q^{3/2}/M)\to0`$，而 $`\lambda\to\infty`$。
其余两式给出 (40.5) 的最后一式。因此未补偿中心与精确中心的差在原窗口中消失，
在展开尺度上却发散；下文始终使用 $`W_c`$。
在计数直线上有精确恒等式

```math
\frac{W(k_0+tQ,l_0+tP)-W_c}{v}=\frac{tQ}{\sqrt\lambda}.
```

式 (40.7)。

先取正确方向。令 $`d_M(x)=\sum_{i\in J_x}p_i(1-p_i)`$、
$`d_J=\sum_{i\in J}p_i(1-p_i)`$。
第 39 章的计数直线隔离、固定块概率与相对尾界，使任意固定 $`x`$ 满足
$`d_M(x)/B^2\to V(x)`$ 依概率。
半无限区间的结论由固定有限区间逼近，再使用相对高斯尾界得到。
实际占据数的一行、两行比较及 $`p_i\to1/2`$ 的一致校准在此均保留；
它们不是把实际观测行替换成独立 Poisson 行。
方差时钟单调非减，极限连续。在固定有限网格上取收敛，再用单调性夹住网格间的值，得到

```math
\sup_{|x|\le R+1}\left|\frac{d_M(x)}{B^2}-V(x)\right|
\longrightarrow0,\qquad \frac{d_J}{B^2}\longrightarrow\gamma
\quad\text{依概率}.
```

式 (40.8)。

在校准独立标签律 $`\mathsf Q_M`$ 下，按递增得分揭示 $`J`$ 中的标签。
定义左尾、正向条带过程和右尾

```math
T_-^M=\frac1B\sum_{i\in J_{-R}}(\zeta_i-p_i),\qquad
D_M(x)=\frac1B\sum_{i\in J_x\setminus J_{-R}}(\zeta_i-p_i),
\quad -R\le x\le R,\qquad
T_+^M=\frac1B\sum_{i\in J\setminus J_R}(\zeta_i-p_i).
```

式 (40.9)。

三个对象相互独立；$`D_M`$ 是从零开始的右连续独立增量鞅，
其可预测方差时钟为 $`(d_M(x)-d_M(-R))/B^2`$。
等分标签必须整组跳跃。对展开位置位于 $`(-R,R]`$ 的得分组 $`E_z`$，
记 $`d_z=\sum_{i\in E_z}p_i(1-p_i)`$。
(40.8) 在稍大区间成立，连续极限因而使 $`\max_z d_z/B^2\to0`$。
在任何满足这些时钟极限的确定数据环境序列上，独立 Bernoulli 和的四阶矩界给出

```math
\sum_z\mathbb E_{\mathsf Q_M}|\Delta_zD_M|^4
\le3\left(\max_z\frac{d_z}{B^2}\right)\frac{d_J}{B^2}
    +\frac1{B^2}\frac{d_J}{B^2}\longrightarrow0.
```

式 (40.10)。

故最大跳幅平方的期望趋零，可预测方差时钟的最大跳跃也趋零。
$`V(x)-V(-R)`$ 连续且严格递增；以其反函数作确定时间变换，
为按半直线表述应用定理，在变换后的末时刻接上独立标准 Brownian 增量，
其可预测方差时钟便在每个紧时间区间趋于恒等时钟，新增部分无跳跃。
[Whitt 定理 2.1(ii)](../../../Library/Dynamics/whitt2007martingale.md)
给出极限后，再限制回原区间并逆变换，得到该条带的连续 Brownian 时间变换极限。
两侧尾变量由有界独立数组中心极限定理收敛，方差分别为
$`V(-R)`$ 和 $`\gamma-V(R)`$，并保持与整个条带独立。
因此辅助轮廓与完整端点共同收敛为
$`(\mathcal W(V(\cdot)),\mathcal W(\gamma))`$。
这一步既控制路径，也保留端点与路径的正确相关性。

后验转移始终使用一个完整并集。
先仅取 $`J`$，其方差为 $`O_{\mathbb P}(B^2)=o_{\mathbb P}(q)`$，补集保留 $`q`$ 量级方差。
(35.11) 给出完整标签向量的总变差趋零；(35.12) 对同一数据实现的全部子集同时成立，故

```math
\sup_{x\in\mathbb R}\frac1B
 \left|\sum_{i\in J_x}(\pi_i-p_i)\right|
\le\frac{C\sqrt{d_J}}B
 \left(\frac{d_J}{q}+\frac{\sqrt{d_J}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (40.11)。

端点也满足相同界。总变差的映射收缩与一致中心位移遂转移整个过程。
从任一数据子序列抽取使时钟、跳跃和中心界几乎处处成立的子序列，
在其确定环境上使用上述论证，得到联合条件律在有界 Lipschitz 距离中依概率趋于确定极限。
该距离有界，故取期望也成立。

映射 $`(y,l)\mapsto l-F_0y`$ 在连续极限处连续。
极限桥与端点的协方差为
$`V(x)-F_0(x)\gamma=0`$；它们联合高斯，因而独立。
桥的协方差为
$`\gamma[F_0(\min(x,y))-F_0(x)F_0(y)]`$，即 (40.3) 的 Brownian 桥分布。

为证明 (40.4)，固定排名截断 $`H_0`$，
将 $`J`$ 加入第 36 章覆盖全部阈值尾集和各边界两侧排名块的同一个并集 $`\mathcal U`$。
$`|J|=O_{\mathbb P}(B^2)=o_{\mathbb P}(q)`$，且

```math
d_{\mathcal U}=O_{\mathbb P}(q/\sqrt\lambda),\qquad
 d_{\mathcal U^c}\ge cq/2
```

式 (40.12)。

在概率趋一的事件上成立。
以 $`d_{\mathcal U}`$ 替换 (40.11) 右边括号内的 $`d_J`$，
新轮廓的全部中心位移仍一致趋零；原阈值和排名前缀的中心界也在各自尺度上保留。
所以一次完整向量比较同时转移所有坐标。

在乘积律下，取有限多个轮廓时刻、阈值时刻与排名时刻。
任意固定线性组合的最大单标签系数趋零，故有联合数组中心极限定理。
新轮廓或端点与旧阈值坐标的协方差绝对值，除以各自归一化后至多为

```math
O_{\mathbb P}\left(\frac{B}{b_M^\circ}\right)
=O_{\mathbb P}(Q^{-1/2})\longrightarrow0.
```

式 (40.13)。

与截断排名块的相同界为

```math
O_{H_0}\left(\frac{\sqrt q}{Bq^{1/4}}\right)
=O_{H_0}\left(\frac{\sqrt Q\,\lambda^{1/4}}{q^{1/4}}\right)
\longrightarrow0.
```

式 (40.14)。

即使新聚簇与排名块相交，此上界也成立。
先有联合高斯性，再由这些消失的交叉协方差得到
$`\mathcal W`$ 与原始 $`H,K_1,\ldots,K_d`$ 独立。
各过程的紧性给出乘积空间紧性。
确定的条件有界 Lipschitz 极限与数据原点的有界连续测试相乘，
使整个原始过程族共同独立于粗尺度原点。
最后按第 36 章加入共同原点、作随机平移、控制排名取整并去掉 $`H_0`$ 截断，
得到 (40.4) 及附加的 $`\mathcal P_{M,j}`$ 坐标。

全部集合、权重、中心及联合对象在共同支持置换下等变，
先验无条件联合分布因而等于每个固定支持下的分布。
实际比较界对支持一致，保留所述一致结论。
未知方向的全部坐标在同一个正确判决事件上与正确对齐版本相等，
其补事件概率为 $`O(q^{-1})`$，故整个联合结论一并转移。∎

## 追加锚（本行以下为增补区）

## 41. 临界算术网格上的高斯阶梯

**定义 41.1（保持幅度，改变计数网格）。** 固定定义 39.1 的同一个 $`r,\alpha,P_j,Q_j`$，
以及 $`\beta\in(1/2,1)`$、$`\vartheta\gt0`$。
把 (39.3) 中的 $`\lambda=Q^3`$ 换成 $`\lambda=\lfloor\vartheta Q^2\rfloor`$，
其余 $`N,M,k_0,l_0,z_0,q,\tau,\mathsf T`$ 按该式重新计算。
补偿参数、实际得分、窗口 $`J`$、计数直线 $`\mathcal L`$ 与精确后验仍按 (39.4) 定义。
令 $`W_c=W(k_0,l_0)`$，$`\Delta`$ 按 (39.18) 的精确得分差定义，并置

```math
B_0=\sqrt{q/\lambda},\qquad
c_0=\frac1{4\pi\sqrt{ab}},\qquad
c_t(\vartheta)=c_0\exp\left(-\frac{\kappa t^2}{2\vartheta}\right),\quad t\in\mathbb Z,
\qquad
\Gamma_\vartheta=\sum_{t\in\mathbb Z}c_t(\vartheta),\qquad
F_\vartheta(x)=\frac1{\Gamma_\vartheta}\sum_{t\le x}c_t(\vartheta).
```

式 (41.1)。

这里 $`a,b,\kappa`$ 保持 (39.2) 的固定值。对充分大下标，$`\Delta\gt0`$，定义

```math
Y_M^\vartheta=\frac1{B_0}\sum_{i\in J}(\mathbf1_{\{i\in S\}}-\pi_i),\qquad
L_M^\vartheta(x)=\frac1{B_0}\sum_{i\in J,\,W_i\le W_c+x\Delta}
                         (\mathbf1_{\{i\in S\}}-\pi_i),\qquad
C_M^\vartheta(x)=L_M^\vartheta(x)-F_\vartheta(x)Y_M^\vartheta.
```

式 (41.2)。

全部坐标使用同一实际数据、优先级和标签；未知方向时共同使用一次方向判决及工作正向权重。
另取相互独立的 $`G_t^\vartheta\sim N(0,c_t(\vartheta))`$，定义

```math
Y_\vartheta=\sum_{t\in\mathbb Z}G_t^\vartheta,\qquad
L_\vartheta(x)=\sum_{t\le x}G_t^\vartheta,\qquad
C_\vartheta(x)=L_\vartheta(x)-F_\vartheta(x)Y_\vartheta.
```

式 (41.3)。

**定理 41.2（相同端点尺度与不同路径结构）。** 定义 41.1 的参数最终合法，
(41.3) 的级数几乎处处绝对收敛。对每个固定 $`R\gt0`$，
两个实际实验、两种方向信息情形均对支持一致地满足

```math
(Y_M^\vartheta,L_M^\vartheta(\cdot),C_M^\vartheta(\cdot))
\Longrightarrow(Y_\vartheta,L_\vartheta(\cdot),C_\vartheta(\cdot))
\quad\text{于 }\mathbb R\times D[-R,R]^2.
```

式 (41.4)。

各路径空间取 $`J_1`$ 拓扑；$`R`$ 可以为整数。
$`Y_\vartheta\sim N(0,\Gamma_\vartheta)`$，$`C_\vartheta`$ 独立于 $`Y_\vartheta`$，
且与 $`\sqrt{\Gamma_\vartheta}\,\mathcal B(F_\vartheta(\cdot))`$ 同律，
其中 $`\mathcal B`$ 为标准 Brownian 桥。
该联合极限可同时加入第 36 章固定紧阈值区间和有限个固定紧容量曲线，
保留其原极限；整个新阶梯族独立于原始 $`G,H,K_1,\ldots,K_d`$。

另一方面，定义原窗口过程

```math
F_M^\vartheta(u)=\frac1{B_0}
 \sum_{\tau-w\lt W_i\le\tau+uw}(\mathbf1_{\{i\in S\}}-\pi_i),
\qquad -1\le u\le1.
```

式 (41.5)。

其端点仍收敛到 $`N(0,\Gamma_\vartheta)`$，但整个过程在 $`D[-1,1]`$ 的 $`J_1`$ 拓扑下不紧。
这里的端点归一化与第 38 章相同，不能据此推断单跳路径极限。

证明。新序列满足 $`\lambda\sim\vartheta Q^2`$，由取整得
$`z_0=\phi\lambda+O(1)`$、$`\log M=\phi\lambda/\beta+O(1)`$、
$`q=M^{1-\beta+o(1)}`$ 和 $`\tau=z_0+O(q^{-1})`$。
特别地，$`\lambda/\log M\to\beta/\phi`$，
$`(\lambda-\tau/\phi)/\sqrt{\log M}\to0`$，
$`q(\log M)^3/M\to0`$ 与 $`\lambda q^2/M\to0`$。
因此实际一行、两行及全信号向量比较仍满足各自条件。
固定幅度的信号增量为同一个非格点分布；整数 $`\lambda`$ 下的固定宽度定位仍由 Stone 定理给出。
算术误差 $`0\lt\alpha-P/Q\lt e^{-Q^4}`$ 对应的指数阶严格快于 $`\lambda`$，因此

```math
\frac{\lambda e^{-Q^4}}w\to0,\qquad
\frac{\epsilon\lambda}w\to0,\qquad
\frac1{qw}\to0,\qquad Qw\to0,\qquad
\frac{\alpha-P/Q}{\epsilon}\to0.
```

式 (41.6)。

在任意充分大的固定计数截断上，(39.10) 的非零整数分子仍给出 $`h/(2Q)`$ 的间隙。
分子为零恰好给出直线，其补偿与取整误差由 (41.6) 控制。
实际行尾界对全部 $`M`$ 行取并集，故窗口恰等于实际直线行的概率趋于一。
由此在新序列上得到隔离结论。
此外

```math
\Delta\sim\epsilon Q(1-\alpha)\gt0,\qquad
\frac{\Delta}{w}\to0,\qquad
\frac{W(k_0+tQ,l_0+tP)-W_c}{\Delta}=t.
```

式 (41.7)。

最后一式精确成立，因此展开后的跳点始终是整数。

在信号比较律下，对每个固定整数 $`t`$，两计数的均值偏差分别为
$`tQ+O(1)`$ 与 $`tP+O(1)`$。Stirling 展开给出

```math
\lambda Q_r\{(N_+,N_-)=(k_0+tQ,l_0+tP)\}
\longrightarrow\frac1{2\pi\sqrt{ab}}
                 \exp\left(-\frac{\kappa t^2}{2\vartheta}\right).
```

式 (41.8)。

这里网格没有趋于连续；不能把右边改成积分。
为对所有整数求和，在两计数均不小于各自均值一半的固定线性截断内，
Poisson 点概率界给出 $`C\lambda^{-1}\exp(-c t^2Q^2/\lambda)`$。
因为 $`Q^2/\lambda\to1/\vartheta`$，归一化后的界是固定可求和的高斯序列。
其余点由边缘 Poisson 指数尾界控制，即使乘以截断中的点数及 $`\lambda`$ 仍趋零。
截断外的总计数尾也有同样性质。
因此 (41.8) 可对整条直线、任意固定整数半线或固定整数块求和，且远端余项一致趋零。

在截断直线上 $`W=\tau+o(1)`$ 一致成立，精确换测度使背景与信号的混合贡献渐近相等。
两种比较律的截断尾分别控制后再乘以各自人口数。
实际一行、两行比较给出各组、半线和整窗的均值与方差界；
它们的正均值为 $`q/\lambda`$ 的固定比例，故相应占据数集中。
校准依然满足 $`\max_{i\in J}|p_i-1/2|\to0`$ 依概率，空集时取零。
若 $`J_t`$ 为第 $`t`$ 个实际直线计数组，便得到

```math
\frac1{B_0^2}\sum_{i\in J_t}p_i(1-p_i)\to c_t(\vartheta),\qquad
\frac{d_J}{B_0^2}\to\Gamma_\vartheta,
\qquad
\frac1{B_0^2}\sum_{i\in J,\,W_i\le W_c+x\Delta}p_i(1-p_i)
 \to\sum_{t\le x}c_t(\vartheta)
```

式 (41.9)。

最后一式对每个固定实数 $`x`$ 成立，包括整数，均为依概率收敛。
实际计数组在整数端点的包含约定与右端完全一致。

极限级数满足
$`\sum_t\mathbb E|G_t^\vartheta|=\sqrt{2/\pi}\sum_t\sqrt{c_t(\vartheta)}\lt\infty`$，
故绝对收敛几乎处处成立。其路径在紧区间只有有限个整数跳点，且为右连续。

先在同一校准乘积律下证明过程收敛。
对 $`[-R,R]`$，把所有标签分成左初始尾、区间 $`(-R,R]`$ 内的有限个完整整数计数组，
以及右终端尾。这些组互不相交。
每个单标签系数至多为 $`1/B_0\to0`$；(41.9) 给出各组及两尾的方差极限。
有界独立数组中心极限定理因此给出整个有限向量的联合高斯极限，且各组独立。
由这个向量到阶梯路径和完整端点的线性映射，在一致范数下连续，
因为所有跳点都是同一组固定整数。
这证明辅助过程的联合收敛，包括整数紧区间端点。
每个完整计数组具有正的极限方差，不能在这里使用要求最大组跳消失的连续极限定理。

$`d_J=O_{\mathbb P}(q/\lambda)=o_{\mathbb P}(q)`$，补集保留 $`q`$ 量级方差。
对整窗标签向量使用一次 (35.11) 的比较；(35.12) 同时控制全部子集中心，并给出

```math
\sup_{E\subseteq J}\frac1{B_0}
 \left|\sum_{i\in E}(\pi_i-p_i)\right|
\le\frac{C\sqrt{d_J}}{B_0}
 \left(\frac{d_J+\sqrt{d_J}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (41.10)。

总变差映射收缩及此一致位移转移完整端点和路径。
确定环境的子序列论证给出后验条件律的有界 Lipschitz 收敛，
其有界性允许再取先验期望。
极限协方差是
$`\mathrm{Cov}(L_\vartheta(x),L_\vartheta(y))=\Gamma_\vartheta F_\vartheta(\min(x,y))`$，
$`\mathrm{Cov}(L_\vartheta(x),Y_\vartheta)=\Gamma_\vartheta F_\vartheta(x)`$。
联合高斯投影即得到桥的协方差及其与端点的独立性。
对有限固定跳点作此投影同样保持一致范数连续；这证明 (41.4)。

加入第 36 章坐标时，使用覆盖旧阈值集、全部截断排名前缀和新 $`J`$ 的一个并集。
其方差仍为 $`O_{\mathbb P}(q/\sqrt\lambda)`$，补集保留 $`q`$ 量级方差，
其大小除以 $`q`$ 趋于 $`1/2`$。
(41.10) 用该并集方差替换括号中的 $`d_J`$ 后仍趋零，旧坐标的中心界亦保留。
在乘积律下，新坐标与旧阈值或细尺度坐标的归一化交叉协方差分别至多为

```math
O_{\mathbb P}\left(\frac{B_0}{b_M^\circ}\right)
=O_{\mathbb P}(\lambda^{-1/4}),\qquad
O_{H_0}\left(\frac{\sqrt q}{B_0q^{1/4}}\right)
=O_{H_0}\left(\frac{\sqrt\lambda}{q^{1/4}}\right),
```

式 (41.11)。

二者均趋零。任意有限坐标的共同标签数组先给出联合高斯性，再给出这些独立关系。
把上述左尾、有限整数组和右尾的系数向量与旧过程共同处理。
联合数组极限与旧过程紧性先给出这个有限向量和旧过程的联合收敛，
再应用固定阶梯重建及桥投影的一致范数连续性。
因此整数紧区间端点与完整终端尾同样保留，无须在不连续跳点使用一般的评价连续性。
确定的后验条件极限按有界连续原点测试和有界 Lipschitz 过程测试加入数据原点，
再作旧排名过程的平移、取整和截断移除，即得所述联合扩展。

最后取外窗口中的三个确定位置，对应 $`t=-1,0,1`$。
由隔离和 (41.7)，它们严格递增并都趋于内部零点。
两个相邻过程增量恰为第零组与第一组的中心化标签和；其联合极限是独立的
$`N(0,c_0)`$ 与 $`N(0,c_1(\vartheta))`$，两方差严格为正。
因此两增量绝对值同时大于固定正数的概率有严格正的极限。
第 39 章使用的内部三点分割振荡判据便排除了 $`J_1`$ 紧性，
而整窗端点的方差极限仍为有限的 $`\Gamma_\vartheta`$。

以上后验计算均在均匀支持先验空间进行。
共同置换等变把整个无条件律转移到每个固定支持，实际比较界保留支持一致性。
一个共同正确方向事件使全部工作坐标逐项一致，补事件概率为 $`O(q^{-1})`$，
所以过程极限、独立关系和外窗口不紧性一并转移。∎

## 追加锚（本行以下为增补区）

## 42. 收缩噪声的 Sobolev 极限与总变差发散

**定义 42.1（同一聚簇的带符号测度）。** 采用定义 39.1 的固定幅度、固定
$`\beta\in(1/2,1)`$ 及原序列 $`\lambda=Q^3`$，并保留第 40 章的同一数据、标签、
精确后验、窗口 $`J`$、完整端点 $`Y_M`$ 和轮廓 $`L_M`$。
置

```math
\delta_M=\frac Q{\sqrt\lambda}=Q^{-1/2},\qquad
B_M=\sqrt{\frac q{Q\sqrt\lambda}},\qquad
u_i=\frac{W_i-\tau}w,\qquad
\mu_M=\frac1{B_M}\sum_{i\in J}
       (\mathbf1_{\{i\in S\}}-\pi_i)\delta_{u_i}.
```

式 (42.1)。

$`\delta_x`$ 表示位置 $`x`$ 的单位点质量。把 $`(-1,1]`$ 嵌入圆周
$`\mathbb T_4=\mathbb R/(4\mathbb Z)`$，相同得分的标签先合成一个原子。
因此 $`\mu_M(\mathbb T_4)=Y_M`$，其总变差范数是完整得分组的中心化标签和的绝对值之和。
未知方向时，全部工作坐标共同使用第 40 章的一次方向判决。

固定 $`s\gt1/2`$。实 Hilbert 空间 $`H^{-s}(\mathbb T_4)`$ 取满足共轭对称条件的
加权平方可和 Fourier 序列，并采用如下范数约定：

```math
\widehat\nu(k)=\int_{\mathbb T_4}e^{-\pi iku/2}\,d\nu(u),\qquad
\|\nu\|_{-s}^2=\sum_{k\in\mathbb Z}(1+k^2)^{-s}|\widehat\nu(k)|^2,
\qquad \widehat\nu(-k)=\overline{\widehat\nu(k)}.
```

式 (42.2)。

此约定不另含圆周长度因子。有限实带符号测度按其 Fourier 系数嵌入该空间。
仍取 $`\rho(x)=c_0e^{-\kappa x^2/2}`$，其中
$`c_0=1/(4\pi\sqrt{ab})`$，$`\kappa=1/a+\alpha^2/b`$，$`D=ab\kappa`$。

**定理 42.2（同一高斯点质量与发散的组变差）。** 对两个实际实验及两种方向信息情形，
以下结论均对固定支持一致成立：

```math
\|\mu_M-Y_M\delta_0\|_{-s}\longrightarrow0\quad\text{依概率},\qquad
\sqrt{\delta_M}\,\|\mu_M\|_{\mathrm{TV}}
\longrightarrow C_*:=\sqrt{\frac2\pi}\frac{(ab)^{1/4}}{\sqrt D}
\quad\text{依概率}.
```

式 (42.3)。

它们与定理 40.2 的完整端点、任意固定紧区间轮廓和桥，以及其中有限个原有场坐标联合成立。
特别地，在第 40 章的同一个 Brownian 实现中，

```math
(Y_M,L_M(\cdot),\mu_M,\sqrt{\delta_M}\|\mu_M\|_{\mathrm{TV}})
\Longrightarrow
(\mathcal W(\gamma),\mathcal W(V(\cdot)),
 \mathcal W(\gamma)\delta_0,C_*),\qquad
\gamma=\frac1{2\sqrt{2\pi}\sqrt D}.
```

式 (42.4)。

测度坐标使用 $`H^{-s}`$ 范数拓扑，轮廓使用固定紧区间上的 $`J_1`$ 拓扑。
点质量的幅度就是完整端点，并非另取的独立正态变量。
同时 $`\|\mu_M\|_{\mathrm{TV}}/Q^{1/4}\to C_*\gt0`$ 依概率。
此处不宣称实际矩收敛；若 $`s\le1/2`$，非零点质量不属于 (42.2) 的空间，
因而不能用同一空间表述 (42.4)。

证明。取第 39 章的共同全行计数截断事件，其概率趋于一。
该事件上，$`J`$ 恰为直线计数组，任意出现的组可写成
$`(k_0+tQ,l_0+tP)`$，$`t\in\mathbb Z`$，并且

```math
x_{M,t}=t\delta_M,\qquad
u_{M,t}=\frac{W_c+t\Delta-\tau}w,\qquad
\max_{i\in J}|u_i|\le a_M\longrightarrow0.
```

式 (42.5)。

这里 $`a_M`$ 可取确定量：截断上原始得分差为
$`O(\lambda e^{-Q^4})`$，补偿差为 $`O(\epsilon\lambda)`$，取整差为 $`O(q^{-1})`$，
它们除以 $`w`$ 全部趋零。$`\Delta\gt0`$ 保证不同计数组对应不同原子。
截断外事件只用于概率误差，不据此转移无界统计量的期望。

记 $`K_s=\sum_k(1+k^2)^{-s}\lt\infty`$。直接由 Fourier 系数得到

```math
\|\delta_u\|_{-s}^2=K_s,\qquad
\omega_s(a):=\sup_{|u|\le a}\|\delta_u-\delta_0\|_{-s}^2
=\sup_{|u|\le a}\sum_{k\in\mathbb Z}(1+k^2)^{-s}
                  |e^{-\pi iku/2}-1|^2\longrightarrow0
\quad(a\downarrow0).
```

式 (42.6)。

最后一步对每个有限频率集用连续性，再用 $`4(1+k^2)^{-s}`$ 控制余项。
这也证明点质量映射可测且范数连续；$`s\le1/2`$ 时同一 Fourier 和发散。

给定数据，在校准乘积律 $`\mathsf Q_M`$ 下令标签为相互独立的
$`\zeta_i\sim\mathrm{Bernoulli}(p_i)`$。
独立中心化使 Hilbert 内积的交叉项消失，因此在 (42.5) 的事件上

```math
\mathbb E_{\mathsf Q_M}\left\|
 \frac1{B_M}\sum_{i\in J}(\zeta_i-p_i)(\delta_{u_i}-\delta_0)
 \right\|_{-s}^2
\le\frac{d_J}{B_M^2}\omega_s(a_M)\longrightarrow0
\quad\text{依概率}.
```

式 (42.7)。

用到了 $`d_J/B_M^2\to\gamma`$。条件 Markov 不等式使相应条件概率趋零；
概率的有界性允许取数据期望。这是辅助乘积律下的二阶矩计算。

精确中心的转移同时控制所有系数。令
$`e_M=(d_J+\sqrt{d_J})/q+q^{-1/2}=o_{\mathbb P}(1)`$。
把 (35.12) 分别用于固定环境中 $`\pi_i-p_i`$ 为正和为负的子集，得到

```math
\sum_{i\in J}|\pi_i-p_i|\le2C\sqrt{d_J}\,e_M,\qquad
\frac1{B_M}\sum_{i\in J}|\pi_i-p_i|\longrightarrow0
\quad\text{依概率}.
```

式 (42.8)。

该不等式允许子集依赖数据，因为原界对固定环境的全部子集同时成立。
由 (42.6)，(42.8) 控制测度中心和端点点质量中心的 Hilbert 位移。
再将整窗标签向量一次性从 $`\mathsf Q_M`$ 转移到精确后验，
总变差比较只用于 (42.7) 所控制的事件概率，即证明 (42.3) 的第一式。

为证明第二式，需要逐组占据数而不仅是累计方差。
令 $`C_{M,t}`$ 为第 $`t`$ 个直线计数组的实际行数，
$`m_{M,t}=qQ_r(E_t)+(M-q)Q_{-\epsilon}(E_t)`$ 为其比较混合均值。
对每个固定 $`R\gt0`$，一致 Stirling 展开与截断上的精确换测度给出

```math
\sup_{|x_{M,t}|\le R}
 \left|\frac{m_{M,t}}{4(q/\lambda)\rho(x_{M,t})}-1\right|\to0.
```

式 (42.9)。

该范围内全部计数最终合法。置 $`\eta_M=(\log M)^3/(2M)`$。
实际一行、两行比较对这些随参数变化的确定事件仍一致成立，故对任意充分大的固定 $`D_0`$，

```math
|\mathbb E C_{M,t}-m_{M,t}|
 \le C\eta_Mm_{M,t}+CM^{1-D_0},\qquad
\mathrm{Var}(C_{M,t})
 \le C\bigl(m_{M,t}+\eta_Mm_{M,t}^2+M^{2-D_0}\bigr).
```

式 (42.10)。

紧区间组数为 $`O_R(\delta_M^{-1})`$，而最小均值至少为 $`c_Rq/\lambda`$。
Chebyshev 不等式及并集界适用，因为
$`\delta_M^{-1}(\lambda/q+\eta_M+M^{2-D_0}\lambda^2/q^2)\to0`$。
因此逐组相对误差的最大值依概率趋零。
同组概率 $`p_t`$ 相同，且校准给出整个 $`J`$ 上 $`p_t\to1/2`$ 一致成立。
记 $`d_{M,t}=C_{M,t}p_t(1-p_t)`$，利用 $`B_M^2\delta_M=q/\lambda`$ 得

```math
\sup_{|x_{M,t}|\le R}
 \left|\frac{d_{M,t}}{B_M^2\delta_M\rho(x_{M,t})}-1\right|
 \longrightarrow0\quad\text{依概率}.
```

式 (42.11)。

给定数据，令 $`S_{M,t}=\sum_{i\in J_t}(\zeta_i-p_i)`$。
不同组在 $`\mathsf Q_M`$ 下独立，且紧区间内最小 $`d_{M,t}`$ 趋于无穷。
归一化单标签增量至多为 $`d_{M,t}^{-1/2}`$，有界独立数组中心极限定理给出组和的正态极限。
归一化组和的二阶矩恒为一，使其绝对值一致可积。
若绝对一阶矩收敛在紧区间组中不一致，选取一列失败的组，
上述两条界仍成立，从而得到矛盾。因此

```math
\sup_{|x_{M,t}|\le R}
 \left|\frac{\mathbb E_{\mathsf Q_M}|S_{M,t}|}{\sqrt{d_{M,t}}}
       -\sqrt{\frac2\pi}\right|\longrightarrow0
\quad\text{依概率}.
```

式 (42.12)。

(42.11) 与网格 $`\delta_M`$ 的 Riemann 和遂给出

```math
\frac{\sqrt{\delta_M}}{B_M}
 \sum_{|x_{M,t}|\le R}\mathbb E_{\mathsf Q_M}|S_{M,t}|
\longrightarrow\sqrt{\frac2\pi}\int_{-R}^R\sqrt{\rho(x)}\,dx,
\qquad
\mathrm{Var}_{\mathsf Q_M}\left(
 \frac{\sqrt{\delta_M}}{B_M}\sum_{|x_{M,t}|\le R}|S_{M,t}|
\right)\le\frac{\delta_Md_J}{B_M^2}\to0
```

式 (42.13)。

均为依概率结论。方差界使用组间独立性及
$`\mathrm{Var}|S_{M,t}|\le\mathbb E S_{M,t}^2=d_{M,t}`$。

以下尾部界保证可以令 $`R\to\infty`$。
只计入固定线性计数截断中的确定直线组。
当两计数均不小于各自信号均值的一半时，Poisson 点概率界及实际一行比较给出

```math
\mathbb E C_{M,t}\le C\frac q\lambda e^{-c x_{M,t}^2}+CM^{1-D_0}.
```

式 (42.14)。

背景项通过截断直线上的 $`W=\tau+o(1)`$ 换测度，不能在未截断尾部直接使用此近似。
由 $`\mathbb E_{\mathsf Q_M}|S_{M,t}|\le\sqrt{C_{M,t}}/2`$ 及 Jensen 不等式，
(42.14) 的高斯项在所需归一化下至多贡献

```math
C\delta_M\sum_{|t\delta_M|\gt R}e^{-c(t\delta_M)^2/2}.
```

式 (42.15)。

其先取样本上极限再令 $`R\to\infty`$ 为零。
截断中总组数为 $`O(\lambda/Q)`$；(42.14) 的加性误差贡献至多为
$`C(\lambda/Q)\sqrt{\delta_M}M^{(1-D_0)/2}/B_M=o(1)`$。
若某个计数低于其均值一半，信号边缘尾界为 $`e^{-c\lambda}`$，
换测度后的混合均值至多 $`Cqe^{-c\lambda}+CM^{1-D_0}`$。
这些组的平方根和贡献至多为 $`C\lambda e^{-c\lambda/2}+o(1)`$，
因为 $`\sqrt{\delta_M}\sqrt q/B_M=Q`$。
截断外则使用全行事件的 $`o(1)`$ 概率误差。
于是条件 Markov 不等式和上述数据期望界证明

```math
\lim_{R\to\infty}\limsup_M
 \mathbb E\left[\frac{\sqrt{\delta_M}}{B_M}
   \sum_{\substack{|x_{M,t}|\gt R\\\text{截断内}}}
        \mathbb E_{\mathsf Q_M}|S_{M,t}|\right]=0.
```

式 (42.16)。

这是平方根强度尾界，不能由累计方差收敛单独推出。
与 (42.13) 合并，辅助组变差依概率收敛到
$`\sqrt{2/\pi}\int_{\mathbb R}\sqrt{\rho(x)}\,dx`$。
由高斯积分及 $`D=ab\kappa`$，

```math
\int_{\mathbb R}\sqrt{\rho(x)}\,dx
=2\sqrt{\frac\pi\kappa}\sqrt{c_0}
=\frac{(ab)^{1/4}}{\sqrt D}.
```

式 (42.17)。

隔离事件上各组位置不同，故上述组绝对值之和恰是辅助带符号测度的总变差。
一次整窗后验比较转移其收敛事件，(42.8) 则控制替换精确中心引起的总变差误差。
再乘 $`\sqrt{\delta_M}`$ 仍趋零，证明 (42.3) 的第二式。

两条依概率近似与第 40 章的完整联合极限用 Slutsky 定理结合，得到 (42.4) 及桥、原有场的扩展。
所有条件乘积律和后验论证先在均匀支持先验空间进行。
共同置换等变使整个无条件律等于每个固定支持的律；实际行界保持支持一致性。
一次共同方向判决的正确事件同时保留测度、组变差和全部既有坐标，
其补事件概率趋零，因此两种方向信息情形同样成立。∎

## 追加锚（本行以下为增补区）
