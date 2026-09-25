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
