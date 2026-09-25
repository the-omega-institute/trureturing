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
