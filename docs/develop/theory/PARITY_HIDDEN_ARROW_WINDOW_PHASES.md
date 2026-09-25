# 隐藏箭头的微观窗口相位

## 45. 逼近误差可见时的微观窗口重开

**定义 45.1（逼近尾与更晚的采样强度）。** 保持[后验阈值卷定义 39.1](PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)的同一个
$`r,\alpha,P_j,Q_j`$，固定 $`\beta\in(1/2,1)`$，记

```math
\eta_j=\alpha-P_j/Q_j,\qquad
L_j=\log(1/\eta_j),\qquad d=\frac{\phi(1-\beta)}\beta,\qquad
\lambda_j=\left\lfloor\frac{2L_j}d\right\rfloor.
```

式 (45.1)。

也允许把最后一个等式换成任意确定正整数序列
$`\lambda_j=2L_j/d+O(1)`$。用该强度重新计算 (39.3) 的全部参数，
保留实际得分、窗口、先验和后验的定义。以下只取参数合法的充分大下标，并省略下标 $`j`$。
令

```math
\chi_j=\eta_j\sqrt{q_j},\qquad B_M=\sqrt{\frac q{Q\sqrt\lambda}},\qquad
c_M=\frac{W(k_0,l_0)-\tau}{w},\qquad
c_0=\frac1{4\pi\sqrt{ab}},\qquad
V_\chi(u)=c_0\int_{-1/(h\chi)}^{u/(h\chi)}e^{-\kappa x^2/2}\,dx,
\quad -1\le u\le1.
```

式 (45.2)。

这里 $`h,a,b,\kappa`$ 均为 (39.2) 的固定常数。
每个 $`V_\chi`$ 连续且严格递增，$`V_\chi(-1)=0`$。
定义原微观窗口上的过程、标准化端点和端点投影

```math
F_M(u)=\frac1{B_M}\sum_{\tau-w\lt W_i\le\tau+uw}
                   (\mathbf1_{\{i\in S\}}-\pi_i),\qquad
T_M=\frac{F_M(1)}{\sqrt{V_{\chi_j}(1)}},\qquad
C_M(u)=F_M(u)-\frac{V_{\chi_j}(u)}{V_{\chi_j}(1)}F_M(1).
```

式 (45.3)。

全部坐标使用同一实际数据与标签；未知方向时仍共同使用一次方向判决和工作正向权重。

**定理 45.2（隔离直线中的连续高斯路径）。** 定义 45.1 的参数最终合法，
存在固定 $`0\lt\chi_-\lt\chi_+\lt\infty`$，使充分大下标均满足

```math
\chi_-\le\chi_j\le\chi_+,\qquad
\lambda_j\sim\frac{2\log10}{d}Q_j^5,\qquad
\frac{\lambda_j}{Q_j^2}\longrightarrow\infty.
```

式 (45.4)。

两个实际平稳实验、两种方向信息情形均对支持一致地具有以下性质。
对任何满足 $`\chi_j\to\chi\in(0,\infty)`$ 的子序列，

```math
(F_M,T_M,C_M)\Longrightarrow
\left(W(V_\chi(\cdot)),\frac{W(V_\chi(1))}{\sqrt{V_\chi(1)}},
W(V_\chi(\cdot))-\frac{V_\chi(\cdot)}{V_\chi(1)}W(V_\chi(1))\right)
\quad\text{于 }D[-1,1]\times\mathbb R\times D[-1,1].
```

式 (45.5)。

$`W`$ 是同一个标准 Brownian 运动，各路径空间取 $`J_1`$ 拓扑。
右端第三坐标与第二坐标独立，并与
$`\sqrt{V_\chi(1)}\,\mathcal B(V_\chi(\cdot)/V_\chi(1))`$ 同律，
其中 $`\mathcal B`$ 为标准 Brownian 桥。
沿完整序列，$`T_M\Longrightarrow N(0,1)`$，路径族 $`F_M,C_M`$ 都是
$`C`$-紧的，即紧且所有趋于无穷下标的弱收敛子序列极限几乎处处连续。
不要求 $`\chi_j`$ 本身收敛，也不主张取整能实现任意预先指定的 $`\chi`$。

该结论使用原来的 $`u=(W-\tau)/w`$ 窗口坐标，没有再放大一个较小的补偿尺度。
它不满足第 44 章的强度上界，因此与该章的充要条件相容。

证明。定义 39.1 的正尾满足

```math
\eta_j=10^{-Q_j^5}(1+o(1)),\qquad
L_j=(\log10)Q_j^5+o(1),\qquad
\log q=d\lambda+O(1),\qquad
\log\chi_j=-L_j+\tfrac12d\lambda_j+O(1)=O(1).
```

式 (45.6)。

第一式来自尾和的首项，下一项与它的比趋零。
最后一式同时给出 $`\chi_j`$ 的正下界与有限上界，而不把有界的取整误差当作趋零。
又有 $`\log M=\phi\lambda/\beta+O(1)`$、$`z_0=\phi\lambda+O(1)`$、
$`\tau=z_0+O(q^{-1})`$，所以参数合法、内在临界偏移趋零，且
$`q(\log M)^3/M\to0`$、$`\lambda q^2/M\to0`$。
实际一行、两行比较和全局后验校准的假设因而仍成立。
特别是 $`\lambda\asymp\log M`$，而 $`q`$ 比 $`Q,\lambda`$ 的任意固定幂更快增长。

补偿与逼近尾的相对大小在此发生变化：

```math
\epsilon=\exp(-\phi\lambda+O(1)),\qquad
\frac\epsilon\eta
=\exp\left[\left(1-\frac{2\phi}d\right)L+O(1)\right]\longrightarrow0,
\qquad \frac{2\phi}d=\frac{2\beta}{1-\beta}\gt2.
```

式 (45.7)。

相邻直线点的精确得分差及中心位置满足

```math
\Delta=hQ\eta+\epsilon(Q-P)+O(\epsilon^2Q)\sim hQ\eta\gt0,\qquad
|c_M|=O\left(\epsilon\sqrt{\lambda q}+\frac1{\sqrt{q\lambda}}\right)
\longrightarrow0,\qquad
\ell_j:=\frac{\Delta\sqrt q}{Q}=h\chi_j(1+o(1)).
```

式 (45.8)。

中心估计利用了 (45.7) 的指数余量，它强于仅有 $`\epsilon/\eta\to0`$。
令 $`x_t=tQ/\sqrt\lambda`$，直线点的位置精确满足

```math
u_t:=\frac{W(k_0+tQ,l_0+tP)-\tau}{w}=c_M+\ell_jx_t,
\qquad
\frac Q{\sqrt\lambda}\longrightarrow0,\qquad
u_{t+1}-u_t=\ell_j\frac Q{\sqrt\lambda}\longrightarrow0.
```

式 (45.9)。

因此直线仍具有细网格，但整条相关直线不再压在外窗口的零点上。

为排除非直线点，在固定充分大的截断 $`k+l\le C\lambda`$ 内使用 (39.10)。
有

```math
Q\lambda\eta\to0,\qquad Q\epsilon\lambda\to0,\qquad
Qw=\frac{Q\sqrt\lambda\,\eta}{\chi_j}\to0,\qquad Q/q\to0.
```

式 (45.10)。

故非零整数分子给出的 $`h/(2Q)`$ 间隙仍超过窗口宽度、补偿和取整误差。
实际行尾界对全部 $`M`$ 行取并集，得到公共截断事件的概率趋于一。
在该事件上，窗口里的全部行均在直线上，但只保留满足
$`-1\lt c_M+\ell_jx_t\le1`$ 的那一段；并非整条直线都进入窗口。
由 (45.4)、(45.8)，所有这些 $`x_t`$ 都在一个固定有界区间内，
相应计数最终非负并处于公共截断中。

以下先沿 $`\chi_j\to\chi`$ 的子序列证明过程极限。
信号比较 Poisson 律在每个固定有界 $`x_t`$ 区间内一致满足

```math
Q_r\{(N_+,N_-)=(k_0+tQ,l_0+tP)\}
=\frac{1+o(1)}{2\pi\lambda\sqrt{ab}}e^{-\kappa x_t^2/2}.
```

式 (45.11)。

这是二维 Stirling 展开，偏差为 $`O(\sqrt\lambda)`$，取整误差有界，
$`P/Q\to\alpha`$；不向某个固定宽度局部极限定理代入变化的窗口。
对任意固定 $`u\in[-1,1]`$，令
$`J(u)=\{i:\tau-w\lt W_i\le\tau+uw\}`$。
式 (45.9) 将它的直线参数变为
$`(-1-c_M)/\ell_j\lt x_t\le(u-c_M)/\ell_j`$。
网格 Riemann 和给出该区间的信号质量；一个端点计数组在归一化后只有
$`O(Q/\sqrt\lambda)=o(1)`$ 的质量，故严格下端点与非严格上端点都被保留。

在窗口中 $`W=\tau+O(w)`$，精确换测度使背景与信号的人口加权主项相等。
两种比较律的截断外余项分别取为足够高次的多项式小量后，再乘以人口数。
实际一行、两行比较因此给出所有固定前缀的占据数集中。
校准使窗口内 $`p_i\to1/2`$ 一致成立。记
$`d_M(u)=\sum_{i\in J(u)}p_i(1-p_i)`$，得到

```math
\frac{|J(u)|}{B_M^2}\longrightarrow4V_\chi(u),\qquad
\frac{d_M(u)}{B_M^2}\longrightarrow V_\chi(u)
\quad\text{依概率},\qquad
\sup_{-1\le u\le1}\left|\frac{d_M(u)}{B_M^2}-V_\chi(u)\right|
\longrightarrow0\quad\text{依概率}.
```

式 (45.12)。

最后一步由单调性和连续极限在有限细分网上夹逼得到。
特别地 $`|J|=O_{\mathbb P}(B_M^2)=o_{\mathbb P}(q)`$，
$`d_J=O_{\mathbb P}(B_M^2)=o_{\mathbb P}(q)`$，补集保留 $`q`$ 量级的方差。
这些是实际环境中的辅助方差估计，没有断言实际噪声矩收敛。

固定好数据，在同一个校准乘积律下按增加的得分揭示完整计数组。
归一化前缀和是从 $`u=-1`$ 的零值开始的有限平方可积鞅。
(45.12) 与 $`V_\chi`$ 的连续性使最大整组方差除以 $`B_M^2`$ 趋零。
若 $`S_g`$ 为一个整组的中心化标签和、$`d_g`$ 为其方差，则独立 Bernoulli 四阶矩界给出

```math
\sum_g\mathbb E_{\mathsf Q_M}(S_g/B_M)^4
\le 3\left(\max_g\frac{d_g}{B_M^2}\right)\frac{d_J}{B_M^2}
    +\frac{d_J}{B_M^4}\longrightarrow0.
```

式 (45.13)。

因此预见方差的最大跳跃与鞅的期望最大平方跳跃都趋零。
对极限时钟使用确定的逆映射，并在终点后接独立 Brownian 运动，
如第 40 章的半直线构造，即可逐项满足
[Whitt 定理 2.1(ii)](../../../Library/Dynamics/whitt2007martingale.md) 的线性时钟条件。
再限制回原区间，得到辅助过程趋于 $`W(V_\chi(\cdot))`$，极限连续。
这里处理的是整个同分组的跳跃，而非仅检查单标签系数。

对全部 $`J=J(1)`$ 使用一次后验标签向量比较，合法的补集计数与方差条件
由 $`|J|=o_{\mathbb P}(q)`$ 及全局校准给出。
精确中心另用 (35.12)，同时对所有 $`E\subseteq J`$ 有

```math
\sup_{E\subseteq J}\frac1{B_M}
 \left|\sum_{i\in E}(\pi_i-p_i)\right|
\le\frac{C\sqrt{d_J}}{B_M}
 \left(\frac{d_J+\sqrt{d_J}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (45.14)。

完整向量比较转移一次路径事件或有界路径测试，该式再转移所有前缀的中心。
确定环境的子序列论证给出后验条件律在有界 Lipschitz 距离下依概率趋于
$`W(V_\chi)`$ 的确定律。其有界性允许再取先验期望。
没有使用精确后验鞅，也没有通过总变差转移无界矩。

沿所取子序列，$`V_{\chi_j}\to V_\chi`$ 一致，且 $`V_\chi(1)\gt0`$。
端点评价和相应线性投影在连续极限处连续，故得到 (45.5)。
高斯投影的协方差计算给出桥的协方差

```math
V_\chi(\min(u,v))-
 \frac{V_\chi(u)V_\chi(v)}{V_\chi(1)},\qquad
\mathrm{Cov}\left(W(V_\chi(u))-
 \frac{V_\chi(u)}{V_\chi(1)}W(V_\chi(1)),\ W(V_\chi(1))\right)=0.
```

式 (45.15)。

联合高斯性随后给出桥与端点的独立性，二者并非从不同的标签实现取出。

最后考虑完整序列。任意趋于无穷的下标序列都可进一步选取
$`\chi_j`$ 收敛于 $`[\chi_-,\chi_+]`$ 的子序列。
上述论证在每一条这样的子序列上给出连续高斯路径极限，故原路径族紧且所有弱极限连续。
同理每一条子序列都存在标准化端点趋于 $`N(0,1)`$ 的进一步子序列，
于是完整序列的 $`T_M`$ 也趋于该同一分布。
桥的极限同样连续，因而其路径族也为 $`C`$-紧。
该论证保留了确定相位的取整振荡，而没有假定它消失。

所有条件后验计算都在均匀固定基数先验空间进行。
整个过程、精确中心、端点及桥对共同支持置换等变，故其无条件联合律
等于任意固定支持下的联合律。实际估计具有支持一致性。
同一个正确方向事件使全部工作坐标与正确对齐坐标逐项相同，补事件概率为
$`O(q^{-1})`$；因此相等耦合将全部弱极限与紧性结论一并转移。
这完成两种实际实验和两种方向信息情形下的证明。∎

## 追加锚（本行以下为增补区）

## 46. 有限窗口网格与紧区间端点的跳跃障碍

**定义 46.1（有限间距的更晚窗口）。** 保持[后验阈值卷定义 39.1](PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)的同一个固定振幅及
$`P_j,Q_j,\alpha`$，固定 $`\beta\in(1/2,1)`$，令

```math
\eta_j=\alpha-P_j/Q_j,\quad L_j=\log(1/\eta_j),\quad
d=\frac{\phi(1-\beta)}\beta,\quad A=\frac{2\log10}{d},\qquad
\lambda_j=\frac{2L_j}{d}+\frac3d\log Q_j+b_j\in\mathbb N,
\quad \sup_j|b_j|\lt\infty.
```

式 (46.1)。

用该强度重新计算 (39.3) 的所有参数，只取最终合法的下标。
相邻直线点的精确补偿得分差仍记为 $`\Delta`$。定义

```math
B_{0,M}=\sqrt{q/\lambda},\qquad
c_j=\frac{W(k_0,l_0)-\tau}{w},\qquad
\sigma_j=\frac\Delta w,\qquad u_{j,t}=c_j+t\sigma_j,\qquad
c_0=\frac1{4\pi\sqrt{ab}}.
```

式 (46.2)。

原窗口的精确中心过程为

```math
F_M(u)=B_{0,M}^{-1}\sum_{\tau-w\lt W_i\le\tau+uw}
               (\mathbf1_{\{i\in S\}}-\pi_i),\qquad -1\le u\le1.
```

式 (46.3)。

仍使用同一实际数据、标签与精确后验；未知方向时，所有坐标共用一次方向判决。

**定理 46.2（有限高斯网格与端点充要条件）。** 定义 46.1 的参数最终合法，且

```math
\lambda_j\sim A Q_j^5,\qquad c_j\longrightarrow0,
\qquad 0\lt\sigma_-\le\sigma_j\le\sigma_+\lt\infty
```

式 (46.4)。

对充分大下标成立，其中上下界为固定常数。
可取一个固定整数 $`K`$，使所有满足 $`-1\lt u_{j,t}\le1`$ 的整数均有
$`|t|\le K`$。令

```math
I_j=\{t\in\mathbb Z:|t|\le K,\ -1\lt u_{j,t}\le1\},\qquad
b_j^*=\min\left(\{1\}\cup
 \{1-|u_{j,t}|:|t|\le K,\ -1\lt u_{j,t}\lt1\}\right).
```

式 (46.5)。

取相互独立的 $`G_t\sim N(0,c_0)`$，$`|t|\le K`$，并置

```math
\mathcal G_j(u)=\sum_{t\in I_j}G_t\mathbf1_{[u_{j,t},1]}(u).
```

式 (46.6)。

在紧区间 $`D[-1,1]`$ 的 $`J_1`$ 拓扑下，$`F_M`$ 的律与
$`\mathcal G_j`$ 的律的有界 Lipschitz 距离趋零。这是与移动高斯律的比较，
不预设该族紧或收敛。两个实际平稳实验、两种方向信息情形都对支持一致地满足

```math
\{F_M\}\text{ 是 }J_1\text{ 紧族}
\quad\Longleftrightarrow\quad
\liminf_{j\to\infty}b_j^*\gt0.
```

式 (46.7)。

这里恰好位于左端点的直线点被原窗口排除；恰好位于右端点的点被包含，
二者都不计入 (46.5) 的内部趋端点距离。
若沿一个子序列 $`\sigma_j\to\sigma`$，每个整数点的排除、内部、恰在右端点
三种状态分别固定，且内部点与两端点的距离有共同正下界，则过程联合其端点趋于
对应的有限高斯阶梯及其端值。内部跳跃位于 $`t\sigma`$，恰在右端点的跳跃仍位于
$`1`$，所有系数来自 (46.6) 的同一高斯向量。
不论路径是否紧，完整序列均有

```math
\frac{F_M(1)}{\sqrt{c_0|I_j|}}\Longrightarrow N(0,1).
```

式 (46.8)。

存在固定常数 $`C`$，使合法选择

```math
\lambda_j=\left\lfloor\frac{2L_j}{d}+\frac3d\log Q_j+C\right\rfloor
```

式 (46.9)。

最终具有 $`I_j=\{0\}`$，并使
$`F_M\Longrightarrow G_0\mathbf1_{[0,1]}`$ 于紧区间 $`J_1`$。
该存在结论不要求取整相位收敛，也不声称任意指定的共振相位可由合法参数实现。

证明。记 $`e_j=k_0-a\lambda\in(-1,0]`$、$`H=h+h_+`$，以及
$`\zeta_j=\phi\lambda/(\beta\log2)-N\in[0,1)`$。
精确取整和正逼近尾给出

```math
\eta_j=10^{-Q_j^5}(1+o(1)),\quad
\log q=d\lambda-\zeta_j\log2-e_jH+o(1),\quad
\eta_j\sqrt q=Q_j^{3/2}
 \exp\left(\frac{db_j-\zeta_j\log2-e_jH}{2}+o(1)\right).
```

式 (46.10)。

又有 $`\log M=\phi\lambda/\beta+O(1)`$、
$`\tau=z_0+O(q^{-1})`$、$`z_0=\phi\lambda+O(1)`$。
所以参数合法、内在临界偏移为零，实际比较所需的
$`q(\log M)^3/M\to0`$、$`\lambda q^2/M\to0`$ 均成立。
指数级增长的 $`q`$ 超过 $`Q,\lambda`$ 的任意固定幂。

由于 $`2\phi/d=2\beta/(1-\beta)\gt2`$，
$`\epsilon/\eta`$ 随 $`L`$ 指数趋零，附加的 $`\log Q`$ 项不改变这一结论。
因此

```math
\Delta\sim hQ\eta\gt0,\qquad
\sigma_j=\frac h{\sqrt A}
 \exp\left(\frac{db_j-\zeta_j\log2-e_jH}{2}+o(1)\right),
\qquad
|c_j|=O\left(\epsilon\sqrt{\lambda q}+
 \frac1{\sqrt{\lambda q}}\right)\longrightarrow0.
```

式 (46.11)。

这同时证明 (46.4) 和有限 $`K`$ 的存在。
在固定充分大的计数截断 $`k+l\le C_1\lambda`$ 内，非直线点的整数分子
仍给出 $`h/(2Q)`$ 间隙，因为

```math
Q\lambda\eta\to0,\qquad Q\epsilon\lambda\to0,\qquad
Qw\to0,\qquad Q/q\to0.
```

式 (46.12)。

实际行尾界对全部行取并集，使该公共截断事件的概率趋一。
其上所有窗口行均在唯一的直线上，直线点的窗口位置精确等于 $`u_{j,t}`$，
只选择 $`t\in I_j`$。这一步保留两端点的严格与非严格不等号。

为在一个标签实现中同时处理全部可能的选择，令
$`J_t=\{i:(N_{i,+},N_{i,-})=(k_0+tQ,l_0+tP)\}`$，
$`J^*=\bigcup_{|t|\le K}J_t`$，包括当前窗口外的这些组。
所有固定 $`|t|\le K`$ 的计数最终合法，且
$`tQ/\sqrt\lambda\to0`$。二维 Stirling 展开在该有限集合上一致给出

```math
Q_r\{(N_+,N_-)=(k_0+tQ,l_0+tP)\}
\sim\frac1{2\pi\lambda\sqrt{ab}},\qquad |t|\le K.
```

式 (46.13)。

各组的 $`W_t-\tau=w(c_j+t\sigma_j)=o(1)`$ 一致成立。
精确换测度使背景和信号的人口加权主项相等，故组占据数的混合比较均值
等价于 $`4c_0q/\lambda`$。
实际一行、两行估计和 Chebyshev 不等式给出相对集中；有限并集无增长群数损失。
全局校准在 $`J^*`$ 上一致给出 $`p_i\to1/2`$，从而

```math
\frac{|J_t|}{B_{0,M}^2}\longrightarrow4c_0,
\qquad
\frac{d_t}{B_{0,M}^2}\longrightarrow c_0,
\quad d_t=\sum_{i\in J_t}p_i(1-p_i),\qquad
|J^*|,d_{J^*}=O_{\mathbb P}(q/\lambda)=o_{\mathbb P}(q).
```

式 (46.14)。

这些依概率结论对支持一致，适用于两种实际实验；没有假设实际观测行独立。
补集保留 $`q`$ 量级的辅助方差，且所有所需的补集整数计数最终合法。
对 $`J^*`$ 只用一次完整后验向量比较 (35.11)。精确中心另由 (35.12) 给出

```math
\sup_{E\subseteq J^*}\frac1{B_{0,M}}
 \left|\sum_{i\in E}(\pi_i-p_i)\right|
\le\frac{C_2\sqrt{d_{J^*}}}{B_{0,M}}
 \left(\frac{d_{J^*}+\sqrt{d_{J^*}}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (46.15)。

固定好环境，在同一个辅助乘积律下作有限向量的 Cramér--Wold 展开。
每个归一化单标签系数为 $`O(B_{0,M}^{-1})=o(1)`$，方差由 (46.14) 收敛，
不同组使用不交的独立辅助标签。因此，先得到联合高斯性，再由对角协方差得到独立性。
完整向量比较及 (46.15) 转移到精确后验，确定环境的子序列论证再给出

```math
\left(B_{0,M}^{-1}\sum_{i\in J_t}
 (\mathbf1_{\{i\in S\}}-\pi_i)\right)_{|t|\le K}
\Longrightarrow (G_t)_{|t|\le K}.
```

式 (46.16)。

条件版本在均匀支持先验下成立于有界 Lipschitz 距离、依数据概率；
其有界性允许取先验期望。未通过总变差转移无界矩。

从系数向量到在 $`u_{j,t}`$ 处累加的路径映射，关于向量的 $`\ell^1`$ 距离
和路径的一致距离为 $`1`$-Lipschitz；恒等时间变换又控制一个有界兼容的
$`J_1`$ 距离。因此这些随 $`j`$ 变化的映射具有共同 Lipschitz 常数。
(46.16) 在有限维有界 Lipschitz 度量中的收敛，连同公共截断事件，证明与
(46.6) 移动律的距离趋零，而无需先证明移动路径族紧。
由于 $`c_j\to0`$，最终 $`0\in I_j`$。有限个选择模式的子序列提取与
(46.16) 同时证明 (46.8)。

若 $`\liminf b_j^*\gt0`$，从任意子序列继续提取，使
$`\sigma_j\to\sigma`$，并使每个点的三种状态固定。
所有选中的内部点与端点保持共同正距离，不同点之间至少相距 $`\sigma_-`$。
它们趋于互异的内部位置 $`t\sigma`$；恰在右端点的点始终位于 $`1`$。
存在分段线性的严格递增端点固定时间变换，将每个极限内部位置送到相应的
$`u_{j,t}`$，其与恒等映射的一致距离趋零。
在同一个高斯系数向量上，变换后的有限阶梯遂一致等于极限阶梯。
于是移动高斯律沿该进一步子序列收敛，(46.16) 和移动律比较给出实际过程收敛。
每条子序列均有收敛的进一步子序列，证明紧性及所述阶梯极限。

反向需要紧区间端点条件。对 $`f\in D[-1,1]`$ 定义

```math
\omega_-(f,\delta)=
 \sup_{s,t\in[-1,-1+\delta]}|f(s)-f(t)|,\qquad
\omega_+(f,\delta)=
 \sup_{s,t\in[1-\delta,1)}|f(s)-f(t)|.
```

式 (46.17)。

对每个 $`J_1`$ 紧集 $`\mathcal K`$，两者都在 $`\delta\downarrow0`$
时于 $`f\in\mathcal K`$ 上一致趋零。
否则可取 $`f_n\in\mathcal K`$、$`\delta_n\downarrow0`$ 违反其中一个结论，
再取 $`f_n\to f`$ 的 $`J_1`$ 子序列。
用端点固定且一致趋于恒等的时间变换拉回违反条件的一对时刻：
左端点处两个时刻都趋于 $`-1`$，由 $`f`$ 的右连续性排除；
右端点处两个时刻都严格小于 $`1`$ 并趋于 $`1`$，由左极限 $`f(1-)`$ 排除。
路径值的一致逼近使原来的正振荡矛盾。
这是紧区间时间变换定义的直接推论；右端点 $`1`$ 被排除于第二个上确界是必要的。

若 $`\liminf b_j^*=0`$，可取子序列及一个固定 $`t_*`$，使
$`u_{j,t_*}`$ 从区间内部趋于一个端点。因为 $`\sigma_j\ge\sigma_-`$，
其余跳跃与它隔开固定正距离。在公共截断事件上，用该点两侧足够近的一对时刻
即可在对应的 (46.17) 中读出这个整组的绝对系数。
由 (46.16)，该系数趋于非退化的 $`N(0,c_0)`$。
因此存在 $`\varepsilon,p\gt0`$，使对每个充分小的固定 $`\delta\gt0`$，
相应振荡超过 $`\varepsilon`$ 的概率沿所取子序列的下极限至少为 $`p`$。
若实际过程族紧，取一个承载至少 $`1-p/2`$ 概率的共同紧集，再用其端点振荡
的一致消失，即得矛盾。这证明 (46.7) 的必要性。
恰位于 $`1`$ 的跳跃没有进入 $`\omega_+`$；它与从内部逼近 $`1`$ 的跳跃不同。

特别地，在 $`\sigma=1/m`$ 的共振相位，$`t=\pm m`$ 的状态不能仅由
$`\sigma_j\to\sigma`$ 判断。内部逼近给出上述障碍；从外部逼近的点不被选择；
恰在左端点者被排除，恰在右端点者保留。
相应模式固定且内部点远离端点时，前面的时间变换证明适用。
这给出条件分类，不推断合法取整序列必然实现其中某个共振分支。

最后，对 (46.9) 有 $`b_j\in(C-1,C]`$。由 (46.11)，

```math
\liminf_j\sigma_j\ge
 \frac h{\sqrt A}\exp\left(\frac{d(C-1)-\log2}{2}\right).
```

式 (46.18)。

选择固定 $`C`$ 使右端大于 $`2`$，则最终所有非零整数点均在窗口外，
中心点仍趋于零且位于内部。公共截断事件上窗口确实只含中央计数组。
(46.16) 和单跳时间变换给出最后的实际单高斯跳结论。

整个系数向量、选择窗口与中心对共同支持置换等变，无条件联合律因而等于每个
固定支持下的联合律。实际估计具有支持一致性。
一次公共正确方向事件同时保持上述全部坐标，补事件概率为 $`O(q^{-1})`$，
故弱极限、移动律比较及紧性结论均一起转移。∎

## 追加锚（本行以下为增补区）

## 47. 密网格的中央平坦化与齐次后验噪声

**定义 47.1（介于重开与有限网格之间的强度）。** 保持[后验阈值卷定义 39.1](PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
的同一个固定振幅及 $`P_j,Q_j,\alpha`$，固定 $`\beta\in(1/2,1)`$，令

```math
\eta_j=\alpha-P_j/Q_j,\quad L_j=\log(1/\eta_j),\quad
d=\frac{\phi(1-\beta)}\beta,\quad A=\frac{2\log10}{d},\qquad
\lambda_j=\frac{2L_j+s_j\log Q_j}{d}+b_j\in\mathbb N,
\quad 0\lt s_-\le s_j\le s_+\lt3,\quad \sup_j|b_j|\lt\infty.
```

式 (47.1)。

各序列均为确定序列。用此强度重新计算 (39.3) 的全部参数，仍用同一实际观测与
精确固定基数后验，只取最终合法的下标。记

```math
\chi_j=\eta_j\sqrt q,\qquad
c_j=\frac{W(k_0,l_0)-\tau}{w},\qquad
\sigma_j=\frac\Delta w,\qquad
R_M=\sqrt{\frac q{\lambda\sigma_j}},\qquad
c_0=\frac1{4\pi\sqrt{ab}}.
```

式 (47.2)。

这里 $`\Delta`$ 为相邻直线计数点的精确补偿得分差，其最终为正将在下文证明。
以原窗口坐标定义

```math
\mathcal F_M(u)=\frac1{R_M}
 \sum_{\tau-w\lt W_i\le\tau+uw}(\mathbf1_{\{i\in S\}}-\pi_i),\qquad
Y_M=\mathcal F_M(1),\qquad
\mathcal C_M(u)=\mathcal F_M(u)-\frac{u+1}{2}Y_M,
\quad -1\le u\le1.
```

式 (47.3)。

未知方向时全部坐标共用一次方向判决和相应工作权重。

**定理 47.2（取整相位任意振荡下的齐次极限）。** 定义 47.1 的参数最终合法，且
$`\chi_j\to\infty`$、$`\sigma_j\to0`$、$`c_j\to0`$、$`R_M\to\infty`$。
对两种实际平稳实验、两种方向信息情形，沿完整序列对支持一致地有

```math
(Y_M,\mathcal F_M,\mathcal C_M)\Longrightarrow
\left(W(2c_0),\ W(c_0(\cdot+1)),\
 W(c_0(\cdot+1))-\frac{\cdot+1}{2}W(2c_0)\right)
\quad\text{于 }\mathbb R\times D[-1,1]\times D[-1,1].
```

式 (47.4)。

路径空间取 $`J_1`$ 拓扑，$`W`$ 是同一个标准 Brownian 运动。
两个路径族均为 $`C`$-紧；极限桥与极限端点独立，并与
$`\sqrt{2c_0}\,\mathcal B((u+1)/2)`$ 同律，其中 $`\mathcal B`$ 为标准 Brownian 桥。
特别地 $`Y_M/\sqrt{2c_0}\Longrightarrow N(0,1)`$。
在正确对齐的均匀固定基数先验空间中，整个三元组的精确后验条件律
在有界 Lipschitz 距离下依数据概率趋于 (47.4) 的确定律。
固定支持下所述的是无条件联合律，不另赋予固定标签条件随机性。

还可把 (47.3) 中的归一化换为

```math
\widetilde R_M^2=\frac{\sqrt q}{h\eta_jQ_j\sqrt\lambda},\qquad
\frac{\widetilde R_M}{R_M}\longrightarrow1.
```

式 (47.5)。

若仍用第 45 章的 $`B_M^2=q/(Q\sqrt\lambda)`$，则同一原窗口和的
$`B_M`$ 归一化过程在一致范数下依概率趋于零。
结论不要求 $`s_j,b_j`$ 或任何取整相位收敛；各固定上下界可进入估计常数。
不声称端点强度 $`s=0,3`$ 上的一致性或实际噪声矩收敛。

证明。令 $`e_j=k_0-a\lambda\in(-1,0]`$、$`H=h+h_+`$，
$`\zeta_j=\phi\lambda/(\beta\log2)-N\in[0,1)`$。
正逼近尾与所有取整给出

```math
\eta_j=10^{-Q_j^5}(1+o(1)),\qquad
\log q=d\lambda-\zeta_j\log2-e_jH+o(1),\qquad
\frac{\chi_j}{Q_j^{s_j/2}}
=\exp\left(\frac{db_j-\zeta_j\log2-e_jH}{2}+o(1)\right).
```

式 (47.6)。

最后的因子有固定正上下界，不把它替换为 $`1`$。
于是 $`\lambda\sim AQ^5`$、$`q\asymp M^{1-\beta}`$、
$`\lambda/\log M\to\beta/\phi`$；
$`q(\log M)^3/M\to0`$、$`\lambda q^2/M\to0`$。
$`q,M`$ 的增长超过 $`Q,\lambda`$ 的任意固定幂。
这些关系保证参数合法，并使内在临界偏移为零。

由 $`2\phi/d=2\beta/(1-\beta)\gt2`$，
$`\epsilon/\eta`$ 乘上 $`Q,\lambda,\chi`$ 的任意固定幂仍趋零。
精确直线间距及中央补偿展开因而给出

```math
\Delta=Q\left(h\eta-\log(1-\epsilon)
                   -\frac PQ\log(1+\epsilon)\right)\sim hQ\eta\gt0,
\qquad
|c_j|=O\left(\epsilon\sqrt{\lambda q}
                 +\frac1{\sqrt{\lambda q}}\right)\longrightarrow0,
```

```math
\sigma_j=\frac{hQ\chi_j}{\sqrt\lambda}(1+o(1))
 \asymp Q_j^{(s_j-3)/2}\longrightarrow0,\qquad
\lambda\sigma_j\asymp Q_j^{(7+s_j)/2}\longrightarrow\infty,
\qquad R_M^2/q=(\lambda\sigma_j)^{-1}\longrightarrow0.
```

式 (47.7)。

$`R_M\to\infty`$ 同时成立。$`s_->0`$ 保证 $`\chi_j\to\infty`$，
$`s_+\lt3`$ 保证网格趋密，这两个严格不等式承担不同义务。
$`\Delta\sim hQ\eta`$ 也立即给出 (47.5)。

在一个固定充分大的公共截断 $`k+l\le C_1\lambda`$ 内，整数分解

```math
Z(k,l)-z_0=h\left(\eta(k-k_0)
 +\frac{P(k-k_0)-Q(l-l_0)}Q\right)
```

式 (47.8)。

使每个非直线点与中央得分相距至少 $`h/(2Q)`$。
这里 $`Q\eta\lambda,Q\epsilon\lambda,Qw,Q/q`$ 均趋零，故补偿和窗口宽度
不能跨过该间隙。实际单行尾界对全部行取并集，使公共截断事件的概率趋一。
其上窗口恰好选择直线点 $`(k_0+tQ,l_0+tP)`$，位置精确为 $`c_j+t\sigma_j`$。
记相应整数前缀为 $`\mathcal T_j(u)`$，则

```math
\mathcal T_j(u)=\{t\in\mathbb Z:-1\lt c_j+t\sigma_j\le u\},\qquad
n_j(u)=|\mathcal T_j(u)|
 =\left\lfloor\frac{u-c_j}{\sigma_j}\right\rfloor
  -\left\lfloor\frac{-1-c_j}{\sigma_j}\right\rfloor,
\qquad
\sup_{-1\le u\le1}|\sigma_j n_j(u)-(u+1)|\le\sigma_j.
```

式 (47.9)。

这是保留严格左端点和非严格右端点的精确计数；不需要任何小数部分收敛。
令 $`\mathcal T_j=\mathcal T_j(1)`$，则
$`|\mathcal T_j|\sim2/\sigma_j\to\infty`$，但所有选中标记同时满足

```math
\sup_{t\in\mathcal T_j}\frac{|t|Q}{\sqrt\lambda}
 \le\frac{(1+|c_j|)Q}{\sigma_j\sqrt\lambda}
 =O(\chi_j^{-1})\longrightarrow0.
```

式 (47.10)。

全部这些计数最终非负并在公共截断内。选中组数增长，而整个标记集合缩到中央。
二维 Stirling 展开因此在整个增长集合上一致给出

```math
f_t:=Q_r\{(N_+,N_-)=(k_0+tQ,l_0+tP)\}
 =\frac{1+o(1)}{2\pi\lambda\sqrt{ab}}
 =\frac{2c_0}{\lambda}(1+o(1)),\qquad t\in\mathcal T_j.
```

式 (47.11)。

具体地，各坐标与 Poisson 均值的偏差为 $`O(\sqrt\lambda/\chi_j+1)`$。
Stirling 对数展开的二次项为 $`O(\chi_j^{-2}+\lambda^{-1})=o(1)`$，
余项 $`O(\lambda^{-1}+|v|/\lambda+|v|^3/\lambda^2)`$ 也一致趋零。
这证明 (47.11) 的一致性，而非只对每个固定整数证明点态结论。

令 $`N_t`$ 为实际计数组占据数，$`W_t`$ 为该组得分。
精确换测度 $`dQ_r=e^W dQ_{-\epsilon}`$ 给出混合比较均值

```math
m_t=qf_t+(M-q)e^{-W_t}f_t
 =qf_t\{1+(1-q/M)e^{\tau-W_t}\}
 =\frac{4c_0q}{\lambda}(1+o(1))
```

式 (47.12)。

并且最后等价关系在全部选中组上一致。
对固定真实支持应用实际一行、两行点质量比较，记
$`\varepsilon_{\rm row}=O((\log M)^3/M)`$，便有
$`|\mathbb E N_t-m_t|\le C_2\varepsilon_{\rm row}m_t`$、
$`\mathrm{Var}(N_t)\le C_2(m_t+\varepsilon_{\rm row}m_t^2)`$。
这里点事件已在固定截断内，比较为相对误差，不需要追加行尾常数。
对任意固定 $`\xi\gt0`$，Chebyshev 和有限并集于是给出

```math
\sup_{|S|=q}\mathbb P_S\left\{
 \max_{t\in\mathcal T_j}|N_t/m_t-1|\gt\xi\right\}
\le C_\xi\sigma_j^{-1}
 \left(\frac\lambda q+\varepsilon_{\rm row}\right)\longrightarrow0.
```

式 (47.13)。

$`\sigma_j^{-1}=O(Q^{(3-s_-)/2})`$ 只付出多项式因子。
上述实际行比较的适用条件已经由 (47.6) 核对；没有假设实际行独立。
全局 logistic 校准仍有 $`\theta_M=O_{\mathbb P}(q^{-1/2})`$ 和
$`q^{-1}\sum_i p_i(1-p_i)\to1/2`$。
它们由精确换测度、实际一行两行集中及临界 Poisson 中心极限定理得到；
其所需 $`q\varepsilon_{\rm row}\to0`$ 在此成立。
窗口内 $`|W_t-\tau|\le w\to0`$，故 $`p_t\to1/2`$ 一致。
置 $`d_t=N_tp_t(1-p_t)`$，则

```math
\max_{t\in\mathcal T_j}
 \left|\frac{N_t}{4c_0q/\lambda}-1\right|\longrightarrow0,
\qquad
\max_{t\in\mathcal T_j}
 \left|\frac{d_t}{c_0q/\lambda}-1\right|\longrightarrow0
\quad\text{依概率}.
```

式 (47.14)。

用同一数据环境下的方差时钟
$`D_M(u)=R_M^{-2}\sum_{t\in\mathcal T_j(u)}d_t`$。
(47.9)、(47.14) 和精确恒等式 $`(q/\lambda)/R_M^2=\sigma_j`$ 直接给出

```math
\begin{split}
\sup_u|D_M(u)-c_0(u+1)|&\longrightarrow0,\\
\sup_u\left||J(u)|/R_M^2-4c_0(u+1)\right|&\longrightarrow0,\\
\max_{t\in\mathcal T_j}d_t/R_M^2
 &=c_0\sigma_j(1+o_{\mathbb P}(1))\longrightarrow0
\end{split}
\quad\text{依概率}.
```

式 (47.15)。

这里 $`J(u)`$ 是原窗口行前缀，$`J=J(1)`$。
特别地 $`d_J/R_M^2\to2c_0`$、$`|J|/R_M^2\to8c_0`$，两者均为
$`o_{\mathbb P}(q)`$。补集因此保留 $`q`$ 量级的辅助方差；
以趋一概率有 $`|J|\le q/2`$ 和 $`M-|J|\gt q`$，所有补集条件计数合法。

在一个好环境中取同一个校准 Bernoulli 乘积律。
[波动卷 (35.11)](PARITY_HIDDEN_ARROW_FLUCTUATIONS.md) 对完整窗口标签向量给出
$`d_{\rm TV}(\mathsf P_J,\mathsf Q_J)\le C_3(d_J/q+q^{-1/2})\to0`$。
精确中心另由该卷 (35.12) 的加权消去估计给出

```math
\sup_{E\subseteq J}\frac1{R_M}
 \left|\sum_{i\in E}(\pi_i-p_i)\right|
\le\frac{C_3\sqrt{d_J}}{R_M}
 \left(\frac{d_J+\sqrt{d_J}}q+q^{-1/2}\right)
\longrightarrow0\quad\text{依概率}.
```

式 (47.16)。

该估计适用于新的较小尺度：$`\sqrt{d_J}/R_M=O_{\mathbb P}(1)`$，而
$`d_J/q=O_{\mathbb P}((\lambda\sigma_j)^{-1})\to0`$。
它同时控制所有前缀，不把总变差乘以标签数。

固定满足这些极限的确定环境序列，按递增得分一次揭示一个完整计数组。
辅助中心过程是平方可积鞅，其可预测二次变差为 $`D_M`$。
独立中心 Bernoulli 和的四阶矩估计给出

```math
\sum_{t\in\mathcal T_j}\mathbb E_{\mathsf Q}
  |\Delta_t\mathcal F_M^{\mathsf Q}|^4
\le3\left(\max_t\frac{d_t}{R_M^2}\right)D_M(1)
  +R_M^{-2}D_M(1)\longrightarrow0,
\qquad
\mathbb E_{\mathsf Q}\max_t|\Delta_t\mathcal F_M^{\mathsf Q}|^2
\le\left(\sum_t\mathbb E_{\mathsf Q}
 |\Delta_t\mathcal F_M^{\mathsf Q}|^4\right)^{1/2}\longrightarrow0.
```

式 (47.17)。

这里控制的是整组跳跃，不是单标签系数。
令时间为 $`t=u+1\in[0,2]`$，并在 $`t=2`$ 后接上独立、方差率为
$`c_0`$ 的 Brownian 增量。延拓只用于应用
[Whitt 定理 2.1(ii)](../../../Library/Dynamics/whitt2007martingale.md)。
延拓鞅从零出发，可预测时钟在每个紧区间一致趋于 $`c_0t`$；
最大时钟跳跃的期望和最大鞅跳跃平方的期望分别由 (47.15)、(47.17) 趋零。
因此辅助过程趋于 $`W(c_0(u+1))`$。
极限在截断端点连续，故从半直线限制回紧区间合法；原窗口恰在右端点的组
同样受消失跳跃界控制，恰在左端点的组按定义排除。

完整向量总变差只转移一次路径律；(47.16) 再转移全部精确中心。
随机环境的任意子序列可继续提取使上述误差几乎处处趋零的子序列，
确定环境结论于是证明精确后验条件律的有界 Lipschitz 收敛依数据概率成立。
这里没有再提取取整相位子序列，因为 (47.15) 已在完整序列上给出同一线性时钟。
距离有界，故取先验期望后得到无条件路径收敛，没有转移无界矩。

端点评价及 $`f\mapsto(f(1),f,f-(u+1)f(1)/2)`$ 在连续极限处连续，
从而得到 (47.4) 的同噪声联合极限。其桥协方差为

```math
c_0\left(\min(u,v)+1-\frac{(u+1)(v+1)}2\right),
\qquad
\mathrm{Cov}\left(W(c_0(u+1))-\frac{u+1}{2}W(2c_0),W(2c_0)\right)=0.
```

式 (47.18)。

联合高斯性随后给出独立性。完整序列的极限连续，故两个路径族均为 $`C`$-紧。
最后，$`\ell_j=\Delta\sqrt q/Q\sim h\chi_j\to\infty`$，且
$`R_M^2/B_M^2=Q/(\sigma_j\sqrt\lambda)=1/\ell_j\to0`$。
新归一化过程的一致范数为 $`O_{\mathbb P}(1)`$，便得到旧归一化下的一致消失。

整个标签、窗口、中心与三元组对共同支持置换等变，无条件联合律因此等于
任意固定支持下的联合律，实际估计具有支持一致性。
所有坐标共用的正确方向事件补集概率为 $`O(q^{-1})`$；一次相等耦合
同时转移弱极限与紧性，不要求方向判决独立于数据。这完成证明。∎

## 追加锚（本行以下为增补区）

## 48. 收缩噪声的临界对数谱与确定高频斜率

**定义 48.1（同一测度的有限频率能量）。** 回到[后验阈值卷第 39、42、43 章](PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
的同一个固定振幅、固定 $`\beta\in(1/2,1)`$ 及原序列 $`\lambda=Q^3`$。
保持该卷的 $`B_M,\mu_M,Y_M,c_M,h_M`$ 与圆周 $`\mathbb T_4`$ 上的 Fourier 约定。
令

```math
\mathfrak L_M=\log(1/h_M),\qquad
K_M(p)=\lfloor e^{p\mathfrak L_M}\rfloor,\qquad
\mathcal E_M(p)=\sum_{|k|\le K_M(p)}
 (1+k^2)^{-1/2}|\widehat\mu_M(k)|^2,
\qquad 0\lt p_0\le p\le p_1\lt\infty.
```

式 (48.1)。

只取 $`h_M\in(0,1)`$ 的充分大下标。令 $`\mathcal U_M`$ 为原窗口中出现的
互异位置集合，并对每个 $`u\in\mathcal U_M`$ 定义完整得分组的系数

```math
A_M(u)=B_M^{-1}\sum_{i\in J:\,u_i=u}
 (\mathbf1_{\{i\in S\}}-\pi_i),\qquad
\mathcal Q_M=\sum_{u\in\mathcal U_M}A_M(u)^2.
```

式 (48.2)。

于是 $`\mu_M=\sum_u A_M(u)\delta_u`$、$`Y_M=\sum_u A_M(u)`$。
所有能量、系数和既有场坐标均使用同一实际数据、标签及精确后验中心；
$`\mathcal E_M`$ 是有限 Fourier 和，不把它定义为一个有限的临界 Sobolev 范数。

**定理 48.2（共同随机质量与高频组方差的分离）。** 定义 48.1 下，令
$`d=\phi(1-\beta)/\beta`$，仍取 (42.4) 的 $`\gamma`$。
对两个实际实验和两种方向信息情形，以下关系对固定支持一致成立：

```math
\frac{\mathfrak L_M}{\lambda}\longrightarrow
 \phi-\frac d2=\frac{\phi(3\beta-1)}{2\beta}\gt0,
\qquad \mathcal Q_M\longrightarrow\gamma\quad\text{依概率},
```

```math
\sup_{p\in[p_0,p_1]}
\left|\frac{\mathcal E_M(p)}{2\mathfrak L_M}
 -\min(p,1)Y_M^2-(p-1)_+\gamma\right|
\longrightarrow0\quad\text{依概率}.
```

式 (48.3)。

因此归一化能量过程与完整端点联合收敛到

```math
\left(Y,\ p\longmapsto\min(p,1)Y^2+(p-1)_+\gamma\right),
\qquad Y\sim N(0,\gamma),
```

式 (48.4)。

能量坐标可取 $`D[p_0,p_1]`$ 的 $`J_1`$ 拓扑，其极限连续。
它还可与定理 40.2、42.2、43.2 中规定的同一实现、固定紧区间轮廓和有限个
既有坐标联合；(48.4) 中的 $`Y`$ 就是这些结论的原端点。
特别地，对固定 $`1\le p_a\lt p_b\lt\infty`$，

```math
\frac{\mathcal E_M(p_b)-\mathcal E_M(p_a)}
 {2\mathfrak L_M(p_b-p_a)}\longrightarrow\gamma
\quad\text{依概率}.
```

式 (48.5)。

这些是概率与弱收敛结论，不包含实际能量矩的收敛，也不使非零点质量属于
$`H^{-1/2}`$。

证明。原序列中算术逼近误差比补偿小，精确直线步长满足

```math
\Delta=(1-\alpha)Q\epsilon(1+o(1)),\qquad
h_M=\frac{\Delta\sqrt q}{Q}
 =(1-\alpha)\epsilon\sqrt q(1+o(1)).
```

式 (48.6)。

$`\log\epsilon=-\phi\lambda+O(1)`$ 和
$`\log q=d\lambda+O(1)`$ 给出 (48.3) 的第一式。
故 $`\mathfrak L_M\asymp Q^3`$，而 $`\delta_M=Q/\sqrt\lambda=Q^{-1/2}`$。

先证明组平方和的集中。在第 42 章的公共全行截断与直线隔离事件上，
$`u_{M,t}=c_M+h_Mt\delta_M`$ 为互异位置，且所有出现的整数均满足
$`|t|\le C_1\lambda/Q`$。置 $`d_t=\sum_{i\in J_t}p_i(1-p_i)`$。
完整方差时钟给出 $`d_J/B_M^2\to\gamma`$ 依概率，并有

```math
\max_t d_t/B_M^2\longrightarrow0\quad\text{依概率}.
```

式 (48.7)。

为核对全窗口而非只核对固定紧标记区间，先用 (42.11) 得到
$`\max_{|t\delta_M|\le R}d_t/B_M^2=O_{\mathbb P}(\delta_M)`$。
对其余截断内的组，(42.14) 的高斯包络给出归一化期望上界
$`C_2\delta_M\sum_{|t\delta_M|\gt R}e^{-c(t\delta_M)^2}+o(1)`$。
低于半均值的计数组由 $`e^{-c\lambda}`$ 尾界处理。
加性实际比较误差至多为
$`C_2(\lambda/Q)M^{1-D_0}/B_M^2=o(1)`$，取充分大的固定 $`D_0`$ 即可。
先取样本上极限再令 $`R\to\infty`$，条件外的 Markov 界使尾部总方差任意小。
最大尾组方差不超过总尾方差，从而证明 (48.7)。截断外只付出趋零的事件概率。

给定一个好环境，在同一个辅助乘积律下，令
$`S_t=\sum_{i\in J_t}(\zeta_i-p_i)`$，$`\mathcal Q_M^{\mathsf Q}=B_M^{-2}\sum_t S_t^2`$。
组间独立性以及中心 Bernoulli 和的四阶矩界给出

```math
\mathbb E_{\mathsf Q}\mathcal Q_M^{\mathsf Q}=d_J/B_M^2,\qquad
\mathrm{Var}_{\mathsf Q}(\mathcal Q_M^{\mathsf Q})
\le3\left(\max_t\frac{d_t}{B_M^2}\right)\frac{d_J}{B_M^2}
 +\frac{d_J}{B_M^4}\longrightarrow0.
```

式 (48.8)。

这些是辅助条件矩，(48.7)、$`B_M\to\infty`$ 使右端依数据概率趋零。
将条件尾概率截在 $`1`$ 以内再平均，得到辅助联合空间上的概率收敛。
(42.8) 另给出组中心误差

```math
\sum_t\left|B_M^{-1}\sum_{i\in J_t}(\pi_i-p_i)\right|
\le B_M^{-1}\sum_{i\in J}|\pi_i-p_i|
\longrightarrow0\quad\text{依概率}.
```

式 (48.9)。

左端控制组误差向量的 $`\ell^2`$ 范数；辅助系数向量的平方范数由 (48.8)
为 $`O_{\mathbb P}(1)`$。Cauchy 不等式使换中心前后的平方范数差趋零。
最后一次完整窗口后验向量比较转移这个收敛事件，证明
$`\mathcal Q_M\to\gamma`$。没有用总变差转移无界平方和的期望。

接着在每个实现上作确定性 Fourier 核计算。
[对数 Fourier 核及固定测度的原子平方关系](../../../Library/Dynamics/iyer2025empirical.md)
是经典先例；此处需要一个对移动原子间距和频率截断同时一致的界。
记

```math
\mathcal K_N(z)=\sum_{|k|\le N}(1+k^2)^{-1/2}e^{-\pi ikz/2}.
```

式 (48.10)。

因为 $`\sum_{k\ge1}(k^{-1}-(1+k^2)^{-1/2})\lt\infty`$，
该核与 $`1+2\sum_{k=1}^N\cos(k\theta)/k`$ 的差一致有界，
其中 $`\theta=\pi z/2`$。对 $`0\lt|\theta|\le1`$，

```math
\sum_{k=1}^N\frac{\cos(k\theta)}k
 =\min\{\log N,\log(1/|\theta|)\}+O(1),\qquad N\ge2,
```

式 (48.11)。

常数与 $`N,\theta`$ 无关。若 $`N\le1/|\theta|`$，
$`|1-\cos(k\theta)|\le k^2\theta^2/2`$ 使该和与调和和相差有界。
若 $`N\gt1/|\theta|`$，先在 $`n=\lfloor1/|\theta|\rfloor`$ 截断，
其余余弦和的部分和至多为 $`C/|\theta|`$；分部求和使加权尾部至多为
$`C/(n|\theta|)=O(1)`$。这证明统一界。
对角线上另有 $`\mathcal K_N(0)=2\log N+O(1)`$。

公共截断事件上，任意两个不同组的位置差满足

```math
h_M\delta_M\le|u_{M,t}-u_{M,s}|
 =h_M\delta_M|t-s|\le C_3h_M\sqrt\lambda\longrightarrow0.
```

式 (48.12)。

所以 $`\log(1/|\pi(u_{M,t}-u_{M,s})/2|)=\mathfrak L_M+O(\log Q)`$
在所有不同组对上一致。函数 $`x\mapsto\min(\log N,x)`$ 为 $`1`$-Lipschitz，
由 (48.11) 对全部 $`N\ge2`$ 同时得到

```math
\mathcal K_N(u_{M,t}-u_{M,s})
 =2\min(\log N,\mathfrak L_M)+O(1+\log Q),\qquad t\ne s.
```

式 (48.13)。

这一步不预先令频率超过最小间距的倒数，因而包含交界指数 $`p=1`$。
用同一个实际精确中心系数 $`A_t=A_M(u_{M,t})`$ 展开有限平方和，
中心 $`c_M`$ 在位置差中精确消去，得

```math
\begin{split}
\sum_{|k|\le N}(1+k^2)^{-1/2}|\widehat\mu_M(k)|^2
={}&2\min(\log N,\mathfrak L_M)Y_M^2\\
&+2(\log N-\mathfrak L_M)_+\mathcal Q_M+\mathcal R_{M,N},\\
\sup_{N\ge2}|\mathcal R_{M,N}|
\le{}&C_4(1+\log Q)\|\mu_M\|_{\mathrm{TV}}^2.
\end{split}
```

式 (48.14)。

这里非对角交叉项保留了同一标签实现，不能把它们替换为独立端点的乘积。
截断内至多有 $`C_5Q^2`$ 个直线组。Cauchy 不等式给出
$`\|\mu_M\|_{\mathrm{TV}}^2\le C_5Q^2\mathcal Q_M`$，故

```math
\frac{1+\log Q}{\mathfrak L_M}\|\mu_M\|_{\mathrm{TV}}^2
 =O_{\mathbb P}(Q^{-1}\log Q)\longrightarrow0.
```

式 (48.15)。

以 $`N=K_M(p)`$ 代入；因为 $`p\ge p_0\gt0`$，
$`\log K_M(p)/\mathfrak L_M\to p`$ 在所取紧区间上一致。
$`Y_M=O_{\mathbb P}(1)`$、$`\mathcal Q_M\to\gamma`$ 与 (48.14)、(48.15)
共同证明 (48.3) 的一致概率近似。

映射 $`y\mapsto[p\mapsto\min(p,1)y^2+(p-1)_+\gamma]`$
从实数到一致范数连续函数空间连续。
它和第 40、42、43 章的既有联合极限、Slutsky 定理一起给出 (48.4) 及其同实现扩展。
(48.5) 则由一致近似在两个指数处相减立即得到。
整个能量及组平方和对共同支持置换等变，故先验论证转移为支持一致的无条件结论。
一次公共方向一致事件同时保持全部坐标，其趋零补事件不影响概率及弱收敛。
所有结论仍是有限截断能量的极限；未将发散的临界全谱范数赋予有限值。∎

## 追加锚（本行以下为增补区）

## 49. 确定谱斜率之下的独立二次波动

**定义 49.1（组能量的环境中心）。** 取定义 48.1 的原序列及同一实际实现，
并沿用后验阈值卷第 42、43 章的校准概率 $`p_i`$、精确后验概率 $`\pi_i`$、
归一化 $`B_M`$ 和标记网格 $`\delta_M=Q^{-1/2}`$。
对原窗口中的每个完整得分组 $`g`$，置

```math
d_g=\sum_{i\in g}p_i(1-p_i),\qquad
V_M=\frac{d_J}{B_M^2},\qquad
T_M=\delta_M^{-1/2}(\mathcal Q_M-V_M),\qquad
\nu_2=2\int_{\mathbb R}\rho(x)^2\,dx
 =2c_0^2\sqrt{\frac\pi\kappa}.
```

式 (49.1)。

这里 $`V_M`$ 是可由观测数据确定的辅助方差中心，并非实际后验平方和的条件期望。
固定 $`1\le p_a\lt p_b\lt\infty`$，另定义有限谱差商

```math
\widehat V_M=
\frac{\mathcal E_M(p_b)-\mathcal E_M(p_a)}
 {2\mathfrak L_M(p_b-p_a)}.
```

式 (49.2)。

**定理 49.2（同一线性噪声之外的二次高斯坐标）。** 定义 49.1 下，两个实际实验及
两种方向信息情形均有

```math
\delta_M^{-1/2}(\widehat V_M-V_M)-T_M
 \longrightarrow0\quad\text{依概率},\qquad
T_M\Longrightarrow N(0,\nu_2).
```

式 (49.3)。

对任意固定 $`R\gt0`$，上述收敛与同一端点 $`Y_M`$、轮廓 $`L_M|_{[-R,R]}`$、
桥 $`C_M|_{[-R,R]}`$ 以及第 43 章的一阶矩系数 $`Z_M`$ 联合成立，极限为

```math
\left(N_2,\ Y,\ L|_{[-R,R]},\ C|_{[-R,R]},\ Z\right),
\qquad N_2\sim N(0,\nu_2),\qquad
N_2\ \perp\ (Y,L|_{[-R,R]},C|_{[-R,R]},Z).
```

式 (49.4)。

轮廓与桥采用既有紧区间 $`J_1`$ 拓扑。结论对固定支持一致；后验条件核的收敛
则在均匀固定基数先验空间、依数据概率理解。
第 42、43 章的测度及偶极近似还可作为同一联合极限的坐标附带。
此处不以 $`\gamma`$ 替换 $`V_M`$，也不主张实际二次噪声矩的收敛。

证明。首先需要比总方差时钟更强的平方时钟。公共全行截断事件上，原窗口正好
包含观测到的直线组 $`J_t`$，标记 $`x_t=t\delta_M`$，组数至多 $`C Q^2`$。
由 (42.11)，每个固定 $`H\gt0`$ 都有

```math
\frac1{B_M^4\delta_M}\sum_{|x_t|\le H}d_t^2
 \longrightarrow\int_{-H}^H\rho(x)^2\,dx
 \quad\text{依概率}.
```

式 (49.5)。

这是逐组相对估计的 Riemann 和，不能仅从累计时钟的收敛推出。
例如确定数组 $`v_t=\delta\rho(t\delta)`$ 与
$`\widetilde v_t=\delta\rho(t\delta)\{1+(-1)^t\}`$ 的累计和有相同极限，
而 $`\delta^{-1}\sum_t v_t^2`$ 与 $`\delta^{-1}\sum_t\widetilde v_t^2`$
分别趋于 $`\int\rho^2`$ 与 $`2\int\rho^2`$：按相邻奇偶网格配对即得。
这说明所需的额外信息是逐组分配，不是累计时钟的后处理。
为移除截断，令 $`m_t`$ 为实际组占据数 $`C_t`$ 的两总体 Poisson 比较均值。
实际一行、两行比较 (42.10) 给出

```math
\mathbb E C_t^2
 \le C(m_t^2+m_t+M^{2-D_0}),
```

式 (49.6)。

其中可预先选择充分大的固定 $`D_0`$，并吸收趋零的相对误差。
在两个计数均不小于各自信号均值一半的截断区域，精确换测度和 Poisson 包络使
$`m_t\le C(q/\lambda)e^{-c x_t^2}`$。
因此将 (49.6) 对 $`|x_t|\gt H`$ 求和、再除以 $`B_M^4\delta_M`$，平方均值项至多为
$`C\delta_M\sum_{|t\delta_M|\gt H}e^{-2c(t\delta_M)^2}`$。
一次均值项在全线至多贡献

```math
\frac{C B_M^2}{B_M^4\delta_M}
 =\frac{C\lambda}{q}\longrightarrow0.
```

式 (49.7)。

低于半均值的计数组由指数尾界处理；其均值与平方均值都只增加指数衰减乘多项式的项。
加性项因组数为 $`O(Q^2)`$、$`D_0`$ 可取充分大而趋零。
又 $`d_t\le C_t/4`$，条件外 Markov 界遂给出平方时钟尾部在先取样本上极限、
再令 $`H\to\infty`$ 时消失。全行截断外只付出趋零的事件概率。
结合 (49.5)，得到

```math
\frac1{B_M^4\delta_M}\sum_t d_t^2
 \longrightarrow\int_{\mathbb R}\rho(x)^2\,dx
 \quad\text{依概率}.
```

式 (49.8)。

给定环境，在同一个辅助乘积律下写
$`S_t=\sum_{i\in J_t}(\zeta_i-p_i)`$。各 $`S_t`$ 独立且中心化。
独立中心 Bernoulli 变量的累积量计算给出

```math
\mathrm{Var}_{\mathsf Q}(S_t^2)
 =2d_t^2+\sum_{i\in J_t}p_i(1-p_i)
                      \{1-6p_i(1-p_i)\}.
```

式 (49.9)。

后一和的绝对值不超过 $`d_t`$；(49.7) 使其在二次波动尺度上可忽略。
于是 $`B_M^{-2}\delta_M^{-1/2}\sum_t(S_t^2-d_t)`$ 的辅助条件方差趋于 $`\nu_2`$。

先限制到固定标记区间 $`[-H,H]`$。对任意中心化、绝对值不超过一的独立变量之和 $`S`$，
展开偶数阶矩时，每个存活索引至少出现两次，故对固定整数 $`m\ge1`$，
$`\mathbb E S^{2m}\le C_m\sum_{j=1}^m d^j`$，其中 $`d=\mathbb E S^2`$。
取 $`m=4`$ 并用幂和不等式，得到

```math
\mathbb E_{\mathsf Q}(S_t^2-d_t)^4
 \le C(d_t^4+d_t^3+d_t^2+d_t).
```

式 (49.10)。

紧区间内 $`d_t/(B_M^2\delta_M)`$ 一致有界，最小 $`d_t`$ 趋于无穷，
且组数为 $`O_H(\delta_M^{-1})`$。因此相应归一化四阶矩之和为 $`O_H(\delta_M)+o(1)`$。
经典独立数组 Lyapunov 定理给出紧区间二次和的高斯极限
（二次型先例及其条件见[文献说明](../../../Library/Dynamics/iyer2025empirical.md)）。
(49.6) 的平方时钟尾界和 (49.9) 又使被删二次尾和的辅助条件二阶矩依概率任意小，
从而可令 $`H\to\infty`$。

必须同时识别线性坐标。固定有限个轮廓取值及紧区间一阶矩截断，
其任意线性组合均是 $`B_M^{-1}\sum_t f_tS_t`$，其中紧区间内 $`f_t`$ 一致有界。
其与二次和的辅助条件协方差满足

```math
\left|\frac1{B_M^3\sqrt{\delta_M}}
 \sum_t f_t\mathbb E_{\mathsf Q}S_t^3\right|
 \le\frac{C_H d_J}{B_M^3\sqrt{\delta_M}}
 =O_{\mathbb P}\!\left(\sqrt{\frac\lambda q}\right)
 \longrightarrow0.
```

式 (49.11)。

用到了 $`|\mathbb E S_t^3|\le d_t`$。
线性组和的四阶矩之和由 $`\mathbb E S_t^4\le3d_t^2+d_t`$ 控制，二次部分由
(49.10) 控制，因而每个混合线性组合均满足同一 Lyapunov 条件。
Cramér–Wold 定理先给出联合高斯性，随后 (49.11) 才给出独立性。
线性方差尾及带 $`x_t^2`$ 的方差尾由第 42、43 章控制；二次尾由 (49.6) 控制。
令 $`H\to\infty`$ 得到完整端点、各固定轮廓取值和一阶矩的共同极限。
既有轮廓过程紧性与二次标量紧性给出乘积空间紧性，连续极限及这些有限维分布
唯一识别 (49.4) 中的联合路径律。桥是同一端点与轮廓的连续投影。

现在转移精确中心。令
$`e_t=B_M^{-1}\sum_{i\in J_t}(\pi_i-p_i)`$、
$`e_M=(d_J+\sqrt{d_J})/q+q^{-1/2}`$。
(42.8) 和 $`d_J/B_M^2\to\gamma`$ 给出

```math
\|(e_t)_t\|_2\le\sum_t|e_t|
 =O_{\mathbb P}(e_M),\qquad
\delta_M^{-1/2}e_M\longrightarrow0\quad\text{依概率}.
```

式 (49.12)。

后一式使用 $`B_M^2/q=(Q\sqrt\lambda)^{-1}=Q^{-5/2}`$ 和 $`q`$ 超过每个固定多项式。
辅助系数向量 $`(S_t/B_M)_t`$ 的平方范数为 $`O_{\mathbb P}(1)`$，故

```math
\delta_M^{-1/2}
\left|\sum_t(S_t/B_M-e_t)^2-\sum_t(S_t/B_M)^2\right|
\le\delta_M^{-1/2}
 \left(2\|(S_t/B_M)_t\|_2\|(e_t)_t\|_2+\|(e_t)_t\|_2^2\right)
\longrightarrow0\quad\text{依概率}.
```

式 (49.13)。

线性坐标的精确中心由既有同时子集界及第 43 章的带权界处理。
窗口大小和方差均为 $`o_{\mathbb P}(q)`$，补集方差与合法条件计数保持既有下界。
一次完整后验向量比较遂转移全部坐标的事件和有界测试函数。
对好环境子序列应用上述确定数组证明，再用条件概率与条件有界距离的有界性平均，
得到依数据概率的后验条件核结论。这里没有经总变差转移无界二次矩。

最后，先在 (48.14) 中使用
$`\log K_M(p)=p\mathfrak L_M+O(e^{-p_a\mathfrak L_M})`$，
再于 $`p_a,p_b\ge1`$ 两处相减，端点平方主项相消。组数与 Cauchy 界使

```math
\widehat V_M-\mathcal Q_M
 =O_{\mathbb P}(Q^{-1}\log Q),\qquad
\delta_M^{-1/2}(\widehat V_M-\mathcal Q_M)
 =O_{\mathbb P}(Q^{-3/4}\log Q)\longrightarrow0.
```

式 (49.14)。

频率取整的指数小误差也包含在该界中。这证明 (49.3) 的第一式并保持全部共同实现。
第 42、43 章的测度和偶极概率近似通过 Slutsky 定理附带，不另造独立噪声。
支持置换等变性把先验结论转移为固定支持一致的无条件结论；一次公共方向一致事件
同时保持所有统计量，趋零补事件只用于概率与分布转移。∎

## 追加锚（本行以下为增补区）

## 50. 临界谱转折的随机曲线

**定义 50.1（分辨聚簇尺度的 Fourier 坐标）。** 取定义 48.1 的同一原序列、实际数据、
完整后验标签和精确中心，保留后验阈值卷第 43 章的 $`x_i,c_M,h_M`$。
置 $`\omega=\pi/2`$，并定义

```math
F_M(v)=\frac1{B_M}\sum_{i\in J}
 (\mathbf1_{\{i\in S\}}-\pi_i)e^{-i\omega vx_i},\qquad
N_M(s)=\lfloor e^s/h_M\rfloor,\qquad
\mathcal R_M(s)=\sum_{|k|\le N_M(s)}
 (1+k^2)^{-1/2}|\widehat\mu_M(k)|^2-2\mathfrak L_M Y_M^2.
```

式 (50.1)。

这里 $`F_M(0)=Y_M`$，且由既定圆周约定精确有
$`\widehat\mu_M(k)=e^{-i\omega k c_M}F_M(kh_M)`$。
下述常数中的级数绝对收敛：

```math
b_* =1+2\gamma_{\mathrm E}
 +2\sum_{k=1}^{\infty}\left\{(1+k^2)^{-1/2}-k^{-1}\right\},
```

式 (50.2)。

其中 $`\gamma_{\mathrm E}`$ 为 Euler 常数，与方差 $`\gamma`$ 区别。
取第 43 章的同一个实 Gaussian 等距过程 $`\mathcal W_\rho`$，置

```math
F(v)=\int_{\mathbb R}e^{-i\omega vx}\,\mathcal W_\rho(dx),\qquad
r(v)=e^{-\omega^2v^2/(2\kappa)},\qquad
\mathcal R(s)=(b_*+2s)Y^2
 +2\int_0^{e^s}\frac{|F(v)|^2-Y^2}{v}\,dv.
```

式 (50.3)。

复积分表示实部和虚部分别作用于同一个实等距过程，并非两个独立的复噪声。

**定理 50.2（共同轮廓的有限分辨率谱律）。** 对固定 $`A\gt0`$ 和紧区间
$`I=[s_0,s_1]`$，在定义 50.1 的两个实际实验与两种方向信息情形下，
以下联合收敛对固定支持一致成立：

```math
\left(F_M|_{[0,A]},\mathcal R_M|_I,Y_M,L_M|_{[-H,H]},
 C_M|_{[-H,H]},Z_M\right)
\Longrightarrow
\left(F|_{[0,A]},\mathcal R|_I,Y,L|_{[-H,H]},C|_{[-H,H]},Z\right)
\qquad(H\gt0).
```

式 (50.4)。

Fourier 因子取复值连续函数的一致拓扑，其余路径取既有 $`J_1`$ 拓扑。
谱曲线极限连续，且可取满足

```math
\mathcal R'(s)=2|F(e^s)|^2
```

式 (50.5)。

的版本。后验条件核结论在均匀固定基数先验空间中依数据概率成立。
极限 Fourier 坐标的协方差和不带共轭的二阶关系分别为

```math
\mathbb E[F(u)\overline{F(v)}]=\gamma r(u-v),\qquad
\mathbb E[F(u)F(v)]=\gamma r(u+v),\qquad F(0)=Y.
```

式 (50.6)。

特别地，任取固定 $`0<b_0<b_1<\infty`$，同一有限谱带能量满足

```math
\sum_{N_M(\log b_0)<|k|\le N_M(\log b_1)}
 (1+k^2)^{-1/2}|\widehat\mu_M(k)|^2
\Longrightarrow
\mathcal B_{b_0,b_1}:=2\int_{b_0}^{b_1} |F(v)|^2\,\frac{dv}{v}.
```

式 (50.7)。

这是非高斯且非退化的随机变量；即使给定同一端点 $`Y`$，仍有正条件方差。
极限变量满足

```math
\begin{split}
\mathbb E[\mathcal B_{b_0,b_1}\mid Y]
 &=2\int_{b_0}^{b_1}
       \{\gamma+(Y^2-\gamma)r(v)^2\}\,\frac{dv}{v},\\
\mathrm{Cov}(\mathcal B_{b_0,b_1},Y^2)
 &=4\gamma^2\int_{b_0}^{b_1} r(v)^2\,\frac{dv}{v}>0.
\end{split}
```

式 (50.8)。

这些是极限 Gaussian 对象的矩恒等式，不主张实际谱能量矩的收敛。

证明。[经验 Fourier 过程与二次谱泛函的先例及适用边界](../../../Library/Dynamics/iyer2025empirical.md)
归于经典理论；下面核对实际后验的带权时钟与常数级截断误差。
先建立保留整个标记分布的 Fourier 紧性。把复 Hilbert 空间
$`H^1[0,A]`$ 视为实 Hilbert 空间。在同一个辅助独立标签律下，令
$`F_M^{\mathsf Q}(v)=B_M^{-1}\sum_{i\in J}(\zeta_i-p_i)e^{-i\omega vx_i}`$。
第 42、43 章的总时钟和二阶带权时钟给出

```math
V_M=\frac{d_J}{B_M^2}\longrightarrow\gamma,\qquad
K_M^{(2)}=\frac1{B_M^2}\sum_{i\in J}x_i^2p_i(1-p_i)
 \longrightarrow\frac\gamma\kappa,
\qquad
\mathbb E_{\mathsf Q}\|F_M^{\mathsf Q}\|_{H^1[0,A]}^2
 =A(V_M+\omega^2K_M^{(2)}).
```

式 (50.9)。

将 (43.9) 用于 Hilbert 系数
$`f_i(v)=B_M^{-1}e^{-i\omega vx_i}`$，其方差和正是 (50.9) 右端，故

```math
\left\|B_M^{-1}\sum_{i\in J}(\pi_i-p_i)e^{-i\omega(\cdot)x_i}
 \right\|_{H^1[0,A]}
 \le C\{A(V_M+\omega^2K_M^{(2)})\}^{1/2}e_J
 \longrightarrow0\quad\text{依概率}.
```

式 (50.10)。

这里 $`e_J`$ 为 (43.9) 的趋零括号。
条件 Markov 界、一次完整后验向量比较及独立的中心界，遂使实际
$`\|F_M\|_{H^1[0,A]}`$ 在概率意义下有界。没有转移无界范数的期望。
有界 $`H^1`$ 集在一维 $`C[0,A]`$ 中相对紧，因而得到实际 Fourier 过程紧性。

同一论证用于 $`|x_i|>R`$ 的尾部；(43.8) 及总方差尾使其 $`H^1`$ 范数
先取样本上极限、再令 $`R\to\infty`$ 后依概率消失。
固定 $`R`$ 时，对带符号计数测度分部积分，将截断的 Fourier 和写成
$`L_M|_{[-R,R]}`$ 的连续线性积分和两个端点项。
既有轮廓极限连续，故 $`J_1`$ 收敛足以给出该截断和在固定频率区间上一致收敛，
并保留同一端点、桥及 $`Z_M`$ 的联合律。
Gaussian 极限一侧有相同的带权尾界，因此可移除 $`R`$。
这识别 $`F`$ 为同一个 $`\mathcal W_\rho`$ 的 Fourier 积分，证明 Fourier 部分的联合收敛。
其二阶关系由实等距性和 Gaussian 密度的 Fourier 变换得到 (50.6)。
此外 $`\mathbb E\|F\|_{H^1[0,A]}^2=A\gamma(1+\omega^2/\kappa)<\infty`$，
故可取局部 $`H^1`$ 的连续版本。

接着需要在常数级而非 $`\mathfrak L_M`$ 级控制频率和。
对任意 $`f\in H^1[0,A]`$，令 $`g(v)=|f(v)|^2-|f(0)|^2`$。
则 $`g(0)=0`$ 且

```math
\|g'\|_2\le2\|f\|_\infty\|f'\|_2,\qquad
|g(v)|\le\sqrt v\,\|g'\|_2,\qquad
\left|\int_0^\varepsilon\frac{g(v)}v\,dv\right|
 \le2\sqrt\varepsilon\,\|g'\|_2.
```

式 (50.11)。

固定 $`0<A_0<A`$，对 $`b\in[A_0,A]`$ 和 $`n=\lfloor b/h\rfloor`$，
按网格区间比较右端点和积分，有

```math
\sup_{A_0\le b\le A}
\left|\sum_{k=1}^{\lfloor b/h\rfloor}\frac{g(kh)}k
 -\int_0^b\frac{g(v)}v\,dv\right|
 \le C_{A_0,A}\sqrt h\,\|f\|_{H^1[0,A]}^2.
```

式 (50.12)。

为核对零端点，第一格的和项与积分都由 $`C\sqrt h\|g'\|_2`$ 控制。
对第 $`k\ge2`$ 格，函数变化项的和由
$`\sqrt h\sum_{k\ge2}k^{-1}\|g'\|_{L^2((k-1)h,kh)}`$ 控制，
Cauchy 不等式给出同一界。分母变化项用 $`|g(v)|\le\sqrt v\|g'\|_2`$，
其和由 $`C\sqrt h\|g'\|_2\sum_{k\ge2}k^{-3/2}`$ 控制。
余下长度小于 $`h`$ 的终格由 $`A_0>0`$ 控制。这证明 (50.12)。

记 $`r_k=(1+k^2)^{-1/2}-1/k=O(k^{-3})`$。
由 (50.11)，一致地对上述 $`b`$，

```math
\sum_{k=1}^{\lfloor b/h\rfloor}r_k|f(kh)|^2
 =|f(0)|^2\sum_{k=1}^{\infty}r_k
   +O_{A_0,A}(\sqrt h\,\|f\|_{H^1}^2),\qquad
\sum_{k=1}^{\lfloor b/h\rfloor}\frac1k
 =\log(1/h)+\log b+\gamma_{\mathrm E}+O_{A_0,A}(h).
```

式 (50.13)。

后一式保留了频率取整误差。
取 $`A>e^{s_1}`$，代入同一个实际函数 $`f=F_M`$、$`h=h_M`$，
零频率贡献恰为 $`Y_M^2`$，正负频率贡献相等。因此

```math
\sup_{s\in I}\left|\mathcal R_M(s)
 -(b_*+2s)Y_M^2
 -2\int_0^{e^s}\frac{|F_M(v)|^2-Y_M^2}{v}\,dv\right|
 \le C_I\sqrt{h_M}\|F_M\|_{H^1[0,A]}^2
 \longrightarrow0\quad\text{依概率}.
```

式 (50.14)。

这个估计直接处理指数多的频率，没有用发散的测度总变差逐项累加误差。

在积分下端先截于 $`\varepsilon>0`$，得到连续函数空间上的连续映射。
(50.11) 与实际 $`H^1`$ 范数的概率有界性使被删积分在
$`\varepsilon\downarrow0`$ 时一致依概率趋零；极限一侧同样成立。
因此连续映射定理、截断及 (50.14) 给出 (50.4) 的谱部分，并保持全部共同坐标。
(50.11) 还证明定义 50.1 中的反常积分存在。
微积分基本定理随后给出 (50.5)，两点相减给出 (50.7)。

最后识别谱带中不能由端点恢复的随机性。联合 Gaussian 性给出
$`F(v)=r(v)Y+G(v)`$，其中 $`G`$ 与 $`Y`$ 独立。
由于 $`\rho`$ 为偶函数，$`\Im F`$ 与整个实部过程和 $`Y`$ 独立，且

```math
K_{\mathrm{im}}(u,v)=\mathbb E[\Im F(u)\Im F(v)]
 =\frac\gamma2\{r(u-v)-r(u+v)\}>0\qquad(u,v>0).
```

式 (50.15)。

Gaussian 四阶矩展开及独立性遂给出

```math
\mathrm{Var}(\mathcal B_{b_0,b_1}\mid Y)
 \ge8\int_{b_0}^{b_1}\int_{b_0}^{b_1}
       K_{\mathrm{im}}(u,v)^2\,\frac{du\,dv}{uv}>0.
```

式 (50.16)。

谱带变量非负且非退化，所以不能为 Gaussian 变量。
同一分解给出 (50.8) 的条件期望；再用 $`\mathrm{Var}(Y^2)=2\gamma^2`$
即得其协方差。此处仅计算极限对象的有限矩。

各条件论证在好环境子序列上成为确定数组论证，条件尾概率和有界测试距离可截于一后平均，
故给出依数据概率的后验条件核结论。共同支持置换等变性及原实际时钟的统一性给出
固定支持一致的无条件结论；一次方向一致事件同时保持 Fourier 和谱坐标。
结论只取固定频率区间与固定 $`s`$ 区间，不把这里的常数级展开宣称为
第 48 章整个固定 $`p`$ 区间上的一致二阶展开。∎

## 追加锚（本行以下为增补区）

## 51. 同时放大的谱尺度与随机仿射极限

**定义 51.1（对数二次核与增长谱坐标）。** 沿用定义 49.1、50.1 的原序列、
同一完整后验标签及精确中心，记 $`\delta=\delta_M=Q^{-1/2}`$、
$`h=h_M`$、$`\mathfrak L=\log(1/h)`$、$`\omega=\pi/2`$。
保留同一组电荷 $`A_t`$、标记 $`x_t=t\delta`$、
$`\mathcal Q_M=\sum_t A_t^2`$、$`V_M=d_J/B_M^2`$ 和 $`T_M`$。
置

```math
D_{\mathrm w}=\sum_{k\ge1}\{(1+k^2)^{-1/2}-k^{-1}\},\qquad
H(x,y)=1+2D_{\mathrm w}-2\log(\omega|x-y|)\quad(x\ne y).
```

式 (51.1)。

对实对称核 $`K\in L^2(\rho\otimes\rho)`$，以第 43 章的同一实 Gaussian
测度 $`\mathcal W_\rho`$ 定义二重 Wiener 积分 $`I_2(K)`$，其规范为

```math
I_2(f\widetilde\otimes g)
 =\mathcal W_\rho(f)\mathcal W_\rho(g)-\int fg\rho,\qquad
\mathbb E I_2(K)^2=2\iint K(x,y)^2\rho(x)\rho(y)\,dx\,dy.
```

式 (51.2)。

有限对称张量和及此等距式给出完备化定义。下述证明核对 $`H`$ 属于该空间；
其对角线取值不影响这个定义。对 $`u>0`$，定义实际有限谱过程

```math
s_M(u)=\frac{u}{\sqrt\delta},\qquad
N_M(u)=\left\lfloor\frac{e^{s_M(u)}}h\right\rfloor,\qquad
\mathcal Z_M(u)=\sum_{|k|\le N_M(u)}(1+k^2)^{-1/2}
 |\widehat\mu_M(k)|^2-2\mathfrak L Y_M^2-2s_M(u)V_M.
```

式 (51.3)。

这里 $`u`$ 是谱尺度参数，不是得分阈值；$`V_M`$ 仍为观测环境中的辅助方差中心。

**定理 51.2（共同轮廓的二次截距与独立高斯斜率）。** 对固定
$`0<u_0<u_1<\infty`$ 及 $`R>0`$，在定义 51.1 的两个实际实验中有联合收敛

```math
\left(\mathcal Z_M|_{[u_0,u_1]},T_M,Y_M,
 L_M|_{[-R,R]},C_M|_{[-R,R]},Z_M\right)
\Longrightarrow
\left(\bigl(b_*\gamma+I_2(H)+2uN_2\bigr)_{u\in[u_0,u_1]},
 N_2,Y,L|_{[-R,R]},C|_{[-R,R]},Z\right).
```

式 (51.4)。

其中 $`b_*`$ 如 (50.2)，$`N_2\sim N(0,\nu_2)`$ 与整个
$`\mathcal W_\rho`$ 独立，故也独立于 $`I_2(H)`$。
所有路径取 $`J_1`$ 拓扑，极限连续。结论对固定支持一致，并在两种方向信息情形下成立。
后验条件核的有界 Lipschitz 收敛，在均匀固定基数先验空间中依数据概率成立。
在任意固定 $`u>0`$，谱极限为非 Gaussian 变量；这一断言及下文的矩计算只涉及极限对象。

证明。[二次型、Wiener 积分与渐近独立性的先例及边界](../../../Library/Dynamics/iyer2025empirical.md)
给出所用经典机制。新增的分析在于实际组的对数平方控制、共同实现以及同时增长的截断。

先固定充分大的全行计数截断。其共同事件概率趋于一；事件上原窗口恰为观测直线组，
组数 $`g_M\le CQ^2`$，且 $`|x_t|\le C\sqrt\lambda`$。
令 $`C_t`$ 为截断直线点的实际占据数，$`m_t`$ 为其两总体 Poisson 比较均值，
$`d_t=\sum_{i\in J_t}p_i(1-p_i)`$、$`v_t=d_t/B_M^2`$。
这些截断点上的变量可在全部数据上定义，以便先取数据期望。
两点 $`t\ne r`$ 不能由同一行同时占据；原实际模型的相对点比较 (17.8)
在两倍固定截断中直接给出

```math
\mathbb E_S(C_tC_r)\le C m_tm_r,\qquad
\mathbb E_S(v_tv_r)\le C a_ta_r,\qquad
a_t=\frac{m_t}{B_M^2}\qquad(t\ne r).
```

式 (51.5)。

第一式把 $`C_tC_r`$ 展为不同实际行的指示量乘积，再逐项使用同一真实支持下的两行比较。
这里没有同一行的对角贡献，也不需要对任意事件作截断而产生的加性误差。
第二式只用 $`d_t\le C_t/4`$，故允许校准根依赖全部数据。

第 42 章使用的精确换测度和 Poisson 点包络，在两个计数均不低于其信号均值一半时给出
$`a_t\le C\delta e^{-c x_t^2}`$；其余截断点满足
$`a_t\le C Q^{5/2}e^{-c\lambda}`$。
这是 $`m_t\le C(q/\lambda)e^{-c x_t^2}`$、$`m_t\le Cq e^{-c\lambda}`$
分别除以 $`B_M^2=q/Q^{5/2}`$ 的结果。低计数组只有 $`O(Q^2)`$ 个；
涉及它们的双和乘以 $`(1+\log Q)^2`$ 仍指数趋零。

对充分小的固定 $`\varepsilon>0`$，Gaussian 网格和满足

```math
\begin{split}
&\delta^2\sum_{0<|t-r|\delta\le\varepsilon}
 e^{-c\{(t\delta)^2+(r\delta)^2\}}
 \{1+|\log(\omega|t-r|\delta)|\}^2\\
&\qquad\le C\delta\sum_{1\le|m|\le\varepsilon/\delta}
       (1+|\log(|m|\delta)|)^2
 \le C\varepsilon(1+\log^2\varepsilon).
\end{split}
```

式 (51.6)。

第一步固定差 $`m=r-t`$，再用平移 Gaussian 网格和的一致界。
第二步把递减函数的右端点和与零端点处可积的积分比较；$`\delta>\varepsilon`$ 时和为空。
若 $`|t\delta|>R`$ 或 $`|r\delta|>R`$，先抽出 Gaussian 因子
$`e^{-cR^2/2}`$。剩余的 $`|t-r|\delta\le1`$ 部分由同一积分界控制，
其余部分用 $`\log^2(\omega|x-y|)\le C(1+x^2+y^2)`$。
于是 (51.5) 给出支持一致的实际数据界

```math
\begin{split}
\mathbb E_S\sum_{\substack{t\ne r\\|x_t-x_r|\le\varepsilon}}
 H(x_t,x_r)^2v_tv_r
 &\le C\varepsilon(1+\log^2\varepsilon)+o(1),\\
\mathbb E_S\sum_{\substack{t\ne r\\|x_t|>R\ \mathrm{or}\ |x_r|>R}}
 H(x_t,x_r)^2v_tv_r
 &\le Ce^{-c'R^2}+o(1).
\end{split}
```

式 (51.7)。

余项来自低计数点，在固定截断参数下指数趋零。远处相邻组也包含在第二式中。
对应的连续积分界同时证明 $`H\in L^2(\rho\otimes\rho)`$。
无权尾质量趋零本身不能给出 (51.7)：例如在
$`R_\delta=(\log(1/\delta))^{1/4}`$ 附近放置两个相邻网格点，
各赋权 $`1/\log(1/\delta)`$，总权及二阶位置加权总权都趋零，
但两点的对数平方加权乘积趋于一。直接代入可得这些结论。
该数组只反驳不足的尾界推理；实际模型由 (51.5) 的 Gaussian 包络排除它。

给定数据，在同一个辅助独立标签律 $`\mathsf Q`$ 下，置
$`U_t=B_M^{-1}\sum_{i\in J_t}(\zeta_i-p_i)`$。
不同组独立、中心化，方差为 $`v_t`$。对任意实对称核 $`K`$，记
$`S_M(K)=\sum_{t\ne r}K(x_t,x_r)U_tU_r`$，则精确有

```math
\mathbb E_{\mathsf Q}S_M(K)=0,\qquad
\mathbb E_{\mathsf Q}|S_M(K)|^2
 =2\sum_{t\ne r}K(x_t,x_r)^2v_tv_r.
```

式 (51.8)。

只需配对两个不同组，无须实际数据的四行独立性。
先取支撑于固定紧区间的对称矩形阶梯核
$`K=\sum_{a,b}k_{ab}\mathbf1_{I_a}\otimes\mathbf1_{I_b}`$，其中 $`I_a`$ 两两不交。
写 $`U(I_a)=\sum_{x_t\in I_a}U_t`$，得到恒等式

```math
S_M(K)=\sum_{a,b}k_{ab}U(I_a)U(I_b)
 -\sum_a k_{aa}\sum_{x_t\in I_a}U_t^2.
```

式 (51.9)。

第 49 章证明中的混合 Lyapunov 论证，使这些有限区间和、辅助二次坐标以及
同一端点、轮廓和一阶矩联合趋于 Gaussian 向量。
其二次坐标与全部线性块独立；这里先有联合 Gaussian 性，再使用协方差趋零。
又区间平方和的均值趋于 $`\int_{I_a}\rho`$，其方差由
$`C\{\sum_t v_t^2+V_M/B_M^2\}\to0`$ 控制。
故 (51.9) 联合趋于 $`I_2(K)`$，并保持与同一个 $`N_2`$ 的独立性。

现在把 $`H`$ 连续截断在 $`[-R-1,R+1]^2`$，并在
$`|x-y|\le\varepsilon`$ 上置零，过渡到 $`|x-y|\ge2\varepsilon`$。
所得核连续、有界，再以对称矩形阶梯核一致逼近。
(51.5) 使 $`\mathbb E_S\sum_{t\ne r}v_tv_r`$ 一致有界，故 (51.8)
控制阶梯逼近误差；(51.7) 控制删去的近对角线与远尾。
具体地，条件误差概率的数据期望至多为

```math
\frac C{b^2}\{e^{-c'R^2}+\varepsilon(1+\log^2\varepsilon)\}
 \quad\text{的样本上极限}\qquad(b>0).
```

式 (51.10)。

Gaussian 极限侧由 (51.2) 有相同的二阶逼近。
逐次令阶梯网格变细、$`\varepsilon\downarrow0`$、$`R\to\infty`$，
收敛逼近给出辅助二次坐标、$`S_M(H)`$ 与整个指定线性束的共同极限。
有限块极限中的乘积律在这些逼近下保留，所以 $`N_2`$ 独立于
$`I_2(H)`$ 和同一 Gaussian 测度的所有区间坐标。
这也给出与整个 $`\mathcal W_\rho`$ 独立的实现。
这里未将不同 Wiener 阶的正交性当作独立性。

还需在此尺度转移精确中心。令
$`e_t=B_M^{-1}\sum_{i\in J_t}(\pi_i-p_i)`$，
$`r_M=(d_J+\sqrt{d_J})/q+q^{-1/2}`$。
(43.9) 用于正交组向量给出

```math
\|e\|_2\le C\sqrt{V_M}\,r_M,\qquad
r_M=O_{\mathbb P}(Q^{-5/2}+q^{-1/2}),\qquad
Q^2(1+\log Q)r_M\longrightarrow0.
```

式 (51.11)。

在截断组上 $`\delta\le|x_t-x_r|\le C\sqrt\lambda`$，故
对角线为零、非对角元素为 $`H(x_t,x_r)`$ 的矩阵满足
$`\|H_M^\circ\|_{\mathrm{op}}\le CQ^2(1+\log Q)`$。
辅助律下 $`\mathbb E_{\mathsf Q}\|U\|_2^2=V_M=O_{\mathbb P}(1)`$，因此

```math
\left|(U-e)^{\mathsf T}H_M^\circ(U-e)-U^{\mathsf T}H_M^\circ U\right|
\le CQ^2(1+\log Q)(2\|U\|_2\|e\|_2+\|e\|_2^2)
 \longrightarrow0
```

式 (51.12)。

以辅助条件概率、依数据概率成立。二次坐标的位移由 (49.13) 控制，
线性束的位移由既有子集与带权中心界控制。
补集保留与 $`q`$ 同阶的方差，所有条件计数合法；一次完整后验向量比较
遂转移这一整束精确中心函数，得到

```math
\left(T_M,\sum_{t\ne r}H(x_t,x_r)A_tA_r,Y_M,L_M,C_M,Z_M\right)
\Longrightarrow (N_2,I_2(H),Y,L,C,Z).
```

式 (51.13)。

路径仍限制于任意固定紧区间。条件版本使用 (51.10) 的条件误差概率期望和 Markov 界，
结合有限逼近的条件有界 Lipschitz 收敛；不要求每个固定截断误差在每条数据实现上消失。
全行截断外只付出其概率，没有转移无界二次矩。

最后直接估计同时增长的有限 Fourier 核。
设 $`a_k=(1+k^2)^{-1/2}`$、$`d_k=a_k-1/k`$，
$`K_N(z)=1+2\sum_{k=1}^Na_k\cos(\omega kz)`$。
由 $`d_k=O(k^{-3})`$ 和调和和的常数项，
$`K_N(0)=2\log N+b_*+O(N^{-1})`$。
对 $`0<|\theta|\le1`$，几何级数及分部求和给出

```math
\sum_{k=1}^N\frac{\cos(k\theta)}k
 =-\log(2|\sin(\theta/2)|)+O((N|\theta|)^{-1}),\qquad
\left|\sum_{k=1}^Nd_k\cos(k\theta)-D_{\mathrm w}\right|
 \le C\theta^2(1+|\log|\theta||)+CN^{-2}.
```

式 (51.14)。

第一式可由 $`-\log(1-ze^{i\theta})`$ 的实部令 $`z\uparrow1`$ 得到无穷和，
尾和再用 $`|\sum_{k=m}^ne^{ik\theta}|\le C/|\theta|`$。
第二式在 $`k=1/|\theta|`$ 两侧分别用
$`1-\cos(k\theta)\le Ck^2\theta^2`$ 与 $`\sum_{k>1/|\theta|}k^{-3}\le C\theta^2`$。
结合 $`-\log(2|\sin(\theta/2)|)=-\log|\theta|+O(\theta^2)`$，
截断组间的 $`|\theta|=\omega h|x_t-x_r|`$ 位于
$`[\omega h\delta,Ch\sqrt\lambda]`$，后者趋零。
于是对 $`u\in[u_0,u_1]`$ 及所有不同组，一致地有

```math
\begin{split}
K_{N_M(u)}(0)&=2\mathfrak L+2s_M(u)+b_*+O(he^{-s_M(u)}),\\
K_{N_M(u)}(h(x_t-x_r))&=2\mathfrak L+H(x_t,x_r)+O(\eta_M),\\
\eta_M&\le C\left\{\frac{e^{-u_0/\sqrt\delta}}\delta
       +h^2\lambda(1+\mathfrak L+\log\lambda)+he^{-u_0/\sqrt\delta}\right\},
\qquad Q^2\eta_M\longrightarrow0.
\end{split}
```

式 (51.15)。

最后一式使用 $`\lambda=Q^3`$、$`\mathfrak L\asymp Q^3`$ 和
$`Q^{5/2}e^{-u_0Q^{1/4}}\to0`$。
频率取整已包含在 $`\log N_M(u)=\mathfrak L+s_M(u)+O(he^{-s_M(u)})`$ 中。
平移相位精确相消，双和展开及 $`(\sum_t|A_t|)^2\le g_M\mathcal Q_M`$ 给出

```math
\sup_{u\in[u_0,u_1]}
\left|\mathcal Z_M(u)-2uT_M-b_*\mathcal Q_M
       -\sum_{t\ne r}H(x_t,x_r)A_tA_r\right|
 \le CQ^2\eta_M\mathcal Q_M\longrightarrow0
 \quad\text{依概率}.
```

式 (51.16)。

此处先精确消去同一个 $`2\mathfrak L Y_M^2`$，再处理剩余的对数矩阵；
没有分别近似两个发散项后相减。由 $`\mathcal Q_M\to\gamma`$、(51.13)
及连续仿射映射，得到整个紧区间上的路径结论 (51.4)。
辅助平方范数的条件期望有界、中心界及同一次向量比较也给出 (51.16) 的条件概率版本。

为核对非 Gaussian 性，把 $`H`$ 对应的实对称 Hilbert–Schmidt 算子特征值记为
$`(\lambda_j)`$。经典谱分解给出
$`I_2(H)=\sum_j\lambda_j(G_j^2-1)`$，其中 $`G_j`$ 独立标准正态，级数在二阶均方收敛。
由于 $`\sum_j\lambda_j^2<\infty`$，中心化矩生成函数在零点邻域收敛，
其四阶累积量为 $`48\sum_j\lambda_j^4`$。
$`H`$ 非零，故该量严格为正；加上独立 Gaussian 的 $`2uN_2`$ 不改变四阶累积量。
这证明固定谱坐标的非 Gaussian 性，不给出实际统计量的矩收敛。

最后，支持置换保留整个数据、校准、后验与谱束，把先验混合律转移为固定支持一致的
无条件律。两种方向信息情形使用同一个方向决定；其一致事件上全部坐标精确相同，
补事件只付出趋零概率，因而保留完整联合结论。∎

## 追加锚（本行以下为增补区）
