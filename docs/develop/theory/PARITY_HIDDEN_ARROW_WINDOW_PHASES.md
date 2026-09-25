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
