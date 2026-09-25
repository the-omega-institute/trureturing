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
