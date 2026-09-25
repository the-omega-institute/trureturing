# 奇偶马尔可夫核的 Hamming 损失波动

## 27. 两种 Hamming 损失的共同波动与独立小尺度

**定义 27.1（同一数据上的两个选择规则）。** 沿用[支持恢复卷定义 21.1、23.1](PARITY_HIDDEN_ARROW_RECOVERY.md)的实际平稳独立对与连续路径实验，
以及[原卷定义 18.1](PARITY_HIDDEN_ARROW.md#18-增补十五固定振幅稀疏支持恢复与方向分离)的补偿核。
固定 $`r\in(0,1)`$、$`\beta\in(1/2,1)`$，取
$`q=M^{1-\beta+o(1)}`$，内在偏移 $`c_M\to c\in\mathbb R`$。
振幅可以为格点或非格点。规则知道维数、样本数、支持基数及振幅。
记标准化中心的极限及相应遗漏比例为

```math
z_*=\lim_M z_M=-\frac{c\phi^{3/2}}{\sqrt{\beta v}},\qquad
p_* =\Phi(z_*)\in(0,1).
```

式 (27.1)。

先假设方向已知，将完整数据对齐为正向。对均匀固定基数先验的完整数据后验，
取 $`B=\{x:\pi_x\gt1/2\}`$，并令 $`T`$ 为补偿得分最大的基数个位置，
同分处用独立均匀优先级排序。两个规则使用同一份数据。定义随机损失

```math
L_{\mathrm u}=\frac{|B\triangle S|}{q},\qquad
L_q=\frac{|T\triangle S|}{2q}=\frac{|S\setminus T|}{q}.
```

式 (27.2)。

它们的期望分别是对应的已知方向极小极大风险。
未知方向时，先按第 23 章的方向检验对齐数据，再使用上述两个规则；两个规则共享
这一次方向判决。反序操作作用于完整的对或完整路径。

**定理 27.2（精确风险中心下的联合极限）。** 对任一实际平稳实验、任一方向信息
情形以及任一真实支持，定义 27.1 的两个随机损失满足

```math
\sqrt q\begin{pmatrix}
L_{\mathrm u}-H_{\mathcal E,\mathrm u}^{\xi}\\[0pt]
L_q-H_{\mathcal E,q}^{\xi}
\end{pmatrix}
\ \Longrightarrow\
\begin{pmatrix}G\\G\end{pmatrix},
\qquad G\sim N\bigl(0,p_*(1-p_*)\bigr).
```

式 (27.3)。

这里使用各个有限实验的精确极小极大风险作中心。结论对支持一致，不要求格点相位
收敛或远离边界。未知方向的组合规则不必是有限样本的精确极小极大规则；其期望与
相应极小极大值之差为 $`O(q^{-1})`$。特别地，

```math
\sqrt q\left[
(L_{\mathrm u}-L_q)
 -(H_{\mathcal E,\mathrm u}^{\xi}-H_{\mathcal E,q}^{\xi})
\right]\ \longrightarrow\ 0
```

式 (27.4)。

最后一个收敛依概率成立。它比较的是分别除以基数及两倍基数的损失。
第 25、26 章的有限阶平均风险展开不能在此直接替代精确中心：其余项只在对数尺度受控，
并未达到本定理要求的平方根基数尺度。

证明。先处理已知正向。固定计数尾指数为十，令 $`\delta_M=\ell^3/n`$。
稀疏假设给出

```math
q\delta_M\longrightarrow0,\qquad
\frac{\lambda q^2}{n}\longrightarrow0.
```

式 (27.5)。

首先把真正支持上的所有行同时作概率比较。
使用 [Arratia–Goldstein–Gordon 的过程近似定理 2](../../../Library/Dynamics/arratia1990poisson.md)。
对一个确定的正类标记集，记大小为 $`m`$，将稀有事件按时刻、标记行和目的奇偶性编号。
同一时刻的标记事件互斥，其总概率为 $`m/n`$；一个事件的依赖邻域包含与它相距
至多两个时刻的全部标记事件。

两步转移恰为均匀投影，因而一个边块与邻域之外的过去和未来所生成的联合信息独立。
具体地，在边块两侧分别积分掉两个转移，两个连接核的每个元素都成为均匀质量；
联合密度遂分解。这也处理了同时观察远处过去与未来的情形。
所引定理的第三个依赖项因此为零。
邻域内的边缘概率乘积和至多为 $`5s(m/n)^2`$。
对两个不同时刻，把所有标记与目的符号求和后，只剩两个起点都落在标记集的概率。
相邻时刻该概率至多为固定倍数的 $`(m/n)^2`$；相隔两个时刻时起点已经独立。
同一时刻的不同标记则不能同时发生。第二个依赖项也至多为固定倍数的
$`s(m/n)^2`$。

对独立对，邻域只需同一时刻，结论相同。将近似过程按行及目的符号聚合，得到

```math
 d_{\mathrm{TV}}\left(
 \mathcal L_S((N_{x,+},N_{x,-})_{x\in S}),
 \bigotimes_{x\in S} Q_r\right)
 \le C\frac{\lambda q^2}{n}=o(1).
```

式 (27.6)。

比较律中的各个信号行独立。加入独立同分优先级不增加此距离。
这里没有将全部背景行同时独立化。
总变差趋零也不单独保证平方根尺度的均值比较；后面仍使用一行相对概率转移，
它对有界行函数给出的总均值误差至多为

```math
Cq\delta_M+CM^{1-D}=o(\sqrt q).
```

式 (27.7)。

接着记录所需的条件方差工具。
固定数据后，支持指示量 $`I_i`$ 的后验具有权重乘积除以基本对称多项式的形式。
[经典 Newton 不等式](../../../Library/Dynamics/borcea2009negative.md)
给出不同位置的条件协方差非正：删去这两个权重后，若连续三个对称多项式为
$`E_{q-2},E_{q-1},E_q`$，协方差的相反数为

```math
-\mathrm{Cov}(I_i,I_j\mid\mathcal D)
 =\frac{w_iw_j(E_{q-1}^2-E_{q-2}E_q)}{e_q(w)^2}\ge0.
```

式 (27.8)。

后验指示量总和恒为基数，故每一行协方差之和为零。于是对任意实系数，

```math
\begin{aligned}
\mathrm{Var}\left(\sum_i c_iI_i\mid\mathcal D\right)
 &=\sum_{i\lt j}\bigl[-\mathrm{Cov}(I_i,I_j\mid\mathcal D)\bigr]
          (c_i-c_j)^2\\[0pt]
 &\le2\sum_i c_i^2\pi_i(1-\pi_i).
\end{aligned}
```

式 (27.9)。

若系数依赖规则的辅助随机数，先固定这些独立随机数再使用此式。
此工具控制同一阈值原子中真实标签的损失波动，而不要求该原子包含的位置数很小。

现在比较无约束规则和确定阈值。
置 $`B_0=(M-q)/q`$、$`t_B=\log B_0`$，令 $`A=\{W\ge t_B\}`$，
按得分将它截到至多基数个元素得到 $`C`$。
沿用第 25 章的后验辅助总均值、总方差及共同倾斜参数，记为
$`U,V,t`$。一行、两行矩转移和 (27.5) 给出

```math
\mathbb E_S(U-q)^2=O(q),\qquad
\mathbb E_SV=q[p_*+o(1)],\qquad \mathrm{Var}_S V=O(q).
```

式 (27.10)。

因此存在一个补集概率为 $`O(q^{-1})`$ 的事件，在其上辅助方差至少为基数的固定
正比例，且 $`|U-q|`$ 至多为基数的一个充分小固定比例。
对辅助总均值关于对数倾斜求导，导数就是辅助方差；沿有限倾斜区间它只改变固定倍数。
结合相邻条件概率比，得到该事件上对所有位置同时成立的界

```math
|\log t|\le\frac{C|U-q|}{q},\qquad
\log\frac{\pi_i}{1-\pi_i}=W_i-t_B+\log t+O(q^{-1}).
```

式 (27.11)。

好事件中的阈值分歧落在 $`|W_i-t_B|\le1`$ 内，且其后验损失权重至多为
$`C(|U-q|+1)/q`$。记这个固定窗口内的总位置数为 $`J`$。
中央局部概率上界、精确换测度及同一支持下的矩转移给出

```math
\mathbb E_S J=O\left(\frac q{\sqrt\lambda}\right),\qquad
\mathbb E_SJ^2=O\left(\frac{q^2}{\lambda}+\frac q{\sqrt\lambda}\right).
```

式 (27.12)。

格点原子也满足此界；这里没有令窗口质量与窗口宽度成比例。
阈值输出的期望大小为 $`q[1-p_*+o(1)]`$、方差为 $`O(q)`$，
所以期望截断数为 $`O(1)`$。
在均匀固定基数先验下使用条件 Bayes 损失差，好事件上的期望损失差由
$`C(|U-q|+1)J/q`$ 和截断数控制。坏事件中两个输出总共至多有三倍基数个位置，
其期望贡献为 $`O(1)`$。Cauchy–Schwarz 不等式和 (27.10)–(27.12) 遂给出

```math
0\le\mathbb E\bigl[|C\triangle S|-|B\triangle S|\bigr]
 \le C\frac{\sqrt q}{\sqrt\lambda}+C=o(\sqrt q).
```

式 (27.13)。

同时，两个输出分歧集的期望大小至多为 $`Cq/\sqrt\lambda+C`$。
给定数据后的损失差是该集上系数为正负二的标签和加一个常数，
所以 (27.9) 将其条件方差控制为分歧集大小的两倍。
先扣除条件均值，再用平方均值控制绝对均值，得到

```math
\mathbb E\left|\,|C\triangle S|-|B\triangle S|\,\right|
 \le C\sqrt q\,\lambda^{-1/4}+C=o(\sqrt q).
```

式 (27.14)。

两规则都对支持置换等变，因此先验平均中的这一绝对误差界也是每个实际支持的误差界。
期望截断数为常数量级，故还可在 (27.14) 中将截断规则换成原阈值规则。

原阈值损失由信号遗漏数和背景误选数相加得到。背景误选数记为 $`F`$。
其比较期望为 $`O(q/\sqrt\lambda)`$，矩转移给出

```math
\mathrm{Var}_S F
 \le C\left(\frac q{\sqrt\lambda}
        +\frac{\delta_Mq^2}{\lambda}+M^{2-D}\right)=o(q).
```

式 (27.15)。

所以中心化后的背景误选数在平方根基数尺度消失。它的均值不能省去。

对于恰好基数规则，直接在补偿得分上选择一个确定阈值和同分接受比例，
使随机阈值输出 $`R`$ 的实际期望大小恰好为基数。
分数的有限支持、尾计数单调性和同分线性插值保证存在；支持置换对称性保证这个
选择不依赖真实支持。令阈值为 $`t_M`$，则

```math
t_M=t_*+O(1),\qquad
 t_* =\tau_M-\tfrac12\log\lambda+k(z_M),\qquad
 \mathbb E_S|R|=q.
```

式 (27.16)。

为验证阈值位置，使用支持恢复卷 (23.4)–(23.7) 对补偿得分直接给出的界：
中央背景尾概率具有固定正倍数上下界 $`e^{-u}/\sqrt\lambda`$。
其下界由一个足够宽的固定窗口获得，使正态窗口质量超过 Berry–Esseen 的两端误差；
随后用精确换测度。这同时覆盖格点与非格点情形。
这里只需上下界，不替换一个穿过格点的分布函数。
在 $`t_*-K`$ 处选取足够大固定常数，严格尾的期望计数超过基数一个固定比例；
在 $`t_*+K`$ 处，弱尾的期望计数低于基数一个固定比例。
单调性证明 (27.16)，而两处计数的方差为 $`O(q)`$，故真实最大基数排序的边界
也落在这个固定区间内，异常概率为 $`O(q^{-1})`$。

让随机阈值与排序规则使用同一得分、同一均匀优先级的字典序。
两个集合都是此顺序的初始片段，所以

```math
|R\triangle T|=\bigl||R|-q\bigr|,\qquad
\mathbb E_S|R\triangle T|=O(\sqrt q).
```

式 (27.17)。

第二式使用精确期望匹配和实际两行方差界。
在边界定位和 (27.11) 同时成立的事件上，所有被更换的位置都位于上述中央区间。
其后验包含概率满足

```math
\pi_i\le C\frac{e^{t_*}}{B_0}\le\frac C{\sqrt\lambda}.
```

式 (27.18)。

条件于数据和辅助随机数，分歧集中真实信号的期望数因此至多为
$`C|R\triangle T|/\sqrt\lambda`$。异常事件中这个数始终至多为基数。
取先验平均并用等变性，得到每个实际支持下

```math
\mathbb E_S\left|\,|S\setminus R|-|S\setminus T|\,\right|
 \le\frac{C\sqrt q}{\sqrt\lambda}+C=o(\sqrt q).
```

式 (27.19)。

这是信号遗漏数的比较，不是对随机阈值规则使用不等基数的 Hamming 损失。
它容许格点处有很大的背景同分组。

在独立信号比较律中，分别记确定阈值和随机阈值的单行遗漏指标为
$`Y_x^A,Y_x^R`$。这些二元对在信号行之间独立同分布，两边的期望都趋于
$`p_*`$。两个阈值相差 $`O(\log\lambda)`$，窗口概率界给出

```math
\mathbb P\{Y_x^A\ne Y_x^R\}
 \le\frac{C(1+\log\lambda)}{\sqrt\lambda}+o(1)
 \longrightarrow0.
```

式 (27.20)。

有界三角阵的联合中心极限定理遂将两列信号遗漏和送到同一个正态变量。
式 (27.6) 转移联合分布，式 (27.7) 单独转移均值。
再由 (27.14) 去掉无约束规则的损失差，由 (27.15) 去掉中心化背景误选数，
由 (27.19) 换回恰好基数规则。两个绝对均值误差都是平方根基数的小量，
所以同时允许换成各自精确期望。这就证明已知正向的 (27.3)；完整反序给出已知反向。

最后加强未知方向的错误率。
仍令方向检验计数 $`T_{\mathrm{dir}}`$ 为得分超过 $`\tau_M+\ell^{1/4}`$ 的正类起点数，
超过 $`q/\ell`$ 时判为正向。在正向实验中，只计真正信号就有基数正比例的期望、
$`O(q)`$ 的方差，故判错概率为 $`O(q^{-1})`$。
在反向实验中，设 $`\varepsilon_M=e^{-\ell^{1/4}}`$，比较期望至多为
$`q\varepsilon_M`$。实际期望最终低于判决阈值的一半。
使用两行方差界和 Chebyshev 不等式，而不是只对计数使用 Markov 不等式，得到

```math
\mathbb P_-\{T_{\mathrm{dir}}>q/\ell\}
 \le C\ell^2\left(
 \frac{\varepsilon_M}{q}
 +\delta_M\varepsilon_M^2
 +\frac{M^{2-D}}{q^2}\right)
 =O(q^{-1}).
```

式 (27.21)。

这里最后一个等号使用固定稀疏指数和 (27.5)。正确方向事件上，组合规则恰等于同一数据
上的已知方向规则。错误方向事件上的归一化损失有固定上界，因而两种组合规则的期望
与已知方向最优风险只相差 $`O(q^{-1})`$。揭示方向给出未知方向极小极大风险的下界，
组合规则给出上界，于是组合规则的期望、已知方向最优值和未知方向最优值之间
都只相差 $`O(q^{-1})`$。
这在平方根基数尺度可忽略；同一数据上的方向检验与选择规则无需独立。
因此得到未知方向的 (27.3)，再作两坐标相减得到 (27.4)。∎


**定理 27.3（共同波动之外的独立小尺度）。** 在定义 27.1 的相同条件下，置

```math
w_M=\frac{\log\lambda}{\sqrt\lambda},\qquad
\kappa_* =\frac{\varphi(z_*)}{2\sqrt v}.
```

式 (27.22)。

同一数据上的损失还满足更细的联合极限

```math
\begin{pmatrix}
\sqrt q\,(L_q-H_{\mathcal E,q}^{\xi})\\[0pt]
\sqrt{q/w_M}\bigl[(L_{\mathrm u}-L_q)
 -(H_{\mathcal E,\mathrm u}^{\xi}-H_{\mathcal E,q}^{\xi})\bigr]
\end{pmatrix}
\ \Longrightarrow\
\begin{pmatrix}G_0\\G_1\end{pmatrix}.
```

式 (27.23)。

右侧两个变量相互独立，分别服从均值为零、方差为 $`p_*(1-p_*)`$ 和
$`\kappa_*`$ 的正态分布。仍使用精确有限实验的极小极大风险作中心。

证明。沿用前一定理的补偿得分阈值和精确期望匹配规则。
两个确定阈值最终满足

```math
t_B-t_M=\tfrac12\log\lambda+O(1)\gt0.
```

式 (27.24)。

在独立信号比较律中，随机阈值遗漏的信号必被较高阈值遗漏。因此
$`J_x=Y_x^A-Y_x^R`$ 是一个零一指标，与 $`Y_x^R`$ 不能同时为一。
令其概率为 $`g_M`$。两跳幅复合 Poisson 和的 Berry–Esseen 界对严格或弱边界
都有 $`O(\lambda^{-1/2})`$ 的误差；补偿导致的均值位移为 $`O(a\lambda)`$，
标准化后可忽略。同分随机化至多改变一个原子的质量，也为
$`O(\lambda^{-1/2})`$。对 (27.24) 两端的正态分布函数作 Taylor 展开，得到

```math
g_M
 =\frac{\varphi(z_M)\log\lambda}{2\sqrt{\lambda v}}
   +O\left(\lambda^{-1/2}+
                  \frac{(\log\lambda)^2}{\lambda}\right),
\qquad \frac{g_M}{w_M}\longrightarrow\kappa_*.
```

式 (27.25)。

因此 $`g_M\to0`$ 而 $`qg_M\to\infty`$。
若 $`p_M=\mathbb E Y_x^R`$，两种互斥指标的协方差为 $`-p_Mg_M`$。
在两个不同尺度下，对应总和的方差和协方差分别趋于

```math
p_*(1-p_*),\qquad \kappa_*,\qquad
-\frac{p_Mg_M}{\sqrt{w_M}}\longrightarrow0.
```

式 (27.26)。

每个中心化单行贡献的模至多为固定倍数的
$`q^{-1/2}+(qw_M)^{-1/2}`$，趋于零。
有界三角阵的联合中心极限定理因而给出两个独立正态极限。

还需在较小的误差尺度转回实际规则。
前一定理的 (27.10)–(27.14) 实际给出无约束后验规则与确定阈值之间的原始损失
绝对均值差为 $`O(\sqrt q\lambda^{-1/4}+1)`$；其中较大的项来自条件标签方差。
式 (27.19) 给出的排序遗漏数误差为 $`O(\sqrt{q/\lambda}+1)`$。
这两者都为 $`o(\sqrt{qw_M})`$：前者还比该尺度小一个
$`\sqrt{\log\lambda}`$ 因子。期望截断数也为常数量级。
式 (27.15) 则给出

```math
\frac{\mathrm{Var}_S F}{qw_M}\longrightarrow0.
```

式 (27.27)。

所以背景误选数在这一尺度上仍须扣除均值，但其中心化波动可忽略。
式 (27.6) 仍可转移联合分布；单行均值转移 (27.7) 的误差也是
$`o(\sqrt{qw_M})`$，因为其幂尺度衰减快于这里的对数因子。
上述绝对均值比较允许把各个比较均值换成真实规则的精确均值。
未知方向造成的原始损失绝对均值误差为 $`O(1)`$，精确极小极大风险之间的
归一化差为 $`O(q^{-1})`$，在两个尺度上都可忽略。
由此得到 (27.23)。格点原子只进入 (27.25) 中较低阶的误差，故无需相位分离。∎

## 追加锚（本行以下为增补区）

## 28. 输出预算的边界波动与格点时钟

**定义 28.1（增加输出后的真实信号增益）。** 沿用定义 27.1 的实验、固定参数、
有限内在偏移及方向处理。对固定实数 $`\kappa\ge1`$，令
$`m_\kappa=\lfloor\kappa q\rfloor`$；下文取维数充分大，使其不超过正类状态数。
令 $`T_\kappa`$ 是补偿得分最大的 $`m_\kappa`$ 个位置。
所有预算使用同一份数据、同一个方向判决和同一组独立均匀同分优先级，因此这些集合嵌套。
置

```math
M_\kappa=\frac{|S\setminus T_\kappa|}{q},\qquad
D_\kappa=M_1-M_\kappa.
```

式 (28.1)。

本章使用遗漏信号比例。输出大小不等于基数时，它不等于 Hamming 损失除以两倍基数。
记相应固定输出大小的精确极小极大遗漏风险为

```math
H_{\mathcal E,\kappa}^{\xi}
 =\inf_{\widehat T:\,|\widehat T|=m_\kappa}
   \sup_{S,\,\varepsilon\in\Xi_\xi}
    \mathbb E_{S,\varepsilon}^{\mathcal E}
       \frac{|S\setminus\widehat T|}{q}.
```

式 (28.2)。

已知方向时，$`\Xi_{\mathrm k}`$ 只含给定方向且规则可使用该方向；
未知方向时，$`\Xi_{\mathrm o}=\{+,-\}`$。
在 $`\kappa=1`$ 处，这与原来的恰好基数风险相同。
已知方向的排序规则达到 (28.2)；未知方向仍使用定义 27.1 的组合规则。

为描述边界概率，定义

```math
d(z)=\frac{\varphi(z)}{\sqrt v},\qquad
b_\kappa(z)=\kappa-1+\Phi(z),\qquad
x_\kappa(z)=\log\frac{d(z)}{b_\kappa(z)},\qquad
\zeta_M=\tau_M-\tfrac12\log\lambda.
```

式 (28.3)。

非格点振幅的时钟为

```math
\Theta(\kappa)
 =d(z_*)\log\frac{\kappa-1+p_*}{p_*}.
```

式 (28.4)。

对最大格距为 $`h`$ 的格点振幅，沿用支持恢复卷第 26 章的
$`L_h=h/(e^h-1)`$、$`l_h=\log L_h`$ 及连续周期函数 $`G_h`$。
对相位 $`\omega\in\mathbb R/h\mathbb Z`$，取任一实代表，置

```math
\begin{aligned}
y_\kappa(\omega)
 &=h\left\lceil\frac{\omega+x_\kappa(z_*)+l_h}{h}\right\rceil
       -\omega-x_\kappa(z_*),\\[0pt]
C_\kappa(\omega)
 &=x_\kappa(z_*)+G_h(y_\kappa(\omega)),\\[0pt]
\Theta_\omega(\kappa)
 &=d(z_*)[C_1(\omega)-C_\kappa(\omega)].
\end{aligned}
```

式 (28.5)。

周期性使它们不依赖相位代表的选择，端点处按 $`G_h`$ 的连续延拓取值。

**定理 28.2（有限预算族的第三尺度）。** 任取有限个固定预算
$`1\le\kappa_1\le\cdots\le\kappa_m`$。
非格点情形使用 (28.4)；格点情形沿任意满足
$`\zeta_M\bmod h\to\omega`$ 的子序列使用 (28.5)。则

```math
\left(
 \sqrt{q\sqrt\lambda}\left[
  D_{\kappa_j}-(H_{\mathcal E,1}^{\xi}
                    -H_{\mathcal E,\kappa_j}^{\xi})
 \right]\right)_{j=1}^m
 \quad\Longrightarrow\quad
 \left(B(\Theta(\kappa_j))\right)_{j=1}^m.
```

式 (28.6)。

右侧 $`B`$ 为标准 Brownian 运动；格点情形将 $`\Theta`$ 换为
$`\Theta_\omega`$。两类时钟都连续、递增、凹，且在预算为一时为零。
非格点时钟光滑；格点时钟对预算分段仿射，其相邻非零斜率的比为 $`e^{-h}`$。

进一步，(28.6) 与定理 27.3 的两个坐标联合收敛，Brownian 向量与那两个正态变量
相互独立。此处只断言任意有限预算族的联合极限，不断言预算连续变化时的过程紧性。
结果对真实支持一致，适用于两个实际平稳实验及两种方向信息情形。
所有中心仍为精确有限实验风险。

证明。先设方向已知并对齐正向。均匀固定基数后验下，条件期望遗漏数为
$`q-\sum_{i\in T}\pi_i`$。后验包含概率与补偿得分同序，故固定输出大小时由
最大得分排序达到 Bayes 最优；置换等变性将其风险变成常数，因此也是极小极大风险。

对每个预算，直接在补偿得分上选取确定阈值 $`u_{\kappa,M}`$ 和同分接受比例，
构造随机阈值集 $`R_\kappa`$，使

```math
\mathbb E_S|R_\kappa|=m_\kappa.
```

式 (28.7)。

有限得分支持和同分线性插值保证存在。可按同一得分与均匀优先级的字典序作单调选择，
使各个 $`R_\kappa`$ 嵌套；在预算为一时选取第 27 章的同一个阈值规则。
支持对称性保证阈值不依赖未知支持。
支持恢复卷 (23.4)–(23.7) 的中央尾界给出

```math
u_{\kappa,M}=\zeta_M+O(1).
```

式 (28.8)。

这是因为中央信号尾占 $`1-p_*+o(1)`$ 倍基数，预算与它之间保有正间隙，
其余期望由量级为 $`e^{\tau_M-u}/\sqrt\lambda`$ 的背景尾提供。
所有常数可同时用于这里有限多个预算。

精确期望匹配及实际两行方差界给出
$`\mathbb E_S||R_\kappa|-m_\kappa|=O(\sqrt q)`$。
在 (28.8) 两侧选取足够远的固定端点，期望计数与预算相差基数的固定比例。
Chebyshev 不等式以 $`O(q^{-1})`$ 的异常概率将样本排序边界夹在这两个端点内。
再交上 (27.11) 的后验好事件，所有被更换位置的后验包含概率都至多为
$`C/\sqrt\lambda`$。同一字典序下，排序集与阈值集嵌套。
条件于数据和优先级，再作先验平均及支持对称化，得到

```math
\mathbb E_S\left|
 |S\setminus T_\kappa|-|S\setminus R_\kappa|
\right|
 \le C\sqrt{q/\lambda}+C
 =o\left(\sqrt{q/\sqrt\lambda}\right).
```

式 (28.9)。

坏事件中被更换的真实信号数始终至多为基数，故其贡献为常数量级。
这一步控制真实信号数，不以全部背景位置的集合差替代它。

现在识别两个阈值之间的单行信号质量。在独立信号比较律及同分优先级下，令

```math
J_{i,\kappa}
 =\mathbf1_{\{i\in R_\kappa\}}
     -\mathbf1_{\{i\in R_1\}},\qquad
 g_{\kappa,M}=\mathbb E_{Q_r}J_{i,\kappa}.
```

式 (28.10)。

这些零一指标随预算嵌套。

非格点情形，由局部极限定理、精确换测度和实际期望匹配，得

```math
b_\kappa(z_M)
 =d(z_M)e^{\zeta_M-u_{\kappa,M}}+o(1),\qquad
u_{\kappa,M}=\zeta_M+x_\kappa(z_M)+o(1).
```

式 (28.11)。

这里使用支持恢复卷第 25 章的局部尾估计。
补偿得分与非格点固定得分在对数计数截断上相差任意对数幂的小量。
先以固定小宽度夹住差异，再用局部极限定理，最后令宽度趋零，可知端点原子及
补偿差异均为 $`o(\lambda^{-1/2})`$。所以长度为常数量级的信号区间满足

```math
\sqrt\lambda\,g_{\kappa,M}
 =d(z_M)\log\frac{b_\kappa(z_M)}{b_1(z_M)}+o(1)
 \longrightarrow\Theta(\kappa).
```

式 (28.12)。

仅用分布函数的 Berry–Esseen 误差不能识别这里的常数；本步骤确实使用局部极限定理。

格点情形需保留边界相位。令 $`G_M`$ 为计数截断事件，两种比较律下的
截断外概率均取为 $`O(M^{-D})`$，其中 $`D`$ 可任取充分大的固定值。截断上令
$`\eta_M=\sup|W-Z|`$，它小于任意固定的负对数幂。
当 $`2\eta_M\lt h`$ 时，确定的补偿阈值至多切开一个固定得分层
$`b\in h\mathbb Z`$，更高层全选，更低层全不选。
令 $`\alpha`$ 为该层内被接受部分与 $`G_M`$ 交集的信号质量，除以完整边界层的
信号质量；接受事件包括独立同分随机数。无需假定补偿在该层内均匀选择：
对任意可测子集 $`E\subseteq\{Z=b\}\cap G_M`$，精确换测度给出

```math
e^{-b-\eta_M}Q_r(E)\le Q_{-a}(E)\le e^{-b+\eta_M}Q_r(E).
```

式 (28.13)。

这些界也适用于零质量或任意小质量的接受子集。
截断外只使用加性界：信号质量为 $`O(M^{-D})=o(\lambda^{-1/2})`$，
背景质量乘以 $`(M-q)/q`$ 后为 $`O(M^{1-D}/q)=o(1)`$。
因此同一有效接受比例控制背景主项；不把截断外误差写成相对误差。
格点局部极限定理、几何尾及实际期望匹配给出

```math
b_\kappa(z_M)
 =d(z_M)e^{\zeta_M-b}(L_h+\alpha h)+o(1).
```

式 (28.14)。

令 $`y=b-\zeta_M-x_\kappa(z_M)`$，则
$`e^y=L_h+\alpha h+o(1)`$，故其代表落在
$`[l_h,l_h+h]+o(1)`$ 内。
支持恢复卷 (26.8) 的严格边界展开加上未接受的边界质量，给出单行遗漏概率

```math
p_{\kappa,M}
 =\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
 \left[
 A(z_M)+\frac{-\tfrac12\log\lambda+x_\kappa(z_M)
                         +y+h/2-\alpha h}{\sqrt v}
 \right]+o(\lambda^{-1/2}).
```

式 (28.15)。

其中 $`A`$ 是第 25、26 章的共同第三累积量项，在预算相减时消去。
代入 (28.14)，并使用 $`G_h(l_h)=G_h(l_h+h)`$，得到

```math
\begin{aligned}
y_{\kappa,M}
 &=h\left\lceil\frac{\zeta_M+x_\kappa(z_M)+l_h}{h}\right\rceil
       -\zeta_M-x_\kappa(z_M),\\[0pt]
C_{\kappa,M}&=x_\kappa(z_M)+G_h(y_{\kappa,M}),\\[0pt]
\sqrt\lambda\,g_{\kappa,M}
 &=d(z_M)(C_{1,M}-C_{\kappa,M})+o(1).
\end{aligned}
```

式 (28.16)。

端点匹配使边界层改变时的误差仍为小量，不要求相位远离切换点。
这里计算的是同一补偿阈值规则的单行质量，没有把补偿排序和固定得分排序的
随机损失当成等价。若 $`\zeta_M\bmod h\to\omega`$，(28.16) 的右侧趋于
$`\Theta_\omega(\kappa)`$。

固定 (28.16) 中由上取整选定的规范格点层 $`b`$ 时，系数满足

```math
C_{\kappa,M}
 =b-\zeta_M+h/2+L_h
   -\frac{e^{b-\zeta_M}}{d(z_M)}\,b_\kappa(z_M).
```

式 (28.17)。

因此时钟在这一预算区间内的斜率是 $`e^{b-\zeta_M}\gt0`$。
预算增加而边界下降一个格距时，斜率乘以 $`e^{-h}`$。
端点连续性证明分段仿射时钟递增且凹；非格点时钟的同样性质由 (28.4) 直接求导得到。

在独立信号比较律中，不同行的整个预算指标向量独立同分布。
嵌套性给出

```math
\mathrm{Cov}(J_{i,\kappa},J_{i,\kappa'})
 =g_{\min(\kappa,\kappa'),M}
    -g_{\kappa,M}g_{\kappa',M}.
```

式 (28.18)。

由 (28.12) 或 (28.16)，乘以 $`\sqrt\lambda`$ 后趋于
$`\Theta(\min(\kappa,\kappa'))`$。
各行在标准化总和中的贡献至多为固定倍数的
$`\lambda^{1/4}/\sqrt q\to0`$，故多元 Lindeberg 定理给出 Brownian 有限维协方差。
式 (27.6) 的过程总变差界转移联合分布；单行相对概率界单独控制总均值误差
$`O(q\delta_M+M^{1-D})=o(\sqrt{q/\sqrt\lambda})`$。
再用 (28.9) 的绝对均值误差，便可换回实际排序规则并换成其精确期望。

增长局部计数的高斯经验过程极限有
[Einmahl–Mason 定理 1.1](../../../Library/Dynamics/einmahl1997local.md)
的经典先例；其中稀有局部质量趋零时，极限协方差为局部交集质量。
同一经验分布的全局与局部极限可渐近独立，参见
[Ferger–Vogel 定理 2.1](../../../Library/Dynamics/ferger2015empirical.md)
的 Brownian 桥与双侧 Poisson 极限。这里的局部期望计数趋于无穷，
所需高斯尺度及相位时钟由 (28.12)、(28.16) 确定。

最后与前两尺度同时比较。在信号比较律中，令
$`Y_i=\mathbf1_{\{i\notin R_1\}}`$，并沿用第 27 章较高阈值规则的对数区间指标
$`J_i^{\mathrm{log}}`$。有 $`J_{i,\kappa}\le Y_i`$，
而 $`J_{i,\kappa}J_i^{\mathrm{log}}=0`$。因此对应的单行协方差为

```math
\mathrm{Cov}(Y_i,J_{i,\kappa})
 =(1-p_{1,M})g_{\kappa,M},\qquad
\mathrm{Cov}(J_i^{\mathrm{log}},J_{i,\kappa})
 =-g_M g_{\kappa,M}.
```

式 (28.19)。

在各自的总和尺度下，前者为 $`O(\lambda^{-1/4})`$，后者为
$`O(\sqrt{\log\lambda}/\sqrt\lambda)`$，均趋于零。
联合三角阵中心极限定理遂给出三部分之间的独立性。
这里对无约束规则仍只使用第 27 章自身所需的误差尺度，不将它的比较误差强行缩到
本章更小的尺度；第三部分只涉及已经由 (28.9) 控制的排序规则。

未知方向时，(27.21) 的判错概率为 $`O(q^{-1})`$，遗漏损失有界于一。
组合规则相对已知方向规则的原始遗漏数绝对均值误差为 $`O(1)`$，小于
$`\sqrt{q/\sqrt\lambda}`$。揭示方向与组合规则分别给出 (28.2) 的下、上界，
故组合规则期望与相应精确未知方向风险相差 $`O(q^{-1})`$。
这也小于所有三个归一化尺度所容许的中心误差。
从而得到未知方向的联合结论；置换等变性保证支持一致性。∎

## 追加锚（本行以下为增补区）

## 29. 整条预算曲线的函数极限

**定义 29.1（紧预算区间上的中心化增益过程）。** 沿用定义 28.1，固定
$`K\gt1`$，令预算遍历 $`[1,K]`$。每个预算仍取输出大小
$`m_\kappa=\lfloor q\kappa\rfloor`$，使用同一份数据和同分优先级。置

```math
\mathcal Z_M(\kappa)
 =\sqrt{q\sqrt\lambda}\left[
 D_\kappa-(H_{\mathcal E,1}^{\xi}
                    -H_{\mathcal E,\kappa}^{\xi})\right].
```

式 (29.1)。

它是预算网格上的右连续阶梯函数，视为带 $`J_1`$ 拓扑的
$`D[1,K]`$ 中的随机元。记 $`\Theta`$ 为 (28.4) 的时钟；格点情形沿
$`\zeta_M\bmod h\to\omega`$ 的任意子序列，将其换成 (28.5) 的
$`\Theta_\omega`$。

**定理 29.2（实际排序规则的预算过程）。** 在定义 27.1 的条件下，

```math
\mathcal Z_M\quad\Longrightarrow\quad B\circ\Theta
 \qquad\text{于 }D[1,K].
```

式 (29.2)。

收敛可与 (27.23) 的两个坐标联合，极限中的 Brownian 过程与两个正态变量
相互独立。结论对真实支持一致，适用于两个平稳实验和两种方向信息情形。
格点时钟的折点不需要可微性。

证明。先设方向已知。对每个整数 $`q\le j\le\lfloor Kq\rfloor`$，
选取 (28.7) 中期望输出大小恰为 $`j`$ 的直接补偿阈值规则 $`R_j`$。
所有规则按同一字典序嵌套，且 $`R_q`$ 使用第 27 章的选择。
置 $`N_j=|R_j|`$，$`T_j`$ 为前 $`j`$ 个位置。

先建立实际数据下的统一计数界。令 $`\ell=\log M`$、
$`\delta_{4,M}=\ell^5/n`$。原始卷 (19.9) 的至多四行相对比较，
对独立优先级积分后仍成立。若 $`0\le f_x\le1`$ 是各行的非负函数，
$`\mu=\sum_x\mathbb E_Qf_x`$ 为相应独立行比较律中的总均值，则

```math
\mathbb E_S\left|\sum_x f_x-\mu\right|^4
 \le C\left[\mu+\mu^2
       +\delta_{4,M}(1+\mu)^4+M^{4-D}\right].
```

式 (29.3)。

这里的比较律按行类型使用信号律或背景律，实际背景行并未被设为独立。
为证此式，展开至四阶原始矩并按不同的行索引分组；每组最多涉及四行，
可用相对比较。独立和的中心四阶矩不超过 $`C(\mu+\mu^2)`$，
所有相对误差经中心化展开后不超过 $`C\delta_{4,M}(1+\mu)^4`$。
逐项的截断余项总计至多为 $`CM^{4-D}`$。
单行均值比较及 Jensen 不等式也允许把中心换成实际均值，并保持这个界。
下文选择任意充分大的固定截断指数 $`D`$。

对于整数 $`i\lt j`$，增量 $`N_j-N_i`$ 是非负行指标之和，
实际期望恰为 $`j-i`$。单行相对比较保证其比较均值与
$`j-i\ge1`$ 相当。因 $`q^2\delta_{4,M}\to0`$，(29.3) 给出

```math
G_j=\frac{N_j-j}{\sqrt q},\qquad
\mathbb E_S|G_j-G_i|^4
 \le C\left|\frac{j-i}{q}\right|^2,\qquad
\mathbb E_S|G_q|^4\le C.
```

式 (29.4)。

单行项可由 $`j-i\le(j-i)^2`$ 吸收；相对误差项则用
$`j-i\le Kq`$ 及 $`\delta_{4,M}q^2\to0`$ 吸收。
因此此式一直有效到相邻预算网格，不只是固定距离的增量。

在节点 $`j/q`$ 之间线性插值 $`G_j`$，并在最后不足一个网格的区间取常数。
同一网格内，插值增量的四次幂多出相对长度的四次幂；跨越网格时拆成两端及
中间三段，并用 $`L^4`$ 三角不等式，便将 (29.4) 延伸到所有实预算。
二进分割第 $`k`$ 层的最大增量，其期望至多为
$`C(2^k2^{-2k})^{1/4}=C2^{-k/4}`$。求和可得

```math
\mathbb E_S D_N\le C\sqrt q,\qquad
D_N=\max_{q\le j\le\lfloor Kq\rfloor}|N_j-j|.
```

式 (29.5)。

这同时给出插值过程的紧性。阶梯版本与插值版本之差至多为最大相邻网格增量，
由 (29.4) 与联合界，其超过任意固定正数的概率为 $`O(q^{-1})`$。

接着控制真实信号数的统一误差。只需用区间两端预算的期望计数，便可选择
$`\zeta_M\pm C_K`$，把全部确定阈值和全部样本排序边界同时夹住，
异常概率为 $`O(q^{-1})`$。这是 (28.8) 的端点论证及两行方差界；
不对 $`O(q)`$ 个预算分别取异常事件。交上 (27.11) 的后验好事件，
所涉及排名区间内的所有后验包含概率都至多为 $`C_K/\sqrt\lambda`$。

条件于完整数据及优先级。固定基数乘积权重后验的概率母多项式为

```math
\frac{e_q(w_1z_1,\ldots,w_Mz_M)}{e_q(w_1,\ldots,w_M)},
\qquad w_i=e^{W_i}\gt0.
```

式 (29.6)。

它实稳定：从 $`\prod_i(t+w_i z_i)`$ 出发，对 $`t`$ 微分
$`M-q`$ 次后令 $`t=0`$，使用稳定多项式的微分和实特化封闭性即可。
[Borcea–Brändén–Liggett 定理 4.9](../../../Library/Dynamics/borcea2009negative.md)
因而给出负关联。对任意条件后固定的索引集 $`I`$ 及 $`t\ge0`$，
这一经典性质蕴含

```math
\mathbb E\left[e^{t\sum_{i\in I}\mathbf1_{\{i\in S\}}}
                       \mid\mathcal D,U\right]
 \le\prod_{i\in I}[1+(e^t-1)\pi_i]
 \le\exp\left((e^t-1)\sum_{i\in I}\pi_i\right).
```

式 (29.7)。

同一总排序中的 $`R_j\mathbin\triangle T_j`$ 是一个区间，长度不超过
$`D_N`$。条件于数据和优先级后，$`D_N`$ 及这些区间都是确定的。
在上述好事件中，考虑中央得分带内所有长度不超过 $`D_N`$ 的排名区间；
其数目不超过 $`M(M+1)/2`$。在 (29.7) 取 $`t=1`$ 并对这些区间取联合界，得到

```math
\mathbb P\left\{
 \max_I|I\cap S|\gt
       \frac{C D_N}{\sqrt\lambda}+2\log M+u
       \ \middle|\ \mathcal D,U\right\}\le e^{-u},
 \qquad u\ge0.
```

式 (29.8)。

积分尾界，再用 (29.5)，坏事件中将真实信号数截在 $`q`$，得到

```math
\mathbb E_S\max_j
 \left|\,|S\setminus T_j|-|S\setminus R_j|\,\right|
 \le C\sqrt{q/\lambda}+C\log M+C
 =o\left(\sqrt{q/\sqrt\lambda}\right).
```

式 (29.9)。

先在均匀支持先验下完成条件平均，再由置换等变性转到每个固定支持。
不能把已固定的真实标签当成后验随机变量，也不能把最大标签计数的期望替换成
最大后验期望；(29.7)–(29.8) 正是控制这个差别。

余下先在独立信号比较律中证明稀有经验过程的极限。对实预算令
$`R_\kappa=R_{\lfloor q\kappa\rfloor}`$，并沿用 (28.10) 的嵌套指标
$`J_{i,\kappa}`$ 和均值 $`g_M(\kappa)`$。
式 (28.12)、(28.16) 给出沿所取相位序列的逐点收敛。
由于均值随预算单调，而极限时钟连续，有限分割夹逼将它提升为

```math
\sup_{1\le\kappa\le K}
 \left|\sqrt\lambda\,g_M(\kappa)-\Theta(\kappa)\right|
 \longrightarrow0.
```

式 (29.10)。

在格点情形，这一步只使用连续性，不要求时钟在折点可微。

令 $`V_M=\sum_{i\in S}J_{i,K}`$。它服从参数
$`q,g_M(K)`$ 的二项分布，且 $`qg_M(K)\to\infty`$。
条件于 $`V_M`$，这些被新捕获信号的进入预算独立同分布，分布函数为

```math
F_M(\kappa)=\frac{g_M(\kappa)}{g_M(K)},\qquad
F_M\longrightarrow F=\frac{\Theta}{\Theta(K)}
\quad\text{一致收敛}.
```

式 (29.11)。

可把 $`V_M`$ 与一列独立均匀变量独立构造，再经 $`F_M`$ 的广义逆生成进入预算。
于是稀有计数过程恰可写成随机样本量的均匀经验过程与总数的组合。
经典均匀经验过程定理可由
[Ferger–Vogel 定理 2.1](../../../Library/Dynamics/ferger2015empirical.md)
的全局分量取均匀分布得到。其 Brownian 桥极限连续，故可与一致收敛的
$`F_M`$ 复合。条件于趋向无穷的随机样本量，桥极限的条件分布趋向同一常律；
再用二项中心极限定理，桥与总数的正态极限联合独立。因此

```math
\frac{\sum_{i\in S}[J_{i,\kappa}-g_M(\kappa)]}
       {\sqrt{q/\sqrt\lambda}}
 \quad\Longrightarrow\quad
 \sqrt{\Theta(K)}\,[\mathbb B(F(\kappa))+Z F(\kappa)]
 \quad\text{于 }D[1,K].
```

式 (29.12)。

这里 $`\mathbb B`$ 是标准 Brownian 桥，$`Z`$ 是与它独立的标准正态变量。
右侧的协方差为 $`\Theta(\min(\kappa,\kappa'))`$，所以其分布就是
$`B\circ\Theta`$。这个经验桥分解是经典概率工具；实际实验的统一比较由
(29.3)–(29.9) 提供。

对于每个维数，整条阈值曲线是有限多个行计数及优先级的可测右连续阶梯函数。
故 (27.6) 的全信号向量总变差界可转移这一完整 $`D[1,K]`$ 随机元的分布。
均值须另行转移：单行相对界一致地给出

```math
\sup_{1\le\kappa\le K}
 \left|\mathbb E_S\sum_{i\in S}J_{i,\kappa}-qg_M(\kappa)\right|
 \le Cq\delta_M+CM^{1-D}
 =o\left(\sqrt{q/\sqrt\lambda}\right).
```

式 (29.13)。

式 (29.9) 还同时控制规则曲线及其精确均值曲线的一致差。
因此可将 (29.12) 换成真实排序增益并用精确期望作中心。
已知方向时，后验排序与支持对称性将其精确期望识别为 (28.2)。

未知方向时，所有预算共用同一方向判决。在判对事件上，两条完整曲线相同；
判错概率为 $`O(q^{-1})`$，任意预算的原始遗漏数差不超过 $`q`$。
于是规则曲线的原始一致误差期望为 $`O(1)`$。揭示方向与组合规则的夹逼
还把全部预算的未知方向极小极大中心误差一致控制在 $`O(q^{-1})`$。
这些量在 (29.1) 的尺度下均可忽略，证明未知方向的 (29.2)。
对任一方向信息情形，增加一个输出位置不能增大风险，删去一个位置至多增加
$`q^{-1}`$ 的遗漏风险。因此相邻输出大小的精确风险之差位于
$`[0,q^{-1}]`$，中心阶梯的归一化跳幅至多为
$`\lambda^{1/4}/\sqrt q\to0`$；真实信号计数的每步跳幅也至多为一。

最后，(27.23) 的两个标量坐标紧，以上给出曲线的紧性，而定理 28.2
给出它们与任意有限个预算值的联合极限。连续 Brownian 时钟过程的分布由
稠密可数预算集合上的取值唯一确定；故任意子序列极限均为所述乘积分布。
这证明联合收敛及过程与前两坐标的独立性。所有比较对支持等变，故支持一致性成立。∎

## 追加锚（本行以下为增补区）

## 30. 增长预算中的相位消失与独立过程

**定义 30.1（幂增长预算曲线）。** 沿用定义 27.1，固定 $`A\gt0`$。
对 $`\gamma\in[0,A]`$ 取输出大小
$`m_{M,\gamma}=\lfloor q\lambda^\gamma\rfloor`$，维数充分大时它小于
$`M`$。所有预算使用同一数据、方向判决和同分优先级，按补偿得分选取
前 $`m_{M,\gamma}`$ 个位置，记为 $`T_{M,\gamma}`$。
令 $`H_{M,\gamma}^{\xi}`$ 为 (28.2) 在此输出大小下的精确极小极大
遗漏风险，并定义

```math
\begin{aligned}
D_{M,\gamma}
 &=\frac{|S\setminus T_{M,0}|-|S\setminus T_{M,\gamma}|}{q},\\[0pt]
w_M&=\frac{\log\lambda}{\sqrt\lambda},\qquad
 d_*=\frac{\varphi(z_*)}{\sqrt v},\\[0pt]
\mathcal V_M(\gamma)
 &=\sqrt{\frac q{w_M}}\left[
 D_{M,\gamma}-(H_{M,0}^{\xi}-H_{M,\gamma}^{\xi})\right].
\end{aligned}
```

式 (30.1)。

此过程为 $`[0,A]`$ 上的右连续阶梯函数，在零处恒为零。

**定理 30.2（增长预算的连续时钟）。** 在定义 27.1 的条件下，

```math
\mathcal V_M\quad\Longrightarrow\quad
 \bigl(B_0(d_*\gamma)\bigr)_{0\le\gamma\le A}
 \qquad\text{于 }D[0,A]\text{ 的 }J_1\text{ 拓扑}.
```

式 (30.2)。

这里 $`B_0`$ 为标准 Brownian 运动。非格点与格点振幅均成立；单独的
(30.2) 不要求格点相位收敛。它可与 (27.23) 的两个标量坐标联合收敛，
三个极限相互独立。进一步，固定 $`K\gt1`$，在非格点情形或沿第 29 章
所需的格点相位子序列，可同时加入整条 $`\mathcal Z_M`$ 曲线；此时
$`B_0`$ 与 $`B\circ\Theta`$ 及上述两个标量极限相互独立。
结论对真实支持一致，适用于两个平稳实验与两种方向信息情形。

证明。先设方向已知。置 $`J_{\max}=\lfloor q\lambda^A\rfloor`$。
对每个整数 $`q\le j\le J_{\max}`$，选取使用共同优先级的嵌套补偿阈值集
$`R_j`$，使其实际期望大小恰为 $`j`$；在 $`j=q`$ 处沿用第 27、28 章
的同一阈值。记 $`N_j=|R_j|`$，得分边界为 $`u_j`$。

首先将阈值定位推广到增长区间。比较律下，直接补偿得分 $`W`$ 是
跳幅一致有界的复合 Poisson 和，均值为 $`\lambda\phi+O(\lambda a_M)`$、
方差为 $`\lambda v+O(\lambda a_M)`$，其中
$`a_M=rq/(M-q)`$。将其拆成 $`\lfloor\lambda\rfloor`$ 个强度有界的独立
复合 Poisson 和，Berry–Esseen 界给出一致的 $`O(\lambda^{-1/2})`$ CDF 误差。
均值和方差的补偿改变量在此尺度可忽略。
在 $`|u-\zeta_M|\le A\log\lambda+C`$ 内，每个固定宽度区间的信号
质量至多为 $`C'/\sqrt\lambda`$；选取一个足够大的固定宽度，正态区间
质量严格超过两端的 CDF 误差，便得到同阶的正下界。
精确换测度 $`dQ_r=e^W dQ_{-a_M}`$ 遂将背景尾质量夹在
$`e^{-u}/\sqrt\lambda`$ 的两个固定倍数之间：上界由固定宽度区间的
几何和给出，下界只用紧贴边界的一个区间。
因此除以基数后的背景期望数，与 $`e^{\tau_M-u}/\sqrt\lambda`$ 相当。
这些估计同时涵盖严格尾和弱尾、格点和非格点得分。
单行实际比较的截断余项单独作加法控制；乘以背景总行数后仍可忽略。
同一窗口内信号接受比例为 $`1-p_*+o(1)`$，一致余项来自窗口宽度
$`O(\log\lambda)=o(\sqrt\lambda)`$。
在期望大小等于 $`j`$ 的规则中，背景提供的期望数因而与 $`j`$ 相当：
$`j\ge2q`$ 时用信号总数至多为 $`q`$，$`q\le j\le2q`$ 时用
$`p_*\gt0`$。在候选位置两侧取足够大的固定裕量并用单调性夹逼，得到

```math
u_j=\zeta_M-\log(j/q)+O_A(1),
\qquad q\le j\le J_{\max}.
```

式 (30.3)。

这个界来自实际均值校准；未把比较律中的预算方程定义为实际阈值。

为了同时比较全部排序边界，置 $`J_k=q2^k`$，将整数预算分成
$`[J_k,\min(2J_k,J_{\max})]`$ 上的二进区间，略去空区间。
区间数为 $`O_A(\log\lambda)`$。令

```math
D_k=\max_{J_k\le j\le\min(2J_k,J_{\max})}|N_j-j|.
```

式 (30.4)。

这里及以下最大值只取整数预算。原卷 (19.9) 与 (29.3) 对至多四行的
比较仍适用，并且

```math
\delta_{4,M}J_{\max}^2
 =\frac{(\log M)^5}{n}\,J_{\max}^2\longrightarrow0.
```

式 (30.5)。

因此 (29.4) 的增量估计可在每个区间把 $`q`$ 换为 $`J_k`$，其常数
对 $`k`$ 一致；区间左端的中心四阶矩也以 $`J_k^2`$ 为界。
沿用 (29.5) 的插值与二进分割求和，得到

```math
\mathbb E_S D_k\le C_A\sqrt{J_k}.
```

式 (30.6)。

这一步比较真实数据下的背景计数，未假设背景行独立。

在每个区间的两个极端阈值外加固定得分裕量。由 (30.3)，这些端点的
期望输出数与对应预算相差固定倍数的 $`J_k`$。
两行方差界及 Chebyshev 不等式将边界定位失败概率控制为
$`C_A/J_k+C_A\delta_M`$，另有任意高次可忽略的截断余项。
对全部区间求和，再交上 (27.11) 的后验好事件，所得事件 $`\mathcal G_M`$
满足

```math
\mathbb P_S(\mathcal G_M^c)=O(q^{-1}),\qquad
\pi_i\le r_k:=\frac{C_Aq}{J_k\sqrt\lambda}
```

式 (30.7)。

第二个不等式适用于第 $`k`$ 个区间内任何阈值与对应排序边界之间的位置。
它使用同一个固定基数后验倾斜参数：在 (30.3) 的得分带上，
$`\pi_i\le C e^{W_i-\tau_M}`$。
概率求和合法，因为 $`\sum_kJ_k^{-1}\le2/q`$，且
$`\delta_M\log\lambda=o(q^{-1})`$。

条件于完整数据和优先级，所有 $`D_k`$ 及排名区间均已确定。
固定基数乘积权重后验满足 (29.7) 的负关联指数矩界；其经典依据仍为
[Borcea–Brändén–Liggett 定理 4.9](../../../Library/Dynamics/borcea2009negative.md)。
对于第 $`k`$ 个得分带中长度至多为 $`D_k`$ 的任一排名区间，取指数参数为一，
指数矩至多为 $`\exp((e-1)r_kD_k)`$。
先对同一排序中的全部至多 $`M(M+1)/2`$ 个区间，以各自的后验均值
作一次条件 Chernoff 联合界，再对每个区间使用所属得分带的上界。于是
在 $`\mathcal G_M`$ 上，

```math
\mathbb P\left\{
 \max_{k,I}|I\cap S|\gt
 (e-1)\max_k(r_kD_k)+2\log M+u
 \ \middle|\ \mathcal D,U\right\}\le e^{-u},
 \qquad u\ge0.
```

式 (30.8)。

对尾积分并取平均时，决定性的加权和为

```math
\begin{aligned}
\mathbb E_S\max_k(r_kD_k)
 &\le\sum_k r_k\mathbb E_S D_k\\[0pt]
 &\le C_A\sqrt{q/\lambda}\sum_{k\ge0}2^{-k/2}
 \le C'_A\sqrt{q/\lambda}.
\end{aligned}
```

式 (30.9)。

虽然大预算的计数误差随 $`\sqrt{J_k}`$ 增长，相关位置的信号后验概率按
$`q/J_k`$ 衰减，使该和收敛。用 (30.7) 控制坏事件，先在均匀支持先验下
条件平均，再由置换等变性转到每个固定支持，便得到

```math
\mathbb E_S\max_{q\le j\le J_{\max}}
 \left|\,|S\setminus T_j|-|S\setminus R_j|\,\right|
 \le C_A\sqrt{q/\lambda}+C_A\log M+C_A
 =o\bigl(\sqrt{qw_M}\bigr).
```

式 (30.10)。

这里 $`T_j`$ 表示输出大小为 $`j`$ 的排序集。
不能用整个增长区间的无权计数最大误差乘以最坏的后验上界代替 (30.9)，
也没有交换最大值与条件期望。

现在识别比较律中的时钟。令 $`R_{M,\gamma}=R_{m_{M,\gamma}}`$，并对信号行置

```math
J_{i,\gamma}
 =\mathbf1_{\{i\in R_{M,\gamma}\}}
   -\mathbf1_{\{i\in R_q\}},\qquad
 g_M(\gamma)=\mathbb E_{Q_r}J_{i,\gamma}.
```

式 (30.11)。

对每个固定 $`\gamma\gt0`$，(30.3) 给出两个边界相距
$`\gamma\log\lambda+O_A(1)`$。计数截断上补偿误差趋零；格点边界质量及
固定宽度误差均为 $`O(\lambda^{-1/2})`$。
第 19 章的正态近似在这个对数宽度区间给出

```math
g_M(\gamma)=d_*\gamma w_M+o(w_M).
```

式 (30.12)。

正态密度在该窗口一致趋向边界密度，CDF 近似的
$`O(\lambda^{-1/2})`$ 误差除以 $`w_M`$ 后趋零；这里不以 CDF 误差推断
常数宽度局部概率。$`\gamma=0`$ 时两侧恒为零。
由于 $`g_M`$ 单调且极限连续，有限分割夹逼进一步给出

```math
\sup_{0\le\gamma\le A}
 \left|g_M(\gamma)/w_M-d_*\gamma\right|\longrightarrow0.
```

式 (30.13)。

格点相位对单个边界造成的有界修正，除以对数带宽后消失；此处没有选择相位子序列。

独立信号比较律下，$`\sum_iJ_{i,A}`$ 为参数 $`q,g_M(A)`$ 的二项变量，
其均值趋于无穷。条件于总数，进入预算的参数独立同分布，其分布函数
$`g_M(\gamma)/g_M(A)`$ 一致趋于 $`\gamma/A`$。
用 (29.11)–(29.12) 的均匀经验桥与二项总数分解，得到

```math
\left(
 \frac{\sum_{i\in S}[J_{i,\gamma}-g_M(\gamma)]}{\sqrt{qw_M}}
\right)_{0\le\gamma\le A}
 \quad\Longrightarrow\quad B_0(d_*\gamma).
```

式 (30.14)。

所用经验桥为经典工具；其与局部 Gaussian 过程的关系见
[Einmahl–Mason](../../../Library/Dynamics/einmahl1997local.md)，
随机样本量分解所需的全局经验桥见
[Ferger–Vogel](../../../Library/Dynamics/ferger2015empirical.md)。
本处的改变分布函数及真实数据比较已分别由 (30.13) 与 (30.10) 给出。

整条阈值曲线是信号行计数和优先级的可测函数，故 (27.6) 的全信号向量
总变差界转移其 $`D[0,A]`$ 分布。均值另由一致的单行相对比较控制：
总误差至多为 $`Cq\delta_M+CM^{1-D}=o(\sqrt{qw_M})`$。
式 (30.10) 同时转移真实排序曲线及其精确期望中心。
已知方向时后验排序与对称性给出精确极小极大中心。
未知方向时全部预算共用方向判决，判错概率为 $`O(q^{-1})`$；整个曲线的
原始遗漏数误差至多为 $`q`$，因而一致误差期望为 $`O(1)`$。
揭示方向与组合规则的夹逼同时控制每个预算的精确风险中心。
相邻输出大小的风险差在 $`[0,q^{-1}]`$ 内，归一化中心及计数跳幅均至多为
$`1/\sqrt{qw_M}\to0`$。这证明 (30.2)。

最后在同一个独立信号数组上核对联合极限。
共同遗漏指标与任一增长预算指标的协方差为 $`O(w_M)`$，标准化后为
$`O(\sqrt{w_M})`$；第 27 章上方对数带与本章下方预算带互不相交，
两者质量均为 $`O(w_M)`$，标准化协方差为 $`O(w_M)`$。
固定紧区间上的窄预算带质量为 $`O(\lambda^{-1/2})`$；它与任一增长预算带
的交集质量不超过此数。因此对两种归一化，其协方差一致地为

```math
O\left(
 \frac{\lambda^{-1/2}}{
       \sqrt{\lambda^{-1/2}w_M}}
\right)=O\bigl((\log\lambda)^{-1/2}\bigr)\longrightarrow0.
```

式 (30.15)。

在 $`\gamma=0`$ 处增长预算指标恒为零。
所有单行向量有界，最小的有效总方差尺度 $`q/\sqrt\lambda`$ 仍趋于无穷，
所以联合三角数组中心极限定理给出块间独立的有限维 Gaussian 极限。
各曲线的紧性与 (27.23) 两个坐标的紧性，结合连续极限在稠密预算集合上
由取值确定其分布，将有限维结论提升为联合过程收敛。
各实际规则的替换使用其各自尺度的误差界，支持一致性由等变性保持。

对固定 $`\kappa\in[1,K]`$，取 $`\gamma_M=\log\kappa/\log\lambda`$，
则两章使用的排序集和精确中心相同，并且恒有

```math
\mathcal V_M(\gamma_M)
 =\frac{\mathcal Z_M(\kappa)}{\sqrt{\log\lambda}}.
```

式 (30.16)。

因此增长预算过程在这个趋零参数处消失，而更细的归一化仍保留第 29 章的
非退化相位时钟。这是同一数据上的两种同时归一化，以上联合证明已给出它们的关系。∎

## 追加锚（本行以下为增补区）

## 31. 格点间隙上的精确容量与非正态波动

**定义 31.1（与间隙阈值配对的容量）。** 沿用定义 27.1，固定格点振幅，
其最大格距为 $`h\gt0`$。取 $`b_M\in h\mathbb Z`$ 满足
$`b_M-\tau_M\to s\in\mathbb R`$。先对齐到正确方向，并置

```math
A_M=\{i:W_i\gt b_M+h/2\},\qquad
N_M=|A_M|,\qquad C_M=|A_M\cap S|,\qquad
m_M=\lfloor\mathbb E_S N_M\rfloor.
```

式 (31.1)。

支持对称性使这个确定容量不依赖未知的支持位置。
令 $`T_M`$ 选取补偿得分最大的 $`m_M`$ 个位置，同分处用独立优先级。
未知方向时先作定义 27.1 的同一方向判决，仍使用这个确定容量。
对任意确定整数 $`0\le m\le M`$，定义已知方向的固定容量风险
$`H_{\mathcal E,m}^{k}=\inf_{|T|=m}\sup_{|S|=q}\mathbb E_S^{\mathcal E}[|S\setminus T|/q]`$，
下确界遍历可随机化的数据规则；未知方向风险 $`H_{\mathcal E,m}^{o}`$
还对两个方向取上确界，规则不获得方向信息。
对 $`m=m_M`$，令 $`\xi\in\{k,o\}`$，并定义配对阈值的正确对齐平均风险

```math
\overline H_M=1-\frac{\mathbb E_S C_M}{q},\qquad
\sigma^2=p_*(1-p_*),\qquad
\pi_- =\frac{e^s}{1+e^s},\qquad
\pi_+ =\frac{e^{s+h}}{1+e^{s+h}}.
```

式 (31.2)。

令 $`a_+=1-\pi_+`$、$`a_-=1-\pi_-`$，于是
$`0\lt a_+\lt a_-\lt1`$，并置

```math
f_s(g)=
\begin{cases}
a_+g,&g\le0,\\[0pt]
a_-g,&g\ge0,
\end{cases}
\qquad
\mu_s=\frac{(a_--a_+)\sigma}{\sqrt{2\pi}}.
```

式 (31.3)。

**定理 31.2（容量修正的两种斜率）。** 上述容量满足
$`m_M/q\to1-p_*\in(0,1)`$，且对两个实际平稳实验、两种方向信息情形，

```math
\begin{aligned}
\sqrt q\left(H_{\mathcal E,m_M}^{\xi}-\overline H_M\right)
 &\longrightarrow\mu_s\gt0,\\[0pt]
\sqrt q\left(\frac{|S\setminus T_M|}{q}
                       -H_{\mathcal E,m_M}^{\xi}\right)
 &\Longrightarrow f_s(G)-\mu_s,
 \qquad G\sim N(0,\sigma^2).
\end{aligned}
```

式 (31.4)。

这里的 $`G`$ 就是第 27 章的共同 Gaussian 坐标：与该坐标联合时，极限为
$`(G,f_s(G)-\mu_s)`$。新极限与对数对比坐标相互独立；在第 29 章时钟
收敛的进一步子序列上，也可同时加入第 29、30 章的两条预算曲线，新坐标与
它们及对数对比坐标联合独立。所有结论对支持一致。

式 (31.4) 的第二个极限不是正态分布。其方差为

```math
\sigma^2\left[
 \frac{a_+^2+a_-^2}{2}
 -\frac{(a_--a_+)^2}{2\pi}\right].
```

式 (31.5)。

这是极限随机变量的方差。

证明。先设方向已知。取充分大的固定截断指数。所有行同时满足
$`|W_i-Z_i|\le\eta_M=O(q\log M/M)=o(1)`$ 的事件，其补集概率可为
任意固定次幂的小量。在此事件上，$`A_M`$ 等于
$`\{Z_i\ge b_M+h\}`$。位于它边界两侧的完整格点层分别为
$`Z_i=b_M+h`$ 和 $`Z_i=b_M`$；层内仍按 $`W_i`$ 排序。

由第 26 章的格点局部界、精确换测度及单行实际比较，两个相邻层的总占据数
$`K_+,K_-`$ 各满足

```math
\mathbb E_S K_\pm\asymp\frac q{\sqrt\lambda},\qquad
\mathrm{Var}_S K_\pm
 \le C\left(\frac q{\sqrt\lambda}
       +\frac{\delta_Mq^2}{\lambda}+M^{2-D}\right),
\qquad \delta_M=\frac{(\log M)^3}{n}.
```

式 (31.6)。

格点尾的几何和还给出背景计数 $`F_M=N_M-C_M`$ 的界

```math
\mathbb E_S F_M
 =\frac{q}{\sqrt\lambda}
       d_*L_he^{-s}[1+o(1)],\qquad
\mathrm{Var}_S F_M=o(q),\qquad
L_h=\frac{h}{e^h-1}.
```

式 (31.7)。

这里上尾从 $`b_M+h`$ 开始，故几何系数为 $`L_h`$。
信号接受比例趋于 $`1-p_*`$。单行、两行比较给出
$`\mathrm{Var}_S C_M=O(q)`$ 及 $`\mathrm{Var}_S N_M=O(q)`$。
全信号向量比较和独立 Bernoulli 中心极限定理，再以单行比较转移精确均值，得到

```math
G_M=-\frac{C_M-\mathbb E_S C_M}{\sqrt q}
 \Longrightarrow G,\qquad
\frac{N_M-\mathbb E_S N_M}{\sqrt q}+G_M
 \longrightarrow0\quad\text{于 }L^2.
```

式 (31.8)。

$`G_M`$ 的二阶矩一致有界，因此它一致可积。
这些结论也证明 $`m_M/q\to1-p_*`$，从而容量最终合法。

记 $`D_M=|N_M-m_M|`$。由精确校准和上述方差界，
$`\mathbb E_S D_M^2=O(q)`$。
两个相邻层的平均大小为 $`q/\sqrt\lambda`$ 阶，大于 $`\sqrt q`$。
在这个较大的尺度对 $`N_M`$ 作 Chebyshev 控制，并对两层占据数作下尾控制，
得到一个补集概率为 $`O(\lambda/q)`$ 的事件，在其上
$`D_M`$ 小于两个层的大小。
再交上 (27.11) 的后验好事件，记共同好事件为 $`\mathcal H_M`$，则

```math
\mathbb P_S(\mathcal H_M^c)=O(\lambda/q),\qquad
\mathbb E_S[D_M\mathbf1_{\mathcal H_M^c}]
 \le\sqrt{\mathbb E_S D_M^2\,
                  \mathbb P_S(\mathcal H_M^c)}
 =O(\sqrt\lambda)=o(\sqrt q).
```

式 (31.9)。

如果 $`N_M\gt m_M`$，排序规则从上方层删去 $`N_M-m_M`$ 个位置；
如果 $`N_M\lt m_M`$，它从下方层补入 $`m_M-N_M`$ 个位置。
好事件中这些改动均停在相邻层内，不跨越第二个格点。

后验概率的近似必须在这些实际排名区间中成立。
使用 (27.11) 的乘法倾斜参数 $`t`$ 及 $`t_B=\log((M-q)/q)`$，有

```math
\log\frac{\pi_i}{1-\pi_i}
 =W_i-t_B+\log t+O(q^{-1}),\qquad
|\log t|\le\frac{C|U-q|}{q},\qquad
\mathbb E_S(U-q)^2=O(q).
```

式 (31.10)。

因为 $`t_B-\tau_M=o(1)`$，两层内的后验概率分别趋向
$`\pi_+`$ 和 $`\pi_-`$，而且相应一致误差至多为
$`\epsilon_M+C|U-q|/q`$，其中确定的 $`\epsilon_M\to0`$ 吸收得分补偿、
相位收敛和单点条件比余项。
因此在实际删补区间内，把后验概率和换成层概率乘以改动长度，其绝对期望误差至多为

```math
\epsilon_M\mathbb E_S D_M
 +\frac Cq\sqrt{\mathbb E_S D_M^2\,
                         \mathbb E_S(U-q)^2}
 =o(\sqrt q).
```

式 (31.11)。

这不要求同一格点层中的各个位置等权或均匀被选。

条件于完整数据和优先级，删补区间及改动方向均为确定量。
式 (27.8) 的后验负协方差，将该区间内真实标签数的条件方差控制在
$`D_M/4`$ 以内。故标签数与其条件均值的绝对误差期望至多为
$`O((\mathbb E_S D_M)^{1/2})=O(q^{1/4})=o(\sqrt q)`$。
先在均匀支持先验下完成此条件计算，再由等变性转到每个固定支持。
在坏事件中，真实标签误差至多为 $`Cq`$，期望代价为
$`O(\lambda)=o(\sqrt q)`$；线性代理中的 $`D_M`$ 不以基数为界，
其坏事件贡献另外由 (31.9) 控制。
结合 (31.11)，记 $`L_M=|S\setminus T_M|`$，得到

```math
\mathbb E_S\left|
 L_M-\left[q-C_M
       +\pi_+(N_M-m_M)_+
       -\pi_-(m_M-N_M)_+\right]\right|
 =o(\sqrt q).
```

式 (31.12)。

利用 (31.8)、正部函数的 Lipschitz 性和取整误差至多为一，便可化为

```math
\mathbb E_S\left|
 \frac{L_M-q\overline H_M}{\sqrt q}-f_s(G_M)
 \right|\longrightarrow0.
```

式 (31.13)。

连续映射给出 $`f_s(G_M)\Rightarrow f_s(G)`$，一致可积性同时给出均值收敛。
这种非线性 Gaussian 映射属于经典方向可微极限方法，参见
[Fang–Santos 定理 2.1](../../../Library/Dynamics/fang2016directional.md)；
本处所需的真实数据近似和均值误差由 (31.9)–(31.13) 给出。
因为 $`\mathbb E G_+=\sigma/\sqrt{2\pi}`$，
$`\mathbb E f_s(G)=\mu_s`$。后验排序在固定输出大小下最优，支持对称性
把它的已知方向风险识别为精确极小极大风险，证明已知方向的 (31.4)。
未知方向仍共用第 27 章的方向判决；原始遗漏数的错误方向代价期望为
$`O(1)`$，揭示方向与组合规则的风险夹逼为 $`O(q^{-1})`$，故两者不改变
(31.4) 的分布或均值结论。

在零点两侧，$`f_s(G)`$ 的密度极限分别为
$`(a_+\sigma\sqrt{2\pi})^{-1}`$ 和
$`(a_-\sigma\sqrt{2\pi})^{-1}`$，二者不相等，因此平移后的分布也不可能为正态。
又有 $`\mathbb E f_s(G)^2=\sigma^2(a_+^2+a_-^2)/2`$，减去均值平方即得 (31.5)。

最后，间隙阈值与第 27 章基数阈值之间的单行信号质量为
$`O(\log\lambda/\sqrt\lambda)=o(1)`$。
其中心化总真实计数的实际方差为 $`o(q)`$；结合第 27 章的排序比较，
$`G_M`$ 与共同损失坐标之差依概率趋零。
第 27、29、30 章已有联合极限及连续映射遂给出所述同源关系和独立性。
各替换沿用自身的归一化尺度，且由支持等变性保持一致性。

校准不能仅保留 $`m_M/q\to1-p_*`$：式 (31.7) 的背景均值本身为
$`q/\sqrt\lambda\gg\sqrt q`$ 阶。
删去这个均值或只按一阶信号比例取容量，一般会移出本定理的临界窗口。∎

## 追加锚（本行以下为增补区）

## 32. 容量修正内的混合正态标签噪声

**定义 32.1（修正区间的精确后验中心）。** 沿用定义 31.1，先对齐到正确方向。
所有条件后验均取均匀固定基数支持先验，并条件于完整数据及独立同分优先级，
记所生的 σ 代数为 $`\mathscr D_M`$。置

```math
I_M=A_M\triangle T_M,\qquad D_M=|N_M-m_M|=|I_M|,\qquad
\varepsilon_M=\mathrm{sgn}(N_M-m_M),\qquad
\widehat G_M=-\frac{N_M-\mathbb E_S N_M}{\sqrt q}.
```

式 (32.1)。

若 $`D_M=0`$，取 $`\varepsilon_M=0`$。
记 $`\pi_i=\mathbb P(i\in S\mid\mathscr D_M)`$ 为精确后验包含概率。
实际遗漏数相对于间隙阈值的修正及其后验中心为

```math
\Delta_M=|S\setminus T_M|-(q-C_M)
       =\varepsilon_M|I_M\cap S|,\qquad
\overline\Delta_M=\varepsilon_M\sum_{i\in I_M}\pi_i,\qquad
\mathcal R_M=\frac{\Delta_M-\overline\Delta_M}{q^{1/4}}.
```

式 (32.2)。

这里 $`\Delta_M`$ 与遗漏损失一样依赖真实支持。
未知方向时先使用第 27 章的方向判决，对所选方向计算同样的得分、排名区间及
正向模型后验；容量仍为定义 31.1 的确定值。
令

```math
v_+=\pi_+(1-\pi_+),\qquad v_-=\pi_-(1-\pi_-),\qquad
v_s(g)=v_+(-g)_++v_-g_+.
```

式 (32.3)。

**定理 32.2（随机容量修正所承载的细尺度噪声）。** 在定理 31.2 的条件下，
对两个实际平稳实验及两种方向信息情形，联合收敛为

```math
\left(
 \widehat G_M,
 \sqrt q\left(\frac{|S\setminus T_M|}{q}-H_{\mathcal E,m_M}^{\xi}\right),
 \mathcal R_M
\right)
\ \Longrightarrow\
\left(G,\ f_s(G)-\mu_s,\ \sqrt{v_s(G)}\,Z\right),
```

式 (32.4)。

其中 $`G\sim N(0,\sigma^2)`$，$`Z\sim N(0,1)`$，二者独立。
结论对支持一致。第三个极限条件于 $`G`$ 为中心正态，其方差由 $`G`$ 决定；
它与 $`G`$ 不相关但不独立，且其边缘分布也不是正态。

证明。先设方向已知。在均匀支持先验下，给定 $`\mathscr D_M`$ 后，
取唯一正数 $`t`$，使下面的独立 Bernoulli 参数总和为 $`q`$。
这个校准对任意数据都有定义；式 (27.11) 还给出总方差的界

```math
p_i=\frac{t\exp(W_i-t_B)}{1+t\exp(W_i-t_B)},\qquad
\sum_i p_i=q,\qquad
c q\le d_M:=\sum_i p_i(1-p_i)\le q
```

式 (32.5)。

这些结论在概率趋一的后验好事件成立；$`t_B=\log((M-q)/q)`$。
精确后验是这个独立数组条件于总数为 $`q`$ 的分布。
$`p_i`$ 是条件化之前的校准参数，不能与 $`\pi_i`$ 混同。

固定 $`L\gt0`$，暂限于 $`D_M\le L\sqrt q`$。
给定数据，区间 $`I_M`$ 是确定集合。在独立 Bernoulli 数组中，记区间和与
补集和为 $`Y_I,Y_O`$，其均值与方差分别记作
$`\mu_I,\mu_O`$ 和 $`d_I,d_O`$。于是

```math
\mu_I+\mu_O=q,\qquad d_I\le D_M/4,\qquad
 d_O=d_M-d_I\ge cq/2
```

式 (32.6)。

最后一个不等式对充分大的 $`M`$ 成立。
异质 Bernoulli 和的经典局部极限定理给出：若总方差为 $`d\to\infty`$，
则点概率与相应正态密度的绝对误差一致为 $`O(d^{-1})`$，
不要求各个参数统一远离零与一；参见
[Siripraparat–Neammanee 定理 2](../../../Library/Dynamics/siripraparat2021local.md)。
将此界分别用于全数组与补集，且利用全数组均值恰为整数 $`q`$，得

```math
\frac{\mathbb P(Y_O=q-k)}{\mathbb P(Y_I+Y_O=q)}
 =\sqrt{\frac{d_M}{d_O}}
      \exp\left[-\frac{(k-\mu_I)^2}{2d_O}\right]
   +O_L(q^{-1/2}),\qquad 0\le k\le D_M.
```

式 (32.7)。

因为 $`D_M\le L\sqrt q`$ 且 $`q=o(M)`$，这些 $`q-k`$ 最终均属于补集和的
支持范围。余项对数据所选的区间及上述 $`k`$ 一致。

式 (32.7) 左边是区间内整个标签向量的精确后验相对于独立乘积律的密度，
在向量上仅通过其总数 $`k`$ 取值。
利用 $`1-e^{-x}\le x`$、$`\mathbb E(Y_I-\mu_I)^2=d_I`$，并在独立区间律下积分，得到

```math
d_{\mathrm{TV}}\left(
 \mathcal L((\mathbf1_{\{i\in S\}})_{i\in I_M}\mid\mathscr D_M),
 \bigotimes_{i\in I_M}\mathrm{Bernoulli}(p_i)
\right)
 \le C\left(\frac{d_I}{q}+q^{-1/2}\right)
 \le C_Lq^{-1/2}.
```

式 (32.8)。

全局支持基数的条件化因此可在这个增长区间内消去，而不是假定后验标签独立。
又因 $`0\le Y_I\le D_M`$，同一总变差界还给出精确中心的误差

```math
\left|\sum_{i\in I_M}\pi_i-\mu_I\right|
 \le C_LD_Mq^{-1/2}=O_L(1)=o(q^{1/4}).
```

式 (32.9)。

固定实数 $`u`$。对独立 Bernoulli 特征函数在
$`u q^{-1/4}`$ 处作三阶余项展开，三阶绝对矩和不超过 $`d_I`$，故

```math
\mathbb E\exp\left[
 iu\varepsilon_M\frac{Y_I-\mu_I}{q^{1/4}}\right]
 =\exp\left[-\frac{u^2d_I}{2\sqrt q}\right]
   +O_{u,L}(q^{-1/4}).
```

式 (32.10)。

这个展开也覆盖很短或空的修正区间，不以 $`D_M`$ 作分母。
结合 (32.8)–(32.9)，得到精确后验下相同的条件特征函数近似。
由于 $`\mathbb E_S D_M^2=O(q)`$，
$`\mathbb P_S(D_M\gt L\sqrt q)\le C/L^2`$。
先令 $`M\to\infty`$，再令 $`L\to\infty`$，而坏事件上的特征函数误差至多为二，便得

```math
\mathbb E\left|
 \mathbb E(e^{iu\mathcal R_M}\mid\mathscr D_M)
       -\exp(-u^2V_M/2)
\right|\longrightarrow0,\qquad
V_M=\frac1{\sqrt q}\sum_{i\in I_M}p_i(1-p_i).
```

式 (32.11)。

这里及条件期望中使用的是均匀支持先验。
$`V_M`$ 使用所有数据上均有定义的校准参数。

定理 31.2 的定位说明，删去的区间停在上方相邻格点层，补入的区间停在下方层。
校准参数在这两层分别一致趋向 $`\pi_+`$ 与 $`\pi_-`$。
再用 $`D_M/\sqrt q`$ 的紧性及取整误差，得到

```math
V_M-v_s(\widehat G_M)\longrightarrow0\quad\text{依概率},\qquad
\widehat G_M\Longrightarrow G.
```

式 (32.12)。

在 (32.11) 中乘以任意有界的 $`\widehat G_M`$ 特征函数，再取期望，
便得到 $`(\widehat G_M,\mathcal R_M)`$ 的联合极限
$`(G,\sqrt{v_s(G)}Z)`$。式 (31.8)、(31.13) 与精确均值转移同时给出
粗尺度损失为 $`f_s(\widehat G_M)-\mu_s+o_P(1)`$，遂得已知方向的 (32.4)。
整个随机向量在同时置换支持、数据和优先级后不变，其分布对每个固定支持相同。
所以先验下的联合分布恰等于每个固定支持下的分布，结论据此转移。
此处没有声称在固定真实支持下、条件于数据后标签仍有上述后验随机性。

未知方向的全部统计量，在方向判决正确时与正确对齐版本逐项相等。
该事件的补集概率为 $`O(q^{-1})`$，故相等耦合转移联合分布极限。
粗尺度损失的未知方向精确风险中心仍由第 31 章的 $`O(q^{-1})`$ 夹逼处理。
这里不把旧的 $`o(\sqrt q)`$ 误差直接用作 $`o(q^{1/4})`$ 误差；
细尺度坐标由精确后验中心、(32.8)–(32.11) 及相等耦合单独控制。

最后令 $`V=v_s(G)`$、$`R=\sqrt V Z`$。
$`V`$ 几乎处处为正且不是常数，并有

```math
\mathbb EV=\frac{\sigma(v_++v_-)}{\sqrt{2\pi}},\qquad
\mathbb EV^2=\frac{\sigma^2(v_+^2+v_-^2)}2,\qquad
\mathbb ER^4=3\mathbb EV^2\gt3(\mathbb EV)^2.
```

式 (32.13)。

因此 $`R`$ 不是中心正态变量。
$`\mathbb E(R\mid G)=0`$ 给出不相关，而
$`\mathbb E(R^2\mid G)=v_s(G)`$ 不是常数，排除独立性。
这些矩等式属于极限随机变量，不断言实际归一化统计量的矩收敛。∎

## 追加锚（本行以下为增补区）

## 33. 非格点容量的线性波动与持续混合噪声

**定义 33.1（非格点阈值的精确平均容量）。** 沿用定义 27.1 的实验和固定参数，
另设 $`\log(1+r)/\log(1-r)\notin\mathbb Q`$。取确定序列
$`s_M\to s\in\mathbb R`$，令 $`u_M=\tau_M+s_M`$。
在正确对齐的数据上定义

```math
A_M=\{i:W_i\gt u_M\},\quad N_M=|A_M|,\quad C_M=|A_M\cap S|,
\quad m_M=\lfloor\mathbb E_S N_M\rfloor,\quad
\overline H_M=1-\frac{\mathbb E_S C_M}{q}.
```

式 (33.1)。

支持对称性使 $`m_M`$ 为不依赖支持位置的确定容量。
令 $`T_M`$ 选取 $`m_M`$ 个最高补偿得分，同分处仍用独立优先级。
任意容量的固定输出风险采用定义 31.1 的公式，记为
$`H_{\mathcal E,m_M}^{\xi}`$。置

```math
\widehat G_M=-\frac{N_M-\mathbb E_S N_M}{\sqrt q},\qquad
p_s=\frac{e^s}{1+e^s},\qquad \sigma^2=p_*(1-p_*).
```

式 (33.2)。

沿用定义 32.1 的 $`I_M,D_M,\varepsilon_M,\Delta_M,\overline\Delta_M,\mathcal R_M`$，
但以本章的 $`A_M,T_M`$ 代入。
已知方向时，$`\pi_i`$ 是均匀固定基数先验在完整对齐数据与优先级下的精确后验概率。
未知方向时，先作第 27 章的方向判决，再以所选方向计算各个量和正向模型后验权重；
仍使用 (33.1) 的确定容量与正确对齐的确定均值。

**定理 33.2（光滑粗尺度不消除随机方差）。** 容量满足
$`m_M/q\to1-p_*\in(0,1)`$。对两个实际平稳实验、两种方向信息情形，
对支持一致地有

```math
\sqrt q\left(H_{\mathcal E,m_M}^{\xi}-\overline H_M\right)\longrightarrow0,
```

式 (33.3)。

且联合收敛为

```math
\left(\widehat G_M,
\sqrt q\left(\frac{|S\setminus T_M|}{q}-H_{\mathcal E,m_M}^{\xi}\right),
\mathcal R_M\right)
\Longrightarrow
\left(G,(1-p_s)G,\sqrt{p_s(1-p_s)|G|}\,Z\right),
```

式 (33.4)。

其中 $`G\sim N(0,\sigma^2)`$ 与 $`Z\sim N(0,1)`$ 独立。
这里 $`G`$ 是第 27 章的共同 Gaussian 坐标。
粗尺度损失极限为正态，第三个极限仍与 $`G`$ 不相关而不独立，其边缘分布不是正态。

证明。先设方向已知。记 $`d_*=\varphi(z_*)/\sqrt v\gt0`$。
[支持恢复卷 (25.7)–(25.8)](PARITY_HIDDEN_ARROW_RECOVERY.md) 的非格点局部界、
精确换测度和实际一行比较给出

```math
\frac{\mathbb E_S C_M}{q}\longrightarrow1-p_*,\qquad
\mathbb E_S(N_M-C_M)
 =\frac q{\sqrt\lambda}d_*e^{-s}[1+o(1)],\qquad
\mathrm{Var}_S(N_M-C_M)=o(q).
```

式 (33.5)。

最后一式由 (25.3) 的实际两行矩转移得到。
信号计数方差为 $`O(q)`$，故 $`\mathrm{Var}_S N_M=O(q)`$，
并有 $`\mathbb E_S D_M^2=O(q)`$。
全信号向量比较 (27.6)、独立 Bernoulli 中心极限定理和单行均值转移 (27.7)
分别处理分布与精确中心，得到

```math
G_M=-\frac{C_M-\mathbb E_S C_M}{\sqrt q}\Longrightarrow G,
\qquad \widehat G_M-G_M\longrightarrow0\quad\text{于 }L^2.
```

式 (33.6)。

这同时证明容量的极限。背景均值在 (33.5) 中保留；它大于平方根基数尺度，
不能在定义容量时删除。

现在证明容量修正的定位。固定任意 $`\eta\gt0`$，取阈值两侧的窗口
$`(u_M,u_M+\eta]`$ 与 $`[u_M-\eta,u_M]`$，记总占据数为 $`K_+,K_-`$。
[Stone 的经典局部极限定理](../../../Library/Dynamics/stone1967local.md)
给出固定宽度、对中心位置一致的区间概率。
单位时间信号得分的复合 Poisson 增量非格点，且具有有限正方差；
把实数时间拆成整数部分和有界时间余增量，即可使用该定理。
端点原子用固定小窗口夹逼后令其宽度趋零。
同样，在计数截断上先用 $`|W-Z|=o(1)`$ 夹住窗口，再令夹逼宽度趋零，
便把固定得分的局部界转到补偿得分。

信号窗口质量为 $`\eta d_*/\sqrt\lambda[1+o(1)]`$；
背景窗口质量由精确换测度取得。
对每个固定 $`\eta`$，实际占据数因此满足

```math
\mathbb E_S K_\pm\asymp_\eta\frac q{\sqrt\lambda},\qquad
\mathrm{Var}_S K_\pm\le C_\eta\left(
\frac q{\sqrt\lambda}+\delta_M\frac{q^2}{\lambda}+M^{2-D}\right),
\qquad \delta_M=\frac{(\log M)^3}{n}.
```

式 (33.7)。

这里 $`D`$ 是任取充分大的计数尾指数。
两个窗口的平均大小均大于 $`\sqrt q`$。
分别控制窗口计数的下尾以及 $`D_M`$ 超过其均值固定比例的事件，
再交上 (27.11) 的后验好事件，得到事件 $`\mathcal H_{M,\eta}`$，使得

```math
\mathbb P_S(\mathcal H_{M,\eta}^{c})=O_\eta(\lambda/q),\qquad
I_M\subseteq\{i:|W_i-u_M|\le\eta\}\quad\text{于 }\mathcal H_{M,\eta},
\qquad
\mathbb E_S[D_M\mathbf1_{\mathcal H_{M,\eta}^{c}}]=O_\eta(\sqrt\lambda).
```

式 (33.8)。

最后一项使用 $`\mathbb E_S D_M^2=O(q)`$ 和 Cauchy 不等式。
两集合都是同一得分与优先级顺序的初始片段，因此窗口包含足够位置即保证该定位；
同分组不被假定为连续分布。

在好事件中，(27.11) 与 logistic 函数的 Lipschitz 性给出

```math
\max_{i\in I_M}|\pi_i-p_s|
\le\eta/4+\epsilon_M+C|U-q|/q,\qquad
\epsilon_M\longrightarrow0,\qquad \mathbb E_S(U-q)^2=O(q).
```

式 (33.9)。

其中确定误差包括 $`s_M-s`$、$`t_B-\tau_M`$ 和单点条件概率比余项。
后验负协方差还使区间标签和的条件方差至多为 $`D_M/4`$，
因此它与精确后验均值的绝对误差期望为 $`O(q^{1/4})`$。
先对均匀支持先验作条件计算，再用支持置换等变性转到每个固定支持。
在好事件中，以 $`p_sD_M`$ 替换后验区间均值的期望误差至多为
$`(\eta/4+\epsilon_M)\mathbb E_S D_M+
(C/q)\sqrt{\mathbb E_S D_M^2\,\mathbb E_S(U-q)^2}`$。
坏事件上的真实标签项以 $`q`$ 为界，线性代理另由 (33.8) 控制。
固定 $`\eta`$ 后令 $`M\to\infty`$，归一化误差的上极限至多为 $`C\eta`$；
再令 $`\eta\downarrow0`$，得到

```math
\mathbb E_S\left|
|S\setminus T_M|-[q-C_M+p_s(N_M-m_M)]\right|=o(\sqrt q).
```

式 (33.10)。

这一步只使用固定窗口的迭代极限。
非格点得分在有限样本下仍可离散，本证明没有在随样本收缩的窗口上调用密度近似。

由 (33.6)、取整误差至多为一及 (33.10)，
$`(|S\setminus T_M|-q\overline H_M)/\sqrt q`$
与 $`(1-p_s)G_M`$ 的 $`L^1`$ 距离趋零。
$`G_M`$ 的二阶矩一致有界且均值为零，故同时得到分布和均值结论。
后验最高分排序的精确固定容量最优性与支持对称性，
把已知方向的期望识别为 $`H_{\mathcal E,m_M}^{k}`$，证明 (33.3) 及粗尺度部分。
阈值与第 27 章基数阈值间的信号概率为
$`O(\log\lambda/\sqrt\lambda)=o(1)`$；
两行矩转移将该带的中心化计数方差控制为 $`o(q)`$，
所以 $`G_M`$ 与第 27 章的共同坐标联合时给出同一个 $`G`$。

最后处理细尺度。第 32 章 (32.5)–(32.11) 的条件数组论证只使用
总校准均值为 $`q`$、总方差为 $`q`$ 的固定正比例以及
$`\mathbb E_S D_M^2=O(q)`$；这里三项仍由 (27.10)–(27.11)、(33.5)–(33.6) 成立。
对 $`D_M\le L\sqrt q`$ 的区间，同样的补集局部界给出全向量总变差
$`O_L(q^{-1/2})`$，其精确中心与独立中心之差为 $`O_L(1)`$。
故在均匀支持先验下，对每个固定实数 $`t`$，

```math
\mathbb E\left|\mathbb E(e^{it\mathcal R_M}\mid\mathscr D_M)
                  -\exp(-t^2V_M/2)\right|\longrightarrow0,\qquad
V_M=\frac1{\sqrt q}\sum_{i\in I_M}p_i(1-p_i).
```

式 (33.11)。

$`p_i`$ 仍是精确后验条件化之前的校准独立参数，区别于 $`\pi_i`$。
(33.8) 的定位和校准公式使 $`p_i`$ 在修正区间内与 $`p_s`$ 相差
$`O(\eta)+o_P(1)`$。利用 $`D_M/\sqrt q`$ 的紧性，先令 $`M\to\infty`$、
再令 $`\eta\downarrow0`$，得

```math
V_M-p_s(1-p_s)|\widehat G_M|\longrightarrow0\quad\text{依概率}.
```

式 (33.12)。

在 (33.11) 中乘以数据可测的 $`\widehat G_M`$ 的特征函数，再取期望，
得到与细尺度坐标的联合极限；用 (33.10) 替换粗尺度损失即可得到 (33.4)。
整个随机向量的置换等变性将先验下的联合分布恰好转移到每个固定支持。
条件后验结论 (33.11) 本身不被解释为固定真实支持下的随机标签结论。

未知方向统计量在方向判决正确时逐项相等于正确对齐版本，
其补集概率为 $`O(q^{-1})`$；粗尺度风险的夹逼也为 $`O(q^{-1})`$。
相等耦合与风险夹逼分别转移分布与精确中心。
错误方向上的正向权重不被声称为未知方向的精确 Bayesian 后验。

令 $`V=p_s(1-p_s)|G|`$。它不是常数，
所以 $`\mathbb E(\sqrt V Z\mid G)=0`$ 与
$`\mathbb E((\sqrt V Z)^2\mid G)=V`$ 分别给出不相关与不独立。
又因 $`\mathbb E[(\sqrt{V}\,Z)^4]=3\mathbb E[V^2]\gt3(\mathbb E[V])^2`$，
第三个极限不是正态。这里使用的只是极限变量的矩，
不包含实际统计量矩收敛或 (33.3) 以外的更细平均风险展开。∎

**命题 33.3（实际非格点行的收缩窗口反例）。** 存在满足定义 33.1 的序列，
其内在偏移极限和 $`s`$ 均为零，使得对两个实际平稳实验、任意真实支持及其中任一信号行，
令 $`w_M=\sqrt{\lambda_M/q_M}`$，都有

```math
\liminf_M\lambda_M\,
 \mathbb P_S\{|W_i-\tau_M|\le w_M/2\}
 \ge\frac{2}{\pi\sqrt3},\qquad
\frac{\mathbb P_S\{|W_i-\tau_M|\le w_M/2\}}
     {w_M/\sqrt{\lambda_M}}\longrightarrow\infty.
```

式 (33.13)。

因此，本模型的非格点条件不足以保证在此收缩尺度上的相对“密度乘宽度”公式。

证明。固定 $`r=1/2`$ 和任意 $`\beta\in(1/2,1)`$。
两个跳幅为 $`h_+=\log(3/2)`$ 与 $`h_-=-\log2`$。
若其比为有理数，便会得到某个正整数次幂的三等于某个整数次幂的二，矛盾。
沿允许的 $`M=2^{d-1}`$，取

```math
\lambda_M=4\left\lfloor\frac{\beta\log M}{4\phi}\right\rfloor,
\qquad q_M=\left\lfloor M e^{-\lambda_M\phi}+\tfrac12\right\rfloor,
\qquad \mathsf T_M=2M\lambda_M,\qquad u_M=\tau_M=\log(M/q_M).
```

式 (33.14)。

对充分大的 $`M`$，样本数与基数均为合法整数，且
$`q_M=M^{1-\beta+o(1)}`$、
$`\tau_M=\lambda_M\phi+O(q_M^{-1})`$。
所以内在偏移趋零，阈值也满足 $`s_M=0`$。

在信号比较律下，两个独立 Poisson 计数的均值
$`3\lambda_M/4`$、$`\lambda_M/4`$ 都是整数。
两者同时等于各自均值的事件，由经典 Stirling 公式有概率

```math
Q_r\{N_+=3\lambda_M/4,\ N_-=\lambda_M/4\}
 \sim\frac{2}{\pi\sqrt3\,\lambda_M}.
```

式 (33.15)。

在该事件上，$`Z_i=\lambda_M\phi`$，而补偿得分满足
$`W_i-Z_i=O(a_M\lambda_M)`$，其中 $`a_M=rq_M/(M-q_M)`$。
这些误差在所选窗口内可忽略，因为

```math
\frac{a_M\lambda_M}{w_M}
 =O\left(\frac{q_M^{3/2}\sqrt{\lambda_M}}{M}\right)\longrightarrow0,
\qquad
\frac{q_M^{-1}}{w_M}\longrightarrow0.
```

式 (33.16)。

因此整个计数事件最终都落在 $`|W_i-\tau_M|\le w_M/2`$ 中。
其计数为 $`O(\log M)`$，所以
[支持恢复卷 (21.5)](PARITY_HIDDEN_ARROW_RECOVERY.md) 的实际一行相对概率比较
适用于两个实验；其相对误差趋零，单独的多项式小余项也是 $`o(\lambda_M^{-1})`$。
这把 (33.15) 的下界转到实际信号行，证明 (33.13) 的第一式。
又因 $`w_M/\sqrt{\lambda_M}=q_M^{-1/2}`$ 且
$`\sqrt{q_M}/\lambda_M\to\infty`$，第二式随之成立。
此反例与固定宽度局部极限定理相容，也不推断平均容量代价的更细展开。∎

## 追加锚（本行以下为增补区）

## 34. 临界容量窗中的随机起点过程

**定义 34.1（共同排序下的容量曲线）。** 固定 $`A\gt0`$，取定义 31.1 的格点情形，
或定义 33.1 的非格点情形。所有容量共用同一实际观测、同一补偿得分和同一组独立连续优先级。
记相应阈值集合为 $`A_M`$，$`N_M=|A_M|`$、$`C_M=|A_M\cap S|`$，置

```math
\nu_M=\mathbb E_S N_M,\qquad
m_M(a)=\lfloor\nu_M+a\sqrt q\rfloor\quad(-A\le a\le A),\qquad
\overline H_M=1-\mathbb E_S C_M/q.
```

式 (34.1)。

这里的期望按所选实验和正确方向对齐计算，支持位置不影响这些确定量。
令 $`T_M(a)`$ 为前 $`m_M(a)`$ 个位置，$`I_M(a)=A_M\triangle T_M(a)`$，
$`e_M(a)=\operatorname{sgn}(N_M-m_M(a))`$。在均匀基数先验下，
给定全部对齐数据与优先级 $`\mathscr D_M`$，记精确后验边缘概率为 $`\pi_i`$，并定义

```math
\begin{aligned}
\Delta_M(a)&=e_M(a)|I_M(a)\cap S|,&
\overline\Delta_M(a)&=e_M(a)\sum_{i\in I_M(a)}\pi_i,\\[0pt]
X_M&=-\frac{N_M-\nu_M}{\sqrt q},&
R_M(a)&=q^{-1/4}\bigl(\Delta_M(a)-\overline\Delta_M(a)\bigr),\\[0pt]
Y_M(a)&=\frac{|S\setminus T_M(a)|-qH_{\mathcal E,m_M(a)}^\xi}{\sqrt q},
&\xi&\in\{k,o\}.
\end{aligned}
```

式 (34.2)。

风险沿用定义 31.1 的确定输出基数 minimax 风险。未知方向时，整条曲线只用一次
定义 27.1 的共同方向判决；全部随机量用该判决对齐后的正向工作得分与权重。
确定容量、$`\nu_M`$ 和 $`\overline H_M`$ 保持正确对齐定义。
错误方向上的工作权重不定义为未知方向的精确后验。

格点情形取 $`\pi_+=\operatorname{logistic}(s+h)`$、
$`\pi_-=\operatorname{logistic}(s)`$；非格点情形取
$`\pi_+=\pi_-=p_s=\operatorname{logistic}(s)`$。置

```math
v_\pm=\pi_\pm(1-\pi_\pm),\qquad
f(t)=\begin{cases}(1-\pi_+)t,&t\le0,\\[0pt](1-\pi_-)t,&t\ge0.\end{cases}
```

式 (34.3)。

令 $`G\sim N(0,\sigma^2)`$，$`\sigma^2=p_*(1-p_*)`$。
令 $`B_+,B_-`$ 为相互独立且独立于 $`G`$ 的标准 Brownian 运动，定义连续过程

```math
K(t)=\begin{cases}\sqrt{v_+}\,B_+(-t),&t\le0,\\[0pt]
-\sqrt{v_-}\,B_-(t),&t\ge0.\end{cases}
```

式 (34.4)。

**定理 34.2（整条容量曲线的共同随机起点）。** 对每个固定 $`A\gt0`$，上述容量最终都合法。
在两个实际平稳实验、两种方向信息情形下，对支持一致地有

```math
\bigl(X_M,Y_M(\cdot),R_M(\cdot)\bigr)
\Longrightarrow
\bigl(G,\ a\mapsto f(G+a)-\mathbb E f(G+a),\ a\mapsto K(G+a)\bigr)
```

式 (34.5)。

收敛空间为 $`\mathbb R\times D[-A,A]\times D[-A,A]`$，两条曲线均取
Skorohod $`J_1`$ 拓扑，极限路径连续。精确风险函数还满足

```math
\sup_{|a|\le A}\left|
\sqrt q\bigl(H_{\mathcal E,m_M(a)}^\xi-\overline H_M\bigr)-\mu(a)
\right|\longrightarrow0,\qquad
\mu(a)=-\pi_+a+(\pi_+-\pi_-)\left[\sigma\varphi(a/\sigma)+a\Phi(a/\sigma)\right].
```

式 (34.6)。

这里 $`\Phi,\varphi`$ 为标准正态分布函数与密度。
给定 $`G=g`$，不同容量的细尺度极限具有共同协方差

```math
\mathrm{Cov}\bigl(K(g+a),K(g+b)\mid G=g\bigr)=
\begin{cases}
v_+\min(|g+a|,|g+b|),&g+a,g+b\le0,\\[0pt]
v_-\min(|g+a|,|g+b|),&g+a,g+b\ge0,\\[0pt]
0,&(g+a)(g+b)\lt0.
\end{cases}
```

式 (34.7)。

证明。先取已知方向。第 31、33 章的实际一、二行估计与信号数组比较给出

```math
X_M\Longrightarrow G,\qquad
\sup_M\mathbb E_S X_M^2\lt\infty,\qquad
\left\|X_M+\frac{C_M-\mathbb E_SC_M}{\sqrt q}\right\|_{L^2}\longrightarrow0,
\qquad \nu_M/q\longrightarrow1-p_*\in(0,1).
```

式 (34.8)。

最后一式证明容量合法；阈值接受的背景均值仍包含在 $`\nu_M`$ 中。
令 $`D_M^*=\max_{|a|\le A}|N_M-m_M(a)|`$，则
$`D_M^*\le |N_M-\nu_M|+A\sqrt q+1`$，故
$`\mathbb E_S(D_M^*)^2=O_A(q)`$。

先在先验与数据的联合概率空间处理标签。令 $`B_0=(M-q)/q`$，选择唯一 $`t\gt0`$
使 $`p_i=t e^{W_i}/(B_0+t e^{W_i})`$ 满足 $`\sum_i p_i=q`$。
独立 Bernoulli 标签 $`\zeta_i`$ 条件于 $`\sum_i\zeta_i=q`$，恰为精确后验。
记 $`U=\sum_i e^{W_i}/(B_0+e^{W_i})`$。第 32 章校准估计给出一个补集概率
$`O(q^{-1})`$ 的数据事件，在其上

```math
|\log t|\le C|U-q|/q,\qquad
cq\le d:=\sum_i p_i(1-p_i)\le q,\qquad
\mathbb E_S(U-q)^2=O(q).
```

式 (34.9)。

固定 $`H\gt0`$，取阈值排名两侧各前 $`r_M=\lceil H\sqrt q\rceil`$ 个位置，
依次记为 $`i_j^+`$（删除侧）与 $`i_j^-`$（添加侧）；它们的并集记为 $`J_H`$。
两侧位置不足的概率由 (34.8) 趋零。并集大小为 $`O_H(\sqrt q)`$，
方差 $`d_J\le |J_H|/4`$，补集方差 $`d_O=d-d_J\ge cq/2`$。
令 $`S_J=\sum_{i\in J_H}\zeta_i`$、$`\mu_J=\mathbb E S_J`$，
$`S_O`$ 为补集和。在独立乘积律下应用
[Siripraparat–Neammanee 的局部定理](../../../Library/Dynamics/siripraparat2021local.md)，
如 (32.5)–(32.8)，得到对所有可能的整数 $`k`$ 一致的比值

```math
\frac{\mathbb P(S_O=q-k)}{\mathbb P(S_J+S_O=q)}
=\sqrt{\frac d{d_O}}\exp\left[-\frac{(k-\mu_J)^2}{2d_O}\right]
 +O_H(q^{-1/2}).
```

式 (34.10)。

分母在整数均值处为 $`(2\pi d)^{-1/2}(1+O(q^{-1/2}))`$，
分子的一致绝对误差为 $`O(q^{-1})`$。整个标签向量的条件密度比就是
(34.10) 在 $`k=S_J`$ 处的值。利用
$`\mathbb E(S_J-\mu_J)^2=d_J`$ 积分，给出

```math
d_{\mathrm{TV}}\left(
\mathcal L((1_{i\in S})_{i\in J_H}\mid\mathscr D_M),
\bigotimes_{i\in J_H}\mathrm{Bernoulli}(p_i)\right)\le C_Hq^{-1/2},\qquad
\sup_{I\subseteq J_H}\left|\sum_{i\in I}(\pi_i-p_i)\right|\le C_H.
```

式 (34.11)。

第二个界由有界标签和与第一个界推出。这是对一个完整并集向量的一次比较，
所有容量都取这个向量的前缀。对单点重复同一估计还得
$`\sup_i|\pi_i-p_i|\le Cq^{-1/2}`$，无需逐坐标概率的并集界。

固定 $`H`$ 的两侧排名均落在相邻格点层的概率趋一，因为每层有
$`\asymp q/\sqrt\lambda\gg\sqrt q`$ 个位置。非格点情形先固定宽度
$`\eta\gt0`$，用第 33 章的固定宽度局部界；两侧窗口也各包含远多于
$`\sqrt q`$ 个位置。先令 $`M\to\infty`$、再令 $`\eta\downarrow0`$，从而

```math
\max_{j\le r_M}|p_{i_j^\pm}-\pi_\pm|\longrightarrow0
\quad\text{依概率},\qquad
\sup_{0\le u\le H}\left|
q^{-1/2}\sum_{j\le\lfloor u\sqrt q\rfloor}
 p_{i_j^\pm}(1-p_{i_j^\pm})-v_\pm u\right|\longrightarrow0
\quad\text{依概率}.
```

式 (34.12)。

这一步没有使用随样本收缩窗口的相对密度公式。

在网格点 $`k/\sqrt q`$ 处定义两条后验中心化前缀和
$`P_{\pm,M}(k/\sqrt q)=q^{-1/4}\sum_{j\le k}(1_{i_j^\pm\in S}-\pi_{i_j^\pm})`$，
并作连续线性插值。令 $`\mathcal K_M(t)=P_{+,M}(-t)`$（$`t\le0`$），
$`\mathcal K_M(t)=-P_{-,M}(t)`$（$`t\ge0`$）。
反射前使用连续插值，避免将右连续阶梯函数的反射误认成右连续函数。

在 (34.11) 的乘积律下，换为 $`\zeta_i-p_i`$ 的两条前缀和相互独立。
它们是二维平方可积鞅；(34.12) 是其对角可预测方差时钟，交叉时钟为零。
跳幅至多 $`q^{-1/4}`$，方差时钟跳幅至多 $`1/(4\sqrt q)`$，满足
[Whitt 定理 2.1(ii)](../../../Library/Dynamics/whitt2007martingale.md) 的条件。
也可直接验证紧性：$`k`$ 项独立中心化和的四阶矩至多 $`C(k+k^2)`$；
归一化并对插值区间分成两个端点片段与整网格中段，便得
$`\mathbb E|P_{\pm,M}(u)-P_{\pm,M}(v)|^4\le C|u-v|^2`$。
有界数组的 Lindeberg 条件和 (34.12) 确定有限维 Gaussian 极限。

由 (34.11)，换回精确后验只改变 $`O_H(q^{-1/2})`$ 的全向量总变差，
并带来至多 $`O_H(q^{-1/4})`$ 的一致中心位移。因此在
$`C[-H,H]`$ 的有界 Lipschitz 距离下，

```math
d_{\mathrm{BL}}\left(
\mathcal L(\mathcal K_M\mid\mathscr D_M),
\mathcal L(K|_{[-H,H]})\right)\longrightarrow0
\quad\text{依概率且在 }L^1\text{ 中}.
```

式 (34.13)。

随机环境的结论可用子序列准则得到：在任一子序列抽取使 (34.9)、(34.12)
几乎处处成立的进一步子序列，再对每个确定环境应用上述数组定理。
距离有界，所以也有 $`L^1`$ 收敛。对任意有界的数据函数与有界路径函数乘积，
先条件于 $`\mathscr D_M`$，用 (34.13) 将路径函数的条件均值换成常数，
再用 (34.8)，证明 $`(X_M,\mathcal K_M)\Rightarrow(G,K)`$，且两极限独立。
这是条件过程极限产生联合独立性的经典机制，亦见
[Pasquazzi 定理 5](../../../Library/Dynamics/whitt2007martingale.md)。

精确排名参数满足

```math
t_M(a)=\frac{m_M(a)-N_M}{\sqrt q}
=X_M+a-\frac{\{\nu_M+a\sqrt q\}}{\sqrt q},\qquad
R_M(a)=\mathcal K_M(t_M(a)).
```

式 (34.14)。

在 $`|X_M|\le L`$ 上选 $`H\gt L+A+2`$。插值斜率至多 $`q^{1/4}`$，
故 $`\sup_a|R_M(a)-\mathcal K_M(X_M+a)|\le q^{-1/4}`$。
连续路径上的平移映射连续，先截断起点到 $`[-L,L]`$ 应用连续映射定理，
再以 (34.8) 的 $`\mathbb P(|X_M|\gt L)\le C/L^2`$ 去截断，得到
$`(X_M,R_M(\cdot))\Rightarrow(G,K(G+\cdot))`$。

还须对整条曲线控制平均误差。精确固定基数乘积权重后验的 Newton 不等式给出
不同标签的非正条件协方差；因而任意 $`m`$ 个不同位置的中心化标签和条件方差
至多 $`m/4`$。将其任意排序的前缀分解为二进制区间，每个前缀在每层至多取一个块。
Cauchy 不等式及每层各块总长度至多 $`2m`$ 给出经典的二进制最大界

```math
\mathbb E\left[\max_{k\le m}
\left|\sum_{j\le k}(1_{i_j\in S}-\pi_{i_j})\right|^2
\middle|\mathscr D_M\right]\le Cm\log^2(2m).
```

式 (34.15)。

它不把精确后验前缀当作鞅。两侧至多各取 $`D_M^*`$ 个位置，故
$`\mathbb E\sup_a|\Delta_M(a)-\overline\Delta_M(a)|
\le C_Aq^{1/4}\log M=o(\sqrt q)`$。

对整个容量窗重复相邻层的占据估计，定位失败概率为 $`O_A(\lambda/q)`$；
非格点情形固定 $`\eta`$ 后为 $`O_{A,\eta}(\lambda/q)`$。
在好事件上，由 (34.9)、单点后验界及局部得分定位，
$`\overline\Delta_M(a)`$ 一致接近
$`P_M(a)=\pi_+(N_M-m_M(a))_+-\pi_-(m_M(a)-N_M)_+`$。
其期望误差至多
$`\epsilon_M\mathbb ED_M^*+Cq^{-1}\mathbb E[D_M^*|U-q|]
+Cq^{-1/2}\mathbb ED_M^*=o(\sqrt q)`$；非格点情形另有
$`C\eta\mathbb ED_M^*`$，在取样本极限后令 $`\eta\downarrow0`$。
坏事件上真实修正与其后验均值均至多 $`q`$，成本为 $`O_{A,\eta}(\lambda)`$；
线性代理仅由 $`D_M^*`$ 控制，要另外用 Cauchy 不等式得到
$`O_{A,\eta}(\sqrt\lambda)`$。两者均为 $`o(\sqrt q)`$。
因此

```math
\mathbb E_S\sup_{|a|\le A}\left|
\frac{|S\setminus T_M(a)|-q\overline H_M}{\sqrt q}
-\{f(X_M+a)-a\}\right|\longrightarrow0.
```

式 (34.16)。

这里用到 $`P_M(a)/\sqrt q=f(t_M(a))-t_M(a)`$、(34.8) 与一致舍入界。
已知方向的后验排名规则在每个确定基数处均为精确 minimax；
(34.8) 的二阶矩界保证一致可积，$`f`$ 的 Lipschitz 常数不依赖平移 $`a`$。
所以 $`\mathbb Ef(X_M+a)\to\mathbb Ef(G+a)`$ 在紧容量窗上一致成立。
取 (34.16) 的期望并减去精确中心，证明 (34.5)、(34.6)。
公式 (34.6) 用 $`\mathbb E(G+a)_+=\sigma\varphi(a/\sigma)+a\Phi(a/\sigma)`$
化简而得；非格点时 $`\mu(a)=-p_sa`$，粗尺度极限整条曲线为 $`(1-p_s)G`$。

以上先验结论的整个联合随机元及所有上确界量均在支持、行数据与优先级的共同置换下不变。
支持置换可迁，故先验混合分布恰等于每个固定支持的无条件联合分布。
条件后验陈述本身仍只在先验概率空间解释。
有限样本容量取 floor，实际曲线是右连续阶梯函数，上确界是有限个排名值的最大值；
上述插值比较与连续极限给出所述可测 $`D`$ 空间收敛。

未知方向使用一次共同判决。在其正确事件上所有容量的随机量同时与已知方向相等，
其补集概率 $`O(q^{-1})`$ 转移整个路径分布。损失至多 $`q`$，所以一致原始平均损失
误差为 $`O(1)`$；揭示方向与组合规则还给出
$`0\le H_{\mathcal E,m}^{o}-H_{\mathcal E,m}^{k}\le C/q`$，对所有容量一致。
这分别转移分布和精确风险中心，不要求组合规则在有限样本达到 minimax。
最后，由两侧 Brownian 前缀的重叠长度得到 (34.7)。∎

**推论 34.3（增量独立的精确边界）。** 定理 34.2 的容量增量曲线满足

```math
\bigl(X_M,\ a\mapsto R_M(a)-R_M(0)\bigr)
\Longrightarrow\bigl(G,\ a\mapsto K(G+a)-K(G)\bigr).
```

式 (34.17)。

第二条极限曲线独立于 $`G`$ 当且仅当 $`v_+=v_-`$。
此时它的分布是 $`\sqrt{v_+}`$ 倍的标准双侧 Brownian 运动，且独立于粗尺度极限曲线。
非格点情形总满足该条件；格点情形当且仅当 $`s=-h/2`$，此时粗尺度函数仍有折点。
然而它不独立于绝对细尺度值 $`K(G)`$：在等方差情形，任意 $`0\lt a\le A`$ 都有

```math
\mathrm{Cov}\bigl(K(G+a)-K(G),K(G)\bigr)
=-v_+\mathbb E\min(a,(-G)_+)\lt0.
```

式 (34.18)。

证明。(34.17) 由连续极限上的求值与相减映射得到。
若两侧方差相等，$`K`$ 是缩放的双侧 Brownian 运动；其平稳增量使
$`a\mapsto K(g+a)-K(g)`$ 的整个分布不依赖确定起点 $`g`$。
又因原始过程 $`K`$ 独立于 $`G`$，给定 $`G`$ 后的增量过程分布恒定，得到充分性。

反之，对固定 $`a\gt0`$，给定 $`G=g`$ 的增量方差为
$`\int_g^{g+a}[v_+1_{t\lt0}+v_-1_{t\gt0}]\,dt`$。
在 $`g\lt-a`$ 和 $`g\gt0`$ 两个正概率事件上分别等于 $`av_+`$ 和 $`av_-`$；
独立性要求它为常数，故两方差相等。
logistic 方差是 $`1/(4\cosh^2(x/2))`$，关于 $`|x|`$ 严格递减，
所以格点下相等恰等于 $`|s+h|=|s|`$，即 $`s=-h/2`$。
此时仍有 $`\pi_+\gt\pi_-`$，故 $`f`$ 的两斜率不同。

等方差下，给定负起点 $`g`$，前进增量与从零至该起点的原有路径重叠且符号相反，
条件协方差为 $`-v_+\min(a,-g)`$；非负起点的条件协方差为零。
条件均值均为零，取期望即得 (34.18)。所用矩均属于极限过程，不推断实际统计量的矩收敛。∎

## 追加锚（本行以下为增补区）
