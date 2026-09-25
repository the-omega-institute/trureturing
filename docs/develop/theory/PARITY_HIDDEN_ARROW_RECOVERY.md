# 奇偶马尔可夫核的支持恢复极限

## 20. 格点边界的后验平分与相位振荡

**定义 20.1（算术振幅、边界相位与格点曲线）。** 沿用[原卷第 17—19 章及定义 19.1](PARITY_HIDDEN_ARROW.md)的实验、
风险、固定基数 $`q=\lfloor M^{1-\beta}\rfloor`$ 与临界参数
$`\alpha_E,\theta,\gamma,V`$。本章改用算术振幅：存在互素正整数
$`m,k`$ 及 $`h\gt0`$，使

```math
\log(1+r)=mh,\qquad \log(1-r)=-kh.
\tag{20.1}
```

由 $`(1+r)(1-r)\lt1`$ 得 $`k\gt m`$；互素条件确定最大格距
$`h`$。记 $`\eta=1-\theta`$，并定义

```math
\delta_M=\beta\ell-h\left\lfloor\frac{\beta\ell}{h}\right\rfloor,
\quad C_c=\frac{e^{c g(\theta)}}{\sqrt{2\pi V}},\quad
x_j(\delta)=hj-\delta,
\quad a_j=C_ch e^{-\theta x_j(\delta)},\quad
b_j=C_ch e^{\eta x_j(\delta)}.
\tag{20.2}
```

相位空间为把端点 $`0,h`$ 识别的圆。对 $`a,b\gt0`$ 置

```math
H(a,b)=
\begin{cases}
\displaystyle\frac{a(e^{-b}-e^{-a})}{a-b},&a\ne b,\\[4pt]
ae^{-a},&a=b,
\end{cases}
\qquad
\Psi_h(c,\delta)=\sum_{j\in\mathbb Z}
\exp\!\left\{-\frac{a_j}{e^{\theta h}-1}
               -\frac{b_j}{e^{\eta h}-1}\right\}H(a_j,b_j).
\tag{20.3}
```

**定理 20.2（实际平稳实验的格点临界曲线）。** 在定义 20.1 的条件下，若

```math
\lambda=\alpha_E\ell-\frac{\log\ell}{2\gamma}+c_M,
\qquad c_M\longrightarrow c\in\mathbb R,
\tag{20.4}
```

则已知方向、未知方向及联合支持与方向恢复的三种精确错误风险均满足

```math
R_M=1-\Psi_h(c,\delta_M)+o(1).
\tag{20.5}
```

该式分别适用于实际平稳独立对实验与实际平稳路径实验，误差对真实支持一致。
函数 $`\Psi_h`$ 连续、关于相位以 $`h`$ 为周期，且
$`0\lt\Psi_h(c,\delta)\lt1`$。另外，若 (20.4) 中
$`c_M\to+\infty`$ 或 $`c_M\to-\infty`$，三种错误风险分别趋于
$`0`$ 或 $`1`$；后两项不要求 $`\lambda/\ell\to\alpha_E`$，只要求样本量非负。

证明。先固定一条 $`\delta_M\to\delta`$ 的子序列，并暂定方向已知；若为反向，先按第 18 章的观测反向映射对齐计数。
第 19 章证明中的任意固定行数比较、全观测似然与计数截断均不使用非格点假设。
以下只替换局部极限定理和边界上的决策步骤。

记不含补偿的行分数为
$`Z_x=N_x^+\log(1+r)+N_x^-\log(1-r)\in h\mathbb Z`$，
完整似然排序分数为 $`W_x`$。先在独立复合 Poisson 参照中作固定指数倾斜
$`Q_\theta`$。单位时间增量的支持含 $`0,mh,-kh`$，故除以
$`h`$ 后最大格距为 $`1`$，均值与方差分别为
$`g'(\theta)/h`$、$`g''(\theta)/h^2`$。
[Stone 的格点局部极限定理](../../../Library/Dynamics/stone1967local.md)
应用于这个增量分布，给出对固定 $`j`$ 的

```math
Q_\theta\!\left\{Z=h\left\lfloor\frac{\beta\ell}{h}\right\rfloor+hj\right\}
=\frac{h}{\sqrt{2\pi\lambda g''(\theta)}}(1+o(1)).
\tag{20.6}
```

这里格点与倾斜均值之差为 $`O(\log\ell)`$。
将 $`\lambda`$ 分成整数部分与不足一单位的独立增量，即可处理非整数时间：
后者的均值、方差一致有界；先截断该增量，再用局部极限定理的全位置一致误差，
最后移去截断。该定理也给出所有格点质量的上界 $`O(\lambda^{-1/2})`$。
这里使用的是最大格距条件，没有把连续密度或非格点假设带入 (20.6)。

设 $`p_{0,M}(j)`$、$`p_{1,M}(j)`$ 分别为补偿背景与信号行的格点概率。
撤销固定倾斜，利用 $`\alpha_Eg'(\theta)=\beta`$、
$`\theta\beta-\alpha_Eg(\theta)=1`$ 及 (20.4)，得到

```math
(M-q)p_{0,M}(j)\longrightarrow a_j,
\qquad q\,p_{1,M}(j)\longrightarrow b_j.
\tag{20.7}
```

补偿的处理仍在原计数上完成：在总计数至多 $`L\ell`$ 的截断内，
补偿背景与未补偿背景的概率质量比为 $`1+o(1)`$，一致于计数组合；
截断外概率可取任意固定的 $`M^{-D}`$。所以 (20.7) 保留了点概率的相对精度。
这里不能把 $`W-Z=o(1)`$ 当作格点上的事件相同；(20.7) 计算的始终是
$`Z`$ 的格点事件，$`W`$ 留待后验论证。

对固定有限的格点集合，令 $`U_{M,j}`$、$`V_{M,j}`$ 分别计数其中的背景行与信号行。
把任意混合下降阶乘展开为互异行的和，全部行都在同一个真实支持下取样。
若总阶数为固定 $`s`$，第 19 章的比较给出相对误差
$`O(\ell^{s+1}/n)`$ 与任意 $`M^{-D}`$ 的加性误差；取 $`D\gt s`$ 后求和，
再用 (20.7)，得

```math
\mathbb E_S\prod_j(U_{M,j})_{u_j}(V_{M,j})_{v_j}
\longrightarrow\prod_j a_j^{u_j}b_j^{v_j}.
\tag{20.8}
```

有限维分布因此趋于全部独立的 Poisson 变量
$`U_j\sim\operatorname{Pois}(a_j)`$、$`V_j\sim\operatorname{Pois}(b_j)`$。
具体地，可对各类格点计数作独立的辅助稀疏化；固定阶 Bonferroni 上下界与
(20.8) 先给出稀疏化后无点的概率，再让阶数趋于无穷，得到联合概率母函数
$`\exp\{-\sum_j(t_ja_j+s_jb_j)\}`$，其中各保留概率在 $`[0,1]`$ 内。
这识别了所述有限维分布，并未假设实际观测行独立。

定义背景最高格点指标与信号最低格点指标为 $`J_{0,M}`$、$`J_{1,M}`$。
局部极限定理的全位置上界、固定倾斜与几何求和给出

```math
\limsup_{M\to\infty}\Pr_S\{J_{0,M}\gt J\}
\le K e^{-\theta hJ},\qquad
\limsup_{M\to\infty}\Pr_S\{J_{1,M}\lt-J\}
\le K e^{-\eta hJ}.
\tag{20.9}
```

常数可一致于紧的 $`(c,\delta)`$ 集。相反方向的紧性由固定格点的无点概率得到：
$`a_{-J}\to\infty`$、$`b_J\to\infty`$ 随 $`J\to\infty`$，
而 $`J_{0,M}\lt-J`$ 蕴含 $`U_{M,-J}=0`$，
$`J_{1,M}\gt J`$ 蕴含 $`V_{M,J}=0`$。
因此两种极值格点都紧。

现在返回全部实际观测。对单行截断取 $`D\gt1`$ 并对所有行取并集，得概率趋于一的事件
$`G_M`$，使

```math
\max_x(N_x^++N_x^-)\le L\ell,
\qquad \max_x|W_x-Z_x|\le\varepsilon_M\longrightarrow0.
\tag{20.10}
```

后一上界可取 $`O((q/M)\ell)`$。在 $`2\varepsilon_M\lt h`$ 时，
不同 $`Z`$ 格点之间的 $`W`$ 排序不变。令 $`j_*`$ 为观测中第
$`q`$ 大的 $`Z`$ 所在格点，$`N_*`$ 为该格点总行数，
$`K_*`$ 为从该格点仍须选取的行数。粗排序最优族 $`\mathcal F`$
包括所有高于 $`j_*`$ 的行，并从边界格点任选 $`K_*`$ 行，故
$`|\mathcal F|=\binom{N_*}{K_*}`$。

均匀支持先验下，第 18 章的完整观测似然给每个候选支持 $`T`$ 的后验权重
$`\exp\{\sum_{x\in T}W_x\}`$ 乘上同一个归一化因子。
在 $`G_M`$ 上，每个 MAP 支持都属于 $`\mathcal F`$；族内两权重之比在
$`[e^{-2N_*\varepsilon_M},e^{2N_*\varepsilon_M}]`$ 内。
边界格点 $`j_*`$ 位于 $`J_{0,M}`$ 与 $`J_{1,M}`$ 之间，包含端点：
所有信号都不低于 $`J_{1,M}`$；若该值不高于背景最大值，则严格高于背景最大值的
行至多有 $`q-1`$ 个；若它更高，则第 $`q`$ 大值恰为最低信号值。
极值紧性与固定窗口内 (20.8) 的计数紧性遂给出 $`N_*`$ 紧。

对 $`N_*\le L_0`$ 先固定截断，比较族内权重，随后平均、应用条件期望塔式法则，
再令 $`L_0\to\infty`$，得到实际 Bayes 成功概率

```math
P_M^{\mathrm{Bayes}}=
\mathbb E\!\left[
 \frac{\mathbf1_{\{S\in\mathcal F\}}}{\binom{N_*}{K_*}}
\right]+o(1).
\tag{20.11}
```

这个结论容许补偿在同一格点内重新排序，也容许实际 $`W`$ 精确并列；
没有给小的分数余项假设独立标记。

事件 $`S\in\mathcal F`$ 等价于 $`J_{1,M}\ge J_{0,M}`$。
若严格大于，边界格点全为信号，(20.11) 中分母为 $`1`$；
若相等于 $`j`$，分母为 $`\binom{U_{M,j}+V_{M,j}}{U_{M,j}}`$。
固定窗口内 (20.8) 的分布收敛适用于这个有界函数，再由极值紧性移去窗口。
按唯一的最高背景格点 $`j`$ 分拆，有

```math
P_M^{\mathrm{Bayes}}\longrightarrow
\sum_j e^{-\sum_{i\gt j}a_i-\sum_{i\lt j}b_i}
\mathbb E\!\left[
 \frac{\mathbf1_{\{U_j\ge1\}}}{\binom{U_j+V_j}{U_j}}
\right].
\tag{20.12}
```

其中 $`V_j=0`$ 恰好包含严格分离，不会重复计数。几何求和给出 (20.3) 的外因子，
而独立 Poisson 变量直接给出

```math
\mathbb E\!\left[
 \frac{\mathbf1_{\{U\ge1\}}}{\binom{U+V}{U}}
\right]
=e^{-a-b}\sum_{u\ge1,v\ge0}\frac{a^ub^v}{(u+v)!}
=a\int_0^1e^{-ta-(1-t)b}\,dt=H(a,b).
\tag{20.13}
```

按 $`u+v`$ 分组即得第一种闭式，取 $`a=b`$ 得第二种闭式。
这证明了所要求的后验平分系数。

正项级数在 $`(c,\delta)`$ 的紧集上一致可和：
当 $`j\to-\infty`$，$`a_j`$ 指数增长，外因子中的背景尾抑制所有幂次；
当 $`j\to+\infty`$，信号尾同样抑制 $`b_j`$ 的增长。
也可直接用 $`H(a,b)\le a e^{-\min(a,b)}`$ 给出可和包络。
所以曲线连续；把 $`\delta`$ 加 $`h`$ 只将指标平移一格。
任何固定相位子序列都已证明同一公式，圆的紧性遂将其提升为 (20.5)。

上述独立 Poisson 格点族的背景最大值与信号最小值均有限。
严格分离事件有正概率，反向交错事件也有正概率，因此曲线严格处于 $`0`$ 与 $`1`$ 之间。
第 18 章的置换对称性使随机化 MAP 的各支持风险相等，Bayes 值等于全规则 minimax 值。
同章的一致方向分类器与同数据联合界，将极限传递给未知方向及联合恢复；
因为 $`\alpha_E\gt\alpha_D`$，临界尺度上其方向错误趋于零。

最后，当 $`c\to+\infty`$ 时 $`C_c\to0`$。
无背景格点不低于 $`0`$ 且无信号格点不高于 $`0`$ 的概率趋于一，且对相位一致。
当 $`c\to-\infty`$ 时 $`C_c\to\infty`$；粗分离蕴含
背景最大格点不高于 $`0`$ 或信号最小格点不低于 $`0`$，两种无点概率之和
对相位一致趋于零。由第 19 章的样本前缀单调性，将任意发散偏移夹在固定有限偏移之外，
再令固定偏移趋于相应无穷，即得两端结论。∎

**定理 20.3（低成功率端的相位衰减率）。** 在定义 20.1 下，记

```math
A=\frac1{e^{\theta h}-1},\qquad B=\frac1{e^{\eta h}-1},\qquad
F_+(x)=h\bigl((A+1)e^{-\theta x}+Be^{\eta x}\bigr),\qquad
\rho_h(\delta)=F_+(h-\delta).
\tag{20.14}
```

则对每个固定 $`\delta\in[0,h]`$，

```math
\lim_{c\to-\infty}\frac{-\log\Psi_h(c,\delta)}{C_c}
=\rho_h(\delta).
\tag{20.15}
```

端点的值相同，而 $`\rho_h`$ 在 $`[0,h]`$ 上严格凸，唯一最小相位为

```math
\delta_*=h-\log\frac{\theta(A+1)}{\eta B}\in(0,h).
\tag{20.16}
```

特别地，存在有限 $`c_0`$，使对每个 $`c\lt c_0`$ 都有
$`\Psi_h(c,\delta_*)\gt\Psi_h(c,0)`$。更一般地，集合
$`E_h=\{c\in\mathbb R:\Psi_h(c,\delta_*)=\Psi_h(c,0)\}`$
在实轴上局部有限，并与 $`(-\infty,c_0)`$ 不交。

证明。暂把 $`C=C_c`$ 视为独立正参数。置

```math
F_-(x)=h\bigl(Ae^{-\theta x}+(B+1)e^{\eta x}\bigr),\qquad
F(x)=h\bigl(Ae^{-\theta x}+Be^{\eta x}
                 +\min(e^{-\theta x},e^{\eta x})\bigr).
\tag{20.17}
```

于是 $`F=F_+`$ 于非负半轴，$`F=F_-`$ 于非正半轴，且

```math
F_-(x)=F_+(x+h),\qquad
F_+(x+h)-F_+(x)=h(e^{\eta x}-e^{-\theta x}),\qquad
F_-(x-h)-F_-(x)=h(e^{-\theta x}-e^{\eta x}).
\tag{20.18}
```

当 $`0\lt\delta\lt h`$，令 $`x_0=h-\delta\in(0,h)`$。
格点 $`x_0`$ 与 $`x_0-h`$ 的 $`F`$ 值相等；由后两式，
向正、负两端逐格远离时该值严格增加。因此
$`\min_jF(hj-\delta)=F_+(h-\delta)`$。
端点由同样的非严格不等式得到，且
$`F_+(0)=F_+(h)`$。

对任一固定格点，(20.13) 的闭式说明相应级数项的负对数除以
$`C`$ 趋于 $`F(x_j)`$；在 $`a_j=b_j`$ 时，多出的因子
$`Ch`$ 不改变这个极限。保留一个最小格点即给出 (20.15) 的上极限界。
反方向利用 $`H(a,b)\le ae^{-\min(a,b)}`$：当 $`C\ge1`$ 时，

```math
\Psi_h(c,\delta)
\le C e^{-(C-1)\rho_h(\delta)}
\sum_{j\in\mathbb Z}h e^{-\theta x_j}e^{-F(x_j)}.
\tag{20.19}
```

右侧级数有限，因为 $`F(x)`$ 在两端指数增长。这给出匹配的下极限界，证明 (20.15)。

$`F_+''(x)\gt0`$，且 $`F_+'(x)=0`$ 恰好给出
$`x_* =\log(\theta(A+1)/(\eta B))`$。
由
$`\theta/(1-e^{-\theta h})\gt1/h\gt\eta/(e^{\eta h}-1)`$
得到 $`x_*\gt0`$；交换 $`\theta,\eta`$ 的同一不等式得到
$`x_*\lt h`$。所以 (20.16) 是严格内点最小值，
$`\rho_h(0)\gt\rho_h(\delta_*)`$。
最后将 (20.15) 分别用于这两个相位，得

```math
\frac1{C_c}\log\frac{\Psi_h(c,\delta_*)}{\Psi_h(c,0)}
\longrightarrow\rho_h(0)-\rho_h(\delta_*)\gt0,
\qquad c\to-\infty.
\tag{20.20}
```

因 $`C_c\to\infty`$，所述严格不等式对所有充分负的 $`c`$ 成立。

为证明例外集合的局部有限性，将 (20.13) 的积分式代回 (20.3)，
并将 $`C`$ 扩展到复半平面 $`\Re C\gt0`$。记
$`a_j^0=h e^{-\theta x_j}`$、$`b_j^0=h e^{\eta x_j}`$，每一项为整函数

```math
C a_j^0\int_0^1
\exp\{-C[(A+t)a_j^0+(B+1-t)b_j^0]\}\,dt.
```

对任意紧集 $`\Re C\ge\epsilon\gt0`$、$`|C|\le K`$，
该项的绝对值至多 $`K a_j^0e^{-\epsilon F(x_j)}`$，构成可和包络。
故级数在此半平面定义全纯函数。相位 $`\delta_*`$ 与 $`0`$ 的函数之差
由 (20.20) 不是恒零，其零点因而孤立。
$`c\mapsto C_c`$ 是实轴到正实轴的连续双射，且紧集映为半平面内部的紧集，
所以 $`E_h`$ 在每个有界闭区间内只有有限个点。∎

**定理 20.4（固定偏移下实际风险不收敛的振幅）。** 取

```math
\varphi=\frac{1+\sqrt5}{2},\qquad
r=\varphi^{-1},\qquad h=\log\varphi,\qquad \beta=\frac34.
\tag{20.21}
```

则 (20.1) 中 $`m=1,k=2`$。对每个固定 $`c\notin E_h`$，
因而也对每个充分负的固定偏移，沿全部整数维数 $`d\to\infty`$，取可实现的整数样本量满足

```math
\lambda=\alpha_E\ell-\frac{\log\ell}{2\gamma}+c+o(1),
\tag{20.22}
```

三种精确错误风险在实际平稳独立对实验和路径实验中都不收敛。
它们分别有趋于 $`1-\Psi_h(c,0)`$ 和 $`1-\Psi_h(c,\delta_*)`$
的两条子序列，且这两个极限不同。离散极值及并列振荡的相关结果见
[Ottolini](../../../Library/Dynamics/ottolini2020oscillations.md)。

证明。恒等式 $`1+r=\varphi`$、$`1-r=\varphi^{-2}`$ 给出格距与整数对。
比值 $`\log2/\log\varphi`$ 无理：若为有理数，则存在正整数
$`p,q`$ 使 $`2^q=\varphi^p`$；在数域 $`\mathbb Q(\sqrt5)`$
中取范数将给出 $`4^q=(-1)^p`$，矛盾。
因此 $`(3/4)\log2/\log\varphi`$ 也无理，圆上的无理旋转使

```math
\delta_M=\frac34(d-1)\log2\pmod{\log\varphi}
\tag{20.23}
```

稠密，且每个尾序列仍稠密。可分别选择相位趋于 $`0`$ 与 $`\delta_*`$ 的子序列。
对目标样本数取最近整数只改变 $`\lambda`$ 至多 $`O(1/n)`$，
不改变 (20.22)，而目标样本数最终为正。
定理 20.2 给出两条子序列的风险极限，定理 20.3 保证其不同。
若 $`c\in E_h`$，本命题的两相位比较不判定风险是否收敛。∎

## 追加锚（本行以下为增补区）

## 21. 几乎全恢复的高斯窗口与支持基数的二阶偏移

**定义 21.1（内在中心与归一化 Hamming 风险）。** 沿用
[定义 18.1](PARITY_HIDDEN_ARROW.md#18-增补十五固定振幅稀疏支持恢复与方向分离)
的补偿核、均匀平稳起点、实际独立对与连续路径实验，以及
$`H_{\mathcal E,q}^{\mathrm k},H_{\mathcal E,\mathrm u}^{\mathrm k}, H_{\mathcal E,q}^{\mathrm o},H_{\mathcal E,\mathrm u}^{\mathrm o}`$。
其中恰好 $`q`$ 元输出的损失为 $`|T\triangle S|/(2q)`$，任意子集输出的损失为
$`|T\triangle S|/q`$；上标分别表示方向已知与未知。固定
$`r\in(0,1)`$、$`\beta\in(1/2,1)`$，取

```math
n=2^d=2M,\qquad \ell=\log M,\qquad
q=M^{1-\beta+o(1)}\in\mathbb N,\qquad
\lambda=\frac{s}{n},\qquad a=\frac{rq}{M-q},\qquad
\tau_M=\log\frac Mq.
\tag{21.1}
```

样本数 $`s`$ 为非负整数，支持 $`S\subset C_+`$ 的大小恰为 $`q`$，在整个观测期间固定。
规则知道 $`d,s,q,r`$，不知道 $`S`$；方向未知时也不知道生成核是否转置。
置

```math
\begin{aligned}
g(\theta)&=\frac{(1+r)^\theta+(1-r)^\theta}{2}-1,\\[0pt]
\phi&=g'(1)=\frac{(1+r)\log(1+r)+(1-r)\log(1-r)}2\gt0,\\[0pt]
v&=g''(1)=\frac{(1+r)\log^2(1+r)+(1-r)\log^2(1-r)}2\gt0,\\[0pt]
\alpha_A&=\frac\beta\phi,\qquad V_A=\alpha_Av,\qquad
c_M=\frac{\lambda-\tau_M/\phi}{\sqrt\ell},\qquad
\mathcal L(c)=\Phi\!\left(-\frac{c\phi}{\sqrt{V_A}}\right),
\end{aligned}
\tag{21.2}
```

其中 $`\Phi`$ 为标准正态分布的下分布函数。
独立高斯稀疏序列中相应的 Hamming 临界轮廓已有
[Abraham–Castillo–Roquain 定理 7](../../../Library/Dynamics/abraham2024sharp.md)。
以下定理针对 (21.1) 的补偿核实际观测律，其推导使用一行、两行的相对概率估计与完整后验。

**定理 21.2（实际支持恢复的高斯临界曲线）。** 对定义 21.1 的任意序列，若
$`c_M\to c\in\mathbb R`$，则对每个
$`\mathcal E\in\{\mathrm{pair},\mathrm{path}\}`$，

```math
\lim_{d\to\infty}H_{\mathcal E,q}^{\mathrm k}
=\lim_{d\to\infty}H_{\mathcal E,\mathrm u}^{\mathrm k}
=\lim_{d\to\infty}H_{\mathcal E,q}^{\mathrm o}
=\lim_{d\to\infty}H_{\mathcal E,\mathrm u}^{\mathrm o}
=\mathcal L(c).
\tag{21.3}
```

本式对每个固定振幅成立，不要求
$`\log(1+r)/\log(1-r)`$ 无理。方向未知时，可以用同一份完整观测先判方向再选择支持；
达到上界的任意子集规则总输出至多 $`q`$ 个状态。

证明。先固定实际正向律与任一真实支持 $`S`$。使用 (18.8) 的得分

```math
\begin{aligned}
W_x&=N_{x,+}\log\frac{1+r}{1-a}
       +N_{x,-}\log\frac{1-r}{1+a},\\[0pt]
Z_x&=N_{x,+}\log(1+r)+N_{x,-}\log(1-r).
\end{aligned}
\tag{21.4}
```

令 $`Q_b`$ 表示均值为 $`\lambda(1+b)/2,\lambda(1-b)/2`$ 的两个独立
Poisson 计数的比较律。在有限 $`c`$ 的窗口内，$`\lambda/\ell\to\alpha_A`$，
所以 (18.11) 适用：对于任意指定的一行或两行计数事件 $`E`$，

```math
\mathbb P_{S,\varepsilon}^{\mathcal E}(E)
=\nu_{S,\varepsilon}(E)
 \left(1+O\!\left(\frac{\ell^{k+1}}n\right)\right)+O(M^{-D}),
\qquad k\in\{1,2\},\quad D\gt0.
\tag{21.5}
```

常数一致于支持、标记行与事件，$`D`$ 可任取固定值。正向信号行、正向背景行与
反向出发行的比较律分别为 $`Q_r,Q_{-a},Q_0`$，两行比较律为对应的乘积；
这不宣称实际行之间独立。

两个 Poisson 强度之和同为 $`\lambda`$，故指数补偿因子精确相消，得到

```math
\frac{dQ_r}{dQ_{-a}}=e^W,\qquad
\mathbb E_{Q_{-a}}e^W=1,\qquad
\frac{dQ_r}{dQ_0}=e^Z,\qquad
\mathbb E_{Q_0}e^Z=1.
\tag{21.6}
```

在 $`Q_r`$ 下，记两个跳幅为
$`h_{+,M}=\log((1+r)/(1-a))`$、$`h_{-,M}=\log((1-r)/(1+a))`$。
它们趋于有限常数，且 $`\lambda a=o(1)`$。因此

```math
\mathbb E_{Q_r}W=\lambda\phi+O(\lambda a),\qquad
\operatorname{Var}_{Q_r}W=\lambda v+O(\lambda a),\qquad
\frac{W-\tau_M}{\sqrt\ell}\ \Longrightarrow\ N(c\phi,V_A).
\tag{21.7}
```

具体地，对任意固定实数 $`u`$，中心化特征函数的对数为

```math
\log\mathbb E_{Q_r}
 \exp\!\left(iu\frac{W-\mathbb E_{Q_r}W}{\sqrt\ell}\right)
=\frac\lambda2\sum_{\sigma\in\{+1,-1\}}(1+\sigma r)
 \left(e^{iu h_{\sigma,M}/\sqrt\ell}-1-
       \frac{iu h_{\sigma,M}}{\sqrt\ell}\right)
\longrightarrow-\frac{u^2V_A}{2}.
\tag{21.8}
```

三阶余项为 $`O(\lambda\ell^{-3/2})=o(1)`$，均值中心由 (21.2) 给出。
(21.5) 将这个极限传到实际信号行，一致于 $`S`$。
对 $`Z`$ 使用固定跳幅得到同一中心极限。此处使用的区间尺度为 $`\sqrt\ell`$，
所以不需要格点局部极限定理。

置 $`h_M=\ell^{1/4}`$、$`t_+=\tau_M+h_M`$，令
$`F_+`$ 为背景行中满足 $`W_x\ge t_+`$ 的个数，
$`G_+`$ 为信号行中满足 $`W_x\lt t_+`$ 的个数。
由 (21.6) 的 Markov 界和 (21.5) 的一行估计，取固定 $`D\gt2`$，有

```math
Q_{-a}\{W\ge t_+\}\le e^{-t_+}=\frac qM e^{-h_M},\qquad
\frac{\mathbb E_{S,+}^{\mathcal E}F_+}{q}
\le(1+o(1))e^{-h_M}+O\!\left(\frac{M^{1-D}}q\right)=o(1),
\qquad
\frac{\mathbb E_{S,+}^{\mathcal E}G_+}{q}\longrightarrow\mathcal L(c).
\tag{21.9}
```

转移的是事件概率，而非实际律下无界的指数矩。
令 $`T_q`$ 为最大的 $`q`$ 个 $`W_x`$ 所组成的集合，并在边界并列值中均匀随机选择。
逐观测成立 $`|S\setminus T_q|\le G_++F_+`$，从而受约束风险的上极限至多为
$`\mathcal L(c)`$。

为得下界，固定 $`\epsilon\gt0`$，置
$`t_-=\tau_M-\epsilon\sqrt\ell`$ 与
$`I_M=[\tau_M-\epsilon\sqrt\ell,\tau_M-\epsilon\sqrt\ell/2]`$。
信号中心极限定理给出

```math
Q_r\{W\in I_M\}\longrightarrow
\kappa_\epsilon
=\Phi\!\left(\frac{-\epsilon/2-c\phi}{\sqrt{V_A}}\right)
 -\Phi\!\left(\frac{-\epsilon-c\phi}{\sqrt{V_A}}\right)\gt0.
\tag{21.10}
```

由精确换测度 (21.6)，充分大 $`M`$ 时背景尾概率满足

```math
p_-:=Q_{-a}\{W\ge t_-\}
\ge\mathbb E_{Q_r}\bigl[e^{-W}\mathbf1_{\{W\in I_M\}}\bigr]
\ge\frac{\kappa_\epsilon}{2}\frac qM
 e^{\epsilon\sqrt\ell/2}.
\tag{21.11}
```

令 $`B_-`$ 为实际背景行中 $`W_x\ge t_-`$ 的个数，
$`\mu=(M-q)p_-`$、$`\delta_M=\ell^3/n`$。在同一个固定真实支持下分别应用
(21.5) 的一行、两行版本，单行均值误差与双行乘积误差给出

```math
\mathbb E B_-=\mu(1+o(1)),\qquad
\operatorname{Var}(B_-)
\le C\bigl(\mu+\delta_M\mu^2+M^{2-D}\bigr),\qquad
\frac\mu q\longrightarrow\infty.
\tag{21.12}
```

例如不同背景行指标的协方差绝对值至多
$`C\delta_Mp_-^2+CM^{-D}`$。由于 $`q\to\infty`$、$`D\gt2`$ 与
$`\delta_M\to0`$，(21.12) 蕴含
$`\operatorname{Var}(B_-)/\mu^2\to0`$，继而
$`\mathbb P\{B_-\ge q\}\to1`$。
在该事件上，所有 $`W_x\lt t_-`$ 的信号都排在至少 $`q`$ 个背景行之后，因此均被
$`T_q`$ 遗漏。记这些信号数为 $`G_-`$，则逐观测有
$`|S\setminus T_q|\ge G_--q\mathbf1_{\{B_-\lt q\}}`$。
由实际信号极限可得

```math
\liminf_{d\to\infty}\mathbb E\frac{|S\setminus T_q|}{q}
\ge\Phi\!\left(\frac{-\epsilon-c\phi}{\sqrt{V_A}}\right).
\tag{21.13}
```

令 $`\epsilon\downarrow0`$，与上界结合，得该规则的归一化风险趋于
$`\mathcal L(c)`$，全部估计一致于真实支持。

这也是对全部受约束规则的极小极大结论。(18.9)–(18.10) 给出的实际完整似然为
$`C_a\prod_{x\in S}e^{W_x}`$，其中 $`C_a`$ 与支持无关；在均匀固定基数先验下，
后验包含概率与 $`W_x`$ 同序。故 $`T_q`$ 是受约束 Hamming Bayes 规则。
正类状态置换作用于全部观测并传送支持；并列时的均匀随机选择使 $`T_q`$ 等变，
风险恒定，所以它在每个有限样本量上就是极小极大规则。这一步只用完整观测的后验，
不将实际路径替换为独立坐标实验。

无约束风险的下界使用固定基数决策的二倍比较，其先例及不依赖错误包含关系的证明见
[Butucea–Mammen–Ndaoud–Tsybakov 条目](../../../Library/Dynamics/butucea2023selection.md)。
这里可直接在后验中验证：将包含概率降序记为
$`\pi_1\ge\cdots\ge\pi_M`$，有 $`\sum_i\pi_i=q`$。
置 $`A=\sum_{i=1}^q\pi_i`$、$`k=\#\{i:\pi_i\gt1/2\}`$、
$`S_k=\sum_{i=1}^k\pi_i`$。当 $`k\le q`$ 时
$`2S_k-k\le S_k\le A`$；当 $`k\gt q`$ 时
$`A\ge S_k-(k-q)\ge2S_k-k`$，最后一步来自 $`S_k\le q`$。
故未归一化的两种条件 Bayes 风险满足

```math
B_{\mathrm u}=q-\sum_i(2\pi_i-1)_+
\ge q-A=\frac{B_q}{2},\qquad
H_{\mathcal E,\mathrm u}^{\mathrm k}\ge H_{\mathcal E,q}^{\mathrm k}.
\tag{21.14}
```

最后的不等式由同一均匀先验的 Bayes 下界与受约束极小极大等式得到。
它不要求无约束 Bayes 输出至多含 $`q`$ 个状态。

匹配的无约束上界由一个有大小上限的规则达到。先选
$`A_+=\{x:W_x\ge t_+\}`$；若大小超过 $`q`$，只保留其最大的 $`q`$ 个得分，
并均匀处理并列。将结果记为 $`T_{\mathrm u}`$。删去的个数为
$`(|A_+|-q)_+=(F_+-G_+)_+\le F_+`$，所以逐观测有

```math
|T_{\mathrm u}|\le q,\qquad
|T_{\mathrm u}\triangle S|\le G_++2F_+.
\tag{21.15}
```

(21.9)、(21.14)–(21.15) 证明已知正向的两种风险均趋于同一曲线。
已知反向时反转每个有序对，或反转包含起终点的整条路径，即精确归约到正向。

最后构造窗口内的方向判别器。对原始观测的出发行 $`Z_x`$ 定义

```math
T=\sum_{x\in C_+}\mathbf1_{\{Z_x\ge\tau_M+h_M\}},\qquad
\widehat\varepsilon=
\begin{cases}+,&T\gt q/\ell,\\[0pt]-,&T\le q/\ell.\end{cases}
\tag{21.16}
```

在实际反向下，每行的比较律是 $`Q_0`$。由 (21.5)–(21.6)，

```math
\max_S\mathbb P_{S,-}^{\mathcal E}\{\widehat\varepsilon=+\}
\le\frac\ell q\max_S\mathbb E_{S,-}^{\mathcal E}T
\le(1+o(1))\ell e^{-h_M}
 +O\!\left(\frac{\ell M^{1-D}}q\right)\longrightarrow0.
\tag{21.17}
```

在正向下，仅计信号对 $`T`$ 的贡献，记为 $`T_S`$。
$`Z`$ 的信号极限与同一真实支持下的两行估计给出

```math
\frac{\mathbb E T_S}{q}\longrightarrow
\rho(c)=\Phi\!\left(\frac{c\phi}{\sqrt{V_A}}\right)\gt0,\qquad
\frac{\operatorname{Var}(T_S)}{q^2}
\le C\left(\frac1q+\frac{\ell^3}n+M^{-D}\right)\longrightarrow0.
\tag{21.18}
```

因此 $`T_S/q\to\rho(c)`$ 依概率成立，正向误判概率也一致趋零。
按判得的方向对齐原观测，再应用 $`T_q`$ 或 $`T_{\mathrm u}`$。
方向判对时，输出就是同一数据上的已知方向规则；方向判错时，两种输出均至多含
$`q`$ 个状态，原始 Hamming 损失至多为 $`2q`$。
所以受约束与无约束归一化风险的增加分别至多为方向错误概率及其两倍。
这里不要求判向结果与支持规则独立，也不需要分割样本。
未知方向的极小极大风险又不小于对应已知方向风险，遂得 (21.3)。∎

**定理 21.3（无限偏移与基数修正的临界位置）。** 在定义 21.1 下，不另要求
$`\lambda/\ell`$ 收敛。如果 $`c_M\to+\infty`$，则 (21.3) 的四种风险均趋于零；
如果 $`c_M\to-\infty`$，则它们均趋于一。此结论同时适用于两个实验。
特别地，若固定 $`b,c\in\mathbb R`$，且

```math
\log q=(1-\beta)\ell+b\sqrt\ell+o(\sqrt\ell),\qquad
\lambda=\alpha_A\ell+c\sqrt\ell+o(\sqrt\ell),
\tag{21.19}
```

则这八种风险的共同极限为

```math
\Phi\!\left(-\frac{c\phi+b}{\sqrt{V_A}}\right).
\tag{21.20}
```

若 $`q=\lfloor M^{1-\beta}\rfloor`$ 且
$`\lambda=\alpha_A\ell+o(\sqrt\ell)`$，共同极限为 $`1/2`$。
单独的 $`\lambda/\ell\to\alpha_A`$ 与
$`q=M^{1-\beta+o(1)}`$ 不能确定该极限。

证明。固定 $`d,q,r`$，增加样本量不会增加任何一种极小极大风险：独立对实验可丢弃
后续样本，路径实验可保留初始路径段；两种操作均保留所论实际平稳律，且不要求知道方向。
对任意固定 $`t\in\mathbb R`$，取

```math
s_M(t)=\max\!\left\{0,
 \left\lfloor n\left(\frac{\tau_M}\phi+t\sqrt\ell\right)\right\rfloor\right\}.
\tag{21.21}
```

因 $`\tau_M\sim\beta\ell`$，充分大 $`M`$ 时截零不作用，取整只使
$`\lambda`$ 改变 $`O(1/n)`$。定理 21.2 给出此样本量下的风险极限为
$`\mathcal L(t)`$。若 $`c_M\to+\infty`$，原样本量最终不小于每个固定
$`s_M(t)`$，故风险上极限至多为 $`\mathcal L(t)`$；令 $`t\to+\infty`$ 即得零。
若 $`c_M\to-\infty`$，反向比较给出风险下极限不小于
$`\mathcal L(t)`$；令 $`t\to-\infty`$ 即得一。
受约束风险用任意固定 $`q`$ 元输出、无约束风险用空集输出，均至多为一。

(21.19) 给出
$`\tau_M=\beta\ell-b\sqrt\ell+o(\sqrt\ell)`$，所以
$`c_M\to c+b/\phi`$，代入 (21.3) 即得 (21.20)。
指定的取整基数满足 $`\log q=(1-\beta)\ell+o(1)`$。
仍取该基数，而令
$`\lambda=\alpha_A\ell\pm\ell^{3/4}+O(1/n)`$，则两条序列均保持相同的一阶比值，
风险却分别趋于零与一。这证明只给出一阶标度不足以指定边界风险。∎

## 追加锚（本行以下为增补区）

## 22. 未知振幅、基数与方向的自适应 Hamming 窗口

**定义 22.1（双向似然混合与逐步选择）。** 对定义 21.1 的状态空间，令
$`M\ge2`$、$`\ell=\log M`$，置

```math
J_M=\max\{2,\lceil\ell^2\rceil\},\qquad
u_j=\frac j{J_M}\quad(1\le j\lt J_M),\qquad
\eta_M=\min\{1/16,\ell^{-2}\}.
```

式 (22.1)。

对原始观测的出发行计数定义 $`N_{x,\pm}^{+}`$；反转每个有序对，或反转包含两端点的
整条路径后，以同样方式定义 $`N_{x,\pm}^{-}`$。对于 $`x\in C_+`$、
$`\sigma\in\{+,-\}`$，定义非负分数

```math
E_x^\sigma=\frac1{J_M-1}\sum_{j=1}^{J_M-1}
 (1+u_j)^{N_{x,+}^\sigma}(1-u_j)^{N_{x,-}^\sigma}.
```

式 (22.2)。

将每个方向的分数按降序记为 $`E_{[1]}^\sigma\ge\cdots\ge E_{[M]}^\sigma`$，并令

```math
R_\sigma=\max\left(\{0\}\cup
 \left\{k\in\{1,\ldots,M\}:E_{[k]}^\sigma\ge\frac M{\eta_M k}\right\}\right).
```

式 (22.3)。

当 $`R_\sigma=0`$ 时置 $`A_\sigma=\varnothing`$；否则取最大的
$`R_\sigma`$ 个分数对应的状态为 $`A_\sigma`$。最后定义

```math
\widehat S=A_+\cup A_-,\qquad
\widehat\varepsilon=
\begin{cases}+,&R_+\ge R_-,\\[0pt]-,&R_+\lt R_-.
\end{cases}
```

式 (22.4)。

这些规则仅使用维数与实际观测，不使用 $`q,r,\beta`$ 或临界偏移。
(22.3) 的阈值形式是
[Wang–Ramdas 的基本 e-BH 规则](../../../Library/Dynamics/wang2022evalues.md)。
背景行分数在实际律下的 e-value 期望条件将在证明中直接核对；
归一化 Hamming 损失还需要比 FDR 更强的期望误选个数控制。

**定理 22.2（未知参数达到已知参数的临界风险）。** 固定
$`r\in(0,1)`$、$`\beta\in(1/2,1)`$，取定义 21.1 的任意序列，满足
$`c_M\to c\in\mathbb R`$。对每个
$`\mathcal E\in\{\mathrm{pair},\mathrm{path}\}`$，定义 22.1 的同一规则满足

```math
\max_{S\in\mathfrak S_q,\ \varepsilon\in\{+,-\}}
 \frac{\mathbb E_{S,\varepsilon}^{\mathcal E}|\widehat S\triangle S|}{q}
\longrightarrow\mathcal L(c),\qquad
\max_{S,\varepsilon}\mathbb P_{S,\varepsilon}^{\mathcal E}
 \{\widehat\varepsilon\ne\varepsilon\}\longrightarrow0.
```

式 (22.5)。

更具体地，实际正向下的两次选择满足一致于 $`S`$ 的界

```math
\mathbb E_{S,+}^{\mathcal E}|A_+\setminus S|
=O\!\left(\frac q{\ell^2}+\frac1\ell\right),\qquad
\mathbb E_{S,+}^{\mathcal E}|A_-|=O(\ell^{-1}),
```

式 (22.6)。

反向时交换两个符号。本定理是对每个固定 $`r,\beta,c`$ 的自适应结论，
不要求这些参数为规则所知，也不声称参数趋近端点时的一致收敛。

证明。固定实际正向及真实支持。由 (21.5)，一行、两行的任意计数事件仍有
相对加加性比较，记 $`\delta_M=\ell^3/n`$，余项指数固定取 $`D=4`$。
原观测中信号行、背景行的比较律为 $`Q_r,Q_{-a}`$；反转观测的全部出发行
比较律为 $`Q_0`$。

先核对实际律的精确期望条件。对固定 $`x\in C_+`$ 与 $`u\in(0,1)`$，
路径乘积 $`(1+u)^{N_{x,+}}(1-u)^{N_{x,-}}`$ 的下一步乘子为
$`1+u\mathbf1_{\{X_t=x\}}\chi(X_{t+1})`$。
在正向核下，其条件期望是
$`1+u b_S(x)\mathbf1_{\{X_t=x\}}`$，背景行 $`x\notin S`$ 时不超过一。
反向核则满足

```math
\sum_y\chi(y)P_S^{\mathsf T}(z,y)
=\frac{\chi(z)}n\sum_y\chi(y)b_S(y)
=\frac{\chi(z)}n\bigl(rq-a(M-q)\bigr)=0.
```

所以每个反向出发行乘积都是从一出发的非负鞅；正向背景行乘积是非负超鞅。
在独立对实验中，下一对的乘子均值分别为 $`1+u b_S(x)/n`$ 与一，结论相同。
取确定权重的有限平均，得到实际背景行的 $`\mathbb E E_x\le1`$，以及反向出发行的
$`\mathbb E E_x=1`$。这是非负鞅与混合的经典期望论证；它在本模型中依赖上述补偿恒等式。
随后由基本 e-BH 的既有结论可控制每个方向的 FDR，但下文另证期望误选个数界。

对于任意 $`u\in(0,1)`$，在比较律下也有

```math
\mathbb E_{Q_{-a}}(1+u)^{N_+}(1-u)^{N_-}
=e^{-\lambda a u}\le1,\qquad
\mathbb E_{Q_0}(1+u)^{N_+}(1-u)^{N_-}=1.
```

式 (22.7)。

算术平均保留此界。因此任一背景比较分数 $`E`$ 满足
$`Q\{E\ge z\}\le z^{-1}`$。下面只将这一事件概率经 (21.5) 传到实际律，
不将无界矩直接移过去。

先证明控制随机选择数所需的误选估计。设某一方向至多有 $`q_0`$ 个信号行，
其余行的比较分数有 (22.7) 的界，且实际一行、两行估计如上。
对固定实数 $`m\ge1`$，令 $`B_m`$ 计数其中满足
$`E_x\ge M/(2\eta_Mm)`$ 的背景行。比较均值至多 $`2\eta_Mm`$。
实际 e-value 条件直接给出均值界；同一实际律下的两行协方差估计再给出

```math
\mathbb E B_m\le2\eta_Mm,\qquad
\mathrm{Var}(B_m)
\le C\left(\eta_Mm+\delta_M\eta_M^2m^2+M^{2-D}\right).
```

式 (22.8)。

因为 $`\eta_M\le1/16`$，对所有 $`m\ge1`$，充分大 $`M`$ 时均值至多
$`m/4`$。Chebyshev 不等式于是给出

```math
\mathbb P\{B_m\ge m/2\}
\le C\left(\frac{\eta_M}m+\delta_M\eta_M^2+
             \frac{M^{2-D}}{m^2}\right).
```

式 (22.9)。

设 $`R,A`$ 是这个方向按 (22.3) 得到的选择数与集合，以 $`F`$ 记所选背景行数。
若 $`q_0\ge1`$ 且 $`R\le2q_0`$，所选背景行均超过
$`M/(2\eta_Mq_0)`$，所以

```math
\mathbb E\bigl[F\mathbf1_{\{R\le2q_0\}}\bigr]
\le2\eta_Mq_0.
```

式 (22.10)。

对 $`R\gt2q_0`$，按 $`m=2q_0\,2^j\lt M`$ 分成不交事件
$`m\lt R\le\min\{2m,M\}`$。在每个事件上，至少
$`R-q_0\ge m/2`$ 个背景行达到 $`M/(\eta_MR)\ge M/(2\eta_Mm)`$，
故该事件包含于 $`\{B_m\ge m/2\}`$。乘以 $`2m`$ 并对 (22.9) 求和，得到

```math
\mathbb E\bigl[R\mathbf1_{\{R\gt2q_0\}}\bigr]
\le C\left(
 \eta_M(1+\log M)+M\delta_M\eta_M^2+
 \frac{M^{2-D}}{q_0}\right).
```

式 (22.11)。

其中使用二进段数为 $`O(1+\log M)`$、$`\sum m\le2M`$ 和
$`\sum m^{-1}\le1/q_0`$。因此 (22.10)–(22.11) 控制的是期望误选个数。
独立序列中用此类计数界证明自适应 Hamming 风险已有
[Abraham–Castillo–Roquain 引理 S-9](../../../Library/Dynamics/abraham2024sharp.md)
的先例；这里的二行估计针对实际补偿路径的共同概率律。
若 $`q_0=0`$，直接从 $`m=1,2,4,\ldots`$ 的区间
$`m\le R\lt2m`$ 分解；区间事件仍迫使 $`B_m\ge m`$，同样得到

```math
\mathbb E R
\le C\left(\eta_M(1+\log M)+M\delta_M\eta_M^2+M^{2-D}\right).
```

式 (22.12)。

由于 $`M\delta_M=\ell^3/2`$、最终 $`\eta_M=\ell^{-2}`$，
(22.10)–(22.12) 在正向分别取 $`q_0=q`$ 和 $`q_0=0`$，即得 (22.6)。
并未从 FDR 界推出期望误选个数界。

下面证明信号检出率。对固定真实 $`r`$，取一个网格点 $`u_{j(M)}`$，使
$`|u_{j(M)}-r|\le1/J_M`$。充分大 $`M`$ 时该点属于开区间网格。
记 $`Z_x(u)=N_{x,+}\log(1+u)+N_{x,-}\log(1-u)`$。
在 $`N_{x,+}+N_{x,-}\le C_D\ell`$ 上，均值定理给出

```math
|Z_x(u_{j(M)})-Z_x(r)|\le C_r\frac\ell{J_M}=o(1),\qquad
\log E_x^+\ge Z_x(r)-\log(J_M-1)-o(1).
```

式 (22.13)。

截断外比较概率与实际概率均可取为 $`O(M^{-D})`$，见 (17.9) 与 (21.5)。
网格平均损失 $`\log(J_M-1)=O(\log\ell)=o(\sqrt\ell)`$。
于是对任意阈值 $`t_M=\tau_M+O(\log\ell)`$，信号中心极限定理给出

```math
\liminf_{M\to\infty}Q_r\{\log E^+\ge t_M\}
\ge\rho(c):=\Phi\!\left(\frac{c\phi}{\sqrt{V_A}}\right)\gt0.
```

式 (22.14)。

固定只用于证明的常数 $`0\lt\kappa\lt\rho(c)`$，令
$`k_M=\lfloor\kappa q\rfloor`$。充分大 $`M`$ 时 $`k_M\ge1`$，且

```math
\log\frac M{\eta_M k_M}
=\tau_M+O(\log\ell).
```

式 (22.15)。

在实际信号行中，超过 (22.15) 阈值的个数记为 $`Y_M`$。
由 (22.14)、一行估计及同一真实支持下的两行协方差估计，
$`\liminf\mathbb EY_M/q\ge\rho(c)`$，且

```math
\frac{\mathrm{Var}(Y_M)}{q^2}
\le C\left(\frac1q+\delta_M+M^{-D}\right)\longrightarrow0.
```

式 (22.16)。

因此 $`\mathbb P\{Y_M\ge k_M\}\to1`$，一致于 $`S`$。
该事件上第 $`k_M`$ 大分数满足 (22.3)，故 $`R_+\ge k_M`$。
当 $`R_+\ge k_M`$ 时，所有达到 $`M/(\eta_Mk_M)`$ 的行都在 $`A_+`$ 中：
若一条被遗漏，则至少 $`R_++1`$ 条分数达到此阈值，因
$`M/(\eta_Mk_M)\ge M/(\eta_M(R_++1))`$，与最大性矛盾。
同样的最大性表明，当 $`0\lt R_+\lt M`$ 时，截断处不可能将相同分数拆开。
所以实际并列值不会影响所选集合或这些包含关系。

结合 (22.13)–(22.16)，被 $`A_+`$ 遗漏的信号比例满足

```math
\limsup_{M\to\infty}\max_S
 \frac{\mathbb E_{S,+}^{\mathcal E}|S\setminus A_+|}{q}
\le1-\rho(c)=\mathcal L(c).
```

式 (22.17)。

并集只能减少漏选，新增误选个数至多为另一方向的选择数。因此

```math
|\widehat S\triangle S|
\le |S\setminus A_+|+|A_+\setminus S|+|A_-|.
```

式 (22.18)。

(22.6)、(22.17) 给出归一化风险的上极限。实际反向由整份观测的精确反转得到同一界。
任何不使用参数的规则在揭示这些参数后仍是合法规则，故其最坏支持风险不小于
定理 21.2 中已知 $`q,r`$ 与方向的无约束极小极大风险。这给出匹配下界，证明 (22.5)
的风险等式。

最后，在正向下 $`R_+\ge\kappa q+o(q)`$ 以趋于一的概率成立，而由 (22.6)
与 Markov 不等式，$`\mathbb P\{R_-\ne0\}\le\mathbb ER_-=O(\ell^{-1})`$。
所以按选择数比较得到的方向也一致正确；反向同理。整段证明没有把方向选择当成独立样本，
也没有用未知基数限制输出大小。∎

## 追加锚（本行以下为增补区）

## 23. 两种 Hamming 风险在共同极限之下的分离

**定义 23.1（保留实际中心的二阶尺度）。** 沿用定义 21.1 的两个实际平稳实验、
固定参数 $`r\in(0,1)`$、$`\beta\in(1/2,1)`$、整数基数
$`q=M^{1-\beta+o(1)}`$ 与四种极小极大风险。假设 $`c_M\to c\in\mathbb R`$，置

```math
z_M=\frac{\tau_M-\lambda\phi}{\sqrt{\lambda v}},\qquad
\varphi(z)=\frac{e^{-z^2/2}}{\sqrt{2\pi}},\qquad
z_*=-\frac{c\phi}{\sqrt{V_A}}.
```

式 (23.1)。

于是 $`\lambda\sim\alpha_A\ell`$、$`z_M\to z_*`$。
这里保留实际的 $`\tau_M=\log(M/q)`$ 与 $`\lambda=s/n`$；
只用一阶等价式替换它们，不保证保留下述余项精度。

**定理 23.2（基数约束的对数修正与风险差）。** 对定义 23.1 的任意序列，
每个 $`\mathcal E\in\{\mathrm{pair},\mathrm{path}\}`$ 与
$`\xi\in\{\mathrm k,\mathrm o\}`$ 均满足

```math
\begin{aligned}
H_{\mathcal E,q}^{\xi}
 &=\Phi(z_M)-\frac{\varphi(z_M)\log\lambda}{2\sqrt{\lambda v}}
       +O(\lambda^{-1/2}),\\[0pt]
H_{\mathcal E,\mathrm u}^{\xi}
 &=\Phi(z_M)+O(\lambda^{-1/2}).
\end{aligned}
```

式 (23.2)。

因此

```math
\lim_{d\to\infty}\frac{\sqrt\ell}{\log\ell}
 \left(H_{\mathcal E,\mathrm u}^{\xi}-H_{\mathcal E,q}^{\xi}\right)
 =\frac{\varphi(z_*)}{2\sqrt{V_A}}\gt0.
```

式 (23.3)。

此处比较的是损失分别除以 $`q`$ 与 $`2q`$ 的两种风险。
余项常数允许依赖固定参数及 $`z_M`$ 所在的有界区间。
结论同时包括格点与非格点得分，不要求任何无理性条件。

独立高斯序列中的一阶先例见
[Abraham–Castillo–Roquain 推论 S-3](../../../Library/Dynamics/abraham2024sharp.md)：
其最大基数排序规则的原始 Hamming 损失除以信号数趋于 $`2\overline\Phi(b)`$，
故再除以二后，与无约束风险有共同的一阶曲线。
式 (23.2) 则在这里的两个实际补偿实验中保留实际中心，给出两种归一化风险的
$`\log\lambda/\sqrt\lambda`$ 差及 $`O(\lambda^{-1/2})`$ 余项。

证明。先固定实际正向及真实支持 $`S`$。
仍用 (21.4) 的 $`W,Z`$ 与比较律 $`Q_r,Q_{-a}`$，记
$`\delta_M=\ell^3/n`$，在 (21.5) 中固定取 $`D=6`$。

先提高比较律中的正态近似精度。所用一般工具是经典 Berry–Esseen 不等式，
其独立同分布、三阶绝对矩版本及统一常数见
[Shevtsova 的式 (1) 与推论 1](../../../Library/Dynamics/shevtsova2011berryesseen.md)。
对于 $`k=\lfloor\lambda\rfloor`$，将总强度为 $`\lambda`$ 的复合 Poisson 和
拆成 $`k`$ 个独立同分布的和，每个强度为 $`\lambda/k\in[1,2]`$。
两个跳幅 $`h_{\pm,M}`$ 有界并趋于 $`\log(1\pm r)`$；单份方差一致下界为正，
中心化三阶绝对矩一致有界。后一点可由跳数的三阶矩控制，因为跳数均值不超过二。
故不等式的同一个常数可用于每个 $`M`$。结合
$`\mathbb EW=\lambda\phi+O(\lambda a)`$、
$`\mathrm{Var}W=\lambda v+O(\lambda a)`$ 与 $`\lambda a=o(1)`$，得到

```math
\sup_t\left|Q_r\{W\lt t\}
 -\Phi\!\left(\frac{t-\lambda\phi}{\sqrt{\lambda v}}\right)\right|
 \le\frac C{\sqrt\lambda}.
```

式 (23.4)。

将真实均值、方差替换为此处中心与尺度的误差也是 $`O(\lambda^{-1/2})`$：
中心误差除以标准差为 $`O(\sqrt\lambda a)`$，相对方差误差为 $`O(a)`$。
由左右极限，单点质量至多为 $`2C/\sqrt\lambda`$，所以严格与非严格事件均可用同一阶界。

对任意固定宽度 $`H\gt0`$，(23.4) 给出全实轴上的区间上界
$`Q_r\{t\le W\lt t+H\}\le C_H/\sqrt\lambda`$。
若 $`|(t-\lambda\phi)/\sqrt{\lambda v}|\le A`$，取足够大而固定的 $`H`$，
使高斯区间质量的系数超过 (23.4) 两端误差之和，即有

```math
\frac{c_H}{\sqrt\lambda}
 \le Q_r\{t\le W\lt t+H\}
 \le\frac{C_H}{\sqrt\lambda}.
```

式 (23.5)。

下界只在所述中心区间断言，上界对所有 $`t`$ 成立。
$`H`$ 可以依赖 $`A,r`$，不依赖 $`M`$。这一步使用固定宽度内的总质量，
无需指定格点相位或单点概率。

由精确换测度 $`dQ_r/dQ_{-a}=e^W`$，把上尾分成宽度为 $`H`$ 的半开区间，
并求和几何级数，得到

```math
Q_{-a}\{W\ge t\}\le\frac{C e^{-t}}{\sqrt\lambda},\qquad
\mathbb E_{Q_{-a}}\!\left[e^{2W}\mathbf1_{\{W\le t\}}\right]
 =\mathbb E_{Q_r}\!\left[e^W\mathbf1_{\{W\le t\}}\right]
 \le\frac{C e^t}{\sqrt\lambda}.
```

式 (23.6)。

两项上界对所有实数 $`t`$ 成立；第二项用从 $`t`$ 向下的分段。
端点质量由 (23.4) 控制。对中心区间的 $`t`$，只取 (23.5) 的一个区间又得

```math
Q_{-a}\{W\ge t\}\ge\frac{c e^{-t}}{\sqrt\lambda}.
```

式 (23.7)。

这些是比较律的精确换测度结果，没有把实际律的无界指数矩当作比较矩。

令 $`t_0=\tau_M-\tfrac12\log\lambda`$。取稍后固定的 $`K\gt0`$，置
$`t_-=t_0-K`$、$`t_+=t_0+K`$。对任一阈值，令 $`B(t)`$、$`Y(t)`$
分别为实际背景与信号中得分至少为 $`t`$ 的个数。由 (23.6)–(23.7)，
背景比较均值满足

```math
c e^Kq\le (M-q)Q_{-a}\{W\ge t_-\}\le C e^Kq,
\qquad (M-q)Q_{-a}\{W\ge t_+\}\le C e^{-K}q.
```

式 (23.8)。

这里 $`q/M\to0`$ 已吸收到常数。又由 (23.4)，
$`Q_r\{W\ge t_+\}=1-\Phi(z_M)+o(1)`$，而 $`\Phi(z_M)`$ 一致远离零。
因而可取固定 $`K`$，使充分大 $`M`$ 时
$`\mathbb EB(t_-)\ge(1+\epsilon)q`$ 与
$`\mathbb E[B(t_+)+Y(t_+)]\le(1-\epsilon)q`$，其中 $`\epsilon\gt0`$ 固定。
这些均值也使用了 (21.5) 的一行转移。

对上述任一计数 $`N`$，同一真实支持下的单行与双行估计给出

```math
\mathrm{Var}N\le C\left(q+\delta_Mq^2+M^{2-D}\right).
```

式 (23.9)。

例如任意两行的协方差绝对值不超过其比较概率乘积的
$`C\delta_M`$ 倍再加 $`CM^{-D}`$；总比较均值为 $`O(q)`$，故求和给出此式。
Chebyshev 不等式于是证明

```math
\mathbb P\{B(t_-)\lt q\}
 +\mathbb P\{B(t_+)+Y(t_+)\ge q\}
 \le C\left(q^{-1}+\delta_M+\frac{M^{2-D}}{q^2}\right)
 =o(\lambda^{-1/2}).
```

式 (23.10)。

令 $`T_q`$ 是并列时均匀随机的最大 $`q`$ 个得分的集合。
在 (23.10) 两个坏事件之外，所有得分小于 $`t_-`$ 的信号均被遗漏，
所有得分至少为 $`t_+`$ 的信号均被选中。
信号漏选比例的期望因此被两个阈值处的信号分布函数夹住，误差为
$`o(\lambda^{-1/2})`$。由 (21.5)、(23.4)，两个端点均为

```math
\Phi\!\left(z_M-\frac{\log\lambda}{2\sqrt{\lambda v}}\right)
 +O(\lambda^{-1/2}).
```

式 (23.11)。

第 21 章的完整后验排序与置换对称性说明 $`T_q`$ 在每个有限样本量上就是
受约束极小极大规则。将 (23.11) 作 Taylor 展开，余项
$`O((\log\lambda)^2/\lambda)=o(\lambda^{-1/2})`$，得到 (23.2) 第一行的已知方向版本。

无约束上界改用 $`\tau_M`$ 阈值。令 $`F,G`$ 为误选和漏选个数；
(23.4)、(23.6) 与一行转移给出

```math
\frac{\mathbb EF}{q}=O(\lambda^{-1/2}),\qquad
\frac{\mathbb EG}{q}=\Phi(z_M)+O(\lambda^{-1/2}).
```

式 (23.12)。

若阈值集合超过 $`q`$ 元，保留最大的 $`q`$ 个得分。
(21.15) 的逐观测界仍给出原始损失至多 $`G+2F`$，故此规则达到
$`\Phi(z_M)+O(\lambda^{-1/2})`$ 的上界且输出大小不超过 $`q`$。

匹配下界使用的每块一信号先验及块内似然后验已有
[Abraham–Castillo–Roquain §8.1](../../../Library/Dynamics/abraham2024sharp.md)
的直接先例。这里对实际补偿律另外控制截断权重之和及其定量误差。取 $`B=\lfloor M/q\rfloor`$，将 $`qB`$ 个正类状态分成
$`q`$ 个互不相交的 $`B`$ 元块，其余状态不设置信号。
先验在每块独立、均匀地选择一个信号，因而支持总大小始终精确等于 $`q`$，
在同一 $`M`$ 下补偿系数 $`a`$ 不随先验支持改变。由实际完整似然
$`C_a(\mathcal D)\prod_{x\in S}e^{W_x}`$，给定全部观测 $`\mathcal D`$ 后，
第 $`j`$ 块中状态 $`x`$ 的包含概率为

```math
\pi_x=\frac{e^{W_x}}{\sum_{y\text{ in block }j}e^{W_y}}.
```

式 (23.13)。

后验因式分解来自先验的乘积及完整似然；它不要求观测或块之间独立。
未使用的行也在完整观测中，其共同似然因子不依赖支持。
无约束 Hamming Bayes 规则逐状态以 $`\pi_x\gt1/2`$ 为选入条件；
等号时任选，在下文只用严格小于的事件。

固定一个实际支持与其中一块，以 $`x_*`$ 表示该块的真信号。
设 $`t=\tau_M-K_0`$，其中 $`K_0\gt0`$ 为任一固定常数，并令

```math
L=e^t,\qquad f(w)=e^w\mathbf1_{\{w\le t\}},\qquad
T=\sum_{x\ne x_*,\ x\text{ in this block}}f(W_x),\qquad
m_f=\mathbb E_{Q_{-a}}f(W)=Q_r\{W\le t\}.
```

式 (23.14)。

这里 $`0\le f\le L`$ 且 $`L\asymp B`$。
为转移这些有界矩，对任意非负有界函数使用层蛋糕积分
$`\mathbb E f=\int_0^L\mathbb P\{f\gt u\}\,du`$，
对两行乘积使用双重积分；(21.5) 的常数一致于所有事件，故

```math
\begin{aligned}
\mathbb E f(W_x)&=m_f(1+O(\delta_M))+O(LM^{-D}),\\[0pt]
|\mathrm{Cov}(f(W_x),f(W_y))|
 &\le C\delta_M m_f^2+CL^2M^{-D}\quad(x\ne y),\\[0pt]
\mathbb E f(W_x)^2
 &\le C\mathbb E_{Q_{-a}}f(W)^2+CL^2M^{-D}
 \le\frac{CL}{\sqrt\lambda}+CL^2M^{-D}.
\end{aligned}
```

式 (23.15)。

协方差式由双行乘积估计减去单行均值之积得到；充分大 $`M`$ 时 $`L\ge1`$、
$`m_f\le1`$，单行加性余项的交叉项可并入 $`CL^2M^{-D}`$。
因此 (23.4)、(23.14)–(23.15) 给出

```math
\frac{\mathbb ET}{B}=\Phi(z_M)+O(\lambda^{-1/2}),\qquad
\frac{\mathrm{Var}T}{B^2}
 \le C\left(\lambda^{-1/2}+\delta_M+B^2M^{-D}\right)
 =O(\lambda^{-1/2}).
```

式 (23.16)。

均值中 $`B-1`$ 与 $`B`$ 的差、$`O(\delta_M)`$ 与 $`O(BM^{-D})`$ 均为更小的误差。
因 $`\Phi(z_M)`$ 一致远离零，可固定足够小的 $`\kappa\gt0`$，使

```math
\mathbb P\{T\lt\kappa B\}=O(\lambda^{-1/2}).
```

式 (23.17)。

当 $`W_{x_*}\lt\log(\kappa B)`$ 且 $`T\ge\kappa B`$ 时，
背景权重之和严格大于信号权重，所以 (23.13) 给出 $`\pi_{x_*}\lt1/2`$。
由 (23.4) 及 $`\log B=\tau_M+o(1)`$，不需要两个事件独立便有

```math
\mathbb P\{\text{Bayes 规则遗漏 }x_*\}
\ge\mathbb P\{W_{x_*}\lt\log(\kappa B)\}
     -\mathbb P\{T\lt\kappa B\}
\ge\Phi(z_M)-O(\lambda^{-1/2}).
```

式 (23.18)。

所有界一致于实际支持和块。对先验及 $`q`$ 个块平均，原始 Bayes Hamming 损失
不小于漏选个数，故任意完整数据规则的最坏归一化风险至少为
$`\Phi(z_M)-O(\lambda^{-1/2})`$。与 (23.12) 结合，得到 (23.2) 第二行的已知方向版本。
这一步使用固定基数先验，没有把稀疏模型替换为独立 Bernoulli 支持模型。

最后处理未知方向。采用 (21.16) 的直接方向检验，仍取
$`h_M=\ell^{1/4}`$。反向错误概率由 (21.17) 至多为
$`C\ell e^{-h_M}+C\ell M^{1-D}/q=o(\lambda^{-1/2})`$。
正向信号的平均检出比例趋于严格正数，故 (21.18) 与 Chebyshev 不等式给出
正向错误概率 $`O(q^{-1}+\delta_M+M^{-D})=o(\lambda^{-1/2})`$。
两种上界规则的输出均不超过 $`q`$，因此在同一数据上判向再选择支持的风险增加
至多为错误概率的两倍。揭示方向给出反向下界，证明所有 $`\xi`$ 的 (23.2)。
由 $`\lambda/\ell\to\alpha_A`$、$`\log\lambda/\log\ell\to1`$ 与 $`z_M\to z_*`$，
两式相减即得 (23.3)。∎

## 追加锚（本行以下为增补区）

## 24. 同批观测的参数修正与自适应二阶精度

**定义 24.1（初选后的振幅估计与再筛选）。** 对定义 22.1 的两组初选集合
$`A_+,A_-`$ 及基数 $`R_+,R_-`$，取基数较大的方向
$`\widehat\varepsilon`$，相等时取正向。置
$`A=A_{\widehat\varepsilon}`$、$`R=|A|`$；以下计数均按这个方向对齐。
若 $`R=0`$，输出 $`\widetilde S=\varnothing`$。若 $`R\ge1`$，令

```math
\epsilon_M=\min\{1/4,\ell^{-1}\},\qquad
U_A=\sum_{x\in A}(N_{x,+}+N_{x,-}),\qquad
V_A^{\mathrm{obs}}=\sum_{x\in A}(N_{x,+}-N_{x,-}),
```

式 (24.1)。

并定义

```math
r_A=
\begin{cases}V_A^{\mathrm{obs}}/U_A,&U_A\gt0,\\[0pt]1/2,&U_A=0,\end{cases}
\qquad
\widehat r=\min\{1-\epsilon_M,\max\{\epsilon_M,r_A\}\}.
```

式 (24.2)。

以 $`Z_x(u)=N_{x,+}\log(1+u)+N_{x,-}\log(1-u)`$ 为分数，取

```math
C=\{x\in C_+:Z_x(\widehat r)\ge\log(M/R)\},\qquad
K=\min\{M,2R\}.
```

式 (24.3)。

当 $`|C|\le K`$ 时置 $`\widetilde S=C`$；否则保留 $`C`$ 中分数最大的
$`K`$ 项，边界并列时均匀随机。方向估计仍为 $`\widehat\varepsilon`$。
该规则只使用维数和同一份观测；初选、估计和再筛选均未引入参数或额外样本。

**定理 24.2（自适应达到无约束的二阶余项）。** 固定
$`r\in(0,1)`$、$`\beta\in(1/2,1)`$，取定义 23.1 的任意序列，
其中 $`c_M\to c\in\mathbb R`$。对两个实际平稳实验，定义 24.1 的同一规则满足

```math
\max_{S\in\mathfrak S_q,\ \varepsilon\in\{+,-\}}
 \frac{\mathbb E_{S,\varepsilon}^{\mathcal E}
       |\widetilde S\triangle S|}{q}
 =\Phi(z_M)+O(\lambda^{-1/2}),\qquad
\max_{S,\varepsilon}\mathbb P_{S,\varepsilon}^{\mathcal E}
 \{\widehat\varepsilon\ne\varepsilon\}=o(\lambda^{-1/2}).
```

式 (24.4)。

余项常数允许依赖固定参数与 $`z_M`$ 所在的有界区间，规则本身不依赖它们。
这里的精度以实际中心 $`z_M`$ 表示，不将其替换为极限值。
独立高斯序列中达到一阶 Hamming 曲线的自适应程序已有
[Abraham–Castillo–Roquain 定理 7](../../../Library/Dynamics/abraham2024sharp.md)
的先例；本条处理实际补偿律下同批观测修正后的定量余项。

证明。固定实际正向及支持 $`S`$，以下所有实际矩与联合事件均在该同一律下计算。
置 $`\rho=1-\Phi(z_*)\gt0`$、$`\delta_M=\ell^3/n`$；在 (21.5) 中取
$`D=8`$。所有常数只用于证明。由 (22.6)、(22.11)–(22.12)，有

```math
\mathbb E|A_+\setminus S|\le C(q\ell^{-2}+\ell^{-1}),\qquad
\mathbb ER_-\le C\ell^{-1},\qquad
\mathbb E\bigl[R\mathbf1_{\{R\gt2q\}}\bigr]\le C\ell^{-1}.
```

式 (24.5)。

最后一项由 $`R=\max(R_+,R_-)`$ 分别取两个最大值事件得到。
在 (22.15)–(22.16) 中取一个固定的 $`\kappa\in(3\rho/4,\rho)`$，
均值与 $`\kappa q`$ 之间最终有固定正比例间隙。故 Chebyshev 不等式给出

```math
\mathbb P\{R_+\lt3\rho q/4\}
 \le C(q^{-1}+\delta_M+M^{-D}),\qquad
\mathbb P\{\widehat\varepsilon\ne+\}
 \le C(q^{-1}+\delta_M+M^{-D}+(q\ell)^{-1}).
```

式 (24.6)。

第二项还使用了 $`\mathbb P\{R_-\ge3\rho q/4\}\le C/(q\ell)`$。
两个上界均为 $`o(\lambda^{-1/2})`$。

先证明振幅估计的充分精度。记
$`N_x=N_{x,+}+N_{x,-}`$、$`T_x=N_{x,+}-N_{x,-}-rN_x`$。
在信号比较律 $`Q_r`$ 下，$`\mathbb ET_x=0`$、
$`\mathbb E T_x^2=\lambda(1-r^2)`$，且
$`\mathbb E(N_x-\lambda)^2=\lambda`$。
因此两类非负变量 $`|T_x|`$ 与 $`|N_x-\lambda|`$ 的均值至多为
$`C\sqrt\lambda`$，二阶矩至多为 $`C\lambda`$。
取固定充分大的 $`L_0`$，令 $`\mathcal N`$ 表示全部行计数均不超过
$`L_0\ell`$。比较 Poisson 尾及一行转移给出
$`\mathbb P(\mathcal N^c)\le CM^{1-D}`$。
将上述两个变量各截断在 $`N_x\le L_0\ell`$ 上，应用 (23.15) 的层积分论证，
得到同一实际支持下每类信号总和的方差界

```math
\mathrm{Var}\!\left(\sum_{x\in S}f_x\right)
 \le C\left(q\lambda+\delta_Mq^2\lambda+q^2\ell^2M^{-D}\right),
\qquad f_x\in\{
 |T_x|\mathbf1_{\{N_x\le L_0\ell\}},
 |N_x-\lambda|\mathbf1_{\{N_x\le L_0\ell\}}\}.
```

式 (24.7)。

这里双行协方差以比较均值的乘积为主项，其量级为 $`O(\lambda)`$；
并未以截断上界平方代替全部协方差。固定足够大的 $`C_1`$，再用 Chebyshev，
除去概率 $`O(q^{-1}+\delta_M+\ell M^{-D}+M^{1-D})`$ 的事件后，有

```math
\sum_{x\in S}|T_x|\le C_1q\sqrt\lambda,\qquad
\sum_{x\in S}|N_x-\lambda|\le C_1q\sqrt\lambda.
```

式 (24.8)。

又由 (24.5) 与 Markov 不等式，

```math
\mathbb P\{|A_+\setminus S|\gt q/\sqrt\lambda\}
 \le C\left(\ell^{-3/2}+(q\sqrt\ell)^{-1}\right)
 =o(\lambda^{-1/2}).
```

式 (24.9)。

令 $`\mathcal G_0`$ 为以下事件的交：方向正确、
$`3\rho q/4\le R\le2q`$、$`\mathcal N`$、(24.8) 以及
$`|A_+\setminus S|\le q/\sqrt\lambda`$。
由 (24.5)–(24.9)，$`\mathbb P(\mathcal G_0^c)=o(\lambda^{-1/2})`$。
在此事件上，$`|A\cap S|\ge\rho q/2`$ 最终成立，且

```math
U_A\ge |A\cap S|\lambda-\sum_{x\in S}|N_x-\lambda|
       \ge c_0q\lambda,\qquad
|V_A^{\mathrm{obs}}-rU_A|
 \le\sum_{x\in S}|T_x|+2L_0\ell|A\setminus S|
 \le Cq\sqrt\lambda.
```

式 (24.10)。

因为固定的 $`r`$ 最终位于剪裁区间内部，剪裁不会增加距 $`r`$ 的距离，故
$`|\widehat r-r|\le C_2/\sqrt\lambda`$。
这只控制选择偏差，并未断言给定初选集合后估计无偏。

接着证明该参数误差所需的得分包络。定义信号得分导数

```math
D_x=\frac{N_{x,+}}{1+r}-\frac{N_{x,-}}{1-r},\qquad
D_*=D_x/\sqrt\lambda.
```

式 (24.11)。

在 $`Q_r`$ 下，$`\mathbb ED_x=0`$，但这不表示导数与得分不相关；事实上
$`\mathrm{Cov}_{Q_r}(W,D_x)=\tfrac\lambda2\log\tfrac{(1+r)(1+a)}{(1-r)(1-a)}\gt0`$。
下文对两者使用共同的计数实现。对每个固定实数 $`h`$，
指数矩 $`A_h=\mathbb E_{Q_r}e^{hD_*}`$ 一致有界：其对数为

```math
\log A_h=
 \frac{\lambda(1+r)}2\left(e^{h/((1+r)\sqrt\lambda)}-1\right)
 +\frac{\lambda(1-r)}2\left(e^{-h/((1-r)\sqrt\lambda)}-1\right)
 =O_h(1).
```

式 (24.12)。

线性项恰好抵消。以 $`e^{hD_*}/A_h`$ 倾斜 $`Q_r`$ 后，两个计数仍独立 Poisson，
均值分别乘以上式中的指数因子，均与 $`\lambda`$ 同阶。
沿用定理 19.3 证明中 (19.22) 的条件计数方法：给定 $`N_-`$ 后，
$`W`$ 以及 $`W+hD_*`$ 中 $`N_+`$ 的系数均趋于严格正数 $`\log(1+r)`$。
任意长度 $`b\ge0`$ 的得分区间至多容纳 $`C_h(b+1)`$ 个整数 $`N_+`$。
由 Poisson 众数公式及 Stirling 不等式，均值与 $`\lambda`$ 同阶的
Poisson 变量最大单点质量为 $`O(\lambda^{-1/2})`$。条件化后再平均，得到

```math
Q_r^{(h)}\{t\le W\le t+b\}
 +Q_r^{(h)}\{t\le W+hD_*\le t+b\}
 \le\frac{C_h(b+1)}{\sqrt\lambda}.
```

式 (24.13)。

该上界不依赖区间位置，允许原子及任意固定格点振幅，亦不要求倾斜后的中心与原中心相同。
右侧大于一时仍是合法上界。

由 $`dQ_r=e^W dQ_{-a}`$，背景律按 $`e^{W+hD_*}`$ 倾斜的归一化常数恰为
$`A_h`$，所得律就是 $`Q_r^{(h)}`$。用 (24.13) 分割单位宽度上尾并求和，得到

```math
Q_{-a}\{W+hD_*\ge t\}
 \le\frac{C_h e^{-t}}{\sqrt\lambda}.
```

式 (24.14)。

另对任意固定 $`b_0,b_1\ge0`$，有联合交叉界

```math
Q_r\{|W-\tau_M|\le b_0+b_1|D_*|\}
 \le C\lambda^{-1/2}.
```

式 (24.15)。

为证此式，将 $`|D_*|`$ 分成区间 $`[j,j+1)`$，$`j\ge0`$，并分别处理正负号。
在正号部分按 $`h=1`$ 倾斜，负号部分按 $`h=-1`$ 倾斜。
逆密度在各自的带上至多为 $`C e^{-j}`$，而所需 $`W`$ 区间的宽度至多为
$`2b_0+2b_1(j+1)`$。由 (24.13)，每带概率至多
$`C e^{-j}(j+1)/\sqrt\lambda`$；求和即得 (24.15)。
该论证在同一二元计数实现上控制得分与导数，没有把两个边缘分布函数相加来替代联合关系。

在 $`\mathcal G_0`$ 上，$`|\log(M/R)-\tau_M|\le C_3`$。
$`Z_x(u)`$ 关于 $`u`$ 凹，且在固定的 $`r`$ 邻域中二阶导数绝对值至多为
$`C_rN_x`$。由 Taylor 定理、(24.10) 及计数截断，

```math
W_x-C_4|D_*|-C_5
 \le Z_x(\widehat r)
 \le W_x+C_4|D_*|+C_5.
```

式 (24.16)。

这里 $`|W_x-Z_x(r)|\le C aN_x=o(1)`$ 已并入 $`C_5`$。
故背景行被候选集合 $`C`$ 选中，必有
$`W_x+C_4|D_*|\ge\tau_M-C_6`$。
这包含在 $`W_x\pm C_4D_*\ge\tau_M-C_6`$ 两事件之并中；
由 (24.14)、一行转移及 $`Me^{-\tau_M}=q`$，得到

```math
\mathbb E\bigl[|C\setminus S|\mathbf1_{\mathcal G_0}\bigr]
 \le Cq\lambda^{-1/2}+CM^{1-D}=O(q\lambda^{-1/2}).
```

式 (24.17)。

这里的包络是确定的计数事件；没有将估计振幅代入 e-value 的边缘有效性结论。
同样，由 (24.16)，信号未被候选集合选中只可能在
$`W_x\lt\tau_M+C_6+C_4|D_*|`$ 时发生。
此事件与 $`\{W_x\lt\tau_M\}`$ 的差由 (24.15) 控制，再用 (23.4) 及一行转移，得到

```math
\frac1q\mathbb E\bigl[|S\setminus C|\mathbf1_{\mathcal G_0}\bigr]
 \le\Phi(z_M)+O(\lambda^{-1/2}).
```

式 (24.18)。

还须控制规则自身的输出上限。令 $`Y`$ 为信号行中满足确定包络
$`W_x+C_4|D_*|\ge\tau_M-C_6`$ 的个数。
由 (23.4)、(24.15)，$`\mathbb EY/q\to\rho`$；同一支持下两行比较给出
$`\mathrm{Var}Y\le C(q+\delta_Mq^2+q^2M^{-D})`$。
因此事件 $`\mathcal G_1=\{Y\le5\rho q/4\}`$ 的补集概率为
$`O(q^{-1}+\delta_M+M^{-D})=o(\lambda^{-1/2})`$。
在 $`\mathcal G=\mathcal G_0\cap\mathcal G_1`$ 上，最终候选信号数不超过
$`5\rho q/4`$，而 $`K=2R\ge3\rho q/2`$，其中 $`2R\lt M`$ 最终成立。
所以从 $`C`$ 删到 $`K`$ 项时，删除个数不超过 $`|C\setminus S|`$，无论删中哪些项。
逐观测有

```math
|\widetilde S\triangle S|
 \le |S\setminus C|+2|C\setminus S|\qquad\text{on }\mathcal G.
```

式 (24.19)。

坏事件上始终有 $`|\widetilde S\triangle S|\le q+2R`$。
故 (24.5) 给出

```math
\frac1q\mathbb E\bigl[|\widetilde S\triangle S|\mathbf1_{\mathcal G^c}\bigr]
 \le5\mathbb P(\mathcal G^c)
       +\frac2q\mathbb E\bigl[R\mathbf1_{\{R\gt2q\}}\bigr]
 =o(\lambda^{-1/2}).
```

式 (24.20)。

随机输出规模的期望尾部在这里是必要的；不曾用 $`M/q`$ 乘以坏事件概率。
(24.17)–(24.20) 给出已固定方向的风险上界，(24.6) 给出方向精度。
实际反向通过反转完整观测得到相同论证，所有界一致于支持。
揭示 $`r,q`$ 与方向后，本规则仍是合法的无约束选择规则；因此定理 23.2 的
全规则下界给出 (24.4) 的另一侧，证明风险等式。∎

## 追加锚（本行以下为增补区）

## 25. 非格点得分的显式 Hamming 风险系数

**定义 25.1（第三累积量与阈值常数）。** 沿用定义 23.1 的实际平稳实验、
固定参数、有限内在偏移及实际中心，另假设
$`\log(1+r)/\log(1-r)\notin\mathbb Q`$。记

```math
h_\pm=\log(1\pm r),\qquad
m_3=\frac{(1+r)h_+^3+(1-r)h_-^3}{2},\qquad
A(z)=\frac{m_3(1-z^2)}{6v^{3/2}},\qquad
k(z)=\log\frac{\varphi(z)}{\sqrt v\,\Phi(z)}.
```

式 (25.1)。

**定理 25.2（固定基数后验与两种风险的下一项）。** 在定义 25.1 下，对每个
$`\mathcal E\in\{\mathrm{pair},\mathrm{path}\}`$ 和
$`\xi\in\{\mathrm k,\mathrm o\}`$，有

```math
\begin{aligned}
H_{\mathcal E,\mathrm u}^{\xi}
 &=\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
       \left[A(z_M)+\frac1{\sqrt v}\right]+o(\lambda^{-1/2}),\\[0pt]
H_{\mathcal E,q}^{\xi}
 &=\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
       \left[A(z_M)+\frac{k(z_M)-\tfrac12\log\lambda}{\sqrt v}\right]
       +o(\lambda^{-1/2}),\\[0pt]
H_{\mathcal E,\mathrm u}^{\xi}-H_{\mathcal E,q}^{\xi}
 &=\frac{\varphi(z_M)}{\sqrt{\lambda v}}
       \left[\tfrac12\log\lambda+1-k(z_M)\right]+o(\lambda^{-1/2}).
\end{aligned}
```

式 (25.2)。

余项对真实支持一致；振幅、稀疏指数与偏移极限均固定。
这里的无约束损失除以 $`q`$，恰好基数输出的损失除以 $`2q`$，
所以第三行不比较两种规则的原始 Hamming 损失。
不要求内在偏移以指定速率收敛，但不能在这些式子中把实际中心直接替换为其极限。
本结论不包含格点相位系数、振幅趋于端点的统一余项或未知参数规则的显式系数。

证明。先取已知正向，在任一固定真实支持下工作。仍记
$`W=N_+\log((1+r)/(1-a))+N_-\log((1-r)/(1+a))`$、
$`Z=h_+N_++h_-N_-`$。比较律下两类计数为独立 Poisson 变量，
均值分别为 $`\lambda(1+b)/2,\lambda(1-b)/2`$，其中信号取
$`b=r`$，背景取 $`b=-a`$。实际观测的一行、两行分布使用 (21.5)，
以下固定 $`D=8`$、$`\delta_M=\ell^3/n`$。

首先记录同一实际支持下的有界矩转移。对各行的任意函数
$`0\le f_x\le1`$，令 $`m_x`$ 为相应一行比较律的期望，并令
$`\mu=\sum_xm_x`$。对一行事件积分，对不同行的两个事件作二重积分，得到

```math
\left|\mathbb E_S\sum_x f_x-\mu\right|
 \le C\delta_M\mu+CM^{1-D},\qquad
\mathrm{Var}_S\!\left(\sum_xf_x\right)
 \le C\left(\mu+\delta_M\mu^2+M^{2-D}\right).
```

式 (25.3)。

第二式的对角项用平方不超过自身；非对角项的误差为
$`C\delta_Mm_xm_y+CM^{-D}`$。这同样适用于信号与背景的混合求和，
不将实际行视为独立。置

```math
e_M=q^{-1}+\delta_M+\frac{M^{2-D}}{q^2}=o(\lambda^{-1/2}).
```

式 (25.4)。

接着在比较律中取出显式系数。非格点一阶 Edgeworth 展开是既有概率工具；
所用连续时间版本见
[Ferré–Hervé–Ledoux 定理 4.3–4.4](../../../Library/Dynamics/ferre2012limit.md)。
这里的驱动状态空间只有一点，加性分量是两跳幅复合 Poisson 过程。
其中心化分量满足该文平稳、谱隙与任意有限阶矩条件；单位时间增量在零和两个跳幅上
均有正质量，跳幅比无理正好排除格点。均值、方差和第三累积量依次为
$`\lambda\phi,\lambda v,\lambda m_3`$，其中第三项使用跳幅的原始三阶矩。
因而对所有实数中心一致有

```math
Q_r\!\left\{\frac{Z-\lambda\phi}{\sqrt{\lambda v}}\le x\right\}
 =\Phi(x)+\frac{\varphi(x)A(x)}{\sqrt\lambda}+o(\lambda^{-1/2}).
```

式 (25.5)。

为明确此处不增加强 Cramér 条件，可直接核对该经典 Fourier 论证的特例。
标准化特征函数的对数在零点附近为
$`-u^2/2+m_3(iu)^3/(6v^{3/2}\sqrt\lambda)+O(u^4/\lambda)`$。
在 $`|u|\le\lambda^{1/12}`$ 上，将特征函数误差除以
$`|u|`$ 后积分为 $`O(\lambda^{-1})`$；到足够小的固定倍数
$`\eta\sqrt\lambda`$ 为止，余下部分由高斯衰减控制。
对任意固定 $`C\gt\eta`$，原始频率所在的紧环上

```math
\frac{1+r}{2}(1-\cos(th_+))+
\frac{1-r}{2}(1-\cos(th_-))\gt0\qquad(t\ne0),
```

式 (25.6)。

故从该处到 $`C\sqrt\lambda`$ 的积分指数衰减。
有界密度的平滑不等式剩余项为 $`O(1/(C\sqrt\lambda))`$。
先令样本尺度趋于无穷，再令固定的 $`C`$ 趋于无穷，便给出 (25.5) 的一致余项。
Edgeworth 密度在极端尾部可能有符号；取其正部并归一化只改变指数小的高斯尾质量，
同样可使用概率分布版本的平滑不等式。论证对每个实际实数时间成立，
没有假设特征函数在所有大频率上一致远离一。

由 (25.5) 连续的近似函数，最大原子质量为 $`o(\lambda^{-1/2})`$。
在两个距离固定的端点相减，得到任意固定 $`h\gt0`$ 的一致区间估计

```math
\sup_t\left|
\sqrt\lambda\,Q_r\{t\le Z\lt t+h\}
-\frac h{\sqrt v}\varphi\!\left(\frac{t-\lambda\phi}{\sqrt{\lambda v}}\right)
\right|\longrightarrow0.
```

式 (25.7)。

这也与 [Stone 的非格点局部极限定理](../../../Library/Dynamics/stone1967local.md)
一致，所述对象为区间概率而非密度。
在计数截断事件上，$`|W-Z|\le Ca\ell=o(1)`$，补集概率可取为
$`O(M^{-D})`$。先用任意固定宽度的区间夹逼，再将宽度趋零，
由 (25.5)–(25.7) 可知用补偿得分替换未补偿得分的分布函数误差为
$`o(\lambda^{-1/2})`$；区间估计及最大原子结论也一并转移。
这不要求变化中的补偿跳幅比始终无理。

令 $`z_t=(t-\lambda\phi)/\sqrt{\lambda v}`$。两比较律满足精确恒等式
$`dQ_r=e^W dQ_{-a}`$，因为总 Poisson 强度相同。
将上尾分成固定宽度区间，在有限段用 (25.7)，其余用一致区间上界与几何级数，
再令区间宽度趋零，即得到

```math
\begin{aligned}
Q_r\{W\lt t\}
 &=\Phi(z_t)+\frac{\varphi(z_t)A(z_t)}{\sqrt\lambda}
       +o(\lambda^{-1/2}),\\[0pt]
Q_{-a}\{W\ge t\}
 &=e^{-t}\frac{\varphi(z_t)}{\sqrt{\lambda v}}(1+o(1)),
 \qquad t=\tau_M+O(\log\lambda).
\end{aligned}
```

式 (25.8)。

尾常数中的一来自 $`\int_0^\infty e^{-u}\,du=1`$。
一行转移中的相对误差与加性误差在本节精度下均可忽略。
特别地，对固定 $`\epsilon\gt0`$，实际落在阈值邻域的行数
$`J_\epsilon=\#\{x:|W_x-\tau_M|\le\epsilon\}`$ 满足

```math
\frac{\mathbb E_SJ_\epsilon}{q}
 =\frac{\varphi(z_M)}{\sqrt{\lambda v}}
    \left(2\epsilon+2\sinh\epsilon\right)+o(\lambda^{-1/2}).
```

式 (25.9)。

两项分别来自信号区间质量和背景上的积分
$`\int_{-\epsilon}^{\epsilon}e^{-u}\,du`$；最大原子估计允许闭区间端点。

先处理恰好基数输出。置
$`t_* =\tau_M-\tfrac12\log\lambda+k(z_M)`$，
令 $`N(t)=\#\{x:W_x\ge t\}`$。对每个固定实数位移，(25.8) 给出

```math
\frac{\mathbb E_SN(t_*+u)}q
 =1-\Phi(z_M)+e^{-u}\Phi(z_M)+o(1).
```

式 (25.10)。

由于正态分布函数在这里一致远离零，对于任意固定正的夹逼宽度，
左右两个期望与目标基数各有线性间隔。由 (25.3)，排序阈值不在
$`[t_*-\epsilon,t_*+\epsilon]`$ 中的概率至多
$`C_\epsilon e_M=o(\lambda^{-1/2})`$。
在其补集上，真信号被遗漏的比例夹在两个端点的信号分布函数之间。
端点间质量由 (25.7) 控制为
$`O(\epsilon/\sqrt\lambda)+o(\lambda^{-1/2})`$。
先固定宽度取极限，再令宽度趋零，排序规则的期望损失因此为
$`Q_r\{W\lt t_*\}+o(\lambda^{-1/2})`$。
定理 21.2 的完整似然与置换对称性已给出此规则在实际两个实验中的精确极小极大性。
在 (25.8) 中展开中心位移，二次余项为
$`O((\log\lambda)^2/\lambda)=o(\lambda^{-1/2})`$，得到 (25.2) 第二行。

无约束问题需要更精确的所有规则下界。记 $`w_x=e^{W_x}`$、
$`B_0=(M-q)/q`$。完整数据的均匀基数先验后验正比于
$`\prod_{x\in S}w_x`$。
这种有限乘积后验及 Hamming Bayes 判别的先例见
[Butucea–Mammen–Ndaoud–Tsybakov](../../../Library/Dynamics/butucea2023selection.md)；
下面的独立性仅属于辅助后验变量。对每个正的公共倾斜参数，取相互独立的辅助变量，并置

```math
p_x(t)=\frac{t w_x}{B_0+t w_x},\qquad
I_x\sim\mathrm{Bernoulli}(p_x(t)).
```

式 (25.11)。

条件于 $`\sum_x I_x=q`$，公共因子全部相消，正好得到上述完整数据后验。
这是经典条件 Poisson／拒绝抽样表示，见
[Boistard–Lopuhaä–Ruiz-Gazen 的式 (2.1)、(2.5)](../../../Library/Dynamics/boistard2012rejective.md)。
实际观测的依赖性不由此消失。

令 $`U(t)=\sum_xp_x(t)`$、$`V(t)=\sum_xp_x(t)(1-p_x(t))`$。
记 $`U=U(1)`$、$`V=V(1)`$。精确换测度给出比较期望的两条恒等式

```math
\begin{aligned}
q\,\mathbb E_{Q_r}p(W)+(M-q)\mathbb E_{Q_{-a}}p(W)&=q,\\[0pt]
q\,\mathbb E_{Q_r}[p(W)(1-p(W))]
 +(M-q)\mathbb E_{Q_{-a}}[p(W)(1-p(W))]
 &=q\,\mathbb E_{Q_r}[1-p(W)].
\end{aligned}
```

式 (25.12)。

第一式的被积函数为 $`p+B_0e^{-W}p=1`$，再乘以
$`1-p`$ 即得第二式。由固定窗口的区间上界，将 logistic 函数与
阈值阶跃函数比较，且 $`\log B_0=\tau_M+o(1)`$，可得右端为
$`q[\Phi(z_M)+o(1)]`$。因此 (25.3) 给出真实数据下

```math
\begin{aligned}
\mathbb E_SU&=q+O(\delta_Mq+M^{1-D}),&
\mathbb E_SV&=q[\Phi(z_M)+o(1)],\\[0pt]
\mathrm{Var}_S U+\mathrm{Var}_S V
 &\le C(q+\delta_Mq^2+M^{2-D}).
\end{aligned}
```

式 (25.13)。

存在固定正数 $`\kappa`$，使对每个固定 $`0\lt \eta\lt 1`$，事件

```math
G_\eta=\left\{V\ge\kappa q,\quad
 |U-q|\le\tfrac12\kappa e^{-\eta}\eta q\right\}
```

式 (25.14)。

的补集概率至多为 $`C_\eta e_M`$。
总均值从零连续严格增长到行数，所以方程 $`U(t)=q`$ 有唯一正解。
又因 $`dU(e^\theta)/d\theta=V(e^\theta)`$，而在
$`|\theta|\le\eta`$ 上每个方差项相对于原项的比值介于
$`e^{-\eta}`$ 和 $`e^\eta`$ 之间，积分得在该好事件上

```math
|\log t|\lt \eta,\qquad V(t)\ge e^{-\eta}\kappa q.
```

式 (25.15)。

现在条件于实际数据，固定这一使总均值等于基数的辅助分布。
设 $`T_{-x}=\sum_{y\ne x}I_y`$，后验包含概率为 $`\pi_x`$。
精确后验赔率满足

```math
\frac{\pi_x}{1-\pi_x}
 =\frac{t w_x}{B_0}
   \frac{\mathbb P\{T_{-x}=q-1\}}{\mathbb P\{T_{-x}=q\}}.
```

式 (25.16)。

这里可直接复用上述拒绝抽样论文的引理 1 与式 (2.10)：
当总方差 $`d_B=V(t)`$ 趋于无穷，条件某一个变量为一时的总数中心概率，
除以未条件化概率，等于 $`1+O(d_B^{-1})`$，对所选坐标一致。
对互补 Bernoulli 数组也使用同一结论，再除两式，(25.16) 中的相邻概率比为
$`1+O(d_B^{-1})`$。
这不要求各概率远离零或一，也不要求总方差占坐标数的固定比例。
于是同时对所有行，在好事件上有

```math
\log\frac{\pi_x}{1-\pi_x}
 =W_x-\log B_0+\log t+O(q^{-1}).
```

式 (25.17)。

此一致界是每个已实现参数数组的确定性结论，无须对行数作并集界。
令 $`B=\{x:\pi_x\gt 1/2\}`$，相等时不选。
由后验概率和等于固定基数，输出大小至多为其两倍。
对每个固定 $`\epsilon\gt0`$，选择足够小的固定倾斜窗口，
由 (25.15)–(25.17) 得

```math
\{x:W_x\gt \tau_M+\epsilon\}\subset B
 \subset\{x:W_x\ge\tau_M-\epsilon\},
```

式 (25.18)。

其失效概率至多为 $`C_\epsilon e_M`$。

为把这个后验阈值结论转成期望风险，令
$`A_\tau=\{x:W_x\ge\tau_M\}`$，将其按得分截到至多基数个元素得
$`C_\tau`$，并在同分处均匀随机化。设
$`N=|A_\tau|`$、$`\mu=\mathbb E_SN`$。
由 (25.8)，存在固定正数 $`\kappa_0`$ 使
$`\mu/q=1-\Phi(z_M)+o(1)\le1-\kappa_0`$。
结合 (25.3) 和确定性不等式，得到

```math
(N-q)_+\le\frac{(N-\mu)^2}{4(q-\mu)},\qquad
\frac{\mathbb E_S|A_\tau\triangle C_\tau|}{q}
 \le C e_M=o(\lambda^{-1/2}).
```

式 (25.19)。

这控制的是删除数的期望，未把未截断输出在异常事件上当作有界。
在 (25.18) 成立时，两集合的差只可能位于阈值窗口；在其补集上，
后验规则与截断规则的输出大小之和至多为三倍基数。因此

```math
\mathbb E_S|B\triangle C_\tau|
 \le\mathbb E_SJ_\epsilon
     +\mathbb E_S|A_\tau\triangle C_\tau|
     +3qC_\epsilon e_M.
```

式 (25.20)。

Hamming 损失对输出集合的变化满足三角不等式。用 (25.9)、(25.19)–(25.20)，
先固定窗口宽度取尺度极限，再令宽度趋零，证明后验规则与原阈值规则的
归一化期望损失相差 $`o(\lambda^{-1/2})`$，且对支持一致。
原阈值风险由一行转移与 (25.8) 得

```math
\frac{\mathbb E_S|A_\tau\triangle S|}{q}
 =\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
       \left[A(z_M)+\frac1{\sqrt v}\right]+o(\lambda^{-1/2}).
```

式 (25.21)。

后验规则是均匀固定基数先验下的 Hamming Bayes 规则。
置换正类状态将完整路径或独立对及其分布一并映到置换后的支持，
该规则连同严格阈值的同分约定均保持等变，所以风险对支持恒定。
任意完整数据规则的最大风险不小于此先验 Bayes 风险；因此该常风险正是
无约束极小极大风险。(25.21) 给出 (25.2) 第一行的匹配上下界。

已知反向由完整数据反序得到同一结果。
未知方向时，定理 23.2 证明中的方向检验误差为 $`o(\lambda^{-1/2})`$。
正确对齐同一数据后，使用恰好基数排序规则或上面的截断阈值规则；
两者输出均至多为基数，故错误对齐对相应归一化损失的影响至多为
方向错误概率的固定倍数。这里不要求方向检验与支持规则独立。
揭示方向给出匹配下界，完成两种未知方向风险的展开。两式相减即得风险差。∎

## 追加锚（本行以下为增补区）

## 26. 格点 Hamming 风险的连续周期修正

**定义 26.1（格距与两种阈值相位）。** 沿用定义 23.1，另假设两个固定跳幅的
比值为有理数。取最大格距，使

```math
h_+=h k_+,\qquad h_-=h k_-,\qquad
h\gt0,\quad k_+,k_-\in\mathbb Z,\quad \gcd(k_+,k_-)=1.
```

式 (26.1)。

第三累积量率及函数 $`A,k`$ 使用 (25.1) 的代数定义；此处不采用定义 25.1 的
非格点假设。置

```math
L_h=\frac h{e^h-1},\qquad U_h=\frac h{1-e^{-h}},\qquad
l_h=\log L_h,\qquad u_h=\log U_h=l_h+h.
```

式 (26.2)。

定义两个连续的周期为格距的函数，其一个周期上的表达式为

```math
\begin{aligned}
F_h(d)&=d-\frac h2+U_he^{-d},&&0\le d\le h,\\[0pt]
G_h(y)&=y+\frac h2-e^y+L_h,&&l_h\le y\le u_h.
\end{aligned}
```

式 (26.3)。

端点满足 $`F_h(0)=F_h(h)=h/2+L_h`$ 和
$`G_h(l_h)=G_h(u_h)=l_h+h/2`$，所以周期延拓确实连续。
令

```math
\begin{aligned}
t_*&=\tau_M-\tfrac12\log\lambda+k(z_M),\\[0pt]
d_M&=h\left\lceil\frac{\tau_M}{h}\right\rceil-\tau_M,\\[0pt]
y_M&=h\left\lceil\frac{t_*+l_h}{h}\right\rceil-t_*.
\end{aligned}
```

式 (26.4)。

于是 $`0\le d_M\lt h`$、$`l_h\le y_M\lt u_h`$；在周期端点采用任一等价代表值
不改变下述结论。两个相位均由同一实际样本尺度和支持基数确定。

**定理 26.2（允许任意贴近格点边界的显式系数）。** 对定义 26.1 的任意序列，
每个实际实验与方向信息情形都满足

```math
\begin{aligned}
H_{\mathcal E,\mathrm u}^{\xi}
 &=\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
   \left[A(z_M)+\frac{F_h(d_M)}{\sqrt v}\right]
   +o(\lambda^{-1/2}),\\[0pt]
H_{\mathcal E,q}^{\xi}
 &=\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
   \left[A(z_M)+\frac{k(z_M)-\tfrac12\log\lambda+G_h(y_M)}{\sqrt v}\right]
   +o(\lambda^{-1/2}).
\end{aligned}
```

式 (26.5)。

其中实验为平稳独立对或平稳连续路径，方向可以已知或未知；振幅、稀疏指数及有限偏移
极限仍固定。余项对真实支持一致，不要求相位与格点边界保持距离，也不要求两个相位收敛。
因此

```math
H_{\mathcal E,\mathrm u}^{\xi}-H_{\mathcal E,q}^{\xi}
 =\frac{\varphi(z_M)}{\sqrt{\lambda v}}
  \left[\tfrac12\log\lambda+F_h(d_M)-k(z_M)-G_h(y_M)\right]
  +o(\lambda^{-1/2}).
```

式 (26.6)。

这里仍比较分别除以 $`q`$ 与 $`2q`$ 的损失。
连续周期修正并不宣称实际相位均匀分布；结论也不包括变化振幅的格点与非格点过渡、
无穷偏移或未知参数规则的显式系数。

证明。先固定正向与真实支持，使用两种实际实验共同的一行、两行转移。
以下取固定 $`D=10`$，仍记 $`\delta_M=\ell^3/n`$，并沿用 (25.4) 的误差量。
稀疏基数按正幂增长，故该误差量及其平方根均小于任意固定负幂的对数尺度。
未补偿信号得分落在格点上；补偿得分与它使用同一计数，满足
$`|W-Z|\le Ca(N_++N_-)`$。在所有行计数不超过固定倍数对数的事件上，
对每个固定 $`K\gt0`$，一致误差为

```math
\eta_M=Ca\ell=o(\lambda^{-K}),
```

式 (26.7)。

其补集实际概率为 $`O(M^{1-D})`$。

首先引用经典格点 Edgeworth 工具。
[Bobkov–Ulyanov 的式 (1.3)、(3.2)](../../../Library/Dynamics/bobkov2022chebyshev.md)
给出独立同分布整数和在整数边界处的一致半格距修正。
单位时间复合 Poisson 增量在零及两个跳幅上有正质量，最大格距正是定义中的格距，
且有任意阶矩。对整数时间直接应用该工具；对实际实数时间，将其拆为整数部分及
独立的不足一单位时间余项。余项仍在同一格点上，所以条件化后的边界仍为格点。
余项的中心化均值为零、矩一致有界，Taylor 展开的额外误差为
$`O(\lambda^{-1})`$。由此对中央区域的格点边界一致有

```math
\begin{aligned}
Q_r\{Z\lt b\}
 &=\Phi(z_b)+\frac{\varphi(z_b)}{\sqrt\lambda}
       \left[A(z_b)-\frac h{2\sqrt v}\right]+o(\lambda^{-1/2}),\\[0pt]
Q_r\{Z=b\}
 &=\frac{h\varphi(z_b)}{\sqrt{\lambda v}}+o(\lambda^{-1/2}),
 \qquad z_b=\frac{b-\lambda\phi}{\sqrt{\lambda v}}.
\end{aligned}
```

式 (26.8)。

第二式也由相邻边界相减得到；最大单点质量由条件 Poisson 最大原子界控制为
$`O(\lambda^{-1/2})`$，对所有位置均成立。
此处半格距的符号来自严格边界：小于一个格点等于不超过它的前一个格点。

精确换测度仍为 $`dQ_r=e^W dQ_{-a}`$。
在计数截断事件上，以未补偿得分替换指数中的补偿得分只产生
$`O(\eta_M)`$ 的相对误差。补集分别在两比较律下以计数尾界处理，
即使乘以背景与信号数之比也可忽略。
对固定格点宽度的尾部作几何求和，由 (26.8) 得

```math
\begin{aligned}
Q_{-a}\{Z=b\}
 &=e^{-b}\frac{h\varphi(z_b)}{\sqrt{\lambda v}}(1+o(1)),\\[0pt]
Q_{-a}\{Z\gt b\}
 &=e^{-b}\frac{L_h\varphi(z_b)}{\sqrt{\lambda v}}(1+o(1)).
\end{aligned}
```

式 (26.9)。

这些式子对本证明所用的有界标准化中心及对数尺度的阈值位移一致成立。
无限几何尾由全位置的原子上界控制。

接着证明无约束问题的后验风险比较。在格点上，固定窄窗口仍可容纳整个原子，
所以这里使用条件损失差。
(25.11)–(25.17) 的固定基数后验表示、精确混合期望和方差转移不依赖非格点假设。
后验辅助方差的期望只需一阶正态极限：logistic 函数在固定大窗口外与阶跃函数的
差指数小，窗口概率为 $`O((L+1)/\sqrt\lambda)`$。
因此其期望仍为 $`q[\Phi(z_M)+o(1)]`$。
对每个固定正的精度参数，实际集中界和拒绝抽样的相邻概率比给出一个数据事件，
其补集在每个支持下的概率至多为 $`C_\epsilon e_M`$，在该事件上对所有行同时有

```math
\left|\log\frac{\pi_x}{1-\pi_x}-(W_x-\tau_M)\right|\le\epsilon.
```

式 (26.10)。

辅助总方差的增长已由真实模型证明；不从总均值等于基数单独推断这一条件。

令后验 Bayes 集合为 $`B=\{x:\pi_x\gt 1/2\}`$，阈值集合为
$`A_\tau=\{x:W_x\ge\tau_M\}`$，将后者按分数截到至多基数个元素得
$`C_\tau`$。先固定规则的独立辅助随机数。对给定完整数据，任意规则与 Bayes 规则的条件 Hamming 损失之差为

```math
\mathbb E\bigl[|T\triangle S|-|B\triangle S|\mid\mathcal D\bigr]
 =\sum_x|2\pi_x-1|\,1_{\{x\in T\triangle B\}}.
```

式 (26.11)。

这一式子在均匀固定基数先验下使用。好事件上的阈值分歧只能发生在
$`|W_x-\tau_M|\le\epsilon`$ 内；由 (26.10)，其中每行的损失差权重
至多为 $`C\epsilon`$。计该窗口行数为 $`J_\epsilon`$。
信号的固定窗口上界和精确换测度给出

```math
\frac{\mathbb E_SJ_\epsilon}{q}
 \le\frac{C(1+\epsilon)}{\sqrt\lambda},
 \qquad 0\lt \epsilon\le1.
```

式 (26.12)。

此上界容许窗口中有原子。
一阶正态极限保证阈值输出的期望大小低于基数一个固定比例，
(25.19) 的方差论证于是仍给出期望截断代价为 $`O(qe_M)`$。
后验输出大小至多为两倍基数，截断输出至多为基数。
因此在好事件补集上，条件损失差至多为三倍基数。
对 (26.11) 取先验及辅助随机数平均，得到

```math
0\le
\frac{\mathbb E|C_\tau\triangle S|-\mathbb E|B\triangle S|}{q}
\le \frac{C\epsilon(1+\epsilon)}{\sqrt\lambda}+C_\epsilon e_M.
```

式 (26.13)。

先固定精度参数取极限，再令精度趋零。
两规则均对支持置换等变，故先验平均风险也是每个实际支持上的相同风险。
完整数据 Bayes 风险等于极小极大风险；再去掉期望截断代价，得出无约束风险与
原阈值风险之差为 $`o(\lambda^{-1/2})`$。
这一结论没有使用局部无原子性。

现在计算该阈值风险。记 $`B_0=(M-q)/q`$。
比较律中在阈值 $`\log B_0`$ 的归一化风险精确等于
$`\mathbb E_{Q_r}\min(1,B_0e^{-W})`$。
改用实际阈值的损失差至多为 $`q/M`$：两阈值间的被积损失差介于零与该值之间。
函数 $`u\mapsto\min(1,e^u)`$ 的 Lipschitz 常数为一，而
$`\mathbb E_{Q_r}|W-Z|=O(a\lambda)`$。
因此结合实际一行转移，有

```math
H_{\mathcal E,\mathrm u}^{\mathrm k}
 =\mathbb E_{Q_r}\min(1,e^{\tau_M-Z})+o(\lambda^{-1/2}).
```

式 (26.14)。

令 $`b=h\lceil\tau_M/h\rceil`$。右端期望可写为

```math
Q_r\{Z\lt b\}
 +e^{\tau_M-b}\sum_{j\ge0}e^{-jh}Q_r\{Z=b+jh\}.
```

式 (26.15)。

代入 (26.8)，半格距项、中心位移项和几何尾项的系数分别为
$`-h/2,d_M,U_he^{-d_M}`$，得到 (26.5) 第一行。
端点处它们的总和连续，故允许补偿把整个原子推过任意贴近格点的阈值。
这里连续的是合并损失，个别分布函数无须有相同连续性。

再处理恰好基数的输出。最大补偿得分规则是精确 Bayes 规则；
将未补偿得分按同分均匀随机排序，得到另一个恰好基数规则。
在计数截断事件上，两个得分的差至多为 (26.7)，最终小于半个格距，
所以不同格点之间的排序相同，两规则的分歧仅位于一个同分组。
对该组中一对被交换的位置，完整数据的后验包含概率满足

```math
|\pi_i-\pi_j|
 =\frac{|w_i-w_j|e_{q-1}(w_{-\{i,j\}})}{e_q(w)}
 \le e^{2\eta_M}-1.
```

式 (26.16)。

因为分母至少为较小权重乘以分子中的对称多项式。
至多交换基数对位置，故归一化条件风险代价至多为右端。
计数异常概率也可忽略；取先验平均并用置换对称性，证明未补偿排序规则与
受约束极小极大风险相差 $`o(\lambda^{-1/2})`$。
此步骤容许补偿真实地拆开同分组。

为分析未补偿排序，选一个确定的格点边界和同分接受比例，使随机阈值规则的
实际期望输出大小恰为基数。该规则接受所有得分高于边界的行，并以独立均匀辅助变量
在边界处按该比例接受。期望计数对边界单调，由线性插值可选到所需比例；
支持置换对称性保证它不依赖真实支持。记此随机集合为 $`R`$。
对同一个得分与辅助变量的字典序，阈值集合与恰好基数排序集合 $`T_Z`$
总是互相包含，故

```math
|R\triangle T_Z|=\bigl||R|-q\bigr|,\qquad
\frac{\mathbb E_S|R\triangle T_Z|}{q}
 \le C\sqrt{e_M}=o(\lambda^{-1/2}).
```

式 (26.17)。

第二式用恰好的期望匹配和 (25.3) 的方差界；对独立的同分辅助变量积分不改变该界。
比较律的期望和由实际期望等于基数可知为相同数量级。
期望遗漏比例的差也由 (26.17) 控制。

设所选边界为 $`b`$、同分接受比例为 $`\alpha`$。
在临界排序阈值两侧取足够大的固定格点位移，由 (26.8)–(26.9) 的期望计数
即可夹住这个边界，故 $`b=t_*+y`$，其中位移有界。
信号接受比例为 $`1-\Phi(z_M)+o(1)`$。
背景在边界之上和边界处的贡献分别给出下式中的两个项，精确期望匹配遂蕴含

```math
1=1-\Phi(z_M)+\Phi(z_M)e^{-y}(L_h+\alpha h)+o(1),
\qquad
\alpha=\frac{e^y-L_h}{h}+o(1).
```

式 (26.18)。

接受比例在零与一之间，因此
$`y\in[l_h,u_h]+o(1)`$。
随机阈值的信号遗漏概率为

```math
Q_r\{Z\lt b\}+(1-\alpha)Q_r\{Z=b\}
 =\Phi(z_M)+\frac{\varphi(z_M)}{\sqrt\lambda}
  \left[A(z_M)+\frac{b-\tau_M+h/2-\alpha h}{\sqrt v}\right]
  +o(\lambda^{-1/2}),
```

式 (26.19)。

实际一行转移的误差仍可忽略。由 (26.18)，方括号中的阈值修正为

```math
-\tfrac12\log\lambda+k(z_M)
   +y+\frac h2-e^y+L_h+o(1).
```

式 (26.20)。

实际边界与 (26.4) 的规范边界均为格点，所以两个位移相差整倍格距。
若实际位移越出规定区间，只能越出一个趋零的距离。
函数代表式在区间两端取同一值，且端点附近导数有界，
所以 (26.20) 中的最后四项可一致替换为 $`G_h(y_M)+o(1)`$。
结合 (26.16)–(26.19)，得到 (26.5) 第二行。
这里对任意贴近端点的序列都使用同一论证，没有排除会使同分接受比例趋于零或一的序列。

已知反向实验由完整数据反序处理。未知方向时，采用第 23 章误差为
$`o(\lambda^{-1/2})`$ 的方向检验，再在同一对齐数据上使用截断阈值或排序规则。
两规则输出均至多为基数，所以误判方向只增加固定倍数的方向错误概率。
揭示方向给出相应下界，无需方向检验与支持规则独立。
最后将两风险展开相减即得 (26.6)。∎

## 追加锚（本行以下为增补区）
