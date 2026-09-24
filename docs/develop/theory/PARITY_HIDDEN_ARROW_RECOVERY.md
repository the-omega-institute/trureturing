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
